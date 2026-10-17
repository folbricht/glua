package glua

import (
	"iter"
	"math"
	"math/bits"
	"strings"
	"unsafe"
)

// node is one slot of a table's hash part. A deleted key stays with a nil value, so
// assigning nil during a traversal is safe; a rehash drops it.
type node struct {
	k, v Value
}

// Table is a Lua table: an array part for the keys 1..n, which may hold nils, and an
// open-addressing hash part of our own. Go maps are not used: they rehash the key on every access and cannot
// support next() without side tables. Table methods are raw: they never run metamethods.
type Table struct {
	arr   []Value
	nodes []node // length is zero or a power of two; linear probing from hash & mask
	used  int    // nodes holding a key, deleted ones included
	meta  *Table
	// index caches this table's __index when it is a table and this table serves as a
	// metatable, for the hot loop's inline hop. Writing a key that starts with "__" clears
	// it; the driver fills it for a mutable metatable, and Freeze for a frozen one.
	index *Table
	flags uint8
	// metaOK caches that setmetatable accepted this table as a metatable: no __mode, and no
	// __gc without __close. Cleared with index.
	metaOK bool
}

// Table flags. The absent bits cache that a metatable lacks a metamethod. They are filled
// lazily only on mutable tables, Freeze computes them in full, so reading a shared table
// never writes. Any raw write of a key that starts with "__" clears them.
const (
	tabFrozen = 1 << iota
	tabNoIndex
	tabNoNewIndex
	tabNoEq
	tabNoLen
	tabNoCall
	tabNoClose
	tabGuarded // an environment: the reserved names in it cannot be assigned

	tabAbsent = tabNoIndex | tabNoNewIndex | tabNoEq | tabNoLen | tabNoCall | tabNoClose
)

// cachedEvents are the metamethods whose absence a metatable caches, with their flag.
var cachedEvents = map[string]uint8{
	"__index": tabNoIndex, "__newindex": tabNoNewIndex, "__eq": tabNoEq,
	"__len": tabNoLen, "__call": tabNoCall, "__close": tabNoClose,
}

// eventBit is cachedEvents[event], without a map lookup.
func eventBit(event string) uint8 {
	switch event {
	case "__index":
		return tabNoIndex
	case "__newindex":
		return tabNoNewIndex
	case "__eq":
		return tabNoEq
	case "__len":
		return tabNoLen
	case "__call":
		return tabNoCall
	case "__close":
		return tabNoClose
	}
	return 0
}

// metaGet returns the metamethod event of the metatable mt, using and filling the cache of
// absent metamethods.
func (mt *Table) metaGet(event string) Value {
	bit := eventBit(event)
	if mt.flags&bit != 0 {
		return Value{}
	}
	v := mt.Get(String(event))
	if v.IsNil() && bit != 0 && mt.flags&tabFrozen == 0 {
		mt.flags |= bit
	}
	return v
}

// NewTable returns a table with room for narr array items and nhash other keys.
func NewTable(narr, nhash int) *Table {
	t := &Table{}
	if narr > 0 {
		// like C Lua, the array part has its full size from the start, nils included, so
		// that {1, nil, 3} has length 3
		t.arr = make([]Value, narr)
	}
	if nhash > 0 {
		t.nodes = make([]node, nodeSize(nhash))
	}
	return t
}

// nodeSize returns the power of two that holds n keys at a load factor of 3/4.
func nodeSize(n int) int {
	size := 4
	for size*3 < n*4 {
		size *= 2
	}
	return size
}

// keyEq is key equality for normalised keys: the same two words, or two strings with the
// same bytes behind different pointers.
func keyEq(a, b *Value) bool {
	if same(a, b) {
		return true
	}
	return a.n == b.n && a.n>>56 == kindString && !isScalar(a.p) && !isScalar(b.p) && a.str() == b.str()
}

// findNode returns the index of key in the hash part, or -1.
func (t *Table) findNode(key *Value, h uint64) int {
	if len(t.nodes) == 0 {
		return -1
	}
	mask := uint64(len(t.nodes) - 1)
	for j := uint64(0); j <= mask; j++ {
		idx := (h + j) & mask
		nd := &t.nodes[idx]
		if nd.k.p == nil {
			return -1
		}
		if keyEq(&nd.k, key) {
			return int(idx)
		}
	}
	return -1
}

// Get returns t[key] without metamethods. A nil or NaN key reads as nil.
func (t *Table) Get(key Value) Value {
	v, _ := t.getSlot(key)
	return v
}

// getSlot returns t[key] and, for a key found in the hash part, its node index (else -1).
func (t *Table) getSlot(key Value) (Value, int) {
	key, ok := normKey(key)
	if !ok {
		return Value{}, -1
	}
	if key.p == tInt() {
		if i := int64(key.n) - 1; uint64(i) < uint64(len(t.arr)) {
			return t.arr[i], -1
		}
	}
	if i := t.findNode(&key, hashValue(key)); i >= 0 {
		return t.nodes[i].v, i
	}
	return Value{}, -1
}

// Set assigns t[key] = val without metamethods. It panics if t is frozen, or if key is nil or NaN.
// A short string key that is a name gets the pointer the constants of loaded scripts share,
// so that Lua code finds it inline.
func (t *Table) Set(key, val Value) {
	if t.flags&tabFrozen != 0 {
		panic("glua: attempt to modify a frozen table")
	}
	key, ok := normKey(key)
	if !ok {
		if key.p == nil {
			panic("glua: table index is nil")
		}
		panic("glua: table index is NaN")
	}
	t.set(canonKey(key), val)
}

// set assigns t[key] = val for a normalised key.
func (t *Table) set(key, val Value) {
	if (t.flags&tabAbsent != 0 || t.index != nil || t.metaOK) && key.isString() && strings.HasPrefix(key.str(), "__") {
		t.flags &^= tabAbsent // a metamethod may have appeared
		t.index, t.metaOK = nil, false
	}
	if key.p == tInt() {
		i := int64(key.n) - 1
		if uint64(i) < uint64(len(t.arr)) {
			t.arr[i] = val
			return
		}
		if i == int64(len(t.arr)) && !val.IsNil() {
			if len(t.arr) == cap(t.arr) && t.sparse() {
				// a full array part, mostly empty, as a queue's that drops its head leaves
				// it: resize it as C Lua would, rather than double it
				t.resize(key)
				t.set(key, val)
				return
			}
			if len(t.nodes) > 0 { // the key may be in the hash part, past the end of the array
				if idx := t.findNode(&key, hashValue(key)); idx >= 0 {
					t.nodes[idx].v = Value{} // a deleted key; the next rehash drops it
				}
			}
			t.appendArr(val)
			return
		}
	}
	h := hashValue(key)
	if idx := t.findNode(&key, h); idx >= 0 {
		t.nodes[idx].v = val
		return
	}
	if val.IsNil() {
		return
	}
	if (t.used+1)*4 > len(t.nodes)*3 {
		if t.resize(key) {
			t.set(key, val) // the key may belong in the array part now
			return
		}
	}
	t.insert(key, val, h)
}

// resize makes room for the new key k, as C Lua's rehash does: it counts the integer keys,
// k included, and gives the array part the largest size n that keys 1..n fill more than
// half, growing or shrinking it, then sizes the hash part for the rest. It reports whether
// the array part grew.
func (t *Table) resize(k Value) bool {
	var nums [64]int // nums[i]: integer keys in (2^(i-1), 2^i]
	nint := 0
	count := func(key Value) {
		if key.p == tInt() {
			if n := int64(key.n); n >= 1 {
				nums[bitsLen(uint64(n-1))]++
				nint++
			}
		}
	}
	for i := range t.arr {
		if !t.arr[i].IsNil() {
			nums[bitsLen(uint64(i))]++
			nint++
		}
	}
	live := 0
	for i := range t.nodes {
		if nd := &t.nodes[i]; !nd.v.IsNil() {
			count(nd.k)
			live++
		}
	}
	count(k)
	na := computeSizes(&nums, nint)
	if na == len(t.arr) {
		t.rehash(1)
		return false
	}
	old, oldArr := t.nodes, t.arr
	if na > len(t.arr) {
		t.arr = append(t.arr, make([]Value, na-len(t.arr))...)
		oldArr = nil
	} else {
		t.arr = append(make([]Value, 0, na), oldArr[:na]...) // a new array, so the old one is freed
		oldArr = oldArr[na:]
		for i := range oldArr {
			if !oldArr[i].IsNil() {
				live++ // moves to the hash part
			}
		}
	}
	t.nodes = nil
	t.used = 0
	movedToArray := 0
	for i := range old {
		nd := &old[i]
		if nd.v.IsNil() {
			continue
		}
		if nd.k.p == tInt() && int64(nd.k.n) >= 1 && int64(nd.k.n) <= int64(na) {
			t.arr[nd.k.n-1] = nd.v
			movedToArray++
		}
	}
	rest := live - movedToArray
	if !(k.p == tInt() && int64(k.n) >= 1 && int64(k.n) <= int64(na)+1) { // na+1 is appended
		rest++ // the new key goes to the hash part
	}
	if rest > 0 {
		t.nodes = make([]node, nodeSize(rest))
	}
	for i := range old {
		nd := &old[i]
		if nd.v.IsNil() || nd.k.p == tInt() && int64(nd.k.n) >= 1 && int64(nd.k.n) <= int64(na) {
			continue
		}
		t.insert(nd.k, nd.v, hashValue(nd.k))
	}
	for i := range oldArr {
		if v := oldArr[i]; !v.IsNil() {
			k := Int(int64(na + i + 1))
			t.insert(k, v, hashValue(k))
		}
	}
	return len(oldArr) == 0
}

// sparse reports whether less than half of the array part, with one more slot, would hold
// values: too empty to double.
func (t *Table) sparse() bool {
	live := 0
	for i := range t.arr {
		if !t.arr[i].IsNil() {
			live++
		}
	}
	return 2*(live+1) <= len(t.arr)+1
}

// bitsLen is the number of bits needed for x: ceil(log2(x+1)).
func bitsLen(x uint64) int { return bits.Len64(x) }

// computeSizes is C Lua's computesizes: the largest power of two n such that more than
// n/2 of the slots 1..n hold an integer key.
func computeSizes(nums *[64]int, nint int) int {
	a, na, optimal := 0, 0, 0
	for i, twotoi := 0, 1; twotoi > 0 && nint > twotoi/2; i, twotoi = i+1, twotoi*2 {
		a += nums[i]
		if a > twotoi/2 {
			optimal, na = twotoi, a
		}
	}
	_ = na
	return optimal
}

// appendArr adds val at the end of the array part, then moves any following integer
// keys over from the hash part.
func (t *Table) appendArr(val Value) {
	if len(t.arr) == cap(t.arr) {
		// double, as C Lua's rehash does: append grows large slices by only a quarter, which
		// copies a growing array many more times
		arr := make([]Value, len(t.arr), max(4, 2*cap(t.arr)))
		copy(arr, t.arr)
		t.arr = arr
	}
	t.arr = append(t.arr, val)
	for len(t.nodes) > 0 {
		next := Int(int64(len(t.arr)) + 1)
		idx := t.findNode(&next, hashValue(next))
		if idx < 0 || t.nodes[idx].v.IsNil() {
			return
		}
		t.arr = append(t.arr, t.nodes[idx].v)
		t.nodes[idx].v = Value{} // leaves a deleted key behind; the next rehash drops it
	}
}

// growArray makes the array part n slots long, moving any keys 1..n from the hash part
// into it, as C Lua's luaH_resizearray does.
func (t *Table) growArray(n int) {
	if n <= len(t.arr) {
		return
	}
	old := len(t.arr)
	t.arr = append(t.arr, make([]Value, n-old)...)
	if len(t.nodes) == 0 {
		return
	}
	for i := old; i < n; i++ {
		k := Int(int64(i) + 1)
		if idx := t.findNode(&k, hashValue(k)); idx >= 0 {
			t.arr[i] = t.nodes[idx].v
			t.nodes[idx].v = Value{} // a deleted key; the next rehash drops it
		}
	}
}

// insert places a new key; the caller has made room.
func (t *Table) insert(key, val Value, h uint64) {
	mask := uint64(len(t.nodes) - 1)
	for j := h; ; j++ {
		nd := &t.nodes[j&mask]
		if nd.k.p == nil {
			nd.k, nd.v = key, val
			t.used++
			return
		}
	}
}

// rehash rebuilds the hash part for its live keys plus extra, dropping deleted keys.
func (t *Table) rehash(extra int) {
	live := 0
	for i := range t.nodes {
		if !t.nodes[i].v.IsNil() {
			live++
		}
	}
	old := t.nodes
	t.nodes = make([]node, nodeSize(live+extra))
	t.used = 0
	for i := range old {
		if nd := &old[i]; !nd.v.IsNil() {
			t.insert(nd.k, nd.v, hashValue(nd.k))
		}
	}
}

// Len returns a border of t, as C Lua's luaH_getn does: an n such that t[n] is not nil
// and t[n+1] is nil, or 0 if t[1] is nil. It does not run metamethods.
func (t *Table) Len() int {
	n := len(t.arr)
	if n > 0 && t.arr[n-1].IsNil() {
		// a border inside the array part: binary search, keeping arr[i-1] non-nil (or i = 0)
		// and arr[j-1] nil
		i, j := 0, n
		for j-i > 1 {
			m := (i + j) / 2
			if t.arr[m-1].IsNil() {
				j = m
			} else {
				i = m
			}
		}
		return i
	}
	if len(t.nodes) == 0 || t.Get(Int(int64(n)+1)).IsNil() {
		return n
	}
	// the hash part continues the sequence: double until a nil, then binary search
	i, j := n+1, n+2
	for !t.Get(Int(int64(j))).IsNil() {
		i = j
		if j > math.MaxInt64/2 {
			for !t.Get(Int(int64(i) + 1)).IsNil() { // a pathological table: linear search
				i++
			}
			return i
		}
		j *= 2
	}
	for j-i > 1 {
		m := i + (j-i)/2
		if t.Get(Int(int64(m))).IsNil() {
			j = m
		} else {
			i = m
		}
	}
	return i
}

// Next returns the key and value after key in traversal order: the array part, then the
// hash part by node index. A nil key starts the traversal; a nil result key ends it. Setting
// existing fields, also to nil, during a traversal is allowed. ok is false for a key that is
// not in the table.
func (t *Table) Next(key Value) (k, v Value, ok bool) {
	i := 0 // position to resume from: 0..len(arr)-1 array, then len(arr)+node index
	if !key.IsNil() {
		nk, valid := normKey(key)
		if !valid {
			return Value{}, Value{}, false
		}
		if nk.p == tInt() && int64(nk.n) >= 1 && int64(nk.n) <= int64(len(t.arr)) {
			i = int(nk.n)
		} else {
			idx := t.findNode(&nk, hashValue(nk))
			if idx < 0 {
				return Value{}, Value{}, false
			}
			i = len(t.arr) + idx + 1
		}
	}
	for ; i < len(t.arr); i++ {
		if !t.arr[i].IsNil() {
			return Int(int64(i) + 1), t.arr[i], true
		}
	}
	for j := i - len(t.arr); j < len(t.nodes); j++ {
		if nd := &t.nodes[j]; !nd.v.IsNil() {
			return nd.k, nd.v, true
		}
	}
	return Value{}, Value{}, true
}

// All iterates over every key and value of t, raw, in traversal order.
func (t *Table) All() iter.Seq2[Value, Value] {
	return func(yield func(Value, Value) bool) {
		k := Value{}
		for {
			nk, v, ok := t.Next(k)
			if !ok || nk.IsNil() || !yield(nk, v) {
				return
			}
			k = nk
		}
	}
}

// Items iterates over t[1], t[2], ... up to the first nil, raw.
func (t *Table) Items() iter.Seq2[int, Value] {
	return func(yield func(int, Value) bool) {
		for i := 1; ; i++ {
			v := t.Get(Int(int64(i)))
			if v.IsNil() || !yield(i, v) {
				return
			}
		}
	}
}

// Frozen reports whether t is read-only.
func (t *Table) Frozen() bool { return t.flags&tabFrozen != 0 }

// tableValue returns t as a Value.
func tableValue(t *Table) Value { return Value{p: unsafe.Pointer(t), n: kindTable << 56} }

// memSize is the bytes t's array and hash parts take.
func (t *Table) memSize() int { return cap(t.arr)*16 + len(t.nodes)*32 }
