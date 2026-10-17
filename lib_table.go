package glua

import (
	"math"
	"slices"
	"strings"
)

// The table library, after C Lua 5.4's ltablib.c. Like C Lua 5.4, it reads and writes
// through __index, __newindex and __len. Work is charged to the step budget.

func openTable(g *Table) {
	g.Set(String("table"), tableValue(newLib("table", map[string]GoFunc{
		"concat": tabConcat, "insert": tabInsert, "move": tabMove, "pack": tabPack,
		"remove": tabRemove, "sort": tabSort, "unpack": tabUnpack,
	})))
}

// setIndex does obj[key] = val with __newindex, from library code. The errors it raises
// itself, a value that cannot be indexed and a chain too long, have no position, as C Lua
// raises them inside the library function.
func (c *Call) setIndex(obj, key, val Value) error {
	for hops := 0; hops < maxIndexHops; hops++ {
		var h Value
		if obj.isObj(kindTable) {
			t := (*Table)(obj.p)
			if t.meta == nil || !t.Get(key).IsNil() {
				return c.rawSet(t, key, val)
			}
			h = t.meta.metaGet("__newindex")
			if h.IsNil() {
				return c.rawSet(t, key, val)
			}
		} else if obj.isObj(kindUser) {
			var err error
			if h, err = c.ex.newindexUser(obj, key, val); err != nil || h.IsNil() {
				return err
			}
		} else {
			h = c.ex.metamethod(obj, "__newindex")
			if h.IsNil() {
				return &Error{Value: String("attempt to index a " + typeName(obj) + " value")}
			}
		}
		if h.isObj(kindLuaFn) || h.isObj(kindGoFn) {
			_, err := c.call(h, obj, key, val)
			return err
		}
		obj = h
	}
	return &Error{Value: String("'__newindex' chain too long; possible loop")}
}

func (c *Call) rawSet(t *Table, key, val Value) error {
	if t.Frozen() {
		return c.libErrorf("attempt to modify a frozen table")
	}
	k, ok := normKey(key)
	if !ok {
		if key.IsNil() {
			return c.libErrorf("table index is nil")
		}
		return c.libErrorf("table index is NaN")
	}
	return c.ex.tableSet(t, k, val)
}

// length is #v with __len, from library code, as luaL_len: the result must be an integer.
func (c *Call) length(v Value) (int64, error) {
	if h := c.ex.metamethod(v, "__len"); !h.IsNil() {
		res, err := c.call(h, v)
		if err != nil {
			return 0, err
		}
		if len(res) > 0 {
			if n, ok := res[0].Int(); ok && res[0].p == tInt() {
				return n, nil
			}
		}
		return 0, c.libErrorf("object length is not an integer")
	}
	switch {
	case v.isObj(kindTable):
		return int64((*Table)(v.p).Len()), nil
	case v.isString():
		return int64(v.n & lenMask), nil
	}
	return 0, c.libErrorf("attempt to get length of a %s value", typeName(v))
}

// checkTab requires argument i to be a table, or to have the metamethods the operation
// needs, as ltablib's checktab does.
func (c *Call) checkTab(i int, fname string, needs ...string) error {
	v := c.Value(i)
	if v.isObj(kindTable) {
		return nil
	}
	for _, e := range needs {
		if c.ex.metamethod(v, e).IsNil() {
			return c.typeArgError(i, fname, "table")
		}
	}
	if len(needs) == 0 {
		return c.typeArgError(i, fname, "table")
	}
	return nil
}

// tick charges one step per 8 elements, as library work is charged.
func (c *Call) tickEvery(i int64) error {
	if i&7 == 0 {
		return c.ex.tick()
	}
	return nil
}

func tabConcat(c *Call) error {
	if err := c.checkTab(0, "concat", "__index", "__len"); err != nil {
		return err
	}
	t := c.Value(0)
	sep, err := c.optString(1, "concat", "")
	if err != nil {
		return err
	}
	i, err := c.optInt(2, "concat", 1)
	if err != nil {
		return err
	}
	var j int64
	if c.Value(3).IsNil() {
		if j, err = c.length(t); err != nil {
			return err
		}
	} else if j, err = c.checkInt(3, "concat"); err != nil {
		return err
	}
	var b strings.Builder
	charge := building{c: c}
	for k := i; k <= j; k++ {
		v, err := c.index(t, Int(k))
		if err != nil {
			return err
		}
		if !v.isString() && !v.isNumber() {
			return c.libErrorf("invalid value (%s) at index %d in table for 'concat'", typeName(v), k)
		}
		b.WriteString(v.String())
		if k != j {
			b.WriteString(sep)
		}
		if err := c.tickEvery(k); err != nil {
			return err
		}
		if err := charge.grew(b.Len()); err != nil {
			return err
		}
		if k == math.MaxInt64 {
			break
		}
	}
	if err := charge.done(b.Len()); err != nil {
		return err
	}
	return c.ReturnValues(String(b.String()))
}

func tabInsert(c *Call) error {
	if err := c.checkTab(0, "insert", "__index", "__newindex", "__len"); err != nil {
		return err
	}
	t := c.Value(0)
	n, err := c.length(t)
	if err != nil {
		return err
	}
	e := n + 1 // first empty element
	var pos int64
	switch c.Len() {
	case 2:
		pos = e
	case 3:
		if pos, err = c.checkInt(1, "insert"); err != nil {
			return err
		}
		if uint64(pos)-1 >= uint64(e) { // check 1 <= pos <= e
			return c.argError(2, "insert", "position out of bounds")
		}
		for i := e; i > pos; i-- { // move up elements
			v, err := c.index(t, Int(i-1))
			if err != nil {
				return err
			}
			if err := c.setIndex(t, Int(i), v); err != nil {
				return err
			}
			if err := c.tickEvery(i); err != nil {
				return err
			}
		}
	default:
		return c.libErrorf("wrong number of arguments to 'insert'")
	}
	return c.setIndex(t, Int(pos), c.Value(c.Len()-1))
}

func tabRemove(c *Call) error {
	if err := c.checkTab(0, "remove", "__index", "__newindex", "__len"); err != nil {
		return err
	}
	t := c.Value(0)
	size, err := c.length(t)
	if err != nil {
		return err
	}
	pos, err := c.optInt(1, "remove", size)
	if err != nil {
		return err
	}
	if pos != size && uint64(pos)-1 > uint64(size) { // check 1 <= pos <= size + 1
		return c.argError(2, "remove", "position out of bounds")
	}
	v, err := c.index(t, Int(pos))
	if err != nil {
		return err
	}
	for ; pos < size; pos++ {
		next, err := c.index(t, Int(pos+1))
		if err != nil {
			return err
		}
		if err := c.setIndex(t, Int(pos), next); err != nil {
			return err
		}
		if err := c.tickEvery(pos); err != nil {
			return err
		}
	}
	if err := c.setIndex(t, Int(pos), Value{}); err != nil { // remove entry t[pos]
		return err
	}
	return c.ReturnValues(v)
}

func tabMove(c *Call) error {
	if err := c.checkTab(0, "move", "__index"); err != nil {
		return err
	}
	a1 := c.Value(0)
	f, err := c.checkInt(1, "move")
	if err != nil {
		return err
	}
	e, err := c.checkInt(2, "move")
	if err != nil {
		return err
	}
	t, err := c.checkInt(3, "move")
	if err != nil {
		return err
	}
	tt := a1
	if !c.Value(4).IsNil() {
		if err := c.checkTab(4, "move", "__newindex"); err != nil {
			return err
		}
		tt = c.Value(4)
	}
	if e >= f {
		if !(f > 0 || e < math.MaxInt64+f) {
			return c.argError(3, "move", "too many elements to move")
		}
		n := e - f + 1 // number of elements to move
		if t > math.MaxInt64-n+1 {
			return c.argError(4, "move", "destination wrap around")
		}
		overlap := t > e || t <= f || (!c.Value(4).IsNil() && !rawEqual(a1, tt))
		for i := int64(0); i < n; i++ {
			j := i
			if !overlap {
				j = n - 1 - i // move backwards when the ranges overlap
			}
			v, err := c.index(a1, Int(f+j))
			if err != nil {
				return err
			}
			if err := c.setIndex(tt, Int(t+j), v); err != nil {
				return err
			}
			if err := c.tickEvery(i); err != nil {
				return err
			}
		}
	}
	return c.ReturnValues(tt)
}

func tabPack(c *Call) error {
	n := c.Len()
	if err := c.ex.charge(64 + n*16); err != nil {
		return err
	}
	t := NewTable(n, 1)
	for i := range n {
		t.arr[i] = c.Value(i)
	}
	t.Set(String("n"), Int(int64(n)))
	return c.ReturnValues(tableValue(t))
}

func tabUnpack(c *Call) error {
	t := c.Value(0)
	i, err := c.optInt(1, "unpack", 1)
	if err != nil {
		return err
	}
	var e int64
	if c.Value(2).IsNil() {
		if e, err = c.length(t); err != nil {
			return err
		}
	} else if e, err = c.checkInt(2, "unpack"); err != nil {
		return err
	}
	if i > e {
		return c.ReturnValues()
	}
	n := uint64(e) - uint64(i)
	if n >= 1<<20 { // the register stack's fixed cap
		return c.libErrorf("too many results to unpack")
	}
	c.res = slices.Grow(c.res, int(n+1)) // the results, built where ReturnValues would copy them
	// a plain table's array part, read directly: it runs no Lua as it is unpacked, so it stays so
	var arr []Value
	if t.isObj(kindTable) && (*Table)(t.p).meta == nil {
		arr = (*Table)(t.p).arr
	}
	for k := i; ; k++ {
		var v Value
		if uint64(k-1) < uint64(len(arr)) {
			v = arr[k-1]
		} else if v, err = c.index(t, Int(k)); err != nil {
			return err
		}
		c.res = append(c.res, v)
		if err := c.tickEvery(k); err != nil {
			return err
		}
		if k == e {
			break
		}
	}
	return nil
}

// table.sort: C Lua's quicksort, so that invalid order functions are detected the same way.

type sorter struct {
	c    *Call
	t    Value
	tab  *Table // t, when it is a table: get and set reach its array part directly while it is plain
	comp Value
	err  error
}

func (s *sorter) get(i int64) Value {
	if s.err != nil {
		return Value{}
	}
	// the order function may change the table, so whether it is plain is asked each time
	if t := s.tab; t != nil && t.meta == nil && uint64(i-1) < uint64(len(t.arr)) {
		return t.arr[i-1]
	}
	v, err := s.c.index(s.t, Int(i))
	if err != nil {
		s.err = err
	}
	return v
}

func (s *sorter) set(i int64, v Value) {
	if s.err != nil {
		return
	}
	if t := s.tab; t != nil && t.meta == nil && t.flags&tabFrozen == 0 && uint64(i-1) < uint64(len(t.arr)) {
		t.arr[i-1] = v // as SETTABLE's inline store does
		return
	}
	s.err = s.c.setIndex(s.t, Int(i), v)
}

// less is a < b with the order function, or the < operator. Each comparison charges a step.
func (s *sorter) less(a, b Value) bool {
	if s.err != nil {
		return false
	}
	if s.err = s.c.ex.tick(); s.err != nil {
		return false
	}
	if !s.comp.IsNil() {
		r, err := s.c.call1(s.comp, a, b)
		if err != nil {
			s.err = err
			return false
		}
		return r.Truthy()
	}
	return s.c.lessThan(a, b, &s.err)
}

// lessThan is a < b with __lt, from library code.
func (c *Call) lessThan(a, b Value, perr *error) bool {
	if (a.isNumber() && b.isNumber()) || (a.isString() && b.isString()) {
		r, _ := c.ex.lessThan(a, b)
		return r
	}
	h := c.ex.binMeta(a, b, "__lt")
	if h.IsNil() {
		// raised inside a Go function, so without a position, as C Lua raises it inside sort
		*perr = &Error{Value: String(compareMessage(a, b))}
		return false
	}
	res, err := c.call(h, a, b)
	if err != nil {
		*perr = err
		return false
	}
	return len(res) > 0 && res[0].Truthy()
}

func (s *sorter) sort(lo, up int64) {
	for lo < up && s.err == nil { // loop for tail recursion
		// sort elements lo, (lo+up)/2 and up
		a, b := s.get(lo), s.get(up)
		if s.less(b, a) {
			s.set(lo, b)
			s.set(up, a)
		}
		if up-lo == 1 {
			return
		}
		p := lo + (up-lo)/2
		a, b = s.get(p), s.get(lo)
		if s.less(a, b) {
			s.set(p, b)
			s.set(lo, a)
		} else {
			b = s.get(up)
			if s.less(b, a) {
				s.set(p, b)
				s.set(up, a)
			}
		}
		if up-lo == 2 {
			return
		}
		pv := s.get(p)
		s.set(p, s.get(up-1)) // a[p] = a[up - 1]
		s.set(up-1, pv)
		p = s.partition(lo, up, pv)
		if s.err != nil {
			return
		}
		// recurse into the smaller half, loop for the larger
		if p-lo < up-p {
			s.sort(lo, p-1)
			lo = p + 1
		} else {
			s.sort(p+1, up)
			up = p - 1
		}
	}
}

// partition is C Lua's: with the pivot at up-1, it raises "invalid order function for
// sorting" when the comparisons run off the ends of the range.
func (s *sorter) partition(lo, up int64, pv Value) int64 {
	i, j := lo, up-1
	for s.err == nil {
		for i++; s.less(s.get(i), pv); i++ {
			if i == up-1 {
				s.err = s.c.libErrorf("invalid order function for sorting")
				return 0
			}
		}
		for j--; s.less(pv, s.get(j)); j-- {
			if j < i {
				s.err = s.c.libErrorf("invalid order function for sorting")
				return 0
			}
		}
		if j < i {
			// swap pivot (a[up - 1]) with a[i]
			v := s.get(i)
			s.set(i, s.get(up-1))
			s.set(up-1, v)
			return i
		}
		vi, vj := s.get(i), s.get(j)
		s.set(i, vj)
		s.set(j, vi)
	}
	return 0
}

func tabSort(c *Call) error {
	if err := c.checkTab(0, "sort", "__index", "__newindex", "__len"); err != nil {
		return err
	}
	t := c.Value(0)
	n, err := c.length(t)
	if err != nil {
		return err
	}
	if n > 1 {
		if n >= math.MaxInt32 {
			return c.argError(1, "sort", "array too big")
		}
		comp := c.Value(1)
		if !comp.IsNil() && !comp.isObj(kindLuaFn) && !comp.isObj(kindGoFn) {
			return c.typeArgError(1, "sort", "function")
		}
		s := &sorter{c: c, t: t, comp: comp}
		if t.isObj(kindTable) {
			s.tab = (*Table)(t.p)
		}
		s.sort(1, n)
		if s.err != nil {
			return s.err
		}
	}
	return nil
}
