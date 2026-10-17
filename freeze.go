package glua

import (
	"fmt"
	"sync"
	"sync/atomic"
	"unique"
	"unsafe"
)

// Freezing makes everything reachable from a value read-only, so that any goroutine may read
// it: tables and their metatables, and the cells of captured variables. It walks with an
// explicit worklist, so depth is no limit and cycles are harmless. It first checks the whole
// graph and only then freezes, so a failure leaves nothing half frozen.

// freezer collects the objects reachable from the values given to add.
type freezer struct {
	plans  *[]*typeInfo // the Runtime's view of bound types; nil for the process-wide one
	intern bool         // give string keys the canonical pointers constants have
	seen   map[unsafe.Pointer]bool
	types  map[uint64]uint8 // the bound types checked: 1 through a live view, 2 a read-only one
	work   []freezeItem
	tables []*Table
	cells  []*cell
}

// freezeItem is a value to visit, and the path it was reached by, for messages.
type freezeItem struct {
	v    Value
	path string
}

func newFreezer() *freezer {
	return &freezer{seen: map[unsafe.Pointer]bool{}, types: map[uint64]uint8{}}
}

// add queues v, reached by path, and everything reachable from it.
func (f *freezer) add(v Value, path string) {
	if isScalar(v.p) || v.isString() || f.seen[v.p] {
		return
	}
	f.seen[v.p] = true
	f.work = append(f.work, freezeItem{v, path})
}

// walk visits the queued values. It fails on what cannot be shared: a coroutine, a library
// function with hidden state, or a Go value a script can change.
func (f *freezer) walk() error {
	for len(f.work) > 0 {
		it := f.work[len(f.work)-1]
		f.work = f.work[:len(f.work)-1]
		v := it.v
		switch v.n >> 56 {
		case kindTable:
			t := (*Table)(v.p)
			if t.Frozen() {
				continue // frozen as a whole earlier
			}
			f.tables = append(f.tables, t)
			for i, x := range t.arr {
				f.add(x, fmt.Sprintf("%s[%d]", it.path, i+1))
			}
			for _, nd := range t.nodes {
				if nd.v.IsNil() {
					continue
				}
				f.add(nd.k, it.path+" (a key)")
				f.add(nd.v, it.path+keyPath(nd.k))
			}
			if t.meta != nil {
				f.add(tableValue(t.meta), it.path+" (its metatable)")
			}
		case kindLuaFn:
			cl := (*closure)(v.p)
			for i, u := range cl.up {
				f.add(u, it.path+" (upvalue '"+upvalName(cl.p, i)+"')")
			}
			if cl.env != nil {
				f.add(tableValue(cl.env), it.path+" (its globals)")
			}
		case kindCell:
			c := v.cell()
			if !c.frozen {
				f.cells = append(f.cells, c)
			}
			f.add(c.v, it.path)
		case kindGoFn:
			if g := (*goFunc)(v.p); g.stateful {
				return fmt.Errorf("%s is a %s function with hidden state, which cannot be shared", it.path, g.displayName())
			}
		case kindThread:
			return fmt.Errorf("%s is a coroutine, which cannot be shared", it.path)
		case kindUser:
			id := v.n & typeIDMask
			if ti := f.plan(id); ti != nil && ti.stateful && !isStdFile(v) {
				return fmt.Errorf("%s is a %s, which has hidden state and cannot be shared", it.path, typeName(v))
			}
			if err := f.checkType(id, v.n&flagReadonly != 0, it.path); err != nil {
				return err
			}
		}
	}
	return nil
}

// plan returns the plan of bound type id, as the Runtime sees it.
func (f *freezer) plan(id uint64) *typeInfo {
	ts := f.plans
	if ts == nil {
		ts = types.Load()
	}
	if id < uint64(len(*ts)) {
		return (*ts)[id]
	}
	return nil
}

// checkType fails if a script can change a value of bound type id, reached by path, or a
// value its fields reach: through writable fields, unless the view is read-only, and through
// a __newindex metamethod or Mutable methods, which a read-only view reaches too. Without a
// Runtime, as for Table.Freeze, a type counts as writable or mutable if any Runtime made it
// so. Each type is checked once for each kind of view.
func (f *freezer) checkType(id uint64, readonly bool, path string) error {
	bit := uint8(1)
	if readonly {
		bit = 2
	}
	if f.types[id]&bit != 0 {
		return nil
	}
	f.types[id] |= bit
	ti := f.plan(id)
	if ti == nil {
		return nil
	}
	var changed uint32
	if f.plans == nil {
		changed = ti.changedBy.Load()
	}
	if !readonly && (ti.writable() || changed&changedWritable != 0) {
		return fmt.Errorf("%s is a %s, whose writable fields cannot be shared", path, ti.rt)
	}
	if ti.mutable || changed&changedMutable != 0 {
		return fmt.Errorf("%s is a %s, which can be changed and cannot be shared", path, ti.rt)
	}
	for i := range ti.fields {
		if err := f.checkField(&ti.fields[i], readonly, path+"."+ti.fields[i].name); err != nil {
			return err
		}
	}
	if ti.kind == planSlice || ti.kind == planMap {
		return f.checkField(&ti.elem, readonly, path+" (an element)")
	}
	return nil
}

// checkField checks the bound type a field reaches, through the view loadField gives: a
// struct, slice or map field is read-only unless the field is writable, and a pointer field
// keeps the view of the value that holds it.
func (f *freezer) checkField(fl *field, readonly bool, path string) error {
	switch fl.kind {
	case fStruct, fSlice, fMap:
		return f.checkType(fl.sub, readonly || !fl.rw, path)
	case fPtr:
		return f.checkType(fl.sub, readonly, path)
	}
	return nil
}

// freeze makes what walk collected read-only.
func (f *freezer) freeze() {
	for _, t := range f.tables {
		if f.intern {
			t.internKeys()
		}
		t.freeze()
	}
	for _, c := range f.cells {
		c.frozen = true
	}
}

// freezeValue freezes v and everything reachable from it. path names v in messages.
func freezeValue(v Value, path string) error {
	f := newFreezer()
	f.add(v, path)
	if err := f.walk(); err != nil {
		return err
	}
	f.freeze()
	return nil
}

// freeze marks t read-only and fills its cache of absent metamethods in full, so that reading
// it as a metatable never writes.
func (t *Table) freeze() {
	for event, bit := range cachedEvents {
		if t.Get(String(event)).IsNil() {
			t.flags |= bit
		}
	}
	if h := t.Get(String("__index")); h.isObj(kindTable) {
		t.index = (*Table)(h.p)
	}
	t.metaOK = t.Get(String("__mode")).IsNil() && (t.Get(String("__gc")).IsNil() || !t.Get(String("__close")).IsNil())
	t.flags |= tabFrozen
}

// Freeze makes t and everything reachable from it read-only, so that any goroutine may read
// it. It fails, freezing nothing, if t reaches a coroutine, a library function with hidden
// state, such as a gmatch iterator, or a Go value a script can change.
func (t *Table) Freeze() error {
	if err := freezeValue(tableValue(t), "table"); err != nil {
		return fmt.Errorf("glua: cannot freeze: %w", err)
	}
	return nil
}

// keyPath renders a table key as a path step: .name or [key].
func keyPath(k Value) string {
	if k.isString() && isName(k.str()) {
		return "." + k.str()
	}
	if k.isString() {
		return fmt.Sprintf("[%q]", k.str())
	}
	return "[" + k.String() + "]"
}

// upvalName returns the name of upvalue i of p, or "?".
func upvalName(p *proto, i int) string {
	if i < len(p.upnames) && p.upnames[i] != "" {
		return p.upnames[i]
	}
	return "?"
}

// displayName returns the name messages use for g.
func (g *goFunc) displayName() string {
	if g.qualname != "" {
		return g.qualname
	}
	return g.name
}

// userType returns the plan of a userdata's bound type, or nil.
func userType(v Value) *typeInfo {
	id := v.n & typeIDMask
	ts := *types.Load()
	if id < uint64(len(ts)) {
		return ts[id]
	}
	return nil
}

// writable reports whether a script may write some field of the type.
func (ti *typeInfo) writable() bool {
	for i := range ti.fields {
		if ti.fields[i].rw {
			return true
		}
	}
	return false
}

// interned keeps canonical strings alive for the keys of tables that outlive the scripts
// loaded after them: library, global, module and member names, frozen with the Runtime. The
// hot loop compares key pointers, and the compiler gives constants these canonical pointers,
// so such a key is found inline only if its pointer stays canonical. The registry is capped,
// and keys that Go code puts in tables call by call, which only need to match the constants
// of scripts already loaded, use canonKey and never enter it.
var (
	interned      sync.Map // string -> unique.Handle[string]
	internedCount atomic.Int64
)

const (
	maxInterned   = 1 << 16 // names in the registry
	maxInternedSz = 64      // longest name interned, in bytes
)

// internKey returns k with the canonical pointer, if k is a short name and the registry
// has room; otherwise k itself.
func internKey(k Value) Value {
	if !k.isString() || k.n&lenMask > maxInternedSz {
		return k
	}
	s := k.str()
	if h, ok := interned.Load(s); ok {
		return String(h.(unique.Handle[string]).Value())
	}
	if !isName(s) || internedCount.Load() >= maxInterned {
		return k
	}
	h := unique.Make(s)
	if _, loaded := interned.LoadOrStore(s, h); !loaded {
		internedCount.Add(1)
	}
	return String(h.Value())
}

// canonKey returns k with the canonical pointer of a short name, which the constants of
// loaded scripts share, for a key Go code puts in a table: Table.Set, or a Go map converted.
// Unlike internKey it keeps nothing, so a host that makes tables with endless distinct
// keys, such as IDs, leaves no names behind.
func canonKey(k Value) Value {
	if !k.isString() || k.n&lenMask > maxInternedSz {
		return k
	}
	s := k.str()
	if h, ok := interned.Load(s); ok {
		return String(h.(unique.Handle[string]).Value())
	}
	if !isName(s) {
		return k
	}
	return String(unique.Make(s).Value())
}

// internKeys gives t's string keys their canonical pointers.
func (t *Table) internKeys() {
	for i := range t.nodes {
		t.nodes[i].k = internKey(t.nodes[i].k)
	}
}
