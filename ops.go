package glua

import (
	"math"
	"strings"
	"unsafe"
)

// The driver's side of the instruction set: everything fast hands back. On entry st.pc
// points one past the primary word. A handler that finishes at once skips the instruction's
// aux word itself. One that calls a Lua metamethod leaves st.pc alone: the continuation
// frame records it, and finishOp completes the instruction when the metamethod returns.

// cell is a captured local that is assigned after its declaration. Its register, and the
// upvalues of closures that capture it, hold the cell.
type cell struct {
	v      Value
	frozen bool
}

func cellValue(c *cell) Value { return Value{p: unsafe.Pointer(c), n: kindCell << 56} }
func (v Value) cell() *cell   { return (*cell)(v.p) }

func (ex *executor) skipAux(op uint8) {
	if hasAux[op] {
		ex.st.pc++
	}
}

// reg returns a pointer to register r of the current frame. It is valid until the stack grows.
func (ex *executor) reg(r int) *Value { return &ex.stack[ex.st.base+r] }

// slowOp does the instruction at pc-1 that fast handed back.
func (ex *executor) slowOp() error {
	st := &ex.st
	i := ex.instr(st.pc - 1)
	op := uint8(i)
	a, b, c := decA(i), decB(i), decC(i)
	p := st.cl.p
	switch op {
	case opMove:
		*ex.reg(a) = *ex.reg(b)
	case opLoadK:
		*ex.reg(a) = p.k[decBx(i)]
	case opLoadKX:
		*ex.reg(a) = p.k[ex.aux()]
	case opLoadI:
		*ex.reg(a) = Int(int64(int16(decBx(i))))
	case opLoadF:
		*ex.reg(a) = Float(float64(int16(decBx(i))))
	case opLoadNil:
		clear(ex.stack[st.base+a : st.base+a+b+1])
	case opLoadFalse:
		*ex.reg(a) = Bool(false)
	case opLoadTrue:
		*ex.reg(a) = Bool(true)
	case opGetUpval:
		*ex.reg(a) = st.cl.up[b]
	case opGetUpCell:
		cl, err := ex.asCell(st.cl.up[b])
		if err != nil {
			return err
		}
		*ex.reg(a) = cl.v
	case opSetUpCell:
		cl, err := ex.asCell(st.cl.up[b])
		if err != nil {
			return err
		}
		if cl.frozen {
			return ex.errorf("attempt to assign to frozen upvalue")
		}
		cl.v = *ex.reg(a)
	case opNewCell:
		if err := ex.charge(24); err != nil {
			return err
		}
		*ex.reg(a) = cellValue(&cell{v: *ex.reg(a)})
	case opGetCell:
		cl, err := ex.asCell(*ex.reg(b))
		if err != nil {
			return err
		}
		*ex.reg(a) = cl.v
	case opSetCell:
		cl, err := ex.asCell(*ex.reg(a))
		if err != nil {
			return err
		}
		if cl.frozen {
			return ex.errorf("attempt to assign to frozen upvalue")
		}
		cl.v = *ex.reg(b)

	case opGetGlobal:
		return ex.index(op, envValue(st.cl), p.k[decBx(i)], a)
	case opSetGlobal:
		return ex.newindex(op, envValue(st.cl), p.k[decBx(i)], *ex.reg(a))
	case opGetEnv:
		*ex.reg(a) = envValue(st.cl)
	case opGetTable:
		obj, key := ex.reg(b), ex.reg(c)
		// a string key, or an integer one the loop did not find in the array part: straight
		// to the hash part
		if obj.isObj(kindTable) {
			if t := (*Table)(obj.p); key.isString() || key.p == tInt() && key.n-1 >= uint64(len(t.arr)) {
				if i := t.findNode(key, hashValue(*key)); i >= 0 {
					if v := &t.nodes[i].v; v.p != nil || t.meta == nil {
						setValue(ex.reg(a), v)
						return nil
					}
				} else if t.meta == nil {
					*ex.reg(a) = Value{}
					return nil
				}
			}
		}
		return ex.index(op, *obj, *key, a)
	case opGetIndex:
		return ex.index(op, *ex.reg(b), Int(int64(c)), a)
	case opGetField:
		if ex.constField(*ex.reg(b), c, a) {
			return nil
		}
		return ex.index(op, *ex.reg(b), p.k[c], a)
	case opSelf:
		obj := *ex.reg(b)
		*ex.reg(a + 1) = obj
		if ex.constField(obj, c, a) {
			return nil
		}
		return ex.index(op, obj, p.k[c], a)
	case opSetTable:
		if key := *ex.reg(b); (key.p == tInt() || key.isString()) && quickSet(*ex.reg(a), key, hashValue(key), *ex.reg(c), false) >= 0 {
			return nil
		}
		return ex.newindex(op, *ex.reg(a), *ex.reg(b), *ex.reg(c))
	case opSetIndex:
		return ex.newindex(op, *ex.reg(a), Int(int64(b)), *ex.reg(c))
	case opSetField:
		if ex.constSet(*ex.reg(a), b, *ex.reg(c)) {
			return nil
		}
		return ex.newindex(op, *ex.reg(a), p.k[b], *ex.reg(c))
	case opSetTableK:
		if key := *ex.reg(b); (key.p == tInt() || key.isString()) && quickSet(*ex.reg(a), key, hashValue(key), p.k[c], false) >= 0 {
			return nil
		}
		return ex.newindex(op, *ex.reg(a), *ex.reg(b), p.k[c])
	case opSetIndexK:
		return ex.newindex(op, *ex.reg(a), Int(int64(b)), p.k[c])
	case opSetFieldK:
		if ex.constSet(*ex.reg(a), b, p.k[c]) {
			return nil
		}
		return ex.newindex(op, *ex.reg(a), p.k[b], p.k[c])
	case opNewTable:
		// the sizes are hints: clamp them, so that no instruction can ask for a huge allocation
		nhash, narr := 0, min(int(ex.aux()), maxSizeHint)
		if b > 0 {
			nhash = 1 << min(b-1, 16)
		}
		if err := ex.charge(64 + narr*16 + nodeSize(nhash)*32); err != nil {
			return err
		}
		*ex.reg(a) = tableValue(newTable(narr, nhash, c == 0))
	case opSetList:
		n := b
		if n == 0 {
			var err error
			if n, err = ex.openCount(st.base + a + 1); err != nil {
				return err
			}
		}
		if !ex.reg(a).isObj(kindTable) {
			return ex.errorf("internal error: SETLIST on a %s value", typeName(*ex.reg(a)))
		}
		t := (*Table)(ex.reg(a).p)
		if t.Frozen() {
			return ex.errorf("attempt to modify a frozen table")
		}
		off := int(ex.aux())
		if off <= len(t.arr) {
			// as C Lua: the list goes in the array part, nils included. The compiler always
			// continues where the last SETLIST stopped, so this grows by at most the list.
			if err := ex.charge(max(off+n-len(t.arr), 0) * 16); err != nil {
				return err
			}
			t.growArray(off + n)
			list := ex.stack[st.base+a+1 : st.base+a+1+n]
			if !t.ptrArr && !scalars(list) {
				t.arrToPtrs()
			}
			copy(t.arr[off:off+n], list)
		} else {
			for j := 1; j <= n; j++ {
				t.set(Int(int64(off+j)), ex.stack[st.base+a+j])
			}
		}

	case opAdd, opSub, opMul, opDiv, opMod, opPow, opIDiv, opBAnd, opBOr, opBXor, opShl, opShr:
		return ex.arithOp(op, a, *ex.reg(b), *ex.reg(c), b, c)
	case opAddK, opSubK, opMulK, opDivK, opModK, opPowK, opIDivK, opBAndK, opBOrK, opBXorK, opShlK, opShrK:
		x, k := *ex.reg(b), p.k[c]
		if op == opSubK && k.p == tInt() && k.n == 0 && x.p == tFloat() {
			// C Lua computes x - 0 as x + (-0), its ADDI instruction: -0.0 - 0 is +0.0
			*ex.reg(a) = Float(math.Float64frombits(x.n) + 0)
			return nil
		}
		return ex.arithOp(op-(opAddK-opAdd), a, x, k, b, -1)
	case opUnm:
		x := *ex.reg(b)
		if n, ok := toNumber(x); ok {
			r, _ := numArith(opSub, Int(0), n)
			if n.p == tFloat() {
				r = Float(-math.Float64frombits(n.n))
			}
			*ex.reg(a) = r
			return nil
		}
		if h := ex.metamethod(x, "__unm"); !h.IsNil() {
			return ex.callMeta("__unm", h, x, x)
		}
		if x.isString() {
			return ex.errorf("attempt to unm a 'string' with a 'string'")
		}
		return ex.typeError("perform arithmetic on", x, b)
	case opBNot:
		x := *ex.reg(b)
		if n, ok := x, x.isNumber(); ok {
			if v, ok := toIntExact(n); ok {
				*ex.reg(a) = Int(^v)
				return nil
			}
			return ex.intError(b)
		}
		if h := ex.metamethod(x, "__bnot"); !h.IsNil() {
			return ex.callMeta("__bnot", h, x, x)
		}
		return ex.typeError("perform bitwise operation on", x, b)
	case opNot:
		*ex.reg(a) = Bool(!ex.reg(b).truthy())
	case opLen:
		x := *ex.reg(b)
		switch {
		case x.isString():
			*ex.reg(a) = Int(int64(x.n & lenMask))
		default:
			if h := ex.metamethod(x, "__len"); !h.IsNil() {
				return ex.callMeta("__len", h, x, x)
			}
			if x.isObj(kindTable) {
				*ex.reg(a) = Int(int64((*Table)(x.p).Len()))
				return nil
			}
			return ex.typeError("get length of", x, b)
		}
	case opConcat:
		return ex.concat(a, b)

	case opJmp:
		off := int(int16(decBx(i)))
		st.pc += off
		if off < 0 {
			return ex.tick()
		}
	case opJmpX:
		off := int(int32(ex.aux())) + 1
		st.pc += off
		if off < 0 {
			return ex.tick()
		}
		return nil
	case opEqJmp:
		x, y := *ex.reg(a), *ex.reg(b)
		if eq := rawEqual(x, y); !eq {
			if h := ex.eqMeta(x, y); !h.IsNil() {
				return ex.callMeta("__eq", h, x, y)
			}
		}
		ex.jumpAux(rawEqual(x, y) == (c != 0))
		return nil
	case opEqKJmp:
		ex.jumpAux(rawEqual(*ex.reg(a), p.k[b]) == (c != 0))
		return nil
	case opLtJmp, opLeJmp, opLtKJmp, opLeKJmp, opGtKJmp, opGeKJmp:
		x, y := *ex.reg(a), Value{}
		switch op {
		case opLtJmp, opLeJmp:
			y = *ex.reg(b)
		case opGtKJmp, opGeKJmp:
			x, y = p.k[b], x
		default:
			y = p.k[b]
		}
		less := op == opLtJmp || op == opLtKJmp || op == opGtKJmp
		if !(x.isNumber() && y.isNumber()) && !(x.isString() && y.isString()) {
			event := "__le"
			if less {
				event = "__lt"
			}
			h := ex.metamethod(x, event)
			if h.IsNil() {
				h = ex.metamethod(y, event)
			}
			if !h.IsNil() {
				return ex.callMeta(event, h, x, y)
			}
		}
		var r bool
		var err error
		if less {
			r, err = ex.lessThan(x, y)
		} else {
			r, err = ex.lessEqual(x, y)
		}
		if err != nil {
			return err
		}
		ex.jumpAux(r == (c != 0))
		return nil
	case opTestJmp:
		ex.jumpAux(ex.reg(a).truthy() == (c != 0))
		return nil
	case opTestSet:
		v := *ex.reg(b)
		if v.truthy() != (c != 0) {
			*ex.reg(a) = v
		}
		ex.jumpAux(v.truthy() == (c != 0))
		return nil

	case opForPrep:
		return ex.forPrep(i)
	case opForLoop:
		return ex.forLoop(i)
	case opTForPrep:
		if err := ex.markTBC(st.base + a + 3); err != nil {
			return err
		}
		st.pc += decBx(i)
	case opFastCall:
		ex.fastCall(i)
		return nil
	case opFastSelect:
		ex.fastSelect(i)
		return nil
	case opTForCall:
		base := st.base + a
		if done, err := ex.builtinIter(base, c); done {
			return err
		}
		if err := ex.ensure(base + 7); err != nil {
			return err
		}
		copy(ex.stack[base+4:base+7], ex.stack[base:base+3])
		return ex.callValue(base+4, 2)
	case opTForLoop:
		if r := ex.reg(a + 4); !r.IsNil() {
			*ex.reg(a + 2) = *r
			st.pc -= decBx(i)
			return ex.tick()
		}

	case opCall, opTailCall:
		fn := st.base + a
		nargs := b - 1
		if b == 0 {
			var err error
			if nargs, err = ex.openCount(fn + 1); err != nil {
				return err
			}
		}
		if op == opTailCall {
			return ex.tailCall(fn, nargs)
		}
		return ex.callValue(fn, nargs)
	case opReturn:
		n := b - 1
		if b == 0 {
			var err error
			if n, err = ex.openCount(st.base + a); err != nil {
				return err
			}
		}
		return ex.doReturn(st.base+a, n)
	case opReturn0:
		return ex.doReturn(st.base, 0)
	case opReturn1:
		return ex.doReturn(st.base+a, 1)
	case opClosure:
		np := p.protos[decBx(i)]
		if err := ex.charge(48 + 16*len(np.upvals)); err != nil {
			return err
		}
		ncl := &closure{p: np, up: make([]Value, len(np.upvals)), env: st.cl.env}
		*ex.reg(a) = luaFnValue(ncl) // stored before the captures, so a local function can capture itself
		for j, u := range np.upvals {
			if u.fromStack {
				ncl.up[j] = *ex.reg(int(u.index))
			} else {
				ncl.up[j] = st.cl.up[u.index]
			}
		}
	case opVarargPrep:
		// the frame was adjusted when it was pushed
	case opVararg:
		return ex.vararg(a, c)
	case opTBC:
		return ex.markTBC(st.base + a)
	case opClose:
		return ex.closeTo(st.base + a)

	default:
		return ex.errorf("bad opcode %d", op)
	}
	ex.skipAux(op)
	return nil
}

// openCount returns the length of the open list that starts at stack index from and ends
// at top. The instruction before must have set top; the compiler guarantees it, and this
// check keeps mutated code from reading outside the stack.
func (ex *executor) openCount(from int) (int, error) {
	if ex.top < from || ex.top > len(ex.stack) {
		return 0, ex.errorf("internal error: no open list for %s", opName(uint8(ex.instr(ex.st.pc-1))))
	}
	n := ex.top - from
	if n > 8 {
		// a list made from varargs or results can grow without bound: copying it costs a step
		// per 8 values, so that a tail call that adds arguments each time cannot run forever
		// on one step per call
		if err := ex.spend(n / 8); err != nil {
			return 0, err
		}
	}
	return n, nil
}

// maxAlloc is the fixed cap on any single allocation made for a script, checked before the
// allocation. It holds even with NoLimit: an allocation beyond it would take the process down.
const maxAlloc = 1 << 30

// maxSizeHint caps the array size a NEWTABLE preallocates; a larger table grows as it fills.
const maxSizeHint = 1 << 16

// intError reports a number that has no integer representation, named after register
// reg when it is one (reg < 0: a constant).
func (ex *executor) intError(reg int) error {
	info := ""
	if reg >= 0 {
		if vi := ex.st.cl.p.varInfo(ex.st.pc-1, reg); vi != "" {
			info = " (" + vi + ")"
		}
	}
	return ex.errorf("number%s has no integer representation", info)
}

// arithName names arithmetic operators as the string library's metamethods report them.
var arithName = map[uint8]string{
	opAdd: "add", opSub: "sub", opMul: "mul", opMod: "mod", opPow: "pow", opDiv: "div", opIDiv: "idiv",
}

// objReg returns the register that holds the table operand of the indexing instruction at
// pc-1, or -1 for GETGLOBAL and SETGLOBAL.
func (ex *executor) objReg() int {
	i := ex.instr(ex.st.pc - 1)
	switch uint8(i) {
	case opGetTable, opGetIndex, opGetField, opSelf:
		return decB(i)
	case opSetTable, opSetIndex, opSetField, opSetTableK, opSetIndexK, opSetFieldK:
		return decA(i)
	}
	return -1
}

// asCell checks that v is a cell. The compiler guarantees it, but the VM trusts only what
// the verifier checks, and the verifier cannot follow what a register holds.
func (ex *executor) asCell(v Value) (*cell, error) {
	if !v.isObj(kindCell) {
		return nil, ex.errorf("internal error: %s value where a cell belongs", typeName(v))
	}
	return v.cell(), nil
}

func envValue(cl *closure) Value {
	if cl.env == nil {
		return Value{}
	}
	return tableValue(cl.env)
}

// tick charges one step, as a back-edge does in fast.
func (ex *executor) tick() error {
	if ex.st.ticks--; ex.st.ticks < 0 {
		return ex.refill()
	}
	return nil
}

// index does R[dst] = obj[key] for the instruction op, with __index. It learns the hint of a
// GETFIELD or GETGLOBAL site.
func (ex *executor) index(op uint8, obj, key Value, dst int) error {
	st := &ex.st
	for hops := 0; hops < maxIndexHops; hops++ {
		switch {
		case obj.isObj(kindTable):
			t := (*Table)(obj.p)
			v, slot := t.getSlot(key)
			if slot >= 0 && hops <= 1 && (op == opGetField || op == opGetGlobal || op == opSelf) {
				learn(&st.cl.p.hints[ex.aux()], slot) // in the object, or one __index hop away
			}
			if !v.IsNil() || t.meta == nil {
				*ex.reg(dst) = v
				ex.skipAux(op)
				return nil
			}
			h := t.meta.metaGet("__index")
			if h.IsNil() {
				*ex.reg(dst) = Value{}
				ex.skipAux(op)
				return nil
			}
			if hops == 0 && h.isObj(kindTable) && t.meta.flags&tabFrozen == 0 {
				t.meta.index = (*Table)(h.p) // for the hot loop's inline hop
			}
			if h.isObj(kindLuaFn) || h.isObj(kindGoFn) {
				return ex.callMeta("__index", h, obj, key)
			}
			obj = h
		case obj.isString() && ex.strMeta != nil:
			h := ex.strMeta.metaGet("__index")
			if h.IsNil() {
				return ex.typeError("index", obj, ex.objReg())
			}
			if h.isObj(kindLuaFn) || h.isObj(kindGoFn) {
				return ex.callMeta("__index", h, obj, key)
			}
			obj = h
		case obj.isObj(kindUser):
			v, slot, err := ex.indexUser(obj, key)
			if err != nil {
				return err
			}
			if slot == -2 { // the type's __index
				if v.isObj(kindLuaFn) || v.isObj(kindGoFn) {
					return ex.callMeta("__index", v, obj, key)
				}
				obj = v
				continue
			}
			if slot >= 0 && (op == opGetField || op == opSelf) {
				learn(&st.cl.p.hints[ex.aux()], slot)
			}
			*ex.reg(dst) = v
			ex.skipAux(op)
			return nil
		default:
			if hops == 0 {
				return ex.typeError("index", obj, ex.objReg())
			}
			return ex.errorf("attempt to index a %s value ('__index')", typeName(obj))
		}
	}
	return ex.errorf("'__index' chain too long; possible loop")
}

// newindex does obj[key] = val for the instruction op, with __newindex.
func (ex *executor) newindex(op uint8, obj, key, val Value) error {
	for hops := 0; hops < maxIndexHops; hops++ {
		switch {
		case obj.isObj(kindTable):
			t := (*Table)(obj.p)
			if key.isString() && !val.IsNil() && t.flags&(tabFrozen|tabGuarded) == 0 && !isMetaName(&key) {
				// a string key with a value, the common store, with one hash and probe: a key the
				// table has takes the value, a deleted one too; an absent one asks the metatable
				// for __newindex, then is inserted when no resize, which tableSet charges, is due.
				// Other keys, nil values, frozen and guarded tables take the general way below
				h := hashString(key.p, int(key.n&lenMask))
				idx := t.findNode(&key, h)
				if idx < 0 || t.nodes[idx].v.IsNil() {
					if t.meta != nil {
						if hm := t.meta.metaGet("__newindex"); !hm.IsNil() {
							if hm.isObj(kindLuaFn) || hm.isObj(kindGoFn) {
								return ex.callMeta("__newindex", hm, obj, key, val)
							}
							obj = hm
							continue
						}
					}
					if idx < 0 && t.memSize() < maxAlloc/2 {
						idx = t.tryInsert(key, val, h)
					}
					if idx < 0 { // a resize is due, or the table may not grow: tableSet charges or refuses
						if err := ex.tableSet(t, key, val); err != nil {
							return err
						}
						idx = t.findNode(&key, h)
					}
				}
				if idx >= 0 {
					t.nodes[idx].v = val
					if (op == opSetField || op == opSetFieldK || op == opSetGlobal) && hops == 0 {
						learn(&ex.st.cl.p.hints[ex.aux()], idx)
					}
				}
				ex.skipAux(op)
				return nil
			}
			if t.meta != nil {
				if old := t.Get(key); old.IsNil() {
					if h := t.meta.metaGet("__newindex"); !h.IsNil() {
						if h.isObj(kindLuaFn) || h.isObj(kindGoFn) {
							return ex.callMeta("__newindex", h, obj, key, val)
						}
						obj = h
						continue
					}
				}
			}
			if t.Frozen() {
				return ex.errorf("attempt to modify a frozen table")
			}
			if t.flags&tabGuarded != 0 && ex.reservedKey(key) {
				return ex.errorf("attempt to assign to reserved name '%s'", key.str())
			}
			k, ok := normKey(key)
			if !ok {
				if key.IsNil() {
					return ex.errorf("table index is nil")
				}
				return ex.errorf("table index is NaN")
			}
			if err := ex.tableSet(t, k, val); err != nil {
				return err
			}
			if (op == opSetField || op == opSetFieldK || op == opSetGlobal) && hops == 0 && k.isString() {
				// learn where the key lives, so the next write at this site is inline
				if idx := t.findNode(&k, hashValue(k)); idx >= 0 {
					learn(&ex.st.cl.p.hints[ex.aux()], idx)
				}
			}
			ex.skipAux(op)
			return nil
		case obj.isObj(kindUser):
			h, err := ex.newindexUser(obj, key, val)
			if err != nil {
				return err
			}
			if !h.IsNil() {
				return ex.callMeta("__newindex", h, obj, key, val)
			}
			ex.skipAux(op)
			return nil
		default:
			if hops == 0 {
				return ex.typeError("index", obj, ex.objReg())
			}
			return ex.errorf("attempt to index a %s value ('__newindex')", typeName(obj))
		}
	}
	return ex.errorf("'__newindex' chain too long; possible loop")
}

// metaCallee resolves the metamethod h of event to a function to call, as luaD_call does: a
// value that is not a function is called through its __call, with itself as the first argument.
func (ex *executor) metaCallee(event string, h Value, args []Value) (Value, []Value, error) {
	for range maxIndexHops {
		if h.isObj(kindLuaFn) || h.isObj(kindGoFn) {
			return h, args, nil
		}
		tm := ex.metamethod(h, "__call")
		if tm.IsNil() {
			return Value{}, nil, ex.errorf("attempt to call a %s value (metamethod '%s')", typeName(h), event[2:])
		}
		args = append([]Value{h}, args...)
		h = tm
	}
	return Value{}, nil, ex.errorf("'__call' chain too long; possible loop")
}

// callMeta calls the metamethod h of event for the instruction at pc-1. A Lua handler runs in a
// continuation frame, and finishOp completes the instruction when it returns. A Go handler
// runs here, and the instruction is completed at once.
func (ex *executor) callMeta(event string, h Value, args ...Value) error {
	h, args, err := ex.metaCallee(event, h, args)
	if err != nil {
		return err
	}
	st := &ex.st
	fn := max(st.base+int(st.cl.p.maxstack), ex.top) // above the frame and any open list
	if err := ex.ensure(fn + 1 + len(args) + stackSlack); err != nil {
		return err
	}
	ex.stack[fn] = h
	copy(ex.stack[fn+1:], args)
	st.hi = max(st.hi, fn+1+len(args)) // so that reset clears them
	if h.isObj(kindLuaFn) {
		return ex.pushLua((*closure)(h.p), fn, len(args), frCont)
	}
	n, err := ex.callGoRawFrom((*goFunc)(h.p), fn, len(args), true)
	if err == errYield {
		return ex.yieldedAt(fn, yieldMeta)
	}
	if err != nil {
		return err
	}
	return ex.finishOp(fn, n)
}

// finishOp completes the instruction at pc-1 after its metamethod returned n results at
// stack[fn], as luaV_finishOp does in C Lua.
func (ex *executor) finishOp(fn, n int) error {
	st := &ex.st
	i := ex.instr(st.pc - 1)
	op := uint8(i)
	var r Value
	if n > 0 {
		r = ex.stack[fn]
	}
	switch op {
	case opGetField, opGetTable, opGetIndex, opGetGlobal, opSelf, opUnm, opBNot, opLen,
		opAdd, opSub, opMul, opDiv, opMod, opPow, opIDiv, opBAnd, opBOr, opBXor, opShl, opShr,
		opAddK, opSubK, opMulK, opDivK, opModK, opPowK, opIDivK, opBAndK, opBOrK, opBXorK, opShlK, opShrK:
		*ex.reg(decA(i)) = r
	case opSetField, opSetTable, opSetIndex, opSetFieldK, opSetTableK, opSetIndexK, opSetGlobal:
	case opEqJmp, opLtJmp, opLeJmp, opLtKJmp, opLeKJmp, opGtKJmp, opGeKJmp:
		ex.jumpAux(r.truthy() == (decC(i) != 0))
		return nil
	case opConcat:
		total := int(ex.cont[st.nf]) // the operands left when the metamethod was called
		*ex.reg(decA(i) + total - 2) = r
		return ex.concatRange(decA(i), total-1)
	case opClose:
		ex.top = int(ex.cont[st.nf]) // as it was before the closer ran
		st.pc--                      // close the next variable
		return nil
	default:
		return ex.errorf("cannot resume %s", opName(op))
	}
	ex.skipAux(op)
	return nil
}

// arithOp does R[dst] = x op y for numbers and numeric strings. rx and ry are the
// operands' registers, or -1 for a constant.
func (ex *executor) arithOp(op uint8, dst int, x, y Value, rx, ry int) error {
	conv := toNumber
	switch op {
	case opBAnd, opBOr, opBXor, opShl, opShr:
		conv = func(v Value) (Value, bool) { return v, v.isNumber() } // no string coercion, as in C Lua 5.4
	}
	a, ok1 := conv(x)
	b, ok2 := conv(y)
	if ok1 && ok2 {
		r, err := numArith(op, a, b)
		switch err {
		case arithDivZero:
			msg := "attempt to divide by zero"
			if op == opMod {
				msg = "attempt to perform 'n%0'"
			}
			if x.isString() || y.isString() {
				// C Lua does this arithmetic inside the string library's metamethod, a C
				// function, so the error has no position
				return &Error{Value: String(msg)}
			}
			return ex.errorf("%s", msg)
		case arithNoInt:
			reg := ry
			if _, ok := toIntExact(a); !ok {
				reg = rx
			}
			return ex.intError(reg)
		}
		*ex.reg(dst) = r
		return nil
	}
	if h := ex.binMeta(x, y, arithEvent[op]); !h.IsNil() {
		return ex.callMeta(arithEvent[op], h, x, y)
	}
	bad, reg := x, rx
	if ok1 {
		bad, reg = y, ry
	}
	switch op {
	case opBAnd, opBOr, opBXor, opShl, opShr:
		if bad.isNumber() { // it is the integer conversion that failed
			return ex.intError(reg)
		}
		if reg < 0 && bad.isString() {
			// C Lua loads a string operand of a bitwise operator into a register, and names
			// the constant it came from
			return ex.errorf("attempt to perform bitwise operation on a string value (constant '%s')", bad.str())
		}
		return ex.typeError("perform bitwise operation on", bad, reg)
	}
	if x.isString() || y.isString() {
		// in C Lua the string library's metamethods do this arithmetic, and report the failure
		return ex.errorf("attempt to %s a '%s' with a '%s'", arithName[op], typeName(x), typeName(y))
	}
	return ex.typeError("perform arithmetic on", bad, reg)
}

// lessThan compares two values exactly, as Lua's < does without metamethods.
func (ex *executor) lessThan(x, y Value) (bool, error) {
	switch {
	case x.p == tInt() && y.p == tInt():
		return int64(x.n) < int64(y.n), nil
	case x.isNumber() && y.isNumber():
		return numLess(x, y), nil
	case x.isString() && y.isString():
		return x.str() < y.str(), nil
	}
	return false, ex.compareError(x, y)
}

// lessEqual is Lua's <= without metamethods.
func (ex *executor) lessEqual(x, y Value) (bool, error) {
	switch {
	case x.p == tInt() && y.p == tInt():
		return int64(x.n) <= int64(y.n), nil
	case x.isNumber() && y.isNumber():
		if x.p == tFloat() && math.IsNaN(math.Float64frombits(x.n)) || y.p == tFloat() && math.IsNaN(math.Float64frombits(y.n)) {
			return false, nil
		}
		return !numLess(y, x), nil
	case x.isString() && y.isString():
		return x.str() <= y.str(), nil
	}
	return false, ex.compareError(x, y)
}

func (ex *executor) compareError(x, y Value) error {
	return ex.errorf("%s", compareMessage(x, y))
}

func compareMessage(x, y Value) string {
	tx, ty := typeName(x), typeName(y)
	if tx == ty {
		return "attempt to compare two " + tx + " values"
	}
	return "attempt to compare " + tx + " with " + ty
}

// concat does R[a] = R[a] .. ... .. R[a+n-1].
func (ex *executor) concat(a, n int) error { return ex.concatRange(a, n) }

// concatRange concatenates R[a], ..., R[a+total-1] into R[a] as C Lua's luaV_concat does:
// from the right, joining as long a run of strings and numbers as possible in one allocation,
// and calling __concat for a pair that is not. The frame's continuation slot records how many
// operands are left, and finishOp resumes here when the metamethod returns.
func (ex *executor) concatRange(a, total int) error {
	for total > 1 {
		regs := ex.stack[ex.st.base+a : ex.st.base+a+total]
		x, y := regs[total-2], regs[total-1]
		if !strNum(x) || !strNum(y) {
			h := ex.binMeta(x, y, "__concat")
			if h.IsNil() {
				// C Lua reports the left operand when it is bad, else the right one
				bad := total - 2
				if strNum(x) {
					bad = total - 1
				}
				return ex.typeError("concatenate", regs[bad], a+bad)
			}
			for len(ex.cont) <= ex.st.nf {
				ex.cont = append(ex.cont, 0)
			}
			ex.cont[ex.st.nf] = int32(total)
			return ex.callMeta("__concat", h, x, y)
		}
		// the longest run of strings and numbers that ends at the right
		n := 2
		for n < total && strNum(regs[total-n-1]) {
			n++
		}
		run := regs[total-n:]
		size := 0
		for _, v := range run {
			if v.isString() {
				size += int(v.n & lenMask)
			} else {
				size += len(v.String())
			}
		}
		if err := ex.produce(size); err != nil {
			return err
		}
		var sb strings.Builder
		sb.Grow(size)
		for _, v := range run {
			if v.isString() {
				sb.WriteString(v.str())
			} else {
				sb.WriteString(v.String())
			}
		}
		run[0] = String(sb.String())
		total -= n - 1
	}
	return nil
}

func strNum(v Value) bool { return v.isString() || v.isNumber() }

// arithEvent names the metamethod of each arithmetic and bitwise operator.
var arithEvent = map[uint8]string{
	opAdd: "__add", opSub: "__sub", opMul: "__mul", opDiv: "__div", opMod: "__mod", opPow: "__pow",
	opIDiv: "__idiv", opBAnd: "__band", opBOr: "__bor", opBXor: "__bxor", opShl: "__shl", opShr: "__shr",
}

// binMeta returns the metamethod event of x, or else of y, or nil, as luaT_trybinTM looks.
func (ex *executor) binMeta(x, y Value, event string) Value {
	if h := ex.metamethod(x, event); !h.IsNil() {
		return h
	}
	return ex.metamethod(y, event)
}

// eqMeta returns the __eq metamethod for comparing x and y, which are not raw equal, or nil.
// As in C Lua, only two tables or two userdata values compare through __eq.
func (ex *executor) eqMeta(x, y Value) Value {
	if (x.isObj(kindTable) && y.isObj(kindTable)) || (x.isObj(kindUser) && y.isObj(kindUser)) {
		return ex.binMeta(x, y, "__eq")
	}
	return Value{}
}

// callValue calls the value at stack[fn] with nargs arguments, for the CALL or TFORCALL at
// pc-1. A value that is not a function is called through its __call metamethod.
func (ex *executor) callValue(fn, nargs int) error {
	for hops := 0; ; hops++ {
		v := ex.stack[fn]
		switch {
		case v.isObj(kindLuaFn):
			return ex.pushLua((*closure)(v.p), fn, nargs, 0)
		case v.isObj(kindGoFn):
			return ex.callGo((*goFunc)(v.p), fn, nargs, false)
		}
		var err error
		if nargs, err = ex.callTM(fn, nargs, hops); err != nil {
			return err
		}
	}
}

// callTM puts the __call metamethod of the value at stack[fn] in its place, with the value
// inserted as the first of the nargs arguments, as C Lua's tryfuncTM does, and returns the
// new number of arguments. hops counts the metamethods already put in place for this call.
func (ex *executor) callTM(fn, nargs, hops int) (int, error) {
	v := ex.stack[fn]
	h := ex.metamethod(v, "__call")
	if h.IsNil() {
		// the message names the register's variable, also after a __call hop, as C Lua does
		if uint8(ex.instr(ex.st.pc-1)) == opTForCall {
			return 0, ex.errorf("attempt to call a %s value (for iterator 'for iterator')", typeName(v))
		}
		return 0, ex.typeError("call", v, fn-ex.st.base)
	}
	if hops >= maxIndexHops {
		return 0, ex.errorf("stack overflow")
	}
	if err := ex.ensure(fn + nargs + 2); err != nil {
		return 0, err
	}
	copy(ex.stack[fn+2:fn+2+nargs], ex.stack[fn+1:fn+1+nargs])
	ex.stack[fn+1], ex.stack[fn] = v, h
	ex.st.hi = max(ex.st.hi, fn+3+nargs)
	return nargs + 1, nil
}

// pushLua starts a call of cl at stack[fn] with nargs arguments as a new frame of the loop.
// The frame record returns to the current frame at st.pc.
func (ex *executor) pushLua(cl *closure, fn, nargs int, flags uint64) error {
	if err := ex.pushFrame(cl, fn, nargs, ex.st.pc, ex.st.base, flags); err != nil {
		return err
	}
	return ex.tick() // a call ticks
}

// pushFrame pushes a frame for cl at stack[fn], which returns to the frame at callerBase,
// resuming at pc. A vararg function's arguments stay below its frame: the function and its
// fixed parameters are copied above them, as C Lua does.
// frameRoom is the stack a frame of cl at function slot fn with nargs arguments needs, as
// pushFrame ensures it: the function, the parameters or the arguments, whichever are more,
// one slot for an adjusted vararg frame, and the slack above every frame.
func frameRoom(cl *closure, fn, nargs int) int {
	return fn + 1 + max(nargs, int(cl.p.nparams)) + 1 + stackSlack
}

func (ex *executor) pushFrame(cl *closure, fn, nargs, pc, callerBase int, flags uint64) error {
	st := &ex.st
	if err := ex.ensure(frameRoom(cl, fn, nargs)); err != nil {
		return err
	}
	if st.nf == len(ex.pframes) {
		if len(ex.pframes) >= ex.frameLimit() {
			return ex.errorf("stack overflow")
		}
		ex.pframes = append(ex.pframes, make([]uint64, min(len(ex.pframes), ex.frameLimit()-len(ex.pframes)))...)
	}
	np := int(cl.p.nparams)
	if nargs < np {
		clear(ex.stack[fn+1+nargs : fn+1+np])
		nargs = np
	}
	base := fn + 1
	if cl.p.vararg {
		nextra := nargs - np
		base = fn + 1 + nargs + 1
		ex.stack[base-1] = ex.stack[fn]
		copy(ex.stack[base:base+np], ex.stack[fn+1:fn+1+np])
		clear(ex.stack[fn+1 : fn+1+np])
		flags |= frVararg
		for len(ex.nvar) < len(ex.pframes) {
			ex.nvar = append(ex.nvar, 0)
		}
		ex.nvar[st.nf] = int32(nextra)
	}
	ex.pframes[st.nf] = uint64(uint32(pc)) | uint64(base-callerBase)<<32 | flags
	st.nf++
	st.cl, st.base, st.pc = cl, base, 0
	st.hi = max(st.hi, base+int(cl.p.maxstack))
	return nil
}

// funcSlot returns the stack index of the current frame's function as its caller placed it:
// below the arguments, for a vararg frame.
func (ex *executor) funcSlot() int {
	st := &ex.st
	fr := ex.pframes[st.nf-1]
	if fr&frVararg == 0 {
		return st.base - 1
	}
	return st.base - int(st.cl.p.nparams) - int(ex.nvar[st.nf-1]) - 2
}

// tailCall calls the value at stack[fn] in place of the current frame. A value that is not a
// function is called through its __call metamethod, still in place of the frame, as C Lua's
// luaD_pretailcall does.
func (ex *executor) tailCall(fn, nargs int) error {
	st := &ex.st
	v := ex.stack[fn]
	if !v.isObj(kindLuaFn) {
		if !v.isObj(kindGoFn) {
			return ex.tailCallTM(fn, nargs)
		}
		return ex.callGo((*goFunc)(v.p), fn, nargs, true)
	}
	dst := ex.funcSlot()
	// the stack the callee needs, checked before this frame goes, as C Lua's luaD_pretailcall
	// does: an overflow is raised by the caller, whose frame catch flags it still holds.
	// pushFrame asks the same; ensure is called only when the stack must grow, as it is hot.
	if n := dst + 1 + max(nargs, int((*closure)(v.p).p.nparams)) + 1 + stackSlack; n+stackSlack > len(ex.stack) {
		if err := ex.ensure(n); err != nil {
			return err
		}
	}
	fr := ex.pframes[st.nf-1]
	callerBase := st.base - int(fr>>32&0xffffff)
	copy(ex.stack[dst:dst+1+nargs], ex.stack[fn:fn+1+nargs])
	clear(ex.stack[dst+1+nargs : fn+1+nargs])
	st.nf--
	if err := ex.pushFrame((*closure)(v.p), dst, nargs, int(uint32(fr)), callerBase, fr&^frVararg&(0xff<<56)); err != nil {
		return err
	}
	return ex.tick()
}

// tailCallTM is tailCall for a value that is not a function: it puts the __call metamethod in
// its place, and that one's in turn, until a function, then calls that in place of the frame.
func (ex *executor) tailCallTM(fn, nargs int) error {
	for hops := 0; ; hops++ {
		var err error
		if nargs, err = ex.callTM(fn, nargs, hops); err != nil {
			return err
		}
		if v := ex.stack[fn]; v.isObj(kindLuaFn) || v.isObj(kindGoFn) {
			return ex.tailCall(fn, nargs)
		}
	}
}

// doReturn returns n results starting at stack[first] from the current frame.
func (ex *executor) doReturn(first, n int) error {
	fn := ex.st.base - 1
	if err := ex.ensure(fn + n); err != nil {
		return err
	}
	copy(ex.stack[fn:fn+n], ex.stack[first:first+n])
	ex.st.nf--
	done, err := ex.frameReturned(fn, n)
	if err != nil {
		return err
	}
	if done {
		return errDone
	}
	return nil
}

// frameReturned pops the frame whose n results start at stack[fn], its function slot, and
// returns to whoever started it. done reports that the goEntry frame of this run returned.
func (ex *executor) frameReturned(fn, n int) (done bool, err error) {
	st := &ex.st
	fr := ex.pframes[st.nf] // already popped
	if fr&frVararg != 0 {
		real := st.base - int(st.cl.p.nparams) - int(ex.nvar[st.nf]) - 2
		copy(ex.stack[real:real+n], ex.stack[fn:fn+n])
		fn = real
	}
	if fr&frGoEntry != 0 {
		ex.top = fn + n
		return true, nil
	}
	handlerFor := int(-1)
	if fr&frErrHandler != 0 {
		handlerFor = int(ex.cont[st.nf])
	}
	st.base -= int(fr >> 32 & 0xffffff)
	st.cl = (*closure)(ex.stack[st.base-1].p)
	st.pc = int(uint32(fr))
	switch {
	case handlerFor >= 0: // an xpcall handler returned: unwind to its xpcall with the result
		ex.nny--
		var r Value
		if n > 0 {
			r = ex.stack[fn]
		}
		return false, ex.unwindFrom(handlerFor, r)
	case fr&frCont != 0:
		return false, ex.finishOp(fn, n)
	case fr&frCatch != 0: // a protected call returned: true, then its results
		fn--
		ex.stack[fn] = Bool(true)
		n++
	}
	ex.adjustResults(ex.instr(st.pc-1), fn, n)
	return false, nil
}

// adjustResults pads or drops the n results at stack[fn] to what the CALL or TFORCALL i expects.
func (ex *executor) adjustResults(i uint32, fn, n int) {
	want := decC(i) - 1
	if want < 0 {
		ex.top = fn + n // open: the next instruction consumes up to top
		return
	}
	if n < want {
		clear(ex.stack[fn+n : fn+want])
	}
}

// vararg copies the current frame's extra arguments to R[a], ...: c-1 of them, or all for c=0.
func (ex *executor) vararg(a, c int) error {
	st := &ex.st
	nextra := 0
	if fr := ex.pframes[st.nf-1]; fr&frVararg != 0 {
		nextra = int(ex.nvar[st.nf-1])
	}
	from := st.base - 1 - nextra
	n := c - 1
	if c == 0 {
		n = nextra
		if err := ex.spend(n / 8); err != nil {
			return err
		}
		if err := ex.ensure(st.base + a + n); err != nil {
			return err
		}
		from = st.base - 1 - nextra
		ex.top = st.base + a + n
		st.hi = max(st.hi, ex.top)
	}
	dst := ex.stack[st.base+a : st.base+a+n]
	m := copy(dst, ex.stack[from:from+min(n, nextra)])
	clear(dst[m:])
	return nil
}

// markTBC registers the to-be-closed variable at stack index r. Nil and false are ignored.
func (ex *executor) markTBC(r int) error {
	v := ex.stack[r]
	if !v.truthy() {
		return nil
	}
	if ex.metamethod(v, "__close").IsNil() {
		p, reg := ex.st.cl.p, r-ex.st.base
		name := p.localName(reg, ex.st.pc)
		if name == "" {
			name = "?"
		}
		return ex.errorf("variable '%s' got a non-closable value", name)
	}
	ex.tbc = append(ex.tbc, r)
	return nil
}

// closeTo calls the __close metamethod of the most recent to-be-closed variable at stack
// index level and above, if there is one. The handler runs in a continuation frame that
// comes back to the same CLOSE instruction, which then closes the next one.
func (ex *executor) closeTo(level int) error {
	if len(ex.tbc) > 0 && ex.tbc[len(ex.tbc)-1] >= level {
		r := ex.tbc[len(ex.tbc)-1]
		ex.tbc = ex.tbc[:len(ex.tbc)-1]
		v := ex.stack[r]
		h, args, err := ex.metaCallee("__close", ex.metamethod(v, "__close"), []Value{v, {}})
		if err != nil {
			return err
		}
		if !h.isObj(kindLuaFn) {
			// a Go closer runs from the trampoline, so that it can yield like a Lua one
			args = append([]Value{h}, args...)
			h = luaFnValue(trampoline)
		}
		for len(ex.cont) <= ex.st.nf {
			ex.cont = append(ex.cont, 0)
		}
		ex.cont[ex.st.nf] = int32(ex.top) // the end of a RETURN's open results, for after the call
		return ex.callMeta("__close", h, args...)
	}
	return nil
}

// metamethod returns the metamethod event of v, or nil.
func (ex *executor) metamethod(v Value, event string) Value {
	if mt := ex.metatable(v); mt != nil {
		return mt.metaGet(event)
	}
	return Value{}
}

// metatable returns the metatable of v: a table's own, or the one all strings share.
func (ex *executor) metatable(v Value) *Table {
	switch {
	case v.isObj(kindTable):
		return (*Table)(v.p).meta
	case v.isString():
		return ex.strMeta
	case v.isObj(kindUser):
		if ti := ex.plan(v); ti != nil {
			return ti.meta
		}
	}
	return nil
}

// forPrep prepares a loop that fast did not: float values, a float limit, numeric strings,
// or a step that is not positive. It follows C Lua's forprep, checks in the same order.
func (ex *executor) forPrep(i uint32) error {
	st := &ex.st
	a := st.base + decA(i)
	r := ex.stack[a : a+4]
	init, limit, step := r[0], r[1], r[2]
	skip := func() { st.pc += decBx(i) }
	if init.p == tInt() && step.p == tInt() {
		s := int64(step.n)
		if s == 0 {
			return ex.errorf("'for' step is zero")
		}
		lim, ok, isNum := forLimit(limit, s)
		if !isNum {
			return ex.errorf("bad 'for' limit (number expected, got %s)", typeName(limit))
		}
		if !ok {
			skip()
			return nil
		}
		ini := int64(init.n)
		if (s > 0 && ini > lim) || (s < 0 && ini < lim) {
			skip()
			return nil
		}
		var count uint64
		if s > 0 {
			count = (uint64(lim) - uint64(ini)) / uint64(s)
		} else {
			count = (uint64(ini) - uint64(lim)) / (uint64(-(s + 1)) + 1)
		}
		r[1] = Value{p: tInt(), n: count}
		r[3] = init
		return nil
	}
	// a float loop: every value becomes a float; strings are converted
	fl, ok := forFloat(limit)
	if !ok {
		return ex.errorf("bad 'for' limit (number expected, got %s)", typeName(limit))
	}
	fs, ok := forFloat(step)
	if !ok {
		return ex.errorf("bad 'for' step (number expected, got %s)", typeName(step))
	}
	fi, ok := forFloat(init)
	if !ok {
		return ex.errorf("bad 'for' initial value (number expected, got %s)", typeName(init))
	}
	if fs == 0 {
		return ex.errorf("'for' step is zero")
	}
	if (fs > 0 && fl < fi) || (fs < 0 && fi < fl) {
		skip()
		return nil
	}
	r[0], r[1], r[2], r[3] = Float(fi), Float(fl), Float(fs), Float(fi)
	return nil
}

// forFloat converts a loop value to a float, accepting numeric strings.
func forFloat(v Value) (float64, bool) {
	if n, ok := toNumber(v); ok {
		return n.Float()
	}
	return 0, false
}

// forLimit converts a loop limit to an integer for an integer loop with step s. ok is false
// when the loop cannot run at all; isNum is false when the limit is not a number.
func forLimit(limit Value, s int64) (lim int64, ok, isNum bool) {
	limit, isNum = toNumber(limit)
	if !isNum {
		return 0, false, false
	}
	if limit.p == tInt() {
		return int64(limit.n), true, true
	}
	f := math.Float64frombits(limit.n)
	if f != f {
		return 0, false, true
	}
	if s > 0 {
		f = math.Floor(f)
		if f >= 0x1p63 {
			return math.MaxInt64, true, true
		}
		if f < -0x1p63 {
			return 0, false, true
		}
	} else {
		f = math.Ceil(f)
		if f < -0x1p63 {
			return math.MinInt64, true, true
		}
		if f >= 0x1p63 {
			return 0, false, true
		}
	}
	return int64(f), true, true
}

// forLoop steps a float loop.
func (ex *executor) forLoop(i uint32) error {
	st := &ex.st
	a := st.base + decA(i)
	r := ex.stack[a : a+4]
	if r[0].p != tFloat() || r[1].p != tFloat() || r[2].p != tFloat() {
		return ex.errorf("internal error: FORLOOP without FORPREP")
	}
	idx, limit, step := math.Float64frombits(r[0].n), math.Float64frombits(r[1].n), math.Float64frombits(r[2].n)
	idx += step
	if (step > 0 && idx <= limit) || (step < 0 && limit <= idx) {
		r[0], r[3] = Float(idx), Float(idx)
		st.pc -= decBx(i)
		if st.ticks--; st.ticks < 0 {
			return ex.refill()
		}
	}
	return nil
}

// numLess is x < y for two numbers, exact for every mix of integers and floats.
func numLess(x, y Value) bool {
	if x.p == tFloat() && y.p == tFloat() {
		return math.Float64frombits(x.n) < math.Float64frombits(y.n)
	}
	if x.p == tInt() {
		i, f := int64(x.n), math.Float64frombits(y.n)
		if f != f {
			return false
		}
		if f >= 0x1p63 {
			return true
		}
		if f < -0x1p63 {
			return false
		}
		c := math.Ceil(f) // i < f  <=>  i < ceil(f), for f in range
		return i < int64(c)
	}
	f, i := math.Float64frombits(x.n), int64(y.n)
	if f != f {
		return false
	}
	if f >= 0x1p63 {
		return false
	}
	if f < -0x1p63 {
		return true
	}
	return int64(math.Floor(f)) < i // f < i  <=>  floor(f) < i
}

// typeName is the Lua type name of v, as error messages use it: "number" for both number
// kinds, and a table's __name when its metatable has a string there, as luaT_objtypename does.
func typeName(v Value) string {
	var mt *Table
	switch {
	case v.isObj(kindTable):
		mt = (*Table)(v.p).meta
	case v.isObj(kindUser):
		if ti := userType(v); ti != nil {
			mt = ti.meta
		}
	}
	if mt != nil {
		if n := mt.Get(String("__name")); n.isString() {
			return n.str()
		}
	}
	switch k := v.Kind(); k {
	case KindInt, KindFloat:
		return "number"
	default:
		return k.String()
	}
}

// reservedKey reports whether key is a name the host or the libraries define, which a
// script cannot assign in its environment.
func (ex *executor) reservedKey(key Value) bool {
	return ex.rt != nil && key.isString() && ex.rt.reserved[key.str()]
}

// builtinIter runs a step of a generic for over next, as pairs gives it, or over ipairs's
// iterator, without a Go call: the iterator, state and control are at stack[base:], and
// the c results go to stack[base+4:]. It reports whether it did the step.
func (ex *executor) builtinIter(base, c int) (bool, error) {
	f, s, ctl := ex.stack[base], ex.stack[base+1], ex.stack[base+2]
	if !s.isObj(kindTable) || c > stackSlack-4 {
		return false, nil
	}
	t := (*Table)(s.p)
	var k, v Value
	switch {
	case f.p == unsafe.Pointer(nextG) && f.n == kindGoFn<<56:
		var ok bool
		if k, v, ex.nextAt, ok = t.next(ctl, ex.nextAt); !ok {
			return false, nil // the general path raises the error
		}
	case f.p == unsafe.Pointer(ipairsAuxG) && f.n == kindGoFn<<56 && t.meta == nil && ctl.p == tInt():
		i := int64(ctl.n) + 1
		if uint64(i-1) < uint64(len(t.arr)) {
			v = t.arr[i-1]
		} else {
			v = t.Get(Int(i))
		}
		if !v.IsNil() {
			k = Int(i)
		}
	default:
		return false, nil
	}
	// stored one by one: clear on a slice of Values is a runtime call with a bulk write barrier
	r := ex.stack[base+4 : base+4+c]
	r[0] = k
	if c > 1 {
		r[1] = v
		for j := 2; j < c; j++ {
			r[j] = Value{}
		}
	}
	ex.st.hi = max(ex.st.hi, base+4+c)
	return true, ex.tick() // a call ticks
}

// constSet does obj[K[kc]] = val for a SETFIELD the loop could not do inline, such as one
// that adds a field to a table just built, with quickSet and the key's hash computed at
// compile time, and records where the key is for the site.
func (ex *executor) constSet(obj Value, kc int, val Value) bool {
	p := ex.st.cl.p
	idx := quickSet(obj, p.k[kc], p.khash[kc], val, true) // a constant has its canonical pointer
	if idx < 0 {
		return false
	}
	learn(&p.hints[ex.aux()], idx)
	ex.st.pc++ // the aux word
	return true
}

// quickSet does obj[key] = val in the hash part, key hashing to h, when obj is a table with
// no metatable, the key is a string not starting with "__" or an integer that does not
// belong in the array part, and the write needs no resize. It returns the key's node index,
// or -1 when newindex must do the write. canonical says that a string key has its canonical
// pointer already, as a constant has; another new key is given it as it is added.
func quickSet(obj, key Value, h uint64, val Value, canonical bool) int {
	if !obj.isObj(kindTable) || val.IsNil() {
		return -1
	}
	t := (*Table)(obj.p)
	if t.meta != nil || t.flags&(tabFrozen|tabGuarded) != 0 || len(t.nodes) == 0 {
		return -1
	}
	switch {
	case key.isString():
		if isMetaName(&key) {
			return -1 // a key starting with "__" clears the table's caches in set
		}
	case key.p == tInt():
		if i := int64(key.n) - 1; uint64(i) <= uint64(len(t.arr)) {
			return -1 // in the array part, or appended to it
		}
	default:
		return -1
	}
	idx := t.findNode(&key, h)
	if idx >= 0 {
		t.nodes[idx].v = val
		return idx
	}
	if t.full() || t.memSize() >= maxAlloc/2 {
		return -1 // a resize, which newindex charges for
	}
	if canonical {
		return t.insert(key, val, h)
	}
	return t.insertNew(key, val, h)
}

// constField does R[dst] = obj[K[kc]] for GETFIELD and SELF, when obj is a table and the
// key is in it or one cached __index hop away, or obj is a string and the key is in the
// string library, with the key's compile-time hash. It learns the site's hint and reports
// whether it was done; the general index does the rest.
func (ex *executor) constField(obj Value, kc, dst int) bool {
	var t *Table
	hops := 0
	switch {
	case obj.isObj(kindTable):
		t = (*Table)(obj.p)
	case obj.isString() && ex.strIdx != nil:
		t, hops = ex.strIdx, 1 // already one hop, through the string metatable
	default:
		return false
	}
	p := ex.st.cl.p
	key, h := p.k[kc], p.khash[kc]
	for ; hops < 2; hops++ {
		if idx := t.findNode(&key, h); idx >= 0 && !t.nodes[idx].v.IsNil() {
			learn(&p.hints[ex.aux()], idx)
			*ex.reg(dst) = t.nodes[idx].v
			ex.st.pc++ // the aux word
			return true
		}
		if t.meta == nil {
			if hops > 0 {
				return false
			}
			*ex.reg(dst) = Value{}
			ex.st.pc++
			return true
		}
		if t = t.meta.index; t == nil {
			return false // not cached yet, or not a table: the general index
		}
	}
	return false
}
