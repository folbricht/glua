package glua

import (
	"math"
	"math/bits"
	"sync/atomic"
	"unsafe"
)

//go:generate go run ./internal/cmd/genloop

// The accessors below read through raw pointers: the verifier guarantees the indices. The
// checked loop, generated from this file, uses the bounds-checked versions in checked.go.

// kAt returns constant i of the constant array at k.
func kAt(k unsafe.Pointer, i uint32) *Value { return (*Value)(unsafe.Add(k, uintptr(i)*16)) }

// hintAt returns the hint word of site i of p.
func hintAt(p *proto, i uint32) *uint32 {
	return (*uint32)(unsafe.Add(unsafe.Pointer(unsafe.SliceData(p.hints)), uintptr(i)*4))
}

// upAt returns upvalue i of cl.
func upAt(cl *closure, i uint8) *Value {
	return (*Value)(unsafe.Add(unsafe.Pointer(unsafe.SliceData(cl.up)), uintptr(i)*16))
}

// khashAt returns the hash of constant i of p.
func khashAt(p *proto, i uint32) uint64 {
	return *(*uint64)(unsafe.Add(unsafe.Pointer(unsafe.SliceData(p.khash)), uintptr(i)*8))
}

// strEqBytes reports whether the strings x and y, both of n bytes, have the same bytes. The
// caller has checked that both are strings of that length; a key a script builds at run
// time, by capture, concatenation or sub, never shares a constant's pointer, so equal keys
// come behind different pointers. A byte loop is the only form the inliner accepts into
// fast; word compares cost more than its budget.
func strEqBytes(x, y unsafe.Pointer, n uintptr) bool {
	for j := range n {
		if *(*byte)(unsafe.Add(x, j)) != *(*byte)(unsafe.Add(y, j)) {
			return false
		}
	}
	return true
}

// wholeIndex returns the array index of the float key f, given n = int64(f), when f has a
// whole value that is an integer: the key it normalises to, less one, as normKey gives it. A
// float out of range converts to an implementation-defined integer, and every integer
// converts back into [-2^63, 2^63], so the round trip can wrongly match only at 2^63: arm64
// saturates to the maximum, which rounds to it. The caller converts, so that the helper fits
// the inliner's budget for a big function. Returning the index whatever the test gives, or
// testing in the caller, costs GETTABLE a stack reload on amd64.
func wholeIndex(f float64, n int64) (uint64, bool) {
	if float64(n) != f || f >= 0x1p63 {
		return 0, false
	}
	return uint64(n) - 1, true
}

// isNum reports whether v is an integer or a float. Small enough to inline into fast.
func isNum(v *Value) bool {
	return v.p == unsafe.Pointer(&tags.integer) || v.p == unsafe.Pointer(&tags.float)
}

// toFloat converts a number to a float. Small enough to inline into fast.
func toFloat(v *Value) float64 {
	if v.p == unsafe.Pointer(&tags.integer) {
		return float64(int64(v.n))
	}
	return math.Float64frombits(v.n)
}

// fast is the hot loop. It makes no Go calls, so the register allocator keeps its state in
// machine registers; the only calls in its code are write barriers, bounds-check panics and
// morestack, which a CI gate checks. Anything rare or allocating leaves through an exit and
// is done by drive. Between runs only indices are kept, never addresses.
//
// One exit convention: pc always points one word past the primary instruction word, so the
// driver can re-decode the instruction at pc-1. It skips auxiliary words itself.
//
//go:noinline
func (ex *executor) fast() exit {
	cl := ex.st.cl
	//gen:fast
	stack0 := unsafe.Pointer(unsafe.SliceData(ex.stack))
	regs := (*[256]Value)(unsafe.Add(stack0, ex.st.base*16))
	k := unsafe.Pointer(unsafe.SliceData(cl.p.k))
	pc := unsafe.Add(unsafe.Pointer(unsafe.SliceData(cl.p.code)), ex.st.pc*4)
	ex.st.limitAddr = uintptr(stack0) + uintptr(len(ex.stack)-stackSlack)*16 // a frame base at or above it cannot fit a [256]Value view
	ex.st.hiAddr = uintptr(stack0) + uintptr(ex.st.hi)*16
	//gen:checked
	//	base := ex.st.base
	//	regs := (*[256]Value)(ex.stack[base : base+256])
	//	k := cl.p.k
	//	code := cl.p.code
	//	pc := ex.st.pc
	//gen:end
	var e exit

dispatch:
	for {
		i := *(*uint32)(pc)
		pc = unsafe.Add(pc, 4)
		switch uint8(i) { // a jump table, after one range check
		case opMove:
			setValue(&regs[uint8(i>>8)], &regs[uint8(i>>16)])

		case opLoadK:
			setValue(&regs[uint8(i>>8)], kAt(k, i>>16))

		case opLoadI:
			setInt(&regs[uint8(i>>8)], uint64(int64(int16(i>>16))))

		case opLoadNil:
			a, b := uint8(i>>8), uint8(i>>16)
			for j := uint8(0); ; j++ { // an index loop: a range loop would become a memclr call
				regs[a+j] = Value{}
				if j == b {
					break
				}
			}

		case opVarargPrep: // the frame was adjusted when the call pushed it

		case opLoadFalse:
			setBool(&regs[uint8(i>>8)], 0)

		case opLoadTrue:
			setBool(&regs[uint8(i>>8)], 1)

		case opGetUpval:
			setValue(&regs[uint8(i>>8)], upAt(cl, uint8(i>>16)))

		case opGetField: // R[A] = R[B][K[C]]; the aux word is the site number
			obj, key := &regs[uint8(i>>16)], kAt(k, i>>24)
			hint := atomic.LoadUint32(hintAt(cl.p, *(*uint32)(pc)))
			slot := hint & hintSlotMask
			if obj.n == kindTable<<56 && !isScalar(obj.p) {
				t := (*Table)(obj.p)
				if int(slot) < len(t.nodes) {
					// a hit needs the key, and a value or no metatable: a deleted key must still consult __index
					if nd := &t.nodes[slot]; same(&nd.k, key) && (nd.v.p != nil || t.meta == nil) {
						setValue(&regs[uint8(i>>8)], &nd.v)
						pc = unsafe.Add(pc, 4)
						continue
					}
				}
				if hint == megamorphic && len(t.nodes) > 0 {
					// the site has given up on its hint: probe inline with the hash computed at compile time
					h, mask := khashAt(cl.p, i>>24), uint64(len(t.nodes)-1)
					for j := uint64(0); j < 8; j++ {
						nd := &t.nodes[(h+j)&mask]
						if same(&nd.k, key) {
							if nd.v.p == nil && t.meta != nil {
								break
							}
							setValue(&regs[uint8(i>>8)], &nd.v)
							pc = unsafe.Add(pc, 4)
							continue dispatch
						}
						if nd.k.p == nil || nd.k.n == key.n {
							break // absent, or an equal-length string behind another pointer: the driver decides
						}
					}
				}
			} else if obj.n>>56 == kindUser && !isScalar(obj.p) { // both halves: an integer can carry these bits
				ts := *ex.types
				// the type ID: below 2^32, so no 48-bit mask constant ties up a register. A type
				// bound during this entry is not in ts yet: the driver reloads the plans
				if id := uint32(obj.n); int(id) < len(ts) && int(slot) < len(ts[id].fields) && same(&ts[id].fields[slot].key, key) {
					ti := ts[id]
					fd, d := &ti.fields[slot], &regs[uint8(i>>8)]
					p := unsafe.Add(obj.p, fd.off)
					switch fd.kind {
					case fInt64:
						setInt(d, uint64(*(*int64)(p)))
					case fInt:
						setInt(d, uint64(*(*int)(p)))
					case fFloat64:
						setFloat(d, *(*float64)(p))
					case fBool:
						setBool(d, uint64(*(*uint8)(p)))
					case fString:
						if s := (*[2]uintptr)(p); s[1] == 0 {
							*d = Value{p: unsafe.Pointer(&emptyStr[0]), n: kindString << 56}
						} else {
							*d = Value{p: *(*unsafe.Pointer)(p), n: kindString<<56 | uint64(s[1])}
						}
					default:
						e = exSlowOp // hints are learnt only for the inline kinds; this cannot happen
						break dispatch
					}
					pc = unsafe.Add(pc, 4)
					continue
				}
			}
			e = exSlowOp // pc still points at the aux word, one past the primary word
			break dispatch

		case opAdd, opAddK:
			x, y := &regs[uint8(i>>16)], &regs[uint8(i>>24)]
			if uint8(i) == opAddK {
				y = kAt(k, i>>24)
			}
			d := &regs[uint8(i>>8)]
			if x.p == tInt() && y.p == tInt() {
				setInt(d, x.n+y.n)
			} else if x.p == tFloat() && y.p == tFloat() {
				setFloat(d, math.Float64frombits(x.n)+math.Float64frombits(y.n))
			} else if isNum(x) && isNum(y) {
				setFloat(d, toFloat(x)+toFloat(y))
			} else {
				e = exSlowOp // strings and metamethods
				break dispatch
			}

		case opSub, opSubK:
			x, y := &regs[uint8(i>>16)], &regs[uint8(i>>24)]
			if uint8(i) == opSubK {
				y = kAt(k, i>>24)
			}
			d := &regs[uint8(i>>8)]
			if x.p == tInt() && y.p == tInt() {
				setInt(d, x.n-y.n)
			} else if x.p == tFloat() && y.p == tFloat() {
				setFloat(d, math.Float64frombits(x.n)-math.Float64frombits(y.n))
			} else if isNum(x) && isNum(y) {
				r := toFloat(x) - toFloat(y)
				if y.n == 0 && uint8(i) == opSubK {
					r = toFloat(x) + 0 // as C Lua's x + (-0): -0.0 - 0 is +0.0
				}
				setFloat(d, r)
			} else {
				e = exSlowOp
				break dispatch
			}

		case opMul, opMulK:
			x, y := &regs[uint8(i>>16)], &regs[uint8(i>>24)]
			if uint8(i) == opMulK {
				y = kAt(k, i>>24)
			}
			d := &regs[uint8(i>>8)]
			if x.p == tInt() && y.p == tInt() {
				setInt(d, x.n*y.n)
			} else if x.p == tFloat() && y.p == tFloat() {
				setFloat(d, math.Float64frombits(x.n)*math.Float64frombits(y.n))
			} else if isNum(x) && isNum(y) {
				setFloat(d, toFloat(x)*toFloat(y))
			} else {
				e = exSlowOp
				break dispatch
			}

		case opJmp:
			off := int(int16(i >> 16))
			pc = unsafe.Add(pc, off*4)
			if off < 0 {
				if ex.st.ticks--; ex.st.ticks < 0 { // every back-edge ticks
					e = exTick
					break dispatch
				}
			}

		case opFastCall: // a built-in; the aux word is its id, and the CALL it stands for follows
			if f := &regs[uint8(i>>8)]; f.n == kindGoFn<<56 && !isScalar(f.p) && uint32((*goFunc)(f.p).fast) == *(*uint32)(pc) {
				e = exSlowOp // the driver does it, or falls through to the CALL
				break dispatch
			}
			pc = unsafe.Add(pc, 4) // not the built-in: the CALL

		case opFastSelect: // select(R[A+1], ...); the VARARG and CALL it stands for follow
			if f := &regs[uint8(i>>8)]; f.n == kindGoFn<<56 && !isScalar(f.p) && (*goFunc)(f.p).fast == fastSelect {
				e = exSlowOp // the driver does it, or falls through to the VARARG
				break dispatch
			}

		case opLen: // R[A] = #R[B], for a string, or a table whose length its array part shows
			x := &regs[uint8(i>>16)]
			if x.n>>56 == kindString && !isScalar(x.p) {
				setInt(&regs[uint8(i>>8)], x.n&lenMask)
				continue
			}
			if x.n == kindTable<<56 && !isScalar(x.p) {
				t := (*Table)(x.p)
				if n := len(t.arr); t.meta == nil && len(t.nodes) == 0 && (n == 0 || t.arr[n-1].p != nil) {
					setInt(&regs[uint8(i>>8)], uint64(n))
					continue
				}
			}
			e = exSlowOp
			break dispatch

		case opJmpX: // pc += int32(aux), counting from the word after the aux word
			off := int(int32(*(*uint32)(pc))) + 1
			pc = unsafe.Add(pc, off*4)
			if off < 0 {
				if ex.st.ticks--; ex.st.ticks < 0 { // every back-edge ticks
					e = exTick
					break dispatch
				}
			}

		case opLtJmp, opLtKJmp: // test R[A] < R[B] (or K[B]); fall through when it equals C, else jump by the aux word
			x, y := &regs[uint8(i>>8)], &regs[uint8(i>>16)]
			if uint8(i) == opLtKJmp {
				y = kAt(k, uint32(uint8(i>>16)))
			}
			var lt bool
			if x.p == tInt() && y.p == tInt() {
				lt = int64(x.n) < int64(y.n)
			} else if x.p == tFloat() && y.p == tFloat() {
				lt = math.Float64frombits(x.n) < math.Float64frombits(y.n)
			} else {
				e = exSlowOp // mixed numbers compare exactly in the driver; strings and metamethods too
				break dispatch
			}
			if lt == (i>>24 != 0) { // C is the polarity: fall through when the test equals it
				pc = unsafe.Add(pc, 4)
			} else {
				pc = unsafe.Add(pc, (int(int32(*(*uint32)(pc)))+1)*4)
			}

		case opEqKJmp: // test R[A] == K[B]; fall through when it equals C, else jump by the aux word
			x, y := &regs[uint8(i>>8)], kAt(k, uint32(uint8(i>>16)))
			var eq bool
			switch {
			case same(x, y):
				eq = x.p != tFloat() || x.n<<1 <= 0x7ff<<53 // the same bits are equal, unless they are a NaN
			case isScalar(x.p):
				if x.p == tFloat() && y.p == tFloat() {
					eq = math.Float64frombits(x.n) == math.Float64frombits(y.n) // 0.0 == -0.0
				} else if x.p != y.p && (x.p == tInt() || x.p == tFloat()) && (y.p == tInt() || y.p == tFloat()) {
					e = exSlowOp // 1 == 1.0: an exact compare of an integer with a float, in the driver
					break dispatch
				} // otherwise: two different integers or booleans, or different kinds: not equal
			case x.n != y.n || x.n>>56 != kindString:
				// different kinds, lengths or objects. Tables and userdata with __eq are not constants.
			case x.n&lenMask <= 32: // equal length behind different pointers: compare inline
				eq = true
				for j := uintptr(0); j < uintptr(x.n&lenMask); j++ {
					if *(*byte)(unsafe.Add(x.p, j)) != *(*byte)(unsafe.Add(y.p, j)) {
						eq = false
						break
					}
				}
			default:
				e = exSlowOp // long strings: memequal is a call
				break dispatch
			}
			if eq == (i>>24 != 0) {
				pc = unsafe.Add(pc, 4)
			} else {
				pc = unsafe.Add(pc, (int(int32(*(*uint32)(pc)))+1)*4)
			}

		case opForPrep: // R[A] init, R[A+1] limit, R[A+2] step, R[A+3] the visible control variable
			a := uint8(i >> 8)
			init, limit, step := &regs[a], &regs[a+1], &regs[a+2]
			if init.p != tInt() || limit.p != tInt() || step.p != tInt() || int64(step.n) <= 0 {
				e = exSlowOp // float loops, float limits, negative and zero steps: the driver prepares them
				break dispatch
			}
			if int64(init.n) > int64(limit.n) {
				pc = unsafe.Add(pc, int(i>>16)*4) // no iteration at all
			} else {
				limit.n = (limit.n - init.n) / step.n // iterations still to come, as a uint64: it cannot overflow
				regs[a+3] = *init
			}

		case opForLoop:
			a := uint8(i >> 8)
			// the counter and index are written through .n alone, so all three must carry the
			// integer tag: the verifier cannot prove that a FORPREP ran, and an object's n
			// changed this way would forge another kind
			if regs[a].p != tInt() || regs[a+1].p != tInt() || regs[a+2].p != tInt() {
				e = exSlowOp // a float loop, or registers no FORPREP prepared
				break dispatch
			}
			if cnt := regs[a+1].n; cnt > 0 {
				regs[a+1].n = cnt - 1
				idx := regs[a].n + regs[a+2].n // never wraps: the count ends the loop first
				regs[a].n = idx
				setInt(&regs[a+3], idx)
				pc = unsafe.Add(pc, -int(i>>16)*4)
				if ex.st.ticks--; ex.st.ticks < 0 { // every back-edge ticks
					e = exTick
					break dispatch
				}
			}

		case opCall: // R[A], ... = R[A](R[A+1], ..., R[A+B-1]); C-1 results are expected
			a := uint8(i >> 8)
			fn := &regs[a]
			if fn.n == kindLuaFn<<56 && !isScalar(fn.p) && uint8(i>>16) != 0 && !(*closure)(fn.p).p.vararg {
				//gen:fast
				if uintptr(unsafe.Pointer(fn)) >= ex.st.limitAddr {
					e = exGrowStack
					break dispatch
				}
				if ex.st.nf == len(ex.pframes) {
					e = exGrowFrames
					break dispatch
				}
				// the record has no pointers: the caller's closure is read back from its own function slot
				code0 := uintptr(unsafe.Pointer(unsafe.SliceData(cl.p.code)))
				ex.pframes[ex.st.nf] = uint64(uint32((uintptr(pc)-code0)>>2)) | uint64(a+1)<<32
				ex.st.nf++
				cl = (*closure)(fn.p)
				regs = (*[256]Value)(unsafe.Pointer(&regs[a+1]))
				for j := int(uint8(i>>16)) - 1; j < int(cl.p.nparams); j++ {
					regs[uint8(j)] = Value{} // only missing parameters are filled
				}
				if top := uintptr(unsafe.Pointer(regs)) + uintptr(cl.p.maxstack)*16; top > ex.st.hiAddr {
					ex.st.hiAddr = top // raised at push, so it is also right after an error
				}
				k = unsafe.Pointer(unsafe.SliceData(cl.p.k))
				pc = unsafe.Pointer(unsafe.SliceData(cl.p.code))
				//gen:checked
				//				if base+int(a)+1+256 > len(ex.stack) {
				//					e = exGrowStack
				//					break dispatch
				//				}
				//				if ex.st.nf == len(ex.pframes) {
				//					e = exGrowFrames
				//					break dispatch
				//				}
				//				ex.pframes[ex.st.nf] = uint64(uint32(pc)) | uint64(a+1)<<32
				//				ex.st.nf++
				//				cl = (*closure)(fn.p)
				//				base += int(a) + 1
				//				regs = (*[256]Value)(ex.stack[base : base+256])
				//				for j := int(uint8(i>>16)) - 1; j < int(cl.p.nparams); j++ {
				//					regs[uint8(j)] = Value{}
				//				}
				//				if top := base + int(cl.p.maxstack); top > ex.st.hi {
				//					ex.st.hi = top
				//				}
				//				k = cl.p.k
				//				code = cl.p.code
				//				pc = 0
				//gen:end
				if ex.st.ticks--; ex.st.ticks < 0 {
					e = exTick
					break dispatch
				}
			} else if fn.n == kindGoFn<<56 && !isScalar(fn.p) {
				e = exHostCall
				break dispatch
			} else {
				e = exSlowOp // open argument lists, vararg callees, __call and errors live in the driver
				break dispatch
			}

		case opReturn1, opReturn0:
			var r Value
			var n int
			if uint8(i) == opReturn1 {
				r, n = regs[uint8(i>>8)], 1
			}
			//gen:fast
			*(*Value)(unsafe.Add(unsafe.Pointer(regs), -16)) = r // the function slot is the result slot
			//gen:checked
			//			ex.stack[base-1] = r
			//gen:end
			ex.st.nf--
			fr := ex.pframes[ex.st.nf]
			if fr>>56 != 0 {
				ex.st.nret = n
				e = exReturn // a frame the VM started: Go entry, or a continuation
				break dispatch
			}
			//gen:fast
			regs = (*[256]Value)(unsafe.Add(unsafe.Pointer(regs), -int(fr>>32&0xffffff)*16))
			cl = (*closure)((*Value)(unsafe.Add(unsafe.Pointer(regs), -16)).p)
			k = unsafe.Pointer(unsafe.SliceData(cl.p.k))
			pc = unsafe.Add(unsafe.Pointer(unsafe.SliceData(cl.p.code)), int(uint32(fr))*4)
			if want := *(*uint32)(unsafe.Add(pc, -4)) >> 24; want != 2 { // C of the CALL at pc-1
				//gen:checked
				//			base -= int(fr >> 32 & 0xffffff)
				//			regs = (*[256]Value)(ex.stack[base : base+256])
				//			cl = checkedCaller(&ex.stack[base-1])
				//			k = cl.p.k
				//			code = cl.p.code
				//			pc = int(uint32(fr))
				//			if want := code[pc-1] >> 24; want != 2 {
				//gen:end
				ex.st.nret = n
				e = exResults // zero, several or an open number of results: the driver pads or drops
				break dispatch
			}

		case opLoadF:
			setFloat(&regs[uint8(i>>8)], float64(int16(i>>16)))

		case opGetGlobal, opSetGlobal: // a field of the closure's globals table; the aux word is the site
			t := cl.env
			key := kAt(k, i>>16)
			hint := atomic.LoadUint32(hintAt(cl.p, *(*uint32)(pc)))
			slot := hint & hintSlotMask
			if t != nil && int(slot) < len(t.nodes) {
				nd := &t.nodes[slot]
				if same(&nd.k, key) && (nd.v.p != nil || t.meta == nil) {
					if uint8(i) == opGetGlobal {
						setValue(&regs[uint8(i>>8)], &nd.v)
						pc = unsafe.Add(pc, 4)
						continue
					}
					if t.flags&(tabFrozen|tabGuarded) == 0 && regs[uint8(i>>8)].p != nil { // a nil store may shrink: the driver
						setValue(&nd.v, &regs[uint8(i>>8)])
						pc = unsafe.Add(pc, 4)
						continue
					}
				}
			}
			e = exSlowOp
			break dispatch

		case opGetTable, opGetIndex: // R[A] = R[B][R[C]] or R[B][C]: the array part inline
			obj := &regs[uint8(i>>16)]
			var idx uint64
			if uint8(i) == opGetIndex {
				idx = uint64(uint8(i>>24)) - 1
			} else if key := &regs[uint8(i>>24)]; key.p == tInt() {
				idx = key.n - 1
			} else if key.p == tFloat() {
				// a float with a whole value, as arithmetic in code written for Lua 5.1 makes
				// indexes: the integer key it normalises to
				var whole bool
				f := math.Float64frombits(key.n)
				if idx, whole = wholeIndex(f, int64(f)); !whole {
					e = exSlowOp
					break dispatch
				}
			} else if key.n>>56 == kindString && !isScalar(key.p) && key.n&lenMask <= 16 && obj.n == kindTable<<56 && !isScalar(obj.p) {
				// a short string key: hash it and probe inline, as hashString and keyEq would
				t, n := (*Table)(obj.p), key.n&lenMask
				if len(t.nodes) > 0 {
					// strWords and hashShort, written out: each costs more than a call in a big
					// function may, and TestShortKeysHashInline holds them to the same result
					p := key.p
					var w1, w2 uint64
					switch {
					case n >= 8:
						w1, w2 = *(*uint64)(p), *(*uint64)(unsafe.Add(p, n-8))
					case n >= 4:
						w1, w2 = uint64(*(*uint32)(p)), uint64(*(*uint32)(unsafe.Add(p, n-4)))
					case n > 0:
						w1 = uint64(*(*byte)(p))<<16 | uint64(*(*byte)(unsafe.Add(p, n/2)))<<8 | uint64(*(*byte)(unsafe.Add(p, n-1)))
					}
					h, a := hashSeed^n*m1, w1<<32|w2
					if n > 8 {
						h, a = mix(h^w1, m2), w2
					} else if n == 8 {
						a = w1
					}
					h, mask := mix(h^a, m1^hashSeed), uint64(len(t.nodes)-1)
					for j := uint64(0); j < 8; j++ {
						nd := &t.nodes[(h+j)&mask]
						if nd.k.n == key.n && !isScalar(nd.k.p) { // a string of the same length
							if nd.k.p != key.p && !strEqBytes(nd.k.p, key.p, uintptr(n)) {
								continue // another string of the same length
							}
							if nd.v.p == nil && t.meta != nil {
								break // a deleted key: __index decides
							}
							setValue(&regs[uint8(*(*uint32)(unsafe.Add(pc, -4))>>8)], &nd.v) // i reloaded: keeping it live spills it in the head
							continue dispatch
						}
						if nd.k.p == nil {
							if t.meta != nil {
								break
							}
							regs[uint8(*(*uint32)(unsafe.Add(pc, -4))>>8)] = Value{}
							continue dispatch
						}
					}
				} else if t.meta == nil {
					regs[uint8(*(*uint32)(unsafe.Add(pc, -4))>>8)] = Value{}
					continue
				}
				e = exSlowOp // a long probe, or __index
				break dispatch
			} else {
				e = exSlowOp
				break dispatch
			}
			if obj.n == kindTable<<56 && !isScalar(obj.p) {
				t := (*Table)(obj.p)
				if idx < uint64(len(t.arr)) {
					if v := &t.arr[idx]; v.p != nil || t.meta == nil {
						setValue(&regs[uint8(i>>8)], v)
						continue
					}
				} else if len(t.nodes) > 0 {
					// an integer key in the hash part, as t[0] is: probe inline, hashing as hashWord does
					hi, lo := bits.Mul64((idx+1^2<<62)*hashMul, m2^hashSeed)
					h, mask := hi^lo, uint64(len(t.nodes)-1)
					for j := uint64(0); j < 4; j++ {
						nd := &t.nodes[(h+j)&mask]
						if nd.k.p == tInt() && nd.k.n == idx+1 {
							if nd.v.p == nil && t.meta != nil {
								break
							}
							setValue(&regs[uint8(i>>8)], &nd.v)
							continue dispatch
						}
						if nd.k.p == nil {
							break
						}
					}
				}
			}
			e = exSlowOp
			break dispatch

		case opSetField, opSetFieldK: // R[A][K[B]] = R[C] or K[C]; the aux word is the site number
			obj, key, v := &regs[uint8(i>>8)], kAt(k, uint32(uint8(i>>16))), &regs[uint8(i>>24)]
			if uint8(i) == opSetFieldK {
				v = kAt(k, i>>24)
			}
			if obj.n == kindTable<<56 && !isScalar(obj.p) {
				t := (*Table)(obj.p)
				slot := atomic.LoadUint32(hintAt(cl.p, *(*uint32)(pc))) & hintSlotMask
				// a write hit also needs the table not frozen, and an old value or no metatable,
				// because of __newindex. Keys starting with "__" go to the driver, which clears
				// the table's cache of absent metamethods.
				if int(slot) < len(t.nodes) && t.flags&(tabFrozen|tabGuarded) == 0 && !isMetaName(key) {
					if nd := &t.nodes[slot]; same(&nd.k, key) && (nd.v.p != nil || t.meta == nil) && v.p != nil {
						setValue(&nd.v, v)
						pc = unsafe.Add(pc, 4)
						continue
					}
				}
			}
			e = exSlowOp
			break dispatch

		case opSetTable, opSetIndex, opSetTableK, opSetIndexK: // R[A][R[B]] or R[A][B] = R[C] or K[C]: the array part inline
			obj, v := &regs[uint8(i>>8)], &regs[uint8(i>>24)]
			if uint8(i) == opSetTableK || uint8(i) == opSetIndexK {
				v = kAt(k, i>>24)
			}
			var idx uint64
			if uint8(i) == opSetIndex || uint8(i) == opSetIndexK {
				idx = uint64(uint8(i>>16)) - 1
			} else if key := &regs[uint8(i>>16)]; key.p == tInt() {
				idx = key.n - 1
			} else if key.p == tFloat() {
				var whole bool
				f := math.Float64frombits(key.n)
				if idx, whole = wholeIndex(f, int64(f)); !whole {
					e = exSlowOp
					break dispatch
				}
			} else {
				e = exSlowOp
				break dispatch
			}
			// an array part that has held only scalars is memory the GC does not scan: the
			// first pointer stored into it goes to the driver, which moves the array
			if obj.n == kindTable<<56 && !isScalar(obj.p) && (isScalar(v.p) || (*Table)(obj.p).ptrArr) {
				t := (*Table)(obj.p)
				if idx < uint64(len(t.arr)) && t.flags&tabFrozen == 0 {
					if d := &t.arr[idx]; d.p != nil || t.meta == nil {
						setValue(d, v)
						continue
					}
				} else if idx == uint64(len(t.arr)) && idx < uint64(cap(t.arr)) && len(t.nodes) == 0 &&
					t.meta == nil && t.flags&tabFrozen == 0 && v.p != nil {
					// an append within capacity: no allocation, and with no hash part no key past
					// the end to move. Only the length word changes, so no pointer is written.
					*(*int)(unsafe.Add(unsafe.Pointer(&t.arr), unsafe.Sizeof(uintptr(0)))) = int(idx) + 1
					setValue(&t.arr[idx], v)
					continue
				}
			}
			e = exSlowOp
			break dispatch

		case opSelf: // R[A+1] = R[B]; R[A] = R[B][K[C]]; the aux word is the site number
			obj, key := &regs[uint8(i>>16)], kAt(k, i>>24)
			var t *Table
			if obj.n == kindTable<<56 && !isScalar(obj.p) {
				t = (*Table)(obj.p)
			} else if obj.n>>56 == kindString && !isScalar(obj.p) {
				t = ex.strIdx // s:method(): the string library, when the metatable is frozen
			}
			if t != nil {
				slot := atomic.LoadUint32(hintAt(cl.p, *(*uint32)(pc))) & hintSlotMask
				if int(slot) < len(t.nodes) {
					if nd := &t.nodes[slot]; same(&nd.k, key) && (nd.v.p != nil || t.meta == nil) {
						a := uint8(i >> 8)
						setValue(&regs[a+1], obj) // obj may be R[A]: copy it first
						setValue(&regs[a], &nd.v)
						pc = unsafe.Add(pc, 4)
						continue
					}
				}
			}
			e = exSlowOp
			break dispatch

		case opDiv, opDivK:
			x, y := &regs[uint8(i>>16)], &regs[uint8(i>>24)]
			if uint8(i) == opDivK {
				y = kAt(k, i>>24)
			}
			if isNum(x) && isNum(y) {
				setFloat(&regs[uint8(i>>8)], toFloat(x)/toFloat(y))
			} else {
				e = exSlowOp
				break dispatch
			}

		case opMod, opModK, opIDiv, opIDivK: // integers with a divisor other than 0 and -1
			x, y := &regs[uint8(i>>16)], &regs[uint8(i>>24)]
			if uint8(i) == opModK || uint8(i) == opIDivK {
				y = kAt(k, i>>24)
			}
			if x.p == tInt() && y.p == tInt() && int64(y.n)+1 > 1 {
				a, b := int64(x.n), int64(y.n)
				q, m := a/b, a%b
				if m != 0 && (m^b) < 0 { // round towards minus infinity
					q--
					m += b
				}
				if uint8(i) == opMod || uint8(i) == opModK {
					setInt(&regs[uint8(i>>8)], uint64(m))
				} else {
					setInt(&regs[uint8(i>>8)], uint64(q))
				}
			} else if (uint8(i) == opMod || uint8(i) == opModK) && (x.p == tFloat() || y.p == tFloat()) && isNum(x) && isNum(y) {
				// a float remainder of whole numbers below 2^53, as code written before Lua had
				// integers takes bits: exact as integers, where math.Mod loops over the quotient's
				// bits. Two integers with a divisor below 1 are the driver's: the result is an integer
				fx, fy := toFloat(x), toFloat(y)
				a, b := int64(fx), int64(fy)
				if float64(a) != fx || float64(b) != fy || b == 0 || fx >= 0x1p53 || fx <= -0x1p53 || fy >= 0x1p53 || fy <= -0x1p53 {
					// not whole, too large, NaN, infinite, or a zero divisor. Spelt out: wholeInt
					// here spills the loop
					e = exSlowOp
					break dispatch
				}
				m := a % b
				if m != 0 && (m^b) < 0 { // round towards minus infinity
					m += b
				}
				// the result's bits, so that no float lives across the branch, which spills it
				r := math.Float64bits(float64(m))
				if m == 0 {
					// as fmod: a zero remainder keeps the dividend's sign, which is bit 63 of an
					// integer and of a float alike
					r = x.n & (1 << 63)
				}
				setFloat(&regs[uint8(i>>8)], math.Float64frombits(r))
			} else {
				e = exSlowOp
				break dispatch
			}

		case opBAnd, opBOr, opBXor, opBAndK, opBOrK, opBXorK:
			x, y := &regs[uint8(i>>16)], &regs[uint8(i>>24)]
			op := uint8(i)
			if op >= opBAndK {
				y = kAt(k, i>>24)
				op -= opBAndK - opBAnd
			}
			if x.p == tInt() && y.p == tInt() {
				r := x.n & y.n
				if op == opBOr {
					r = x.n | y.n
				} else if op == opBXor {
					r = x.n ^ y.n
				}
				setInt(&regs[uint8(i>>8)], r)
			} else {
				e = exSlowOp
				break dispatch
			}

		case opShl, opShr, opShlK, opShrK:
			x, y := &regs[uint8(i>>16)], &regs[uint8(i>>24)]
			if uint8(i) == opShlK || uint8(i) == opShrK {
				y = kAt(k, i>>24)
			}
			if x.p == tInt() && y.p == tInt() {
				n := int64(y.n)
				if uint8(i) == opShr || uint8(i) == opShrK {
					n = -n
				}
				var r uint64
				if n > -64 && n < 64 { // 64 or more either way gives 0
					if n >= 0 {
						r = x.n << uint(n)
					} else {
						r = x.n >> uint(-n)
					}
				}
				setInt(&regs[uint8(i>>8)], r)
			} else {
				e = exSlowOp
				break dispatch
			}

		case opUnm:
			x := &regs[uint8(i>>16)]
			if x.p == tInt() {
				setInt(&regs[uint8(i>>8)], -x.n)
			} else if x.p == tFloat() {
				setFloat(&regs[uint8(i>>8)], -math.Float64frombits(x.n))
			} else {
				e = exSlowOp
				break dispatch
			}

		case opNot:
			x := &regs[uint8(i>>16)]
			if x.p == nil || (x.p == tBool() && x.n == 0) {
				setBool(&regs[uint8(i>>8)], 1)
			} else {
				setBool(&regs[uint8(i>>8)], 0)
			}

		case opEqJmp: // test R[A] == R[B]: the same words, or numbers of one kind
			x, y := &regs[uint8(i>>8)], &regs[uint8(i>>16)]
			var eq bool
			if same(x, y) {
				eq = x.p != tFloat() || x.n<<1 <= 0x7ff<<53 // the same bits are equal, unless they are a NaN
			} else if x.p == tFloat() && y.p == tFloat() {
				eq = math.Float64frombits(x.n) == math.Float64frombits(y.n)
			} else if x.p == y.p && (x.p == tInt() || x.p == tBool()) || x.p == nil || y.p == nil {
				eq = false // scalars of one kind with other bits, or nil against anything else
			} else {
				e = exSlowOp // mixed numbers, strings behind other pointers, __eq
				break dispatch
			}
			if eq == (i>>24 != 0) {
				pc = unsafe.Add(pc, 4)
			} else {
				pc = unsafe.Add(pc, (int(int32(*(*uint32)(pc)))+1)*4)
			}

		case opLeJmp, opLeKJmp, opGtKJmp, opGeKJmp: // R[A] <= R[B] or K[B]; K[B] < R[A]; K[B] <= R[A]
			x, y := &regs[uint8(i>>8)], &regs[uint8(i>>16)]
			op := uint8(i)
			if op != opLeJmp {
				y = kAt(k, uint32(uint8(i>>16)))
			}
			if op == opGtKJmp || op == opGeKJmp {
				x, y = y, x
			}
			var r bool
			if x.p == tInt() && y.p == tInt() {
				r = int64(x.n) < int64(y.n) || (op != opGtKJmp && x.n == y.n)
			} else if x.p == tFloat() && y.p == tFloat() {
				a, b := math.Float64frombits(x.n), math.Float64frombits(y.n)
				r = a < b || (op != opGtKJmp && a == b)
			} else {
				e = exSlowOp
				break dispatch
			}
			if r == (i>>24 != 0) {
				pc = unsafe.Add(pc, 4)
			} else {
				pc = unsafe.Add(pc, (int(int32(*(*uint32)(pc)))+1)*4)
			}

		case opTestJmp: // test R[A] is truthy
			x := &regs[uint8(i>>8)]
			if (x.p != nil && !(x.p == tBool() && x.n == 0)) == (i>>24 != 0) {
				pc = unsafe.Add(pc, 4)
			} else {
				pc = unsafe.Add(pc, (int(int32(*(*uint32)(pc)))+1)*4)
			}

		case opTestSet: // test R[B]; fall through when it equals C, else R[A] = R[B] and jump
			x := &regs[uint8(i>>16)]
			if (x.p != nil && !(x.p == tBool() && x.n == 0)) == (i>>24 != 0) {
				pc = unsafe.Add(pc, 4)
			} else {
				setValue(&regs[uint8(i>>8)], x)
				pc = unsafe.Add(pc, (int(int32(*(*uint32)(pc)))+1)*4)
			}

		case opGetCell, opGetUpCell: // R[A] = cell of R[B] or of Up[B]
			var c *Value
			if uint8(i) == opGetCell {
				c = &regs[uint8(i>>16)]
			} else {
				c = upAt(cl, uint8(i>>16))
			}
			if c.n == kindCell<<56 && !isScalar(c.p) {
				setValue(&regs[uint8(i>>8)], &(*cell)(c.p).v)
			} else {
				e = exSlowOp
				break dispatch
			}

		case opSetCell, opSetUpCell: // cell of R[A] = R[B]; cell of Up[B] = R[A]
			var c, v *Value
			if uint8(i) == opSetCell {
				c, v = &regs[uint8(i>>8)], &regs[uint8(i>>16)]
			} else {
				c, v = upAt(cl, uint8(i>>16)), &regs[uint8(i>>8)]
			}
			if c.n == kindCell<<56 && !isScalar(c.p) && !(*cell)(c.p).frozen {
				setValue(&(*cell)(c.p).v, v)
			} else {
				e = exSlowOp
				break dispatch
			}

		case opTForLoop: // if R[A+4] ~= nil then R[A+2] = R[A+4]; pc -= Bx
			a := uint8(i >> 8)
			if regs[a+4].p != nil {
				setValue(&regs[a+2], &regs[a+4])
				pc = unsafe.Add(pc, -int(i>>16)*4)
				if ex.st.ticks--; ex.st.ticks < 0 { // every back-edge ticks
					e = exTick
					break dispatch
				}
			}

		default: // everything else is done by the driver, which also rejects opBad. Listing all 256
			// values would not drop the range check: the compiler merges the unused ones into one run,
			// and the switch then fails the jump-table density test.
			e = exSlowOp
			break dispatch
		}
	}

	// indices, never addresses: nothing outside this function may hold a pointer into the stack
	//gen:fast
	// stack0 is recomputed rather than kept: one live register less in the loop
	stack0 = unsafe.Pointer(unsafe.SliceData(ex.stack))
	ex.st.cl = cl
	ex.st.base = int((uintptr(unsafe.Pointer(regs)) - uintptr(stack0)) / 16)
	ex.st.pc = int((uintptr(pc) - uintptr(unsafe.Pointer(unsafe.SliceData(cl.p.code)))) / 4)
	ex.st.hi = int((ex.st.hiAddr - uintptr(stack0)) / 16)
	//gen:checked
	//	ex.st.cl = cl
	//	ex.st.base = base
	//	ex.st.pc = pc
	//gen:end
	return e
}
