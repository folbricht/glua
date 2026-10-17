package glua

import (
	"math"
	"unsafe"
)

// Built-ins that FASTCALL does inline. A library function carries its id in goFunc.fast;
// host functions carry none, so a script that defines its own math.floor gets the ordinary
// call.
const (
	fastNone = iota
	fastMathAbs
	fastMathFloor
	fastMathCeil
	fastMathSqrt
	fastMathMax
	fastMathMin
	fastType
	fastStrLen
	fastStrByte
	fastStrSub
	fastSelect

	numFast
)

// fastIDs maps a library function's name, as the compiler sees the call, to its built-in.
var fastIDs = map[string]uint8{
	"math.abs": fastMathAbs, "math.floor": fastMathFloor, "math.ceil": fastMathCeil,
	"math.sqrt": fastMathSqrt, "math.max": fastMathMax, "math.min": fastMathMin,
	"type": fastType, "string.len": fastStrLen, "string.byte": fastStrByte, "string.sub": fastStrSub,
	"select": fastSelect,
}

// methodIDs maps a method name to the built-in that s:name(...) calls when s is a string,
// through the string metatable. FASTCALL checks at run time that the method found is it.
var methodIDs = map[string]uint8{"len": fastStrLen, "byte": fastStrByte, "sub": fastStrSub}

// typeNames are the results of type, by Kind, with the pointers of the compiler's
// constants, so that type(x) == "table" compares pointers.
var typeNames = func() (t [KindThread + 1]Value) {
	for k := range t {
		name := Kind(k).String()
		if Kind(k) == KindInt || Kind(k) == KindFloat {
			name = "number"
		}
		t[k] = internKey(String(name), maxInterned)
	}
	return t
}()

// fastCall does the FASTCALL at pc-1: the built-in inline when R[A] is it and the
// arguments suit its inline form, skipping the CALL that follows; otherwise nothing, and
// the CALL runs.
func (ex *executor) fastCall(i uint32) {
	st := &ex.st
	call := ex.instr(st.pc + 1)
	st.pc++ // past the aux word: the CALL is next
	a, nargs, nres := decA(i), decB(i)-1, decC(call)-1
	f := *ex.reg(a)
	if !f.isObj(kindGoFn) || nres < 0 || nres > 1 || st.ticks <= 0 { // open results set top: the CALL does that
		return
	}
	id := (*goFunc)(f.p).fast
	if uint32(id) != ex.aux0() {
		return
	}
	x, y, z := ex.stack[st.base+a+1], ex.stack[st.base+a+2], Value{}
	if nargs >= 3 {
		z = ex.stack[st.base+a+3]
	}
	r, ok := fastBuiltin(id, nargs, x, y, z)
	if !ok {
		return
	}
	st.ticks-- // a call ticks
	if nres == 1 {
		*ex.reg(a) = r
	}
	st.pc++ // past the CALL
}

// aux0 returns the aux word of the instruction before the CALL at pc.
func (ex *executor) aux0() uint32 { return ex.st.cl.p.code[ex.st.pc-1] }

// fastBuiltin computes built-in id on the arguments x, y and z, nargs of them, if its inline
// form applies; ok is false otherwise, and the ordinary call does the work.
func fastBuiltin(id uint8, nargs int, x, y, z Value) (r Value, ok bool) {
	switch id {
	case fastMathAbs:
		if nargs != 1 {
			return
		}
		switch x.p {
		case tInt():
			if v := int64(x.n); v < 0 {
				return Int(-v), true // minint wraps, as in C Lua
			}
			return x, true
		case tFloat():
			return Value{p: tFloat(), n: x.n &^ (1 << 63)}, true
		}
	case fastMathFloor, fastMathCeil:
		if nargs != 1 {
			return
		}
		switch x.p {
		case tInt():
			return x, true
		case tFloat():
			fv := math.Float64frombits(x.n)
			if id == fastMathFloor {
				fv = math.Floor(fv)
			} else {
				fv = math.Ceil(fv)
			}
			if t, fits := floatToInt(fv); fits {
				return Int(t), true
			}
			return Float(fv), true
		}
	case fastMathSqrt:
		if f, isNum := x.Float(); nargs == 1 && isNum {
			return Float(math.Sqrt(f)), true
		}
	case fastMathMax, fastMathMin:
		if nargs != 2 {
			return
		}
		less := false
		switch {
		case x.p == tInt() && y.p == tInt():
			less = int64(x.n) < int64(y.n)
		case x.p == tFloat() && y.p == tFloat():
			xf, yf := math.Float64frombits(x.n), math.Float64frombits(y.n)
			if id == fastMathMax {
				less = xf < yf
			} else {
				less = yf < xf
			}
			if less {
				return y, true
			}
			return x, true
		default:
			return
		}
		if less == (id == fastMathMax) {
			return y, true
		}
		return x, true
	case fastType:
		if nargs == 1 {
			k := x.Kind()
			if k == KindFloat {
				k = KindInt
			}
			return typeNames[k], true
		}
	case fastStrLen:
		if nargs == 1 && x.isString() {
			return Int(int64(x.n & lenMask)), true
		}
	case fastStrByte:
		if !x.isString() || !(nargs == 1 || nargs == 2 && y.p == tInt()) {
			return
		}
		n, at := int64(x.n&lenMask), int64(1)
		if nargs == 2 {
			at = int64(y.n)
		}
		if at < 0 {
			at += n + 1
		}
		if at >= 1 && at <= n {
			return Int(int64(*(*byte)(unsafe.Add(x.p, at-1)))), true
		}
		return Value{}, true // no byte there: no result
	case fastStrSub:
		if !x.isString() || y.p != tInt() || !(nargs == 2 || nargs == 3 && z.p == tInt()) {
			return
		}
		n, j := int(x.n&lenMask), int64(-1)
		if nargs == 3 {
			j = int64(z.n)
		}
		return subString(x, strStart(int64(y.n), n), strEnd(j, n)), true
	case fastSelect:
		if nargs < 1 {
			return // select(): the call reports the missing argument
		}
		if x.isString() && x.n&lenMask >= 1 && *(*byte)(x.p) == '#' {
			return Int(int64(nargs - 1)), true
		}
		if x.p != tInt() || int64(x.n) < 1 || nargs > 3 && int64(x.n) > 2 {
			return // negative and out of range indexes, and arguments fastCall did not read
		}
		switch int64(x.n) {
		case 1:
			if nargs >= 2 {
				return y, true
			}
		case 2:
			if nargs >= 3 {
				return z, true
			}
		}
		return Value{}, true // past the last argument: no result
	}
	return
}

// fastSelect does the FASTSELECT at pc-1: select(R[A+1], ...) with one result, read from the
// frame's varargs without copying them, when R[A] is the built-in select. It then skips the
// VARARG and CALL that follow. Otherwise it does nothing, and they run.
func (ex *executor) fastSelect(i uint32) {
	st := &ex.st
	a := decA(i)
	f := *ex.reg(a)
	if call := ex.instr(st.pc + 1); !f.isObj(kindGoFn) || (*goFunc)(f.p).fast != fastSelect || uint8(call) != opCall || decC(call) != 2 || st.ticks <= 0 {
		return
	}
	nextra := 0
	if ex.pframes[st.nf-1]&frVararg != 0 {
		nextra = int(ex.nvar[st.nf-1])
	}
	var r Value
	switch x := *ex.reg(a + 1); {
	case x.isString() && x.n&lenMask >= 1 && *(*byte)(x.p) == '#':
		r = Int(int64(nextra))
	case x.p == tInt():
		n := int64(x.n)
		if n < 0 {
			n += int64(nextra) + 1
		}
		if n < 1 {
			return // out of range: the call reports it
		}
		if n <= int64(nextra) {
			r = ex.stack[st.base-1-nextra+int(n)-1]
		}
	default:
		return
	}
	st.ticks-- // a call ticks
	*ex.reg(a) = r
	st.pc += 2 // past the VARARG and the CALL
}
