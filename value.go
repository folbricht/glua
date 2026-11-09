package glua

import (
	"math"
	"math/rand/v2"
	"strconv"
	"unsafe"
)

// Value is any Lua value. It is 16 bytes, the size of a Go interface, and is passed by value.
// The zero Value is nil. Values cannot be compared with == or used as map keys; use Equal.
//
// Scalars are identified by p, objects by n:
//
//	nil       p == nil                n == 0
//	boolean   p == &tags.boolean      n is 0 or 1
//	integer   p == &tags.integer      n holds the int64 bits
//	float     p == &tags.float        n holds the float64 bits
//	string    first byte, or emptyStr n is kindString<<56 | length
//	table     *Table                  n is kindTable<<56
//	function  *closure or *goFunc     n is kindLuaFn<<56 or kindGoFn<<56
//	thread    *coroutine              n is kindThread<<56
//	userdata  the Go pointer itself   n is kindUser<<56 | flags<<48 | type ID
//
// Every constructor keeps four invariants, which checkValue asserts:
//
//  1. p == nil exactly when the Value is {nil, 0}.
//  2. Every empty string is {&emptyStr[0], kindString<<56}.
//  3. p points inside its allocation, never one past the end.
//  4. Type IDs are process-wide and never reused.
type Value struct {
	_ [0]func()      // no size; makes == and map keys a compile error
	p unsafe.Pointer // a type sentinel, or a real pointer the Go GC can follow
	n uint64         // the scalar, or kind<<56 | payload
}

// A 32-bit build fails here instead of misbehaving: the constant overflows unless the size is 16.
const _ = -(unsafe.Sizeof(Value{}) ^ 16)

var (
	// the sentinels for float, bool and int, kept together so that isScalar is one range
	// check. Fields, not array elements, as &tags.integer costs the inliner less than an
	// index, and the address of the field at offset zero costs it nothing: the float tag is
	// there, since setFloat would otherwise exceed the budget of a big function. hashValue
	// mixes in each tag's offset; the loop's inline hash of integer keys assumes 2.
	tags     struct{ float, boolean, integer, unused byte }
	emptyStr [1]byte // "" needs a pointer of its own, or it would collide with nil
)

// Object kinds, kept in the top byte of n.
const (
	kindString = 1 + iota
	kindTable
	kindLuaFn
	kindGoFn
	kindThread
	kindUser
	kindCell // internal: a captured variable's cell; never visible to Lua
)

// A userdata's n is kindUser<<56 | flags<<48 | typeID.
const (
	flagReadonly   = 1 << 48
	flagCallscoped = 1 << 49
	typeIDMask     = 1<<48 - 1
	lenMask        = 1<<56 - 1
)

func tBool() unsafe.Pointer  { return unsafe.Pointer(&tags.boolean) }
func tInt() unsafe.Pointer   { return unsafe.Pointer(&tags.integer) }
func tFloat() unsafe.Pointer { return unsafe.Pointer(&tags.float) }

func emptyString() Value { return Value{p: unsafe.Pointer(&emptyStr[0]), n: kindString << 56} }

// isScalar reports whether p is nil or one of the sentinels.
func isScalar(p unsafe.Pointer) bool {
	return p == nil || uintptr(p)-uintptr(unsafe.Pointer(&tags)) < unsafe.Sizeof(tags)
}

// Bool returns a Lua boolean.
func Bool(b bool) Value {
	if b {
		return Value{p: tBool(), n: 1}
	}
	return Value{p: tBool()}
}

// Int returns a Lua integer.
func Int(i int64) Value { return Value{p: tInt(), n: uint64(i)} }

// Float returns a Lua float.
func Float(f float64) Value { return Value{p: tFloat(), n: math.Float64bits(f)} }

// String returns a Lua string. It does not copy s.
func String(s string) Value {
	if len(s) == 0 {
		return emptyString()
	}
	return Value{p: unsafe.Pointer(unsafe.StringData(s)), n: kindString<<56 | uint64(len(s))}
}

// subString returns bytes [i, j) of the string v without copying. It is the one producer
// of substrings, so invariant 3 holds: an empty result never points at the end of v.
func subString(v Value, i, j int) Value {
	if i >= j {
		return emptyString()
	}
	return Value{p: unsafe.Add(v.p, i), n: kindString<<56 | uint64(j-i)}
}

// str returns the Go string for a string Value, without copying.
func (v Value) str() string {
	return unsafe.String((*byte)(v.p), int(v.n&lenMask))
}

// isObj is the object check. Both halves are needed: an integer can hold any 64-bit pattern.
func (v Value) isObj(kind uint64) bool { return v.n>>56 == kind && !isScalar(v.p) }

func (v Value) isString() bool { return v.isObj(kindString) }

func (v Value) truthy() bool { return v.p != nil && !(v.p == tBool() && v.n == 0) }

// same reports whether two Values are the same two words. It implies Lua equality unless they are floats.
func same(a, b *Value) bool { return a.p == b.p && a.n == b.n }

// setInt stores an integer result. It leaves p alone when the slot already has the tag,
// so a register that keeps its type never takes the GC write barrier.
//
// The setters, isNum, toFloat and the other helpers that fast uses must each cost at most 20,
// the inliner's budget for a call in a big function, so that fast can grow past the size
// at which it becomes one; asmgate checks it. They name the tags directly, as calls to tInt
// and the others cost more.
func setInt(d *Value, n uint64) {
	if d.p != unsafe.Pointer(&tags.integer) {
		d.p = unsafe.Pointer(&tags.integer)
	}
	d.n = n
}

// setValue copies v into d. Like setInt, it writes p only when it changes, so copying a
// number over a number, or the same object over itself, takes no write barrier.
func setValue(d *Value, v *Value) {
	if d.p != v.p {
		d.p = v.p
	}
	d.n = v.n
}

// setFloat stores a float result, like setInt.
func setFloat(d *Value, f float64) {
	if d.p != unsafe.Pointer(&tags.float) {
		d.p = unsafe.Pointer(&tags.float)
	}
	d.n = math.Float64bits(f)
}

// setBool stores a boolean result, like setInt. b must be 0 or 1.
func setBool(d *Value, b uint64) {
	if d.p != unsafe.Pointer(&tags.boolean) {
		d.p = unsafe.Pointer(&tags.boolean)
	}
	d.n = b
}

// numEq is exact: an int64 is never rounded to a float64.
func numEq(x, y Value) bool {
	switch {
	case x.p == tInt() && y.p == tInt():
		return x.n == y.n
	case x.p == tFloat() && y.p == tFloat():
		return math.Float64frombits(x.n) == math.Float64frombits(y.n)
	case x.p == tFloat():
		x, y = y, x
	}
	f := math.Float64frombits(y.n) // x is the integer
	return f >= -0x1p63 && f < 0x1p63 && f == math.Trunc(f) && int64(f) == int64(x.n)
}

func (v Value) isNumber() bool { return v.p == tInt() || v.p == tFloat() }

// rawEqual is Lua equality without metamethods.
func rawEqual(a, b Value) bool {
	if same(&a, &b) {
		return a.p != tFloat() || a.n<<1 <= 0x7ff<<53 // the same bits are equal, unless they are a NaN
	}
	if isScalar(a.p) || isScalar(b.p) {
		return a.isNumber() && b.isNumber() && numEq(a, b)
	}
	if a.n>>56 == kindUser && b.n>>56 == kindUser {
		return a.p == b.p && a.n&typeIDMask == b.n&typeIDMask // the same object, whatever the flags
	}
	if a.n != b.n || a.n>>56 != kindString {
		return false // different kinds, lengths or objects
	}
	return a.str() == b.str() // equal length behind different pointers
}

// Kind is the type of a Value as Lua sees it.
type Kind uint8

// The kinds of Value. Lua's number type is split into KindInt and KindFloat.
const (
	KindNil      Kind = iota // nil
	KindBool                 // boolean
	KindInt                  // integer number
	KindFloat                // float number
	KindString               // string
	KindTable                // table
	KindFunction             // a Lua or Go function
	KindUserdata             // a Go pointer
	KindThread               // a coroutine
)

var kindNames = [...]string{"nil", "boolean", "integer", "float", "string", "table", "function", "userdata", "thread"}

// String returns the Lua type name, with integer and float told apart.
func (k Kind) String() string {
	if int(k) < len(kindNames) {
		return kindNames[k]
	}
	return "Kind(" + strconv.Itoa(int(k)) + ")"
}

// Kind returns the type of v.
func (v Value) Kind() Kind {
	switch v.p {
	case nil:
		return KindNil
	case tBool():
		return KindBool
	case tInt():
		return KindInt
	case tFloat():
		return KindFloat
	}
	switch v.n >> 56 {
	case kindString:
		return KindString
	case kindTable:
		return KindTable
	case kindLuaFn, kindGoFn:
		return KindFunction
	case kindThread:
		return KindThread
	}
	return KindUserdata
}

// IsNil reports whether v is nil.
func (v Value) IsNil() bool { return v.p == nil }

// Truthy reports whether v counts as true in a Lua condition: anything but nil and false.
func (v Value) Truthy() bool { return v.truthy() }

// Equal reports whether v and w are equal in Lua without metamethods (rawequal).
// 1 equals 1.0, 0.0 equals -0.0, and NaN equals nothing.
func (v Value) Equal(w Value) bool { return rawEqual(v, w) }

// Int returns v as an integer if v is an integer, or a float with an exact integer value.
// Strings are not converted.
func (v Value) Int() (int64, bool) {
	switch v.p {
	case tInt():
		return int64(v.n), true
	case tFloat():
		return floatToInt(math.Float64frombits(v.n))
	}
	return 0, false
}

// Float returns v as a float if v is a number. Strings are not converted.
func (v Value) Float() (float64, bool) {
	switch v.p {
	case tInt():
		return float64(int64(v.n)), true
	case tFloat():
		return math.Float64frombits(v.n), true
	}
	return 0, false
}

// Str returns the contents of v if v is a string. Numbers are not converted.
// The result shares memory with v and must not be modified through unsafe means.
func (v Value) Str() (string, bool) {
	if v.isString() {
		return v.str(), true
	}
	return "", false
}

// floatToInt converts f to an int64 if f has an exact integer value in range.
func floatToInt(f float64) (int64, bool) {
	if f >= -0x1p63 && f < 0x1p63 && f == math.Trunc(f) {
		return int64(f), true
	}
	return 0, false
}

// String returns what Lua's tostring would return, without running metamethods.
// Objects show a keyed hash in place of their address, so no heap address is ever revealed.
func (v Value) String() string {
	switch k := v.Kind(); k {
	case KindNil:
		return "nil"
	case KindBool:
		if v.n != 0 {
			return "true"
		}
		return "false"
	case KindInt:
		return strconv.FormatInt(int64(v.n), 10)
	case KindFloat:
		return formatFloat(math.Float64frombits(v.n))
	case KindString:
		return v.str()
	default:
		return k.String() + ": " + hidePointer(v.p)
	}
}

// formatFloat formats f as C Lua does with LUAI_NUMFFORMAT "%.14g", adding ".0" when
// the result would otherwise read as an integer.
func formatFloat(f float64) string {
	switch {
	case math.IsInf(f, 1):
		return "inf"
	case math.IsInf(f, -1):
		return "-inf"
	case math.IsNaN(f):
		if math.Signbit(f) {
			return "-nan"
		}
		return "nan"
	}
	b := strconv.AppendFloat(make([]byte, 0, 24), f, 'g', 14, 64)
	for _, c := range b {
		if c == '.' || c == 'e' {
			return string(b)
		}
	}
	return string(append(b, '.', '0'))
}

// addrKey is the per-process key for hidePointer.
var addrKey = rand.Uint64() | 1

// hidePointer formats a keyed hash of p, so tostring(t) can tell objects apart without
// telling a script anything about the heap layout.
func hidePointer(p unsafe.Pointer) string {
	x := uint64(uintptr(p)) * addrKey
	x ^= x >> 29
	x *= 0xbf58476d1ce4e5b9
	x ^= x >> 32
	b := make([]byte, 0, 18)
	b = append(b, "0x"...)
	s := strconv.FormatUint(x&(1<<48-1), 16)
	for range 12 - len(s) {
		b = append(b, '0')
	}
	return string(append(b, s...))
}

// checkValue reports which invariant v breaks, or "" if none. The checked loop and the
// tests call it; the fast loop trusts it.
func checkValue(v Value) string {
	switch {
	case v.p == nil:
		if v.n != 0 {
			return "nil pointer with a non-zero payload"
		}
	case v.p == unsafe.Pointer(&tags.unused):
		return "pointer to the unused tag"
	case v.p == tBool():
		if v.n > 1 {
			return "boolean payload other than 0 or 1"
		}
	case v.p == tInt(), v.p == tFloat():
	case v.p == unsafe.Pointer(&emptyStr[0]):
		if v.n != kindString<<56 {
			return "empty-string pointer on a non-empty string or another kind"
		}
	default:
		switch k := v.n >> 56; k {
		case kindString:
			if v.n&lenMask == 0 {
				return "empty string that is not the canonical empty string"
			}
		case kindTable, kindLuaFn, kindGoFn, kindThread, kindCell:
			if v.n&lenMask != 0 {
				return "object with a payload"
			}
		case kindUser:
			if v.n&lenMask&^(flagReadonly|flagCallscoped|typeIDMask) != 0 {
				return "userdata with unknown flags"
			}
		default:
			return "unknown object kind"
		}
	}
	return ""
}
