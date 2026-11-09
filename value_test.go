package glua

import (
	"math"
	"reflect"
	"strings"
	"testing"
	"unsafe"
)

func TestValueLayout(t *testing.T) {
	if s := unsafe.Sizeof(Value{}); s != 16 {
		t.Fatalf("Value is %d bytes, want 16", s)
	}
	if reflect.TypeFor[Value]().Comparable() {
		t.Fatal("Value must not be comparable with ==")
	}
	// The string fast path loads a string field as two words: data pointer, then length.
	s := "abc"
	h := (*[2]uintptr)(unsafe.Pointer(&s))
	if h[0] != uintptr(unsafe.Pointer(unsafe.StringData(s))) || h[1] != 3 {
		t.Fatal("string header is not {data, len}")
	}
}

func TestZeroValueIsNil(t *testing.T) {
	var v Value
	if !v.IsNil() || v.Kind() != KindNil || v.Truthy() || v.String() != "nil" {
		t.Fatalf("zero Value is not nil: kind %v", v.Kind())
	}
	if msg := checkValue(v); msg != "" {
		t.Fatal(msg)
	}
}

// Invariant 1: p == nil exactly when the Value is {nil, 0}.
func TestInvariantNil(t *testing.T) {
	for _, v := range []Value{Bool(false), Int(0), Float(0), String(""), String("x")} {
		if v.p == nil {
			t.Errorf("%v (%v) has a nil pointer", v, v.Kind())
		}
	}
	if msg := checkValue(Value{n: 1}); msg == "" {
		t.Error("checkValue accepts a nil pointer with a payload")
	}
}

// Invariant 2: every empty string is {&emptyStr[0], kindString<<56}.
func TestInvariantEmptyString(t *testing.T) {
	big := "hello"
	empties := []Value{
		String(""),
		String(big[5:]),
		String(big[2:2]),
		subString(String(big), 5, 5),
		subString(String(big), 3, 1),
	}
	for i, v := range empties {
		if !same(&v, &empties[0]) {
			t.Errorf("empty string %d is not canonical: %p %x", i, v.p, v.n)
		}
		if msg := checkValue(v); msg != "" {
			t.Errorf("empty string %d: %s", i, msg)
		}
	}
	if s, ok := empties[0].Str(); !ok || s != "" {
		t.Errorf("Str() = %q, %v", s, ok)
	}
	bad := Value{p: unsafe.Pointer(unsafe.StringData(big)), n: kindString << 56}
	if checkValue(bad) == "" {
		t.Error("checkValue accepts a non-canonical empty string")
	}
}

// Invariant 3: p points inside its allocation, never one past the end.
func TestInvariantSubstringInBounds(t *testing.T) {
	src := String(strings.Repeat("abcdef", 3))
	base := uintptr(src.p)
	end := base + uintptr(src.n&lenMask)
	n := int(src.n & lenMask)
	for i := 0; i <= n; i++ {
		for j := i; j <= n; j++ {
			v := subString(src, i, j)
			if msg := checkValue(v); msg != "" {
				t.Fatalf("sub(%d, %d): %s", i, j, msg)
			}
			if v.n&lenMask != 0 && (uintptr(v.p) < base || uintptr(v.p) >= end) {
				t.Fatalf("sub(%d, %d) points outside its string", i, j)
			}
			if got, want := v.str(), src.str()[i:j]; got != want {
				t.Fatalf("sub(%d, %d) = %q, want %q", i, j, got, want)
			}
		}
	}
}

func TestStringNoCopy(t *testing.T) {
	s := "no copy here"
	v := String(s)
	got, _ := v.Str()
	if unsafe.StringData(got) != unsafe.StringData(s) {
		t.Fatal("String or Str copied the bytes")
	}
	if a := testing.AllocsPerRun(100, func() { v = String(s); got, _ = v.Str() }); a != 0 {
		t.Fatalf("String round trip allocates %v times", a)
	}
}

func TestKinds(t *testing.T) {
	var x int
	tests := []struct {
		v    Value
		kind Kind
	}{
		{Value{}, KindNil},
		{Bool(true), KindBool},
		{Int(-1), KindInt},
		{Float(1.5), KindFloat},
		{String("s"), KindString},
		{Value{p: unsafe.Pointer(&x), n: kindTable << 56}, KindTable},
		{Value{p: unsafe.Pointer(&x), n: kindLuaFn << 56}, KindFunction},
		{Value{p: unsafe.Pointer(&x), n: kindGoFn << 56}, KindFunction},
		{Value{p: unsafe.Pointer(&x), n: kindThread << 56}, KindThread},
		{Value{p: unsafe.Pointer(&x), n: kindUser<<56 | flagReadonly | 7}, KindUserdata},
	}
	for _, tt := range tests {
		if got := tt.v.Kind(); got != tt.kind {
			t.Errorf("%v: Kind() = %v, want %v", tt.v, got, tt.kind)
		}
		if msg := checkValue(tt.v); msg != "" {
			t.Errorf("%v: %s", tt.kind, msg)
		}
	}
}

// An integer can carry any 64-bit pattern, including one that looks like an object's n.
// The object check must not be fooled by it.
func TestIsObjRejectsForgedIntegers(t *testing.T) {
	for _, kind := range []uint64{kindString, kindTable, kindLuaFn, kindGoFn, kindThread, kindUser} {
		forged := Int(int64(kind<<56 | 3))
		if forged.isObj(kind) {
			t.Errorf("an integer passes the object check for kind %d", kind)
		}
		if forged.Kind() != KindInt {
			t.Errorf("forged integer has kind %v", forged.Kind())
		}
	}
	f := Float(math.Float64frombits(kindTable << 56))
	if f.isObj(kindTable) {
		t.Error("a float passes the object check")
	}
}

func TestTruthy(t *testing.T) {
	falsy := []Value{{}, Bool(false)}
	truthy := []Value{Bool(true), Int(0), Float(0), String(""), Float(math.NaN())}
	for _, v := range falsy {
		if v.Truthy() {
			t.Errorf("%v is truthy", v)
		}
	}
	for _, v := range truthy {
		if !v.Truthy() {
			t.Errorf("%v is falsy", v)
		}
	}
}

func TestEqual(t *testing.T) {
	nan := math.NaN()
	a := "hello world"
	b := strings.Clone(a)
	var x, y int
	tests := []struct {
		a, b Value
		want bool
	}{
		{Value{}, Value{}, true},
		{Value{}, Bool(false), false},
		{Bool(true), Bool(true), true},
		{Bool(true), Bool(false), false},
		{Int(1), Float(1), true},
		{Float(1), Int(1), true},
		{Float(0), Float(math.Copysign(0, -1)), true},
		{Float(nan), Float(nan), false},
		{Value{p: tFloat(), n: math.Float64bits(nan)}, Value{p: tFloat(), n: math.Float64bits(nan)}, false},
		{Int(1<<53 + 1), Float(1 << 53), false},
		{Int(math.MaxInt64), Float(0x1p63), false},
		{Int(math.MinInt64), Float(-0x1p63), true},
		{Int(3), Float(3.5), false},
		{Int(1), String("1"), false},
		{String(a), String(b), true},
		{String(a), String(a[:5]), false},
		{String(""), String(b[3:3]), true},
		{Float(math.Inf(1)), Float(math.Inf(1)), true},
		{Int(5), Float(math.Inf(1)), false},
		{Value{p: unsafe.Pointer(&x), n: kindTable << 56}, Value{p: unsafe.Pointer(&x), n: kindTable << 56}, true},
		{Value{p: unsafe.Pointer(&x), n: kindTable << 56}, Value{p: unsafe.Pointer(&y), n: kindTable << 56}, false},
	}
	for _, tt := range tests {
		if got := tt.a.Equal(tt.b); got != tt.want {
			t.Errorf("%v == %v: got %v, want %v", tt.a, tt.b, got, tt.want)
		}
		if got := tt.b.Equal(tt.a); got != tt.want {
			t.Errorf("%v == %v (swapped): got %v, want %v", tt.b, tt.a, got, tt.want)
		}
	}
}

// Two equal words mean equal values, unless they are floats.
func TestSameImpliesEqual(t *testing.T) {
	for _, v := range []Value{{}, Bool(true), Int(-7), Float(2.5), String("x")} {
		if !same(&v, &v) || !v.Equal(v) {
			t.Errorf("%v is not equal to itself", v)
		}
	}
}

func TestConversions(t *testing.T) {
	if i, ok := Int(-3).Int(); !ok || i != -3 {
		t.Error("Int(-3).Int()")
	}
	if i, ok := Float(4).Int(); !ok || i != 4 {
		t.Error("Float(4).Int()")
	}
	for _, f := range []float64{4.5, math.NaN(), math.Inf(1), 0x1p63} {
		if _, ok := Float(f).Int(); ok {
			t.Errorf("Float(%v).Int() succeeded", f)
		}
	}
	if _, ok := String("4").Int(); ok {
		t.Error("String.Int() converted a string")
	}
	if f, ok := Int(1 << 40).Float(); !ok || f != 1<<40 {
		t.Error("Int.Float()")
	}
	if _, ok := Int(1).Str(); ok {
		t.Error("Int.Str() converted a number")
	}
}

func TestSetHelpersKeepTag(t *testing.T) {
	var d Value
	setInt(&d, 5)
	if d.p != tInt() || int64(d.n) != 5 {
		t.Fatal("setInt")
	}
	setFloat(&d, 1.25)
	if f, _ := d.Float(); d.p != tFloat() || f != 1.25 {
		t.Fatal("setFloat")
	}
	setBool(&d, 1)
	if d.p != tBool() || !d.Truthy() {
		t.Fatal("setBool")
	}
}

// The expected strings were produced by C Lua 5.4.8's tostring.
func TestString(t *testing.T) {
	tests := []struct {
		v    Value
		want string
	}{
		{Bool(true), "true"},
		{Bool(false), "false"},
		{Int(math.MinInt64), "-9223372036854775808"},
		{Float(1e15), "1e+15"},
		{Float(1e14), "1e+14"},
		{Float(0x1p63), "9.2233720368548e+18"},
		{Float(math.Copysign(0, -1)), "-0.0"},
		{Float(1e100), "1e+100"},
		{Float(123456789012345), "1.2345678901234e+14"},
		{Float(0.1), "0.1"},
		{Float(1.0 / 3), "0.33333333333333"},
		{Float(math.Pi), "3.1415926535898"},
		{Float(1e-5), "1e-05"},
		{Float(3), "3.0"},
		{Float(math.Inf(1)), "inf"},
		{Float(math.Inf(-1)), "-inf"},
		{Float(math.NaN()), "nan"},
		{Float(-math.NaN()), "-nan"},
		{String("raw"), "raw"},
	}
	for _, tt := range tests {
		if got := tt.v.String(); got != tt.want {
			t.Errorf("String() = %q, want %q", got, tt.want)
		}
	}
}

func TestStringHidesAddresses(t *testing.T) {
	var x, y [16]byte
	tx := Value{p: unsafe.Pointer(&x), n: kindTable << 56}
	ty := Value{p: unsafe.Pointer(&y), n: kindTable << 56}
	sx, sy := tx.String(), ty.String()
	if !strings.HasPrefix(sx, "table: 0x") || sx == sy {
		t.Fatalf("got %q and %q", sx, sy)
	}
	if sx != tx.String() {
		t.Fatal("the same object prints differently")
	}
	addr := strings.TrimLeft(strings.TrimPrefix(sx, "table: 0x"), "0")
	if strings.Contains(strings.ToLower(sx), strings.ToLower(uintptrHex(uintptr(unsafe.Pointer(&x))))) || addr == "" {
		t.Fatalf("%q reveals the address", sx)
	}
	f := Value{p: unsafe.Pointer(&x), n: kindGoFn << 56}
	if s := f.String(); !strings.HasPrefix(s, "function: 0x") {
		t.Fatalf("Go function prints as %q", s)
	}
}

func uintptrHex(p uintptr) string {
	const digits = "0123456789abcdef"
	var b []byte
	for ; p > 0; p >>= 4 {
		b = append([]byte{digits[p&15]}, b...)
	}
	return string(b)
}

func TestCheckValueRejects(t *testing.T) {
	var x int
	bad := []Value{
		{p: unsafe.Pointer(&tags.unused)},
		{p: tBool(), n: 2},
		{p: unsafe.Pointer(&emptyStr[0]), n: kindString<<56 | 1},
		{p: unsafe.Pointer(&emptyStr[0]), n: kindTable << 56},
		{p: unsafe.Pointer(&x), n: kindTable<<56 | 1},
		{p: unsafe.Pointer(&x), n: 0},
		{p: unsafe.Pointer(&x), n: 99 << 56},
		{p: unsafe.Pointer(&x), n: kindUser<<56 | 1<<55},
	}
	for i, v := range bad {
		if checkValue(v) == "" {
			t.Errorf("case %d: checkValue accepts an invalid Value", i)
		}
	}
}

// Hashing must never form a pointer past the end of a string. checkptr, on in race builds,
// catches one; this exercises every length around the 8-byte block size.
func TestHashStringInBounds(t *testing.T) {
	seen := map[uint64]bool{}
	for n := range 40 {
		s := strings.Repeat("x", n)
		v := String(strings.Clone(s))
		h := hashString(v.p, n)
		if h != hashString(String(s).p, n) {
			t.Fatalf("length %d: equal strings hash differently", n)
		}
		seen[h] = true
	}
	if len(seen) < 39 {
		t.Errorf("only %d distinct hashes for 40 lengths", len(seen))
	}
}
