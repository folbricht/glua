package glua

import (
	"fmt"
	"maps"
	"math"
	"reflect"
	"sort"
	"sync"
	"sync/atomic"
	"time"
	"unsafe"
)

// Conversions between Go and Lua values. The rules are built in, plus the conversions
// registered with Convert:
//
//   - bool, integers, floats and strings are Lua scalars. An integer that does not fit, or a
//     float without an exact integer value, does not convert to a Go integer.
//   - time.Duration is a number of seconds; time.Time is Unix seconds, and decodes from a
//     number or an RFC 3339 string.
//   - A pointer to a struct is a userdata: the Go pointer itself. A struct by value is copied
//     to the heap first.
//   - Slices, arrays and maps become new tables; []byte becomes a string. Tables decode into
//     slices, maps and structs, whose fields are named as in Lua; a key that names no field is
//     an error.
//   - Value, *Table and GoFunc pass through. A bare Go function needs an adapter.
//   - any decodes to nil, bool, int64, float64, string, []any for a sequence, map[string]any
//     or map[any]any for other tables, the Go pointer of a userdata, or else the Value.

// maxConvDepth is the fixed cap on the nesting of a Go-Lua conversion.
const maxConvDepth = 64

var (
	valueType    = reflect.TypeFor[Value]()
	tableType    = reflect.TypeFor[*Table]()
	goFuncType   = reflect.TypeFor[GoFunc]()
	durationType = reflect.TypeFor[time.Duration]()
	timeType     = reflect.TypeFor[time.Time]()
	bytesType    = reflect.TypeFor[[]byte]()
)

// converter is a conversion registered with Convert, working on reflect values.
type converter struct {
	enc func(reflect.Value) Value
	dec func(Value) (reflect.Value, error)
}

var (
	convMu     sync.Mutex                                  // serialises registration
	converters atomic.Pointer[map[reflect.Type]*converter] // copy on write, so lookups take no lock
	convGen    atomic.Uint64                               // counts registrations, for plans that depend on them
)

func init() {
	converters.Store(&map[reflect.Type]*converter{})
}

// Convert gives T a scalar or string form instead of a userdata: netip.Addr, uuid.UUID,
// decimals. Conversions are process-wide, like type IDs; registering a second conversion for
// the same type fails.
func Convert[T any](enc func(T) Value, dec func(Value) (T, error)) Option {
	return optionFunc(func(o *options) {
		o.converts = append(o.converts, convertReg{reflect.TypeFor[T](), &converter{
			enc: func(rv reflect.Value) Value { return enc(rv.Interface().(T)) },
			dec: func(v Value) (reflect.Value, error) {
				x, err := dec(v)
				return reflect.ValueOf(&x).Elem(), err
			},
		}})
	})
}

type convertReg struct {
	t reflect.Type
	c *converter
}

// register installs the conversions of New. A type keeps its first conversion.
func (r convertReg) register() error {
	convMu.Lock()
	defer convMu.Unlock()
	cur := *converters.Load()
	if _, ok := cur[r.t]; ok {
		return &BindError{Type: r.t, Reason: "the type already has a conversion"}
	}
	next := maps.Clone(cur)
	next[r.t] = r.c
	converters.Store(&next)
	convGen.Add(1)
	return nil
}

func converterFor(t reflect.Type) *converter {
	return (*converters.Load())[t]
}

// ValueOf converts v to a Value by the built-in rules and registered conversions. It panics
// on a type that cannot be converted, which is a programming error.
func ValueOf[T any](v T) Value {
	switch x := any(v).(type) {
	case int64:
		return Int(x)
	case int:
		return Int(int64(x))
	case float64:
		return Float(x)
	case string:
		return String(x)
	case bool:
		return Bool(x)
	case Value:
		return x
	}
	if x, ok := encodePlanned(v, planFor[T]()); ok {
		return x
	}
	val, err := toValue(v)
	if err != nil {
		panic("glua: ValueOf: " + err.Error())
	}
	return val
}

// toValue converts a Go value to a Lua value.
func toValue(v any) (Value, error) {
	return encodeReflect(reflect.ValueOf(v), 0)
}

// encodeReflect converts the Go value rv.
func encodeReflect(rv reflect.Value, depth int) (Value, error) {
	if depth > maxConvDepth {
		return Value{}, fmt.Errorf("nested more than %d levels deep", maxConvDepth)
	}
	if !rv.IsValid() {
		return Value{}, nil
	}
	t := rv.Type()
	if c := converterFor(t); c != nil {
		return c.enc(rv), nil
	}
	switch t {
	case valueType:
		return rv.Interface().(Value), nil
	case tableType:
		if rv.IsNil() {
			return Value{}, nil
		}
		return tableValue(rv.Interface().(*Table)), nil
	case goFuncType:
		if rv.IsNil() {
			return Value{}, nil
		}
		return goFnValue(&goFunc{name: "?", f: rv.Interface().(GoFunc), host: true}), nil
	case durationType:
		return Float(time.Duration(rv.Int()).Seconds()), nil
	case timeType:
		return timeValue(rv.Interface().(time.Time)), nil
	case bytesType:
		return String(string(rv.Bytes())), nil
	}
	switch t.Kind() {
	case reflect.Bool:
		return Bool(rv.Bool()), nil
	case reflect.Int, reflect.Int8, reflect.Int16, reflect.Int32, reflect.Int64:
		return Int(rv.Int()), nil
	case reflect.Uint, reflect.Uint8, reflect.Uint16, reflect.Uint32, reflect.Uint64, reflect.Uintptr:
		u := rv.Uint()
		if u > math.MaxInt64 {
			return Value{}, fmt.Errorf("%d does not fit in a Lua integer", u)
		}
		return Int(int64(u)), nil
	case reflect.Float32, reflect.Float64:
		return Float(rv.Float()), nil
	case reflect.String:
		return String(rv.String()), nil
	case reflect.Interface:
		return encodeReflect(rv.Elem(), depth+1)
	case reflect.Pointer:
		if rv.IsNil() {
			return Value{}, nil
		}
		if t.Elem().Kind() == reflect.Struct {
			return userValue(rv.UnsafePointer(), t.Elem()), nil
		}
		return encodeReflect(rv.Elem(), depth+1)
	case reflect.Struct:
		p := reflect.New(t) // a copy on the heap: the script may keep it
		p.Elem().Set(rv)
		return userValue(p.UnsafePointer(), t), nil
	case reflect.Slice, reflect.Array:
		if t.Kind() == reflect.Slice && rv.IsNil() {
			return Value{}, nil
		}
		tab := NewTable(rv.Len(), 0)
		for i := range rv.Len() {
			x, err := encodeReflect(rv.Index(i), depth+1)
			if err != nil {
				return Value{}, err
			}
			tab.arr[i] = x
		}
		return tableValue(tab), nil
	case reflect.Map:
		if rv.IsNil() {
			return Value{}, nil
		}
		tab := NewTable(0, rv.Len())
		for it := rv.MapRange(); it.Next(); {
			k, err := encodeReflect(it.Key(), depth+1)
			if err != nil {
				return Value{}, err
			}
			x, err := encodeReflect(it.Value(), depth+1)
			if err != nil {
				return Value{}, err
			}
			nk, ok := normKey(k)
			if !ok {
				return Value{}, fmt.Errorf("map key %v is not a valid table key", it.Key())
			}
			tab.set(canonKey(nk), x)
		}
		return tableValue(tab), nil
	case reflect.Func:
		return Value{}, fmt.Errorf("a Go function needs an adapter, such as lua.Fn1 or lua.Reflect")
	}
	return Value{}, fmt.Errorf("unsupported type %s", t)
}

// userValue is the userdata for a pointer p to a struct of type t.
func userValue(p unsafe.Pointer, t reflect.Type) Value {
	if p == nil {
		return Value{} // invariant 1: p == nil exactly when the Value is {nil, 0}
	}
	return Value{p: p, n: kindUser<<56 | bindType(t)}
}

// timeValue is t as Unix seconds: an integer when t has no fraction of a second.
func timeValue(t time.Time) Value {
	if t.Nanosecond() == 0 {
		return Int(t.Unix())
	}
	return Float(float64(t.Unix()) + float64(t.Nanosecond())/1e9) // UnixNano overflows outside 1678 to 2262
}

// As converts v to T by the built-in rules and registered conversions.
func (v Value) As[T any]() (T, error) {
	switch any(*new(T)).(type) {
	case int64:
		i, err := decInt(v)
		return any(i).(T), err
	case float64:
		f, err := decFloat(v)
		return any(f).(T), err
	case string:
		s, err := decString(v)
		return any(s).(T), err
	case bool:
		return any(v.truthy()).(T), nil
	case Value:
		return any(v).(T), nil
	}
	var r T
	err := decodeReflect(v, reflect.ValueOf(&r).Elem(), "", 0)
	return r, err
}

// convError reports a value that does not convert to a Go type, at path.
func convError(path string, v Value, t reflect.Type, why string) error {
	msg := fmt.Sprintf("cannot convert %s to %s", typeName(v), t)
	if path != "" {
		msg = path + ": " + msg
	}
	if why != "" {
		msg += ": " + why
	}
	return &convErr{msg: msg}
}

// convErr is a Lua value that does not convert to the Go type asked for.
type convErr struct{ msg string }

// Error returns the message.
func (e *convErr) Error() string { return "glua: " + e.msg }

// decodeReflect stores v, converted, in rv, which must be settable. path names v in messages.
func decodeReflect(v Value, rv reflect.Value, path string, depth int) error {
	if depth > maxConvDepth {
		return &convErr{msg: fmt.Sprintf("%s: nested more than %d levels deep", path, maxConvDepth)}
	}
	t := rv.Type()
	if c := converterFor(t); c != nil {
		x, err := c.dec(v)
		if err != nil {
			return convError(path, v, t, err.Error())
		}
		rv.Set(x)
		return nil
	}
	switch t {
	case valueType:
		rv.Set(reflect.ValueOf(v))
		return nil
	case tableType:
		switch {
		case v.isObj(kindTable):
			rv.Set(reflect.ValueOf((*Table)(v.p)))
		case v.IsNil():
			rv.SetZero()
		default:
			return convError(path, v, t, "")
		}
		return nil
	case durationType:
		f, ok := v.Float()
		ns := math.Round(f * 1e9) // f*1e9 can land just below a whole number of nanoseconds
		if !ok || math.IsNaN(f) || ns >= 1<<63 || ns < -(1<<63) {
			return convError(path, v, t, "out of range")
		}
		rv.SetInt(int64(ns))
		return nil
	case timeType:
		var tm time.Time
		if s, ok := v.Str(); ok {
			var err error
			if tm, err = time.Parse(time.RFC3339Nano, s); err != nil {
				return convError(path, v, t, err.Error())
			}
		} else if i, ok := v.Int(); ok {
			tm = time.Unix(i, 0)
		} else if f, ok := v.Float(); ok && f >= -(1<<63) && f < 1<<63 { // NaN fails both
			sec, frac := math.Modf(f)
			tm = time.Unix(int64(sec), int64(math.Round(frac*1e9)))
		} else {
			return convError(path, v, t, "")
		}
		rv.Set(reflect.ValueOf(tm))
		return nil
	case bytesType:
		s, ok := v.Str()
		if !ok {
			return convError(path, v, t, "")
		}
		rv.SetBytes([]byte(s))
		return nil
	}
	switch t.Kind() {
	case reflect.Bool:
		rv.SetBool(v.truthy())
	case reflect.Int, reflect.Int8, reflect.Int16, reflect.Int32, reflect.Int64:
		i, ok := v.Int()
		if !ok {
			return convError(path, v, t, "")
		}
		if rv.OverflowInt(i) {
			return convError(path, v, t, fmt.Sprintf("%d is out of range", i))
		}
		rv.SetInt(i)
	case reflect.Uint, reflect.Uint8, reflect.Uint16, reflect.Uint32, reflect.Uint64, reflect.Uintptr:
		i, ok := v.Int()
		if !ok {
			return convError(path, v, t, "")
		}
		if i < 0 || rv.OverflowUint(uint64(i)) {
			return convError(path, v, t, fmt.Sprintf("%d is out of range", i))
		}
		rv.SetUint(uint64(i))
	case reflect.Float32, reflect.Float64:
		f, ok := v.Float()
		if !ok {
			return convError(path, v, t, "")
		}
		if rv.OverflowFloat(f) && !math.IsInf(f, 0) {
			return convError(path, v, t, fmt.Sprintf("%g is out of range", f))
		}
		rv.SetFloat(f)
	case reflect.String:
		s, ok := v.Str()
		if !ok {
			return convError(path, v, t, "")
		}
		rv.SetString(s)
	case reflect.Interface:
		if v.IsNil() {
			rv.SetZero()
			return nil
		}
		x, err := naturalValue(v, depth)
		if err != nil {
			return err
		}
		xv := reflect.ValueOf(x)
		if !xv.Type().AssignableTo(t) {
			return convError(path, v, t, "")
		}
		rv.Set(xv)
	case reflect.Pointer:
		switch {
		case v.IsNil():
			rv.SetZero()
		case v.isObj(kindUser) && t.Elem().Kind() == reflect.Struct:
			if v.n&typeIDMask != bindType(t.Elem()) {
				return convError(path, v, t, "a userdata of another type")
			}
			if v.n&flagCallscoped != 0 {
				return convError(path, v, t, "the value lives only during the call")
			}
			rv.Set(reflect.NewAt(t.Elem(), v.p))
		default:
			p := reflect.New(t.Elem())
			if err := decodeReflect(v, p.Elem(), path, depth+1); err != nil {
				return err
			}
			rv.Set(p)
		}
	case reflect.Struct:
		switch {
		case v.isObj(kindUser):
			if v.n&typeIDMask != bindType(t) {
				return convError(path, v, t, "a userdata of another type")
			}
			rv.Set(reflect.NewAt(t, v.p).Elem())
		case v.isObj(kindTable):
			return decodeStruct((*Table)(v.p), rv, path, depth)
		default:
			return convError(path, v, t, "")
		}
	case reflect.Slice:
		if v.IsNil() {
			rv.SetZero()
			return nil
		}
		if !v.isObj(kindTable) {
			return convError(path, v, t, "")
		}
		tab := (*Table)(v.p)
		n := tab.Len()
		s := reflect.MakeSlice(t, n, n)
		for i := range n {
			if err := decodeReflect(tab.Get(Int(int64(i+1))), s.Index(i), fmt.Sprintf("%s[%d]", path, i+1), depth+1); err != nil {
				return err
			}
		}
		rv.Set(s)
	case reflect.Array:
		if !v.isObj(kindTable) {
			return convError(path, v, t, "")
		}
		tab := (*Table)(v.p)
		if n := tab.Len(); n > t.Len() {
			return convError(path, v, t, fmt.Sprintf("%d items", n))
		}
		for i := range t.Len() {
			if err := decodeReflect(tab.Get(Int(int64(i+1))), rv.Index(i), fmt.Sprintf("%s[%d]", path, i+1), depth+1); err != nil {
				return err
			}
		}
	case reflect.Map:
		if v.IsNil() {
			rv.SetZero()
			return nil
		}
		if !v.isObj(kindTable) {
			return convError(path, v, t, "")
		}
		tab := (*Table)(v.p)
		m := reflect.MakeMap(t)
		for k, x := range tab.All() {
			kv := reflect.New(t.Key()).Elem()
			if err := decodeReflect(k, kv, path+" (a key)", depth+1); err != nil {
				return err
			}
			xv := reflect.New(t.Elem()).Elem()
			if err := decodeReflect(x, xv, path+keyPath(k), depth+1); err != nil {
				return err
			}
			m.SetMapIndex(kv, xv)
		}
		rv.Set(m)
	default:
		return convError(path, v, t, "unsupported type")
	}
	return nil
}

// decodeStruct fills the struct rv from the fields of tab. A key that names no field is an
// error: the Go side is strict.
func decodeStruct(tab *Table, rv reflect.Value, path string, depth int) error {
	t := rv.Type()
	fields := structFields(t)
	for k, x := range tab.All() {
		name, ok := k.Str()
		f, found := fields[name]
		if !ok || !found {
			return &convErr{msg: fmt.Sprintf("%sno field %s in %s", prefix(path), keyName(k), t)}
		}
		if err := decodeReflect(x, rv.FieldByIndex(f), path+keyPath(k), depth+1); err != nil {
			return err
		}
	}
	return nil
}

func prefix(path string) string {
	if path == "" {
		return ""
	}
	return path + ": "
}

// keyName renders a key for messages: 'name', or the value.
func keyName(k Value) string {
	if s, ok := k.Str(); ok {
		return "'" + s + "'"
	}
	return k.String()
}

var structFieldCache sync.Map // reflect.Type -> map[string][]int

// structFields maps the Lua names of t's visible fields, embedded structs included, to
// their index paths.
func structFields(t reflect.Type) map[string][]int {
	if m, ok := structFieldCache.Load(t); ok {
		return m.(map[string][]int)
	}
	m := map[string][]int{}
	for _, f := range reflect.VisibleFields(t) {
		if !f.IsExported() || f.Anonymous && f.Type.Kind() == reflect.Struct {
			continue
		}
		name, _, skip := fieldName(f)
		if skip {
			continue
		}
		if _, dup := m[name]; !dup {
			m[name] = f.Index
		}
	}
	structFieldCache.Store(t, m)
	return m
}

// naturalValue converts v to the Go value an any receives.
func naturalValue(v Value, depth int) (any, error) {
	if depth > maxConvDepth {
		return nil, &convErr{msg: fmt.Sprintf("nested more than %d levels deep", maxConvDepth)}
	}
	switch v.Kind() {
	case KindNil:
		return nil, nil
	case KindBool:
		return v.truthy(), nil
	case KindInt:
		return int64(v.n), nil
	case KindFloat:
		return math.Float64frombits(v.n), nil
	case KindString:
		return v.str(), nil
	case KindUserdata:
		if ti := userType(v); ti != nil {
			return reflect.NewAt(ti.rt, v.p).Interface(), nil
		}
	case KindTable:
		tab := (*Table)(v.p)
		n := tab.Len()
		count, allStrings := 0, true
		for k := range tab.All() {
			count++
			allStrings = allStrings && k.isString()
		}
		if count == n {
			s := make([]any, n)
			for i := range n {
				x, err := naturalValue(tab.Get(Int(int64(i+1))), depth+1)
				if err != nil {
					return nil, err
				}
				s[i] = x
			}
			return s, nil
		}
		if allStrings {
			m := make(map[string]any, count)
			for k, x := range tab.All() {
				y, err := naturalValue(x, depth+1)
				if err != nil {
					return nil, err
				}
				m[k.str()] = y
			}
			return m, nil
		}
		m := make(map[any]any, count)
		for k, x := range tab.All() {
			kk, err := naturalValue(k, depth+1)
			if err != nil {
				return nil, err
			}
			y, err := naturalValue(x, depth+1)
			if err != nil {
				return nil, err
			}
			m[kk] = y
		}
		return m, nil
	}
	return v, nil
}

// checkDecodable reports, at bind time, a type that no Lua value can decode into.
func checkDecodable(t reflect.Type, depth int, seen map[reflect.Type]bool) error {
	if seen[t] || depth > maxConvDepth {
		return nil
	}
	seen[t] = true
	if converterFor(t) != nil {
		return nil
	}
	switch t {
	case valueType, tableType, durationType, timeType, bytesType:
		return nil
	}
	switch t.Kind() {
	case reflect.Bool, reflect.Int, reflect.Int8, reflect.Int16, reflect.Int32, reflect.Int64,
		reflect.Uint, reflect.Uint8, reflect.Uint16, reflect.Uint32, reflect.Uint64, reflect.Uintptr,
		reflect.Float32, reflect.Float64, reflect.String, reflect.Interface:
		return nil
	case reflect.Pointer, reflect.Slice, reflect.Array:
		return checkDecodable(t.Elem(), depth+1, seen)
	case reflect.Map:
		if err := checkDecodable(t.Key(), depth+1, seen); err != nil {
			return err
		}
		return checkDecodable(t.Elem(), depth+1, seen)
	case reflect.Struct:
		fields := structFields(t)
		names := make([]string, 0, len(fields))
		for name := range fields {
			names = append(names, name)
		}
		sort.Strings(names)
		for _, name := range names {
			if err := checkDecodable(t.FieldByIndex(fields[name]).Type, depth+1, seen); err != nil {
				return err
			}
		}
		return nil
	}
	return fmt.Errorf("unsupported type %s", t)
}

// checkEncodable reports, at bind time, a type that cannot become a Lua value.
func checkEncodable(t reflect.Type, depth int, seen map[reflect.Type]bool) error {
	if seen[t] || depth > maxConvDepth {
		return nil
	}
	seen[t] = true
	if converterFor(t) != nil {
		return nil
	}
	switch t {
	case valueType, tableType, goFuncType, durationType, timeType, bytesType:
		return nil
	}
	switch t.Kind() {
	case reflect.Bool, reflect.Int, reflect.Int8, reflect.Int16, reflect.Int32, reflect.Int64,
		reflect.Uint, reflect.Uint8, reflect.Uint16, reflect.Uint32, reflect.Uint64, reflect.Uintptr,
		reflect.Float32, reflect.Float64, reflect.String, reflect.Interface:
		return nil
	case reflect.Pointer:
		if t.Elem().Kind() == reflect.Struct {
			return nil
		}
		return checkEncodable(t.Elem(), depth+1, seen)
	case reflect.Struct:
		return nil
	case reflect.Slice, reflect.Array:
		return checkEncodable(t.Elem(), depth+1, seen)
	case reflect.Map:
		if err := checkEncodable(t.Key(), depth+1, seen); err != nil {
			return err
		}
		return checkEncodable(t.Elem(), depth+1, seen)
	case reflect.Func:
		return fmt.Errorf("a Go function needs an adapter, such as lua.Fn1 or lua.Reflect")
	}
	return fmt.Errorf("unsupported type %s", t)
}

// Field returns t[name], raw, converted to T.
func (t *Table) Field[T any](name string) (T, error) {
	v := t.Get(String(name))
	r, err := v.As[T]()
	if ce, ok := err.(*convErr); ok {
		err = &convErr{msg: "field '" + name + "': " + ce.msg}
	}
	return r, err
}

// SetField sets t[name] = v, raw, converting v with ValueOf. It panics if t is frozen or v
// cannot be converted.
func (t *Table) SetField[T any](name string, v T) {
	t.Set(String(name), ValueOf(v))
}
