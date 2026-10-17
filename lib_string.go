package glua

import (
	"bytes"
	"fmt"
	"math"
	"strconv"
	"strings"
)

// The string library, after C Lua 5.4's lstrlib.c. Substrings share memory with their
// source; results that grow are charged to the allocation budget.

// openString installs the string library in g and returns the metatable all strings share:
// its __index is the library, so that s:sub(1, 2) works.
func openString(g *Table) *Table {
	lib := newLib("string", map[string]GoFunc{
		"byte": strByte, "char": strChar, "find": strFind, "format": strFormat, "gmatch": strGmatch,
		"gsub": strGsub, "len": strLen, "lower": strLower, "match": strMatch, "rep": strRep,
		"reverse": strReverse, "sub": strSub, "upper": strUpper,
		"pack": strPack, "unpack": strUnpack, "packsize": strPacksize,
	})
	g.Set(String("string"), tableValue(lib))
	mt := NewTable(0, 2)
	mt.Set(String("__index"), tableValue(lib))
	return mt
}

// strIndex turns a Lua string position (1-based, negative from the end) into a 0-based
// offset, as C Lua's posrelat does for the start of a range.
func strStart(pos int64, n int) int {
	switch {
	case pos > 0:
		return int(min(pos, int64(n)+1)) - 1
	case pos == 0:
		return 0
	case pos < -int64(n):
		return 0
	}
	return n + int(pos)
}

// strEnd is the end of a range: inclusive, 1-based, clamped to the length.
func strEnd(pos int64, n int) int {
	switch {
	case pos > int64(n):
		return n
	case pos >= 0:
		return int(pos)
	case pos < -int64(n):
		return 0
	}
	return n + int(pos) + 1
}

func strLen(c *Call) error {
	s, err := c.checkString(0, "len")
	if err != nil {
		return err
	}
	return c.ReturnValues(Int(int64(len(s))))
}

func strSub(c *Call) error {
	v := c.Value(0)
	s, err := c.checkString(0, "sub")
	if err != nil {
		return err
	}
	if !v.isString() {
		v = String(s)
	}
	i, err := c.checkInt(1, "sub")
	if err != nil {
		return err
	}
	j, err := c.optInt(2, "sub", -1)
	if err != nil {
		return err
	}
	start, end := strStart(i, len(s)), strEnd(j, len(s))
	if start >= end {
		return c.ReturnValues(String(""))
	}
	return c.ReturnValues(subString(v, start, end)) // no copy
}

func strUpper(c *Call) error { return strMap(c, "upper", 'a', 'z', -32) }
func strLower(c *Call) error { return strMap(c, "lower", 'A', 'Z', 32) }

func strMap(c *Call, fname string, lo, hi byte, delta int) error {
	s, err := c.checkString(0, fname)
	if err != nil {
		return err
	}
	if err := c.ex.produce(len(s)); err != nil {
		return err
	}
	b := []byte(s)
	for i, ch := range b {
		if ch >= lo && ch <= hi {
			b[i] = byte(int(ch) + delta)
		}
	}
	return c.ReturnValues(String(string(b)))
}

func strReverse(c *Call) error {
	s, err := c.checkString(0, "reverse")
	if err != nil {
		return err
	}
	if err := c.ex.produce(len(s)); err != nil {
		return err
	}
	b := make([]byte, len(s))
	for i := range len(s) {
		b[len(s)-1-i] = s[i]
	}
	return c.ReturnValues(String(string(b)))
}

func strRep(c *Call) error {
	s, err := c.checkString(0, "rep")
	if err != nil {
		return err
	}
	n, err := c.checkInt(1, "rep")
	if err != nil {
		return err
	}
	sep, err := c.optString(2, "rep", "")
	if err != nil {
		return err
	}
	if n <= 0 {
		return c.ReturnValues(String(""))
	}
	total := int64(len(s)+len(sep))*n - int64(len(sep))
	if total > maxAlloc || total < 0 || n > maxAlloc {
		return c.libErrorf("resulting string too large")
	}
	if err := c.ex.produce(int(total) + int(n)); err != nil { // the copies, and a step per 64 pieces
		return err
	}
	var sb strings.Builder
	sb.Grow(int(total))
	for i := int64(0); i < n; i++ {
		if i > 0 {
			sb.WriteString(sep)
		}
		sb.WriteString(s)
	}
	return c.ReturnValues(String(sb.String()))
}

func strByte(c *Call) error {
	s, err := c.checkString(0, "byte")
	if err != nil {
		return err
	}
	i, err := c.optInt(1, "byte", 1)
	if err != nil {
		return err
	}
	j, err := c.optInt(2, "byte", i)
	if err != nil {
		return err
	}
	start, end := strStart(i, len(s)), strEnd(j, len(s))
	if start >= end {
		return c.ReturnValues()
	}
	vals := make([]Value, 0, end-start)
	for k := start; k < end; k++ {
		vals = append(vals, Int(int64(s[k])))
	}
	return c.ReturnValues(vals...)
}

func strChar(c *Call) error {
	b := make([]byte, c.Len())
	for i := range c.Len() {
		v, err := c.checkInt(i, "char")
		if err != nil {
			return err
		}
		if uint64(v) > 255 {
			return c.argError(i+1, "char", "value out of range")
		}
		b[i] = byte(v)
	}
	return c.ReturnValues(String(string(b)))
}

// noSpecials reports whether a pattern has no special characters, so find can search plainly.
func noSpecials(p string) bool { return !strings.ContainsAny(p, specials) }

func strFind(c *Call) error  { return strFindAux(c, true) }
func strMatch(c *Call) error { return strFindAux(c, false) }

func strFindAux(c *Call, find bool) error {
	fname := "match"
	if find {
		fname = "find"
	}
	s, err := c.checkString(0, fname)
	if err != nil {
		return err
	}
	p, err := c.checkString(1, fname)
	if err != nil {
		return err
	}
	init, err := c.optInt(2, fname, 1)
	if err != nil {
		return err
	}
	start := strStart(init, len(s))
	if init > int64(len(s))+1 {
		return c.ReturnValues(Value{}) // cannot find anything
	}
	if find && (c.Value(3).Truthy() || noSpecials(p)) {
		if i := strings.Index(s[start:], p); i >= 0 {
			return c.ReturnValues(Int(int64(start+i+1)), Int(int64(start+i+len(p))))
		}
		return c.ReturnValues(Value{})
	}
	ms := &matchState{src: s, pat: p, c: c}
	anchor := len(p) > 0 && p[0] == '^'
	pi := 0
	if anchor {
		pi = 1
	}
	for s1 := start; ; s1++ {
		ms.level, ms.depth = 0, 0
		if e := ms.match(s1, pi); e != -1 {
			if ms.err != nil {
				return ms.err
			}
			caps := ms.captures(s1, e, !find)
			if ms.err != nil {
				return ms.err
			}
			if find {
				return c.ReturnValues(append([]Value{Int(int64(s1 + 1)), Int(int64(e))}, caps...)...)
			}
			return c.ReturnValues(caps...)
		}
		if ms.err != nil {
			return ms.err
		}
		if s1 >= len(s) || anchor {
			break
		}
	}
	return c.ReturnValues(Value{})
}

func strGmatch(c *Call) error {
	s, err := c.checkString(0, "gmatch")
	if err != nil {
		return err
	}
	p, err := c.checkString(1, "gmatch")
	if err != nil {
		return err
	}
	init, err := c.optInt(2, "gmatch", 1)
	if err != nil {
		return err
	}
	pos := strStart(init, len(s))
	if init > int64(len(s))+1 {
		pos = len(s) + 1
	}
	lastMatch := -1
	it := &goFunc{name: "gmatch iterator", stateful: true}
	it.f = func(c *Call) error {
		ms := &matchState{src: s, pat: p, c: c}
		for ; pos <= len(s); pos++ {
			ms.level, ms.depth = 0, 0
			if e := ms.match(pos, 0); e != -1 && e != lastMatch {
				if ms.err != nil {
					return ms.err
				}
				caps := ms.captures(pos, e, true)
				pos, lastMatch = e, e
				if ms.err != nil {
					return ms.err
				}
				return c.ReturnValues(caps...)
			}
			if ms.err != nil {
				return ms.err
			}
		}
		return c.ReturnValues() // no match: no results, as C Lua's gmatch_aux returns 0
	}
	return c.ReturnValues(goFnValue(it))
}

func strGsub(c *Call) error {
	src, err := c.checkString(0, "gsub")
	if err != nil {
		return err
	}
	p, err := c.checkString(1, "gsub")
	if err != nil {
		return err
	}
	repl := c.Value(2)
	switch {
	case repl.isString() || repl.isNumber() || repl.isObj(kindTable) || repl.isObj(kindLuaFn) || repl.isObj(kindGoFn):
	default:
		return c.typeArgError(2, "gsub", "string/function/table")
	}
	maxN, err := c.optInt(3, "gsub", int64(len(src))+1)
	if err != nil {
		return err
	}
	anchor := len(p) > 0 && p[0] == '^'
	pi := 0
	if anchor {
		pi = 1
	}
	ms := &matchState{src: src, pat: p, c: c}
	var b strings.Builder
	charge := building{c: c}
	s, n, lastMatch, changed := 0, int64(0), -1, false
	for n < maxN {
		ms.level, ms.depth = 0, 0
		e := ms.match(s, pi)
		if ms.err != nil {
			return ms.err
		}
		switch {
		case e != -1 && e != lastMatch: // a match, but not an empty one right after the last
			n++
			ch, err := addValue(c, ms, &b, &charge, s, e, repl)
			if err != nil {
				return err
			}
			changed = changed || ch
			if err := c.ex.charge(e - s + 16); err != nil {
				return err
			}
			// until something changed it is a copy of src, given back as it is; the bytes
			// copied between matches come to no more than src, and are charged with the next
			if changed {
				if err := charge.grew(b.Len()); err != nil {
					return err
				}
			}
			s, lastMatch = e, e
		case s < len(src):
			b.WriteByte(src[s])
			s++
		default:
			goto done
		}
		if anchor {
			break
		}
	}
done:
	if !changed && c.Value(0).isString() {
		return c.ReturnValues(c.Value(0), Int(n)) // the original string, as C Lua returns it
	}
	b.WriteString(src[s:])
	if err := charge.done(b.Len()); err != nil {
		return err
	}
	return c.ReturnValues(String(b.String()), Int(n))
}

// addValue adds the replacement for the match from s to e, charging a string's as each
// capture is written: %0 over and over writes far more than the match.
func addValue(c *Call, ms *matchState, b *strings.Builder, charge *building, s, e int, repl Value) (changed bool, err error) {
	var v Value
	switch {
	case repl.isString() || repl.isNumber():
		r := repl.String()
		for i := 0; i < len(r); i++ {
			ch := r[i]
			if ch != luaEsc {
				b.WriteByte(ch)
				continue
			}
			i++
			if i >= len(r) {
				return false, c.libErrorf("invalid use of '%%' in replacement string")
			}
			switch d := r[i]; {
			case d == luaEsc:
				b.WriteByte(luaEsc)
			case d >= '0' && d <= '9':
				var cv Value
				if d == '0' {
					cv = subString(String(ms.src), s, e)
				} else {
					cv = ms.getCapture(int(d-'1'), s, e)
					if ms.err != nil {
						return false, ms.err
					}
				}
				b.WriteString(cv.String())
				if err := charge.grew(b.Len()); err != nil {
					return false, err
				}
			default:
				return false, c.libErrorf("invalid use of '%%' in replacement string")
			}
		}
		return true, nil
	case repl.isObj(kindTable):
		k := ms.getCapture(0, s, e)
		if ms.err != nil {
			return false, ms.err
		}
		if v, err = c.index(repl, k); err != nil {
			return false, err
		}
	default:
		caps := ms.captures(s, e, true)
		if ms.err != nil {
			return false, ms.err
		}
		var err error
		if v, err = c.call1(repl, caps...); err != nil {
			return false, err
		}
	}
	switch {
	case !v.Truthy():
		b.WriteString(ms.src[s:e]) // keep the original text
		return false, nil
	case v.isString() || v.isNumber():
		b.WriteString(v.String())
	default:
		return false, c.libErrorf("invalid replacement value (a %s)", typeName(v))
	}
	return true, nil
}

// string.format

const (
	fmtFlagsF = "-+ #0"
	fmtFlagsX = "-#0"
	fmtFlagsI = "-+ 0"
	fmtFlagsU = "-0"
	fmtFlagsC = "-"
)

// maxFormat is C Lua's MAX_FORMAT, the room for one conversion specification.
const maxFormat = 32

func strFormat(c *Call) error {
	f, err := c.checkString(0, "format")
	if err != nil {
		return err
	}
	var b strings.Builder
	charge := building{c: c}
	arg := 0
	for i := 0; i < len(f); i++ {
		if f[i] != '%' {
			b.WriteByte(f[i])
			continue
		}
		i++
		if i < len(f) && f[i] == '%' {
			b.WriteByte('%')
			continue
		}
		arg++
		if arg >= c.Len() { // as C Lua, before looking at the conversion
			return c.argError(arg+1, "format", "no value")
		}
		// the spec: flags, width and precision, up to the conversion character, spanned as
		// C Lua's getformat does; checkSpec then checks their order for the conversion
		start := i
		for i < len(f) && strings.IndexByte("-+#0 123456789.", f[i]) >= 0 {
			i++
		}
		if i-start+1 >= maxFormat-10 {
			return c.libErrorf("invalid format (too long)")
		}
		if i >= len(f) {
			return c.libErrorf("invalid conversion '%%%s' to 'format'", f[start:])
		}
		spec, conv := f[start:i], f[i]
		v := c.Value(arg)
		checkSpec := func(flags string, precision bool) error {
			j := 0
			for j < len(spec) && strings.IndexByte(flags, spec[j]) >= 0 {
				j++
			}
			digits := func() {
				for k := 0; k < 2 && j < len(spec) && spec[j] >= '0' && spec[j] <= '9'; k++ {
					j++
				}
			}
			if j >= len(spec) || spec[j] != '0' { // a width cannot start with '0'
				digits()
				if j < len(spec) && spec[j] == '.' && precision {
					j++
					digits()
				}
			}
			if j != len(spec) {
				return c.libErrorf("invalid conversion specification: '%%%s'", spec+string(conv))
			}
			return nil
		}
		switch conv {
		case 'c':
			if err := checkSpec(fmtFlagsC, false); err != nil {
				return err
			}
			n, err := c.checkInt(arg, "format")
			if err != nil {
				return err
			}
			b.WriteString(pad(spec, string([]byte{byte(n)})))
		case 'd', 'i', 'u', 'o', 'x', 'X':
			flags := fmtFlagsI
			switch conv {
			case 'u':
				flags = fmtFlagsU
			case 'o', 'x', 'X':
				flags = fmtFlagsX
			}
			n, err := c.checkInt(arg, "format")
			if err != nil {
				return err
			}
			if err := checkSpec(flags, true); err != nil {
				return err
			}
			b.WriteString(formatIntC(spec, conv, n))
		case 'a', 'A', 'e', 'E', 'f', 'g', 'G':
			// as C Lua 5.4.9's str_format: %a checks the spec before the argument, the others after
			if conv == 'a' || conv == 'A' {
				if err := checkSpec(fmtFlagsF, true); err != nil {
					return err
				}
			}
			x, err := c.checkFloat(arg, "format")
			if err != nil {
				return err
			}
			if err := checkSpec(fmtFlagsF, true); err != nil {
				return err
			}
			b.WriteString(formatFloatC(spec, conv, x))
		case 'p':
			if err := checkSpec(fmtFlagsC, false); err != nil {
				return err
			}
			s := "(null)"
			if !isScalar(v.p) {
				s = hidePointer(v.p)
			}
			b.WriteString(pad(spec, s))
		case 'q':
			if spec != "" {
				return c.libErrorf("specifier '%%q' cannot have modifiers")
			}
			q, err := quoteValue(c, v, arg)
			if err != nil {
				return err
			}
			b.WriteString(q)
		case 's':
			s, err := c.tostring(v)
			if err != nil {
				return err
			}
			if spec == "" {
				b.WriteString(s)
				break
			}
			if strings.IndexByte(s, 0) >= 0 {
				return c.argError(arg+1, "format", "string contains zeros")
			}
			if err := checkSpec(fmtFlagsC, true); err != nil {
				return err
			}
			if dot := strings.IndexByte(spec, '.'); dot >= 0 {
				prec, _ := strconv.Atoi(spec[dot+1:])
				if prec < len(s) {
					s = s[:prec] // bytes, as C counts them
				}
				spec = spec[:dot]
			}
			b.WriteString(pad(spec, s))
		default:
			// the specification with its conversion, as C's form buffer: a C string, so up to a NUL
			shown, _, _ := strings.Cut(f[start:i+1], "\x00")
			return c.libErrorf("invalid conversion '%%%s' to 'format'", shown)
		}
		if err := charge.grew(b.Len()); err != nil {
			return err
		}
	}
	if err := charge.done(b.Len()); err != nil {
		return err
	}
	return c.ReturnValues(String(b.String()))
}

// pad applies the width and '-' flag of spec to s.
func pad(spec, s string) string {
	left := strings.Contains(spec, "-")
	width, _, _ := strings.Cut(strings.TrimLeft(spec, "-+ #0"), ".") // the precision does not pad
	w, _ := strconv.Atoi(width)
	if len(s) >= w {
		return s
	}
	fill := strings.Repeat(" ", w-len(s))
	if left {
		return s + fill
	}
	return fill + s
}

// formatIntC formats n as C's printf formats an integer conversion: d and i signed, u, o, x
// and X unsigned. Go's fmt differs at the edges: it drops the sign of a zero printed with
// precision 0, gives # a 0x prefix for zero, and counts the prefix out of the zero padding.
func formatIntC(spec string, conv byte, n int64) string {
	flags := spec[:len(spec)-len(strings.TrimLeft(spec, "-+ #0"))]
	width, precision, hasPrec := strings.Cut(spec[len(flags):], ".")
	w, _ := strconv.Atoi(width)
	prec, _ := strconv.Atoi(precision)
	u, sign := uint64(n), ""
	if conv == 'd' || conv == 'i' {
		switch {
		case n < 0:
			u, sign = -u, "-" // minint's magnitude, as an unsigned
		case strings.Contains(flags, "+"):
			sign = "+"
		case strings.Contains(flags, " "):
			sign = " "
		}
	}
	base := 10
	switch conv {
	case 'o':
		base = 8
	case 'x', 'X':
		base = 16
	}
	digits := strconv.FormatUint(u, base)
	if conv == 'X' {
		digits = strings.ToUpper(digits)
	}
	if hasPrec {
		if prec == 0 && u == 0 {
			digits = "" // C: precision 0 prints no digits for zero
		}
		if len(digits) < prec {
			digits = strings.Repeat("0", prec-len(digits)) + digits
		}
	}
	prefix := ""
	if strings.Contains(flags, "#") {
		switch {
		case conv == 'o' && !strings.HasPrefix(digits, "0"):
			digits = "0" + digits
		case conv == 'x' && u != 0:
			prefix = "0x"
		case conv == 'X' && u != 0:
			prefix = "0X"
		}
	}
	size := len(sign) + len(prefix) + len(digits)
	switch {
	case size >= w:
		return sign + prefix + digits
	case strings.Contains(flags, "-"):
		return sign + prefix + digits + strings.Repeat(" ", w-size)
	case strings.Contains(flags, "0") && !hasPrec:
		return sign + prefix + strings.Repeat("0", w-size) + digits
	}
	return strings.Repeat(" ", w-size) + sign + prefix + digits
}

// formatFloatC formats x like C's printf with the given spec and conversion: Go's fmt
// does most of it, but not inf, nan or %a in C's form.
func formatFloatC(spec string, conv byte, x float64) string {
	upper := conv >= 'A' && conv <= 'Z'
	if math.IsInf(x, 0) || math.IsNaN(x) {
		s := "inf"
		if math.IsNaN(x) {
			s = "nan"
		}
		sign := ""
		switch {
		case math.Signbit(x):
			sign = "-"
		case strings.Contains(spec, "+"):
			sign = "+"
		case strings.Contains(spec, " "):
			sign = " "
		}
		s = sign + s
		if upper {
			s = strings.ToUpper(s)
		}
		return pad(spec, s) // pad fills with spaces: the 0 flag does not apply to inf and nan
	}
	if conv == 'a' || conv == 'A' {
		return hexFloat(spec, x, upper)
	}
	if (conv == 'g' || conv == 'G') && !strings.Contains(spec, ".") {
		spec += ".6" // C's default precision; Go's %g would give the shortest form instead
	}
	return fmt.Sprintf("%"+spec+string(conv), x)
}

// hexFloat formats x as glibc's printf formats %a, which is what C Lua gives on Linux: the
// leading digit is 1, or 0 for zero and subnormals, which keep the exponent -1022; rounding to
// the precision is half to even, and a carry goes into the leading digit (0x2.0p+5) rather than
// the exponent; # keeps the point, and the 0 flag pads after the 0x. The result is padded to
// the width of spec.
func hexFloat(spec string, x float64, upper bool) string {
	flags := spec[:len(spec)-len(strings.TrimLeft(spec, "-+ #0"))]
	prec := -1
	if dot := strings.IndexByte(spec, '.'); dot >= 0 {
		prec, _ = strconv.Atoi(spec[dot+1:])
	}
	bits := math.Float64bits(x)
	biased, mant := int(bits>>52&0x7ff), bits&(1<<52-1)
	lead, exp := 1, biased-1023
	if biased == 0 {
		lead, exp = 0, -1022
		if mant == 0 {
			exp = 0
		}
	}
	digits := []byte(fmt.Sprintf("%013x", mant))
	switch {
	case prec < 0:
		digits = bytes.TrimRight(digits, "0")
	case prec < len(digits):
		rest := digits[prec:]
		digits = digits[:prec]
		odd := lead&1 == 1
		if prec > 0 {
			odd = hexVal(digits[prec-1])&1 == 1
		}
		more := len(bytes.TrimRight(rest[1:], "0")) > 0
		if h := hexVal(rest[0]); h > 8 || h == 8 && (more || odd) {
			carry := true
			for i := prec - 1; i >= 0 && carry; i-- {
				if digits[i] == 'f' {
					digits[i] = '0'
				} else {
					digits[i] = "0123456789abcdef"[hexVal(digits[i])+1]
					carry = false
				}
			}
			if carry {
				lead++
			}
		}
	default:
		digits = append(digits, bytes.Repeat([]byte("0"), prec-len(digits))...)
	}
	sign := ""
	switch {
	case bits>>63 != 0:
		sign = "-"
	case strings.Contains(flags, "+"):
		sign = "+"
	case strings.Contains(flags, " "):
		sign = " "
	}
	body := strconv.Itoa(lead)
	if len(digits) > 0 || strings.Contains(flags, "#") {
		body += "."
	}
	body += string(digits) + "p"
	if exp >= 0 {
		body += "+"
	}
	body += strconv.Itoa(exp)
	prefix := "0x"
	if upper {
		prefix, body = "0X", strings.ToUpper(body)
	}
	width, _, _ := strings.Cut(strings.TrimLeft(spec, "-+ #0"), ".")
	w, _ := strconv.Atoi(width)
	n := len(sign) + len(prefix) + len(body)
	switch {
	case n >= w:
		return sign + prefix + body
	case strings.Contains(flags, "-"):
		return sign + prefix + body + strings.Repeat(" ", w-n)
	case strings.Contains(flags, "0"):
		return sign + prefix + strings.Repeat("0", w-n) + body
	}
	return strings.Repeat(" ", w-n) + sign + prefix + body
}

func hexVal(c byte) int {
	if c >= 'a' {
		return int(c-'a') + 10
	}
	return int(c - '0')
}

// quoteValue is %q: a value written so that Lua reads it back.
func quoteValue(c *Call, v Value, arg int) (string, error) {
	switch {
	case v.isString():
		s := v.str()
		var b strings.Builder
		b.WriteByte('"')
		for i := 0; i < len(s); i++ {
			ch := s[i]
			switch {
			case ch == '"' || ch == '\\' || ch == '\n':
				b.WriteByte('\\')
				b.WriteByte(ch)
			case ch == 0:
				if i+1 < len(s) && s[i+1] >= '0' && s[i+1] <= '9' {
					b.WriteString("\\000")
				} else {
					b.WriteString("\\0")
				}
			case ch < 32 || ch == 127:
				if i+1 < len(s) && s[i+1] >= '0' && s[i+1] <= '9' {
					fmt.Fprintf(&b, "\\%03d", ch)
				} else {
					fmt.Fprintf(&b, "\\%d", ch)
				}
			default:
				b.WriteByte(ch)
			}
		}
		b.WriteByte('"')
		return b.String(), nil
	case v.p == tInt():
		n := int64(v.n)
		if n == math.MinInt64 {
			return "0x8000000000000000", nil
		}
		return strconv.FormatInt(n, 10), nil
	case v.p == tFloat():
		x := math.Float64frombits(v.n)
		switch {
		case math.IsInf(x, 1):
			return "1e9999", nil
		case math.IsInf(x, -1):
			return "-1e9999", nil
		case x != x:
			return "(0/0)", nil
		}
		return hexFloat("", x, false), nil // hexadecimal, so it reads back exactly
	case v.IsNil(), v.p == tBool():
		return v.String(), nil
	}
	return "", c.argError(arg+1, "format", "value has no literal form")
}
