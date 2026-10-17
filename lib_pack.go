package glua

import (
	"encoding/binary"
	"math"
	"strings"
)

// string.pack, string.unpack and string.packsize, after C Lua 5.4's lstrlib.c, for a 64-bit
// machine: int is 4 bytes, long, size_t and lua_Integer 8, and the maximum alignment 8.

// nativeLittle reports whether this machine is little-endian, what '=' selects.
var nativeLittle = binary.NativeEndian.Uint16([]byte{1, 0}) == 1

const (
	packMaxIntSize = 16
	packSzInt      = 8             // sizeof(lua_Integer)
	packMaxAlign   = 8             // offsetof(struct cD, u)
	packMaxSize    = math.MaxInt32 // MAXSIZE, INT_MAX where size_t is wider than int
	packNumLimit   = (math.MaxInt32 - 9) / 10
)

type packOpt uint8

// The options that take a value come before kPadding.
const (
	kInt packOpt = iota
	kUint
	kFloat
	kNumber
	kDouble
	kChar
	kString
	kZstr
	kPadding
	kPaddAlign
	kNop
)

// packHeader is the state of a format being read: endianness and maximum alignment.
type packHeader struct {
	c        *Call
	fmt      string
	pos      int
	little   bool
	maxalign int
}

func newPackHeader(c *Call, format string) *packHeader {
	return &packHeader{c: c, fmt: format, little: nativeLittle, maxalign: 1}
}

// fail is luaL_error, raised by panic and recovered by the caller.
type packError struct{ err error }

func (h *packHeader) fail(err error) { panic(packError{err}) }

func (h *packHeader) digit() bool {
	return h.pos < len(h.fmt) && h.fmt[h.pos] >= '0' && h.fmt[h.pos] <= '9'
}

func (h *packHeader) getnum(df int) int {
	if !h.digit() {
		return df
	}
	a := 0
	for {
		a = a*10 + int(h.fmt[h.pos]-'0')
		h.pos++
		if !h.digit() || a > packNumLimit {
			return a
		}
	}
}

func (h *packHeader) getnumlimit(df int) int {
	sz := h.getnum(df)
	if sz > packMaxIntSize || sz <= 0 {
		h.fail(h.c.libErrorf("integral size (%d) out of limits [1,%d]", sz, packMaxIntSize))
	}
	return sz
}

func (h *packHeader) getoption() (packOpt, int) {
	opt := h.fmt[h.pos]
	h.pos++
	switch opt {
	case 'b':
		return kInt, 1
	case 'B':
		return kUint, 1
	case 'h':
		return kInt, 2
	case 'H':
		return kUint, 2
	case 'l', 'j':
		return kInt, 8
	case 'L', 'J', 'T':
		return kUint, 8
	case 'f':
		return kFloat, 4
	case 'n':
		return kNumber, 8
	case 'd':
		return kDouble, 8
	case 'i':
		return kInt, h.getnumlimit(4)
	case 'I':
		return kUint, h.getnumlimit(4)
	case 's':
		return kString, h.getnumlimit(8)
	case 'c':
		size := h.getnum(-1)
		if size == -1 {
			h.fail(h.c.libErrorf("missing size for format option 'c'"))
		}
		return kChar, size
	case 'z':
		return kZstr, 0
	case 'x':
		return kPadding, 1
	case 'X':
		return kPaddAlign, 0
	case ' ':
	case '<':
		h.little = true
	case '=':
		h.little = nativeLittle
	case '>':
		h.little = false
	case '!':
		h.maxalign = h.getnumlimit(packMaxAlign)
	default:
		h.fail(h.c.libErrorf("invalid format option '%c'", opt))
	}
	return kNop, 0
}

// details reads the next option and the padding that aligns it at totalsize.
func (h *packHeader) details(totalsize int) (opt packOpt, size, ntoalign int) {
	opt, size = h.getoption()
	align := size
	if opt == kPaddAlign {
		if h.pos >= len(h.fmt) {
			h.fail(h.c.argError(1, "pack", "invalid next option for option 'X'"))
		}
		var next packOpt
		if next, align = h.getoption(); next == kChar || align == 0 {
			h.fail(h.c.argError(1, "pack", "invalid next option for option 'X'"))
		}
	}
	if align <= 1 || opt == kChar {
		return opt, size, 0
	}
	align = min(align, h.maxalign)
	if align&(align-1) != 0 {
		h.fail(h.c.argError(1, "pack", "format asks for alignment not power of 2"))
	}
	return opt, size, (align - totalsize&(align-1)) & (align - 1)
}

// recoverPack turns a packError panic into the function's error.
func recoverPack(err *error) {
	if r := recover(); r != nil {
		pe, ok := r.(packError)
		if !ok {
			panic(r)
		}
		*err = pe.err
	}
}

// packInt appends n in size bytes.
func packInt(b []byte, n uint64, little bool, size int, neg bool) []byte {
	buf := make([]byte, size)
	for i := range size {
		var byt byte
		if i < 8 {
			byt = byte(n >> (8 * i))
		} else if neg {
			byt = 0xff // sign extension past a Lua integer
		}
		if little {
			buf[i] = byt
		} else {
			buf[size-1-i] = byt
		}
	}
	return append(b, buf...)
}

func withEndian(raw []byte, little bool) []byte {
	if !little {
		for i, j := 0, len(raw)-1; i < j; i, j = i+1, j-1 {
			raw[i], raw[j] = raw[j], raw[i]
		}
	}
	return raw
}

func strPack(c *Call) (err error) {
	defer recoverPack(&err)
	format, err := c.checkString(0, "pack")
	if err != nil {
		return err
	}
	h := newPackHeader(c, format)
	var b []byte
	charge := building{c: c}
	arg, totalsize := 0, 0
	for h.pos < len(h.fmt) {
		opt, size, ntoalign := h.details(totalsize)
		totalsize += ntoalign + size
		for range ntoalign {
			b = append(b, 0)
		}
		arg++
		if arg == c.Len() && opt < kPadding { // C Lua marks the end of the arguments with a nil
			want := "number"
			if opt == kChar || opt == kString || opt == kZstr {
				want = "string"
			}
			return c.argError(arg+1, "pack", want+" expected, got nil")
		}
		switch opt {
		case kInt:
			n, err := c.checkInt(arg, "pack")
			if err != nil {
				return err
			}
			if size < packSzInt {
				lim := int64(1) << (size*8 - 1)
				if !(-lim <= n && n < lim) {
					return c.argError(arg+1, "pack", "integer overflow")
				}
			}
			b = packInt(b, uint64(n), h.little, size, n < 0)
		case kUint:
			n, err := c.checkInt(arg, "pack")
			if err != nil {
				return err
			}
			if size < packSzInt && uint64(n) >= uint64(1)<<(size*8) {
				return c.argError(arg+1, "pack", "unsigned overflow")
			}
			b = packInt(b, uint64(n), h.little, size, false)
		case kFloat:
			f, err := c.checkFloat(arg, "pack")
			if err != nil {
				return err
			}
			b = append(b, withEndian(packInt(nil, uint64(math.Float32bits(float32(f))), true, 4, false), h.little)...)
		case kNumber, kDouble:
			f, err := c.checkFloat(arg, "pack")
			if err != nil {
				return err
			}
			b = append(b, withEndian(packInt(nil, math.Float64bits(f), true, 8, false), h.little)...)
		case kChar:
			s, err := c.checkString(arg, "pack")
			if err != nil {
				return err
			}
			if len(s) > size {
				return c.argError(arg+1, "pack", "string longer than given size")
			}
			if err := charge.grew(len(b) + size); err != nil { // charged before, as string.rep
				return err
			}
			b = append(append(b, s...), make([]byte, size-len(s))...)
		case kString:
			s, err := c.checkString(arg, "pack")
			if err != nil {
				return err
			}
			if size < 8 && uint64(len(s)) >= uint64(1)<<(size*8) {
				return c.argError(arg+1, "pack", "string length does not fit in given size")
			}
			b = packInt(b, uint64(len(s)), h.little, size, false)
			b = append(b, s...)
			totalsize += len(s)
		case kZstr:
			s, err := c.checkString(arg, "pack")
			if err != nil {
				return err
			}
			if strings.IndexByte(s, 0) >= 0 {
				return c.argError(arg+1, "pack", "string contains zeros")
			}
			b = append(append(b, s...), 0)
			totalsize += len(s) + 1
		case kPadding:
			b = append(b, 0)
			arg--
		case kPaddAlign, kNop:
			arg--
		}
		if err := charge.grew(len(b)); err != nil {
			return err
		}
	}
	if err := charge.done(len(b)); err != nil {
		return err
	}
	return c.ReturnValues(String(string(b)))
}

func strPacksize(c *Call) (err error) {
	defer recoverPack(&err)
	format, err := c.checkString(0, "packsize")
	if err != nil {
		return err
	}
	h := newPackHeader(c, format)
	totalsize := 0
	for h.pos < len(h.fmt) {
		opt, size, ntoalign := h.details(totalsize)
		if opt == kString || opt == kZstr {
			return c.argError(1, "packsize", "variable-length format")
		}
		size += ntoalign
		if totalsize > packMaxSize-size {
			return c.argError(1, "packsize", "format result too large")
		}
		totalsize += size
	}
	return c.ReturnValues(Int(int64(totalsize)))
}

// unpackInt reads an integer of size bytes.
func (h *packHeader) unpackInt(s string, little bool, size int, signed bool) int64 {
	var res uint64
	limit := min(size, packSzInt)
	for i := limit - 1; i >= 0; i-- {
		res <<= 8
		if little {
			res |= uint64(s[i])
		} else {
			res |= uint64(s[size-1-i])
		}
	}
	if size < packSzInt {
		if signed {
			mask := uint64(1) << (size*8 - 1)
			res = (res ^ mask) - mask
		}
	} else if size > packSzInt {
		var mask byte
		if signed && int64(res) < 0 {
			mask = 0xff
		}
		for i := limit; i < size; i++ {
			at := i
			if !little {
				at = size - 1 - i
			}
			if s[at] != mask {
				h.fail(h.c.libErrorf("%d-byte integer does not fit into Lua Integer", size))
			}
		}
	}
	return int64(res)
}

func strUnpack(c *Call) (err error) {
	defer recoverPack(&err)
	format, err := c.checkString(0, "unpack")
	if err != nil {
		return err
	}
	data, err := c.checkString(1, "unpack")
	if err != nil {
		return err
	}
	init, err := c.optInt(2, "unpack", 1)
	if err != nil {
		return err
	}
	ld := len(data)
	pos := int(strStartI(init, ld)) - 1
	if pos > ld || pos < 0 {
		return c.argError(3, "unpack", "initial position out of string")
	}
	h := newPackHeader(c, format)
	var res []Value
	for h.pos < len(h.fmt) {
		opt, size, ntoalign := h.details(pos)
		if ntoalign+size > ld-pos {
			return c.argError(2, "unpack", "data string too short")
		}
		pos += ntoalign
		if err := c.ex.tick(); err != nil {
			return err
		}
		switch opt {
		case kInt, kUint:
			res = append(res, Int(h.unpackInt(data[pos:], h.little, size, opt == kInt)))
		case kFloat:
			raw := withEndian([]byte(data[pos:pos+4]), h.little)
			res = append(res, Float(float64(math.Float32frombits(uint32(h.unpackInt(string(raw), true, 4, false))))))
		case kNumber, kDouble:
			raw := withEndian([]byte(data[pos:pos+8]), h.little)
			res = append(res, Float(math.Float64frombits(uint64(h.unpackInt(string(raw), true, 8, false)))))
		case kChar:
			res = append(res, subString(c.Value(1), pos, pos+size))
		case kString:
			n := uint64(h.unpackInt(data[pos:], h.little, size, false))
			if n > uint64(ld-pos-size) {
				return c.argError(2, "unpack", "data string too short")
			}
			res = append(res, subString(c.Value(1), pos+size, pos+size+int(n)))
			pos += int(n)
		case kZstr:
			n := strings.IndexByte(data[pos:], 0)
			if n < 0 {
				return c.argError(2, "unpack", "unfinished string for format 'z'")
			}
			res = append(res, subString(c.Value(1), pos, pos+n))
			pos += n + 1
		}
		pos += size
	}
	return c.ReturnValues(append(res, Int(int64(pos)+1))...)
}

// strStartI is C Lua's posrelatI: a position counted from the end when negative, and at
// least 1.
func strStartI(pos int64, n int) int64 {
	switch {
	case pos > 0:
		return pos
	case pos == 0:
		return 1
	case pos < -int64(n):
		return 1
	}
	return int64(n) + pos + 1
}
