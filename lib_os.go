package glua

import (
	"fmt"
	"math"
	"strconv"
	"strings"
	"time"
)

// The os library of LibOS, after C Lua 5.4's loslib.c, with only clock, time, date and
// difftime. Time comes from the Runtime's Clock; os.clock is the time since the Runtime was
// made, not processor time, which a shared process cannot attribute to one script. Dates use
// the local time zone, or UTC with a leading '!', in the C locale.

func openOS(g *Table) {
	g.Set(String("os"), tableValue(newLib("os", map[string]GoFunc{
		"clock": osClock, "time": osTime, "date": osDate, "difftime": osDifftime,
	})))
}

// now returns the current time from the Runtime's Clock.
func (c *Call) now() time.Time {
	if rt := c.ex.rt; rt != nil {
		return rt.clock()
	}
	return time.Now()
}

func osClock(c *Call) error {
	start := time.Time{}
	if rt := c.ex.rt; rt != nil {
		start = rt.started
	}
	return c.ReturnValues(Float(c.now().Sub(start).Seconds()))
}

func osDifftime(c *Call) error {
	t2, err := c.checkInt(0, "difftime")
	if err != nil {
		return err
	}
	t1, err := c.checkInt(1, "difftime")
	if err != nil {
		return err
	}
	return c.ReturnValues(Float(float64(t2) - float64(t1)))
}

func osTime(c *Call) error {
	if c.Value(0).IsNil() {
		return c.ReturnValues(Int(c.now().Unix()))
	}
	t, err := c.checkTable(0, "time")
	if err != nil {
		return err
	}
	field := func(key string, def int64, delta int64) (int64, error) {
		v, err := c.index(tableValue(t), String(key))
		if err != nil {
			return 0, err
		}
		if v.IsNil() {
			if def < 0 {
				return 0, c.libErrorf("field '%s' missing in date table", key)
			}
			return def, nil
		}
		n, ok := v.Int()
		if s, isStr := v.Str(); !ok && isStr { // as C Lua's lua_tointegerx: a numeric string converts
			if nv, isNum := strToNumber(s); isNum {
				n, ok = nv.Int()
			}
		}
		if !ok {
			return 0, c.libErrorf("field '%s' is not an integer", key)
		}
		// as C Lua: the field, less delta, must fit a C int
		if n-delta < math.MinInt32 || n-delta > math.MaxInt32 {
			return 0, c.libErrorf("field '%s' is out-of-bound", key)
		}
		return n, nil
	}
	year, err := field("year", -1, 1900)
	if err != nil {
		return err
	}
	month, err := field("month", -1, 1)
	if err != nil {
		return err
	}
	day, err := field("day", -1, 0)
	if err != nil {
		return err
	}
	hour, err := field("hour", 12, 0)
	if err != nil {
		return err
	}
	minute, err := field("min", 0, 0)
	if err != nil {
		return err
	}
	sec, err := field("sec", 0, 0)
	if err != nil {
		return err
	}
	tm := time.Date(int(year), time.Month(month), int(day), int(hour), int(minute), int(sec), 0, time.Local)
	if tm.Year() < -10000000 || tm.Year() > 10000000 {
		return c.libErrorf("time result cannot be represented in this installation")
	}
	// as C Lua's mktime: the table is updated with the normalised fields
	setDateFields(t, tm)
	return c.ReturnValues(Int(tm.Unix()))
}

// setDateFields fills t with the fields of tm, as os.date("*t") gives them.
func setDateFields(t *Table, tm time.Time) {
	t.Set(String("year"), Int(int64(tm.Year())))
	t.Set(String("month"), Int(int64(tm.Month())))
	t.Set(String("day"), Int(int64(tm.Day())))
	t.Set(String("hour"), Int(int64(tm.Hour())))
	t.Set(String("min"), Int(int64(tm.Minute())))
	t.Set(String("sec"), Int(int64(tm.Second())))
	t.Set(String("yday"), Int(int64(tm.YearDay())))
	t.Set(String("wday"), Int(int64(tm.Weekday())+1))
	t.Set(String("isdst"), Bool(tm.IsDST()))
}

// dateConversions are the strftime conversions C Lua 5.4 accepts with C99: one letter, or
// E or O and a letter.
const (
	dateSingle = "aAbBcCdDeFgGhHIjmMnprRStTuUVwWxXyYzZ%"
	dateE      = "cCxXyY"
	dateO      = "deHImMSuUVwWy"
)

func osDate(c *Call) error {
	format, err := c.optString(0, "date", "%c")
	if err != nil {
		return err
	}
	tm := c.now()
	if v := c.Value(1); !v.IsNil() {
		secs, err := c.checkInt(1, "date")
		if err != nil {
			return err
		}
		tm = time.Unix(secs, 0)
	}
	if strings.HasPrefix(format, "!") {
		format = format[1:]
		tm = tm.UTC()
	} else {
		tm = tm.Local()
	}
	if y := int64(tm.Year()) - 1900; y < math.MinInt32 || y > math.MaxInt32 { // C's struct tm has an int year
		return c.libErrorf("date result cannot be represented in this installation")
	}
	if cstr, _, _ := strings.Cut(format, "\x00"); cstr == "*t" { // as C Lua's strcmp: "*t" alone, to a NUL
		t := NewTable(0, 9)
		setDateFields(t, tm)
		return c.ReturnValues(tableValue(t))
	}
	var b strings.Builder
	charge := building{c: c}
	for i := 0; i < len(format); i++ {
		if format[i] != '%' {
			b.WriteByte(format[i])
			continue
		}
		i++
		if i >= len(format) {
			return c.argError(1, "date", "invalid conversion specifier '%'")
		}
		conv := format[i]
		switch {
		case (conv == 'E' || conv == 'O') && i+1 < len(format) &&
			strings.IndexByte(map[byte]string{'E': dateE, 'O': dateO}[conv], format[i+1]) >= 0:
			i++
			conv = format[i] // the C locale has no alternative forms
		case strings.IndexByte(dateSingle, conv) < 0 || conv == 'E' || conv == 'O':
			// as C Lua: the message quotes the rest of the format from the bad conversion, to a NUL
			rest, _, _ := strings.Cut(format[i:], "\x00")
			return c.argError(1, "date", fmt.Sprintf("invalid conversion specifier '%%%s'", rest))
		}
		strftime(&b, conv, tm)
		if err := charge.grew(b.Len()); err != nil {
			return err
		}
	}
	if err := charge.done(b.Len()); err != nil {
		return err
	}
	return c.ReturnValues(String(b.String()))
}

// strftime writes the conversion conv of tm, in the C locale.
func strftime(b *strings.Builder, conv byte, tm time.Time) {
	pad := func(n, width int, fill byte) {
		s := strconv.Itoa(n)
		for len(s) < width {
			s = string(fill) + s
		}
		b.WriteString(s)
	}
	switch conv {
	case 'a':
		b.WriteString(tm.Weekday().String()[:3])
	case 'A':
		b.WriteString(tm.Weekday().String())
	case 'b', 'h':
		b.WriteString(tm.Month().String()[:3])
	case 'B':
		b.WriteString(tm.Month().String())
	case 'c':
		strftime(b, 'a', tm)
		b.WriteByte(' ')
		strftime(b, 'b', tm)
		b.WriteByte(' ')
		strftime(b, 'e', tm)
		b.WriteByte(' ')
		strftime(b, 'T', tm)
		b.WriteByte(' ')
		strftime(b, 'Y', tm)
	case 'C':
		pad(tm.Year()/100, 2, '0')
	case 'd':
		pad(tm.Day(), 2, '0')
	case 'D', 'x':
		strftime(b, 'm', tm)
		b.WriteByte('/')
		strftime(b, 'd', tm)
		b.WriteByte('/')
		strftime(b, 'y', tm)
	case 'e':
		pad(tm.Day(), 2, ' ')
	case 'F':
		strftime(b, 'Y', tm)
		b.WriteByte('-')
		strftime(b, 'm', tm)
		b.WriteByte('-')
		strftime(b, 'd', tm)
	case 'g':
		y, _ := tm.ISOWeek()
		pad(y%100, 2, '0')
	case 'G':
		y, _ := tm.ISOWeek()
		pad(y, 1, '0')
	case 'H':
		pad(tm.Hour(), 2, '0')
	case 'I':
		h := tm.Hour() % 12
		if h == 0 {
			h = 12
		}
		pad(h, 2, '0')
	case 'j':
		pad(tm.YearDay(), 3, '0')
	case 'm':
		pad(int(tm.Month()), 2, '0')
	case 'M':
		pad(tm.Minute(), 2, '0')
	case 'n':
		b.WriteByte('\n')
	case 'p':
		if tm.Hour() < 12 {
			b.WriteString("AM")
		} else {
			b.WriteString("PM")
		}
	case 'r':
		strftime(b, 'I', tm)
		b.WriteByte(':')
		strftime(b, 'M', tm)
		b.WriteByte(':')
		strftime(b, 'S', tm)
		b.WriteByte(' ')
		strftime(b, 'p', tm)
	case 'R':
		strftime(b, 'H', tm)
		b.WriteByte(':')
		strftime(b, 'M', tm)
	case 'S':
		pad(tm.Second(), 2, '0')
	case 't':
		b.WriteByte('\t')
	case 'T', 'X':
		strftime(b, 'H', tm)
		b.WriteByte(':')
		strftime(b, 'M', tm)
		b.WriteByte(':')
		strftime(b, 'S', tm)
	case 'u':
		wd := int(tm.Weekday())
		if wd == 0 {
			wd = 7
		}
		pad(wd, 1, '0')
	case 'U': // week of the year, Sunday first
		pad((tm.YearDay()+6-int(tm.Weekday()))/7, 2, '0')
	case 'V':
		_, w := tm.ISOWeek()
		pad(w, 2, '0')
	case 'w':
		pad(int(tm.Weekday()), 1, '0')
	case 'W': // week of the year, Monday first
		pad((tm.YearDay()+6-(int(tm.Weekday())+6)%7)/7, 2, '0')
	case 'y':
		pad(tm.Year()%100, 2, '0')
	case 'Y':
		pad(tm.Year(), 1, '0')
	case 'z':
		_, off := tm.Zone()
		sign := byte('+')
		if off < 0 {
			sign, off = '-', -off
		}
		b.WriteByte(sign)
		pad(off/3600, 2, '0')
		pad(off%3600/60, 2, '0')
	case 'Z':
		name, _ := tm.Zone()
		b.WriteString(name)
	case '%':
		b.WriteByte('%')
	}
}
