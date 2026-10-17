package glua

import (
	"context"
	"fmt"
	"unsafe"
)

// Protected calls. pcall and xpcall are built-in stubs: the function they call runs as an
// ordinary frame flagged catch, so the normal path needs no special case and nothing is
// added to the Go stack. An error unwinds to the nearest catch frame of the current run and
// becomes the results false, message. xpcall's handler runs on top of the failing frame,
// before anything is unwound, so it sees the whole stack.

var (
	builtinPcall  = &goFunc{name: "pcall", qualname: "pcall"}
	builtinXpcall = &goFunc{name: "xpcall", qualname: "xpcall"}
	builtinError  = &goFunc{name: "error", qualname: "error"}
)

func init() {
	builtinError.f = luaError
	builtinPcall.f = func(c *Call) error { return protectedSync(c, false) }
	builtinXpcall.f = func(c *Call) error { return protectedSync(c, true) }
}

// protectedSync is pcall or xpcall called from Go rather than by a CALL instruction, as in
// pcall(pcall, f) or as a metamethod: it runs the function in a nested run.
func protectedSync(c *Call, handler bool) error {
	ex := c.ex
	fi, first := 0, 1
	var h Value
	if handler {
		if h = c.Value(1); !h.isObj(kindLuaFn) && !h.isObj(kindGoFn) { // as luaL_checktype
			return c.typeArgError(1, "xpcall", "function")
		}
		first = 2
	} else if err := c.checkAny(0, "pcall"); err != nil {
		return err
	}
	f := c.Value(fi)
	args := make([]Value, 0, max(c.Len()-first, 0))
	for i := first; i < c.Len(); i++ {
		args = append(args, c.Value(i))
	}
	res, err := ex.callSync(f, args)
	if err != nil {
		le, ok := err.(*Error)
		if !ok || le.terminal {
			return err
		}
		v := le.Value
		if handler {
			if v, err = ex.callHandler(h, v); err != nil {
				if hl, ok := err.(*Error); ok && hl.terminal {
					return err
				}
				v = String(errorInErrorHandling)
			}
		}
		return c.ReturnValues(Bool(false), v)
	}
	return c.ReturnValues(append([]Value{Bool(true)}, res...)...)
}

// callSync calls f with args from Go code running on this executor and returns all results.
func (ex *executor) callSync(f Value, args []Value) ([]Value, error) {
	return ex.callSyncInto(nil, f, args)
}

// callSyncInto is callSync, appending the results to dst. A Lua function runs in a nested
// run, which counts as a host re-entry.
func (ex *executor) callSyncInto(dst []Value, f Value, args []Value) ([]Value, error) {
	slot, n, err := ex.callSyncAt(f, args)
	if err != nil {
		return nil, err
	}
	return append(dst, ex.stack[slot:slot+n]...), nil
}

// callSync1 is callSync for the first result only, without allocating.
func (ex *executor) callSync1(f Value, args []Value) (Value, error) {
	slot, n, err := ex.callSyncAt(f, args)
	if err != nil || n == 0 {
		return Value{}, err
	}
	return ex.stack[slot], nil
}

// callSyncAt calls f and leaves its n results at stack[slot:], above ex.top, which it puts
// back: the caller reads them at once, and the next call from the same Go function must
// not climb the stack. A panic passing through leaves the state as it is: the executor is
// never used again.
func (ex *executor) callSyncAt(f Value, args []Value) (slot, n int, err error) {
	st := &ex.st
	cl, base, pc, top := st.cl, st.base, st.pc, ex.top
	ex.nny++ // a nested run: it cannot yield
	slot, err = ex.callSyncBody(f, args, cl, base)
	st.cl, st.base, st.pc = cl, base, pc
	ex.nny--
	n = max(ex.top-slot, 0)
	ex.top = top
	return slot, n, err
}

func (ex *executor) callSyncBody(f Value, args []Value, cl *closure, base int) (int, error) {
	st := &ex.st
	slot := ex.top // a coroutine with a Go body has no Lua frame yet
	if cl != nil {
		slot = max(base+int(cl.p.maxstack), ex.top)
	}
	if d := ex.depth - 1; d >= 0 && d < len(ex.calls) {
		slot = max(slot, ex.calls[d].base+ex.calls[d].nargs) // above the calling Go function's arguments
	}
	for hops := 0; ; hops++ {
		if err := ex.ensure(slot + 1 + len(args) + stackSlack); err != nil {
			return 0, err
		}
		ex.stack[slot] = f
		copy(ex.stack[slot+1:], args)
		st.hi = max(st.hi, slot+1+len(args))
		var err error
		switch {
		case f.isObj(kindLuaFn):
			if ex.depth >= ex.maxHostDepth {
				return 0, ex.terminal(ErrHostDepth)
			}
			ex.depth++
			err = ex.run((*closure)(f.p), slot, len(args))
			ex.depth--
		case f.isObj(kindGoFn):
			var n int
			n, err = ex.callGoRaw((*goFunc)(f.p), slot, len(args))
			ex.top = slot + n
		default:
			h := ex.metamethod(f, "__call")
			if h.IsNil() || hops >= maxIndexHops {
				return 0, &Error{Value: String(fmt.Sprintf("attempt to call a %s value", typeName(f)))}
			}
			args = append([]Value{f}, args...)
			f = h
			continue
		}
		return slot, err
	}
}

// errorInErrorHandling is what an error inside an xpcall message handler turns into.
const errorInErrorHandling = "error in error handling"

// handlerFrames and handlerSlots are how far past the limits on frames and stack slots a
// message handler may go, so that it can handle a stack overflow.
const (
	handlerFrames = 200
	handlerSlots  = 200 * 64
)

// argErrorf is pcallValue's error for a bad argument: with the position of the Lua code
// that called pcall or xpcall, and none when pcall called it through the trampoline, as C
// Lua raises it in a function that C called.
func (ex *executor) argErrorf(format string, args ...any) error {
	if ex.st.cl != nil && ex.st.cl.p == trampoline.p {
		return &Error{Value: String(fmt.Sprintf(format, args...))}
	}
	return ex.errorf(format, args...)
}

// pcallValue does pcall(f, ...) or xpcall(f, h, ...) for the call at stack[fn] with nargs
// arguments. On success the results are true and f's results, at stack[fn].
func (ex *executor) pcallValue(g *goFunc, fn, nargs int) error {
	if g == builtinXpcall {
		if nargs < 2 {
			return ex.argErrorf("bad argument #2 to 'xpcall' (function expected, got no value)")
		}
		h := ex.stack[fn+2]
		if !h.isObj(kindLuaFn) && !h.isObj(kindGoFn) { // as luaL_checktype
			return ex.argErrorf("bad argument #2 to 'xpcall' (function expected, got %s)", typeName(h))
		}
		// keep the handler in xpcall's own slot, and move f down beside it
		copy(ex.stack[fn+2:fn+1+nargs], ex.stack[fn+3:fn+2+nargs])
		ex.stack[fn+1+nargs] = Value{}
		ex.stack[fn] = h
		nargs--
	} else if nargs < 1 {
		return ex.argErrorf("bad argument #1 to 'pcall' (value expected)")
	}
	slot, nargs := fn+1, nargs-1 // f and its arguments
	flags := uint64(frCatch)
	if g == builtinXpcall {
		flags |= frHandler
	}
	for hops := 0; ; hops++ {
		v := ex.stack[slot]
		switch {
		case v.isObj(kindLuaFn):
			return ex.pushLua((*closure)(v.p), slot, nargs, flags)
		case v.isObj(kindGoFn) && ((*goFunc)(v.p) == builtinPcall || (*goFunc)(v.p) == builtinXpcall):
			// a protected call of pcall: through the trampoline, a Lua frame for this catch
			// whose call of pcall pushes the inner one, so that both can yield
			if err := ex.ensure(slot + nargs + 2); err != nil {
				return err
			}
			copy(ex.stack[slot+1:slot+2+nargs], ex.stack[slot:slot+1+nargs])
			ex.stack[slot] = luaFnValue(trampoline)
			ex.st.hi = max(ex.st.hi, slot+2+nargs)
			return ex.pushLua(trampoline, slot, nargs+1, flags)
		case v.isObj(kindGoFn):
			n, err := ex.callGoRaw((*goFunc)(v.p), slot, nargs)
			if err == errYield && flags&frHandler == 0 {
				return ex.yieldedAt(slot, yieldPcall)
			}
			if err != nil {
				return ex.caughtNow(fn, flags, err)
			}
			ex.stack[fn] = Bool(true)
			ex.adjustResults(ex.instr(ex.st.pc-1), fn, n+1)
			return nil
		}
		h := ex.metamethod(v, "__call")
		if h.IsNil() || hops >= maxIndexHops {
			// called from pcall, a Go function: the message has no position, as in C Lua
			return ex.caughtNow(fn, flags, &Error{Value: String(fmt.Sprintf("attempt to call a %s value", typeName(v)))})
		}
		if err := ex.ensure(slot + nargs + 2); err != nil {
			return err
		}
		copy(ex.stack[slot+2:slot+2+nargs], ex.stack[slot+1:slot+1+nargs])
		ex.stack[slot+1], ex.stack[slot] = v, h
		nargs++
	}
}

// caughtNow finishes a protected call that failed before any frame was pushed: a Go
// function or a value that cannot be called.
func (ex *executor) caughtNow(fn int, flags uint64, err error) error {
	le, ok := err.(*Error)
	if !ok || le.terminal {
		return err
	}
	v := le.Value
	if flags&frHandler != 0 {
		r, herr := ex.callHandler(ex.stack[fn], v)
		if herr != nil {
			if hl, ok := herr.(*Error); ok && hl.terminal {
				return herr
			}
			r = String(errorInErrorHandling)
		}
		v = r
	}
	ex.stack[fn], ex.stack[fn+1] = Bool(false), v
	ex.adjustResults(ex.instr(ex.st.pc-1), fn, 2)
	return nil
}

// callHandler calls an xpcall message handler synchronously and returns its first result.
// It leaves ex.top as it found it: the handler's results are gone once the first is read.
func (ex *executor) callHandler(h, msg Value) (Value, error) {
	st := &ex.st
	cl, base, pc, top := st.cl, st.base, st.pc, ex.top
	defer func() { ex.top = top }()
	slot := max(base+int(cl.p.maxstack), ex.top)
	if err := ex.ensure(slot + 2 + stackSlack); err != nil {
		return Value{}, err
	}
	ex.stack[slot], ex.stack[slot+1] = h, msg
	st.hi = max(st.hi, slot+2)
	var err error
	ex.nny++ // a handler runs in a nested run: it cannot yield
	defer func() { ex.nny-- }()
	switch {
	case h.isObj(kindLuaFn):
		err = ex.run((*closure)(h.p), slot, 1)
	case h.isObj(kindGoFn):
		var n int
		n, err = ex.callGoRaw((*goFunc)(h.p), slot, 1)
		ex.top = slot + n
	default:
		err = &Error{Value: String(errorInErrorHandling)}
	}
	st.cl, st.base, st.pc = cl, base, pc
	if err != nil {
		return Value{}, err
	}
	if ex.top > slot {
		return ex.stack[slot], nil
	}
	return Value{}, nil
}

// unwind looks for a catch frame of the current run, above nf0, that stops err. If it finds
// one it either starts the xpcall handler or unwinds to it, and reports true; the driver
// then carries on. Terminal errors are never caught.
func (ex *executor) unwind(err error, nf0 int) error {
	le, ok := err.(*Error)
	if !ok || le.terminal {
		return err
	}
	st := &ex.st
	value := le.Value
	inHandler := false
	base := st.base
	for f := st.nf - 1; f > nf0; f-- {
		fr := ex.pframes[f]
		cl := (*closure)(ex.stack[base-1].p)
		if fr&frErrHandler != 0 {
			inHandler = true // an error inside a message handler
			value = String(errorInErrorHandling)
			ex.nny-- // the handler's frame goes as the unwinding passes it
		}
		if fr&frCatch != 0 {
			fn := ex.frameFuncSlot(f, base, cl) - 1 // pcall's slot, below the protected function
			if fr&frHandler != 0 && !inHandler {
				return ex.startHandler(f, fn, value)
			}
			return ex.unwindTo(f, base, fn, value)
		}
		base -= int(fr >> 32 & 0xffffff)
	}
	return err
}

// frameFuncSlot returns the stack index of frame f's function as its caller placed it.
func (ex *executor) frameFuncSlot(f, base int, cl *closure) int {
	if ex.pframes[f]&frVararg == 0 {
		return base - 1
	}
	return base - int(cl.p.nparams) - int(ex.nvar[f]) - 2
}

// unwindTo pops every frame down to and including catch frame f, whose base is base, and
// leaves false and value as the results of the pcall at stack[fn].
func (ex *executor) unwindTo(f, base, fn int, value Value) error {
	st := &ex.st
	if ex.errExtra > 0 && f < ex.maxCallDepth {
		ex.errExtra = 0
		ex.pframes = ex.pframes[:min(len(ex.pframes), ex.maxCallDepth)] // take back the handler's room
	}
	// pop the frames, then close their variables, as C Lua does: pcall calls the closers
	fr := ex.pframes[f]
	st.nf = f
	st.base = base - int(fr>>32&0xffffff)
	st.cl = (*closure)(ex.stack[st.base-1].p)
	st.pc = int(uint32(fr))
	value, err := ex.closeOnError(fn, value, false)
	if err != nil {
		return err // a terminal error while closing
	}
	ex.stack[fn], ex.stack[fn+1] = Bool(false), value
	ex.adjustResults(ex.instr(st.pc-1), fn, 2)
	return nil
}

// closeOnError calls the __close metamethods of the to-be-closed variables at stack index
// level and above, newest first, each with the error value. A closer that fails replaces
// the error for the closers after it and for the result, as in C Lua. The closers run
// synchronously, called by the current frame, or by Go code when goClose is set, and their
// calls go above the variables still to close.
func (ex *executor) closeOnError(level int, value Value, goClose bool) (Value, error) {
	if len(ex.tbc) == 0 || ex.tbc[len(ex.tbc)-1] < level {
		return value, nil
	}
	top, mark := ex.top, ex.st.goClose
	defer func() { ex.top, ex.st.goClose = top, mark }()
	ex.top = max(top, ex.tbc[len(ex.tbc)-1]+1)
	if ex.st.goClose = 0; goClose {
		ex.st.goClose = ex.st.nf + 1
	}
	for len(ex.tbc) > 0 && ex.tbc[len(ex.tbc)-1] >= level {
		r := ex.tbc[len(ex.tbc)-1]
		ex.tbc = ex.tbc[:len(ex.tbc)-1]
		v := ex.stack[r]
		h := ex.metamethod(v, "__close")
		var err error
		if !h.isObj(kindLuaFn) && !h.isObj(kindGoFn) && ex.metamethod(h, "__call").IsNil() {
			// C Lua names neither the position nor the metamethod here
			err = &Error{Value: String("attempt to call a " + typeName(h) + " value")}
		} else {
			_, err = ex.callSync(h, []Value{v, value})
		}
		if err != nil {
			le, ok := err.(*Error)
			if !ok || le.terminal {
				ex.dropTBC(level)
				return value, err
			}
			value = le.Value
		}
	}
	return value, nil
}

// closeTerminal runs the closers at level and above after a terminal error. Go closers
// always run. Lua closers share one grace budget of 1,024 steps and 4 KB; a second breach
// abandons the rest. The terminal error itself stands.
func (ex *executor) closeTerminal(level int, le *Error) {
	if len(ex.tbc) == 0 || ex.tbc[len(ex.tbc)-1] < level || ex.st.cl == nil {
		return
	}
	steps, ticks, alloc, fatal, fixed := ex.steps, ex.st.ticks, ex.allocLeft, ex.fatal, ex.fixed
	ex.steps, ex.st.ticks, ex.allocLeft, ex.fatal, ex.fixed = 0, tickQuantum, 4<<10, nil, true
	ctx, deadline := ex.ctx, ex.deadline
	if ctx.Err() != nil {
		ex.ctx = context.WithoutCancel(ctx) // let the closers run after a cancellation
	}
	ex.deadline = 0 // or after the time ran out: the grace budget bounds them
	ex.closeOnError(level, le.Value, true)
	ex.dropTBC(level)
	ex.ctx, ex.deadline = ctx, deadline
	ex.steps, ex.st.ticks, ex.allocLeft, ex.fatal, ex.fixed = steps, ticks, alloc, fatal, fixed
}

// dropTBC forgets the to-be-closed variables at stack index level and above.
func (ex *executor) dropTBC(level int) {
	for len(ex.tbc) > 0 && ex.tbc[len(ex.tbc)-1] >= level {
		ex.tbc = ex.tbc[:len(ex.tbc)-1]
	}
}

// startHandler calls the message handler of the xpcall whose catch frame is f, on top of
// the failing frame. A Lua handler runs as a frame flagged errHandler; when it returns,
// frameReturned unwinds to f with its result. A handler cannot yield, as in C Lua: a Lua one
// counts as a nested run until its frame goes.
func (ex *executor) startHandler(f, fn int, msg Value) error {
	h := ex.stack[fn]
	ex.errExtra = handlerFrames // room for the handler of a stack overflow; unwindTo takes it back
	if !h.isObj(kindLuaFn) {
		r, err := ex.callHandler(h, msg)
		if err != nil {
			if le, ok := err.(*Error); ok && le.terminal {
				return err
			}
			r = String(errorInErrorHandling)
		}
		return ex.unwindFrom(f, r)
	}
	st := &ex.st
	slot := max(st.base+int(st.cl.p.maxstack), ex.top)
	if err := ex.ensure(slot + 2 + stackSlack); err != nil {
		return err
	}
	ex.stack[slot], ex.stack[slot+1] = h, msg
	for len(ex.cont) <= st.nf {
		ex.cont = append(ex.cont, 0)
	}
	ex.cont[st.nf] = int32(f) // the catch frame to unwind to when the handler returns
	if err := ex.pushLua((*closure)(h.p), slot, 1, frErrHandler); err != nil {
		if le, ok := err.(*Error); ok && le.terminal {
			return err
		}
		return ex.unwindFrom(f, String(errorInErrorHandling))
	}
	ex.nny++
	return nil
}

// unwindFrom unwinds from the current frame to catch frame f with the result value.
func (ex *executor) unwindFrom(f int, value Value) error {
	st := &ex.st
	base := st.base
	for g := st.nf - 1; g > f; g-- {
		base -= int(ex.pframes[g] >> 32 & 0xffffff)
	}
	cl := (*closure)(ex.stack[base-1].p)
	return ex.unwindTo(f, base, ex.frameFuncSlot(f, base, cl)-1, value)
}

// luaError is the built-in error(message [, level]).
func luaError(c *Call) error {
	ex := c.ex
	msg := c.Value(0)
	n, err := c.optInt(1, "error", 1) // as luaL_optinteger: nil is 1, "2" is 2
	if err != nil {
		return err
	}
	level := int64(int32(n)) // as C Lua's (int) cast
	if msg.isString() && level > 0 {
		if pos := ex.whereLevel(c, int(level)); pos != "" {
			msg = String(pos + ": " + msg.str())
		}
	}
	le := &Error{Value: msg}
	if msg.isString() {
		le.cause = ex.goErrs[unsafe.Pointer(unsafe.StringData(msg.str()))] // raised again: the Go error
	}
	return le
}

// whereLevel returns the position of the function at the given level above the one that
// called error: 1 is the caller of error, 2 its caller. As C functions are in C Lua, a Go
// function is a level without a position: pcall or xpcall below a protected call, and the Go
// function below a nested run. The trampoline is no level of its own: the Go function it
// calls is.
func (ex *executor) whereLevel(c *Call, level int) string {
	st := &ex.st
	if !c.fromLua {
		level-- // error was called from pcall or another Go function: that is level 1
		if level == 0 {
			return ""
		}
	}
	cl, base, pc, nf := st.cl, st.base, st.pc, st.nf
	if cl != nil && cl.p == trampoline.p {
		level++ // the trampoline is no level: the Go function it runs is
	}
	for level > 1 {
		if nf == 0 {
			return ""
		}
		fr := ex.pframes[nf-1]
		if fr&(frCatch|frGoEntry) != 0 {
			if level--; level == 1 || uint32(fr) == 0 {
				return "" // the Go function that called this frame, or one no Lua code called
			}
		}
		base -= int(fr >> 32 & 0xffffff)
		cl = (*closure)(ex.stack[base-1].p)
		pc = int(uint32(fr))
		nf--
		if cl.p != trampoline.p {
			level--
		}
	}
	return fmt.Sprintf("%s:%d", cl.p.source, cl.p.lineAt(pc-1))
}
