package glua

import (
	"context"
	"errors"
	"fmt"
	"reflect"
	"unsafe"

	"github.com/folbricht/glua/internal/syntax"
)

// Errors that errors.Is finds. The first three are terminal: pcall cannot catch them, and
// an *Error that wraps them carries the script's position and traceback.
var (
	ErrSteps       = errors.New("glua: step limit exceeded")                      // Limits.Steps ran out
	ErrAlloc       = errors.New("glua: allocation limit exceeded")                // Limits.AllocBytes ran out, or one allocation was over 1 GiB
	ErrHostDepth   = errors.New("glua: too many nested calls between Go and Lua") // Limits.HostDepth was reached
	ErrTime        = errors.New("glua: time limit exceeded")                      // Limits.Time ran out
	ErrUndefined   = errors.New("glua: name is not defined")                      // FuncN or Get named nothing
	ErrNotFunction = errors.New("glua: value is not a function")                  // FuncN, Call or CallN got something else
)

// Terminate wraps err so that a host function returning it ends the whole entry, as running
// out of steps does: pcall, xpcall and coroutine.resume do not see it, __close handlers run
// on the grace budget, and the entry returns an *Error that unwraps to err. It must be
// returned as it is: wrapped again, as by fmt.Errorf with %w, it is an ordinary error. It is
// for a host that finds the script must not go on, for a permission it lacks or a quota it
// spent. A terminal error that already stands wins. Terminate(nil) is nil.
func Terminate(err error) error {
	if err == nil {
		return nil
	}
	return &terminateError{err}
}

// terminateError is an error from Terminate.
type terminateError struct{ err error }

// Error returns err's message.
func (e *terminateError) Error() string { return e.err.Error() }

// Unwrap returns err.
func (e *terminateError) Unwrap() error { return e.err }

// errDone tells the driver that a general RETURN ended the run's goEntry frame.
var errDone = errors.New("glua: done")

// Error is a runtime error raised by a script or by a host function it called.
type Error struct {
	Value    Value // what was raised: for VM errors a message with its position; a string for Go errors
	where    string
	cause    error // the Go error, a limit error or the context's cause
	terminal bool  // limits, cancellation, host depth, Terminate: pcall cannot catch it
	trace    []traceEntry
}

// traceEntry is one frame of a traceback, kept as a prototype and pc until it is read. A nil
// prototype marks Go code between two entries from Go.
type traceEntry struct {
	p  *proto
	pc int
}

// Error returns one line, such as "policy.lua:4: boom".
func (e *Error) Error() string {
	var msg string
	switch {
	case e.Value.isString() || e.Value.isNumber():
		msg = e.Value.String()
	case e.Value.IsNil():
		msg = "nil"
	default:
		msg = "(error object is a " + typeName(e.Value) + " value)"
	}
	if e.where != "" {
		return e.where + ": " + msg
	}
	return msg
}

// PanicError is a panic recovered at the entry: one inside the VM itself, which the
// checked loop of [Hardened] turns bugs into, or, with RecoverPanics, one in a host function.
type PanicError struct {
	Value any
	Stack []byte
}

// Error returns "glua: panic: " and the panic value.
func (e *PanicError) Error() string { return fmt.Sprintf("glua: panic: %v", e.Value) }

// Frame is one level of a traceback.
type Frame struct {
	Source   string // "" for Go code
	Line     int
	Function string // "main chunk", "function 'f'", "function <policy.lua:12>", or "Go function"
}

// Traceback returns the frames the error passed through, innermost first. Lines are looked
// up only now, so scripts that use error for control flow do not pay for them.
func (e *Error) Traceback() []Frame {
	frames := make([]Frame, 0, len(e.trace))
	for _, t := range e.trace {
		frames = append(frames, traceFrame(t))
	}
	return frames
}

// traceFrame is the Frame of a traceback entry.
func traceFrame(t traceEntry) Frame {
	if t.p == nil {
		return Frame{Function: "Go function"}
	}
	f := Frame{Source: t.p.source, Line: t.p.lineAt(max(t.pc-1, 0))}
	switch name := t.p.name; {
	case name == "main chunk":
		f.Function = name
	case name == "" || name == "<anonymous>":
		f.Function = fmt.Sprintf("function <%s:%d>", t.p.source, t.p.lineAt(0))
	default:
		f.Function = "function '" + name + "'"
	}
	return f
}

// captureTrace adds the frames of the current run, above nf0, to an error that leaves it
// uncaught.
func (ex *executor) captureTrace(le *Error, nf0 int) {
	if len(le.trace) > 0 {
		le.trace = append(le.trace, traceEntry{}) // Go code between the inner run and this one
	}
	le.trace = appendFrames(le.trace, &ex.st, ex.pframes, ex.stack, nf0)
}

// appendFrames adds the frames of a thread's run above frame nf0 to trace, innermost first.
// The trampoline is Go code as far as Lua can tell, and is added as such.
func appendFrames(trace []traceEntry, st *state, pframes []uint64, stack []Value, nf0 int) []traceEntry {
	entry := func(cl *closure, pc int) traceEntry {
		if cl.p == trampoline.p {
			return traceEntry{}
		}
		return traceEntry{p: cl.p, pc: pc}
	}
	cl, base, pc := st.cl, st.base, st.pc
	for f := st.nf - 1; f > nf0 && cl != nil; f-- {
		trace = append(trace, entry(cl, pc))
		fr := pframes[f]
		base -= int(fr >> 32 & 0xffffff)
		pc = int(uint32(fr))
		if v := stack[base-1]; v.isObj(kindLuaFn) {
			cl = (*closure)(v.p)
		} else {
			cl = nil
		}
	}
	if cl != nil && st.nf > nf0 {
		trace = append(trace, entry(cl, pc))
	}
	return trace
}

// Unwrap returns the Go error behind e, if any.
func (e *Error) Unwrap() error { return e.cause }

// where reports the current position as source:line, from the instruction at pc-1. In the
// trampoline, which runs a Go function that Go code called, it is the Lua code that called the
// trampoline, or none when Go did.
func (ex *executor) where() string {
	cl, base, pc, nf := ex.st.cl, ex.st.base, ex.st.pc, ex.st.nf
	for cl != nil && cl.p == trampoline.p {
		if nf == 0 || ex.pframes[nf-1]&frGoEntry != 0 {
			return ""
		}
		fr := ex.pframes[nf-1]
		base -= int(fr >> 32 & 0xffffff)
		cl = (*closure)(ex.stack[base-1].p)
		pc = int(uint32(fr))
		nf--
	}
	if cl == nil {
		return ""
	}
	return fmt.Sprintf("%s:%d", cl.p.source, cl.p.lineAt(max(pc-1, 0))) // a call ticks before its first instruction
}

// errorf raises an ordinary, catchable runtime error at the current position. As in C Lua,
// the position is part of the error value, which pcall returns.
func (ex *executor) errorf(format string, args ...any) error {
	return &Error{Value: String(ex.where() + ": " + fmt.Sprintf(format, args...))}
}

// typeError raises "attempt to <what> a <type> value", naming where the value came from
// when it is in register reg of the current frame (reg < 0: not in a register).
func (ex *executor) typeError(what string, v Value, reg int) error {
	info := ""
	if op := uint8(ex.instr(ex.st.pc - 1)); what == "index" && (op == opGetGlobal || op == opSetGlobal) {
		info = " (upvalue '_ENV')" // a nil globals table, which C Lua sees as the _ENV upvalue
	} else if reg >= 0 {
		if vi := ex.st.cl.p.varInfo(ex.st.pc-1, reg); vi != "" {
			info = " (" + vi + ")"
		}
	}
	return ex.errorf("attempt to %s a %s value%s", what, typeName(v), info)
}

// terminal raises an error that pcall cannot catch: limits, context cancellation, host depth,
// Terminate.
func (ex *executor) terminal(cause error) error {
	err := &Error{Value: String(cause.Error()), where: ex.where(), cause: cause, terminal: true}
	if ex.fatal == nil {
		ex.fatal = err
	}
	return err
}

// hostError turns an error that the host function of c returned into a Lua error. The Go
// error is kept on the side, so errors.Is and errors.As still find it. A Lua error returned
// as it is stays itself; one the host wrapped, as a Lua error from Invoke in an Errorf, is
// the host's own error, as in C Lua, while a terminal one has already replaced err. One that
// Errorf or ArgError made, wrapped or not, starts with the position of the Lua code that
// called the function, as luaL_error's does.
func (ex *executor) hostError(c *Call, err error) error {
	if _, ok := err.(*Error); ok {
		return err
	}
	msg, where, pos := err.Error(), "", ""
	if pe := (*positioned)(nil); errors.As(err, &pe) {
		pos = ex.whereLevel(c, 1)
	}
	if pos != "" {
		msg = pos + ": " + msg
	} else {
		where = ex.where()
	}
	if ex.goErrs == nil {
		ex.goErrs = map[unsafe.Pointer]error{}
	}
	if len(ex.goErrs) >= maxGoErrs {
		// an entry that runs long and catches errors without end: forget the old ones, which
		// a script raising one again would carry without its Go error
		clear(ex.goErrs)
	}
	if msg != "" {
		ex.goErrs[unsafe.Pointer(unsafe.StringData(msg))] = err // for error(e) raising it again
	}
	return &Error{Value: String(msg), where: where, cause: err}
}

// maxGoErrs is how many Go errors an entry keeps for raising again.
const maxGoErrs = 1024

func ctxError(ctx context.Context) error {
	return context.Cause(ctx)
}

// SyntaxError is a chunk that does not compile.
type SyntaxError struct {
	Source    string
	Line, Col int
	Msg       string
}

// Error returns "source:line: message", as C Lua reports a syntax error.
func (e *SyntaxError) Error() string { return fmt.Sprintf("%s:%d: %s", e.Source, e.Line, e.Msg) }

// syntaxError turns the compiler's error into a *SyntaxError.
func syntaxError(err error) error {
	if se, ok := err.(*syntax.Error); ok {
		return &SyntaxError{Source: se.Source, Line: se.Line, Col: se.Col, Msg: se.Msg}
	}
	return err
}

// BindError is a binding that cannot work: a Go value or type that cannot be converted, a
// duplicate or reserved name, a missing field. New, Load, Expr and FuncN return it, before
// anything runs.
type BindError struct {
	Name   string
	Type   reflect.Type
	Reason string
}

// Error names the binding, its type when known, and the reason.
func (e *BindError) Error() string {
	var s string
	switch {
	case e.Name != "" && e.Type != nil:
		s = fmt.Sprintf("glua: cannot bind '%s' (%s): ", e.Name, e.Type)
	case e.Name != "":
		s = fmt.Sprintf("glua: cannot bind '%s': ", e.Name)
	case e.Type != nil:
		s = fmt.Sprintf("glua: cannot bind %s: ", e.Type)
	default:
		s = "glua: cannot bind: "
	}
	return s + e.Reason
}
