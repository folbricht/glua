package glua

import (
	"context"
	"math"
	"runtime/debug"
	"sync"
	"sync/atomic"
	"time"
	"unsafe"
)

const (
	stackSlack    = 256      // free slots above any frame base, so a frame can be viewed as *[256]Value
	initStack     = 512      // 8 KB of registers
	maxPoolStack  = 4096     // an executor whose stack grew beyond 64 KB is not pooled
	maxPoolFrames = 1024     // nor one whose frames grew beyond 8 KB
	shrinkAfter   = 4        // checks in a row that a grown stack went unused before it shrinks
	maxStack      = 1 << 20  // fixed cap: register stack slots
	tickQuantum   = 1024     // steps handed to the loop between refills
	defaultSteps  = 10000000 // Limits.Steps default
	defaultDepth  = 10000    // Limits.CallDepth default
	defaultHost   = 100      // Limits.HostDepth default
	defaultAlloc  = 64 << 20 // Limits.AllocBytes default
	maxIndexHops  = 2000     // fixed cap: __index, __newindex and __call chains
)

// Frame flags, in the top byte of a frame record. RETURN tests them all at once.
const (
	frGoEntry    = 1 << (56 + iota) // pushed by run: unwinding and returning stop here
	frCatch                         // pcall
	frCont                          // a metamethod, iterator or closer: finish the interrupted instruction
	frVararg                        // a vararg function: its arguments lie below the frame
	frHandler                       // with frCatch: an xpcall, whose message handler is in the slot below the function
	frErrHandler                    // an xpcall message handler running on top of the failing frame
)

// Hint words are missCount<<24 | slot. The driver calls learn after a slow lookup.
const (
	hintSlotMask = 1<<24 - 1
	maxMisses    = 4
	megamorphic  = ^uint32(0)
)

// learn records where a slow lookup found its key. A site gives up after four misses: it is
// marked megamorphic and never written again, so it stops invalidating other cores' caches.
func learn(hint *uint32, slot int) {
	h := atomic.LoadUint32(hint)
	if h == megamorphic {
		return
	}
	if misses := h>>24 + 1; misses > maxMisses {
		atomic.StoreUint32(hint, megamorphic)
	} else {
		atomic.StoreUint32(hint, misses<<24|uint32(slot))
	}
}

// state is what the loop saves between runs. Only indices persist; the two addresses are
// valid only while fast is running, when nothing can move the stack.
type state struct {
	cl    *closure
	base  int
	pc    int
	ticks int
	nf    int
	hi    int // high-water mark: registers below it may hold pointers and are cleared on reset
	nret  int // number of results of an inline RETURN0 or RETURN1
	// nf+1 while Go code runs closers on top of nf frames: a run it makes at that height
	// records no Lua frame below
	goClose int

	limitAddr uintptr // last legal address of a CALL's function slot, plus one
	hiAddr    uintptr
}

// executor is a register stack, a frame list and counters. It holds no script state, so
// one pool per Runtime serves every Script and Rule. It is not the public VM, which is a
// private environment plus an executor of its own.
type executor struct {
	stack   []Value
	pframes []uint64 // pc:32 | delta:24 | flags:8. No pointers, so no write barrier and nothing to scan
	calls   []*Call  // one record per host-call depth
	depth   int
	slots   []unsafe.Pointer // by type ID: a *T made with new(T), for structs passed by value
	ctx     context.Context
	steps   int64                    // budget not yet handed to st.ticks
	top     int                      // end of an open list of results or arguments, as a stack index
	nvar    []int32                  // per frame: the number of extra arguments of a vararg function
	tbc     []int                    // stack indices of active to-be-closed variables, innermost last
	cont    []int32                  // per frame: what a continuation frame needs to resume, such as CONCAT's operand count
	strMeta *Table                   // the metatable all strings share; the string library sets it
	strIdx  *Table                   // strMeta's __index when it is a table and strMeta is frozen, for s:method()
	goErrs  map[unsafe.Pointer]error // Go errors by the data of their message, so raising it again keeps the chain
	co      *coroutine               // the running coroutine, nil on the main thread
	mainCo  *coroutine               // stands for the main thread in coroutine.running
	nny     int                      // Go calls and nested runs in progress: a yield cannot cross them
	st      state
	types   *[]*typeInfo
	rt      *Runtime // nil for executors the tests make

	maxSteps     int64
	maxCallDepth int
	errExtra     int // frames a message handler may use beyond maxCallDepth, as C Lua's error stack

	// under lua_stackstress, the stack moves between two buffers: spare is the other one,
	// whose first spareDirty slots hold poison
	spare        []Value
	spareDirty   int
	maxHostDepth int
	maxAlloc     int64 // bytes one entry may allocate
	allocLeft    int64 // what is left of it in the current entry

	checked    bool      // run the bounds-checked loop
	output     writeFunc // where print and warn write; nil discards
	warnOn     bool      // warn("@on") was called
	rand       [4]uint64 // math.random's state, per entry
	randSeeded bool
	randSeed   *uint64   // the RandSeed option, if set
	hostCalls  int       // Go functions running: a panic now is the host's, not the VM's
	fatal      error     // the terminal error of this entry, which stands once raised
	ectx       *entryCtx // the context host functions of this entry see, made on first use

	running, poisoned bool
	// Renew does nothing: the entry borrows its parent's budgets, or closers are running on
	// the grace budget of a terminal error
	fixed bool

	// what the entry used before its last Renew, which CallStats adds to what it used since
	renewedSteps, renewedAlloc int64
	maxTime                    time.Duration // Limits.Time, or 0
	quietChecks                int           // shrink's checks in a row that found the stack too large
	deadline                   int64         // when the entry, or the round since Renew, runs out of time, on monoNow's clock; 0 for never
	// liveKnown says that collectgarbage measured liveBase bytes live when the entry had
	// allocated liveAt: its count is that plus what was allocated since
	liveKnown        bool
	liveBase, liveAt int64

	coStacks []coStack // stacks of coroutines that returned in this entry, for the next ones
}

// write sends text from print or warn to the output.
func (ex *executor) write(s string) error {
	if ex.output == nil {
		return nil
	}
	return ex.output(ex.ctx, s)
}

// defaultChecked selects the loop new executors run: the fast loop, except under Hardened,
// which always runs the checked one.
var defaultChecked = false

func newExecutor() *executor {
	return &executor{
		stack:        make([]Value, initStack),
		pframes:      make([]uint64, 64),
		maxSteps:     defaultSteps,
		maxCallDepth: defaultDepth,
		maxHostDepth: defaultHost,
		maxAlloc:     defaultAlloc,
		checked:      defaultChecked,
		types:        types.Load(),
	}
}

// call is the only way in from Go. Arguments are already in stack[fn+1:], and the first
// result lands in stack[fn]; ex.top is one past the last result.
func (ex *executor) call(ctx context.Context, cl *closure, fn, nargs int) (err error) {
	if ex.running {
		panic("glua: concurrent use of an executor")
	}
	if ctx.Err() != nil {
		return ctxError(ctx) // a cancelled context never runs script code
	}
	parent := ex.inherit(ctx)
	if ex.maxHostDepth < 0 {
		return ErrHostDepth
	}
	ex.deadline = 0
	if ex.maxTime > 0 {
		ex.deadline = monoAfter(ex.maxTime)
	}
	if parent != nil { // a nested entry ends when the entry that made it runs out of time
		if n := parent.deadline.Load(); n != 0 && (ex.deadline == 0 || n < ex.deadline) {
			ex.deadline = n
		}
	}
	q := min(tickQuantum, ex.maxSteps)
	ex.steps, ex.st.ticks = ex.maxSteps-q, int(q) // set as the entry starts, and by Renew: a nested run shares them
	ex.allocLeft = ex.maxAlloc
	if ex.deadline != 0 && monoNow() >= ex.deadline {
		return ErrTime // as a cancelled context: out of time before it starts, it runs nothing
	}
	// ex.types stays from entry to entry: plans are only ever added, and plan reloads the
	// list when it meets a type bound since
	ex.running, ex.ctx = true, ctx
	ex.fixed = parent != nil
	completed := false
	defer func() {
		ex.running = false
		if completed {
			return
		}
		ex.poisoned = true // a panic or runtime.Goexit is passing through: never pool this one again
		if ex.hostCalls > 0 {
			// a host function's panic, or Goexit: it continues, unless the Runtime recovers
			// panics. recover returns nil for Goexit, which then goes on.
			if ex.rt != nil && ex.rt.recover {
				if r := recover(); r != nil {
					err = &PanicError{Value: r, Stack: debug.Stack()}
				}
			}
			return
		}
		// a panic inside the VM itself, such as a failed bounds check in the checked loop: a VM
		// bug must not take the process down
		if r := recover(); r != nil {
			err = &PanicError{Value: r, Stack: debug.Stack()}
		}
	}()
	err = ex.run(cl, fn, nargs)
	completed = true
	if parent != nil {
		parent.usedSteps.Add(ex.maxSteps - ex.steps - int64(max(ex.st.ticks, 0)))
		parent.usedAlloc.Add(max(ex.maxAlloc-ex.allocLeft, 0))
	}
	if le, ok := err.(*Error); ok && le.terminal {
		ex.poisoned = true // a terminal error may leave closers half run: start the next entry afresh
	}
	return err
}

// run pushes a goEntry frame and drives the loop until that frame returns. Host functions re-enter here.
// A nested run's frame records the Lua frame below it, for whereLevel and tracebacks; returning
// never uses it. Pc 0 records none: the outermost run, or a closer that Go code runs.
func (ex *executor) run(cl *closure, fn, nargs int) error {
	st := &ex.st
	nf := st.nf
	ex.stack[fn] = luaFnValue(cl)
	pc, callerBase := 0, fn+1
	if nf > 0 && st.goClose != nf+1 {
		pc, callerBase = st.pc, st.base
	}
	if err := ex.pushFrame(cl, fn, nargs, pc, callerBase, frGoEntry); err != nil {
		return err
	}
	err := ex.drive(nf)
	if le, ok := err.(*Error); ok {
		ex.captureTrace(le, nf) // the error leaves this run uncaught
		// close what this run left open, with the error
		if le.terminal {
			ex.closeTerminal(fn, le)
		} else if v, cerr := ex.closeOnError(fn, le.Value, true); cerr != nil {
			err = cerr
		} else if !same(&v, &le.Value) {
			le.Value, le.cause = v, nil // a closer replaced the error
		}
	}
	st.nf = nf // on an error this is the unwinding: it never crosses a goEntry frame
	return err
}

// reset drops every pointer the call may have left behind.
func (ex *executor) reset() {
	if hi := ex.st.hi; hi <= 16 {
		for j := range hi { // a small call: plain stores beat memclrHasPointers and its bulk barrier
			ex.stack[j] = Value{}
		}
	} else {
		clear(ex.stack[:hi])
	}
	// the Call records are cleared after every host call; an executor that a panic left with
	// one in use is never pooled again
	ex.st = state{}
	ex.ctx, ex.top, ex.depth = nil, 0, 0
	ex.tbc = ex.tbc[:0]
	if len(ex.goErrs) > 0 {
		clear(ex.goErrs)
	}
	if ex.ectx != nil {
		liveEntryCtx.Add(-1)
		ex.ectx = nil
	}
	ex.co, ex.nny, ex.fatal = nil, 0, nil
	ex.renewedSteps, ex.renewedAlloc = 0, 0
	ex.liveKnown = false
	ex.randSeeded = false
	if len(ex.coStacks) > 0 { // kept for the entry, not between entries
		clear(ex.coStacks)
		ex.coStacks = ex.coStacks[:0]
	}
}

// release returns an executor to the pool, unless it ended abnormally or has grown large.
func release(pool *sync.Pool, ex *executor) {
	if !ex.poisoned && len(ex.stack) <= maxPoolStack && len(ex.pframes) <= maxPoolFrames {
		pool.Put(ex)
	}
}

// frameLimit is the number of frames allowed now.
func (ex *executor) frameLimit() int { return ex.maxCallDepth + ex.errExtra }

// ensure grows the stack so that n slots plus the slack exist. Under the lua_stackstress
// build tag it moves the stack every time, and poisons the old one.
func (ex *executor) ensure(n int) error {
	if n+stackSlack <= len(ex.stack) {
		if !stackStress || len(ex.stack) > stressMax {
			return nil
		}
		ex.moveStack(len(ex.stack))
		return nil
	}
	limit := maxStack
	if ex.errExtra > 0 {
		limit += handlerSlots
	}
	if n+stackSlack > limit {
		return ex.errorf("stack overflow")
	}
	ex.moveStack(min(max(2*len(ex.stack), n+stackSlack), limit))
	return nil
}

// stressMax is the largest stack lua_stackstress moves at every check; past it, moving the
// whole stack per call would make deep recursion quadratic.
const stressMax = 64 << 10

// stalePoison fills a stack that was moved away from, under lua_stackstress: a stale read
// shows up as this string in a result or a message.
var stalePoison = String("glua: stale stack slot")

// moveStack moves the stack to a new one of size slots.
func (ex *executor) moveStack(size int) {
	if stackStress {
		// only the part in use: above the high-water mark and top, every slot is nil
		used := min(len(ex.stack), max(ex.st.hi, ex.top)+stackSlack)
		s, dirty := ex.spare, ex.spareDirty
		if len(s) != size {
			s, dirty = make([]Value, size), 0
		}
		copy(s, ex.stack[:used])
		if dirty > used {
			clear(s[used:dirty])
		}
		for i := range used {
			ex.stack[i] = stalePoison
		}
		ex.spare, ex.spareDirty = ex.stack, used
		ex.stack = s
		return
	}
	if ex.running && size > len(ex.stack) {
		ex.allocLeft -= int64(size-len(ex.stack)) * 16 // the stack is capped; an overdraft fails the next charge
	}
	s := make([]Value, size)
	copy(s, ex.stack)
	clear(ex.stack) // the old stack may stay reachable from a stale pointer; leave nothing in it
	ex.stack = s
}

// charge takes n bytes from the entry's allocation budget, before the allocation. Running
// out is a terminal error.
func (ex *executor) charge(n int) error {
	if n > maxAlloc {
		return ex.terminal(ErrAlloc)
	}
	ex.allocLeft -= int64(n)
	if ex.allocLeft < 0 {
		return ex.terminal(ErrAlloc)
	}
	return nil
}

// produce charges a library function for making n bytes: n to the allocation budget, and
// one step per 64 bytes.
func (ex *executor) produce(n int) error {
	if err := ex.charge(n); err != nil {
		return err
	}
	return ex.spend(n / 64)
}

// spend takes k steps at once, for library work in proportion to its size.
func (ex *executor) spend(k int) error {
	if k <= 0 {
		return nil
	}
	ex.st.ticks -= k
	if ex.st.ticks >= 0 {
		return nil
	}
	need := int64(-ex.st.ticks)
	if need > ex.steps {
		ex.steps, ex.st.ticks = 0, -1
		return ex.terminal(ErrSteps)
	}
	ex.steps -= need
	ex.st.ticks = 0
	return ex.interrupted()
}

// interrupted reports a cancelled context or the entry's time run out, as a terminal error.
// The loop asks at each refill, and library work as it takes its steps.
func (ex *executor) interrupted() error {
	if ex.ctx.Err() != nil { // never Done(): it allocates a channel on a fresh context
		return ex.terminal(ctxError(ex.ctx))
	}
	if ex.deadline != 0 && monoNow() >= ex.deadline {
		return ex.terminal(ErrTime)
	}
	return nil
}

// monoEpoch starts monoNow's clock, which reads the monotonic clock as nanoseconds since,
// so that a deadline is one integer: no wall-clock jumps, and a compare to check.
var monoEpoch = time.Now()

func monoNow() int64 { return int64(time.Since(monoEpoch)) }

// monoAfter is the deadline d from now, saturating: a Time of centuries is never, not a
// deadline wrapped into the past.
func monoAfter(d time.Duration) int64 {
	now := monoNow()
	if int64(d) > math.MaxInt64-now {
		return math.MaxInt64
	}
	return now + int64(d)
}

// tableSet does t[k] = v for Lua code, charging what the table grows by. A table already
// half the size of the largest single allocation may not grow further.
func (ex *executor) tableSet(t *Table, k, v Value) error {
	before := t.memSize()
	if before >= maxAlloc/2 && t.Get(k).IsNil() && !v.IsNil() {
		return ex.terminal(ErrAlloc)
	}
	t.set(k, v)
	if after := t.memSize(); after > before {
		return ex.charge(after - before)
	}
	return nil
}

// refill runs when the tick counter expires: at most once per 1,024 back-edges and calls.
// The tick that brought us here has already happened, so it is paid for out of the new quantum.
//
//go:noinline
func (ex *executor) refill() error {
	if err := ex.interrupted(); err != nil {
		return err
	}
	if ex.steps == 0 {
		return ex.terminal(ErrSteps)
	}
	q := min(tickQuantum, ex.steps)
	ex.steps -= q
	ex.st.ticks = int(q) - 1
	return nil
}

// drive runs fast and does the work it hands back, until the goEntry frame of the
// current run, frame nf0, returns. Errors stop at catch frames above nf0.
func (ex *executor) drive(nf0 int) error {
	for {
		var err error
		var e exit
		if ex.checked {
			e = ex.checkedLoop()
		} else {
			e = ex.fast()
		}
		switch e {
		case exReturn:
			var done bool
			if done, err = ex.frameReturned(ex.st.base-1, ex.st.nret); done {
				return nil
			}
		case exResults:
			i := ex.instr(ex.st.pc - 1)
			fn := ex.st.base + decA(i)
			ex.adjustResults(i, fn, ex.st.nret)
		case exSlowOp:
			err = ex.slowOp()
		case exHostCall:
			err = ex.hostCall()
		case exGrowStack:
			fn := ex.st.base + decA(ex.instr(ex.st.pc-1))
			if err = ex.ensure(fn + 1 + stackSlack); err == nil {
				ex.st.pc-- // run the CALL again
			}
		case exGrowFrames:
			if len(ex.pframes) >= ex.frameLimit() {
				err = ex.errorf("stack overflow")
			} else {
				grow := min(len(ex.pframes), ex.frameLimit()-len(ex.pframes))
				if err = ex.charge(grow * 8); err != nil {
					break
				}
				ex.pframes = append(ex.pframes, make([]uint64, grow)...)
				ex.st.pc--
			}
		case exTick:
			// the tick comes after a back-edge's jump or a call's frame push: pc is the next
			// instruction, which is where an error belongs, while positions read pc-1
			ex.st.pc++
			if err = ex.refill(); err == nil {
				ex.st.pc--
			}
		default:
			err = ex.errorf("bad opcode %d", uint8(ex.instr(ex.st.pc-1)))
		}
		if err == errDone {
			return nil
		}
		if err != nil {
			if err = ex.unwind(err, nf0); err == nil {
				continue
			}
			return err
		}
	}
}

// instr returns the instruction at index pc of the current function.
func (ex *executor) instr(pc int) uint32 { return ex.st.cl.p.code[pc] }

// aux returns the auxiliary word that follows the instruction at pc-1.
func (ex *executor) aux() uint32 { return ex.st.cl.p.code[ex.st.pc] }

// jumpAux takes or skips the jump in the aux word of a compare-and-jump at pc-1.
func (ex *executor) jumpAux(fallThrough bool) {
	if fallThrough {
		ex.st.pc++
	} else {
		ex.st.pc += int(int32(ex.aux())) + 1
	}
}
