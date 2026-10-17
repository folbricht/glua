package glua

import (
	"context"
	"errors"
	"fmt"
	"math"
	"strings"
	"testing"
	"time"
)

// runLimited loads src under rt and calls its function f.
func runLimited(t *testing.T, rt *Runtime, ctx context.Context, src string) (Value, error) {
	t.Helper()
	s, err := rt.Load(context.Background(), "hostile.lua", src)
	if err != nil {
		t.Fatal(err)
	}
	f, err := s.Func0[Value]("f")
	if err != nil {
		t.Fatal(err)
	}
	return f(ctx)
}

func TestHostileScripts(t *testing.T) {
	ctx := context.Background()
	rt := MustNew(LibSafe|LibCoroutine|LibLoad, Limits{Steps: 200_000, AllocBytes: 1 << 20})
	for _, tc := range []struct {
		name string
		src  string
		want error
	}{
		{"loop", "function f() while true do end end", ErrSteps},
		{"pcall loop", "local function g() end function f() while true do pcall(g) end end", ErrSteps},
		{"pcall spin", "local function spin() while true do end end function f() while true do pcall(spin) end end", ErrSteps},
		{"xpcall handler", "function f() while true do xpcall(function() while true do end end, print) end end", ErrSteps},
		{"coroutine", "function f() local co = coroutine.wrap(function() while true do end end) while true do pcall(co) end end", ErrSteps},
		{"recursion in pcall", "local function r() return pcall(r) end function f() while true do r() end end", ErrSteps},
		{"array growth", "function f() local t = {} for i = 1, 1e9 do t[i] = i end end", ErrAlloc},
		{"hash growth", "function f() local t = {} for i = 1, 1e9 do t['k' .. i] = i end end", ErrAlloc},
		{"rawset growth", "function f() local t = {} for i = 1, 1e9 do rawset(t, i, i) end end", ErrAlloc},
		{"table.insert", "function f() local t = {} while true do table.insert(t, 1) end end", ErrAlloc},
		{"concat doubling", "function f() local s = 'x' while true do s = s .. s end end", ErrAlloc},
		{"string.rep", "function f() return string.rep('x', 1 << 22) end", ErrAlloc},
		{"rep then upper", "function f() local s = string.rep('x', 1 << 19) for i = 1, 100 do s:upper() end end", ErrAlloc},
		{"closures", "function f() local t = {} for i = 1, 1e9 do t[i] = function() return i end end end", ErrAlloc},
		{"coroutines", "function f() local t = {} for i = 1, 1e9 do t[i] = coroutine.create(print) end end", ErrAlloc},
		{"gsub", "function f() local s = string.rep('x', 1 << 16) while true do s = s:gsub('x', 'xx') end end", ErrAlloc},
		{"pattern set", "function f() return string.rep('a', 1 << 16):find('[' .. string.rep('b', 1 << 14) .. ']*c') end", ErrSteps},
		{"pattern set repeated", "function f() return string.rep('a', 512):find('[' .. string.rep('b', 1024) .. 'a]*c') end", ErrSteps},
		{"pattern set repeated lazily", "function f() return string.rep('a', 512):find('[' .. string.rep('b', 1024) .. 'a]-c') end", ErrSteps},
		{"back-reference", "function f() return (string.rep('a', 1 << 16) .. 'c'):find('^(.*)%1b') end", ErrSteps},
		{"format", "function f() local s = 'x' while true do s = string.format('%s%s', s, s) end end", ErrAlloc},
		{"table.concat", "function f() local t = {} for i = 1, 100 do t[i] = string.rep('y', 1 << 14) end for i = 1, 100 do table.concat(t) end end", ErrAlloc},
		{"load", "function f() local s = string.rep(' ', 1 << 18) for i = 1, 10 do load(s) end end", ErrAlloc},
		{"pcall swallows nothing", "function f() local ok = pcall(string.rep, 'x', 1 << 22) return ok end", ErrAlloc},
		{"error handler", "function f() return xpcall(error, function() while true do end end) end", ErrSteps},
		{"growing tail calls", "local function r(...) return r(1, 2, 3, ...) end function f() return r() end", ErrSteps},
	} {
		_, err := runLimited(t, rt, ctx, tc.src)
		if !errors.Is(err, tc.want) {
			t.Errorf("%s: got %v, want %v", tc.name, err, tc.want)
		}
		var le *Error
		if errors.As(err, &le) && !strings.HasPrefix(le.Error(), "hostile.lua:") {
			t.Errorf("%s: no position: %v", tc.name, le)
		}
	}
}

func TestStackOverflowCatchable(t *testing.T) {
	rt := MustNew(Limits{CallDepth: 1000})
	v, err := runLimited(t, rt, context.Background(), `
		local function r(n) return 1 + r(n + 1) end
		function f() local ok, e = pcall(r, 1) return tostring(ok) .. " " .. e end`)
	if err != nil || !strings.Contains(v.String(), "false hostile.lua:2: stack overflow") {
		t.Errorf("got %v, %v", v, err)
	}
}

func TestCancellation(t *testing.T) {
	rt := MustNew(Limits{Steps: NoLimit})
	ctx, cancel := context.WithTimeout(context.Background(), 20*time.Millisecond)
	defer cancel()
	start := time.Now()
	_, err := runLimited(t, rt, ctx, "local function g() end function f() while true do pcall(g) end end")
	if !errors.Is(err, context.DeadlineExceeded) {
		t.Errorf("deadline: %v", err)
	}
	if d := time.Since(start); d > time.Second {
		t.Errorf("took %v to stop", d)
	}
	var le *Error
	if !errors.As(err, &le) || !strings.HasPrefix(le.Error(), "hostile.lua:1:") {
		t.Errorf("no position: %v", err)
	}
	cctx, cancel2 := context.WithCancelCause(context.Background())
	cause := errors.New("tenant removed")
	cancel2(cause)
	if _, err := runLimited(t, rt, cctx, "function f() end"); !errors.Is(err, cause) {
		t.Errorf("cause: %v", err)
	}
}

func TestTerminate(t *testing.T) {
	denied := errors.New("permission denied")
	var after int
	var stop context.CancelFunc
	rt := MustNew(LibSafe|LibCoroutine,
		Global("deny", GoFunc(func(c *Call) error { return Terminate(denied) })),
		Global("cancelDeny", GoFunc(func(c *Call) error { stop(); return Terminate(denied) })),
		Global("wrapped", GoFunc(func(c *Call) error { return fmt.Errorf("deny: %w", Terminate(denied)) })),
		Global("after", Do0(func() { after++ })))
	for _, src := range []string{
		"function f() deny() after() end",
		"function f() pcall(deny) after() end",
		"function f() xpcall(deny, function() after() end) after() end",
		"function f() coroutine.resume(coroutine.create(function() deny() end)) after() end",
		"function f() coroutine.wrap(function() pcall(deny) end)() after() end",
		"function f() table.sort({1, 2, 3}, function() deny() end) after() end",
	} {
		after = 0
		_, err := runLimited(t, rt, context.Background(), src)
		var le *Error
		if !errors.As(err, &le) || errors.Unwrap(le) != denied || !le.terminal || !strings.HasPrefix(le.Error(), "hostile.lua:1:") {
			t.Errorf("%s: got %v", src, err)
		}
		if after != 0 {
			t.Errorf("%s: the script went on", src)
		}
	}
	after = 0
	if _, err := runLimited(t, rt, context.Background(), "function f() local t <close> = setmetatable({}, {__close = after}) deny() end"); !errors.Is(err, denied) || after != 1 {
		t.Errorf("closer: %v, ran %d times", err, after)
	}
	// wrapped again, it is an ordinary error
	if v, err := runLimited(t, rt, context.Background(), "function f() return select(2, pcall(wrapped)) end"); err != nil || v.String() != "deny: permission denied" {
		t.Errorf("wrapped: got %v, %v", v, err)
	}
	// a Terminate wins over the context it cancelled on its way out
	ctx, cancel := context.WithCancel(context.Background())
	stop = cancel
	if _, err := runLimited(t, rt, ctx, "function f() pcall(cancelDeny) end"); !errors.Is(err, denied) {
		t.Errorf("Terminate after cancelling: %v", err)
	}
	cancel()
	if Terminate(nil) != nil {
		t.Error("Terminate(nil) is not nil")
	}
}

func TestCancelledHostError(t *testing.T) {
	gone := errors.New("client left")
	var stop context.CancelCauseFunc // the running entry's
	var after int
	rt := MustNew(
		Global("wait", GoFunc(func(c *Call) error {
			stop(gone)
			<-c.Context().Done()
			return context.Cause(c.Context())
		})),
		Global("fail", GoFunc(func(c *Call) error {
			stop(gone)
			return errors.New("unrelated")
		})),
		Global("hog", GoFunc(func(c *Call) error {
			stop(gone)
			return c.Charge(1 << 20)
		})),
		Global("after", Do0(func() { after++ })),
		Limits{AllocBytes: 1 << 16})
	for _, tc := range []struct {
		src  string
		want error
	}{
		{"function f() pcall(wait) after() end", gone},
		{"function f() pcall(fail) after() end", gone},
		{"function f() pcall(hog) after() end", ErrAlloc}, // a terminal error that stands is not replaced
	} {
		ctx, cancel := context.WithCancelCause(context.Background())
		stop, after = cancel, 0
		_, err := runLimited(t, rt, ctx, tc.src)
		cancel(nil)
		var le *Error
		if !errors.Is(err, tc.want) || !errors.As(err, &le) || !le.terminal {
			t.Errorf("%s: got %v, want %v", tc.src, err, tc.want)
		}
		if after != 0 {
			t.Errorf("%s: the script went on", tc.src)
		}
	}
}

func TestExactSteps(t *testing.T) {
	// a loop of n iterations takes n-1 back-edges; the limit is exact
	for _, n := range []int64{1, 100, 1023, 1024, 1025, 5000} {
		rt := MustNew(Limits{Steps: n})
		s := mustLoad(t, rt, "function f(n) for i = 1, n do end end")
		f, _ := s.Func1[int64, struct{}]("f")
		if _, err := f(context.Background(), n+1); err != nil {
			t.Errorf("%d steps: n+1 iterations failed: %v", n, err)
		}
		if _, err := f(context.Background(), n+2); !errors.Is(err, ErrSteps) {
			t.Errorf("%d steps: n+2 iterations: %v", n, err)
		}
	}
}

func TestRenew(t *testing.T) {
	var stats CallStats
	renew := GoFunc(func(c *Call) error { c.Renew(); return nil })
	rt := MustNew(LibSafe|LibCoroutine, Limits{Steps: 10_000, AllocBytes: 1 << 17},
		Global("renew", renew), Global("wait", GoFunc(func(c *Call) error { return nil })),
		Observe(func(cs CallStats) { stats = cs }))
	s := mustLoad(t, rt, `
		local function rounds(pause)
			for i = 1, 10 do
				local s = string.rep("x", 1 << 14)
				for j = 1, 3000 do end
				pause()
			end
		end
		function renewed() rounds(renew) end
		function waited() rounds(wait) end
		function inCoroutine() coroutine.wrap(rounds)(renew) end
		function count() rounds(renew) return collectgarbage("count") end`)
	renewed, _ := s.Func0[struct{}]("renewed")
	waited, _ := s.Func0[struct{}]("waited")
	inCoroutine, _ := s.Func0[struct{}]("inCoroutine")
	count, _ := s.Func0[float64]("count")
	// ten rounds of some 3,500 steps and 32 KB fit only if each round has the budgets afresh
	if _, err := renewed(context.Background()); err != nil {
		t.Errorf("renewed: %v", err)
	}
	renewedStats := stats
	unbounded := MustNew(Limits{Steps: NoLimit, AllocBytes: NoLimit}, Global("renew", renew), Global("wait", GoFunc(func(c *Call) error { return nil })),
		Observe(func(cs CallStats) { stats = cs }))
	waitedUnbounded, _ := mustLoad(t, unbounded, `
		local function rounds(pause)
			for i = 1, 10 do
				local s = string.rep("x", 1 << 14)
				for j = 1, 3000 do end
				pause()
			end
		end
		function waited() rounds(wait) end`).Func0[struct{}]("waited")
	waitedUnbounded(context.Background())
	// steps exactly; bytes at least the rounds' strings, since a fresh executor's stack growth
	// is charged too, and which executor an entry gets is the pool's business
	if renewedStats.Steps != stats.Steps || stats.Steps < 35_000 || renewedStats.AllocBytes < 10<<15 {
		t.Errorf("renewed: CallStats %+v, but the same work unrenewed used %+v", renewedStats, stats)
	}
	if _, err := waited(context.Background()); !errors.Is(err, ErrSteps) {
		t.Errorf("not renewed: %v", err)
	}
	renewed(context.Background())
	cancelled, cancel := context.WithCancel(context.Background())
	cancel()
	if _, err := renewed(cancelled); !errors.Is(err, context.Canceled) || stats.Steps > 10_000 { // what the last run renewed is not carried over
		t.Errorf("an entry that never ran: %v, CallStats %+v", err, stats)
	}
	if _, err := inCoroutine(context.Background()); err != nil {
		t.Errorf("renewed in a coroutine: %v", err)
	}
	// count is what the entry keeps, not what its rounds allocated: none of their strings
	if kb, err := count(context.Background()); err != nil || kb > 64 {
		t.Errorf("collectgarbage('count') after renewing: %v KB, %v", kb, err)
	}

	// a limit already exceeded stays exceeded, even for Lua the host calls after renewing
	late := GoFunc(func(c *Call) error {
		c.Invoke(c.Value(0))
		c.Renew()
		c.Invoke(c.Value(0))
		return nil
	})
	rt = MustNew(Limits{Steps: 10_000}, Global("late", late), Observe(func(cs CallStats) { stats = cs }))
	_, err := runLimited(t, rt, context.Background(), "function f() late(function() while true do end end) end")
	if !errors.Is(err, ErrSteps) || stats.Steps > 10_000 {
		t.Errorf("after the limit: %v, after %d steps", err, stats.Steps)
	}

	// so does a stack that grew past the allocation budget: Renew is the charge that fails
	rt = MustNew(Limits{AllocBytes: 2 << 10, InitAllocBytes: 1 << 20}, Global("renew", renew))
	s = mustLoad(t, rt, "t = {} for i = 1, 5000 do t[i] = i end function f() renew(table.unpack(t)) renew() end")
	f, _ := s.Func0[struct{}]("f")
	if _, err := f(context.Background()); !errors.Is(err, ErrAlloc) && !stackStress { // lua_stackstress does not charge a moved stack
		t.Errorf("overdrawn stack: %v", err)
	}

	// closers after a terminal error keep the grace budget
	var calls int
	rt = MustNew(Limits{Steps: 10_000}, Global("renew", renew), Global("call", Do0(func() { calls++ })))
	_, err = runLimited(t, rt, context.Background(), `function f()
		local t <close> = setmetatable({}, {__close = function() renew() while true do call() end end})
		while true do end
	end`)
	if !errors.Is(err, ErrSteps) || calls == 0 || calls > tickQuantum+1 { // a back-edge a call, and one call before the first
		t.Errorf("closer: %v after %d calls", err, calls)
	}
}

func TestRenewNested(t *testing.T) {
	var inner *Script
	callInner := GoFunc(func(c *Call) error {
		_, err := inner.Call(c.Context(), inner.Globals().Get(String(c.Arg[string](0))), c.Value(1))
		return err
	})
	renew := GoFunc(func(c *Call) error { c.Renew(); return nil })
	callRenew := GoFunc(func(c *Call) error { // a nested entry, then a wait, then Renew
		_, err := inner.Call(c.Context(), inner.Globals().Get(String("spin")), c.Value(0))
		c.Renew()
		return err
	})
	rt := MustNew(Limits{Steps: 10_000}, Global("call_inner", callInner), Global("renew", renew), Global("call_renew", callRenew))
	inner = mustLoad(t, rt, `
		function spin(n) for i = 1, n do end end
		function spinRenew(n) spin(n) renew() spin(n) end`)
	outer := mustLoad(t, rt, `
		function f(n) for i = 1, 4 do call_inner("spinRenew", n) end end
		function g(n) for i = 1, 3 do call_renew(n) for j = 1, 1000 do end end end`)
	f, _ := outer.Func1[int64, struct{}]("f")
	// a nested entry shares the outer one's budgets, so its Renew does nothing: eight loops
	// of 1,500 do not fit in 10,000 steps
	if _, err := f(context.Background(), 1500); !errors.Is(err, ErrSteps) {
		t.Errorf("nested: %v", err)
	}
	// what nested entries used is paid out of the budgets before they are renewed, not out of
	// the new ones: rounds of 8,000 nested steps and 1,000 more fit
	g, _ := outer.Func1[int64, struct{}]("g")
	if _, err := g(context.Background(), 8000); err != nil {
		t.Errorf("renewed after nested entries: %v", err)
	}
	// a context taken before Renew gives nested entries the renewed budgets: after 8,000
	// steps, 5,000 nested ones fit only in renewed budgets
	held := GoFunc(func(c *Call) error {
		ctx := c.Context()
		for range 3 {
			c.Renew()
			if _, err := inner.Call(ctx, inner.Globals().Get(String("spin")), Int(5000)); err != nil {
				return err
			}
		}
		return nil
	})
	rt2 := MustNew(Limits{Steps: 10_000}, Global("held", held))
	if _, err := runLimited(t, rt2, context.Background(), "function f() for i = 1, 8000 do end held() end"); err != nil {
		t.Errorf("a context held across Renew: %v", err)
	}
}

func TestNestedScriptsShareBudget(t *testing.T) {
	var inner *Script
	callInner := GoFunc(func(c *Call) error {
		v, err := inner.Call(c.Context(), inner.Globals().Get(String("spin")), c.Value(0))
		if err != nil {
			return err
		}
		return c.ReturnValues(v)
	})
	rt := MustNew(Limits{Steps: 10_000}, Global("call_inner", callInner))
	inner = mustLoad(t, rt, "function spin(n) for i = 1, n do end return n end")
	outer := mustLoad(t, rt, "function f(n) local s = 0 for i = 1, 4 do s = s + call_inner(n) end return s end")
	f, _ := outer.Func1[int64, int64]("f")
	// four inner loops of 2,000 fit in 10,000 steps together
	if n, err := f(context.Background(), 2000); err != nil || n != 8000 {
		t.Errorf("2000: %v %v", n, err)
	}
	// four of 3,000 do not, though each would on its own
	if _, err := f(context.Background(), 3000); !errors.Is(err, ErrSteps) {
		t.Errorf("3000: %v", err)
	}
	// a fresh context gives the inner script a budget of its own
	fresh := GoFunc(func(c *Call) error {
		v, err := inner.Call(context.Background(), inner.Globals().Get(String("spin")), c.Value(0))
		if err != nil {
			return err
		}
		return c.ReturnValues(v)
	})
	rt2 := MustNew(Limits{Steps: 10_000}, Global("call_inner", fresh))
	inner = mustLoad(t, rt2, "function spin(n) for i = 1, n do end return n end")
	outer2 := mustLoad(t, rt2, "function f(n) local s = 0 for i = 1, 4 do s = s + call_inner(n) end return s end")
	f2, _ := outer2.Func1[int64, int64]("f")
	if _, err := f2(context.Background(), 3000); err != nil {
		t.Errorf("fresh context: %v", err)
	}
}

func TestGraceBudgetForClose(t *testing.T) {
	var closed []string
	rt := MustNew(Limits{Steps: 2000}, Global("note", Do1(func(s string) { closed = append(closed, s) })))
	_, err := runLimited(t, rt, context.Background(), `
		function f()
			local a <close> = setmetatable({}, {__close = function() note("a") end})
			local b <close> = setmetatable({}, {__close = function() while true do end end})
			local c <close> = setmetatable({}, {__close = function() note("c") end})
			while true do end
		end`)
	if !errors.Is(err, ErrSteps) {
		t.Errorf("got %v", err)
	}
	// c runs; b breaches the grace budget, which abandons the rest
	if strings.Join(closed, ",") != "c" {
		t.Errorf("closed %v", closed)
	}
}

func TestHostResultsCharged(t *testing.T) {
	big := Global("big", Fn0(func() string { return strings.Repeat("x", 1<<16) }))
	rt := MustNew(Limits{AllocBytes: 1 << 20}, big)
	if _, err := runLimited(t, rt, context.Background(), "function f() for i = 1, 100 do big() end end"); !errors.Is(err, ErrAlloc) {
		t.Errorf("got %v", err)
	}
}

// Callbacks from library code, such as sort's comparator, must not climb the stack.
func TestCallbacksDoNotClimbStack(t *testing.T) {
	p, info, err := compileChunk("climb", `
		local t = {}
		for i = 1, 5000 do t[i] = (i * 7919) % 5000 end
		table.sort(t, function(a, b) return a < b end)
		local s = string.rep("ab", 5000):gsub("a", function() return "c" end)
		return #s`)
	if err != nil {
		t.Fatal(err)
	}
	g := testGlobals()
	ex := newExecutor()
	ex.strMeta = testStrMeta
	ex.maxSteps = 100_000_000
	if _, err := runClosure(context.Background(), ex, newMainClosure(p, info, g)); err != nil {
		t.Fatal(err)
	}
	if len(ex.stack) > 4*initStack {
		t.Errorf("the stack grew to %d slots", len(ex.stack))
	}
}

// A Go function that Go code called runs from the trampoline. A limit hit there is reported
// at the Lua code that made the call, not at the trampoline: the pcall, or the resume.
func TestLimitPositionThroughTrampoline(t *testing.T) {
	for _, tc := range []struct{ src, want string }{
		{"\n\npcall(pcall, string.rep, 'x', 1e8)", "t.lua:3: "},
		{"local co = coroutine.wrap(string.rep)\n\nco('x', 1e8)", "t.lua:3: "},
		{"local co = coroutine.create(string.rep)\n\ncoroutine.resume(co, 'x', 1e8)", "t.lua:3: "},
	} {
		rt := MustNew(LibSafe|LibCoroutine, Limits{AllocBytes: 1 << 20})
		_, err := rt.Load(context.Background(), "t.lua", tc.src)
		if !errors.Is(err, ErrAlloc) || !strings.HasPrefix(err.Error(), tc.want) {
			t.Errorf("%q: got %v, want %q", tc.src, err, tc.want)
		}
	}
}

// A long entry that renews its budgets keeps nothing from one round to the next: a message
// handler's results, the host errors it caught, or what calls that have returned left on
// the stack.
func TestLongEntryKeepsNothing(t *testing.T) {
	var top, stack, goErrs, stale int
	rt := MustNew(LibSafe, Limits{Steps: 100_000, AllocBytes: 1 << 20},
		Global("renew", GoFunc(func(c *Call) error {
			ex := c.ex
			hi := ex.st.hi
			c.Renew()
			stale = 0
			for _, v := range ex.stack[c.base+c.nargs : hi] {
				if !v.IsNil() {
					stale++
				}
			}
			top, stack, goErrs = ex.top, len(ex.stack), len(ex.goErrs)
			return nil
		})),
		Global("fail", GoFunc(func(c *Call) error { return fmt.Errorf("no %d", c.Arg[int64](0)) })))
	s := mustLoad(t, rt, `
		local function deep(n)
			local s = string.rep("z", 1000) .. n
			if n > 0 then return deep(n - 1) + #s end
			return #s
		end
		function handlers(n)
			for i = 1, n do
				xpcall(error, debug.traceback, "e")
				xpcall(fail, function(m) return m end, i)
				xpcall(function() error("e") end, tostring)
				renew()
			end
		end
		function hostErrors(n)
			for i = 1, n do pcall(fail, i) if i % 100 == 0 then renew() end end
		end
		function afterDeep() deep(100) renew() end`)
	ctx := context.Background()
	call := func(name string, args ...Value) {
		t.Helper()
		if _, err := s.Call(ctx, s.Globals().Get(String(name)), args...); err != nil {
			t.Fatalf("%s: %v", name, err)
		}
	}
	call("handlers", Int(20_000))
	if top != 0 || stack > 1024 {
		t.Errorf("after 60,000 message handlers: top %d, stack %d slots", top, stack)
	}
	call("hostErrors", Int(5_000))
	if goErrs > maxGoErrs {
		t.Errorf("after 5,000 distinct host errors: %d kept", goErrs)
	}
	call("afterDeep")
	if stale != 0 {
		t.Errorf("after a deep call and a renewal: %d stale slots above the call", stale)
	}
}

// Limits.Time ends an entry that runs too long, and Renew gives a long entry's round its
// time afresh, so that only a round that runs too long ends it.
func TestTimeLimit(t *testing.T) {
	rt := MustNew(Limits{Steps: NoLimit, Time: 50 * time.Millisecond},
		Global("wait", GoFunc(func(c *Call) error {
			time.Sleep(20 * time.Millisecond)
			c.Renew()
			return nil
		})))
	s := mustLoad(t, rt, `
		function spin() pcall(function() while true do end end) end
		function rounds(n) for i = 1, n do wait() for j = 1, 5000 do end end end -- steps, so the time is checked
		function slowRound() wait() while true do end end`)
	ctx := context.Background()
	start := time.Now()
	if _, err := s.Call(ctx, s.Globals().Get(String("spin"))); !errors.Is(err, ErrTime) || time.Since(start) > 5*time.Second {
		t.Errorf("a loop without end: %v after %v", err, time.Since(start))
	}
	if _, err := s.Call(ctx, s.Globals().Get(String("rounds")), Int(10)); err != nil {
		t.Errorf("10 rounds of 20 ms, renewed after each: %v", err)
	}
	if _, err := s.Call(ctx, s.Globals().Get(String("slowRound"))); !errors.Is(err, ErrTime) {
		t.Errorf("a round without end after a renewal: %v", err)
	}
	if _, err := New(Limits{Time: -time.Second}); err == nil {
		t.Error("a negative Time was accepted")
	}
	if _, err := New(Limits{Time: NoLimit}); err != nil {
		t.Errorf("Time: NoLimit: %v", err)
	}
}

// Limits.Time reaches what the entry does on its behalf: a nested entry made with the host
// function's Context ends with the entry's time, and a host function that charges for its
// work as it goes is told when the time runs out.
func TestTimeLimitNested(t *testing.T) {
	var s *Script
	rt := MustNew(Limits{Steps: NoLimit, AllocBytes: NoLimit, Time: 100 * time.Millisecond},
		Global("nested", GoFunc(func(c *Call) error {
			time.Sleep(60 * time.Millisecond)
			_, err := s.Call(c.Context(), s.Globals().Get(String("spin")))
			return err
		})),
		Global("chunks", GoFunc(func(c *Call) error {
			for end := time.Now().Add(2 * time.Second); time.Now().Before(end); {
				if err := c.Charge(64 << 10); err != nil {
					return err
				}
				time.Sleep(time.Millisecond) // a chunk of the host's own work
			}
			return nil
		})))
	s = mustLoad(t, rt, `
		function spin() while true do end end
		function outer() return nested() end
		function work() return chunks() end`)
	ctx := context.Background()
	start := time.Now()
	_, err := s.Call(ctx, s.Globals().Get(String("outer")))
	if took := time.Since(start); !errors.Is(err, ErrTime) || took > 150*time.Millisecond {
		t.Errorf("a nested entry spinning: %v after %v, want ErrTime at 100 ms", err, took)
	}
	start = time.Now()
	if _, err := s.Call(ctx, s.Globals().Get(String("work"))); !errors.Is(err, ErrTime) || time.Since(start) > 300*time.Millisecond {
		t.Errorf("a host function charging for its work in chunks: %v after %v, want ErrTime at 100 ms", err, time.Since(start))
	}
}

// The time limit's edges: a Time of centuries is no limit rather than a deadline wrapped into
// the past; Renew after a wait longer than Time renews, even with nested work to pay for; a
// nested entry made after the time ran out runs nothing; and a host function's own timeout,
// derived from its Context, still fires.
func TestTimeLimitEdges(t *testing.T) {
	var s *Script
	touched := false
	rt := MustNew(Limits{Steps: NoLimit, AllocBytes: NoLimit, Time: 50 * time.Millisecond},
		Global("touch", GoFunc(func(c *Call) error { touched = true; return nil })),
		Global("waitRenew", GoFunc(func(c *Call) error {
			if _, err := s.Call(c.Context(), s.Globals().Get(String("busy"))); err != nil {
				return err
			}
			time.Sleep(80 * time.Millisecond)
			c.Renew()
			return nil
		})),
		Global("late", GoFunc(func(c *Call) error {
			time.Sleep(80 * time.Millisecond)
			_, err := s.Call(c.Context(), s.Globals().Get(String("side")))
			return err
		})),
		Global("timeout", GoFunc(func(c *Call) error {
			// later than the entry's time: a parent deadline reported earlier would make
			// WithTimeout trust the parent's Done, which never closes for Time
			ctx, cancel := context.WithTimeout(c.Context(), 100*time.Millisecond)
			defer cancel()
			select {
			case <-ctx.Done():
				return nil
			case <-time.After(2 * time.Second):
				return errors.New("the host's own timeout did not fire")
			}
		})))
	s = mustLoad(t, rt, `
		function busy() for i = 1, 5000 do end end
		function renewing() waitRenew() waitRenew() for i = 1, 5000 do end end
		function side() touch() end
		function tooLate() return late() end
		function own() return timeout() end`)
	ctx := context.Background()
	if _, err := s.Call(ctx, s.Globals().Get(String("renewing"))); err != nil {
		t.Errorf("renewing after waits longer than Time: %v", err)
	}
	if _, err := s.Call(ctx, s.Globals().Get(String("tooLate"))); !errors.Is(err, ErrTime) || touched {
		t.Errorf("a nested entry made after the time ran out: %v, ran: %v", err, touched)
	}
	if _, err := s.Call(ctx, s.Globals().Get(String("own"))); err != nil {
		t.Error(err)
	}
	var long *Script
	long = mustLoad(t, MustNew(Limits{Time: math.MaxInt64},
		Global("nest", GoFunc(func(c *Call) error {
			_, err := long.Call(c.Context(), long.Globals().Get(String("work")))
			return err
		}))), "function work() for i = 1, 5000 do end return 1 end function f() return nest() end")
	if _, err := long.Call(ctx, long.Globals().Get(String("f"))); err != nil {
		t.Errorf("Time of math.MaxInt64, nested: %v", err)
	}
}
