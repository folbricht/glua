package glua

import (
	"context"
	"testing"
)

func liveRuntime(t *testing.T) *Runtime {
	t.Helper()
	return MustNew(LibSafe|LibCoroutine, Limits{Steps: NoLimit, AllocBytes: NoLimit},
		Global("live", GoFunc(func(c *Call) error { return c.Return(c.LiveBytes()) })))
}

// LiveBytes counts what the entry keeps: it grows with what the script holds, falls when the
// script lets go, and reaches into coroutines, suspended, wrapped or waiting in resume.
func TestCallLiveBytes(t *testing.T) {
	s := mustLoad(t, liveRuntime(t), `
		local big = {}
		for i = 1, 1000 do big[i] = i end
		function f()
			local base = live()
			local t = {}
			for i = 1, 1000 do t[i] = string.rep("x", 100) .. i end
			local held = live()
			t = nil
			local dropped = live()
			local co = coroutine.create(function()
				local s = string.rep("y", 100000)
				coroutine.yield()
				return s
			end)
			coroutine.resume(co)
			local suspended = live()
			co = nil
			local w = coroutine.wrap(function() local s = string.rep("w", 100000) coroutine.yield() return s end)
			w()
			local wrapped = live()
			w = nil
			local m = string.rep("m", 100000)
			local inside = coroutine.wrap(function() return live() end)()
			return base, held, dropped, suspended, wrapped, inside, #m
		end`)
	res, err := s.CallN(context.Background(), nil, s.Globals().Get(String("f")))
	if err != nil {
		t.Fatal(err)
	}
	n := func(i int) int64 { x, _ := res[i].Int(); return x }
	base, held, dropped, suspended, wrapped, inside := n(0), n(1), n(2), n(3), n(4), n(5)
	switch {
	case held-base < 100_000:
		t.Errorf("1000 strings of 100 bytes held: %d bytes more than %d", held-base, base)
	case dropped-base > 1_000:
		t.Errorf("after letting go: %d bytes more than %d", dropped-base, base)
	case suspended-base < 100_000:
		t.Errorf("a suspended coroutine holding 100 KB: %d bytes more", suspended-base)
	case wrapped-base < 100_000:
		t.Errorf("a wrapped coroutine holding 100 KB: %d bytes more", wrapped-base)
	case inside-base < 100_000:
		t.Errorf("measured inside a coroutine, the main thread's 100 KB: %d bytes more", inside-base)
	case base > 50_000:
		t.Errorf("the frozen globals, a table of 1000, counted: %d bytes", base)
	}
}

// A VM keeps its state between calls, each with its budgets afresh: LiveBytes shows it.
func TestVMLiveBytes(t *testing.T) {
	s := mustLoad(t, liveRuntime(t), `
		seen = {}
		function add() seen[#seen + 1] = string.rep("y", 1000) end
		function forget() seen = {} end`)
	vm := must(s.NewVM(context.Background()))
	ctx := context.Background()
	before := vm.LiveBytes()
	for range 100 {
		if _, err := vm.Call(ctx, vm.Globals().Get(String("add"))); err != nil {
			t.Fatal(err)
		}
	}
	grown := vm.LiveBytes()
	vm.Call(ctx, vm.Globals().Get(String("forget")))
	after := vm.LiveBytes()
	if grown-before < 100_000 || after-before > 1_000 {
		t.Errorf("before %d, after 100 adds %d, after forgetting %d", before, grown, after)
	}
}

// collectgarbage("count") falls when the script lets go, once collect has measured, and
// collect lets go of what returned calls left on the stack, deep's strings among it.
func TestCollectGarbageCount(t *testing.T) {
	var stale int
	rt := MustNew(LibSafe, Limits{Steps: NoLimit, AllocBytes: NoLimit},
		Global("stale", GoFunc(func(c *Call) error {
			stale = 0
			for _, v := range c.ex.stack[c.base+c.nargs : max(c.ex.st.hi, c.base+c.nargs)] {
				if v.isString() && len(v.str()) > 500 { // one of deep's strings
					stale++
				}
			}
			return nil
		})))
	s := mustLoad(t, rt, `
		local function deep(n)
			local s = string.rep("z", 1000) .. n
			if n > 0 then return deep(n - 1) + #s end
			return #s
		end
		function f()
			local t = {}
			for i = 1, 1000 do t[i] = string.rep("x", 1000) .. i end
			local full = collectgarbage("count")
			t = nil
			collectgarbage()
			local empty = collectgarbage("count")
			deep(100)
			collectgarbage("collect")
			stale()
			return full, empty
		end`)
	res, err := s.CallN(context.Background(), nil, s.Globals().Get(String("f")))
	if err != nil {
		t.Fatal(err)
	}
	full, _ := res[0].Float()
	empty, _ := res[1].Float()
	if full < 1000 || empty > full/10 {
		t.Errorf("count holding 1 MB: %v KB, after letting go and collecting: %v KB", full, empty)
	}
	if stale != 0 {
		t.Errorf("after collect: %d stale slots above the call", stale)
	}
}

// A stack and frames that one deep call grew shrink again: at Renew in a long entry, and
// between the calls of a VM, which lets go of such an executor as the pool does.
func TestDeepStackShrinks(t *testing.T) {
	var stack, frames []int
	rt := MustNew(LibSafe, Limits{Steps: NoLimit, AllocBytes: NoLimit, CallDepth: 50_000},
		Global("renew", GoFunc(func(c *Call) error {
			stack = append(stack, len(c.ex.stack))
			frames = append(frames, len(c.ex.pframes))
			c.Renew()
			stack = append(stack, len(c.ex.stack))
			frames = append(frames, len(c.ex.pframes))
			return nil
		})))
	s := mustLoad(t, rt, `
		local function deep(n) if n > 0 then return 1 + deep(n - 1) end return 0 end
		function f() deep(20000) renew() return deep(10) end
		function g() return deep(20000) end`)
	ctx := context.Background()
	if _, err := s.Call(ctx, s.Globals().Get(String("f"))); err != nil {
		t.Fatal(err)
	}
	if stack[0] < 20_000 || stack[1] > maxPoolStack || frames[0] < 20_000 || frames[1] > 1024 {
		t.Errorf("stack %v slots and frames %v, before and after Renew", stack, frames)
	}
	vm := must(s.NewVM(ctx))
	if _, err := vm.Call(ctx, vm.Globals().Get(String("g"))); err != nil {
		t.Fatal(err)
	}
	if vm.ex != nil {
		t.Errorf("the VM keeps a stack of %d slots between calls", len(vm.ex.stack))
	}
	if got, err := vm.Call(ctx, vm.Globals().Get(String("g"))); err != nil || got.String() != "20000" {
		t.Errorf("called again: %v, %v", got, err)
	}
}
