package glua

import "unsafe"

// Live memory. The allocation budget counts what an entry allocates, which bounds what it
// keeps only until the budget starts again: Call.Renew in a long entry, or the next call of
// a VM, whose state persists. A walk measures what is kept instead: everything reachable
// from the entry's roots that a script could have allocated, at the sizes the allocation
// budget charges for it. Frozen state, which is shared and made at load, function
// prototypes, Go functions and userdata, the host's own values, are not counted.

// liveWalker measures what is reachable from the values given to add.
type liveWalker struct {
	running *coroutine // the coroutine whose stack is the executor's, walked as a root
	seen    map[unsafe.Pointer]bool
	work    []Value
	size    int64
	objects int // visited, for collectgarbage to charge
}

func newLiveWalker() *liveWalker {
	return &liveWalker{seen: map[unsafe.Pointer]bool{}}
}

// add queues v, unless it holds nothing to measure or was seen already.
func (w *liveWalker) add(v Value) {
	if v.p == nil || isScalar(v.p) || v.n>>56 == kindUser || w.seen[v.p] {
		return
	}
	w.seen[v.p] = true
	w.work = append(w.work, v)
}

func (w *liveWalker) addAll(vs []Value) {
	for _, v := range vs {
		w.add(v)
	}
}

// stack counts a thread's stack and frames, and queues its first n slots.
func (w *liveWalker) stack(ts *threadState, n int) {
	w.size += 16*int64(len(ts.stack)) + 8*int64(len(ts.pframes))
	w.addAll(ts.stack[:min(n, len(ts.stack))])
}

// walk visits the queued values and returns the bytes they hold.
func (w *liveWalker) walk() int64 {
	for len(w.work) > 0 {
		v := w.work[len(w.work)-1]
		w.work = w.work[:len(w.work)-1]
		w.objects++
		switch v.n >> 56 {
		case kindString:
			w.size += 16 + int64(v.n&lenMask)
		case kindTable:
			t := (*Table)(v.p)
			if t.Frozen() {
				continue // shared state, made at load
			}
			w.size += 64 + int64(t.memSize())
			w.addAll(t.arr)
			for i := range t.nodes {
				if nd := &t.nodes[i]; !nd.v.IsNil() {
					w.add(nd.k)
					w.add(nd.v)
				}
			}
			if t.meta != nil {
				w.add(tableValue(t.meta))
			}
		case kindLuaFn:
			cl := (*closure)(v.p)
			w.size += 48 + 16*int64(len(cl.up))
			w.addAll(cl.up)
			if cl.env != nil {
				w.add(tableValue(cl.env))
			}
		case kindCell:
			if c := v.cell(); !c.frozen {
				w.size += 24
				w.add(c.v)
			}
		case kindGoFn:
			if g := (*goFunc)(v.p); g.co != nil {
				w.add(threadValue(g.co))
			}
		case kindThread:
			w.thread((*coroutine)(v.p))
		}
	}
	return w.size
}

// thread counts a coroutine and queues what it holds: its stack where it stopped, or, for
// one waiting in resume, the state it waits in. The running one's stack is a root.
func (w *liveWalker) thread(co *coroutine) {
	w.size += 4 << 10
	w.add(co.fn)
	w.addAll(co.yielded)
	switch {
	case co == w.running:
	case co.status == coNormal:
		w.stack(&co.waiting, co.waiting.st.hi)
	default:
		w.stack(&co.threadState, co.st.hi)
	}
}

// liveWalk measures what the entry of c keeps reachable: the stack up to the end of c's
// arguments, the results c has set, and the coroutines waiting for the running one.
func (c *Call) liveWalk() *liveWalker {
	ex := c.ex
	w := newLiveWalker()
	w.running = ex.co
	w.stack(&threadState{stack: ex.stack, pframes: ex.pframes}, c.base+c.nargs)
	w.addAll(c.res)
	if ex.co != nil && ex.mainCo != nil {
		w.add(threadValue(ex.mainCo)) // waiting in resume, with what it reaches
	}
	w.walk()
	return w
}

// LiveBytes measures the memory the entry keeps reachable now: its tables, strings,
// closures, coroutines and stack, at the sizes the allocation budget charges for them.
// Frozen state, which every entry shares, and Go values are not counted. The allocation
// budget bounds this only until it starts again, at Renew in a long entry or at each call
// of a VM, so a host that runs such an entry for scripts it does not trust can check
// LiveBytes from time to time and end the entry with Terminate when it grows too large. It
// takes time in proportion to what it measures.
func (c *Call) LiveBytes() int64 {
	return c.liveWalk().size
}

// LiveBytes measures the memory the VM keeps between calls: what its globals and the
// results of its top level reach, as Call.LiveBytes counts it. Each call of a VM has its
// budgets afresh, so they do not bound what the VM keeps.
func (vm *VM) LiveBytes() int64 {
	w := newLiveWalker()
	w.add(tableValue(vm.env))
	w.addAll(vm.result)
	return w.walk()
}

// clearDead clears the stack above c's arguments, which calls that have returned left
// there and which would otherwise stay reachable until the entry ends, as C Lua's collector
// clears a stack above its top. A stack and frames that a deep call grew far beyond what is
// in use now shrink, as C Lua's luaD_shrinkstack does.
func (c *Call) clearDead() {
	ex := c.ex
	end := c.base + c.nargs
	if end < ex.st.hi {
		clear(ex.stack[end:ex.st.hi])
		ex.st.hi = end
	}
	if need := max(end, ex.st.hi, ex.top) + stackSlack; len(ex.stack) > maxPoolStack && len(ex.stack) > 4*need {
		ex.moveStack(max(initStack, 2*need))
	}
	if nf := ex.st.nf + 1; len(ex.pframes) > 1024 && len(ex.pframes) > 4*nf {
		ex.pframes = append(make([]uint64, 0, max(64, 2*nf)), ex.pframes[:max(64, 2*nf)]...)
		if len(ex.nvar) > len(ex.pframes) {
			ex.nvar = append([]int32(nil), ex.nvar[:len(ex.pframes)]...)
		}
		if len(ex.cont) > len(ex.pframes) {
			ex.cont = append([]int32(nil), ex.cont[:len(ex.pframes)]...)
		}
	}
}

// measureLive measures what the entry keeps for collectgarbage, a step per object visited.
func (c *Call) measureLive() error {
	ex := c.ex
	w := c.liveWalk()
	if err := ex.spend(w.objects); err != nil {
		return err
	}
	ex.liveKnown, ex.liveBase, ex.liveAt = true, w.size, ex.allocated()
	return nil
}

// allocated is what the entry has charged to its allocation budget, renewals included.
func (ex *executor) allocated() int64 {
	return ex.renewedAlloc + ex.maxAlloc - ex.allocLeft
}
