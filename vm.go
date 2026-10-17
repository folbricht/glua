package glua

import (
	"context"
	"fmt"
	"strings"
)

// VM is a private, mutable instance of a Script: its top level run again in an environment
// of its own, which is not frozen, so state persists between calls. The Runtime's layer, the
// libraries, host globals and Go modules, is still shared and frozen. One goroutine at a
// time; values from a VM are mutable and follow that rule wherever they go.
type VM struct {
	s      *Script
	env    *Table
	result []Value
	ex     *executor // its own, kept between calls; replaced after an abnormal end
}

// NewVM runs the top level again in a private environment that is not frozen, under the
// init limits. Lua modules it requires run again too, and host calls the top level makes are
// repeated.
func (s *Script) NewVM(ctx context.Context) (*VM, error) {
	rt := s.rt
	vm := &VM{s: s}
	ld := newEnvLoader(rt)
	vm.env = rt.newEnv(ld)
	cl := newMainClosure(s.main, s.info, vm.env)
	ex := vm.executor()
	ex.setLimits(&rt.init)
	err := ex.call(ctx, cl, 0, 0)
	if err == nil {
		vm.result = append(vm.result, ex.stack[:ex.top]...)
	}
	rt.observeEntry(ex, s.name, "", err)
	vm.leave(ex)
	if err != nil {
		return nil, err
	}
	return vm, nil
}

// Function returns ch as a function of this VM, as Lua's load gives one: a Value for Call or
// CallN, which runs ch's top level in the VM's environment, with the call's arguments as its
// ..., and returns what the chunk returns. Unlike require, each call runs the chunk again. Its
// _ENV is the function's, as with load: a chunk that assigns it changes it for later calls.
// A nil or zero Chunk gives nil.
func (vm *VM) Function(ch *Chunk) Value {
	if ch == nil || ch.p == nil {
		return Value{}
	}
	return luaFnValue(newMainClosure(ch.p, ch.info, vm.env))
}

// executor returns the VM's executor, a fresh one after an abnormal end.
func (vm *VM) executor() *executor {
	if vm.ex == nil || vm.ex.poisoned {
		vm.ex = vm.s.rt.newExecutor()
	}
	return vm.ex
}

// enter returns the VM's executor for a call.
func (vm *VM) enter() *executor {
	ex := vm.executor()
	ex.setLimits(vm.s.lim)
	return ex
}

// leave clears the executor after a call. One whose stack a deep call grew is let go, as
// the pool lets go of one, so that the VM does not keep the stack between calls.
func (vm *VM) leave(ex *executor) {
	ex.reset()
	if len(ex.stack) > maxPoolStack && vm.ex == ex {
		vm.ex = nil
	}
}

// Globals returns the VM's globals table, which is not frozen.
func (vm *VM) Globals() *Table { return vm.env }

// Get reads a global, or a dotted path, and converts it to T.
func (vm *VM) Get[T any](name string) (T, error) {
	var r T
	v, err := lookup(vm.env, vm.result, name)
	if err != nil {
		return r, err
	}
	return v.As[T]()
}

// Set assigns a global, or a field at a dotted path, converted by the general rules. Names
// the host or the libraries define are reserved.
func (vm *VM) Set[T any](name string, v T) error {
	val, err := resultValue(v)
	if err != nil {
		return err
	}
	t := vm.env
	path, last := "", name
	if i := strings.LastIndexByte(name, '.'); i >= 0 {
		path, last = name[:i], name[i+1:]
		pv, err := lookup(vm.env, nil, path)
		if err != nil {
			return err
		}
		if !pv.isObj(kindTable) {
			return fmt.Errorf("glua: '%s' is a %s, not a table", path, typeName(pv))
		}
		t = (*Table)(pv.p)
	} else if vm.s.rt.reserved[name] {
		return fmt.Errorf("glua: '%s' is a reserved name", name)
	}
	if t.Frozen() {
		return fmt.Errorf("glua: '%s' is frozen", path)
	}
	t.Set(String(last), val)
	return nil
}

// bindFunc finds the function name of a VM for FuncN.
func (vm *VM) bindFunc(name string) (*boundFunc, error) {
	fn, err := lookupFunc(vm.env, vm.result, name)
	if err != nil {
		return nil, err
	}
	cl, base, _ := entryFunc(fn)
	return &boundFunc{rt: vm.s.rt, lim: vm.s.lim, fn: fn, cl: cl, base: base, script: vm.s.name, name: name, vm: vm}, nil
}

// Func0 returns a Go function backed by the Lua function name, as Script.Func0 does, running
// on this VM: not safe for concurrent use. A struct passed by value is copied to the heap.
func (vm *VM) Func0[R any](name string) (func(context.Context) (R, error), error) {
	b, err := vm.bindFunc(name)
	if err != nil {
		return nil, err
	}
	return func0[R](b)
}

// Func1 is Func0 for a function of one argument.
func (vm *VM) Func1[A, R any](name string) (func(context.Context, A) (R, error), error) {
	b, err := vm.bindFunc(name)
	if err != nil {
		return nil, err
	}
	return func1[A, R](b)
}

// Func2 is Func0 for a function of two arguments.
func (vm *VM) Func2[A, B, R any](name string) (func(context.Context, A, B) (R, error), error) {
	b, err := vm.bindFunc(name)
	if err != nil {
		return nil, err
	}
	return func2[A, B, R](b)
}

// Func3 is Func0 for a function of three arguments.
func (vm *VM) Func3[A, B, C, R any](name string) (func(context.Context, A, B, C) (R, error), error) {
	b, err := vm.bindFunc(name)
	if err != nil {
		return nil, err
	}
	return func3[A, B, C, R](b)
}

// Call calls fn on this VM and returns its first result.
func (vm *VM) Call(ctx context.Context, fn Value, args ...Value) (Value, error) {
	var buf [1]Value
	res, err := vm.CallN(ctx, buf[:0], fn, args...)
	if err != nil || len(res) == 0 {
		return Value{}, err
	}
	return res[0], nil
}

// CallN calls fn on this VM and appends its results to dst[:0].
func (vm *VM) CallN(ctx context.Context, dst []Value, fn Value, args ...Value) ([]Value, error) {
	cl, base, err := entryFunc(fn)
	if err != nil {
		return dst[:0], err
	}
	ex := vm.enter()
	if err = ex.ensure(base + len(args) + 1); err == nil {
		ex.stack[1] = fn
		copy(ex.stack[base:], args)
		ex.st.hi = base + len(args)
		err = ex.call(ctx, cl, 0, base-1+len(args))
	}
	dst = dst[:0]
	if err == nil {
		dst = append(dst, ex.stack[:ex.top]...)
	}
	vm.s.rt.observeEntry(ex, vm.s.name, "", err)
	vm.leave(ex)
	return dst, err
}
