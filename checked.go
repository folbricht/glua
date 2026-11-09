package glua

import "unsafe"

// Bounds-checked accessors for the checked loop, which genloop generates from fast.go into
// checked_gen.go. In the checked loop, a compiler or verifier bug becomes a Go panic, which
// the entry recovers and returns as a PanicError, instead of memory corruption.

func kAtChecked(k []Value, i uint32) *Value    { return &k[i] }
func hintAtChecked(p *proto, i uint32) *uint32 { return &p.hints[i] }
func upAtChecked(cl *closure, i uint8) *Value  { return &cl.up[i] }
func khashAtChecked(p *proto, i uint32) uint64 { return p.khash[i] }

// checkedCaller returns the closure in a caller's function slot, asserting what the fast loop
// trusts. It tests only the sentinels of isScalar, to stay within the inliner's budget for a
// big function: a nil pointer with a function's n breaks invariant 1, and still panics, at
// the first read through the closure.
func checkedCaller(f *Value) *closure {
	if f.n != kindLuaFn<<56 || uintptr(f.p)-uintptr(unsafe.Pointer(&tags)) < unsafe.Sizeof(tags) {
		panic("glua: checked loop: no Lua function in the caller's function slot")
	}
	return (*closure)(f.p)
}
