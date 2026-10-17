// Package glua is a pure-Go Lua 5.4 for small embedded scripts: rules, policies, handlers
// and configuration. It needs no cgo and no assembly, and supports 64-bit platforms only.
//
// Clients that prefer the shorter name can alias the import:
//
//	import lua "github.com/folbricht/glua"
//
// # The model
//
// Three types carry it. A [Runtime] is the host's configuration: libraries, host globals,
// Go modules, bound Go types and limits. A [Script] is code loaded into a Runtime: its top
// level runs once, in [Runtime.Load], and everything it built is then frozen. A [VM] is a
// private, mutable instance of a Script, for the rare script that must keep state between
// calls. Runtimes and Scripts never change after they are made, so any goroutine may use
// them at the same time.
//
//	rt := lua.MustNew(lua.Limits{Steps: 100_000})
//	script, err := rt.Load(ctx, "policy.lua", src)
//	allow, err := script.Func2[*Request, int64, bool]("allow")
//	ok, err := allow(ctx, req, 10) // safe from any goroutine
//
// The functions Func0 to Func3 return plain Go functions backed by Lua functions. Their
// argument and result types are checked when they are bound, not when they are called, and
// a call allocates nothing in the library. [Script.Get] reads a frozen global without
// running anything, and [Script.Call] and [Script.CallN] call any function with Values.
//
// [Runtime.Expr] compiles an expression over the fields of a Go struct into a [Rule]:
//
//	rule, err := rt.Expr[Order, bool]("gold", `total > 100 and customer.tier == "gold"`)
//	ok, err := rule.Eval(ctx, &order)
//
// Free names are the struct's fields, then the Runtime's globals; a misspelt name is an error
// from Expr, not from Eval. In a chunk, fields tagged rw can be assigned and come back to Go.
// [Eval] runs a chunk on a default Runtime, for one-off use.
//
// # Freezing
//
// After the top level runs, Load freezes every table reachable from the globals and from what
// the chunk returned, their metatables included, and every captured variable that closures can
// write. Writing one later raises an ordinary Lua error, "attempt to modify a frozen table".
// A call can still build and change tables of its own, which die with the call. Load fails if
// the state reaches something that cannot be shared: a coroutine, a library function with
// hidden state such as a gmatch iterator, a file, or a Go value a script can change, itself
// or through its fields: one of a type with writable fields or a __newindex metamethod, or
// that the host marked [Mutable]. State that must outlive a call belongs in a host function
// or in a [VM].
//
// Names that the host or the libraries define are reserved: a script cannot assign them,
// although it can shadow them with a local.
//
// # Host functions
//
// [GoFunc] is the one native signature for Go functions called from Lua. [Call] gives a
// GoFunc its arguments, with [Call.Arg] and [Call.Opt] converting them, and takes its results
// with [Call.Return]. The typed adapters [Fn1], [Fn2E], [Do1] and their relatives wrap plain
// Go functions without reflection; [Reflect] wraps any function by reflection, and is never
// applied implicitly. A first parameter of type [context.Context] receives the call's context
// and takes no Lua argument. Host functions see their arguments the Lua way: a numeric string
// is a number. Results going back to Go are strict.
//
// # Go values in Lua
//
// Scalars and strings convert directly; time.Duration is a number of seconds. A pointer to a
// struct is a userdata whose fields Lua reads by their snake_case names, or the name a lua
// struct tag gives; fields are read-only unless tagged rw. Nested structs, slices and maps are
// live views of the Go value. [Type] adds methods and metamethods and renames, hides or opens
// fields; [Convert] gives a type a scalar or string form instead. Values, tables and GoFuncs
// pass through. [ValueOf] and [Value.As] convert by the same rules.
//
// # Limits
//
// Every entry from Go runs under [Limits]: a step budget, an allocation budget, a call depth,
// a depth of nesting between Go and Lua and, if set, a time. A zero field takes its default,
// so a Runtime made with no options is bounded. Running out of steps, bytes or time, nesting
// too deep and a cancelled context are terminal errors: pcall cannot catch them, and the
// entry returns them as an [*Error] that wraps [ErrSteps], [ErrAlloc], [ErrTime],
// [ErrHostDepth] or the context's cause. A host function ends the entry the same way by
// returning an error made with [Terminate]. A set of fixed caps holds even with [NoLimit].
// [Hardened] is the profile for untrusted scripts. An entry that runs long and waits on its
// host can have its budgets and time renewed after each wait, with [Call.Renew].
//
// The documents under docs/ in the repository describe the sandbox and limits in full, the
// ways glua differs from Lua 5.4, and how common tasks look in GopherLua and in glua.
//
// # Errors
//
// A runtime error is an [*Error]: Error returns one line such as "policy.lua:4: boom",
// [Error.Traceback] the frames it passed through, and Unwrap the Go error behind it. A Go
// error returned by a host function is a string inside Lua; if that same string leaves Lua,
// errors.Is and errors.As still find the original, as they find the error of a module that
// require could not load. Code that does not compile gives a [*SyntaxError], and a binding
// that cannot work a [*BindError], before anything runs.
package glua
