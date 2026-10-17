# Sandbox and limits

glua is built to run scripts the host does not fully trust: rules written by customers,
policies, handlers. This document says what the sandbox promises, what the host controls, and
what remains the host's job.

## What a script cannot do

Whatever a script does, it cannot:

- reach files, processes, the network, the environment or the clock, unless the host grants
  it with a library or a host function;
- run without bound, or allocate without bound;
- crash the process: exhaust the Go stack, run it out of memory with one allocation, or hit a
  fault that `recover` cannot stop;
- see data from another call, because a shared script's state is frozen;
- learn heap addresses, because `tostring` and `%p` show a keyed hash.

The sandbox does not cover what host functions do, data races the host creates on Go values it
passes in, or timing side channels.

## Two profiles

| | Default | `lua.Hardened()` |
| --- | --- | --- |
| Libraries | `LibSafe`; more on request | `LibSafe` only: `New` fails if `LibLoad`, `LibCoroutine`, `LibOS` or `LibIO` is added |
| Go types | Bound when a binding reaches them | Only types registered with `lua.Type[T]` |
| Slices and maps in bound structs | Live views of the Go value | Copies |
| Limits | Defaults; `NoLimit` allowed | Defaults; `NoLimit` refused |

`LibSafe` is the base library, `string`, `table`, `math` and `utf8`. The `io` library gives a
script the file system, and is meant for trusted scripts only. `Without` trims single names
from what the libraries give, such as `string.rep` or `collectgarbage`.

## Limits

Limits apply to one entry from Go: a call through a function from `FuncN`, `Call` or
`Rule.Eval`, or the top level that `Load` and `NewVM` run. They cover everything the entry
runs, nested calls included, until a host function renews them ([Long entries](#long-entries)).
A zero field takes the default, so a `Runtime` made with no options is bounded; `lua.NoLimit`
switches a limit off.

| Limit | Default | What it counts | When it runs out |
| --- | --- | --- | --- |
| `Steps` | 10 million | Backward jumps, calls, and library work in proportion to its size: a step per 64 bytes a library function produces or a pattern match works through, per comparison in `table.sort`, per 8 values copied for varargs | `ErrSteps`, terminal |
| `AllocBytes` | 64 MiB | Bytes allocated for the script: tables and their growth, closures, strings, coroutines, stack growth, host functions' results, `load`'s source. It counts what is allocated, not what is live | `ErrAlloc`, terminal |
| `CallDepth` | 10,000 | Lua frames | `stack overflow`, which `pcall` can catch |
| `HostDepth` | 100 | Nesting of Go and Lua: host functions that call back into Lua, library callbacks such as sort's comparator, scripts called from host functions | `ErrHostDepth`, terminal |
| `InitSteps`, `InitAllocBytes` | `Steps`, `AllocBytes` | The same, for the top level in `Load` and `NewVM` | As above |
| `Time` | none | Wall-clock time since the entry started or last renewed, checked every 1,024 steps and when a host function charges for its work. Nested entries made with a host function's `Context` end with it, and that context reports it as its deadline; a host function that runs long is not interrupted | `ErrTime`, terminal |
| context | none | Checked when the entry starts, again every 1,024 steps, and when a host function returns an error | The context's cause, terminal |

`Script.WithLimits` gives the same code and state other limits, for example per tenant. The
`Observe` option reports what each entry used.

### Terminal errors

Running out of steps or bytes, nesting too deep, a cancelled context, and a host function
returning an error made with `lua.Terminate`, end the entry:

- `pcall`, `xpcall`, message handlers and `coroutine.resume` never see them.
- After a host function returns, the error stands, whatever the function did with it.
- `__close` handlers written in Lua still run, sharing a grace budget of 1,024 steps and 4 KB.
- The entry returns an `*lua.Error` that unwraps to `ErrSteps`, `ErrAlloc`, `ErrTime`,
  `ErrHostDepth`, the context's cause or the error given to `Terminate`, with the script's
  position and traceback.

### Budgets across scripts

A host function that calls another script with `c.Context()` shares the entry's budgets: the
nested call can use at most what the entry has left, and what it uses is charged back. A
nested call made with an unrelated context gets budgets of its own.

### Long entries

An entry that runs long and waits on its host, such as a session that reads input or a worker
that waits for events, would run out of any budget in the end. A host function that calls
`c.Renew()` after each wait gives the entry its step and allocation budgets, and its `Time`,
afresh, so they bound the work between waits rather than over the whole entry; `Observe`
still counts the whole. A deadline on the entry's context still holds for the whole entry. Renew only after a real wait: a script that loops on a function that renews at once is
bounded by its context alone. A nested call made with `c.Context()` cannot renew the budgets it
shares, and closers running on the grace budget cannot renew it.

### Memory an entry keeps

The allocation budget counts what is allocated, so it bounds what an entry keeps only until it
starts again: at a renewal, and at each call of a `VM`, whose state persists between calls. A
script that keeps a little more each round, or each call, grows without limit.
`c.LiveBytes()` and `vm.LiveBytes()` measure what an entry or a VM keeps reachable, at the
sizes the allocation budget charges; frozen state, which every entry shares, and Go values are
not counted. A host that runs such scripts without trusting them can check from time to time
and end the entry with `Terminate`. A measurement takes time in proportion to what it
measures. A script sees the same measure in `collectgarbage("count")`.

## Fixed caps

These hold even with `NoLimit`, because what they prevent would end the process.

| Cap | Value | What happens |
| --- | --- | --- |
| Syntax nesting in the parser | 200 levels | `chunk has too many syntax levels` |
| Depth of the syntax tree, chains such as `a.b.c` and `1+2+3` included | 2,000 | `chunk has too many syntax levels` |
| Pattern matching recursion | 200 levels; 32 captures | `pattern too complex`, `too many captures` |
| `__index` and `__newindex` chains | 2,000 | `'__index' chain too long; possible loop`, and the same for `__newindex` |
| `__call` chains | 2,000 | `stack overflow`; `'__call' chain too long; possible loop` for a metamethod; `attempt to call a table value` from `pcall` |
| Register stack | 1 million slots | `stack overflow` |
| Lua frames with `CallDepth: NoLimit` | about 1 million | `stack overflow` |
| Nesting of Go and Lua with `HostDepth: NoLimit` | 10,000 | `ErrHostDepth` |
| Any single allocation | 1 GiB, checked before the allocation | `ErrAlloc` |
| `string.format` width and precision | two digits, as in C Lua | `invalid conversion` |
| Go–Lua conversion | 64 levels deep, so cycles end too | A conversion error |

## Panics

A panic inside the VM itself is recovered at the entry and returned as a `*lua.PanicError`;
the bounds-checked interpreter loop of `Hardened` turns any VM bug into one. A panic in a host
function is the host's: it passes through to the caller, unless the `RecoverPanics` option turns it into a
`*lua.PanicError` too. Either way the executor involved is discarded. `runtime.Goexit` passes
through.

## The interpreter loop

glua has two interpreter loops generated from one source. The checked loop indexes everything
through bounds-checked slices, so even a VM bug is a recoverable panic. The fast loop reads
through raw pointers that the bytecode verifier vouches for, so a VM bug there could corrupt
memory instead. The fast loop is the default, after differential and coverage-guided fuzzing
of both loops; `Hardened` runs the checked one.

## What remains the host's job

- **Host functions must be safe for concurrent use.** A shared script calls them from every
  goroutine that calls the script. So must the functions given to `Loader` and `ChunkLoader`,
  which run for every goroutine that loads a script or makes a VM; what they return, error
  text and chunk names included, reaches the script.
- **Go values passed in are shared, not copied**, except structs passed by value and, under
  `Hardened`, slices and maps. No goroutine may write a value while a script can read it. Such
  a race can tear a string header or hit `concurrent map read and map write`, which no
  `recover` stops.
- **Go values and functions given to `Global` and `Module`** are reachable from every script
  of the Runtime.
- **A script's output** goes to the `Output` writer, serialised by the Runtime, or to the
  `OutputFunc` function with the entry's context, unserialised. Errors carry script text and
  values: decide what reaches your logs and users.
