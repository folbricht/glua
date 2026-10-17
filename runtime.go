package glua

import (
	"context"
	"errors"
	"fmt"
	"io"
	"math"
	"reflect"
	"sort"
	"strings"
	"sync"
	"sync/atomic"
	"time"

	"github.com/folbricht/glua/internal/syntax"
)

// Runtime is the host side of the sandbox: libraries, globals, modules, bound Go types and
// limits. It never changes after New, so it is safe to share between goroutines.
type Runtime struct {
	libs    Lib
	run     limits // for calls
	init    limits // for the top level, in Load and NewVM
	layer   *Table // frozen: the libraries, host globals and Go modules every environment starts with
	modules *Table // frozen: the Go modules, by name, for package.loaded
	sources map[string]*Chunk
	loader  func(name string) (string, error)
	chunks  func(ctx context.Context, name string) (*Chunk, error) // ChunkLoader's

	reserved map[string]bool // names a script cannot assign
	without  map[string]bool // the names Without left out of each environment
	strMeta  *Table          // the metatable all strings share
	out      writeFunc       // nil discards
	randSeed *uint64
	clock    func() time.Time
	started  time.Time // when New ran, by the clock: os.clock counts from here
	observe  func(CallStats)
	autoBind bool
	strict   bool
	recover  bool
	hardened bool
	checked  bool

	custom     map[uint64]*typeInfo  // plans customised by Type, by type ID
	registered map[reflect.Type]bool // the types Type registered
	planCache  atomic.Pointer[planSet]
	planMu     sync.Mutex

	pool sync.Pool // executors; they hold no script state, so one pool serves every Script and Rule
}

// limits are resolved Limits: no zero means default, and no NoLimit.
type limits struct {
	steps     int64
	alloc     int64
	callDepth int
	hostDepth int
	time      time.Duration // 0: none
}

// Lib options are OR-ed together. With none given, LibSafe is used.
type Lib uint

const (
	LibBase      Lib = 1 << iota // the base library, without dofile and loadfile; also require and package
	LibString                    // string, with pack and unpack
	LibTable                     // table
	LibMath                      // math
	LibUTF8                      // utf8
	LibCoroutine                 // coroutine
	LibOS                        // os: clock, time, date and difftime only
	LibIO                        // io, for trusted scripts only
	LibLoad                      // load: compile text at run time

	LibNone Lib = 1 << 31                                            // an empty environment; with other flags, only those
	LibSafe     = LibBase | LibString | LibTable | LibMath | LibUTF8 // the default
)

func (l Lib) apply(o *options) { o.libs |= l; o.libsSet = true }

// Limits apply to one entry from Go, including everything it re-enters, until a host
// function renews them with Call.Renew. A zero field takes the default. NoLimit switches a
// limit off.
type Limits struct {
	Steps          int64 // default 10M. Back-edges, calls, and library work in proportion to its size
	AllocBytes     int64 // default 64 MiB. Charged before each allocation made for the script
	CallDepth      int   // default 10,000 Lua frames. Catchable "stack overflow"
	HostDepth      int   // default 100 nested Go re-entries
	InitSteps      int64 // defaults to Steps. Used by Load and NewVM for the top level
	InitAllocBytes int64 // defaults to AllocBytes
	// Time is how long an entry may run, checked as it takes steps, and given afresh by
	// Renew; default none. A nested entry made with a host function's Call.Context ends
	// with it. A host function's own time counts, but one that runs long is not
	// interrupted, nor is its context cancelled.
	Time time.Duration
}

func (l Limits) apply(o *options) { o.limits = l }

// NoLimit switches a limit off. The fixed caps still hold.
const NoLimit = -1

// Caps that hold even with NoLimit.
const (
	maxCallFrames = 1 << 20 // frames; the register stack's cap is reached first
	maxHostDepth  = 10000   // nested Go re-entries: each one uses Go stack
)

// Option is implemented by Lib, Limits and the results of the functions below.
type Option interface{ apply(*options) }

type optionFunc func(*options)

func (f optionFunc) apply(o *options) { f(o) }

// options is what the options of New collect.
type options struct {
	libs     Lib
	libsSet  bool
	limits   Limits
	globals  []namedValue
	modules  []namedValue
	sources  []namedValue
	loader   func(string) (string, error)
	chunks   func(context.Context, string) (*Chunk, error)
	without  []string
	output   writeFunc
	randSeed *uint64
	clock    func() time.Time
	observe  func(CallStats)
	autoBind *bool
	strict   bool
	recover  bool
	hardened bool
	checked  *bool // tests choose the loop
	converts []convertReg
	types    []*typeOptions
}

type namedValue struct {
	name string
	v    any
}

// Members holds the contents of a module: GoFuncs, scalars, strings, nested Members,
// pointers to bound types.
type Members map[string]any

// Global defines a global that every script of the Runtime sees, under a reserved name.
// Tables given here are frozen.
func Global(name string, v any) Option {
	return optionFunc(func(o *options) { o.globals = append(o.globals, namedValue{name, v}) })
}

// Module defines a module of Go members. It is a global under its name, and require returns
// the same table.
func Module(name string, members Members) Option {
	return optionFunc(func(o *options) { o.modules = append(o.modules, namedValue{name, members}) })
}

// SourceModule defines a module written in Lua, which require runs in the environment that
// loads it.
func SourceModule(name, src string) Option {
	return optionFunc(func(o *options) { o.sources = append(o.sources, namedValue{name, src}) })
}

// Loader gives require the source of modules not defined by Module or SourceModule. It runs
// only while a script loads, or in a VM. An error it returns, or the *SyntaxError of its
// source, is behind the error of require, for errors.Is and errors.As.
func Loader(find func(name string) (src string, err error)) Option {
	return optionFunc(func(o *options) { o.loader = find })
}

// Without leaves out names the libraries define: globals such as "collectgarbage" or
// "require", or library members such as "string.rep". A global left out is free, so the
// host may define its own under it with Global or Module, and a script may assign it. Strings'
// methods are the string library's, so leaving out "string.rep" takes s:rep too, while
// leaving out "string" takes only the global. Naming something the libraries do not define
// is an error from New.
func Without(names ...string) Option {
	return optionFunc(func(o *options) { o.without = append(o.without, names...) })
}

// ChunkLoader is Loader for a host that compiles modules itself: find receives the context
// of the entry that requires name, so it can choose the module by who asks, and returns it
// compiled, so it can name it in messages as it likes and give the same Chunk again rather
// than have each environment compile it. Like Loader, it runs from any goroutine that loads
// a Script or makes a VM, so it must be safe for concurrent use. An error from find says
// the module was not found, or did not compile when it is or wraps a *SyntaxError; so does
// a nil Chunk. A Chunk's source is not charged to the script, as a SourceModule's is not.
// Loader and ChunkLoader cannot both be given.
func ChunkLoader(find func(ctx context.Context, name string) (*Chunk, error)) Option {
	return optionFunc(func(o *options) { o.chunks = find })
}

// Output is where print and warn write; the default discards. Writes are serialised, so w
// need not be safe for concurrent use. Of Output and OutputFunc, the last given wins.
func Output(w io.Writer) Option {
	return optionFunc(func(o *options) { o.output = writerOutput(w) })
}

// OutputFunc is Output for a host that needs to know which entry wrote: f receives what
// Output's writer would, one call for each print, warn or io.write, with the entry's
// context, so it can tag the text with the request or tenant behind it. Calls are not
// serialised: f must be safe for concurrent use. An error it returns is raised in the
// script, as a write error is.
func OutputFunc(f func(ctx context.Context, s string) error) Option {
	return optionFunc(func(o *options) { o.output = f })
}

// RandSeed seeds math.random at the start of every entry, for reproducible runs. It also
// makes math.randomseed() without arguments reproducible: it takes its seed from the generator.
func RandSeed(seed uint64) Option { return optionFunc(func(o *options) { o.randSeed = &seed }) }

// Clock is the time source of the os library.
func Clock(now func() time.Time) Option { return optionFunc(func(o *options) { o.clock = now }) }

// Observe is called after every entry from Go with what it used.
func Observe(f func(CallStats)) Option { return optionFunc(func(o *options) { o.observe = f }) }

// AutoBind chooses whether Go types statically reachable from a binding are bound with the
// default rules. Without it, only types registered with Type are. It is on by default, and
// off under Hardened.
func AutoBind(on bool) Option { return optionFunc(func(o *options) { o.autoBind = &on }) }

// StrictGlobals makes reading an undefined global an error, instead of nil.
func StrictGlobals() Option { return optionFunc(func(o *options) { o.strict = true }) }

// RecoverPanics turns a panic in a host function into a *PanicError returned by the entry,
// instead of letting it continue.
func RecoverPanics() Option { return optionFunc(func(o *options) { o.recover = true }) }

// Hardened is the profile for untrusted scripts: the bounds-checked loop, AutoBind(false), no
// LibLoad, LibCoroutine, LibOS or LibIO, no NoLimit, and maps and slices passed by copy.
func Hardened() Option { return optionFunc(func(o *options) { o.hardened = true }) }

// withLoop chooses the loop, for tests: checked or fast.
func withLoop(checked bool) Option { return optionFunc(func(o *options) { o.checked = &checked }) }

// CallStats is what one entry from Go used, as Observe reports it.
type CallStats struct {
	Script, Func      string
	Steps, AllocBytes int64
	Err               error
}

// New makes a Runtime. It reports bad options: a value that cannot be converted, a duplicate
// name, a syntax error in a source module, both Loader and ChunkLoader.
func New(opts ...Option) (*Runtime, error) {
	used.Store(true)
	var o options
	for _, opt := range opts {
		opt.apply(&o)
	}
	rt := &Runtime{
		libs:     LibSafe,
		loader:   o.loader,
		chunks:   o.chunks,
		randSeed: o.randSeed,
		clock:    o.clock,
		observe:  o.observe,
		autoBind: !o.hardened,
		strict:   o.strict,
		recover:  o.recover,
		hardened: o.hardened,
		checked:  defaultChecked || o.hardened,
		reserved: map[string]bool{},
		without:  map[string]bool{},
		sources:  map[string]*Chunk{},
	}
	if o.libsSet {
		rt.libs = o.libs &^ LibNone
	}
	if o.autoBind != nil {
		rt.autoBind = *o.autoBind
	}
	if o.checked != nil && !o.hardened {
		rt.checked = *o.checked
	}
	rt.out = o.output
	if rt.clock == nil {
		rt.clock = time.Now
	}
	rt.started = rt.clock()
	if o.loader != nil && o.chunks != nil {
		return nil, errors.New("glua: Loader and ChunkLoader cannot both be given")
	}
	if o.hardened {
		if bad := rt.libs & (LibLoad | LibCoroutine | LibOS | LibIO); bad != 0 {
			return nil, fmt.Errorf("glua: the hardened profile refuses %s", bad)
		}
	}
	for _, c := range o.converts {
		if err := c.register(); err != nil {
			return nil, err
		}
	}
	if err := rt.registerTypes(o.types); err != nil {
		return nil, err
	}
	var err error
	if rt.run, rt.init, err = resolveLimits(o.limits, o.hardened); err != nil {
		return nil, err
	}
	if err := rt.buildLayer(&o); err != nil {
		return nil, err
	}
	rt.pool.New = func() any { return rt.newExecutor() }
	return rt, nil
}

// MustNew is New for package-level variables. It panics on error.
func MustNew(opts ...Option) *Runtime {
	rt, err := New(opts...)
	if err != nil {
		panic(err)
	}
	return rt
}

// String returns the names of the flags in l, such as "LibLoad|LibCoroutine".
func (l Lib) String() string {
	names := []string{"LibBase", "LibString", "LibTable", "LibMath", "LibUTF8", "LibCoroutine", "LibOS", "LibIO", "LibLoad"}
	s := ""
	for i, name := range names {
		if l&(1<<i) != 0 {
			if s != "" {
				s += "|"
			}
			s += name
		}
	}
	if l&LibNone != 0 {
		if s != "" {
			s += "|"
		}
		s += "LibNone"
	}
	if s == "" {
		return "Lib(0)"
	}
	return s
}

// resolveLimits fills in defaults and checks the limits against the profile.
func resolveLimits(l Limits, hardened bool) (run, init limits, err error) {
	check := func(name string, v int64) error {
		if v < NoLimit {
			return fmt.Errorf("glua: Limits.%s is negative: %d", name, v)
		}
		if v == NoLimit && hardened {
			return fmt.Errorf("glua: the hardened profile refuses NoLimit for Limits.%s", name)
		}
		return nil
	}
	for _, f := range []struct {
		name string
		v    int64
	}{
		{"Steps", l.Steps}, {"AllocBytes", l.AllocBytes}, {"CallDepth", int64(l.CallDepth)},
		{"HostDepth", int64(l.HostDepth)}, {"InitSteps", l.InitSteps}, {"InitAllocBytes", l.InitAllocBytes},
	} {
		if err := check(f.name, f.v); err != nil {
			return run, init, err
		}
	}
	if l.Time < 0 && l.Time != NoLimit {
		return run, init, fmt.Errorf("glua: Limits.Time is negative: %v", l.Time)
	}
	pick := func(v, def, unlimited int64) int64 {
		switch v {
		case 0:
			return def
		case NoLimit:
			return unlimited
		}
		return v
	}
	run = limits{
		steps:     pick(l.Steps, defaultSteps, math.MaxInt64),
		alloc:     pick(l.AllocBytes, defaultAlloc, math.MaxInt64),
		callDepth: int(min(pick(int64(l.CallDepth), defaultDepth, maxCallFrames), maxCallFrames)),
		hostDepth: int(min(pick(int64(l.HostDepth), defaultHost, maxHostDepth), maxHostDepth)),
		time:      max(l.Time, 0),
	}
	init = run
	init.steps = pick(l.InitSteps, run.steps, math.MaxInt64)
	init.alloc = pick(l.InitAllocBytes, run.alloc, math.MaxInt64)
	return run, init, nil
}

// buildLayer builds the frozen table of what every environment starts with: the libraries,
// the host globals and the Go modules. Their names are reserved.
func (rt *Runtime) buildLayer(o *options) error {
	g := NewTable(0, 32)
	if rt.libs&LibBase != 0 {
		openBase(g)
	}
	if rt.libs&LibString != 0 {
		rt.strMeta = openString(g)
	}
	if rt.libs&LibTable != 0 {
		openTable(g)
	}
	if rt.libs&LibMath != 0 {
		openMath(g)
	}
	if rt.libs&LibUTF8 != 0 {
		openUTF8(g)
	}
	if rt.libs&LibOS != 0 {
		openOS(g)
	}
	if rt.libs&LibIO != 0 {
		openIO(g, rt)
	}
	if rt.libs&LibCoroutine != 0 {
		g.Set(String("coroutine"), tableValue(coroutineLib()))
	}
	g.Set(String("_G"), Value{}) // per environment
	if err := rt.leaveOut(g, o.without); err != nil {
		return err
	}
	for k := range g.All() {
		rt.reserved[k.str()] = true
	}
	for _, name := range []string{"_G", "package", "require", "load"} {
		if rt.envName(name) && !rt.without[name] {
			rt.reserved[name] = true
		}
	}
	define := func(name string, v Value) error {
		if v.n>>56 == kindUser && !isScalar(v.p) {
			if ti := userType(v); ti != nil {
				if err := rt.checkType(ti.rt); err != nil {
					return bindName(name, err)
				}
			}
		}
		if !isName(name) {
			return &BindError{Name: name, Reason: "not a Lua name"}
		}
		if !g.Get(String(name)).IsNil() || rt.reserved[name] {
			return &BindError{Name: name, Reason: "the name is already defined"}
		}
		g.Set(String(name), v)
		rt.reserved[name] = true
		return nil
	}
	for _, nv := range o.globals {
		v, err := hostValue(nv.name, nv.v, "")
		if err != nil {
			return err
		}
		if err := define(nv.name, v); err != nil {
			return err
		}
	}
	rt.modules = NewTable(0, len(o.modules))
	for _, nv := range o.modules {
		v, err := hostValue(nv.name, nv.v, nv.name+".")
		if err != nil {
			return err
		}
		if err := define(nv.name, v); err != nil {
			return err
		}
		rt.modules.Set(String(nv.name), v)
	}
	for _, nv := range o.sources {
		name, src := nv.name, nv.v.(string)
		if _, ok := rt.sources[name]; ok || !rt.modules.Get(String(name)).IsNil() {
			return &BindError{Name: name, Reason: "the module is already defined"}
		}
		m, err := compileModule(name, src)
		if err != nil {
			return err
		}
		rt.sources[name] = m
	}
	fr := newFreezer()
	fr.plans, fr.intern = rt.plans(), maxInterned
	fr.add(tableValue(g), "globals")
	if rt.strMeta != nil {
		fr.add(tableValue(rt.strMeta), "the string metatable") // its library, even when Without left out the global
	}
	if err := fr.walk(); err != nil {
		return &BindError{Reason: err.Error()}
	}
	fr.freeze()
	if err := freezeValue(tableValue(rt.modules), "package.loaded"); err != nil { // the modules are frozen already
		return &BindError{Reason: err.Error()}
	}
	rt.layer = g
	return nil
}

// leaveOut removes the names given to Without from the libraries in g. Every name is found
// before any is removed, so their order does not matter. The names newEnv gives each
// environment are recorded in rt.without for newEnv to leave out.
func (rt *Runtime) leaveOut(g *Table, names []string) error {
	type member struct {
		t   *Table
		key Value
	}
	var drop []member
	for _, name := range names {
		if rt.envName(name) {
			rt.without[name] = true
			continue
		}
		t, key := g, name
		if lib, k, ok := strings.Cut(name, "."); ok {
			t, key = nil, k
			if v := g.Get(String(lib)); v.isObj(kindTable) {
				t = (*Table)(v.p)
			}
		}
		if t == nil || t.Get(String(key)).IsNil() {
			return &BindError{Name: name, Reason: "the libraries define no such name"}
		}
		drop = append(drop, member{t, String(key)})
	}
	for _, m := range drop {
		m.t.Set(m.key, Value{})
	}
	return nil
}

// envName reports whether name is one of the globals newEnv gives each environment rather
// than the layer: _G, and package, require and load when their libraries are open.
func (rt *Runtime) envName(name string) bool {
	switch name {
	case "_G":
		return true
	case "package", "require":
		return rt.libs&LibBase != 0
	case "load":
		return rt.libs&LibLoad != 0
	}
	return false
}

// compileModule compiles the source of a module.
func compileModule(name, src string) (*Chunk, error) {
	p, info, err := compile("="+name, src)
	if err != nil {
		return nil, err
	}
	return &Chunk{p: p, info: info}, nil
}

// newExecutor makes an executor for this Runtime's pool.
func (rt *Runtime) newExecutor() *executor {
	ex := newExecutor()
	ex.rt = rt
	ex.types = rt.plans()
	ex.strMeta = rt.strMeta
	if rt.strMeta != nil && rt.strMeta.flags&tabFrozen != 0 {
		if h := rt.strMeta.metaGet("__index"); h.isObj(kindTable) {
			ex.strIdx = (*Table)(h.p)
		}
	}
	ex.randSeed = rt.randSeed
	ex.checked = rt.checked
	ex.output = rt.out
	return ex
}

// setLimits gives the executor the limits of the entry about to start.
func (ex *executor) setLimits(l *limits) {
	ex.maxSteps, ex.maxAlloc = l.steps, l.alloc
	ex.maxCallDepth, ex.maxHostDepth = l.callDepth, l.hostDepth
	ex.maxTime = l.time
}

// writeFunc is where print and warn write: the Output writer or the OutputFunc function.
type writeFunc func(ctx context.Context, s string) error

// writerOutput is the output of an Output writer: one write at a time. A nil writer discards.
func writerOutput(w io.Writer) writeFunc {
	if w == nil {
		return nil
	}
	var mu sync.Mutex
	return func(_ context.Context, s string) error {
		mu.Lock()
		defer mu.Unlock()
		_, err := io.WriteString(w, s)
		return err
	}
}

// isName reports whether s is a Lua name: letters, digits and underscores, not starting
// with a digit, and not a reserved word.
func isName(s string) bool {
	if s == "" || syntax.IsReserved(s) {
		return false
	}
	for i := 0; i < len(s); i++ {
		c := s[i]
		if !(c == '_' || 'a' <= c && c <= 'z' || 'A' <= c && c <= 'Z' || i > 0 && '0' <= c && c <= '9') {
			return false
		}
	}
	return true
}

// hostValue converts a value given to Global or Module. Functions must be GoFuncs: a bare
// Go function needs an explicit adapter. qual is the name messages give a function from a
// call that names none, and for Members the prefix of its functions' names: "m." for a
// module's, so that they are named m.f as C Lua's pushglobalfuncname names them.
func hostValue(name string, v any, qual string) (Value, error) {
	switch x := v.(type) {
	case GoFunc:
		return goFnValue(&goFunc{name: name, qualname: qual, f: x, host: true}), nil
	case func(*Call) error:
		return goFnValue(&goFunc{name: name, qualname: qual, f: x, host: true}), nil
	case Members:
		t := NewTable(0, len(x))
		keys := make([]string, 0, len(x))
		for k := range x {
			keys = append(keys, k)
		}
		sort.Strings(keys)
		for _, k := range keys {
			memberQual := ""
			if _, nested := x[k].(Members); qual != "" && !nested { // as C Lua, which names no deeper
				memberQual = qual + k
			}
			mv, err := hostValue(k, x[k], memberQual)
			if err != nil {
				var be *BindError
				if errors.As(err, &be) {
					be.Name = name + "." + be.Name
				}
				return Value{}, err
			}
			t.Set(String(k), mv)
		}
		return tableValue(t), nil
	}
	if v != nil && reflect.TypeOf(v).Kind() == reflect.Func {
		return Value{}, &BindError{Name: name, Type: reflect.TypeOf(v), Reason: "a Go function needs an adapter, such as lua.Fn1 or lua.Reflect"}
	}
	val, err := toValue(v)
	if err != nil {
		return Value{}, &BindError{Name: name, Type: reflect.TypeOf(v), Reason: err.Error()}
	}
	return val, nil
}

// newEnv builds the globals table of a new environment: the Runtime's layer, plus what
// belongs to the environment, but for what Without left out: _G; package and require with
// LibBase; load with LibLoad.
func (rt *Runtime) newEnv(ld *envLoader) *Table {
	env := NewTable(0, rt.layer.used+8)
	for k, v := range rt.layer.All() {
		env.set(k, v)
	}
	if !rt.without["_G"] {
		env.set(String("_G"), tableValue(env))
	}
	if rt.libs&LibLoad != 0 && !rt.without["load"] {
		env.set(String("load"), goFnValue(&goFunc{name: "load", f: func(c *Call) error { return baseLoad(c, env) }}))
	}
	if rt.libs&LibBase != 0 {
		if !rt.without["package"] {
			pkg := NewTable(0, 2)
			pkg.set(String("loaded"), tableValue(ld.loaded))
			env.set(String("package"), tableValue(pkg))
		}
		if !rt.without["require"] {
			env.set(String("require"), goFnValue(&goFunc{name: "require", f: ld.require}))
		}
	}
	if rt.strict {
		mt := NewTable(0, 1)
		mt.set(String("__index"), goFnValue(strictIndex))
		env.meta = mt
	}
	env.flags |= tabGuarded
	ld.env = env
	return env
}

// strictIndex is the __index of an environment under StrictGlobals.
var strictIndex = &goFunc{name: "strict", f: func(c *Call) error {
	k := c.Value(1)
	if k.isString() {
		return c.libErrorf("undefined global '%s'", k.str())
	}
	return c.libErrorf("undefined global %s", k.String())
}}

// envLoader is the record of the modules an environment loaded. require can load a module
// for the first time only while the environment is being built, or in a private VM.
type envLoader struct {
	rt     *Runtime
	env    *Table
	loaded *Table // package.loaded of the environment
}

func newEnvLoader(rt *Runtime) *envLoader {
	ld := &envLoader{rt: rt, loaded: NewTable(0, rt.modules.used+4)}
	for k, v := range rt.modules.All() {
		ld.loaded.set(k, v)
	}
	return ld
}

// require is require(name): the module from package.loaded, or else a source module or
// one the Loader or ChunkLoader finds, run now and recorded.
func (ld *envLoader) require(c *Call) error {
	name, err := c.checkString(0, "require")
	if err != nil {
		return err
	}
	if v := ld.loaded.Get(String(name)); !v.IsNil() {
		return c.ReturnValues(v)
	}
	if ld.loaded.Frozen() {
		return c.libErrorf("module '%s' not found: modules can be loaded only while the script loads", name)
	}
	m := ld.rt.sources[name]
	if m == nil && ld.rt.chunks != nil {
		if m, err = ld.rt.chunks(c.Context(), name); err != nil {
			var se *SyntaxError
			if errors.As(err, &se) {
				return c.libErrorCause(err, "error loading module '%s': %s", name, err.Error())
			}
			return c.libErrorCause(err, "module '%s' not found: %s", name, err.Error())
		}
	}
	if m == nil && ld.rt.loader != nil {
		src, err := ld.rt.loader(name)
		if err != nil {
			return c.libErrorCause(err, "module '%s' not found: %s", name, err.Error())
		}
		if err := c.ex.charge(len(src)); err != nil {
			return err
		}
		if m, err = compileModule(name, src); err != nil {
			return c.libErrorCause(err, "error loading module '%s': %s", name, err.Error())
		}
	}
	if m == nil || m.p == nil { // a zero Chunk from ChunkLoader is none
		return c.libErrorf("module '%s' not found", name)
	}
	res, err := c.call(luaFnValue(newMainClosure(m.p, m.info, ld.env)), String(name))
	if err != nil {
		return err
	}
	v := Bool(true)
	if len(res) > 0 && !res[0].IsNil() {
		v = res[0]
	}
	if got := ld.loaded.Get(String(name)); !got.IsNil() {
		v = got // the module set package.loaded itself
	}
	ld.loaded.Set(String(name), v)
	return c.ReturnValues(v)
}
