package glua

import (
	"fmt"
	"math"
	"unique"

	"github.com/folbricht/glua/internal/syntax"
)

const (
	maxRegs   = 255 // registers per function; R255 marks an unpatched TESTSET target
	noReg     = 255
	noJump    = -1
	listFlush = 50 // table constructor items stored per SETLIST
)

// compileExpr compiles src as an expression over a Go struct: first as `return <src>`, and
// if that does not parse, as a chunk. The main function takes the struct as its parameter.
func compileExpr(source, src string, env *syntax.ExprEnv) (p *proto, info *syntax.Info, err error) {
	fn, err := syntax.ParseFixed(source, "return "+src)
	if err != nil {
		if fn, err = syntax.ParseFixed(source, src); err != nil {
			return nil, nil, err
		}
	}
	fn.Params = []string{env.Param}
	info, err = syntax.ResolveExpr(source, fn, env)
	if err != nil {
		return nil, nil, err
	}
	return compileResolved(source, fn, info)
}

// compileChunk parses, resolves and compiles a chunk into the prototype of its main function.
func compileChunk(source, src string) (p *proto, info *syntax.Info, err error) {
	fn, err := syntax.Parse(source, src)
	if err != nil {
		return nil, nil, err
	}
	info, err = syntax.Resolve(source, fn)
	if err != nil {
		return nil, nil, err
	}
	return compileResolved(source, fn, info)
}

// compileResolved generates the code of a resolved chunk.
func compileResolved(source string, fn *syntax.FunctionExpr, info *syntax.Info) (p *proto, _ *syntax.Info, err error) {
	c := &compiler{source: source, info: info}
	defer func() {
		if r := recover(); r != nil {
			e, ok := r.(*syntax.Error)
			if !ok {
				panic(r)
			}
			p, err = nil, e
		}
	}()
	return c.function(fn, nil), info, nil
}

type compiler struct {
	source string
	info   *syntax.Info
	// aliases are locals bound once to a built-in, as in local floor = math.floor, and never
	// assigned again: calls through them get a FASTCALL too
	aliases map[*syntax.Var]uint8
}

// ekind is the state of an expression that has been parsed but not yet placed. Like C Lua's
// expdesc, it lets the compiler pick an instruction form only once it knows where the value
// goes.
type ekind uint8

const (
	eVoid     ekind = iota // no value
	eNil                   // nil
	eTrue                  // true
	eFalse                 // false
	eK                     // a constant: val
	eLocal                 // a local in register info
	eCell                  // a local whose register info holds its cell
	eUpval                 // upvalue info, captured by value
	eUpCell                // upvalue info, which is a cell
	eGlobal                // global name
	eIndexed               // tbl[key]: see keyKind
	eNonReloc              // a value in register info
	eReloc                 // the instruction at info can put the value in any register
	eCall                  // the call at info; its result count can still change
	eVararg                // the VARARG at info; likewise
	eJmp                   // the compare-and-jump at info, which jumps when the test is true
)

type keyKind uint8

const (
	keyReg keyKind = iota // key in register key
	keyStr                // key is string constant key, an index below 256
	keyInt                // key is the integer key, 0..255
)

type expdesc struct {
	k    ekind
	val  Value
	info int
	name string
	tbl  int
	kk   keyKind
	key  int
	t, f []int // pending jumps, as aux-word sites: taken when the value is true / false
}

func (e *expdesc) hasJumps() bool { return len(e.t) > 0 || len(e.f) > 0 }

// fstate is the state of the function being compiled.
type fstate struct {
	c         *compiler
	parent    *fstate
	node      *syntax.FunctionExpr
	fi        *syntax.FuncInfo
	p         *proto
	kcache    map[kkey]int
	freereg   int
	nactive   int // registers held by active locals
	regOf     map[*syntax.Var]int
	consts    map[*syntax.Var]Value
	bl        *cblock
	line      int
	tbc       []int        // registers of active to-be-closed variables
	open      []int        // indices into p.locvars of the active locals, for their end pc
	target    int          // pc of the last jump target: no peephole across it
	fastCalls map[int]bool // CALLs a FASTCALL stands before
}

type kkey struct {
	kind uint8
	bits uint64
	s    string
}

// cblock is a block being compiled.
type cblock struct {
	parent  *cblock
	nactive int // registers active when the block was entered
	ntbc    int // len(fs.tbc) when the block was entered
	nlocs   int // len(fs.open) when the block was entered
	loop    bool
	breaks  []int
	labels  map[string]labelPos
	gotos   []*pendingGoto
}

type labelPos struct {
	pc    int
	level int
}

type pendingGoto struct {
	name  string
	site  int
	close bool // it leaves a block with to-be-closed variables
}

func (c *compiler) errorf(line int, format string, args ...any) {
	panic(&syntax.Error{Source: c.source, Line: line, Msg: fmt.Sprintf(format, args...)})
}

// function compiles one function and returns its prototype.
func (c *compiler) function(node *syntax.FunctionExpr, parent *fstate) *proto {
	fs := &fstate{
		c: c, parent: parent, node: node, fi: c.info.Funcs[node],
		p:      &proto{source: c.source, name: node.Name, vararg: node.IsVararg, nparams: uint8(len(node.Params))},
		kcache: map[kkey]int{},
		regOf:  map[*syntax.Var]int{},
		consts: map[*syntax.Var]Value{},
		line:   node.Line,
		target: -1,
	}
	if parent != nil {
		fs.p.linedefined, fs.p.lastline = int32(node.Line), int32(node.EndLine)
	}
	for _, u := range fs.fi.Upvals {
		d := upvalDesc{fromStack: u.Parent == nil}
		if u.Parent != nil {
			d.index = uint8(u.Parent.Index)
		} else if parent != nil {
			d.index = uint8(parent.regOf[u.Var])
		}
		fs.p.upvals = append(fs.p.upvals, d)
		fs.p.upnames = append(fs.p.upnames, u.Name)
	}
	fs.enterBlock(false)
	if node.IsVararg {
		fs.abc(opVarargPrep, len(node.Params), 0, 0)
	}
	params := c.info.Decls[node]
	fs.reserve(len(params))
	for i, v := range params {
		fs.activate(v, i)
	}
	for _, v := range params {
		if v.Cell() {
			fs.abc(opNewCell, fs.regOf[v], 0, 0)
		}
	}
	fs.stmts(node.Body.Stmts)
	fs.line = node.EndLine
	fs.leaveBlock()
	fs.abc(opReturn0, 0, 0, 0)
	fs.emit(opBad) // padding: pc never points past the allocation
	if err := verify(fs.p); err != nil {
		panic(fmt.Sprintf("glua: compiler produced invalid code: %v\n%s", err, fs.p.disasm()))
	}
	return fs.p
}

// emit appends one code word and its line.
func (fs *fstate) emit(w uint32) int {
	fs.p.code = append(fs.p.code, w)
	fs.p.lines = append(fs.p.lines, int32(fs.line))
	return len(fs.p.code) - 1
}

func (fs *fstate) abc(op uint8, a, b, c int) int {
	return fs.emit(iABC(op, uint8(a), uint8(b), uint8(c)))
}

func (fs *fstate) abx(op uint8, a, bx int) int {
	return fs.emit(iABx(op, uint8(a), uint16(bx)))
}

// site allocates a new hint site.
func (fs *fstate) site() uint32 {
	fs.p.hints = append(fs.p.hints, 0)
	return uint32(len(fs.p.hints) - 1)
}

func (fs *fstate) pc() int { return len(fs.p.code) }

// label marks the current pc as a jump target and returns it.
func (fs *fstate) label() int {
	fs.target = fs.pc()
	return fs.target
}

func (fs *fstate) setA(pc, a int) {
	fs.p.code[pc] = fs.p.code[pc]&^0xff00 | uint32(uint8(a))<<8
}

func (fs *fstate) setB(pc, b int) {
	fs.p.code[pc] = fs.p.code[pc]&^0xff0000 | uint32(uint8(b))<<16
}

func (fs *fstate) setC(pc, c int) {
	fs.p.code[pc] = fs.p.code[pc]&^0xff000000 | uint32(uint8(c))<<24
}

func (fs *fstate) setBx(pc, bx int) {
	fs.p.code[pc] = fs.p.code[pc]&0xffff | uint32(uint16(bx))<<16
}

// registers

func (fs *fstate) reserve(n int) {
	fs.freereg += n
	if fs.freereg > maxRegs-1 {
		fs.c.errorf(fs.line, "function or expression needs too many registers")
	}
	if fs.freereg > int(fs.p.maxstack) {
		fs.p.maxstack = uint8(fs.freereg)
	}
}

func (fs *fstate) freeReg(r int) {
	if r >= fs.nactive {
		fs.freereg--
		if r != fs.freereg {
			panic(fmt.Sprintf("glua: compiler freed register %d, expected %d", r, fs.freereg))
		}
	}
}

func (fs *fstate) freeExp(e *expdesc) {
	if e.k == eNonReloc {
		fs.freeReg(e.info)
	}
}

// freeExps frees two expressions' registers, the higher one first.
func (fs *fstate) freeExps(e1, e2 *expdesc) {
	r1, r2 := -1, -1
	if e1.k == eNonReloc {
		r1 = e1.info
	}
	if e2.k == eNonReloc {
		r2 = e2.info
	}
	if r1 > r2 {
		fs.freeRegOpt(r1)
		fs.freeRegOpt(r2)
	} else {
		fs.freeRegOpt(r2)
		fs.freeRegOpt(r1)
	}
}

func (fs *fstate) freeRegOpt(r int) {
	if r >= 0 {
		fs.freeReg(r)
	}
}

// activate makes v a local in register r.
func (fs *fstate) activate(v *syntax.Var, r int) {
	fs.regOf[v] = r
	fs.nactive = r + 1
	fs.p.locvars = append(fs.p.locvars, locVar{name: v.Name, reg: r, startpc: fs.pc(), endpc: -1})
	fs.open = append(fs.open, len(fs.p.locvars)-1)
}

// constants

func (fs *fstate) addK(v Value) int {
	var key kkey
	switch v.Kind() {
	case KindNil:
		key = kkey{kind: 0}
	case KindBool:
		key = kkey{kind: 1, bits: v.n}
	case KindInt:
		key = kkey{kind: 2, bits: v.n}
	case KindFloat:
		key = kkey{kind: 3, bits: v.n}
	case KindString:
		key = kkey{kind: 4, s: v.str()}
	}
	if i, ok := fs.kcache[key]; ok {
		return i
	}
	if v.isString() {
		h := unique.Make(v.str())
		fs.p.handles = append(fs.p.handles, h)
		register(v.str(), h)  // so that keys Go code sets find this pointer too
		v = String(h.Value()) // canonical: field names and constants share pointers
	}
	fs.p.k = append(fs.p.k, v)
	fs.p.khash = append(fs.p.khash, hashValue(v))
	i := len(fs.p.k) - 1
	fs.kcache[key] = i
	return i
}

func (fs *fstate) strK(s string) int { return fs.addK(String(s)) }

// loadK puts constant v in register r with the shortest form.
func (fs *fstate) loadK(r int, v Value) {
	switch {
	case v.p == tInt() && int64(v.n) >= math.MinInt16 && int64(v.n) <= math.MaxInt16:
		fs.abx(opLoadI, r, int(uint16(int16(int64(v.n)))))
		return
	case v.p == tFloat():
		f := math.Float64frombits(v.n)
		if f == math.Trunc(f) && f >= math.MinInt16 && f <= math.MaxInt16 && !(f == 0 && math.Signbit(f)) {
			fs.abx(opLoadF, r, int(uint16(int16(f))))
			return
		}
	}
	k := fs.addK(v)
	if k <= math.MaxUint16 {
		fs.abx(opLoadK, r, k)
	} else {
		fs.abc(opLoadKX, r, 0, 0)
		fs.emit(uint32(k))
	}
}

// jumps. A jump site is the index of the aux word that holds the offset.

func (fs *fstate) jump() int {
	fs.abc(opJmpX, 0, 0, 0)
	return fs.emit(0)
}

func (fs *fstate) condJump(op uint8, a, b, c int) int {
	fs.abc(op, a, b, c)
	return fs.emit(0)
}

func (fs *fstate) fixJump(site, target int) {
	fs.p.code[site] = uint32(int32(target - (site + 1)))
}

// jumpBack emits an unconditional backward jump to target, which ticks.
func (fs *fstate) jumpBack(target int) {
	off := target - (fs.pc() + 1)
	if off >= math.MinInt16 {
		fs.abx(opJmp, 0, int(uint16(int16(off))))
		return
	}
	site := fs.jump()
	fs.fixJump(site, target)
}

// patchTestReg makes the TESTSET at site store into reg, or turns it into a TESTJMP when
// the value is not needed. It reports whether the jump was a TESTSET.
func (fs *fstate) patchTestReg(site, reg int) bool {
	pc := site - 1
	i := fs.p.code[pc]
	if uint8(i) != opTestSet {
		return false
	}
	if reg != noReg && reg != decB(i) {
		fs.setA(pc, reg)
	} else {
		fs.p.code[pc] = iABC(opTestJmp, uint8(decB(i)), 0, uint8(decC(i)))
	}
	return true
}

func (fs *fstate) patchListAux(list []int, vtarget, reg, dtarget int) {
	for _, site := range list {
		if fs.patchTestReg(site, reg) {
			fs.fixJump(site, vtarget)
		} else {
			fs.fixJump(site, dtarget)
		}
	}
}

func (fs *fstate) patchList(list []int, target int) {
	fs.patchListAux(list, target, noReg, target)
}

func (fs *fstate) patchToHere(list []int) {
	fs.patchList(list, fs.label())
}

// needValue reports whether some jump in list is not a TESTSET, and so does not produce a value.
func (fs *fstate) needValue(list []int) bool {
	for _, site := range list {
		if uint8(fs.p.code[site-1]) != opTestSet {
			return true
		}
	}
	return false
}

// expressions

func (fs *fstate) setReturns(e *expdesc, n int) {
	switch e.k {
	case eCall:
		fs.setC(e.info, n+1)
	case eVararg:
		fs.setC(e.info, n+1)
		fs.setA(e.info, fs.freereg)
		fs.reserve(1)
	}
}

func (fs *fstate) setOneRet(e *expdesc) {
	switch e.k {
	case eCall:
		e.k, e.info = eNonReloc, decA(fs.p.code[e.info])
	case eVararg:
		fs.setC(e.info, 2)
		e.k = eReloc
	}
}

// dischargeVars turns a variable into a value: a register or an instruction to place.
func (fs *fstate) dischargeVars(e *expdesc) {
	switch e.k {
	case eLocal:
		e.k = eNonReloc
	case eCell:
		e.info, e.k = fs.abc(opGetCell, 0, e.info, 0), eReloc
	case eUpval:
		e.info, e.k = fs.abc(opGetUpval, 0, e.info, 0), eReloc
	case eUpCell:
		e.info, e.k = fs.abc(opGetUpCell, 0, e.info, 0), eReloc
	case eGlobal:
		k := fs.strK(e.name)
		if k <= math.MaxUint16 {
			e.info = fs.abx(opGetGlobal, 0, k)
			fs.emit(fs.site())
			e.k = eReloc
			return
		}
		r := fs.freereg // too many constants: GETENV, then a register key
		fs.reserve(2)
		fs.abc(opGetEnv, r, 0, 0)
		fs.loadK(r+1, String(e.name))
		fs.freeReg(r + 1)
		fs.freeReg(r)
		e.info, e.k = fs.abc(opGetTable, 0, r, r+1), eReloc
	case eIndexed:
		switch e.kk {
		case keyReg:
			fs.freeRegsOrdered(e.tbl, e.key)
			e.info = fs.abc(opGetTable, 0, e.tbl, e.key)
		case keyStr:
			fs.freeRegOptIfTemp(e.tbl)
			e.info = fs.abc(opGetField, 0, e.tbl, e.key)
			fs.emit(fs.site())
		case keyInt:
			fs.freeRegOptIfTemp(e.tbl)
			e.info = fs.abc(opGetIndex, 0, e.tbl, e.key)
		}
		e.k = eReloc
	case eCall, eVararg:
		fs.setOneRet(e)
	}
}

func (fs *fstate) freeRegOptIfTemp(r int) {
	if r >= fs.nactive {
		fs.freeReg(r)
	}
}

func (fs *fstate) freeRegsOrdered(r1, r2 int) {
	if r1 > r2 {
		fs.freeRegOptIfTemp(r1)
		fs.freeRegOptIfTemp(r2)
	} else {
		fs.freeRegOptIfTemp(r2)
		fs.freeRegOptIfTemp(r1)
	}
}

func (fs *fstate) discharge2reg(e *expdesc, reg int) {
	fs.dischargeVars(e)
	switch e.k {
	case eNil:
		fs.abc(opLoadNil, reg, 0, 0)
	case eFalse:
		fs.abc(opLoadFalse, reg, 0, 0)
	case eTrue:
		fs.abc(opLoadTrue, reg, 0, 0)
	case eK:
		fs.loadK(reg, e.val)
	case eReloc:
		fs.setA(e.info, reg)
	case eNonReloc:
		if reg != e.info {
			fs.abc(opMove, reg, e.info, 0)
		}
	default: // eJmp: nothing to do yet
		return
	}
	e.k, e.info = eNonReloc, reg
}

func (fs *fstate) discharge2anyreg(e *expdesc) {
	if e.k != eNonReloc {
		fs.reserve(1)
		fs.discharge2reg(e, fs.freereg-1)
	}
}

// codeLoadBool emits a boolean load and returns its pc.
func (fs *fstate) codeLoadBool(reg int, b bool) int {
	fs.label()
	if b {
		return fs.abc(opLoadTrue, reg, 0, 0)
	}
	return fs.abc(opLoadFalse, reg, 0, 0)
}

// exp2reg puts e in register reg, materialising true and false for pending jumps.
func (fs *fstate) exp2reg(e *expdesc, reg int) {
	fs.discharge2reg(e, reg)
	if e.k == eJmp {
		e.t = append(e.t, e.info+1)
	}
	if e.hasJumps() {
		pf, pt := noJump, noJump
		if fs.needValue(e.t) || fs.needValue(e.f) {
			fj := noJump
			if e.k != eJmp {
				fj = fs.jump()
			}
			pf = fs.codeLoadBool(reg, false)
			fs.abx(opJmp, 0, 1) // skip the LOADTRUE
			pt = fs.codeLoadBool(reg, true)
			if fj != noJump {
				fs.patchToHere([]int{fj})
			}
		}
		final := fs.label()
		fs.patchListAux(e.f, final, reg, pf)
		fs.patchListAux(e.t, final, reg, pt)
	}
	e.t, e.f = nil, nil
	e.k, e.info = eNonReloc, reg
}

func (fs *fstate) exp2nextreg(e *expdesc) {
	fs.dischargeVars(e)
	fs.freeExp(e)
	fs.reserve(1)
	fs.exp2reg(e, fs.freereg-1)
}

// exp2anyreg puts e in some register and returns it.
func (fs *fstate) exp2anyreg(e *expdesc) int {
	fs.dischargeVars(e)
	if e.k == eNonReloc {
		if !e.hasJumps() {
			return e.info
		}
		if e.info >= fs.nactive { // a temporary: reuse it
			fs.exp2reg(e, e.info)
			return e.info
		}
	}
	fs.exp2nextreg(e)
	return e.info
}

// kIndex returns the constant index of e if e is a constant that fits a K operand, else -1.
func (fs *fstate) kIndex(e *expdesc) int {
	if e.hasJumps() {
		return -1
	}
	var v Value
	switch e.k {
	case eK:
		v = e.val
	case eNil:
		v = Value{}
	case eTrue:
		v = Bool(true)
	case eFalse:
		v = Bool(false)
	default:
		return -1
	}
	if k := fs.addK(v); k <= math.MaxUint8 {
		return k
	}
	return -1
}

func isNumeral(e *expdesc) bool {
	return e.k == eK && e.val.isNumber() && !e.hasJumps()
}

// storeVar assigns ex to the variable v.
func (fs *fstate) storeVar(v, ex *expdesc) {
	switch v.k {
	case eLocal:
		fs.freeExp(ex)
		fs.exp2reg(ex, v.info)
		return
	case eCell:
		r := fs.exp2anyreg(ex)
		fs.abc(opSetCell, v.info, r, 0)
	case eUpCell:
		r := fs.exp2anyreg(ex)
		fs.abc(opSetUpCell, r, v.info, 0)
	case eGlobal:
		r := fs.exp2anyreg(ex)
		k := fs.strK(v.name)
		if k <= math.MaxUint16 {
			fs.abx(opSetGlobal, r, k)
			fs.emit(fs.site())
		} else {
			t := fs.freereg
			fs.reserve(2)
			fs.abc(opGetEnv, t, 0, 0)
			fs.loadK(t+1, String(v.name))
			fs.abc(opSetTable, t, t+1, r)
			fs.freeReg(t + 1)
			fs.freeReg(t)
		}
	case eIndexed:
		if kc := fs.kIndex(ex); kc >= 0 { // a constant value, as in t[k] = true
			switch v.kk {
			case keyReg:
				fs.abc(opSetTableK, v.tbl, v.key, kc)
			case keyStr:
				fs.abc(opSetFieldK, v.tbl, v.key, kc)
				fs.emit(fs.site())
			case keyInt:
				fs.abc(opSetIndexK, v.tbl, v.key, kc)
			}
			break
		}
		r := fs.exp2anyreg(ex)
		switch v.kk {
		case keyReg:
			fs.abc(opSetTable, v.tbl, v.key, r)
		case keyStr:
			fs.abc(opSetField, v.tbl, v.key, r)
			fs.emit(fs.site())
		case keyInt:
			fs.abc(opSetIndex, v.tbl, v.key, r)
		}
	default:
		panic("glua: compiler: cannot assign to this expression")
	}
	fs.freeExp(ex)
}

// indexed turns t (already in a register) and key into t[key].
func (fs *fstate) indexed(t, key *expdesc) {
	tr := fs.exp2anyreg(t)
	e := expdesc{k: eIndexed, tbl: tr}
	switch {
	case key.k == eK && key.val.isString() && !key.hasJumps():
		if k := fs.strK(key.val.str()); k <= math.MaxUint8 {
			e.kk, e.key = keyStr, k
			*t = e
			return
		}
	case key.k == eK && key.val.p == tInt() && int64(key.val.n) >= 0 && int64(key.val.n) <= 255 && !key.hasJumps():
		e.kk, e.key = keyInt, int(key.val.n)
		*t = e
		return
	}
	e.kk, e.key = keyReg, fs.exp2anyreg(key)
	*t = e
}

func (fs *fstate) negateCondition(e *expdesc) {
	pc := e.info
	fs.setC(pc, decC(fs.p.code[pc])^1)
}

// jumpOnCond emits a jump taken when e's truthiness equals cond, and returns its site.
func (fs *fstate) jumpOnCond(e *expdesc, cond int) int {
	if e.k == eReloc {
		if i := fs.p.code[e.info]; uint8(i) == opNot && e.info == fs.pc()-1 && fs.target != fs.pc() {
			// "not x": drop the NOT and test x the other way round
			fs.p.code = fs.p.code[:e.info]
			fs.p.lines = fs.p.lines[:e.info]
			return fs.condJump(opTestJmp, decB(i), 0, cond)
		}
	}
	fs.discharge2anyreg(e)
	fs.freeExp(e)
	// TESTSET falls through when truthy(R[B]) == C, so C is the opposite of cond
	return fs.condJump(opTestSet, noReg, e.info, 1-cond)
}

// goIfTrue continues when e is true and jumps out, through e.f, when it is false.
func (fs *fstate) goIfTrue(e *expdesc) {
	fs.dischargeVars(e)
	pj := noJump
	switch e.k {
	case eJmp:
		fs.negateCondition(e)
		pj = e.info + 1
	case eK, eTrue:
	default:
		pj = fs.jumpOnCond(e, 0)
	}
	if pj != noJump {
		e.f = append(e.f, pj)
	}
	fs.patchToHere(e.t)
	e.t = nil
}

// goIfFalse continues when e is false and jumps out, through e.t, when it is true.
func (fs *fstate) goIfFalse(e *expdesc) {
	fs.dischargeVars(e)
	pj := noJump
	switch e.k {
	case eJmp:
		pj = e.info + 1
	case eNil, eFalse:
	default:
		pj = fs.jumpOnCond(e, 1)
	}
	if pj != noJump {
		e.t = append(e.t, pj)
	}
	fs.patchToHere(e.f)
	e.f = nil
}

// removeValues turns the TESTSETs of a list into TESTJMPs, for 'not', whose value is a fresh boolean.
func (fs *fstate) removeValues(list []int) {
	for _, site := range list {
		fs.patchTestReg(site, noReg)
	}
}

func (fs *fstate) codeNot(e *expdesc) {
	switch e.k {
	case eNil, eFalse:
		e.k = eTrue
	case eK, eTrue:
		e.k = eFalse
	case eJmp:
		fs.negateCondition(e)
	default:
		fs.dischargeVars(e)
		if e.k == eJmp {
			fs.negateCondition(e)
			break
		}
		fs.discharge2anyreg(e)
		fs.freeExp(e)
		e.info, e.k = fs.abc(opNot, 0, e.info, 0), eReloc
	}
	e.t, e.f = e.f, e.t
	fs.removeValues(e.f)
	fs.removeValues(e.t)
}

var arithOps = map[syntax.Kind]uint8{
	syntax.Plus: opAdd, syntax.Minus: opSub, syntax.Star: opMul, syntax.Slash: opDiv,
	syntax.Percent: opMod, syntax.Caret: opPow, syntax.DSlash: opIDiv, syntax.Amp: opBAnd,
	syntax.Pipe: opBOr, syntax.Tilde: opBXor, syntax.Shl: opShl, syntax.Shr: opShr,
}

// infix prepares the left operand of a binary operator before the right one is compiled.
func (fs *fstate) infix(op syntax.Kind, v *expdesc) {
	switch op {
	case syntax.And:
		fs.goIfTrue(v)
	case syntax.Or:
		fs.goIfFalse(v)
	case syntax.Concat:
		fs.exp2nextreg(v) // operands go in consecutive registers
	case syntax.Eq, syntax.Ne:
		if fs.kIndex(v) < 0 {
			fs.exp2anyreg(v)
		}
	default:
		if !isNumeral(v) {
			fs.exp2anyreg(v)
		}
	}
}

// posfix finishes a binary operation; the result replaces e1.
func (fs *fstate) posfix(op syntax.Kind, e1, e2 *expdesc, line int) {
	fs.line = line
	switch op {
	case syntax.And:
		fs.dischargeVars(e2)
		e2.f = append(e2.f, e1.f...)
		*e1 = *e2
	case syntax.Or:
		fs.dischargeVars(e2)
		e2.t = append(e2.t, e1.t...)
		*e1 = *e2
	case syntax.Concat:
		fs.exp2nextreg(e2)
		last := fs.pc() - 1
		if i := fs.p.code[last]; uint8(i) == opConcat && fs.target != fs.pc() && decA(i) == e1.info+1 {
			fs.freeExp(e2)
			fs.setA(last, e1.info)
			fs.setB(last, decB(i)+1)
		} else {
			fs.abc(opConcat, e1.info, 2, 0)
			fs.freeExp(e2)
		}
	case syntax.Eq, syntax.Ne:
		fs.codeEq(op, e1, e2)
	case syntax.Lt, syntax.Le, syntax.Gt, syntax.Ge:
		fs.codeOrder(op, e1, e2)
	default:
		if fs.foldBinary(op, e1, e2) {
			return
		}
		fs.codeArith(arithOps[op], e1, e2)
	}
}

func (fs *fstate) codeArith(op uint8, e1, e2 *expdesc) {
	if isNumeral(e2) {
		if k := fs.addK(e2.val); k <= math.MaxUint8 {
			r1 := fs.exp2anyreg(e1)
			fs.freeExp(e1)
			e1.info, e1.k = fs.abc(op+(opAddK-opAdd), 0, r1, k), eReloc
			return
		}
	}
	r2 := fs.exp2anyreg(e2)
	r1 := fs.exp2anyreg(e1)
	fs.freeExps(e1, e2)
	e1.info, e1.k = fs.abc(op, 0, r1, r2), eReloc
}

func (fs *fstate) codeEq(op syntax.Kind, e1, e2 *expdesc) {
	pol := 0 // the jump of an eJmp is taken when the test is true: fall through when it is false
	if op == syntax.Ne {
		pol = 1
	}
	if e1.k != eNonReloc { // e1 was a constant; e2 is a register
		*e1, *e2 = *e2, *e1
	}
	r1 := fs.exp2anyreg(e1)
	if k := fs.kIndex(e2); k >= 0 {
		fs.freeExp(e1)
		e1.info = fs.condJump(opEqKJmp, r1, k, pol) - 1
	} else {
		r2 := fs.exp2anyreg(e2)
		fs.freeExps(e1, e2)
		e1.info = fs.condJump(opEqJmp, r1, r2, pol) - 1
	}
	e1.k = eJmp
}

func (fs *fstate) codeOrder(op syntax.Kind, e1, e2 *expdesc) {
	// a > b is b < a, and a >= b is b <= a
	if op == syntax.Gt || op == syntax.Ge {
		*e1, *e2 = *e2, *e1
		if op == syntax.Gt {
			op = syntax.Lt
		} else {
			op = syntax.Le
		}
	}
	var pc int
	switch {
	case isNumeral(e2) && fs.addK(e2.val) <= math.MaxUint8:
		r1 := fs.exp2anyreg(e1)
		fs.freeExp(e1)
		kop := uint8(opLtKJmp)
		if op == syntax.Le {
			kop = opLeKJmp
		}
		pc = fs.condJump(kop, r1, fs.addK(e2.val), 0) - 1
	case isNumeral(e1) && fs.addK(e1.val) <= math.MaxUint8:
		// k < b is b > k, and k <= b is b >= k
		r2 := fs.exp2anyreg(e2)
		fs.freeExp(e2)
		kop := uint8(opGtKJmp)
		if op == syntax.Le {
			kop = opGeKJmp
		}
		pc = fs.condJump(kop, r2, fs.addK(e1.val), 0) - 1
	default:
		r2 := fs.exp2anyreg(e2)
		r1 := fs.exp2anyreg(e1)
		fs.freeExps(e1, e2)
		rop := uint8(opLtJmp)
		if op == syntax.Le {
			rop = opLeJmp
		}
		pc = fs.condJump(rop, r1, r2, 0) - 1
	}
	e1.info, e1.k = pc, eJmp
}

// foldBinary folds arithmetic on two numerals. It never folds what would raise or give a
// result that could differ at run time: integer division or modulo by zero, NaN, or -0.0.
func (fs *fstate) foldBinary(op syntax.Kind, e1, e2 *expdesc) bool {
	if !isNumeral(e1) || !isNumeral(e2) {
		return false
	}
	r, ok := foldArith(arithOps[op], e1.val, e2.val)
	if !ok {
		return false
	}
	e1.k, e1.val = eK, r
	return true
}

// prefix compiles a unary operator applied to e.
func (fs *fstate) prefix(op syntax.Kind, e *expdesc, line int) {
	fs.line = line
	switch op {
	case syntax.Not:
		fs.codeNot(e)
		return
	case syntax.Minus:
		if isNumeral(e) {
			if r, ok := foldArith(opSub, Int(0), e.val); ok && e.val.p == tInt() {
				e.val = r
				return
			}
			if e.val.p == tFloat() {
				f := -math.Float64frombits(e.val.n)
				if f != 0 { // never fold to -0.0
					e.val = Float(f)
					return
				}
			}
		}
	case syntax.Tilde:
		if isNumeral(e) {
			if i, ok := e.val.Int(); ok { // a float with an exact integer value folds too, as in C Lua
				e.val = Int(^i)
				return
			}
		}
	}
	r := fs.exp2anyreg(e)
	fs.freeExp(e)
	var o uint8
	switch op {
	case syntax.Minus:
		o = opUnm
	case syntax.Tilde:
		o = opBNot
	case syntax.Hash:
		o = opLen
	}
	e.info, e.k = fs.abc(o, 0, r, 0), eReloc
}

// expression compilation

func (fs *fstate) expr(n syntax.Expr) expdesc {
	switch n := n.(type) {
	case *syntax.NilExpr:
		return expdesc{k: eNil}
	case *syntax.TrueExpr:
		return expdesc{k: eTrue}
	case *syntax.FalseExpr:
		return expdesc{k: eFalse}
	case *syntax.IntExpr:
		return expdesc{k: eK, val: Int(n.Value)}
	case *syntax.FloatExpr:
		return expdesc{k: eK, val: Float(n.Value)}
	case *syntax.StringExpr:
		return expdesc{k: eK, val: String(n.Value)}
	case *syntax.VarargExpr:
		fs.line = n.Line
		return expdesc{k: eVararg, info: fs.abc(opVararg, 0, 0, 1)}
	case *syntax.NameExpr:
		return fs.name(n)
	case *syntax.IndexExpr:
		t := fs.expr(n.Obj)
		fs.exp2anyreg(&t) // before the key, so that the key's temporaries sit above it
		fs.line = n.Line
		k := fs.expr(n.Key)
		fs.indexed(&t, &k)
		return t
	case *syntax.CallExpr:
		return fs.call(n)
	case *syntax.MethodCallExpr:
		return fs.methodCall(n)
	case *syntax.FunctionExpr:
		p := fs.c.function(n, fs)
		fs.p.protos = append(fs.p.protos, p)
		if len(fs.p.protos) > math.MaxUint16+1 {
			fs.c.errorf(n.Line, "too many functions")
		}
		fs.line = n.Line
		return expdesc{k: eReloc, info: fs.abx(opClosure, 0, len(fs.p.protos)-1)}
	case *syntax.BinaryExpr:
		e1 := fs.expr(n.L)
		fs.line = n.Line
		fs.infix(n.Op, &e1)
		e2 := fs.expr(n.R)
		fs.posfix(n.Op, &e1, &e2, n.Line)
		return e1
	case *syntax.UnaryExpr:
		e := fs.expr(n.X)
		fs.prefix(n.Op, &e, n.Line)
		return e
	case *syntax.TableExpr:
		return fs.table(n)
	case *syntax.ParenExpr:
		e := fs.expr(n.X)
		fs.dischargeVars(&e) // one value; and not assignable
		return e
	}
	panic(fmt.Sprintf("glua: compiler: unknown expression %T", n))
}

// name compiles a reference to a variable.
func (fs *fstate) name(n *syntax.NameExpr) expdesc {
	fs.line = n.Line
	ref := fs.c.info.Names[n]
	return fs.ref(ref, n.Name)
}

func (fs *fstate) ref(ref syntax.Ref, name string) expdesc {
	if ref.Field != "" { // a field of an expression's environment parameter
		field := ref.Field
		ref.Field = ""
		obj := fs.ref(ref, "")
		key := expdesc{k: eK, val: String(field)}
		fs.indexed(&obj, &key)
		return obj
	}
	switch ref.Kind {
	case syntax.RefLocal:
		if v, ok := fs.consts[ref.Var]; ok {
			return constExp(v)
		}
		if ref.Var.Cell() {
			return expdesc{k: eCell, info: fs.regOf[ref.Var]}
		}
		return expdesc{k: eLocal, info: fs.regOf[ref.Var]}
	case syntax.RefUpval:
		if v, ok := fs.constOf(ref.Var); ok {
			return constExp(v)
		}
		if ref.Var.Cell() {
			return expdesc{k: eUpCell, info: ref.Upval.Index}
		}
		return expdesc{k: eUpval, info: ref.Upval.Index}
	}
	if ref.Env == nil {
		if name == "_ENV" {
			return expdesc{k: eReloc, info: fs.abc(opGetEnv, 0, 0, 0)}
		}
		return expdesc{k: eGlobal, name: name}
	}
	env := fs.ref(*ref.Env, "_ENV")
	key := expdesc{k: eK, val: String(name)}
	fs.indexed(&env, &key)
	return env
}

// constExp is the expression of a compile-time constant's value, as C Lua's const2exp: nil
// and the booleans have kinds of their own, which conditions rely on.
func constExp(v Value) expdesc {
	switch {
	case v.IsNil():
		return expdesc{k: eNil}
	case v.p == tBool():
		if v.n != 0 {
			return expdesc{k: eTrue}
		}
		return expdesc{k: eFalse}
	}
	return expdesc{k: eK, val: v}
}

// constOf finds a compile-time constant local of an enclosing function.
func (fs *fstate) constOf(v *syntax.Var) (Value, bool) {
	for f := fs; f != nil; f = f.parent {
		if c, ok := f.consts[v]; ok {
			return c, true
		}
	}
	return Value{}, false
}

// exprList compiles a list into consecutive registers, leaving the last one undischarged
// so the caller can let a multi-value last expression produce several values. It returns
// the last expression and the number of expressions.
func (fs *fstate) exprList(list []syntax.Expr) (expdesc, int) {
	var e expdesc
	for i, x := range list {
		if i > 0 {
			fs.exp2nextreg(&e)
		}
		e = fs.expr(x)
	}
	return e, len(list)
}

// adjustAssign makes an expression list of nexps produce exactly nvars values.
func (fs *fstate) adjustAssign(nvars, nexps int, e *expdesc) {
	needed := nvars - nexps
	if e.k == eCall || e.k == eVararg {
		extra := max(needed+1, 0)
		fs.setReturns(e, extra)
	} else {
		if e.k != eVoid {
			fs.exp2nextreg(e)
		}
		if needed > 0 {
			fs.abc(opLoadNil, fs.freereg, needed-1, 0) // reserved below
		}
	}
	if needed > 0 {
		fs.reserve(needed)
	} else {
		fs.freereg += needed // drop extra values
	}
}

func (fs *fstate) call(n *syntax.CallExpr) expdesc {
	f := fs.expr(n.Fn)
	fs.line = n.Line
	fs.exp2nextreg(&f)
	return fs.finishCall(f.info, n.Args, n.Line, fs.builtin(n.Fn))
}

// builtin returns the FASTCALL id for a call of fn, a free name such as type or a field of
// one such as math.floor, when that names a built-in; or 0. FASTCALL checks at run time
// that the function really is the built-in, so a script that defines its own math still
// gets its own.
func (fs *fstate) builtin(fn syntax.Expr) uint8 {
	global := func(e syntax.Expr) (string, bool) {
		n, ok := e.(*syntax.NameExpr)
		if !ok {
			return "", false
		}
		ref := fs.c.info.Names[n]
		return n.Name, ref.Kind == syntax.RefGlobal && ref.Env == nil && ref.Field == ""
	}
	switch e := fn.(type) {
	case *syntax.NameExpr:
		if name, ok := global(e); ok {
			return fastIDs[name]
		}
		if ref := fs.c.info.Names[e]; ref.Var != nil && ref.Field == "" && (ref.Kind == syntax.RefLocal || ref.Kind == syntax.RefUpval) {
			return fs.c.aliases[ref.Var]
		}
	case *syntax.IndexExpr:
		k, isStr := e.Key.(*syntax.StringExpr)
		if name, ok := global(e.Obj); ok && isStr {
			return fastIDs[name+"."+k.Value]
		}
	}
	return 0
}

func (fs *fstate) methodCall(n *syntax.MethodCallExpr) expdesc {
	obj := fs.expr(n.Obj)
	fs.line = n.Line
	r := fs.exp2anyreg(&obj)
	fs.freeExp(&obj)
	base := fs.freereg
	fs.reserve(2)
	if k := fs.strK(n.Name); k <= math.MaxUint8 {
		fs.abc(opSelf, base, r, k)
		fs.emit(fs.site())
	} else {
		fs.abc(opMove, base+1, r, 0)
		fs.loadK(base, String(n.Name))
		fs.abc(opGetTable, base, base+1, base)
	}
	fs.freereg = base + 1 // the function; self is the first argument
	return fs.finishCall(base, append([]syntax.Expr{nil}, n.Args...), n.Line, methodIDs[n.Name])
}

// finishCall compiles the arguments of a call whose function is in register base. A nil
// first argument stands for self, which is already in place.
func (fs *fstate) finishCall(base int, args []syntax.Expr, line int, fast uint8) expdesc {
	nargs := 0
	open := false
	var last expdesc
	for i, a := range args {
		if a == nil {
			fs.reserve(1) // self
			nargs++
			continue
		}
		if i > 0 && last.k != eVoid {
			fs.exp2nextreg(&last)
		}
		if _, isVararg := a.(*syntax.VarargExpr); isVararg && fast == fastSelect && i == 1 && len(args) == 2 {
			fs.abc(opFastSelect, base, 0, 0) // select(x, ...): before the VARARG, which it may skip
		}
		last = fs.expr(a)
		nargs++
	}
	if last.k == eCall || last.k == eVararg {
		fs.setReturns(&last, -1)
		open = true
	} else if last.k != eVoid {
		fs.exp2nextreg(&last)
	}
	b := nargs + 1
	if open {
		b = 0
	}
	fs.line = line
	if fast != 0 && !open {
		fs.abc(opFastCall, base, b, 0)
		fs.emit(uint32(fast))
	}
	pc := fs.abc(opCall, base, b, 2)
	if fast != 0 && !open {
		if fs.fastCalls == nil {
			fs.fastCalls = map[int]bool{}
		}
		fs.fastCalls[pc] = true
	}
	fs.freereg = base + 1 // the call leaves one result in base, until told otherwise
	return expdesc{k: eCall, info: pc}
}

func (fs *fstate) table(n *syntax.TableExpr) expdesc {
	fs.line = n.Line
	pc := fs.abc(opNewTable, 0, 0, 0)
	fs.emit(0)
	t := expdesc{k: eNonReloc, info: fs.freereg}
	fs.reserve(1)
	fs.setA(pc, t.info)
	narr, nhash, pending := 0, 0, 0
	var last expdesc
	flush := func() {
		fs.abc(opSetList, t.info, pending, 0)
		fs.emit(uint32(narr - pending))
		fs.freereg = t.info + 1
		pending = 0
	}
	for i, f := range n.Fields {
		if last.k != eVoid {
			fs.exp2nextreg(&last)
			last = expdesc{}
			if pending == listFlush {
				flush()
			}
		}
		if f.Key == nil {
			last = fs.expr(f.Value)
			narr++
			pending++
			if i == len(n.Fields)-1 && (last.k == eCall || last.k == eVararg) {
				fs.setReturns(&last, -1)
				fs.abc(opSetList, t.info, 0, 0)
				fs.emit(uint32(narr - pending))
				fs.freereg = t.info + 1
				narr-- // the open list's length is unknown
				pending, last = 0, expdesc{}
			}
			continue
		}
		nhash++
		tab := expdesc{k: eNonReloc, info: t.info}
		k := fs.expr(f.Key)
		fs.indexed(&tab, &k)
		v := fs.expr(f.Value)
		fs.storeVar(&tab, &v)
		if tab.kk == keyReg {
			fs.freeRegOptIfTemp(tab.key)
		}
	}
	if last.k != eVoid {
		fs.exp2nextreg(&last)
	}
	if pending > 0 {
		flush()
	}
	// sizes: aux holds the array size, B the hash size as log2+1
	fs.p.code[pc+1] = uint32(narr)
	if nhash > 0 {
		b := 1
		for 1<<(b-1) < nhash {
			b++
		}
		fs.setB(pc, b)
	}
	return t
}

// statements

func (fs *fstate) enterBlock(loop bool) *cblock {
	b := &cblock{parent: fs.bl, nactive: fs.nactive, ntbc: len(fs.tbc), nlocs: len(fs.open), loop: loop, labels: map[string]labelPos{}}
	fs.bl = b
	return b
}

// leaveBlock closes the block's to-be-closed variables, drops its locals, and hands its
// unresolved gotos to the enclosing block.
func (fs *fstate) leaveBlock() {
	b := fs.bl
	hasTBC := len(fs.tbc) > b.ntbc
	if b.loop {
		fs.patchToHere(b.breaks) // before the CLOSE, so that a break closes too
	}
	if hasTBC {
		fs.abc(opClose, b.nactive, 0, 0)
		fs.tbc = fs.tbc[:b.ntbc]
	}
	for _, i := range fs.open[b.nlocs:] {
		fs.p.locvars[i].endpc = fs.pc()
	}
	fs.open = fs.open[:b.nlocs]
	fs.nactive = b.nactive
	fs.freereg = b.nactive
	fs.bl = b.parent
	if fs.bl != nil {
		for _, g := range b.gotos {
			g.close = g.close || hasTBC
			fs.bl.gotos = append(fs.bl.gotos, g)
		}
	}
}

func (fs *fstate) stmts(list []syntax.Stmt) {
	for _, s := range list {
		fs.stmt(s)
		fs.freereg = fs.nactive
	}
}

func (fs *fstate) block(b *syntax.Block, loop bool) {
	fs.enterBlock(loop)
	fs.stmts(b.Stmts)
	fs.line = b.EndLine
	fs.leaveBlock()
}

func (fs *fstate) stmt(s syntax.Stmt) {
	fs.line = s.Pos()
	switch s := s.(type) {
	case *syntax.AssignStmt:
		fs.assign(s)
	case *syntax.CallStmt:
		e := fs.expr(s.Call)
		fs.setC(e.info, 1) // no results
	case *syntax.DoStmt:
		fs.block(s.Body, false)
	case *syntax.WhileStmt:
		start := fs.label()
		cond := fs.expr(s.Cond)
		fs.goIfTrue(&cond)
		fs.enterBlock(true) // breaks land after the back-edge
		fs.block(s.Body, false)
		fs.jumpBack(start)
		fs.patchToHere(cond.f)
		fs.leaveBlock()
	case *syntax.RepeatStmt:
		fs.repeat(s)
	case *syntax.IfStmt:
		var escape []int
		for i, c := range s.Conds {
			fs.line = c.Pos()
			cond := fs.expr(c)
			fs.goIfTrue(&cond)
			fs.block(s.Blocks[i], false)
			if i < len(s.Conds)-1 || s.Else != nil {
				escape = append(escape, fs.jump())
			}
			fs.patchToHere(cond.f)
		}
		if s.Else != nil {
			fs.block(s.Else, false)
		}
		fs.patchToHere(escape)
	case *syntax.NumericForStmt:
		fs.numericFor(s)
	case *syntax.GenericForStmt:
		fs.genericFor(s)
	case *syntax.FunctionStmt:
		v := fs.expr(s.Target)
		fn := fs.expr(s.Func)
		fs.line = s.Line
		fs.storeVar(&v, &fn)
	case *syntax.LocalFunctionStmt:
		v := fs.c.info.Decls[s][0]
		r := fs.freereg
		fs.reserve(1)
		fs.activate(v, r)
		if v.Cell() {
			fs.abc(opLoadNil, r, 0, 0)
			fs.abc(opNewCell, r, 0, 0)
			fn := fs.expr(s.Func)
			fr := fs.exp2anyreg(&fn)
			fs.abc(opSetCell, r, fr, 0)
			fs.freeExp(&fn)
		} else {
			fn := fs.expr(s.Func) // CLOSURE stores before capturing, so f can capture itself
			fs.exp2reg(&fn, r)
		}
	case *syntax.LocalStmt:
		fs.local(s)
	case *syntax.ReturnStmt:
		fs.ret(s)
	case *syntax.BreakStmt:
		fs.breakStmt()
	case *syntax.GotoStmt:
		fs.gotoStmt(s.Label)
	case *syntax.LabelStmt:
		fs.labelStmt(s.Name)
	}
}

func (fs *fstate) assign(s *syntax.AssignStmt) {
	targets := make([]expdesc, len(s.Targets))
	for i, t := range s.Targets {
		targets[i] = fs.expr(t)
		if targets[i].k == eLocal {
			fs.checkConflict(targets[:i], &targets[i])
		}
		if targets[i].k == eUpval {
			panic("glua: compiler: assignment to a captured value")
		}
	}
	fs.line = s.Line
	if len(targets) == 1 && len(s.Values) == 1 {
		v := fs.expr(s.Values[0])
		fs.setOneRet(&v)
		fs.storeVar(&targets[0], &v)
		return
	}
	e, n := fs.exprList(s.Values)
	if n != len(targets) {
		fs.adjustAssign(len(targets), n, &e)
	} else {
		fs.setOneRet(&e)
		fs.exp2nextreg(&e)
	}
	// the values are in consecutive registers; assign from the last to the first
	for i := len(targets) - 1; i >= 0; i-- {
		v := expdesc{k: eNonReloc, info: fs.freereg - 1}
		fs.storeVar(&targets[i], &v)
	}
}

// checkConflict handles "t, t.x = ..." style conflicts: if an earlier target indexes
// through the local that v assigns, it must use a copy made before the assignment.
func (fs *fstate) checkConflict(earlier []expdesc, v *expdesc) {
	conflict := false
	for i := range earlier {
		e := &earlier[i]
		if e.k != eIndexed {
			continue
		}
		if e.tbl == v.info {
			conflict, e.tbl = true, fs.freereg
		}
		if e.kk == keyReg && e.key == v.info {
			conflict, e.key = true, fs.freereg
		}
	}
	if conflict {
		fs.abc(opMove, fs.freereg, v.info, 0)
		fs.reserve(1)
	}
}

func (fs *fstate) local(s *syntax.LocalStmt) {
	vars := fs.c.info.Decls[s]
	nvars := len(vars)
	// a compile-time constant: "local x <const> = 42" needs no register
	if nvars == len(s.Values) && vars[nvars-1].Attrib == "const" {
		last := fs.exprPreview(s.Values[nvars-1])
		if last.ok {
			if nvars > 1 {
				e, n := fs.exprList(s.Values[:nvars-1])
				fs.adjustAssign(nvars-1, n, &e)
			}
			base := fs.freereg - (nvars - 1)
			for i, v := range vars[:nvars-1] {
				fs.activate(v, base+i)
			}
			fs.consts[vars[nvars-1]] = last.v
			fs.afterLocal(vars[:nvars-1])
			return
		}
	}
	base := fs.freereg
	for i, v := range vars {
		if i < len(s.Values) && !v.Assigned && v.Attrib != "close" {
			if id := fs.builtin(s.Values[i]); id != 0 {
				if fs.c.aliases == nil {
					fs.c.aliases = map[*syntax.Var]uint8{}
				}
				fs.c.aliases[v] = id
			}
		}
	}
	if len(s.Values) == 0 {
		fs.reserve(nvars)
		fs.abc(opLoadNil, base, nvars-1, 0)
	} else {
		e, n := fs.exprList(s.Values)
		fs.adjustAssign(nvars, n, &e)
	}
	for i, v := range vars {
		fs.activate(v, base+i)
	}
	fs.afterLocal(vars)
}

// afterLocal wraps new cell locals and registers a to-be-closed one.
func (fs *fstate) afterLocal(vars []*syntax.Var) {
	for _, v := range vars {
		if v.Cell() {
			fs.abc(opNewCell, fs.regOf[v], 0, 0)
		}
		if v.Attrib == "close" {
			fs.abc(opTBC, fs.regOf[v], 0, 0)
			fs.tbc = append(fs.tbc, fs.regOf[v])
		}
	}
}

type preview struct {
	v  Value
	ok bool
}

// exprPreview reports whether n is a compile-time constant (nil, a boolean, a number or a
// string, possibly folded), without emitting code.
func (fs *fstate) exprPreview(n syntax.Expr) preview {
	switch n := n.(type) {
	case *syntax.NilExpr:
		return preview{Value{}, true}
	case *syntax.TrueExpr:
		return preview{Bool(true), true}
	case *syntax.FalseExpr:
		return preview{Bool(false), true}
	case *syntax.IntExpr:
		return preview{Int(n.Value), true}
	case *syntax.FloatExpr:
		return preview{Float(n.Value), true}
	case *syntax.StringExpr:
		return preview{String(n.Value), true}
	case *syntax.NameExpr:
		ref := fs.c.info.Names[n]
		if ref.Var != nil {
			if v, ok := fs.constOf(ref.Var); ok {
				return preview{v, true}
			}
		}
	case *syntax.UnaryExpr:
		x := fs.exprPreview(n.X)
		if x.ok && x.v.isNumber() {
			switch n.Op {
			case syntax.Minus:
				if r, ok := foldArith(opSub, Int(0), x.v); ok && x.v.p == tInt() {
					return preview{r, true}
				}
				if x.v.p == tFloat() && math.Float64frombits(x.v.n) != 0 {
					return preview{Float(-math.Float64frombits(x.v.n)), true}
				}
			case syntax.Tilde:
				if x.v.p == tInt() {
					return preview{Int(^int64(x.v.n)), true}
				}
			}
		}
	case *syntax.BinaryExpr:
		if op, ok := arithOps[n.Op]; ok {
			l, r := fs.exprPreview(n.L), fs.exprPreview(n.R)
			if l.ok && r.ok && l.v.isNumber() && r.v.isNumber() {
				if v, ok := foldArith(op, l.v, r.v); ok {
					return preview{v, true}
				}
			}
		}
	}
	return preview{}
}

func (fs *fstate) ret(s *syntax.ReturnStmt) {
	closing := len(fs.tbc) > 0
	switch {
	case len(s.Values) == 0:
		if closing {
			fs.abc(opClose, 0, 0, 0)
			fs.abc(opReturn, 0, 1, 0)
		} else {
			fs.abc(opReturn0, 0, 0, 0)
		}
		return
	case len(s.Values) == 1:
		e := fs.expr(s.Values[0])
		if e.k == eCall && !closing {
			i := fs.p.code[e.info]
			fs.p.code[e.info] = iABC(opTailCall, uint8(decA(i)), uint8(decB(i)), 0)
			if fs.fastCalls[e.info] {
				// FASTCALL stands only before a CALL: make it a jump to the next instruction
				fs.p.code[e.info-2], fs.p.code[e.info-1] = iABC(opJmpX, 0, 0, 0), 0
			}
			fs.abc(opReturn, decA(i), 0, 0) // for a Go function, which returns here
			return
		}
		if e.k == eCall || e.k == eVararg {
			fs.setReturns(&e, -1)
			base := decA(fs.p.code[e.info])
			if closing {
				fs.abc(opClose, 0, 0, 0)
			}
			fs.abc(opReturn, base, 0, 0)
			return
		}
		r := fs.exp2anyreg(&e)
		if closing {
			fs.abc(opClose, 0, 0, 0)
			fs.abc(opReturn, r, 2, 0)
		} else {
			fs.abc(opReturn1, r, 0, 0)
		}
		return
	}
	base := fs.freereg
	e, n := fs.exprList(s.Values)
	b := n + 1
	if e.k == eCall || e.k == eVararg {
		fs.setReturns(&e, -1)
		b = 0
	} else {
		fs.exp2nextreg(&e)
	}
	if closing {
		fs.abc(opClose, 0, 0, 0)
	}
	fs.abc(opReturn, base, b, 0)
}

func (fs *fstate) repeat(s *syntax.RepeatStmt) {
	start := fs.label()
	loop := fs.enterBlock(true)
	inner := fs.enterBlock(false)
	fs.stmts(s.Body.Stmts)
	fs.line = s.Body.EndLine
	cond := fs.expr(s.Cond)
	// exit forward when the condition holds; loop back through a JMP, which ticks
	fs.goIfFalse(&cond)
	if len(fs.tbc) > inner.ntbc {
		fs.abc(opClose, inner.nactive, 0, 0) // the next iteration's locals are new
	}
	fs.jumpBack(start)
	fs.patchToHere(cond.t)
	fs.leaveBlock() // inner: closes the body's to-be-closed variables on exit
	_ = loop
	fs.leaveBlock() // loop: patches breaks
}

func (fs *fstate) numericFor(s *syntax.NumericForStmt) {
	base := fs.freereg
	fs.enterBlock(true)
	e := fs.expr(s.Start)
	fs.exp2nextreg(&e)
	e = fs.expr(s.Limit)
	fs.exp2nextreg(&e)
	if s.Step != nil {
		e = fs.expr(s.Step)
		fs.exp2nextreg(&e)
	} else {
		fs.reserve(1)
		fs.abx(opLoadI, base+2, 1)
	}
	fs.reserve(1) // the visible control variable
	fs.nactive = base + 3
	fs.line = s.Line
	prep := fs.abx(opForPrep, base, 0)
	body := fs.label()
	fs.enterBlock(false)
	v := fs.c.info.Decls[s][0]
	fs.activate(v, base+3)
	fs.afterLocal([]*syntax.Var{v})
	fs.stmts(s.Body.Stmts)
	fs.line = s.Body.EndLine
	fs.leaveBlock()
	fs.line = s.Line
	loop := fs.pc()
	fs.forJump(prep, loop+1-(prep+1))
	fs.forJump(fs.abx(opForLoop, base, 0), loop+1-body)
	fs.leaveBlock()
}

// forJump sets the unsigned 16-bit jump of a loop instruction.
func (fs *fstate) forJump(pc, off int) {
	if off > math.MaxUint16 {
		fs.c.errorf(fs.line, "control structure too long")
	}
	fs.setBx(pc, off)
}

func (fs *fstate) genericFor(s *syntax.GenericForStmt) {
	base := fs.freereg
	fs.enterBlock(true)
	e, n := fs.exprList(s.Exprs)
	fs.adjustAssign(4, n, &e) // iterator, state, control, closing value
	fs.nactive = base + 4
	fs.line = s.Line
	prep := fs.abx(opTForPrep, base, 0)
	// the closing value may be to be closed; returns and gotos in the body must close it
	fs.tbc = append(fs.tbc, base+3)
	body := fs.label()
	fs.enterBlock(false)
	vars := fs.c.info.Decls[s]
	fs.reserve(len(vars))
	if int(fs.p.maxstack) < base+7 {
		fs.p.maxstack = uint8(base + 7) // TFORCALL copies the iterator, state and control above R[A+3]
	}
	for i, v := range vars {
		fs.activate(v, base+4+i)
	}
	fs.afterLocal(vars)
	fs.stmts(s.Body.Stmts)
	fs.line = s.Body.EndLine
	fs.leaveBlock()
	fs.line = s.ExprLine
	call := fs.label()
	fs.forJump(prep, call-(prep+1))
	fs.abc(opTForCall, base, 0, len(vars)+1)
	loop := fs.abx(opTForLoop, base, 0)
	fs.forJump(loop, loop+1-body)
	fs.leaveBlock() // closes the closing value, after the breaks land
}

// closeTo emits a CLOSE if to-be-closed variables at or above level are active.
func (fs *fstate) closeTo(level int) {
	for _, r := range fs.tbc {
		if r >= level {
			fs.abc(opClose, level, 0, 0)
			return
		}
	}
}

func (fs *fstate) breakStmt() {
	for b := fs.bl; b != nil; b = b.parent {
		if b.loop {
			fs.closeTo(b.nactive)
			b.breaks = append(b.breaks, fs.jump())
			return
		}
	}
	panic("glua: compiler: break outside a loop")
}

func (fs *fstate) gotoStmt(name string) {
	for b := fs.bl; b != nil; b = b.parent {
		if l, ok := b.labels[name]; ok { // backward
			fs.closeTo(l.level)
			fs.jumpBack(l.pc)
			return
		}
	}
	fs.bl.gotos = append(fs.bl.gotos, &pendingGoto{name: name, site: fs.jump()})
}

func (fs *fstate) labelStmt(name string) {
	b := fs.bl
	pc := fs.label()
	b.labels[name] = labelPos{pc: pc, level: fs.nactive}
	needClose := false
	kept := b.gotos[:0]
	for _, g := range b.gotos {
		if g.name == name {
			fs.patchList([]int{g.site}, pc)
			needClose = needClose || g.close
		} else {
			kept = append(kept, g)
		}
	}
	b.gotos = kept
	if needClose {
		// a goto arrived from a block with to-be-closed variables: close what is above here
		fs.abc(opClose, fs.nactive, 0, 0)
	}
}
