package glua

// Instructions are 32 bits with byte-aligned fields: op:8 A:8 B:8 C:8, or op:8 A:8 Bx:16.
// Byte-wide operands index a frame viewed as *[256]Value with no bounds check. Some
// instructions are followed by one auxiliary word: a hint site, a 32-bit jump offset, a
// wide constant index or a size.
//
// Compare-and-jump instructions fall through when their test equals C (0 or 1) and jump by
// their aux word otherwise. The polarity is explicit because, with NaN, not (a < b) is not
// a >= b. Jump offsets count words from the word after the instruction and its aux word.
const (
	opBad = iota // never emitted; also the padding word after the last instruction

	// loads and moves
	opMove      // R[A] = R[B]
	opLoadK     // R[A] = K[Bx]
	opLoadKX    // R[A] = K[aux]
	opLoadI     // R[A] = int16(Bx)
	opLoadF     // R[A] = float(int16(Bx))
	opLoadNil   // R[A], ..., R[A+B] = nil
	opLoadFalse // R[A] = false
	opLoadTrue  // R[A] = true

	// captured variables. A captured local that is never assigned is copied into closures;
	// one that is assigned lives in a cell, and its register holds the cell.
	opGetUpval  // R[A] = Up[B], the raw value: for a cell, the cell itself
	opGetUpCell // R[A] = Up[B].cell
	opSetUpCell // Up[B].cell = R[A]
	opNewCell   // R[A] = new cell holding R[A]
	opGetCell   // R[A] = R[B].cell
	opSetCell   // R[A].cell = R[B]

	// globals: fields of the globals table of the running closure
	opGetGlobal // R[A] = G[K[Bx]]; aux: hint site
	opSetGlobal // G[K[Bx]] = R[A]; aux: hint site
	opGetEnv    // R[A] = G, for a free _ENV read

	// tables
	opGetTable  // R[A] = R[B][R[C]]
	opGetIndex  // R[A] = R[B][C], integer key 0..255
	opGetField  // R[A] = R[B][K[C]]; aux: hint site
	opSetTable  // R[A][R[B]] = R[C]
	opSetIndex  // R[A][B] = R[C], integer key 0..255
	opSetField  // R[A][K[B]] = R[C]; aux: hint site
	opSetTableK // R[A][R[B]] = K[C]
	opSetIndexK // R[A][B] = K[C], integer key 0..255
	opSetFieldK // R[A][K[B]] = K[C]; aux: hint site
	opSelf      // R[A+1] = R[B]; R[A] = R[B][K[C]]; aux: hint site
	opNewTable  // R[A] = {}; B: hash size, C: 1 when the array items look like scalars; aux: array size
	opSetList   // R[A][aux+i] = R[A+i] for 1 <= i <= B; B=0: up to top

	// arithmetic and bitwise operators: R[A] = R[B] op R[C]
	opAdd
	opSub
	opMul
	opDiv
	opMod
	opPow
	opIDiv
	opBAnd
	opBOr
	opBXor
	opShl
	opShr

	// the same with a constant right operand: R[A] = R[B] op K[C]
	opAddK
	opSubK
	opMulK
	opDivK
	opModK
	opPowK
	opIDivK
	opBAndK
	opBOrK
	opBXorK
	opShlK
	opShrK

	opUnm    // R[A] = -R[B]
	opNot    // R[A] = not R[B]
	opLen    // R[A] = #R[B]
	opBNot   // R[A] = ~R[B]
	opConcat // R[A] = R[A] .. ... .. R[A+B-1]

	// jumps
	opJmp     // pc += int16(Bx); a backward jump ticks
	opJmpX    // pc += int32(aux)
	opEqJmp   // test R[A] == R[B]
	opLtJmp   // test R[A] < R[B]
	opLeJmp   // test R[A] <= R[B]
	opEqKJmp  // test R[A] == K[B]
	opLtKJmp  // test R[A] < K[B]
	opLeKJmp  // test R[A] <= K[B]
	opGtKJmp  // test R[A] > K[B], that is K[B] < R[A]
	opGeKJmp  // test R[A] >= K[B], that is K[B] <= R[A]
	opTestJmp // test R[A] is truthy
	opTestSet // test R[B] is truthy; fall through when it equals C, else R[A] = R[B] and jump

	// loops
	opForPrep  // prepare R[A..A+3]; skip the loop, pc += Bx, when it runs no times
	opForLoop  // count down; while iterations remain, R[A+3] = next, pc -= Bx
	opTForPrep // mark R[A+3] to be closed; pc += Bx, to the TFORCALL
	opTForCall // R[A+4], ..., R[A+2+C] = R[A](R[A+1], R[A+2]); C-1 results, as CALL counts them
	opTForLoop // if R[A+4] ~= nil then R[A+2] = R[A+4]; pc -= Bx end

	// calls
	opCall       // R[A], ..., R[A+C-2] = R[A](R[A+1], ..., R[A+B-1]); B=0: args to top; C=0: results to top
	opTailCall   // return R[A](R[A+1], ..., R[A+B-1]); B=0: args to top
	opReturn     // return R[A], ..., R[A+B-2]; B=0: up to top
	opReturn0    // return
	opReturn1    // return R[A]
	opClosure    // R[A] = closure(P[Bx])
	opVarargPrep // adjust a vararg function's frame; A: number of fixed parameters
	opVararg     // R[A], ..., R[A+C-2] = ...; C=0: all, to top
	opTBC        // mark R[A] to be closed
	opClose      // close the to-be-closed variables in R[A] and above

	// built-ins. FASTCALL stands right before the CALL of a library function with B-1
	// arguments: if R[A] is built-in aux and its inline form applies, it does the call and
	// skips the CALL; otherwise it falls through to it.
	opFastCall
	// FASTSELECT stands right before the VARARG and CALL (or TAILCALL) of select(x, ...): if
	// R[A] is the built-in select and the CALL wants one result, it reads the result from the
	// frame and skips both.
	opFastSelect

	numOps
)

// operand kinds, for the verifier and the disassembler
type operand uint8

const (
	oNone  operand = iota
	oReg           // a register
	oK             // a constant index
	oKStr          // a constant index; the constant must be a string
	oUp            // an upvalue index
	oInt           // a plain number
	oProto         // a prototype index
	oJump          // a signed 16-bit jump (Bx)
	oFwd           // an unsigned forward jump (Bx)
	oBack          // an unsigned backward jump (Bx)
	oSite          // aux: a hint site
	oJumpX         // aux: a signed 32-bit jump
	oKX            // aux: a constant index
	oSize          // aux: a size or an index
)

// opInfo describes one opcode. wide is set when B and C together form Bx.
type opInfo struct {
	name    string
	a, b, c operand
	wide    bool
	aux     operand
}

var opTable = [numOps]opInfo{
	opBad:        {name: "BAD"},
	opMove:       {"MOVE", oReg, oReg, oNone, false, oNone},
	opLoadK:      {"LOADK", oReg, oK, oNone, true, oNone},
	opLoadKX:     {"LOADKX", oReg, oNone, oNone, false, oKX},
	opLoadI:      {"LOADI", oReg, oInt, oNone, true, oNone},
	opLoadF:      {"LOADF", oReg, oInt, oNone, true, oNone},
	opLoadNil:    {"LOADNIL", oReg, oInt, oNone, false, oNone},
	opLoadFalse:  {"LOADFALSE", oReg, oNone, oNone, false, oNone},
	opLoadTrue:   {"LOADTRUE", oReg, oNone, oNone, false, oNone},
	opGetUpval:   {"GETUPVAL", oReg, oUp, oNone, false, oNone},
	opGetUpCell:  {"GETUPCELL", oReg, oUp, oNone, false, oNone},
	opSetUpCell:  {"SETUPCELL", oReg, oUp, oNone, false, oNone},
	opNewCell:    {"NEWCELL", oReg, oNone, oNone, false, oNone},
	opGetCell:    {"GETCELL", oReg, oReg, oNone, false, oNone},
	opSetCell:    {"SETCELL", oReg, oReg, oNone, false, oNone},
	opGetGlobal:  {"GETGLOBAL", oReg, oKStr, oNone, true, oSite},
	opSetGlobal:  {"SETGLOBAL", oReg, oKStr, oNone, true, oSite},
	opGetEnv:     {"GETENV", oReg, oNone, oNone, false, oNone},
	opGetTable:   {"GETTABLE", oReg, oReg, oReg, false, oNone},
	opGetIndex:   {"GETINDEX", oReg, oReg, oInt, false, oNone},
	opGetField:   {"GETFIELD", oReg, oReg, oKStr, false, oSite},
	opSetTable:   {"SETTABLE", oReg, oReg, oReg, false, oNone},
	opSetIndex:   {"SETINDEX", oReg, oInt, oReg, false, oNone},
	opSetField:   {"SETFIELD", oReg, oKStr, oReg, false, oSite},
	opSetTableK:  {"SETTABLEK", oReg, oReg, oK, false, oNone},
	opSetIndexK:  {"SETINDEXK", oReg, oInt, oK, false, oNone},
	opSetFieldK:  {"SETFIELDK", oReg, oKStr, oK, false, oSite},
	opSelf:       {"SELF", oReg, oReg, oKStr, false, oSite},
	opNewTable:   {"NEWTABLE", oReg, oInt, oInt, false, oSize},
	opSetList:    {"SETLIST", oReg, oInt, oNone, false, oSize},
	opAdd:        {"ADD", oReg, oReg, oReg, false, oNone},
	opSub:        {"SUB", oReg, oReg, oReg, false, oNone},
	opMul:        {"MUL", oReg, oReg, oReg, false, oNone},
	opDiv:        {"DIV", oReg, oReg, oReg, false, oNone},
	opMod:        {"MOD", oReg, oReg, oReg, false, oNone},
	opPow:        {"POW", oReg, oReg, oReg, false, oNone},
	opIDiv:       {"IDIV", oReg, oReg, oReg, false, oNone},
	opBAnd:       {"BAND", oReg, oReg, oReg, false, oNone},
	opBOr:        {"BOR", oReg, oReg, oReg, false, oNone},
	opBXor:       {"BXOR", oReg, oReg, oReg, false, oNone},
	opShl:        {"SHL", oReg, oReg, oReg, false, oNone},
	opShr:        {"SHR", oReg, oReg, oReg, false, oNone},
	opAddK:       {"ADDK", oReg, oReg, oK, false, oNone},
	opSubK:       {"SUBK", oReg, oReg, oK, false, oNone},
	opMulK:       {"MULK", oReg, oReg, oK, false, oNone},
	opDivK:       {"DIVK", oReg, oReg, oK, false, oNone},
	opModK:       {"MODK", oReg, oReg, oK, false, oNone},
	opPowK:       {"POWK", oReg, oReg, oK, false, oNone},
	opIDivK:      {"IDIVK", oReg, oReg, oK, false, oNone},
	opBAndK:      {"BANDK", oReg, oReg, oK, false, oNone},
	opBOrK:       {"BORK", oReg, oReg, oK, false, oNone},
	opBXorK:      {"BXORK", oReg, oReg, oK, false, oNone},
	opShlK:       {"SHLK", oReg, oReg, oK, false, oNone},
	opShrK:       {"SHRK", oReg, oReg, oK, false, oNone},
	opUnm:        {"UNM", oReg, oReg, oNone, false, oNone},
	opNot:        {"NOT", oReg, oReg, oNone, false, oNone},
	opLen:        {"LEN", oReg, oReg, oNone, false, oNone},
	opBNot:       {"BNOT", oReg, oReg, oNone, false, oNone},
	opConcat:     {"CONCAT", oReg, oInt, oNone, false, oNone},
	opJmp:        {"JMP", oNone, oJump, oNone, true, oNone},
	opJmpX:       {"JMPX", oNone, oNone, oNone, false, oJumpX},
	opEqJmp:      {"EQJMP", oReg, oReg, oInt, false, oJumpX},
	opLtJmp:      {"LTJMP", oReg, oReg, oInt, false, oJumpX},
	opLeJmp:      {"LEJMP", oReg, oReg, oInt, false, oJumpX},
	opEqKJmp:     {"EQKJMP", oReg, oK, oInt, false, oJumpX},
	opLtKJmp:     {"LTKJMP", oReg, oK, oInt, false, oJumpX},
	opLeKJmp:     {"LEKJMP", oReg, oK, oInt, false, oJumpX},
	opGtKJmp:     {"GTKJMP", oReg, oK, oInt, false, oJumpX},
	opGeKJmp:     {"GEKJMP", oReg, oK, oInt, false, oJumpX},
	opTestJmp:    {"TESTJMP", oReg, oNone, oInt, false, oJumpX},
	opTestSet:    {"TESTSET", oReg, oReg, oInt, false, oJumpX},
	opForPrep:    {"FORPREP", oReg, oFwd, oNone, true, oNone},
	opForLoop:    {"FORLOOP", oReg, oBack, oNone, true, oNone},
	opTForPrep:   {"TFORPREP", oReg, oFwd, oNone, true, oNone},
	opTForCall:   {"TFORCALL", oReg, oNone, oInt, false, oNone},
	opTForLoop:   {"TFORLOOP", oReg, oBack, oNone, true, oNone},
	opCall:       {"CALL", oReg, oInt, oInt, false, oNone},
	opTailCall:   {"TAILCALL", oReg, oInt, oInt, false, oNone},
	opReturn:     {"RETURN", oReg, oInt, oNone, false, oNone},
	opReturn0:    {"RETURN0", oNone, oNone, oNone, false, oNone},
	opReturn1:    {"RETURN1", oReg, oNone, oNone, false, oNone},
	opClosure:    {"CLOSURE", oReg, oProto, oNone, true, oNone},
	opVarargPrep: {"VARARGPREP", oInt, oNone, oNone, false, oNone},
	opVararg:     {"VARARG", oReg, oNone, oInt, false, oNone},
	opTBC:        {"TBC", oReg, oNone, oNone, false, oNone},
	opClose:      {"CLOSE", oReg, oNone, oNone, false, oNone},
	opFastCall:   {"FASTCALL", oReg, oInt, oNone, false, oSize},
	opFastSelect: {"FASTSELECT", oReg, oNone, oNone, false, oNone},
}

// hasAux reports whether an opcode is followed by an auxiliary word.
var hasAux = func() (t [256]bool) {
	for op, info := range opTable {
		t[op] = info.aux != oNone
	}
	return t
}()

func opName(op uint8) string {
	if int(op) < len(opTable) && opTable[op].name != "" {
		return opTable[op].name
	}
	return "BAD"
}

func iABC(op, a, b, c uint8) uint32      { return uint32(op) | uint32(a)<<8 | uint32(b)<<16 | uint32(c)<<24 }
func iABx(op, a uint8, bx uint16) uint32 { return uint32(op) | uint32(a)<<8 | uint32(bx)<<16 }

func decA(i uint32) int  { return int(uint8(i >> 8)) }
func decB(i uint32) int  { return int(uint8(i >> 16)) }
func decC(i uint32) int  { return int(uint8(i >> 24)) }
func decBx(i uint32) int { return int(i >> 16) }

// exit is why fast returned to the driver.
type exit uint8

const (
	exBadOp      exit = iota // an opcode the loop does not know
	exSlowOp                 // the instruction at pc-1 needs the driver
	exReturn                 // a frame the VM started itself has returned: goEntry or cont
	exResults                // a call returned one result inline, but its caller wanted another count
	exHostCall               // the CALL at pc-1 calls a Go function
	exGrowStack              // the CALL at pc-1 needs a larger register stack
	exGrowFrames             // the CALL at pc-1 needs a larger frame list
	exTick                   // the tick counter expired
)
