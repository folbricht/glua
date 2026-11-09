// Command asmgate checks the machine code of the interpreter's hot loop, (*executor).fast.
// The loop is fast only while it makes no Go calls: a call anywhere in it makes the register
// allocator spill the loop's state on every instruction. For amd64 (GOAMD64 v1 and v3) and
// arm64 it fails when
//
//   - fast calls anything other than a GC write barrier, a bounds-check panic or morestack,
//   - the dispatch switch is not a jump table,
//   - the dispatch head or a hot opcode touches the stack more often than the checked-in
//     baseline allows. The design allows one store of pc in the head.
//
// It also fails when fast or checkedLoop would inline less once it grew past the compiler's
// size for a big function, in which only callees costing up to 20 are inlined: a helper over
// that budget would turn into a call, and spill the loop, the day the loop grew. It builds the
// package once as it is and once with both loops padded past that size, through an overlay,
// and compares the calls each inlines.
//
// Stack accesses on the write-barrier slow path, which runs only while the GC is marking, do
// not count. Run with -update to accept a new baseline after an improvement.
//
//	go run ./bench/asmgate
package main

import (
	"bufio"
	"flag"
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"slices"
	"strconv"
	"strings"
)

type config struct {
	name string
	env  []string
}

var configs = []config{
	{"amd64-v1", []string{"GOARCH=amd64", "GOAMD64=v1"}},
	{"amd64-v3", []string{"GOARCH=amd64", "GOAMD64=v3"}},
	{"arm64", []string{"GOARCH=arm64"}},
}

var allowedCalls = []string{"runtime.gcWriteBarrier", "runtime.panicBounds", "runtime.panicIndex", "runtime.morestack"}

var (
	asmLine      = regexp.MustCompile(`^\s+(\S+?):(\d+)\t+0x([0-9a-f]+)\t+[0-9a-f]+\t+(.*?)\s*$`)
	directJump   = regexp.MustCompile(`^(?:J\w*|B\w*|CBN?ZW?|TBN?Z)\s+(?:.*,\s*)?(?:0x([0-9a-f]+)|(-?\d+)\(PC\))$`)
	callRe       = regexp.MustCompile(`^CALL\s+(\S+)`)
	stackRe      = regexp.MustCompile(`\((R?SP)\)`)
	indirectJump = regexp.MustCompile(`^JMP\s+(\S*\([A-Z][A-Z0-9]*\)(\([A-Z][A-Z0-9]*\*\d\))?|R\w+)$`)
)

// region is a part of fast's source: the dispatch head or one case clause.
type region struct {
	name       string
	start, end int
}

func main() {
	update := flag.Bool("update", false, "write the measured spill counts as the new baseline")
	verbose := flag.Bool("v", false, "list every counted stack access")
	baselineFile := flag.String("baseline", "bench/asmgate/baseline.txt", "baseline file")
	flag.Parse()

	regions, loopEnd := parseRegions("fast.go")
	headLine := regions[0].start // regions[0] is the head, from the loop's opening brace
	baseline := readBaseline(*baselineFile)
	measured := map[string]int{}
	failed := false
	tmp, err := os.MkdirTemp("", "asmgate")
	check(err)
	defer os.RemoveAll(tmp)

	if lost := bigInlining(tmp); len(lost) > 0 {
		fmt.Println("inlining when the loops are big:")
		for _, l := range lost {
			fmt.Printf("  FAIL: %s\n", l)
		}
		failed = true
	}

	for _, c := range configs {
		bin := filepath.Join(tmp, c.name+".test")
		build := exec.Command("go", "test", "-c", "-o", bin, ".")
		build.Env = append(os.Environ(), append(c.env, "CGO_ENABLED=0")...)
		if out, err := build.CombinedOutput(); err != nil {
			fatalf("%s: build: %v\n%s", c.name, err, out)
		}
		out, err := exec.Command("go", "tool", "objdump", "-s", `glua\.\(\*executor\)\.fast$`, bin).Output()
		check(err)
		insns := parseAsm(string(out))
		if len(insns) == 0 {
			fatalf("%s: no instructions for fast", c.name)
		}

		var problems []string
		jumpTable := false
		head := headBlock(insns)
		prologueEnd := slices.IndexFunc(insns, func(in insn) bool { return unconditional(in.text) })
		if prologueEnd < 0 || prologueEnd > head[0] {
			prologueEnd = head[0]
		}
		spills := map[string]int{}
		for i, in := range insns {
			if m := callRe.FindStringSubmatch(in.text); m != nil {
				if !slices.ContainsFunc(allowedCalls, func(p string) bool { return strings.HasPrefix(m[1], p) }) {
					problems = append(problems, fmt.Sprintf("forbidden call %s at %s:%d", m[1], in.file, in.line))
				}
			}
			if indirectJump.MatchString(in.text) {
				jumpTable = true
			}
			if !stackRe.MatchString(in.text) || nearBarrier(insns, i) || i < prologueEnd ||
				(i < head[0] || i > head[1]) && exitPath(insns, i, head[0], loopEnd) {
				continue
			}
			r := regionOf(regions, insns, i)
			if i >= head[0] && i <= head[1] {
				if filepath.Base(in.file) == "fast.go" && in.line < headLine {
					continue // the function's prologue, which falls into the head on some ports
				}
				r = "head"
			}
			if r != "" {
				spills[r]++
				if *verbose {
					fmt.Printf("  %-12s %s:%d %s\n", r, filepath.Base(in.file), in.line, in.text)
				}
			}
		}
		if !jumpTable {
			problems = append(problems, "the dispatch switch is not a jump table")
		}
		names := make([]string, 0, len(regions))
		for _, r := range regions {
			names = append(names, r.name) // "head" included: the design allows one store of pc there
		}
		fmt.Printf("%s: %d instructions, jump table %v\n", c.name, len(insns), jumpTable)
		for _, name := range names {
			key := c.name + " " + name
			n := spills[name]
			measured[key] = n
			base, ok := baseline[key]
			switch {
			case !ok && n > 0 && !*update:
				problems = append(problems, fmt.Sprintf("%s touches the stack %d times; the baseline has no entry", name, n))
			case n > base && !*update:
				problems = append(problems, fmt.Sprintf("%s touches the stack %d times, baseline %d", name, n, base))
			case n < base:
				fmt.Printf("  %s improved: %d stack accesses, baseline %d; run with -update\n", name, n, base)
			}
			if n > 0 {
				fmt.Printf("  %-36s %d stack accesses\n", name, n)
			}
		}
		for _, p := range problems {
			fmt.Printf("  FAIL: %s\n", p)
			failed = true
		}
	}
	if *update {
		writeBaseline(*baselineFile, measured)
		fmt.Println("baseline written to", *baselineFile)
		return
	}
	if failed {
		os.Exit(1)
	}
	fmt.Println("ok")
}

type insn struct {
	file string
	line int
	addr uint64
	text string
}

func parseAsm(out string) []insn {
	var insns []insn
	sc := bufio.NewScanner(strings.NewReader(out))
	for sc.Scan() {
		m := asmLine.FindStringSubmatch(sc.Text())
		if m == nil {
			continue
		}
		line, _ := strconv.Atoi(m[2])
		addr, _ := strconv.ParseUint(m[3], 16, 64)
		insns = append(insns, insn{file: m[1], line: line, addr: addr, text: m[4]})
	}
	return insns
}

// nearBarrier reports whether instruction i is within a few instructions of a write-barrier
// call: the spill and reload around it run only while the GC is marking.
func nearBarrier(insns []insn, i int) bool {
	for j := max(0, i-6); j < min(len(insns), i+7); j++ {
		if strings.Contains(insns[j].text, "runtime.gcWriteBarrier") {
			return true
		}
	}
	return false
}

// branchTarget returns the address a direct branch goes to. amd64 listings give absolute
// addresses; arm64 listings count 4-byte instructions relative to the branch.
func branchTarget(in insn) (uint64, bool) {
	m := directJump.FindStringSubmatch(in.text)
	switch {
	case m == nil:
		return 0, false
	case m[1] != "":
		a, _ := strconv.ParseUint(m[1], 16, 64)
		return a, true
	default:
		n, _ := strconv.ParseInt(m[2], 10, 64)
		return uint64(int64(in.addr) + 4*n), true
	}
}

// jumpTargets returns the indices of all instructions that some direct jump lands on.
func jumpTargets(insns []insn) map[int]int {
	index := map[uint64]int{}
	for j, in := range insns {
		index[in.addr] = j
	}
	t := map[int]int{}
	for _, in := range insns {
		if a, ok := branchTarget(in); ok {
			if j, ok := index[a]; ok {
				t[j]++
			}
		}
	}
	return t
}

// headBlock returns the first and last index of the dispatch head: the block that ends in
// the jump table's indirect jump, starting at the nearest jump target before it.
func headBlock(insns []insn) [2]int {
	end := slices.IndexFunc(insns, func(in insn) bool { return indirectJump.MatchString(in.text) })
	if end < 0 {
		return [2]int{-1, -1}
	}
	targets := jumpTargets(insns)
	start := end
	for start > 0 && targets[start] == 0 && !unconditional(insns[start-1].text) {
		start--
	}
	return [2]int{start, end}
}

// exitPath reports whether instruction i lies on a path that leaves the loop: following
// fall-through and unconditional jumps, it reaches the code after the loop (line > loopEnd)
// before it gets back to the dispatch head.
func exitPath(insns []insn, i, headStart, loopEnd int) bool {
	index := map[uint64]int{}
	for j, in := range insns {
		index[in.addr] = j
	}
	seen := map[int]bool{}
	for j := i; j < len(insns) && !seen[j]; j++ {
		seen[j] = true
		in := insns[j]
		if j == headStart {
			return false
		}
		if filepath.Base(in.file) == "fast.go" && in.line > loopEnd {
			return true
		}
		if strings.HasPrefix(in.text, "RET") {
			return true
		}
		if a, ok := branchTarget(in); ok && strings.HasPrefix(in.text, "JMP") {
			t, ok := index[a]
			if !ok {
				return false
			}
			j = t - 1
		}
	}
	return false
}

func unconditional(text string) bool {
	return strings.HasPrefix(text, "JMP ") || strings.HasPrefix(text, "RET")
}

// regionOf names the case clause that instruction i belongs to. Spills and reloads carry the
// source position of the value they move, and inlined helpers carry the helper's, so it
// looks at the nearest instruction from fast.go that is neither, first backwards within the
// block, then forwards.
func regionOf(regions []region, insns []insn, i int) string {
	usable := func(j int) string {
		in := insns[j]
		if filepath.Base(in.file) != "fast.go" || stackRe.MatchString(in.text) {
			return ""
		}
		for _, r := range regions {
			if r.name != "head" && in.line >= r.start && in.line <= r.end {
				return r.name
			}
		}
		return ""
	}
	for j := i - 1; j >= 0 && !unconditional(insns[j].text); j-- {
		if r := usable(j); r != "" {
			return r
		}
	}
	for j := i + 1; j < len(insns); j++ {
		if r := usable(j); r != "" {
			return r
		}
	}
	return ""
}

// parseRegions finds the dispatch head and the case clauses of the switch in fast.
func parseRegions(path string) ([]region, int) {
	fset := token.NewFileSet()
	f, err := parser.ParseFile(fset, path, nil, 0)
	check(err)
	var regions []region
	loopEnd := 0
	ast.Inspect(f, func(n ast.Node) bool {
		fd, ok := n.(*ast.FuncDecl)
		if !ok || fd.Name.Name != "fast" {
			return true
		}
		ast.Inspect(fd.Body, func(n ast.Node) bool {
			loop, ok := n.(*ast.ForStmt)
			if !ok || loop.Cond != nil {
				return true
			}
			loopEnd = fset.Position(loop.End()).Line
			for _, st := range loop.Body.List {
				sw, ok := st.(*ast.SwitchStmt)
				if !ok {
					continue
				}
				regions = append(regions, region{"head", fset.Position(loop.Body.Lbrace).Line, fset.Position(sw.Body.Lbrace).Line})
				for _, cc := range sw.Body.List {
					cc := cc.(*ast.CaseClause)
					var names []string
					for _, e := range cc.List {
						if id, ok := e.(*ast.Ident); ok {
							names = append(names, id.Name)
						}
					}
					name := strings.Join(names, ",")
					if cc.List == nil {
						name = "default"
					}
					regions = append(regions, region{name, fset.Position(cc.Pos()).Line, fset.Position(cc.End()).Line})
				}
			}
			return false
		})
		return false
	})
	if len(regions) == 0 {
		fatalf("no dispatch switch found in %s", path)
	}
	return regions, loopEnd
}

func readBaseline(path string) map[string]int {
	b := map[string]int{}
	data, err := os.ReadFile(path)
	if os.IsNotExist(err) {
		return b
	}
	check(err)
	for line := range strings.SplitSeq(string(data), "\n") {
		f := strings.Fields(line)
		if len(f) != 3 || strings.HasPrefix(line, "#") {
			continue
		}
		n, err := strconv.Atoi(f[2])
		check(err)
		b[f[0]+" "+f[1]] = n
	}
	return b
}

func writeBaseline(path string, m map[string]int) {
	keys := make([]string, 0, len(m))
	for k, n := range m {
		if n > 0 {
			keys = append(keys, k)
		}
	}
	slices.Sort(keys)
	var sb strings.Builder
	sb.WriteString("# Stack accesses per hot opcode in (*executor).fast, outside write-barrier slow paths.\n")
	sb.WriteString("# Opcodes not listed must have none. Written by go run ./bench/asmgate -update.\n")
	for _, k := range keys {
		fmt.Fprintf(&sb, "%s %d\n", k, m[k])
	}
	check(os.WriteFile(path, []byte(sb.String()), 0o644))
}

// loops are the functions that must inline as much when big, and the files that hold them.
var loops = []struct{ file, fn string }{{"fast.go", "fast"}, {"checked_gen.go", "checkedLoop"}}

var (
	inlinedRe = regexp.MustCompile(`^\./(\S+\.go):(\d+):\d+: inlining call to (\S+)`)
	bigRe     = regexp.MustCompile(`function \(\*executor\)\.(\w+) considered 'big'`)
)

// bigInlining builds the package with -m=2 as it is and with each loop padded past the size of
// a big function, and describes the callees that the loops inline only in the first build. A
// helper inlined into another one is lost with it. The padding goes on the line of each
// function's opening brace, so no line number moves.
func bigInlining(tmp string) []string {
	overlay := map[string]string{}
	spans := map[string][2]int{}
	for _, l := range loops {
		src, err := os.ReadFile(l.file)
		check(err)
		fset := token.NewFileSet()
		f, err := parser.ParseFile(fset, l.file, src, 0)
		check(err)
		var fd *ast.FuncDecl
		for _, d := range f.Decls {
			if d, ok := d.(*ast.FuncDecl); ok && d.Name.Name == l.fn {
				fd = d
			}
		}
		if fd == nil {
			fatalf("no func %s in %s", l.fn, l.file)
		}
		spans[l.file] = [2]int{fset.Position(fd.Pos()).Line, fset.Position(fd.End()).Line}
		at := fset.Position(fd.Body.Lbrace).Offset + 1
		pad := " if ex.st.hi < -1 {" + strings.Repeat(" ex.st.hi++;", 1500) + " };"
		padded := filepath.Join(tmp, "big-"+l.file)
		check(os.WriteFile(padded, append(append(append([]byte{}, src[:at]...), pad...), src[at:]...), 0o644))
		abs, err := filepath.Abs(l.file)
		check(err)
		overlay[abs] = padded
	}
	ov := filepath.Join(tmp, "overlay.json")
	var sb strings.Builder
	sb.WriteString(`{"Replace":{`)
	first := true
	for k, v := range overlay {
		if !first {
			sb.WriteString(",")
		}
		first = false
		sb.WriteString(strconv.Quote(k) + ":" + strconv.Quote(v))
	}
	sb.WriteString("}}")
	check(os.WriteFile(ov, []byte(sb.String()), 0o644))

	inlined := func(args ...string) (map[string]int, map[string]bool) {
		cmd := exec.Command("go", append([]string{"build", "-gcflags=-m=2", "-o", os.DevNull}, append(args, ".")...)...)
		cmd.Env = append(os.Environ(), "CGO_ENABLED=0")
		out, err := cmd.CombinedOutput()
		if err != nil {
			fatalf("build with -m=2: %v\n%s", err, out)
		}
		calls, big := map[string]int{}, map[string]bool{}
		for _, line := range strings.Split(string(out), "\n") {
			if m := bigRe.FindStringSubmatch(line); m != nil {
				big[m[1]] = true
			}
			m := inlinedRe.FindStringSubmatch(line)
			if m == nil {
				continue
			}
			span, ok := spans[m[1]]
			if n, _ := strconv.Atoi(m[2]); !ok || n < span[0] || n > span[1] {
				continue
			}
			calls[m[1]+":"+m[2]+" "+m[3]]++
		}
		return calls, big
	}
	normal, _ := inlined()
	padded, big := inlined("-overlay=" + ov)
	for _, l := range loops {
		if !big[l.fn] {
			fatalf("the padding did not make %s big", l.fn)
		}
	}
	sites := map[string]int{} // callee -> call sites it is lost at
	for k, n := range normal {
		if d := n - padded[k]; d > 0 {
			sites[k[strings.IndexByte(k, ' ')+1:]] += d
		}
	}
	var lost []string
	for name, n := range sites {
		lost = append(lost, fmt.Sprintf("%s is not inlined (call sites lost: %d): it costs over 20, or a helper that inlines it does", name, n))
	}
	slices.Sort(lost)
	return lost
}

func check(err error) {
	if err != nil {
		fatalf("%v", err)
	}
}

func fatalf(format string, args ...any) {
	fmt.Fprintf(os.Stderr, "asmgate: "+format+"\n", args...)
	os.Exit(1)
}
