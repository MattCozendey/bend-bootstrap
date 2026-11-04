// gen2.ts: a general, fast, deliberately incomplete prover for Bend2 proof holes.
// ================================================================================
//
// Dev tool, OUTSIDE the trust: bend2 checks each candidate in-process, and the kernel (the gate,
// ~/lead/gate.sh) is the only judge of what it writes. Exempt from review sweeps (AGENTS.md 2.1.3)
// and from the TypeScript rules of 2.5, by the owner's explicit decision: it is a dev tool outside the
// trust that must only help and be fast (as src/Compiler/Machine/scripts/gen.ts). Excluded in
// tsconfig.json for the same reason.
//
// STATUS: v3 (stopped by the owner's order; see NEXT): prove (several defs per run), serve/ask (the
// book stays loaded), batch and bench modes; decomposition of large goals; forward unification;
// rewrites on the raw goal and with hypotheses' normal forms. 178/256 (70%) of the benchmark.
//
// PURPOSE
// -------
// Given a .bend file and a def to prove (its whole body, or the ?TODO holes in its body), write a
// proof that bend2 accepts, or give up fast. Partial proofs (a skeleton whose open subgoals are
// ?TODO, each with its goal and context printed) are suggestions for the agent that owns the proof:
// never commit a partial as a finished proof.
//
// RUN (bun; in WSL through ~/lead/heavy.sh, as every bend2 load):
//   bun src/Shared/scripts/gen2.ts prove <file.bend> <def> [<def> ...] [--only RE] [options]
//       prove each <def> of <file.bend> (defs of the file itself; with --only RE also every def of the
//       file whose body is exactly ?TODO and whose name matches RE), the book loaded once for all:
//       a body that is exactly ?TODO is proven whole (case splits allowed); otherwise each ?TODO in
//       the body (leaf tactics, then decomposition). Prints the proof text (ready to paste) on stdout,
//       under a `# <def>` line when there are several; a miss prints its partial; exit 2 if any miss.
//   bun src/Shared/scripts/gen2.ts serve <file.bend> [--port 7311]
//   bun src/Shared/scripts/gen2.ts ask [--port 7311] <def> [<def> ...] [prove options]
//       serve keeps the book loaded (a local HTTP server on 127.0.0.1) and answers `ask`, which takes
//       the arguments of prove after the file and prints what prove prints (same exit code). Before
//       each ask, the entry file is re-read if it changed: only its own defs are re-parsed and
//       re-checked (the imports stay loaded; a change in an imported file needs a restart). Measured
//       on moves_copy.bend (5730 entries): load + check 20 s once, then an ask of two leaves 0.27 s;
//       a reload after an edit of need_big.bend 0.4 s. Start it in the background (through heavy.sh,
//       which holds one of the 3 slots while it runs: stop it when done), e.g.
//         ~/lead/heavy.sh bun Shared/scripts/gen2.ts serve Compiler/Machine/moves_copy.bend &
//         bun Shared/scripts/gen2.ts ask kc.at fs.arg.at --budget 8000 --partial
//   bun src/Shared/scripts/gen2.ts batch <file.bend> [--out DIR] [--only RE] [options]
//       every def of the book (the file and all it imports, not Base) with a ?TODO in its body: a body
//       that is exactly ?TODO is proven whole, other holes one by one. Writes DIR/report.txt (per hole:
//       the proof, or OPEN with its goal and context and the best partial with its open subgoals) and
//       DIR/gen2.patch (a unified diff from the repository root with the proven holes filled; apply
//       with `git apply DIR/gen2.patch`; partials never go in the patch). DIR defaults to ./gen2-out.
//   bun src/Shared/scripts/gen2.ts bench <file.bend> [options]
//       benchmark: for each proven lemma of <file.bend> (in book order), forget its body, re-prove it
//       with only the defs before it, and report hit rate by size, time and tactics.
//   options:
//       --budget MS    time budget per def (default 4000)
//       --splits N     max case-split depth (default 6; 3 candidates at the top, 2 below depth 2, 1 below depth 4)
//       --depth N      max leaf depth: nesting of apply/premise (default 3)
//       --rw N         max rewrites in a chain (default 4)
//       --beam N       rewrite candidates explored per goal (default 4)
//       --fuel N       def lookups allowed per single check (default 300000)
//       --partial      on failure, print the best partial proof (holes with goals)
//       --no-decomp    do not decompose open subgoals (see DESIGN)
//       --hole-budget MS  budget of each open subgoal in the decomposition (default budget/4, >= 300)
//       --stream       print each closed subgoal to stderr as it is found
//       --only RE      bench: only defs whose name matches RE;  --max N: at most N defs
//       --json FILE    bench: write per-def results as JSON
//       --debug        print internal errors and failed final checks
//   example (WSL):
//       cd /mnt/c/Users/mathe/source/repos/bb-wt/gen2/src
//       ~/lead/heavy.sh bun Shared/scripts/gen2.ts bench Compiler/need_big.bend --budget 3000
//       ~/lead/heavy.sh bun Shared/scripts/gen2.ts prove Compiler/need_big.bend le_trans --partial
//
// DESIGN
// ------
// * In-process checking: the book is loaded and validated ONCE with bend2's own book_load and
//   book_valid. A candidate is proof TEXT, parsed by bend2's parser in the def's file scope (its
//   namespace and aliases) with the subgoal's context names bound, then checked by bend2's
//   term_check against the subgoal's goal type in its context (never a bend2 process per try). The
//   final proof is checked with def_check on that def only. What is checked is what is printed.
// * Fuel and time: book.tlds is wrapped in a Proxy that counts def lookups (every unfolding goes
//   through it): each check gets --fuel lookups, and the whole def has a deadline (--budget). Out of
//   fuel = that candidate fails; past the deadline = the search stops and the best partial is kept.
//   A stack overflow in the checker is a failed candidate.
// * Normal form: nf(t) is a bounded strong normal form built on term_wnf: a stuck call stays a call
//   (bend2's canonical stuck form), its arguments are normalized, a closed constant (a def with no
//   parameter) is unfolded only when its value is tiny, and a node budget falls back to the raw term.
//   Literals are canonical (Succ/Zero chains to Nat literals, U32 words to U32 literals).
// * Lemma index (built once): every def with a body (or Base's) by the head symbol of its conclusion
//   (an equation: by the head of its left side; a bare type parameter: the ex-falso bucket), and a
//   rewrite index by the head of each side of an equation conclusion. Only defs before the target
//   in book order are candidates (the target itself only as the induction hypothesis).
// * Matching: first-order, on lowered terms, the conclusion (parameters as metavariables) against the
//   goal (raw, then its normal form). Parameters not fixed by the conclusion are fixed by matching
//   premises against hypotheses; if still open, the lemma is skipped (no enumeration).
// * Search, bounded everywhere (no blowups): iterative deepening on cost = split depth + leaf depth;
//   at most 3 split candidates per node (only pending binders that block evaluation); at most
//   --beam rewrite children per goal; at most 48 lemma candidates per goal; memo per (context, goal,
//   demand) of successes and of failures at a budget; a cycle check on the goal path; per-check fuel;
//   per-def deadline. Nothing ever enumerates combinations of arguments.
// * Decomposition (large goals): when the full search fails, a partial pass (splits <= 3, depth <= 2)
//   keeps the best skeleton (fewest holes, then most closed subgoals); each hole is then attacked
//   with its own budget (--hole-budget, deeper leaf depth); a hole that stays open takes one step
//   (bestStep: the most specific callee whose open premises are fewest and smallest, none restating
//   the goal) and its premises recurse, at most 2 levels, all holes within 2 x --budget. If every
//   hole closes, the proof is full (tag "decomp").
//
// TACTICS (in this order)
// -----------------------
// Node (a def body with pending binders):
//   1. leaf: introduce all pending binders, run the leaf tactics.
//   2. split: `match x:` on a pending binder x of a datatype that blocks evaluation (the strict
//      argument of a stuck call, in the goal or in a hypothesis), each arm solved recursively. The
//      self-call (induction hypothesis) is allowed only below a split; bend2 checks its descent.
// Leaf (a goal in a context), memoized:
//   1. closers: `{==}`, the unit constructor (Unit{}), a hypothesis whose type converts.
//   2. intro: a function goal gets `x => ...`.
//   3. absurd: a hypothesis whose normal form is Empty gives Empty.absurd(GOAL, h) (the goal as stated,
//      kernel rule R3); for Empty goals, a hypothesis that equates two different constructors is
//      discriminated by a predicate def on their type (`%h : P(_); Unit{}`); with depth, an ex-falso
//      lemma (conclusion: its own type parameter) whose premise a closer proves.
//   4. apply: hypotheses (functions, also through aliases), the induction hypothesis, then the indexed
//      lemmas whose conclusion matches (raw against raw goal and normal form, normal form of the
//      conclusion against the normal form of the goal; every distinct solution is tried), most
//      specific pattern first, at most CAPS[level] completions per goal (48, 12, 4, 2 by premise
//      level). A parameter that the conclusion leaves open is fixed by matching a premise against a
//      hypothesis (raw or normal form), else (top level only, depth >= 2) by unifying a premise with
//      an indexed lemma's conclusion (forward: le_trans's middle term). Premises at depth - 1.
//   5. rewrite: `%e : P; rest` with an equation from a hypothesis (raw or normal form, both
//      directions, Equal.sym), the induction hypothesis or an indexed lemma whose side matches a
//      subterm of the goal: of nf(goal), and of the goal as stated (a lemma stated on raw forms); P is
//      that base with the subterm replaced by `_` (kernel rule R2: rewrite, do not convert). In a
//      rewrite, a premise {a == x} with x an open parameter fixes x := a (then {==}). Rewrites of
//      blocking subterms first; a rewrite that closes by {==} wins at once; else the best --beam
//      continue with one less rewrite.
//
// OUTPUT
// ------
// * full proof: the body text on stdout, indented as a def body (two spaces), checked by def_check.
// * partial (--partial, and always in batch): the best skeleton (fewest holes, then most closed
//   subgoals) with ?TODO holes, then for each hole its case path, goal and context (raw and normal
//   form). A hole inside an applied lemma has the path <case path>#<callee>.<parameter index>.
// * streaming (--stream): each closed subgoal (its case path and first line) on stderr.
//
// BENCHMARK
// ---------
// Rerun (WSL, from src/):  ~/lead/heavy.sh bun Shared/scripts/gen2.ts bench <file> --budget 3000 --partial
// Each proven lemma of <file> (book order; a def whose conclusion is a proposition) has its body
// forgotten in memory (no file is touched) and is re-proven with only the defs before it; size class =
// non-empty lines of its original body (S 1-3, M 4-10, L 11+). Measured at commit 95e13d5, budget 3000 ms:
//   file                   tried  full       S       M       L      partial (closed/total)  median
//   need_big.bend          119  81 (68%)   28/36   36/49   17/34   29 (123/161)               8 ms
//   heap_facts.bend         70  57 (81%)   14/14   33/40   10/16   11 (19/32)                 6 ms
//   statement_runs.bend     67  40 (60%)   18/18   19/28   3/21    10 (17/44)                31 ms
//   total                  256  178 (70%); every hit takes < 3 s (median a few ms); a miss runs to the budget,
//   then the partial pass and the decomposition (up to 3 x budget). The kernel (gate) accepts gen2's
//   need_big proofs pasted in place of the originals (bend2 ALL PROOFS CHECK, kdiag3 0 fail).
//   (History and raw results: bb-wt/reports/gen2.md and bb-wt/scratch/gen2/, if present.)
//
// LIMITS
// ------
// * No helper-lemma synthesis (a match on a computed value or an introduced binder needs its own def).
// * Splits only in whole-body mode; ?TODO holes inside a body get leaf tactics only.
// * No lets (`+x = ...`) in output, no congruence tactic beyond rewriting, no templates (~ binders).
// * Matching is syntactic (after the bounded normal form): a lemma stated in a shape that only
//   converts to the goal by deeper computation is missed.
// * Hypotheses are never rewritten (forward reasoning): a fact that needs one hypothesis rewritten
//   by another before a lemma applies (k.cell_of) is missed.
// * Whole simulation proofs (moves.bend's holes) are out of reach: their structure is not found by
//   a bounded search; gen.ts writes those, and gen2 proves the leaves they state.
// * Printed names: a term of a file that the target file does not import under an alias prints as
//   its path name (in goals only; a candidate that needs one fails to parse and is skipped).
//
// NEXT (the ordered plan, for whoever continues; keep it current)
// ----
// 1. Book load between calls: DONE (serve/ask, commit ff24e5e): moves_copy.bend (5730 entries) loads
//    and checks in about 20-30 s once, then each ask takes well under 1 s; an edit of the entry file
//    costs a re-check of that file only. Next: an option to reload an imported file too (today a
//    restart), and a slot policy for heavy.sh (a server holds one of the 3 slots while it runs).
// 2. The implementer's 3 misses, in bb-wt/impl src/Compiler/Machine/moves_copy.bend at commit
//    c28021c; the hand proofs there are the references (regression set: add them to a bench-like run
//    with `ask kc.at fs.arg.at kept.at.own --whole --partial`):
//    a. kc.at: destructure the hypothesis hkc : D.Kept.cells(..) (a Tuple of facts) with
//       `match hkc: case Tuple{_, Tuple{kg, _}}`, then apply kept.at.own with xs = List.append(ps, Nil)
//       (bound by matching kg's type) and its premise hm rewritten by mem.app.nil. Today the split
//       candidates open a record only when no blocker exists. Drafted, NOT tested, not committed:
//       open pending binders of one-constructor types with fields first (at most 2), except U32, F32,
//       Chr, Word.Con, Word.Nil (they are records too, and splitting them to bits is useless), in
//       splitCands before the blockers. Measure the three bench files after it (it may cost splits).
//    b. fs.arg.at: ps is general; the proof is one rewrite with e (Equal.sym) of every occurrence of
//       Cr.Cir.Cells.get(M, z) in the normal form of D.Fs(M, ps, z), then {==}. gen2 split on ps
//       instead (D.Mem(ps, z) blocks) and missed the rewrite: check why the leaf rewrite of the
//       unsplit goal fails (motive size cap 600 nodes in rewrite? the normal form keeps D.Fd(..)
//       calls?); with GEN2_TRACE=1 each rewrite candidate and motive is printed.
//    c. kept.at.own: needs U6.kg.at with premises from U13.own.lo, U13.own.end and D.u.lt (through
//       N.le_rw_r, a transitivity-like step with an explicit middle term), then a 2-step rewrite of the
//       D.Kept.if(Bool.or(..)) condition by hm and ht. The lead's diagnosis: induction on the fuel of
//       the recursive hypothesis hk : D.Kept.go(Nat.sub(..), ..) with the fuel generalized, through a
//       helper lemma: synthesize a helper def whose statement is the subgoal with the computed fuel
//       replaced by a fresh variable (and the hypotheses that mention it), prove it whole (split on the
//       fuel, IH), and apply it. That is item 5 below; until then this lemma is out of reach.
// 3. Functions counted as lemmas: FIXED (95e13d5): the bench took `ones` (a function returning
//    Word(n)) for a lemma and pasted another body; isPropType now accepts only propositions. Verified:
//    gen2's 81 need_big proofs pasted in place pass bend2 and the kernel (kdiag3: 0 fail).
// 4. Derived hypotheses (forward reasoning): rewrite a hypothesis by another equation, the term
//    `(%E : P; h)` used as a closer or to bind a lemma's premise (k.cell_of in statement_runs). Drafted
//    in bb-wt/scratch/gen2/p14.py (not applied, not tested). Should move statement_runs M (19/28).
// 5. Helper-lemma synthesis: a match on a computed value, an introduced binder, or a generalized
//    fuel needs its own def; emit the helper (its statement from the subgoal), prove it as a separate
//    job in the same book (parse it into a shadow book: Object.create(book.tlds), as def_check does
//    for templates), and output both. Should move need_big L (17/34) and kept.at.own.
// 6. Fail fast on misses: a miss costs budget + partial pass + decomposition (up to 3 x budget;
//    statement_runs L lemmas take 4-7 s each). A premise not simpler than its goal should cost two
//    levels; memo rewrite candidates per goal; a cheaper decomposition pass.
// 7. Readable motives: stop the normal form at a wrapper def when its unfolding stays stuck
//    (Cr.Cir.is_cell(i, im, fi, nx) instead of its Bool.or body; Cmp.is_lt(U32.cmp(..)) instead of
//    U32.is_lt(..)). Cosmetic, but the hand proofs read better.
// 8. Closed rewrites: zero-parameter lemmas (literal facts such as lit_M) in the rewrite index
//    (need_big val_M, val_65536, sq_65536: S misses).
// 9. Splits inside ?TODO holes of a partial body (the hole's pending binders), not only whole bodies.
// 10. Read bb-wt/reports/impl.md (the implementer's list of leaves gen2 missed) and close those kinds.
//
// EXTEND
// ------
// A new leaf tactic goes in `leaf` (keep the order cheap -> expensive), returning a Pf or null and
// tagging itself in `tags` for the benchmark. A new node tactic goes in `solve`. Candidate lemmas come
// from `lemmaCands` (apply) and `rwIndex` (rewrite).

import * as fs from "node:fs";
import * as path from "node:path";
import * as B from "../../../bend/bend2/bend.ts";

type HTerm = B.HTerm;
type LTerm = B.LTerm;

// ---- options ----
const argv = process.argv.slice(2);
const MODE = argv[0], FILE = argv[1], TARGET = argv[2];
const opt = (k: string, d: string) => { const i = argv.indexOf("--" + k); return i >= 0 ? argv[i + 1] : d; };
const flag = (k: string) => argv.includes("--" + k);
let BUDGET = 0, MAX_SPLIT = 0, MAX_DEPTH = 0, MAX_RW = 0, BEAM = 0, FUEL_CHECK = 0, HOLE_BUDGET = 0;
let DECOMP = true, PARTIAL = false, STREAM = false, DEBUG = false;
const readOpts = () => {
  BUDGET = +opt("budget", "4000");
  MAX_SPLIT = +opt("splits", "6");
  MAX_DEPTH = +opt("depth", "3");
  MAX_RW = +opt("rw", "4");
  BEAM = +opt("beam", "4");
  FUEL_CHECK = +opt("fuel", "300000");
  DECOMP = !flag("no-decomp");
  HOLE_BUDGET = +opt("hole-budget", String(Math.max(300, BUDGET / 4)));
  PARTIAL = flag("partial"); STREAM = flag("stream"); DEBUG = flag("debug");
};
readOpts();
const FUEL_NF = 100000;
const FUEL_FINAL = 50000000;
const NF_NODES = 3000;
const MAX_CANDS = 48;
const CAPS = [48, 12, 4, 2]; // matched apply candidates tried, by premise level below the leaf
const MAX_SPLIT_CANDS = 3;
const MAX_DECOMP = 2;
const META = 1 << 20;

// ---- fuel and time ----
class Stop { constructor(readonly why: string) {} }
const OOF = new Stop("fuel"), TIMEOUT = new Stop("time"), LIN = new Stop("linearity");
let fuel = Infinity, deadline = Infinity, ticks = 0, internal = 0;

const attempt = <T>(n: number, f: () => T): T | undefined => {
  const old = fuel;
  fuel = n;
  try {
    return f();
  } catch (e: any) {
    if (e === TIMEOUT) throw e;
    if (!(e instanceof Stop) && !(e instanceof RangeError) && !(e && e.$ === "Err")) {
      internal++;
      if (DEBUG) console.error("[gen2] internal:", e?.stack ?? e);
    }
    return undefined;
  } finally {
    fuel = old;
  }
};

// ---- ask: a client of `serve` (loads nothing) ----
if (MODE === "ask") {
  const port = +opt("port", "7311");
  const args = argv.slice(1);
  const res = await fetch("http://127.0.0.1:" + port + "/prove", { method: "POST", body: JSON.stringify({ args }) }).catch((e) => null);
  if (!res) { console.error("gen2 ask: no server on port " + port + " (start one: gen2.ts serve <file.bend>)"); process.exit(1); }
  const r: any = await res.json();
  if (r.stderr) process.stderr.write(r.stderr);
  if (r.stdout) process.stdout.write(r.stdout);
  process.exit(r.code);
}

// ---- load ----
const entry = fs.realpathSync(path.resolve(FILE ?? ""));
const TOP = path.dirname(entry) + "/";
const entryText = fs.readFileSync(entry, "utf8");
const entryNames = new Set([...entryText.matchAll(/^def\s+([A-Za-z_][\w.]*)\(/gm)].flatMap((m) => [m[1], m[1].replace(/^[^.]+\./, "")]));
const autoImports: { file: string; alias: string; ns: string; proofs: Set<string> }[] = [];
if (entryText.includes("?TODO")) {
  for (const name of fs.readdirSync(TOP).filter((n) => n.endsWith(".bend") && path.join(TOP, n) !== entry)) {
    const proofs = new Set([...fs.readFileSync(path.join(TOP, name), "utf8").matchAll(/^def\s+([A-Za-z_][\w.]*)\.proof\(/gm)]
      .map((m) => m[1]).filter((n) => entryNames.has(n)));
    if (proofs.size > 0) autoImports.push({ file: path.join(TOP, name), alias: "Gen2" + path.basename(name, ".bend").replace(/(^|_)([a-z])/g, (_, __, c) => c.toUpperCase()), ns: path.basename(name, ".bend"), proofs });
  }
}
const book = B.book_nil();
const seen = new Map<string, string | null>();
for (const imp of autoImports) await B.book_load(book, imp.file, imp.ns, seen, undefined, TOP);
const N0 = await B.book_load(book, entry, "", seen, undefined, TOP); // the entry's first entry in book order
const tLoad = performance.now();
try {
  B.book_valid(book, autoImports.length ? N0 : 0);
} catch (e: any) {
  console.error(e?.$ === "Err" ? B.err_show(e) : e);
  process.exit(1);
}
const tValid = performance.now();
const RAW: Record<string, B.TLD> = book.tlds;
book.tlds = new Proxy(RAW, {
  get(t, k, r) {
    if (--fuel < 0) throw OOF;
    if ((++ticks & 4095) === 0 && performance.now() > deadline) throw TIMEOUT;
    return Reflect.get(t, k, r);
  },
});
const ORDER = new Map<string, number>();
book.order.forEach((k, i) => ORDER.set(k, i));

// ---- source text of defs ----
type Src = { file: string; header: string; body: string; bodyLine: number };
const texts = new Map<string, string>();
const fileText = (f: string) => { let t = texts.get(f); if (t === undefined) { t = fs.readFileSync(f, "utf8"); texts.set(f, t); } return t; };
const fileLines = new Map<string, string[]>();
const defLines = new Map<string, Map<string, number>>();
const linesOf = (file: string) => {
  let lines = fileLines.get(file);
  if (!lines) { lines = fileText(file).split("\n"); fileLines.set(file, lines); }
  return lines;
};
const defLine = (file: string, name: string) => {
  let defs = defLines.get(file);
  if (!defs) {
    defs = new Map();
    linesOf(file).forEach((line, i) => {
      const m = /^(?:@unsafe\s+)?def\s+([A-Za-z0-9_.]+)\??\(/.exec(line);
      if (!m) return;
      if (!defs!.has(m[1])) defs!.set(m[1], i);
      const suffix = m[1].slice(m[1].indexOf(".") + 1);
      if (!defs!.has(suffix)) defs!.set(suffix, i);
    });
    defLines.set(file, defs);
  }
  return defs.get(name) ?? -1;
};
const nsOf = (k: string) => (k.includes(":") ? k.slice(0, k.indexOf(":")) : "");
const shortOf = (k: string) => (k.includes(":") ? k.slice(k.indexOf(":") + 1) : k);
const pathOf = (k: string) => {
  if ((ORDER.get(k) ?? -1) >= N0) return entry;
  return nsOf(k) === "" ? entry : path.resolve(TOP, nsOf(k) + ".bend");
};
const srcCache = new Map<string, Src | null>();
const defSrc = (k: string): Src | null => {
  if (srcCache.has(k)) return srcCache.get(k)!;
  let res: Src | null = null;
  const file = pathOf(k);
  if (fs.existsSync(file)) {
    const lines = linesOf(file);
    const li = defLine(file, shortOf(k));
    if (li >= 0) {
      let depth = 0, he = li;
      for (; he < lines.length; he++) {
        const l = lines[he].replace(/#.*$/, "");
        for (const ch of l) { if ("([{".includes(ch)) depth++; else if (")]}".includes(ch)) depth--; }
        if (depth <= 0 && /:\s*$/.test(l)) break;
      }
      let be = he + 1;
      while (be < lines.length && (lines[be].startsWith(" ") || lines[be].trim() === "")) be++;
      while (be > he + 1 && (lines[be - 1].trim() === "" || lines[be - 1].trim().startsWith("#"))) be--;
      res = { file, header: lines.slice(li, he + 1).join("\n"), body: lines.slice(he + 1, be).join("\n"), bodyLine: he + 1 };
    }
  }
  srcCache.set(k, res);
  return res;
};

const spanFile = (t: any, n = 0): B.File | undefined => {
  if (!t || n > 50) return undefined;
  if (t.s?.file) return t.s.file;
  if (t.$ === "All") return spanFile(t.A, n + 1) ?? spanFile(t.B(B.Var("_", 0)), n + 1);
  return undefined;
};
const sourceFiles = new Map<string, B.File>();
for (const k of book.order) {
  const t = RAW[k];
  if (t?.$ === "Def") {
    const f = spanFile(t.v) ?? spanFile(t.T);
    if (f) sourceFiles.set(k, f);
  }
}
for (const k of book.order.slice(N0)) {
  const file = sourceFiles.get(k);
  if (file) for (const imp of autoImports) file.al[imp.alias] = imp.ns;
}
const openBySource = new Map<string, Set<string>>();
const isOpen = (k: string) => {
  const source = sourceFiles.get(k)?.str;
  if (!source) return false;
  let names = openBySource.get(source);
  if (!names) {
    names = new Set();
    let current = "";
    for (const line of source.split("\n")) {
      const def = /^(?:@unsafe\s+)?def\s+([A-Za-z0-9_.]+)\??\(/.exec(line);
      if (def) current = def[1];
      else if (current && line.includes("?TODO") && !line.trimStart().startsWith("#")) {
        names.add(current);
        names.add(current.slice(current.indexOf(".") + 1));
      }
    }
    openBySource.set(source, names);
  }
  return names.has(shortOf(k));
};

// checks <def> with the body text <body> (a def body, indented); throws bend2's Err on failure
const checkDef = (k: string, body: string) => {
  const ds = defSrc(k)!;
  const def = RAW[k] as B.Def;
  const file = sourceFiles.get(k)!;
  const str = ds.header + "\n" + body + "\n";
  const p: B.Parse = { book, dir: path.dirname(ds.file) + "/", str, pos: str.indexOf("(") + 1, stk: [], frs: 0, ns: file.ns, al: file.al };
  const hols = book.hols;
  const tele = B.parse_tele(p, ")");
  p.pos = ds.header.length;
  const vars = tele.map((c): B.PVar => ({ $: "PVar", k: c[1], i: c[2], q: B.Lone(), s: c[4] }));
  const v = B.term_higher(B.term_lower(B.term_higher(B.body_flatten(B.parse_body(p), vars, () => p.frs++))));
  B.parse_skip(p);
  book.hols = hols;
  if (p.pos < str.length) B.parse_fail(p, "the end of the body");
  B.def_check(book, k, { ...def, v });
};

// ---- terms ----
const lit = (k: "Nat" | "U32", v: number): LTerm => B.Lit(k, v);
const canon = (t: LTerm): LTerm => {
  switch (t.$) {
    case "Ctr": {
      const x = t.x.map(canon);
      if (t.k === "Zero" && x.length === 0) return lit("Nat", 0);
      if (t.k === "Succ" && x.length === 1 && x[0].$ === "Lit" && x[0].k === "Nat") return lit("Nat", (x[0].v as number) + 1);
      const c = B.Ctr<[LTerm]>(t.k, x);
      if (t.k === "U32") { const u = B.u32_from_term(c); if (u !== null) return lit("U32", u); }
      return c;
    }
    case "App": return B.App(canon(t.f), canon(t.x));
    case "Eql": return B.Eql(canon(t.a), canon(t.b), canon(t.T));
    case "ADT": return B.ADT(t.k, t.x.map(canon), undefined, t.r);
    case "All": return B.All<LTerm>(t.q, t.k, t.i, canon(t.A), canon(t.B as LTerm));
    case "Lam": return B.Lam<LTerm>(t.k, t.i, canon(t.f as LTerm), undefined, t.q);
    case "Ann": return canon(t.x);
    case "Var": return t.v !== undefined && t.i >= 0 ? B.Var(t.k, t.i) : t;
    case "Ref": { const a = RAW[t.k]; return a?.$ === "ADT" && a.n === 0 ? B.ADT(t.k, [], undefined, []) : t; } // U32 is <U32> once whnf'd
    default: return t;
  }
};
const lower = (h: HTerm, d: number): LTerm => canon(B.term_lower(h, d));

const key = (t: LTerm): string => {
  switch (t.$) {
    case "Var": return "$" + t.i;
    case "Ref": return "@" + t.k;
    case "App": return "(" + key(t.f) + " " + key(t.x) + ")";
    case "Ctr": return t.k + "{" + t.x.map(key).join(",") + "}";
    case "Lit": return "#" + t.k + String(t.v);
    case "Eql": return "{" + key(t.a) + "==" + key(t.b) + ":" + key(t.T) + "}";
    case "ADT": return "<" + t.k + " " + t.x.map(key).join(",") + "-" + t.r.join(",") + ">";
    case "All": return "A" + t.q.$[0] + t.i + "(" + key(t.A) + ")" + key(t.B as LTerm);
    case "Lam": return "L" + t.i + key(t.f as LTerm);
    default: return B.term_key(t);
  }
};
// node count, stopping past cap (iterative: a deep term cannot overflow the stack)
const size = (t0: LTerm, cap = 100000): number => {
  const st: LTerm[] = [t0];
  let n = 0;
  while (st.length && n <= cap) {
    const t = st.pop()!;
    n++;
    switch (t.$) {
      case "App": st.push(t.f, t.x); break;
      case "Ctr": case "ADT": st.push(...t.x); break;
      case "Eql": st.push(t.a, t.b); break;
      case "All": st.push(t.A, t.B as LTerm); break;
      case "Lam": st.push(t.f as LTerm); break;
    }
  }
  return n;
};
const unapply = (t: LTerm): [LTerm, LTerm[]] => B.term_unapply(t);
const hasMeta = (t: LTerm): boolean => {
  switch (t.$) {
    case "Var": return t.i >= META;
    case "App": return hasMeta(t.f) || hasMeta(t.x);
    case "Ctr": case "ADT": return t.x.some(hasMeta);
    case "Eql": return hasMeta(t.a) || hasMeta(t.b) || hasMeta(t.T);
    case "All": return hasMeta(t.A) || hasMeta(t.B as LTerm);
    case "Lam": return hasMeta(t.f as LTerm);
    default: return false;
  }
};
const closedBelow = (t: LTerm, d: number): boolean => {
  switch (t.$) {
    case "Var": return t.i < d;
    case "App": return closedBelow(t.f, d) && closedBelow(t.x, d);
    case "Ctr": case "ADT": return t.x.every((x) => closedBelow(x, d));
    case "Eql": return closedBelow(t.a, d) && closedBelow(t.b, d) && closedBelow(t.T, d);
    case "All": case "Lam": return false;
    default: return true;
  }
};
const replace = (t: LTerm, k: string, by: LTerm): LTerm => {
  if (key(t) === k) return by;
  switch (t.$) {
    case "App": return B.App(replace(t.f, k, by), replace(t.x, k, by));
    case "Ctr": return B.Ctr<[LTerm]>(t.k, t.x.map((x) => replace(x, k, by)));
    case "Eql": return B.Eql(replace(t.a, k, by), replace(t.b, k, by), t.T);
    case "ADT": return B.ADT(t.k, t.x.map((x) => replace(x, k, by)), undefined, t.r);
    default: return t;
  }
};
const subterms = (t: LTerm, out: Map<string, LTerm>) => {
  out.set(key(t), t);
  switch (t.$) {
    case "App": { const [h, xs] = unapply(t); if (h.$ !== "Ref") subterms(t.f, out); xs.forEach((x) => subterms(x, out)); break; }
    case "Ctr": case "ADT": t.x.forEach((x) => subterms(x, out)); break;
    case "Eql": subterms(t.a, out); subterms(t.b, out); break;
  }
};
const litStep = (t: LTerm): LTerm | null => (t.$ === "Lit" && (t.k === "Nat" || t.k === "U32") ? canonShallow(B.lit_step(t)) : null);
const canonShallow = (t: LTerm): LTerm => t;

const match = (p: LTerm, t: LTerm, sol: (LTerm | null)[], d: number): boolean => {
  if (p.$ === "Var" && p.i >= META) {
    const s = sol[p.i - META];
    if (s) return key(s) === key(t);
    if (!closedBelow(t, d)) return false;
    sol[p.i - META] = t;
    return true;
  }
  switch (p.$) {
    case "Var": return t.$ === "Var" && t.i === p.i;
    case "Ref": return t.$ === "Ref" && t.k === p.k;
    case "App": return t.$ === "App" && match(p.f, t.f, sol, d) && match(p.x, t.x, sol, d);
    case "Ctr": {
      if (t.$ === "Lit") { const s = litStep(t); if (!s) return false; t = s; }
      return t.$ === "Ctr" && t.k === p.k && t.x.length === p.x.length && p.x.every((x, i) => match(x, (t as any).x[i], sol, d));
    }
    case "Lit": {
      if (t.$ === "Lit") return t.k === p.k && t.v === p.v;
      if (t.$ === "Ctr") { const s = litStep(p); return s !== null && match(s, t, sol, d); }
      return false;
    }
    case "Eql": {
      if (t.$ !== "Eql" || !match(p.a, t.a, sol, d) || !match(p.b, t.b, sol, d)) return false;
      const s2 = sol.slice();
      if (match(p.T, t.T, s2, d)) for (let i = 0; i < sol.length; i++) sol[i] = s2[i];
      return true;
    }
    case "ADT": return t.$ === "ADT" && t.k === p.k && t.x.length === p.x.length && t.r.join() === p.r.join() && p.x.every((x, i) => match(x, (t as any).x[i], sol, d));
    case "All": return t.$ === "All" && t.q.$ === p.q.$ && match(p.A, t.A, sol, d) && match(p.B as LTerm, t.B as LTerm, sol, d);
    case "Lam": return t.$ === "Lam" && match(p.f as LTerm, t.f as LTerm, sol, d);
    case "Typ": return t.$ === "Typ" && match(p.g, t.g, sol, d);
    default: return key(p) === key(t);
  }
};

// ---- normal form ----
const wnf = (h: HTerm): HTerm | undefined => attempt(FUEL_NF, () => B.term_wnf(book, h));
const nfGo = (h: HTerm, d: number, b: { n: number }): LTerm => {
  b.n--;
  const w = wnf(h) ?? B.term_strip(h);
  switch (w.$) {
    case "App": {
      const [hd, xs] = B.term_unapply(w);
      const f = B.term_strip(hd);
      if (f.$ === "Ref") return xs.reduce<LTerm>((r, x) => B.App(r, nfArg(x, d, b)), B.Ref(f.k));
      return B.term_lower(w, d);
    }
    case "Ctr": return B.Ctr<[LTerm]>(w.k, w.x.map((x) => nfArg(x, d, b)));
    case "Eql": return B.Eql(nfArg(w.a, d, b), nfArg(w.b, d, b), B.term_lower(w.T, d));
    default: return B.term_lower(w, d);
  }
};
const nfArg = (x: HTerm, d: number, b: { n: number }): LTerm => {
  if (b.n <= 0) return B.term_lower(x, d);
  const s = B.term_strip(x);
  if (s.$ === "Ref") {
    const t = RAW[s.k];
    if (t?.$ === "Def" && t.n === 0 && t.v !== null) {
      const lb = { n: 24 };
      const r = nfGo(s, d, lb);
      return lb.n <= 0 ? B.Ref(s.k) : r;
    }
  }
  return nfGo(x, d, b);
};
const nf = (h: HTerm, d: number): LTerm => canon(nfGo(h, d, { n: NF_NODES }));

const headKey = (t: LTerm): string => {
  switch (t.$) {
    case "App": { const [h] = unapply(t); return h.$ === "Ref" ? "R:" + h.k : h.$ === "Var" && h.i >= META ? "*" : "V"; }
    case "Ref": return "R:" + t.k;
    case "Ctr": return "C:" + t.k;
    case "Lit": return t.k === "Nat" ? (t.v === 0 ? "C:Zero" : "C:Succ") : "C:" + t.k;
    case "Var": return t.i >= META ? "*" : "V";
    case "ADT": return "A:" + t.k;
    case "Eql": return "E|" + headKey(t.a);
    case "All": return "P";
    default: return t.$;
  }
};

// strict parameter of a def: the one its body matches first
const strictMemo = new Map<string, number | null>();
const strictOf = (k: string): number | null => {
  if (strictMemo.has(k)) return strictMemo.get(k)!;
  let r: number | null = null;
  const t0 = RAW[k];
  if (t0?.$ === "Def" && t0.v !== null) {
    let t: HTerm = t0.v, j = 0;
    for (; j <= t0.n; j++) {
      t = B.term_strip(t);
      if (t.$ === "Lam") { t = t.f(B.Var("_", 1e7 + j)); continue; }
      if ((t.$ === "Mat" || t.$ === "Efq") && j < t0.n) r = j;
      break;
    }
  }
  strictMemo.set(k, r);
  return r;
};
// the parameters that a def's case tree matches (at any depth)
const matchedMemo = new Map<string, Set<number>>();
const matchedOf = (k: string): Set<number> => {
  let r = matchedMemo.get(k);
  if (r) return r;
  r = new Set();
  const t0 = RAW[k];
  if (t0?.$ === "Def" && t0.v !== null) {
    let budget = 400;
    const walk = (t: HTerm, q: number[]) => {
      if (--budget < 0) return;
      t = B.term_strip(t);
      if (t.$ === "Lam") { walk(t.f(B.Var("_", 1e7)), q.slice(1)); return; }
      if (t.$ === "Mat") {
        const b = q[0];
        if (b !== undefined && b >= 0) r!.add(b);
        const ctr = RAW[t.k] === undefined ? (book.ctrs as any)[t.k] : null;
        const nf = ctr ? ctr.n : 0;
        walk(t.h, [...new Array(nf).fill(-1), ...q.slice(1)]);
        walk(t.m, q);
      }
    };
    walk(t0.v, Array.from({ length: t0.n }, (_, i) => i));
  }
  matchedMemo.set(k, r);
  return r;
};
// subterms that block evaluation: the strict argument of a stuck call, when a variable or a stuck call
const blockers = (t: LTerm, out: LTerm[]) => {
  switch (t.$) {
    case "App": {
      const [h, xs] = unapply(t);
      if (h.$ === "Ref") {
        const j = strictOf(h.k);
        const blk = (a: LTerm) => a.$ === "Var" || (a.$ === "App" && unapply(a)[0].$ === "Ref");
        if (j !== null && j < xs.length && blk(xs[j])) out.push(xs[j]);
        // the strict argument is a constructor (a nested match reads another one): the other matched ones
        else { const ms = matchedOf(h.k); xs.forEach((a, i) => { if (ms.has(i) && blk(a)) out.push(a); }); }
      }
      xs.forEach((x) => blockers(x, out));
      break;
    }
    case "Ctr": case "ADT": t.x.forEach((x) => blockers(x, out)); break;
    case "Eql": blockers(t.a, out); blockers(t.b, out); break;
  }
};

// ---- lemma index ----
type Lemma = { k: string; order: number; n: number };
const applyIndex = new Map<string, Lemma[]>();
const rwIndex = new Map<string, { L: Lemma; side: 0 | 1 }[]>();
const wild: Lemma[] = [];
const isProp = (h: HTerm, n = 0): boolean => {
  const w = wnf(h);
  if (!w) return true;
  switch (w.$) {
    case "Eql": return true;
    case "ADT": { const t = RAW[w.k]; return t?.$ === "ADT" && (t.c.length === 0 || (t.c.length === 1 && t.c[0].n === 0)); }
    case "Typ": case "Qnt": case "Qua": return false;
    case "All": return n < 20 ? isProp(w.B(B.Var("_", 1e7 + n)), n + 1) : true;
    case "Var": return false;
    case "Ref": return false;
    default: return true;
  }
};
const openMeta = (T: HTerm, n: number, sol: (HTerm | null)[] = []): { doms: { q: B.Quant; k: string; A: HTerm }[]; concl: HTerm } | null => {
  let t = T;
  const doms: { q: B.Quant; k: string; A: HTerm }[] = [];
  for (let j = 0; j < n; j++) {
    let s = B.term_strip(t);
    if (s.$ !== "All") { const w = wnf(t); if (!w || w.$ !== "All") return null; s = w; }
    doms.push({ q: s.q, k: s.k, A: s.A });
    t = s.B(sol[j] ?? B.Var("?" + j, META + j));
  }
  return { doms, concl: t };
};
const preds = new Map<string, Lemma[]>();
let tIndex = 0;
const buildIndex = () => {
const tIndex0 = performance.now();
applyIndex.clear(); rwIndex.clear(); wild.length = 0; preds.clear();
for (const k of Object.keys(RAW)) {
  const t = RAW[k];
  if (t.$ !== "Def" || (t.v === null && t.b !== true) || t.x > 0 || t.i || isOpen(k)) continue;
  const L: Lemma = { k, order: ORDER.get(k) ?? -1, n: t.n };
  const o = attempt(20000, () => openMeta(t.T, t.n));
  if (!o) continue;
  const c = attempt(20000, () => lower(o.concl, 0));
  if (!c) continue;
  const hk = headKey(c);
  if (hk === "*") { if (t.n <= 4) wild.push(L); continue; }
  if (hk === "V" || hk === "Typ") continue;
  if (!applyIndex.has(hk)) applyIndex.set(hk, []);
  applyIndex.get(hk)!.push(L);
  // also by the head of the conclusion's normal form (Le(a, b) is T(..) once unfolded)
  if (t.n > 0) {
    const cn = attempt(20000, () => nf(o.concl, 0));
    const nk = cn ? headKey(cn) : "*";
    if (nk !== hk && nk !== "*" && nk !== "V" && nk !== "E|*" && nk !== "E|V") {
      if (!applyIndex.has(nk)) applyIndex.set(nk, []);
      applyIndex.get(nk)!.push(L);
    }
  }
  if (c.$ === "Eql") {
    for (const side of [0, 1] as const) {
      const s = side === 0 ? c.a : c.b;
      const sk = headKey(s);
      if (!sk.startsWith("R:") && !(t.n === 0 && (sk.startsWith("C:") || sk.startsWith("A:")))) continue;
      if (!rwIndex.has(sk)) rwIndex.set(sk, []);
      rwIndex.get(sk)!.push({ L, side });
    }
  }
}
// predicates on one datatype (P: T -> Type), to discriminate two constructors (`%e : P(_); Unit{}`)
for (const k of Object.keys(RAW)) {
  const t = RAW[k];
  if (t.$ !== "Def" || t.v === null || t.n !== 1 || t.x > 0 || isOpen(k)) continue;
  const s0 = B.term_strip(t.T);
  if (s0.$ !== "All") continue;
  const r = attempt(20000, () => wnf(s0.B(B.Var("_", 0))));
  if (!r || r.$ !== "Typ") continue;
  const pk = attempt(20000, () => key(lower(s0.A, 0)));
  if (!pk) continue;
  if (!preds.has(pk)) preds.set(pk, []);
  preds.get(pk)!.push({ k, order: ORDER.get(k) ?? -1, n: 1 });
}
for (const v of preds.values()) v.sort((a, b) => b.order - a.order);
for (const m of [applyIndex]) for (const v of m.values()) v.sort((a, b) => b.order - a.order);
for (const v of rwIndex.values()) v.sort((a, b) => b.L.order - a.L.order);
wild.sort((a, b) => b.order - a.order);
tIndex = performance.now() - tIndex0;
};
buildIndex();

// ---- proofs ----
type Pf =
  | { t: "tm"; s: string }
  | { t: "rw"; e: string; P: string; k: Pf }
  | { t: "mt"; x: string; arms: { pat: string; k: Pf }[] }
  | { t: "hole"; g: Goal }
  | { t: "app"; s: string; subs: Pf[] }; // a call whose open premises are subs (marked HOLE in s)
const HOLE = "\u0000";
const inline = (p: Pf): string => {
  switch (p.t) {
    case "tm": return p.s;
    case "app": { let i = 0; return p.s.replace(/\u0000/g, () => inline(p.subs[i++])); }
    case "rw": return "(%" + p.e + " : " + p.P + "; " + inline(p.k) + ")";
    case "hole": return "?TODO";
    case "mt": throw new Error("a match cannot be inlined");
  }
};
const flat = (p: Pf): string => (p.t === "rw" ? "%" + p.e + " : " + p.P + "; " + flat(p.k) : inline(p));
const render = (p: Pf, ind: string, out: string[]) => {
  switch (p.t) {
    case "tm": out.push(ind + p.s); break;
    case "app": out.push(ind + inline(p)); break;
    case "hole": out.push(ind + "?TODO"); break;
    case "rw": out.push(ind + "%" + p.e + " :"); out.push(ind + "  " + p.P); render(p.k, ind, out); break;
    case "mt":
      out.push(ind + "match " + p.x + ":");
      for (const a of p.arms) { out.push(ind + "  case " + a.pat + ":"); render(a.k, ind + "    ", out); }
      break;
  }
};
const holesOf = (p: Pf, out: Goal[] = []): Goal[] => {
  if (p.t === "hole") out.push(p.g);
  else if (p.t === "rw") holesOf(p.k, out);
  else if (p.t === "mt") p.arms.forEach((a) => holesOf(a.k, out));
  else if (p.t === "app") p.subs.forEach((a) => holesOf(a, out));
  return out;
};

// ---- goals ----
type Goal = {
  ctx: B.Ctx; d: number; ty: HTerm; lhs: B.LHS; qt: B.Quant; env: B.Env;
  names: string[]; ckey: string;
  pend: number; pnames: string[]; pmany: boolean[];
  split: boolean; path: string; lvl: number;
  hc: Map<number, LTerm[]>;
};
type Job = { k: string; def: B.Def; order: number; file: B.File; short: string; tags: Map<string, number>; memo: Map<string, { pf: Pf | null; depth: number; rw: number }>; smemo: Map<string, Res>; closed: number; ih: boolean };
let job: Job;
type Res = { pf: Pf; holes: number; closed: number };
const tag = (t: string) => job.tags.set(t, (job.tags.get(t) ?? 0) + 1);
const tm = (s: string): Pf => ({ t: "tm", s });

const show = (t: LTerm, names: string[]): string => B.term_show(t, -1, names.slice(), job.file);
const ann = (g: Goal, i: number) => B.pmap_get(g.ctx, i);
const goalKey = (g: Goal) => g.ckey + "|-" + g.qt.$[0] + key(lower(g.ty, g.d));

const parseFrag = (text: string, g: Goal): HTerm => {
  const p: B.Parse = { book, dir: "", str: text, pos: 0, stk: g.names.map((k, i) => [k, i] as [string, number]), frs: g.d, ns: job.file.ns, al: job.file.al };
  const hols = book.hols;
  const lt = B.parse_block(p);
  book.hols = hols;
  B.parse_skip(p);
  if (p.pos < text.length) B.parse_fail(p, "the end of the fragment");
  return B.term_higher(lt, g.env);
};
// does text check at g (bend2's term_check, plus the linearity of g's live binders)?
const tryText = (g: Goal, text: string): boolean =>
  attempt(FUEL_CHECK, () => {
    const c = B.term_check(book, g.lhs, parseFrag(text, g), g.qt, g.ty, g.ctx, g.d);
    if (g.qt.$ !== "None") {
      for (const [i, a] of B.pmap_to_array(g.ctx)) if (a.q.$ === "Lone" && B.pmap_get(c.us, i)?.$ === "Many") throw LIN;
    }
    return true;
  }) === true;

const intro = (g: Goal, name: string, many: boolean): Goal | null => {
  let t: HTerm | undefined = B.term_strip(g.ty);
  if (t.$ !== "All") t = wnf(g.ty);
  if (!t || t.$ !== "All") return null;
  const x: HTerm = B.Var(name, g.d);
  const lhs = g.lhs.n > 0 ? { ...g.lhs, t: B.term_apply(g.lhs.t, x), n: g.lhs.n - 1 } : g.lhs;
  let q = t.q;
  if (many && q.$ === "Lone") q = B.Many();
  const A = t.A;
  const Ak = attempt(FUEL_NF, () => key(lower(A, g.d))) ?? "?";
  return {
    ...g, ctx: B.ctx_bind(g.ctx, g.d, q, name, A), d: g.d + 1, ty: t.B(x), lhs, env: B.list_set(g.env, g.d, x),
    names: [...g.names, name], ckey: g.ckey + "|" + q.$[0] + name + ":" + Ak,
    pend: Math.max(0, g.pend - 1), pnames: g.pnames.slice(1), pmany: g.pmany.slice(1), hc: new Map(),
  };
};
const introAll = (g: Goal): Goal | null => {
  let c: Goal | null = g;
  while (c && c.pend > 0) c = intro(c, c.pnames[0], c.pmany[0]);
  return c;
};

const reserved = (nm: string) => {
  const q = job.file.ns === "" ? nm : job.file.ns + ":" + nm;
  return q in RAW || nm in RAW || nm === "_" || /^(def|type|law|match|case|do|return|for|exs|where|is|import|Type|Data|Kind|Quant)$/.test(nm);
};
const fresh = (base: string, used: Set<string>): string => {
  const b = base.replace(/[^A-Za-z0-9_]/g, "") || "x";
  for (let i = 0; ; i++) {
    const nm = i === 0 ? b : b + String(i);
    if (!used.has(nm) && !reserved(nm)) { used.add(nm); return nm; }
  }
};

// hypothesis types (raw and normal form), cached per goal context
const hypTargets = (g: Goal, i: number): LTerm[] => {
  let r = g.hc.get(i);
  if (!r) {
    const a = ann(g, i)!;
    const raw = lower(a.T, g.d);
    const n = attempt(FUEL_NF * 2, () => nf(a.T, g.d));
    r = n && key(n) !== key(raw) ? [raw, n] : [raw];
    g.hc.set(i, r);
  }
  return r;
};
const usable = (g: Goal, i: number, qt: B.Quant) => {
  const a = ann(g, i);
  return !!a && g.names[i] !== "_" && (qt.$ === "None" || a.q.$ !== "None");
};

// ---- leaf tactics ----
type Callee = { text: string; T: HTerm; n: number; kind: string };

// apply a callee whose conclusion matches one of targets; premises proven at depth - 1
type Applied = { args: string[]; doms: any[]; sol: (LTerm | null)[]; holes?: Goal[] };
const applyCallee = (g: Goal, c: Callee, targets: LTerm[], depth: number, rw: number, path: Set<string>, concl: ((o: LTerm) => LTerm | null) | null, accept: (a: Applied) => boolean, cnt?: { n: number; probe?: boolean; spec?: number }, holesOk = false): Applied | null => {
  const toH = (s: (LTerm | null)[]) => s.map((x) => (x ? B.term_higher(x, g.env) : null));
  const o = openMeta(c.T, c.n);
  if (!o) return null;
  const pc0 = attempt(FUEL_NF, () => lower(o.concl, g.d));
  if (!pc0) return null;
  const pc = concl ? concl(pc0) : pc0;
  if (!pc) return null;
  // the distinct solutions of the conclusion against the goal: raw pattern against each target, then
  // the normal form of the conclusion (metavariables stay stuck) against the normal form of the goal
  const sols: (LTerm | null)[][] = [];
  const seen = new Set<string>();
  const push = (p: LTerm, t: LTerm) => {
    const s2: (LTerm | null)[] = new Array(c.n).fill(null);
    if (!match(p, t, s2, g.d)) return;
    const k = s2.map((x) => (x ? key(x) : "_")).join(";");
    if (!seen.has(k)) { seen.add(k); sols.push(s2); }
  };
  for (const t of targets) push(pc, t);
  if (!concl && targets.length > 0) {
    const pn = nfPattern(c, o.concl, g.d);
    if (pn && key(pn) !== key(pc)) push(pn, targets[targets.length - 1]);
  }
  if (cnt && cnt.probe) { cnt.spec = sols.length ? specOf(pc) : -1; return null; }
  for (const s0 of sols) {
    if (cnt) cnt.n++;
    const r = complete(g, c, s0, toH, depth, rw, path, holesOk, concl !== null);
    if (r && accept(r)) return r;
  }
  return null;
};
// specificity of a pattern: its nodes that are not metavariables
const specOf = (t: LTerm): number => size(t) - metas(t);
const metas = (t: LTerm): number => {
  switch (t.$) {
    case "Var": return t.i >= META ? 1 : 0;
    case "App": return metas(t.f) + metas(t.x);
    case "Ctr": case "ADT": return t.x.reduce((a, x) => a + metas(x), 0);
    case "Eql": return metas(t.a) + metas(t.b);
    default: return 0;
  }
};
const complete = (g: Goal, c: Callee, s0: (LTerm | null)[], toH: (s: (LTerm | null)[]) => (HTerm | null)[], depth: number, rw: number, path: Set<string>, holesOk = false, refl = false): Applied | null => {
  let sol = s0.slice();
  let o2 = openMeta(c.T, c.n, toH(sol));
  if (!o2) return null;
  const prem: boolean[] = o2.doms.map((dm, j) => !sol[j] && isProp(dm.A));
  const viaHyp: (string | null)[] = new Array(c.n).fill(null);
  // parameters not fixed by the conclusion: from premises that match hypotheses (raw, then normal forms)
  for (let iter = 0; iter < 3 && sol.some((s, j) => !s && !prem[j]); iter++) {
    let progress = false;
    for (let j = 0; j < c.n; j++) {
      if (!prem[j] || viaHyp[j]) continue;
      const Araw = attempt(FUEL_NF, () => lower(o2!.doms[j].A, g.d));
      if (!Araw || !hasMeta(Araw)) continue;
      const An = attempt(FUEL_NF, () => nf(o2!.doms[j].A, g.d));
      const pats = An && key(An) !== key(Araw) ? [Araw, An] : [Araw];
      const qt = B.quant_dem(o2.doms[j].q, g.qt);
      for (let i = g.d - 1; i >= 0 && !viaHyp[j]; i--) {
        if (!usable(g, i, qt)) continue;
        const hts = hypTargets(g, i);
        for (let pi = 0; pi < pats.length && !viaHyp[j]; pi++) {
          const ht = pi === 0 ? hts : [hts[hts.length - 1]];
          for (const t of ht) {
            const s2 = sol.slice();
            if (match(pats[pi], t, s2, g.d)) { sol = s2; viaHyp[j] = g.names[i]; progress = true; break; }
          }
        }
      }
    }
    if (!progress) break;
    o2 = openMeta(c.T, c.n, toH(sol));
    if (!o2) return null;
  }
  // (rewrites only) still open: a premise {a == x} or {x == a} whose x is an open parameter fixes x := a (the premise
  // then holds by {==}: L.len(t, p, v, List.length(t), {==}))
  if (refl && sol.some((s, j) => !s && !prem[j])) {
    for (let j = 0; j < c.n; j++) {
      if (!prem[j] || viaHyp[j]) continue;
      const A = attempt(FUEL_NF, () => lower(o2!.doms[j].A, g.d));
      if (!A || A.$ !== "Eql") continue;
      const isOpen = (t: LTerm) => t.$ === "Var" && t.i >= META && !sol[t.i - META] && !prem[t.i - META];
      const [x, a] = isOpen(A.b) && !hasMeta(A.a) ? [A.b, A.a] : isOpen(A.a) && !hasMeta(A.b) ? [A.a, A.b] : [null, null];
      if (!x || !a || !closedBelow(a, g.d)) continue;
      sol[(x as any).i - META] = a;
      const o3 = openMeta(c.T, c.n, toH(sol));
      if (!o3) return null;
      o2 = o3;
    }
  }
  if (sol.some((s, j) => !s && !prem[j])) {
    // still open: unify a premise with an indexed lemma's conclusion (le_trans's middle term from
    // the lemma that proves its first premise); at most 3 alternatives, each one completed
    // only at the top of a leaf (premise level 0) with depth for the premises: it is costly
    if (depth < 2 || g.lvl > 0) return null;
    for (const alt of forwardBinds(g, c, sol, prem, viaHyp, o2).slice(0, 2)) {
      const s2 = sol.slice();
      for (const [j, t] of alt) s2[j] = t;
      if (s2.some((x, j) => !x && !prem[j])) continue;
      const o3 = openMeta(c.T, c.n, toH(s2));
      if (!o3) continue;
      const r = finish(g, c, s2, viaHyp, o3, depth, rw, path, holesOk);
      if (r) { tag("forward"); return r; }
    }
    return null;
  }
  return finish(g, c, sol, viaHyp, o2, depth, rw, path, holesOk);
};
const finish = (g: Goal, c: Callee, sol: (LTerm | null)[], viaHyp: (string | null)[], o2: { doms: { q: B.Quant; k: string; A: HTerm }[] }, depth: number, rw: number, path: Set<string>, holesOk: boolean): Applied | null => {
  const args: string[] = [];
  const holes: Goal[] = [];
  for (let j = 0; j < c.n; j++) {
    if (sol[j]) { args.push(show(sol[j]!, g.names)); continue; }
    if (viaHyp[j]) { args.push(viaHyp[j]!); continue; }
    const sg: Goal = { ...g, ty: o2.doms[j].A, qt: B.quant_dem(o2.doms[j].q, g.qt), lvl: g.lvl + 1, path: g.path + "#" + c.text + "." + j };
    const pf = leaf(sg, Math.max(0, depth - 1), rw, path);
    if (!pf && !holesOk) return null;
    if (!pf) { holes.push(sg); args.push(HOLE); continue; }
    args.push(inline(pf));
  }
  return { args, doms: o2.doms, sol, holes };
};
// two-sided first-order unification; metavariables >= META on both sides (the callee's below META2)
const META2 = 2 * META;
const shiftMetas = (t: LTerm): LTerm => {
  switch (t.$) {
    case "Var": return t.i >= META ? B.Var(t.k, t.i + META) : t;
    case "App": return B.App(shiftMetas(t.f), shiftMetas(t.x));
    case "Ctr": return B.Ctr<[LTerm]>(t.k, t.x.map(shiftMetas));
    case "Eql": return B.Eql(shiftMetas(t.a), shiftMetas(t.b), shiftMetas(t.T));
    case "ADT": return B.ADT(t.k, t.x.map(shiftMetas), undefined, t.r);
    default: return t;
  }
};
const deref = (t: LTerm, s: Map<number, LTerm>): LTerm => { while (t.$ === "Var" && t.i >= META && s.has(t.i)) t = s.get(t.i)!; return t; };
const resolve = (t: LTerm, s: Map<number, LTerm>, n = 0): LTerm => {
  t = deref(t, s);
  if (n > 200) return t;
  switch (t.$) {
    case "App": return B.App(resolve(t.f, s, n + 1), resolve(t.x, s, n + 1));
    case "Ctr": return B.Ctr<[LTerm]>(t.k, t.x.map((x) => resolve(x, s, n + 1)));
    case "Eql": return B.Eql(resolve(t.a, s, n + 1), resolve(t.b, s, n + 1), resolve(t.T, s, n + 1));
    case "ADT": return B.ADT(t.k, t.x.map((x) => resolve(x, s, n + 1)), undefined, t.r);
    default: return t;
  }
};
const occurs = (i: number, t: LTerm, s: Map<number, LTerm>): boolean => {
  t = deref(t, s);
  switch (t.$) {
    case "Var": return t.i === i;
    case "App": return occurs(i, t.f, s) || occurs(i, t.x, s);
    case "Ctr": case "ADT": return t.x.some((x) => occurs(i, x, s));
    case "Eql": return occurs(i, t.a, s) || occurs(i, t.b, s);
    default: return false;
  }
};
const unify = (a: LTerm, b: LTerm, s: Map<number, LTerm>, d: number): boolean => {
  a = deref(a, s); b = deref(b, s);
  if (a.$ === "Var" && b.$ === "Var" && a.i === b.i) return true;
  if (a.$ === "Var" && a.i >= META) { if (occurs(a.i, b, s)) return false; s.set(a.i, b); return true; }
  if (b.$ === "Var" && b.i >= META) { if (occurs(b.i, a, s)) return false; s.set(b.i, a); return true; }
  if (a.$ === "Lit" && b.$ === "Ctr") { const x = litStep(a); return !!x && unify(x, b, s, d); }
  if (b.$ === "Lit" && a.$ === "Ctr") { const x = litStep(b); return !!x && unify(a, x, s, d); }
  switch (a.$) {
    case "Var": return false;
    case "Ref": return b.$ === "Ref" && a.k === b.k;
    case "App": return b.$ === "App" && unify(a.f, b.f, s, d) && unify(a.x, b.x, s, d);
    case "Ctr": return b.$ === "Ctr" && a.k === b.k && a.x.length === b.x.length && a.x.every((x, i) => unify(x, (b as any).x[i], s, d));
    case "Lit": return b.$ === "Lit" && a.k === b.k && a.v === b.v;
    case "Eql": return b.$ === "Eql" && unify(a.a, b.a, s, d) && unify(a.b, b.b, s, d) && (unify(a.T, b.T, s, d) || true);
    case "ADT": return b.$ === "ADT" && a.k === b.k && a.x.length === b.x.length && a.x.every((x, i) => unify(x, (b as any).x[i], s, d));
    default: return key(a) === key(b);
  }
};
// bindings of the callee's open parameters that make one of its premises an instance of an indexed
// lemma's conclusion (ground values only)
const forwardBinds = (g: Goal, c: Callee, sol: (LTerm | null)[], prem: boolean[], viaHyp: (string | null)[], o2: { doms: { A: HTerm }[] }): [number, LTerm][][] => {
  const out: [number, LTerm][][] = [];
  const seen = new Set<string>();
  for (let j = 0; j < c.n && out.length < 3; j++) {
    if (!prem[j] || viaHyp[j]) continue;
    const A = attempt(FUEL_NF, () => lower(o2.doms[j].A, g.d));
    if (!A || !hasMeta(A)) continue;
    const open: number[] = [];
    for (let m = 0; m < c.n; m++) if (!sol[m] && !prem[m]) open.push(META + m);
    let looked = 0;
    for (const L of applyIndex.get(headKey(A)) ?? []) {
      if (out.length >= 3 || looked++ > 64) break;
      if (L.order >= job.order || L.k === job.k || L.k === shortKey(c)) continue;
      const o = attempt(FUEL_NF, () => openMeta((RAW[L.k] as B.Def).T, L.n));
      if (!o) continue;
      const P = attempt(FUEL_NF, () => shiftMetas(lower(o.concl, g.d)));
      if (!P) continue;
      const sb = new Map<number, LTerm>();
      if (!unify(P, A, sb, g.d)) continue;
      const alt: [number, LTerm][] = [];
      let ok = true;
      for (const m of open) {
        if (!sb.has(m)) continue;
        const v = resolve(B.Var("?", m), sb);
        if (hasMeta(v) || !closedBelow(v, g.d)) { ok = false; break; }
        alt.push([m - META, v]);
      }
      if (!ok || alt.length === 0) continue;
      const k = alt.map(([m, v]) => m + "=" + key(v)).join(";");
      if (seen.has(k)) continue;
      seen.add(k);
      out.push(alt);
    }
  }
  return out;
};
const shortKey = (c: Callee) => c.text;
const nfPat = new WeakMap<object, Map<number, LTerm | null>>();
const nfPattern = (c: Callee, concl: HTerm, d: number): LTerm | null => {
  let m = nfPat.get(c.T);
  if (!m) { m = new Map(); nfPat.set(c.T, m); }
  if (!m.has(d)) m.set(d, attempt(FUEL_NF, () => nf(concl, d)) ?? null);
  return m.get(d)!;
};
const callText = (c: Callee, args: string[]) => c.text + "(" + args.join(", ") + ")";

const lemmaCands = (g: Goal, targets: LTerm[]): Callee[] => {
  const seen = new Set<string>();
  const out: Callee[] = [];
  for (const t of targets) {
    const ks = t.$ === "Eql" ? [headKey(t), "E|*"] : [headKey(t)];
    for (const hk of ks) {
      for (const L of applyIndex.get(hk) ?? []) {
        if (L.order >= job.order || L.k === job.k || seen.has(L.k)) continue;
        seen.add(L.k);
        out.push({ text: B.name_show(job.file, L.k), T: (RAW[L.k] as B.Def).T, n: L.n, kind: "lemma" });
      }
    }
  }
  return out;
};
// hypotheses that are functions (through aliases): callees
const hypCallees = (g: Goal): Callee[] => {
  const out: Callee[] = [];
  for (let i = g.d - 1; i >= 0; i--) {
    if (!usable(g, i, g.qt)) continue;
    const a = ann(g, i)!;
    let t: HTerm = B.term_strip(a.T), k = 0;
    if (t.$ !== "All") t = wnf(a.T) ?? t;
    while (t.$ === "All" && k < 12) { const b: HTerm = t.B(B.Var("_", 1e7 + k)); t = B.term_strip(b); if (t.$ !== "All") t = wnf(b) ?? t; k++; }
    if (k > 0) out.push({ text: g.names[i], T: a.T, n: k, kind: "hyp" });
  }
  return out;
};
const ihCallee = (): Callee => ({ text: job.short, T: job.def.T, n: job.def.n, kind: "ih" });

const contradictory = (g: Goal): number[] => {
  const out: number[] = [];
  for (let i = g.d - 1; i >= 0; i--) {
    if (!usable(g, i, B.Lone())) continue;
    const ts = hypTargets(g, i);
    const n = ts[ts.length - 1];
    if (n.$ === "Eql") {
      const ha = headKey(n.a), hb = headKey(n.b);
      if (ha.startsWith("C:") && hb.startsWith("C:") && (ha !== hb || (n.a.$ === "Lit" && n.b.$ === "Lit" && n.a.v !== n.b.v))) out.push(i);
    }
  }
  return out;
};

const leaf = (g: Goal, depth: number, rw: number, path: Set<string>): Pf | null => {
  if (performance.now() > deadline) throw TIMEOUT;
  const gk = attempt(FUEL_NF, () => goalKey(g));
  if (gk === undefined) return null;
  if (path.has(gk)) return null;
  const ok = job.memo.get(gk);
  if (ok?.pf) return ok.pf;
  // a failure is memoized with its budget (depth, rewrites) and its candidate cap (level)
  const fk = gk + "#" + Math.min(g.lvl, CAPS.length - 1);
  const m = job.memo.get(fk);
  if (m && m.depth >= depth && m.rw >= rw) return null;
  const p2 = new Set(path);
  p2.add(gk);
  const r = leafGo(g, depth, rw, p2);
  if (r) job.memo.set(gk, { pf: r, depth, rw });
  else job.memo.set(fk, { pf: null, depth: Math.max(depth, m?.depth ?? 0), rw: Math.max(rw, m?.rw ?? 0) });
  return r;
};

const leafGo = (g: Goal, depth: number, rw: number, path: Set<string>): Pf | null => {
  const w = wnf(g.ty);
  if (!w) return null;
  // 1. closers
  if (w.$ === "Eql" && tryText(g, "{==}")) { tag("rfl"); return tm("{==}"); }
  if (w.$ === "ADT") {
    const t = RAW[w.k];
    if (t?.$ === "ADT" && t.c.length === 1 && t.c[0].n === 0) {
      const s = B.name_show(job.file, t.c[0].k) + "{}";
      if (tryText(g, s)) { tag("unit"); return tm(s); }
    }
  }
  for (let i = g.d - 1; i >= 0; i--) {
    if (!usable(g, i, g.qt)) continue;
    const a = ann(g, i)!;
    if (attempt(FUEL_CHECK, () => B.term_compare("LE", book, a.T, g.ty, g.d)) && tryText(g, g.names[i])) { tag("hyp"); return tm(g.names[i]); }
  }
  if (g.path === "" && g.d === job.def.n) {
    for (const imp of autoImports) {
      if (!imp.proofs.has(job.short)) continue;
      if (isOpen(imp.ns + ":" + job.short + ".proof")) continue;
      const call = imp.alias + "." + job.short + ".proof(" + g.names.join(", ") + ")";
      if (tryText(g, call)) { tag("reuse"); return tm(call); }
    }
  }
  // 2. intro
  if (w.$ === "All") {
    const used = new Set(g.names);
    const x = fresh(w.k === "_" || w.k === "" ? "x" : w.k, used);
    const b = intro({ ...g, ty: w, pend: 1, pnames: [x], pmany: [false] }, x, false);
    if (!b) return null;
    const r = leaf(b, depth, rw, path);
    if (!r) return null;
    const s = x + " => " + inline(r);
    if (tryText(g, s)) { tag("intro"); return tm(s); }
    return null;
  }
  // 3. absurd
  const raw = lower(g.ty, g.d);
  for (let i = g.d - 1; i >= 0; i--) {
    if (!usable(g, i, g.qt)) continue;
    const ts = hypTargets(g, i);
    const n = ts[ts.length - 1];
    if (n.$ === "ADT") {
      const t = RAW[n.k];
      if (t?.$ === "ADT" && t.c.length === 0) {
        const s = "Empty.absurd(" + show(raw, g.names) + ", " + g.names[i] + ")";
        if (tryText(g, s)) { tag("absurd"); return tm(s); }
      }
    }
  }
  const contra = contradictory(g);
  if (contra.length > 0 && w.$ === "ADT" && (RAW[w.k] as any)?.c?.length === 0) {
    for (const i of contra) {
      const ts = hypTargets(g, i);
      const E = ts[ts.length - 1] as Extract<LTerm, { $: "Eql" }>;
      const Tk = key(E.T);
      for (const L of (preds.get(Tk) ?? []).slice(0, MAX_CANDS)) {
        if (L.order >= job.order) continue;
        const P = B.name_show(job.file, L.k);
        for (const sym of [false, true]) {
          const [x, y] = sym ? [E.b, E.a] : [E.a, E.b];
          const e = sym ? "Equal.sym(" + show(E.T, g.names) + ", " + show(E.a, g.names) + ", " + show(E.b, g.names) + ", " + g.names[i] + ")" : g.names[i];
          const sub: Goal = { ...g, ty: B.App(B.Ref(L.k), B.term_higher(x, g.env)) };
          if (!tryText(g, "%" + e + " : " + P + "(_); ?TODO")) continue;
          const r = leaf(sub, 0, 0, path);
          if (r) { const pf: Pf = { t: "rw", e, P: P + "(_)", k: r }; if (tryText(g, flat(pf))) { tag("discriminate"); return pf; } }
          void y;
        }
      }
    }
  }
  if (contra.length > 0 && depth > 0) {
    for (const L of wild) {
      if (L.order >= job.order || L.k === job.k) continue;
      const c: Callee = { text: B.name_show(job.file, L.k), T: (RAW[L.k] as B.Def).T, n: L.n, kind: "lemma" };
      const a = applyCallee(g, c, [raw], 1, 0, path, null, (a) => tryText(g, callText(c, a.args)));
      if (a) { tag("exfalso"); return tm(callText(c, a.args)); }
    }
  }
  if (depth === 0 && rw === 0) return null;
  const n = attempt(FUEL_NF * 2, () => nf(g.ty, g.d));
  const targets = n && key(n) !== key(raw) ? [raw, n] : [raw];
  // 4. apply
  if (depth > 0) {
    const callees: Callee[] = hypCallees(g);
    if (job.ih && g.split) callees.push(ihCallee());
    // lemmas: those whose conclusion matches, most specific first (a general lemma such as
    // weaken: Le(a, b) from Le(1+a, b) matches every goal of its head, and is tried last)
    const lem = lemmaCands(g, targets).map((c) => { const pr = { n: 0, probe: true, spec: -1 }; applyCallee(g, c, targets, depth, rw, path, null, () => false, pr); return { c, spec: pr.spec! }; });
    callees.push(...lem.filter((x) => x.spec >= 0).sort((a, b) => b.spec - a.spec).map((x) => x.c));
    const cap = CAPS[Math.min(g.lvl, CAPS.length - 1)];
    const tries = { n: 0 };
    for (const c of callees) {
      if (performance.now() > deadline) throw TIMEOUT;
      if (tries.n >= cap) break;
      const a = applyCallee(g, c, targets, depth, rw, path, null, (a) => tryText(g, callText(c, a.args)), tries);
      if (a) { tag("apply:" + c.kind); return tm(callText(c, a.args)); }
    }
  }
  // 5. rewrite
  if (rw > 0) {
    const r = rewrite(g, depth, rw, path);
    if (r) return r;
  }
  return null;
};

type RwCand = { base: LTerm; from: LTerm; to: LTerm; e: string; kind: string; score: number };
const rewrite = (g: Goal, depth: number, rw: number, path: Set<string>): Pf | null => {
  const N0 = attempt(FUEL_NF * 2, () => nf(g.ty, g.d + 1));
  const R = attempt(FUEL_NF, () => lower(g.ty, g.d + 1));
  const bases: LTerm[] = [];
  if (N0 && size(N0, 600) <= 600) bases.push(N0);
  if (R && size(R, 600) <= 600 && (!N0 || key(R) !== key(N0))) bases.push(R);
  if (bases.length === 0) return null;
  const N = bases[0];
  const cands: RwCand[] = [];
  for (const base of bases) rwCands(g, base, base === R && bases.length > 1, depth, path, cands);
  return rwRun(g, cands, depth, rw, path);
};
const rwCands = (g: Goal, N: LTerm, isRaw: boolean, depth: number, path: Set<string>, cands: RwCand[]) => {
  const subs = new Map<string, LTerm>();
  subterms(N, subs);
  const blk: LTerm[] = [];
  blockers(N, blk);
  const blkKeys = new Set(blk.map(key));
  const okFrom = (t: LTerm) => t.$ === "Var" || t.$ === "App" || (t.$ === "Ctr" && t.x.length > 0);
  // hypotheses
  for (let i = g.d - 1; i >= 0; i--) {
    if (!usable(g, i, g.qt)) continue;
    const ts = hypTargets(g, i);
    for (const E of ts) {
      if (E.$ !== "Eql") continue;
      const ka = key(E.a), kb = key(E.b);
      if (ka === kb) continue;
      if (subs.has(kb) && okFrom(E.b)) cands.push({ base: N, from: E.b, to: E.a, e: g.names[i], kind: "rw:hyp", score: (blkKeys.has(kb) ? 0 : 1) + (isRaw ? 0.2 : 0) });
      if (subs.has(ka) && okFrom(E.a)) cands.push({ base: N, from: E.a, to: E.b, e: "Equal.sym(" + show(E.T, g.names) + ", " + show(E.a, g.names) + ", " + show(E.b, g.names) + ", " + g.names[i] + ")", kind: "rw:hyp", score: (blkKeys.has(ka) ? 0 : 1) + (isRaw ? 0.2 : 0) });
    }
  }
  // the induction hypothesis and lemmas, on the stuck calls of nf(goal)
  for (const [sk, s] of subs) {
    const hk = headKey(s);
    const h = s.$ === "App" ? unapply(s)[0] : s;
    if (h.$ !== "Ref" && !(s.$ !== "App" && rwIndex.has(hk))) continue;
    const entries: { c: Callee; side: 0 | 1; kind: string }[] = [];
    if (h.$ === "Ref" && job.ih && g.split) {
      const o = attempt(FUEL_NF, () => { const oo = openMeta(job.def.T, job.def.n); return oo ? lower(oo.concl, g.d + 1) : null; });
      if (o && o.$ === "Eql") for (const side of [0, 1] as const) if (headKey(side === 0 ? o.a : o.b) === "R:" + h.k) entries.push({ c: ihCallee(), side, kind: "rw:ih" });
    }
    for (const { L, side } of rwIndex.get(hk) ?? []) {
      if (L.order >= job.order || L.k === job.k) continue;
      entries.push({ c: { text: B.name_show(job.file, L.k), T: (RAW[L.k] as B.Def).T, n: L.n, kind: "lemma" }, side, kind: "rw:lemma" });
      if (entries.length > MAX_CANDS) break;
    }
    for (const { c, side, kind } of entries) {
      if (performance.now() > deadline) throw TIMEOUT;
      const gg: Goal = { ...g, d: g.d + 1 - 1 };
      const a = applyCallee(gg, c, [s], depth, 0, path, (o) => (o.$ === "Eql" ? (side === 0 ? o.a : o.b) : null), () => true);
      if (process.env.GEN2_TRACE && kind === "rw:ih") console.error("[trace] ih on " + show(s, [...g.names, "_"]).slice(0, 100) + " -> " + (a ? a.args.join(", ") : "no"));
      if (!a) continue;
      const o2 = openMeta(c.T, c.n, a.sol.map((x) => (x ? B.term_higher(x, g.env) : null)));
      if (!o2) continue;
      const E = attempt(FUEL_NF, () => lower(o2.concl, g.d + 1));
      if (!E || E.$ !== "Eql" || hasMeta(E)) continue;
      const call = callText(c, a.args);
      const to = side === 0 ? E.b : E.a;
      if (key(to) === sk) continue;
      const e = side === 0 ? "Equal.sym(" + show(E.T, g.names) + ", " + show(E.a, g.names) + ", " + show(E.b, g.names) + ", " + call + ")" : call;
      cands.push({ base: N, from: s, to, e, kind, score: (blkKeys.has(sk) ? 0 : 1) + (c.n === 0 ? -0.5 : kind === "rw:ih" ? 0 : 0.5) + (isRaw ? 0.2 : 0) });
    }
  }
};
const rwRun = (g: Goal, cands: RwCand[], depth: number, rw: number, path: Set<string>): Pf | null => {
  cands.sort((a, b) => a.score - b.score);
  const motiveNames = [...g.names, "_"];
  const later: { c: RwCand; P: string; sub: Goal; gk: string }[] = [];
  const seen = new Set<string>();
  for (const c of cands) {
    if (performance.now() > deadline) throw TIMEOUT;
    const fk = key(c.from);
    const Pt = replace(c.base, fk, B.Var("_", g.d));
    const Gp = replace(c.base, fk, c.to);
    const gpk = key(Gp);
    if (seen.has(gpk)) continue;
    seen.add(gpk);
    if (!closedBelow(Gp, g.d) && Gp.$ !== "Eql") { /* binders: keep */ }
    const P = show(Pt, motiveNames);
    if (process.env.GEN2_TRACE) console.error("[trace] rw " + c.kind + " " + c.e.slice(0, 120) + " : " + P.slice(0, 160));
    if (!tryText(g, "%" + c.e + " : " + P + "; ?TODO")) continue;
    const sub: Goal = { ...g, ty: B.term_higher(Gp, g.env) };
    if (tryText(sub, "{==}")) { tag(c.kind); tag("rfl"); return { t: "rw", e: c.e, P, k: tm("{==}") }; }
    later.push({ c, P, sub, gk: gpk });
  }
  for (const l of later.slice(0, BEAM)) {
    const r = leaf(l.sub, depth, rw - 1, path);
    if (r) {
      const pf: Pf = { t: "rw", e: l.c.e, P: l.P, k: r };
      if (tryText(g, flat(pf))) { tag(l.c.kind); return pf; }
    }
  }
  return null;
};

// ---- node tactics: split ----
const isData = (g: Goal, A: HTerm) => attempt(FUEL_NF, () => { B.term_check(book, g.lhs, A, B.None(), B.Typ(B.Qua(B.Many())), g.ctx, g.d); return true; }) === true;

const split = (n: Goal, j: number): { pat: string; node: Goal }[] | null => {
  let g: Goal | null = n;
  for (let i = 0; i < j && g; i++) g = intro(g, g.pnames[0], g.pmany[0]);
  if (!g) return null;
  const t = wnf(g.ty);
  if (!t || t.$ !== "All" || t.q.$ === "None") return null;
  const A = wnf(t.A);
  if (!A || A.$ !== "ADT") return null;
  const adt = attempt(FUEL_NF, () => B.book_adt(book, A, g!.ctx, job.k));
  if (!adt || adt.c.length === 0) return null;
  const sname = g.pnames[0];
  const used = new Set([...g.names, ...g.pnames]);
  const arms: { pat: string; node: Goal }[] = [];
  for (const ctr of adt.c) {
    const gg = g;
    const tel = attempt(FUEL_NF, () => B.tele_fill(book, ctr.T, A.x, gg.ctx, job.k));
    if (!tel) return null;
    const mk = (cur: HTerm, m: number, xs: HTerm[]): HTerm => {
      if (m === 0) return t.B(B.Ctr(ctr.k, xs));
      const c = B.tele_head(book, cur, gg.ctx, job.k);
      const dem = c.q.$ === "None" ? B.None() : c.q.$ === "Lone" ? t.q : B.quant_add(t.q, t.q);
      return B.All<B.HBody>(dem, c.k, c.i, c.A, (x: HTerm) => mk(c.B(x), m - 1, xs.concat([x])));
    };
    const goal = attempt(FUEL_NF, () => mk(tel, ctr.n, []));
    if (!goal) return null;
    const lhs = g.lhs.n > 0 ? { ...g.lhs, t: B.lhs_ext(g.lhs.t, ctr.k, ctr.n), n: g.lhs.n - 1 + ctr.n } : g.lhs;
    // field names and marks
    const fnames: string[] = [], fmany: boolean[] = [];
    const isNat = ctr.k === "Succ" || ctr.k === "Zero";
    let probe: Goal | null = { ...g, ty: goal, lhs, pend: ctr.n, pnames: [], pmany: [] };
    let cur: HTerm = goal;
    for (let f = 0; f < ctr.n; f++) {
      const c = wnf(cur) as any;
      if (!c || c.$ !== "All") return null;
      const base = isNat ? (sname.length <= 2 ? sname + "p" : "p") : c.k;
      const nm = fresh(base, used);
      const many = !isNat && c.q.$ === "Lone" && probe !== null && isData(probe, c.A);
      fnames.push(nm);
      fmany.push(many);
      probe = probe ? intro({ ...probe, pend: 1, pnames: [nm], pmany: [many] }, nm, many) : null;
      cur = c.B(B.Var(nm, g.d + f));
    }
    const node: Goal = {
      ...g, ty: goal, lhs, pend: ctr.n + g.pend - 1, pnames: [...fnames, ...g.pnames.slice(1)], pmany: [...fmany, ...g.pmany.slice(1)],
      split: true, path: n.path + "/" + shortOf(ctr.k), hc: new Map(),
    };
    const cn = B.name_show(job.file, ctr.k);
    const pat = isNat ? (ctr.k === "Zero" ? "0n" : "1n+" + fnames[0]) : cn + "{" + fnames.map((f, i) => (fmany[i] ? "+" : "") + f).join(", ") + "}";
    arms.push({ pat, node });
  }
  return arms;
};

const splitCands = (n: Goal, lg: Goal): number[] => {
  const out: number[] = [];
  const records: number[] = [];
  let record: Goal | null = n;
  for (let j = 0; j < n.pend && record; j++) {
    const t = wnf(record.ty);
    if (!t || t.$ !== "All") break;
    const A = wnf(t.A);
    if (A?.$ === "ADT" && t.q.$ !== "None") {
      const a = RAW[A.k];
      if (a?.$ === "ADT" && a.c.length === 1 && a.c[0].n > 0 &&
          !/^(U32|F32|Chr|Word)$/.test(A.k) && !/\b(?:WCon|WNil)$/.test(a.c[0].k)) records.push(j);
    }
    record = intro(record, record.pnames[0], record.pmany[0]);
  }
  out.push(...records.slice(-2).reverse());
  const add = (t: LTerm) => {
    if (t.$ !== "Var") return;
    const j = t.i - n.d;
    if (j >= 0 && j < n.pend && !out.includes(j)) out.push(j);
  };
  const N = attempt(FUEL_NF * 2, () => nf(lg.ty, lg.d));
  const blk: LTerm[] = [];
  if (N) blockers(N, blk);
  for (let i = lg.d - 1; i >= n.d; i--) {
    const h = hypTargets(lg, i);
    blockers(h[h.length - 1], blk);
  }
  for (let i = n.d - 1; i >= 0; i--) {
    const h = hypTargets(lg, i);
    blockers(h[h.length - 1], blk);
  }
  blk.forEach(add);
  const depth = n.path.split("/").length - 1;
  return out.slice(0, depth >= 4 ? 1 : depth >= 2 ? 2 : MAX_SPLIT_CANDS);
};

const solve = (n: Goal, S: number, D: number, partial: boolean): Res => {
  if (performance.now() > deadline) throw TIMEOUT;
  const nk = (attempt(FUEL_NF, () => goalKey(n)) ?? Math.random()) + "#" + n.pnames.join(",") + "#" + S + "," + D + (partial ? "p" : "");
  const m = job.smemo.get(nk);
  if (m) return m;
  let r: Res;
  try {
    r = solveGo(n, S, D, partial);
  } catch (e) {
    // a partial pass keeps what it has: a goal reached past the deadline is a hole
    if (e !== TIMEOUT || !partial) throw e;
    return { pf: { t: "hole", g: introAll(n) ?? n }, holes: 1, closed: 0 };
  }
  job.smemo.set(nk, r);
  return r;
};
const solveGo = (n: Goal, S: number, D: number, partial: boolean): Res => {
  const lg = introAll(n);
  if (!lg) return { pf: { t: "hole", g: n }, holes: 1, closed: 0 };
  for (let dd = 0; dd <= D; dd++) {
    const lf = leaf(lg, dd, dd === 0 ? 1 : MAX_RW, new Set());
    if (lf) {
      if (STREAM) console.error("[gen2] closed " + (n.path || "/") + ": " + flat(lf).slice(0, 160));
      return { pf: lf, holes: 0, closed: 1 };
    }
  }
  let best: Res = { pf: { t: "hole", g: lg }, holes: 1, closed: 0 };
  if (S === 0 || n.pend === 0) return best;
  for (const j of splitCands(n, lg)) {
    const arms = split(n, j);
    if (!arms) continue;
    let holes = 0, closed = 0;
    const out: { pat: string; k: Pf }[] = [];
    let i = 0;
    for (; i < arms.length; i++) {
      const r = solve(arms[i].node, S - 1, D, partial);
      holes += r.holes; closed += r.closed;
      out.push({ pat: arms[i].pat, k: r.pf });
      if (!partial && r.holes > 0) break;
    }
    if (i < arms.length) continue;
    const pf: Pf = { t: "mt", x: n.pnames[j], arms: out };
    if (holes === 0) { tag("split"); return { pf, holes: 0, closed }; }
    if (holes < best.holes || (holes === best.holes && closed > best.closed)) best = { pf, holes, closed };
  }
  return best;
};

// ---- decomposition ----
// the best one-step skeleton for a leaf goal that the search does not close: an applied callee (most
// specific first) whose solved premises are filled and whose open premises are holes; fewest holes
// first, then the smallest holes; no hole may restate the goal
// the keys of a goal: as stated, and with the sides of an equation swapped
const goalKeys = (g: Goal): string[] => {
  const pre = g.ckey + "|-" + g.qt.$[0];
  const out: string[] = [];
  for (const t of [lower(g.ty, g.d), nf(g.ty, g.d)]) {
    out.push(pre + key(t));
    if (t.$ === "Eql") out.push(pre + key(B.Eql(t.b, t.a, t.T)), pre + "=" + key(t.a) + "|" + key(t.b), pre + "=" + key(t.b) + "|" + key(t.a));
  }
  return out;
};
const bestStep = (g: Goal, anc: Set<string> = new Set()): Pf | null => {
  const raw = lower(g.ty, g.d);
  const n = attempt(FUEL_NF * 2, () => nf(g.ty, g.d));
  const targets = n && key(n) !== key(raw) ? [raw, n] : [raw];
  const gk = goalKey(g);
  const own = new Set(attempt(FUEL_NF, () => goalKeys(g)) ?? []);
  const callees: Callee[] = hypCallees(g);
  if (job.ih && g.split) callees.push(ihCallee());
  const lem = lemmaCands(g, targets).map((c) => { const pr = { n: 0, probe: true, spec: -1 }; applyCallee(g, c, targets, 1, 0, new Set(), null, () => false, pr); return { c, spec: pr.spec! }; });
  callees.push(...lem.filter((x) => x.spec >= 0).sort((a, b) => b.spec - a.spec).map((x) => x.c));
  let best: { pf: Pf; holes: number; size: number } | null = null;
  const tries = { n: 0 };
  for (const c of callees) {
    if (tries.n >= 24) break;
    applyCallee(g, c, targets, MAX_DEPTH - 1, MAX_RW, new Set([gk]), null, (a) => {
      const hs = a.holes ?? [];
      if (hs.length === 0 || hs.length >= c.n) return false;
      if (hs.some((h) => (attempt(FUEL_NF, () => goalKeys(h)) ?? [gk]).some((k) => k === gk || anc.has(k) || own.has(k)))) return false;
      const s = callText(c, a.args.map((x) => (x === HOLE ? "?TODO" : x)));
      if (!tryText(g, s)) return false;
      const sz = hs.reduce((acc, h) => acc + (attempt(FUEL_NF, () => size(lower(h.ty, h.d))) ?? 99), 0);
      if (!best || hs.length < best.holes || (hs.length === best.holes && sz < best.size)) {
        best = { pf: { t: "app", s: callText(c, a.args), subs: hs.map((h) => ({ t: "hole", g: h }) as Pf) }, holes: hs.length, size: sz };
      }
      return false;
    }, tries, true);
  }
  return best ? (best as any).pf : null;
};

// attack a leaf goal with its own budget; when it stays open, decompose it one step and recurse
const decompose = (g: Goal, level: number, until: number, anc: Set<string> = new Set()): Res => {
  const hole: Res = { pf: { t: "hole", g }, holes: 1, closed: 0 };
  if (performance.now() > until) return hole;
  deadline = Math.min(until, performance.now() + HOLE_BUDGET);
  try {
    for (let dd = 0; dd <= MAX_DEPTH + 1; dd++) {
      const r = leaf({ ...g, lvl: 0 }, dd, dd === 0 ? 1 : MAX_RW, new Set());
      if (r) { tag("decomp"); if (STREAM) console.error("[gen2] closed " + g.path + ": " + flat(r).slice(0, 160)); return { pf: r, holes: 0, closed: 1 }; }
    }
  } catch (e) { if (e !== TIMEOUT) throw e; }
  if (level >= MAX_DECOMP) return hole;
  deadline = Math.min(until, performance.now() + HOLE_BUDGET);
  let step: Pf | null = null;
  const anc2 = new Set([...anc, ...(attempt(FUEL_NF, () => goalKeys(g)) ?? [])]);
  try { step = bestStep({ ...g, lvl: 0 }, anc2); } catch (e) { if (e !== TIMEOUT) throw e; }
  if (!step || step.t !== "app") return hole;
  const subs: Pf[] = [];
  let holes = 0, closed = 1;
  for (const s of step.subs) {
    const r = decompose((s as any).g, level + 1, until, anc2);
    subs.push(r.pf); holes += r.holes; closed += r.closed;
  }
  return { pf: { t: "app", s: step.s, subs }, holes, closed };
};
const fillHoles = (p: Pf, f: (g: Goal) => Res, acc: { holes: number; closed: number }): Pf => {
  switch (p.t) {
    case "hole": { const r = f(p.g); acc.holes += r.holes; acc.closed += r.closed; return r.pf; }
    case "rw": return { ...p, k: fillHoles(p.k, f, acc) };
    case "mt": return { ...p, arms: p.arms.map((a) => ({ pat: a.pat, k: fillHoles(a.k, f, acc) })) };
    case "app": return { ...p, subs: p.subs.map((x) => fillHoles(x, f, acc)) };
    default: return p;
  }
};

// ---- jobs ----
const rootGoal = (k: string): Goal => {
  const def = RAW[k] as B.Def;
  const qs = B.tele_unbind(book, def.T).doms.map((dm) => dm[0]);
  const pnames: string[] = [];
  let t = def.T;
  for (let j = 0; j < def.n; j++) { const s = B.term_strip(t) as any; pnames.push(s.k); t = s.B(B.Var(s.k, j)); }
  return {
    ctx: B.ctx_nil(), d: 0, ty: def.T, lhs: { t: B.Ref(k), n: def.n - def.x, def: k, qs, u: def.u }, qt: B.Lone(), env: null,
    names: [], ckey: "", pend: def.n, pnames, pmany: pnames.map(() => false), split: false, path: "", lvl: 0, hc: new Map(),
  };
};
const newJob = (k: string): Job => {
  const def = RAW[k] as B.Def;
  return { k, def, order: ORDER.get(k) ?? book.order.length, file: sourceFiles.get(k)!, short: shortOf(k), tags: new Map(), memo: new Map(), smemo: new Map(), closed: 0, ih: true };
};

type Outcome = { ok: boolean; text: string | null; partial: string | null; holes: number; closed: number; ms: number; tags: string[]; why?: string };

const showGoal = (g: Goal): string => {
  const lines: string[] = [];
  for (let i = 0; i < g.d; i++) {
    const a = ann(g, i)!;
    lines.push("    " + B.quant_show(a.q) + g.names[i] + " : " + show(lower(a.T, i), g.names.slice(0, i)));
  }
  const raw = show(lower(g.ty, g.d), g.names);
  const n = attempt(FUEL_NF * 2, () => show(nf(g.ty, g.d), g.names));
  return "  goal : " + raw + (n && n !== raw ? "\n  nf   : " + n : "") + "\n  context:\n" + lines.join("\n");
};

// prove the whole body of k (its body forgotten)
const proveDef = (k: string, budget: number): Outcome => {
  job = newJob(k);
  const t0 = performance.now();
  deadline = t0 + budget;
  const root = rootGoal(k);
  let best: Res | null = null;
  let full: Pf | null = null;
  let why = "";
  try {
    outer: for (let cost = 1; cost <= MAX_SPLIT + MAX_DEPTH; cost++) {
      for (let S = Math.min(MAX_SPLIT, cost - 1); S >= 0; S--) {
        const D = Math.min(MAX_DEPTH, cost - S);
        if (D < 1 && cost > 1) continue;
        const r = solve(root, S, D, false);
        if (r.holes === 0) { full = r.pf; break outer; }
      }
    }
  } catch (e) {
    if (e !== TIMEOUT) throw e;
    why = "time";
  }
  if (!full && (PARTIAL || DECOMP)) {
    deadline = performance.now() + Math.max(500, budget / 3);
    try { best = solve(root, Math.min(MAX_SPLIT, 3), Math.min(MAX_DEPTH, 2), true); } catch (e) { if (e !== TIMEOUT) throw e; }
    if (best && best.holes > 0 && DECOMP) {
      // each open subgoal with its own budget (HOLE_BUDGET), all of them within 2 x budget
      const until = performance.now() + 2 * budget;
      const acc = { holes: 0, closed: best.closed };
      const pf = fillHoles(best.pf, (g) => decompose(g, 0, until), acc);
      best = { pf, holes: acc.holes, closed: acc.closed };
      if (acc.holes === 0) { full = pf; tag("decomp"); }
    }
  }
  deadline = Infinity;
  const ms = performance.now() - t0;
  const tags = [...job.tags.keys()];
  if (full) {
    const out: string[] = [];
    render(full, "  ", out);
    const text = out.join("\n");
    const ok = attempt(FUEL_FINAL, () => { checkDef(k, text); return true; });
    if (ok) return { ok: true, text, partial: null, holes: 0, closed: 0, ms: performance.now() - t0, tags };
    if (DEBUG) {
      try { checkDef(k, text); } catch (e: any) { console.error("[gen2] final check failed for " + k + ":\n" + text + "\n" + (e?.$ === "Err" ? B.err_show(e) : e)); }
    }
    why = "final check";
  }
  let partial: string | null = null;
  if (best && best.holes > 0) {
    const out: string[] = [];
    render(best.pf, "  ", out);
    const hs = holesOf(best.pf);
    partial = out.join("\n") + "\n" + hs.map((g, i) => "# hole " + (i + 1) + " at " + (g.path || "/") + "\n" + showGoal(g)).join("\n");
  }
  return { ok: false, text: null, partial, holes: best?.holes ?? 1, closed: best?.closed ?? 0, ms, tags, why };
};

// prove the ?TODO holes of k's body, one by one (leaf tactics)
type HoleRes = { hole: number; ok: boolean; ms: number; text: string; partial?: string };
const proveHoles = (k: string, budget: number, log = true): { body: string; n: number; done: number; res: HoleRes[] } => {
  const res: HoleRes[] = [];
  const ds = defSrc(k)!;
  let body = ds.body;
  const n = (body.match(/\?TODO/g) ?? []).length;
  let done = 0;
  for (let h = 0; h < n; h++) {
    // find the next ?TODO not yet filled: mark it, read its goal from bend2's error
    let idx = -1;
    for (let c = 0, from = 0; c <= h - done; c++) { idx = body.indexOf("?TODO", from); from = idx + 1; }
    const marked = body.slice(0, idx) + "?gen2hole" + body.slice(idx + 5);
    job = newJob(k);
    job.ih = true;
    let err: any = null;
    try { checkDef(k, marked); } catch (e) { err = e; }
    if (!err || err.$ !== "Err" || typeof err.exp === "string") {
      const why = "no goal (" + (err ? (err.$ === "Err" ? B.err_show(err) : String(err)) : "checked") + ")";
      if (log) console.error("[gen2] hole " + (h + 1) + ": " + why);
      res.push({ hole: h + 1, ok: false, ms: 0, text: why });
      continue;
    }
    const arr = B.pmap_to_array(err.ctx as B.Ctx).sort((a, b) => a[0] - b[0]);
    const d = arr.length ? arr[arr.length - 1][0] + 1 : 0;
    const names: string[] = [];
    let env: B.Env = null;
    let ckey = "";
    for (let i = 0; i < d; i++) {
      const a = B.pmap_get(err.ctx as B.Ctx, i);
      names.push(a?.k ?? "_");
      env = B.list_set(env, i, B.Var(a?.k ?? "_", i));
      ckey += "|" + (a ? a.q.$[0] + a.k + ":" + (attempt(FUEL_NF, () => key(lower(a.T, i))) ?? "?") : "_");
    }
    const def = RAW[k] as B.Def;
    const g: Goal = {
      ctx: err.ctx, d, ty: err.exp, lhs: { t: B.Ref(k), n: 0, def: k, qs: [], u: true }, qt: B.Lone(), env, names, ckey,
      pend: 0, pnames: [], pmany: [], split: true, path: "hole" + (h + 1), lvl: 0, hc: new Map(),
    };
    const t0 = performance.now();
    deadline = t0 + budget;
    let pf: Pf | null = null;
    try {
      for (let dd = 0; dd <= MAX_DEPTH && !pf; dd++) pf = leaf(g, dd, dd === 0 ? 1 : MAX_RW, new Set());
    } catch (e) { if (e !== TIMEOUT) throw e; }
    deadline = Infinity;
    const ms = (performance.now() - t0).toFixed(0);
    if (!pf) {
      let partial = "";
      if (DECOMP) {
        const r = decompose(g, 0, performance.now() + budget);
        deadline = Infinity;
        if (r.closed > 0) {
          const out: string[] = [];
          render(r.pf, "", out);
          partial = "# PARTIAL (" + r.holes + " holes, " + r.closed + " subgoals closed): not a finished proof\n" + out.join("\n") + "\n" + holesOf(r.pf).map((hg, i) => "# subgoal " + (i + 1) + " at " + hg.path + "\n" + showGoal(hg)).join("\n");
        }
      }
      const text = "not found (" + ms + " ms)\n" + showGoal(g);
      if (log) console.error("[gen2] hole " + (h + 1) + ": " + text + (partial ? "\n" + partial : ""));
      res.push({ hole: h + 1, ok: false, ms: +ms, text, partial: partial || undefined });
      continue;
    }
    const line = body.slice(body.lastIndexOf("\n", idx) + 1, idx);
    const ind = /^\s*$/.test(line) ? line : line.replace(/\S.*$/, "").replace(/$/, "  ");
    const out: string[] = [];
    render(pf, ind, out);
    const text = out.join("\n").slice(ind.length);
    const nb = body.slice(0, idx) + text + body.slice(idx + 5);
    const ok = attempt(FUEL_FINAL, () => { checkDef(k, nb); return true; });
    if (!ok) {
      if (log) console.error("[gen2] hole " + (h + 1) + ": candidate failed the def check: " + flat(pf));
      res.push({ hole: h + 1, ok: false, ms: +ms, text: "candidate failed the def check: " + flat(pf) });
      continue;
    }
    body = nb;
    done++;
    if (log) console.error("[gen2] hole " + (h + 1) + ": filled (" + ms + " ms)");
    res.push({ hole: h + 1, ok: true, ms: +ms, text });
  }
  return { body, n, done, res };
};

// ---- bench ----
// a proposition: an equation, Empty or Unit, a function to a proposition, or a stuck call of a def
// whose every case gives a proposition (Le(a, b) = T(..): Unit or Empty); a datatype with fields
// (Word(n), Nat, a state) is data, and its def is a function, not a lemma
const isPropType = (h: HTerm, n = 0): boolean => {
  if (n > 6) return false;
  const w = wnf(h);
  if (!w) return false;
  switch (w.$) {
    case "Eql": return true;
    case "ADT": { const t = RAW[w.k]; return t?.$ === "ADT" && (t.c.length === 0 || (t.c.length === 1 && t.c[0].n === 0)); }
    case "All": return isPropType(w.B(B.Var("_", 1e7 + n)), n + 1);
    case "App": {
      const [hd] = B.term_unapply(w);
      const f = B.term_strip(hd);
      if (f.$ !== "Ref") return false;
      const t = RAW[f.k];
      if (t?.$ !== "Def" || t.v === null) return false;
      const leaves: HTerm[] = [];
      let budget = 64;
      const walk = (x: HTerm) => {
        if (--budget < 0) return;
        x = B.term_strip(x);
        if (x.$ === "Lam") { walk(x.f(B.Var("_", 1e7 + 50 + budget))); return; }
        if (x.$ === "Mat") { walk(x.h); walk(x.m); return; }
        if (x.$ === "Efq") return;
        leaves.push(x);
      };
      walk(t.v);
      return budget >= 0 && leaves.length > 0 && leaves.every((l) => isPropType(l, n + 1));
    }
    default: return false;
  }
};
const isLemma = (def: B.Def): boolean => {
  const o = attempt(20000, () => openMeta(def.T, def.n));
  return !!o && attempt(20000, () => isPropType(o.concl)) === true;
};
const bench = () => {
  const only = new RegExp(opt("only", ".*"));
  const max = +opt("max", "100000");
  const rows: any[] = [];
  const own = book.order.slice(N0).filter((k) => RAW[k]?.$ === "Def" && !(RAW[k] as B.Def).b);
  for (const k of own) {
    if (rows.length >= max) break;
    const def = RAW[k] as B.Def;
    if (!only.test(k) || def.v === null || def.x > 0 || def.i || !isLemma(def)) continue;
    const ds = defSrc(k);
    if (!ds || ds.body.includes("?TODO")) continue;
    const lines = ds.body.split("\n").filter((l) => l.trim() !== "" && !l.trim().startsWith("#")).length;
    RAW[k] = { ...def, v: null };
    let o: Outcome;
    try { o = proveDef(k, BUDGET); } finally { RAW[k] = def; }
    const cls = lines <= 3 ? "S(1-3)" : lines <= 10 ? "M(4-10)" : "L(11+)";
    rows.push({ k, lines, cls, ok: o.ok, ms: Math.round(o.ms), tags: o.tags, holes: o.holes, closed: o.closed, why: o.why, proof: o.text, orig: ds.body });
    console.error((o.ok ? "OK  " : "--  ") + String(Math.round(o.ms)).padStart(6) + " ms  " + cls.padEnd(8) + " " + k + (o.ok ? "  [" + o.tags.join(" ") + "]" : o.why ? "  (" + o.why + ")" : ""));
  }
  const by = new Map<string, { n: number; ok: number; ms: number }>();
  for (const r of rows) { const b = by.get(r.cls) ?? { n: 0, ok: 0, ms: 0 }; b.n++; if (r.ok) b.ok++; b.ms += r.ms; by.set(r.cls, b); }
  const tot = rows.reduce((a, r) => a + r.ms, 0);
  const okn = rows.filter((r) => r.ok).length;
  console.log("file " + FILE + ": " + okn + "/" + rows.length + " re-proven, total " + (tot / 1000).toFixed(1) + " s" + (rows.length ? ", mean " + Math.round(tot / rows.length) + " ms" : "") + " (budget " + BUDGET + " ms; load " + Math.round(tLoad) + " ms, valid " + Math.round(tValid - tLoad) + " ms, index " + Math.round(tIndex) + " ms)");
  for (const c of ["S(1-3)", "M(4-10)", "L(11+)"]) { const b = by.get(c); if (b) console.log("  " + c.padEnd(8) + " " + b.ok + "/" + b.n + "  mean " + Math.round(b.ms / b.n) + " ms"); }
  const okMs = rows.filter((r) => r.ok).map((r) => r.ms).sort((a, b) => a - b);
  if (okMs.length) console.log("  hits: median " + okMs[okMs.length >> 1] + " ms, max " + okMs[okMs.length - 1] + " ms");
  const tg = new Map<string, number>();
  for (const r of rows) if (r.ok) for (const t of r.tags) tg.set(t, (tg.get(t) ?? 0) + 1);
  console.log("  tactics in hits: " + [...tg].sort((a, b) => b[1] - a[1]).map(([t, n]) => t + " " + n).join(", "));
  if (PARTIAL) {
    const fails = rows.filter((r) => !r.ok);
    console.log("  partial: " + fails.filter((r) => r.closed > 0).length + "/" + fails.length + " misses close some subgoal; " + fails.reduce((a, r) => a + r.closed, 0) + " subgoals closed, " + fails.reduce((a, r) => a + r.holes, 0) + " holes left");
  }
  if (internal) console.log("  internal errors: " + internal);
  const jf = opt("json", "");
  if (jf) fs.writeFileSync(jf, JSON.stringify(rows, null, 1));
};

// ---- batch ----
// every def of the book (not Base) with a ?TODO in its body: a whole ?TODO body is proven whole (splits),
// other holes one by one; writes DIR/report.txt (per hole: proof, or partial with its open subgoals)
// and DIR/gen2.patch (a unified diff, from the repository root, of the holes it proved)
const batch = () => {
  const only = new RegExp(opt("only", ".*"));
  const dir = path.resolve(opt("out", "gen2-out"));
  fs.mkdirSync(dir, { recursive: true });
  const todo = Object.keys(RAW).filter((k) => {
    const t = RAW[k];
    if (t.$ !== "Def" || t.b === true || !only.test(k)) return false;
    const ds = defSrc(k);
    return !!ds && /\?TODO/.test(ds.body);
  }).sort((a, b) => (ORDER.get(a) ?? 0) - (ORDER.get(b) ?? 0));
  const report: string[] = [];
  const newBody = new Map<string, string>();
  let holes = 0, proven = 0, partials = 0;
  const t0 = performance.now();
  for (const k of todo) {
    const ds = defSrc(k)!;
    const where = path.relative(TOP, ds.file) + ":" + (ds.bodyLine + 1);
    if (ds.body.trim() === "?TODO") {
      holes++;
      const def = RAW[k] as B.Def;
      RAW[k] = { ...def, v: null };
      let o: Outcome;
      try { o = proveDef(k, BUDGET); } finally { RAW[k] = def; }
      if (o.ok) { proven++; newBody.set(k, o.text!); report.push("== " + shortOf(k) + " (" + where + "): PROVEN whole body in " + Math.round(o.ms) + " ms [" + o.tags.join(" ") + "]\n" + o.text); }
      else { if (o.partial) partials++; report.push("== " + shortOf(k) + " (" + where + "): OPEN (" + Math.round(o.ms) + " ms)\n" + (o.partial ? "# PARTIAL (" + o.holes + " holes, " + o.closed + " subgoals closed): not a finished proof\n" + o.partial : "(no partial)")); }
      console.error("[gen2] " + (o.ok ? "PROVEN " : "open   ") + shortOf(k) + " (" + Math.round(o.ms) + " ms)");
      continue;
    }
    const r = proveHoles(k, BUDGET, false);
    holes += r.n;
    proven += r.done;
    if (r.done > 0) newBody.set(k, r.body);
    for (const h of r.res) {
      if (h.partial) partials++;
      report.push("== " + shortOf(k) + " (" + where + ") hole " + h.hole + ": " + (h.ok ? "PROVEN in " + h.ms + " ms\n" + h.text : "OPEN: " + h.text + (h.partial ? "\n" + h.partial : "")));
    }
    console.error("[gen2] " + r.done + "/" + r.n + " holes of " + shortOf(k));
  }
  // the patch: each file with its proven bodies replaced, diffed against the file
  let root = TOP;
  while (root !== "/" && !fs.existsSync(path.join(root, ".git"))) root = path.dirname(root);
  const byFile = new Map<string, [Src, string][]>();
  for (const [k, b] of newBody) { const ds = defSrc(k)!; if (!byFile.has(ds.file)) byFile.set(ds.file, []); byFile.get(ds.file)!.push([ds, b]); }
  let patch = "";
  for (const [file, edits] of byFile) {
    const lines = fileText(file).split("\n");
    edits.sort((a, b) => b[0].bodyLine - a[0].bodyLine);
    for (const [ds, b] of edits) lines.splice(ds.bodyLine, ds.body.split("\n").length, ...b.split("\n"));
    if (file === entry) for (const imp of autoImports) {
      if (!edits.some(([, body]) => body.includes(imp.alias + "."))) continue;
      const relative = path.relative(TOP, imp.file);
      const line = "import ./" + relative + " as " + imp.alias;
      if (!lines.includes(line)) lines.splice(lines.findLastIndex((l) => l.startsWith("import ")) + 1, 0, line);
    }
    const tmp = path.join(dir, "new-" + path.basename(file));
    fs.writeFileSync(tmp, lines.join("\n"));
    const rel = path.relative(root, file);
    const d = Bun.spawnSync(["diff", "-u", "--label", "a/" + rel, "--label", "b/" + rel, file, tmp]);
    patch += d.stdout.toString();
    fs.unlinkSync(tmp);
  }
  fs.writeFileSync(path.join(dir, "gen2.patch"), patch);
  const head = "gen2 batch " + FILE + ": " + proven + "/" + holes + " holes proven, " + partials + " partials, " + todo.length + " defs, " + ((performance.now() - t0) / 1000).toFixed(1) + " s (budget " + BUDGET + " ms per hole)";
  fs.writeFileSync(path.join(dir, "report.txt"), head + "\n\n" + report.join("\n\n") + "\n");
  console.log(head + "\nreport: " + path.join(dir, "report.txt") + "\npatch:  " + path.join(dir, "gen2.patch") + " (apply from the repository root: git apply)");
};

// ---- prove ----
class Exit { constructor(readonly code: number) {} }
const runProve = () => {
  // the defs: the names after the file (options excluded), and with --only RE every def of the file
  // whose body is exactly ?TODO and whose name matches; the book is loaded once for all of them
  const names = argv.slice(2).filter((a, i, xs) => !a.startsWith("--") && !(i > 0 && xs[i - 1].startsWith("--") && !["--partial", "--stream", "--debug", "--whole", "--no-decomp"].includes(xs[i - 1])));
  const entryDefs = new Set(book.order.slice(N0));
  const own = (x: string) => entryDefs.has(x) && RAW[x].$ === "Def" && !(RAW[x] as B.Def).b;
  const ks: string[] = [];
  for (const nm of names) {
    const k = Object.keys(RAW).find((x) => own(x) && shortOf(x) === nm);
    if (!k) { console.error("gen2: no def " + nm + " in " + FILE); { throw new Exit(1); }; }
    ks.push(k);
  }
  if (argv.includes("--only")) {
    const re = new RegExp(opt("only", ".*"));
    for (const k of book.order) if (own(k) && re.test(shortOf(k)) && !ks.includes(k) && defSrc(k)?.body.trim() === "?TODO") ks.push(k);
  }
  if (ks.length === 0) { console.error("gen2: no def to prove"); { throw new Exit(1); }; }
  let failed = 0;
  for (const k of ks) {
    const ds = defSrc(k);
    if (!ds) { console.error("gen2: no source for " + k); failed++; continue; }
    if (ks.length > 1) console.log("# " + shortOf(k));
    if (ds.body.trim() === "?TODO" || flag("whole")) {
      const def = RAW[k] as B.Def;
      RAW[k] = { ...def, v: null };
      let o: Outcome;
      try { o = proveDef(k, BUDGET); } finally { RAW[k] = def; }
      if (o.ok) {
        console.log(o.text);
        for (const imp of autoImports) if (o.text?.includes(imp.alias + ".")) console.error("[gen2] add import ./" + path.relative(TOP, imp.file) + " as " + imp.alias);
        console.error("[gen2] " + shortOf(k) + ": proven in " + Math.round(o.ms) + " ms [" + o.tags.join(" ") + "]");
      }
      else {
        failed++;
        console.error("[gen2] " + shortOf(k) + ": no proof (" + Math.round(o.ms) + " ms" + (o.why ? ", " + o.why : "") + ")");
        console.log(o.partial ? "# PARTIAL (" + o.holes + " holes, " + o.closed + " subgoals closed): not a finished proof\n" + o.partial : "# NO PROOF");
      }
    } else {
      const r = proveHoles(k, BUDGET);
      console.log(r.body);
      if (r.done < r.n) failed++;
      console.error("[gen2] " + shortOf(k) + ": " + r.done + "/" + r.n + " holes filled");
    }
  }
  if (failed) throw new Exit(2);
};

// ---- serve: the book stays loaded between prove calls ----
// gen2.ts serve <file.bend> [--port 7311]; then `gen2.ts ask [--port N] <def> ... [options]` (the
// arguments of prove after the file). Before each call the entry file is re-read if it changed: its
// defs are re-parsed and re-checked on top of the imports, which stay loaded and checked; a change
// in an imported file needs a restart.
const entryAl = (() => { for (const k of book.order.slice(N0)) { const f = sourceFiles.get(k); if (f) return f.al; } return {} as Record<string, string>; })();
let entryMtime = fs.statSync(entry).mtimeMs;
const reloadEntry = (): string | null => {
  const mt = fs.statSync(entry).mtimeMs;
  if (mt === entryMtime) return null;
  const t0 = performance.now();
  const lines = fs.readFileSync(entry, "utf8").split("\n");
  for (let i = 0; i < lines.length; i++) { const l = lines[i].trim(); if (l === "" || l.startsWith("#")) continue; if (!/^import(\s|$)/.test(l)) break; lines[i] = ""; }
  const own = new Set(book.order.slice(N0));
  const nb = B.book_nil();
  for (const k of Object.keys(RAW)) if (!own.has(k) && !k.includes("~")) nb.tlds[k] = RAW[k];
  const ownCtrs = new Set<string>();
  for (const k of own) { const t = RAW[k]; if (t?.$ === "ADT") for (const c of t.c) ownCtrs.add(c.k); }
  for (const c of Object.keys(book.ctrs)) if (!ownCtrs.has(c)) nb.ctrs[c] = book.ctrs[c];
  nb.order = book.order.slice(0, N0);
  B.parse_book(nb, path.dirname(entry) + "/", lines.join("\n"), "", entryAl);
  B.book_valid(nb, N0);
  for (const k of Object.keys(RAW)) delete RAW[k];
  Object.assign(RAW, nb.tlds);
  book.ctrs = nb.ctrs; book.order = nb.order; book.tmps = nb.tmps; book.hols = nb.hols;
  ORDER.clear(); book.order.forEach((k, i) => ORDER.set(k, i));
  sourceFiles.clear();
  openBySource.clear();
  for (const k of book.order) {
    const t = RAW[k];
    if (t?.$ === "Def") {
      const f = spanFile(t.v) ?? spanFile(t.T);
      if (f) sourceFiles.set(k, f);
    }
  }
  for (const k of book.order.slice(N0)) {
    const file = sourceFiles.get(k);
    if (file) for (const imp of autoImports) file.al[imp.alias] = imp.ns;
  }
  texts.delete(entry); fileLines.delete(entry); defLines.delete(entry); srcCache.clear(); strictMemo.clear(); matchedMemo.clear();
  buildIndex();
  entryMtime = mt;
  return "[gen2] reloaded " + path.basename(entry) + " in " + Math.round(performance.now() - t0) + " ms";
};
const serve = () => {
  const port = +opt("port", "7311");
  Bun.serve({
    port, hostname: "127.0.0.1",
    async fetch(req) {
      const { args } = (await req.json()) as { args: string[] };
      const out: string[] = [], err: string[] = [];
      const ol = console.log, oe = console.error;
      console.log = (...a: any[]) => { out.push(a.join(" ")); };
      console.error = (...a: any[]) => { err.push(a.join(" ")); };
      let code = 0;
      const t0 = performance.now();
      try {
        const r = reloadEntry();
        if (r) err.push(r);
        argv.length = 0; argv.push("prove", FILE, ...args); readOpts();
        runProve();
      } catch (e: any) {
        if (e instanceof Exit) code = e.code;
        else { code = 1; err.push("[gen2] " + (e?.$ === "Err" ? B.err_show(e) : String(e?.stack ?? e))); entryMtime = 0; }
      } finally {
        console.log = ol; console.error = oe;
        deadline = Infinity;
      }
      err.push("[gen2] served in " + Math.round(performance.now() - t0) + " ms");
      return Response.json({ stdout: out.length ? out.join("\n") + "\n" : "", stderr: err.join("\n") + "\n", code });
    },
  });
  console.error("[gen2] serving " + FILE + " on 127.0.0.1:" + port + " (book: " + book.order.length + " entries, load " + Math.round(tLoad) + " ms, valid " + Math.round(tValid - tLoad) + " ms); ask with: gen2.ts ask [--port " + port + "] <def> ... [options]");
};

// ---- main ----
if (MODE === "bench") {
  bench();
} else if (MODE === "batch") {
  batch();
} else if (MODE === "prove") {
  try { runProve(); } catch (e) { if (e instanceof Exit) process.exit(e.code); throw e; }
} else if (MODE === "serve") {
  serve();
} else {
  console.error("usage: bun gen2.ts prove <file.bend> <def> | batch <file.bend> | bench <file.bend> [options] (see the header)");
  process.exit(1);
}
