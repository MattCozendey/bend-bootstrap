// gen2.ts: a general, fast, deliberately incomplete prover for Bend2 proof holes.
// ================================================================================
//
// Dev tool, OUTSIDE the trust: bend2 checks each candidate in-process, and the kernel (the gate,
// ~/lead/gate.sh) is the only judge of what it writes. Exempt from review sweeps (AGENTS.md 2.1.3)
// and from the TypeScript rules of 2.5, by the owner's explicit decision: it is a dev tool outside the
// trust that must only help and be fast (as src/Compiler/Machine/scripts/gen.ts). Excluded in
// tsconfig.json for the same reason.
//
// STATUS: v1 (see the report bb-wt/reports/gen2.md for the log and numbers).
//
// PURPOSE
// -------
// Given a .bend file and a def to prove (its whole body, or the ?TODO holes in its body), write a
// proof that bend2 accepts, or give up fast. Partial proofs (a skeleton whose open subgoals are
// ?TODO, each with its goal and context printed) are suggestions for the agent that owns the proof:
// never commit a partial as a finished proof.
//
// RUN (bun; in WSL through ~/lead/heavy.sh, as every bend2 load):
//   bun src/Shared/scripts/gen2.ts prove <file.bend> <def> [options]
//       prove <def> of <file.bend> (a def of the file itself): when its body is exactly ?TODO, the
//       whole body (case splits allowed); otherwise each ?TODO in its body (leaf tactics only).
//       Prints the proof text (ready to paste) on stdout; progress on stderr.
//   bun src/Shared/scripts/gen2.ts bench <file.bend> [options]
//       benchmark: for each proven lemma of <file.bend> (in book order), forget its body, re-prove it
//       with only the defs before it, and report hit rate by size, time and tactics.
//   options:
//       --budget MS    time budget per def (default 4000)
//       --splits N     max case-split depth (default 3)
//       --depth N      max leaf depth: nesting of apply/premise (default 3)
//       --rw N         max rewrites in a chain (default 4)
//       --beam N       rewrite candidates explored per goal (default 4)
//       --fuel N       def lookups allowed per single check (default 300000)
//       --partial      on failure, print the best partial proof (holes with goals)
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
//      kernel rule R3); a hypothesis that equates two different constructors uses an ex-falso lemma
//      (conclusion: its own type parameter), its premise proven at depth 1.
//   4. apply: hypotheses (functions), the induction hypothesis, indexed lemmas (nearest first);
//      premises proven recursively at depth - 1.
//   5. rewrite: `%e : P; rest` with an equation from a hypothesis (both directions, Equal.sym), the
//      induction hypothesis or an indexed lemma whose side matches a subterm of nf(goal); P is
//      nf(goal) with that subterm replaced by `_` (kernel rule R2: rewrite, do not convert). Rewrites
//      of blocking subterms first; a rewrite that closes by {==} wins at once; else the best --beam
//      continue with one less rewrite.
//
// OUTPUT
// ------
// * full proof: the body text on stdout, indented as a def body (two spaces), checked by def_check.
// * partial (--partial): the best skeleton (fewest holes, then most closed subgoals) with ?TODO holes,
//   then for each hole its case path, goal and context (raw and normal form).
// * streaming (--stream): each closed subgoal (its case path and first line) on stderr.
//
// BENCHMARK (latest numbers: see bb-wt/reports/gen2.md)
//
// LIMITS (v1)
// -----------
// * No helper-lemma synthesis (a match on a computed value or an introduced binder needs its own def).
// * Splits only in whole-body mode; ?TODO holes inside a body get leaf tactics only.
// * No lets (`+x = ...`) in output, no congruence tactic beyond rewriting, no templates (~ binders).
// * Matching is syntactic (after the bounded normal form): a lemma stated in a shape that only
//   converts to the goal by deeper computation is missed.
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
const opt = (k: string, d: string) => { const i = argv.indexOf("--" + k); return i >= 0 ? argv[i + 1] : d; };
const flag = (k: string) => argv.includes("--" + k);
const MODE = argv[0], FILE = argv[1], TARGET = argv[2];
const BUDGET = +opt("budget", "4000");
const MAX_SPLIT = +opt("splits", "3");
const MAX_DEPTH = +opt("depth", "3");
const MAX_RW = +opt("rw", "4");
const BEAM = +opt("beam", "4");
const FUEL_CHECK = +opt("fuel", "300000");
const FUEL_NF = 100000;
const FUEL_FINAL = 50000000;
const NF_NODES = 3000;
const MAX_CANDS = 48;
const MAX_SPLIT_CANDS = 3;
const PARTIAL = flag("partial"), STREAM = flag("stream"), DEBUG = flag("debug");
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

// ---- load ----
const entry = fs.realpathSync(path.resolve(FILE ?? ""));
const TOP = path.dirname(entry) + "/";
const book = B.book_nil();
await B.book_load(book, entry, "", new Map());
const tLoad = performance.now();
try {
  B.book_valid(book, 0);
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
const nsOf = (k: string) => (k.includes(":") ? k.slice(0, k.indexOf(":")) : "");
const shortOf = (k: string) => (k.includes(":") ? k.slice(k.indexOf(":") + 1) : k);
const pathOf = (k: string) => (nsOf(k) === "" ? entry : path.resolve(TOP, nsOf(k) + ".bend"));
const esc = (s: string) => s.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
const srcCache = new Map<string, Src | null>();
const defSrc = (k: string): Src | null => {
  if (srcCache.has(k)) return srcCache.get(k)!;
  let res: Src | null = null;
  const file = pathOf(k);
  if (fs.existsSync(file)) {
    const lines = fileText(file).split("\n");
    const re = new RegExp("^(@unsafe\\s+)?def\\s+" + esc(shortOf(k)) + "\\??\\(");
    const li = lines.findIndex((l) => re.test(l));
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

// checks <def> with the body text <body> (a def body, indented); throws bend2's Err on failure
const checkDef = (k: string, body: string) => {
  const ds = defSrc(k)!;
  const def = RAW[k] as B.Def;
  const file = spanFile(def.T)!;
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
const size = (t: LTerm): number => {
  switch (t.$) {
    case "App": return 1 + size(t.f) + size(t.x);
    case "Ctr": case "ADT": return 1 + t.x.reduce((a, x) => a + size(x), 0);
    case "Eql": return 1 + size(t.a) + size(t.b);
    case "All": return 1 + size(t.A) + size(t.B as LTerm);
    case "Lam": return 1 + size(t.f as LTerm);
    default: return 1;
  }
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
// subterms that block evaluation: the strict argument of a stuck call, when a variable or a stuck call
const blockers = (t: LTerm, out: LTerm[]) => {
  switch (t.$) {
    case "App": {
      const [h, xs] = unapply(t);
      if (h.$ === "Ref") {
        const j = strictOf(h.k);
        if (j !== null && j < xs.length) { const a = xs[j]; if (a.$ === "Var" || (a.$ === "App" && unapply(a)[0].$ === "Ref")) out.push(a); }
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
const tIndex0 = performance.now();
for (const k of Object.keys(RAW)) {
  const t = RAW[k];
  if (t.$ !== "Def" || (t.v === null && t.b !== true) || t.x > 0 || t.i) continue;
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
  if (c.$ === "Eql") {
    for (const side of [0, 1] as const) {
      const s = side === 0 ? c.a : c.b;
      const sk = headKey(s);
      if (!sk.startsWith("R:")) continue;
      if (!rwIndex.has(sk)) rwIndex.set(sk, []);
      rwIndex.get(sk)!.push({ L, side });
    }
  }
}
for (const m of [applyIndex]) for (const v of m.values()) v.sort((a, b) => b.order - a.order);
for (const v of rwIndex.values()) v.sort((a, b) => b.L.order - a.L.order);
wild.sort((a, b) => b.order - a.order);
const tIndex = performance.now() - tIndex0;

// ---- proofs ----
type Pf =
  | { t: "tm"; s: string }
  | { t: "rw"; e: string; P: string; k: Pf }
  | { t: "mt"; x: string; arms: { pat: string; k: Pf }[] }
  | { t: "hole"; g: Goal };
const inline = (p: Pf): string => {
  switch (p.t) {
    case "tm": return p.s;
    case "rw": return "(%" + p.e + " : " + p.P + "; " + inline(p.k) + ")";
    case "hole": return "?TODO";
    case "mt": throw new Error("a match cannot be inlined");
  }
};
const flat = (p: Pf): string => (p.t === "rw" ? "%" + p.e + " : " + p.P + "; " + flat(p.k) : inline(p));
const render = (p: Pf, ind: string, out: string[]) => {
  switch (p.t) {
    case "tm": out.push(ind + p.s); break;
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
  return out;
};

// ---- goals ----
type Goal = {
  ctx: B.Ctx; d: number; ty: HTerm; lhs: B.LHS; qt: B.Quant; env: B.Env;
  names: string[]; ckey: string;
  pend: number; pnames: string[]; pmany: boolean[];
  split: boolean; path: string;
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
const applyCallee = (g: Goal, c: Callee, targets: LTerm[], depth: number, rw: number, path: Set<string>, concl?: (o: LTerm) => LTerm | null): { args: string[]; doms: any[]; sol: (LTerm | null)[] } | null => {
  let sol: (LTerm | null)[] = new Array(c.n).fill(null);
  const toH = (s: (LTerm | null)[]) => s.map((x) => (x ? B.term_higher(x, g.env) : null));
  const o = openMeta(c.T, c.n);
  if (!o) return null;
  const pc0 = attempt(FUEL_NF, () => lower(o.concl, g.d));
  if (!pc0) return null;
  const pc = concl ? concl(pc0) : pc0;
  if (!pc) return null;
  let ok = false;
  for (const t of targets) {
    const s2 = sol.slice();
    if (match(pc, t, s2, g.d)) { sol = s2; ok = true; break; }
  }
  if (!ok) return null;
  let o2 = openMeta(c.T, c.n, toH(sol));
  if (!o2) return null;
  const prem: boolean[] = o2.doms.map((dm, j) => !sol[j] && isProp(dm.A));
  const viaHyp: (string | null)[] = new Array(c.n).fill(null);
  // parameters not fixed by the conclusion: from premises that match hypotheses
  for (let iter = 0; iter < 3 && sol.some((s, j) => !s && !prem[j]); iter++) {
    let progress = false;
    for (let j = 0; j < c.n; j++) {
      if (!prem[j] || viaHyp[j]) continue;
      const A = attempt(FUEL_NF, () => lower(o2!.doms[j].A, g.d));
      if (!A || !hasMeta(A)) continue;
      const qt = B.quant_dem(o2.doms[j].q, g.qt);
      for (let i = g.d - 1; i >= 0 && !viaHyp[j]; i--) {
        if (!usable(g, i, qt)) continue;
        for (const ht of hypTargets(g, i)) {
          const s2 = sol.slice();
          if (match(A, ht, s2, g.d)) { sol = s2; viaHyp[j] = g.names[i]; progress = true; break; }
        }
      }
    }
    if (!progress) break;
    o2 = openMeta(c.T, c.n, toH(sol));
    if (!o2) return null;
  }
  if (sol.some((s, j) => !s && !prem[j])) return null;
  const args: string[] = [];
  for (let j = 0; j < c.n; j++) {
    if (sol[j]) { args.push(show(sol[j]!, g.names)); continue; }
    if (viaHyp[j]) { args.push(viaHyp[j]!); continue; }
    const sg: Goal = { ...g, ty: o2.doms[j].A, qt: B.quant_dem(o2.doms[j].q, g.qt) };
    const pf = leaf(sg, Math.max(0, depth - 1), rw, path);
    if (!pf) return null;
    args.push(inline(pf));
  }
  return { args, doms: o2.doms, sol };
};
const callText = (c: Callee, args: string[]) => (c.n === 0 ? c.text : c.text + "(" + args.join(", ") + ")");

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
  out.sort(() => 0);
  return out.slice(0, MAX_CANDS);
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
  const m = job.memo.get(gk);
  if (m) {
    if (m.pf) return m.pf;
    if (m.depth >= depth && m.rw >= rw) return null;
  }
  const p2 = new Set(path);
  p2.add(gk);
  const r = leafGo(g, depth, rw, p2);
  if (r) job.memo.set(gk, { pf: r, depth, rw });
  else if (!m || m.depth < depth || m.rw < rw) job.memo.set(gk, { pf: null, depth: Math.max(depth, m?.depth ?? 0), rw: Math.max(rw, m?.rw ?? 0) });
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
  if (contradictory(g).length > 0) {
    for (const L of wild) {
      if (L.order >= job.order || L.k === job.k) continue;
      const c: Callee = { text: B.name_show(job.file, L.k), T: (RAW[L.k] as B.Def).T, n: L.n, kind: "lemma" };
      const a = applyCallee(g, c, [raw], 1, 0, path);
      if (!a) continue;
      const s = callText(c, a.args);
      if (tryText(g, s)) { tag("exfalso"); return tm(s); }
    }
  }
  if (depth === 0 && rw === 0) return null;
  const n = attempt(FUEL_NF * 2, () => nf(g.ty, g.d));
  const targets = n && key(n) !== key(raw) ? [raw, n] : [raw];
  // 4. apply
  if (depth > 0) {
    const callees: Callee[] = [];
    for (let i = g.d - 1; i >= 0; i--) {
      if (!usable(g, i, g.qt)) continue;
      const a = ann(g, i)!;
      let t = B.term_strip(a.T), k = 0;
      while (t.$ === "All" && k < 12) { t = B.term_strip(t.B(B.Var("_", 1e7 + k))); k++; }
      if (k > 0) callees.push({ text: g.names[i], T: a.T, n: k, kind: "hyp" });
    }
    if (job.ih && g.split) callees.push(ihCallee());
    callees.push(...lemmaCands(g, targets));
    for (const c of callees) {
      if (performance.now() > deadline) throw TIMEOUT;
      const a = applyCallee(g, c, targets, depth, rw, path);
      if (!a) continue;
      const s = callText(c, a.args);
      if (tryText(g, s)) { tag("apply:" + c.kind); return tm(s); }
    }
  }
  // 5. rewrite
  if (rw > 0) {
    const r = rewrite(g, depth, rw, path);
    if (r) return r;
  }
  return null;
};

type RwCand = { from: LTerm; to: LTerm; e: string; kind: string; score: number };
const rewrite = (g: Goal, depth: number, rw: number, path: Set<string>): Pf | null => {
  const N = attempt(FUEL_NF * 2, () => nf(g.ty, g.d + 1));
  if (!N || size(N) > 600) return null;
  const subs = new Map<string, LTerm>();
  subterms(N, subs);
  const blk: LTerm[] = [];
  blockers(N, blk);
  const blkKeys = new Set(blk.map(key));
  const cands: RwCand[] = [];
  const okFrom = (t: LTerm) => t.$ === "Var" || t.$ === "App" || (t.$ === "Ctr" && t.x.length > 0);
  // hypotheses
  for (let i = g.d - 1; i >= 0; i--) {
    if (!usable(g, i, g.qt)) continue;
    const ts = hypTargets(g, i);
    for (const E of ts) {
      if (E.$ !== "Eql") continue;
      const ka = key(E.a), kb = key(E.b);
      if (ka === kb) continue;
      if (subs.has(kb) && okFrom(E.b)) cands.push({ from: E.b, to: E.a, e: g.names[i], kind: "rw:hyp", score: blkKeys.has(kb) ? 0 : 1 });
      if (subs.has(ka) && okFrom(E.a)) cands.push({ from: E.a, to: E.b, e: "Equal.sym(" + show(E.T, g.names) + ", " + show(E.a, g.names) + ", " + show(E.b, g.names) + ", " + g.names[i] + ")", kind: "rw:hyp", score: blkKeys.has(ka) ? 0 : 1 });
      break;
    }
  }
  // the induction hypothesis and lemmas, on the stuck calls of nf(goal)
  for (const [sk, s] of subs) {
    if (s.$ !== "App") continue;
    const [h] = unapply(s);
    if (h.$ !== "Ref") continue;
    const entries: { c: Callee; side: 0 | 1; kind: string }[] = [];
    if (job.ih && g.split) {
      const o = attempt(FUEL_NF, () => { const oo = openMeta(job.def.T, job.def.n); return oo ? lower(oo.concl, g.d + 1) : null; });
      if (o && o.$ === "Eql") for (const side of [0, 1] as const) if (headKey(side === 0 ? o.a : o.b) === "R:" + h.k) entries.push({ c: ihCallee(), side, kind: "rw:ih" });
    }
    for (const { L, side } of rwIndex.get("R:" + h.k) ?? []) {
      if (L.order >= job.order || L.k === job.k) continue;
      entries.push({ c: { text: B.name_show(job.file, L.k), T: (RAW[L.k] as B.Def).T, n: L.n, kind: "lemma" }, side, kind: "rw:lemma" });
      if (entries.length > MAX_CANDS) break;
    }
    for (const { c, side, kind } of entries) {
      if (performance.now() > deadline) throw TIMEOUT;
      const gg: Goal = { ...g, d: g.d + 1 - 1 };
      const a = applyCallee(gg, c, [s], depth, 0, path, (o) => (o.$ === "Eql" ? (side === 0 ? o.a : o.b) : null));
      if (!a) continue;
      const o2 = openMeta(c.T, c.n, a.sol.map((x) => (x ? B.term_higher(x, g.env) : null)));
      if (!o2) continue;
      const E = attempt(FUEL_NF, () => lower(o2.concl, g.d + 1));
      if (!E || E.$ !== "Eql" || hasMeta(E)) continue;
      const call = callText(c, a.args);
      const to = side === 0 ? E.b : E.a;
      if (key(to) === sk) continue;
      const e = side === 0 ? "Equal.sym(" + show(E.T, g.names) + ", " + show(E.a, g.names) + ", " + show(E.b, g.names) + ", " + call + ")" : call;
      cands.push({ from: s, to, e, kind, score: (blkKeys.has(sk) ? 0 : 1) + (kind === "rw:ih" ? 0 : 0.5) });
    }
  }
  cands.sort((a, b) => a.score - b.score);
  const motiveNames = [...g.names, "_"];
  const later: { c: RwCand; P: string; sub: Goal; gk: string }[] = [];
  const seen = new Set<string>();
  for (const c of cands) {
    if (performance.now() > deadline) throw TIMEOUT;
    const fk = key(c.from);
    const Pt = replace(N, fk, B.Var("_", g.d));
    const Gp = replace(N, fk, c.to);
    const gpk = key(Gp);
    if (seen.has(gpk)) continue;
    seen.add(gpk);
    if (!closedBelow(Gp, g.d) && Gp.$ !== "Eql") { /* binders: keep */ }
    const P = show(Pt, motiveNames);
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
  // records (one constructor) are free to open
  if (out.length === 0) {
    let g: Goal | null = n;
    for (let j = 0; j < n.pend && g; j++) {
      const t = wnf(g.ty) as any;
      if (!t || t.$ !== "All") break;
      const A = wnf(t.A) as any;
      if (A?.$ === "ADT" && t.q.$ !== "None") { const a = RAW[A.k]; if (a?.$ === "ADT" && a.c.length === 1 && a.c[0].n > 0) out.push(j); }
      g = intro(g, g.pnames[0], g.pmany[0]);
    }
  }
  return out.slice(0, MAX_SPLIT_CANDS);
};

const solve = (n: Goal, S: number, D: number, partial: boolean): Res => {
  if (performance.now() > deadline) throw TIMEOUT;
  const nk = (attempt(FUEL_NF, () => goalKey(n)) ?? Math.random()) + "#" + n.pnames.join(",") + "#" + S + "," + D + (partial ? "p" : "");
  const m = job.smemo.get(nk);
  if (m) return m;
  const r = solveGo(n, S, D, partial);
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

// ---- jobs ----
const rootGoal = (k: string): Goal => {
  const def = RAW[k] as B.Def;
  const qs = B.tele_unbind(book, def.T).doms.map((dm) => dm[0]);
  const pnames: string[] = [];
  let t = def.T;
  for (let j = 0; j < def.n; j++) { const s = B.term_strip(t) as any; pnames.push(s.k); t = s.B(B.Var(s.k, j)); }
  return {
    ctx: B.ctx_nil(), d: 0, ty: def.T, lhs: { t: B.Ref(k), n: def.n - def.x, def: k, qs, u: def.u }, qt: B.Lone(), env: null,
    names: [], ckey: "", pend: def.n, pnames, pmany: pnames.map(() => false), split: false, path: "", hc: new Map(),
  };
};
const newJob = (k: string): Job => {
  const def = RAW[k] as B.Def;
  return { k, def, order: ORDER.get(k) ?? book.order.length, file: spanFile(def.T)!, short: shortOf(k), tags: new Map(), memo: new Map(), smemo: new Map(), closed: 0, ih: true };
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
  if (!full && PARTIAL) {
    deadline = performance.now() + Math.max(500, budget / 3);
    try { best = solve(root, MAX_SPLIT, MAX_DEPTH, true); } catch (e) { if (e !== TIMEOUT) throw e; }
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
const proveHoles = (k: string, budget: number) => {
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
    if (!err || err.$ !== "Err" || typeof err.exp === "string") { console.error("[gen2] hole " + (h + 1) + ": no goal (" + (err ? B.err_show(err) : "checked") + ")"); continue; }
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
      pend: 0, pnames: [], pmany: [], split: true, path: "hole" + (h + 1), hc: new Map(),
    };
    const t0 = performance.now();
    deadline = t0 + budget;
    let pf: Pf | null = null;
    try {
      for (let dd = 0; dd <= MAX_DEPTH && !pf; dd++) pf = leaf(g, dd, dd === 0 ? 1 : MAX_RW, new Set());
    } catch (e) { if (e !== TIMEOUT) throw e; }
    deadline = Infinity;
    const ms = (performance.now() - t0).toFixed(0);
    if (!pf) { console.error("[gen2] hole " + (h + 1) + ": not found (" + ms + " ms)\n" + showGoal(g)); continue; }
    const line = body.slice(body.lastIndexOf("\n", idx) + 1, idx);
    const ind = /^\s*$/.test(line) ? line : line.replace(/\S.*$/, "").replace(/$/, "  ");
    const out: string[] = [];
    render(pf, ind, out);
    const text = out.join("\n").slice(ind.length);
    const nb = body.slice(0, idx) + text + body.slice(idx + 5);
    const ok = attempt(FUEL_FINAL, () => { checkDef(k, nb); return true; });
    if (!ok) { console.error("[gen2] hole " + (h + 1) + ": candidate failed the def check: " + flat(pf)); continue; }
    body = nb;
    done++;
    console.error("[gen2] hole " + (h + 1) + ": filled (" + ms + " ms)");
  }
  console.log(body);
  console.error("[gen2] " + done + "/" + n + " holes filled");
};

// ---- bench ----
const isLemma = (def: B.Def): boolean => {
  const o = attempt(20000, () => openMeta(def.T, def.n));
  return !!o && attempt(20000, () => isProp(o.concl)) === true && (wnf(o.concl)?.$ !== "ADT" || true);
};
const bench = () => {
  const only = new RegExp(opt("only", ".*"));
  const max = +opt("max", "100000");
  const rows: any[] = [];
  const own = book.order.filter((k, i) => nsOf(k) === "" && ORDER.get(k) === i && RAW[k]?.$ === "Def" && !(RAW[k] as B.Def).b);
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

// ---- main ----
if (MODE === "bench") {
  bench();
} else if (MODE === "prove") {
  const k = Object.keys(RAW).find((x) => nsOf(x) === "" && shortOf(x) === TARGET && RAW[x].$ === "Def" && !(RAW[x] as B.Def).b);
  if (!k) { console.error("gen2: no def " + TARGET + " in " + FILE); process.exit(1); }
  const ds = defSrc(k);
  if (!ds) { console.error("gen2: no source for " + k); process.exit(1); }
  if (ds.body.trim() === "?TODO" || flag("whole")) {
    const def = RAW[k] as B.Def;
    RAW[k] = { ...def, v: null };
    const o = proveDef(k, BUDGET);
    RAW[k] = def;
    if (o.ok) { console.log(o.text); console.error("[gen2] proven in " + Math.round(o.ms) + " ms [" + o.tags.join(" ") + "]"); }
    else {
      console.error("[gen2] no proof (" + Math.round(o.ms) + " ms" + (o.why ? ", " + o.why : "") + ")");
      if (o.partial) { console.log("# PARTIAL (" + o.holes + " holes, " + o.closed + " subgoals closed): not a finished proof\n" + o.partial); }
      process.exit(2);
    }
  } else {
    proveHoles(k, BUDGET);
  }
} else {
  console.error("usage: bun gen2.ts prove <file.bend> <def> [options] | bench <file.bend> [options] (see the header)");
  process.exit(1);
}
