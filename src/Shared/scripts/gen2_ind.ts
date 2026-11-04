// gen2_ind.ts: gen2's induction schemes and helper lemmas (--ind), a dev tool outside the trust like
// gen2.ts (exempt from the review sweeps and the TypeScript rules of AGENTS.md 2.5 for the same reason;
// excluded in tsconfig). Every text it prints passed bend2's def check in gen2's book.
//
// WHAT (a whole body that gen2's own search did not prove; off unless --ind):
// * schemes: a skeleton TEXT with ?TODO arms, checked by bend2 (each arm's goal read from bend2's
//   error at a marked hole); each arm is closed by gen2's leaf tactics (with the induction
//   hypothesis), else by a helper lemma (below). Schemes, in order:
//   - enum: a Nat parameter bounded by a hypothesis {Nat.is_le(x, c) == True} (or is_lt), c <= 8:
//     every value and the rest (refuted by the hypothesis), jointly with the other parameters that
//     block the goal (a record such as Cir.Cell: its constructor);
//   - u32: the U32 parameters destructured (U32{w}); a goal over words of width 32n is the instance
//     at 32n of a helper over any width n (Equal.cong(Word(32n), U32, w => U32{w}, ..) for a U32
//     equation): the classic generalization before induction;
//   - word: a statement over n: Nat and words of width n: match n, then the words (WCon{h, t}),
//     then their head bits;
//   - nat: a Nat parameter that blocks the goal: 0n and 1n+p;
//   - fun: the case tree of a recursive def that the goal calls on parameters (functional
//     induction: List.get(xs, n) gives match xs n with its three cases).
// * helpers for an arm that the leaf tactics do not close (depth <= MAX_DEPTH, each proven by the
//   same schemes before it is used; only proven helpers are printed): the arm's goal over its
//   context (true iff the arm is); the goal after the induction hypothesis rewrote it, with the
//   stuck calls common to both sides generalized to variables (U32.shrn(a, p) -> y); the goal with
//   those generalized directly. A generalization can be false: then its proof fails and nothing is
//   printed.
// * leaf (inside gen2's search): a constructor clash in a hypothesis {None == Some{c}} closes any
//   goal, through a predicate def with type parameters (maybe.T(A, _)).
// * splits (inside gen2's search): a parameter of an enumeration type (Bool) that only a hypothesis
//   names is a split candidate (bool.case).
//
// BOUNDS: the caller's budget (each helper a slice), at most MAX_ARMS arms per skeleton, MAX_DEPTH
// nested helpers, MAX_HELPERS per def. Never throws past gen2's catch; an internal failure is one line.

import * as B from "../../../bend/bend2/bend.ts";

type HTerm = B.HTerm;
type LTerm = B.LTerm;

// ---- types ----
export type IndOut = { text: string; helpers: string[]; open: number; closed: number; report: string; ms: number } | null;
type Api = any;
type Goal = any;
type Run = { A: Api; k: string; until: number; helpers: { order: number; text: string }[]; notes: string[]; used: Set<string>; nHelpers: number; failed: Set<string>; proven: Map<string, string> };
type Fill = { body: string; open: number; closed: number; goals: string[] };
type Scheme = { name: string; body: string };

// ---- constants ----
const MAX_ARMS = 64;
const MAX_DEPTH = 3;
const MAX_HELPERS = 16;
const ENUM_MAX = 8;
const ARM_MS = 300;
const IND_FLOOR_MS = 2500; // the schemes get at least this (a def with helpers needs 0.5-2 s)
const MAX_HELPER_ARMS = 16; // arms left after the leaf pass that may each get a helper
const NL = String.fromCharCode(10);
// which skeleton gets the helpers: the most specific split first (the functions' own recursion)
const SCHEME_RANK = ["enum", "u32+width", "word+split", "fun", "word", "nat", "u32"];
const ONLY = process.env.GEN2_IND_ONLY ? new RegExp(process.env.GEN2_IND_ONLY) : null; // debug: schemes by name

// ---- small helpers ----
const tele = (A: Api, k: string) => {
  // the parameters of def k: names, quantities, types (as text in k's file), and the conclusion's text
  const g0 = A.rootGoal(k);
  const g = A.introAll(g0);
  if (!g) return null;
  const ps: { name: string; q: string; ty: string; T: HTerm; i: number }[] = [];
  for (let i = 0; i < g.d; i++) {
    const a = A.ann(g, i);
    const ty = A.attempt(A.FUEL_NF, () => A.show(A.lower(a.T, i), g.names.slice(0, i)));
    if (ty === undefined) return null;
    ps.push({ name: g.names[i], q: B.quant_show(a.q), ty, T: a.T, i });
  }
  return { g, ps };
};
const adtOf = (A: Api, g: Goal, T: HTerm): any => {
  const w = A.wnf(T);
  if (!w || w.$ !== "ADT") return null;
  const t = A.RAW[w.k];
  return t?.$ === "ADT" ? t : null;
};
const isWord = (ty: string) => /^Word\(/.test(ty);
const ctrPat = (A: Api, k: string, ctr: any, base: string, used: Set<string>): string => {
  const job = A.job();
  const cn = B.name_show(job.file, ctr.k);
  const fs: string[] = [];
  for (let i = 0; i < ctr.n; i++) fs.push(A.fresh(base + i, used));
  return cn + "{" + fs.join(", ") + "}";
};
const indent = (s: string, ind: string) => s.split("\n").map((l) => (l.trim() === "" ? l : ind + l)).join("\n");
// the cartesian product of case lists
const product = (xs: string[][]): string[][] => xs.reduce<string[][]>((acc, c) => acc.flatMap((a) => c.map((x) => [...a, x])), [[]]);
const matchText = (scruts: string[], cases: string[][], arm: (i: number) => string): string =>
  "match " + scruts.join(" ") + ":\n" + cases.map((c, i) => "  case " + c.join(" ") + ":\n" + indent(arm(i), "    ")).join("\n");
const freeVars = (t: LTerm, out: Set<number>) => {
  const st: LTerm[] = [t];
  while (st.length) {
    const x: any = st.pop();
    switch (x.$) {
      case "Var": if (x.i < (1 << 20)) out.add(x.i); break;
      case "App": st.push(x.f, x.x); break;
      case "Ctr": case "ADT": st.push(...x.x); break;
      case "Eql": st.push(x.a, x.b, x.T); break;
      case "All": st.push(x.A, x.B); break;
      case "Lam": st.push(x.f); break;
    }
  }
};

// ---- arms: fill the ?TODO of a skeleton ----
// the def check of k with body; for each ?TODO in order: its goal (the hole marked), the leaf tactics,
// then a helper; returns the body with the closed arms filled
const fillArms = (R: Run, k: string, body: string, depth: number, passes = [0, 1]): Fill | null => {
  const { A } = R;
  const e0 = A.checkBody(k, body);
  if (e0) { if (A.debug()) console.error("[gen2] --ind: skeleton of " + A.shortOf(k) + " does not check: " + A.errText(e0).split(NL).slice(0, 6).join(" | ")); return null; }
  const n = (body.match(/\?TODO/g) ?? []).length;
  if (n === 0) return { body, open: 0, closed: 0, goals: [] };
  if (n > MAX_ARMS) return null;
  let text = body, closed = 0;
  // pass 0: the leaf tactics on every arm; pass 1: a helper for each arm left (when few are left)
  let goals: string[] = [];
  for (const pass of passes) {
    const left = (text.match(/\?TODO/g) ?? []).length;
    if (left === 0 || (pass === 1 && (depth >= MAX_DEPTH || left > MAX_HELPER_ARMS))) break;
    goals = [];
    let pos = 0;
    for (let i = 0; i < left; i++) {
      const at = text.indexOf("?TODO", pos);
      if (at < 0) break;
      const err = A.checkBody(k, text.slice(0, at) + "?gen2hole" + text.slice(at + 5));
      const g = typeof err === "object" ? A.holeGoal(k, err, "ind" + (i + 1)) : null;
      let fill: string | null = null;
      const fits = (f: string | null): f is string => f !== null && A.checkBody(k, text.slice(0, at) + f + text.slice(at + 5)) === null;
      if (g && A.now() < R.until) {
        fill = pass === 0 ? A.leafText(k, g, Math.min(ARM_MS, R.until - A.now())) : armHelper(R, k, g, depth, fits);
        if (!fits(fill)) fill = null;
      }
      if (pass === 1 && A.debug()) console.error("[gen2] --ind: " + A.shortOf(k) + " arm " + (i + 1) + ": " + (g ? (fill ? "closed" : "open") : "no goal: " + (err ? A.errText(err).split(NL).slice(0, 3).join(" | ") : "checks")));
      if (fill !== null) {
        text = text.slice(0, at) + fill + text.slice(at + 5);
        pos = at + fill.length;
        closed++;
        continue;
      }
      goals.push(g ? A.attempt(A.FUEL_NF, () => A.show(A.lower(g.ty, g.d), g.names)) ?? "?" : "?");
      pos = at + 5;
    }
  }
  return { body: text, open: (text.match(/\?TODO/g) ?? []).length, closed, goals };
};

// ---- helpers ----
// prove a new lemma (head: its `def name(..) -> concl:` text) for k's file: gen2's search, then the
// schemes; on success it stays in the book as a lemma and its text is kept for the output
const proveHelper = (R: Run, head: string, depth: number): string | null => {
  const { A } = R;
  const stmt = head.replace(/^def\s+[A-Za-z0-9_.]+\(/, "(");
  if (R.failed.has(stmt)) return null;
  const had = R.proven.get(stmt);
  if (had) return had;
  if (R.nHelpers >= MAX_HELPERS || A.now() > R.until) return null;
  const name = /^def\s+([A-Za-z0-9_.]+)\(/.exec(head)?.[1];
  if (!name) return null;
  const hk = A.addTemp(R.k, head, "  ?TODO", false);
  if (A.debug()) console.error("[gen2] --ind: helper " + (hk ? "" : "(does not parse) ") + head.replace(/\s+/g, " ").slice(0, 300));
  if (!hk) return null;
  const order = A.ORDER.get(hk);
  if (A.attempt(A.FUEL_FINAL, () => A.stmtOk(hk)) !== true) { if (A.debug()) console.error("[gen2] --ind: its statement does not check"); A.dropTemp(hk); return null; }
  let body: string | null = null;
  const until0 = R.until;
  try {
    const rem = R.until - A.now();
    body = A.proveQuick(hk, Math.max(150, Math.min(A.budget() / 4, rem / 4)));
    if (!body) {
      R.until = A.now() + Math.max(200, (R.until - A.now()) / 2);
      const r = schemesProve(R, hk, depth + 1);
      if (r && r.open === 0) body = r.body;
    }
  } finally { A.dropTemp(hk); R.until = until0; }
  if (!body) { R.failed.add(stmt); return null; }
  const hk2 = A.addTemp(R.k, head, body, true, order);
  if (!hk2 || A.checkBody(hk2, body) !== null) { if (hk2) A.dropTemp(hk2); return null; }
  R.nHelpers++;
  R.proven.set(stmt, name);
  R.helpers.push({ order, text: "# gen2 --ind: a helper lemma (proven)\n" + head + "\n" + body + "\n" });
  return name;
};
const newName = (R: Run): string => R.A.helperName(R.k, R.used, "i");
// a statement over the context of g: the parameters that the goal (or a kept parameter's type) names
const ctxParams = (A: Api, g: Goal, goalT: LTerm, rename: (s: string) => string, skip: Set<number> = new Set()): { params: string[]; args: string[] } | null => {
  const need = new Set<number>();
  freeVars(goalT, need);
  for (let i = g.d - 1; i >= 0; i--) if (need.has(i)) { const a = A.ann(g, i); freeVars(A.lower(a.T, i), need); }
  // the facts (equations) of the context over those parameters stay premises (the statement is no stronger)
  for (let i = 0; i < g.d; i++) {
    if (need.has(i) || skip.has(i)) continue;
    const T = A.attempt(A.FUEL_NF, () => A.lower(A.ann(g, i).T, i));
    if (!T || T.$ !== "Eql") continue;
    const fv = new Set<number>();
    freeVars(T, fv);
    if ([...fv].every((v) => need.has(v))) need.add(i);
  }
  const names = g.names.slice(0, g.d);
  if (new Set(names).size !== names.length) return null;
  const params: string[] = [], args: string[] = [];
  for (let i = 0; i < g.d; i++) {
    if (!need.has(i) || skip.has(i)) continue;
    const a = A.ann(g, i);
    const T = A.attempt(A.FUEL_NF, () => A.show(A.lower(a.T, i), names.slice(0, i)));
    if (T === undefined || names[i] === "_") return null;
    params.push(B.quant_show(a.q) + names[i] + ": " + rename(T));
    args.push(names[i]);
  }
  return { params, args };
};
// an arm the leaf tactics did not close: a helper (its goal rewritten by the induction hypothesis,
// with the common stuck calls generalized; generalized directly; the arm's goal over its context)
const armHelper = (R: Run, k: string, g: Goal, depth: number, fits: (f: string | null) => boolean): string | null => {
  const { A } = R;
  const raw = A.attempt(A.FUEL_NF, () => A.lower(g.ty, g.d));
  if (!raw || A.attempt(A.FUEL_NF, () => hasMetaOrHole(raw)) !== false) return null;
  const N = A.attempt(A.FUEL_NF * 2, () => A.nf(g.ty, g.d));
  const left = () => Math.min(ARM_MS, R.until - A.now());
  if (R.nHelpers > 0) { const lf = A.leafText(k, g, left()); if (fits(lf)) return lf; }
  const cands: { t: LTerm; rw?: IhRw }[] = [];
  if (N && N.$ === "Eql") {
    for (const [dir, useNf] of [[0, false], [1, false], [0, true], [1, true]] as [number, boolean][]) {
      const rw = A.attempt(A.FUEL_NF * 2, () => ihRewrite(A, k, g, N, dir, useNf));
      if (!rw) continue;
      // the rewritten goal is closed by computation
      const t = rw.t as any;
      if (t.$ === "Eql" && A.key(t.a) === A.key(t.b)) { const txt = "(%" + rw.e + " : " + rw.P + "; {==})"; if (A.tryText(g, txt) && fits(txt)) return txt; if (A.debug()) console.error("[gen2] --ind: the closed rewrite does not check: " + txt.slice(0, 400)); }
      cands.push({ t: rw.t, rw });
    }
    cands.push({ t: N });
    const seen = new Set<string>();
    for (const [c, enums] of cands.flatMap((c) => (c.rw ? [[c, false], [c, true]] : [[c, true], [c, false]]) as [{ t: LTerm; rw?: IhRw }, boolean][])) {
      if (A.now() > R.until) return null;
      const gen = A.attempt(A.FUEL_NF * 2, () => generalize(A, g, c.t, enums));
      if (A.debug()) console.error("[gen2] --ind: arm " + g.path + (c.rw ? " (IH rewritten)" : "") + (enums ? " enums" : "") + ": " + (gen ? gen.goal.slice(0, 200) : "no generalization"));
      if (!gen || seen.has(gen.goal)) continue;
      seen.add(gen.goal);
      const nm = proveHelper(R, "def " + newName(R) + "(" + gen.params.join(", ") + ") ->" + NL + "  " + gen.goal + ":", depth);
      if (!nm) continue;
      const call = nm + "(" + gen.args.join(", ") + ")";
      const text = c.rw ? "(%" + c.rw.e + " : " + c.rw.P + "; " + call + ")" : call;
      if (A.tryText(g, text) && fits(text)) return text;
      if (A.debug()) console.error("[gen2] --ind: the arm does not take " + text.slice(0, 300));
      // the helper is a lemma now: the leaf tactics again (a rewrite by the IH, then the helper)
      const lf = A.leafText(k, g, left());
      if (fits(lf)) return lf;
    }
  }
  // the arm's goal over its context (true iff the arm is), when no instance of the induction
  // hypothesis occurs in it (another induction may prove it)
  const cp = ctxParams(A, g, raw, (s) => s);
  // as stated, or its normal form when shorter (the bits that a shift drops are gone)
  const goalText = A.attempt(A.FUEL_NF, () => { const a = A.show(raw, g.names), b = N ? A.show(N, g.names) : a; return b.length < a.length ? b : a; });
  if (cp && goalText !== undefined && cp.params.length > 0 && depth + 1 < MAX_DEPTH && cands.length <= 1) {
    const nm = proveHelper(R, "def " + newName(R) + "(" + cp.params.join(", ") + ") ->" + NL + "  " + goalText + ":", depth);
    if (nm) {
      const call = nm + "(" + cp.args.join(", ") + ")";
      if (A.tryText(g, call) && fits(call)) return call;
    }
  }
  return null;
};
// N (an equation) with each instance of one side of k's conclusion (the induction hypothesis) replaced
// by the other side (dir 0: left to right); null if none occurs
type IhRw = { t: LTerm; P: string; e: string };
const ihRewrite = (A: Api, k: string, g: Goal, N: any, dir: number, useNf = false): IhRw | null => {
  const def = A.RAW[k];
  const o = A.openMeta(def.T, def.n);
  if (!o) return null;
  const c = A.lower(o.concl, 0);
  if (c.$ !== "Eql") return null;
  // the sides as stated, or their normal forms (St.nregs(St0(n, ..)) is List.length(List.replicate(..)))
  const cn = useNf ? A.nf(o.concl, 0) : c;
  if (A.debug() && useNf) console.error("[gen2] --ind: IH normal form " + A.show(cn, []).slice(0, 200));
  if (cn.$ !== "Eql" || (useNf && A.key(cn) === A.key(c))) return null;
  const [from, to] = dir === 0 ? [cn.a, cn.b] : [cn.b, cn.a];
  if (from.$ === "Var") return null;
  // the arm's own instance of k's parameters (its columns), from the goal as stated; an instance of the
  // hypothesis must descend: live parameters equal, left to right, until one is a strict subterm
  const raw = A.lower(g.ty, g.d);
  const cols: (LTerm | null)[] = new Array(def.n).fill(null);
  if (!A.matchT(c, raw, cols, g.d)) { if (A.debug()) console.error("[gen2] --ind: no columns for " + A.show(raw, g.names).slice(0, 200)); return null; }
  if (A.debug()) console.error("[gen2] --ind: columns " + cols.map((x) => (x ? A.show(x, g.names) + "/" + x.$ : "-")).join(", ").slice(0, 300));
  const live = o.doms.map((d: any) => d.q.$ !== "None");
  const sub = (a: LTerm, b: LTerm): boolean => strictSub(A, A.key(a), b);
  const descends = (sol: (LTerm | null)[]): boolean => {
    for (let j = 0; j < def.n; j++) {
      if (!live[j]) continue;
      const a = sol[j], b = cols[j];
      if (!a || !b) return false;
      if (A.key(a) === A.key(b)) continue;
      return sub(a, b) || (b.$ === "Lit" && b.k === "Nat" && a.$ === "Lit" && a.k === "Nat" && a.v < b.v);
    }
    return false;
  };
  let hit: { key: string; to: LTerm; sol: (LTerm | null)[] } | null = null;
  const inst = (t: LTerm, sol: (LTerm | null)[]): LTerm => {
    switch (t.$) {
      case "Var": return t.i >= A.META ? (sol[t.i - A.META] ?? t) : t;
      case "App": return { ...t, f: inst(t.f, sol), x: inst(t.x, sol) } as LTerm;
      case "Ctr": case "ADT": return { ...t, x: (t as any).x.map((x: LTerm) => inst(x, sol)) } as LTerm;
      case "Eql": return { ...t, a: inst(t.a, sol), b: inst(t.b, sol), T: inst(t.T, sol) } as LTerm;
      default: return t;
    }
  };
  // the first instance found is rewritten at each of its occurrences (one rewrite)
  const go = (t: LTerm, hole: boolean): LTerm => {
    if (hit && A.key(t) === hit.key) return hole ? (B.Ref("_") as LTerm) : hit.to;
    const sol: (LTerm | null)[] = new Array(def.n).fill(null);
    // a parameter that the side does not name stays the arm's own
    // a premise (a hypothesis of k) is the context's hypothesis of the same normal form
    const full = () => {
      for (let j = 0; j < sol.length; j++) {
        if (sol[j]) continue;
        const pA = A.attempt(A.FUEL_NF, () => { const T = inst(A.lower(o.doms[j].A, 0), sol); return hasMetaOrHole(T) ? null : A.key(A.nf(B.term_higher(T, g.env), g.d)); });
        if (pA) for (let i = g.d - 1; i >= 0 && !sol[j]; i--) {
          const a = A.ann(g, i);
          if (!a || g.names[i] === "_") continue;
          if (A.attempt(A.FUEL_NF, () => A.key(A.nf(a.T, g.d))) === pA) sol[j] = B.Var(g.names[i], i) as LTerm;
        }
        sol[j] ??= cols[j];
      }
      return true;
    };
    if (!hit && t.$ !== "Var" && A.matchT(from, t, sol, g.d) && full() && descends(sol) && sol.every((x) => x)) {
      const r = inst(to, sol);
      if (!A.attempt(A.FUEL_NF, () => hasMetaOrHole(r))) { hit = { key: A.key(t), to: r, sol }; return hole ? (B.Ref("_") as LTerm) : r; }
    }
    switch (t.$) {
      case "App": return { ...t, f: go(t.f, hole), x: go(t.x, hole) } as LTerm;
      case "Ctr": case "ADT": return { ...t, x: (t as any).x.map((x: LTerm) => go(x, hole)) } as LTerm;
      default: return t;
    }
  };
  const r = { ...N, a: go(N.a, false), b: go(N.b, false) } as LTerm;
  if (!hit) return null;
  const P = { ...N, a: go(N.a, true), b: go(N.b, true) } as LTerm;
  const h = hit as { key: string; to: LTerm; sol: (LTerm | null)[] };
  const call = B.name_show(A.job().file, k) + "(" + h.sol.map((x) => A.show(x!, g.names)).join(", ") + ")";
  const L = inst(c.a, h.sol), Rr = inst(c.b, h.sol);
  // (%e : P; t) has type P[b] for t : P[a] (e : {a == b}): P[b] is the goal, P[a] the rewritten goal
  const e = dir === 0 ? "Equal.sym(" + A.show(inst(c.T, h.sol), g.names) + ", " + A.show(L, g.names) + ", " + A.show(Rr, g.names) + ", " + call + ")" : call;
  return { t: r, P: A.show(P, g.names), e };
};
// a term whose key is ka occurs strictly inside b (any position)
const strictSubAny = (A: Api, ka: string, b: any): boolean => {
  const kids = (t: any): any[] => t.$ === "App" ? [t.f, t.x] : t.$ === "Ctr" || t.$ === "ADT" ? t.x : t.$ === "Eql" ? [t.a, t.b] : [];
  const st = kids(b);
  for (let n = 0; st.length && n < 5000; n++) { const x = st.pop(); if (A.key(x) === ka) return true; st.push(...kids(x)); }
  return false;
};
// a term whose key is ka is a strict subterm of b (Nat literals step: 2n has 1n inside)
const strictSub = (A: Api, ka: string, b: any): boolean => {
  const kids = (t: any): any[] => {
    if (t.$ === "Lit" && t.k === "Nat" && t.v > 0) return [B.Lit("Nat", t.v - 1)];
    return t.$ === "Ctr" ? t.x : [];
  };
  const st = kids(b);
  for (let n = 0; st.length && n < 2000; n++) { const x = st.pop(); if (A.key(x) === ka) return true; st.push(...kids(x)); }
  return false;
};
const hasMetaOrHole = (t: LTerm): boolean => {
  const st: any[] = [t];
  while (st.length) {
    const x = st.pop();
    if (!x || typeof x !== "object") continue;
    if (x.$ === "Var" && x.i >= (1 << 20)) return true;
    if (x.$ === "Hol") return true;
    for (const f of ["f", "x", "a", "b", "T", "A", "B"]) if (x[f] && typeof x[f] === "object" && !Array.isArray(x[f])) st.push(x[f]);
    if (Array.isArray(x.x)) st.push(...x.x);
  }
  return false;
};
// the stuck calls (a def applied, blocked on a variable) that occur on both sides of an equation,
// replaced by new parameters of their types
const generalize = (A: Api, g: Goal, N: any, enums = false): { params: string[]; args: string[]; goal: string } | null => {
  const seen = new Map<string, { t: LTerm; n: number }>();
  const walk = (t: LTerm, side: number) => {
    if (t.$ === "App") {
      const [h, xs] = A.unapply(t);
      if (h.$ === "Ref") {
        const blk: LTerm[] = [];
        A.blockers(t, blk);
        const vars = new Set<number>();
        freeVars(t, vars);
        if (blk.length > 0 && vars.size > 0) {
          const kk = A.key(t);
          const e = seen.get(kk) ?? { t, n: 0 };
          e.n |= side;
          seen.set(kk, e);
        }
      }
      xs.forEach((x: LTerm) => walk(x, side));
    } else if (t.$ === "Ctr" || t.$ === "ADT") (t as any).x.forEach((x: LTerm) => walk(x, side));
  };
  walk(N.a, 1); walk(N.b, 2);
  // maximal common subterms: drop one inside another common one
  const isEnum = (t: LTerm) => {
    const T = A.attempt(A.FUEL_NF, () => B.term_infer(A.book, g.lhs, B.term_higher(t, g.env), B.None(), g.ctx, g.d).ty);
    const adt = T ? adtOf(A, g, T) : null;
    return !!adt && adt.c.length >= 2 && adt.c.length <= 4 && adt.c.every((c: any) => c.n === 0);
  };
  // common stuck calls become plain variables; with enums, a stuck call of an enumeration type (Cmp,
  // Bool) on one side becomes a variable with its equation (so the helper holds iff the goal does)
  const inside = (a: LTerm, b: LTerm) => a !== b && strictSubAny(A, A.key(a), b);
  const common0 = [...seen.values()].filter((e) => e.n === 3).map((e) => e.t);
  const common = common0.filter((a) => !common0.some((b) => inside(a, b))).slice(0, 4);
  const eqs0 = enums ? [...seen.values()].filter((e) => e.n !== 3 && isEnum(e.t)).map((e) => e.t) : [];
  const eqs = eqs0.filter((a) => !eqs0.some((b) => inside(b, a)) && !common.some((b) => inside(a, b) || inside(b, a))).slice(0, 2);
  if (enums && eqs.length === 0) return null;
  const gens = [...common, ...eqs];
  if (gens.length === 0) return null;
  const used = new Set<string>(g.names);
  const vs: { nm: string; ty: string; t: LTerm; eq?: string }[] = [];
  for (const t of gens) {
    const h = B.term_higher(t, g.env);
    const T = A.attempt(A.FUEL_NF, () => B.term_infer(A.book, g.lhs, h, B.None(), g.ctx, g.d).ty);
    if (!T) return null;
    const ty = A.attempt(A.FUEL_NF, () => A.show(A.lower(T, g.d), g.names));
    if (ty === undefined) return null;
    vs.push({ nm: A.fresh("g", used), ty, t, eq: eqs.includes(t) ? A.fresh("hg", used) : undefined });
  }
  // the goal with each generalized call a variable (by key, from the largest)
  const repl = (t: LTerm): LTerm => {
    const kk = A.key(t);
    const v = vs.find((x) => A.key(x.t) === kk);
    if (v) return B.Ref(v.nm) as LTerm;
    switch (t.$) {
      case "App": return { ...t, f: repl(t.f), x: repl(t.x) } as LTerm;
      case "Ctr": case "ADT": return { ...t, x: (t as any).x.map(repl) } as LTerm;
      case "Eql": return { ...t, a: repl(t.a), b: repl(t.b), T: repl(t.T) } as LTerm;
      default: return t;
    }
  };
  const G = repl(N) as any;
  if (G.$ === "Eql" && A.key(G.a) === A.key(G.b)) return null;
  const goal = A.attempt(A.FUEL_NF, () => A.show(G, g.names));
  if (goal === undefined) return null;
  const cp = ctxParams(A, g, eqs.length ? (B.Eql(G, B.Ctr("Tuple", eqs) as LTerm, G) as LTerm) : G, (s) => s);
  if (!cp) return null;
  const shown = vs.map((v) => A.show(v.t, g.names));
  return {
    params: [...cp.params, ...vs.flatMap((v, i) => ["+" + v.nm + ": " + v.ty, ...(v.eq ? ["+" + v.eq + ": {" + v.nm + " == " + shown[i] + " : " + v.ty + "}"] : [])])],
    args: [...cp.args, ...vs.flatMap((v, i) => [shown[i], ...(v.eq ? ["{==}"] : [])])], goal,
  };
};

// ---- schemes ----
const schemes = (R: Run, k: string): Scheme[] => {
  const { A } = R;
  const tl = tele(A, k);
  if (!tl) { if (A.debug()) console.error("[gen2] --ind: no parameters for " + A.shortOf(k)); return []; }
  const out: Scheme[] = [];
  const add = (name: string, body: string | null) => { if (body) out.push({ name, body: indent(body, "  ") }); };
  for (const s of [enumScheme, u32Scheme, wordScheme, natScheme, funScheme]) {
    const r = A.attempt(A.FUEL_NF * 4, () => s(R, k, tl));
    if (r) for (const [nm, b] of r) add(nm, b);
  }
  return out;
};
type Tele = { g: Goal; ps: { name: string; q: string; ty: string; T: HTerm; i: number }[] };
// the parameters that block the goal's normal form (strict arguments of stuck calls)
const blocking = (A: Api, tl: Tele): number[] => {
  const N = A.attempt(A.FUEL_NF * 2, () => A.nf(tl.g.ty, tl.g.d));
  const blk: LTerm[] = [];
  if (N) A.blockers(N, blk);
  const out: number[] = [];
  for (const b of blk) if (b.$ === "Var" && b.i < tl.ps.length && !out.includes(b.i)) out.push(b.i);
  return out.sort((a, b) => a - b);
};
// the parameters that a stuck call of the goal's normal form matches (any position its case tree reads)
const matchedParams = (A: Api, tl: Tele): number[] => {
  const N = A.attempt(A.FUEL_NF * 2, () => A.nf(tl.g.ty, tl.g.d));
  const out = new Set<number>(blocking(A, tl));
  const walk = (t: LTerm) => {
    if (t.$ === "App") {
      const [h, xs] = A.unapply(t);
      if (h.$ === "Ref") { const ms: Set<number> = A.matchedOf(h.k); xs.forEach((x: LTerm, j: number) => { if (ms.has(j) && x.$ === "Var" && x.i < tl.ps.length) out.add(x.i); }); }
      xs.forEach(walk);
    } else if (t.$ === "Ctr" || t.$ === "ADT") (t as any).x.forEach(walk);
    else if (t.$ === "Eql") { walk(t.a); walk(t.b); }
  };
  if (N) walk(N);
  return [...out].filter((i) => tl.ps[i].q !== "-").sort((a, b) => a - b);
};
// the case list of parameter i: its constructors (fields named after it)
const casesOf = (A: Api, tl: Tele, i: number, used: Set<string>): string[] | null => {
  const p = tl.ps[i];
  if (p.ty === "Nat") return ["0n", "1n+" + A.fresh(p.name + "p", used)];
  const adt = adtOf(A, tl.g, p.T);
  if (!adt || adt.c.length === 0 || adt.c.length > 6 || /^(U32|F32|Char)$/.test(p.ty)) return null;
  return adt.c.map((c: any) => (c.n === 0 ? B.name_show(A.job().file, c.k) + "{}" : ctrPat(A, "", c, p.name, used)));
};
const enumScheme = (R: Run, k: string, tl: Tele): [string, string][] | null => {
  const { A } = R;
  const bound = new Map<number, number>();
  for (const p of tl.ps) {
    const m = /^\{Nat\.is_(le|lt)\(([A-Za-z_]\w*), (\d+)n\) == True\{\} : Bool\}$/.exec(p.ty);
    if (!m) continue;
    const i = tl.ps.findIndex((x) => x.name === m[2] && x.ty === "Nat");
    const c = +m[3] - (m[1] === "lt" ? 1 : 0);
    if (i >= 0 && c >= 0 && c <= ENUM_MAX) bound.set(i, Math.min(c, bound.get(i) ?? c));
  }
  if (bound.size === 0) return null;
  const used = new Set(tl.ps.map((p) => p.name));
  const idx = [...new Set([...bound.keys(), ...matchedParams(A, tl)])].sort((a, b) => a - b);
  const cases: string[][] = [];
  for (const i of idx) {
    if (bound.has(i)) cases.push([...Array.from({ length: bound.get(i)! + 1 }, (_, v) => v + "n"), (bound.get(i)! + 1) + "n+" + A.fresh(tl.ps[i].name + "p", used)]);
    else { const c = casesOf(A, tl, i, used); if (!c) return null; cases.push(c); }
  }
  const all = product(cases);
  if (all.length > MAX_ARMS) return null;
  return [["enum", matchText(idx.map((i) => tl.ps[i].name), all, () => "?TODO")]];
};
const u32Scheme = (R: Run, k: string, tl: Tele): [string, string][] | null => {
  const { A } = R;
  // the U32 parameters that a stuck call reads, or that a U32 operation takes
  const mp = new Set(matchedParams(A, tl));
  const N0 = A.attempt(A.FUEL_NF * 2, () => A.nf(tl.g.ty, tl.g.d));
  const walk = (t: LTerm) => {
    if (t.$ === "App") {
      const [h, xs] = A.unapply(t);
      if (h.$ === "Ref" && /^U32\./.test(A.shortOf(h.k))) xs.forEach((x: LTerm) => { if (x.$ === "Var") mp.add(x.i); });
      xs.forEach(walk);
    } else if (t.$ === "Ctr" || t.$ === "ADT") (t as any).x.forEach(walk);
    else if (t.$ === "Eql") { walk(t.a); walk(t.b); }
  };
  if (N0) walk(N0);
  const us = tl.ps.filter((p) => p.ty === "U32" && p.q !== "-" && mp.has(p.i));
  if (us.length === 0 || us.length > 4) return null;
  const used = new Set(tl.ps.map((p) => p.name));
  const ws = us.map((p) => A.fresh(p.name + "w", used));
  const skel = matchText(us.map((p) => p.name), [ws.map((w) => "U32{" + w + "}")], () => "?TODO");
  // the arm's goal: a statement over words of width 32n generalizes to width n
  const body = indent(skel, "  ");
  const err = A.checkBody(k, body.replace("?TODO", "?gen2hole"));
  const g = typeof err === "object" ? A.holeGoal(k, err, "u32") : null;
  if (!g) return [["u32", skel]];
  const N = A.attempt(A.FUEL_NF * 2, () => A.nf(g.ty, g.d));
  if (!N || N.$ !== "Eql") return [["u32", skel]];
  const lifted = liftWidth(R, g, N);
  return lifted ? [["u32+width", skel.replace("?TODO", lifted)], ["u32", skel]] : [["u32", skel]];
};
// a goal over words of width 32 (after U32{w} splits): the helper over width n, proven, and its call
const liftWidth = (R: Run, g: Goal, N: any): string | null => {
  const { A } = R;
  // a U32 side: U32{w} (its word w), or the literal 0 (Word.zero); a constant word of zeros is
  // Word.zero at any width
  const isU32 = (t: any) => (t.$ === "Ctr" && A.shortOf(t.k) === "U32" && t.x.length === 1) || (t.$ === "Lit" && t.k === "U32" && t.v === 0);
  const u32 = A.show(N.T, g.names) === "U32" && isU32(N.a) && isU32(N.b);
  const zeros = (n: number): string => (n === 0 ? "WNil{}" : "WCon{False{}, " + zeros(n - 1) + "}");
  const z32 = zeros(32);
  const side = (t: any) => (u32 ? (t.$ === "Lit" ? "Word.zero(32n)" : A.show(t.x[0], g.names)) : A.show(t, g.names)).split(z32).join("Word.zero(32n)");
  const L = u32 ? (N.a.$ === "Lit" ? N.b.x[0] : N.a.x[0]) : N.a, Rr = u32 ? (N.b.$ === "Lit" ? N.a.x[0] : N.b.x[0]) : N.b;
  const T = u32 ? "Word(32n)" : A.show(N.T, g.names);
  const ls = side(N.a), rs = side(N.b);
  if (!/\b32n\b/.test(ls + rs)) return null;
  const used = new Set<string>(g.names);
  const nv = A.fresh("n", used);
  const w = (s: string) => s.replace(/\b32n\b/g, nv).replace(/\b0n\b/g, "0n");
  const cp = ctxParams(A, g, B.Eql(L, Rr, N.T) as LTerm, w);
  if (!cp) return null;
  const nm = proveHelper(R, "def " + newName(R) + "(+" + nv + ": Nat, " + cp.params.join(", ") + ") ->\n  {" + w(ls) + " == " + w(rs) + " : " + w(T) + "}:", 0);
  if (!nm) return null;
  const call = nm + "(32n, " + cp.args.join(", ") + ")";
  return u32 ? "Equal.cong(Word(32n), U32, w => U32{w}, " + ls + ", " + rs + ", " + call + ")" : call;
};
// n: Nat and words of width n: match n; then the words with their head bits as nested patterns
// (WCon{False{}, t}: a pattern binder cannot be matched after a later parameter); as a second
// skeleton, also the other parameters that a stuck call matches
const wordScheme = (R: Run, k: string, tl: Tele): [string, string][] | null => {
  const { A } = R;
  const n = tl.ps.findIndex((p) => p.ty === "Nat" && p.q !== "-");
  if (n < 0) return null;
  const nm = tl.ps[n].name;
  const words = tl.ps.filter((p) => p.ty === "Word(" + nm + ")" && p.q !== "-");
  if (words.length === 0 || words.length > 4) return null;
  const out: [string, string][] = [];
  for (const extra of [false, true]) {
    const used = new Set(tl.ps.map((p) => p.name));
    const pv = A.fresh("p", used);
    const others = extra ? matchedParams(A, tl).filter((i) => i !== n && !words.some((w) => w.i === i)) : [];
    if (extra && others.length === 0) continue;
    const idx = [...words.map((w) => w.i), ...others].sort((a, b) => a - b);
    const cases: string[][] = [];
    for (const i of idx) {
      const p = tl.ps[i];
      if (words.some((w) => w.i === i)) { const t = A.fresh(p.name + "t", used); cases.push(["WCon{False{}, " + t + "}", "WCon{True{}, " + t + "}"]); }
      else { const c = casesOf(A, tl, i, used); if (!c) return null; cases.push(c); }
    }
    const all = product(cases);
    if (all.length > MAX_ARMS) continue;
    // at width 0 every word is WNil{}
    const zu = new Set(used);
    const zc = idx.map((i) => (words.some((w) => w.i === i) ? ["WNil{}"] : casesOf(A, tl, i, zu)));
    const zero = zc.every((c) => c) ? matchText(idx.map((i) => tl.ps[i].name), product(zc as string[][]), () => "?TODO") : "?TODO";
    const succ = matchText(idx.map((i) => tl.ps[i].name), all, () => "?TODO");
    out.push([extra ? "word+split" : "word", "match " + nm + ":" + NL + "  case 0n:" + NL + indent(zero, "    ") + NL + "  case 1n+" + pv + ":" + NL + indent(succ, "    ")]);
  }
  return out;
};
const natScheme = (R: Run, k: string, tl: Tele): [string, string][] | null => {
  const { A } = R;
  const out: [string, string][] = [];
  for (const i of blocking(A, tl)) {
    const p = tl.ps[i];
    if (p.ty !== "Nat" || p.q === "-") continue;
    const used = new Set(tl.ps.map((x) => x.name));
    out.push(["nat:" + p.name, matchText([p.name], [["0n"], ["1n+" + A.fresh(p.name + "p", used)]], () => "?TODO")]);
    if (out.length >= 2) break;
  }
  return out;
};
// functional induction: a recursive def of the goal applied to parameters at the positions it
// matches: one skeleton with its matched parameters split jointly (their constructors)
const funScheme = (R: Run, k: string, tl: Tele): [string, string][] | null => {
  const { A } = R;
  const raw = A.lower(tl.g.ty, tl.g.d);
  const N = A.attempt(A.FUEL_NF * 2, () => A.nf(tl.g.ty, tl.g.d));
  const out: [string, string][] = [];
  const seen = new Set<string>();
  // the parameters that a call reads (its matched arguments), also through a recursive call in a
  // matched position (List.get(List.replicate(U32, n, 0), q) reads n and q)
  const reads = (t: LTerm, idx: number[], rec: { r: boolean }, n = 0) => {
    if (n > 6) return;
    if (t.$ === "Var") { if (t.i < tl.ps.length && tl.ps[t.i].q !== "-" && !idx.includes(t.i)) idx.push(t.i); return; }
    if (t.$ !== "App") return;
    const [h, xs] = A.unapply(t);
    if (h.$ !== "Ref") return;
    if (isRecursive(A, h.k)) rec.r = true;
    const ms: Set<number> = A.matchedOf(h.k);
    xs.forEach((x: LTerm, j: number) => { if (ms.has(j)) reads(x, idx, rec, n + 1); });
  };
  const walk = (t: LTerm) => {
    if (t.$ === "App") {
      const [h, xs] = A.unapply(t);
      const idx: number[] = [], rec = { r: false };
      reads(t, idx, rec);
      const kk = idx.slice().sort().join(",");
      if (h.$ === "Ref" && rec.r && idx.length >= 2 && idx.length <= 3 && !seen.has(kk)) {
        seen.add(kk);
        idx.sort((a, b) => a - b);
        const used = new Set(tl.ps.map((p) => p.name));
        const cs = idx.map((i) => casesOf(A, tl, i, used));
        if (cs.every((c) => c) && product(cs as string[][]).length <= MAX_ARMS)
          out.push(["fun:" + A.shortOf(h.k), matchText(idx.map((i) => tl.ps[i].name), product(cs as string[][]), () => "?TODO")]);
      }
      xs.forEach(walk);
    } else if (t.$ === "Ctr" || t.$ === "ADT") (t as any).x.forEach(walk);
    else if (t.$ === "Eql") { walk(t.a); walk(t.b); }
  };
  walk(raw);
  if (N) walk(N);
  return out.slice(0, 2);
};
const recMemo = new Map<string, boolean>();
const isRecursive = (A: Api, k: string): boolean => {
  if (recMemo.has(k)) return recMemo.get(k)!;
  const t = A.RAW[k];
  let r = false;
  if (t?.$ === "Def" && t.v) {
    // the body (lowered) names k: a self-call
    const body = A.attempt(A.FUEL_NF, () => A.lower(t.v, 0));
    const st: any[] = body ? [body] : [];
    for (let n = 0; st.length && n < 20000 && !r; n++) {
      const x = st.pop();
      if (!x || typeof x !== "object") continue;
      if (x.$ === "Ref" && x.k === k) { r = true; break; }
      for (const f in x) if (f !== "s" && x[f] && typeof x[f] === "object") st.push(x[f]);
    }
  }
  recMemo.set(k, r);
  return r;
};

// ---- the schemes on def k: the first that closes every arm, else the best partial ----
const schemesProve = (R: Run, k: string, depth: number): Fill | null => {
  const { A } = R;
  // the leaf tactics on every scheme's arms first; then helpers for the arms left of the best two
  const tried: Fill[] = [];
  for (const s of schemes(R, k)) {
    if (A.now() > R.until) break;
    if (ONLY && depth === 0 && !ONLY.test(s.name)) continue;
    const r = fillArms(R, k, s.body, depth, [0]);
    if (A.debug()) console.error("[gen2] --ind: " + A.shortOf(k) + " scheme " + s.name + ": " + (r ? r.open + " open, " + r.closed + " closed" : "does not check") + " (" + Math.round(R.until - A.now()) + " ms left)");
    if (!r) continue;
    if (r.open === 0) { if (A.checkBody(k, r.body) === null) { R.notes.push(A.shortOf(k) + ": scheme " + s.name); return r; } continue; }
    tried.push({ ...r, name: s.name } as any);
  }
  // the skeleton whose largest open arm is smallest (a split that made progress), then fewest open
  const rank = (f: any) => SCHEME_RANK.findIndex((r) => f.name.startsWith(r));
  tried.sort((a, b) => rank(a) - rank(b) || a.open - b.open || b.closed - a.closed);
  let best: Fill | null = tried[0] ?? null;
  if (depth < MAX_DEPTH) for (const t of tried.slice(0, 2)) {
    if (A.now() > R.until || t.open > MAX_HELPER_ARMS) break;
    if (t.closed === 0) continue; // no arm closed: the split made no progress
    const r = fillArms(R, k, t.body, depth, [1]);
    if (A.debug()) console.error("[gen2] --ind: " + A.shortOf(k) + " scheme " + (t as any).name + " with helpers: " + (r ? r.open + " open" : "-"));
    if (!r) continue;
    const merged = { ...r, closed: r.closed + t.closed };
    if (r.open === 0 && A.checkBody(k, r.body) === null) { R.notes.push(A.shortOf(k) + ": scheme " + (t as any).name + " with helpers"); return merged; }
    if (!best || merged.open < best.open) best = merged;
  }
  return best;
};

// ---- entry points ----
export const indProve = (A: Api, k: string, budget: number): IndOut => {
  const t0 = A.now();
  const R: Run = { A, k, until: t0 + Math.max(budget, IND_FLOOR_MS), helpers: [], notes: [], used: new Set(), nHelpers: 0, failed: new Set(), proven: new Map() };
  A.setJob(A.newJob(k));
  const r = schemesProve(R, k, 0);
  const ms = A.now() - t0;
  if (!r) return null;
  const helpers = R.helpers.sort((a, b) => a.order - b.order).map((h) => h.text);
  const report = "# --ind: " + (r.open === 0 ? "proven" : r.open + " arm(s) open") + " (" + (R.notes.join("; ") || "skeleton") + (helpers.length ? ", " + helpers.length + " helper(s)" : "") + "), " + Math.round(ms) + " ms" +
    r.goals.map((g, i) => "\n# arm " + (i + 1) + " (the " + (i + 1) + ". ?TODO): goal " + A.clipTo(g, 400)).join("");
  return { text: r.body, helpers, open: r.open, closed: r.closed, report, ms };
};

// a goal closed by a constructor clash in a hypothesis, through a predicate with type parameters
// (`%e : maybe.T(A, _); Unit{}`, under Empty.absurd when the goal is not Empty); the proof text or null
const predMemo = new Map<string, { k: string; n: number }[]>();
const predsOf = (A: Api, adt: string): { k: string; n: number }[] => {
  if (predMemo.size === 0) {
    for (const k of Object.keys(A.RAW)) {
      const t = A.RAW[k];
      if (t?.$ !== "Def" || !t.v || t.n < 2 || t.n > 4) continue;
      const o = A.attempt(20000, () => {
        let T: HTerm = t.T;
        let last: HTerm | null = null;
        for (let j = 0; j < t.n; j++) {
          const s = B.term_strip(T) as any;
          if (s.$ !== "All") return null;
          if (j < t.n - 1 && s.q.$ !== "None") return null;
          last = s.A;
          T = s.B(B.Var("_", 1e7 + j));
        }
        const w = A.wnf(T);
        const la = last ? (B.term_strip(last) as any) : null;
        return w && w.$ === "Typ" && la && la.$ === "ADT" ? la.k : null;
      });
      if (o) { let a = predMemo.get(o); if (!a) predMemo.set(o, a = []); a.push({ k, n: t.n }); }
    }
    if (predMemo.size === 0) predMemo.set("", []);
  }
  return predMemo.get(adt) ?? [];
};
export const indLeaf = (A: Api, g: Goal): string | null => {
  const contra: number[] = A.contradictory(g);
  if (contra.length === 0) return null;
  const job = A.job();
  const w = A.wnf(g.ty);
  const empty = w && w.$ === "ADT" && A.RAW[w.k]?.c?.length === 0;
  const goal = A.attempt(A.FUEL_NF, () => A.show(A.lower(g.ty, g.d), g.names));
  if (goal === undefined) return null;
  for (const i of contra.slice(0, 2)) {
    const ts = A.hypTargets(g, i);
    const E = ts[ts.length - 1];
    const Tt = B.term_strip(E.T) as any;
    if (Tt.$ !== "ADT") continue;
    const targs = (Tt.x as LTerm[]).filter((x: any) => x.$ !== "Qua" && x.$ !== "Qnt").map((x) => A.show(x, g.names));
    for (const P of predsOf(A, Tt.k).slice(0, 8)) {
      if ((A.ORDER.get(P.k) ?? Infinity) >= job.order) continue;
      if (targs.length < P.n - 1) continue;
      const pn = B.name_show(job.file, P.k) + "(" + [...targs.slice(targs.length - (P.n - 1)), "_"].join(", ") + ")";
      for (const sym of [false, true]) {
        const e = sym ? "Equal.sym(" + A.show(E.T, g.names) + ", " + A.show(E.a, g.names) + ", " + A.show(E.b, g.names) + ", " + g.names[i] + ")" : g.names[i];
        const d = "(%" + e + " : " + pn + "; Unit{})";
        const s = empty ? d : "Empty.absurd(" + goal + ", " + d + ")";
        if (A.tryText(g, s)) return s;
      }
    }
  }
  return null;
};

// split candidates: a pending parameter of an enumeration type (constructors without fields) that the
// goal does not block on (bool.case's b: only its hypotheses name it), after the others
export const indSplits = (A: Api, n: Goal, out: number[]) => {
  let g: Goal | null = n;
  for (let j = 0; j < n.pend && g; j++) {
    const t = A.wnf(g.ty);
    if (!t || t.$ !== "All") break;
    if (t.q.$ !== "None" && !out.includes(j)) {
      const adt = adtOf(A, g, t.A);
      if (adt && adt.c.length >= 2 && adt.c.length <= 4 && adt.c.every((c: any) => c.n === 0)) out.push(j);
    }
    g = A.intro(g, g.pnames[0], g.pmany[0]);
  }
};
