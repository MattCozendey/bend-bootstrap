// gen2_wp.ts: gen2's Cir stepper (--wp), a dev tool outside the trust like gen2.ts (exempt from the
// review sweeps and the TypeScript rules of AGENTS.md 2.5 for the same reason; excluded in tsconfig).
//
// On a goal `Lg.Tot(code, st, b, Q, H)` or `Lg.WP(code, b, K, H, st)` (logic/spec.bend of lane S1)
// whose code is closed, it writes the proof that steps the code. A Tot goal becomes a WP goal by
// tot.of_wp (K = h => Q). WP is computed by the code's structure, so a sequence and an if need no law:
// the proof of WP(seq{a, c}, ..) is the proof of a's WP with the post "then c's WP"; an if's
// condition is rewritten by its value (WP.if), and its branch is taken when the value's U32.is_zero
// computes (by itself, or once Bool facts of the context rewrite parts of it). A set is wp.set, a
// store wp.store; their premises: each register read rewritten by its fact (a hypothesis
// {Lg.Reg(st, r) == Some{c}} for the start state, reg.set / reg.store after a step, chained by
// Equal.trans), the register count by a hypothesis {Lg.St.nregs(st) == N} (N computes to a number)
// carried by nregs.set / nregs.store, a cell by a hypothesis {Lg.St.is_cell(st, c) == True{}}.
// What is left is ?TODO leaves, each with a one-line hint: the post at the end, a branch that no fact
// decides, a loop, a halt, a routine with a law (wp.of_tot), a statement or read the stepper does not
// cover. The proof is a body: typed lets for the states, the facts and the code's suffixes (its size
// grows linearly with the code), then the proof term.
//
// Bounded: at most MAX_STEPS statements and the caller's deadline; past either, the rest is one
// leaf. Never throws: an internal failure is a one-line `why`.
//
// The laws are found through NAMES (one indirection): each logical name lists the short names it may
// have in the book (S1's, from reports/redesign/s1-names.md), the first that exists wins.

import * as B from "../../../bend/bend2/bend.ts";

type HTerm = B.HTerm;
type LTerm = B.LTerm;

// ---- types ----
export type WpGoal = { ctx: B.Ctx; d: number; ty: HTerm; names: string[]; self?: string };
export type WpApi = {
  RAW: Record<string, B.TLD>;
  show: (t: LTerm, names: string[]) => string;
  lower: (h: HTerm, d: number) => LTerm;
  nf: (h: HTerm, d: number) => LTerm;
  wnf: (h: HTerm) => HTerm | undefined;
  attempt: <T>(n: number, f: () => T) => T | undefined;
  key: (t: LTerm) => string;
  deadline: number;
  // a routine law instantiated at a call (gen2's openMeta and match): its parameters fixed by the call's
  // code and state, the types of the others, and the law's b, Q, H
  inst?: (law: string, code: LTerm, st: LTerm, b: LTerm, facts: { T: LTerm; pf: string }[], d: number) => WpInst | null;
  // a law instantiated by its premises alone (each parameter fixed by a fact that a premise fits)
  instPrem?: (law: string, facts: { T: LTerm; pf: string }[], d: number) => WpInst | null;
  // an equation law instantiated at the term its left side matches
  instEq?: (law: string, lhs: LTerm, facts: { T: LTerm; pf: string }[], d: number) => WpInst | null;
};
export type WpInst = { sol: (LTerm | null)[]; pfs: (string | null)[]; doms: { k: string; A: LTerm | null; fact: boolean }[]; concl: LTerm[]; T: LTerm };
export type WpLeaf = { hole: number; hint: string };
export type WpOut = { text: string; leaves: WpLeaf[]; steps: number } | { why: string };

// ---- constants ----
const MAX_STEPS = 400;
const MAX_SPLITS = 4; // nested Bool splits of undecided ifs (each doubles the rest of the code)
const FUEL = 100000;
// logical name -> the short names (key less its namespace) it may have; the first found wins
const NAMES: Record<string, string[]> = {
  tot: ["Tot"], wp: ["WP"], wpIf: ["WP.if"], wpPick: ["WP.pick"], reg: ["Reg"],
  nregs: ["St.nregs"], isCell: ["St.is_cell"], stSet: ["St.set"], stStore: ["St.store"],
  totOfWp: ["tot.of_wp"], wpSet: ["wp.set"], wpAlloc: ["wp.alloc"], wpEmit: ["wp.emit"], stAlloc: ["St.alloc"], stEmit: ["St.emit"], stNext: ["St.next"], stOutn: ["St.outn"],
  regAlloc: ["reg.alloc"], regEmit: ["reg.emit"], nregsAlloc: ["nregs.alloc"], nregsEmit: ["nregs.emit"],
  outnSet: ["outn.set"], outnStore: ["outn.store"], outnAlloc: ["outn.alloc"], outnEmit: ["outn.emit"], regSome: ["reg.some"], regLt: ["reg.lt"], stReg: ["St.reg"], natIsEqOk: ["nat.is_eq_ok"], wpOfTot: ["wp.of_tot"], totWhile: ["tot.while"], totWk: ["tot.wk"], leRefl: ["lg.le_refl", "nat.le_refl"], wpStore: ["wp.store"],
  regSet: ["reg.set"], regStore: ["reg.store"], nregsSet: ["nregs.set"], nregsStore: ["nregs.store"],
  evalOp: ["Cir.eval.op"], evalEqz: ["Cir.eval.eqz"], cirEval: ["Cir.eval"], evalField: ["Cir.eval.field"],
  fieldIf: ["Cir.eval.field.if"], stCells: ["St.cells"], cellGet: ["Cir.Cell.get"], cellsGet: ["Cir.Cells.get"],
  equalSym: ["Equal.sym"], equalTrans: ["Equal.trans"],
  boolCase: ["bool.case"],
  cirState: ["Cir.State"], cirOut: ["Cir.Out"], cirStmt: ["Cir.Stmt"], isZero: ["U32.is_zero"],
};

// ---- functions ----
class Fail { constructor(readonly why: string) {} }
const fail = (why: string): never => { throw new Fail(why); };

// t with every subterm whose key is k replaced by by (t itself when there is none)
const replaceKey = (t: LTerm, k: string, by: LTerm, key: (t: LTerm) => string): LTerm => {
  if (key(t) === k) return by;
  switch (t.$) {
    case "App": { const f = replaceKey(t.f, k, by, key), x = replaceKey(t.x, k, by, key); return f === t.f && x === t.x ? t : B.App(f, x); }
    case "Ctr": { const x = t.x.map((a) => replaceKey(a, k, by, key)); return x.every((a, i) => a === t.x[i]) ? t : B.Ctr<[LTerm]>(t.k, x); }
    case "Eql": { const a = replaceKey(t.a, k, by, key), b = replaceKey(t.b, k, by, key), T = replaceKey(t.T, k, by, key); return a === t.a && b === t.b && T === t.T ? t : B.Eql(a, b, T); }
    case "ADT": { const x = t.x.map((a) => replaceKey(a, k, by, key)); return x.every((a, i) => a === t.x[i]) ? t : B.ADT(t.k, x, undefined, t.r); }
    case "Lam": { const f = replaceKey(t.f as LTerm, k, by, key); return f === t.f ? t : B.Lam<LTerm>(t.k, t.i, f, undefined, t.q); }
    case "All": { const A = replaceKey(t.A, k, by, key), Bd = replaceKey(t.B as LTerm, k, by, key); return A === t.A && Bd === t.B ? t : B.All<LTerm>(t.q, t.k, t.i, A, Bd); }
    default: return t;
  }
};

// dst: the start state is a parameter: the proof begins with `match st` (its accessors and updaters
// then compute: a field read needs only an is_cell fact, and a cell fact holds after sets and stores)
export const wpProve = (api: WpApi, g: WpGoal, dst = false): WpOut => {
  try {
    return run(api, g, dst);
  } catch (e: any) {
    if (e instanceof Fail) return { why: e.why };
    return { why: "internal: " + String(e?.message ?? e).slice(0, 200) };
  }
};

const run = (api: WpApi, g: WpGoal, dst: boolean): WpOut => {
  // the book's names
  const shortOf = (k: string) => (k.includes(":") ? k.slice(k.indexOf(":") + 1) : k);
  const byShort = new Map<string, string>();
  for (const k of Object.keys(api.RAW)) { const s = shortOf(k); if (!byShort.has(s) || !k.includes(":")) byShort.set(s, k); }
  const K: Record<string, string | undefined> = {};
  for (const [n, cands] of Object.entries(NAMES)) K[n] = cands.map((c) => byShort.get(c)).find((k) => k !== undefined);
  if (!K.tot && !K.wp) return { why: "not a Tot goal" };
  const names = g.names.slice(0, g.d);
  // a term printed in this file's names; a state built by the stepper prints as its let
  const stateReps: { key: string; ref: LTerm }[] = [];
  const sh = (t: LTerm) => {
    if (stateReps.length > 0) {
      const k = api.key(t);
      if (dstKey !== "" || stepRefs.some((r) => k.includes(r))) for (let i = stateReps.length - 1; i >= 0; i--) t = replaceKey(t, stateReps[i]!.key, stateReps[i]!.ref, api.key);
    }
    return api.show(t, names);
  };
  const stepRefs: string[] = [];
  let dstKey = "";
  const ref = (n: string): LTerm => {
    const k = K[n] ?? fail("the law " + NAMES[n]![0] + " is not in the book (import logic/impl.bend)");
    if (g.self && (k === g.self || shortOf(k) === shortOf(g.self))) fail("the stepped proof would use " + shortOf(k) + ", the law being proven (circular): not used");
    return B.Ref(k) as LTerm;
  };
  const nm = (n: string) => sh(ref(n));
  const ctor = (short: string) => { const k = K.cirOut ?? fail("no Cir.Out in the book"); return sh(B.Ctr<[LTerm]>((k.includes(":") ? k.slice(0, k.indexOf(":") + 1) : "") + short, [])).replace(/\{\}$/, ""); };
  const unapply = (t: LTerm) => B.term_unapply(t);
  const isRef = (t: LTerm, n: string) => t.$ === "Ref" && K[n] !== undefined && t.k === K[n];
  let env: B.Env | null = null;
  // the context's depth: g.d, plus the page binders of the allocs and emits being stepped; scope: their number
  let D = g.d, scope = 0;
  const envOf = (): B.Env => {
    if (env === null) { let e: B.Env = null; for (let i = 0; i < D; i++) e = B.list_set(e, i, B.Var(names[i] ?? "_", i)); env = e; }
    return env;
  };
  const wnfL = (t: LTerm): LTerm | undefined => { const w = api.wnf(B.term_higher(t, envOf())); return w ? api.lower(w, D) : undefined; };
  const nfL = (t: LTerm): LTerm | undefined => api.attempt(FUEL, () => api.nf(B.term_higher(t, envOf()), D));
  const natOf = (t: LTerm): number | null => { const n = nfL(t); return n && n.$ === "Lit" && n.k === "Nat" ? (n.v as number) : null; };
  // a register: a number, or a term (a parameter r with facts about it)
  type Rg = { key: string; text: string; lit: number | null; term: LTerm };
  const rgOf = (t: LTerm): Rg => {
    const n = natOf(t);
    if (n !== null) return { key: "n" + n, text: n + "n", lit: n, term: B.Lit("Nat", n) as LTerm };
    const f = nfL(t) ?? t;
    return { key: "t" + api.key(f), text: sh(t), lit: null, term: t };
  };
  const isBool = (t: LTerm | undefined): t is Extract<LTerm, { $: "Ctr" }> => !!t && t.$ === "Ctr" && (t.k === "True" || t.k === "False") && t.x.length === 0;

  // the goal: Tot(code, st, b, Q, H), or WP(code, b, K, H, st)
  const goal0 = api.lower(g.ty, g.d);
  const [gh0, gargs0] = unapply(goal0);
  // destructuring: the start state, a parameter, is matched (`match st`): its fields are binders after the
  // context, and the goal and the context's facts are read with st as the constructor of them (as the
  // checker reads them in the case), so that accessors, updaters and facts compute alike; it prints as ws0
  const stArg = isRef(gh0, "tot") ? gargs0[1] : isRef(gh0, "wp") ? gargs0[4] : undefined;
  let stName = "", patText = "";
  let subst = (t: LTerm): LTerm => t;
  if (dst) {
    if (!stArg || stArg.$ !== "Var" || stArg.i < 0 || stArg.i >= g.d) return { why: "the start state is not a parameter (no match st)" };
    stName = names[stArg.i]!;
    names[stArg.i] = "_matched";
    const taken = new Set(names);
    const fs = ["wrg", "wcl", "wnx", "wfi", "wim", "wpg", "wlm", "win", "wou", "won"].map((b) => { let n = b; for (let i = 2; taken.has(n); i++) n = b + "_" + i; taken.add(n); return n; });
    const kc = K.cirOut ?? fail("no Cir.Out in the book");
    const C = B.Ctr((kc.includes(":") ? kc.slice(0, kc.indexOf(":") + 1) : "") + "Cir.State", fs.map((f, i) => B.Var(f, g.d + i))) as LTerm;
    for (const f of fs) names[D++] = f;
    env = null;
    patText = ctor("Cir.State") + "{" + fs.join(", ") + "}";
    const sk = api.key(stArg);
    subst = (t) => replaceKey(t, sk, C, api.key);
    dstKey = api.key(C);
    stateReps.push({ key: dstKey, ref: B.Ref("ws0") as LTerm });
  }
  // read again past the fields: the goal's own binders must not take their levels
  const goal = dst ? subst(api.lower(g.ty, D)) : goal0;
  const [gh, gargs] = unapply(goal);
  let code0: LTerm, st0: LTerm, bS: string, HS: string, KS: string, QS = "", wrap: (p: string) => string;
  if (isRef(gh, "tot") && gargs.length === 5) {
    code0 = gargs[0]!; st0 = gargs[1]!; bS = sh(gargs[2]!); HS = sh(gargs[4]!); QS = sh(gargs[3]!); KS = "";
    wrap = (p) => nm("totOfWp") + "(" + sh(code0) + ", " + sh(st0) + ", " + bS + ", " + KS + ", " + HS + ", " + p + ")";
  } else if (isRef(gh, "wp") && gargs.length === 5) {
    code0 = gargs[0]!; bS = sh(gargs[1]!); KS = sh(gargs[2]!); HS = sh(gargs[3]!); st0 = gargs[4]!;
    wrap = (p) => p;
  } else return { why: "not a Tot goal" };
  const gargsB = isRef(gh, "tot") ? gargs[2]! : gargs[1]!, gargsQ = isRef(gh, "tot") ? gargs[3]! : gargs[2]!;
  if ([bS, HS, KS].some((s) => s.includes("/"))) return { why: "a name of the goal is not reachable from this file (an import is missing)" };

  // the context's facts: registers and cells of a state, the register count, Bool facts
  const used = new Set(names);
  const fresh = (base: string) => { let s = base; for (let i = 2; used.has(s); i++) s = base + "_" + i; used.add(s); return s; };
  // the binders of the printed continuations: names that no parameter has (a parameter h or t would be captured)
  const BH = fresh("h"), BT = fresh("t"), BK = fresh("k"), BX = fresh("x");
  if (QS) KS = BH + " => " + QS;
  const regHyp = new Map<string, { c: LTerm; pf: string }>(); // key(state) + "|" + r
  const ctxFact = new Map<string, string>(); // key(type) -> a hypothesis of that type
  const ctxFactT: { T: LTerm; pf: string }[] = [];
  const nregHyp = new Map<string, { n: LTerm; pf: string }>(); // key(state)
  const cellHyp = new Map<string, string>(); // key(state) + "|" + key(nf(c))
  const boolHyp: { lhs: LTerm; nk: string; val: boolean; name: string }[] = [];
  const ltFact = new Map<string, string>(); // r -> a proof of {Nat.is_lt(r, St.nregs(st)) == True{}} (the start state)
  // a Bool fact {a == True/False}, and its conjuncts (bool.and_l / bool.and_r of a true &&): Bool facts for the ifs, and
  // facts r < St.nregs(st) for the sets (S2's invariants carry them so)
  const harvest = (a: LTerm, val: boolean, pf: string, depth: number) => {
    const n = nfL(a);
    if (n) boolHyp.push({ lhs: a, nk: api.key(n), val, name: pf });
    const [h, xs] = unapply(a);
    if (h.$ !== "Ref") return;
    // a Bool def (an invariant: Hp.H, Room, Fix): its body, one step unfolded, when that is an && (its
    // conjuncts are then facts too; the proof is the same term, by conversion)
    if (val && depth < 24 && !["Bool.and", "Bool.not", "Nat.is_lt", "Nat.is_eq", "Cir.is_cell"].includes(shortOf(h.k))) {
      const w = wnfL(a);
      if (w && w.$ === "App") { const [wh] = unapply(w); if (wh.$ === "Ref" && shortOf(wh.k) === "Bool.and") return harvest(w, val, pf, depth + 1); }
    }
    // Bool.not(a) == True: a == False (bool.not_t)
    if (val && shortOf(h.k) === "Bool.not" && xs.length === 1 && byShort.has("bool.not_t")) harvest(xs[0]!, false, sh(B.Ref(byShort.get("bool.not_t")!) as LTerm) + "(" + sh(xs[0]!) + ", " + pf + ")", depth + 1);
    if (!val) return;
    if (shortOf(h.k) === "Bool.and" && xs.length === 2 && depth < 24 && byShort.has("bool.and_l") && byShort.has("bool.and_r")) {
      const al = sh(B.Ref(byShort.get("bool.and_l")!) as LTerm), ar = sh(B.Ref(byShort.get("bool.and_r")!) as LTerm);
      harvest(xs[0]!, true, al + "(" + sh(xs[0]!) + ", " + sh(xs[1]!) + ", " + pf + ")", depth + 1);
      harvest(xs[1]!, true, ar + "(" + sh(xs[0]!) + ", " + sh(xs[1]!) + ", " + pf + ")", depth + 1);
    }
    // Cir.is_cell(c, St.image(st), St.first(st), St.next(st)): St.is_cell(st, c) unfolded
    if (shortOf(h.k) === "Cir.is_cell" && xs.length === 4) {
      const [ih, ia] = unapply(xs[1]!);
      const c = nfL(xs[0]!);
      if (c && ih.$ === "Ref" && shortOf(ih.k) === "St.image" && ia.length === 1) cellHyp.set(api.key(ia[0]!) + "|" + api.key(c), pf);
    }
    if (shortOf(h.k) === "Nat.is_eq" && xs.length === 2 && byShort.has("nat.is_eq_ok")) {
      const [nh, na] = unapply(xs[0]!);
      if (isRef(nh, "nregs") && na.length === 1 && !nregHyp.has(api.key(na[0]!)))
        nregHyp.set(api.key(na[0]!), { n: xs[1]!, pf: sh(B.Ref(byShort.get("nat.is_eq_ok")!) as LTerm) + "(" + sh(xs[0]!) + ", " + sh(xs[1]!) + ", " + pf + ")" });
    }
    if (shortOf(h.k) === "Nat.is_lt" && xs.length === 2) {
      const [nh, na] = unapply(xs[1]!);
      if (isRef(nh, "nregs") && na.length === 1 && api.key(na[0]!) === api.key(st0)) ltFact.set(rgOf(xs[0]!).key, pf);
    }
  };
  // a fact T with its proof pf: by its kind (a register, the count, a cell, a Bool invariant), and as itself
  const addFact = (T: LTerm, pf: string) => {
    ctxFact.set(api.key(T), pf);
    ctxFactT.push({ T, pf });
    if (T.$ !== "Eql") return;
    const [lh, la] = unapply(T.a);
    if (isRef(lh, "reg") && la.length === 2 && T.b.$ === "Ctr" && T.b.k === "Some" && T.b.x.length === 1) {
      regHyp.set(api.key(la[0]!) + "|" + rgOf(la[1]!).key, { c: T.b.x[0]!, pf });
      return;
    }
    if (isRef(lh, "nregs") && la.length === 1) { nregHyp.set(api.key(la[0]!), { n: T.b, pf }); return; }
    if (isRef(lh, "isCell") && la.length === 2 && T.b.$ === "Ctr" && T.b.k === "True") {
      const c = nfL(la[1]!);
      if (c) cellHyp.set(api.key(la[0]!) + "|" + api.key(c), pf);
      return;
    }
    if (isBool(T.b)) harvest(T.a, T.b.k === "True", pf, 0);
  };
  for (let i = 0; i < g.d; i++) {
    const a = B.pmap_get(g.ctx, i);
    if (!a || names[i] === "_" || names[i] === "" || /^w[sfnc]\d/.test(names[i]!)) continue;
    const T0 = api.attempt(FUEL, () => api.lower(a.T, dst ? D : i));
    if (T0) addFact(subst(T0), names[i]!);
  }
  // the helpers of the def being proven, <def>.<name>: their conclusions are facts, each parameter fixed by a
  // premise that a fact of the context fits (at most 32 helpers)
  if (g.self && api.instPrem) {
    const pre = shortOf(g.self) + ".";
    const hs = [...byShort].filter(([s2, k]) => s2.startsWith(pre) && k !== g.self).slice(0, 32);
    const facts = ctxFactT.slice();
    for (const [, k] of hs) {
      const ins = api.instPrem(k, facts, D);
      if (!ins || !ins.sol.every((v, i) => v || ins.pfs[i])) continue;
      addFact(ins.T, sh(B.Ref(k) as LTerm) + "(" + ins.sol.map((v, i) => (v ? sh(v) : ins.pfs[i]!)).join(", ") + ")");
    }
  }

  // the facts a law's premise may take: the context's, and the Bool facts (with their conjuncts)
  const lawFacts = (): { T: LTerm; pf: string }[] => [...ctxFactT, ...boolHyp.map((h) => ({ T: B.Eql(h.lhs, B.Ctr<[LTerm]>(h.val ? "True" : "False", []), B.Ref(byShort.get("Bool") ?? "Bool") as LTerm), pf: h.name }))];
  // a premise's proof: a fact of the context, a Bool fact, or {==} when it computes
  const premPf = (A: LTerm): string | undefined => {
    const pf = ctxFact.get(api.key(A));
    if (pf || A.$ !== "Eql") return pf;
    const n = nfL(A.a);
    if (isBool(A.b) && n) { const want = A.b.k === "True"; const h = boolHyp.find((x) => x.nk === api.key(n) && x.val === want); if (h) return h.name; }
    const nb = nfL(A.b);
    return n && nb && api.key(n) === api.key(nb) ? "{==}" : undefined;
  };
  // an equation law about a state that a function F builds (the start I.St0(..), or Alloc.st(..)): <f>.<what>,
  // f F's name in lower case (St0: st0.nregs; Alloc.st: alloc.reg); its premises from the facts or computed
  const eqLaws = new Map<string, string[]>();
  const eqLaw = (stt: LTerm, what: string, lhs: LTerm): { rhs: LTerm; pf: string } | null => {
    const [h] = unapply(stt);
    if (!api.instEq || h.$ !== "Ref") return null;
    const segs = shortOf(h.k).split(".");
    const base = (segs.length > 1 && segs[segs.length - 1] === "st" ? segs[segs.length - 2]! : segs[segs.length - 1]!).toLowerCase() + "." + what;
    let laws = eqLaws.get(base);
    if (!laws) {
      laws = [...byShort].filter(([s2, k]) => (s2 === base || s2.endsWith("." + base)) && !(g.self && (k === g.self || shortOf(k) === shortOf(g.self)))).map(([, k]) => k);
      eqLaws.set(base, laws);
    }
    for (const k of laws) {
      const ins = api.instEq(k, lhs, lawFacts(), D);
      if (!ins || ins.T.$ !== "Eql") continue;
      const args: string[] = [];
      for (let i = 0; i < ins.sol.length && args.length === i; i++) {
        const v = ins.sol[i], dm = ins.doms[i]!;
        const a = v ? sh(v) : ins.pfs[i] ?? (dm.fact && dm.A ? premPf(dm.A) : undefined);
        if (a !== undefined) args.push(a);
      }
      if (args.length === ins.sol.length) return { rhs: ins.T.b, pf: sh(B.Ref(k) as LTerm) + "(" + args.join(", ") + ")" };
    }
    return null;
  };
  if (!nregHyp.has(api.key(st0)) && K.nregs) {
    const f = eqLaw(st0, "nregs", B.App(ref("nregs"), st0));
    if (f) nregHyp.set(api.key(st0), { n: f.rhs, pf: f.pf });
  }

  // the states: 0 is the goal's; k is the state k-1 after a set (r, v) or a store (kf, c, v)
  type Op = "set" | "store" | "alloc" | "emit";
  type St = { text: string; key: string; lt: LTerm; prev: number; op: Op | null; r: Rg | null; c: LTerm | null; v: LTerm | null; p: string; scope: number };
  const sts: St[] = [{ text: sh(st0), key: api.key(st0), lt: st0, prev: -1, op: null, r: null, c: null, v: null, p: "", scope: 0 }];
  const OPS: Record<Op, { up: string; nregs: string; outn: string }> = {
    set: { up: "stSet", nregs: "nregsSet", outn: "outnSet" }, store: { up: "stStore", nregs: "nregsStore", outn: "outnStore" },
    alloc: { up: "stAlloc", nregs: "nregsAlloc", outn: "outnAlloc" }, emit: { up: "stEmit", nregs: "nregsEmit", outn: "outnEmit" },
  };
  // a let at the top (a state, a fact) when nothing in it is bound by a page binder; else the term itself
  const bind = (sc: number, base: string, type: string, value: string): string => {
    if (sc > 0) return "(" + value + ")";
    const name = fresh(base);
    lets.push("+" + name + " : " + type + " = " + value);
    return name;
  };
  const lets: string[] = [];
  stepRefs.push("@" + (K.stSet ?? "St.set"), "@" + (K.stStore ?? "St.store"), "@" + (K.stAlloc ?? "St.alloc"), "@" + (K.stEmit ?? "St.emit"));
  if (dst) {
    used.add(stName); used.add("ws0");
    lets.push("+ws0 : " + nm("cirState") + " = " + patText);
  }
  const regFacts = new Map<string, { c: LTerm; pf: string }>();
  const nregFacts = new Map<number, { n: string; pf: string }>();
  const MB = "Maybe<&2, U32>";
  const stepArgs = (s: St, p: St) => p.text + ", " + (s.op === "set" ? s.r!.text + ", " + sh(s.v!) : s.op === "store" ? s.r!.text + ", " + sh(s.c!) + ", " + sh(s.v!)
    : s.op === "alloc" ? s.r!.text + ", " + s.p : sh(s.v!) + ", " + s.p);
  // {St.nregs(st_j) == N}
  const nregOf = (j: number): { n: string; pf: string } => {
    const memo = nregFacts.get(j);
    if (memo) return memo;
    const s = sts[j]!;
    let out: { n: string; pf: string };
    if (s.prev < 0) {
      // no count fact: the count of the start itself (the sets then need facts r < its count)
      const h = nregHyp.get(s.key);
      out = h ? { n: sh(h.n), pf: h.pf } : { n: nm("nregs") + "(" + s.text + ")", pf: "{==}" };
    } else {
      const p = sts[s.prev]!, pn = nregOf(s.prev);
      const name = bind(s.scope, "wn" + j, "{" + nm("nregs") + "(" + s.text + ") == " + pn.n + " : Nat}", nm("equalTrans") + "(Nat, " + nm("nregs") + "(" + s.text + "), " + nm("nregs") + "(" + p.text + "), " + pn.n + ", " + nm(OPS[s.op!].nregs) + "(" + stepArgs(s, p) + "), " + pn.pf + ")");
      out = { n: pn.n, pf: name };
    }
    nregFacts.set(j, out);
    return out;
  };
  // {St.nregs(st_j) == St.nregs(st_0)}
  const relFacts = new Map<number, string>();
  const relOf = (j: number): string => {
    const memo = relFacts.get(j);
    if (memo) return memo;
    const s = sts[j]!;
    if (s.prev < 0) return "{==}";
    const p = sts[s.prev]!, s0 = nm("nregs") + "(" + sts[0]!.text + ")";
    const name = bind(s.scope, "wm" + j, "{" + nm("nregs") + "(" + s.text + ") == " + s0 + " : Nat}", nm("equalTrans") + "(Nat, " + nm("nregs") + "(" + s.text + "), " + nm("nregs") + "(" + p.text + "), " + s0 + ", " + nm(OPS[s.op!].nregs) + "(" + stepArgs(s, p) + "), " + relOf(s.prev) + ")");
    relFacts.set(j, name);
    return name;
  };
  // {Nat.is_lt(r, St.nregs(st_j)) == True{}}: by computation from a count fact (a number r), or from a
  // fact on the start (r < count, or r has a value: reg.lt) carried by the counts' relation
  const ltOf = (j: number, r: Rg): string => {
    const f = nregOf(j);
    const via = (h: string) => "(%" + nm("equalSym") + "(Nat, " + nm("nregs") + "(" + sts[j]!.text + "), " + f.n + ", " + f.pf + ") : {Nat.is_lt(" + r.text + ", _) == True{} : Bool}; " + h + ")";
    // a symbolic r, a known count N: a Bool fact r < N
    const n0 = nregHyp.get(sts[0]!.key);
    if (n0 && r.lit === null) {
      const z = nfL(B.App(B.App(B.Ref(byShort.get("Nat.is_lt") ?? "Nat.is_lt") as LTerm, r.term), n0.n));
      const h = z && boolHyp.find((x) => x.val && x.nk === api.key(z));
      if (h) return via(h.name);
    }
    if (!nregHyp.has(sts[0]!.key) || r.lit === null) {
      const h0 = regHyp.get(sts[0]!.key + "|" + r.key);
      const base = ltFact.get(r.key) ?? (h0 && K.regLt ? nm("regLt") + "(" + sts[0]!.text + ", " + r.text + ", " + sh(h0.c) + ", " + h0.pf + ")" : undefined)
        ?? fail(n0 ? "no fact {Nat.is_lt(" + r.text + ", " + sh(n0.n) + ") == True{}} in the context (the register " + r.text + " is written)"
          : "no fact {" + nm("nregs") + "(" + sts[0]!.text + ") == ..} nor {Nat.is_lt(" + r.text + ", " + nm("nregs") + "(" + sts[0]!.text + ")) == True{}} in the context");
      return j === 0 ? base : "(%" + nm("equalSym") + "(Nat, " + nm("nregs") + "(" + sts[j]!.text + "), " + nm("nregs") + "(" + sts[0]!.text + "), " + relOf(j) + ") : {Nat.is_lt(" + r.text + ", _) == True{} : Bool}; " + base + ")";
    }
    return via("{==}");
  };
  const sameReg = (r: Rg, q: Rg): boolean | string | null => {
    if (r.lit !== null && q.lit !== null) return r.lit === q.lit;
    if (r.key === q.key) return true;
    const eq = (a: Rg, b: Rg) => B.App(B.App(B.Ref(byShort.get("Nat.is_eq") ?? "Nat.is_eq") as LTerm, a.term), b.term);
    const z = nfL(eq(r, q));
    if (isBool(z)) return z.k === "True";
    const k1 = z ? api.key(z) : "", z2 = nfL(eq(q, r)), k2 = z2 ? api.key(z2) : "";
    for (const h of boolHyp) {
      if (h.val) continue;
      if (h.nk === k1) return h.name;
      if (h.nk === k2 && byShort.has("nat.is_eq_sym")) return nm("equalTrans") + "(Bool, Nat.is_eq(" + r.text + ", " + q.text + "), Nat.is_eq(" + q.text + ", " + r.text + "), False{}, " + sh(B.Ref(byShort.get("nat.is_eq_sym")!) as LTerm) + "(" + r.text + ", " + q.text + "), " + h.name + ")";
    }
    return null;
  };
  // {Reg(st_j, q) == Some{c}}
  const regOf = (j: number, q: Rg): { c: LTerm; pf: string } => {
    const mk = j + "|" + q.key;
    const memo = regFacts.get(mk);
    if (memo) return memo;
    const s = sts[j]!;
    let out: { c: LTerm; pf: string };
    if (s.prev < 0) {
      const h = regHyp.get(s.key + "|" + q.key);
      const e = h ? null : eqLaw(s.lt, "reg", B.App(B.App(ref("reg"), s.lt), q.term));
      if (h) out = h;
      else if (e && e.rhs.$ === "Ctr" && e.rhs.k === "Some" && e.rhs.x.length === 1) out = { c: e.rhs.x[0]!, pf: e.pf };
      else if (K.regSome && K.stReg) out = { c: B.App(B.App(ref("stReg"), s.lt), q.term), pf: nm("regSome") + "(" + s.text + ", " + q.text + ", " + ltOf(0, q) + ")" };
      else out = fail("no fact {" + nm("reg") + "(" + s.text + ", " + q.text + ") == Some{..}} in the context (register " + q.text + " is read)");
    }
    else {
      const p = sts[s.prev]!;
      const same = s.op === "set" || s.op === "alloc" ? sameReg(s.r!, q) : false;
      if (same === null) fail("the registers " + s.r!.text + " and " + q.text + ": no fact tells them apart ({Nat.is_eq(" + s.r!.text + ", " + q.text + ") == False{}})");
      const here = same === true;
      let law = s.op === "set" ? nm("regSet") + "(" + p.text + ", " + s.r!.text + ", " + sh(s.v!) + ", " + q.text + ", " + ltOf(s.prev, s.r!) + ")"
        : s.op === "store" ? nm("regStore") + "(" + p.text + ", " + s.r!.text + ", " + sh(s.c!) + ", " + sh(s.v!) + ", " + q.text + ")"
        : s.op === "alloc" ? nm("regAlloc") + "(" + p.text + ", " + s.r!.text + ", " + s.p + ", " + q.text + ", " + ltOf(s.prev, s.r!) + ")"
        : nm("regEmit") + "(" + p.text + ", " + sh(s.v!) + ", " + s.p + ", " + q.text + ")";
      // the register an alloc writes gets the old next
      const written = s.op === "alloc" ? B.App(ref("stNext"), p.lt) : s.v!;
      // told apart by a fact: the pick's condition rewritten to False
      // the same register, symbolic: the pick's condition Nat.is_eq(r, r) rewritten to True (nat.is_eq_refl)
      if ((s.op === "set" || s.op === "alloc") && here && q.lit === null && !isBool(nfL(B.App(B.App(B.Ref(byShort.get("Nat.is_eq") ?? "Nat.is_eq") as LTerm, s.r!.term), q.term)))) {
        const rf = byShort.get("nat.is_eq_refl") ?? fail("the register " + q.text + " is written, then read: no law nat.is_eq_refl in the book");
        law = "(%" + sh(B.Ref(rf) as LTerm) + "(" + q.text + ") : {" + nm("reg") + "(" + s.text + ", " + q.text + ") == Bool.pick(" + MB + ", _, Some{" + sh(written) + "}, " + nm("reg") + "(" + p.text + ", " + q.text + ")) : " + MB + "}; " + law + ")";
      }
      if ((s.op === "set" || s.op === "alloc") && !here && typeof same === "string") law = "(%" + same + " : {" + nm("reg") + "(" + s.text + ", " + q.text + ") == Bool.pick(" + MB + ", _, Some{" + sh(written) + "}, " + nm("reg") + "(" + p.text + ", " + q.text + ")) : " + MB + "}; " + law + ")";
      const c = here ? written : regOf(s.prev, q).c;
      const pf = here ? law : nm("equalTrans") + "(" + MB + ", " + nm("reg") + "(" + s.text + ", " + q.text + "), " + nm("reg") + "(" + p.text + ", " + q.text + "), Some{" + sh(c) + "}, " + law + ", " + regOf(s.prev, q).pf + ")";
      const name = bind(s.scope, "wf" + j + "_" + (q.lit ?? "r"), "{" + nm("reg") + "(" + s.text + ", " + q.text + ") == Some{" + sh(c) + "} : " + MB + "}", pf);
      out = { c, pf: name };
    }
    regFacts.set(mk, out);
    return out;
  };
  const push = (j: number, op: Op, r: Rg | null, c: LTerm | null, v: LTerm | null, pv: LTerm | null = null, pn = ""): number => {
    const p = sts[j]!;
    const sc = Math.max(p.scope, pv ? scope : 0);
    const lt = op === "set" ? B.App(B.App(B.App(ref("stSet"), p.lt), r!.term), v!) : op === "store" ? B.App(B.App(B.App(B.App(ref("stStore"), p.lt), r!.term), c!), v!)
      : op === "alloc" ? B.App(B.App(B.App(ref("stAlloc"), p.lt), r!.term), pv!) : B.App(B.App(B.App(ref("stEmit"), p.lt), v!), pv!);
    const s: St = { text: "", key: "", lt, prev: j, op, r, c, v, p: pn, scope: sc };
    s.text = bind(sc, "ws" + sts.length, nm("cirState"), nm(OPS[op].up) + "(" + stepArgs(s, p) + ")");
    s.key = "let:" + s.text;
    sts.push(s);
    if (sc === 0) stateReps.push({ key: api.key(lt), ref: B.Ref(s.text) as LTerm });
    return sts.length - 1;
  };

  // an expression's value at the state j, and the proof of {Cr.Cir.eval(e, st_j) == Some{v}}: its
  // rewrites (a register read by its fact; with dst, a field read's cell condition by its is_cell
  // fact) one by one, the first outermost, then the computation
  // the context's equations {a == u} over a value type (not Bool), by the key of a computed
  let valFactsM: Map<string, { rhs: LTerm; pf: string; A: LTerm }> | null = null;
  const valFacts = () => {
    if (valFactsM) return valFactsM;
    valFactsM = new Map();
    for (const f of ctxFactT) {
      if (f.T.$ !== "Eql" || (f.T.b.$ === "Ctr" && f.T.b.k === "Some") || isBool(f.T.b)) continue;
      const n = nfL(f.T.a);
      if (n && n.$ !== "Lit" && !valFactsM.has(api.key(n))) valFactsM.set(api.key(n), { rhs: f.T.b, pf: f.pf, A: f.T.T });
    }
    return valFactsM;
  };
  // how a fact gets in: a helper def (the def being proven has no room for a let before a match)
  const helperHint = g.self ? "; give it as a helper def " + shortOf(g.self) + ".<name>, its parameters those of " + shortOf(g.self)
    + " that its premises fix, its conclusion the fact over st (or an equation naming a part, e.g. a tag {U32.and(..) == Mc.T.ann()}): --wp uses it" : "";
  const evalAt = (e: LTerm, j: number): { v: LTerm; he: string } => {
    const S = sts[j]!.text;
    // orig: the part as the unfolded eval holds it; sub: its value; eq: {sub == orig}
    const rws: { orig: string; sub: string; eq: string }[] = [];
    type Tm = { tmpl: (cur: number) => string; val: LTerm; last: number };
    // a part's value that an equation of the context names ({v == u}, v as computed): u, by one more rewrite
    const go = (x: LTerm): Tm => {
      const r = go0(x);
      const fs = valFacts();
      if (fs.size === 0) return r;
      const n = nfL(r.val);
      if (!n || n.$ !== "Ctr" || n.k !== "Some" || n.x.length !== 1) return r;
      const f = fs.get(api.key(n.x[0]!));
      if (!f) return r;
      const orig = sh(n.x[0]!), sub = sh(f.rhs);
      rws.push({ orig, sub, eq: nm("equalSym") + "(" + sh(f.A) + ", " + orig + ", " + sub + ", " + f.pf + ")" });
      const vi = rws.length - 1, last = r.last;
      const at = (cur: number) => (vi < cur ? sub : vi === cur ? "_" : orig);
      return { tmpl: (cur) => (last < cur ? "Some{" + at(cur) + "}" : r.tmpl(cur)), val: B.Ctr<[LTerm]>("Some", [f.rhs]), last: vi };
    };
    const go0 = (x: LTerm): Tm => {
      const w = wnfL(x) ?? fail("an expression does not evaluate: " + sh(x).slice(0, 120));
      if (w.$ !== "Ctr") fail("an expression with no constructor form: " + sh(x).slice(0, 120));
      const c = w as Extract<LTerm, { $: "Ctr" }>;
      const at = (i: number) => (cur: number) => (i < cur ? rws[i]!.sub : i === cur ? "_" : rws[i]!.orig);
      switch (shortOf(c.k)) {
        case "Cir.Expr.const": { const n = c.x[0]!; const t = "Some{" + sh(n) + "}"; return { tmpl: () => t, val: B.Ctr<[LTerm]>("Some", [n]), last: rws.length - 1 }; }
        case "Cir.Expr.get": {
          const q = rgOf(c.x[0]!);
          const f = regOf(j, q);
          const orig = nm("reg") + "(" + S + ", " + q.text + ")", sub = "Some{" + sh(f.c) + "}";
          rws.push({ orig, sub, eq: nm("equalSym") + "(" + MB + ", " + orig + ", " + sub + ", " + f.pf + ")" });
          return { tmpl: at(rws.length - 1), val: B.Ctr<[LTerm]>("Some", [f.c]), last: rws.length - 1 };
        }
        case "Cir.Expr.op": {
          const o = sh(c.x[0]!);
          if (o.includes("/")) fail("the Wasm ops are not named in this file: it needs an import of Wasm/impl.bend");
          const a = go(c.x[1]!), b = go(c.x[2]!);
          return { tmpl: (cur) => nm("evalOp") + "(" + o + ", " + a.tmpl(cur) + ", " + b.tmpl(cur) + ")", val: B.App(B.App(B.App(ref("evalOp"), c.x[0]!), a.val), b.val), last: rws.length - 1 };
        }
        case "Cir.Expr.eqz": { const a = go(c.x[0]!); return { tmpl: (cur) => nm("evalEqz") + "(" + a.tmpl(cur) + ")", val: B.App(ref("evalEqz"), a.val), last: rws.length - 1 }; }
        case "Cir.Expr.field": {
          if (!dst) fail("a field read: --wp reads fields only when the proof can match the start state (a state that is a parameter)");
          const kf = natOf(c.x[0]!);
          if (kf === null) fail("a field read with a field that is not a number");
          const a = go(c.x[1]!);
          const iv = nfL(a.val);
          if (!iv || iv.$ !== "Ctr" || iv.k !== "Some") fail("a field read whose cell has no value");
          const I = (iv as Extract<LTerm, { $: "Ctr" }>).x[0]!;
          const ik = nfL(I);
          const hi = cellHyp.get(sts[0]!.key + "|" + (ik ? api.key(ik) : "")) ?? fail("a field read of the cell " + sh(I) + ": no fact {" + nm("isCell") + "(st, " + sh(I) + ") == True{}}" + helperHint);
          const orig = nm("isCell") + "(" + S + ", " + sh(I) + ")";
          rws.push({ orig, sub: "True{}", eq: nm("equalSym") + "(Bool, " + orig + ", True{}, " + hi + ")" });
          const ci = rws.length - 1, lastA = a.last;
          const ifT = (cur: number) => nm("fieldIf") + "(" + at(ci)(cur) + ", " + kf + "n, " + nm("stCells") + "(" + S + "), " + sh(I) + ")";
          // before the cell's own reads are rewritten, the read is as eval holds it
          return {
            tmpl: (cur) => (lastA < cur ? ifT(cur) : nm("evalField") + "(" + kf + "n, " + a.tmpl(cur) + ", " + S + ")"),
            val: B.Ctr<[LTerm]>("Some", [B.App(B.App(ref("cellGet"), B.Lit("Nat", kf!) as LTerm), B.App(B.App(ref("cellsGet"), B.App(ref("stCells"), sts[j]!.lt)), I))]),
            last: ci,
          };
        }
        case "Cir.Expr.size": case "Cir.Expr.byte": {
          // the input's size, or its byte i: computed from the state's input (a constructor form: the start
          // is one, or the proof matches it)
          const kind = shortOf(c.k).replace(/^Cir\.Expr\./, "");
          const rf = (n: string): LTerm => B.Ref(byShort.get(n) ?? fail("no " + n + " in the book")) as LTerm;
          const a = kind === "byte" ? go(c.x[0]!) : null;
          const lt = sts[j]!.lt;
          const v = nfL(a ? B.App(B.App(rf("Cir.eval.byte"), a.val), B.App(rf("Cir.eval.input"), lt)) : B.App(rf("Cir.eval.size"), lt));
          if (!v || v.$ !== "Ctr" || v.k !== "Some" || v.x.length !== 1) return fail("a " + kind + " read at " + S + ": the state's input has no constructor form (a whole body whose state is a parameter matches it)");
          const t = "Some{" + sh(v.x[0]!) + "}";
          return { tmpl: a ? (cur) => sh(rf("Cir.eval.byte")) + "(" + a.tmpl(cur) + ", " + sh(rf("Cir.eval.input")) + "(" + S + "))" : () => t, val: v, last: rws.length - 1 };
        }
        default: return fail("a " + shortOf(c.k).replace(/^Cir\.Expr\./, "") + " read: not stepped by --wp");
      }
    };
    const t = go(e);
    const n = nfL(t.val);
    if (!n || n.$ !== "Ctr" || n.k !== "Some" || n.x.length !== 1) fail("an expression's value is not Some{..}: " + sh(e).slice(0, 120));
    const v = (n as Extract<LTerm, { $: "Ctr" }>).x[0]!;
    let he = "{==}";
    for (let i = rws.length - 1; i >= 0; i--) he = "(%" + rws[i]!.eq + " : {" + t.tmpl(i) + " == Some{" + sh(v) + "} : " + MB + "}; " + he + ")";
    return { v, he };
  };

  // a law that is the def being proven (or the law it fills) is never suggested: that would be circular
  const isSelf = (short: string) => !!g.self && (shortOf(g.self) === short || shortOf(g.self).endsWith("." + short));
  // the rest of a proof under the page binder of an alloc or an emit: the binder extends the context
  // (its name prints; terms over it are not let-bound), then is dropped
  const underPages = (j: number, mk: (pn: string, pv: LTerm) => number, body: (pn: string, j2: number) => string): string => {
    const pn = fresh("wp" + j);
    names[D] = pn;
    const pv = B.Var(pn, D) as LTerm;
    D++; scope++; env = null;
    try { return body(pn, mk(pn, pv)); } finally { D--; scope--; env = null; names.length = D; }
  };
  // a fact of the context whose type prints as T (by its key, or as it prints)
  const factFor = (T: string): string | undefined => {
    for (const f of ctxFactT) if (sh(f.T) === T) return f.pf;
    for (const h of boolHyp) if ("{" + sh(h.lhs) + " == " + (h.val ? "True{}" : "False{}") + " : Bool}" === T) return h.name;
    return undefined;
  };
  // {St.outn(st_j) == 0}: from a fact on the start, carried by outn.set / outn.store / outn.alloc (an emit adds 1)
  const outnZero = (j: number): string | undefined => {
    if (!K.stOutn) return undefined;
    const s0 = sts[0]!;
    let base: string | undefined;
    for (const f of ctxFactT) {
      if (f.T.$ !== "Eql") continue;
      const [h, xs] = unapply(f.T.a);
      if (h.$ === "Ref" && h.k === K.stOutn && xs.length === 1 && api.key(xs[0]!) === s0.key) { const z = nfL(f.T.b); if (z && z.$ === "Lit" && z.v === 0) base = f.pf; }
    }
    if (!base) return undefined;
    // the chain back to the start: each step keeps outn (no emit in between)
    let pf = base, cur = 0;
    const chain: number[] = [];
    for (let i = j; i > 0; i = sts[i]!.prev) chain.push(i);
    for (const i of chain.reverse()) {
      const st2 = sts[i]!, p = sts[st2.prev]!;
      if (st2.op === "emit" || !K[OPS[st2.op!].outn]) return undefined;
      pf = nm("equalTrans") + "(U32, " + nm("stOutn") + "(" + st2.text + "), " + nm("stOutn") + "(" + p.text + "), 0, " + nm(OPS[st2.op!].outn) + "(" + stepArgs(st2, p) + "), " + pf + ")";
      cur = i;
    }
    void cur;
    return pf;
  };
  // the registers a loop reads and writes (its code walked, at most 400 nodes)
  const regsOfLoop = (c: LTerm, body: LTerm): { reads: Rg[]; writes: Rg[] } => {
    const reads = new Map<string, Rg>(), writes = new Map<string, Rg>();
    let n = 0;
    const go = (t: LTerm) => {
      if (++n > 400) return;
      const w = wnfL(t);
      if (!w || w.$ !== "Ctr") return;
      const x = w.x;
      switch (shortOf(w.k)) {
        case "Cir.Expr.get": { const r = rgOf(x[0]!); reads.set(r.key, r); return; }
        case "Cir.Stmt.set": case "Cir.Stmt.alloc": { const r = rgOf(x[0]!); writes.set(r.key, r); if (x[1]) go(x[1]); return; }
        case "Cir.Expr.const": case "Cir.Stmt.halt": case "Cir.Stmt.nop": case "Cir.Expr.size": return;
        case "Cir.Expr.field": case "Cir.Stmt.store": x.slice(1).forEach(go); return;
        default: x.forEach(go);
      }
    };
    go(c); go(body);
    return { reads: [...reads.values()], writes: [...writes.values()] };
  };
  // a loop with no law: tot.while's exact obligations, and an invariant skeleton over its registers
  const loopHint = (sText: string, c: LTerm, body: LTerm, j: number, k: Cont): string => {
    const S = sts[j]!.text;
    const { reads, writes } = regsOfLoop(c, body);
    const now = (r: Rg) => { try { return r.text + " = " + sh(regOf(j, r).c); } catch { return r.text + " (no fact)"; } };
    const lines = [
      "a loop at " + S + ", no routine law: prove its WP (its Tot) with Lg.tot.while; replace this ?TODO by",
      "  " + nm("wpOfTot") + "(" + sText + ", " + S + ", " + bS + ", " + kText(k) + ", " + HS + ", " + nm("totWhile") + "(" + sh(c) + ", " + sh(body) + ", " + bS + ", I, " + (k === null && QS ? QS : BX + " => " + kApp(k, BX)) + ", " + HS + ", r, n0, " + S + ", i))",
      "  I : Nat -> Cr.Cir.State -> Type, the invariant at the measure n, e.g. n => x => {" + nm("nregs") + "(x) == Mc.Mach.regs() : Nat} & "
        + (writes.map((w) => "{" + nm("reg") + "(x, " + w.text + ") == Some{..} : Maybe<&2, U32>}").join(" & ") || "..") + " & <the facts the rest needs>",
      "  r : @n: Nat -> @x: Cr.Cir.State -> I(n, x) -> Lg.Loop(" + sh(c) + ", <body>, x, " + bS + ", n, I, Q, " + HS + ")  (a round: the condition's value; at 0 the post; else the body's WP to I at a smaller n)",
      "  i : I(n0, " + S + ");  n0: a measure, e.g. the number of rounds left (U32.to_nat of the register the condition tests)",
      "  the loop reads " + (reads.map(now).join(", ") || "no register") + "; writes " + (writes.map((w) => w.text).join(", ") || "no register"),
    ];
    return lines.join("\n#     ");
  };
  // the code: a statement's constructor, with its parts as written
  const stmtOf = (s: LTerm): { k: string; x: LTerm[] } => {
    const w = wnfL(s) ?? fail("a statement does not evaluate: " + sh(s).slice(0, 120));
    if (w.$ !== "Ctr") fail("a statement with no constructor form: " + sh(s).slice(0, 120));
    return { k: shortOf((w as any).k), x: (w as any).x };
  };
  // a routine with a law: <name>.spec for a call of M.<name> (the plan's convention)
  const lawOf = (s: LTerm): string | null => {
    const [h] = unapply(s);
    if (h.$ !== "Ref") return null;
    const sn = shortOf(h.k).replace(/^M\./, "");
    if (/^(set|st|do|if|when|while|halt|c|g|f|add|sub|and|or|shl|shr|eq|ne|lt|le|gt|ge|not)$/.test(sn)) return null;
    for (const [s2, k] of byShort) if ((s2 === sn + ".spec" || s2.endsWith("." + sn + ".spec")) && k !== g.self && shortOf(k) !== shortOf(g.self ?? "")) return k;
    return null;
  };

  // continuations: the post of a statement is the goal's K, or "then the WP of code from there"
  // (list: code is the suffix i of a flattened sequence, whose statements are not read again)
  type Seq = { items: LTerm[]; texts: string[]; suf: string[]; tail: LTerm };
  type Cont = { code: string; term: LTerm; next: Cont; list?: { seq: Seq; i: number } } | null;
  const kText = (k: Cont): string => (k === null ? KS : BH + " => " + BT + " => " + nm("wp") + "(" + k.code + ", " + bS + ", " + kText(k.next) + ", " + BH + ", " + BT + ")");
  const leaves: WpLeaf[] = [];
  const leaf = (hint: string): string => { leaves.push({ hole: leaves.length + 1, hint }); return "?TODO"; };
  let steps = 0, splits = 0;
  const over = () => steps >= MAX_STEPS || performance.now() > api.deadline;
  const overLeaf = (j: number) => leaf((steps >= MAX_STEPS ? "the step limit (" + MAX_STEPS + ")" : "the time budget") + ": the rest of the code from " + sts[j]!.text);
  const codeLet = (t: string): string => {
    if (/^[A-Za-z_][\w.]*$/.test(t) || t.length < 60) return t;
    const name = fresh("wc" + lets.length);
    lets.push("+" + name + " : " + nm("cirStmt") + " = " + t);
    return name;
  };
  // the proof of K(H, st_j) for the continuation k
  const post = (k: Cont, j: number): string =>
    k === null ? leaf("the post at the final state " + sts[j]!.text)
      : k.list ? proveList(k.list.seq, k.list.i, j, k.next) : prove(k.code, k.term, j, k.next);
  // the proof of WP(suffix i of the sequence, b, kText(k), H, st_j)
  const proveList = (L: Seq, i: number, j: number, k: Cont): string =>
    i === L.items.length ? prove(L.suf[i]!, L.tail, j, k) : prove(L.texts[i]!, L.items[i]!, j, { code: L.suf[i + 1]!, term: L.tail, next: k, list: { seq: L, i: i + 1 } });
  // K(H, x) for the continuation k, applied (beta-reduced)
  const kApp = (k: Cont, x: string): string =>
    k === null ? (QS ? QS + "(" + x + ")" : KS + "(" + HS + ", " + x + ")") : nm("wp") + "(" + k.code + ", " + bS + ", " + kText(k.next) + ", " + HS + ", " + x + ")";
  // a call of a routine with its law L: WP(call, b, K, H, st) by wp.of_tot from tot.wk of L, instantiated at
  // the call: L's parameters from the call's code and state, its premises from the context (facts, Bool
  // conjuncts) or leaves; the weakening's posts: Q_L implies K (a leaf, unless Q_L is the goal's own post),
  // H_L implies H (identity, or Empty for Lg.No); its budget b_L <= b by computation (or a leaf)
  const callLaw = (law: string, sText: string, term: LTerm, j: number, k: Cont): string | null => {
    const S = sts[j]!.text;
    const ins = api.inst?.(law, term, sts[j]!.lt, gargsB, lawFacts(), D);
    if (!ins || ins.concl.length !== 5) return null;
    const [bL, QL, HL] = [ins.concl[2]!, ins.concl[3]!, ins.concl[4]!];
    const lawName = sh(B.Ref(law) as LTerm);
    const args: string[] = [];
    for (let i = 0; i < ins.sol.length; i++) {
      const v = ins.sol[i];
      if (v) { args.push(sh(v)); continue; }
      if (ins.pfs[i]) { args.push(ins.pfs[i]!); continue; }
      const dm = ins.doms[i]!;
      if (!dm.fact || !dm.A) return null;
      args.push(premPf(dm.A) ?? leaf("the premise " + dm.k + " of " + lawName + " at " + S + ": " + sh(dm.A).slice(0, 300)));
    }
    const lawApp = lawName + "(" + args.join(", ") + ")";
    const bLS = sh(bL);
    const isLe = (() => { const z = nfL(B.App(B.App(B.Ref(byShort.get("Nat.is_le") ?? "Nat.is_le") as LTerm, bL), gargsB)); return isBool(z) && z.k === "True"; })();
    const hb = isLe ? "{==}" : bLS === bS && K.leRefl ? nm("leRefl") + "(" + bS + ")" : leaf("the budget of " + lawName + ": {Nat.is_le(" + bLS + ", " + bS + ") == True{}}");
    const x = fresh("wx"), q = fresh("wq"), kk = fresh("wk"), e = fresh("we");
    const Q2 = x + " => " + kApp(k, x);
    const hq = k === null && QS && api.key(QL) === api.key(gargsQ) ? x + " => " + q + " => " + q
      : x + " => " + q + " => " + leaf("after " + lawName + " at " + S + ": the rest from the state " + x + ", with " + q + " : " + sh(QL) + "(" + x + ")");
    const hh = sh(HL) === HS ? kk + " => " + x + " => " + e + " => " + e
      : /(^|\.)No$/.test(sh(HL)) ? kk + " => " + x + " => " + e + " => Empty.absurd(" + HS + "(" + kk + ", " + x + "), " + e + ")"
      : leaf("the halts of " + lawName + " (" + sh(HL) + ") as the goal's (" + HS + ")");
    return nm("wpOfTot") + "(" + sText + ", " + S + ", " + bS + ", " + kText(k) + ", " + HS + ", " + nm("totWk") + "(" + sText + ", " + S + ", " + bLS + ", " + bS + ", " + sh(QL) + ", " + Q2 + ", " + sh(HL) + ", " + HS + ", " + hb + ", " + hq + ", " + hh + ", " + lawApp + "))";
  };
  // the proof of WP(s, b, kText(k), H, st_j); sText is the code as printed (or its let)
  const prove = (sText: string, term: LTerm, j: number, k: Cont): string => {
    const S = sts[j]!.text;
    if (over()) return overLeaf(j);
    steps++;
    const law = lawOf(term);
    if (law) return callLaw(law, sText, term, j, k) ?? leaf("a routine with a law: close its WP by Lg.wp.of_tot with " + sh(B.Ref(law) as LTerm) + " and Lg.tot.wk (at " + S + "); gen2 could not instantiate the law from the call and the context");
    const st = stmtOf(term);
    const Kt = kText(k);
    switch (st.k) {
      case "Cir.Stmt.nop":
        return post(k, j);
      case "Cir.Stmt.seq": {
        // the spine, flattened: the suffixes are lets built from the end, each statement printed once
        const items: LTerm[] = [st.x[0]!];
        let tail = st.x[1]!;
        for (let n = 0; n < 4000; n++) { const t = stmtOf(tail); if (t.k !== "Cir.Stmt.seq") break; items.push(t.x[0]!); tail = t.x[1]!; }
        const texts = items.map((x) => codeLet(sh(x)));
        const suf: string[] = new Array(items.length + 1);
        suf[items.length] = codeLet(sh(tail));
        for (let i = items.length - 1; i >= 1; i--) {
          const name = fresh("wc" + i);
          lets.push("+" + name + " : " + nm("cirStmt") + " = " + ctor("Cir.Stmt.seq") + "{" + texts[i] + ", " + suf[i + 1] + "}");
          suf[i] = name;
        }
        suf[0] = sText;
        steps--;
        return proveList({ items, texts, suf, tail }, 0, j, k);
      }
      case "Cir.Stmt.set": {
        const [rT, e] = st.x as [LTerm, LTerm];
        const r = rgOf(rT);
        let ev: { v: LTerm; he: string }, hr: string;
        try { ev = evalAt(e, j); hr = ltOf(j, r); } catch (x) { if (x instanceof Fail) return leaf("set " + r.text + " at " + S + ": " + x.why); throw x; }
        const j2 = push(j, "set", r, null, ev.v);
        return nm("wpSet") + "(" + r.text + ", " + sh(e) + ", " + S + ", " + bS + ", " + Kt + ", " + HS + ", " + sh(ev.v) + ", " + ev.he + ", " + hr + ", " + post(k, j2) + ")";
      }
      case "Cir.Stmt.store": {
        const [kfT, c, e] = st.x as [LTerm, LTerm, LTerm];
        const kf = natOf(kfT);
        if (kf === null) return leaf("a store to a field that is not a number: " + sh(kfT));
        let ec: { v: LTerm; he: string }, ee: { v: LTerm; he: string };
        try { ec = evalAt(c, j); ee = evalAt(e, j); } catch (x) { if (x instanceof Fail) return leaf("store " + kf + " at " + S + ": " + x.why); throw x; }
        const ck = nfL(ec.v);
        // the cell fact: for this state, or the start's when the start is a destructured state (its
        // is_cell then computes to the same term after sets and stores)
        const hi = cellHyp.get(sts[j]!.key + "|" + (ck ? api.key(ck) : "")) ?? (st0.$ === "Ctr" || dst ? cellHyp.get(sts[0]!.key + "|" + (ck ? api.key(ck) : "")) : undefined);
        if (!hi) return leaf("store " + kf + " at " + S + ": no fact {" + nm("isCell") + "(" + S + ", " + sh(ec.v) + ") == True{}} (" + (j > 0 ? "match st at the start, then the start's fact serves" : "give it") + ")");
        const j2 = push(j, "store", rgOf(kfT), ec.v, ee.v);
        return nm("wpStore") + "(" + kf + "n, " + sh(c) + ", " + sh(e) + ", " + S + ", " + bS + ", " + Kt + ", " + HS + ", " + sh(ec.v) + ", " + sh(ee.v) + ", " + ec.he + ", " + ee.he + ", " + hi + ", " + post(k, j2) + ")";
      }
      case "Cir.Stmt.if": {
        const [c, y, n] = st.x as [LTerm, LTerm, LTerm];
        let ev: { v: LTerm; he: string };
        try { ev = evalAt(c, j); } catch (x) { if (x instanceof Fail) return leaf("an if at " + S + ": its condition: " + x.why); throw x; }
        const yT = codeLet(sh(y)), nT = codeLet(sh(n));
        const Y = BK + " => " + BH + " => " + nm("wp") + "(" + yT + ", " + bS + ", " + BK + ", " + BH + ", " + S + ")", N = BK + " => " + BH + " => " + nm("wp") + "(" + nT + ", " + bS + ", " + BK + ", " + BH + ", " + S + ")";
        const pickOf = (z: string) => nm("wpPick") + "(" + z + ", " + Y + ", " + N + ", " + Kt + ", " + HS + ")";
        const head = "(%" + nm("equalSym") + "(" + MB + ", " + nm("cirEval") + "(" + sh(c) + ", " + S + "), Some{" + sh(ev.v) + "}, " + ev.he + ") : " + nm("wpIf") + "(_, " + Y + ", " + N + ", " + Kt + ", " + HS + "); ";
        // z = U32.is_zero(v): False is the yes branch
        const z = nfL(B.App(ref("isZero"), ev.v));
        const branch = (zv: boolean) => (zv ? prove(nT, n, j, k) : prove(yT, y, j, k));
        if (isBool(z)) return head + branch(z.k === "True") + ")";
        // Bool facts on parts of z (in normal form), one rewrite each, until z computes
        if (z) {
          const HOLE = B.Ref("_") as LTerm;
          let cur: LTerm = z;
          const used2: { h: (typeof boolHyp)[number]; P: string }[] = [];
          for (const h of boolHyp) {
            const r = replaceKey(cur, h.nk, HOLE, api.key);
            if (r === cur) continue;
            used2.push({ h, P: pickOf(sh(r)) });
            cur = replaceKey(cur, h.nk, B.Ctr<[LTerm]>(h.val ? "True" : "False", []), api.key);
            const c2 = nfL(cur);
            if (isBool(c2)) {
              let pf = branch(c2.k === "True");
              for (let i = used2.length - 1; i >= 0; i--) {
                const u = used2[i]!;
                pf = "(%" + nm("equalSym") + "(Bool, " + sh(u.h.lhs) + ", " + (u.h.val ? "True{}" : "False{}") + ", " + u.h.name + ") : " + u.P + "; " + pf + ")";
              }
              return head + pf + ")";
            }
          }
        }
        // a split on the smallest Bool part of z that decides it both ways (by the kit's bool.case:
        // each branch gets the fact {part == True/False}, which later ifs may use too)
        if (z && K.boolCase && splits < MAX_SPLITS) {
          const parts = new Map<string, LTerm>();
          const walk = (t: LTerm) => { parts.set(api.key(t), t); if (t.$ === "App") { walk(t.f); walk(t.x); } else if (t.$ === "Ctr") t.x.forEach(walk); };
          walk(z);
          // a part that is a call of a def whose result is a Bool
          const isBoolCall = (t: LTerm): boolean => {
            const [h] = unapply(t);
            const d = h.$ === "Ref" ? api.RAW[h.k] : undefined;
            if (d?.$ !== "Def") return false;
            let T = api.attempt(FUEL, () => api.lower(d.T, 0));
            for (let i = 0; T && i < d.n; i++) T = T.$ === "All" ? (T.B as LTerm) : undefined;
            return !!T && (T.$ === "Ref" || T.$ === "ADT") && shortOf(T.k) === "Bool";
          };
          const cands = [...parts.values()].filter((t) => t.$ === "App" && isBoolCall(t)).sort((a, b) => sh(a).length - sh(b).length);
          for (const p of cands.slice(0, 24)) {
            const pk = api.key(p);
            const zt = nfL(replaceKey(z, pk, B.Ctr<[LTerm]>("True", []), api.key)), zf = nfL(replaceKey(z, pk, B.Ctr<[LTerm]>("False", []), api.key));
            if (!isBool(zt) || !isBool(zf)) continue;
            const P = pickOf(sh(replaceKey(z, pk, B.Ref("_") as LTerm, api.key)));
            const arm = (val: boolean, zv: Extract<LTerm, { $: "Ctr" }>) => {
              const hn = fresh(val ? "wt" : "wu");
              boolHyp.push({ lhs: p, nk: pk, val, name: hn });
              splits++;
              const pf = branch(zv.k === "True");
              splits--;
              boolHyp.pop();
              return hn + " => (%" + nm("equalSym") + "(Bool, " + sh(p) + ", " + (val ? "True{}" : "False{}") + ", " + hn + ") : " + P + "; " + pf + ")";
            };
            return head + nm("boolCase") + "(" + sh(p) + ", " + pickOf(sh(z)) + ", " + arm(true, zt) + ", " + arm(false, zf) + "))";
          }
        }
        return head + leaf("an if at " + S + " that no fact decides: U32.is_zero(" + sh(ev.v) + "); give a Bool fact on a part of it" + helperHint + (K.boolCase ? "" : ", or add the kit lemma bool.case (see gen2-wp-notes.md) so --wp splits it")) + ")";
      }
      case "Cir.Stmt.while":
        {
          let h = "a loop at " + S;
          if (!isSelf("tot.while")) try { h = loopHint(sText, st.x[0]!, st.x[1]!, j, k); } catch (x) { if (!(x instanceof Fail)) throw x; }
          return leaf(h);
        }
      case "Cir.Stmt.halt":
        return leaf("a halt at " + S + ": " + HS + "(its status, " + S + ")" + (/\bNo\b/.test(HS) ? " is Empty: a fact must rule this path out" : ""));
      case "Cir.Stmt.alloc": {
        if (!K.wpAlloc || isSelf("wp.alloc") || !K.stAlloc || !K.regAlloc || !K.nregsAlloc) return leaf("an alloc at " + S + (isSelf("wp.alloc") ? "" : ": apply Lg.wp.alloc (it asks St.outn == 0 and the budget 20 (next + 1) <= b)"));
        const r = rgOf(st.x[0]!);
        let hr: string;
        try { hr = ltOf(j, r); } catch (x) { if (x instanceof Fail) return leaf("alloc " + r.text + " at " + S + ": " + x.why); throw x; }
        const ho = outnZero(j) ?? leaf("alloc " + r.text + " at " + S + ": the output has not begun: {" + nm("stOutn") + "(" + S + ") == 0 : U32}");
        const need = "Nat.mul(20n, Nat.add(U32.to_nat(" + nm("stNext") + "(" + S + ")), 1n))";
        const hb = factFor("{Nat.is_le(" + need + ", " + bS + ") == True{} : Bool}") ?? leaf("alloc " + r.text + " at " + S + ": the budget: {Nat.is_le(" + need + ", " + bS + ") == True{}}");
        return underPages(j, (pn, pv) => push(j, "alloc", r, null, null, pv, pn), (pn, j2) =>
          nm("wpAlloc") + "(" + r.text + ", " + S + ", " + bS + ", " + Kt + ", " + HS + ", " + hr + ", " + ho + ", " + hb + ", " + pn + " => " + post(k, j2) + ")");
      }
      case "Cir.Stmt.emit": {
        if (!K.wpEmit || isSelf("wp.emit") || !K.stEmit || !K.regEmit || !K.nregsEmit) return leaf("an emit at " + S + (isSelf("wp.emit") ? "" : ": apply Lg.wp.emit (it asks the budget 20 next + outn + 1 <= b)"));
        const e = st.x[0]!;
        let ev: { v: LTerm; he: string };
        try { ev = evalAt(e, j); } catch (x) { if (x instanceof Fail) return leaf("emit at " + S + ": " + x.why); throw x; }
        const need = "Nat.add(Nat.mul(20n, U32.to_nat(" + nm("stNext") + "(" + S + "))), Nat.add(U32.to_nat(" + nm("stOutn") + "(" + S + ")), 1n))";
        const hb = factFor("{Nat.is_le(" + need + ", " + bS + ") == True{} : Bool}") ?? leaf("emit at " + S + ": the budget: {Nat.is_le(" + need + ", " + bS + ") == True{}}");
        return underPages(j, (pn, pv) => push(j, "emit", null, null, ev.v, pv, pn), (pn, j2) =>
          nm("wpEmit") + "(" + sh(e) + ", " + S + ", " + bS + ", " + Kt + ", " + HS + ", " + sh(ev.v) + ", " + ev.he + ", " + hb + ", " + pn + " => " + post(k, j2) + ")");
      }
      default:
        return leaf("the statement " + st.k + " at " + S + ": not stepped by --wp");
    }
  };

  const body = wrap(prove(codeLet(sh(code0)), code0, 0, null));
  if (dst) return { text: "match " + stName + ":\n  case " + patText + ":\n" + [...lets, body].map((l) => "    " + l).join("\n"), leaves, steps };
  return { text: [...lets, body].join("\n"), leaves, steps };
};
