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
export type WpGoal = { ctx: B.Ctx; d: number; ty: HTerm; names: string[] };
export type WpApi = {
  RAW: Record<string, B.TLD>;
  show: (t: LTerm, names: string[]) => string;
  lower: (h: HTerm, d: number) => LTerm;
  nf: (h: HTerm, d: number) => LTerm;
  wnf: (h: HTerm) => HTerm | undefined;
  attempt: <T>(n: number, f: () => T) => T | undefined;
  key: (t: LTerm) => string;
  deadline: number;
};
export type WpLeaf = { hole: number; hint: string };
export type WpOut = { text: string; leaves: WpLeaf[]; steps: number } | { why: string };

// ---- constants ----
const MAX_STEPS = 400;
const FUEL = 100000;
// logical name -> the short names (key less its namespace) it may have; the first found wins
const NAMES: Record<string, string[]> = {
  tot: ["Tot"], wp: ["WP"], wpIf: ["WP.if"], wpPick: ["WP.pick"], reg: ["Reg"],
  nregs: ["St.nregs"], isCell: ["St.is_cell"], stSet: ["St.set"], stStore: ["St.store"],
  totOfWp: ["tot.of_wp"], wpSet: ["wp.set"], wpStore: ["wp.store"],
  regSet: ["reg.set"], regStore: ["reg.store"], nregsSet: ["nregs.set"], nregsStore: ["nregs.store"],
  evalOp: ["Cir.eval.op"], evalEqz: ["Cir.eval.eqz"], cirEval: ["Cir.eval"],
  equalSym: ["Equal.sym"], equalTrans: ["Equal.trans"],
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
    case "Eql": { const a = replaceKey(t.a, k, by, key), b = replaceKey(t.b, k, by, key); return a === t.a && b === t.b ? t : B.Eql(a, b, t.T); }
    default: return t;
  }
};

export const wpProve = (api: WpApi, g: WpGoal): WpOut => {
  try {
    return run(api, g);
  } catch (e: any) {
    if (e instanceof Fail) return { why: e.why };
    return { why: "internal: " + String(e?.message ?? e).slice(0, 200) };
  }
};

const run = (api: WpApi, g: WpGoal): WpOut => {
  // the book's names
  const shortOf = (k: string) => (k.includes(":") ? k.slice(k.indexOf(":") + 1) : k);
  const byShort = new Map<string, string>();
  for (const k of Object.keys(api.RAW)) { const s = shortOf(k); if (!byShort.has(s) || !k.includes(":")) byShort.set(s, k); }
  const K: Record<string, string | undefined> = {};
  for (const [n, cands] of Object.entries(NAMES)) K[n] = cands.map((c) => byShort.get(c)).find((k) => k !== undefined);
  if (!K.tot && !K.wp) return { why: "not a Tot goal" };
  const names = g.names.slice(0, g.d);
  const sh = (t: LTerm) => api.show(t, names);
  const ref = (n: string): LTerm => B.Ref(K[n] ?? fail("the law " + NAMES[n]![0] + " is not in the book (import logic/impl.bend)")) as LTerm;
  const nm = (n: string) => sh(ref(n));
  const ctor = (short: string) => { const k = K.cirOut ?? fail("no Cir.Out in the book"); return sh(B.Ctr<[LTerm]>((k.includes(":") ? k.slice(0, k.indexOf(":") + 1) : "") + short, [])).replace(/\{\}$/, ""); };
  const unapply = (t: LTerm) => B.term_unapply(t);
  const isRef = (t: LTerm, n: string) => t.$ === "Ref" && K[n] !== undefined && t.k === K[n];
  let env: B.Env | null = null;
  const envOf = (): B.Env => {
    if (env === null) { let e: B.Env = null; for (let i = 0; i < g.d; i++) e = B.list_set(e, i, B.Var(names[i] ?? "_", i)); env = e; }
    return env;
  };
  const wnfL = (t: LTerm): LTerm | undefined => { const w = api.wnf(B.term_higher(t, envOf())); return w ? api.lower(w, g.d) : undefined; };
  const nfL = (t: LTerm): LTerm | undefined => api.attempt(FUEL, () => api.nf(B.term_higher(t, envOf()), g.d));
  const natOf = (t: LTerm): number | null => { const n = nfL(t); return n && n.$ === "Lit" && n.k === "Nat" ? (n.v as number) : null; };
  const isBool = (t: LTerm | undefined): t is Extract<LTerm, { $: "Ctr" }> => !!t && t.$ === "Ctr" && (t.k === "True" || t.k === "False") && t.x.length === 0;

  // the goal: Tot(code, st, b, Q, H), or WP(code, b, K, H, st)
  const goal = api.lower(g.ty, g.d);
  const [gh, gargs] = unapply(goal);
  let code0: LTerm, st0: LTerm, bS: string, HS: string, KS: string, wrap: (p: string) => string;
  if (isRef(gh, "tot") && gargs.length === 5) {
    code0 = gargs[0]!; st0 = gargs[1]!; bS = sh(gargs[2]!); HS = sh(gargs[4]!); KS = "h => " + sh(gargs[3]!);
    wrap = (p) => nm("totOfWp") + "(" + sh(code0) + ", " + sh(st0) + ", " + bS + ", " + KS + ", " + HS + ", " + p + ")";
  } else if (isRef(gh, "wp") && gargs.length === 5) {
    code0 = gargs[0]!; bS = sh(gargs[1]!); KS = sh(gargs[2]!); HS = sh(gargs[3]!); st0 = gargs[4]!;
    wrap = (p) => p;
  } else return { why: "not a Tot goal" };
  if ([bS, HS, KS].some((s) => s.includes("/"))) return { why: "a name of the goal is not reachable from this file (an import is missing)" };

  // the context's facts: registers and cells of a state, the register count, Bool facts
  const used = new Set(names);
  const fresh = (base: string) => { let s = base; for (let i = 2; used.has(s); i++) s = base + "_" + i; used.add(s); return s; };
  const regHyp = new Map<string, { c: LTerm; pf: string }>(); // key(state) + "|" + r
  const nregHyp = new Map<string, { n: LTerm; pf: string }>(); // key(state)
  const cellHyp = new Map<string, string>(); // key(state) + "|" + key(nf(c))
  const boolHyp: { lhs: LTerm; nk: string; val: boolean; name: string }[] = [];
  for (let i = 0; i < g.d; i++) {
    const a = B.pmap_get(g.ctx, i);
    if (!a || names[i] === "_" || names[i] === "" || /^w[sfnc]\d/.test(names[i]!)) continue;
    const T = api.attempt(FUEL, () => api.lower(a.T, i));
    if (!T || T.$ !== "Eql") continue;
    const [lh, la] = unapply(T.a);
    if (isRef(lh, "reg") && la.length === 2 && T.b.$ === "Ctr" && T.b.k === "Some" && T.b.x.length === 1) {
      const r = natOf(la[1]!);
      if (r !== null) regHyp.set(api.key(la[0]!) + "|" + r, { c: T.b.x[0]!, pf: names[i]! });
      continue;
    }
    if (isRef(lh, "nregs") && la.length === 1) { nregHyp.set(api.key(la[0]!), { n: T.b, pf: names[i]! }); continue; }
    if (isRef(lh, "isCell") && la.length === 2 && T.b.$ === "Ctr" && T.b.k === "True") {
      const c = nfL(la[1]!);
      if (c) cellHyp.set(api.key(la[0]!) + "|" + api.key(c), names[i]!);
      continue;
    }
    if (isBool(T.b)) {
      const n = nfL(T.a);
      if (n) boolHyp.push({ lhs: T.a, nk: api.key(n), val: T.b.k === "True", name: names[i]! });
    }
  }

  // the states: 0 is the goal's; k is the state k-1 after a set (r, v) or a store (kf, c, v)
  type St = { text: string; key: string; prev: number; op: "set" | "store" | null; r: number; c: LTerm | null; v: LTerm | null };
  const sts: St[] = [{ text: sh(st0), key: api.key(st0), prev: -1, op: null, r: -1, c: null, v: null }];
  const lets: string[] = [];
  const regFacts = new Map<string, { c: LTerm; pf: string }>();
  const nregFacts = new Map<number, { n: string; pf: string }>();
  const MB = "Maybe<&2, U32>";
  const stepArgs = (s: St, p: St) => p.text + ", " + (s.op === "set" ? s.r + "n, " + sh(s.v!) : s.r + "n, " + sh(s.c!) + ", " + sh(s.v!));
  // {St.nregs(st_j) == N}
  const nregOf = (j: number): { n: string; pf: string } => {
    const memo = nregFacts.get(j);
    if (memo) return memo;
    const s = sts[j]!;
    let out: { n: string; pf: string };
    if (s.prev < 0) {
      const h = nregHyp.get(s.key) ?? fail("no fact {" + nm("nregs") + "(" + s.text + ") == ..} in the context (the register count)");
      out = { n: sh(h.n), pf: h.pf };
    } else {
      const p = sts[s.prev]!, pn = nregOf(s.prev);
      const name = fresh("wn" + j);
      lets.push("+" + name + " : {" + nm("nregs") + "(" + s.text + ") == " + pn.n + " : Nat} = " + nm("equalTrans") + "(Nat, " + nm("nregs") + "(" + s.text + "), " + nm("nregs") + "(" + p.text + "), " + pn.n + ", " + nm(s.op === "set" ? "nregsSet" : "nregsStore") + "(" + stepArgs(s, p) + "), " + pn.pf + ")");
      out = { n: pn.n, pf: name };
    }
    nregFacts.set(j, out);
    return out;
  };
  // {Nat.is_lt(r, St.nregs(st_j)) == True{}}
  const ltOf = (j: number, r: number): string => {
    const f = nregOf(j);
    return "(%" + nm("equalSym") + "(Nat, " + nm("nregs") + "(" + sts[j]!.text + "), " + f.n + ", " + f.pf + ") : {Nat.is_lt(" + r + "n, _) == True{} : Bool}; {==})";
  };
  // {Reg(st_j, q) == Some{c}}
  const regOf = (j: number, q: number): { c: LTerm; pf: string } => {
    const mk = j + "|" + q;
    const memo = regFacts.get(mk);
    if (memo) return memo;
    const s = sts[j]!;
    let out: { c: LTerm; pf: string };
    if (s.prev < 0) out = regHyp.get(s.key + "|" + q) ?? fail("no fact {" + nm("reg") + "(" + s.text + ", " + q + "n) == Some{..}} in the context (register " + q + " is read)");
    else {
      const p = sts[s.prev]!;
      const here = s.op === "set" && s.r === q;
      const law = s.op === "set" ? nm("regSet") + "(" + p.text + ", " + s.r + "n, " + sh(s.v!) + ", " + q + "n, " + ltOf(s.prev, s.r) + ")"
        : nm("regStore") + "(" + p.text + ", " + s.r + "n, " + sh(s.c!) + ", " + sh(s.v!) + ", " + q + "n)";
      const c = here ? s.v! : regOf(s.prev, q).c;
      const pf = here ? law : nm("equalTrans") + "(" + MB + ", " + nm("reg") + "(" + s.text + ", " + q + "n), " + nm("reg") + "(" + p.text + ", " + q + "n), Some{" + sh(c) + "}, " + law + ", " + regOf(s.prev, q).pf + ")";
      const name = fresh("wf" + j + "_" + q);
      lets.push("+" + name + " : {" + nm("reg") + "(" + s.text + ", " + q + "n) == Some{" + sh(c) + "} : " + MB + "} = " + pf);
      out = { c, pf: name };
    }
    regFacts.set(mk, out);
    return out;
  };
  const push = (j: number, op: "set" | "store", r: number, c: LTerm | null, v: LTerm): number => {
    const name = fresh("ws" + sts.length);
    const s: St = { text: name, key: "let:" + name, prev: j, op, r, c, v };
    lets.push("+" + name + " : " + nm("cirState") + " = " + nm(op === "set" ? "stSet" : "stStore") + "(" + stepArgs(s, sts[j]!) + ")");
    sts.push(s);
    return sts.length - 1;
  };

  // an expression's value at the state j, and the proof of {Cr.Cir.eval(e, st_j) == Some{v}}
  const evalAt = (e: LTerm, j: number): { v: LTerm; he: string } => {
    const reads: { q: number; c: LTerm; pf: string }[] = [];
    const go = (x: LTerm): { tmpl: (sub: (i: number) => string) => string; val: LTerm } => {
      const w = wnfL(x) ?? fail("an expression does not evaluate: " + sh(x).slice(0, 120));
      if (w.$ !== "Ctr") fail("an expression with no constructor form: " + sh(x).slice(0, 120));
      const c = w as Extract<LTerm, { $: "Ctr" }>;
      switch (shortOf(c.k)) {
        case "Cir.Expr.const": { const n = c.x[0]!; const t = "Some{" + sh(n) + "}"; return { tmpl: () => t, val: B.Ctr<[LTerm]>("Some", [n]) }; }
        case "Cir.Expr.get": {
          const q = natOf(c.x[0]!);
          if (q === null) fail("a read of a register that is not a number: " + sh(c.x[0]!));
          const f = regOf(j, q!);
          const i = reads.length;
          reads.push({ q: q!, c: f.c, pf: f.pf });
          return { tmpl: (sub) => sub(i), val: B.Ctr<[LTerm]>("Some", [f.c]) };
        }
        case "Cir.Expr.op": {
          const o = sh(c.x[0]!);
          if (o.includes("/")) fail("the Wasm ops are not named in this file: it needs an import of Wasm/impl.bend");
          const a = go(c.x[1]!), b = go(c.x[2]!);
          return { tmpl: (sub) => nm("evalOp") + "(" + o + ", " + a.tmpl(sub) + ", " + b.tmpl(sub) + ")", val: B.App(B.App(B.App(ref("evalOp"), c.x[0]!), a.val), b.val) };
        }
        case "Cir.Expr.eqz": { const a = go(c.x[0]!); return { tmpl: (sub) => nm("evalEqz") + "(" + a.tmpl(sub) + ")", val: B.App(ref("evalEqz"), a.val) }; }
        default: return fail("a " + shortOf(c.k).replace(/^Cir\.Expr\./, "") + " read (field, byte or size): no kit law gives its value to --wp yet");
      }
    };
    const t = go(e);
    const n = nfL(t.val);
    if (!n || n.$ !== "Ctr" || n.k !== "Some" || n.x.length !== 1) fail("an expression's value is not Some{..}: " + sh(e).slice(0, 120));
    const v = (n as Extract<LTerm, { $: "Ctr" }>).x[0]!;
    // the reads rewritten one by one, the first outermost; the last proof is by computation
    const S = sts[j]!.text;
    let he = "{==}";
    for (let i = reads.length - 1; i >= 0; i--) {
      const P = t.tmpl((k) => (k < i ? "Some{" + sh(reads[k]!.c) + "}" : k === i ? "_" : nm("reg") + "(" + S + ", " + reads[k]!.q + "n)"));
      const rd = reads[i]!;
      he = "(%" + nm("equalSym") + "(" + MB + ", " + nm("reg") + "(" + S + ", " + rd.q + "n), Some{" + sh(rd.c) + "}, " + rd.pf + ") : {" + P + " == Some{" + sh(v) + "} : " + MB + "}; " + he + ")";
    }
    return { v, he };
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
    for (const [s2, k] of byShort) if (s2 === sn + ".spec" || s2.endsWith("." + sn + ".spec")) return sh(B.Ref(k) as LTerm);
    return null;
  };

  // continuations: the post of a statement is the goal's K, or "then the WP of code from there"
  // (list: code is the suffix i of a flattened sequence, whose statements are not read again)
  type Seq = { items: LTerm[]; texts: string[]; suf: string[]; tail: LTerm };
  type Cont = { code: string; term: LTerm; next: Cont; list?: { seq: Seq; i: number } } | null;
  const kText = (k: Cont): string => (k === null ? KS : "h => t => " + nm("wp") + "(" + k.code + ", " + bS + ", " + kText(k.next) + ", h, t)");
  const leaves: WpLeaf[] = [];
  const leaf = (hint: string): string => { leaves.push({ hole: leaves.length + 1, hint }); return "?TODO"; };
  let steps = 0;
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
  // the proof of WP(s, b, kText(k), H, st_j); sText is the code as printed (or its let)
  const prove = (sText: string, term: LTerm, j: number, k: Cont): string => {
    const S = sts[j]!.text;
    if (over()) return overLeaf(j);
    steps++;
    const law = lawOf(term);
    if (law) return leaf("a routine with a law: close its WP by " + nm("wp") + ".of_tot (Lg.wp.of_tot) with " + law + " and Lg.tot.wk (at " + S + ")");
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
        const r = natOf(rT);
        if (r === null) return leaf("a set of a register that is not a number: " + sh(rT));
        let ev: { v: LTerm; he: string }, hr: string;
        try { ev = evalAt(e, j); hr = ltOf(j, r); } catch (x) { if (x instanceof Fail) return leaf("set " + r + " at " + S + ": " + x.why); throw x; }
        const j2 = push(j, "set", r, null, ev.v);
        return nm("wpSet") + "(" + r + "n, " + sh(e) + ", " + S + ", " + bS + ", " + Kt + ", " + HS + ", " + sh(ev.v) + ", " + ev.he + ", " + hr + ", " + post(k, j2) + ")";
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
        const hi = cellHyp.get(sts[j]!.key + "|" + (ck ? api.key(ck) : "")) ?? (st0.$ === "Ctr" ? cellHyp.get(sts[0]!.key + "|" + (ck ? api.key(ck) : "")) : undefined);
        if (!hi) return leaf("store " + kf + " at " + S + ": no fact {" + nm("isCell") + "(" + S + ", " + sh(ec.v) + ") == True{}} (" + (j > 0 ? "match st at the start, then the start's fact serves" : "give it") + ")");
        const j2 = push(j, "store", kf, ec.v, ee.v);
        return nm("wpStore") + "(" + kf + "n, " + sh(c) + ", " + sh(e) + ", " + S + ", " + bS + ", " + Kt + ", " + HS + ", " + sh(ec.v) + ", " + sh(ee.v) + ", " + ec.he + ", " + ee.he + ", " + hi + ", " + post(k, j2) + ")";
      }
      case "Cir.Stmt.if": {
        const [c, y, n] = st.x as [LTerm, LTerm, LTerm];
        let ev: { v: LTerm; he: string };
        try { ev = evalAt(c, j); } catch (x) { if (x instanceof Fail) return leaf("an if at " + S + ": its condition: " + x.why); throw x; }
        const yT = codeLet(sh(y)), nT = codeLet(sh(n));
        const Y = "k => h => " + nm("wp") + "(" + yT + ", " + bS + ", k, h, " + S + ")", N = "k => h => " + nm("wp") + "(" + nT + ", " + bS + ", k, h, " + S + ")";
        const pickOf = (z: string) => nm("wpPick") + "(" + z + ", " + Y + ", " + N + ", " + Kt + ", " + HS + ")";
        const head = "(%" + nm("equalSym") + "(" + MB + ", " + nm("cirEval") + "(" + sh(c) + ", " + S + "), Some{" + sh(ev.v) + "}, " + ev.he + ") : " + nm("wpIf") + "(_, " + Y + ", " + N + ", " + Kt + ", " + HS + "); ";
        // z = U32.is_zero(v): False is the yes branch
        const z = nfL(B.App(ref("isZero"), ev.v));
        const branch = (zv: boolean) => (zv ? prove(nT, n, j, k) : prove(yT, y, j, k));
        if (isBool(z)) return head + branch(z.k === "True") + ")";
        // Bool facts on parts of z (in normal form), one rewrite each, until z computes
        if (z) {
          const HOLE = B.Ref("_") as LTerm;
          let cur = z;
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
        return head + leaf("an if at " + S + " that no fact decides: U32.is_zero(" + sh(ev.v) + "); split it: a Bool parameter z with {<part> == z} in a helper (each arm then steps), or give a Bool fact") + ")";
      }
      case "Cir.Stmt.while":
        return leaf("a loop at " + S + ": its WP is its Tot: apply Lg.tot.while with an invariant I(n, st) and a measure n (obligations: the condition has a value; at 0 the post; else the body's WP to I at a smaller measure), or a routine law (Lg.wp.of_tot)");
      case "Cir.Stmt.halt":
        return leaf("a halt at " + S + ": " + HS + "(its status, " + S + ")" + (/\bNo\b/.test(HS) ? " is Empty: a fact must rule this path out" : ""));
      case "Cir.Stmt.alloc":
        return leaf("an alloc at " + S + ": apply Lg.wp.alloc (it asks St.outn == 0 and the budget 20 (next + 1) <= b)");
      case "Cir.Stmt.emit":
        return leaf("an emit at " + S + ": apply Lg.wp.emit (it asks the budget 20 next + outn + 1 <= b)");
      default:
        return leaf("the statement " + st.k + " at " + S + ": not stepped by --wp");
    }
  };

  const body = wrap(prove(codeLet(sh(code0)), code0, 0, null));
  return { text: [...lets, body].join("\n"), leaves, steps };
};
