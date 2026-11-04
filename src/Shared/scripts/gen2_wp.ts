// gen2_wp.ts: gen2's Cir stepper (--wp), a dev tool outside the trust like gen2.ts (exempt from the
// review sweeps and the TypeScript rules of AGENTS.md 2.5 for the same reason; excluded in tsconfig).
//
// Given a goal `Lg.Tot(code, st, b, Q, H)` (redesign-plan.md 4.1) whose code is closed, it writes
// the proof that steps the code by the logic's laws: tot.seq for a sequence, tot.if for an if (when
// its condition is decided by computation or by a Bool fact of the context), and for a set
// tot.wp with the run rewritten by exec.set; each register read is rewritten by its fact (a
// hypothesis {Lg.Reg(st, r) == Some{c}}, or reg.set after a set), the length of the registers is
// carried by len.set. What is left is ?TODO leaves, each with a one-line hint: the post Q at the
// end, a branch that no fact decides, a loop (tot.while's obligations), a statement the kit does
// not cover. The proof is a body: typed lets for the states, the facts and the code's suffixes (so
// its size grows linearly with the code), then the proof term.
//
// Bounded: at most MAX_STEPS statements and the caller's deadline; past either, the rest is one
// leaf. Never throws: an internal failure is a one-line `why`.
//
// The laws are found through NAMES (one indirection): each logical name lists the short names it
// may have in the book; the first that exists wins. S1 publishes the real names in
// reports/redesign/s1-names.md; adapt NAMES to them.

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
  tot: ["Tot"], reg: ["Reg"], ok: ["Ok"], lim: ["Lim"], stSet: ["St.set"], stRegs: ["St.regs"],
  seq: ["tot.seq"], if: ["tot.if"], wp: ["tot.wp"], execSet: ["exec.set"], regSet: ["reg.set"],
  lenSet: ["len.set", "regs.len.set", "St.set.len"], machRegs: ["Mach.regs"],
  evalOp: ["Cir.eval.op"], evalEqz: ["Cir.eval.eqz"], equalSym: ["Equal.sym"], equalTrans: ["Equal.trans"],
  cirState: ["Cir.State"], cirOut: ["Cir.Out"], cirStmt: ["Cir.Stmt"], cirExec: ["Cir.exec"], isZero: ["U32.is_zero"],
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
  if (!K.tot) return { why: "no Tot in the book (logic/spec.bend not imported)" };
  const names = g.names.slice(0, g.d);
  const sh = (t: LTerm) => api.show(t, names);
  const ref = (n: string): LTerm => B.Ref(K[n] ?? fail("the law " + NAMES[n]![0] + " is not in the book")) as LTerm;
  const nm = (n: string) => sh(ref(n));
  // a constructor of Cir (Cir.Out.next, Cir.Stmt.seq) as this file names it
  const ctor = (short: string) => { const k = K.cirOut ?? fail("no Cir.Out in the book"); return sh(B.Ctr<[LTerm]>((k.includes(":") ? k.slice(0, k.indexOf(":") + 1) : "") + short, [])).replace(/\{\}$/, ""); };
  const unapply = (t: LTerm) => B.term_unapply(t);
  const isRef = (t: LTerm, n: string) => t.$ === "Ref" && K[n] !== undefined && t.k === K[n];
  const wnfL = (t: LTerm): LTerm | undefined => { const w = api.wnf(B.term_higher(t, envOf())); return w ? api.lower(w, g.d) : undefined; };
  const nfL = (t: LTerm): LTerm | undefined => api.attempt(FUEL, () => api.nf(B.term_higher(t, envOf()), g.d));
  let env: B.Env | null = null;
  const envOf = (): B.Env => {
    if (env === null) { let e: B.Env = null; for (let i = 0; i < g.d; i++) e = B.list_set(e, i, B.Var(names[i] ?? "_", i)); env = e; }
    return env;
  };
  const natOf = (t: LTerm): number | null => { const n = nfL(t); return n && n.$ === "Lit" && n.k === "Nat" ? (n.v as number) : null; };

  // the goal
  const goal = api.lower(g.ty, g.d);
  const [gh, gargs] = unapply(goal);
  if (!isRef(gh, "tot") || gargs.length !== 5) return { why: "not a Tot goal" };
  const [code0, st0, bT, QT, HT] = gargs as [LTerm, LTerm, LTerm, LTerm, LTerm];
  const bS = sh(bT), QS = sh(QT), HS = sh(HT);
  if ([bS, QS, HS].some((s) => s.includes("/"))) return { why: "a name of the goal is not reachable from this file (an import missing)" };

  // the context's facts: registers of a state, the registers' length, Bool facts
  const used = new Set(names);
  const fresh = (base: string) => { let s = base; for (let i = 2; used.has(s); i++) s = base + "_" + i; used.add(s); return s; };
  const regHyp = new Map<string, { c: LTerm; pf: string }>(); // key(state) + "|" + r
  const lenHyp = new Map<string, string>(); // key(state)
  const boolHyp: { lhs: LTerm; nk: string; val: boolean; name: string }[] = [];
  for (let i = 0; i < g.d; i++) {
    const a = B.pmap_get(g.ctx, i);
    if (!a || names[i] === "_" || names[i] === "") continue;
    const T = api.attempt(FUEL, () => api.lower(a.T, i));
    if (!T || T.$ !== "Eql") continue;
    const [lh, la] = unapply(T.a);
    if (isRef(lh, "reg") && la.length === 2 && T.b.$ === "Ctr" && T.b.k === "Some" && T.b.x.length === 1) {
      const r = natOf(la[1]!);
      if (r !== null) regHyp.set(api.key(la[0]!) + "|" + r, { c: T.b.x[0]!, pf: names[i]! });
      continue;
    }
    if (lh.$ === "Ref" && shortOf(lh.k) === "List.length" && la.length === 3) {
      const [rh, ra] = unapply(la[2]!);
      if (isRef(rh, "stRegs") && ra.length === 1) { lenHyp.set(api.key(ra[0]!), names[i]!); continue; }
    }
    if (T.b.$ === "Ctr" && (T.b.k === "True" || T.b.k === "False") && T.b.x.length === 0) {
      const n = nfL(T.a);
      if (n) boolHyp.push({ lhs: T.a, nk: api.key(n), val: T.b.k === "True", name: names[i]! });
    }
  }

  // the states: 0 is the goal's; k is the state k-1 with the register r set to the value v
  type St = { text: string; key: string; prev: number; r: number; v: LTerm | null };
  const sts: St[] = [{ text: sh(st0), key: api.key(st0), prev: -1, r: -1, v: null }];
  const lets: string[] = [];
  const regFacts = new Map<string, { c: LTerm; pf: string }>();
  const lenFacts = new Map<number, string>();
  const M = (t: string) => "Maybe<&2, U32>";
  const lenOf = (j: number): string => {
    const memo = lenFacts.get(j);
    if (memo) return memo;
    const s = sts[j]!;
    let pf: string;
    if (s.prev < 0) pf = lenHyp.get(s.key) ?? fail("no fact {List.length(&2, U32, St.regs(" + s.text + ")) == Mach.regs()} in the context");
    else {
      const p = sts[s.prev]!;
      const name = fresh("wl" + j);
      lets.push("+" + name + " : {List.length(&2, U32, " + nm("stRegs") + "(" + s.text + ")) == " + nm("machRegs") + "() : Nat} = " + nm("equalTrans") + "(Nat, List.length(&2, U32, " + nm("stRegs") + "(" + s.text + ")), List.length(&2, U32, " + nm("stRegs") + "(" + p.text + ")), " + nm("machRegs") + "(), " + nm("lenSet") + "(" + p.text + ", " + s.r + "n, " + sh(s.v!) + "), " + lenOf(s.prev) + ")");
      pf = name;
    }
    lenFacts.set(j, pf);
    return pf;
  };
  const ltOf = (j: number, r: number): string =>
    "(%" + nm("equalSym") + "(Nat, List.length(&2, U32, " + nm("stRegs") + "(" + sts[j]!.text + ")), " + nm("machRegs") + "(), " + lenOf(j) + ") : {Nat.is_lt(" + r + "n, _) == True{} : Bool}; {==})";
  const regOf = (j: number, q: number): { c: LTerm; pf: string } => {
    const mk = j + "|" + q;
    const memo = regFacts.get(mk);
    if (memo) return memo;
    const s = sts[j]!;
    let out: { c: LTerm; pf: string };
    if (s.prev < 0) out = regHyp.get(s.key + "|" + q) ?? fail("no fact {" + nm("reg") + "(" + s.text + ", " + q + "n) == Some{..}} in the context (register " + q + " is read)");
    else {
      const p = sts[s.prev]!;
      const rs = nm("regSet") + "(" + p.text + ", " + s.r + "n, " + sh(s.v!) + ", " + q + "n, " + ltOf(s.prev, s.r) + ")";
      const c = s.r === q ? s.v! : regOf(s.prev, q).c;
      const pf = s.r === q ? rs : nm("equalTrans") + "(" + M("") + ", " + nm("reg") + "(" + s.text + ", " + q + "n), " + nm("reg") + "(" + p.text + ", " + q + "n), Some{" + sh(c) + "}, " + rs + ", " + regOf(s.prev, q).pf + ")";
      const name = fresh("wf" + j + "_" + q);
      lets.push("+" + name + " : {" + nm("reg") + "(" + s.text + ", " + q + "n) == Some{" + sh(c) + "} : " + M("") + "} = " + pf);
      out = { c, pf: name };
    }
    regFacts.set(mk, out);
    return out;
  };
  const setState = (j: number, r: number, v: LTerm): number => {
    const name = fresh("ws" + sts.length);
    lets.push("+" + name + " : " + nm("cirState") + " = " + nm("stSet") + "(" + sts[j]!.text + ", " + r + "n, " + sh(v) + ")");
    sts.push({ text: name, key: "let:" + name, prev: j, r, v });
    return sts.length - 1;
  };

  // an expression's value at the state j, and the proof of {Cr.Cir.eval(e, st_j) == Some{v}}
  type Ev = { tmpl: (sub: (i: number) => string) => string; val: LTerm; reads: { q: number; c: LTerm; pf: string }[] };
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
          if (q === null) fail("a register that is not a literal: " + sh(c.x[0]!));
          const f = regOf(j, q!);
          const i = reads.length;
          reads.push({ q: q!, c: f.c, pf: f.pf });
          return { tmpl: (sub) => sub(i), val: B.Ctr<[LTerm]>("Some", [f.c]) };
        }
        case "Cir.Expr.op": {
          const o = sh(c.x[0]!);
          if (o.includes("/")) fail("the Wasm ops are not named in this file: import ../../Wasm/impl.bend (alias Wa)");
          const a = go(c.x[1]!), b = go(c.x[2]!);
          return { tmpl: (sub) => nm("evalOp") + "(" + o + ", " + a.tmpl(sub) + ", " + b.tmpl(sub) + ")", val: B.App(B.App(B.App(ref("evalOp"), c.x[0]!), a.val), b.val) };
        }
        case "Cir.Expr.eqz": { const a = go(c.x[0]!); return { tmpl: (sub) => nm("evalEqz") + "(" + a.tmpl(sub) + ")", val: B.App(ref("evalEqz"), a.val) }; }
        default: return fail("the expression " + shortOf(c.k) + " (a field, byte or size read) needs a kit law that --wp does not apply yet");
      }
    };
    const t = go(e);
    const n = nfL(t.val);
    if (!n || n.$ !== "Ctr" || n.k !== "Some" || n.x.length !== 1) fail("an expression's value is not Some{..}: " + sh(e).slice(0, 120));
    const v = (n as Extract<LTerm, { $: "Ctr" }>).x[0]!;
    // rewrite the reads one by one, the first outermost; the last proof is by computation
    const S = sts[j]!.text;
    let he = "{==}";
    for (let i = reads.length - 1; i >= 0; i--) {
      const P = t.tmpl((k) => (k < i ? "Some{" + sh(reads[k]!.c) + "}" : k === i ? "_" : nm("reg") + "(" + S + ", " + reads[k]!.q + "n)"));
      const rd = reads[i]!;
      he = "(%" + nm("equalSym") + "(" + M("") + ", " + nm("reg") + "(" + S + ", " + rd.q + "n), Some{" + sh(rd.c) + "}, " + rd.pf + ") : {" + P + " == Some{" + sh(v) + "} : " + M("") + "}; " + he + ")";
    }
    return { v, he };
  };

  // the code: a statement's constructor, with its parts as written
  const stmtOf = (s: LTerm): { k: string; x: LTerm[] } => {
    const w = wnfL(s) ?? fail("a statement does not evaluate: " + sh(s).slice(0, 120));
    if (w.$ !== "Ctr") fail("a statement with no constructor form: " + sh(s).slice(0, 120));
    return { k: shortOf((w as any).k), x: (w as any).x };
  };
  // continuations: the post of a statement is the original Q, or "then run code from there"
  // (list: the code is the suffix i of a flattened sequence, so its statements are not read again)
  type Seq = { items: LTerm[]; texts: string[]; suf: string[]; tail: LTerm };
  type Cont = { code: string; term: LTerm; next: Cont; list?: { seq: Seq; i: number } } | null;
  const qText = (k: Cont): string => (k === null ? QS : "st2 => " + nm("tot") + "(" + k.code + ", st2, " + bS + ", " + qText(k.next) + ", " + HS + ")");
  const leaves: WpLeaf[] = [];
  const leaf = (hint: string): string => { leaves.push({ hole: leaves.length + 1, hint }); return "?TODO"; };
  let steps = 0;
  const over = () => steps >= MAX_STEPS || performance.now() > api.deadline;
  const codeLet = (t: string): string => {
    if (/^[A-Za-z_][\w.]*$/.test(t) || t.length < 60) return t;
    const name = fresh("wc" + lets.length);
    lets.push("+" + name + " : " + nm("cirStmt") + " = " + t);
    return name;
  };
  // the proof that the post k holds at the state j
  const post = (k: Cont, j: number): string =>
    k === null ? leaf("the post: " + QS + " at the final state " + sts[j]!.text)
      : k.list ? proveList(k.list.seq, k.list.i, j, k.next) : prove(k.code, k.term, j, k.next);
  // the proof of Tot(suffix i of the sequence, st_j, b, qText(k), H)
  const proveList = (L: Seq, i: number, j: number, k: Cont): string => {
    if (i === L.items.length) return prove(L.suf[i]!, L.tail, j, k);
    if (over()) return leaf((steps >= MAX_STEPS ? "the step limit (" + MAX_STEPS + ")" : "the time budget") + ": the rest of the code from " + sts[j]!.text);
    const inner = prove(L.texts[i]!, L.items[i]!, j, { code: L.suf[i + 1]!, term: L.tail, next: k, list: { seq: L, i: i + 1 } });
    return nm("seq") + "(" + L.texts[i] + ", " + L.suf[i + 1] + ", " + sts[j]!.text + ", " + bS + ", " + qText(k) + ", " + HS + ", " + inner + ")";
  };
  // the proof of Tot(s, st_j, b, qText(k), H); sText is the code as printed (or its let), term its term
  const prove = (sText: string, term: LTerm, j: number, k: Cont): string => {
    const S = sts[j]!.text;
    if (over()) return leaf((steps >= MAX_STEPS ? "the step limit (" + MAX_STEPS + ")" : "the time budget") + ": the rest of the code from " + S);
    steps++;
    const st = stmtOf(term);
    const Q = qText(k);
    switch (st.k) {
      case "Cir.Stmt.nop":
        return nm("wp") + "(" + sText + ", " + S + ", " + bS + ", " + Q + ", " + HS + ", " + post(k, j) + ")";
      case "Cir.Stmt.seq": {
        // the sequence's spine, flattened: its suffixes are lets built from the end, so that each
        // statement is printed once
        const [a, c] = st.x as [LTerm, LTerm];
        const items: LTerm[] = [a];
        let tail = c;
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
        if (r === null) return leaf("a set of a register that is not a literal: " + sh(rT));
        let ev: { v: LTerm; he: string };
        let hl: string;
        try { ev = evalAt(e, j); hl = lenOf(j); } catch (x) { if (x instanceof Fail) return leaf("set " + r + ": " + x.why); throw x; }
        const j2 = setState(j, r, ev.v);
        const S2 = sts[j2]!.text;
        const eq = nm("equalSym") + "(" + nm("cirOut") + ", " + nm("cirExec") + "(0n, " + sText + ", " + S + "), " + ctor("Cir.Out.next") + "{" + S2 + "}, " + nm("execSet") + "(0n, " + r + "n, " + sh(e) + ", " + S + ", " + sh(ev.v) + ", " + ev.he + ", {==}, " + hl + "))";
        return nm("wp") + "(" + sText + ", " + S + ", " + bS + ", " + Q + ", " + HS + ", (%" + eq + " : " + nm("ok") + "(_, " + nm("lim") + "(" + S + "), " + bS + ", " + Q + ", " + HS + "); " + post(k, j2) + "))";
      }
      case "Cir.Stmt.if": {
        const [c, y, n] = st.x as [LTerm, LTerm, LTerm];
        let ev: { v: LTerm; he: string };
        try { ev = evalAt(c, j); } catch (x) { if (x instanceof Fail) return leaf("an if: its condition: " + x.why); throw x; }
        const yT = codeLet(sh(y)), nT = codeLet(sh(n));
        const head = nm("if") + "(" + sh(c) + ", " + yT + ", " + nT + ", " + S + ", " + bS + ", " + Q + ", " + HS + ", " + sh(ev.v) + ", " + ev.he + ", ";
        const z = nfL(B.App(ref("isZero"), ev.v));
        if (z && z.$ === "Ctr" && (z.k === "True" || z.k === "False")) return head + (z.k === "True" ? prove(nT, n, j, k) : prove(yT, y, j, k)) + ")";
        // Bool facts of the context on parts of the condition (in normal form): each rewrites its part
        // (one rewrite per fact, in order), until the condition computes to True or False
        if (z) {
          const HOLE = B.Ref("_") as LTerm;
          let cur = z;
          const used2: { h: (typeof boolHyp)[number]; P: string }[] = [];
          for (const h of boolHyp) {
            const r = replaceKey(cur, h.nk, HOLE, api.key);
            if (r === cur) continue;
            used2.push({ h, P: sh(r) });
            cur = replaceKey(cur, h.nk, B.Ctr<[LTerm]>(h.val ? "True" : "False", []), api.key);
            const c2 = nfL(cur);
            if (c2 && c2.$ === "Ctr" && (c2.k === "True" || c2.k === "False")) {
              let pf = c2.k === "True" ? prove(nT, n, j, k) : prove(yT, y, j, k);
              for (let i = used2.length - 1; i >= 0; i--) {
                const u = used2[i]!;
                const pick = nm("tot") + "(Bool.pick(" + nm("cirStmt") + ", " + u.P + ", " + nT + ", " + yT + "), " + S + ", " + bS + ", " + Q + ", " + HS + ")";
                pf = "(%" + nm("equalSym") + "(Bool, " + sh(u.h.lhs) + ", " + (u.h.val ? "True{}" : "False{}") + ", " + u.h.name + ") : " + pick + "; " + pf + ")";
              }
              return head + pf + ")";
            }
          }
        }
        return head + leaf("an if whose condition no fact decides: U32.is_zero(" + sh(ev.v) + "); give a Bool fact, or split it in a helper (a Bool parameter z with {U32.is_zero(..) == z})") + ")";
      }
      case "Cir.Stmt.while":
        return leaf("a loop at " + S + ": apply the while rule (tot.while) with an invariant I(n, st) and a measure n (obligations: the condition has a value; at 0 the post; else the body runs to I at a smaller measure), or a routine law whose conclusion is this loop's Tot");
      case "Cir.Stmt.halt":
        return nm("wp") + "(" + sText + ", " + S + ", " + bS + ", " + Q + ", " + HS + ", " + leaf("a halt: " + HS + "(its status, " + S + ")") + ")";
      default:
        return leaf("the statement " + st.k + " at " + S + ": its kit law (exec.store, exec.alloc.new, ..) is not applied by --wp yet");
    }
  };

  const body = (() => {
    const cT = codeLet(sh(code0));
    return prove(cT, code0, 0, null);
  })();
  return { text: [...lets, body].join("\n"), leaves, steps };
};
