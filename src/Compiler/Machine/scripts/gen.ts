// gen.ts: writes the mechanical part of the move proofs (symbolic runs of the
// machine's Cir code). Dev tool, outside the trust: the kernel checks its output.
// Exempt from review sweeps (AGENTS.md 2.1.3) and from the TypeScript rules of 2.5, by the owner's
// explicit decision: it is a dev tool outside the trust that must only help and be fast.
//
// usage: bun gen.ts <src/Compiler/Machine dir> <mode> [options]
//   br <chain> <target>      body of a br.* lemma: the if-chain <chain> (e.g. K.B.else())
//                            tests a register against constants; reach the branch <target>
//                            (e.g. Mc.M.ev.let()). Options: --st st --tag 'D.TgW(f0)' --f0 f0
//                            --tagv 3 --er er --etag etag
//   rn <path> --name N       a segment lemma in the Rn kit of moves_copy.bend: from the
//                            statement <path> (e.g. 'X.sel.e(Mc.M.ev.let())') run sets,
//                            stores and chosen if branches; stop at an opaque statement
//                            (law call), a nop or a halt; premise k: Rn of the rest.
//        --br tee            branch choices, one char per if met (t or e)
//        --md 0              the mode register's value in the initial state
//        --reg 8=foc         initial register texts (repeatable); --param '+f0: U32' extra params
//        --opaque a,b        extra opaque statement makers (default: the law-backed M.*)
// One pass over the code; defs are indexed once and parsed on demand (memo).

import { readFileSync } from "node:fs";

type Node =
  | { k: "call"; f: string; a: Node[] }
  | { k: "ctor"; f: string; a: Node[] }
  | { k: "name"; n: string }
  | { k: "num"; v: string }
  | { k: "list"; a: Node[] };

type Def = { params: string[]; body: string; alias: string; aliases: Map<string, string>; own: Set<string>; parsed?: Node | null };

const FILES: [string, string][] = [
  ["impl.bend", "Mc"],
  ["move_kit.bend", "K"],
  ["definitions.bend", "D"],
  ["statement_runs.bend", "X"],
];
const MODULE_ALIAS: Record<string, string> = { "./impl.bend": "Mc", "./move_kit.bend": "K", "./definitions.bend": "D", "./statement_runs.bend": "X" };
const OPAQUE_DEFAULT = ["M.one", "M.copy", "M.data", "M.dec", "M.inc", "M.release", "M.make", "M.alloc", "M.walk", "M.push", "M.pop", "M.swap", "M.release.arg", "M.release.all", "M.redex", "M.while"];

const defs = new Map<string, Def>();

// ---- loading ----
const load = (dir: string) => {
  for (const [file, alias] of FILES) {
    const lines = readFileSync(dir + "/" + file, "utf8").split("\n");
    const aliases = new Map<string, string>();
    const own = new Set<string>();
    for (const l of lines) {
      const im = /^import (\S+) as (\S+)/.exec(l);
      if (im) aliases.set(im[2], MODULE_ALIAS[im[1]] ?? "");
      const dm = /^def ([A-Za-z0-9_.]+)\(/.exec(l);
      if (dm) own.add(dm[1]);
    }
    let i = 0;
    while (i < lines.length) {
      const dm = /^def ([A-Za-z0-9_.]+)\(/.exec(lines[i]);
      if (!dm) { i++; continue; }
      // header: until a line ending with ':' at paren depth 0
      let hdr = "";
      let depth = 0;
      for (;;) {
        const l = lines[i];
        hdr += l + "\n";
        for (const ch of l) { if (ch === "(" || ch === "[" || ch === "{" || ch === "<") depth++; else if (ch === ")" || ch === "]" || ch === "}" || ch === ">") depth--; }
        i++;
        if (depth <= 0 && /:\s*$/.test(l)) break;
        if (i >= lines.length) break;
      }
      const body: string[] = [];
      while (i < lines.length && (lines[i].startsWith(" ") || lines[i].trim() === "")) { body.push(lines[i]); i++; }
      // params: names before ':' at depth 1 of the first paren group
      const open = hdr.indexOf("(");
      const params: string[] = [];
      let d = 0, cur = "";
      for (let j = open + 1; j < hdr.length; j++) {
        const ch = hdr[j];
        if (d === 0 && ch === ")") { if (cur.trim()) params.push(cur); break; }
        if ("([{<".includes(ch)) d++;
        if (")]}>".includes(ch)) d--;
        if (d === 0 && ch === ",") { params.push(cur); cur = ""; } else cur += ch;
      }
      const names = params.map((p) => p.split(":")[0].trim().replace(/^[+-]/, "")).filter((x) => x);
      const key = (alias + "." + dm[1]);
      if (!defs.has(key)) defs.set(key, { params: names, body: body.filter((l) => !l.trim().startsWith("#")).join("\n"), alias, aliases, own });
    }
  }
};

// ---- parsing ----
const tokenize = (s: string): string[] => {
  const out: string[] = [];
  const re = /\s*([A-Za-z_][A-Za-z0-9_.]*|\d+n?|[()\[\]{},])/y;
  let m: RegExpExecArray | null;
  re.lastIndex = 0;
  while (re.lastIndex < s.length) {
    const at = re.lastIndex;
    m = re.exec(s);
    if (!m) { if (s.slice(at).trim() === "") break; throw new Error("tokenize at: " + s.slice(at, at + 40)); }
    out.push(m[1]);
  }
  return out;
};

const qualify = (n: string, d: Def | null): string => {
  if (!d) return n;
  const dot = n.indexOf(".");
  if (dot > 0) {
    const head = n.slice(0, dot);
    if (d.aliases.has(head)) { const a = d.aliases.get(head)!; return a ? a + n.slice(dot) : n; }
  }
  if (d.own.has(n)) return d.alias + "." + n;
  return n;
};

const parse = (s: string, d: Def | null): Node => {
  const t = tokenize(s);
  let p = 0;
  const expr = (): Node => {
    const x = t[p++];
    if (x === "[") {
      const a: Node[] = [];
      while (t[p] !== "]") { a.push(expr()); if (t[p] === ",") p++; }
      p++;
      return { k: "list", a };
    }
    if (/^\d/.test(x)) return { k: "num", v: x };
    if (t[p] === "(" || t[p] === "{") {
      const close = t[p] === "(" ? ")" : "}";
      const kind = t[p] === "(" ? "call" : "ctor";
      p++;
      const a: Node[] = [];
      while (t[p] !== close) { a.push(expr()); if (t[p] === ",") p++; }
      p++;
      return { k: kind, f: qualify(x, d), a } as Node;
    }
    return { k: "name", n: x };
  };
  const r = expr();
  if (p !== t.length) throw new Error("trailing tokens: " + t.slice(p, p + 8).join(" "));
  return r;
};

const bodyOf = (f: string): Node | null => {
  const d = defs.get(f);
  if (!d) return null;
  if (d.parsed !== undefined) return d.parsed;
  const b = d.body.trim();
  d.parsed = null;
  if (b && !b.startsWith("match") && !b.includes("\n  +") && !/^[+%]/.test(b)) {
    try { d.parsed = parse(b, d); } catch { d.parsed = null; }
  }
  return d.parsed;
};

const subst = (n: Node, env: Map<string, Node>): Node => {
  switch (n.k) {
    case "name": return env.get(n.n) ?? n;
    case "num": return n;
    case "list": return { k: "list", a: n.a.map((x) => subst(x, env)) };
    default: return { k: n.k, f: n.f, a: n.a.map((x) => subst(x, env)) } as Node;
  }
};

// one unfolding of a def call; null if not unfoldable
const unfold = (n: Node): Node | null => {
  if (n.k !== "call") return null;
  const b = bodyOf(n.f);
  if (!b) return null;
  const d = defs.get(n.f)!;
  const env = new Map<string, Node>();
  d.params.forEach((x, i) => env.set(x, n.a[i]));
  return subst(b, env);
};

const print = (n: Node): string => {
  switch (n.k) {
    case "name": return n.n;
    case "num": return n.v;
    case "list": return "[" + n.a.map(print).join(", ") + "]";
    case "call": {
      if (n.a.length === 0 && !n.f.startsWith("Mc.R.")) { const b = bodyOf(n.f); if (b && b.k === "num") return b.v; }
      return n.f + "(" + n.a.map(print).join(", ") + ")";
    }
    case "ctor": return n.f + "{" + n.a.map(print).join(", ") + "}";
  }
};

// ---- statements ----
type Stmt =
  | { k: "seq"; a: Node; b: Node }
  | { k: "if"; c: Node; t: Node; e: Node }
  | { k: "set"; r: Node; e: Node }
  | { k: "store"; f: Node; c: Node; v: Node }
  | { k: "nop" }
  | { k: "halt"; s: Node }
  | { k: "opaque"; n: Node };

let opaque = new Set<string>(OPAQUE_DEFAULT.map((x) => "Mc." + x));

const isOpaque = (n: Node) => n.k === "call" && opaque.has(n.f);

const whnfStmt = (n0: Node): Stmt => {
  let n = n0;
  for (let guard = 0; guard < 10000; guard++) {
    if (n.k === "ctor") {
      const a = n.a;
      switch (n.f) {
        case "Cr.Cir.Stmt.seq": return { k: "seq", a: a[0], b: a[1] };
        case "Cr.Cir.Stmt.if": return { k: "if", c: a[0], t: a[1], e: a[2] };
        case "Cr.Cir.Stmt.set": return { k: "set", r: a[0], e: a[1] };
        case "Cr.Cir.Stmt.store": return { k: "store", f: a[0], c: a[1], v: a[2] };
        case "Cr.Cir.Stmt.nop": return { k: "nop" };
        case "Cr.Cir.Stmt.halt": return { k: "halt", s: a[0] };
        default: return { k: "opaque", n };
      }
    }
    if (n.k !== "call") return { k: "opaque", n };
    if (n.f === "Mc.M.do") {
      const l = n.a[0];
      if (l.k !== "list") return { k: "opaque", n };
      if (l.a.length === 0) return { k: "nop" };
      return { k: "seq", a: l.a[0], b: { k: "call", f: "Mc.M.do", a: [{ k: "list", a: l.a.slice(1) }] } };
    }
    const sel = /^X\.sel\.([abte])$/.exec(n.f);
    if (sel) {
      const s = whnfStmt(n.a[0]);
      const pick = sel[1];
      if (s.k === "seq" && (pick === "a" || pick === "b")) { n = pick === "a" ? s.a : s.b; continue; }
      if (s.k === "if" && (pick === "t" || pick === "e")) { n = pick === "t" ? s.t : s.e; continue; }
      return { k: "nop" };
    }
    const u = unfold(n);
    if (!u) return { k: "opaque", n };
    n = u;
  }
  throw new Error("whnfStmt: no end");
};

const whnfExpr = (n0: Node): Node => {
  let n = n0;
  for (;;) {
    if (n.k !== "call") return n;
    const u = unfold(n);
    if (!u) return n;
    n = u;
  }
};

const natOf = (n: Node): number => {
  const w = whnfExpr(n);
  if (w.k !== "num") throw new Error("not a number: " + print(n));
  return parseInt(w.v);
};

// ---- br mode ----
const genBr = (chain: string, target: string, o: Record<string, string>): string => {
  const f = o.f ?? "f", st = o.st ?? "st", tag = o.tag ?? "D.TgW(f0)", f0 = o.f0 ?? "f0", er = o.er ?? "er", etag = o.etag ?? "etag";
  const tv = o.tagv;
  const goal = `Cr.Cir.exec(${f}, ${target}, ${st})`;
  const out: string[] = [];
  let cur: Node = parse(chain, null);
  for (let step = 0; step < 1000; step++) {
    const s = whnfStmt(cur);
    if (s.k !== "if") throw new Error("br: not an if: " + print(cur));
    const c = whnfExpr(s.c);
    if (c.k !== "ctor" || c.f !== "Cr.Cir.Expr.op") throw new Error("br: condition not an op");
    const [op, a, b] = c.a;
    const kv = print(whnfExpr(b).k === "ctor" ? (whnfExpr(b) as any).a[0] : b);
    const C = print(s.c), T = print(s.t), E = print(s.e), A = print(a), B = print(b), O = print(op);
    const ev = `D.ev.op(${O}, ${A}, ${B}, ${st}, ${tag}, ${kv}, ${er}, {==})`;
    if (print(s.t) === target || T === target) {
      out.push(`D.eq.if.t(${f}, ${C}, ${T}, ${E}, ${st}, Wa.Wasm.op(${O}, ${tag}, ${kv}),\n  ${ev},\n  (%Equal.sym(U32, ${tag}, ${tv}, ${etag}) : {U32.is_zero(Wa.Wasm.op(${O}, _, ${kv})) == False{} : Bool}; {==}))`);
      return out.join("\n");
    }
    out.push(`%Equal.sym(Cr.Cir.Out, Cr.Cir.exec(${f}, ${print(cur)}, ${st}), Cr.Cir.exec(${f}, ${E}, ${st}),\n  D.eq.if.e(${f}, ${C}, ${T}, ${E}, ${st}, Wa.Wasm.op(${O}, ${tag}, ${kv}),\n    ${ev}, K.tag.ne(${f0}, ${tv}, ${kv}, ${etag}, {==}))) :\n  {_ == ${goal} : Cr.Cir.Out}`);
    cur = s.e;
  }
  throw new Error("br: target not found");
};

// ---- rn mode ----
const genRn = (path: string, o: Record<string, string>, regOver: Map<number, string>, extra: string[]): string => {
  const kit = "ds, ks, img, st0, t, w";
  const regs: string[] = [];
  regs.push("foc", o.md ?? "0", "sp", "pend");
  for (let r = 4; r < 63; r++) regs.push("r" + r);
  for (const [r, v] of regOver) regs[r] = v;
  let cells = "m";
  const params: string[] = ["+ds: List<&2, Bk.Def>", "+ks: List<&2, List<&2, Word(8n)>>", "+img: List<&2, Bk.Term>", "+st0: Cr.Cir.State", "+t: Bk.Term", "+w: Nat"];
  const used = new Set(regs);
  const regParams = ["foc", "sp", "pend"].concat(Array.from({ length: 59 }, (_, i) => "r" + (i + 4)));
  for (const p of regParams) params.push("+" + p + ": U32");
  params.push("+m: Cr.Cir.Cells", "+nx: U32", "+fi: U32", "+im: U32", "+pg: U32", "+lim: U32", "+inp: List<&2, Word(8n)>");
  for (const e of extra) params.push(e);
  const prem: string[] = [];
  const lets: string[] = [];
  const st0text = `X.X.st([${regs.join(", ")}], m, nx, fi, im, pg, lim, inp)`;
  let stName = "s0";
  let stFull = st0text; // full text, for the final premise only
  lets.push(`+s0 = ${st0text}`);
  let nst = 0, nprem = 0;
  const cellSeen = new Map<string, string>();
  const cellPrem = (i: string): string => {
    const old = cellSeen.get(i);
    if (old) return old;
    const h = "hc" + nprem++;
    prem.push(`+${h}: {Cr.Cir.is_cell(${i}, im, fi, nx) == True{} : Bool}`);
    cellSeen.set(i, h);
    return h;
  };
  // expression value and proof (null: {==})
  const ev = (e: Node): { v: string; p: string | null } => {
    const w = whnfExpr(e);
    if (w.k === "ctor") {
      switch (w.f) {
        case "Cr.Cir.Expr.const": return { v: print(w.a[0]), p: null };
        case "Cr.Cir.Expr.get": return { v: regs[natOf(w.a[0])], p: null };
        case "Cr.Cir.Expr.op": {
          const x = ev(w.a[1]), y = ev(w.a[2]);
          const O = print(w.a[0]);
          const v = `Wa.Wasm.op(${O}, ${x.v}, ${y.v})`;
          if (!x.p && !y.p) return { v, p: null };
          return { v, p: `X.ev.op(${O}, ${print(w.a[1])}, ${print(w.a[2])}, ${stName}, ${x.v}, ${y.v}, ${x.p ?? "{==}"}, ${y.p ?? "{==}"})` };
        }
        case "Cr.Cir.Expr.field": {
          const k = print(whnfExpr(w.a[0]));
          const c = ev(w.a[1]);
          const h = cellPrem(c.v);
          return { v: `Cr.Cir.Cell.get(${k}, Cr.Cir.Cells.get(${cells}, ${c.v}))`, p: `X.ev.fld(${k}, ${print(w.a[1])}, ${stName}, ${c.v}, ${c.p ?? "{==}"}, ${h})` };
        }
        case "Cr.Cir.Expr.eqz": {
          const x = ev(w.a[0]);
          const v = `Bool.to_u32(U32.is_zero(${x.v}))`;
          return { v, p: x.p ? `X.ev.eqz(${print(w.a[0])}, ${stName}, ${x.v}, ${x.p})` : null };
        }
      }
    }
    throw new Error("ev: unknown expression " + print(e));
  };
  const br = (o.br ?? "").split("");
  let bi = 0;
  const Rn = (p: string, st: string) => `Rn(${kit}, ${p}, ${st})`;
  // the chain: an array of open calls, closed at the end (no nesting by recursion)
  const calls: string[] = [];
  let P = path;
  let cur: Node = parse(path, null);
  for (;;) {
    const s = whnfStmt(cur);
    if (s.k === "seq" && !isOpaque(s.a)) {
      const a = whnfStmt(s.a);
      const PB = `X.sel.b(${P})`;
      if (a.k === "set") {
        const r = natOf(a.r);
        const x = ev(a.e);
        const nxt = "s" + ++nst;
        lets.push(`+${nxt} = X.X.setst(${stName}, ${r}n, ${x.v})`);
        stFull = `X.X.setst(${stFull}, ${r}n, ${x.v})`;
        calls.push(`rn.set(${kit}, ${r}n, ${print(a.e)}, ${PB}, ${stName}, ${x.v}, ${x.p ?? "{==}"}, {==}, {==},`);
        regs[r] = x.v; stName = nxt; P = PB; cur = s.b; continue;
      }
      if (a.k === "store") {
        const k = print(whnfExpr(a.f));
        const c = ev(a.c), x = ev(a.v);
        const h = cellPrem(c.v);
        const nxt = "s" + ++nst;
        lets.push(`+${nxt} = X.X.store(${stName}, ${k}, ${c.v}, ${x.v})`);
        stFull = `X.X.store(${stFull}, ${k}, ${c.v}, ${x.v})`;
        calls.push(`rn.store(${kit}, ${k}, ${print(a.c)}, ${print(a.v)}, ${PB}, ${stName}, ${c.v}, ${x.v}, ${c.p ?? "{==}"}, ${x.p ?? "{==}"}, ${h},`);
        cells = `X.X.put(${cells}, ${k}, ${c.v}, ${x.v})`;
        stName = nxt; P = PB; cur = s.b; continue;
      }
    }
    if (s.k === "if") {
      const ch = br[bi++];
      if (ch !== "t" && ch !== "e") break;
      const x = ev(s.c);
      const h = "hz" + nprem++;
      const C = `X.sel.c(${P})`;
      if (ch === "t") {
        prem.push(`+${h}: {U32.is_zero(${x.v}) == False{} : Bool}`);
        calls.push(`rn.if.t(${kit}, ${C}, X.sel.t(${P}), X.sel.e(${P}), ${stName}, ${x.v}, ${x.p ?? "{==}"}, ${h},`);
        P = `X.sel.t(${P})`; cur = s.t;
      } else {
        prem.push(`+${h}: {${x.v} == 0 : U32}`);
        calls.push(`rn.if.e(${kit}, ${C}, X.sel.t(${P}), X.sel.e(${P}), ${stName}, (%${h} : {Cr.Cir.eval(${C}, ${stName}) == Some{_} : Maybe<&2, U32>}; ${x.p ?? "{==}"}),`);
        P = `X.sel.e(${P})`; cur = s.e;
      }
      continue;
    }
    break;
  }
  prem.push(`k: ${Rn(P, stFull)}`);
  const out: string[] = [];
  out.push(`# generated by tools/gen/gen.ts rn ${path} ${o.br ? "--br " + o.br : ""}`);
  out.push(`def ${o.name ?? "seg"}(${params.concat(prem).join(",\n  ")}) ->`);
  out.push(`  ${Rn(path, st0text)}:`);
  for (const l of lets) out.push("  " + l);
  for (let i = 0; i < calls.length; i++) out.push("  " + " ".repeat(i) + calls[i]);
  out.push("  " + " ".repeat(calls.length) + "k" + ")".repeat(calls.length));
  return out.join("\n");
};

// ---- main ----
const argv = process.argv.slice(2);
const t0 = performance.now();
load(argv[0]);
const opts: Record<string, string> = {};
const pos: string[] = [];
const regOver = new Map<number, string>();
const extra: string[] = [];
for (let i = 2; i < argv.length; i++) {
  const a = argv[i];
  if (a.startsWith("--")) {
    const key = a.slice(2), val = argv[++i];
    if (key === "reg") { const [r, v] = val.split("="); regOver.set(parseInt(r), v); }
    else if (key === "param") extra.push(val);
    else if (key === "opaque") for (const x of val.split(",")) opaque.add("Mc." + x);
    else opts[key] = val;
  } else pos.push(a);
}
const mode = argv[1];
const text = mode === "br" ? genBr(pos[0], pos[1], opts) : mode === "rn" ? genRn(pos[0], opts, regOver, extra) : (() => { throw new Error("mode: br | rn"); })();
console.log(text);
console.error(`gen.ts: ${(performance.now() - t0).toFixed(0)} ms`);
