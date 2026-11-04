# S2 notes: statement decisions vs the plan (heap, image, routines, Inv)

Lane S2 of P2. Branch `w/s2` (worktree `bb-wt/s2`), on feature/redesign 9daf8f5 + w/s1 (merged at
eac7893, S1's names as of 6189fe1). Files: `src/Compiler/Machine/heap/{spec,view,count}.bend`,
`image/{spec,impl}.bend`, `routines/{spec,prims,nth,dec,copy,walk,out,input}.bend`, `s2_smoke.bend`.
Checked against Machine/impl.bend as P1 implemented it (p1-handoff.md), Cir/impl.bend's semantics
and the kernel's Eval (Eval/impl.bend). Each deviation is decided on merit.

## Deviations from the plan's text (§4.3, §4.4, §4.7), and why

1. **Roots carry their depth: `Rt{c, d, t}`.** The plan's `Rt{c, t}` reads every root at depth 0.
   But a frame's term is not always at depth 0 (Let's body under 1 binder, Rwt's motive under 2),
   and a popped Let frame's body is an owned root (`M.ret.let`'s z) that the copy reads at depth 1.
   A poison reads as `Var{d}`, so the depth changes the term. With d in the root, push/pop/copy move
   (cell, depth, term) unchanged. `Rts` also asks `fv(c) <= d` (no real variable free at its depth):
   it holds for every root the code makes, and it is what makes a local shareable at any depth
   (the copy's locals have fv 0) and the focus fv 0.
2. **Frames' depths** (`V.FK.depth`): Let 1, Rwt 2 (field 2), Rwt's f (field 3) 0, others 0. Frs
   reads each frame term at its depth, with fv at most it. For a frame other than Rwt, `AF.b` is not
   read (AF.plug ignores it).
3. **ImgOK lives in heap/spec.bend, not image/spec.bend**: H (its `Fix` clause) needs it, and
   image/spec needs heap's view: a cycle otherwise. image/spec keeps Cx.of, St0, Start,
   Cells.bytes and the image laws.
4. **ImgOK pins each view's footprint inside the image** (`ImgOK.within`: cells 1 to 15 or 291 to
   im). Without it `img.frame` (agreement on the image's cells keeps ImgOK) is false: a body view
   could read an own cell. ImgOK does **not** cover the input's cache (cells 16 to 271): only
   M.input reads it, and changes it; its facts belong to input.spec's proof.
5. **The table clause is concrete** (cells 272 to 290 equal `Mc.Img.table`'s fields 2 to 4), and
   `img.table` gives the Bend-function form (`Hs.Tbl.mask/bind/former`, as M.entry and M.bump read
   them). `img.ref`: a Ref's field 2 (Img.ref) is the body of `Book.get`'s def, STATIC, or 0.
6. **Plan's `Base` is `Fix`** (no clash with the module Base): ImgOK; `Cx.im/fi` are the state's
   image and first; im < fi <= next <= 214748364; `St.nregs == Mach.regs()`; outn 0 and out []
   (M.alloc traps once output began, so every routine that takes a cell needs it).
   `Room = Part && Fix` is all that M.alloc needs.
7. **Rts, Frs, Chs take no L**: they ask an own cell (or a STATIC image cell for a root); a cell that
   V.tm reads is no FREE cell (tag 46), so by Part it is live. Clo asks each pointer of a live cell
   to be live or a STATIC image cell (a table or cache cell reads as a poison: no pointer may hold
   one).
8. **V.tm's checks** (`V.chk`): no BUILD; DATA iff Term.is_data; VALUE only on Eval.vals; quantity
   bits for Let/All/Lam/App/Sig/Tup (3 rejected); field 2 of a real Var is its index, of a Ref the
   image's body cell, of a Lab/Mat its name's first number; fv local (`V.fv.kids`, saturating, as
   M.finish and Img.go compute it); a STATIC cell has STATIC parts and is no poison; cell 0 reads
   nothing. A Ref/Enu reads only at an image cell (from `Cx.img`).
9. **view.deeper, view.canon, view.closed ask fv < 524287** besides fv <= d: a saturated fv says
   nothing about the variables. Added laws: view.static (a STATIC cell reads the same at any depth),
   view.canon (fv <= d: canonical at d), view.closed (STATIC, fv <= k: closed at k), view.chk,
   view.tag, view.kid (the generic per-field decomposition: field k of the tag's mask reads, one
   level less, at d + Tbl.bind, as `V.kid(t, k)`), agree.put, agree.refl, agree.trans.
10. **copy.spec is stated for the source's depth `Copy.depth(wt)`** (0 for wt, 1 for z) with the
    premise `|es| <= depth || STATIC(c)` (S3's finding: canon.subst_below needs |es| <= n; a call
    leaf is a STATIC, poison-free image cell). Its result `A.AM.copy(t, es)` is the plan's
    `Copy.term`.
11. **Exact-state laws for the primitives**: alloc.spec, make.spec, release.spec, nth.spec give
    `st2 == Alloc.st/Make.st/Release.st/Nth.st(...)`. make's and push's expressions are evaluated
    by `Ev`/`Evs`: Cir.eval when the expression reads no register of a list (the target and free)
    and only fields of live or STATIC image cells (so the alloc and the stores do not change it).
    The plan's `Took` is these states; `h.node` (the plan's h.new_node) and `h.arg` join them to H.
12. **H-level laws** for what moves call: inc, dec, push, pop, swap, one, release_arg, release_all,
    copy, walk, out, input. Posts: `Kept(st, st2, L, ws)` (cells of L keep fields 0, 2, 3, 4, and
    `Same`: registers outside ws, limit, input, first, image, out, outn), `Shrunk(L2, L)` for those
    that free, and a bound on |L2| for those that take cells, so S4 can compose budgets.
13. **walk.spec's post** quantifies the end chains: `&L2 &e2 &ys2 . Walk.post(...)`: H with the
    chains of wenv (e2, wn = |e2|) and wargs (ys2) in front; at a leaf wres 1, e2 = e, ys2 = ys and wt
    a STATIC image cell of u; waits: wres 2, wargs 0; none: wres 3. Same outside M.walk.scr().
14. **out.spec's Q is `st2 => Empty`** (the plan's `Lg.No` has the halt post's arity).
15. **Not stated**: poison.spec (make.spec applies to M.poison by unfolding), call.spec (M.call
    takes statements; S4 proves it inside the moves), projection laws of H's clauses (one
    `K.bool.and_l/and_r` step), h.dec1/h.release/h.pop_free/h.frame/h.unarg (the H-level routine
    laws cover their uses; P3 lanes add them as helpers in their proof files).
16. **No `K.P2`** (S1's decision): joined facts are one Bool (`&&`), witnesses `&x:T -> ..`. Every
    equation hypothesis is reusable (`for +h: {..}`), as S1 asks.
17. **Aliases**: heap/spec is imported as `Hp` (its defs keep the `V.` prefix: `Hp.V.tm`, `Hp.H`,
    `Hp.Rt`), image/spec as `I`, routines/spec as `R`, header/spec as `Hs`.

## Smoke (s2_smoke.bend; bend2 --check-only: only the imports' TODO count)

- View on the start image of a two-def book (main = λx. f x, f = λy. (y, Lab a)): both bodies, f's
  body deeper, cell 11 (Nil); cell 0 reads nothing; ImgOK at the start; img.ref for a present and an
  absent name; img.table for Let, Rwt, Lam; Start for Cir.result's values.
- **AM.move vs Mach.round()** (the check S3 could not do): whole runs of Mach.code from St0
  (M.input, Mode0), and after every round `Inv(x, st, s)` for s the abstract machine's state, with
  `Mach.round()` run by Cir.exec and `AM.move(ds, VALUE flag of the focus, s)`; halts compared
  (status, and bytes for 0). All pass: id on [] (6 rounds) and [5]; tail (λ-matches of pairs and
  labels in the walk) on [] and [5, 7]; a walk through a poison argument; a stuck free variable
  (halt 2); Let/Min/Rwt/Ann/unlet; a failed meet (halt 2); redexes of λ-matches in the running term
  on [5, 7]; a def call ending in no list of bytes (halt 2). So Inv's clauses (exact counts, Clo,
  Cov, Part, Frs, ImgOK) hold on real states, and the move matches the machine on these branches.
  Negative controls: a state run against the wrong abstract state fails; a wrong view fails.
- Not covered by the runs: a Rwt whose proof is not Rfl, Mat misses by redex with frames, a Q2 bind
  of non-Data (halt 2), Prj on a non-pair, the alloc of a new cell at the edge of memory.

## Register count in the routine laws (review for gen2 --wp, after gen2-wp-notes.md)

No premise added: none is clearly missing.
- Every law with an `Hp.H` or `Hp.Room` premise (alloc, make, inc, dec, push, pop, swap, one,
  release_arg, release_all, copy, walk; out via Inv) reaches the count by `bool.and_l/and_r`:
  H = Room && ..; Room = Part && Fix; Fix's 7th conjunct is `Nat.is_eq(Lg.St.nregs(st), Mc.Mach.regs())`
  (to an equation by `K.nat.is_eq_ok`). With S1's `reg.some`, every register read follows.
- input.spec starts from `I.St0(Mc.Mach.regs(), ..)`: its registers are `List.replicate(U32, 53n, 0)`,
  so the count and every read compute.
- release.spec gives `Nat.is_lt(Mc.R.free(), Lg.St.nregs(st))` (its only set) and the read of r as
  `Lg.Reg(st, r) == Some{c}`; the read of free follows by `reg.some` from the same premise.
- nth.spec gives no count: its two registers come as `Lg.Reg(st, t2) == Some{ce}` and
  `Lg.Reg(st, t1) == Some{..}`, from which `t1, t2 < St.nregs(st)` follow (a List.get that gives Some
  has its index below the length). The prover needs that one list fact (or a kit law
  `reg.lt`: `Reg(st, q) == Some{v}` ⊢ `Nat.is_lt(q, St.nregs(st))`); its callers (copy, walk) have H,
  so a count premise could be added at no cost if P3 prefers it.

## Registers read by Lg.St.reg (0e4b5e8)

`Hp.V.reg(st, r)` (`V.or0(Lg.Reg(st, r))`: the value, 0 when none) and `V.or0` are deleted; every
use (heap/spec 3, routines/spec 13, s2_smoke 1) reads `Lg.St.reg(st, r)` (`Maybe.default(Reg(st, r), 0)`,
S1, feature/redesign 85af8f7): the same value, so each statement means what it meant. So S1's
`Lg.reg.some` (q < St.nregs ⇒ Reg(st, q) == Some{St.reg(st, q)}) applies to H, Frs, Part, Alloc.*,
Walk.*, Inv as written; no bridging lemma (and so nothing for gen2 to prove).

## Review fixes (review-s123.md), statement by statement (d542ce0, 2b666bc, 4bf709a)

Each one checked again against Machine/impl.bend; all smoke runs pass after them (below).

- **F1** `V.rc(g, m, c, d)` (heap/spec): the real variables of the read are bound at d (a real
  Var's index below the binders above it; a poison needs none; by `V.mask`, the fields that
  `V.cells` reads; g = 0 gives False). It does not read fv, which saturates at 524287 (a shared
  bound Var of index >= 524286 gives a root fv_max: the old `fv <= d` at roots was false).
  - `V.held.at` (so `Rts`, `V.frame`, `V.frame.b`, `Chs.go`, `Node.ok`, `Inv`) asks
    `V.rc(next, cells, c, d)` in place of `fv <= d`.
  - `inc.spec`'s premise `hn`: `V.Held && V.rc(next, cells, c, d)` in place of `fv <= d`.
  - `view.deeper`, `view.canon`: premise `hr: V.rc(g, m, c, d)` in place of `hs` (fv < 524287) and
    `hf` (fv <= d); `view.closed`: `hr: V.rc(g, m, c, k)` in place of `hm`, `hf`.
  - New laws: `view.rc_fv` (fv < 524287, fv <= d, a read at any depth ⊢ V.rc at d: the copy's
    sharing test), `view.rc_frame` (Agree on V.cells keeps V.rc), `view.rc_more`, `view.rc_up`
    (d <= d2).
- **F2** `alloc.spec`, `make.spec` posts: `{st2 == ..} & {U32.is_le(St.next(st2), 214748364) == True}`.
  `h.node`, `h.arg`: new premise `hn: U32.is_le(St.next(Make.st(st, r, v)), 214748364)` (h.arg: of its
  arg cell).
- **F3** `inc.spec`, `copy.spec`, `walk.spec`: new premise `hb: |rs| <= 64`. New law `h.count` (H,
  |rs| <= 64, c live and counted ⊢ `U32.is_lt(Fd(1, m, c), 2147483648)`).
- **G1** `Cov` (so H) asks also `V.stat(L, m) <= 6144` (live cells flagged STATIC: the input's
  cache, 256 × 24). Only M.input makes STATIC cells (copy.push drops the flag).
- **G2** `h.rts_swap`, `h.chs_swap`: two neighbouring roots (chains) swap after any prefix `pre`
  (`List.append(pre, a :: b :: rs)`), so any reorder by steps.
- **G4** `h.static_root`: H, `V.img(x, m, c)`, `V.held.at(x, st, c, d, t)` ⊢ H with `Rt{c, d, t}` first.
- (G3, M.call's frame loop, is S4's.)
- For gen2 --wp (no meaning change): `Rts`, `Frs.go`, `Chs.go` state `Cir.is_cell(c, St.image,
  St.first, St.next)` (implied by own/STATIC-image and Fix); laws `alloc.reg`, `make.reg` (the
  registers of Alloc.st/Make.st: r the new cell, free `Alloc.free(st)`, others kept; premise r and
  free below nregs, r ≠ free), `st0.nregs`, `st0.reg` (St0's n registers, each 0; **proven**).
- Smoke after the fixes: s2_smoke all pass (bend2); the reviewer's rv_smoke (9 runs: Rwt not Rfl,
  Mat miss in a redex, Q2 binds, Prj on no pair / in a walk / dead, Mat dead, a partial call) all
  pass, its negative control fails.
