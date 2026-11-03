# compiler: layer B, the move kit
# ===============================
#
# What the moves of the machine share, and the statements that the units of
# layer B prove (each a law, filled by a def of the same name in its unit's
# file; reports/B-laws.md lists them):
#
#   IV: what Inv finds in a state (InvOf, and Acc beside it), the premise of
#     a move; MV: what a move gives (the round's outcome in PostB form, with
#     the peak of its cells, and a fuel that ends it); mv.post, mv.done;
#   the phases' premises (copy.post, data.post, walk.post, input.post and
#     their .done): laws with the types of definitions.bend's conclusions;
#   the moves, one law each (mv.ev.*, mv.ret.*, mv.out);
#   the helpers that the moves use: the table's values (A.*, tbl.*), the
#     tests of M.ev (B.*), the runs of a round's first statements (ev.*,
#     stmt.*), the halts (hr.*, res.val, post.map), the image (img.*).
#
# A move takes IV of a state that Inv finds, of the term t and the measure w,
# and gives MV: for any fuel, the round is an admin move (Inv of t, a smaller
# measure), a step (Inv of Eval's step of t), a halt as HR says, or out of
# memory only when the limit has fewer bytes than Budget; the own cells after
# it are within max(before, Need(ds, t)), and its STATIC own cells (Stat) are
# no more than before; and with some fuel it ends.

import Base
import ../../Book/impl.bend as Bk
import ../../Eval/impl.bend as El
import ../../Wasm/impl.bend as Wa
import ../../Program/impl.bend as Pg
import ../Cir/impl.bend as Cr
import ./impl.bend as Mc
import ./cell_terms.bend as T
import ../need_big.bend as N
import ./definitions.bend as D
import ./statement_runs.bend as X
import ./eval_facts.bend as EV
import ./accounting.bend as AC

# The phases' premises (laws)
# ---------------------------
#
# Each is filled in its unit's file (copy_bridge.bend U5, data_check.bend U6,
# walk.bend U7, input_bridge.bend U8); its conclusion is the named type of
# definitions.bend.

law copy.post:
  for +f: Nat
  for +ds: List<&2, Bk.Def>
  for +ks: List<&2, List<&2, Word(8n)>>
  for +img: List<&2, Bk.Term>
  for +regs: List<&2, U32>
  for +m: Cr.Cir.Cells
  for +nx: U32
  for +fi: U32
  for +im: U32
  for +pg: U32
  for +lim: U32
  for +inp: List<&2, Word(8n)>
  for +wt: Bool
  for +keep: List<&2, Nat>
  for +os: List<&2, D.Rt>
  for +bs: List<&2, D.Rt>
  for +fs: List<&2, D.AF>
  for +sp: U32
  for +pend: U32
  for +ps: List<&2, U32>
  for +c: U32
  for +t: Bk.Term
  for +ce: U32
  for +es: List<&2, El.Arg>
  for +xs: List<&2, D.TmpE>
  for +zs: List<&2, D.Rt>
  for hs: D.HS(ds, ks, img, m, nx, fi, im, os, Con{D.Rt{c, t}, bs}, fs, sp, pend, ps)
  for hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, os, List.append(&2, D.TmpE, D.Ag.cells(es, m, ce), xs), sp, fs, ps, zs)
  for hl: {List.length(&2, U32, regs) == 63n : Nat}
  for hc: {List.get(&2, U32, regs, D.Copy.src(wt)) == Some{c} : Maybe<&2, U32>}
  for hp: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>}
  for he: {List.get(&2, U32, regs, 36n) == Some{ce} : Maybe<&2, U32>}
  for hn: {List.get(&2, U32, regs, 37n) == Some{U32.from_nat(List.length(&2, El.Arg, es))} : Maybe<&2, U32>}
  for env: D.Ag(ds, m, im, fi, nx, ks, img, ps, os, Nil{}, ce, es)
  for ho: N.Le(List.length(&2, D.Rt, os), 64n)
  for hv: {D.Terms.below(D.Arg.terms(es), U32.to_nat(2147483648)) == True{} : Bool}
  for hk: {D.Disj(keep, D.Copy.scr(Mc.R.n())) == True{} : Bool}
  D.CopyPost(f, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, wt, keep, os, bs, fs, sp, pend, ps, c, t, ce, es, xs, zs, hs, hac, hl, hc, hp, he, hn, env, ho, hv, hk)

law copy.done:
  for +ds: List<&2, Bk.Def>
  for +ks: List<&2, List<&2, Word(8n)>>
  for +img: List<&2, Bk.Term>
  for +regs: List<&2, U32>
  for +m: Cr.Cir.Cells
  for +nx: U32
  for +fi: U32
  for +im: U32
  for +pg: U32
  for +lim: U32
  for +inp: List<&2, Word(8n)>
  for +wt: Bool
  for +os: List<&2, D.Rt>
  for +bs: List<&2, D.Rt>
  for +fs: List<&2, D.AF>
  for +sp: U32
  for +pend: U32
  for +ps: List<&2, U32>
  for +c: U32
  for +t: Bk.Term
  for +ce: U32
  for +es: List<&2, El.Arg>
  for +xs: List<&2, D.TmpE>
  for +zs: List<&2, D.Rt>
  for hs: D.HS(ds, ks, img, m, nx, fi, im, os, Con{D.Rt{c, t}, bs}, fs, sp, pend, ps)
  for hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, os, List.append(&2, D.TmpE, D.Ag.cells(es, m, ce), xs), sp, fs, ps, zs)
  for hl: {List.length(&2, U32, regs) == 63n : Nat}
  for hc: {List.get(&2, U32, regs, D.Copy.src(wt)) == Some{c} : Maybe<&2, U32>}
  for hp: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>}
  for he: {List.get(&2, U32, regs, 36n) == Some{ce} : Maybe<&2, U32>}
  for hn: {List.get(&2, U32, regs, 37n) == Some{U32.from_nat(List.length(&2, El.Arg, es))} : Maybe<&2, U32>}
  for env: D.Ag(ds, m, im, fi, nx, ks, img, ps, os, Nil{}, ce, es)
  for ho: N.Le(List.length(&2, D.Rt, os), 64n)
  for hv: {D.Terms.below(D.Arg.terms(es), U32.to_nat(2147483648)) == True{} : Bool}
  D.CopyDone(ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, wt, os, bs, fs, sp, pend, ps, c, t, ce, es, xs, zs, hs, hac, hl, hc, hp, he, hn, env, ho, hv)

law data.post:
  for +f: Nat
  for +ds: List<&2, Bk.Def>
  for +ks: List<&2, List<&2, Word(8n)>>
  for +img: List<&2, Bk.Term>
  for +regs: List<&2, U32>
  for +m: Cr.Cir.Cells
  for +nx: U32
  for +fi: U32
  for +im: U32
  for +pg: U32
  for +lim: U32
  for +inp: List<&2, Word(8n)>
  for +r: Nat
  for +keep: List<&2, Nat>
  for +os: List<&2, D.Rt>
  for +bs: List<&2, D.Rt>
  for +fs: List<&2, D.AF>
  for +sp: U32
  for +pend: U32
  for +ps: List<&2, U32>
  for +c: U32
  for +v: Bk.Term
  for +xs: List<&2, D.TmpE>
  for +zs: List<&2, D.Rt>
  for hs: D.HS(ds, ks, img, m, nx, fi, im, os, Con{D.Rt{c, v}, bs}, fs, sp, pend, ps)
  for hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, os, xs, sp, fs, ps, zs)
  for hl: {List.length(&2, U32, regs) == 63n : Nat}
  for hc: {List.get(&2, U32, regs, r) == Some{c} : Maybe<&2, U32>}
  for hp: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>}
  for hr: {D.Nat.mem(D.Data.scr(), r) == False{} : Bool}
  for hk: {D.Disj(keep, D.Data.scr()) == True{} : Bool}
  D.DataPost(f, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, r, keep, os, bs, fs, sp, pend, ps, c, v, xs, zs, hs, hac, hl, hc, hp, hr, hk)

law data.done:
  for +ds: List<&2, Bk.Def>
  for +ks: List<&2, List<&2, Word(8n)>>
  for +img: List<&2, Bk.Term>
  for +regs: List<&2, U32>
  for +m: Cr.Cir.Cells
  for +nx: U32
  for +fi: U32
  for +im: U32
  for +pg: U32
  for +lim: U32
  for +inp: List<&2, Word(8n)>
  for +r: Nat
  for +os: List<&2, D.Rt>
  for +bs: List<&2, D.Rt>
  for +fs: List<&2, D.AF>
  for +sp: U32
  for +pend: U32
  for +ps: List<&2, U32>
  for +c: U32
  for +v: Bk.Term
  for hs: D.HS(ds, ks, img, m, nx, fi, im, os, Con{D.Rt{c, v}, bs}, fs, sp, pend, ps)
  for hl: {List.length(&2, U32, regs) == 63n : Nat}
  for hc: {List.get(&2, U32, regs, r) == Some{c} : Maybe<&2, U32>}
  for hp: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>}
  for hr: {D.Nat.mem(D.Data.scr(), r) == False{} : Bool}
  D.DataDone(ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, r, os, bs, fs, sp, pend, ps, c, v, hs, hl, hc, hp, hr)

law walk.post:
  for +f: Nat
  for +ds: List<&2, Bk.Def>
  for +ks: List<&2, List<&2, Word(8n)>>
  for +img: List<&2, Bk.Term>
  for +regs: List<&2, U32>
  for +m: Cr.Cir.Cells
  for +nx: U32
  for +fi: U32
  for +im: U32
  for +pg: U32
  for +lim: U32
  for +inp: List<&2, Word(8n)>
  for +keep: List<&2, Nat>
  for +os: List<&2, D.Rt>
  for +bs: List<&2, D.Rt>
  for +fs: List<&2, D.AF>
  for +sp: U32
  for +pend: U32
  for +ps: List<&2, U32>
  for +tc: U32
  for +tt: Bk.Term
  for +a: U32
  for +xs: List<&2, El.Arg>
  for +xs0: List<&2, D.TmpE>
  for +zs: List<&2, D.Rt>
  for hs: D.HS(ds, ks, img, m, nx, fi, im, os, Con{D.Rt{tc, tt}, bs}, fs, sp, pend, ps)
  for hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, os, List.append(&2, D.TmpE, D.Ag.cells(xs, m, a), xs0), sp, fs, ps, zs)
  for hst: {D.Fl(m, tc, 1024) == True{} : Bool}
  for hl: {List.length(&2, U32, regs) == 63n : Nat}
  for ht: {List.get(&2, U32, regs, 19n) == Some{tc} : Maybe<&2, U32>}
  for ha: {List.get(&2, U32, regs, 21n) == Some{a} : Maybe<&2, U32>}
  for hp: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>}
  for args: D.Ag(ds, m, im, fi, nx, ks, img, ps, os, Nil{}, a, xs)
  for hk: {D.Disj(keep, D.Walk.scr()) == True{} : Bool}
  D.WalkPost(f, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, keep, os, bs, fs, sp, pend, ps, tc, tt, a, xs, xs0, zs, hs, hac, hst, hl, ht, ha, hp, args, hk)

law walk.done:
  for +ds: List<&2, Bk.Def>
  for +ks: List<&2, List<&2, Word(8n)>>
  for +img: List<&2, Bk.Term>
  for +regs: List<&2, U32>
  for +m: Cr.Cir.Cells
  for +nx: U32
  for +fi: U32
  for +im: U32
  for +pg: U32
  for +lim: U32
  for +inp: List<&2, Word(8n)>
  for +os: List<&2, D.Rt>
  for +bs: List<&2, D.Rt>
  for +fs: List<&2, D.AF>
  for +sp: U32
  for +pend: U32
  for +ps: List<&2, U32>
  for +tc: U32
  for +tt: Bk.Term
  for +a: U32
  for +xs: List<&2, El.Arg>
  for hs: D.HS(ds, ks, img, m, nx, fi, im, os, Con{D.Rt{tc, tt}, bs}, fs, sp, pend, ps)
  for hst: {D.Fl(m, tc, 1024) == True{} : Bool}
  for hl: {List.length(&2, U32, regs) == 63n : Nat}
  for ht: {List.get(&2, U32, regs, 19n) == Some{tc} : Maybe<&2, U32>}
  for ha: {List.get(&2, U32, regs, 21n) == Some{a} : Maybe<&2, U32>}
  for hp: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>}
  for args: D.Ag(ds, m, im, fi, nx, ks, img, ps, os, Nil{}, a, xs)
  D.WalkDone(ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, os, bs, fs, sp, pend, ps, tc, tt, a, xs, hs, hst, hl, ht, ha, hp, args)

# Open: the start (start_input.bend). From St0, with the image of a book that
# Book.read reads, M.input ends with InvIn, or runs out of memory, for any
# fuel; and with some fuel it ends.
law input.post:
  for +f: Nat
  for +p: List<&2, Word(8n)>
  for +ds: List<&2, Bk.Def>
  for +i: List<&2, Word(8n)>
  for +m: U32
  for +k: U32
  for +len: U32
  for +pg: U32
  for +lim: U32
  for +first: U32
  for rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>}
  for small: {Mc.Img.small(p, 0) == True{} : Bool}
  for s: D.Start(Mc.Img.cells(ds), i, m, k, len, pg, lim, first)
  D.InputPost(f, p, ds, i, m, k, len, pg, lim, first, rd, small, s)

law input.done:
  for +p: List<&2, Word(8n)>
  for +ds: List<&2, Bk.Def>
  for +i: List<&2, Word(8n)>
  for +m: U32
  for +k: U32
  for +len: U32
  for +pg: U32
  for +lim: U32
  for +first: U32
  for rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>}
  for small: {Mc.Img.small(p, 0) == True{} : Bool}
  for s: D.Start(Mc.Img.cells(ds), i, m, k, len, pg, lim, first)
  D.InputDone(p, ds, i, m, k, len, pg, lim, first, rd, small, s)

# Kit
# ---

# Eval: a value has no step (Lean's eval_value)
def ev.stops(+ds: List<&2, Bk.Def>, +t: Bk.Term, h: {El.Eval.vals(ds, t, False{}) == True{} : Bool}) ->
  {El.Eval.step(ds, t) == None{} : Maybe<Bk.Term>}:
  EV.ev.stops(ds, t, h)

# a term with a step is no value
def vals.of(b: Bool, +ds: List<&2, Bk.Def>, +t: Bk.Term, -u: Bk.Term, eb: {El.Eval.vals(ds, t, False{}) == b : Bool},
  es: {El.Eval.step(ds, t) == Some{u} : Maybe<Bk.Term>}) -> {El.Eval.vals(ds, t, False{}) == False{} : Bool}:
  match b:
    case False{}:
      eb
    case True{}:
      Empty.absurd({El.Eval.vals(ds, t, False{}) == False{} : Bool},
        D.st.ne(u, Equal.trans(Maybe<Bk.Term>, None{}, El.Eval.step(ds, t), Some{u},
          Equal.sym(Maybe<Bk.Term>, El.Eval.step(ds, t), None{}, ev.stops(ds, t, eb)), es)))


# Inv's facts of that state, with the abstract state of ret, focus and fs:
# InvOf, and the accounting of its cells (Acc, with the zombies zs)
def IV(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +t: Bk.Term, +w: Nat, +ret: Bool, +focus: Bk.Term,
  +fs: List<&2, D.AF>, +ps: List<&2, U32>) -> Data:
  D.P2(D.InvOf(ds, ks, img, D.RG(foc, Bool.to_u32(ret), sp, pend, D.R59.list(rest)), m, nx, fi, im, Nil{}, 0, t, w, ret, focus, fs, foc, sp,
    pend, ps, rest),
    D.Ex(List<&2, D.Rt>, zs => D.AccK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{foc, focus}], Nil{}, sp, fs, ps, zs)))

# the next state of a round from st, of the term t and the measure w: an admin
# move or a step (Rnd), with the own cells within the round's peak, and no
# more STATIC own cells than st has
def MV.next(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st: Cr.Cir.State, +t: Bk.Term,
  +w: Nat, s: Cr.Cir.State) -> Type:
  D.Rnd(ds, ks, img, t, w, s) & N.Le(D.Mem.cells(s), Nat.max(D.Mem.cells(st), D.Need(ds, st, t))) &
    N.Le(D.Stat(D.Mem.cells(s), D.St.cells(s), D.St.first(s)), D.Stat(D.Mem.cells(st), D.St.cells(st), D.St.first(st)))

# a move from st: for any fuel, a round that goes on (MV.next) or halts as HR
# says, out of memory only below Budget; and a fuel with which it ends
def MV(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st: Cr.Cir.State, +t: Bk.Term, +w: Nat) ->
  Type:
  (@f: Nat -> D.PostB(False{}, Cr.Cir.exec(f, D.B.body(), st), s => MV.next(ds, ks, img, st, t, w, s), s => st2 => D.HR(ds, t, s, st2),
    D.Budget(ds, st, t), D.St.lim(st))) &
    D.Ex(Nat, f => D.Ends(Cr.Cir.exec(f, D.B.body(), st)))

# MV.next's round
def MV.rnd(-ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -st: Cr.Cir.State, -t: Bk.Term,
  -w: Nat, -s: Cr.Cir.State, h: MV.next(ds, ks, img, st, t, w, s)) -> D.Rnd(ds, ks, img, t, w, s):
  match h:
    case Tuple{r, _}:
      r

def mv.post(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st: Cr.Cir.State,
  +t: Bk.Term, +w: Nat, h: MV(ds, ks, img, st, t, w)) ->
  D.Post(False{}, Cr.Cir.exec(f, D.B.body(), st), s => D.Rnd(ds, ks, img, t, w, s), s => st2 => D.HR(ds, t, s, st2)):
  match h:
    case Tuple{p, _}:
      D.postb.post(False{}, Cr.Cir.exec(f, D.B.body(), st), s => MV.next(ds, ks, img, st, t, w, s), s => D.Rnd(ds, ks, img, t, w, s),
        s => st2 => D.HR(ds, t, s, st2), D.Budget(ds, st, t), D.St.lim(st), p(f), s => r => MV.rnd(ds, ks, img, st, t, w, s, r))

def mv.done(-ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -st: Cr.Cir.State, -t: Bk.Term,
  -w: Nat, h: MV(ds, ks, img, st, t, w)) -> D.Ex(Nat, f => D.Ends(Cr.Cir.exec(f, D.B.body(), st))):
  match h:
    case Tuple{_, d}:
      d

# The STATIC own cells of a round
# -------------------------------
#
# A move carries "Stat now <= Stat at the round's start" through its
# statements: inc.post, dec.post and release.post keep Stat, and a store of a
# cell with no flag STATIC (AC.stat.set), the flag DATA (AC.stat.flag) and
# M.alloc's cell (stat.alloc) do not raise it.

# the first cell is at most next (Heap's last part), which stat.alloc asks
def heap.fin(-m: Cr.Cir.Cells, -nx: U32, -fi: U32, -im: U32, -rs: List<&2, U32>, -pend: U32, -ps: List<&2, U32>,
  h: D.Heap(m, nx, fi, im, rs, pend, ps)) -> {U32.is_le(fi, nx) == True{} : Bool}:
  match h:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, e}}}}}:
      e

# so in HSK
def hsk.fin(-dk: Bool, -ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -m: Cr.Cir.Cells, -nx: U32,
  -fi: U32, -im: U32, -os: List<&2, D.Rt>, -bs: List<&2, D.Rt>, -fs: List<&2, D.AF>, -sp: U32, -pend: U32, -ps: List<&2, U32>,
  h: D.HSK(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps)) -> {U32.is_le(fi, nx) == True{} : Bool}:
  match h:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{hp, _}}}}}:
      heap.fin(m, nx, fi, im, D.Rt.cells(os), pend, ps, hp)

# a step that keeps Stat keeps a bound of it
def stat.keep(+n: Nat, +m: Cr.Cir.Cells, +m1: Cr.Cir.Cells, +fi: U32, -S: Nat,
  e: {D.Stat(n, m1, fi) == D.Stat(n, m, fi) : Nat}, h: N.Le(D.Stat(n, m, fi), S)) -> N.Le(D.Stat(n, m1, fi), S):
  N.le_rw_l(D.Stat(n, m, fi), D.Stat(n, m1, fi), S, Equal.sym(Nat, D.Stat(n, m1, fi), D.Stat(n, m, fi), e), h)

# the new cell nx of M.alloc (stat.alloc)
def stat.new(+m: Cr.Cir.Cells, +nx: U32, +fi: U32, +ps: List<&2, U32>, +z: U32, +nx1: U32, +ws: List<&2, D.W1>,
  hfn: {U32.is_le(fi, nx) == True{} : Bool},
  e: {Bool.and(D.Pend.none(ps), Bool.and(U32.is_eq(z, nx), U32.is_eq(nx1, U32.inc(nx)))) == True{} : Bool},
  hown: {D.Own(fi, nx1, z) == True{} : Bool}) ->
  N.Le(D.Stat(Nat.sub(U32.to_nat(nx1), U32.to_nat(fi)), Cr.Cir.Cells.set(D.Put1(ws, m), z, Cr.Cir.Cell.zero()), fi),
    D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi)):
  +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
  +P = D.Put1(ws, m)
  +Z = Cr.Cir.Cell.zero()
  +e2 = D.and.r(D.Pend.none(ps), Bool.and(U32.is_eq(z, nx), U32.is_eq(nx1, U32.inc(nx))), e)
  +ez = D.u32.eq(z, nx, D.and.l(U32.is_eq(z, nx), U32.is_eq(nx1, U32.inc(nx)), e2))
  +en = D.u32.eq(nx1, U32.inc(nx), D.and.r(U32.is_eq(z, nx), U32.is_eq(nx1, U32.inc(nx)), e2))
  +hl = {(%ez : {U32.is_lt(_, nx1) == True{} : Bool}; D.and.r(U32.is_le(fi, z), U32.is_lt(z, nx1), hown)) :
    {U32.is_lt(nx, nx1) == True{} : Bool}}
  %Equal.sym(U32, z, nx, ez) : N.Le(D.Stat(Nat.sub(U32.to_nat(nx1), U32.to_nat(fi)), Cr.Cir.Cells.set(P, _, Z), fi), D.Stat(n, m, fi))
  %Equal.sym(U32, nx1, U32.inc(nx), en) : N.Le(D.Stat(Nat.sub(U32.to_nat(_), U32.to_nat(fi)), Cr.Cir.Cells.set(P, nx, Z), fi), D.Stat(n, m, fi))
  N.le_rw_l(D.Stat(n, m, fi), D.Stat(Nat.sub(U32.to_nat(U32.inc(nx)), U32.to_nat(fi)), Cr.Cir.Cells.set(P, nx, Z), fi), D.Stat(n, m, fi),
    Equal.sym(Nat, D.Stat(Nat.sub(U32.to_nat(U32.inc(nx)), U32.to_nat(fi)), Cr.Cir.Cells.set(P, nx, Z), fi), D.Stat(n, m, fi),
      Equal.trans(Nat, D.Stat(Nat.sub(U32.to_nat(U32.inc(nx)), U32.to_nat(fi)), Cr.Cir.Cells.set(P, nx, Z), fi), D.Stat(n, P, fi), D.Stat(n, m, fi),
        AC.stat.fresh(P, nx, fi, nx1, hfn, hl), AC.stat.put1(n, ws, m, fi))),
    N.le_refl(D.Stat(n, m, fi)))

# M.alloc's cell z, as alloc.post gives it: the cells m1 are m with stores to
# field 1 and z all zeros, z of the pend list (next stays) or the new cell nx
# (next grows by one)
def stat.alloc(+m: Cr.Cir.Cells, +nx: U32, +fi: U32, +ps: List<&2, U32>, +z: U32, +nx1: U32, +m1: Cr.Cir.Cells,
  hfn: {U32.is_le(fi, nx) == True{} : Bool},
  hws: D.Ex(List<&2, D.W1>, ws => D.P2({m1 == Cr.Cir.Cells.set(D.Put1(ws, m), z, Cr.Cir.Cell.zero()) : Cr.Cir.Cells}, {D.Took(ws, ps, m) == True{} : Bool})),
  hor: {Bool.or(Bool.and(D.Mem(ps, z), U32.is_eq(nx1, nx)), Bool.and(D.Pend.none(ps), Bool.and(U32.is_eq(z, nx), U32.is_eq(nx1, U32.inc(nx))))) == True{} : Bool},
  hown: {D.Own(fi, nx1, z) == True{} : Bool}) ->
  N.Le(D.Stat(Nat.sub(U32.to_nat(nx1), U32.to_nat(fi)), m1, fi), D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi)):
  match hws:
    case Tuple{+ws, Tuple{em1, _}}:
      +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
      +P = D.Put1(ws, m)
      +Z = Cr.Cir.Cell.zero()
      +ep = AC.stat.put1(n, ws, m, fi)
      %Equal.sym(Cr.Cir.Cells, m1, Cr.Cir.Cells.set(P, z, Z), em1) :
        N.Le(D.Stat(Nat.sub(U32.to_nat(nx1), U32.to_nat(fi)), _, fi), D.Stat(n, m, fi))
      D.or.cases(Bool.and(D.Mem(ps, z), U32.is_eq(nx1, nx)), Bool.and(D.Pend.none(ps), Bool.and(U32.is_eq(z, nx), U32.is_eq(nx1, U32.inc(nx)))),
        N.Le(D.Stat(Nat.sub(U32.to_nat(nx1), U32.to_nat(fi)), Cr.Cir.Cells.set(P, z, Z), fi), D.Stat(n, m, fi)), hor,
        e => (%Equal.sym(U32, nx1, nx, D.u32.eq(nx1, nx, D.and.r(D.Mem(ps, z), U32.is_eq(nx1, nx), e))) :
            N.Le(D.Stat(Nat.sub(U32.to_nat(_), U32.to_nat(fi)), Cr.Cir.Cells.set(P, z, Z), fi), D.Stat(n, m, fi));
          N.le_rw_r(D.Stat(n, Cr.Cir.Cells.set(P, z, Z), fi), D.Stat(n, P, fi), D.Stat(n, m, fi), ep, AC.stat.set(n, P, fi, z, Z, {==}))),
        e => stat.new(m, nx, fi, ps, z, nx1, ws, hfn, e, hown))

# M.alloc's cell z, then a store at z of a cell x with no flag STATIC (as
# M.make and M.push do)
def stat.make(+m: Cr.Cir.Cells, +nx: U32, +fi: U32, +ps: List<&2, U32>, +z: U32, +nx1: U32, +m1: Cr.Cir.Cells, +x: Cr.Cir.Cell,
  hx: {D.FlW(Cr.Cir.Cell.get(0n, x), 1024) == False{} : Bool}, hfn: {U32.is_le(fi, nx) == True{} : Bool},
  hws: D.Ex(List<&2, D.W1>, ws => D.P2({m1 == Cr.Cir.Cells.set(D.Put1(ws, m), z, Cr.Cir.Cell.zero()) : Cr.Cir.Cells}, {D.Took(ws, ps, m) == True{} : Bool})),
  hor: {Bool.or(Bool.and(D.Mem(ps, z), U32.is_eq(nx1, nx)), Bool.and(D.Pend.none(ps), Bool.and(U32.is_eq(z, nx), U32.is_eq(nx1, U32.inc(nx))))) == True{} : Bool},
  hown: {D.Own(fi, nx1, z) == True{} : Bool}) ->
  N.Le(D.Stat(Nat.sub(U32.to_nat(nx1), U32.to_nat(fi)), Cr.Cir.Cells.set(m1, z, x), fi), D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi)):
  +n1 = Nat.sub(U32.to_nat(nx1), U32.to_nat(fi))
  N.le_trans(D.Stat(n1, Cr.Cir.Cells.set(m1, z, x), fi), D.Stat(n1, m1, fi), D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi),
    AC.stat.set(n1, m1, fi, z, x, hx), stat.alloc(m, nx, fi, ps, z, nx1, m1, hfn, hws, hor, hown))


# a frame of App q □ x: app_arg or app_val
def FK.isapp(k: D.FK) -> Bool:
  match k:
    case D.FK.arg{}:
      True{}
    case D.FK.val{}:
      True{}
    case _:
      False{}

# a value by its form, as the table says (I.table's field 4): every former but
# Tup
def A.tbl(t: Bk.Term) -> Bool:
  match t:
    case Bk.Term.Typ{_}:
      True{}
    case Bk.Term.All{_, _, _}:
      True{}
    case Bk.Term.Lam{_, _}:
      True{}
    case Bk.Term.Sig{_, _, _}:
      True{}
    case Bk.Term.Prj{_}:
      True{}
    case Bk.Term.Enu{_}:
      True{}
    case Bk.Term.Lab{_}:
      True{}
    case Bk.Term.Mat{_, _, _}:
      True{}
    case Bk.Term.Efq{}:
      True{}
    case Bk.Term.Eql{_, _, _}:
      True{}
    case Bk.Term.Rfl{}:
      True{}
    case _:
      False{}

# a λ, a λ-match of pairs or of labels: the redexes of M.redex's first cases
def A.node(t: Bk.Term) -> Bool:
  match t:
    case Bk.Term.Lam{_, _}:
      True{}
    case Bk.Term.Prj{_}:
      True{}
    case Bk.Term.Mat{_, _, _}:
      True{}
    case _:
      False{}

# the table's cell of the tag of a term's cell is a cell
def vt.of(-m: Cr.Cir.Cells, -im: U32, -fi: U32, -nx: U32, -f0: U32, +focus: Bk.Term, etag: {D.TgW(f0) == D.A.tag(focus) : U32},
  tb: D.Tbl(m, im, fi, nx)) -> {Cr.Cir.is_cell(U32.add(272, U32.and(f0, 63)), im, fi, nx) == True{} : Bool}:
  %Equal.sym(U32, D.TgW(f0), D.A.tag(focus), etag) : {Cr.Cir.is_cell(U32.add(272, _), im, fi, nx) == True{} : Bool}
  D.tbl.at(m, im, fi, nx, focus, tb)

# the test of M.ev on a cell flagged VALUE is not 0
def nz.of(-f0: U32, +e4: U32, hv: {U32.is_ne(U32.and(f0, 256), 0) == True{} : Bool}) ->
  {U32.is_zero(U32.or(Bool.to_u32(U32.is_ne(U32.and(f0, 256), 0)), Bool.to_u32(U32.is_ne(e4, 0)))) == False{} : Bool}:
  %Equal.sym(Bool, U32.is_ne(U32.and(f0, 256), 0), True{}, hv) :
    {U32.is_zero(U32.or(Bool.to_u32(_), Bool.to_u32(U32.is_ne(e4, 0)))) == False{} : Bool}
  D.or1(U32.is_ne(e4, 0))

# field 4 of the table's cell of a tag: 1 for a value by its form
def A.f4(t: Bk.Term) -> U32:
  match t:
    case Bk.Term.Var{_}:
      0
    case Bk.Term.Ref{_}:
      0
    case Bk.Term.Ann{_, _}:
      0
    case Bk.Term.Let{_, _, _}:
      0
    case Bk.Term.Typ{_}:
      1
    case Bk.Term.Min{_, _}:
      0
    case Bk.Term.All{_, _, _}:
      1
    case Bk.Term.Lam{_, _}:
      1
    case Bk.Term.App{_, _, _}:
      0
    case Bk.Term.Sig{_, _, _}:
      1
    case Bk.Term.Tup{_, _, _}:
      0
    case Bk.Term.Prj{_}:
      1
    case Bk.Term.Enu{_}:
      1
    case Bk.Term.Lab{_}:
      1
    case Bk.Term.Mat{_, _, _}:
      1
    case Bk.Term.Efq{}:
      1
    case Bk.Term.Eql{_, _, _}:
      1
    case Bk.Term.Rfl{}:
      1
    case Bk.Term.Rwt{_, _, _}:
      0

def tbl.f4(-m: Cr.Cir.Cells, -im: U32, -fi: U32, -nx: U32, t: Bk.Term, h: D.Tbl(m, im, fi, nx)) ->
  {D.Fd(4n, m, U32.add(272, D.A.tag(t))) == A.f4(t) : U32}:
  match t:
    case Bk.Term.Var{_}:
      match h:
        case Tuple{_, Tuple{e, _}}:
          D.tbl.fd(4n, m, 272, Cr.Cir.Cell{0, 0, 0, 0, 0}, e)
    case Bk.Term.Ref{_}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}:
          D.tbl.fd(4n, m, 273, Cr.Cir.Cell{0, 0, 0, 0, 0}, e)
    case Bk.Term.Ann{_, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}:
          D.tbl.fd(4n, m, 274, Cr.Cir.Cell{0, 0, 3, 0, 0}, e)
    case Bk.Term.Let{_, _, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}:
          D.tbl.fd(4n, m, 275, Cr.Cir.Cell{0, 0, 3, 4, 0}, e)
    case Bk.Term.Typ{_}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}:
          D.tbl.fd(4n, m, 276, Cr.Cir.Cell{0, 0, 1, 0, 1}, e)
    case Bk.Term.Min{_, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}:
          D.tbl.fd(4n, m, 277, Cr.Cir.Cell{0, 0, 3, 0, 0}, e)
    case Bk.Term.All{_, _, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}:
          D.tbl.fd(4n, m, 278, Cr.Cir.Cell{0, 0, 3, 4, 1}, e)
    case Bk.Term.Lam{_, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}:
          D.tbl.fd(4n, m, 279, Cr.Cir.Cell{0, 0, 1, 1, 1}, e)
    case Bk.Term.App{_, _, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}:
          D.tbl.fd(4n, m, 280, Cr.Cir.Cell{0, 0, 3, 0, 0}, e)
    case Bk.Term.Sig{_, _, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}:
          D.tbl.fd(4n, m, 281, Cr.Cir.Cell{0, 0, 3, 4, 1}, e)
    case Bk.Term.Tup{_, _, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}:
          D.tbl.fd(4n, m, 282, Cr.Cir.Cell{0, 0, 3, 0, 0}, e)
    case Bk.Term.Prj{_}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}:
          D.tbl.fd(4n, m, 283, Cr.Cir.Cell{0, 0, 1, 0, 1}, e)
    case Bk.Term.Enu{_}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}:
          D.tbl.fd(4n, m, 284, Cr.Cir.Cell{0, 0, 0, 0, 1}, e)
    case Bk.Term.Lab{_}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          D.tbl.fd(4n, m, 285, Cr.Cir.Cell{0, 0, 0, 0, 1}, e)
    case Bk.Term.Mat{_, _, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          D.tbl.fd(4n, m, 286, Cr.Cir.Cell{0, 0, 6, 0, 1}, e)
    case Bk.Term.Efq{}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          D.tbl.fd(4n, m, 287, Cr.Cir.Cell{0, 0, 0, 0, 1}, e)
    case Bk.Term.Eql{_, _, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          D.tbl.fd(4n, m, 288, Cr.Cir.Cell{0, 0, 7, 0, 1}, e)
    case Bk.Term.Rfl{}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          D.tbl.fd(4n, m, 289, Cr.Cir.Cell{0, 0, 0, 0, 1}, e)
    case Bk.Term.Rwt{_, _, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          D.tbl.fd(4n, m, 290, Cr.Cir.Cell{0, 0, 7, 8, 0}, e)


# a value by its form, as the table says, has field 4 set
def f4.one(t: Bk.Term, hf: {A.tbl(t) == True{} : Bool}) -> {A.f4(t) == 1 : U32}:
  match t:
    case Bk.Term.Var{+x0}:
      D.bool.ft({A.f4(Bk.Term.Var{x0}) == 1 : U32}, hf)
    case Bk.Term.Ref{+x0}:
      D.bool.ft({A.f4(Bk.Term.Ref{x0}) == 1 : U32}, hf)
    case Bk.Term.Ann{+x0, +x1}:
      D.bool.ft({A.f4(Bk.Term.Ann{x0, x1}) == 1 : U32}, hf)
    case Bk.Term.Let{+x0, +x1, +x2}:
      D.bool.ft({A.f4(Bk.Term.Let{x0, x1, x2}) == 1 : U32}, hf)
    case Bk.Term.Typ{+x0}:
      {==}
    case Bk.Term.Min{+x0, +x1}:
      D.bool.ft({A.f4(Bk.Term.Min{x0, x1}) == 1 : U32}, hf)
    case Bk.Term.All{+x0, +x1, +x2}:
      {==}
    case Bk.Term.Lam{+x0, +x1}:
      {==}
    case Bk.Term.App{+x0, +x1, +x2}:
      D.bool.ft({A.f4(Bk.Term.App{x0, x1, x2}) == 1 : U32}, hf)
    case Bk.Term.Sig{+x0, +x1, +x2}:
      {==}
    case Bk.Term.Tup{+x0, +x1, +x2}:
      D.bool.ft({A.f4(Bk.Term.Tup{x0, x1, x2}) == 1 : U32}, hf)
    case Bk.Term.Prj{+x0}:
      {==}
    case Bk.Term.Enu{+x0}:
      {==}
    case Bk.Term.Lab{+x0}:
      {==}
    case Bk.Term.Mat{+x0, +x1, +x2}:
      {==}
    case Bk.Term.Efq{}:
      {==}
    case Bk.Term.Eql{+x0, +x1, +x2}:
      {==}
    case Bk.Term.Rfl{}:
      {==}
    case Bk.Term.Rwt{+x0, +x1, +x2}:
      D.bool.ft({A.f4(Bk.Term.Rwt{x0, x1, x2}) == 1 : U32}, hf)

# a value by its form, as the table says, is a value
def tbl.vals(+ds: List<&2, Bk.Def>, t: Bk.Term, hf: {A.tbl(t) == True{} : Bool}) ->
  {Bool.or(Bool.not(True{}), El.Eval.vals(ds, t, False{})) == True{} : Bool}:
  match t:
    case Bk.Term.Var{+x0}:
      D.bool.ft({Bool.or(Bool.not(True{}), El.Eval.vals(ds, Bk.Term.Var{x0}, False{})) == True{} : Bool}, hf)
    case Bk.Term.Ref{+x0}:
      D.bool.ft({Bool.or(Bool.not(True{}), El.Eval.vals(ds, Bk.Term.Ref{x0}, False{})) == True{} : Bool}, hf)
    case Bk.Term.Ann{+x0, +x1}:
      D.bool.ft({Bool.or(Bool.not(True{}), El.Eval.vals(ds, Bk.Term.Ann{x0, x1}, False{})) == True{} : Bool}, hf)
    case Bk.Term.Let{+x0, +x1, +x2}:
      D.bool.ft({Bool.or(Bool.not(True{}), El.Eval.vals(ds, Bk.Term.Let{x0, x1, x2}, False{})) == True{} : Bool}, hf)
    case Bk.Term.Typ{+x0}:
      {==}
    case Bk.Term.Min{+x0, +x1}:
      D.bool.ft({Bool.or(Bool.not(True{}), El.Eval.vals(ds, Bk.Term.Min{x0, x1}, False{})) == True{} : Bool}, hf)
    case Bk.Term.All{+x0, +x1, +x2}:
      {==}
    case Bk.Term.Lam{+x0, +x1}:
      {==}
    case Bk.Term.App{+x0, +x1, +x2}:
      D.bool.ft({Bool.or(Bool.not(True{}), El.Eval.vals(ds, Bk.Term.App{x0, x1, x2}, False{})) == True{} : Bool}, hf)
    case Bk.Term.Sig{+x0, +x1, +x2}:
      {==}
    case Bk.Term.Tup{+x0, +x1, +x2}:
      D.bool.ft({Bool.or(Bool.not(True{}), El.Eval.vals(ds, Bk.Term.Tup{x0, x1, x2}, False{})) == True{} : Bool}, hf)
    case Bk.Term.Prj{+x0}:
      {==}
    case Bk.Term.Enu{+x0}:
      {==}
    case Bk.Term.Lab{+x0}:
      {==}
    case Bk.Term.Mat{+x0, +x1, +x2}:
      {==}
    case Bk.Term.Efq{}:
      {==}
    case Bk.Term.Eql{+x0, +x1, +x2}:
      {==}
    case Bk.Term.Rfl{}:
      {==}
    case Bk.Term.Rwt{+x0, +x1, +x2}:
      D.bool.ft({Bool.or(Bool.not(True{}), El.Eval.vals(ds, Bk.Term.Rwt{x0, x1, x2}, False{})) == True{} : Bool}, hf)

def or1r(b: Bool) -> {U32.is_zero(U32.or(Bool.to_u32(b), 1)) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the test of M.ev on a value by its form is not 0
def nzf.of(-m: Cr.Cir.Cells, -im: U32, -fi: U32, -nx: U32, +f0: U32, +focus: Bk.Term, etag: {D.TgW(f0) == D.A.tag(focus) : U32},
  tb: D.Tbl(m, im, fi, nx), hf: {A.tbl(focus) == True{} : Bool}) ->
  {U32.is_zero(U32.or(Bool.to_u32(U32.is_ne(U32.and(f0, 256), 0)),
    Bool.to_u32(U32.is_ne(Cr.Cir.Cell.get(4n, Cr.Cir.Cells.get(m, U32.add(272, U32.and(f0, 63)))), 0)))) == False{} : Bool}:
  %Equal.sym(U32, D.TgW(f0), D.A.tag(focus), etag) :
    {U32.is_zero(U32.or(Bool.to_u32(U32.is_ne(U32.and(f0, 256), 0)),
      Bool.to_u32(U32.is_ne(Cr.Cir.Cell.get(4n, Cr.Cir.Cells.get(m, U32.add(272, _))), 0)))) == False{} : Bool}
  %Equal.sym(U32, D.Fd(4n, m, U32.add(272, D.A.tag(focus))), A.f4(focus), tbl.f4(m, im, fi, nx, focus, tb)) :
    {U32.is_zero(U32.or(Bool.to_u32(U32.is_ne(U32.and(f0, 256), 0)), Bool.to_u32(U32.is_ne(_, 0)))) == False{} : Bool}
  %Equal.sym(U32, A.f4(focus), 1, f4.one(focus, hf)) :
    {U32.is_zero(U32.or(Bool.to_u32(U32.is_ne(U32.and(f0, 256), 0)), Bool.to_u32(U32.is_ne(_, 0)))) == False{} : Bool}
  or1r(U32.is_ne(U32.and(f0, 256), 0))

# the test of M.ev on a value by its form, from the facts of its cell
def nzf.go(-ds: List<&2, Bk.Def>, -im: U32, -fi: U32, -nx: U32, +foc: U32, +m: Cr.Cir.Cells, +focus: Bk.Term,
  nd: D.Nd(ds, im, fi, nx, foc, Cr.Cir.Cells.get(m, foc), focus, D.A.tag(focus)), tb: D.Tbl(m, im, fi, nx),
  hf: {A.tbl(focus) == True{} : Bool}) ->
  {U32.is_zero(U32.or(Bool.to_u32(U32.is_ne(U32.and(D.Fd(0n, m, foc), 256), 0)), Bool.to_u32(U32.is_ne(Cr.Cir.Cell.get(4n, Cr.Cir.Cells.get(m, U32.add(272, U32.and(D.Fd(0n, m, foc), 63)))), 0)))) == False{} : Bool}:
  match nd:
    case Tuple{_, Tuple{_, Tuple{etag, _}}}:
      nzf.of(m, im, fi, nx, D.Fd(0n, m, foc), focus, etag, tb, hf)

# M.ev, past its first statement, and past its second
def B.cond2() -> Cr.Cir.Expr:
  Mc.M.or(Mc.M.flag(Mc.M.g(Mc.R.c()), Mc.F.value()), Mc.M.ne(Mc.M.entry(4n, Mc.M.g(Mc.R.c())), Mc.M.c(0)))

# a halt
def eq.halt(+f: Nat, +x: U32, +st: Cr.Cir.State) -> {Cr.Cir.exec(f, Cr.Cir.Stmt.halt{x}, st) == Cr.Cir.Out.halt{x, st} : Cr.Cir.Out}:
  match f:
    case 0n:
      {==}
    case 1n+g:
      {==}

# a then b, when a halts
def eq.seq.h(+f: Nat, a: Cr.Cir.Stmt, +b: Cr.Cir.Stmt, +st: Cr.Cir.State, +x: U32, +st1: Cr.Cir.State,
  e1: {Cr.Cir.exec(f, a, st) == Cr.Cir.Out.halt{x, st1} : Cr.Cir.Out}) ->
  {Cr.Cir.exec(f, Cr.Cir.Stmt.seq{a, b}, st) == Cr.Cir.Out.halt{x, st1} : Cr.Cir.Out}:
  match f:
    case 0n:
      %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(0n, a, st), Cr.Cir.Out.halt{x, st1}, e1) :
        {Cr.Cir.exec.then(_, u => Cr.Cir.exec(0n, b, u)) == Cr.Cir.Out.halt{x, st1} : Cr.Cir.Out}
      {==}
    case 1n+g:
      %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(1n+g, a, st), Cr.Cir.Out.halt{x, st1}, e1) :
        {Cr.Cir.exec.then(_, u => Cr.Cir.exec(1n+g, b, u)) == Cr.Cir.Out.halt{x, st1} : Cr.Cir.Out}
      {==}

# a test of the tag of a cell whose tag is another
def tag.ne(+f0: U32, +tag: U32, +x: U32, etag: {D.TgW(f0) == tag : U32}, e: {U32.is_eq(tag, x) == False{} : Bool}) ->
  {U32.is_zero(Wa.Wasm.op(Wa.Wasm.Op.eq{}, D.TgW(f0), x)) == True{} : Bool}:
  %Equal.sym(U32, D.TgW(f0), tag, etag) : {U32.is_zero(Wa.Wasm.op(Wa.Wasm.Op.eq{}, _, x)) == True{} : Bool}
  %Equal.sym(Bool, U32.is_eq(tag, x), False{}, e) : {U32.is_zero(Bool.to_u32(_)) == True{} : Bool}
  {==}

# the test of M.ev on a cell not flagged VALUE, whose tag's table field 4 is 0, is 0
def z.of(-m: Cr.Cir.Cells, -im: U32, -fi: U32, -nx: U32, +f0: U32, +focus: Bk.Term, etag: {D.TgW(f0) == D.A.tag(focus) : U32},
  tb: D.Tbl(m, im, fi, nx), hv: {U32.is_ne(U32.and(f0, 256), 0) == False{} : Bool}, h0: {A.f4(focus) == 0 : U32}) ->
  {U32.is_zero(U32.or(Bool.to_u32(U32.is_ne(U32.and(f0, 256), 0)),
    Bool.to_u32(U32.is_ne(Cr.Cir.Cell.get(4n, Cr.Cir.Cells.get(m, U32.add(272, U32.and(f0, 63)))), 0)))) == True{} : Bool}:
  %Equal.sym(U32, D.TgW(f0), D.A.tag(focus), etag) :
    {U32.is_zero(U32.or(Bool.to_u32(U32.is_ne(U32.and(f0, 256), 0)),
      Bool.to_u32(U32.is_ne(Cr.Cir.Cell.get(4n, Cr.Cir.Cells.get(m, U32.add(272, _))), 0)))) == True{} : Bool}
  %Equal.sym(U32, D.Fd(4n, m, U32.add(272, D.A.tag(focus))), A.f4(focus), tbl.f4(m, im, fi, nx, focus, tb)) :
    {U32.is_zero(U32.or(Bool.to_u32(U32.is_ne(U32.and(f0, 256), 0)), Bool.to_u32(U32.is_ne(_, 0)))) == True{} : Bool}
  %Equal.sym(U32, A.f4(focus), 0, h0) :
    {U32.is_zero(U32.or(Bool.to_u32(U32.is_ne(U32.and(f0, 256), 0)), Bool.to_u32(U32.is_ne(_, 0)))) == True{} : Bool}
  %Equal.sym(Bool, U32.is_ne(U32.and(f0, 256), 0), False{}, hv) :
    {U32.is_zero(U32.or(Bool.to_u32(_), Bool.to_u32(U32.is_ne(0, 0)))) == True{} : Bool}
  {==}

# Eval: a focus with no step that is no value makes its frames' term so
def ev.stuck(+ds: List<&2, Bk.Def>, fs: List<&2, D.AF>, +u: Bk.Term, hfs: D.AFs.ok(ds, fs),
  hs: {El.Eval.step(ds, u) == None{} : Maybe<Bk.Term>}, hv: {El.Eval.vals(ds, u, False{}) == False{} : Bool}) ->
  D.P2({El.Eval.step(ds, D.A.plugs(fs, u)) == None{} : Maybe<Bk.Term>}, {El.Eval.vals(ds, D.A.plugs(fs, u), False{}) == False{} : Bool}):
  EV.ev.stuck(ds, fs, u, hfs, hs, hv)

# a halt of a round, from a term equal to t
def hr.eq(+ds: List<&2, Bk.Def>, -u: Bk.Term, -t: Bk.Term, -s: U32, -st: Cr.Cir.State, e: {u == t : Bk.Term},
  h: D.HR(ds, u, s, st)) -> D.HR(ds, t, s, st):
  %e : D.HR(ds, _, s, st)
  h

# a halt with 2 from a term that is stuck
def hr.stuck(+ds: List<&2, Bk.Def>, +t: Bk.Term, -st: Cr.Cir.State,
  h: D.P2({El.Eval.step(ds, t) == None{} : Maybe<Bk.Term>}, {El.Eval.vals(ds, t, False{}) == False{} : Bool})) -> D.HR(ds, t, 2, st):
  match h:
    case Tuple{es, ev}:
      Inr{({==}, (es, D.res.nv(ds, t, ev)))}

# M.ev's tests of the tag, from the last
def B.e6() -> Cr.Cir.Stmt:
  Mc.M.if(Mc.M.eq(Mc.M.g(Mc.R.tag()), Mc.M.c(Mc.T.min())), Mc.M.ev.min(), Mc.M.halt(2))

def B.e5() -> Cr.Cir.Stmt:
  Mc.M.if(Mc.M.eq(Mc.M.g(Mc.R.tag()), Mc.M.c(Mc.T.rwt())), Mc.M.ev.rwt(), B.e6())

def B.e4() -> Cr.Cir.Stmt:
  Mc.M.if(Mc.M.eq(Mc.M.g(Mc.R.tag()), Mc.M.c(Mc.T.tup())), Mc.M.ev.tup(), B.e5())

def B.e3() -> Cr.Cir.Stmt:
  Mc.M.if(Mc.M.eq(Mc.M.g(Mc.R.tag()), Mc.M.c(Mc.T.let())), Mc.M.ev.let(), B.e4())

def B.e2() -> Cr.Cir.Stmt:
  Mc.M.if(Mc.M.eq(Mc.M.g(Mc.R.tag()), Mc.M.c(Mc.T.ann())), Mc.M.ev.ann(), B.e3())

def B.e1() -> Cr.Cir.Stmt:
  Mc.M.if(Mc.M.eq(Mc.M.g(Mc.R.tag()), Mc.M.c(Mc.T.ref())), Mc.M.ev.ref(), B.e2())

def B.else() -> Cr.Cir.Stmt:
  Mc.M.if(Mc.M.eq(Mc.M.g(Mc.R.tag()), Mc.M.c(Mc.T.app())), Mc.M.ev.app(), B.e1())

def B.ev2() -> Cr.Cir.Stmt:
  Mc.M.do([Mc.M.set(Mc.R.tag(), Mc.M.tag(Mc.M.g(Mc.R.c()))), Mc.M.if(B.cond2(), Mc.M.set(Mc.R.mode(), Mc.M.c(1)), B.else())])

def B.ev3() -> Cr.Cir.Stmt:
  Mc.M.do([Mc.M.if(B.cond2(), Mc.M.set(Mc.R.mode(), Mc.M.c(1)), B.else())])

# M.ev's first two statements, from a state of mode 0: c and tag get the
# focus' cell and its tag
def ev.st1(+foc: U32, +sp: U32, +pend: U32, +r4: U32, +r5: U32, +r6: U32, +r7: U32, +r8: U32, +r9: U32, +r10: U32, +r11: U32, +r12: U32, +r13: U32, +r14: U32, +r15: U32, +r16: U32, +r17: U32, +r18: U32, +r19: U32, +r20: U32, +r21: U32, +r22: U32, +r23: U32, +r24: U32, +r25: U32, +r26: U32, +r27: U32, +r28: U32, +r29: U32, +r30: U32, +r31: U32, +r32: U32, +r33: U32, +r34: U32, +r35: U32, +r36: U32, +r37: U32, +r38: U32, +r39: U32, +r40: U32, +r41: U32, +r42: U32, +r43: U32, +r44: U32, +r45: U32, +r46: U32, +r47: U32, +r48: U32, +r49: U32, +r50: U32, +r51: U32, +r52: U32, +r53: U32, +r54: U32, +r55: U32, +r56: U32, +r57: U32, +r58: U32, +r59: U32, +r60: U32, +r61: U32, +r62: U32, +m: Cr.Cir.Cells, +nx: U32, +fi: U32,
  +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>) -> Cr.Cir.State:
  D.St.set(D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), 8n, foc)

def ev.st2(+foc: U32, +sp: U32, +pend: U32, +r4: U32, +r5: U32, +r6: U32, +r7: U32, +r8: U32, +r9: U32, +r10: U32, +r11: U32, +r12: U32, +r13: U32, +r14: U32, +r15: U32, +r16: U32, +r17: U32, +r18: U32, +r19: U32, +r20: U32, +r21: U32, +r22: U32, +r23: U32, +r24: U32, +r25: U32, +r26: U32, +r27: U32, +r28: U32, +r29: U32, +r30: U32, +r31: U32, +r32: U32, +r33: U32, +r34: U32, +r35: U32, +r36: U32, +r37: U32, +r38: U32, +r39: U32, +r40: U32, +r41: U32, +r42: U32, +r43: U32, +r44: U32, +r45: U32, +r46: U32, +r47: U32, +r48: U32, +r49: U32, +r50: U32, +r51: U32, +r52: U32, +r53: U32, +r54: U32, +r55: U32, +r56: U32, +r57: U32, +r58: U32, +r59: U32, +r60: U32, +r61: U32, +r62: U32, +m: Cr.Cir.Cells, +nx: U32, +fi: U32,
  +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>) -> Cr.Cir.State:
  D.St.set(ev.st1(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp), 10n, D.TgW(D.Fd(0n, m, foc)))

# a round from mode 0 whose focus' cell c is flagged VALUE: c and tag are
# set, then the mode is 1
def ev.val.E(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32,
  +pend: U32, +r4: U32, +r5: U32, +r6: U32, +r7: U32, +r8: U32, +r9: U32, +r10: U32, +r11: U32, +r12: U32, +r13: U32, +r14: U32, +r15: U32, +r16: U32, +r17: U32, +r18: U32, +r19: U32, +r20: U32, +r21: U32, +r22: U32, +r23: U32, +r24: U32, +r25: U32, +r26: U32, +r27: U32, +r28: U32, +r29: U32, +r30: U32, +r31: U32, +r32: U32, +r33: U32, +r34: U32, +r35: U32, +r36: U32, +r37: U32, +r38: U32, +r39: U32, +r40: U32, +r41: U32, +r42: U32, +r43: U32, +r44: U32, +r45: U32, +r46: U32, +r47: U32, +r48: U32, +r49: U32, +r50: U32, +r51: U32, +r52: U32, +r53: U32, +r54: U32, +r55: U32, +r56: U32, +r57: U32, +r58: U32, +r59: U32, +r60: U32, +r61: U32, +r62: U32, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32,
  +inp: List<&2, Word(8n)>, +focus: Bk.Term,
  +nd: D.Nd(ds, im, fi, nx, foc, Cr.Cir.Cells.get(m, foc), focus, D.A.tag(focus)),
  +tb: D.Tbl(m, im, fi, nx), +nz2: {U32.is_zero(U32.or(Bool.to_u32(U32.is_ne(U32.and(D.Fd(0n, m, foc), 256), 0)), Bool.to_u32(U32.is_ne(Cr.Cir.Cell.get(4n, Cr.Cir.Cells.get(m, U32.add(272, U32.and(D.Fd(0n, m, foc), 63)))), 0)))) == False{} : Bool}) ->
  {Cr.Cir.exec(f, D.B.body(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)) ==
    Cr.Cir.Out.next{D.St.set(ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp), 1n, 1)} : Cr.Cir.Out}:
  match nd:
    case Tuple{+valid, Tuple{_, Tuple{+etag, _}}}:
      +st1 = ev.st1(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)
      +st2 = ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)
      +st3 = D.St.set(st2, 1n, 1)
      +f0 = D.Fd(0n, m, foc)
      +ef1 = D.ev.fld(0n, Mc.M.g(Mc.R.c()), D.St.regs(st1), m, nx, fi, im, pg, lim, inp, Nil{}, 0, foc, {==}, valid)
      +ef2 = D.ev.fld(0n, Mc.M.g(Mc.R.c()), D.St.regs(st2), m, nx, fi, im, pg, lim, inp, Nil{}, 0, foc, {==}, valid)
      +etg = D.ev.op(Wa.Wasm.Op.and{}, Mc.M.f(0n, Mc.M.g(Mc.R.c())), Mc.M.c(63), st1, f0, 63, ef1, {==})
      +etg2 = D.ev.op(Wa.Wasm.Op.and{}, Mc.M.f(0n, Mc.M.g(Mc.R.c())), Mc.M.c(63), st2, f0, 63, ef2, {==})
      +efl = D.ev.op(Wa.Wasm.Op.ne{}, Mc.M.and(Mc.M.f(0n, Mc.M.g(Mc.R.c())), Mc.M.c(256)), Mc.M.c(0), st2, Wa.Wasm.op(Wa.Wasm.Op.and{}, f0, 256), 0,
        D.ev.op(Wa.Wasm.Op.and{}, Mc.M.f(0n, Mc.M.g(Mc.R.c())), Mc.M.c(256), st2, f0, 256, ef2, {==}), {==})
      +addr = Wa.Wasm.op(Wa.Wasm.Op.add{}, 272, Wa.Wasm.op(Wa.Wasm.Op.and{}, f0, 63))
      +eadr = D.ev.op(Wa.Wasm.Op.add{}, Mc.M.c(272), Mc.M.tag(Mc.M.g(Mc.R.c())), st2, 272, Wa.Wasm.op(Wa.Wasm.Op.and{}, f0, 63), {==}, etg2)
      +vt = vt.of(m, im, fi, nx, f0, focus, etag, tb)
      +e4 = Cr.Cir.Cell.get(4n, Cr.Cir.Cells.get(m, addr))
      +ee4 = D.ev.fld(4n, Mc.M.add(Mc.M.c(272), Mc.M.tag(Mc.M.g(Mc.R.c()))), D.St.regs(st2), m, nx, fi, im, pg, lim, inp, Nil{}, 0, addr, eadr, vt)
      +ene = D.ev.op(Wa.Wasm.Op.ne{}, Mc.M.entry(4n, Mc.M.g(Mc.R.c())), Mc.M.c(0), st2, e4, 0, ee4, {==})
      +flv = Wa.Wasm.op(Wa.Wasm.Op.ne{}, Wa.Wasm.op(Wa.Wasm.Op.and{}, f0, 256), 0)
      +nev = Wa.Wasm.op(Wa.Wasm.Op.ne{}, e4, 0)
      +ec2 = D.ev.op(Wa.Wasm.Op.or{}, Mc.M.flag(Mc.M.g(Mc.R.c()), Mc.F.value()), Mc.M.ne(Mc.M.entry(4n, Mc.M.g(Mc.R.c())), Mc.M.c(0)), st2, flv, nev, efl, ene)
      +e3a = Equal.trans(Cr.Cir.Out, Cr.Cir.exec(f, Cr.Cir.Stmt.if{B.cond2(), Mc.M.set(Mc.R.mode(), Mc.M.c(1)), B.else()}, st2),
        Cr.Cir.exec(f, Mc.M.set(Mc.R.mode(), Mc.M.c(1)), st2), Cr.Cir.Out.next{st3},
        D.eq.if.t(f, B.cond2(), Mc.M.set(Mc.R.mode(), Mc.M.c(1)), B.else(), st2, Wa.Wasm.op(Wa.Wasm.Op.or{}, flv, nev), ec2, nz2),
        D.eq.set(f, 1n, Mc.M.c(1), st2, 1, {==}, {==}))
      %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, D.B.body(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(f, Mc.M.ev(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)),
        D.eq.if.t(f, Mc.M.eq(Mc.M.g(Mc.R.mode()), Mc.M.c(0)), Mc.M.ev(), Mc.M.ret(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), 1, {==}, {==})) :
        {_ == Cr.Cir.Out.next{st3} : Cr.Cir.Out}
      %D.rw.seq(f, Mc.M.set(Mc.R.c(), Mc.M.g(Mc.R.focus())), B.ev2(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), st1,
        D.eq.set(f, 8n, Mc.M.g(Mc.R.focus()), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), foc, {==}, {==})) : {_ == Cr.Cir.Out.next{st3} : Cr.Cir.Out}
      %D.rw.seq(f, Mc.M.set(Mc.R.tag(), Mc.M.tag(Mc.M.g(Mc.R.c()))), B.ev3(), st1, st2,
        D.eq.set(f, 10n, Mc.M.tag(Mc.M.g(Mc.R.c())), st1, D.TgW(f0), etg, {==})) : {_ == Cr.Cir.Out.next{st3} : Cr.Cir.Out}
      %D.rw.seq(f, Cr.Cir.Stmt.if{B.cond2(), Mc.M.set(Mc.R.mode(), Mc.M.c(1)), B.else()}, Cr.Cir.Stmt.nop{}, st2, st3, e3a) :
        {_ == Cr.Cir.Out.next{st3} : Cr.Cir.Out}
      %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, Cr.Cir.Stmt.nop{}, st3), Cr.Cir.Out.next{st3}, D.eq.nop(f, st3)) :
        {_ == Cr.Cir.Out.next{st3} : Cr.Cir.Out}
      {==}

# the table of the image
def img.tbl(-ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -m: Cr.Cir.Cells, -im: U32,
  -fi: U32, -nx: U32, io: D.ImgOK(ds, ks, img, m, im, fi, nx)) -> D.Tbl(m, im, fi, nx):
  match io:
    case Tuple{tb, _}:
      tb

# a cell flagged VALUE stands for a value
def nd.val(-ds: List<&2, Bk.Def>, -im: U32, -fi: U32, -nx: U32, -c: U32, -x: Cr.Cir.Cell, -t: Bk.Term, -tag: U32,
  nd: D.Nd(ds, im, fi, nx, c, x, t, tag), hv: {D.FlW(Cr.Cir.Cell.get(0n, x), 256) == True{} : Bool}) ->
  {Bool.or(Bool.not(True{}), El.Eval.vals(ds, t, False{})) == True{} : Bool}:
  match nd:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{nv, _}}}}:
      %hv : {Bool.or(Bool.not(_), El.Eval.vals(ds, t, False{})) == True{} : Bool}
      nv

# mode 1 costs less than mode 0 by the focus' measure
def ret.lt(+focus: Bk.Term, +fs: List<&2, D.AF>, -w: Nat, ew: {D.A.w(False{}, focus, fs) == w : Nat}) ->
  N.Le(1n+D.A.w(True{}, focus, fs), w):
  %ew : N.Le(1n+D.A.w(True{}, focus, fs), _)
  N.add_mono(1n, D.A.w3(focus), D.A.w.frames(fs), D.A.w.frames(fs), D.A.w3.pos(focus), N.le_refl(D.A.w.frames(fs)))

# the tests of M.ev on a cell of the tag 0: none takes it, a halt with 2
def B.chain0(+f: Nat, +st: Cr.Cir.State, +f0: U32,
  +etag: {D.TgW(f0) == 0 : U32}, +er: {Cr.Cir.eval(Mc.M.g(Mc.R.tag()), st) == Some{D.TgW(f0)} : Maybe<&2, U32>}) ->
  {Cr.Cir.exec(f, B.else(), st) == Cr.Cir.Out.halt{2, st} : Cr.Cir.Out}:
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, B.else(), st), Cr.Cir.exec(f, B.e1(), st),
    D.eq.if.e(f, Mc.M.eq(Mc.M.g(Mc.R.tag()), Mc.M.c(8)), Mc.M.ev.app(), B.e1(), st, Wa.Wasm.op(Wa.Wasm.Op.eq{}, D.TgW(f0), 8),
      D.ev.op(Wa.Wasm.Op.eq{}, Mc.M.g(Mc.R.tag()), Mc.M.c(8), st, D.TgW(f0), 8, er, {==}), tag.ne(f0, 0, 8, etag, {==}))) :
    {_ == Cr.Cir.Out.halt{2, st} : Cr.Cir.Out}
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, B.e1(), st), Cr.Cir.exec(f, B.e2(), st),
    D.eq.if.e(f, Mc.M.eq(Mc.M.g(Mc.R.tag()), Mc.M.c(1)), Mc.M.ev.ref(), B.e2(), st, Wa.Wasm.op(Wa.Wasm.Op.eq{}, D.TgW(f0), 1),
      D.ev.op(Wa.Wasm.Op.eq{}, Mc.M.g(Mc.R.tag()), Mc.M.c(1), st, D.TgW(f0), 1, er, {==}), tag.ne(f0, 0, 1, etag, {==}))) :
    {_ == Cr.Cir.Out.halt{2, st} : Cr.Cir.Out}
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, B.e2(), st), Cr.Cir.exec(f, B.e3(), st),
    D.eq.if.e(f, Mc.M.eq(Mc.M.g(Mc.R.tag()), Mc.M.c(2)), Mc.M.ev.ann(), B.e3(), st, Wa.Wasm.op(Wa.Wasm.Op.eq{}, D.TgW(f0), 2),
      D.ev.op(Wa.Wasm.Op.eq{}, Mc.M.g(Mc.R.tag()), Mc.M.c(2), st, D.TgW(f0), 2, er, {==}), tag.ne(f0, 0, 2, etag, {==}))) :
    {_ == Cr.Cir.Out.halt{2, st} : Cr.Cir.Out}
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, B.e3(), st), Cr.Cir.exec(f, B.e4(), st),
    D.eq.if.e(f, Mc.M.eq(Mc.M.g(Mc.R.tag()), Mc.M.c(3)), Mc.M.ev.let(), B.e4(), st, Wa.Wasm.op(Wa.Wasm.Op.eq{}, D.TgW(f0), 3),
      D.ev.op(Wa.Wasm.Op.eq{}, Mc.M.g(Mc.R.tag()), Mc.M.c(3), st, D.TgW(f0), 3, er, {==}), tag.ne(f0, 0, 3, etag, {==}))) :
    {_ == Cr.Cir.Out.halt{2, st} : Cr.Cir.Out}
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, B.e4(), st), Cr.Cir.exec(f, B.e5(), st),
    D.eq.if.e(f, Mc.M.eq(Mc.M.g(Mc.R.tag()), Mc.M.c(10)), Mc.M.ev.tup(), B.e5(), st, Wa.Wasm.op(Wa.Wasm.Op.eq{}, D.TgW(f0), 10),
      D.ev.op(Wa.Wasm.Op.eq{}, Mc.M.g(Mc.R.tag()), Mc.M.c(10), st, D.TgW(f0), 10, er, {==}), tag.ne(f0, 0, 10, etag, {==}))) :
    {_ == Cr.Cir.Out.halt{2, st} : Cr.Cir.Out}
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, B.e5(), st), Cr.Cir.exec(f, B.e6(), st),
    D.eq.if.e(f, Mc.M.eq(Mc.M.g(Mc.R.tag()), Mc.M.c(18)), Mc.M.ev.rwt(), B.e6(), st, Wa.Wasm.op(Wa.Wasm.Op.eq{}, D.TgW(f0), 18),
      D.ev.op(Wa.Wasm.Op.eq{}, Mc.M.g(Mc.R.tag()), Mc.M.c(18), st, D.TgW(f0), 18, er, {==}), tag.ne(f0, 0, 18, etag, {==}))) :
    {_ == Cr.Cir.Out.halt{2, st} : Cr.Cir.Out}
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, B.e6(), st), Cr.Cir.exec(f, Mc.M.halt(2), st),
    D.eq.if.e(f, Mc.M.eq(Mc.M.g(Mc.R.tag()), Mc.M.c(5)), Mc.M.ev.min(), Mc.M.halt(2), st, Wa.Wasm.op(Wa.Wasm.Op.eq{}, D.TgW(f0), 5),
      D.ev.op(Wa.Wasm.Op.eq{}, Mc.M.g(Mc.R.tag()), Mc.M.c(5), st, D.TgW(f0), 5, er, {==}), tag.ne(f0, 0, 5, etag, {==}))) :
    {_ == Cr.Cir.Out.halt{2, st} : Cr.Cir.Out}
  eq.halt(f, 2, st)

# a round from mode 0 whose focus' cell is a variable: no case of M.ev takes
# it, a halt with 2
def ev.var.E(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32,
  +pend: U32, +r4: U32, +r5: U32, +r6: U32, +r7: U32, +r8: U32, +r9: U32, +r10: U32, +r11: U32, +r12: U32, +r13: U32, +r14: U32, +r15: U32, +r16: U32, +r17: U32, +r18: U32, +r19: U32, +r20: U32, +r21: U32, +r22: U32, +r23: U32, +r24: U32, +r25: U32, +r26: U32, +r27: U32, +r28: U32, +r29: U32, +r30: U32, +r31: U32, +r32: U32, +r33: U32, +r34: U32, +r35: U32, +r36: U32, +r37: U32, +r38: U32, +r39: U32, +r40: U32, +r41: U32, +r42: U32, +r43: U32, +r44: U32, +r45: U32, +r46: U32, +r47: U32, +r48: U32, +r49: U32, +r50: U32, +r51: U32, +r52: U32, +r53: U32, +r54: U32, +r55: U32, +r56: U32, +r57: U32, +r58: U32, +r59: U32, +r60: U32, +r61: U32, +r62: U32, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32,
  +inp: List<&2, Word(8n)>, +i: Nat,
  +nd: D.Nd(ds, im, fi, nx, foc, Cr.Cir.Cells.get(m, foc), Bk.Term.Var{i}, 0),
  +tb: D.Tbl(m, im, fi, nx), +hv: {D.Fl(m, foc, 256) == False{} : Bool}) ->
  {Cr.Cir.exec(f, D.B.body(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)) == Cr.Cir.Out.halt{2, ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)} : Cr.Cir.Out}:
  match nd:
    case Tuple{+valid, Tuple{_, Tuple{+etag, _}}}:
      +st1 = ev.st1(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)
      +st2 = ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)
      +f0 = D.Fd(0n, m, foc)
      +ef1 = D.ev.fld(0n, Mc.M.g(Mc.R.c()), D.St.regs(st1), m, nx, fi, im, pg, lim, inp, Nil{}, 0, foc, {==}, valid)
      +ef2 = D.ev.fld(0n, Mc.M.g(Mc.R.c()), D.St.regs(st2), m, nx, fi, im, pg, lim, inp, Nil{}, 0, foc, {==}, valid)
      +etg = D.ev.op(Wa.Wasm.Op.and{}, Mc.M.f(0n, Mc.M.g(Mc.R.c())), Mc.M.c(63), st1, f0, 63, ef1, {==})
      +etg2 = D.ev.op(Wa.Wasm.Op.and{}, Mc.M.f(0n, Mc.M.g(Mc.R.c())), Mc.M.c(63), st2, f0, 63, ef2, {==})
      +efl = D.ev.op(Wa.Wasm.Op.ne{}, Mc.M.and(Mc.M.f(0n, Mc.M.g(Mc.R.c())), Mc.M.c(256)), Mc.M.c(0), st2, Wa.Wasm.op(Wa.Wasm.Op.and{}, f0, 256), 0,
        D.ev.op(Wa.Wasm.Op.and{}, Mc.M.f(0n, Mc.M.g(Mc.R.c())), Mc.M.c(256), st2, f0, 256, ef2, {==}), {==})
      +addr = Wa.Wasm.op(Wa.Wasm.Op.add{}, 272, Wa.Wasm.op(Wa.Wasm.Op.and{}, f0, 63))
      +eadr = D.ev.op(Wa.Wasm.Op.add{}, Mc.M.c(272), Mc.M.tag(Mc.M.g(Mc.R.c())), st2, 272, Wa.Wasm.op(Wa.Wasm.Op.and{}, f0, 63), {==}, etg2)
      +vt = vt.of(m, im, fi, nx, f0, Bk.Term.Var{i}, etag, tb)
      +e4 = Cr.Cir.Cell.get(4n, Cr.Cir.Cells.get(m, addr))
      +ee4 = D.ev.fld(4n, Mc.M.add(Mc.M.c(272), Mc.M.tag(Mc.M.g(Mc.R.c()))), D.St.regs(st2), m, nx, fi, im, pg, lim, inp, Nil{}, 0, addr, eadr, vt)
      +ene = D.ev.op(Wa.Wasm.Op.ne{}, Mc.M.entry(4n, Mc.M.g(Mc.R.c())), Mc.M.c(0), st2, e4, 0, ee4, {==})
      +flv = Wa.Wasm.op(Wa.Wasm.Op.ne{}, Wa.Wasm.op(Wa.Wasm.Op.and{}, f0, 256), 0)
      +nev = Wa.Wasm.op(Wa.Wasm.Op.ne{}, e4, 0)
      +ec2 = D.ev.op(Wa.Wasm.Op.or{}, Mc.M.flag(Mc.M.g(Mc.R.c()), Mc.F.value()), Mc.M.ne(Mc.M.entry(4n, Mc.M.g(Mc.R.c())), Mc.M.c(0)), st2, flv, nev, efl, ene)
      +z2 = z.of(m, im, fi, nx, f0, Bk.Term.Var{i}, etag, tb, hv, {==})
      +e3a = Equal.trans(Cr.Cir.Out, Cr.Cir.exec(f, Cr.Cir.Stmt.if{B.cond2(), Mc.M.set(Mc.R.mode(), Mc.M.c(1)), B.else()}, st2),
        Cr.Cir.exec(f, B.else(), st2), Cr.Cir.Out.halt{2, st2},
        D.eq.if.e(f, B.cond2(), Mc.M.set(Mc.R.mode(), Mc.M.c(1)), B.else(), st2, Wa.Wasm.op(Wa.Wasm.Op.or{}, flv, nev), ec2, z2),
        B.chain0(f, st2, f0, etag, {==}))
      %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, D.B.body(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(f, Mc.M.ev(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)),
        D.eq.if.t(f, Mc.M.eq(Mc.M.g(Mc.R.mode()), Mc.M.c(0)), Mc.M.ev(), Mc.M.ret(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), 1, {==}, {==})) :
        {_ == Cr.Cir.Out.halt{2, st2} : Cr.Cir.Out}
      %D.rw.seq(f, Mc.M.set(Mc.R.c(), Mc.M.g(Mc.R.focus())), B.ev2(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), st1,
        D.eq.set(f, 8n, Mc.M.g(Mc.R.focus()), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), foc, {==}, {==})) : {_ == Cr.Cir.Out.halt{2, st2} : Cr.Cir.Out}
      %D.rw.seq(f, Mc.M.set(Mc.R.tag(), Mc.M.tag(Mc.M.g(Mc.R.c()))), B.ev3(), st1, st2,
        D.eq.set(f, 10n, Mc.M.tag(Mc.M.g(Mc.R.c())), st1, D.TgW(f0), etg, {==})) : {_ == Cr.Cir.Out.halt{2, st2} : Cr.Cir.Out}
      eq.seq.h(f, Cr.Cir.Stmt.if{B.cond2(), Mc.M.set(Mc.R.mode(), Mc.M.c(1)), B.else()}, Cr.Cir.Stmt.nop{}, st2, 2, st2, e3a)

# the parts of an if, to name the parts of a statement of impl.bend without
# copying them
def stmt.cond(x: Cr.Cir.Stmt) -> Cr.Cir.Expr:
  match x:
    case Cr.Cir.Stmt.if{c, _, _}:
      c
    case _:
      Cr.Cir.Expr.const{0}

def stmt.then(x: Cr.Cir.Stmt) -> Cr.Cir.Stmt:
  match x:
    case Cr.Cir.Stmt.if{_, t, _}:
      t
    case _:
      Cr.Cir.Stmt.nop{}

def stmt.else(x: Cr.Cir.Stmt) -> Cr.Cir.Stmt:
  match x:
    case Cr.Cir.Stmt.if{_, _, e}:
      e
    case _:
      Cr.Cir.Stmt.nop{}

# a weaker outcome
def post.map(dn: Bool, o: Cr.Cir.Out, -Q1: Cr.Cir.State -> Type, -Q2: Cr.Cir.State -> Type, -H1: U32 -> Cr.Cir.State -> Type,
  -H2: U32 -> Cr.Cir.State -> Type, h: D.Post(dn, o, Q1, H1), q: @st: Cr.Cir.State -> Q1(st) -> Q2(st),
  hh: @s: U32 -> @st: Cr.Cir.State -> H1(s, st) -> H2(s, st)) -> D.Post(dn, o, Q2, H2):
  match o:
    case Cr.Cir.Out.next{st}:
      q(st, h)
    case Cr.Cir.Out.halt{s, st}:
      hh(s, st, h)
    case Cr.Cir.Out.out_of_memory{}:
      Unit{}
    case Cr.Cir.Out.trap{}:
      h
    case Cr.Cir.Out.not_done{}:
      h

# the result of a value is its bytes
def res.val(+ds: List<&2, Bk.Def>, +v: Bk.Term, -x: Maybe<&2, List<&2, Word(8n)>>, ev: {El.Eval.vals(ds, v, False{}) == True{} : Bool},
  eu: {Pg.Program.unbytes(v) == x : Maybe<&2, List<&2, Word(8n)>>}) -> {Pg.Program.result(ds, Some{v}) == x : Maybe<&2, List<&2, Word(8n)>>}:
  %Equal.sym(Bool, El.Eval.vals(ds, v, False{}), True{}, ev) : {Pg.Program.result.if(_, v) == x : Maybe<&2, List<&2, Word(8n)>>}
  eu

# M.out's halts are a round's, from its value v
def out.hr(+ds: List<&2, Bk.Def>, +v: Bk.Term, +ev: {El.Eval.vals(ds, v, False{}) == True{} : Bool}, -s: U32, -st2: Cr.Cir.State,
  h: D.OutH(v, s, st2)) -> D.HR(ds, v, s, st2):
  match h:
    case Inl{x}:
      (e0, eu) = x
      Inl{(e0, (ev.stops(ds, v, ev), res.val(ds, v, Some{List.reverse(&2, Word(8n), D.St.out(st2))}, ev, eu)))}
    case Inr{x}:
      (e2, eu) = x
      Inr{(e2, (ev.stops(ds, v, ev), res.val(ds, v, None{}, ev, eu)))}

# a round from mode 1 with no frame is M.out
def out.E(+f: Nat, +foc: U32, +pend: U32, +r4: U32, +r5: U32, +r6: U32, +r7: U32, +r8: U32, +r9: U32, +r10: U32, +r11: U32, +r12: U32, +r13: U32, +r14: U32, +r15: U32, +r16: U32, +r17: U32, +r18: U32, +r19: U32, +r20: U32, +r21: U32, +r22: U32, +r23: U32, +r24: U32, +r25: U32, +r26: U32, +r27: U32, +r28: U32, +r29: U32, +r30: U32, +r31: U32, +r32: U32, +r33: U32, +r34: U32, +r35: U32, +r36: U32, +r37: U32, +r38: U32, +r39: U32, +r40: U32, +r41: U32, +r42: U32, +r43: U32, +r44: U32, +r45: U32, +r46: U32, +r47: U32, +r48: U32, +r49: U32, +r50: U32, +r51: U32, +r52: U32, +r53: U32, +r54: U32, +r55: U32, +r56: U32, +r57: U32, +r58: U32, +r59: U32, +r60: U32, +r61: U32, +r62: U32, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32,
  +inp: List<&2, Word(8n)>) -> {Cr.Cir.exec(f, D.B.body(), D.S(foc, 1, 0, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)) == Cr.Cir.exec(f, Mc.M.out(), D.S(foc, 1, 0, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)) : Cr.Cir.Out}:
  Equal.trans(Cr.Cir.Out, Cr.Cir.exec(f, D.B.body(), D.S(foc, 1, 0, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(f, Mc.M.ret(), D.S(foc, 1, 0, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(f, Mc.M.out(), D.S(foc, 1, 0, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)),
    D.eq.if.e(f, Mc.M.eq(Mc.M.g(Mc.R.mode()), Mc.M.c(0)), Mc.M.ev(), Mc.M.ret(), D.S(foc, 1, 0, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), 0, {==}, {==}),
    D.eq.if.t(f, stmt.cond(Mc.M.ret()), stmt.then(Mc.M.ret()), stmt.else(Mc.M.ret()), D.S(foc, 1, 0, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), 1, {==}, {==}))

# the image's names, the machine's first
def img.ks(-ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -m: Cr.Cir.Cells, -im: U32,
  -fi: U32, -nx: U32, io: D.ImgOK(ds, ks, img, m, im, fi, nx)) -> D.Ex(List<&2, List<&2, Word(8n)>>, ks2 => {ks == Mc.Img.known(ks2) : List<&2, List<&2, Word(8n)>>}):
  match io:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{k, _}}}}}}:
      k

# The moves (laws), one each
# --------------------------
#
# Each is filled in its unit's file (moves_push.bend U10, swap_moves.bend U11,
# moves_copy.bend U12, moves_match.bend U13, moves_call.bend U14,
# moves_out.bend U9).

# mode 0, a focus flagged VALUE: a value, mode 1; an admin move
law mv.ev.val:
  for +ds: List<&2, Bk.Def>
  for +ks: List<&2, List<&2, Word(8n)>>
  for +img: List<&2, Bk.Term>
  for +foc: U32
  for +sp: U32
  for +pend: U32
  for +rest: D.R59
  for +m: Cr.Cir.Cells
  for +nx: U32
  for +fi: U32
  for +im: U32
  for +pg: U32
  for +lim: U32
  for +inp: List<&2, Word(8n)>
  for +t: Bk.Term
  for +w: Nat
  for +fs: List<&2, D.AF>
  for +ps: List<&2, U32>
  for +focus: Bk.Term
  for +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, False{}, focus, fs, ps)
  for +hv: {D.Fl(m, foc, 256) == True{} : Bool}
  MV(ds, ks, img, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w)

# mode 0, a focus that is a value by its form, as the table says (A.tbl): mode 1; an admin move
law mv.ev.former:
  for +ds: List<&2, Bk.Def>
  for +ks: List<&2, List<&2, Word(8n)>>
  for +img: List<&2, Bk.Term>
  for +foc: U32
  for +sp: U32
  for +pend: U32
  for +rest: D.R59
  for +m: Cr.Cir.Cells
  for +nx: U32
  for +fi: U32
  for +im: U32
  for +pg: U32
  for +lim: U32
  for +inp: List<&2, Word(8n)>
  for +t: Bk.Term
  for +w: Nat
  for +fs: List<&2, D.AF>
  for +ps: List<&2, U32>
  for +focus: Bk.Term
  for +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, False{}, focus, fs, ps)
  for +hf: {A.tbl(focus) == True{} : Bool}
  MV(ds, ks, img, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w)

# mode 0, a variable: free in the whole term, which has no step and is no value; halt 2
law mv.ev.var:
  for +ds: List<&2, Bk.Def>
  for +ks: List<&2, List<&2, Word(8n)>>
  for +img: List<&2, Bk.Term>
  for +foc: U32
  for +sp: U32
  for +pend: U32
  for +rest: D.R59
  for +m: Cr.Cir.Cells
  for +nx: U32
  for +fi: U32
  for +im: U32
  for +pg: U32
  for +lim: U32
  for +inp: List<&2, Word(8n)>
  for +t: Bk.Term
  for +w: Nat
  for +fs: List<&2, D.AF>
  for +ps: List<&2, U32>
  for +i: Nat
  for +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, False{}, Bk.Term.Var{i}, fs, ps)
  for +hv: {D.Fl(m, foc, 256) == False{} : Bool}
  MV(ds, ks, img, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w)

# mode 0, Ref k: the call of k on no arguments (M.call, with M.walk and M.copy): a step to the copy of its leaf; or, when its case tree takes an argument, mode 1, an admin move; halt 2 when no walk exists
law mv.ev.ref:
  for +ds: List<&2, Bk.Def>
  for +ks: List<&2, List<&2, Word(8n)>>
  for +img: List<&2, Bk.Term>
  for +foc: U32
  for +sp: U32
  for +pend: U32
  for +rest: D.R59
  for +m: Cr.Cir.Cells
  for +nx: U32
  for +fi: U32
  for +im: U32
  for +pg: U32
  for +lim: U32
  for +inp: List<&2, Word(8n)>
  for +t: Bk.Term
  for +w: Nat
  for +fs: List<&2, D.AF>
  for +ps: List<&2, U32>
  for +k: List<&2, Word(8n)>
  for +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, False{}, Bk.Term.Ref{k}, fs, ps)
  for +hv: {D.Fl(m, foc, 256) == False{} : Bool}
  for +hfv: {D.Term.below(t, U32.to_nat(2147483648)) == True{} : Bool}
  MV(ds, ks, img, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w)

# mode 0, Ann x y: x, a step
law mv.ev.ann:
  for +ds: List<&2, Bk.Def>
  for +ks: List<&2, List<&2, Word(8n)>>
  for +img: List<&2, Bk.Term>
  for +foc: U32
  for +sp: U32
  for +pend: U32
  for +rest: D.R59
  for +m: Cr.Cir.Cells
  for +nx: U32
  for +fi: U32
  for +im: U32
  for +pg: U32
  for +lim: U32
  for +inp: List<&2, Word(8n)>
  for +t: Bk.Term
  for +w: Nat
  for +fs: List<&2, D.AF>
  for +ps: List<&2, U32>
  for +x: Bk.Term
  for +y: Bk.Term
  for +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, False{}, Bk.Term.Ann{x, y}, fs, ps)
  for +hv: {D.Fl(m, foc, 256) == False{} : Bool}
  MV(ds, ks, img, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w)

# mode 0, Let q v b with q live: v in the frame Let q □ b; an admin move
law mv.ev.let:
  for +ds: List<&2, Bk.Def>
  for +ks: List<&2, List<&2, Word(8n)>>
  for +img: List<&2, Bk.Term>
  for +foc: U32
  for +sp: U32
  for +pend: U32
  for +rest: D.R59
  for +m: Cr.Cir.Cells
  for +nx: U32
  for +fi: U32
  for +im: U32
  for +pg: U32
  for +lim: U32
  for +inp: List<&2, Word(8n)>
  for +t: Bk.Term
  for +w: Nat
  for +fs: List<&2, D.AF>
  for +ps: List<&2, U32>
  for +q: Bk.Quan
  for +v: Bk.Term
  for +b: Bk.Term
  for +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, False{}, Bk.Term.Let{q, v, b}, fs, ps)
  for +hv: {D.Fl(m, foc, 256) == False{} : Bool}
  for +hq: {El.Quan.live(q) == True{} : Bool}
  MV(ds, ks, img, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w)

# mode 0, Let q v b with q dead: b with v put in (M.copy), a step
law mv.ev.unlet:
  for +ds: List<&2, Bk.Def>
  for +ks: List<&2, List<&2, Word(8n)>>
  for +img: List<&2, Bk.Term>
  for +foc: U32
  for +sp: U32
  for +pend: U32
  for +rest: D.R59
  for +m: Cr.Cir.Cells
  for +nx: U32
  for +fi: U32
  for +im: U32
  for +pg: U32
  for +lim: U32
  for +inp: List<&2, Word(8n)>
  for +t: Bk.Term
  for +w: Nat
  for +fs: List<&2, D.AF>
  for +ps: List<&2, U32>
  for +q: Bk.Quan
  for +v: Bk.Term
  for +b: Bk.Term
  for +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, False{}, Bk.Term.Let{q, v, b}, fs, ps)
  for +hv: {D.Fl(m, foc, 256) == False{} : Bool}
  for +hq: {El.Quan.live(q) == False{} : Bool}
  for +hfv: {D.Term.below(t, U32.to_nat(2147483648)) == True{} : Bool}
  MV(ds, ks, img, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w)

# mode 0, App q g x: g in the frame App q □ x; an admin move
law mv.ev.app:
  for +ds: List<&2, Bk.Def>
  for +ks: List<&2, List<&2, Word(8n)>>
  for +img: List<&2, Bk.Term>
  for +foc: U32
  for +sp: U32
  for +pend: U32
  for +rest: D.R59
  for +m: Cr.Cir.Cells
  for +nx: U32
  for +fi: U32
  for +im: U32
  for +pg: U32
  for +lim: U32
  for +inp: List<&2, Word(8n)>
  for +t: Bk.Term
  for +w: Nat
  for +fs: List<&2, D.AF>
  for +ps: List<&2, U32>
  for +q: Bk.Quan
  for +g: Bk.Term
  for +x: Bk.Term
  for +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, False{}, Bk.Term.App{q, g, x}, fs, ps)
  for +hv: {D.Fl(m, foc, 256) == False{} : Bool}
  MV(ds, ks, img, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w)

# mode 0, Tup q a b with q live, not flagged VALUE: a in the frame Tup q □ b; an admin move
law mv.ev.tup:
  for +ds: List<&2, Bk.Def>
  for +ks: List<&2, List<&2, Word(8n)>>
  for +img: List<&2, Bk.Term>
  for +foc: U32
  for +sp: U32
  for +pend: U32
  for +rest: D.R59
  for +m: Cr.Cir.Cells
  for +nx: U32
  for +fi: U32
  for +im: U32
  for +pg: U32
  for +lim: U32
  for +inp: List<&2, Word(8n)>
  for +t: Bk.Term
  for +w: Nat
  for +fs: List<&2, D.AF>
  for +ps: List<&2, U32>
  for +q: Bk.Quan
  for +a: Bk.Term
  for +b: Bk.Term
  for +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, False{}, Bk.Term.Tup{q, a, b}, fs, ps)
  for +hv: {D.Fl(m, foc, 256) == False{} : Bool}
  for +hq: {El.Quan.live(q) == True{} : Bool}
  MV(ds, ks, img, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w)

# mode 0, Tup q a b with q dead, not flagged VALUE: b in the frame Tup q a □; an admin move
law mv.ev.tup0:
  for +ds: List<&2, Bk.Def>
  for +ks: List<&2, List<&2, Word(8n)>>
  for +img: List<&2, Bk.Term>
  for +foc: U32
  for +sp: U32
  for +pend: U32
  for +rest: D.R59
  for +m: Cr.Cir.Cells
  for +nx: U32
  for +fi: U32
  for +im: U32
  for +pg: U32
  for +lim: U32
  for +inp: List<&2, Word(8n)>
  for +t: Bk.Term
  for +w: Nat
  for +fs: List<&2, D.AF>
  for +ps: List<&2, U32>
  for +q: Bk.Quan
  for +a: Bk.Term
  for +b: Bk.Term
  for +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, False{}, Bk.Term.Tup{q, a, b}, fs, ps)
  for +hv: {D.Fl(m, foc, 256) == False{} : Bool}
  for +hq: {El.Quan.live(q) == False{} : Bool}
  MV(ds, ks, img, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w)

# mode 0, Rwt e p b: e in the frame Rwt □ p b; an admin move
law mv.ev.rwt:
  for +ds: List<&2, Bk.Def>
  for +ks: List<&2, List<&2, Word(8n)>>
  for +img: List<&2, Bk.Term>
  for +foc: U32
  for +sp: U32
  for +pend: U32
  for +rest: D.R59
  for +m: Cr.Cir.Cells
  for +nx: U32
  for +fi: U32
  for +im: U32
  for +pg: U32
  for +lim: U32
  for +inp: List<&2, Word(8n)>
  for +t: Bk.Term
  for +w: Nat
  for +fs: List<&2, D.AF>
  for +ps: List<&2, U32>
  for +e: Bk.Term
  for +p: Bk.Term
  for +b: Bk.Term
  for +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, False{}, Bk.Term.Rwt{e, p, b}, fs, ps)
  for +hv: {D.Fl(m, foc, 256) == False{} : Bool}
  MV(ds, ks, img, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w)

# mode 0, Min a b: a in the frame Min □ b; an admin move
law mv.ev.min:
  for +ds: List<&2, Bk.Def>
  for +ks: List<&2, List<&2, Word(8n)>>
  for +img: List<&2, Bk.Term>
  for +foc: U32
  for +sp: U32
  for +pend: U32
  for +rest: D.R59
  for +m: Cr.Cir.Cells
  for +nx: U32
  for +fi: U32
  for +im: U32
  for +pg: U32
  for +lim: U32
  for +inp: List<&2, Word(8n)>
  for +t: Bk.Term
  for +w: Nat
  for +fs: List<&2, D.AF>
  for +ps: List<&2, U32>
  for +a: Bk.Term
  for +b: Bk.Term
  for +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, False{}, Bk.Term.Min{a, b}, fs, ps)
  for +hv: {D.Fl(m, foc, 256) == False{} : Bool}
  MV(ds, ks, img, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w)

# mode 1, no frame: M.out halts with 0 and the bytes of the value (Program.unbytes), or with 2 when it is no list of bytes
law mv.out:
  for +ds: List<&2, Bk.Def>
  for +ks: List<&2, List<&2, Word(8n)>>
  for +img: List<&2, Bk.Term>
  for +foc: U32
  for +sp: U32
  for +pend: U32
  for +rest: D.R59
  for +m: Cr.Cir.Cells
  for +nx: U32
  for +fi: U32
  for +im: U32
  for +pg: U32
  for +lim: U32
  for +inp: List<&2, Word(8n)>
  for +t: Bk.Term
  for +w: Nat
  for +fs: List<&2, D.AF>
  for +ps: List<&2, U32>
  for +focus: Bk.Term
  for +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Nil{}, ps)
  MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w)

# mode 1, App q □ a (app_arg, app_val) with q live and a not known: a to evaluate, in the frame App q v □; an admin move
law mv.ret.swap:
  for +ds: List<&2, Bk.Def>
  for +ks: List<&2, List<&2, Word(8n)>>
  for +img: List<&2, Bk.Term>
  for +foc: U32
  for +sp: U32
  for +pend: U32
  for +rest: D.R59
  for +m: Cr.Cir.Cells
  for +nx: U32
  for +fi: U32
  for +im: U32
  for +pg: U32
  for +lim: U32
  for +inp: List<&2, Word(8n)>
  for +t: Bk.Term
  for +w: Nat
  for +fs: List<&2, D.AF>
  for +ps: List<&2, U32>
  for +focus: Bk.Term
  for +kind: D.FK
  for +q: Bk.Quan
  for +k: Bool
  for +a: Bk.Term
  for +b: Bk.Term
  for +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Con{D.AF{kind, q, k, a, b}, fs}, ps)
  for +hk: {FK.isapp(kind) == True{} : Bool}
  for +hs: {Bool.and(El.Quan.live(q), Bool.not(k)) == True{} : Bool}
  MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w)

# mode 1, App q v □ a (app_arg, app_val), when q is dead or a known: the redex of a λ (Eval.redex): its body with the argument put in (M.data, M.copy), a step; halt 2 when the λ does not bind it
law mv.ret.app.lam:
  for +ds: List<&2, Bk.Def>
  for +ks: List<&2, List<&2, Word(8n)>>
  for +img: List<&2, Bk.Term>
  for +foc: U32
  for +sp: U32
  for +pend: U32
  for +rest: D.R59
  for +m: Cr.Cir.Cells
  for +nx: U32
  for +fi: U32
  for +im: U32
  for +pg: U32
  for +lim: U32
  for +inp: List<&2, Word(8n)>
  for +t: Bk.Term
  for +w: Nat
  for +fs: List<&2, D.AF>
  for +ps: List<&2, U32>
  for +r: Bk.Quan
  for +h: Bk.Term
  for +kind: D.FK
  for +q: Bk.Quan
  for +k: Bool
  for +a: Bk.Term
  for +b: Bk.Term
  for +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, Bk.Term.Lam{r, h}, Con{D.AF{kind, q, k, a, b}, fs}, ps)
  for +hk: {FK.isapp(kind) == True{} : Bool}
  for +hs: {Bool.and(El.Quan.live(q), Bool.not(k)) == False{} : Bool}
  for +hfv: {D.Term.below(t, U32.to_nat(2147483648)) == True{} : Bool}
  MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w)

# mode 1, App q g □ (app_fun), with the value v: the redex of a λ (Eval.redex): its body with the argument put in (M.data, M.copy), a step; halt 2 when the λ does not bind it
law mv.ret.fun.lam:
  for +ds: List<&2, Bk.Def>
  for +ks: List<&2, List<&2, Word(8n)>>
  for +img: List<&2, Bk.Term>
  for +foc: U32
  for +sp: U32
  for +pend: U32
  for +rest: D.R59
  for +m: Cr.Cir.Cells
  for +nx: U32
  for +fi: U32
  for +im: U32
  for +pg: U32
  for +lim: U32
  for +inp: List<&2, Word(8n)>
  for +t: Bk.Term
  for +w: Nat
  for +fs: List<&2, D.AF>
  for +ps: List<&2, U32>
  for +r: Bk.Quan
  for +h: Bk.Term
  for +focus: Bk.Term
  for +q: Bk.Quan
  for +k: Bool
  for +b: Bk.Term
  for +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Con{D.AF{D.FK.fun{}, q, k, Bk.Term.Lam{r, h}, b}, fs}, ps)
  for +hfv: {D.Term.below(t, U32.to_nat(2147483648)) == True{} : Bool}
  MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w)

# mode 1, App q v □ a (app_arg, app_val), when q is dead or a known: the redex of a λ-match of pairs: its case on the pair's fields, a step; halt 2 when the argument is no live pair
law mv.ret.app.prj:
  for +ds: List<&2, Bk.Def>
  for +ks: List<&2, List<&2, Word(8n)>>
  for +img: List<&2, Bk.Term>
  for +foc: U32
  for +sp: U32
  for +pend: U32
  for +rest: D.R59
  for +m: Cr.Cir.Cells
  for +nx: U32
  for +fi: U32
  for +im: U32
  for +pg: U32
  for +lim: U32
  for +inp: List<&2, Word(8n)>
  for +t: Bk.Term
  for +w: Nat
  for +fs: List<&2, D.AF>
  for +ps: List<&2, U32>
  for +h: Bk.Term
  for +kind: D.FK
  for +q: Bk.Quan
  for +k: Bool
  for +a: Bk.Term
  for +b: Bk.Term
  for +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, Bk.Term.Prj{h}, Con{D.AF{kind, q, k, a, b}, fs}, ps)
  for +hk: {FK.isapp(kind) == True{} : Bool}
  for +hs: {Bool.and(El.Quan.live(q), Bool.not(k)) == False{} : Bool}
  MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w)

# mode 1, App q g □ (app_fun), with the value v: the redex of a λ-match of pairs: its case on the pair's fields, a step; halt 2 when the argument is no live pair
law mv.ret.fun.prj:
  for +ds: List<&2, Bk.Def>
  for +ks: List<&2, List<&2, Word(8n)>>
  for +img: List<&2, Bk.Term>
  for +foc: U32
  for +sp: U32
  for +pend: U32
  for +rest: D.R59
  for +m: Cr.Cir.Cells
  for +nx: U32
  for +fi: U32
  for +im: U32
  for +pg: U32
  for +lim: U32
  for +inp: List<&2, Word(8n)>
  for +t: Bk.Term
  for +w: Nat
  for +fs: List<&2, D.AF>
  for +ps: List<&2, U32>
  for +h: Bk.Term
  for +focus: Bk.Term
  for +q: Bk.Quan
  for +k: Bool
  for +b: Bk.Term
  for +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Con{D.AF{D.FK.fun{}, q, k, Bk.Term.Prj{h}, b}, fs}, ps)
  MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w)

# mode 1, App q v □ a (app_arg, app_val), when q is dead or a known: the redex of a λ-match of labels: the case of the label, a step; halt 2 when the argument is no live label
law mv.ret.app.mat:
  for +ds: List<&2, Bk.Def>
  for +ks: List<&2, List<&2, Word(8n)>>
  for +img: List<&2, Bk.Term>
  for +foc: U32
  for +sp: U32
  for +pend: U32
  for +rest: D.R59
  for +m: Cr.Cir.Cells
  for +nx: U32
  for +fi: U32
  for +im: U32
  for +pg: U32
  for +lim: U32
  for +inp: List<&2, Word(8n)>
  for +t: Bk.Term
  for +w: Nat
  for +fs: List<&2, D.AF>
  for +ps: List<&2, U32>
  for +j: List<&2, Word(8n)>
  for +h: Bk.Term
  for +n: Bk.Term
  for +kind: D.FK
  for +q: Bk.Quan
  for +k: Bool
  for +a: Bk.Term
  for +b: Bk.Term
  for +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, Bk.Term.Mat{j, h, n}, Con{D.AF{kind, q, k, a, b}, fs}, ps)
  for +hk: {FK.isapp(kind) == True{} : Bool}
  for +hs: {Bool.and(El.Quan.live(q), Bool.not(k)) == False{} : Bool}
  MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w)

# mode 1, App q g □ (app_fun), with the value v: the redex of a λ-match of labels: the case of the label, a step; halt 2 when the argument is no live label
law mv.ret.fun.mat:
  for +ds: List<&2, Bk.Def>
  for +ks: List<&2, List<&2, Word(8n)>>
  for +img: List<&2, Bk.Term>
  for +foc: U32
  for +sp: U32
  for +pend: U32
  for +rest: D.R59
  for +m: Cr.Cir.Cells
  for +nx: U32
  for +fi: U32
  for +im: U32
  for +pg: U32
  for +lim: U32
  for +inp: List<&2, Word(8n)>
  for +t: Bk.Term
  for +w: Nat
  for +fs: List<&2, D.AF>
  for +ps: List<&2, U32>
  for +j: List<&2, Word(8n)>
  for +h: Bk.Term
  for +n: Bk.Term
  for +focus: Bk.Term
  for +q: Bk.Quan
  for +k: Bool
  for +b: Bk.Term
  for +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Con{D.AF{D.FK.fun{}, q, k, Bk.Term.Mat{j, h, n}, b}, fs}, ps)
  MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w)

# mode 1, App q v □ a (app_arg, app_val), when q is dead or a known: the redex of any other value: a call (M.call, with M.walk and M.copy) of the def at the head of its spine: a step to the copy of its leaf, or a value that waits for more arguments (an admin move); halt 2 when no walk exists
law mv.ret.app.call:
  for +ds: List<&2, Bk.Def>
  for +ks: List<&2, List<&2, Word(8n)>>
  for +img: List<&2, Bk.Term>
  for +foc: U32
  for +sp: U32
  for +pend: U32
  for +rest: D.R59
  for +m: Cr.Cir.Cells
  for +nx: U32
  for +fi: U32
  for +im: U32
  for +pg: U32
  for +lim: U32
  for +inp: List<&2, Word(8n)>
  for +t: Bk.Term
  for +w: Nat
  for +fs: List<&2, D.AF>
  for +ps: List<&2, U32>
  for +focus: Bk.Term
  for +kind: D.FK
  for +q: Bk.Quan
  for +k: Bool
  for +a: Bk.Term
  for +b: Bk.Term
  for +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Con{D.AF{kind, q, k, a, b}, fs}, ps)
  for +hk: {FK.isapp(kind) == True{} : Bool}
  for +hs: {Bool.and(El.Quan.live(q), Bool.not(k)) == False{} : Bool}
  for +hn: {A.node(focus) == False{} : Bool}
  for +hfv: {D.Term.below(t, U32.to_nat(2147483648)) == True{} : Bool}
  MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w)

# mode 1, App q g □ (app_fun), with the value v: the redex of any other value: a call (M.call, with M.walk and M.copy) of the def at the head of its spine: a step to the copy of its leaf, or a value that waits for more arguments (an admin move); halt 2 when no walk exists
law mv.ret.fun.call:
  for +ds: List<&2, Bk.Def>
  for +ks: List<&2, List<&2, Word(8n)>>
  for +img: List<&2, Bk.Term>
  for +foc: U32
  for +sp: U32
  for +pend: U32
  for +rest: D.R59
  for +m: Cr.Cir.Cells
  for +nx: U32
  for +fi: U32
  for +im: U32
  for +pg: U32
  for +lim: U32
  for +inp: List<&2, Word(8n)>
  for +t: Bk.Term
  for +w: Nat
  for +fs: List<&2, D.AF>
  for +ps: List<&2, U32>
  for +g: Bk.Term
  for +focus: Bk.Term
  for +q: Bk.Quan
  for +k: Bool
  for +b: Bk.Term
  for +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Con{D.AF{D.FK.fun{}, q, k, g, b}, fs}, ps)
  for +hn: {A.node(g) == False{} : Bool}
  for +hfv: {D.Term.below(t, U32.to_nat(2147483648)) == True{} : Bool}
  MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w)

# mode 1, Let q □ a, with the value v: a with v put in (M.data, M.copy), a step; halt 2 when q is 2 and v is no Data
law mv.ret.let:
  for +ds: List<&2, Bk.Def>
  for +ks: List<&2, List<&2, Word(8n)>>
  for +img: List<&2, Bk.Term>
  for +foc: U32
  for +sp: U32
  for +pend: U32
  for +rest: D.R59
  for +m: Cr.Cir.Cells
  for +nx: U32
  for +fi: U32
  for +im: U32
  for +pg: U32
  for +lim: U32
  for +inp: List<&2, Word(8n)>
  for +t: Bk.Term
  for +w: Nat
  for +fs: List<&2, D.AF>
  for +ps: List<&2, U32>
  for +focus: Bk.Term
  for +q: Bk.Quan
  for +k: Bool
  for +a: Bk.Term
  for +b: Bk.Term
  for +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Con{D.AF{D.FK.let{}, q, k, a, b}, fs}, ps)
  for +hfv: {D.Term.below(t, U32.to_nat(2147483648)) == True{} : Bool}
  MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w)

# mode 1, Tup q □ a, with the value v: a to evaluate, in the frame Tup q v □; an admin move
law mv.ret.tupb:
  for +ds: List<&2, Bk.Def>
  for +ks: List<&2, List<&2, Word(8n)>>
  for +img: List<&2, Bk.Term>
  for +foc: U32
  for +sp: U32
  for +pend: U32
  for +rest: D.R59
  for +m: Cr.Cir.Cells
  for +nx: U32
  for +fi: U32
  for +im: U32
  for +pg: U32
  for +lim: U32
  for +inp: List<&2, Word(8n)>
  for +t: Bk.Term
  for +w: Nat
  for +fs: List<&2, D.AF>
  for +ps: List<&2, U32>
  for +focus: Bk.Term
  for +q: Bk.Quan
  for +k: Bool
  for +a: Bk.Term
  for +b: Bk.Term
  for +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Con{D.AF{D.FK.tupb{}, q, k, a, b}, fs}, ps)
  MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w)

# mode 1, Tup q a □, with the value v: the value Tup q a v; an admin move
law mv.ret.tupa:
  for +ds: List<&2, Bk.Def>
  for +ks: List<&2, List<&2, Word(8n)>>
  for +img: List<&2, Bk.Term>
  for +foc: U32
  for +sp: U32
  for +pend: U32
  for +rest: D.R59
  for +m: Cr.Cir.Cells
  for +nx: U32
  for +fi: U32
  for +im: U32
  for +pg: U32
  for +lim: U32
  for +inp: List<&2, Word(8n)>
  for +t: Bk.Term
  for +w: Nat
  for +fs: List<&2, D.AF>
  for +ps: List<&2, U32>
  for +focus: Bk.Term
  for +q: Bk.Quan
  for +k: Bool
  for +a: Bk.Term
  for +b: Bk.Term
  for +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Con{D.AF{D.FK.tupa{}, q, k, a, b}, fs}, ps)
  MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w)

# mode 1, Rwt □ a b, with the value v: b when v is Rfl, a step; else halt 2
law mv.ret.rwt:
  for +ds: List<&2, Bk.Def>
  for +ks: List<&2, List<&2, Word(8n)>>
  for +img: List<&2, Bk.Term>
  for +foc: U32
  for +sp: U32
  for +pend: U32
  for +rest: D.R59
  for +m: Cr.Cir.Cells
  for +nx: U32
  for +fi: U32
  for +im: U32
  for +pg: U32
  for +lim: U32
  for +inp: List<&2, Word(8n)>
  for +t: Bk.Term
  for +w: Nat
  for +fs: List<&2, D.AF>
  for +ps: List<&2, U32>
  for +focus: Bk.Term
  for +q: Bk.Quan
  for +k: Bool
  for +a: Bk.Term
  for +b: Bk.Term
  for +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Con{D.AF{D.FK.rwt{}, q, k, a, b}, fs}, ps)
  MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w)

# mode 1, Min □ a, with the value v: a to evaluate, in the frame Min v □; an admin move
law mv.ret.minb:
  for +ds: List<&2, Bk.Def>
  for +ks: List<&2, List<&2, Word(8n)>>
  for +img: List<&2, Bk.Term>
  for +foc: U32
  for +sp: U32
  for +pend: U32
  for +rest: D.R59
  for +m: Cr.Cir.Cells
  for +nx: U32
  for +fi: U32
  for +im: U32
  for +pg: U32
  for +lim: U32
  for +inp: List<&2, Word(8n)>
  for +t: Bk.Term
  for +w: Nat
  for +fs: List<&2, D.AF>
  for +ps: List<&2, U32>
  for +focus: Bk.Term
  for +q: Bk.Quan
  for +k: Bool
  for +a: Bk.Term
  for +b: Bk.Term
  for +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Con{D.AF{D.FK.minb{}, q, k, a, b}, fs}, ps)
  MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w)

# mode 1, Min a □, with the value v: the meet of a and v, a step, when both are labels of quantities; else halt 2
law mv.ret.mina:
  for +ds: List<&2, Bk.Def>
  for +ks: List<&2, List<&2, Word(8n)>>
  for +img: List<&2, Bk.Term>
  for +foc: U32
  for +sp: U32
  for +pend: U32
  for +rest: D.R59
  for +m: Cr.Cir.Cells
  for +nx: U32
  for +fi: U32
  for +im: U32
  for +pg: U32
  for +lim: U32
  for +inp: List<&2, Word(8n)>
  for +t: Bk.Term
  for +w: Nat
  for +fs: List<&2, D.AF>
  for +ps: List<&2, U32>
  for +focus: Bk.Term
  for +q: Bk.Quan
  for +k: Bool
  for +a: Bk.Term
  for +b: Bk.Term
  for +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Con{D.AF{D.FK.mina{}, q, k, a, b}, fs}, ps)
  MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w)
