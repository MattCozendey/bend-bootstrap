# compiler: layer B, the machine
# ==============================
#
# The shared definitions (the invariant, the heap, the accounting, Post and
# PostB, the premises' named types, the store and cell kit) live in
# definitions.bend (D); the execution equations of the machine's statements in
# statement_runs.bend (X); the moves' kit and the laws that the units prove
# (IV, MV, the premises, one law per move) in move_kit.bend (K). This file
# keeps the choice of the move, the loop and the assembly.
#
# mach.safe, mach.sound and mach.complete of runs_as_eval.bend, with exactly their
# types (mach.safe.proof, mach.sound.proof, mach.complete.proof, at the end
# of "The run"), from the invariant of the machine (Inv) and one law per
# move. The Lean machine (lean, Interpreter/Machine.lean, Interpreter/Machine/*.lean) is
# the template: a move is an admin move that keeps the term, or one step of
# Eval, and keeps what the state knows.
#
# The loop: loop.post (by induction on the fuel) gives only what Eval gives;
# loop.done (by induction on Eval's steps, then on the measure) finds a fuel
# that gives it, or runs out of memory.
#
# Proven: the choice of the moves (round.post, round.done), the loop, the run
# from Cir.result's start, the three lemmas. Open: the laws of move_kit.bend,
# definitions.bend and copy_substitution.bend (filled, some as ?TODO for now,
# in the units' files that this file imports), and mach.memory with what it
# needs (round.peak, round.room).

import Base
import ../../Book/impl.bend as Bk
import ../../Eval/impl.bend as El
import ../../Wasm/impl.bend as Wa
import ../../Program/impl.bend as Pg
import ../Cir/impl.bend as Cr
import ./impl.bend as Mc
import ./cell_terms.bend as T
import ../need_big.bend as N
import ./copy_terms.bend as CT
import ./free_variables.bend as Fv
import ./read_bound.bend as Rb
import ./definitions.bend as D
import ./statement_runs.bend as X
import ./move_kit.bend as K
import ./cir_fits.bend as CF
import ./heap_ops.bend as U2
import ./copy_gives_subst.bend as U4
import ./copy_bridge.bend as U5
import ./data_check.bend as U6
import ./walk.bend as U7
import ./input_bridge.bend as U8
import ./moves_out.bend as U9
import ./moves_push.bend as U10
import ./swap_moves.bend as U11
import ./moves_copy.bend as U12
import ./moves_match.bend as U13
import ./moves_call.bend as U14

# The choice of the move
# ----------------------

# mode 0: by the flag VALUE of the focus' cell, then by its term
def round.ev(b: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +focus: Bk.Term, eb: {D.Fl(m, foc, 256) == b : Bool},
  iv: K.IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, False{}, focus, fs, ps),
  hfv: {D.Term.below(t, U32.to_nat(2147483648)) == True{} : Bool}) -> K.MV(ds, ks, img, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  match b:
    case True{}:
      K.mv.ev.val(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, focus, iv, eb)
    case False{}:
      match focus:
        case Bk.Term.Var{+i}:
          K.mv.ev.var(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, i, iv, eb)
        case Bk.Term.Ref{+k}:
          K.mv.ev.ref(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, k, iv, eb, hfv)
        case Bk.Term.Ann{+x, +y}:
          K.mv.ev.ann(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, x, y, iv, eb)
        case Bk.Term.Let{+q, +v, +b2}:
          match q:
            case Bk.Quan.Q0{}:
              K.mv.ev.unlet(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Quan.Q0{}, v, b2, iv, eb, {==}, hfv)
            case Bk.Quan.Q1{}:
              K.mv.ev.let(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Quan.Q1{}, v, b2, iv, eb, {==})
            case Bk.Quan.Q2{}:
              K.mv.ev.let(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Quan.Q2{}, v, b2, iv, eb, {==})
        case Bk.Term.Typ{+x}:
          K.mv.ev.former(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Typ{x}, iv, {==})
        case Bk.Term.Min{+a, +b2}:
          K.mv.ev.min(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, a, b2, iv, eb)
        case Bk.Term.All{+q, +a, +b2}:
          K.mv.ev.former(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.All{q, a, b2}, iv, {==})
        case Bk.Term.Lam{+q, +b2}:
          K.mv.ev.former(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Lam{q, b2}, iv, {==})
        case Bk.Term.App{+q, +g, +x}:
          K.mv.ev.app(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, g, x, iv, eb)
        case Bk.Term.Sig{+q, +a, +b2}:
          K.mv.ev.former(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Sig{q, a, b2}, iv, {==})
        case Bk.Term.Tup{+q, +a, +b2}:
          match q:
            case Bk.Quan.Q0{}:
              K.mv.ev.tup0(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Quan.Q0{}, a, b2, iv, eb, {==})
            case Bk.Quan.Q1{}:
              K.mv.ev.tup(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Quan.Q1{}, a, b2, iv, eb, {==})
            case Bk.Quan.Q2{}:
              K.mv.ev.tup(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Quan.Q2{}, a, b2, iv, eb, {==})
        case Bk.Term.Prj{+h}:
          K.mv.ev.former(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Prj{h}, iv, {==})
        case Bk.Term.Enu{+e}:
          K.mv.ev.former(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Enu{e}, iv, {==})
        case Bk.Term.Lab{+k}:
          K.mv.ev.former(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Lab{k}, iv, {==})
        case Bk.Term.Mat{+k, +h, +n}:
          K.mv.ev.former(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Mat{k, h, n}, iv, {==})
        case Bk.Term.Efq{}:
          K.mv.ev.former(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Efq{}, iv, {==})
        case Bk.Term.Eql{+a, +b2, +y}:
          K.mv.ev.former(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Eql{a, b2, y}, iv, {==})
        case Bk.Term.Rfl{}:
          K.mv.ev.former(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Rfl{}, iv, {==})
        case Bk.Term.Rwt{+e, +p2, +b2}:
          K.mv.ev.rwt(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, e, p2, b2, iv, eb)

# mode 1, App q □ a: swap when q is live and a is not known; else the redex, by
# the value's term
def round.app(b: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +focus: Bk.Term, +kind: D.FK, +q: Bk.Quan, +k: Bool, +a: Bk.Term, +bb: Bk.Term,
  eb: {Bool.and(El.Quan.live(q), Bool.not(k)) == b : Bool}, hk: {K.FK.isapp(kind) == True{} : Bool},
  iv: K.IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Con{D.AF{kind, q, k, a, bb}, fs}, ps),
  hfv: {D.Term.below(t, U32.to_nat(2147483648)) == True{} : Bool}) -> K.MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  match b:
    case True{}:
      K.mv.ret.swap(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, focus, kind, q, k, a, bb, iv, hk, eb)
    case False{}:
      match focus:
        case Bk.Term.Var{+i}:
          K.mv.ret.app.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Var{i}, kind, q, k, a, bb, iv, hk, eb, {==}, hfv)
        case Bk.Term.Ref{+kk}:
          K.mv.ret.app.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Ref{kk}, kind, q, k, a, bb, iv, hk, eb, {==}, hfv)
        case Bk.Term.Ann{+x, +y}:
          K.mv.ret.app.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Ann{x, y}, kind, q, k, a, bb, iv, hk, eb, {==}, hfv)
        case Bk.Term.Let{+qq, +v, +b2}:
          K.mv.ret.app.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Let{qq, v, b2}, kind, q, k, a, bb, iv, hk, eb, {==}, hfv)
        case Bk.Term.Typ{+x}:
          K.mv.ret.app.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Typ{x}, kind, q, k, a, bb, iv, hk, eb, {==}, hfv)
        case Bk.Term.Min{+aa, +b2}:
          K.mv.ret.app.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Min{aa, b2}, kind, q, k, a, bb, iv, hk, eb, {==}, hfv)
        case Bk.Term.All{+qq, +aa, +b2}:
          K.mv.ret.app.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.All{qq, aa, b2}, kind, q, k, a, bb, iv, hk, eb, {==}, hfv)
        case Bk.Term.Lam{+r, +b2}:
          K.mv.ret.app.lam(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, r, b2, kind, q, k, a, bb, iv, hk, eb, hfv)
        case Bk.Term.App{+qq, +g, +x}:
          K.mv.ret.app.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.App{qq, g, x}, kind, q, k, a, bb, iv, hk, eb, {==}, hfv)
        case Bk.Term.Sig{+qq, +aa, +b2}:
          K.mv.ret.app.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Sig{qq, aa, b2}, kind, q, k, a, bb, iv, hk, eb, {==}, hfv)
        case Bk.Term.Tup{+qq, +aa, +b2}:
          K.mv.ret.app.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Tup{qq, aa, b2}, kind, q, k, a, bb, iv, hk, eb, {==}, hfv)
        case Bk.Term.Prj{+h}:
          K.mv.ret.app.prj(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, h, kind, q, k, a, bb, iv, hk, eb)
        case Bk.Term.Enu{+e}:
          K.mv.ret.app.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Enu{e}, kind, q, k, a, bb, iv, hk, eb, {==}, hfv)
        case Bk.Term.Lab{+kk}:
          K.mv.ret.app.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Lab{kk}, kind, q, k, a, bb, iv, hk, eb, {==}, hfv)
        case Bk.Term.Mat{+kk, +h, +n}:
          K.mv.ret.app.mat(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, kk, h, n, kind, q, k, a, bb, iv, hk, eb)
        case Bk.Term.Efq{}:
          K.mv.ret.app.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Efq{}, kind, q, k, a, bb, iv, hk, eb, {==}, hfv)
        case Bk.Term.Eql{+aa, +b2, +y}:
          K.mv.ret.app.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Eql{aa, b2, y}, kind, q, k, a, bb, iv, hk, eb, {==}, hfv)
        case Bk.Term.Rfl{}:
          K.mv.ret.app.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Rfl{}, kind, q, k, a, bb, iv, hk, eb, {==}, hfv)
        case Bk.Term.Rwt{+e, +p2, +b2}:
          K.mv.ret.app.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Rwt{e, p2, b2}, kind, q, k, a, bb, iv, hk, eb, {==}, hfv)

# mode 1, App q g □: the redex, by the function's term
def round.fun(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +focus: Bk.Term, +q: Bk.Quan, +k: Bool, +g: Bk.Term, +bb: Bk.Term,
  iv: K.IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Con{D.AF{D.FK.fun{}, q, k, g, bb}, fs}, ps),
  hfv: {D.Term.below(t, U32.to_nat(2147483648)) == True{} : Bool}) -> K.MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  match g:
    case Bk.Term.Var{+i}:
      K.mv.ret.fun.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Var{i}, focus, q, k, bb, iv, {==}, hfv)
    case Bk.Term.Ref{+kk}:
      K.mv.ret.fun.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Ref{kk}, focus, q, k, bb, iv, {==}, hfv)
    case Bk.Term.Ann{+x, +y}:
      K.mv.ret.fun.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Ann{x, y}, focus, q, k, bb, iv, {==}, hfv)
    case Bk.Term.Let{+r, +v, +b2}:
      K.mv.ret.fun.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Let{r, v, b2}, focus, q, k, bb, iv, {==}, hfv)
    case Bk.Term.Typ{+x}:
      K.mv.ret.fun.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Typ{x}, focus, q, k, bb, iv, {==}, hfv)
    case Bk.Term.Min{+a, +b2}:
      K.mv.ret.fun.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Min{a, b2}, focus, q, k, bb, iv, {==}, hfv)
    case Bk.Term.All{+r, +a, +b2}:
      K.mv.ret.fun.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.All{r, a, b2}, focus, q, k, bb, iv, {==}, hfv)
    case Bk.Term.Lam{+r, +b2}:
      K.mv.ret.fun.lam(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, r, b2, focus, q, k, bb, iv, hfv)
    case Bk.Term.App{+r, +g, +x}:
      K.mv.ret.fun.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.App{r, g, x}, focus, q, k, bb, iv, {==}, hfv)
    case Bk.Term.Sig{+r, +a, +b2}:
      K.mv.ret.fun.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Sig{r, a, b2}, focus, q, k, bb, iv, {==}, hfv)
    case Bk.Term.Tup{+r, +a, +b2}:
      K.mv.ret.fun.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Tup{r, a, b2}, focus, q, k, bb, iv, {==}, hfv)
    case Bk.Term.Prj{+h}:
      K.mv.ret.fun.prj(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, h, focus, q, k, bb, iv)
    case Bk.Term.Enu{+e}:
      K.mv.ret.fun.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Enu{e}, focus, q, k, bb, iv, {==}, hfv)
    case Bk.Term.Lab{+kk}:
      K.mv.ret.fun.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Lab{kk}, focus, q, k, bb, iv, {==}, hfv)
    case Bk.Term.Mat{+kk, +h, +n}:
      K.mv.ret.fun.mat(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, kk, h, n, focus, q, k, bb, iv)
    case Bk.Term.Efq{}:
      K.mv.ret.fun.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Efq{}, focus, q, k, bb, iv, {==}, hfv)
    case Bk.Term.Eql{+a, +b2, +y}:
      K.mv.ret.fun.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Eql{a, b2, y}, focus, q, k, bb, iv, {==}, hfv)
    case Bk.Term.Rfl{}:
      K.mv.ret.fun.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Rfl{}, focus, q, k, bb, iv, {==}, hfv)
    case Bk.Term.Rwt{+e, +p2, +b2}:
      K.mv.ret.fun.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Rwt{e, p2, b2}, focus, q, k, bb, iv, {==}, hfv)

# the move of a state that Inv finds: by the mode, then by the focus or the
# top frame
def round.go(+ret: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +focus: Bk.Term,
  iv: K.IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, ret, focus, fs, ps),
  hfv: {D.Term.below(t, U32.to_nat(2147483648)) == True{} : Bool}) -> K.MV(ds, ks, img, D.S(foc, Bool.to_u32(ret), sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  match ret:
    case False{}:
      round.ev(D.Fl(m, foc, 256), ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, focus, {==}, iv, hfv)
    case True{}:
      match fs:
        case Nil{}:
          K.mv.out(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, focus, iv)
        case Con{D.AF{+kind, +q, +k, +a, +bb}, +fs2}:
          match kind:
            case D.FK.arg{}:
              round.app(Bool.and(El.Quan.live(q), Bool.not(k)), ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs2, ps, focus, D.FK.arg{}, q, k, a, bb, {==}, {==}, iv, hfv)
            case D.FK.val{}:
              round.app(Bool.and(El.Quan.live(q), Bool.not(k)), ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs2, ps, focus, D.FK.val{}, q, k, a, bb, {==}, {==}, iv, hfv)
            case D.FK.fun{}:
              round.fun(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs2, ps, focus, q, k, a, bb, iv, hfv)
            case D.FK.let{}:
              K.mv.ret.let(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs2, ps, focus, q, k, a, bb, iv, hfv)
            case D.FK.tupb{}:
              K.mv.ret.tupb(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs2, ps, focus, q, k, a, bb, iv)
            case D.FK.tupa{}:
              K.mv.ret.tupa(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs2, ps, focus, q, k, a, bb, iv)
            case D.FK.rwt{}:
              K.mv.ret.rwt(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs2, ps, focus, q, k, a, bb, iv)
            case D.FK.minb{}:
              K.mv.ret.minb(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs2, ps, focus, q, k, a, bb, iv)
            case D.FK.mina{}:
              K.mv.ret.mina(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs2, ps, focus, q, k, a, bb, iv)

# the registers, the output and its length that Inv finds
def inv.regs(-ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -regs: List<&2, U32>, -m: Cr.Cir.Cells, -nx: U32, -fi: U32, -im: U32, -out: List<&2, Word(8n)>, -outn: U32, -t: Bk.Term, -w: Nat, -ret: Bool, -focus: Bk.Term, -fs: List<&2, D.AF>, -foc: U32, -sp: U32, -pend: U32, -ps: List<&2, U32>, -rest: D.R59, iw: D.InvOf(ds, ks, img, regs, m, nx, fi, im, out, outn, t, w, ret, focus, fs, foc, sp, pend, ps, rest)) ->
  {regs == D.RG(foc, Bool.to_u32(ret), sp, pend, D.R59.list(rest)) : List<&2, U32>}:
  match iw:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}:
      e

def inv.out(-ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -regs: List<&2, U32>, -m: Cr.Cir.Cells, -nx: U32, -fi: U32, -im: U32, -out: List<&2, Word(8n)>, -outn: U32, -t: Bk.Term, -w: Nat, -ret: Bool, -focus: Bk.Term, -fs: List<&2, D.AF>, -foc: U32, -sp: U32, -pend: U32, -ps: List<&2, U32>, -rest: D.R59, iw: D.InvOf(ds, ks, img, regs, m, nx, fi, im, out, outn, t, w, ret, focus, fs, foc, sp, pend, ps, rest)) -> {out == Nil{} : List<&2, Word(8n)>}:
  match iw:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}:
      e

def inv.outn(-ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -regs: List<&2, U32>, -m: Cr.Cir.Cells, -nx: U32, -fi: U32, -im: U32, -out: List<&2, Word(8n)>, -outn: U32, -t: Bk.Term, -w: Nat, -ret: Bool, -focus: Bk.Term, -fs: List<&2, D.AF>, -foc: U32, -sp: U32, -pend: U32, -ps: List<&2, U32>, -rest: D.R59, iw: D.InvOf(ds, ks, img, regs, m, nx, fi, im, out, outn, t, w, ret, focus, fs, foc, sp, pend, ps, rest)) -> {outn == 0 : U32}:
  match iw:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, e}}}}}}}}}}:
      e

# Inv's facts, in the state that it finds: its InvOf at the registers RG,
# with no output
def iv.inv(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +out: List<&2, Word(8n)>, +outn: U32, +t: Bk.Term, +w: Nat, +ret: Bool, +focus: Bk.Term, +fs: List<&2, D.AF>, +foc: U32, +sp: U32, +pend: U32, +ps: List<&2, U32>, +rest: D.R59,
  er: {regs == D.RG(foc, Bool.to_u32(ret), sp, pend, D.R59.list(rest)) : List<&2, U32>}, eo: {out == Nil{} : List<&2, Word(8n)>},
  en: {outn == 0 : U32}, iw: D.InvOf(ds, ks, img, regs, m, nx, fi, im, out, outn, t, w, ret, focus, fs, foc, sp, pend, ps, rest)) ->
  D.InvOf(ds, ks, img, D.RG(foc, Bool.to_u32(ret), sp, pend, D.R59.list(rest)), m, nx, fi, im, Nil{}, 0, t, w, ret, focus, fs, foc, sp,
    pend, ps, rest):
  %er : D.InvOf(ds, ks, img, _, m, nx, fi, im, Nil{}, 0, t, w, ret, focus, fs, foc, sp, pend, ps, rest)
  %eo : D.InvOf(ds, ks, img, regs, m, nx, fi, im, _, 0, t, w, ret, focus, fs, foc, sp, pend, ps, rest)
  %en : D.InvOf(ds, ks, img, regs, m, nx, fi, im, out, _, t, w, ret, focus, fs, foc, sp, pend, ps, rest)
  iw

# Inv's facts, and its accounting
def iv.of(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +out: List<&2, Word(8n)>, +outn: U32, +t: Bk.Term, +w: Nat, +ret: Bool, +focus: Bk.Term, +fs: List<&2, D.AF>, +foc: U32, +sp: U32, +pend: U32, +ps: List<&2, U32>, +rest: D.R59,
  er: {regs == D.RG(foc, Bool.to_u32(ret), sp, pend, D.R59.list(rest)) : List<&2, U32>}, eo: {out == Nil{} : List<&2, Word(8n)>},
  en: {outn == 0 : U32}, iw: D.InvOf(ds, ks, img, regs, m, nx, fi, im, out, outn, t, w, ret, focus, fs, foc, sp, pend, ps, rest),
  acc: D.Ex(List<&2, D.Rt>, zs => D.AccK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{foc, focus}], Nil{}, sp, fs, ps, zs))) ->
  K.IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, ret, focus, fs, ps):
  (iv.inv(ds, ks, img, regs, m, nx, fi, im, out, outn, t, w, ret, focus, fs, foc, sp, pend, ps, rest, er, eo, en, iw), acc)

def round.iw(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +out: List<&2, Word(8n)>, +outn: U32, +t: Bk.Term, +w: Nat, +ret: Bool, +focus: Bk.Term, +fs: List<&2, D.AF>, +foc: U32, +sp: U32, +pend: U32, +ps: List<&2, U32>, +rest: D.R59, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +iw: D.InvOf(ds, ks, img, regs, m, nx, fi, im, out, outn, t, w, ret, focus, fs, foc, sp, pend, ps, rest),
  hfv: {D.Term.below(t, U32.to_nat(2147483648)) == True{} : Bool},
  acc: D.Ex(List<&2, D.Rt>, zs => D.AccK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{foc, focus}], Nil{}, sp, fs, ps, zs))) ->
  K.MV(ds, ks, img, Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, out, outn}, t, w):
  +er = inv.regs(ds, ks, img, regs, m, nx, fi, im, out, outn, t, w, ret, focus, fs, foc, sp, pend, ps, rest, iw)
  +eo = inv.out(ds, ks, img, regs, m, nx, fi, im, out, outn, t, w, ret, focus, fs, foc, sp, pend, ps, rest, iw)
  +en = inv.outn(ds, ks, img, regs, m, nx, fi, im, out, outn, t, w, ret, focus, fs, foc, sp, pend, ps, rest, iw)
  %Equal.sym(List<&2, U32>, regs, D.RG(foc, Bool.to_u32(ret), sp, pend, D.R59.list(rest)), er) :
    K.MV(ds, ks, img, Cr.Cir.State{_, m, nx, fi, im, pg, lim, inp, out, outn}, t, w)
  %Equal.sym(List<&2, Word(8n)>, out, Nil{}, eo) :
    K.MV(ds, ks, img, Cr.Cir.State{D.RG(foc, Bool.to_u32(ret), sp, pend, D.R59.list(rest)), m, nx, fi, im, pg, lim, inp, _, outn}, t, w)
  %Equal.sym(U32, outn, 0, en) :
    K.MV(ds, ks, img, Cr.Cir.State{D.RG(foc, Bool.to_u32(ret), sp, pend, D.R59.list(rest)), m, nx, fi, im, pg, lim, inp, Nil{}, _}, t, w)
  round.go(ret, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, focus,
    iv.of(ds, ks, img, regs, m, nx, fi, im, out, outn, t, w, ret, focus, fs, foc, sp, pend, ps, rest, er, eo, en, iw, acc),
    hfv)

def round.wit(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +out: List<&2, Word(8n)>, +outn: U32,
  +t: Bk.Term, +w: Nat, inv: D.Inv(ds, ks, img, Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, out, outn}, t, w),
  hfv: {D.Term.below(t, U32.to_nat(2147483648)) == True{} : Bool}) ->
  K.MV(ds, ks, img, Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, out, outn}, t, w):
  (x, pr) = inv
  match x:
    case D.Wit{+ret, +focus, +fs, +foc, +sp, +pend, +ps, +rest}:
      (iw, acc) = pr
      round.iw(ds, ks, img, regs, m, nx, fi, im, out, outn, t, w, ret, focus, fs, foc, sp, pend, ps, rest, pg, lim, inp, iw, hfv, acc)

# the move of a state of the invariant
def round.mv(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, st: Cr.Cir.State, +t: Bk.Term,
  +w: Nat, inv: D.Inv(ds, ks, img, st, t, w),
  hfv: {D.Term.below(t, U32.to_nat(2147483648)) == True{} : Bool}) -> K.MV(ds, ks, img, st, t, w):
  match st:
    case Cr.Cir.State{+regs, +m, +nx, +fi, +im, +pg, +lim, +inp, +out, +outn}:
      round.wit(ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, out, outn, t, w, inv, hfv)

# a round of the main loop, for any fuel: an admin move, a step, a halt that
# says what Eval gives, or out of memory
def round.post(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +st: Cr.Cir.State, +t: Bk.Term, +w: Nat, inv: D.Inv(ds, ks, img, st, t, w),
  hfv: {D.Term.below(t, U32.to_nat(2147483648)) == True{} : Bool}) ->
  D.Post(False{}, Cr.Cir.exec(f, D.B.body(), st), s => D.Rnd(ds, ks, img, t, w, s), s => st2 => D.HR(ds, t, s, st2)):
  K.mv.post(f, ds, ks, img, st, t, w, round.mv(ds, ks, img, st, t, w, inv, hfv))

# a round of the main loop ends, with some fuel
def round.done(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st: Cr.Cir.State,
  +t: Bk.Term, +w: Nat, inv: D.Inv(ds, ks, img, st, t, w),
  hfv: {D.Term.below(t, U32.to_nat(2147483648)) == True{} : Bool}) -> D.Ex(Nat, f => D.Ends(Cr.Cir.exec(f, D.B.body(), st))):
  K.mv.done(ds, ks, img, st, t, w, round.mv(ds, ks, img, st, t, w, inv, hfv))

# The loop gives what Eval gives
# ------------------------------

# the start term is closed, hence below every bound B (the machine's: 2^31)
def fv.start.big(+i: List<&2, Word(8n)>, +B: Nat) -> {D.Term.below(Pg.Program.start(i), B) == True{} : Bool}:
  CT.Tz.below_mono(Pg.Program.start(i), 0n, B, Fv.fv.toB(0n, B, N.le_zero(B)), Fv.fv.start(i))

# a weaker halt
def post.wk(dn: Bool, o: Cr.Cir.Out, -Q: Cr.Cir.State -> Type, -H1: U32 -> Cr.Cir.State -> Type,
  -H2: U32 -> Cr.Cir.State -> Type, h: D.Post(dn, o, Q, H1), hh: @s: U32 -> @st: Cr.Cir.State -> H1(s, st) -> H2(s, st)) ->
  D.Post(dn, o, Q, H2):
  match o:
    case Cr.Cir.Out.next{st}:
      h
    case Cr.Cir.Out.halt{s, st}:
      hh(s, st, h)
    case Cr.Cir.Out.out_of_memory{}:
      Unit{}
    case Cr.Cir.Out.trap{}:
      h
    case Cr.Cir.Out.not_done{}:
      h

# no result after a term with no step
def none.after(+j: Nat, +ds: List<&2, Bk.Def>, +t: Bk.Term, es: {El.Eval.step(ds, t) == None{} : Maybe<Bk.Term>}) ->
  {Pg.Program.result(ds, El.Eval.steps(1n+j, ds, t)) == None{} : Maybe<&2, List<&2, Word(8n)>>}:
  %Equal.sym(Maybe<Bk.Term>, El.Eval.step(ds, t), None{}, es) : {Pg.Program.result(ds, El.Eval.run(j, ds, _)) == None{} : Maybe<&2, List<&2, Word(8n)>>}
  %Equal.sym(Maybe<Bk.Term>, El.Eval.run(j, ds, None{}), None{}, D.run.none(j, ds)) : {Pg.Program.result(ds, _) == None{} : Maybe<&2, List<&2, Word(8n)>>}
  {==}

# no result ever, from a term with no step and no result
def he.none(k: Nat, +ds: List<&2, Bk.Def>, +t: Bk.Term, +es: {El.Eval.step(ds, t) == None{} : Maybe<Bk.Term>},
  er: {Pg.Program.result(ds, Some{t}) == None{} : Maybe<&2, List<&2, Word(8n)>>}) ->
  {Pg.Program.result(ds, El.Eval.steps(k, ds, t)) == None{} : Maybe<&2, List<&2, Word(8n)>>}:
  match k:
    case 0n:
      er
    case 1n+(+j):
      none.after(j, ds, t, es)

# a round's halt says what the loop's says
def he.of(+ds: List<&2, Bk.Def>, +t: Bk.Term, -s: U32, -st: Cr.Cir.State, h: D.HR(ds, t, s, st)) -> D.HE(ds, t, s, st):
  match h:
    case Inl{x}:
      (e0, r) = x
      (es, er) = r
      Inl{(e0, (0n, er))}
    case Inr{x}:
      (e2, r) = x
      (es, er) = r
      Inr{(e2, k => he.none(k, ds, t, es, er))}

# the result after a step, from the result of its term
def step.res(+j: Nat, +ds: List<&2, Bk.Def>, +t: Bk.Term, -u: Bk.Term, -x: Maybe<&2, List<&2, Word(8n)>>,
  es: {El.Eval.step(ds, t) == Some{u} : Maybe<Bk.Term>},
  e: {Pg.Program.result(ds, El.Eval.steps(j, ds, u)) == x : Maybe<&2, List<&2, Word(8n)>>}) ->
  {Pg.Program.result(ds, El.Eval.steps(1n+j, ds, t)) == x : Maybe<&2, List<&2, Word(8n)>>}:
  %Equal.sym(Maybe<Bk.Term>, El.Eval.step(ds, t), Some{u}, es) : {Pg.Program.result(ds, El.Eval.run(j, ds, _)) == x : Maybe<&2, List<&2, Word(8n)>>}
  e

# the result of a term from that of its step
def res.step(+j: Nat, +ds: List<&2, Bk.Def>, +t: Bk.Term, -u: Bk.Term, -x: Maybe<&2, List<&2, Word(8n)>>,
  es: {El.Eval.step(ds, t) == Some{u} : Maybe<Bk.Term>},
  e: {Pg.Program.result(ds, El.Eval.steps(1n+j, ds, t)) == x : Maybe<&2, List<&2, Word(8n)>>}) ->
  {Pg.Program.result(ds, El.Eval.steps(j, ds, u)) == x : Maybe<&2, List<&2, Word(8n)>>}:
  %es : {Pg.Program.result(ds, El.Eval.run(j, ds, _)) == x : Maybe<&2, List<&2, Word(8n)>>}
  e

def he.all(k: Nat, +ds: List<&2, Bk.Def>, +t: Bk.Term, +u: Bk.Term, +es: {El.Eval.step(ds, t) == Some{u} : Maybe<Bk.Term>},
  g: @k: Nat -> {Pg.Program.result(ds, El.Eval.steps(k, ds, u)) == None{} : Maybe<&2, List<&2, Word(8n)>>}) ->
  {Pg.Program.result(ds, El.Eval.steps(k, ds, t)) == None{} : Maybe<&2, List<&2, Word(8n)>>}:
  match k:
    case 0n:
      D.res.nv(ds, t, K.vals.of(El.Eval.vals(ds, t, False{}), ds, t, u, {==}, es))
    case 1n+(+j):
      step.res(j, ds, t, u, None{}, es, g(j))

# a halt of the loop after a step says what Eval gives before the step
def he.step(+ds: List<&2, Bk.Def>, +t: Bk.Term, +u: Bk.Term, +es: {El.Eval.step(ds, t) == Some{u} : Maybe<Bk.Term>},
  -s: U32, -st: Cr.Cir.State, h: D.HE(ds, u, s, st)) -> D.HE(ds, t, s, st):
  match h:
    case Inl{x}:
      (e0, r) = x
      (+k, ek) = r
      Inl{(e0, (1n+k, step.res(k, ds, t, u, Some{List.reverse(&2, Word(8n), D.St.out(st))}, es, ek)))}
    case Inr{x}:
      (e2, g) = x
      Inr{(e2, k => he.all(k, ds, t, u, es, g))}

# after a round that goes on: the loop from the next state, by ia after an
# admin move and by ist after a step
def loop.next(+p: Nat, +ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, +u: Cr.Cir.State,
  +t: Bk.Term, -w: Nat, r: D.Rnd(ds, ks, img, t, w, u),
  +hd: {Fv.Defs.below(ds, U32.to_nat(2147483648)) == True{} : Bool},
  +hfv: {D.Term.below(t, U32.to_nat(2147483648)) == True{} : Bool},
  ia: @w2: Nat -> D.Inv(ds, ks, img, u, t, w2) ->
    D.Post(False{}, Cr.Cir.exec(p, D.B.loop(), u), s => Empty, s => st2 => D.HE(ds, t, s, st2)),
  ist: @v: Bk.Term -> @w2: Nat -> D.Inv(ds, ks, img, u, v, w2) ->
    {D.Term.below(v, U32.to_nat(2147483648)) == True{} : Bool} ->
    D.Post(False{}, Cr.Cir.exec(p, D.B.loop(), u), s => Empty, s => st2 => D.HE(ds, v, s, st2))) ->
  D.Post(False{}, Cr.Cir.exec(p, D.B.loop(), u), s => Empty, s => st2 => D.HE(ds, t, s, st2)):
  match r:
    case Inl{a}:
      (w2, r2) = a
      (inv2, lt) = r2
      ia(w2, inv2)
    case Inr{b}:
      (+v, r2) = b
      (+es, r3) = r2
      (w2, inv2) = r3
      post.wk(False{}, Cr.Cir.exec(p, D.B.loop(), u), s => Empty, s => st2 => D.HE(ds, v, s, st2), s => st2 => D.HE(ds, t, s, st2),
        ist(v, w2, inv2, Fv.fv.step(ds, t, v, U32.to_nat(2147483648), hd, hfv, es)), s => st2 => h => he.step(ds, t, v, es, s, st2, h))

# the main loop, from a state of the invariant of the term t, halts only as
# HE says, with any fuel: by induction on the fuel
def loop.post(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st: Cr.Cir.State,
  +t: Bk.Term, +w: Nat, inv: D.Inv(ds, ks, img, st, t, w),
  +hd: {Fv.Defs.below(ds, U32.to_nat(2147483648)) == True{} : Bool},
  +hfv: {D.Term.below(t, U32.to_nat(2147483648)) == True{} : Bool}) ->
  D.Post(False{}, Cr.Cir.exec(f, D.B.loop(), st), s => Empty, s => st2 => D.HE(ds, t, s, st2)):
  match f:
    case 0n:
      Unit{}
    case 1n+p:
      D.post.then(False{}, Cr.Cir.exec(p, D.B.body(), st), u => Cr.Cir.exec(p, D.B.loop(), u), s => D.Rnd(ds, ks, img, t, w, s),
        s => Empty, s => st2 => D.HR(ds, t, s, st2), s => st2 => D.HE(ds, t, s, st2),
        round.post(p, ds, ks, img, st, t, w, inv, hfv),
        s => st2 => h => he.of(ds, t, s, st2, h),
        +u => r => loop.next(p, ds, ks, img, u, t, w, r, hd, hfv, w2 => i2 => loop.post(p, ds, ks, img, u, t, w2, i2, hd, hfv),
          v => w2 => i2 => hfv2 => loop.post(p, ds, ks, img, u, v, w2, i2, hd, hfv2)))

# The loop reaches what Eval reaches
# ----------------------------------

def good.ends(-o: List<&2, Word(8n)>, r: Cr.Cir.Out, g: D.Good(o, r)) -> D.Ends(r):
  match r:
    case Cr.Cir.Out.next{_}:
      Unit{}
    case Cr.Cir.Out.halt{_, _}:
      Unit{}
    case Cr.Cir.Out.out_of_memory{}:
      Unit{}
    case Cr.Cir.Out.trap{}:
      Unit{}
    case Cr.Cir.Out.not_done{}:
      g

def good.then(-o: List<&2, Word(8n)>, r: Cr.Cir.Out, -k: Cr.Cir.State -> Cr.Cir.Out, g: D.Good(o, r)) ->
  D.Good(o, Cr.Cir.exec.then(r, k)):
  match r:
    case Cr.Cir.Out.next{st}:
      Empty.absurd(D.Good(o, k(st)), g)
    case Cr.Cir.Out.halt{s, st}:
      g
    case Cr.Cir.Out.out_of_memory{}:
      Unit{}
    case Cr.Cir.Out.trap{}:
      g
    case Cr.Cir.Out.not_done{}:
      g

def ends.eq(-a: Cr.Cir.Out, -b: Cr.Cir.Out, e: {a == b : Cr.Cir.Out}, d: D.Ends(b)) -> D.Ends(a):
  %Equal.sym(Cr.Cir.Out, a, b, e) : D.Ends(_)
  d

# a round that halts or runs out of memory with the fuel f0 ends the loop the
# same with 1 + f0
def out.fin(-o: List<&2, Word(8n)>, +f0: Nat, -st: Cr.Cir.State, r: Cr.Cir.Out, er: {Cr.Cir.exec(f0, D.B.body(), st) == r : Cr.Cir.Out},
  g: D.Good(o, r)) -> D.Good(o, Cr.Cir.exec(1n+f0, D.B.loop(), st)):
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f0, D.B.body(), st), r, er) : D.Good(o, Cr.Cir.exec.then(_, u => Cr.Cir.exec(f0, D.B.loop(), u)))
  good.then(o, r, u => Cr.Cir.exec(f0, D.B.loop(), u), g)

# a round that goes on with the fuel f0, then the loop with n1, are the loop
# with 1 + f0 + n1
def next.fin(+o: List<&2, Word(8n)>, +f0: Nat, +n1: Nat, +st: Cr.Cir.State, +u: Cr.Cir.State,
  +er: {Cr.Cir.exec(f0, D.B.body(), st) == Cr.Cir.Out.next{u} : Cr.Cir.Out},
  +g1: D.Good(o, Cr.Cir.exec(n1, D.B.loop(), u))) -> D.Good(o, Cr.Cir.exec(1n+Nat.add(f0, n1), D.B.loop(), st)):
  +n = Nat.add(f0, n1)
  +d0 = ends.eq(Cr.Cir.exec(f0, D.B.body(), st), Cr.Cir.Out.next{u}, er, Unit{})
  +e1 = Equal.trans(Cr.Cir.Out, Cr.Cir.Out.next{u}, Cr.Cir.exec(f0, D.B.body(), st), Cr.Cir.exec(n, D.B.body(), st),
    Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f0, D.B.body(), st), Cr.Cir.Out.next{u}, er),
    D.mono(f0, n, D.B.body(), st, N.le_add_r(f0, n1), d0))
  +e2 = D.mono(n1, n, D.B.loop(), u, N.le_add_l(f0, n1), good.ends(o, Cr.Cir.exec(n1, D.B.loop(), u), g1))
  %e1 : D.Good(o, Cr.Cir.exec.then(_, v => Cr.Cir.exec(n, D.B.loop(), v)))
  %e2 : D.Good(o, _)
  g1

# a round that halts, from a term from which Eval reaches the bytes o: the
# loop gives them
def loop.halt(k: Nat, +ds: List<&2, Bk.Def>, +t: Bk.Term, -s: U32, +st2: Cr.Cir.State, +o: List<&2, Word(8n)>,
  e: {Pg.Program.result(ds, El.Eval.steps(k, ds, t)) == Some{o} : Maybe<&2, List<&2, Word(8n)>>},
  h: D.HR(ds, t, s, st2)) -> D.Good(o, Cr.Cir.Out.halt{s, st2}):
  match k:
    case 0n:
      match h:
        case Inl{x}:
          (e0, r) = x
          (es, er) = r
          (e0, D.mb.inj(List.reverse(&2, Word(8n), D.St.out(st2)), o,
            Equal.trans(Maybe<&2, List<&2, Word(8n)>>, Some{List.reverse(&2, Word(8n), D.St.out(st2))}, Pg.Program.result(ds, Some{t}), Some{o},
              Equal.sym(Maybe<&2, List<&2, Word(8n)>>, Pg.Program.result(ds, Some{t}), Some{List.reverse(&2, Word(8n), D.St.out(st2))}, er), e)))
        case Inr{x}:
          (e2, r) = x
          (es, er) = r
          Empty.absurd(D.Good(o, Cr.Cir.Out.halt{s, st2}), D.mb.ne(o,
            Equal.trans(Maybe<&2, List<&2, Word(8n)>>, None{}, Pg.Program.result(ds, Some{t}), Some{o},
              Equal.sym(Maybe<&2, List<&2, Word(8n)>>, Pg.Program.result(ds, Some{t}), None{}, er), e)))
    case 1n+(+j):
      match h:
        case Inl{x}:
          (e0, r) = x
          (es, er) = r
          Empty.absurd(D.Good(o, Cr.Cir.Out.halt{s, st2}), D.mb.ne(o,
            Equal.trans(Maybe<&2, List<&2, Word(8n)>>, None{}, Pg.Program.result(ds, El.Eval.steps(1n+j, ds, t)), Some{o},
              Equal.sym(Maybe<&2, List<&2, Word(8n)>>, Pg.Program.result(ds, El.Eval.steps(1n+j, ds, t)), None{}, none.after(j, ds, t, es)), e)))
        case Inr{x}:
          (e2, r) = x
          (es, er) = r
          Empty.absurd(D.Good(o, Cr.Cir.Out.halt{s, st2}), D.mb.ne(o,
            Equal.trans(Maybe<&2, List<&2, Word(8n)>>, None{}, Pg.Program.result(ds, El.Eval.steps(1n+j, ds, t)), Some{o},
              Equal.sym(Maybe<&2, List<&2, Word(8n)>>, Pg.Program.result(ds, El.Eval.steps(1n+j, ds, t)), None{}, none.after(j, ds, t, es)), e)))

# a step from a term from which Eval reaches the bytes o at once: none
def loop.step0(+ds: List<&2, Bk.Def>, +t: Bk.Term, +u: Bk.Term, -o: List<&2, Word(8n)>,
  e: {Pg.Program.result(ds, Some{t}) == Some{o} : Maybe<&2, List<&2, Word(8n)>>},
  es: {El.Eval.step(ds, t) == Some{u} : Maybe<Bk.Term>}) -> Empty:
  D.mb.ne(o, Equal.trans(Maybe<&2, List<&2, Word(8n)>>, None{}, Pg.Program.result(ds, Some{t}), Some{o},
    Equal.sym(Maybe<&2, List<&2, Word(8n)>>, Pg.Program.result(ds, Some{t}), None{},
      D.res.nv(ds, t, K.vals.of(El.Eval.vals(ds, t, False{}), ds, t, u, {==}, es))), e))

# when Eval reaches the bytes o from t within k steps, the loop gives them or
# runs out of memory, with some fuel: by induction on k, and on b, above the
# measure of the admin moves; r0 is the round with the fuel f0, that ends
def loop.done(k: Nat, b: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +st: Cr.Cir.State, +t: Bk.Term, +w: Nat, +o: List<&2, Word(8n)>, +hw: N.Le(1n+w, b),
  +e: {Pg.Program.result(ds, El.Eval.steps(k, ds, t)) == Some{o} : Maybe<&2, List<&2, Word(8n)>>},
  +f0: Nat, r0: Cr.Cir.Out, +er: {Cr.Cir.exec(f0, D.B.body(), st) == r0 : Cr.Cir.Out}, d0: D.Ends(r0),
  p0: D.Post(False{}, r0, s => D.Rnd(ds, ks, img, t, w, s), s => st2 => D.HR(ds, t, s, st2)),
  +hd: {Fv.Defs.below(ds, U32.to_nat(2147483648)) == True{} : Bool},
  +hfv: {D.Term.below(t, U32.to_nat(2147483648)) == True{} : Bool}) ->
  D.Ex(Nat, n => D.Good(o, Cr.Cir.exec(n, D.B.loop(), st))):
  match k:
    case 0n:
      match b:
        case 0n:
          Empty.absurd(D.Ex(Nat, n => D.Good(o, Cr.Cir.exec(n, D.B.loop(), st))), hw)
        case 1n+(+c):
          match r0:
            case Cr.Cir.Out.next{+u}:
              match p0:
                case Inl{+a}:
                  +w2 = D.adm.w(ds, ks, img, u, t, w, a)
                  +inv2 = D.adm.inv(ds, ks, img, u, t, w, a)
                  +lt = D.adm.lt(ds, ks, img, u, t, w, a)
                  +rd = round.done(ds, ks, img, u, t, w2, inv2, hfv)
                  +f1 = D.Ex.fst(Nat, f => D.Ends(Cr.Cir.exec(f, D.B.body(), u)), rd)
                  +ld = loop.done(0n, c, ds, ks, img, u, t, w2, o, N.le_trans(1n+w2, w, c, lt, hw), e, f1,
                    Cr.Cir.exec(f1, D.B.body(), u), {==}, D.Ex.snd(Nat, f => D.Ends(Cr.Cir.exec(f, D.B.body(), u)), rd),
                    round.post(f1, ds, ks, img, u, t, w2, inv2, hfv), hd, hfv)
                  +n1 = D.Ex.fst(Nat, n => D.Good(o, Cr.Cir.exec(n, D.B.loop(), u)), ld)
                  (1n+Nat.add(f0, n1), next.fin(o, f0, n1, st, u, er, D.Ex.snd(Nat, n => D.Good(o, Cr.Cir.exec(n, D.B.loop(), u)), ld)))
                case Inr{+x}:
                  +v = D.stp.u(ds, ks, img, u, t, x)
                  +es = D.stp.es(ds, ks, img, u, t, x)
                  +w2 = D.stp.w(ds, ks, img, u, t, x)
                  +inv2 = D.stp.inv(ds, ks, img, u, t, x)
                  Empty.absurd(D.Ex(Nat, n => D.Good(o, Cr.Cir.exec(n, D.B.loop(), st))), loop.step0(ds, t, v, o, e, es))
            case Cr.Cir.Out.halt{+s, +st2}:
              (1n+f0, out.fin(o, f0, st, Cr.Cir.Out.halt{s, st2}, er, loop.halt(0n, ds, t, s, st2, o, e, p0)))
            case Cr.Cir.Out.out_of_memory{}:
              (1n+f0, out.fin(o, f0, st, Cr.Cir.Out.out_of_memory{}, er, Unit{}))
            case Cr.Cir.Out.trap{}:
              Empty.absurd(D.Ex(Nat, n => D.Good(o, Cr.Cir.exec(n, D.B.loop(), st))), p0)
            case Cr.Cir.Out.not_done{}:
              Empty.absurd(D.Ex(Nat, n => D.Good(o, Cr.Cir.exec(n, D.B.loop(), st))), d0)
    case 1n+(+j):
      match b:
        case 0n:
          Empty.absurd(D.Ex(Nat, n => D.Good(o, Cr.Cir.exec(n, D.B.loop(), st))), hw)
        case 1n+(+c):
          match r0:
            case Cr.Cir.Out.next{+u}:
              match p0:
                case Inl{+a}:
                  +w2 = D.adm.w(ds, ks, img, u, t, w, a)
                  +inv2 = D.adm.inv(ds, ks, img, u, t, w, a)
                  +lt = D.adm.lt(ds, ks, img, u, t, w, a)
                  +rd = round.done(ds, ks, img, u, t, w2, inv2, hfv)
                  +f1 = D.Ex.fst(Nat, f => D.Ends(Cr.Cir.exec(f, D.B.body(), u)), rd)
                  +ld = loop.done(1n+j, c, ds, ks, img, u, t, w2, o, N.le_trans(1n+w2, w, c, lt, hw), e, f1,
                    Cr.Cir.exec(f1, D.B.body(), u), {==}, D.Ex.snd(Nat, f => D.Ends(Cr.Cir.exec(f, D.B.body(), u)), rd),
                    round.post(f1, ds, ks, img, u, t, w2, inv2, hfv), hd, hfv)
                  +n1 = D.Ex.fst(Nat, n => D.Good(o, Cr.Cir.exec(n, D.B.loop(), u)), ld)
                  (1n+Nat.add(f0, n1), next.fin(o, f0, n1, st, u, er, D.Ex.snd(Nat, n => D.Good(o, Cr.Cir.exec(n, D.B.loop(), u)), ld)))
                case Inr{+x}:
                  +v = D.stp.u(ds, ks, img, u, t, x)
                  +es = D.stp.es(ds, ks, img, u, t, x)
                  +w2 = D.stp.w(ds, ks, img, u, t, x)
                  +inv2 = D.stp.inv(ds, ks, img, u, t, x)
                  +hfv2 = Fv.fv.step(ds, t, v, U32.to_nat(2147483648), hd, hfv, es)
                  +rd = round.done(ds, ks, img, u, v, w2, inv2, hfv2)
                  +f1 = D.Ex.fst(Nat, f => D.Ends(Cr.Cir.exec(f, D.B.body(), u)), rd)
                  +ld = loop.done(j, 1n+w2, ds, ks, img, u, v, w2, o, N.le_refl(1n+w2), res.step(j, ds, t, v, Some{o}, es, e), f1,
                    Cr.Cir.exec(f1, D.B.body(), u), {==}, D.Ex.snd(Nat, f => D.Ends(Cr.Cir.exec(f, D.B.body(), u)), rd),
                    round.post(f1, ds, ks, img, u, v, w2, inv2, hfv2), hd, hfv2)
                  +n1 = D.Ex.fst(Nat, n => D.Good(o, Cr.Cir.exec(n, D.B.loop(), u)), ld)
                  (1n+Nat.add(f0, n1), next.fin(o, f0, n1, st, u, er, D.Ex.snd(Nat, n => D.Good(o, Cr.Cir.exec(n, D.B.loop(), u)), ld)))
            case Cr.Cir.Out.halt{+s, +st2}:
              (1n+f0, out.fin(o, f0, st, Cr.Cir.Out.halt{s, st2}, er, loop.halt(1n+j, ds, t, s, st2, o, e, p0)))
            case Cr.Cir.Out.out_of_memory{}:
              (1n+f0, out.fin(o, f0, st, Cr.Cir.Out.out_of_memory{}, er, Unit{}))
            case Cr.Cir.Out.trap{}:
              Empty.absurd(D.Ex(Nat, n => D.Good(o, Cr.Cir.exec(n, D.B.loop(), st))), p0)
            case Cr.Cir.Out.not_done{}:
              Empty.absurd(D.Ex(Nat, n => D.Good(o, Cr.Cir.exec(n, D.B.loop(), st))), d0)

# the loop, from a state of the invariant
def loop.start(k: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +st: Cr.Cir.State, +t: Bk.Term, +w: Nat, +o: List<&2, Word(8n)>, +inv: D.Inv(ds, ks, img, st, t, w),
  +e: {Pg.Program.result(ds, El.Eval.steps(k, ds, t)) == Some{o} : Maybe<&2, List<&2, Word(8n)>>},
  +hd: {Fv.Defs.below(ds, U32.to_nat(2147483648)) == True{} : Bool},
  +hfv: {D.Term.below(t, U32.to_nat(2147483648)) == True{} : Bool}) ->
  D.Ex(Nat, n => D.Good(o, Cr.Cir.exec(n, D.B.loop(), st))):
  +rd = round.done(ds, ks, img, st, t, w, inv, hfv)
  +f0 = D.Ex.fst(Nat, f => D.Ends(Cr.Cir.exec(f, D.B.body(), st)), rd)
  loop.done(k, 1n+w, ds, ks, img, st, t, w, o, N.le_refl(1n+w), e, f0, Cr.Cir.exec(f0, D.B.body(), st), {==},
    D.Ex.snd(Nat, f => D.Ends(Cr.Cir.exec(f, D.B.body(), st)), rd), round.post(f0, ds, ks, img, st, t, w, inv, hfv), hd, hfv)

def res.alloced(r: Maybe<&2, U32>, fuel: Nat, prog: Cr.Cir.Stmt, +regs: Nat, +cells: List<&2, Cr.Cir.Cell>, +k: U32,
  +len: U32, +lim: U32, +i: List<&2, Word(8n)>, +m: U32, -P: Wa.Wasm.Outcome -> Type, po: P(Wa.Wasm.Outcome.out_of_memory{}),
  ek: {k == Cr.Wasm.encode.len(Cr.Cir.Cell, cells) : U32},
  em: {U32.is_le(Cr.Cir.pages(Cr.Cir.input.at(k)), m) == True{} : Bool},
  elim: {lim == Wa.Wasm.min(m, 65536) : U32},
  el: {Wa.Wasm.length32(i) == Some{len} : Maybe<&2, U32>},
  er: {Cr.Cir.alloc.pages(k, len, Cr.Cir.pages(Cr.Cir.input.at(k)), lim) == r : Maybe<&2, U32>},
  g: @k2: U32 -> @len2: U32 -> @p2: U32 -> @lim2: U32 -> @first2: U32 -> D.Start(cells, i, m, k2, len2, p2, lim2, first2) ->
    P(Cr.Cir.ended(Cr.Cir.exec(fuel, prog, D.St0(regs, cells, first2, k2, p2, lim2, i))))) ->
  P(Cr.Cir.result.alloced(r, fuel, prog, regs, cells, k, U32.add(Cr.Cir.input.at(k), len), lim, i)):
  match r:
    case None{}:
      po
    case Some{+p}:
      g(k, len, p, lim, Cr.Cir.first(k, U32.add(Cr.Cir.input.at(k), len)), (ek, (em, (elim, (el, (er, {==}))))))

def res.sized(nl: Maybe<&2, U32>, fuel: Nat, prog: Cr.Cir.Stmt, +regs: Nat, +cells: List<&2, Cr.Cir.Cell>, +k: U32,
  +lim: U32, +i: List<&2, Word(8n)>, +m: U32, -P: Wa.Wasm.Outcome -> Type, po: P(Wa.Wasm.Outcome.out_of_memory{}),
  ek: {k == Cr.Wasm.encode.len(Cr.Cir.Cell, cells) : U32},
  em: {U32.is_le(Cr.Cir.pages(Cr.Cir.input.at(k)), m) == True{} : Bool},
  elim: {lim == Wa.Wasm.min(m, 65536) : U32},
  el: {Wa.Wasm.length32(i) == nl : Maybe<&2, U32>},
  g: @k2: U32 -> @len2: U32 -> @p2: U32 -> @lim2: U32 -> @first2: U32 -> D.Start(cells, i, m, k2, len2, p2, lim2, first2) ->
    P(Cr.Cir.ended(Cr.Cir.exec(fuel, prog, D.St0(regs, cells, first2, k2, p2, lim2, i))))) ->
  P(Cr.Cir.result.sized(nl, fuel, prog, regs, cells, k, Cr.Cir.pages(Cr.Cir.input.at(k)), lim, i)):
  match nl:
    case None{}:
      po
    case Some{+len}:
      res.alloced(Cr.Cir.alloc.pages(k, len, Cr.Cir.pages(Cr.Cir.input.at(k)), lim), fuel, prog, regs, cells, k, len, lim, i, m,
        P, po, ek, em, elim, el, {==}, g)

def res.memory(ok: Bool, fuel: Nat, prog: Cr.Cir.Stmt, +regs: Nat, +cells: List<&2, Cr.Cir.Cell>, +k: U32,
  +lim: U32, +i: List<&2, Word(8n)>, +m: U32, -P: Wa.Wasm.Outcome -> Type, po: P(Wa.Wasm.Outcome.out_of_memory{}),
  ek: {k == Cr.Wasm.encode.len(Cr.Cir.Cell, cells) : U32},
  em: {U32.is_le(Cr.Cir.pages(Cr.Cir.input.at(k)), m) == ok : Bool},
  elim: {lim == Wa.Wasm.min(m, 65536) : U32},
  g: @k2: U32 -> @len2: U32 -> @p2: U32 -> @lim2: U32 -> @first2: U32 -> D.Start(cells, i, m, k2, len2, p2, lim2, first2) ->
    P(Cr.Cir.ended(Cr.Cir.exec(fuel, prog, D.St0(regs, cells, first2, k2, p2, lim2, i))))) ->
  P(Cr.Cir.result.memory(ok, fuel, prog, regs, cells, k, Cr.Cir.pages(Cr.Cir.input.at(k)), lim, i)):
  match ok:
    case False{}:
      po
    case True{}:
      res.sized(Wa.Wasm.length32(i), fuel, prog, regs, cells, k, lim, i, m, P, po, ek, em, elim, {==}, g)

# what holds of every run from the start, and of out of memory, holds of
# Cir.result
def res.on(fuel: Nat, prog: Cr.Cir.Stmt, +regs: Nat, +cells: List<&2, Cr.Cir.Cell>, +i: List<&2, Word(8n)>, +m: U32,
  -P: Wa.Wasm.Outcome -> Type, po: P(Wa.Wasm.Outcome.out_of_memory{}),
  g: @k2: U32 -> @len2: U32 -> @p2: U32 -> @lim2: U32 -> @first2: U32 -> D.Start(cells, i, m, k2, len2, p2, lim2, first2) ->
    P(Cr.Cir.ended(Cr.Cir.exec(fuel, prog, D.St0(regs, cells, first2, k2, p2, lim2, i))))) ->
  P(Cr.Cir.result(fuel, prog, regs, cells, i, m)):
  res.memory(U32.is_le(Cr.Cir.pages(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), m), fuel, prog, regs, cells,
    Cr.Wasm.encode.len(Cr.Cir.Cell, cells), Wa.Wasm.min(m, 65536), i, m, P, po, {==}, {==}, {==}, g)

def rex.alloced(r: Maybe<&2, U32>, prog: Cr.Cir.Stmt, +regs: Nat, +cells: List<&2, Cr.Cir.Cell>, +k: U32,
  +len: U32, +lim: U32, +i: List<&2, Word(8n)>, +m: U32, -P: Wa.Wasm.Outcome -> Type, po: P(Wa.Wasm.Outcome.out_of_memory{}),
  ek: {k == Cr.Wasm.encode.len(Cr.Cir.Cell, cells) : U32},
  em: {U32.is_le(Cr.Cir.pages(Cr.Cir.input.at(k)), m) == True{} : Bool},
  elim: {lim == Wa.Wasm.min(m, 65536) : U32},
  el: {Wa.Wasm.length32(i) == Some{len} : Maybe<&2, U32>},
  er: {Cr.Cir.alloc.pages(k, len, Cr.Cir.pages(Cr.Cir.input.at(k)), lim) == r : Maybe<&2, U32>},
  g: @k2: U32 -> @len2: U32 -> @p2: U32 -> @lim2: U32 -> @first2: U32 -> D.Start(cells, i, m, k2, len2, p2, lim2, first2) ->
    &n: Nat -> P(Cr.Cir.ended(Cr.Cir.exec(n, prog, D.St0(regs, cells, first2, k2, p2, lim2, i))))) ->
  &n: Nat -> P(Cr.Cir.result.alloced(r, n, prog, regs, cells, k, U32.add(Cr.Cir.input.at(k), len), lim, i)):
  match r:
    case None{}:
      (0n, po)
    case Some{+p}:
      g(k, len, p, lim, Cr.Cir.first(k, U32.add(Cr.Cir.input.at(k), len)), (ek, (em, (elim, (el, (er, {==}))))))

def rex.sized(nl: Maybe<&2, U32>, prog: Cr.Cir.Stmt, +regs: Nat, +cells: List<&2, Cr.Cir.Cell>, +k: U32,
  +lim: U32, +i: List<&2, Word(8n)>, +m: U32, -P: Wa.Wasm.Outcome -> Type, po: P(Wa.Wasm.Outcome.out_of_memory{}),
  ek: {k == Cr.Wasm.encode.len(Cr.Cir.Cell, cells) : U32},
  em: {U32.is_le(Cr.Cir.pages(Cr.Cir.input.at(k)), m) == True{} : Bool},
  elim: {lim == Wa.Wasm.min(m, 65536) : U32},
  el: {Wa.Wasm.length32(i) == nl : Maybe<&2, U32>},
  g: @k2: U32 -> @len2: U32 -> @p2: U32 -> @lim2: U32 -> @first2: U32 -> D.Start(cells, i, m, k2, len2, p2, lim2, first2) ->
    &n: Nat -> P(Cr.Cir.ended(Cr.Cir.exec(n, prog, D.St0(regs, cells, first2, k2, p2, lim2, i))))) ->
  &n: Nat -> P(Cr.Cir.result.sized(nl, n, prog, regs, cells, k, Cr.Cir.pages(Cr.Cir.input.at(k)), lim, i)):
  match nl:
    case None{}:
      (0n, po)
    case Some{+len}:
      rex.alloced(Cr.Cir.alloc.pages(k, len, Cr.Cir.pages(Cr.Cir.input.at(k)), lim), prog, regs, cells, k, len, lim, i, m,
        P, po, ek, em, elim, el, {==}, g)

def rex.memory(ok: Bool, prog: Cr.Cir.Stmt, +regs: Nat, +cells: List<&2, Cr.Cir.Cell>, +k: U32,
  +lim: U32, +i: List<&2, Word(8n)>, +m: U32, -P: Wa.Wasm.Outcome -> Type, po: P(Wa.Wasm.Outcome.out_of_memory{}),
  ek: {k == Cr.Wasm.encode.len(Cr.Cir.Cell, cells) : U32},
  em: {U32.is_le(Cr.Cir.pages(Cr.Cir.input.at(k)), m) == ok : Bool},
  elim: {lim == Wa.Wasm.min(m, 65536) : U32},
  g: @k2: U32 -> @len2: U32 -> @p2: U32 -> @lim2: U32 -> @first2: U32 -> D.Start(cells, i, m, k2, len2, p2, lim2, first2) ->
    &n: Nat -> P(Cr.Cir.ended(Cr.Cir.exec(n, prog, D.St0(regs, cells, first2, k2, p2, lim2, i))))) ->
  &n: Nat -> P(Cr.Cir.result.memory(ok, n, prog, regs, cells, k, Cr.Cir.pages(Cr.Cir.input.at(k)), lim, i)):
  match ok:
    case False{}:
      (0n, po)
    case True{}:
      rex.sized(Wa.Wasm.length32(i), prog, regs, cells, k, lim, i, m, P, po, ek, em, elim, {==}, g)

# a fuel for each run from the start gives one for Cir.result, which runs out
# of memory or runs from the same start with any fuel
def res.ex(prog: Cr.Cir.Stmt, +regs: Nat, +cells: List<&2, Cr.Cir.Cell>, +i: List<&2, Word(8n)>, +m: U32,
  -P: Wa.Wasm.Outcome -> Type, po: P(Wa.Wasm.Outcome.out_of_memory{}),
  g: @k2: U32 -> @len2: U32 -> @p2: U32 -> @lim2: U32 -> @first2: U32 -> D.Start(cells, i, m, k2, len2, p2, lim2, first2) ->
    &n: Nat -> P(Cr.Cir.ended(Cr.Cir.exec(n, prog, D.St0(regs, cells, first2, k2, p2, lim2, i))))) ->
  &n: Nat -> P(Cr.Cir.result(n, prog, regs, cells, i, m)):
  rex.memory(U32.is_le(Cr.Cir.pages(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), m), prog, regs, cells,
    Cr.Wasm.encode.len(Cr.Cir.Cell, cells), Wa.Wasm.min(m, 65536), i, m, P, po, {==}, {==}, {==}, g)

# The machine gives what Eval gives
# ---------------------------------

def run.loop(+n: Nat, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +st2: Cr.Cir.State,
  q: D.Ex(Nat, w => D.Inv(ds, T.tm.names(ds), T.tm.img(ds), st2, Pg.Program.start(i), w)),
  +hd: {Fv.Defs.below(ds, U32.to_nat(2147483648)) == True{} : Bool}) ->
  D.Post(False{}, Cr.Cir.exec(n, Cr.Cir.Stmt.seq{D.B.loop(), Cr.Cir.Stmt.nop{}}, st2), st => Unit,
    s2 => st3 => D.HE(ds, Pg.Program.start(i), s2, st3)):
  (w, inv) = q
  D.post.seq(n, False{}, D.B.loop(), Cr.Cir.Stmt.nop{}, st2, s => Empty, s => Unit, s2 => st3 => D.HE(ds, Pg.Program.start(i), s2, st3),
    s2 => st3 => D.HE(ds, Pg.Program.start(i), s2, st3),
    loop.post(n, ds, T.tm.names(ds), T.tm.img(ds), st2, Pg.Program.start(i), w, inv, hd, fv.start.big(i, U32.to_nat(2147483648))),
    s2 => st3 => h => h, st3 => h => Empty.absurd(D.Post(False{}, Cr.Cir.exec(n, Cr.Cir.Stmt.nop{}, st3), s => Unit,
      s2 => st4 => D.HE(ds, Pg.Program.start(i), s2, st4)), h))

def run.rest(+n: Nat, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +st1: Cr.Cir.State, q1: D.InvIn(ds, i, st1),
  +hd: {Fv.Defs.below(ds, U32.to_nat(2147483648)) == True{} : Bool}) ->
  D.Post(False{}, Cr.Cir.exec(n, D.B.rest(), st1), st => Unit, s2 => st2 => D.HE(ds, Pg.Program.start(i), s2, st2)):
  (len, q0) = q1
  (_, ex) = q0
  D.post.seq(n, False{}, Mc.M.set(Mc.R.mode(), Mc.M.c(0)), Cr.Cir.Stmt.seq{D.B.loop(), Cr.Cir.Stmt.nop{}}, st1,
    st2 => D.Ex(Nat, w => D.Inv(ds, T.tm.names(ds), T.tm.img(ds), st2, Pg.Program.start(i), w)), st => Unit,
    s2 => st2 => Empty, s2 => st2 => D.HE(ds, Pg.Program.start(i), s2, st2),
    (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec(n, Mc.M.set(Mc.R.mode(), Mc.M.c(0)), st1), Cr.Cir.Out.next{D.Mode0(st1)}, D.setmode(n, st1, len)) :
      D.Post(False{}, _, st2 => D.Ex(Nat, w => D.Inv(ds, T.tm.names(ds), T.tm.img(ds), st2, Pg.Program.start(i), w)), s2 => st2 => Empty);
     ex),
    s2 => st2 => h => Empty.absurd(D.HE(ds, Pg.Program.start(i), s2, st2), h),
    st2 => q2 => run.loop(n, ds, i, st2, q2, hd))

# input.post as the loop takes it: Post, out of memory with no budget
def input.post.p(+f: Nat, +p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +m: U32, +k: U32, +len: U32,
  +pg: U32, +lim: U32, +first: U32,
  rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  small: {Mc.Img.small(p, 0) == True{} : Bool},
  s: D.Start(Mc.Img.cells(ds), i, m, k, len, pg, lim, first)) ->
  D.Post(False{}, Cr.Cir.exec(f, Mc.M.input(), D.St0(Mc.Mach.regs(), Mc.Img.cells(ds), first, k, pg, lim, i)),
    st => D.InvIn(ds, i, st), s2 => st2 => Empty):
  D.postb.post(False{}, Cr.Cir.exec(f, Mc.M.input(), D.St0(Mc.Mach.regs(), Mc.Img.cells(ds), first, k, pg, lim, i)),
    st => D.InvIn(ds, i, st), st => D.InvIn(ds, i, st), s2 => st2 => Empty,
    D.Cells.bytes(first, 1n+Nat.mul(27n, List.length(&2, Word(8n), i))), lim,
    K.input.post(f, p, ds, i, m, k, len, pg, lim, first, rd, small, s), st => h => h)

# a run of Mach.code from the start halts only as HE says, from Program.start
def run.post(+n: Nat, +p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +m: U32, +k: U32, +len: U32,
  +pg: U32, +lim: U32, +first: U32,
  +rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  +small: {Mc.Img.small(p, 0) == True{} : Bool},
  s: D.Start(Mc.Img.cells(ds), i, m, k, len, pg, lim, first)) ->
  D.Post(False{}, Cr.Cir.exec(n, Mc.Mach.code(), D.St0(Mc.Mach.regs(), Mc.Img.cells(ds), first, k, pg, lim, i)), st => Unit,
    s2 => st2 => D.HE(ds, Pg.Program.start(i), s2, st2)):
  +hd = Rb.Gx.read.below(p, ds, rd, small)
  D.post.seq(n, False{}, Mc.M.input(), D.B.rest(), D.St0(Mc.Mach.regs(), Mc.Img.cells(ds), first, k, pg, lim, i),
    st => D.InvIn(ds, i, st), st => Unit, s2 => st2 => Empty, s2 => st2 => D.HE(ds, Pg.Program.start(i), s2, st2),
    input.post.p(n, p, ds, i, m, k, len, pg, lim, first, rd, small, s),
    s2 => st2 => h => Empty.absurd(D.HE(ds, Pg.Program.start(i), s2, st2), h),
    st1 => q1 => run.rest(n, ds, i, st1, q1, hd))

# the outcomes that are no trap
def oc.nt(x: Wa.Wasm.Outcome) -> Type:
  match x:
    case Wa.Wasm.Outcome.result{_}:
      Unit
    case Wa.Wasm.Outcome.out_of_memory{}:
      Unit
    case Wa.Wasm.Outcome.no_result{}:
      Unit
    case Wa.Wasm.Outcome.unsupported{}:
      Unit
    case Wa.Wasm.Outcome.trap{}:
      Empty
    case Wa.Wasm.Outcome.not_done{}:
      Unit

# the outcomes that are no result
def oc.nr(x: Wa.Wasm.Outcome) -> Type:
  match x:
    case Wa.Wasm.Outcome.result{_}:
      Empty
    case Wa.Wasm.Outcome.out_of_memory{}:
      Unit
    case Wa.Wasm.Outcome.no_result{}:
      Unit
    case Wa.Wasm.Outcome.unsupported{}:
      Unit
    case Wa.Wasm.Outcome.trap{}:
      Unit
    case Wa.Wasm.Outcome.not_done{}:
      Unit

def oc.get(x: Wa.Wasm.Outcome, d: List<&2, Word(8n)>) -> List<&2, Word(8n)>:
  match x:
    case Wa.Wasm.Outcome.result{y}:
      y
    case _:
      d

# result is one to one
def oc.inj(+a: List<&2, Word(8n)>, -b: List<&2, Word(8n)>, e: {Wa.Wasm.Outcome.result{a} == Wa.Wasm.Outcome.result{b} : Wa.Wasm.Outcome}) ->
  {a == b : List<&2, Word(8n)>}:
  Equal.cong(Wa.Wasm.Outcome, List<&2, Word(8n)>, x => oc.get(x, a), Wa.Wasm.Outcome.result{a}, Wa.Wasm.Outcome.result{b}, e)

# a run that halts with 0 gives its output as the host reads it
def ended0(-s: U32, -fits: Bool, +out: List<&2, Word(8n)>, e0: {s == 0 : U32}) ->
  {Cr.Cir.ended.halt(U32.is_eq(s, 0), U32.is_eq(s, 1), U32.is_eq(s, 2), fits, out) == Cr.Cir.ended.output(fits, out) : Wa.Wasm.Outcome}:
  %Equal.sym(U32, s, 0, e0) : {Cr.Cir.ended.halt(U32.is_eq(_, 0), U32.is_eq(_, 1), U32.is_eq(_, 2), fits, out) == Cr.Cir.ended.output(fits, out) : Wa.Wasm.Outcome}
  {==}

# a run that halts with 2 gives no result
def ended2(-s: U32, -fits: Bool, +out: List<&2, Word(8n)>, e2: {s == 2 : U32}) ->
  {Cr.Cir.ended.halt(U32.is_eq(s, 0), U32.is_eq(s, 1), U32.is_eq(s, 2), fits, out) == Wa.Wasm.Outcome.no_result{} : Wa.Wasm.Outcome}:
  %Equal.sym(U32, s, 2, e2) : {Cr.Cir.ended.halt(U32.is_eq(_, 0), U32.is_eq(_, 1), U32.is_eq(_, 2), fits, out) == Wa.Wasm.Outcome.no_result{} : Wa.Wasm.Outcome}
  {==}

# an output that the host reads as the result x is its bytes: one that does
# not fit gives a trap
def output.inj(fits: Bool, +out: List<&2, Word(8n)>, -x: List<&2, Word(8n)>,
  e: {Cr.Cir.ended.output(fits, out) == Wa.Wasm.Outcome.result{x} : Wa.Wasm.Outcome}) ->
  {List.reverse(&2, Word(8n), out) == x : List<&2, Word(8n)>}:
  match fits:
    case True{}:
      oc.inj(List.reverse(&2, Word(8n), out), x, e)
    case False{}:
      Empty.absurd({List.reverse(&2, Word(8n), out) == x : List<&2, Word(8n)>}, (%e : oc.nr(_); Unit{}))

# at halt 0, the output fits in the memory, as the host checks (Cir.ended)
def HaltFits(o: Cr.Cir.Out) -> Type:
  match o:
    case Cr.Cir.Out.halt{s, Cr.Cir.State{_, _, nx, _, _, pg, _, _, _, on}}:
      {s == 0 : U32} -> {Wa.Wasm.fits(pg, Cr.Cir.at(nx), on) == True{} : Bool}
    case _:
      Unit

# an outcome that fits (CF.FitsOut) has its output in the memory at halt 0
def halt.fits(o: Cr.Cir.Out, h: CF.FitsOut(o)) -> HaltFits(o):
  match o:
    case Cr.Cir.Out.next{st}:
      Unit{}
    case Cr.Cir.Out.halt{s, Cr.Cir.State{rg, m, +nx, fi, im, +pg, lim, inp, out, +on}}:
      e0 => CF.fits.wasm(nx, pg, on, h)
    case Cr.Cir.Out.out_of_memory{}:
      Unit{}
    case Cr.Cir.Out.trap{}:
      Unit{}
    case Cr.Cir.Out.not_done{}:
      Unit{}

# a run of Mach.code from the start has its output in the memory at halt 0:
# the start's pend register holds 0, so the run fits (CF.fits.code), and what
# fits passes the host's check (CF.fits.wasm, in halt.fits)
def code.fits(+n: Nat, +cells: List<&2, Cr.Cir.Cell>, +first: U32, +k: U32, +pg: U32, +lim: U32, +i: List<&2, Word(8n)>) ->
  HaltFits(Cr.Cir.exec(n, Mc.Mach.code(), D.St0(Mc.Mach.regs(), cells, first, k, pg, lim, i))):
  halt.fits(Cr.Cir.exec(n, Mc.Mach.code(), D.St0(Mc.Mach.regs(), cells, first, k, pg, lim, i)),
    CF.fits.code(n, D.St0(Mc.Mach.regs(), cells, first, k, pg, lim, i), {==}))

# a run that halts only as HE says, with its output in the memory at halt 0,
# never traps
def safe.end(o: Cr.Cir.Out, -ds: List<&2, Bk.Def>, -t: Bk.Term,
  h: D.Post(False{}, o, st => Unit, s => st2 => D.HE(ds, t, s, st2)), hf: HaltFits(o)) ->
  {Cr.Cir.ended(o) != Wa.Wasm.Outcome.trap{} : Wa.Wasm.Outcome}:
  match o:
    case Cr.Cir.Out.next{st}:
      e => (%e : oc.nt(_); Unit{})
    case Cr.Cir.Out.halt{s, Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, +out, outn}}:
      match h:
        case Inl{x}:
          (+e0, r) = x
          %Equal.sym(Wa.Wasm.Outcome, Cr.Cir.ended.halt(U32.is_eq(s, 0), U32.is_eq(s, 1), U32.is_eq(s, 2), Wa.Wasm.fits(pg, Cr.Cir.at(nx), outn), out),
            Cr.Cir.ended.output(Wa.Wasm.fits(pg, Cr.Cir.at(nx), outn), out), ended0(s, Wa.Wasm.fits(pg, Cr.Cir.at(nx), outn), out, e0)) :
            {_ != Wa.Wasm.Outcome.trap{} : Wa.Wasm.Outcome}
          %Equal.sym(Bool, Wa.Wasm.fits(pg, Cr.Cir.at(nx), outn), True{}, hf(e0)) : {Cr.Cir.ended.output(_, out) != Wa.Wasm.Outcome.trap{} : Wa.Wasm.Outcome}
          e => (%e : oc.nt(_); Unit{})
        case Inr{x}:
          (e2, r) = x
          %Equal.sym(Wa.Wasm.Outcome, Cr.Cir.ended.halt(U32.is_eq(s, 0), U32.is_eq(s, 1), U32.is_eq(s, 2), Wa.Wasm.fits(pg, Cr.Cir.at(nx), outn), out),
            Wa.Wasm.Outcome.no_result{}, ended2(s, Wa.Wasm.fits(pg, Cr.Cir.at(nx), outn), out, e2)) : {_ != Wa.Wasm.Outcome.trap{} : Wa.Wasm.Outcome}
          e => (%e : oc.nt(_); Unit{})
    case Cr.Cir.Out.out_of_memory{}:
      e => (%e : oc.nt(_); Unit{})
    case Cr.Cir.Out.trap{}:
      Empty.absurd({Wa.Wasm.Outcome.trap{} != Wa.Wasm.Outcome.trap{} : Wa.Wasm.Outcome}, h)
    case Cr.Cir.Out.not_done{}:
      e => (%e : oc.nt(_); Unit{})

# a result of a run that halts only as HE says is one that Eval reaches
def sound.end(o: Cr.Cir.Out, +ds: List<&2, Bk.Def>, +t: Bk.Term, +x: List<&2, Word(8n)>,
  h: D.Post(False{}, o, st => Unit, s => st2 => D.HE(ds, t, s, st2)),
  e: {Cr.Cir.ended(o) == Wa.Wasm.Outcome.result{x} : Wa.Wasm.Outcome}) ->
  &k: Nat -> {Pg.Program.result(ds, El.Eval.steps(k, ds, t)) == Some{x} : Maybe<&2, List<&2, Word(8n)>>}:
  match o:
    case Cr.Cir.Out.next{st}:
      Empty.absurd(&k: Nat -> {Pg.Program.result(ds, El.Eval.steps(k, ds, t)) == Some{x} : Maybe<&2, List<&2, Word(8n)>>},
        (%e : oc.nr(_); Unit{}))
    case Cr.Cir.Out.halt{s, Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, +out, outn}}:
      match h:
        case Inl{y}:
          (e0, r) = y
          (+k, ek) = r
          +rx = output.inj(Wa.Wasm.fits(pg, Cr.Cir.at(nx), outn), out, x,
            Equal.trans(Wa.Wasm.Outcome, Cr.Cir.ended.output(Wa.Wasm.fits(pg, Cr.Cir.at(nx), outn), out),
              Cr.Cir.ended.halt(U32.is_eq(s, 0), U32.is_eq(s, 1), U32.is_eq(s, 2), Wa.Wasm.fits(pg, Cr.Cir.at(nx), outn), out), Wa.Wasm.Outcome.result{x},
              Equal.sym(Wa.Wasm.Outcome, Cr.Cir.ended.halt(U32.is_eq(s, 0), U32.is_eq(s, 1), U32.is_eq(s, 2), Wa.Wasm.fits(pg, Cr.Cir.at(nx), outn), out),
                Cr.Cir.ended.output(Wa.Wasm.fits(pg, Cr.Cir.at(nx), outn), out), ended0(s, Wa.Wasm.fits(pg, Cr.Cir.at(nx), outn), out, e0)), e))
          (k, (%rx :
            {Pg.Program.result(ds, El.Eval.steps(k, ds, t)) == Some{_} : Maybe<&2, List<&2, Word(8n)>>}; ek))
        case Inr{y}:
          (e2, g) = y
          Empty.absurd(&k: Nat -> {Pg.Program.result(ds, El.Eval.steps(k, ds, t)) == Some{x} : Maybe<&2, List<&2, Word(8n)>>},
            (%Equal.trans(Wa.Wasm.Outcome, Wa.Wasm.Outcome.no_result{},
              Cr.Cir.ended.halt(U32.is_eq(s, 0), U32.is_eq(s, 1), U32.is_eq(s, 2), Wa.Wasm.fits(pg, Cr.Cir.at(nx), outn), out), Wa.Wasm.Outcome.result{x},
              Equal.sym(Wa.Wasm.Outcome, Cr.Cir.ended.halt(U32.is_eq(s, 0), U32.is_eq(s, 1), U32.is_eq(s, 2), Wa.Wasm.fits(pg, Cr.Cir.at(nx), outn), out),
                Wa.Wasm.Outcome.no_result{}, ended2(s, Wa.Wasm.fits(pg, Cr.Cir.at(nx), outn), out, e2)), e) : oc.nr(_); Unit{}))
    case Cr.Cir.Out.out_of_memory{}:
      Empty.absurd(&k: Nat -> {Pg.Program.result(ds, El.Eval.steps(k, ds, t)) == Some{x} : Maybe<&2, List<&2, Word(8n)>>},
        (%e : oc.nr(_); Unit{}))
    case Cr.Cir.Out.trap{}:
      Empty.absurd(&k: Nat -> {Pg.Program.result(ds, El.Eval.steps(k, ds, t)) == Some{x} : Maybe<&2, List<&2, Word(8n)>>}, h)
    case Cr.Cir.Out.not_done{}:
      Empty.absurd(&k: Nat -> {Pg.Program.result(ds, El.Eval.steps(k, ds, t)) == Some{x} : Maybe<&2, List<&2, Word(8n)>>},
        (%e : oc.nr(_); Unit{}))

# a run that gives the bytes o, or runs out of memory, ends so, when its
# output is in the memory at halt 0
def good.end(+o: List<&2, Word(8n)>, r: Cr.Cir.Out, g: D.Good(o, r), hf: HaltFits(r)) ->
  Or({Cr.Cir.ended(r) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome}, {Cr.Cir.ended(r) == Wa.Wasm.Outcome.out_of_memory{} : Wa.Wasm.Outcome}):
  match r:
    case Cr.Cir.Out.next{st}:
      Empty.absurd(Or({Wa.Wasm.Outcome.no_result{} == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome},
        {Wa.Wasm.Outcome.no_result{} == Wa.Wasm.Outcome.out_of_memory{} : Wa.Wasm.Outcome}), g)
    case Cr.Cir.Out.halt{s, Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, +out, outn}}:
      (+e0, eo) = g
      Inl{Equal.trans(Wa.Wasm.Outcome, Cr.Cir.ended.halt(U32.is_eq(s, 0), U32.is_eq(s, 1), U32.is_eq(s, 2), Wa.Wasm.fits(pg, Cr.Cir.at(nx), outn), out),
        Cr.Cir.ended.output(Wa.Wasm.fits(pg, Cr.Cir.at(nx), outn), out), Wa.Wasm.Outcome.result{o}, ended0(s, Wa.Wasm.fits(pg, Cr.Cir.at(nx), outn), out, e0),
        (%Equal.sym(Bool, Wa.Wasm.fits(pg, Cr.Cir.at(nx), outn), True{}, hf(e0)) : {Cr.Cir.ended.output(_, out) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome};
          Equal.cong(List<&2, Word(8n)>, Wa.Wasm.Outcome, y => Wa.Wasm.Outcome.result{y}, List.reverse(&2, Word(8n), out), o, eo)))}
    case Cr.Cir.Out.out_of_memory{}:
      Inr{{==}}
    case Cr.Cir.Out.trap{}:
      Empty.absurd(Or({Wa.Wasm.Outcome.trap{} == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome},
        {Wa.Wasm.Outcome.trap{} == Wa.Wasm.Outcome.out_of_memory{} : Wa.Wasm.Outcome}), g)
    case Cr.Cir.Out.not_done{}:
      Empty.absurd(Or({Wa.Wasm.Outcome.not_done{} == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome},
        {Wa.Wasm.Outcome.not_done{} == Wa.Wasm.Outcome.out_of_memory{} : Wa.Wasm.Outcome}), g)

# M.input with the fuel f1, then the loop with n2, are Mach.code with
# 1 + f1 + n2
def run.fin(+o: List<&2, Word(8n)>, +f1: Nat, +n2: Nat, +st0: Cr.Cir.State, +st1: Cr.Cir.State,
  +er1: {Cr.Cir.exec(f1, Mc.M.input(), st0) == Cr.Cir.Out.next{st1} : Cr.Cir.Out},
  +len: {List.length(&2, U32, D.St.regs(st1)) == 63n : Nat},
  +g2: D.Good(o, Cr.Cir.exec(n2, D.B.loop(), D.Mode0(st1)))) -> D.Good(o, Cr.Cir.exec(1n+Nat.add(f1, n2), Mc.Mach.code(), st0)):
  +n = {1n+Nat.add(f1, n2) : Nat}
  +d1 = ends.eq(Cr.Cir.exec(f1, Mc.M.input(), st0), Cr.Cir.Out.next{st1}, er1, Unit{})
  +e1 = Equal.trans(Cr.Cir.Out, Cr.Cir.Out.next{st1}, Cr.Cir.exec(f1, Mc.M.input(), st0), Cr.Cir.exec(n, Mc.M.input(), st0),
    Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f1, Mc.M.input(), st0), Cr.Cir.Out.next{st1}, er1),
    D.mono(f1, n, Mc.M.input(), st0, N.le_succ(f1, Nat.add(f1, n2), N.le_add_r(f1, n2)), d1))
  +e2 = Equal.sym(Cr.Cir.Out, Cr.Cir.exec(n, Mc.M.set(Mc.R.mode(), Mc.M.c(0)), st1), Cr.Cir.Out.next{D.Mode0(st1)}, D.setmode(n, st1, len))
  +e3 = D.mono(n2, n, D.B.loop(), D.Mode0(st1), N.le_succ(n2, Nat.add(f1, n2), N.le_add_l(f1, n2)),
    good.ends(o, Cr.Cir.exec(n2, D.B.loop(), D.Mode0(st1)), g2))
  %e1 : D.Good(o, Cr.Cir.exec.then(_, s1 => Cr.Cir.exec(n, D.B.rest(), s1)))
  %e2 : D.Good(o, Cr.Cir.exec.then(_, s2 => Cr.Cir.exec(n, Cr.Cir.Stmt.seq{D.B.loop(), Cr.Cir.Stmt.nop{}}, s2)))
  %e3 : D.Good(o, Cr.Cir.exec.then(_, s3 => Cr.Cir.exec(n, Cr.Cir.Stmt.nop{}, s3)))
  good.then(o, Cr.Cir.exec(n2, D.B.loop(), D.Mode0(st1)), s3 => Cr.Cir.exec(n, Cr.Cir.Stmt.nop{}, s3), g2)

# M.input that runs out of memory with the fuel f1 ends Mach.code so with 1 + f1
def oom.fin(-o: List<&2, Word(8n)>, +f1: Nat, +st0: Cr.Cir.State,
  er1: {Cr.Cir.exec(f1, Mc.M.input(), st0) == Cr.Cir.Out.out_of_memory{} : Cr.Cir.Out}) ->
  D.Good(o, Cr.Cir.exec(1n+f1, Mc.Mach.code(), st0)):
  +n = {1n+f1 : Nat}
  +er = er1
  +e1 = Equal.trans(Cr.Cir.Out, Cr.Cir.Out.out_of_memory{}, Cr.Cir.exec(f1, Mc.M.input(), st0), Cr.Cir.exec(n, Mc.M.input(), st0),
    Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f1, Mc.M.input(), st0), Cr.Cir.Out.out_of_memory{}, er),
    D.mono(f1, n, Mc.M.input(), st0, N.le_succ(f1, f1, N.le_refl(f1)), ends.eq(Cr.Cir.exec(f1, Mc.M.input(), st0), Cr.Cir.Out.out_of_memory{}, er, Unit{})))
  %e1 : D.Good(o, Cr.Cir.exec.then(_, s1 => Cr.Cir.exec(n, D.B.rest(), s1)))
  Unit{}

def run.next(k: Nat, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +o: List<&2, Word(8n)>, +f1: Nat, +st0: Cr.Cir.State,
  +st1: Cr.Cir.State, +er1: {Cr.Cir.exec(f1, Mc.M.input(), st0) == Cr.Cir.Out.next{st1} : Cr.Cir.Out},
  +len: {List.length(&2, U32, D.St.regs(st1)) == 63n : Nat}, +w: Nat,
  +inv: D.Inv(ds, T.tm.names(ds), T.tm.img(ds), D.Mode0(st1), Pg.Program.start(i), w),
  +e: {Pg.Program.result(ds, El.Eval.steps(k, ds, Pg.Program.start(i))) == Some{o} : Maybe<&2, List<&2, Word(8n)>>},
  +hd: {Fv.Defs.below(ds, U32.to_nat(2147483648)) == True{} : Bool}) ->
  D.Ex(Nat, n => D.Good(o, Cr.Cir.exec(n, Mc.Mach.code(), st0))):
  +ls = loop.start(k, ds, T.tm.names(ds), T.tm.img(ds), D.Mode0(st1), Pg.Program.start(i), w, o, inv, e, hd, fv.start.big(i, U32.to_nat(2147483648)))
  +n2 = D.Ex.fst(Nat, n => D.Good(o, Cr.Cir.exec(n, D.B.loop(), D.Mode0(st1))), ls)
  (1n+Nat.add(f1, n2), run.fin(o, f1, n2, st0, st1, er1, len, D.Ex.snd(Nat, n => D.Good(o, Cr.Cir.exec(n, D.B.loop(), D.Mode0(st1))), ls)))

def run.done.r(k: Nat, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +o: List<&2, Word(8n)>, +f1: Nat, +st0: Cr.Cir.State,
  r1: Cr.Cir.Out, +er1: {Cr.Cir.exec(f1, Mc.M.input(), st0) == r1 : Cr.Cir.Out}, d1: D.Ends(r1),
  p1: D.Post(False{}, r1, st => D.InvIn(ds, i, st), s2 => st2 => Empty),
  +e: {Pg.Program.result(ds, El.Eval.steps(k, ds, Pg.Program.start(i))) == Some{o} : Maybe<&2, List<&2, Word(8n)>>},
  +hd: {Fv.Defs.below(ds, U32.to_nat(2147483648)) == True{} : Bool}) ->
  D.Ex(Nat, n => D.Good(o, Cr.Cir.exec(n, Mc.Mach.code(), st0))):
  match r1:
    case Cr.Cir.Out.next{+st1}:
      (len, q0) = p1
      (_, q) = q0
      (w, inv) = q
      run.next(k, ds, i, o, f1, st0, st1, er1, len, w, inv, e, hd)
    case Cr.Cir.Out.halt{s, st}:
      Empty.absurd(D.Ex(Nat, n => D.Good(o, Cr.Cir.exec(n, Mc.Mach.code(), st0))), p1)
    case Cr.Cir.Out.out_of_memory{}:
      (1n+f1, oom.fin(o, f1, st0, er1))
    case Cr.Cir.Out.trap{}:
      Empty.absurd(D.Ex(Nat, n => D.Good(o, Cr.Cir.exec(n, Mc.Mach.code(), st0))), p1)
    case Cr.Cir.Out.not_done{}:
      Empty.absurd(D.Ex(Nat, n => D.Good(o, Cr.Cir.exec(n, Mc.Mach.code(), st0))), d1)

# when Eval reaches the bytes o from Program.start(i), a run of Mach.code from
# the start gives them, or runs out of memory, with some fuel
def run.done(k: Nat, +p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +m: U32, +o: List<&2, Word(8n)>, +kk: U32,
  +len: U32, +pg: U32, +lim: U32, +first: U32,
  +rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  +small: {Mc.Img.small(p, 0) == True{} : Bool},
  +s: D.Start(Mc.Img.cells(ds), i, m, kk, len, pg, lim, first),
  +e: {Pg.Program.result(ds, El.Eval.steps(k, ds, Pg.Program.start(i))) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}) ->
  D.Ex(Nat, n => D.Good(o, Cr.Cir.exec(n, Mc.Mach.code(), D.St0(Mc.Mach.regs(), Mc.Img.cells(ds), first, kk, pg, lim, i)))):
  +hd = Rb.Gx.read.below(p, ds, rd, small)
  +st0 = D.St0(Mc.Mach.regs(), Mc.Img.cells(ds), first, kk, pg, lim, i)
  +id = K.input.done(p, ds, i, m, kk, len, pg, lim, first, rd, small, s)
  +f1 = D.Ex.fst(Nat, f => D.Ends(Cr.Cir.exec(f, Mc.M.input(), st0)), id)
  run.done.r(k, ds, i, o, f1, st0, Cr.Cir.exec(f1, Mc.M.input(), st0), {==}, D.Ex.snd(Nat, f => D.Ends(Cr.Cir.exec(f, Mc.M.input(), st0)), id),
    input.post.p(f1, p, ds, i, m, kk, len, pg, lim, first, rd, small, s), e, hd)

def comp.of(k: Nat, +p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +m: U32, +o: List<&2, Word(8n)>, +kk: U32,
  +len: U32, +pg: U32, +lim: U32, +first: U32,
  +rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  +small: {Mc.Img.small(p, 0) == True{} : Bool},
  +s: D.Start(Mc.Img.cells(ds), i, m, kk, len, pg, lim, first),
  +e: {Pg.Program.result(ds, El.Eval.steps(k, ds, Pg.Program.start(i))) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}) ->
  &n: Nat -> Or({Cr.Cir.ended(Cr.Cir.exec(n, Mc.Mach.code(), D.St0(Mc.Mach.regs(), Mc.Img.cells(ds), first, kk, pg, lim, i))) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome},
    {Cr.Cir.ended(Cr.Cir.exec(n, Mc.Mach.code(), D.St0(Mc.Mach.regs(), Mc.Img.cells(ds), first, kk, pg, lim, i))) == Wa.Wasm.Outcome.out_of_memory{} : Wa.Wasm.Outcome}):
  +st0 = D.St0(Mc.Mach.regs(), Mc.Img.cells(ds), first, kk, pg, lim, i)
  +rn = run.done(k, p, ds, i, m, o, kk, len, pg, lim, first, rd, small, s, e)
  +n = D.Ex.fst(Nat, n => D.Good(o, Cr.Cir.exec(n, Mc.Mach.code(), st0)), rn)
  (n, good.end(o, Cr.Cir.exec(n, Mc.Mach.code(), st0), D.Ex.snd(Nat, n => D.Good(o, Cr.Cir.exec(n, Mc.Mach.code(), st0)), rn),
    code.fits(n, Mc.Img.cells(ds), first, kk, pg, lim, i)))

# Layer B
# -------
#
# The lemmas of runs_as_eval.bend, with exactly their types.

# B: the machine never makes an access that its module could not make the
# same way
def mach.safe.proof(
  +p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +m: U32, +n: Nat,
  rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  small: {Mc.Img.small(p, 0) == True{} : Bool}
) -> {Cr.Cir.result(n, Mc.Mach.code(), Mc.Mach.regs(), Mc.Img.cells(ds), i, m) != Wa.Wasm.Outcome.trap{} : Wa.Wasm.Outcome}:
  res.on(n, Mc.Mach.code(), Mc.Mach.regs(), Mc.Img.cells(ds), i, m, x => {x != Wa.Wasm.Outcome.trap{} : Wa.Wasm.Outcome},
    e => (%e : oc.nt(_); Unit{}),
    +kk => +len => +pg => +lim => +first => s =>
      safe.end(Cr.Cir.exec(n, Mc.Mach.code(), D.St0(Mc.Mach.regs(), Mc.Img.cells(ds), first, kk, pg, lim, i)), ds, Pg.Program.start(i),
        run.post(n, p, ds, i, m, kk, len, pg, lim, first, rd, small, s), code.fits(n, Mc.Img.cells(ds), first, kk, pg, lim, i)))

# B: a result of the machine is the list of bytes of a value that Eval reaches
def mach.sound.proof(
  +p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +m: U32, +n: Nat, +o: List<&2, Word(8n)>,
  rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  small: {Mc.Img.small(p, 0) == True{} : Bool},
  e: {Cr.Cir.result(n, Mc.Mach.code(), Mc.Mach.regs(), Mc.Img.cells(ds), i, m) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome}
) -> &k:Nat -> {Pg.Program.result(ds, El.Eval.steps(k, ds, Pg.Program.start(i))) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}:
  res.on(n, Mc.Mach.code(), Mc.Mach.regs(), Mc.Img.cells(ds), i, m,
    x => {x == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome} ->
      &k:Nat -> {Pg.Program.result(ds, El.Eval.steps(k, ds, Pg.Program.start(i))) == Some{o} : Maybe<&2, List<&2, Word(8n)>>},
    e2 => Empty.absurd(&k:Nat -> {Pg.Program.result(ds, El.Eval.steps(k, ds, Pg.Program.start(i))) == Some{o} : Maybe<&2, List<&2, Word(8n)>>},
      (%e2 : oc.nr(_); Unit{})),
    +kk => +len => +pg => +lim => +first => s => e2 =>
      sound.end(Cr.Cir.exec(n, Mc.Mach.code(), D.St0(Mc.Mach.regs(), Mc.Img.cells(ds), first, kk, pg, lim, i)), ds, Pg.Program.start(i), o,
        run.post(n, p, ds, i, m, kk, len, pg, lim, first, rd, small, s), e2), e)

# B: when Eval reaches a list of bytes, the machine gives it, or runs out of
# memory
def mach.complete.proof(
  +p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +m: U32, +k: Nat, +o: List<&2, Word(8n)>,
  rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  small: {Mc.Img.small(p, 0) == True{} : Bool},
  e: {Pg.Program.result(ds, El.Eval.steps(k, ds, Pg.Program.start(i))) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}
) -> &n:Nat -> Or({Cr.Cir.result(n, Mc.Mach.code(), Mc.Mach.regs(), Mc.Img.cells(ds), i, m) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome},
  {Cr.Cir.result(n, Mc.Mach.code(), Mc.Mach.regs(), Mc.Img.cells(ds), i, m) == Wa.Wasm.Outcome.out_of_memory{} : Wa.Wasm.Outcome}):
  res.ex(Mc.Mach.code(), Mc.Mach.regs(), Mc.Img.cells(ds), i, m,
    x => Or({x == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome}, {x == Wa.Wasm.Outcome.out_of_memory{} : Wa.Wasm.Outcome}),
    Inr{{==}},
    +kk => +len => +pg => +lim => +first => s => comp.of(k, p, ds, i, m, o, kk, len, pg, lim, first, rd, small, s, e))

def round.peak.next(-ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>,
  -st: Cr.Cir.State, -t: Bk.Term, -w: Nat, -s: Cr.Cir.State, h: K.MV.next(ds, ks, img, st, t, w, s)) ->
  N.Le(D.Mem.cells(s), Nat.max(D.Mem.cells(st), D.Need(ds, st, t))):
  match h:
    case Tuple{_, Tuple{peak, _}}:
      peak

def round.peak.mv(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +st: Cr.Cir.State, +t: Bk.Term, +w: Nat, h: K.MV(ds, ks, img, st, t, w)) ->
  D.Post(False{}, Cr.Cir.exec(f, D.B.body(), st), s => N.Le(D.Mem.cells(s), Nat.max(D.Mem.cells(st), D.Need(ds, st, t))), s => st2 => Unit):
  match h:
    case Tuple{p, _}:
      post.wk(False{}, Cr.Cir.exec(f, D.B.body(), st), s => N.Le(D.Mem.cells(s), Nat.max(D.Mem.cells(st), D.Need(ds, st, t))),
        s => st2 => D.HR(ds, t, s, st2), s => st2 => Unit,
        D.postb.post(False{}, Cr.Cir.exec(f, D.B.body(), st), s => K.MV.next(ds, ks, img, st, t, w, s),
          s => N.Le(D.Mem.cells(s), Nat.max(D.Mem.cells(st), D.Need(ds, st, t))), s => st2 => D.HR(ds, t, s, st2),
          D.Budget(ds, st, t), D.St.lim(st), p(f), s => r => round.peak.next(ds, ks, img, st, t, w, s, r)),
        s => st2 => r => Unit{})

def round.room.out(o: Cr.Cir.Out, -Q: Cr.Cir.State -> Type, -H: U32 -> Cr.Cir.State -> Type, +b: Nat, +lim: U32,
  h: D.PostB(False{}, o, Q, H, b, lim), room: N.Le(b, D.Lim.bytes(lim))) -> D.NoOom(o):
  match o:
    case Cr.Cir.Out.out_of_memory{}:
      N.not_succ_le(D.Lim.bytes(lim), N.le_trans(1n+D.Lim.bytes(lim), b, D.Lim.bytes(lim), h, room))
    case Cr.Cir.Out.next{_}:
      Unit{}
    case Cr.Cir.Out.halt{_, _}:
      Unit{}
    case Cr.Cir.Out.trap{}:
      Unit{}
    case Cr.Cir.Out.not_done{}:
      Unit{}

def round.room.mv(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +st: Cr.Cir.State, +t: Bk.Term, +w: Nat, h: K.MV(ds, ks, img, st, t, w),
  room: N.Le(D.Budget(ds, st, t), D.Lim.bytes(D.St.lim(st)))) -> D.NoOom(Cr.Cir.exec(f, D.B.body(), st)):
  match h:
    case Tuple{p, _}:
      round.room.out(Cr.Cir.exec(f, D.B.body(), st), s => K.MV.next(ds, ks, img, st, t, w, s),
        s => st2 => D.HR(ds, t, s, st2), D.Budget(ds, st, t), D.St.lim(st), p(f), room)

# Open (U15): a round keeps the machine's own cells within the peak of its
# term and of its step's result (MV's peak)
def round.peak(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +st: Cr.Cir.State, +t: Bk.Term, +w: Nat, inv: D.Inv(ds, ks, img, st, t, w),
  hfv: {D.Term.below(t, U32.to_nat(2147483648)) == True{} : Bool}) ->
  D.Post(False{}, Cr.Cir.exec(f, D.B.body(), st), s => N.Le(D.Mem.cells(s), Nat.max(D.Mem.cells(st), D.Need(ds, st, t))), s => st2 => Unit):
  round.peak.mv(f, ds, ks, img, st, t, w, round.mv(ds, ks, img, st, t, w, inv, hfv))

# Open (U15): a round whose limit has room for its budget (the peak, the
# bytes before first and the output) does not run out of memory (MV's PostB)
def round.room(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +st: Cr.Cir.State, +t: Bk.Term, +w: Nat, inv: D.Inv(ds, ks, img, st, t, w),
  hfv: {D.Term.below(t, U32.to_nat(2147483648)) == True{} : Bool},
  room: N.Le(D.Budget(ds, st, t), D.Lim.bytes(D.St.lim(st)))) ->
  D.NoOom(Cr.Cir.exec(f, D.B.body(), st)):
  round.room.mv(f, ds, ks, img, st, t, w, round.mv(ds, ks, img, st, t, w, inv, hfv), room)

# B: with the memory of AGENTS.md 3.9.1.4, the machine gives the list of bytes
# (open, U15: loop.mem from round.room, and memory_bound.bend's Budget <= F)
def mach.memory.proof(
  +p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +m: U32, +k: Nat, +o: List<&2, Word(8n)>,
  rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  small: {Mc.Img.small(p, 0) == True{} : Bool},
  e: {Pg.Program.result(ds, El.Eval.steps(k, ds, Pg.Program.start(i))) == Some{o} : Maybe<&2, List<&2, Word(8n)>>},
  big: {Nat.is_le(Pg.Program.need(p, i, k), Pg.Program.memory(m)) == True{} : Bool}
) -> &n:Nat -> {Cr.Cir.result(n, Mc.Mach.code(), Mc.Mach.regs(), Mc.Img.cells(ds), i, m) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome}:
  ?TODO
