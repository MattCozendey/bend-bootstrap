# compiler: layer B7, round.sim from the move laws
# ================================================
#
# round.sim, proven: Mach.round tests the mode (Inv's mode register), then a
# move law per case of AM.move: by the focus' VALUE flag and term in mode 0,
# by the top frame and, at a redex, the function in mode 1. Each case's law
# states its outcome as AM.move computes it there. inv.vb is open (?TODO).

import Base
import ../../../Shared/shared.bend as Sd
import ../../../Book/impl.bend as Bk
import ../../../Eval/impl.bend as El
import ../../../Program/impl.bend as Pg
import ../../../Wasm/impl.bend as Wa
import ../../Cir/impl.bend as Cr
import ../impl.bend as Mc
import ../shared.bend as K
import ../logic/spec.bend as Lg
import ../header/spec.bend as Hs
import ../canon/spec.bend as C
import ../am/spec.bend as A
import ../heap/spec.bend as Hp
import ../image/spec.bend as I
import ../routines/spec.bend as R
import ../memory/spec.bend as Me
import ./spec.bend as Mv
import ../logic/impl.bend as LgP
import ../header/impl.bend as HsP
import ../canon/impl.bend as CP
import ../am/impl.bend as AP
import ../heap/view.bend as HpV
import ../heap/count.bend as HpC
import ../image/impl.bend as IP
import ../routines/prims.bend as RP
import ../routines/nth.bend as RN
import ../routines/dec.bend as RD
import ../routines/copy.bend as RC
import ../routines/walk.bend as RW
import ../routines/out.bend as RO
import ../routines/input.bend as RI
import ../memory/impl.bend as MeP
import ../../Cir/simulation_memory_bytes.bend as SB
import ./ev.bend as MvE
import ./ret.bend as MvR
import ./call.bend as MvC

# Kit
# ---

# Mb.is says the register's value
def rd.mb(r: Maybe<&2, U32>, +v: U32, +h: {I.Mb.is(r, v) == True{} : Bool}) -> {r == Some{v} : Maybe<&2, U32>}:
  match r:
    case Some{+u}:
      Equal.cong(U32, Maybe<&2, U32>, z => Some{z}, u, v, SB.U32.eq(u, v, h))
    case None{}:
      K.bool.ff({None{} == Some{v} : Maybe<&2, U32>}, h)

# the mode's test, in mode 0 and in mode 1
def rd.c0(+st: Cr.Cir.State, +e: {Lg.Reg(st, Mc.R.mode()) == Some{0} : Maybe<&2, U32>}) ->
  {Cr.Cir.eval(Mc.M.eq(Mc.M.g(Mc.R.mode()), Mc.M.c(0)), st) == Some{1} : Maybe<&2, U32>}:
  %Equal.sym(Maybe<&2, U32>, Lg.Reg(st, Mc.R.mode()), Some{0}, e) : {Cr.Cir.eval.op(Wa.Wasm.Op.eq{}, _, Some{0}) == Some{1} : Maybe<&2, U32>}
  {==}

def rd.c1(+st: Cr.Cir.State, +e: {Lg.Reg(st, Mc.R.mode()) == Some{1} : Maybe<&2, U32>}) ->
  {Cr.Cir.eval(Mc.M.eq(Mc.M.g(Mc.R.mode()), Mc.M.c(0)), st) == Some{0} : Maybe<&2, U32>}:
  %Equal.sym(Maybe<&2, U32>, Lg.Reg(st, Mc.R.mode()), Some{1}, e) : {Cr.Cir.eval.op(Wa.Wasm.Op.eq{}, _, Some{0}) == Some{0} : Maybe<&2, U32>}
  {==}

# Mode 0
# ------

# M.ev past the VALUE flag (False), by the focus' term
def rd.ev.t(t: Bk.Term, +x: Hp.Cx, +st: Cr.Cir.State, +fs: List<&2, A.AF>, +iv: {R.Inv(x, st, A.AS{False{}, t, fs}) == True{} : Bool},
  +hv: {Mv.Vb(st) == False{} : Bool}) ->
  Lg.Tot(Mc.M.ev(), st, Me.Budget(x, st, A.AS{False{}, t, fs}), Mv.Next(x, A.AM.move(Hp.Cx.ds(x), False{}, A.AS{False{}, t, fs})), Mv.Halt(A.AM.move(Hp.Cx.ds(x), False{}, A.AS{False{}, t, fs}))):
  match t:
    case Bk.Term.Var{+i}:
      Mv.mv.ev.var(x, st, i, fs, iv, hv)
    case Bk.Term.Ref{+k0}:
      Mv.mv.ev.ref(x, st, k0, fs, iv, hv)
    case Bk.Term.Ann{+a0, +b0}:
      Mv.mv.ev.ann(x, st, a0, b0, fs, iv, hv)
    case Bk.Term.Let{+q0, +v0, +f0}:
      match q0:
        case Bk.Quan.Q0{}:
          Mv.mv.ev.unlet(x, st, Bk.Quan.Q0{}, v0, f0, fs, iv, hv, {==})
        case Bk.Quan.Q1{}:
          Mv.mv.ev.let(x, st, Bk.Quan.Q1{}, v0, f0, fs, iv, hv, {==})
        case Bk.Quan.Q2{}:
          Mv.mv.ev.let(x, st, Bk.Quan.Q2{}, v0, f0, fs, iv, hv, {==})
    case Bk.Term.Typ{+a0}:
      Mv.mv.ev.val(x, st, Bk.Term.Typ{a0}, fs, iv, K.bool.or_r(Mv.Vb(st), A.AM.former(Bk.Term.Typ{a0}), {==}))
    case Bk.Term.Min{+a0, +b0}:
      Mv.mv.ev.min(x, st, a0, b0, fs, iv, hv)
    case Bk.Term.All{+q0, +a0, +b0}:
      Mv.mv.ev.val(x, st, Bk.Term.All{q0, a0, b0}, fs, iv, K.bool.or_r(Mv.Vb(st), A.AM.former(Bk.Term.All{q0, a0, b0}), {==}))
    case Bk.Term.Lam{+p0, +f0}:
      Mv.mv.ev.val(x, st, Bk.Term.Lam{p0, f0}, fs, iv, K.bool.or_r(Mv.Vb(st), A.AM.former(Bk.Term.Lam{p0, f0}), {==}))
    case Bk.Term.App{+q0, +f0, +a0}:
      Mv.mv.ev.app(x, st, q0, f0, a0, fs, iv, hv)
    case Bk.Term.Sig{+q0, +a0, +b0}:
      Mv.mv.ev.val(x, st, Bk.Term.Sig{q0, a0, b0}, fs, iv, K.bool.or_r(Mv.Vb(st), A.AM.former(Bk.Term.Sig{q0, a0, b0}), {==}))
    case Bk.Term.Tup{+q0, +a0, +b0}:
      match q0:
        case Bk.Quan.Q0{}:
          Mv.mv.ev.tup0(x, st, Bk.Quan.Q0{}, a0, b0, fs, iv, hv, {==})
        case Bk.Quan.Q1{}:
          Mv.mv.ev.tup(x, st, Bk.Quan.Q1{}, a0, b0, fs, iv, hv, {==})
        case Bk.Quan.Q2{}:
          Mv.mv.ev.tup(x, st, Bk.Quan.Q2{}, a0, b0, fs, iv, hv, {==})
    case Bk.Term.Prj{+h0}:
      Mv.mv.ev.val(x, st, Bk.Term.Prj{h0}, fs, iv, K.bool.or_r(Mv.Vb(st), A.AM.former(Bk.Term.Prj{h0}), {==}))
    case Bk.Term.Enu{+e0}:
      Mv.mv.ev.val(x, st, Bk.Term.Enu{e0}, fs, iv, K.bool.or_r(Mv.Vb(st), A.AM.former(Bk.Term.Enu{e0}), {==}))
    case Bk.Term.Lab{+k0}:
      Mv.mv.ev.val(x, st, Bk.Term.Lab{k0}, fs, iv, K.bool.or_r(Mv.Vb(st), A.AM.former(Bk.Term.Lab{k0}), {==}))
    case Bk.Term.Mat{+j0, +h0, +m0}:
      Mv.mv.ev.val(x, st, Bk.Term.Mat{j0, h0, m0}, fs, iv, K.bool.or_r(Mv.Vb(st), A.AM.former(Bk.Term.Mat{j0, h0, m0}), {==}))
    case Bk.Term.Efq{}:
      Mv.mv.ev.val(x, st, Bk.Term.Efq{}, fs, iv, K.bool.or_r(Mv.Vb(st), A.AM.former(Bk.Term.Efq{}), {==}))
    case Bk.Term.Eql{+a0, +b0, +c0}:
      Mv.mv.ev.val(x, st, Bk.Term.Eql{a0, b0, c0}, fs, iv, K.bool.or_r(Mv.Vb(st), A.AM.former(Bk.Term.Eql{a0, b0, c0}), {==}))
    case Bk.Term.Rfl{}:
      Mv.mv.ev.val(x, st, Bk.Term.Rfl{}, fs, iv, K.bool.or_r(Mv.Vb(st), A.AM.former(Bk.Term.Rfl{}), {==}))
    case Bk.Term.Rwt{+e0, +p0, +f0}:
      Mv.mv.ev.rwt(x, st, e0, p0, f0, fs, iv, hv)

# M.ev, by the focus' VALUE flag b
def rd.ev(b: Bool, +x: Hp.Cx, +st: Cr.Cir.State, +t: Bk.Term, +fs: List<&2, A.AF>, +iv: {R.Inv(x, st, A.AS{False{}, t, fs}) == True{} : Bool},
  +eb: {Mv.Vb(st) == b : Bool}) ->
  Lg.Tot(Mc.M.ev(), st, Me.Budget(x, st, A.AS{False{}, t, fs}), Mv.Next(x, A.AM.move(Hp.Cx.ds(x), b, A.AS{False{}, t, fs})), Mv.Halt(A.AM.move(Hp.Cx.ds(x), b, A.AS{False{}, t, fs}))):
  match b:
    case True{}:
      Mv.mv.ev.val(x, st, t, fs, iv, K.bool.or_l(Mv.Vb(st), A.AM.former(t), eb))
    case False{}:
      rd.ev.t(t, x, st, fs, iv, eb)

# Mode 1
# ------

# App q □ a, not swapped: the redex, by the value v
def rd.redex(v: Bk.Term, +x: Hp.Cx, +st: Cr.Cir.State, +kind: A.FK, +q: Bk.Quan, +k: Bool, +a: Bk.Term, +b: Bk.Term, +fs: List<&2, A.AF>, +iv: {R.Inv(x, st, A.AS{True{}, v, Con{A.AF{kind, q, k, a, b}, fs}}) == True{} : Bool},
  +hk: {Mv.Kind.is_app(kind) == True{} : Bool}, +hs: {El.Quan.live(q) && Bool.not(k) == False{} : Bool}) ->
  Lg.Tot(Mc.M.ret(), st, Me.Budget(x, st, A.AS{True{}, v, Con{A.AF{kind, q, k, a, b}, fs}}), Mv.Next(x, A.AM.redex(Hp.Cx.ds(x), q, v, a, fs)), Mv.Halt(A.AM.redex(Hp.Cx.ds(x), q, v, a, fs))):
  match v:
    case Bk.Term.Var{+i}:
      Mv.mv.ret.app.call(x, st, Bk.Term.Var{i}, kind, q, k, a, b, fs, iv, hk, hs, {==})
    case Bk.Term.Ref{+k0}:
      Mv.mv.ret.app.call(x, st, Bk.Term.Ref{k0}, kind, q, k, a, b, fs, iv, hk, hs, {==})
    case Bk.Term.Ann{+a0, +b0}:
      Mv.mv.ret.app.call(x, st, Bk.Term.Ann{a0, b0}, kind, q, k, a, b, fs, iv, hk, hs, {==})
    case Bk.Term.Let{+q0, +v0, +f0}:
      Mv.mv.ret.app.call(x, st, Bk.Term.Let{q0, v0, f0}, kind, q, k, a, b, fs, iv, hk, hs, {==})
    case Bk.Term.Typ{+a0}:
      Mv.mv.ret.app.call(x, st, Bk.Term.Typ{a0}, kind, q, k, a, b, fs, iv, hk, hs, {==})
    case Bk.Term.Min{+a0, +b0}:
      Mv.mv.ret.app.call(x, st, Bk.Term.Min{a0, b0}, kind, q, k, a, b, fs, iv, hk, hs, {==})
    case Bk.Term.All{+q0, +a0, +b0}:
      Mv.mv.ret.app.call(x, st, Bk.Term.All{q0, a0, b0}, kind, q, k, a, b, fs, iv, hk, hs, {==})
    case Bk.Term.Lam{+p0, +f0}:
      Mv.mv.ret.app.lam(x, st, p0, f0, kind, q, k, a, b, fs, iv, hk, hs)
    case Bk.Term.App{+q0, +f0, +a0}:
      Mv.mv.ret.app.call(x, st, Bk.Term.App{q0, f0, a0}, kind, q, k, a, b, fs, iv, hk, hs, {==})
    case Bk.Term.Sig{+q0, +a0, +b0}:
      Mv.mv.ret.app.call(x, st, Bk.Term.Sig{q0, a0, b0}, kind, q, k, a, b, fs, iv, hk, hs, {==})
    case Bk.Term.Tup{+q0, +a0, +b0}:
      Mv.mv.ret.app.call(x, st, Bk.Term.Tup{q0, a0, b0}, kind, q, k, a, b, fs, iv, hk, hs, {==})
    case Bk.Term.Prj{+h0}:
      Mv.mv.ret.app.prj(x, st, h0, kind, q, k, a, b, fs, iv, hk, hs)
    case Bk.Term.Enu{+e0}:
      Mv.mv.ret.app.call(x, st, Bk.Term.Enu{e0}, kind, q, k, a, b, fs, iv, hk, hs, {==})
    case Bk.Term.Lab{+k0}:
      Mv.mv.ret.app.call(x, st, Bk.Term.Lab{k0}, kind, q, k, a, b, fs, iv, hk, hs, {==})
    case Bk.Term.Mat{+j0, +h0, +m0}:
      Mv.mv.ret.app.mat(x, st, j0, h0, m0, kind, q, k, a, b, fs, iv, hk, hs)
    case Bk.Term.Efq{}:
      Mv.mv.ret.app.call(x, st, Bk.Term.Efq{}, kind, q, k, a, b, fs, iv, hk, hs, {==})
    case Bk.Term.Eql{+a0, +b0, +c0}:
      Mv.mv.ret.app.call(x, st, Bk.Term.Eql{a0, b0, c0}, kind, q, k, a, b, fs, iv, hk, hs, {==})
    case Bk.Term.Rfl{}:
      Mv.mv.ret.app.call(x, st, Bk.Term.Rfl{}, kind, q, k, a, b, fs, iv, hk, hs, {==})
    case Bk.Term.Rwt{+e0, +p0, +f0}:
      Mv.mv.ret.app.call(x, st, Bk.Term.Rwt{e0, p0, f0}, kind, q, k, a, b, fs, iv, hk, hs, {==})

# App q □ a: swap when q is live and a not KNOWN (sw); else the redex
def rd.app(sw: Bool, +x: Hp.Cx, +st: Cr.Cir.State, +v: Bk.Term, +kind: A.FK, +q: Bk.Quan, +k: Bool, +a: Bk.Term, +b: Bk.Term, +fs: List<&2, A.AF>, +iv: {R.Inv(x, st, A.AS{True{}, v, Con{A.AF{kind, q, k, a, b}, fs}}) == True{} : Bool},
  +hk: {Mv.Kind.is_app(kind) == True{} : Bool}, +hs: {El.Quan.live(q) && Bool.not(k) == sw : Bool}) ->
  Lg.Tot(Mc.M.ret(), st, Me.Budget(x, st, A.AS{True{}, v, Con{A.AF{kind, q, k, a, b}, fs}}), Mv.Next(x, A.AM.arg(Hp.Cx.ds(x), sw, q, v, a, fs)), Mv.Halt(A.AM.arg(Hp.Cx.ds(x), sw, q, v, a, fs))):
  match sw:
    case True{}:
      Mv.mv.ret.swap(x, st, v, kind, q, k, a, b, fs, iv, hk, hs)
    case False{}:
      rd.redex(v, x, st, kind, q, k, a, b, fs, iv, hk, hs)

# App q g □: the redex, by the function g
def rd.fun(g: Bk.Term, +x: Hp.Cx, +st: Cr.Cir.State, +v: Bk.Term, +q: Bk.Quan, +k: Bool, +b: Bk.Term, +fs: List<&2, A.AF>, +iv: {R.Inv(x, st, A.AS{True{}, v, Con{A.AF{A.FK.fun{}, q, k, g, b}, fs}}) == True{} : Bool}) ->
  Lg.Tot(Mc.M.ret(), st, Me.Budget(x, st, A.AS{True{}, v, Con{A.AF{A.FK.fun{}, q, k, g, b}, fs}}), Mv.Next(x, A.AM.redex(Hp.Cx.ds(x), q, g, v, fs)), Mv.Halt(A.AM.redex(Hp.Cx.ds(x), q, g, v, fs))):
  match g:
    case Bk.Term.Var{+i}:
      Mv.mv.ret.fun.call(x, st, v, q, k, Bk.Term.Var{i}, b, fs, iv, {==})
    case Bk.Term.Ref{+k0}:
      Mv.mv.ret.fun.call(x, st, v, q, k, Bk.Term.Ref{k0}, b, fs, iv, {==})
    case Bk.Term.Ann{+a0, +b0}:
      Mv.mv.ret.fun.call(x, st, v, q, k, Bk.Term.Ann{a0, b0}, b, fs, iv, {==})
    case Bk.Term.Let{+q0, +v0, +f0}:
      Mv.mv.ret.fun.call(x, st, v, q, k, Bk.Term.Let{q0, v0, f0}, b, fs, iv, {==})
    case Bk.Term.Typ{+a0}:
      Mv.mv.ret.fun.call(x, st, v, q, k, Bk.Term.Typ{a0}, b, fs, iv, {==})
    case Bk.Term.Min{+a0, +b0}:
      Mv.mv.ret.fun.call(x, st, v, q, k, Bk.Term.Min{a0, b0}, b, fs, iv, {==})
    case Bk.Term.All{+q0, +a0, +b0}:
      Mv.mv.ret.fun.call(x, st, v, q, k, Bk.Term.All{q0, a0, b0}, b, fs, iv, {==})
    case Bk.Term.Lam{+p0, +f0}:
      Mv.mv.ret.fun.lam(x, st, v, q, k, p0, f0, b, fs, iv)
    case Bk.Term.App{+q0, +f0, +a0}:
      Mv.mv.ret.fun.call(x, st, v, q, k, Bk.Term.App{q0, f0, a0}, b, fs, iv, {==})
    case Bk.Term.Sig{+q0, +a0, +b0}:
      Mv.mv.ret.fun.call(x, st, v, q, k, Bk.Term.Sig{q0, a0, b0}, b, fs, iv, {==})
    case Bk.Term.Tup{+q0, +a0, +b0}:
      Mv.mv.ret.fun.call(x, st, v, q, k, Bk.Term.Tup{q0, a0, b0}, b, fs, iv, {==})
    case Bk.Term.Prj{+h0}:
      Mv.mv.ret.fun.prj(x, st, v, q, k, h0, b, fs, iv)
    case Bk.Term.Enu{+e0}:
      Mv.mv.ret.fun.call(x, st, v, q, k, Bk.Term.Enu{e0}, b, fs, iv, {==})
    case Bk.Term.Lab{+k0}:
      Mv.mv.ret.fun.call(x, st, v, q, k, Bk.Term.Lab{k0}, b, fs, iv, {==})
    case Bk.Term.Mat{+j0, +h0, +m0}:
      Mv.mv.ret.fun.mat(x, st, v, q, k, j0, h0, m0, b, fs, iv)
    case Bk.Term.Efq{}:
      Mv.mv.ret.fun.call(x, st, v, q, k, Bk.Term.Efq{}, b, fs, iv, {==})
    case Bk.Term.Eql{+a0, +b0, +c0}:
      Mv.mv.ret.fun.call(x, st, v, q, k, Bk.Term.Eql{a0, b0, c0}, b, fs, iv, {==})
    case Bk.Term.Rfl{}:
      Mv.mv.ret.fun.call(x, st, v, q, k, Bk.Term.Rfl{}, b, fs, iv, {==})
    case Bk.Term.Rwt{+e0, +p0, +f0}:
      Mv.mv.ret.fun.call(x, st, v, q, k, Bk.Term.Rwt{e0, p0, f0}, b, fs, iv, {==})

# M.ret (past the mode's test), by the top frame
def rd.ret(fs: List<&2, A.AF>, +x: Hp.Cx, +st: Cr.Cir.State, +v: Bk.Term, +iv: {R.Inv(x, st, A.AS{True{}, v, fs}) == True{} : Bool}) ->
  Lg.Tot(Mc.M.ret(), st, Me.Budget(x, st, A.AS{True{}, v, fs}), Mv.Next(x, A.AM.move(Hp.Cx.ds(x), Mv.Vb(st), A.AS{True{}, v, fs})), Mv.Halt(A.AM.move(Hp.Cx.ds(x), Mv.Vb(st), A.AS{True{}, v, fs}))):
  match fs:
    case Nil{}:
      Mv.mv.out(x, st, v, iv)
    case Con{A.AF{+kind, +q, +k, +a, +b}, +rest}:
      match kind:
        case A.FK.arg{}:
          rd.app(Bool.and(El.Quan.live(q), Bool.not(k)), x, st, v, A.FK.arg{}, q, k, a, b, rest, iv, {==}, {==})
        case A.FK.val{}:
          rd.app(Bool.and(El.Quan.live(q), Bool.not(k)), x, st, v, A.FK.val{}, q, k, a, b, rest, iv, {==}, {==})
        case A.FK.fun{}:
          rd.fun(a, x, st, v, q, k, b, rest, iv)
        case A.FK.let{}:
          Mv.mv.ret.let(x, st, v, q, k, a, b, rest, iv)
        case A.FK.tupb{}:
          Mv.mv.ret.tupb(x, st, v, q, k, a, b, rest, iv)
        case A.FK.tupa{}:
          Mv.mv.ret.tupa(x, st, v, q, k, a, b, rest, iv)
        case A.FK.rwt{}:
          Mv.mv.ret.rwt(x, st, v, q, k, a, b, rest, iv)
        case A.FK.minb{}:
          Mv.mv.ret.minb(x, st, v, q, k, a, b, rest, iv)
        case A.FK.mina{}:
          Mv.mv.ret.mina(x, st, v, q, k, a, b, rest, iv)

# The round
# ---------

# the round, by the mode r
def rd.go(r: Bool, +x: Hp.Cx, +st: Cr.Cir.State, +t: Bk.Term, +fs: List<&2, A.AF>, +iv: {R.Inv(x, st, A.AS{r, t, fs}) == True{} : Bool}) ->
  Lg.Tot(Mc.Mach.round(), st, Me.Budget(x, st, A.AS{r, t, fs}), Mv.Next(x, A.AM.move(Hp.Cx.ds(x), Mv.Vb(st), A.AS{r, t, fs})), Mv.Halt(A.AM.move(Hp.Cx.ds(x), Mv.Vb(st), A.AS{r, t, fs}))):
  match r:
    case False{}:
      +em = rd.mb(Lg.Reg(st, Mc.R.mode()), 0, K.bool.and_l(R.Inv.mode(st, False{}), Hp.H(x, st, Hp.V.Live(st), [Hp.Rt{Lg.St.reg(st, Mc.R.focus()), 0n, t}], fs, []), iv))
      Lg.tot.if(Mc.M.eq(Mc.M.g(Mc.R.mode()), Mc.M.c(0)), Mc.M.ev(), Mc.M.ret(), st, Me.Budget(x, st, A.AS{False{}, t, fs}),
        Mv.Next(x, A.AM.move(Hp.Cx.ds(x), Mv.Vb(st), A.AS{False{}, t, fs})), Mv.Halt(A.AM.move(Hp.Cx.ds(x), Mv.Vb(st), A.AS{False{}, t, fs})), 1, rd.c0(st, em),
        rd.ev(Mv.Vb(st), x, st, t, fs, iv, {==}))
    case True{}:
      +em = rd.mb(Lg.Reg(st, Mc.R.mode()), 1, K.bool.and_l(R.Inv.mode(st, True{}), Hp.H(x, st, Hp.V.Live(st), [Hp.Rt{Lg.St.reg(st, Mc.R.focus()), 0n, t}], fs, []), iv))
      Lg.tot.if(Mc.M.eq(Mc.M.g(Mc.R.mode()), Mc.M.c(0)), Mc.M.ev(), Mc.M.ret(), st, Me.Budget(x, st, A.AS{True{}, t, fs}),
        Mv.Next(x, A.AM.move(Hp.Cx.ds(x), Mv.Vb(st), A.AS{True{}, t, fs})), Mv.Halt(A.AM.move(Hp.Cx.ds(x), Mv.Vb(st), A.AS{True{}, t, fs})), 0, rd.c1(st, em),
        rd.ret(fs, x, st, t, iv))

# Laws
# ----

def Mv.round.sim(x, st, s, iv):
  match s:
    case A.AS{+r, +t, +fs}:
      rd.go(r, x, st, t, fs, iv)

def Mv.inv.vb(x, st, s, iv):
  ?TODO
