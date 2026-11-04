# compiler: layer B8, the proofs of memory/spec.bend
# =================================================
#
# One def per law of memory/spec.bend. A body that is ?TODO is open. The
# routes: eval.stops ports ev.stops (eval_facts.bend at 4ebef88); need.peak,
# budget.need, input.need and need.lim port memory_bound.bend's arithmetic
# (largest.*, start.size, first.le, k.le, big.le, w.le, room.need,
# memory.le), with 3 S for 2 S and |i| <= S / 72 for |i| <= S; code.fits
# ports cir_fits.bend (Fits is kept by every statement; M.input takes a new
# cell first); round.mem and input.mem step the round and M.input as their
# moves' and routines' proofs do, with the free list's discipline: a new cell
# is taken only when the free list is empty, so next - first is then the
# live cells' number.

import Base
import ../../../Shared/shared.bend as Sd
import ../../../Book/impl.bend as Bk
import ../../../Eval/impl.bend as El
import ../../../Program/impl.bend as Pg
import ../../../Wasm/impl.bend as Wa
import ../../Cir/impl.bend as Cr
import ../impl.bend as Mc
import ../../need_big.bend as N
import ../../Cir/simulation_memory_bytes.bend as SB
import ../shared.bend as K
import ../logic/spec.bend as Lg
import ../canon/spec.bend as C
import ../am/spec.bend as A
import ../heap/spec.bend as Hp
import ../image/spec.bend as I
import ../routines/spec.bend as R
import ./spec.bend as Me
import ../logic/impl.bend as LgP
import ../canon/impl.bend as CP
import ../am/impl.bend as AP

# Kit
# ---

# a Bool that is true, from its truth as a type
def me.fromT(b: Bool, t: N.T(b)) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, t)

# The limit's bytes (memory_bound.bend at 4ebef88)
# ------------------------------------------------

def me.D_mono(k: Nat, +a: Nat, +b: Nat, h: N.Le(a, b)) -> N.Le(N.D(k, a), N.D(k, b)):
  match k:
    case 0n:
      h
    case 1n+(+q):
      N.double_mono(N.D(q, a), N.D(q, b), me.D_mono(q, a, b, h))

# the pages of min(m, 65536) are the limit's
def me.lim.y(+m: U32, +lim: U32, elim: {lim == Wa.Wasm.min(m, 65536) : U32}) ->
  N.Le(U32.to_nat(Wa.Wasm.min.if(Cmp.is_le(U32.cmp(m, 65536)), m, 65536)), U32.to_nat(lim)):
  %Equal.sym(U32, lim, Wa.Wasm.min(m, 65536), elim) :
    N.Le(U32.to_nat(Wa.Wasm.min.if(Cmp.is_le(U32.cmp(m, 65536)), m, 65536)), U32.to_nat(_))
  N.le_refl(U32.to_nat(Wa.Wasm.min(m, 65536)))

# so they are at most the pages min(lim, 65536) that Lim counts, by the
# branch of U32.is_le(lim, 65536)
def me.lim.pages(b: Bool, +lim: U32, +y: Nat, hy: N.Le(y, U32.to_nat(65536)), hl: N.Le(y, U32.to_nat(lim))) ->
  N.Le(y, U32.to_nat(Wa.Wasm.min.if(b, lim, 65536))):
  match b:
    case True{}:
      hl
    case False{}:
      %{{==} : {65536 == Wa.Wasm.min.if(False{}, lim, 65536) : U32}} : N.Le(y, U32.to_nat(_))
      hy

# the bytes of m pages are within the limit lim = min(m, 65536)
def me.memory.le(+m: U32, +lim: U32, elim: {lim == Wa.Wasm.min(m, 65536) : U32}) ->
  N.Le(Pg.Program.memory(m), N.D(16n, U32.to_nat(Wa.Wasm.min(lim, 65536)))):
  +L = N.D(16n, U32.to_nat(Wa.Wasm.min(lim, 65536)))
  +y = U32.to_nat(Wa.Wasm.min.if(Cmp.is_le(U32.cmp(m, 65536)), m, 65536))
  +t = U32.to_nat(65536)
  +z = U32.to_nat(Wa.Wasm.min(lim, 65536))
  +hy = N.min.case(Cmp.is_le(U32.cmp(m, 65536)), m, 65536, {==})
  +hz = me.lim.pages(U32.is_le(lim, 65536), lim, y, hy, me.lim.y(m, lim, elim))
  +e2 = Equal.trans(Nat, Nat.mul(t, y), Nat.mul(N.D(16n, 1n), y), N.D(16n, y),
    Equal.cong(Nat, Nat, x => Nat.mul(x, y), t, N.D(16n, 1n), N.val_65536()), N.mul_D(16n, y))
  +h2 = N.le_rw_r(Nat.mul(65536n, y), Nat.mul(t, y), N.D(16n, y), e2, N.mul_mono_l(65536n, t, y, N.le_65536()))
  +h3 = N.le_trans(Nat.mul(65536n, y), N.D(16n, y), L, h2, me.D_mono(16n, y, z, hz))
  N.bridge(m, L, N.le_rw_l(Nat.mul(65536n, y), Nat.add(y, Nat.mul(65535n, y)), L, N.mul_succ(65535n, y), h3))

# the limit of Cir.result's start, from Start
def me.start.lim(+cells: List<&2, Cr.Cir.Cell>, +i: List<&2, Word(8n)>, +m: U32, +k: U32, +len: U32, +pg: U32, +lim: U32,
  +first: U32, +hs: {I.Start(cells, i, m, k, len, pg, lim, first) == True{} : Bool}) -> {lim == Wa.Wasm.min(m, 65536) : U32}:
  +c1 = U32.is_eq(k, Cr.Wasm.encode.len(Cr.Cir.Cell, cells))
  +c2 = U32.is_le(Cr.Cir.pages(Cr.Cir.input.at(k)), m)
  +c3 = U32.is_eq(lim, Wa.Wasm.min(m, 65536))
  +c4 = I.Mb.is(Wa.Wasm.length32(i), len)
  +c6 = U32.is_eq(first, Cr.Cir.first(k, U32.add(Cr.Cir.input.at(k), len)))
  +h5 = K.bool.and_l(Bool.and(Bool.and(Bool.and(Bool.and(c1, c2), c3), c4), I.Mb.is(Cr.Cir.alloc.pages(k, len,
    Cr.Cir.pages(Cr.Cir.input.at(k)), lim), pg)), c6, hs)
  +h4 = K.bool.and_l(Bool.and(Bool.and(Bool.and(c1, c2), c3), c4), I.Mb.is(Cr.Cir.alloc.pages(k, len, Cr.Cir.pages(Cr.Cir.input.at(k)), lim), pg), h5)
  +h3 = K.bool.and_l(Bool.and(Bool.and(c1, c2), c3), c4, h4)
  SB.U32.eq(lim, Wa.Wasm.min(m, 65536), K.bool.and_r(Bool.and(c1, c2), c3, h3))

# Eval's facts: a value has no step (eval_facts.bend at 4ebef88, ported:
# its defs prefixed evf., definitions.bend's two kit lemmas written here)
# --------------------------------------------------------------------------

def evf.P2(-A: Data, -B: Data) -> Data:
  Sigma<&2, &2, A, _ => B>

def evf.bool.t(b: Bool) -> Type:
  match b:
    case True{}:
      Empty
    case False{}:
      Unit

def evf.bool.ft(-G: Type, e: {False{} == True{} : Bool}) -> G:
  Empty.absurd(G, (%e : evf.bool.t(_); Unit{}))

def evf.st.none(x: Maybe<Bk.Term>) -> Type:
  match x:
    case None{}:
      Unit
    case Some{_}:
      Empty

def evf.st.ne(-u: Bk.Term, e: {None{} == Some{u} : Maybe<Bk.Term>}) -> Empty:
  %e : evf.st.none(_)
  Unit{}

# Kit
# ---

def evf.ft(-G: Type, e: {True{} == False{} : Bool}) -> G:
  evf.bool.ft(G, Equal.sym(Bool, True{}, False{}, e))

def evf.and.l(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def evf.and.r(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      evf.bool.ft({b == True{} : Bool}, h)

def evf.and.f(a: Bool, -b: Bool, h: {b == False{} : Bool}) -> {Bool.and(a, b) == False{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      {==}

# a step is not none
def evf.sm.ne(-u: Bk.Term, e: {Some{u} == None{} : Maybe<Bk.Term>}) -> Empty:
  evf.st.ne(u, Equal.sym(Maybe<Bk.Term>, Some{u}, None{}, e))

# x is True when y is, and y is False when x is
def evf.bool.back(b: Bool, -x: Bool, -y: Bool, eb: {x == b : Bool}, more: {x == False{} : Bool} -> {y == False{} : Bool},
  hy: {y == True{} : Bool}) -> {x == True{} : Bool}:
  match b:
    case True{}:
      eb
    case False{}:
      evf.bool.ft({x == True{} : Bool}, Equal.trans(Bool, False{}, y, True{}, Equal.sym(Bool, y, False{}, more(eb)), hy))

# A walk that does not wait does not wait with more arguments
# ------------------------------------------------------------

def evf.w.if(b: Bool, -r: Maybe<Maybe<Bk.Term>>, -s: Maybe<Maybe<Bk.Term>>,
  h: {El.Eval.waits(El.Eval.walk.if(b, r)) == False{} : Bool},
  g: {El.Eval.waits(r) == False{} : Bool} -> {El.Eval.waits(s) == False{} : Bool}) ->
  {El.Eval.waits(El.Eval.walk.if(b, s)) == False{} : Bool}:
  match b:
    case True{}:
      g(h)
    case False{}:
      {==}

def evf.w.pick(b: Bool, -r1: Maybe<Maybe<Bk.Term>>, -s1: Maybe<Maybe<Bk.Term>>, -r2: Maybe<Maybe<Bk.Term>>, -s2: Maybe<Maybe<Bk.Term>>,
  h: {El.Eval.waits(El.Eval.walk.pick(b, r1, s1)) == False{} : Bool},
  g1: {El.Eval.waits(r1) == False{} : Bool} -> {El.Eval.waits(r2) == False{} : Bool},
  g2: {El.Eval.waits(s1) == False{} : Bool} -> {El.Eval.waits(s2) == False{} : Bool}) ->
  {El.Eval.waits(El.Eval.walk.pick(b, r2, s2)) == False{} : Bool}:
  match b:
    case True{}:
      g1(h)
    case False{}:
      g2(h)

def evf.w.app(b: Bool, -r: Maybe<Maybe<Bk.Term>>, -s: Maybe<Maybe<Bk.Term>>, -u: Bk.Term, -v: Bk.Term,
  h: {El.Eval.waits(El.Eval.walk.app(b, r, u)) == False{} : Bool},
  g: {El.Eval.waits(r) == False{} : Bool} -> {El.Eval.waits(s) == False{} : Bool}) ->
  {El.Eval.waits(El.Eval.walk.app(b, s, v)) == False{} : Bool}:
  match b:
    case True{}:
      g(h)
    case False{}:
      {==}

# the walk of the case tree t, with e bound, on xs then ys
def evf.WM(t: Bk.Term, e: List<&2, Bk.Term>, xs: List<&2, El.Arg>, ys: List<&2, El.Arg>) -> Type:
  {El.Eval.waits(El.Eval.walk(t, e, List.append(&2, El.Arg, xs, ys))) == False{} : Bool}

def evf.walk.more(t: Bk.Term, +e: List<&2, Bk.Term>, xs: List<&2, El.Arg>, +ys: List<&2, El.Arg>,
  h: {El.Eval.waits(El.Eval.walk(t, e, xs)) == False{} : Bool}) -> evf.WM(t, e, xs, ys):
  match t:
    case Bk.Term.Var{+z0}:
      {==}
    case Bk.Term.Ref{+z0}:
      {==}
    case Bk.Term.Ann{+z0, +z1}:
      {==}
    case Bk.Term.Let{+z0, +z1, +z2}:
      {==}
    case Bk.Term.Typ{+z0}:
      {==}
    case Bk.Term.Min{+z0, +z1}:
      {==}
    case Bk.Term.All{+z0, +z1, +z2}:
      {==}
    case Bk.Term.Lam{+z0, +z1}:
      match xs:
        case Nil{}:
          evf.ft(evf.WM(Bk.Term.Lam{z0, z1}, e, Nil{}, ys), h)
        case Con{El.Arg{+q, +x}, +rest}:
          evf.w.if(El.Quan.binds(z0, q, x), El.Eval.walk(z1, Con{x, e}, rest), El.Eval.walk(z1, Con{x, e}, List.append(&2, El.Arg, rest, ys)), h,
            hr => evf.walk.more(z1, Con{x, e}, rest, ys, hr))
    case Bk.Term.App{+z0, +z1, +z2}:
      match z2:
        case Bk.Term.Var{+y0}:
          evf.w.app(El.Term.takes(El.Term.head(z1)), El.Eval.walk(z1, e, Con{El.Arg{z0, El.Env.sub(e, y0)}, xs}),
            El.Eval.walk(z1, e, Con{El.Arg{z0, El.Env.sub(e, y0)}, List.append(&2, El.Arg, xs, ys)}),
            El.Term.spine(xs, El.Term.subst(Bk.Term.App{z0, z1, Bk.Term.Var{y0}}, e, 0n)),
            El.Term.spine(List.append(&2, El.Arg, xs, ys), El.Term.subst(Bk.Term.App{z0, z1, Bk.Term.Var{y0}}, e, 0n)), h,
            hr => evf.walk.more(z1, e, Con{El.Arg{z0, El.Env.sub(e, y0)}, xs}, ys, hr))
        case Bk.Term.Ref{+y0}:
          {==}
        case Bk.Term.Ann{+y0, +y1}:
          {==}
        case Bk.Term.Let{+y0, +y1, +y2}:
          {==}
        case Bk.Term.Typ{+y0}:
          {==}
        case Bk.Term.Min{+y0, +y1}:
          {==}
        case Bk.Term.All{+y0, +y1, +y2}:
          {==}
        case Bk.Term.Lam{+y0, +y1}:
          {==}
        case Bk.Term.App{+y0, +y1, +y2}:
          {==}
        case Bk.Term.Sig{+y0, +y1, +y2}:
          {==}
        case Bk.Term.Tup{+y0, +y1, +y2}:
          {==}
        case Bk.Term.Prj{+y0}:
          {==}
        case Bk.Term.Enu{+y0}:
          {==}
        case Bk.Term.Lab{+y0}:
          {==}
        case Bk.Term.Mat{+y0, +y1, +y2}:
          {==}
        case Bk.Term.Efq{}:
          {==}
        case Bk.Term.Eql{+y0, +y1, +y2}:
          {==}
        case Bk.Term.Rfl{}:
          {==}
        case Bk.Term.Rwt{+y0, +y1, +y2}:
          {==}
    case Bk.Term.Sig{+z0, +z1, +z2}:
      {==}
    case Bk.Term.Tup{+z0, +z1, +z2}:
      {==}
    case Bk.Term.Prj{+z0}:
      match xs:
        case Nil{}:
          evf.ft(evf.WM(Bk.Term.Prj{z0}, e, Nil{}, ys), h)
        case Con{El.Arg{+q, +x}, +rest}:
          match x:
            case Bk.Term.Var{+y0}:
              {==}
            case Bk.Term.Ref{+y0}:
              {==}
            case Bk.Term.Ann{+y0, +y1}:
              {==}
            case Bk.Term.Let{+y0, +y1, +y2}:
              {==}
            case Bk.Term.Typ{+y0}:
              {==}
            case Bk.Term.Min{+y0, +y1}:
              {==}
            case Bk.Term.All{+y0, +y1, +y2}:
              {==}
            case Bk.Term.Lam{+y0, +y1}:
              {==}
            case Bk.Term.App{+y0, +y1, +y2}:
              {==}
            case Bk.Term.Sig{+y0, +y1, +y2}:
              {==}
            case Bk.Term.Tup{+y0, +y1, +y2}:
              evf.w.if(El.Quan.live(q), El.Eval.walk(z0, e, Con{El.Arg{El.Quan.fld(y0, q), y1}, Con{El.Arg{q, y2}, rest}}),
                El.Eval.walk(z0, e, Con{El.Arg{El.Quan.fld(y0, q), y1}, Con{El.Arg{q, y2}, List.append(&2, El.Arg, rest, ys)}}), h,
                hr => evf.walk.more(z0, e, Con{El.Arg{El.Quan.fld(y0, q), y1}, Con{El.Arg{q, y2}, rest}}, ys, hr))
            case Bk.Term.Prj{+y0}:
              {==}
            case Bk.Term.Enu{+y0}:
              {==}
            case Bk.Term.Lab{+y0}:
              {==}
            case Bk.Term.Mat{+y0, +y1, +y2}:
              {==}
            case Bk.Term.Efq{}:
              {==}
            case Bk.Term.Eql{+y0, +y1, +y2}:
              {==}
            case Bk.Term.Rfl{}:
              {==}
            case Bk.Term.Rwt{+y0, +y1, +y2}:
              {==}
    case Bk.Term.Enu{+z0}:
      {==}
    case Bk.Term.Lab{+z0}:
      {==}
    case Bk.Term.Mat{+z0, +z1, +z2}:
      match xs:
        case Nil{}:
          evf.ft(evf.WM(Bk.Term.Mat{z0, z1, z2}, e, Nil{}, ys), h)
        case Con{El.Arg{+q, +x}, +rest}:
          match x:
            case Bk.Term.Var{+y0}:
              {==}
            case Bk.Term.Ref{+y0}:
              {==}
            case Bk.Term.Ann{+y0, +y1}:
              {==}
            case Bk.Term.Let{+y0, +y1, +y2}:
              {==}
            case Bk.Term.Typ{+y0}:
              {==}
            case Bk.Term.Min{+y0, +y1}:
              {==}
            case Bk.Term.All{+y0, +y1, +y2}:
              {==}
            case Bk.Term.Lam{+y0, +y1}:
              {==}
            case Bk.Term.App{+y0, +y1, +y2}:
              {==}
            case Bk.Term.Sig{+y0, +y1, +y2}:
              {==}
            case Bk.Term.Tup{+y0, +y1, +y2}:
              {==}
            case Bk.Term.Prj{+y0}:
              {==}
            case Bk.Term.Enu{+y0}:
              {==}
            case Bk.Term.Lab{+y0}:
              evf.w.if(El.Quan.live(q), El.Eval.walk.pick(Sd.Name.is_eq(y0, z0), El.Eval.walk(z1, e, rest), El.Eval.walk(z2, e, Con{El.Arg{q, Bk.Term.Lab{y0}}, rest})),
                El.Eval.walk.pick(Sd.Name.is_eq(y0, z0), El.Eval.walk(z1, e, List.append(&2, El.Arg, rest, ys)), El.Eval.walk(z2, e, Con{El.Arg{q, Bk.Term.Lab{y0}}, List.append(&2, El.Arg, rest, ys)})), h,
                hr => evf.w.pick(Sd.Name.is_eq(y0, z0), El.Eval.walk(z1, e, rest), El.Eval.walk(z2, e, Con{El.Arg{q, Bk.Term.Lab{y0}}, rest}),
                  El.Eval.walk(z1, e, List.append(&2, El.Arg, rest, ys)), El.Eval.walk(z2, e, Con{El.Arg{q, Bk.Term.Lab{y0}}, List.append(&2, El.Arg, rest, ys)}), hr,
                  a1 => evf.walk.more(z1, e, rest, ys, a1), a2 => evf.walk.more(z2, e, Con{El.Arg{q, Bk.Term.Lab{y0}}, rest}, ys, a2)))
            case Bk.Term.Mat{+y0, +y1, +y2}:
              {==}
            case Bk.Term.Efq{}:
              {==}
            case Bk.Term.Eql{+y0, +y1, +y2}:
              {==}
            case Bk.Term.Rfl{}:
              {==}
            case Bk.Term.Rwt{+y0, +y1, +y2}:
              {==}
    case Bk.Term.Efq{}:
      match xs:
        case Nil{}:
          evf.ft(evf.WM(Bk.Term.Efq{}, e, Nil{}, ys), h)
        case Con{+x, +rest}:
          {==}
    case Bk.Term.Eql{+z0, +z1, +z2}:
      {==}
    case Bk.Term.Rfl{}:
      {==}
    case Bk.Term.Rwt{+z0, +z1, +z2}:
      {==}

# the same for a call's walk, from the head of its spine
def evf.cwd.more(mb: Maybe<Bk.Def>, xs: List<&2, El.Arg>, +ys: List<&2, El.Arg>,
  h: {El.Eval.waits(El.Eval.callWalk.def(mb, xs)) == False{} : Bool}) ->
  {El.Eval.waits(El.Eval.callWalk.def(mb, List.append(&2, El.Arg, xs, ys))) == False{} : Bool}:
  match mb:
    case None{}:
      {==}
    case Some{Bk.Def{+k, +T, +v, +o}}:
      evf.walk.more(v, Nil{}, xs, ys, h)

def evf.cwh.more(+ds: List<&2, Bk.Def>, hd: Bk.Term, xs: List<&2, El.Arg>, +ys: List<&2, El.Arg>,
  h: {El.Eval.waits(El.Eval.callWalk.head(ds, hd, xs)) == False{} : Bool}) ->
  {El.Eval.waits(El.Eval.callWalk.head(ds, hd, List.append(&2, El.Arg, xs, ys))) == False{} : Bool}:
  match hd:
    case Bk.Term.Var{+z0}:
      {==}
    case Bk.Term.Ref{+z0}:
      evf.cwd.more(El.Book.get(ds, z0), xs, ys, h)
    case Bk.Term.Ann{+z0, +z1}:
      {==}
    case Bk.Term.Let{+z0, +z1, +z2}:
      {==}
    case Bk.Term.Typ{+z0}:
      {==}
    case Bk.Term.Min{+z0, +z1}:
      {==}
    case Bk.Term.All{+z0, +z1, +z2}:
      {==}
    case Bk.Term.Lam{+z0, +z1}:
      {==}
    case Bk.Term.App{+z0, +z1, +z2}:
      {==}
    case Bk.Term.Sig{+z0, +z1, +z2}:
      {==}
    case Bk.Term.Tup{+z0, +z1, +z2}:
      {==}
    case Bk.Term.Prj{+z0}:
      {==}
    case Bk.Term.Enu{+z0}:
      {==}
    case Bk.Term.Lab{+z0}:
      {==}
    case Bk.Term.Mat{+z0, +z1, +z2}:
      {==}
    case Bk.Term.Efq{}:
      {==}
    case Bk.Term.Eql{+z0, +z1, +z2}:
      {==}
    case Bk.Term.Rfl{}:
      {==}
    case Bk.Term.Rwt{+z0, +z1, +z2}:
      {==}

# the arguments of a spine, in front of xs then ys
def evf.args.app(t: Bk.Term, xs: List<&2, El.Arg>, +ys: List<&2, El.Arg>) ->
  {El.Term.args(t, List.append(&2, El.Arg, xs, ys)) == List.append(&2, El.Arg, El.Term.args(t, xs), ys) : List<&2, El.Arg>}:
  match t:
    case Bk.Term.Var{+z0}:
      {==}
    case Bk.Term.Ref{+z0}:
      {==}
    case Bk.Term.Ann{+z0, +z1}:
      {==}
    case Bk.Term.Let{+z0, +z1, +z2}:
      {==}
    case Bk.Term.Typ{+z0}:
      {==}
    case Bk.Term.Min{+z0, +z1}:
      {==}
    case Bk.Term.All{+z0, +z1, +z2}:
      {==}
    case Bk.Term.Lam{+z0, +z1}:
      {==}
    case Bk.Term.App{+z0, +z1, +z2}:
      evf.args.app(z1, Con{El.Arg{z0, z2}, xs}, ys)
    case Bk.Term.Sig{+z0, +z1, +z2}:
      {==}
    case Bk.Term.Tup{+z0, +z1, +z2}:
      {==}
    case Bk.Term.Prj{+z0}:
      {==}
    case Bk.Term.Enu{+z0}:
      {==}
    case Bk.Term.Lab{+z0}:
      {==}
    case Bk.Term.Mat{+z0, +z1, +z2}:
      {==}
    case Bk.Term.Efq{}:
      {==}
    case Bk.Term.Eql{+z0, +z1, +z2}:
      {==}
    case Bk.Term.Rfl{}:
      {==}
    case Bk.Term.Rwt{+z0, +z1, +z2}:
      {==}

# a call's walk that does not wait does not wait with one more argument
def evf.cw.app(+ds: List<&2, Bk.Def>, +u: Bk.Term, +q: Bk.Quan, +a: Bk.Term,
  h: {El.Eval.waits(El.Eval.callWalk(ds, u)) == False{} : Bool}) ->
  {El.Eval.waits(El.Eval.callWalk(ds, Bk.Term.App{q, u, a})) == False{} : Bool}:
  %Equal.sym(List<&2, El.Arg>, El.Term.args(u, List.append(&2, El.Arg, Nil{}, [El.Arg{q, a}])), List.append(&2, El.Arg, El.Term.args(u, Nil{}), [El.Arg{q, a}]),
    evf.args.app(u, Nil{}, [El.Arg{q, a}])) : {El.Eval.waits(El.Eval.callWalk.head(ds, El.Term.head(u), _)) == False{} : Bool}
  evf.cwh.more(ds, El.Term.head(u), El.Term.args(u, Nil{}), [El.Arg{q, a}], h)

def evf.cw.acc(+ds: List<&2, Bk.Def>, +f: Bk.Term, +acc: List<&2, El.Arg>,
  hw: {El.Eval.waits(El.Eval.callWalk.head(ds, El.Term.head(f), El.Term.args(f, acc))) == True{} : Bool}) ->
  {El.Eval.waits(El.Eval.callWalk.head(ds, El.Term.head(f), List.append(&2, El.Arg, El.Term.args(f, Nil{}), acc))) == True{} : Bool}:
  %evf.args.app(f, Nil{}, acc) : {El.Eval.waits(El.Eval.callWalk.head(ds, El.Term.head(f), _)) == True{} : Bool}
  hw

# a call's walk that waits with more arguments waits with none
def evf.cw.back(+ds: List<&2, Bk.Def>, +f: Bk.Term, +acc: List<&2, El.Arg>,
  hw: {El.Eval.waits(El.Eval.callWalk.head(ds, El.Term.head(f), El.Term.args(f, acc))) == True{} : Bool}) ->
  {El.Eval.waits(El.Eval.callWalk(ds, f)) == True{} : Bool}:
  +hw2 = evf.cw.acc(ds, f, acc, hw)
  evf.bool.back(El.Eval.waits(El.Eval.callWalk(ds, f)), El.Eval.waits(El.Eval.callWalk(ds, f)),
    El.Eval.waits(El.Eval.callWalk.head(ds, El.Term.head(f), List.append(&2, El.Arg, El.Term.args(f, Nil{}), acc))), {==},
    e => evf.cwh.more(ds, El.Term.head(f), El.Term.args(f, Nil{}), acc, e), hw2)

# Values
# ------

# a spine of a def on arguments that are values is a value when its walk waits
def evf.vals.tf(+ds: List<&2, Bk.Def>, u: Bk.Term, ht: {El.Eval.vals(ds, u, True{}) == True{} : Bool}) ->
  {El.Eval.vals(ds, u, False{}) == El.Eval.waits(El.Eval.callWalk(ds, u)) : Bool}:
  match u:
    case Bk.Term.Var{+z0}:
      evf.bool.ft({El.Eval.vals(ds, Bk.Term.Var{z0}, False{}) == El.Eval.waits(El.Eval.callWalk(ds, Bk.Term.Var{z0})) : Bool}, ht)
    case Bk.Term.Ref{+z0}:
      {==}
    case Bk.Term.Ann{+z0, +z1}:
      evf.bool.ft({El.Eval.vals(ds, Bk.Term.Ann{z0, z1}, False{}) == El.Eval.waits(El.Eval.callWalk(ds, Bk.Term.Ann{z0, z1})) : Bool}, ht)
    case Bk.Term.Let{+z0, +z1, +z2}:
      evf.bool.ft({El.Eval.vals(ds, Bk.Term.Let{z0, z1, z2}, False{}) == El.Eval.waits(El.Eval.callWalk(ds, Bk.Term.Let{z0, z1, z2})) : Bool}, ht)
    case Bk.Term.Typ{+z0}:
      evf.bool.ft({El.Eval.vals(ds, Bk.Term.Typ{z0}, False{}) == El.Eval.waits(El.Eval.callWalk(ds, Bk.Term.Typ{z0})) : Bool}, ht)
    case Bk.Term.Min{+z0, +z1}:
      evf.bool.ft({El.Eval.vals(ds, Bk.Term.Min{z0, z1}, False{}) == El.Eval.waits(El.Eval.callWalk(ds, Bk.Term.Min{z0, z1})) : Bool}, ht)
    case Bk.Term.All{+z0, +z1, +z2}:
      evf.bool.ft({El.Eval.vals(ds, Bk.Term.All{z0, z1, z2}, False{}) == El.Eval.waits(El.Eval.callWalk(ds, Bk.Term.All{z0, z1, z2})) : Bool}, ht)
    case Bk.Term.Lam{+z0, +z1}:
      evf.bool.ft({El.Eval.vals(ds, Bk.Term.Lam{z0, z1}, False{}) == El.Eval.waits(El.Eval.callWalk(ds, Bk.Term.Lam{z0, z1})) : Bool}, ht)
    case Bk.Term.App{+z0, +z1, +z2}:
      %Equal.sym(Bool, Bool.and(El.Eval.vals(ds, z1, True{}), Bool.or(Bool.not(El.Quan.live(z0)), El.Eval.vals(ds, z2, False{}))), True{}, ht) :
        {Bool.and(_, El.Eval.waits(El.Eval.callWalk(ds, Bk.Term.App{z0, z1, z2}))) == El.Eval.waits(El.Eval.callWalk(ds, Bk.Term.App{z0, z1, z2})) : Bool}
      {==}
    case Bk.Term.Sig{+z0, +z1, +z2}:
      evf.bool.ft({El.Eval.vals(ds, Bk.Term.Sig{z0, z1, z2}, False{}) == El.Eval.waits(El.Eval.callWalk(ds, Bk.Term.Sig{z0, z1, z2})) : Bool}, ht)
    case Bk.Term.Tup{+z0, +z1, +z2}:
      evf.bool.ft({El.Eval.vals(ds, Bk.Term.Tup{z0, z1, z2}, False{}) == El.Eval.waits(El.Eval.callWalk(ds, Bk.Term.Tup{z0, z1, z2})) : Bool}, ht)
    case Bk.Term.Prj{+z0}:
      evf.bool.ft({El.Eval.vals(ds, Bk.Term.Prj{z0}, False{}) == El.Eval.waits(El.Eval.callWalk(ds, Bk.Term.Prj{z0})) : Bool}, ht)
    case Bk.Term.Enu{+z0}:
      evf.bool.ft({El.Eval.vals(ds, Bk.Term.Enu{z0}, False{}) == El.Eval.waits(El.Eval.callWalk(ds, Bk.Term.Enu{z0})) : Bool}, ht)
    case Bk.Term.Lab{+z0}:
      evf.bool.ft({El.Eval.vals(ds, Bk.Term.Lab{z0}, False{}) == El.Eval.waits(El.Eval.callWalk(ds, Bk.Term.Lab{z0})) : Bool}, ht)
    case Bk.Term.Mat{+z0, +z1, +z2}:
      evf.bool.ft({El.Eval.vals(ds, Bk.Term.Mat{z0, z1, z2}, False{}) == El.Eval.waits(El.Eval.callWalk(ds, Bk.Term.Mat{z0, z1, z2})) : Bool}, ht)
    case Bk.Term.Efq{}:
      evf.bool.ft({El.Eval.vals(ds, Bk.Term.Efq{}, False{}) == El.Eval.waits(El.Eval.callWalk(ds, Bk.Term.Efq{})) : Bool}, ht)
    case Bk.Term.Eql{+z0, +z1, +z2}:
      evf.bool.ft({El.Eval.vals(ds, Bk.Term.Eql{z0, z1, z2}, False{}) == El.Eval.waits(El.Eval.callWalk(ds, Bk.Term.Eql{z0, z1, z2})) : Bool}, ht)
    case Bk.Term.Rfl{}:
      evf.bool.ft({El.Eval.vals(ds, Bk.Term.Rfl{}, False{}) == El.Eval.waits(El.Eval.callWalk(ds, Bk.Term.Rfl{})) : Bool}, ht)
    case Bk.Term.Rwt{+z0, +z1, +z2}:
      evf.bool.ft({El.Eval.vals(ds, Bk.Term.Rwt{z0, z1, z2}, False{}) == El.Eval.waits(El.Eval.callWalk(ds, Bk.Term.Rwt{z0, z1, z2})) : Bool}, ht)

# the call of a walk that waits is none
def evf.call.none(ok: Bool, r: Maybe<Maybe<Bk.Term>>, h: {El.Eval.waits(r) == True{} : Bool}) -> {El.Eval.call.if(ok, r) == None{} : Maybe<Bk.Term>}:
  match ok:
    case True{}:
      match r:
        case None{}:
          evf.bool.ft({El.Eval.call.if(True{}, None{}) == None{} : Maybe<Bk.Term>}, h)
        case Some{+s}:
          match s:
            case None{}:
              {==}
            case Some{+u}:
              evf.bool.ft({El.Eval.call.if(True{}, Some{Some{u}}) == None{} : Maybe<Bk.Term>}, h)
    case False{}:
      {==}

# the redex of a spine of a def is its call
def evf.redex.call(+ds: List<&2, Bk.Def>, g: Bk.Term, +q: Bk.Quan, +x: Bk.Term, ht: {El.Eval.vals(ds, g, True{}) == True{} : Bool}) ->
  {El.Eval.redex(ds, q, g, x) == El.Eval.call(ds, Bk.Term.App{q, g, x}) : Maybe<Bk.Term>}:
  match g:
    case Bk.Term.Var{+z0}:
      evf.bool.ft({El.Eval.redex(ds, q, Bk.Term.Var{z0}, x) == El.Eval.call(ds, Bk.Term.App{q, Bk.Term.Var{z0}, x}) : Maybe<Bk.Term>}, ht)
    case Bk.Term.Ref{+z0}:
      {==}
    case Bk.Term.Ann{+z0, +z1}:
      evf.bool.ft({El.Eval.redex(ds, q, Bk.Term.Ann{z0, z1}, x) == El.Eval.call(ds, Bk.Term.App{q, Bk.Term.Ann{z0, z1}, x}) : Maybe<Bk.Term>}, ht)
    case Bk.Term.Let{+z0, +z1, +z2}:
      evf.bool.ft({El.Eval.redex(ds, q, Bk.Term.Let{z0, z1, z2}, x) == El.Eval.call(ds, Bk.Term.App{q, Bk.Term.Let{z0, z1, z2}, x}) : Maybe<Bk.Term>}, ht)
    case Bk.Term.Typ{+z0}:
      evf.bool.ft({El.Eval.redex(ds, q, Bk.Term.Typ{z0}, x) == El.Eval.call(ds, Bk.Term.App{q, Bk.Term.Typ{z0}, x}) : Maybe<Bk.Term>}, ht)
    case Bk.Term.Min{+z0, +z1}:
      evf.bool.ft({El.Eval.redex(ds, q, Bk.Term.Min{z0, z1}, x) == El.Eval.call(ds, Bk.Term.App{q, Bk.Term.Min{z0, z1}, x}) : Maybe<Bk.Term>}, ht)
    case Bk.Term.All{+z0, +z1, +z2}:
      evf.bool.ft({El.Eval.redex(ds, q, Bk.Term.All{z0, z1, z2}, x) == El.Eval.call(ds, Bk.Term.App{q, Bk.Term.All{z0, z1, z2}, x}) : Maybe<Bk.Term>}, ht)
    case Bk.Term.Lam{+z0, +z1}:
      evf.bool.ft({El.Eval.redex(ds, q, Bk.Term.Lam{z0, z1}, x) == El.Eval.call(ds, Bk.Term.App{q, Bk.Term.Lam{z0, z1}, x}) : Maybe<Bk.Term>}, ht)
    case Bk.Term.App{+z0, +z1, +z2}:
      {==}
    case Bk.Term.Sig{+z0, +z1, +z2}:
      evf.bool.ft({El.Eval.redex(ds, q, Bk.Term.Sig{z0, z1, z2}, x) == El.Eval.call(ds, Bk.Term.App{q, Bk.Term.Sig{z0, z1, z2}, x}) : Maybe<Bk.Term>}, ht)
    case Bk.Term.Tup{+z0, +z1, +z2}:
      evf.bool.ft({El.Eval.redex(ds, q, Bk.Term.Tup{z0, z1, z2}, x) == El.Eval.call(ds, Bk.Term.App{q, Bk.Term.Tup{z0, z1, z2}, x}) : Maybe<Bk.Term>}, ht)
    case Bk.Term.Prj{+z0}:
      evf.bool.ft({El.Eval.redex(ds, q, Bk.Term.Prj{z0}, x) == El.Eval.call(ds, Bk.Term.App{q, Bk.Term.Prj{z0}, x}) : Maybe<Bk.Term>}, ht)
    case Bk.Term.Enu{+z0}:
      evf.bool.ft({El.Eval.redex(ds, q, Bk.Term.Enu{z0}, x) == El.Eval.call(ds, Bk.Term.App{q, Bk.Term.Enu{z0}, x}) : Maybe<Bk.Term>}, ht)
    case Bk.Term.Lab{+z0}:
      evf.bool.ft({El.Eval.redex(ds, q, Bk.Term.Lab{z0}, x) == El.Eval.call(ds, Bk.Term.App{q, Bk.Term.Lab{z0}, x}) : Maybe<Bk.Term>}, ht)
    case Bk.Term.Mat{+z0, +z1, +z2}:
      evf.bool.ft({El.Eval.redex(ds, q, Bk.Term.Mat{z0, z1, z2}, x) == El.Eval.call(ds, Bk.Term.App{q, Bk.Term.Mat{z0, z1, z2}, x}) : Maybe<Bk.Term>}, ht)
    case Bk.Term.Efq{}:
      evf.bool.ft({El.Eval.redex(ds, q, Bk.Term.Efq{}, x) == El.Eval.call(ds, Bk.Term.App{q, Bk.Term.Efq{}, x}) : Maybe<Bk.Term>}, ht)
    case Bk.Term.Eql{+z0, +z1, +z2}:
      evf.bool.ft({El.Eval.redex(ds, q, Bk.Term.Eql{z0, z1, z2}, x) == El.Eval.call(ds, Bk.Term.App{q, Bk.Term.Eql{z0, z1, z2}, x}) : Maybe<Bk.Term>}, ht)
    case Bk.Term.Rfl{}:
      evf.bool.ft({El.Eval.redex(ds, q, Bk.Term.Rfl{}, x) == El.Eval.call(ds, Bk.Term.App{q, Bk.Term.Rfl{}, x}) : Maybe<Bk.Term>}, ht)
    case Bk.Term.Rwt{+z0, +z1, +z2}:
      evf.bool.ft({El.Eval.redex(ds, q, Bk.Term.Rwt{z0, z1, z2}, x) == El.Eval.call(ds, Bk.Term.App{q, Bk.Term.Rwt{z0, z1, z2}, x}) : Maybe<Bk.Term>}, ht)

# App q f x has no step, when f has none, is a value, and x has none and is a
# value when q is live, and the redex is none
def evf.app.none(+q: Bk.Quan, +f: Bk.Term, +x: Bk.Term, sf: Maybe<Bk.Term>, vf: Bool, live: Bool, sx: Maybe<Bk.Term>, vx: Bool, -r: Maybe<Bk.Term>,
  esf: {sf == None{} : Maybe<Bk.Term>}, hx: {Bool.or(Bool.not(live), vx) == True{} : Bool},
  esx: {vx == True{} : Bool} -> {sx == None{} : Maybe<Bk.Term>}, er: {r == None{} : Maybe<Bk.Term>}) ->
  {El.Eval.step.app(q, f, x, sf, vf, live, sx, vx, r) == None{} : Maybe<Bk.Term>}:
  match sf:
    case Some{+f2}:
      Empty.absurd({El.Eval.step.app(q, f, x, Some{f2}, vf, live, sx, vx, r) == None{} : Maybe<Bk.Term>}, evf.sm.ne(f2, esf))
    case None{}:
      match vf:
        case False{}:
          {==}
        case True{}:
          match live:
            case False{}:
              er
            case True{}:
              match sx:
                case Some{+x2}:
                  Empty.absurd({El.Eval.step.app(q, f, x, None{}, True{}, True{}, Some{x2}, vx, r) == None{} : Maybe<Bk.Term>}, evf.sm.ne(x2, esx(hx)))
                case None{}:
                  match vx:
                    case True{}:
                      er
                    case False{}:
                      {==}

# Tup q a b has no step, when a has none when it is a value and q live, and b
# has none
def evf.tup.none(+q: Bk.Quan, +a: Bk.Term, +b: Bk.Term, live: Bool, sa: Maybe<Bk.Term>, va: Bool, sb: Maybe<Bk.Term>,
  hx: {Bool.or(Bool.not(live), va) == True{} : Bool}, esa: {va == True{} : Bool} -> {sa == None{} : Maybe<Bk.Term>},
  esb: {sb == None{} : Maybe<Bk.Term>}) -> {El.Eval.step.tup(q, a, b, live, sa, va, sb) == None{} : Maybe<Bk.Term>}:
  match live:
    case False{}:
      %Equal.sym(Maybe<Bk.Term>, sb, None{}, esb) : {El.Eval.step.tup_b(q, a, _) == None{} : Maybe<Bk.Term>}
      {==}
    case True{}:
      match sa:
        case Some{+a2}:
          Empty.absurd({El.Eval.step.tup(q, a, b, True{}, Some{a2}, va, sb) == None{} : Maybe<Bk.Term>}, evf.sm.ne(a2, esa(hx)))
        case None{}:
          match va:
            case True{}:
              %Equal.sym(Maybe<Bk.Term>, sb, None{}, esb) : {El.Eval.step.tup_b(q, a, _) == None{} : Maybe<Bk.Term>}
              {==}
            case False{}:
              {==}

# A value has no step
# -------------------

# what evf.stops says has no step: a value (a False), or a spine of a def on
# arguments that are values, whose walk with more arguments acc waits (a True)
def evf.SH(a: Bool, +ds: List<&2, Bk.Def>, +t: Bk.Term, +acc: List<&2, El.Arg>) -> Data:
  match a:
    case False{}:
      {El.Eval.vals(ds, t, False{}) == True{} : Bool}
    case True{}:
      evf.P2({El.Eval.vals(ds, t, True{}) == True{} : Bool},
        {El.Eval.waits(El.Eval.callWalk.head(ds, El.Term.head(t), El.Term.args(t, acc))) == True{} : Bool})

def evf.stops(t: Bk.Term, a: Bool, +ds: List<&2, Bk.Def>, +acc: List<&2, El.Arg>, +h: evf.SH(a, ds, t, acc)) ->
  {El.Eval.step(ds, t) == None{} : Maybe<Bk.Term>}:
  match t:
    case Bk.Term.Var{+z0}:
      match a:
        case False{}:
          {==}
        case True{}:
          (ht, hw) = h
          evf.bool.ft({El.Eval.step(ds, Bk.Term.Var{z0}) == None{} : Maybe<Bk.Term>}, ht)
    case Bk.Term.Ref{+z0}:
      match a:
        case False{}:
          evf.call.none(True{}, El.Eval.callWalk(ds, Bk.Term.Ref{z0}), h)
        case True{}:
          (ht, hw) = h
          evf.call.none(True{}, El.Eval.callWalk(ds, Bk.Term.Ref{z0}), evf.cw.back(ds, Bk.Term.Ref{z0}, acc, hw))
    case Bk.Term.Ann{+z0, +z1}:
      match a:
        case False{}:
          evf.bool.ft({El.Eval.step(ds, Bk.Term.Ann{z0, z1}) == None{} : Maybe<Bk.Term>}, h)
        case True{}:
          (ht, hw) = h
          evf.bool.ft({El.Eval.step(ds, Bk.Term.Ann{z0, z1}) == None{} : Maybe<Bk.Term>}, ht)
    case Bk.Term.Let{+z0, +z1, +z2}:
      match a:
        case False{}:
          evf.bool.ft({El.Eval.step(ds, Bk.Term.Let{z0, z1, z2}) == None{} : Maybe<Bk.Term>}, h)
        case True{}:
          (ht, hw) = h
          evf.bool.ft({El.Eval.step(ds, Bk.Term.Let{z0, z1, z2}) == None{} : Maybe<Bk.Term>}, ht)
    case Bk.Term.Typ{+z0}:
      match a:
        case False{}:
          {==}
        case True{}:
          (ht, hw) = h
          evf.bool.ft({El.Eval.step(ds, Bk.Term.Typ{z0}) == None{} : Maybe<Bk.Term>}, ht)
    case Bk.Term.Min{+z0, +z1}:
      match a:
        case False{}:
          evf.bool.ft({El.Eval.step(ds, Bk.Term.Min{z0, z1}) == None{} : Maybe<Bk.Term>}, h)
        case True{}:
          (ht, hw) = h
          evf.bool.ft({El.Eval.step(ds, Bk.Term.Min{z0, z1}) == None{} : Maybe<Bk.Term>}, ht)
    case Bk.Term.All{+z0, +z1, +z2}:
      match a:
        case False{}:
          {==}
        case True{}:
          (ht, hw) = h
          evf.bool.ft({El.Eval.step(ds, Bk.Term.All{z0, z1, z2}) == None{} : Maybe<Bk.Term>}, ht)
    case Bk.Term.Lam{+z0, +z1}:
      match a:
        case False{}:
          {==}
        case True{}:
          (ht, hw) = h
          evf.bool.ft({El.Eval.step(ds, Bk.Term.Lam{z0, z1}) == None{} : Maybe<Bk.Term>}, ht)
    case Bk.Term.App{+z0, +z1, +z2}:
      match a:
        case False{}:
          +ok = evf.and.l(Bool.and(El.Eval.vals(ds, z1, True{}), Bool.or(Bool.not(El.Quan.live(z0)), El.Eval.vals(ds, z2, False{}))), El.Eval.waits(El.Eval.callWalk(ds, Bk.Term.App{z0, z1, z2})), h)
          +hw = evf.and.r(Bool.and(El.Eval.vals(ds, z1, True{}), Bool.or(Bool.not(El.Quan.live(z0)), El.Eval.vals(ds, z2, False{}))), El.Eval.waits(El.Eval.callWalk(ds, Bk.Term.App{z0, z1, z2})), h)
          +hg = evf.and.l(El.Eval.vals(ds, z1, True{}), Bool.or(Bool.not(El.Quan.live(z0)), El.Eval.vals(ds, z2, False{})), ok)
          +hx = evf.and.r(El.Eval.vals(ds, z1, True{}), Bool.or(Bool.not(El.Quan.live(z0)), El.Eval.vals(ds, z2, False{})), ok)
          +er = Equal.trans(Maybe<Bk.Term>, El.Eval.redex(ds, z0, z1, z2), El.Eval.call(ds, Bk.Term.App{z0, z1, z2}), None{},
            evf.redex.call(ds, z1, z0, z2, hg),
            evf.call.none(El.Eval.vals(ds, Bk.Term.App{z0, z1, z2}, True{}), El.Eval.callWalk(ds, Bk.Term.App{z0, z1, z2}), hw))
          evf.app.none(z0, z1, z2, El.Eval.step(ds, z1), El.Eval.vals(ds, z1, False{}), El.Quan.live(z0), El.Eval.step(ds, z2), El.Eval.vals(ds, z2, False{}),
            El.Eval.redex(ds, z0, z1, z2), evf.stops(z1, True{}, ds, [El.Arg{z0, z2}], (hg, hw)), hx, e => evf.stops(z2, False{}, ds, Nil{}, e), er)
        case True{}:
          (+ht, +hw) = h
          +hg = evf.and.l(El.Eval.vals(ds, z1, True{}), Bool.or(Bool.not(El.Quan.live(z0)), El.Eval.vals(ds, z2, False{})), ht)
          +hx = evf.and.r(El.Eval.vals(ds, z1, True{}), Bool.or(Bool.not(El.Quan.live(z0)), El.Eval.vals(ds, z2, False{})), ht)
          +er = Equal.trans(Maybe<Bk.Term>, El.Eval.redex(ds, z0, z1, z2), El.Eval.call(ds, Bk.Term.App{z0, z1, z2}), None{},
            evf.redex.call(ds, z1, z0, z2, hg),
            evf.call.none(El.Eval.vals(ds, Bk.Term.App{z0, z1, z2}, True{}), El.Eval.callWalk(ds, Bk.Term.App{z0, z1, z2}), evf.cw.back(ds, Bk.Term.App{z0, z1, z2}, acc, hw)))
          evf.app.none(z0, z1, z2, El.Eval.step(ds, z1), El.Eval.vals(ds, z1, False{}), El.Quan.live(z0), El.Eval.step(ds, z2), El.Eval.vals(ds, z2, False{}),
            El.Eval.redex(ds, z0, z1, z2), evf.stops(z1, True{}, ds, Con{El.Arg{z0, z2}, acc}, (hg, hw)), hx, e => evf.stops(z2, False{}, ds, Nil{}, e), er)
    case Bk.Term.Sig{+z0, +z1, +z2}:
      match a:
        case False{}:
          {==}
        case True{}:
          (ht, hw) = h
          evf.bool.ft({El.Eval.step(ds, Bk.Term.Sig{z0, z1, z2}) == None{} : Maybe<Bk.Term>}, ht)
    case Bk.Term.Tup{+z0, +z1, +z2}:
      match a:
        case False{}:
          +hx = evf.and.l(Bool.or(Bool.not(El.Quan.live(z0)), El.Eval.vals(ds, z1, False{})), El.Eval.vals(ds, z2, False{}), h)
          +hb = evf.and.r(Bool.or(Bool.not(El.Quan.live(z0)), El.Eval.vals(ds, z1, False{})), El.Eval.vals(ds, z2, False{}), h)
          evf.tup.none(z0, z1, z2, El.Quan.live(z0), El.Eval.step(ds, z1), El.Eval.vals(ds, z1, False{}), El.Eval.step(ds, z2), hx,
            e => evf.stops(z1, False{}, ds, Nil{}, e), evf.stops(z2, False{}, ds, Nil{}, hb))
        case True{}:
          (ht, hw) = h
          evf.bool.ft({El.Eval.step(ds, Bk.Term.Tup{z0, z1, z2}) == None{} : Maybe<Bk.Term>}, ht)
    case Bk.Term.Prj{+z0}:
      match a:
        case False{}:
          {==}
        case True{}:
          (ht, hw) = h
          evf.bool.ft({El.Eval.step(ds, Bk.Term.Prj{z0}) == None{} : Maybe<Bk.Term>}, ht)
    case Bk.Term.Enu{+z0}:
      match a:
        case False{}:
          {==}
        case True{}:
          (ht, hw) = h
          evf.bool.ft({El.Eval.step(ds, Bk.Term.Enu{z0}) == None{} : Maybe<Bk.Term>}, ht)
    case Bk.Term.Lab{+z0}:
      match a:
        case False{}:
          {==}
        case True{}:
          (ht, hw) = h
          evf.bool.ft({El.Eval.step(ds, Bk.Term.Lab{z0}) == None{} : Maybe<Bk.Term>}, ht)
    case Bk.Term.Mat{+z0, +z1, +z2}:
      match a:
        case False{}:
          {==}
        case True{}:
          (ht, hw) = h
          evf.bool.ft({El.Eval.step(ds, Bk.Term.Mat{z0, z1, z2}) == None{} : Maybe<Bk.Term>}, ht)
    case Bk.Term.Efq{}:
      match a:
        case False{}:
          {==}
        case True{}:
          (ht, hw) = h
          evf.bool.ft({El.Eval.step(ds, Bk.Term.Efq{}) == None{} : Maybe<Bk.Term>}, ht)
    case Bk.Term.Eql{+z0, +z1, +z2}:
      match a:
        case False{}:
          {==}
        case True{}:
          (ht, hw) = h
          evf.bool.ft({El.Eval.step(ds, Bk.Term.Eql{z0, z1, z2}) == None{} : Maybe<Bk.Term>}, ht)
    case Bk.Term.Rfl{}:
      match a:
        case False{}:
          {==}
        case True{}:
          (ht, hw) = h
          evf.bool.ft({El.Eval.step(ds, Bk.Term.Rfl{}) == None{} : Maybe<Bk.Term>}, ht)
    case Bk.Term.Rwt{+z0, +z1, +z2}:
      match a:
        case False{}:
          evf.bool.ft({El.Eval.step(ds, Bk.Term.Rwt{z0, z1, z2}) == None{} : Maybe<Bk.Term>}, h)
        case True{}:
          (ht, hw) = h
          evf.bool.ft({El.Eval.step(ds, Bk.Term.Rwt{z0, z1, z2}) == None{} : Maybe<Bk.Term>}, ht)

# a value has no step (Lean's eval_value)
def evf.ev.stops(+ds: List<&2, Bk.Def>, +t: Bk.Term, h: {El.Eval.vals(ds, t, False{}) == True{} : Bool}) ->
  {El.Eval.step(ds, t) == None{} : Maybe<Bk.Term>}:
  evf.stops(t, False{}, ds, Nil{}, h)

# Laws
# ----

def Me.eval.stops(ds, t, h):
  evf.ev.stops(ds, t, h)

def Me.round.mem(x, st, s, iv, f, st2, e):
  ?TODO

def Me.input.mem(p, ds, i, m, k, len, pg, lim, first, n, rd, small, s, f, st, e):
  ?TODO

def Me.need.peak(p, ds, i, n, j, o, C, st, s, rd, he, hj, ht, hst):
  ?TODO

def Me.budget.need(p, ds, i, m, k, len, pg, lim, first, n, j, o, C, st, s, rd, hs, he, hj, ht, iv, hC, hst, hm):
  ?TODO

def Me.input.need(p, ds, i, m, k, len, pg, lim, first, n, rd, hs):
  ?TODO

def Me.need.lim(p, ds, i, m, k, len, pg, lim, first, n, hs, big):
  me.fromT(Nat.is_le(Pg.Program.need(p, i, n), Lg.Lim(I.St0(Mc.Mach.regs(), Mc.Img.cells(ds), first, k, pg, lim, i))),
    N.le_trans(Pg.Program.need(p, i, n), Pg.Program.memory(m), N.D(16n, U32.to_nat(Wa.Wasm.min(lim, 65536))),
      N.toLe(Pg.Program.need(p, i, n), Pg.Program.memory(m), big),
      me.memory.le(m, lim, me.start.lim(Mc.Img.cells(ds), i, m, k, len, pg, lim, first, hs))))

def Me.start.ok(p, ds, i, m, n, rd, big):
  ?TODO

def Me.code.fits(n, cells, first, k, pg, lim, i):
  ?TODO
