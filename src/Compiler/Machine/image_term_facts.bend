# compiler: what Img.go's fv, VALUE and DATA say of a term (layer B)
# =================================================================
#
# Img.go gives each node an fv, VALUE and DATA from its parts' (the same one
# pass that lays out the cells). What NdK asks of them: fv bounds the free
# variables of the term (Term.below), unless it is fv_max, and it is at most
# fv_max, so that its 19 bits hold it (go.fv); VALUE says that the term is a
# value (go.val); DATA that it is Data (go.data). A Var's fv needs its index
# below 2^32 (VB, read_var_bound.bend).
#
# Z is fv_max's number, a variable with eZ: Z = U32.to_nat(524287): the
# checkers never expand it.

import Base
import ../../Book/impl.bend as Bk
import ../../Eval/impl.bend as El
import ../Cir/impl.bend as Cr
import ../Cir/leb_round_trip.bend as L
import ../Cir/module_round_trip.bend as MO
import ./impl.bend as Mc
import ./definitions.bend as D
import ../need_big.bend as N
import ./copy_kit.bend as CK
import ./copy_terms.bend as CT
import ./first_cell_past_table.bend as FC
import ./image_layout.bend as IL
import ./read_var_bound.bend as RV

# Kit
# ---

# b or c, with b false, gives c
def or.rr(b: Bool, -c: Bool, e: {Bool.or(b, c) == True{} : Bool}, n: {b == False{} : Bool}) -> {c == True{} : Bool}:
  match b:
    case False{}:
      e
    case True{}:
      Empty.absurd({c == True{} : Bool}, N.true_ne_false(n))

# a true Bool is True
def ofT(x: Bool, t: N.T(x)) -> {x == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, t)

# a <= b, as a Bool
def toB(+a: Nat, +b: Nat, h: N.Le(a, b)) -> {Nat.is_le(a, b) == True{} : Bool}:
  ofT(Nat.is_le(a, b), h)

# i < 1 + i
def lt.succ(i: Nat) -> {Nat.is_lt(i, 1n+i) == True{} : Bool}:
  match i:
    case 0n:
      {==}
    case 1n+p:
      lt.succ(p)

# a comparison other than LT: y <= x
def nlt.rel(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), e: {Cmp.is_lt(c) == False{} : Bool}) -> N.Le(y, x):
  match c:
    case LT{}:
      Empty.absurd(N.Le(y, x), N.true_ne_false(e))
    case EQ{}:
      (%r : N.Le(_, x); N.le_refl(x))
    case GT{}:
      N.weaken(y, x, r)

def nlt.le(+a: U32, +b: U32, e: {U32.is_lt(a, b) == False{} : Bool}) -> N.Le(U32.to_nat(b), U32.to_nat(a)):
  nlt.rel(U32.cmp(a, b), U32.to_nat(a), U32.to_nat(b), N.U32.rel(a, b), e)

# a comparison GT: y < x; any other: x <= y
def gt.rel(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), e: {Cmp.is_gt(c) == True{} : Bool}) -> N.Le(1n+y, x):
  match c:
    case LT{}:
      Empty.absurd(N.Le(1n+y, x), N.false_ne_true(e))
    case EQ{}:
      Empty.absurd(N.Le(1n+y, x), N.false_ne_true(e))
    case GT{}:
      r

def ngt.rel(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), e: {Cmp.is_gt(c) == False{} : Bool}) -> N.Le(x, y):
  match c:
    case LT{}:
      N.weaken(x, y, r)
    case EQ{}:
      (%r : N.Le(x, _); N.le_refl(x))
    case GT{}:
      Empty.absurd(N.Le(x, y), N.true_ne_false(e))

def gt.lt(+a: U32, +b: U32, e: {U32.is_gt(a, b) == True{} : Bool}) -> N.Le(1n+U32.to_nat(b), U32.to_nat(a)):
  gt.rel(U32.cmp(a, b), U32.to_nat(a), U32.to_nat(b), N.U32.rel(a, b), e)

def ngt.le(+a: U32, +b: U32, e: {U32.is_gt(a, b) == False{} : Bool}) -> N.Le(U32.to_nat(a), U32.to_nat(b)):
  ngt.rel(U32.cmp(a, b), U32.to_nat(a), U32.to_nat(b), N.U32.rel(a, b), e)

# U32.max, as a pick
def max.pick(+a: U32, +b: U32) -> {U32.max(a, b) == Bool.pick(U32, U32.is_lt(a, b), b, a) : U32}:
  match a b:
    case U32{+x} U32{+y}:
      {==}

# 1 + (2x) = 2x + 1, as the words with the lowest bit clear and set
def succ.w(+w: Word(31n), +a: U32, +b: U32, ea: {a == U32{WCon{False{}, w}} : U32}, eb: {b == U32{WCon{True{}, w}} : U32}) ->
  {1n+U32.to_nat(a) == U32.to_nat(b) : Nat}:
  %Equal.sym(U32, a, U32{WCon{False{}, w}}, ea) : {1n+U32.to_nat(_) == U32.to_nat(b) : Nat}
  %Equal.sym(U32, b, U32{WCon{True{}, w}}, eb) : {1n+U32.to_nat(U32{WCon{False{}, w}}) == U32.to_nat(_) : Nat}
  {==}

# fv_max is at most Z, and 524286 below it
def top.le(+Z: Nat, +eZ: {U32.to_nat(524287) == Z : Nat}) -> N.Le(U32.to_nat(524287), Z):
  N.le_rw_r(U32.to_nat(524287), U32.to_nat(524287), Z, eZ, N.le_refl(U32.to_nat(524287)))

def top.lt(+Z: Nat, +eZ: {U32.to_nat(524287) == Z : Nat}) -> N.Le(1n+U32.to_nat(524286), Z):
  N.le_rw_r(1n+U32.to_nat(524286), 1n+U32.to_nat(524286), Z,
    Equal.trans(Nat, 1n+U32.to_nat(524286), U32.to_nat(524287), Z,
      succ.w(L.Word.low(31n, 18n), 524286, 524287, {==}, {==}), eZ),
    N.le_refl(1n+U32.to_nat(524286)))

# a pick of fv_max is fv_max (a rewrite: the checkers compare picks by
# unfolding, which would expand 524287 under U32.to_nat)
def top.t(+y: U32) -> {524287 == Bool.pick(U32, True{}, 524287, y) : U32}:
  {==}

def top.f(+y: U32) -> {524287 == Bool.pick(U32, False{}, y, 524287) : U32}:
  {==}

# a number at most Z and not fv_max is below it
def nt.lt(+f: U32, +Z: Nat, +eZ: {U32.to_nat(524287) == Z : Nat}, +ne: {U32.is_eq(f, 524287) == False{} : Bool},
  +b: N.Le(U32.to_nat(f), Z)) -> N.Le(1n+U32.to_nat(f), U32.to_nat(524287)):
  D.lt.ne(U32.cmp(f, 524287), U32.to_nat(f), U32.to_nat(524287), N.U32.rel(f, 524287), ne,
    N.le_rw_r(U32.to_nat(f), Z, U32.to_nat(524287), Equal.sym(Nat, U32.to_nat(524287), Z, eZ), b))

# The fv
# ------

# a part of fv f under k binders: f is fv_max, or the part's free
# variables are below k + f
def FvK(t: Bk.Term, +f: U32, +k: Nat) -> Bool:
  Bool.or(U32.is_eq(f, 524287), D.Term.below(t, Nat.add(k, U32.to_nat(f))))

# a part not of fv_max is below k + M, for M at least its fv
def side(+t: Bk.Term, +f: U32, +k: Nat, +M: U32, h: {FvK(t, f, k) == True{} : Bool}, ne: {U32.is_eq(f, 524287) == False{} : Bool},
  le: N.Le(U32.to_nat(f), U32.to_nat(M))) -> {D.Term.below(t, Nat.add(k, U32.to_nat(M))) == True{} : Bool}:
  CT.Tz.below_mono(t, Nat.add(k, U32.to_nat(f)), Nat.add(k, U32.to_nat(M)),
    toB(Nat.add(k, U32.to_nat(f)), Nat.add(k, U32.to_nat(M)), N.add_mono(k, k, U32.to_nat(f), U32.to_nat(M), N.le_refl(k), le)),
    or.rr(U32.is_eq(f, 524287), D.Term.below(t, Nat.add(k, U32.to_nat(f))), h, ne))

# the max of two numbers: at least each, at most a bound of both
def max.go(c: Bool, +fa: U32, +fb: U32, +Z: Nat, +ec: {U32.is_lt(fa, fb) == c : Bool}, +ba: N.Le(U32.to_nat(fa), Z),
  +bb: N.Le(U32.to_nat(fb), Z)) ->
  D.P2(N.Le(U32.to_nat(fa), U32.to_nat(Bool.pick(U32, c, fb, fa))),
  D.P2(N.Le(U32.to_nat(fb), U32.to_nat(Bool.pick(U32, c, fb, fa))), N.Le(U32.to_nat(Bool.pick(U32, c, fb, fa)), Z))):
  match c:
    case True{}:
      (N.weaken(U32.to_nat(fa), U32.to_nat(fb), D.u.lt(fa, fb, ec)), (N.le_refl(U32.to_nat(fb)), bb))
    case False{}:
      (N.le_refl(U32.to_nat(fa)), (nlt.le(fa, fb, ec), ba))

def max.of(+fa: U32, +fb: U32, +Z: Nat, +ba: N.Le(U32.to_nat(fa), Z), +bb: N.Le(U32.to_nat(fb), Z)) ->
  D.P2(N.Le(U32.to_nat(fa), U32.to_nat(U32.max(fa, fb))),
  D.P2(N.Le(U32.to_nat(fb), U32.to_nat(U32.max(fa, fb))), N.Le(U32.to_nat(U32.max(fa, fb)), Z))):
  %Equal.sym(U32, U32.max(fa, fb), Bool.pick(U32, U32.is_lt(fa, fb), fb, fa), max.pick(fa, fb)) :
    D.P2(N.Le(U32.to_nat(fa), U32.to_nat(_)), D.P2(N.Le(U32.to_nat(fb), U32.to_nat(_)), N.Le(U32.to_nat(_), Z)))
  max.go(U32.is_lt(fa, fb), fa, fb, Z, {==}, ba, bb)

# a node's fv M at most Z: it is fv_max, or P holds when M is below fv_max
def fv.cases(e: Bool, +M: U32, +Z: Nat, +eZ: {U32.to_nat(524287) == Z : Nat}, +P: Bool, +he: {U32.is_eq(M, 524287) == e : Bool},
  +bM: N.Le(U32.to_nat(M), Z), k: N.Le(1n+U32.to_nat(M), U32.to_nat(524287)) -> {P == True{} : Bool}) ->
  {Bool.or(U32.is_eq(M, 524287), P) == True{} : Bool}:
  match e:
    case True{}:
      %Equal.sym(Bool, U32.is_eq(M, 524287), True{}, he) : {Bool.or(_, P) == True{} : Bool}
      {==}
    case False{}:
      D.or.r(U32.is_eq(M, 524287), P, k(nt.lt(M, Z, eZ, he, bM)))

# a part of fv f under k binders, in a node of fv M below fv_max, f <= M:
# below k + M
def part(+t: Bk.Term, +f: U32, +k: Nat, +M: U32, h: {FvK(t, f, k) == True{} : Bool}, +g: N.Le(U32.to_nat(f), U32.to_nat(M)),
  lt: N.Le(1n+U32.to_nat(M), U32.to_nat(524287))) -> {D.Term.below(t, Nat.add(k, U32.to_nat(M))) == True{} : Bool}:
  side(t, f, k, M, h, IL.ne.to(f, 524287, N.le_trans(1n+U32.to_nat(f), 1n+U32.to_nat(M), U32.to_nat(524287), g, lt)), g)

# a node of two parts a and b, of fvs fa and fb under ka and kb binders:
# their max (of its bounds, max.of, given as a parameter: a match on a call
# is not Bend, a match on a parameter is)
def fv.max.go(+a: Bk.Term, +b: Bk.Term, +fa: U32, +fb: U32, +ka: Nat, +kb: Nat, +Z: Nat, +eZ: {U32.to_nat(524287) == Z : Nat},
  +ha: {FvK(a, fa, ka) == True{} : Bool}, +hb: {FvK(b, fb, kb) == True{} : Bool},
  +r: D.P2(N.Le(U32.to_nat(fa), U32.to_nat(U32.max(fa, fb))),
    D.P2(N.Le(U32.to_nat(fb), U32.to_nat(U32.max(fa, fb))), N.Le(U32.to_nat(U32.max(fa, fb)), Z)))) ->
  D.P2({Bool.or(U32.is_eq(U32.max(fa, fb), 524287), Bool.and(D.Term.below(a, Nat.add(ka, U32.to_nat(U32.max(fa, fb)))),
      D.Term.below(b, Nat.add(kb, U32.to_nat(U32.max(fa, fb)))))) == True{} : Bool},
    N.Le(U32.to_nat(U32.max(fa, fb)), Z)):
  (ga, q) = r
  (gb, bM) = q
  +M = U32.max(fa, fb)
  (fv.cases(U32.is_eq(M, 524287), M, Z, eZ, Bool.and(D.Term.below(a, Nat.add(ka, U32.to_nat(M))), D.Term.below(b, Nat.add(kb, U32.to_nat(M)))),
      {==}, bM,
      +lt => D.and.i(D.Term.below(a, Nat.add(ka, U32.to_nat(M))), D.Term.below(b, Nat.add(kb, U32.to_nat(M))),
        part(a, fa, ka, M, ha, ga, lt), part(b, fb, kb, M, hb, gb, lt))),
    bM)

def fv.max(+a: Bk.Term, +b: Bk.Term, +fa: U32, +fb: U32, +ka: Nat, +kb: Nat, +Z: Nat, +eZ: {U32.to_nat(524287) == Z : Nat},
  +ha: {FvK(a, fa, ka) == True{} : Bool}, +hb: {FvK(b, fb, kb) == True{} : Bool},
  +ba: N.Le(U32.to_nat(fa), Z), +bb: N.Le(U32.to_nat(fb), Z)) ->
  D.P2({Bool.or(U32.is_eq(U32.max(fa, fb), 524287), Bool.and(D.Term.below(a, Nat.add(ka, U32.to_nat(U32.max(fa, fb)))),
      D.Term.below(b, Nat.add(kb, U32.to_nat(U32.max(fa, fb)))))) == True{} : Bool},
    N.Le(U32.to_nat(U32.max(fa, fb)), Z)):
  fv.max.go(a, b, fa, fb, ka, kb, Z, eZ, ha, hb, max.of(fa, fb, Z, ba, bb))

# a node of three parts a, b and c: the max of their fvs (the two max.of
# pairs arrive as parameters, as in fv.max.go)
def fv.max3.go2(+a: Bk.Term, +b: Bk.Term, +c: Bk.Term, +fa: U32, +fb: U32, +fc: U32, +ka: Nat, +kb: Nat, +kc: Nat, +Z: Nat,
  +eZ: {U32.to_nat(524287) == Z : Nat},
  +ha: {FvK(a, fa, ka) == True{} : Bool}, +hb: {FvK(b, fb, kb) == True{} : Bool}, +hc: {FvK(c, fc, kc) == True{} : Bool},
  +bX: N.Le(U32.to_nat(U32.max(fb, fc)), Z), +gb2: N.Le(U32.to_nat(fb), U32.to_nat(U32.max(fb, fc))),
  +gc2: N.Le(U32.to_nat(fc), U32.to_nat(U32.max(fb, fc))),
  +r2: D.P2(N.Le(U32.to_nat(fa), U32.to_nat(U32.max(fa, U32.max(fb, fc)))),
    D.P2(N.Le(U32.to_nat(U32.max(fb, fc)), U32.to_nat(U32.max(fa, U32.max(fb, fc)))),
      N.Le(U32.to_nat(U32.max(fa, U32.max(fb, fc))), Z)))) ->
  D.P2({Bool.or(U32.is_eq(U32.max(fa, U32.max(fb, fc)), 524287), Bool.and(D.Term.below(a, Nat.add(ka, U32.to_nat(U32.max(fa, U32.max(fb, fc))))),
      Bool.and(D.Term.below(b, Nat.add(kb, U32.to_nat(U32.max(fa, U32.max(fb, fc))))),
        D.Term.below(c, Nat.add(kc, U32.to_nat(U32.max(fa, U32.max(fb, fc)))))))) == True{} : Bool},
    N.Le(U32.to_nat(U32.max(fa, U32.max(fb, fc))), Z)):
  (ga, q2) = r2
  (gX, bM) = q2
  +M = U32.max(fa, U32.max(fb, fc))
  +gb = N.le_trans(U32.to_nat(fb), U32.to_nat(U32.max(fb, fc)), U32.to_nat(M), gb2, gX)
  +gc = N.le_trans(U32.to_nat(fc), U32.to_nat(U32.max(fb, fc)), U32.to_nat(M), gc2, gX)
  +Pb = Bool.and(D.Term.below(b, Nat.add(kb, U32.to_nat(M))), D.Term.below(c, Nat.add(kc, U32.to_nat(M))))
  (fv.cases(U32.is_eq(M, 524287), M, Z, eZ, Bool.and(D.Term.below(a, Nat.add(ka, U32.to_nat(M))), Pb), {==}, bM,
      +lt => D.and.i(D.Term.below(a, Nat.add(ka, U32.to_nat(M))), Pb, part(a, fa, ka, M, ha, ga, lt),
        D.and.i(D.Term.below(b, Nat.add(kb, U32.to_nat(M))), D.Term.below(c, Nat.add(kc, U32.to_nat(M))),
          part(b, fb, kb, M, hb, gb, lt), part(c, fc, kc, M, hc, gc, lt)))),
    bM)

def fv.max3.go(+a: Bk.Term, +b: Bk.Term, +c: Bk.Term, +fa: U32, +fb: U32, +fc: U32, +ka: Nat, +kb: Nat, +kc: Nat, +Z: Nat,
  +eZ: {U32.to_nat(524287) == Z : Nat}, +ha: {FvK(a, fa, ka) == True{} : Bool}, +hb: {FvK(b, fb, kb) == True{} : Bool},
  +hc: {FvK(c, fc, kc) == True{} : Bool}, +ba: N.Le(U32.to_nat(fa), Z),
  +r1: D.P2(N.Le(U32.to_nat(fb), U32.to_nat(U32.max(fb, fc))),
    D.P2(N.Le(U32.to_nat(fc), U32.to_nat(U32.max(fb, fc))), N.Le(U32.to_nat(U32.max(fb, fc)), Z)))) ->
  D.P2({Bool.or(U32.is_eq(U32.max(fa, U32.max(fb, fc)), 524287), Bool.and(D.Term.below(a, Nat.add(ka, U32.to_nat(U32.max(fa, U32.max(fb, fc))))),
      Bool.and(D.Term.below(b, Nat.add(kb, U32.to_nat(U32.max(fa, U32.max(fb, fc))))),
        D.Term.below(c, Nat.add(kc, U32.to_nat(U32.max(fa, U32.max(fb, fc)))))))) == True{} : Bool},
    N.Le(U32.to_nat(U32.max(fa, U32.max(fb, fc))), Z)):
  (gb2, q1) = r1
  (gc2, bX) = q1
  fv.max3.go2(a, b, c, fa, fb, fc, ka, kb, kc, Z, eZ, ha, hb, hc, bX, gb2, gc2, max.of(fa, U32.max(fb, fc), Z, ba, bX))

def fv.max3(+a: Bk.Term, +b: Bk.Term, +c: Bk.Term, +fa: U32, +fb: U32, +fc: U32, +ka: Nat, +kb: Nat, +kc: Nat, +Z: Nat,
  +eZ: {U32.to_nat(524287) == Z : Nat}, +ha: {FvK(a, fa, ka) == True{} : Bool}, +hb: {FvK(b, fb, kb) == True{} : Bool},
  +hc: {FvK(c, fc, kc) == True{} : Bool}, +ba: N.Le(U32.to_nat(fa), Z), +bb: N.Le(U32.to_nat(fb), Z), +bc: N.Le(U32.to_nat(fc), Z)) ->
  D.P2({Bool.or(U32.is_eq(U32.max(fa, U32.max(fb, fc)), 524287), Bool.and(D.Term.below(a, Nat.add(ka, U32.to_nat(U32.max(fa, U32.max(fb, fc))))),
      Bool.and(D.Term.below(b, Nat.add(kb, U32.to_nat(U32.max(fa, U32.max(fb, fc))))),
        D.Term.below(c, Nat.add(kc, U32.to_nat(U32.max(fa, U32.max(fb, fc)))))))) == True{} : Bool},
    N.Le(U32.to_nat(U32.max(fa, U32.max(fb, fc))), Z)):
  fv.max3.go(a, b, c, fa, fb, fc, ka, kb, kc, Z, eZ, ha, hb, hc, ba, max.of(fb, fc, Z, bb, bc))

# a part under k binders: below k + its fv down by k (fv_max stays)
def fv.dn.gt(e2: Bool, +t: Bk.Term, +f: U32, +kU: U32, +k: Nat, +ek: {U32.to_nat(kU) == k : Nat}, +Z: Nat,
  +he2: {U32.is_gt(f, kU) == e2 : Bool}, +hbt: {D.Term.below(t, U32.to_nat(f)) == True{} : Bool}, +b: N.Le(U32.to_nat(f), Z)) ->
  D.P2({FvK(t, Bool.pick(U32, e2, U32.sub(f, kU), 0), k) == True{} : Bool}, N.Le(U32.to_nat(Bool.pick(U32, e2, U32.sub(f, kU), 0)), Z)):
  match e2:
    case True{}:
      +hk = {(%ek : N.Le(_, U32.to_nat(f)); N.weaken(U32.to_nat(kU), U32.to_nat(f), gt.lt(f, kU, he2))) : N.Le(k, U32.to_nat(f))}
      +es = {(%ek : {U32.to_nat(U32.sub(f, kU)) == Nat.sub(U32.to_nat(f), _) : Nat};
          FC.hf.sub.nat(f, kU, N.weaken(U32.to_nat(kU), U32.to_nat(f), gt.lt(f, kU, he2)))) :
        {U32.to_nat(U32.sub(f, kU)) == Nat.sub(U32.to_nat(f), k) : Nat}}
      +ea = Equal.trans(Nat, Nat.add(k, U32.to_nat(U32.sub(f, kU))), Nat.add(k, Nat.sub(U32.to_nat(f), k)), U32.to_nat(f),
        Equal.cong(Nat, Nat, z => Nat.add(k, z), U32.to_nat(U32.sub(f, kU)), Nat.sub(U32.to_nat(f), k), es), D.add.sub(k, U32.to_nat(f), hk))
      (D.or.r(U32.is_eq(U32.sub(f, kU), 524287), D.Term.below(t, Nat.add(k, U32.to_nat(U32.sub(f, kU)))),
          (%Equal.sym(Nat, Nat.add(k, U32.to_nat(U32.sub(f, kU))), U32.to_nat(f), ea) : {D.Term.below(t, _) == True{} : Bool}; hbt)),
        (%Equal.sym(Nat, U32.to_nat(U32.sub(f, kU)), Nat.sub(U32.to_nat(f), k), es) : N.Le(_, Z);
          N.le_trans(Nat.sub(U32.to_nat(f), k), U32.to_nat(f), Z, N.toLe(Nat.sub(U32.to_nat(f), k), U32.to_nat(f), CT.Tz.sub_le(U32.to_nat(f), k)), b)))
    case False{}:
      +hk = {(%ek : N.Le(U32.to_nat(f), _); ngt.le(f, kU, he2)) : N.Le(U32.to_nat(f), k)}
      (CT.Tz.below_mono(t, U32.to_nat(f), Nat.add(k, U32.to_nat(0)),
          toB(U32.to_nat(f), Nat.add(k, U32.to_nat(0)), N.le_trans(U32.to_nat(f), k, Nat.add(k, U32.to_nat(0)), hk, N.le_add_r(k, U32.to_nat(0)))),
          hbt),
        N.le_zero(Z))

def fv.dn.go(e1: Bool, +t: Bk.Term, +f: U32, +kU: U32, +k: Nat, +ek: {U32.to_nat(kU) == k : Nat}, +Z: Nat,
  +eZ: {U32.to_nat(524287) == Z : Nat}, +he1: {U32.is_eq(f, 524287) == e1 : Bool}, +h: {FvK(t, f, 0n) == True{} : Bool},
  +b: N.Le(U32.to_nat(f), Z)) ->
  D.P2({FvK(t, Bool.pick(U32, e1, 524287, Bool.pick(U32, U32.is_gt(f, kU), U32.sub(f, kU), 0)), k) == True{} : Bool},
    N.Le(U32.to_nat(Bool.pick(U32, e1, 524287, Bool.pick(U32, U32.is_gt(f, kU), U32.sub(f, kU), 0))), Z)):
  match e1:
    case True{}:
      ({==}, (%top.t(Bool.pick(U32, U32.is_gt(f, kU), U32.sub(f, kU), 0)) : N.Le(U32.to_nat(_), Z); top.le(Z, eZ)))
    case False{}:
      fv.dn.gt(U32.is_gt(f, kU), t, f, kU, k, ek, Z, {==}, or.rr(U32.is_eq(f, 524287), D.Term.below(t, U32.to_nat(f)), h, he1), b)

# a part of fv f under k binders, of the number of kU: Img.down(f, kU)
def fv.dn(+t: Bk.Term, +f: U32, +kU: U32, +k: Nat, +ek: {U32.to_nat(kU) == k : Nat}, +Z: Nat, +eZ: {U32.to_nat(524287) == Z : Nat},
  +h: {FvK(t, f, 0n) == True{} : Bool}, +b: N.Le(U32.to_nat(f), Z)) ->
  D.P2({FvK(t, Mc.Img.down(f, kU), k) == True{} : Bool}, N.Le(U32.to_nat(Mc.Img.down(f, kU)), Z)):
  fv.dn.go(U32.is_eq(f, 524287), t, f, kU, k, ek, Z, eZ, {==}, h, b)

# a Var's fv: 1 + its index, fv_max from 524286 on
def fv.var(b: Bool, +i: Nat, +B: Nat, +MB: U32, +hB: N.Le(B, U32.to_nat(MB)), +Z: Nat, +eZ: {U32.to_nat(524287) == Z : Nat},
  +eb: {U32.is_lt(U32.from_nat(i), 524286) == b : Bool}, +hv: {Nat.is_lt(i, B) == True{} : Bool}) ->
  D.P2({FvK(Bk.Term.Var{i}, Bool.pick(U32, b, U32.inc(U32.from_nat(i)), 524287), 0n) == True{} : Bool},
    N.Le(U32.to_nat(Bool.pick(U32, b, U32.inc(U32.from_nat(i)), 524287)), Z)):
  match b:
    case True{}:
      +u = U32.from_nat(i)
      +hlt = D.u.lt(u, 524286, eb)
      +ei = D.u.inc(u, 524286, hlt)
      +eu = MO.tofrom(i, MB, N.le_trans(i, B, U32.to_nat(MB), N.weaken(i, B, CK.Na.lt1(i, B, hv)), hB))
      +e = Equal.trans(Nat, U32.to_nat(U32.inc(u)), 1n+U32.to_nat(u), 1n+i, ei, Equal.cong(Nat, Nat, z => 1n+z, U32.to_nat(u), i, eu))
      (D.or.r(U32.is_eq(U32.inc(u), 524287), Nat.is_lt(i, U32.to_nat(U32.inc(u))),
          (%Equal.sym(Nat, U32.to_nat(U32.inc(u)), 1n+i, e) : {Nat.is_lt(i, _) == True{} : Bool}; lt.succ(i))),
        N.le_trans(U32.to_nat(U32.inc(u)), U32.to_nat(524286), Z,
          N.le_rw_l(1n+U32.to_nat(u), U32.to_nat(U32.inc(u)), U32.to_nat(524286), Equal.sym(Nat, U32.to_nat(U32.inc(u)), 1n+U32.to_nat(u), ei), hlt),
          N.weaken(U32.to_nat(524286), Z, top.lt(Z, eZ))))
    case False{}:
      ({==}, (%top.f(U32.inc(U32.from_nat(i))) : N.Le(U32.to_nat(_), Z); top.le(Z, eZ)))
