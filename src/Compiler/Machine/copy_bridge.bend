# compiler: layer B, the copy's premises, from copy_substitution.bend's Cp.ok (U5)
# ================================================================================
#
# copy.post and copy.done of move_kit.bend: from HS, AccK, Ag and the registers to Cp.ok's Pre, Tm, Env, Fits
# and Cp.W; and from Cp.ok's Post back to CopyQ, AccK and the budget.
# Filled by U5; U0 left each as ?TODO.
#
# Here so far: a cell that stands for a term (IsK), none of whose nodes is one
# of the cells X nor of the table, has that term as its checked term (Tm), the
# copy's view of a term (tm.is.at).

import Base
import ../../Book/impl.bend as Bk
import ../../Program/impl.bend as Pg
import ../Cir/impl.bend as Cr
import ./impl.bend as Mc
import ./cell_terms.bend as T
import ../need_big.bend as N
import ./definitions.bend as D
import ./copy_substitution.bend as S
import ./copy_kit.bend as CK
import ./copy_terms.bend as CT
import ./cell_stands_for.bend as CF
import ./checked_terms_stay.bend as TS
import ./move_kit.bend as K

# Free variables
# --------------
#
# NdK bounds a term's free variables by Term.below; the copy's FvOK by Fv,
# 1 + the highest one: the first gives the second.

# i < n gives 1 + i <= n
def lt.le(i: Nat, n: Nat, h: {Nat.is_lt(i, n) == True{} : Bool}) -> {Nat.is_le(1n+i, n) == True{} : Bool}:
  match i n:
    case 0n 0n:
      CK.Bo.tf({Nat.is_le(1n, 0n) == True{} : Bool}, h)
    case 0n 1n+np:
      CK.Na.le0(np)
    case 1n+ip 0n:
      CK.Bo.tf({Nat.is_le(2n+ip, 0n) == True{} : Bool}, h)
    case 1n+ip 1n+np:
      lt.le(ip, np, h)

# a <= n and b <= n give max(a, b) <= n
def max.le(a: Nat, b: Nat, n: Nat, ha: {Nat.is_le(a, n) == True{} : Bool}, hb: {Nat.is_le(b, n) == True{} : Bool}) ->
  {Nat.is_le(Nat.max(a, b), n) == True{} : Bool}:
  match a b:
    case 0n 0n:
      hb
    case 0n 1n+bp:
      hb
    case 1n+ap 0n:
      ha
    case 1n+ap 1n+bp:
      match n:
        case 0n:
          CK.Bo.tf({Nat.is_le(1n+Nat.max(ap, bp), 0n) == True{} : Bool}, ha)
        case 1n+np:
          max.le(ap, bp, np, ha, hb)

# a <= 1 + n gives a - 1 <= n
def sub1.le(a: Nat, n: Nat, h: {Nat.is_le(a, 1n+n) == True{} : Bool}) -> {Nat.is_le(Nat.sub(a, 1n), n) == True{} : Bool}:
  match a:
    case 0n:
      CK.Na.le0(n)
    case 1n+ap:
      %Equal.sym(Nat, Nat.sub(ap, 0n), ap, CT.Tz.sub0(ap)) : {Nat.is_le(_, n) == True{} : Bool}
      h

# a <= 2 + n gives a - 2 <= n
def sub2.le(a: Nat, n: Nat, h: {Nat.is_le(a, 2n+n) == True{} : Bool}) -> {Nat.is_le(Nat.sub(a, 2n), n) == True{} : Bool}:
  match a:
    case 0n:
      CK.Na.le0(n)
    case 1n+ap:
      sub1.le(ap, n, h)

# every free variable of t below n: Fv(t) <= n
def below.fv(t: Bk.Term, +n: Nat, +h: {D.Term.below(t, n) == True{} : Bool}) -> {Nat.is_le(S.Fv(t), n) == True{} : Bool}:
  match t:
    case Bk.Term.Var{+i}:
      lt.le(i, n, h)
    case Bk.Term.Ref{_}:
      CK.Na.le0(n)
    case Bk.Term.Ann{+x, +y}:
      max.le(S.Fv(x), S.Fv(y), n, below.fv(x, n, CK.Bo.and_l(D.Term.below(x, n), D.Term.below(y, n), h)),
        below.fv(y, n, CK.Bo.and_r(D.Term.below(x, n), D.Term.below(y, n), h)))
    case Bk.Term.Let{_, +x, +y}:
      max.le(S.Fv(x), Nat.sub(S.Fv(y), 1n), n, below.fv(x, n, CK.Bo.and_l(D.Term.below(x, n), D.Term.below(y, 1n+n), h)),
        sub1.le(S.Fv(y), n, below.fv(y, 1n+n, CK.Bo.and_r(D.Term.below(x, n), D.Term.below(y, 1n+n), h))))
    case Bk.Term.Typ{+x}:
      below.fv(x, n, h)
    case Bk.Term.Min{+x, +y}:
      max.le(S.Fv(x), S.Fv(y), n, below.fv(x, n, CK.Bo.and_l(D.Term.below(x, n), D.Term.below(y, n), h)),
        below.fv(y, n, CK.Bo.and_r(D.Term.below(x, n), D.Term.below(y, n), h)))
    case Bk.Term.All{_, +x, +y}:
      max.le(S.Fv(x), Nat.sub(S.Fv(y), 1n), n, below.fv(x, n, CK.Bo.and_l(D.Term.below(x, n), D.Term.below(y, 1n+n), h)),
        sub1.le(S.Fv(y), n, below.fv(y, 1n+n, CK.Bo.and_r(D.Term.below(x, n), D.Term.below(y, 1n+n), h))))
    case Bk.Term.Lam{_, +y}:
      sub1.le(S.Fv(y), n, below.fv(y, 1n+n, h))
    case Bk.Term.App{_, +x, +y}:
      max.le(S.Fv(x), S.Fv(y), n, below.fv(x, n, CK.Bo.and_l(D.Term.below(x, n), D.Term.below(y, n), h)),
        below.fv(y, n, CK.Bo.and_r(D.Term.below(x, n), D.Term.below(y, n), h)))
    case Bk.Term.Sig{_, +x, +y}:
      max.le(S.Fv(x), Nat.sub(S.Fv(y), 1n), n, below.fv(x, n, CK.Bo.and_l(D.Term.below(x, n), D.Term.below(y, 1n+n), h)),
        sub1.le(S.Fv(y), n, below.fv(y, 1n+n, CK.Bo.and_r(D.Term.below(x, n), D.Term.below(y, 1n+n), h))))
    case Bk.Term.Tup{_, +x, +y}:
      max.le(S.Fv(x), S.Fv(y), n, below.fv(x, n, CK.Bo.and_l(D.Term.below(x, n), D.Term.below(y, n), h)),
        below.fv(y, n, CK.Bo.and_r(D.Term.below(x, n), D.Term.below(y, n), h)))
    case Bk.Term.Prj{+x}:
      below.fv(x, n, h)
    case Bk.Term.Enu{_}:
      CK.Na.le0(n)
    case Bk.Term.Lab{_}:
      CK.Na.le0(n)
    case Bk.Term.Mat{_, +x, +y}:
      max.le(S.Fv(x), S.Fv(y), n, below.fv(x, n, CK.Bo.and_l(D.Term.below(x, n), D.Term.below(y, n), h)),
        below.fv(y, n, CK.Bo.and_r(D.Term.below(x, n), D.Term.below(y, n), h)))
    case Bk.Term.Efq{}:
      CK.Na.le0(n)
    case Bk.Term.Eql{+x, +y, +z}:
      +r = CK.Bo.and_r(D.Term.below(x, n), Bool.and(D.Term.below(y, n), D.Term.below(z, n)), h)
      max.le(S.Fv(x), Nat.max(S.Fv(y), S.Fv(z)), n,
        below.fv(x, n, CK.Bo.and_l(D.Term.below(x, n), Bool.and(D.Term.below(y, n), D.Term.below(z, n)), h)),
        max.le(S.Fv(y), S.Fv(z), n, below.fv(y, n, CK.Bo.and_l(D.Term.below(y, n), D.Term.below(z, n), r)),
          below.fv(z, n, CK.Bo.and_r(D.Term.below(y, n), D.Term.below(z, n), r))))
    case Bk.Term.Rfl{}:
      CK.Na.le0(n)
    case Bk.Term.Rwt{+x, +y, +z}:
      +r = CK.Bo.and_r(D.Term.below(x, n), Bool.and(D.Term.below(y, 2n+n), D.Term.below(z, n)), h)
      max.le(S.Fv(x), Nat.max(Nat.sub(S.Fv(y), 2n), S.Fv(z)), n,
        below.fv(x, n, CK.Bo.and_l(D.Term.below(x, n), Bool.and(D.Term.below(y, 2n+n), D.Term.below(z, n)), h)),
        max.le(Nat.sub(S.Fv(y), 2n), S.Fv(z), n,
          sub2.le(S.Fv(y), n, below.fv(y, 2n+n, CK.Bo.and_l(D.Term.below(y, 2n+n), D.Term.below(z, n), r))),
          below.fv(z, n, CK.Bo.and_r(D.Term.below(y, 2n+n), D.Term.below(z, n), r))))

# NdK's bound on the free variables gives FvOK's (a tag with fv)
def fv.ok(b: Bool, t: Bk.Term, +n: Nat, h: {Bool.or(b, D.Term.below(t, n)) == True{} : Bool}) ->
  {Bool.or(b, Nat.is_le(S.Fv(t), n)) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      below.fv(t, n, h)

# a fv of 0 is zero
def zero.ok(+v: U32, e: {v == 0 : U32}) -> {U32.is_zero(v) == True{} : Bool}:
  %Equal.sym(U32, v, 0, e) : {U32.is_zero(_) == True{} : Bool}
  {==}

# Checked terms of the machine's terms
# ------------------------------------

# the run may read y, as far as the cells X and the table go
def Rx(+X: List<&2, U32>, +y: U32) -> Bool:
  Bool.and(Bool.not(S.Has(X, y)), Bool.not(S.Tbc(y)))

# what NdK says of a node: a cell, its tag, its free variables below its fv
def nk.cell(-dk: Bool, -ds: List<&2, Bk.Def>, -im: U32, -fi: U32, -nx: U32, -c: U32, -x: Cr.Cir.Cell, -t: Bk.Term, -tag: U32,
  h: D.NdK(dk, ds, im, fi, nx, c, x, t, tag)) -> {Cr.Cir.is_cell(c, im, fi, nx) == True{} : Bool}:
  (e, r) = h
  e

def nk.tag(-dk: Bool, -ds: List<&2, Bk.Def>, -im: U32, -fi: U32, -nx: U32, -c: U32, -x: Cr.Cir.Cell, -t: Bk.Term, -tag: U32,
  h: D.NdK(dk, ds, im, fi, nx, c, x, t, tag)) -> {D.TgW(Cr.Cir.Cell.get(0n, x)) == tag : U32}:
  (e0, r0) = h
  (e1, r1) = r0
  (e, r) = r1
  e

def nk.ok(-dk: Bool, -ds: List<&2, Bk.Def>, -im: U32, -fi: U32, -nx: U32, -c: U32, +x: Cr.Cir.Cell, t: Bk.Term, -tag: U32,
  h: D.NdK(dk, ds, im, fi, nx, c, x, t, tag)) ->
  {Bool.or(U32.is_eq(D.FvW(Cr.Cir.Cell.get(0n, x)), 524287), Nat.is_le(S.Fv(t), U32.to_nat(D.FvW(Cr.Cir.Cell.get(0n, x))))) == True{} : Bool}:
  (e0, r0) = h
  (e1, r1) = r0
  (e2, r2) = r1
  (e3, r3) = r2
  (e4, r4) = r3
  fv.ok(U32.is_eq(D.FvW(Cr.Cir.Cell.get(0n, x)), 524287), t, U32.to_nat(D.FvW(Cr.Cir.Cell.get(0n, x))), r4)

# the checked term one level down, at a cell that may be read, of the tag tg:
# T.tm.cell of its parts' checked terms, when its fv is right for t
def tm.at(+g: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +K: U32, +F: U32,
  +X: List<&2, U32>, +N: U32, +c: U32, +tg: U32, -t: Bk.Term, ha: {S.Al(K, F, X, N, c) == True{} : Bool},
  e: {D.Tg(m, c) == tg : U32},
  hc: {T.tm.cell(U32.to_nat(tg), T.tm.quan(D.Qn(m, c)), c, D.Fd(2n, m, c), ks, img,
    u => S.Tm(g, m, ks, img, K, F, X, N, D.Fd(2n, m, c)), u => S.Tm(g, m, ks, img, K, F, X, N, D.Fd(3n, m, c)),
    u => S.Tm(g, m, ks, img, K, F, X, N, D.Fd(4n, m, c))) == Some{t} : Maybe<&2, Bk.Term>},
  hf: {S.FvOK(U32.to_nat(tg), D.Fv(m, c), t) == True{} : Bool}) ->
  {S.Tm(1n+g, m, ks, img, K, F, X, N, c) == Some{t} : Maybe<&2, Bk.Term>}:
  %Equal.sym(Bool, S.Al(K, F, X, N, c), True{}, ha) :
    {TS.Tm.at.b(_, g, m, ks, img, K, F, X, N, c, Cr.Cir.Cells.get(m, c)) == Some{t} : Maybe<&2, Bk.Term>}
  %Equal.sym(U32, D.Tg(m, c), tg, e) :
    {S.Tm.chk(U32.to_nat(_), D.Fv(m, c), T.tm.cell(U32.to_nat(_), T.tm.quan(D.Qn(m, c)), c, D.Fd(2n, m, c), ks, img,
      u => S.Tm(g, m, ks, img, K, F, X, N, D.Fd(2n, m, c)), u => S.Tm(g, m, ks, img, K, F, X, N, D.Fd(3n, m, c)),
      u => S.Tm(g, m, ks, img, K, F, X, N, D.Fd(4n, m, c)))) == Some{t} : Maybe<&2, Bk.Term>}
  %Equal.sym(Maybe<&2, Bk.Term>, T.tm.cell(U32.to_nat(tg), T.tm.quan(D.Qn(m, c)), c, D.Fd(2n, m, c), ks, img,
      u => S.Tm(g, m, ks, img, K, F, X, N, D.Fd(2n, m, c)), u => S.Tm(g, m, ks, img, K, F, X, N, D.Fd(3n, m, c)),
      u => S.Tm(g, m, ks, img, K, F, X, N, D.Fd(4n, m, c))), Some{t}, hc) :
    {S.Tm.chk(U32.to_nat(tg), D.Fv(m, c), _) == Some{t} : Maybe<&2, Bk.Term>}
  %Equal.sym(Bool, S.FvOK(U32.to_nat(tg), D.Fv(m, c), t), True{}, hf) : {S.Tm.ok(_, t) == Some{t} : Maybe<&2, Bk.Term>}
  {==}

# a node of the tag tg, which NdK says is a cell, and which the run may read
def tm.node(+g: Nat, +dk: Bool, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +X: List<&2, U32>, +c: U32, +tg: U32, -t: Bk.Term,
  +nd: D.NdK(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), t, tg), hr: {Rx(X, c) == True{} : Bool},
  hc: {T.tm.cell(U32.to_nat(tg), T.tm.quan(D.Qn(m, c)), c, D.Fd(2n, m, c), ks, img,
    u => S.Tm(g, m, ks, img, im, fi, X, nx, D.Fd(2n, m, c)), u => S.Tm(g, m, ks, img, im, fi, X, nx, D.Fd(3n, m, c)),
    u => S.Tm(g, m, ks, img, im, fi, X, nx, D.Fd(4n, m, c))) == Some{t} : Maybe<&2, Bk.Term>},
  hf: {S.FvOK(U32.to_nat(tg), D.Fv(m, c), t) == True{} : Bool}) ->
  {S.Tm(1n+g, m, ks, img, im, fi, X, nx, c) == Some{t} : Maybe<&2, Bk.Term>}:
  tm.at(g, m, ks, img, im, fi, X, nx, c, tg, t,
    CK.Bo.and_i(Cr.Cir.is_cell(c, im, fi, nx), Rx(X, c), nk.cell(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), t, tg, nd), hr),
    nk.tag(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), t, tg, nd), hc, hf)

# no node of the term t at r is one of X nor of the table (Rx)
def Rx.all(t: Bk.Term, +m: Cr.Cir.Cells, +r: U32, +X: List<&2, U32>) -> Bool:
  match t:
    case Bk.Term.Var{_}:
      Rx(X, r)
    case Bk.Term.Ref{_}:
      Rx(X, r)
    case Bk.Term.Ann{y, z}:
      Bool.and(Rx(X, r), Bool.and(Rx.all(y, m, D.Fd(2n, m, r), X), Rx.all(z, m, D.Fd(3n, m, r), X)))
    case Bk.Term.Let{_, y, z}:
      Bool.and(Rx(X, r), Bool.and(Rx.all(y, m, D.Fd(2n, m, r), X), Rx.all(z, m, D.Fd(3n, m, r), X)))
    case Bk.Term.Typ{y}:
      Bool.and(Rx(X, r), Rx.all(y, m, D.Fd(2n, m, r), X))
    case Bk.Term.Min{y, z}:
      Bool.and(Rx(X, r), Bool.and(Rx.all(y, m, D.Fd(2n, m, r), X), Rx.all(z, m, D.Fd(3n, m, r), X)))
    case Bk.Term.All{_, y, z}:
      Bool.and(Rx(X, r), Bool.and(Rx.all(y, m, D.Fd(2n, m, r), X), Rx.all(z, m, D.Fd(3n, m, r), X)))
    case Bk.Term.Lam{_, y}:
      Bool.and(Rx(X, r), Rx.all(y, m, D.Fd(2n, m, r), X))
    case Bk.Term.App{_, y, z}:
      Bool.and(Rx(X, r), Bool.and(Rx.all(y, m, D.Fd(2n, m, r), X), Rx.all(z, m, D.Fd(3n, m, r), X)))
    case Bk.Term.Sig{_, y, z}:
      Bool.and(Rx(X, r), Bool.and(Rx.all(y, m, D.Fd(2n, m, r), X), Rx.all(z, m, D.Fd(3n, m, r), X)))
    case Bk.Term.Tup{_, y, z}:
      Bool.and(Rx(X, r), Bool.and(Rx.all(y, m, D.Fd(2n, m, r), X), Rx.all(z, m, D.Fd(3n, m, r), X)))
    case Bk.Term.Prj{y}:
      Bool.and(Rx(X, r), Rx.all(y, m, D.Fd(2n, m, r), X))
    case Bk.Term.Enu{_}:
      Rx(X, r)
    case Bk.Term.Lab{_}:
      Rx(X, r)
    case Bk.Term.Mat{_, y, z}:
      Bool.and(Rx(X, r), Bool.and(Rx.all(y, m, D.Fd(3n, m, r), X), Rx.all(z, m, D.Fd(4n, m, r), X)))
    case Bk.Term.Efq{}:
      Rx(X, r)
    case Bk.Term.Eql{y, z, w}:
      Bool.and(Rx(X, r), Bool.and(Rx.all(y, m, D.Fd(2n, m, r), X), Bool.and(Rx.all(z, m, D.Fd(3n, m, r), X), Rx.all(w, m, D.Fd(4n, m, r), X))))
    case Bk.Term.Rfl{}:
      Rx(X, r)
    case Bk.Term.Rwt{y, z, w}:
      Bool.and(Rx(X, r), Bool.and(Rx.all(y, m, D.Fd(2n, m, r), X), Bool.and(Rx.all(z, m, D.Fd(3n, m, r), X), Rx.all(w, m, D.Fd(4n, m, r), X))))

# the cell c stands for t (IsK, with any meaning of DATA) and no node of t is
# one of X nor of the table (Rx.all): its checked term, with any fuel f that is at
# least t's size, is t
def tm.is.at(+f: Nat, +dk: Bool, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +X: List<&2, U32>, +c: U32, t: Bk.Term,
  +le: N.Le(Pg.Term.size(t), f), +h: D.IsK(dk, ds, m, im, fi, nx, ks, img, c, t),
  +hx: {Rx.all(t, m, c, X) == True{} : Bool}) ->
  {S.Tm(f, m, ks, img, im, fi, X, nx, c) == Some{t} : Maybe<&2, Bk.Term>}:
  match f:
    case 0n:
      Empty.absurd({S.Tm(0n, m, ks, img, im, fi, X, nx, c) == Some{t} : Maybe<&2, Bk.Term>}, CF.size.nz(t, le))
    case 1n+(+g):
      match t:
        case Bk.Term.Var{+i}:
          (+nd, ei) = h
          tm.node(g, dk, ds, m, im, fi, nx, ks, img, X, c, 0, Bk.Term.Var{i}, nd, hx,
            Equal.cong(Nat, Maybe<&2, Bk.Term>, j => Some{Bk.Term.Var{j}}, U32.to_nat(D.Fd(2n, m, c)), i, ei),
            nk.ok(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Var{i}, 0, nd))
        case Bk.Term.Ref{+k}:
          (+nd, r) = h
          (ei, r2) = r
          (ez, ef) = r2
          tm.node(g, dk, ds, m, im, fi, nx, ks, img, X, c, 1, Bk.Term.Ref{k}, nd, hx,
            ei,
            zero.ok(D.FvW(Cr.Cir.Cell.get(0n, Cr.Cir.Cells.get(m, c))), ez))
        case Bk.Term.Ann{+y, +z}:
          (+nd, r) = h
          (py, pz) = r
          (sy, hy) = py
          (sz, hz) = pz
          +hp = CK.Bo.and_r(Rx(X, c), Bool.and(Rx.all(y, m, D.Fd(2n, m, c), X), Rx.all(z, m, D.Fd(3n, m, c), X)), hx)
          tm.node(g, dk, ds, m, im, fi, nx, ks, img, X, c, 2, Bk.Term.Ann{y, z}, nd, CK.Bo.and_l(Rx(X, c), Bool.and(Rx.all(y, m, D.Fd(2n, m, c), X), Rx.all(z, m, D.Fd(3n, m, c), X)), hx),
            CF.two.of(a => d => Bk.Term.Ann{a, d}, S.Tm(g, m, ks, img, im, fi, X, nx, D.Fd(2n, m, c)), S.Tm(g, m, ks, img, im, fi, X, nx, D.Fd(3n, m, c)), y, z, Bk.Term.Ann{y, z},
            tm.is.at(g, dk, ds, m, im, fi, nx, ks, img, X, D.Fd(2n, m, c), y, CF.le.l(Pg.Term.size(y), Pg.Term.size(z), g, le), hy,
              CK.Bo.and_l(Rx.all(y, m, D.Fd(2n, m, c), X), Rx.all(z, m, D.Fd(3n, m, c), X), hp)),
            tm.is.at(g, dk, ds, m, im, fi, nx, ks, img, X, D.Fd(3n, m, c), z, CF.le.r(Pg.Term.size(y), Pg.Term.size(z), g, le), hz,
              CK.Bo.and_r(Rx.all(y, m, D.Fd(2n, m, c), X), Rx.all(z, m, D.Fd(3n, m, c), X), hp)),
            {==}),
            nk.ok(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Ann{y, z}, 2, nd))
        case Bk.Term.Let{+q, +y, +z}:
          (+nd, r) = h
          (hq, r2) = r
          (py, pz) = r2
          (sy, hy) = py
          (sz, hz) = pz
          +hp = CK.Bo.and_r(Rx(X, c), Bool.and(Rx.all(y, m, D.Fd(2n, m, c), X), Rx.all(z, m, D.Fd(3n, m, c), X)), hx)
          tm.node(g, dk, ds, m, im, fi, nx, ks, img, X, c, 3, Bk.Term.Let{q, y, z}, nd, CK.Bo.and_l(Rx(X, c), Bool.and(Rx.all(y, m, D.Fd(2n, m, c), X), Rx.all(z, m, D.Fd(3n, m, c), X)), hx),
            CF.two.of(a => d => Bk.Term.Let{T.tm.quan(D.Qn(m, c)), a, d}, S.Tm(g, m, ks, img, im, fi, X, nx, D.Fd(2n, m, c)), S.Tm(g, m, ks, img, im, fi, X, nx, D.Fd(3n, m, c)), y, z, Bk.Term.Let{q, y, z},
            tm.is.at(g, dk, ds, m, im, fi, nx, ks, img, X, D.Fd(2n, m, c), y, CF.le.l(Pg.Term.size(y), Pg.Term.size(z), g, le), hy,
              CK.Bo.and_l(Rx.all(y, m, D.Fd(2n, m, c), X), Rx.all(z, m, D.Fd(3n, m, c), X), hp)),
            tm.is.at(g, dk, ds, m, im, fi, nx, ks, img, X, D.Fd(3n, m, c), z, CF.le.r(Pg.Term.size(y), Pg.Term.size(z), g, le), hz,
              CK.Bo.and_r(Rx.all(y, m, D.Fd(2n, m, c), X), Rx.all(z, m, D.Fd(3n, m, c), X), hp)),
            Equal.cong(Bk.Quan, Bk.Term, p => Bk.Term.Let{p, y, z}, T.tm.quan(D.Qn(m, c)), q, CF.quan.of(Cr.Cir.Cells.get(m, c), q, hq))),
            nk.ok(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Let{q, y, z}, 3, nd))
        case Bk.Term.Typ{+y}:
          (+nd, r) = h
          (sy, hy) = r
          tm.node(g, dk, ds, m, im, fi, nx, ks, img, X, c, 4, Bk.Term.Typ{y}, nd, CK.Bo.and_l(Rx(X, c), Rx.all(y, m, D.Fd(2n, m, c), X), hx),
            CF.one.of(a => Bk.Term.Typ{a}, S.Tm(g, m, ks, img, im, fi, X, nx, D.Fd(2n, m, c)), y, Bk.Term.Typ{y},
            tm.is.at(g, dk, ds, m, im, fi, nx, ks, img, X, D.Fd(2n, m, c), y, le, hy,
              CK.Bo.and_r(Rx(X, c), Rx.all(y, m, D.Fd(2n, m, c), X), hx)), {==}),
            nk.ok(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Typ{y}, 4, nd))
        case Bk.Term.Min{+y, +z}:
          (+nd, r) = h
          (py, pz) = r
          (sy, hy) = py
          (sz, hz) = pz
          +hp = CK.Bo.and_r(Rx(X, c), Bool.and(Rx.all(y, m, D.Fd(2n, m, c), X), Rx.all(z, m, D.Fd(3n, m, c), X)), hx)
          tm.node(g, dk, ds, m, im, fi, nx, ks, img, X, c, 5, Bk.Term.Min{y, z}, nd, CK.Bo.and_l(Rx(X, c), Bool.and(Rx.all(y, m, D.Fd(2n, m, c), X), Rx.all(z, m, D.Fd(3n, m, c), X)), hx),
            CF.two.of(a => d => Bk.Term.Min{a, d}, S.Tm(g, m, ks, img, im, fi, X, nx, D.Fd(2n, m, c)), S.Tm(g, m, ks, img, im, fi, X, nx, D.Fd(3n, m, c)), y, z, Bk.Term.Min{y, z},
            tm.is.at(g, dk, ds, m, im, fi, nx, ks, img, X, D.Fd(2n, m, c), y, CF.le.l(Pg.Term.size(y), Pg.Term.size(z), g, le), hy,
              CK.Bo.and_l(Rx.all(y, m, D.Fd(2n, m, c), X), Rx.all(z, m, D.Fd(3n, m, c), X), hp)),
            tm.is.at(g, dk, ds, m, im, fi, nx, ks, img, X, D.Fd(3n, m, c), z, CF.le.r(Pg.Term.size(y), Pg.Term.size(z), g, le), hz,
              CK.Bo.and_r(Rx.all(y, m, D.Fd(2n, m, c), X), Rx.all(z, m, D.Fd(3n, m, c), X), hp)),
            {==}),
            nk.ok(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Min{y, z}, 5, nd))
        case Bk.Term.All{+q, +y, +z}:
          (+nd, r) = h
          (hq, r2) = r
          (py, pz) = r2
          (sy, hy) = py
          (sz, hz) = pz
          +hp = CK.Bo.and_r(Rx(X, c), Bool.and(Rx.all(y, m, D.Fd(2n, m, c), X), Rx.all(z, m, D.Fd(3n, m, c), X)), hx)
          tm.node(g, dk, ds, m, im, fi, nx, ks, img, X, c, 6, Bk.Term.All{q, y, z}, nd, CK.Bo.and_l(Rx(X, c), Bool.and(Rx.all(y, m, D.Fd(2n, m, c), X), Rx.all(z, m, D.Fd(3n, m, c), X)), hx),
            CF.two.of(a => d => Bk.Term.All{T.tm.quan(D.Qn(m, c)), a, d}, S.Tm(g, m, ks, img, im, fi, X, nx, D.Fd(2n, m, c)), S.Tm(g, m, ks, img, im, fi, X, nx, D.Fd(3n, m, c)), y, z, Bk.Term.All{q, y, z},
            tm.is.at(g, dk, ds, m, im, fi, nx, ks, img, X, D.Fd(2n, m, c), y, CF.le.l(Pg.Term.size(y), Pg.Term.size(z), g, le), hy,
              CK.Bo.and_l(Rx.all(y, m, D.Fd(2n, m, c), X), Rx.all(z, m, D.Fd(3n, m, c), X), hp)),
            tm.is.at(g, dk, ds, m, im, fi, nx, ks, img, X, D.Fd(3n, m, c), z, CF.le.r(Pg.Term.size(y), Pg.Term.size(z), g, le), hz,
              CK.Bo.and_r(Rx.all(y, m, D.Fd(2n, m, c), X), Rx.all(z, m, D.Fd(3n, m, c), X), hp)),
            Equal.cong(Bk.Quan, Bk.Term, p => Bk.Term.All{p, y, z}, T.tm.quan(D.Qn(m, c)), q, CF.quan.of(Cr.Cir.Cells.get(m, c), q, hq))),
            nk.ok(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.All{q, y, z}, 6, nd))
        case Bk.Term.Lam{+q, +y}:
          (+nd, r) = h
          (hq, r2) = r
          (sy, hy) = r2
          tm.node(g, dk, ds, m, im, fi, nx, ks, img, X, c, 7, Bk.Term.Lam{q, y}, nd, CK.Bo.and_l(Rx(X, c), Rx.all(y, m, D.Fd(2n, m, c), X), hx),
            CF.one.of(a => Bk.Term.Lam{T.tm.quan(D.Qn(m, c)), a}, S.Tm(g, m, ks, img, im, fi, X, nx, D.Fd(2n, m, c)), y, Bk.Term.Lam{q, y},
            tm.is.at(g, dk, ds, m, im, fi, nx, ks, img, X, D.Fd(2n, m, c), y, le, hy,
              CK.Bo.and_r(Rx(X, c), Rx.all(y, m, D.Fd(2n, m, c), X), hx)),
            Equal.cong(Bk.Quan, Bk.Term, p => Bk.Term.Lam{p, y}, T.tm.quan(D.Qn(m, c)), q, CF.quan.of(Cr.Cir.Cells.get(m, c), q, hq))),
            nk.ok(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Lam{q, y}, 7, nd))
        case Bk.Term.App{+q, +y, +z}:
          (+nd, r) = h
          (hq, r2) = r
          (py, pz) = r2
          (sy, hy) = py
          (sz, hz) = pz
          +hp = CK.Bo.and_r(Rx(X, c), Bool.and(Rx.all(y, m, D.Fd(2n, m, c), X), Rx.all(z, m, D.Fd(3n, m, c), X)), hx)
          tm.node(g, dk, ds, m, im, fi, nx, ks, img, X, c, 8, Bk.Term.App{q, y, z}, nd, CK.Bo.and_l(Rx(X, c), Bool.and(Rx.all(y, m, D.Fd(2n, m, c), X), Rx.all(z, m, D.Fd(3n, m, c), X)), hx),
            CF.two.of(a => d => Bk.Term.App{T.tm.quan(D.Qn(m, c)), a, d}, S.Tm(g, m, ks, img, im, fi, X, nx, D.Fd(2n, m, c)), S.Tm(g, m, ks, img, im, fi, X, nx, D.Fd(3n, m, c)), y, z, Bk.Term.App{q, y, z},
            tm.is.at(g, dk, ds, m, im, fi, nx, ks, img, X, D.Fd(2n, m, c), y, CF.le.l(Pg.Term.size(y), Pg.Term.size(z), g, le), hy,
              CK.Bo.and_l(Rx.all(y, m, D.Fd(2n, m, c), X), Rx.all(z, m, D.Fd(3n, m, c), X), hp)),
            tm.is.at(g, dk, ds, m, im, fi, nx, ks, img, X, D.Fd(3n, m, c), z, CF.le.r(Pg.Term.size(y), Pg.Term.size(z), g, le), hz,
              CK.Bo.and_r(Rx.all(y, m, D.Fd(2n, m, c), X), Rx.all(z, m, D.Fd(3n, m, c), X), hp)),
            Equal.cong(Bk.Quan, Bk.Term, p => Bk.Term.App{p, y, z}, T.tm.quan(D.Qn(m, c)), q, CF.quan.of(Cr.Cir.Cells.get(m, c), q, hq))),
            nk.ok(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.App{q, y, z}, 8, nd))
        case Bk.Term.Sig{+q, +y, +z}:
          (+nd, r) = h
          (hq, r2) = r
          (py, pz) = r2
          (sy, hy) = py
          (sz, hz) = pz
          +hp = CK.Bo.and_r(Rx(X, c), Bool.and(Rx.all(y, m, D.Fd(2n, m, c), X), Rx.all(z, m, D.Fd(3n, m, c), X)), hx)
          tm.node(g, dk, ds, m, im, fi, nx, ks, img, X, c, 9, Bk.Term.Sig{q, y, z}, nd, CK.Bo.and_l(Rx(X, c), Bool.and(Rx.all(y, m, D.Fd(2n, m, c), X), Rx.all(z, m, D.Fd(3n, m, c), X)), hx),
            CF.two.of(a => d => Bk.Term.Sig{T.tm.quan(D.Qn(m, c)), a, d}, S.Tm(g, m, ks, img, im, fi, X, nx, D.Fd(2n, m, c)), S.Tm(g, m, ks, img, im, fi, X, nx, D.Fd(3n, m, c)), y, z, Bk.Term.Sig{q, y, z},
            tm.is.at(g, dk, ds, m, im, fi, nx, ks, img, X, D.Fd(2n, m, c), y, CF.le.l(Pg.Term.size(y), Pg.Term.size(z), g, le), hy,
              CK.Bo.and_l(Rx.all(y, m, D.Fd(2n, m, c), X), Rx.all(z, m, D.Fd(3n, m, c), X), hp)),
            tm.is.at(g, dk, ds, m, im, fi, nx, ks, img, X, D.Fd(3n, m, c), z, CF.le.r(Pg.Term.size(y), Pg.Term.size(z), g, le), hz,
              CK.Bo.and_r(Rx.all(y, m, D.Fd(2n, m, c), X), Rx.all(z, m, D.Fd(3n, m, c), X), hp)),
            Equal.cong(Bk.Quan, Bk.Term, p => Bk.Term.Sig{p, y, z}, T.tm.quan(D.Qn(m, c)), q, CF.quan.of(Cr.Cir.Cells.get(m, c), q, hq))),
            nk.ok(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Sig{q, y, z}, 9, nd))
        case Bk.Term.Tup{+q, +y, +z}:
          (+nd, r) = h
          (hq, r2) = r
          (py, pz) = r2
          (sy, hy) = py
          (sz, hz) = pz
          +hp = CK.Bo.and_r(Rx(X, c), Bool.and(Rx.all(y, m, D.Fd(2n, m, c), X), Rx.all(z, m, D.Fd(3n, m, c), X)), hx)
          tm.node(g, dk, ds, m, im, fi, nx, ks, img, X, c, 10, Bk.Term.Tup{q, y, z}, nd, CK.Bo.and_l(Rx(X, c), Bool.and(Rx.all(y, m, D.Fd(2n, m, c), X), Rx.all(z, m, D.Fd(3n, m, c), X)), hx),
            CF.two.of(a => d => Bk.Term.Tup{T.tm.quan(D.Qn(m, c)), a, d}, S.Tm(g, m, ks, img, im, fi, X, nx, D.Fd(2n, m, c)), S.Tm(g, m, ks, img, im, fi, X, nx, D.Fd(3n, m, c)), y, z, Bk.Term.Tup{q, y, z},
            tm.is.at(g, dk, ds, m, im, fi, nx, ks, img, X, D.Fd(2n, m, c), y, CF.le.l(Pg.Term.size(y), Pg.Term.size(z), g, le), hy,
              CK.Bo.and_l(Rx.all(y, m, D.Fd(2n, m, c), X), Rx.all(z, m, D.Fd(3n, m, c), X), hp)),
            tm.is.at(g, dk, ds, m, im, fi, nx, ks, img, X, D.Fd(3n, m, c), z, CF.le.r(Pg.Term.size(y), Pg.Term.size(z), g, le), hz,
              CK.Bo.and_r(Rx.all(y, m, D.Fd(2n, m, c), X), Rx.all(z, m, D.Fd(3n, m, c), X), hp)),
            Equal.cong(Bk.Quan, Bk.Term, p => Bk.Term.Tup{p, y, z}, T.tm.quan(D.Qn(m, c)), q, CF.quan.of(Cr.Cir.Cells.get(m, c), q, hq))),
            nk.ok(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Tup{q, y, z}, 10, nd))
        case Bk.Term.Prj{+y}:
          (+nd, r) = h
          (sy, hy) = r
          tm.node(g, dk, ds, m, im, fi, nx, ks, img, X, c, 11, Bk.Term.Prj{y}, nd, CK.Bo.and_l(Rx(X, c), Rx.all(y, m, D.Fd(2n, m, c), X), hx),
            CF.one.of(a => Bk.Term.Prj{a}, S.Tm(g, m, ks, img, im, fi, X, nx, D.Fd(2n, m, c)), y, Bk.Term.Prj{y},
            tm.is.at(g, dk, ds, m, im, fi, nx, ks, img, X, D.Fd(2n, m, c), y, le, hy,
              CK.Bo.and_r(Rx(X, c), Rx.all(y, m, D.Fd(2n, m, c), X), hx)), {==}),
            nk.ok(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Prj{y}, 11, nd))
        case Bk.Term.Enu{+e}:
          (+nd, r) = h
          (ei, ez) = r
          tm.node(g, dk, ds, m, im, fi, nx, ks, img, X, c, 12, Bk.Term.Enu{e}, nd, hx,
            ei,
            zero.ok(D.FvW(Cr.Cir.Cell.get(0n, Cr.Cir.Cells.get(m, c))), ez))
        case Bk.Term.Lab{+k}:
          (+nd, nm) = h
          (en, ej) = nm
          tm.node(g, dk, ds, m, im, fi, nx, ks, img, X, c, 13, Bk.Term.Lab{k}, nd, hx,
            CF.named.of(T.tm.name(ks, D.Fd(2n, m, c)), k, en),
            nk.ok(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Lab{k}, 13, nd))
        case Bk.Term.Mat{+k, +y, +z}:
          (+nd, r) = h
          (nm, r2) = r
          (en, ej) = nm
          (py, pz) = r2
          (sy, hy) = py
          (sz, hz) = pz
          +hp = CK.Bo.and_r(Rx(X, c), Bool.and(Rx.all(y, m, D.Fd(3n, m, c), X), Rx.all(z, m, D.Fd(4n, m, c), X)), hx)
          tm.node(g, dk, ds, m, im, fi, nx, ks, img, X, c, 14, Bk.Term.Mat{k, y, z}, nd, CK.Bo.and_l(Rx(X, c), Bool.and(Rx.all(y, m, D.Fd(3n, m, c), X), Rx.all(z, m, D.Fd(4n, m, c), X)), hx),
            CF.mat.of(T.tm.name(ks, D.Fd(2n, m, c)), S.Tm(g, m, ks, img, im, fi, X, nx, D.Fd(3n, m, c)), S.Tm(g, m, ks, img, im, fi, X, nx, D.Fd(4n, m, c)), k, y, z, en,
            tm.is.at(g, dk, ds, m, im, fi, nx, ks, img, X, D.Fd(3n, m, c), y, CF.le.l(Pg.Term.size(y), Pg.Term.size(z), g, le), hy,
              CK.Bo.and_l(Rx.all(y, m, D.Fd(3n, m, c), X), Rx.all(z, m, D.Fd(4n, m, c), X), hp)),
            tm.is.at(g, dk, ds, m, im, fi, nx, ks, img, X, D.Fd(4n, m, c), z, CF.le.r(Pg.Term.size(y), Pg.Term.size(z), g, le), hz,
              CK.Bo.and_r(Rx.all(y, m, D.Fd(3n, m, c), X), Rx.all(z, m, D.Fd(4n, m, c), X), hp))),
            nk.ok(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Mat{k, y, z}, 14, nd))
        case Bk.Term.Efq{}:
          tm.node(g, dk, ds, m, im, fi, nx, ks, img, X, c, 15, Bk.Term.Efq{}, h, hx,
            {==},
            nk.ok(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Efq{}, 15, h))
        case Bk.Term.Eql{+y, +z, +w}:
          (+nd, r) = h
          (py, r2) = r
          (sy, hy) = py
          (pz, pw) = r2
          (sz, hz) = pz
          (sw, hw) = pw
          +hp = CK.Bo.and_r(Rx(X, c), Bool.and(Rx.all(y, m, D.Fd(2n, m, c), X), Bool.and(Rx.all(z, m, D.Fd(3n, m, c), X), Rx.all(w, m, D.Fd(4n, m, c), X))), hx)
          +hp2 = CK.Bo.and_r(Rx.all(y, m, D.Fd(2n, m, c), X), Bool.and(Rx.all(z, m, D.Fd(3n, m, c), X), Rx.all(w, m, D.Fd(4n, m, c), X)), hp)
          tm.node(g, dk, ds, m, im, fi, nx, ks, img, X, c, 16, Bk.Term.Eql{y, z, w}, nd, CK.Bo.and_l(Rx(X, c), Bool.and(Rx.all(y, m, D.Fd(2n, m, c), X), Bool.and(Rx.all(z, m, D.Fd(3n, m, c), X), Rx.all(w, m, D.Fd(4n, m, c), X))), hx),
            CF.three.of(a => b => d => Bk.Term.Eql{a, b, d}, S.Tm(g, m, ks, img, im, fi, X, nx, D.Fd(2n, m, c)), S.Tm(g, m, ks, img, im, fi, X, nx, D.Fd(3n, m, c)), S.Tm(g, m, ks, img, im, fi, X, nx, D.Fd(4n, m, c)), y, z, w,
            tm.is.at(g, dk, ds, m, im, fi, nx, ks, img, X, D.Fd(2n, m, c), y, CF.le.l(Pg.Term.size(y), Nat.add(Pg.Term.size(z), Pg.Term.size(w)), g, le), hy,
              CK.Bo.and_l(Rx.all(y, m, D.Fd(2n, m, c), X), Bool.and(Rx.all(z, m, D.Fd(3n, m, c), X), Rx.all(w, m, D.Fd(4n, m, c), X)), hp)),
            tm.is.at(g, dk, ds, m, im, fi, nx, ks, img, X, D.Fd(3n, m, c), z, CF.le.m(Pg.Term.size(y), Pg.Term.size(z), Pg.Term.size(w), g, le), hz,
              CK.Bo.and_l(Rx.all(z, m, D.Fd(3n, m, c), X), Rx.all(w, m, D.Fd(4n, m, c), X), hp2)),
            tm.is.at(g, dk, ds, m, im, fi, nx, ks, img, X, D.Fd(4n, m, c), w, CF.le.e(Pg.Term.size(y), Pg.Term.size(z), Pg.Term.size(w), g, le), hw,
              CK.Bo.and_r(Rx.all(z, m, D.Fd(3n, m, c), X), Rx.all(w, m, D.Fd(4n, m, c), X), hp2))),
            nk.ok(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Eql{y, z, w}, 16, nd))
        case Bk.Term.Rfl{}:
          tm.node(g, dk, ds, m, im, fi, nx, ks, img, X, c, 17, Bk.Term.Rfl{}, h, hx,
            {==},
            nk.ok(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Rfl{}, 17, h))
        case Bk.Term.Rwt{+y, +z, +w}:
          (+nd, r) = h
          (py, r2) = r
          (sy, hy) = py
          (pz, pw) = r2
          (sz, hz) = pz
          (sw, hw) = pw
          +hp = CK.Bo.and_r(Rx(X, c), Bool.and(Rx.all(y, m, D.Fd(2n, m, c), X), Bool.and(Rx.all(z, m, D.Fd(3n, m, c), X), Rx.all(w, m, D.Fd(4n, m, c), X))), hx)
          +hp2 = CK.Bo.and_r(Rx.all(y, m, D.Fd(2n, m, c), X), Bool.and(Rx.all(z, m, D.Fd(3n, m, c), X), Rx.all(w, m, D.Fd(4n, m, c), X)), hp)
          tm.node(g, dk, ds, m, im, fi, nx, ks, img, X, c, 18, Bk.Term.Rwt{y, z, w}, nd, CK.Bo.and_l(Rx(X, c), Bool.and(Rx.all(y, m, D.Fd(2n, m, c), X), Bool.and(Rx.all(z, m, D.Fd(3n, m, c), X), Rx.all(w, m, D.Fd(4n, m, c), X))), hx),
            CF.three.of(a => b => d => Bk.Term.Rwt{a, b, d}, S.Tm(g, m, ks, img, im, fi, X, nx, D.Fd(2n, m, c)), S.Tm(g, m, ks, img, im, fi, X, nx, D.Fd(3n, m, c)), S.Tm(g, m, ks, img, im, fi, X, nx, D.Fd(4n, m, c)), y, z, w,
            tm.is.at(g, dk, ds, m, im, fi, nx, ks, img, X, D.Fd(2n, m, c), y, CF.le.l(Pg.Term.size(y), Nat.add(Pg.Term.size(z), Pg.Term.size(w)), g, le), hy,
              CK.Bo.and_l(Rx.all(y, m, D.Fd(2n, m, c), X), Bool.and(Rx.all(z, m, D.Fd(3n, m, c), X), Rx.all(w, m, D.Fd(4n, m, c), X)), hp)),
            tm.is.at(g, dk, ds, m, im, fi, nx, ks, img, X, D.Fd(3n, m, c), z, CF.le.m(Pg.Term.size(y), Pg.Term.size(z), Pg.Term.size(w), g, le), hz,
              CK.Bo.and_l(Rx.all(z, m, D.Fd(3n, m, c), X), Rx.all(w, m, D.Fd(4n, m, c), X), hp2)),
            tm.is.at(g, dk, ds, m, im, fi, nx, ks, img, X, D.Fd(4n, m, c), w, CF.le.e(Pg.Term.size(y), Pg.Term.size(z), Pg.Term.size(w), g, le), hw,
              CK.Bo.and_r(Rx.all(z, m, D.Fd(3n, m, c), X), Rx.all(w, m, D.Fd(4n, m, c), X), hp2))),
            nk.ok(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Rwt{y, z, w}, 18, nd))

# The two kits
# ------------
#
# definitions.bend (D, the machine's side) and copy_substitution.bend (S, the
# copy's) each define the cells' kit for their own side: they agree.

def nat.of.eq(b: Bool) -> {D.Nat.of(b) == S.Nat.of(b) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def mem.has(xs: List<&2, U32>, +c: U32) -> {D.Mem(xs, c) == S.Has(xs, c) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      %mem.has(rest, c) : {Bool.or(U32.is_eq(x, c), D.Mem(rest, c)) == Bool.or(U32.is_eq(x, c), _) : Bool}
      {==}

def rcl.occ(xs: List<&2, U32>, +c: U32) -> {D.RcL(xs, c) == S.Occ(xs, c) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      %nat.of.eq(U32.is_eq(x, c)) : {Nat.add(D.Nat.of(U32.is_eq(x, c)), D.RcL(rest, c)) == Nat.add(_, S.Occ(rest, c)) : Nat}
      %rcl.occ(rest, c) : {Nat.add(D.Nat.of(U32.is_eq(x, c)), D.RcL(rest, c)) == Nat.add(D.Nat.of(U32.is_eq(x, c)), _) : Nat}
      {==}

# the pointers of a cell, as the heap counts them (Fs) and as the copy does (Ps)
def fs.ps(+m: Cr.Cir.Cells, +ps: List<&2, U32>, +o: U32) -> {D.Fs(m, ps, o) == S.Ps(m, ps, o) : List<&2, U32>}:
  %Equal.sym(Bool, D.Mem(ps, o), S.Has(ps, o), mem.has(ps, o)) :
    {Bool.pick(List<&2, U32>, U32.is_lt(D.TgW(D.Fd(0n, m, o)), 19),
      D.Fs.term(D.Fd(2n, m, U32.add(272, D.TgW(D.Fd(0n, m, o)))), D.Fd(2n, m, o), D.Fd(3n, m, o), D.Fd(4n, m, o)),
      Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_le(32, D.TgW(D.Fd(0n, m, o))), U32.is_le(D.TgW(D.Fd(0n, m, o)), 40)), Bool.not(_)),
        Con{D.Fd(2n, m, o), D.Fs.opt(U32.is_eq(D.TgW(D.Fd(0n, m, o)), 38), D.Fd(3n, m, o), Nil{})},
        Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_eq(D.TgW(D.Fd(0n, m, o)), 41), D.FlW(D.Fd(0n, m, o), 4096)), Bool.not(_)),
          [D.Fd(2n, m, o)], Nil{}))) == S.Ps(m, ps, o) : List<&2, U32>}
  {==}

# a sum, part by part
def add.cong(-a1: Nat, -a2: Nat, -b1: Nat, -b2: Nat, ea: {a1 == a2 : Nat}, eb: {b1 == b2 : Nat}) ->
  {Nat.add(a1, b1) == Nat.add(a2, b2) : Nat}:
  %ea : {Nat.add(a1, b1) == Nat.add(_, b2) : Nat}
  %eb : {Nat.add(a1, b1) == Nat.add(a1, _) : Nat}
  {==}

# a disjunction, part by part
def or.cong(-a1: Bool, -a2: Bool, -b1: Bool, -b2: Bool, ea: {a1 == a2 : Bool}, eb: {b1 == b2 : Bool}) ->
  {Bool.or(a1, b1) == Bool.or(a2, b2) : Bool}:
  %ea : {Bool.or(a1, b1) == Bool.or(_, b2) : Bool}
  %eb : {Bool.or(a1, b1) == Bool.or(a1, _) : Bool}
  {==}

# the pointers to c of the n cells from o: the heap's count (Pc over Fs) is the copy's (Pc over Ps)
def pc.eq(n: Nat, +m: Cr.Cir.Cells, +ps: List<&2, U32>, +o: U32, +c: U32) -> {D.Pc(n, m, ps, o, c) == S.Pc(n, m, ps, o, c) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      add.cong(D.RcL(D.Fs(m, ps, o), c), S.Occ(S.Ps(m, ps, o), c), D.Pc(p, m, ps, U32.inc(o), c), S.Pc(p, m, ps, U32.inc(o), c),
        Equal.trans(Nat, D.RcL(D.Fs(m, ps, o), c), S.Occ(D.Fs(m, ps, o), c), S.Occ(S.Ps(m, ps, o), c), rcl.occ(D.Fs(m, ps, o), c),
          Equal.cong(List<&2, U32>, Nat, xs => S.Occ(xs, c), D.Fs(m, ps, o), S.Ps(m, ps, o), fs.ps(m, ps, o))),
        pc.eq(p, m, ps, U32.inc(o), c))

# definitions.bend's Node is copy_substitution.bend's
def node.eq(t: Bk.Term, +m: Cr.Cir.Cells, +r: U32, +c: U32) -> {D.Node(t, m, r, c) == S.Node(t, m, r, c) : Bool}:
  match t:
    case Bk.Term.Var{_}:
      {==}
    case Bk.Term.Ref{_}:
      {==}
    case Bk.Term.Ann{+y, +z}:
      or.cong(U32.is_eq(r, c), U32.is_eq(r, c), Bool.or(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c)), Bool.or(S.Node(y, m, S.Fd(2n, m, r), c), S.Node(z, m, S.Fd(3n, m, r), c)), {==},
        or.cong(D.Node(y, m, D.Fd(2n, m, r), c), S.Node(y, m, S.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c), S.Node(z, m, S.Fd(3n, m, r), c), node.eq(y, m, D.Fd(2n, m, r), c), node.eq(z, m, D.Fd(3n, m, r), c)))
    case Bk.Term.Let{_, +y, +z}:
      or.cong(U32.is_eq(r, c), U32.is_eq(r, c), Bool.or(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c)), Bool.or(S.Node(y, m, S.Fd(2n, m, r), c), S.Node(z, m, S.Fd(3n, m, r), c)), {==},
        or.cong(D.Node(y, m, D.Fd(2n, m, r), c), S.Node(y, m, S.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c), S.Node(z, m, S.Fd(3n, m, r), c), node.eq(y, m, D.Fd(2n, m, r), c), node.eq(z, m, D.Fd(3n, m, r), c)))
    case Bk.Term.Typ{+y}:
      or.cong(U32.is_eq(r, c), U32.is_eq(r, c), D.Node(y, m, D.Fd(2n, m, r), c), S.Node(y, m, S.Fd(2n, m, r), c), {==},
        node.eq(y, m, D.Fd(2n, m, r), c))
    case Bk.Term.Min{+y, +z}:
      or.cong(U32.is_eq(r, c), U32.is_eq(r, c), Bool.or(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c)), Bool.or(S.Node(y, m, S.Fd(2n, m, r), c), S.Node(z, m, S.Fd(3n, m, r), c)), {==},
        or.cong(D.Node(y, m, D.Fd(2n, m, r), c), S.Node(y, m, S.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c), S.Node(z, m, S.Fd(3n, m, r), c), node.eq(y, m, D.Fd(2n, m, r), c), node.eq(z, m, D.Fd(3n, m, r), c)))
    case Bk.Term.All{_, +y, +z}:
      or.cong(U32.is_eq(r, c), U32.is_eq(r, c), Bool.or(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c)), Bool.or(S.Node(y, m, S.Fd(2n, m, r), c), S.Node(z, m, S.Fd(3n, m, r), c)), {==},
        or.cong(D.Node(y, m, D.Fd(2n, m, r), c), S.Node(y, m, S.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c), S.Node(z, m, S.Fd(3n, m, r), c), node.eq(y, m, D.Fd(2n, m, r), c), node.eq(z, m, D.Fd(3n, m, r), c)))
    case Bk.Term.Lam{_, +y}:
      or.cong(U32.is_eq(r, c), U32.is_eq(r, c), D.Node(y, m, D.Fd(2n, m, r), c), S.Node(y, m, S.Fd(2n, m, r), c), {==},
        node.eq(y, m, D.Fd(2n, m, r), c))
    case Bk.Term.App{_, +y, +z}:
      or.cong(U32.is_eq(r, c), U32.is_eq(r, c), Bool.or(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c)), Bool.or(S.Node(y, m, S.Fd(2n, m, r), c), S.Node(z, m, S.Fd(3n, m, r), c)), {==},
        or.cong(D.Node(y, m, D.Fd(2n, m, r), c), S.Node(y, m, S.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c), S.Node(z, m, S.Fd(3n, m, r), c), node.eq(y, m, D.Fd(2n, m, r), c), node.eq(z, m, D.Fd(3n, m, r), c)))
    case Bk.Term.Sig{_, +y, +z}:
      or.cong(U32.is_eq(r, c), U32.is_eq(r, c), Bool.or(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c)), Bool.or(S.Node(y, m, S.Fd(2n, m, r), c), S.Node(z, m, S.Fd(3n, m, r), c)), {==},
        or.cong(D.Node(y, m, D.Fd(2n, m, r), c), S.Node(y, m, S.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c), S.Node(z, m, S.Fd(3n, m, r), c), node.eq(y, m, D.Fd(2n, m, r), c), node.eq(z, m, D.Fd(3n, m, r), c)))
    case Bk.Term.Tup{_, +y, +z}:
      or.cong(U32.is_eq(r, c), U32.is_eq(r, c), Bool.or(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c)), Bool.or(S.Node(y, m, S.Fd(2n, m, r), c), S.Node(z, m, S.Fd(3n, m, r), c)), {==},
        or.cong(D.Node(y, m, D.Fd(2n, m, r), c), S.Node(y, m, S.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c), S.Node(z, m, S.Fd(3n, m, r), c), node.eq(y, m, D.Fd(2n, m, r), c), node.eq(z, m, D.Fd(3n, m, r), c)))
    case Bk.Term.Prj{+y}:
      or.cong(U32.is_eq(r, c), U32.is_eq(r, c), D.Node(y, m, D.Fd(2n, m, r), c), S.Node(y, m, S.Fd(2n, m, r), c), {==},
        node.eq(y, m, D.Fd(2n, m, r), c))
    case Bk.Term.Enu{_}:
      {==}
    case Bk.Term.Lab{_}:
      {==}
    case Bk.Term.Mat{_, +y, +z}:
      or.cong(U32.is_eq(r, c), U32.is_eq(r, c), Bool.or(D.Node(y, m, D.Fd(3n, m, r), c), D.Node(z, m, D.Fd(4n, m, r), c)), Bool.or(S.Node(y, m, S.Fd(3n, m, r), c), S.Node(z, m, S.Fd(4n, m, r), c)), {==},
        or.cong(D.Node(y, m, D.Fd(3n, m, r), c), S.Node(y, m, S.Fd(3n, m, r), c), D.Node(z, m, D.Fd(4n, m, r), c), S.Node(z, m, S.Fd(4n, m, r), c), node.eq(y, m, D.Fd(3n, m, r), c), node.eq(z, m, D.Fd(4n, m, r), c)))
    case Bk.Term.Efq{}:
      {==}
    case Bk.Term.Eql{+y, +z, +w}:
      or.cong(U32.is_eq(r, c), U32.is_eq(r, c), Bool.or(D.Node(y, m, D.Fd(2n, m, r), c), Bool.or(D.Node(z, m, D.Fd(3n, m, r), c), D.Node(w, m, D.Fd(4n, m, r), c))), Bool.or(S.Node(y, m, S.Fd(2n, m, r), c), Bool.or(S.Node(z, m, S.Fd(3n, m, r), c), S.Node(w, m, S.Fd(4n, m, r), c))), {==},
        or.cong(D.Node(y, m, D.Fd(2n, m, r), c), S.Node(y, m, S.Fd(2n, m, r), c), Bool.or(D.Node(z, m, D.Fd(3n, m, r), c), D.Node(w, m, D.Fd(4n, m, r), c)), Bool.or(S.Node(z, m, S.Fd(3n, m, r), c), S.Node(w, m, S.Fd(4n, m, r), c)), node.eq(y, m, D.Fd(2n, m, r), c),
        or.cong(D.Node(z, m, D.Fd(3n, m, r), c), S.Node(z, m, S.Fd(3n, m, r), c), D.Node(w, m, D.Fd(4n, m, r), c), S.Node(w, m, S.Fd(4n, m, r), c), node.eq(z, m, D.Fd(3n, m, r), c), node.eq(w, m, D.Fd(4n, m, r), c))))
    case Bk.Term.Rfl{}:
      {==}
    case Bk.Term.Rwt{+y, +z, +w}:
      or.cong(U32.is_eq(r, c), U32.is_eq(r, c), Bool.or(D.Node(y, m, D.Fd(2n, m, r), c), Bool.or(D.Node(z, m, D.Fd(3n, m, r), c), D.Node(w, m, D.Fd(4n, m, r), c))), Bool.or(S.Node(y, m, S.Fd(2n, m, r), c), Bool.or(S.Node(z, m, S.Fd(3n, m, r), c), S.Node(w, m, S.Fd(4n, m, r), c))), {==},
        or.cong(D.Node(y, m, D.Fd(2n, m, r), c), S.Node(y, m, S.Fd(2n, m, r), c), Bool.or(D.Node(z, m, D.Fd(3n, m, r), c), D.Node(w, m, D.Fd(4n, m, r), c)), Bool.or(S.Node(z, m, S.Fd(3n, m, r), c), S.Node(w, m, S.Fd(4n, m, r), c)), node.eq(y, m, D.Fd(2n, m, r), c),
        or.cong(D.Node(z, m, D.Fd(3n, m, r), c), S.Node(z, m, S.Fd(3n, m, r), c), D.Node(w, m, D.Fd(4n, m, r), c), S.Node(w, m, S.Fd(4n, m, r), c), node.eq(z, m, D.Fd(3n, m, r), c), node.eq(w, m, D.Fd(4n, m, r), c))))

# the machine's roots as the copy's, each with its term's size as its fuel
def Rs.of(rs: List<&2, D.Rt>) -> List<&2, S.Rt>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{D.Rt{c, +t}, +rest}:
      Con{S.Rt{Pg.Term.size(t), c, t}, Rs.of(rest)}

# a node of the machine's roots is a node of the copy's
def nodes.eq(rs: List<&2, D.Rt>, +m: Cr.Cir.Cells, +c: U32) -> {D.Nodes(rs, m, c) == S.Nodes(Rs.of(rs), m, c) : Bool}:
  match rs:
    case Nil{}:
      {==}
    case Con{D.Rt{+r, +u}, +rest}:
      or.cong(D.Node(u, m, r, c), S.Node(u, m, r, c), D.Nodes(rest, m, c), S.Nodes(Rs.of(rest), m, c), node.eq(u, m, r, c),
        nodes.eq(rest, m, c))

# The registers
# -------------

# a Nat that is_eq says is j is j
def nat.eq(i: Nat, j: Nat, h: {Nat.is_eq(i, j) == True{} : Bool}) -> {i == j : Nat}:
  match i j:
    case 0n 0n:
      {==}
    case 0n 1n+jp:
      CK.Bo.tf({0n == 1n+jp : Nat}, h)
    case 1n+ip 0n:
      CK.Bo.tf({1n+ip == 0n : Nat}, h)
    case 1n+ip 1n+jp:
      Equal.cong(Nat, Nat, k => 1n+k, ip, jp, nat.eq(ip, jp, h))

# a write to the register i leaves the register j, another
def set.get(xs: List<&2, U32>, i: Nat, j: Nat, +v: U32, h: {Nat.is_eq(i, j) == False{} : Bool}) ->
  {List.get(&2, U32, List.set(&2, U32, xs, i, v), j) == List.get(&2, U32, xs, j) : Maybe<&2, U32>}:
  match xs i j:
    case Nil{} _ _:
      {==}
    case Con{x, rest} 0n 0n:
      CK.Bo.ft({List.get(&2, U32, List.set(&2, U32, Con{x, rest}, 0n, v), 0n) == List.get(&2, U32, Con{x, rest}, 0n) : Maybe<&2, U32>}, h)
    case Con{x, rest} 0n 1n+jp:
      {==}
    case Con{x, rest} 1n+ip 0n:
      {==}
    case Con{x, +rest} 1n+ip 1n+jp:
      set.get(rest, ip, jp, v, h)

# a write keeps the number of registers
def set.len(xs: List<&2, U32>, i: Nat, +v: U32) -> {List.length(&2, U32, List.set(&2, U32, xs, i, v)) == List.length(&2, U32, xs) : Nat}:
  match xs i:
    case Nil{} _:
      {==}
    case Con{x, +rest} 0n:
      {==}
    case Con{x, +rest} 1n+ip:
      Equal.cong(Nat, Nat, k => 1n+k, List.length(&2, U32, List.set(&2, U32, rest, ip, v)), List.length(&2, U32, rest), set.len(rest, ip, v))

def has.ne.b(b: Bool, rs: List<&2, Nat>, +i: Nat, +j: Nat, eb: {Nat.is_eq(i, j) == b : Bool}, hi: {S.Has.nat(rs, i) == True{} : Bool},
  hj: {S.Has.nat(rs, j) == False{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      +e = nat.eq(i, j, eb)
      CK.Bo.tf({True{} == False{} : Bool}, Equal.trans(Bool, False{}, S.Has.nat(rs, i), True{},
        (%Equal.sym(Nat, i, j, e) : {False{} == S.Has.nat(rs, _) : Bool}; Equal.sym(Bool, S.Has.nat(rs, j), False{}, hj)), hi))

# i is one of rs and j is not: i is not j
def has.ne(rs: List<&2, Nat>, +i: Nat, +j: Nat, hi: {S.Has.nat(rs, i) == True{} : Bool}, hj: {S.Has.nat(rs, j) == False{} : Bool}) ->
  {Nat.is_eq(i, j) == False{} : Bool}:
  has.ne.b(Nat.is_eq(i, j), rs, i, j, {==}, hi, hj)

# writes to the registers of scr leave a register out of scr
def ups.get(ups: List<&2, S.Up>, +xs: List<&2, U32>, +scr: List<&2, Nat>, +j: Nat, +hu: {S.Ups.in(ups, scr) == True{} : Bool},
  +hj: {S.Has.nat(scr, j) == False{} : Bool}) -> {List.get(&2, U32, S.Ups(ups, xs), j) == List.get(&2, U32, xs, j) : Maybe<&2, U32>}:
  match ups:
    case Nil{}:
      {==}
    case Con{S.Up{+i, +v}, +rest}:
      +hi = CK.Bo.and_l(S.Has.nat(scr, i), S.Ups.in(rest, scr), hu)
      Equal.trans(Maybe<&2, U32>, List.get(&2, U32, S.Ups(rest, List.set(&2, U32, xs, i, v)), j),
        List.get(&2, U32, List.set(&2, U32, xs, i, v), j), List.get(&2, U32, xs, j),
        ups.get(rest, List.set(&2, U32, xs, i, v), scr, j, CK.Bo.and_r(S.Has.nat(scr, i), S.Ups.in(rest, scr), hu), hj),
        set.get(xs, i, j, v, has.ne(scr, i, j, hi, hj)))

# writes keep the number of registers
def ups.len(ups: List<&2, S.Up>, +xs: List<&2, U32>) -> {List.length(&2, U32, S.Ups(ups, xs)) == List.length(&2, U32, xs) : Nat}:
  match ups:
    case Nil{}:
      {==}
    case Con{S.Up{+i, +v}, +rest}:
      Equal.trans(Nat, List.length(&2, U32, S.Ups(rest, List.set(&2, U32, xs, i, v))), List.length(&2, U32, List.set(&2, U32, xs, i, v)),
        List.length(&2, U32, xs), ups.len(rest, List.set(&2, U32, xs, i, v)), set.len(xs, i, v))

# the registers made explicit from the (1 + i)-th of x then rest are rest's from the i-th
def rg.ex.cons(n: Nat, +x: U32, +rest: List<&2, U32>, +i: Nat) -> {S.Rg.ex(n, Con{x, rest}, 1n+i) == S.Rg.ex(n, rest, i) : List<&2, U32>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %rg.ex.cons(p, x, rest, 1n+i) : {Con{T.tm.reg(Con{x, rest}, 1n+i), S.Rg.ex(p, Con{x, rest}, 2n+i)} == Con{T.tm.reg(rest, i), _} : List<&2, U32>}
      {==}

# the registers made explicit are the registers
def rg.ex.self(xs: List<&2, U32>) -> {S.Rg.ex(List.length(&2, U32, xs), xs, 0n) == xs : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      %Equal.sym(List<&2, U32>, S.Rg.ex(List.length(&2, U32, rest), Con{x, rest}, 1n), S.Rg.ex(List.length(&2, U32, rest), rest, 0n),
        rg.ex.cons(List.length(&2, U32, rest), x, rest, 0n)) : {Con{x, _} == Con{x, rest} : List<&2, U32>}
      %Equal.sym(List<&2, U32>, S.Rg.ex(List.length(&2, U32, rest), rest, 0n), rest, rg.ex.self(rest)) : {Con{x, _} == Con{x, rest} : List<&2, U32>}
      {==}

# 63 registers made explicit are the registers
def rg.ex.all(+regs: List<&2, U32>, hl: {List.length(&2, U32, regs) == 63n : Nat}) -> {S.Rg.ex(63n, regs, 0n) == regs : List<&2, U32>}:
  %hl : {S.Rg.ex(_, regs, 0n) == regs : List<&2, U32>}
  rg.ex.self(regs)

# every one of xs is one of ys
def Sub.nat(xs: List<&2, Nat>, +ys: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, +rest}:
      Bool.and(D.Nat.mem(ys, x), Sub.nat(rest, ys))

def sub.nat.or(b: Bool, +x: Nat, +j: Nat, +ys: List<&2, Nat>, r: Bool, eb: {Nat.is_eq(x, j) == b : Bool},
  hx: {D.Nat.mem(ys, x) == True{} : Bool}, hj: {D.Nat.mem(ys, j) == False{} : Bool}, hr: {r == False{} : Bool}) ->
  {Bool.or(b, r) == False{} : Bool}:
  match b:
    case False{}:
      hr
    case True{}:
      +e = nat.eq(x, j, eb)
      CK.Bo.tf({Bool.or(True{}, r) == False{} : Bool}, Equal.trans(Bool, False{}, D.Nat.mem(ys, x), True{},
        (%Equal.sym(Nat, x, j, e) : {False{} == D.Nat.mem(ys, _) : Bool}; Equal.sym(Bool, D.Nat.mem(ys, j), False{}, hj)), hx))

# j is not one of ys, nor of xs, which ys holds
def sub.nat.out(xs: List<&2, Nat>, +ys: List<&2, Nat>, +j: Nat, +hs: {Sub.nat(xs, ys) == True{} : Bool},
  +hj: {D.Nat.mem(ys, j) == False{} : Bool}) -> {S.Has.nat(xs, j) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      +hx = CK.Bo.and_l(D.Nat.mem(ys, x), Sub.nat(rest, ys), hs)
      +hr = sub.nat.out(rest, ys, j, CK.Bo.and_r(D.Nat.mem(ys, x), Sub.nat(rest, ys), hs), hj)
      sub.nat.or(Nat.is_eq(x, j), x, j, ys, S.Has.nat(rest, j), {==}, hx, hj, hr)

# the registers that M.copy(n, _) may write are among those that the move gives it
def scr.sub() -> {Sub.nat(S.Cp.scratch(Mc.R.n()), D.Copy.scr(Mc.R.n())) == True{} : Bool}:
  {==}

# the registers of keep are kept by writes to the registers of scr, which keep avoids
def kept.ups(keep: List<&2, Nat>, +regs: List<&2, U32>, +ups: List<&2, S.Up>, +scr: List<&2, Nat>, +ys: List<&2, Nat>,
  +hu: {S.Ups.in(ups, scr) == True{} : Bool}, +hs: {Sub.nat(scr, ys) == True{} : Bool}, +hk: {D.Disj(keep, ys) == True{} : Bool}) ->
  D.Kept(regs, S.Ups(ups, regs), keep):
  match keep:
    case Nil{}:
      Unit{}
    case Con{+j, +rest}:
      +hj = CK.Bo.not_t(D.Nat.mem(ys, j), CK.Bo.and_l(Bool.not(D.Nat.mem(ys, j)), D.Disj(rest, ys), hk))
      (ups.get(ups, regs, scr, j, hu, sub.nat.out(scr, ys, j, hs, hj)),
       kept.ups(rest, regs, ups, scr, ys, hu, hs, CK.Bo.and_r(Bool.not(D.Nat.mem(ys, j)), D.Disj(rest, ys), hk)))

# The fuel
# --------
#
# Cp.ok gives one fuel that ends the run; CopyPost asks for any fuel: more
# keeps an outcome that ended (D.mono), less either does not end or ends the
# same way.

# what Ok allows, PostB allows (no halt; out of memory within the same budget)
def ok.postb(o: Cr.Cir.Out, +F: U32, +K: U32, +L: U32, +I: List<&2, Word(8n)>, -B: Nat,
  -Q: List<&2, U32> -> Cr.Cir.Cells -> U32 -> U32 -> Type, -R: Cr.Cir.State -> Type, -H: U32 -> Cr.Cir.State -> Type,
  h: S.Ok(o, F, K, L, I, B, Q), g: @st: Cr.Cir.State -> S.At(st, F, K, L, I, Q) -> R(st)) -> D.PostB(False{}, o, R, H, B, L):
  match o:
    case Cr.Cir.Out.next{st}:
      g(st, h)
    case Cr.Cir.Out.halt{s, st}:
      Empty.absurd(H(s, st), h)
    case Cr.Cir.Out.out_of_memory{}:
      h
    case Cr.Cir.Out.trap{}:
      h
    case Cr.Cir.Out.not_done{}:
      Unit{}

# Ends of y gives Ends of x, for x == y
def ends.rw(-x: Cr.Cir.Out, -y: Cr.Cir.Out, e: {x == y : Cr.Cir.Out}, d: D.Ends(y)) -> D.Ends(x):
  %Equal.sym(Cr.Cir.Out, x, y, e) : D.Ends(_)
  d

# an outcome o of the fuel f <= n that ends is the one of n
def fuel.at(-o: Cr.Cir.Out, +f: Nat, +n: Nat, +s: Cr.Cir.Stmt, +st: Cr.Cir.State, +F: U32, +K: U32, +L: U32,
  +I: List<&2, Word(8n)>, -B: Nat, -Q: List<&2, U32> -> Cr.Cir.Cells -> U32 -> U32 -> Type, -R: Cr.Cir.State -> Type,
  -H: U32 -> Cr.Cir.State -> Type, +le: N.Le(f, n), +eo: {Cr.Cir.exec(f, s, st) == o : Cr.Cir.Out}, d: D.Ends(o),
  h: S.Ok(Cr.Cir.exec(n, s, st), F, K, L, I, B, Q), g: @st2: Cr.Cir.State -> S.At(st2, F, K, L, I, Q) -> R(st2)) ->
  D.PostB(False{}, o, R, H, B, L):
  +e = D.mono(f, n, s, st, le, ends.rw(Cr.Cir.exec(f, s, st), o, eo, d))
  %Equal.trans(Cr.Cir.Out, Cr.Cir.exec(n, s, st), Cr.Cir.exec(f, s, st), o, Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, s, st), Cr.Cir.exec(n, s, st), e), eo) :
    D.PostB(False{}, _, R, H, B, L)
  ok.postb(Cr.Cir.exec(n, s, st), F, K, L, I, B, Q, R, H, h, g)

# not n <= f gives f <= n
def le.not(n: Nat, f: Nat, h: {Nat.is_le(n, f) == False{} : Bool}) -> N.Le(f, n):
  match n f:
    case 0n _:
      CK.Bo.tf(N.Le(f, 0n), Equal.trans(Bool, False{}, Nat.is_le(0n, f), True{}, Equal.sym(Bool, Nat.is_le(0n, f), False{}, h),
        CK.Na.le0(f)))
    case 1n+np 0n:
      N.le_zero(1n+np)
    case 1n+np 1n+fp:
      le.not(np, fp, h)

# with the fuel f <= n, an outcome o of the run that ends is the one of n
def fuel.low(o: Cr.Cir.Out, +f: Nat, +n: Nat, +s: Cr.Cir.Stmt, +st: Cr.Cir.State, +F: U32, +K: U32, +L: U32,
  +I: List<&2, Word(8n)>, -B: Nat, -Q: List<&2, U32> -> Cr.Cir.Cells -> U32 -> U32 -> Type, -R: Cr.Cir.State -> Type,
  -H: U32 -> Cr.Cir.State -> Type, +le: N.Le(f, n), eo: {Cr.Cir.exec(f, s, st) == o : Cr.Cir.Out},
  h: S.Ok(Cr.Cir.exec(n, s, st), F, K, L, I, B, Q), g: @st2: Cr.Cir.State -> S.At(st2, F, K, L, I, Q) -> R(st2)) ->
  D.PostB(False{}, o, R, H, B, L):
  match o:
    case Cr.Cir.Out.not_done{}:
      Unit{}
    case Cr.Cir.Out.next{st2}:
      fuel.at(Cr.Cir.Out.next{st2}, f, n, s, st, F, K, L, I, B, Q, R, H, le, eo, Unit{}, h, g)
    case Cr.Cir.Out.halt{c, st2}:
      fuel.at(Cr.Cir.Out.halt{c, st2}, f, n, s, st, F, K, L, I, B, Q, R, H, le, eo, Unit{}, h, g)
    case Cr.Cir.Out.out_of_memory{}:
      fuel.at(Cr.Cir.Out.out_of_memory{}, f, n, s, st, F, K, L, I, B, Q, R, H, le, eo, Unit{}, h, g)
    case Cr.Cir.Out.trap{}:
      fuel.at(Cr.Cir.Out.trap{}, f, n, s, st, F, K, L, I, B, Q, R, H, le, eo, Unit{}, h, g)

# with the fuel f >= n, the outcome o of n, which ended, is the one of f
def fuel.end(o: Cr.Cir.Out, +f: Nat, +n: Nat, +s: Cr.Cir.Stmt, +st: Cr.Cir.State, +F: U32, +K: U32, +L: U32,
  +I: List<&2, Word(8n)>, -B: Nat, -Q: List<&2, U32> -> Cr.Cir.Cells -> U32 -> U32 -> Type, -R: Cr.Cir.State -> Type,
  -H: U32 -> Cr.Cir.State -> Type, +le: N.Le(n, f), +eo: {Cr.Cir.exec(n, s, st) == o : Cr.Cir.Out}, d: D.Ends(o),
  h: S.Ok(o, F, K, L, I, B, Q), g: @st2: Cr.Cir.State -> S.At(st2, F, K, L, I, Q) -> R(st2)) ->
  D.PostB(False{}, Cr.Cir.exec(f, s, st), R, H, B, L):
  +e = D.mono(n, f, s, st, le, ends.rw(Cr.Cir.exec(n, s, st), o, eo, d))
  %Equal.trans(Cr.Cir.Out, o, Cr.Cir.exec(n, s, st), Cr.Cir.exec(f, s, st), Equal.sym(Cr.Cir.Out, Cr.Cir.exec(n, s, st), o, eo), e) :
    D.PostB(False{}, _, R, H, B, L)
  ok.postb(o, F, K, L, I, B, Q, R, H, h, g)

# with the fuel f >= n, the outcome o of n (which Ok says ends) is the one of f
def fuel.high(o: Cr.Cir.Out, +f: Nat, +n: Nat, +s: Cr.Cir.Stmt, +st: Cr.Cir.State, +F: U32, +K: U32, +L: U32,
  +I: List<&2, Word(8n)>, -B: Nat, -Q: List<&2, U32> -> Cr.Cir.Cells -> U32 -> U32 -> Type, -R: Cr.Cir.State -> Type,
  -H: U32 -> Cr.Cir.State -> Type, +le: N.Le(n, f), eo: {Cr.Cir.exec(n, s, st) == o : Cr.Cir.Out},
  h: S.Ok(o, F, K, L, I, B, Q), g: @st2: Cr.Cir.State -> S.At(st2, F, K, L, I, Q) -> R(st2)) ->
  D.PostB(False{}, Cr.Cir.exec(f, s, st), R, H, B, L):
  match o:
    case Cr.Cir.Out.next{st2}:
      fuel.end(Cr.Cir.Out.next{st2}, f, n, s, st, F, K, L, I, B, Q, R, H, le, eo, Unit{}, h, g)
    case Cr.Cir.Out.halt{c, st2}:
      Empty.absurd(D.PostB(False{}, Cr.Cir.exec(f, s, st), R, H, B, L), h)
    case Cr.Cir.Out.out_of_memory{}:
      fuel.end(Cr.Cir.Out.out_of_memory{}, f, n, s, st, F, K, L, I, B, Q, R, H, le, eo, Unit{}, h, g)
    case Cr.Cir.Out.trap{}:
      Empty.absurd(D.PostB(False{}, Cr.Cir.exec(f, s, st), R, H, B, L), h)
    case Cr.Cir.Out.not_done{}:
      Empty.absurd(D.PostB(False{}, Cr.Cir.exec(f, s, st), R, H, B, L), h)

def fuel.cmp(b: Bool, +f: Nat, +n: Nat, +s: Cr.Cir.Stmt, +st: Cr.Cir.State, +F: U32, +K: U32, +L: U32,
  +I: List<&2, Word(8n)>, -B: Nat, -Q: List<&2, U32> -> Cr.Cir.Cells -> U32 -> U32 -> Type, -R: Cr.Cir.State -> Type,
  -H: U32 -> Cr.Cir.State -> Type, eb: {Nat.is_le(n, f) == b : Bool}, h: S.Ok(Cr.Cir.exec(n, s, st), F, K, L, I, B, Q),
  g: @st2: Cr.Cir.State -> S.At(st2, F, K, L, I, Q) -> R(st2)) -> D.PostB(False{}, Cr.Cir.exec(f, s, st), R, H, B, L):
  match b:
    case True{}:
      fuel.high(Cr.Cir.exec(n, s, st), f, n, s, st, F, K, L, I, B, Q, R, H, N.toLe(n, f, eb), {==}, h, g)
    case False{}:
      fuel.low(Cr.Cir.exec(f, s, st), f, n, s, st, F, K, L, I, B, Q, R, H, le.not(n, f, eb), {==}, h, g)

# the run of one fuel n that Ok allows: for any fuel f, what PostB allows
def fuel.post(+f: Nat, +n: Nat, +s: Cr.Cir.Stmt, +st: Cr.Cir.State, +F: U32, +K: U32, +L: U32, +I: List<&2, Word(8n)>, -B: Nat,
  -Q: List<&2, U32> -> Cr.Cir.Cells -> U32 -> U32 -> Type, -R: Cr.Cir.State -> Type, -H: U32 -> Cr.Cir.State -> Type,
  h: S.Ok(Cr.Cir.exec(n, s, st), F, K, L, I, B, Q), g: @st2: Cr.Cir.State -> S.At(st2, F, K, L, I, Q) -> R(st2)) ->
  D.PostB(False{}, Cr.Cir.exec(f, s, st), R, H, B, L):
  fuel.cmp(Nat.is_le(n, f), f, n, s, st, F, K, L, I, B, Q, R, H, {==}, h, g)

# The locals' bound
# -----------------

# 2147483648 is the word of bit 31
def lit.b31() -> {2147483648 == U32{N.bit(32n, 31n)} : U32}:
  {==}

# 2147483648 = 2^31 (with a parameter, so that the checker never expands 2^31)
def val.b31(-u: Unit) -> {U32.to_nat(2147483648) == N.D(31n, 1n) : Nat}:
  %Equal.sym(U32, 2147483648, U32{N.bit(32n, 31n)}, lit.b31()) : {U32.to_nat(_) == N.D(31n, 1n) : Nat}
  %Equal.sym(Nat, U32.to_nat(U32{N.bit(32n, 31n)}), Word.to_nat(32n, N.bit(32n, 31n)), N.u32_to_nat(N.bit(32n, 31n))) :
    {_ == N.D(31n, 1n) : Nat}
  N.bit_val(32n, 31n, Unit{})

# the free variables of each of xs below n: Fvs
def fvs.of(xs: List<&2, Bk.Term>, +n: Nat, +h: {D.Terms.below(xs, n) == True{} : Bool}) -> S.Fvs(xs, n):
  match xs:
    case Nil{}:
      Unit{}
    case Con{+x, +rest}:
      (N.toT(Nat.is_le(S.Fv(x), n), below.fv(x, n, CK.Bo.and_l(D.Term.below(x, n), D.Terms.below(rest, n), h))),
       fvs.of(rest, n, CK.Bo.and_r(D.Term.below(x, n), D.Terms.below(rest, n), h)))

# the free variables of each of xs below n, which is b: Fvs of b (over
# variables, so that no rewrite meets the closed 2^31)
def fvs.eq(xs: List<&2, Bk.Term>, +n: Nat, -b: Nat, e: {n == b : Nat}, +h: {D.Terms.below(xs, n) == True{} : Bool}) -> S.Fvs(xs, b):
  %e : S.Fvs(xs, _)
  fvs.of(xs, n, h)

# copy.post's bound on the locals is Cp.ok's
def fvs.b31(xs: List<&2, Bk.Term>, +h: {D.Terms.below(xs, U32.to_nat(2147483648)) == True{} : Bool}) -> S.Fvs(xs, N.D(31n, 1n)):
  fvs.eq(xs, U32.to_nat(2147483648), N.D(31n, 1n), val.b31(Unit{}), h)

# The laws
# --------

def K.copy.post(f, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, wt, keep, os, bs, fs, sp, pend, ps, c, t, ce, es, xs, zs, hs, hac, hl, hc, hp, he, hn, env, ho, hv, hk):
  ?TODO

def K.copy.done(ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, wt, os, bs, fs, sp, pend, ps, c, t, ce, es, xs, zs, hs, hac, hl, hc, hp, he, hn, env, ho, hv):
  ?TODO
