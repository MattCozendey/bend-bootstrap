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

# The laws
# --------

def K.copy.post(f, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, r, src, keep, os, bs, fs, sp, pend, ps, c, t, ce, es, xs, zs, hs, hac, hl, hc, hp, he, hn, env, hr, hsrc, ho, hv, hk):
  ?TODO

def K.copy.done(ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, r, src, os, bs, fs, sp, pend, ps, c, t, ce, es, hs, hl, hc, hp, he, hn, env, hr, hsrc, ho):
  ?TODO
