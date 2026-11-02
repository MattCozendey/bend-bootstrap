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
import ../../Eval/impl.bend as El
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

# The counts
# ----------
#
# HS counts each term cell's pointers exactly (Cnt), with at most 64 roots;
# Pre asks a count of at most 64 more than the own cells' pointers (Cb).

# a Bool whose truth holds is True
def of.t(+b: Bool, +t: N.T(b)) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, t)

# not x < y gives y <= x
def nlt.le(+x: U32, +y: U32, +h: {U32.is_lt(x, y) == False{} : Bool}) -> {U32.is_le(y, x) == True{} : Bool}:
  CK.U.le_t(y, x, CK.nlt.of(U32.cmp(x, y), U32.to_nat(x), U32.to_nat(y), N.U32.rel(x, y), h))

# a sum the other way
def add.comm(+a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, N.add_zero(b))
    case 1n+(+p):
      Equal.trans(Nat, 1n+Nat.add(p, b), 1n+Nat.add(b, p), Nat.add(b, 1n+p), Equal.cong(Nat, Nat, k => 1n+k, Nat.add(p, b), Nat.add(b, p), add.comm(p, b)),
        Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), N.add_succ_r(b, p)))

# a Bool's number is at most 1
def of.le1(+b: Bool) -> N.Le(D.Nat.of(b), 1n):
  match b:
    case True{}:
      Unit{}
    case False{}:
      Unit{}

# the roots that are c are at most the roots
def rcl.le(+rs: List<&2, U32>, +c: U32) -> N.Le(D.RcL(rs, c), List.length(&2, U32, rs)):
  match rs:
    case Nil{}:
      Unit{}
    case Con{+r, +rest}:
      N.add_mono(D.Nat.of(U32.is_eq(r, c)), 1n, D.RcL(rest, c), List.length(&2, U32, rest), of.le1(U32.is_eq(r, c)), rcl.le(rest, c))

# the roots' cells are as many as the roots
def cells.len(+os: List<&2, D.Rt>) -> {List.length(&2, U32, D.Rt.cells(os)) == List.length(&2, D.Rt, os) : Nat}:
  match os:
    case Nil{}:
      {==}
    case Con{D.Rt{c, u}, +rest}:
      Equal.cong(Nat, Nat, k => 1n+k, List.length(&2, U32, D.Rt.cells(rest)), List.length(&2, D.Rt, rest), cells.len(rest))

# a count that is the pointers, the own cells' and at most 64 roots', is at
# most the own cells' and 64
def cnt.le(+k: Nat, +p: Nat, +r: Nat, +e: {Nat.is_eq(k, Nat.add(p, r)) == True{} : Bool}, +hr: N.Le(r, 64n)) ->
  {Nat.is_le(k, Nat.add(64n, p)) == True{} : Bool}:
  %Equal.sym(Nat, k, Nat.add(p, r), nat.eq(k, Nat.add(p, r), e)) : {Nat.is_le(_, Nat.add(64n, p)) == True{} : Bool}
  of.t(Nat.is_le(Nat.add(p, r), Nat.add(64n, p)), N.le_rw_r(Nat.add(p, r), Nat.add(p, 64n), Nat.add(64n, p), add.comm(p, 64n),
    N.add_mono(p, p, r, 64n, N.le_refl(p), hr)))

# one cell: each case of Cnt is one of Cb
def cb.at(+a: Bool, +b: Bool, +c: Bool, +d: Bool, +a2: Bool, +b2: Bool, +c2: Bool, +d2: Bool,
  +h: {Bool.or(a, Bool.or(b, Bool.or(c, d))) == True{} : Bool}, fa: {a == True{} : Bool} -> {a2 == True{} : Bool},
  fb: {b == True{} : Bool} -> {b2 == True{} : Bool}, fc: {c == True{} : Bool} -> {c2 == True{} : Bool},
  fd: {d == True{} : Bool} -> {d2 == True{} : Bool}) -> {Bool.or(Bool.or(a2, Bool.or(b2, c2)), d2) == True{} : Bool}:
  match a:
    case True{}:
      CK.Bo.or_il(Bool.or(a2, Bool.or(b2, c2)), d2, CK.Bo.or_il(a2, Bool.or(b2, c2), fa({==})))
    case False{}:
      match b:
        case True{}:
          CK.Bo.or_il(Bool.or(a2, Bool.or(b2, c2)), d2, CK.Bo.or_ir(a2, Bool.or(b2, c2), CK.Bo.or_il(b2, c2, fb({==}))))
        case False{}:
          match c:
            case True{}:
              CK.Bo.or_il(Bool.or(a2, Bool.or(b2, c2)), d2, CK.Bo.or_ir(a2, Bool.or(b2, c2), CK.Bo.or_ir(b2, c2, fc({==}))))
            case False{}:
              CK.Bo.or_ir(Bool.or(a2, Bool.or(b2, c2)), d2, fd(h))

# HS's exact counts, with at most 64 roots, give Pre's bound on them
def cnt.cb(+n: Nat, +m: Cr.Cir.Cells, +c: U32, +N0: Nat, +fi: U32, +ps: List<&2, U32>, +rs: List<&2, U32>,
  +h: {D.Cnt(n, m, c, N0, fi, ps, rs) == True{} : Bool}, +hr: N.Le(List.length(&2, U32, rs), 64n)) ->
  {S.Cb(n, m, c, ps, fi, N0) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      +at = Bool.or(Bool.not(U32.is_lt(D.Tg(m, c), 19)), Bool.or(D.Fl(m, c, 1024), Bool.or(D.Mem(ps, c),
        Nat.is_eq(U32.to_nat(D.Fd(1n, m, c)), D.Ptr(N0, m, fi, ps, rs, c)))))
      +bt = Bool.or(Bool.or(U32.is_le(19, U32.and(S.Fd(0n, m, c), 63)), Bool.or(S.Stc(m, c), S.Has(ps, c))),
        Nat.is_le(U32.to_nat(S.Fd(1n, m, c)), Nat.add(64n, S.Pc(N0, m, ps, fi, c))))
      +rl = N.le_trans(D.RcL(rs, c), List.length(&2, U32, rs), 64n, rcl.le(rs, c), hr)
      CK.Bo.and_i(bt, S.Cb(p, m, U32.inc(c), ps, fi, N0),
        cb.at(Bool.not(U32.is_lt(D.Tg(m, c), 19)), D.Fl(m, c, 1024), D.Mem(ps, c), Nat.is_eq(U32.to_nat(D.Fd(1n, m, c)), D.Ptr(N0, m, fi, ps, rs, c)),
          U32.is_le(19, U32.and(S.Fd(0n, m, c), 63)), S.Stc(m, c), S.Has(ps, c), Nat.is_le(U32.to_nat(S.Fd(1n, m, c)), Nat.add(64n, S.Pc(N0, m, ps, fi, c))),
          CK.Bo.and_l(at, D.Cnt(p, m, U32.inc(c), N0, fi, ps, rs), h),
          e => nlt.le(D.Tg(m, c), 19, CK.Bo.not_t(U32.is_lt(D.Tg(m, c), 19), e)),
          e => e,
          e => Equal.trans(Bool, S.Has(ps, c), D.Mem(ps, c), True{}, Equal.sym(Bool, D.Mem(ps, c), S.Has(ps, c), mem.has(ps, c)), e),
          e => (%pc.eq(N0, m, ps, fi, c) :
            {Nat.is_le(U32.to_nat(D.Fd(1n, m, c)), Nat.add(64n, _)) == True{} : Bool};
            cnt.le(U32.to_nat(D.Fd(1n, m, c)), D.Pc(N0, m, ps, fi, c), D.RcL(rs, c), e, rl))),
        cnt.cb(p, m, U32.inc(c), N0, fi, ps, rs, CK.Bo.and_r(at, D.Cnt(p, m, U32.inc(c), N0, fi, ps, rs), h), hr))

# The pend list
# -------------

# HS's pend list is AL's chain
def chain.of(+ps: List<&2, U32>, +m: Cr.Cir.Cells, +p: U32, +h: D.Chain(ps, m, p)) -> {S.Chain(ps, m, p) == True{} : Bool}:
  match ps:
    case Nil{}:
      zero.ok(p, h)
    case Con{+x, +rest}:
      (e1, r1) = h
      (e2, h2) = r1
      CK.Bo.and_i(U32.is_eq(p, x), Bool.and(Bool.not(U32.is_zero(x)), S.Chain(rest, m, S.Fd(1n, m, x))),
        (%Equal.sym(U32, p, x, e1) : {U32.is_eq(_, x) == True{} : Bool}; CK.U.eq_refl(x)),
        CK.Bo.and_i(Bool.not(U32.is_zero(x)), S.Chain(rest, m, S.Fd(1n, m, x)), CK.Bo.not_i(U32.is_zero(x), e2),
          chain.of(rest, m, D.Fd(1n, m, x), h2)))

# a chain from p is the only one
def chain.det(+xs: List<&2, U32>, +ys: List<&2, U32>, +m: Cr.Cir.Cells, +p: U32, +hx: D.Chain(xs, m, p), +hy: D.Chain(ys, m, p)) ->
  {xs == ys : List<&2, U32>}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{+y, +yr}:
      (ey, ry) = hy
      (ez, hy2) = ry
      CK.Bo.tf({Nil{} == Con{y, yr} : List<&2, U32>}, Equal.trans(Bool, False{}, U32.is_eq(y, 0), True{}, Equal.sym(Bool, U32.is_eq(y, 0), False{}, ez),
        (%Equal.trans(U32, y, p, 0, Equal.sym(U32, p, y, ey), hx) : {U32.is_eq(y, _) == True{} : Bool}; CK.U.eq_refl(y))))
    case Con{+x, +xr} Nil{}:
      (ex, rx) = hx
      (ez, hx2) = rx
      CK.Bo.tf({Con{x, xr} == Nil{} : List<&2, U32>}, Equal.trans(Bool, False{}, U32.is_eq(x, 0), True{}, Equal.sym(Bool, U32.is_eq(x, 0), False{}, ez),
        (%Equal.trans(U32, x, p, 0, Equal.sym(U32, p, x, ex), hy) : {U32.is_eq(x, _) == True{} : Bool}; CK.U.eq_refl(x))))
    case Con{+x, +xr} Con{+y, +yr}:
      (ex, rx) = hx
      (ezx, hx2) = rx
      (ey, ry) = hy
      (ezy, hy2) = ry
      +exy = Equal.trans(U32, x, p, y, Equal.sym(U32, p, x, ex), ey)
      +er = chain.det(xr, yr, m, D.Fd(1n, m, x), hx2, (%Equal.sym(U32, x, y, exy) : D.Chain(yr, m, D.Fd(1n, m, _)); hy2))
      %exy : {Con{x, xr} == Con{_, yr} : List<&2, U32>}
      %er : {Con{x, xr} == Con{x, _} : List<&2, U32>}
      {==}

def chain.at.r(+rest: List<&2, U32>, +m: Cr.Cir.Cells, +x: U32,
  +r: D.Ex(List<&2, U32>, ys => D.P2(D.Chain(ys, m, x), N.Le(List.length(&2, U32, ys), List.length(&2, U32, rest))))) ->
  D.Ex(List<&2, U32>, ys => D.P2(D.Chain(ys, m, x), N.Le(List.length(&2, U32, ys), 1n+List.length(&2, U32, rest)))):
  (+ys, rr) = r
  (hc, hl) = rr
  (ys, (hc, N.le_succ(List.length(&2, U32, ys), List.length(&2, U32, rest), hl)))

# the place of x in a chain from p: the rest from there is a chain from x, at most as long
def chain.at.b(+b: Bool, +y: U32, +rest: List<&2, U32>, +m: Cr.Cir.Cells, +p: U32, +x: U32, +eb: {U32.is_eq(y, x) == b : Bool},
  +h: D.Chain(Con{y, rest}, m, p), +hx: {Bool.or(b, S.Has(rest, x)) == True{} : Bool},
  k: {S.Has(rest, x) == True{} : Bool} -> D.Ex(List<&2, U32>, ys => D.P2(D.Chain(ys, m, x), N.Le(List.length(&2, U32, ys), List.length(&2, U32, rest))))) ->
  D.Ex(List<&2, U32>, ys => D.P2(D.Chain(ys, m, x), N.Le(List.length(&2, U32, ys), 1n+List.length(&2, U32, rest)))):
  match b:
    case True{}:
      (h1, h2) = h
      (Con{y, rest}, ((Equal.sym(U32, y, x, CK.U.eq(y, x, eb)), h2), N.le_refl(1n+List.length(&2, U32, rest))))
    case False{}:
      chain.at.r(rest, m, x, k(hx))

def chain.at(+xs: List<&2, U32>, +m: Cr.Cir.Cells, +p: U32, +x: U32, +h: D.Chain(xs, m, p), +hx: {S.Has(xs, x) == True{} : Bool}) ->
  D.Ex(List<&2, U32>, ys => D.P2(D.Chain(ys, m, x), N.Le(List.length(&2, U32, ys), List.length(&2, U32, xs)))):
  match xs:
    case Nil{}:
      CK.Bo.tf(D.Ex(List<&2, U32>, ys => D.P2(D.Chain(ys, m, x), N.Le(List.length(&2, U32, ys), 0n))), hx)
    case Con{+y, +rest}:
      (h1, h2) = h
      (h3, h4) = h2
      chain.at.b(U32.is_eq(y, x), y, rest, m, p, x, {==}, h, hx, e => chain.at(rest, m, D.Fd(1n, m, y), x, h4, e))

# a chain from x, at most as long as rest, is not x then rest
def chain.loop(+x: U32, +rest: List<&2, U32>, +m: Cr.Cir.Cells,
  +r: D.Ex(List<&2, U32>, ys => D.P2(D.Chain(ys, m, x), N.Le(List.length(&2, U32, ys), List.length(&2, U32, rest)))),
  hx: D.Chain(Con{x, rest}, m, x)) -> {True{} == False{} : Bool}:
  (+ys, rr) = r
  (hc, hl) = rr
  +e = chain.det(ys, Con{x, rest}, m, x, hc, hx)
  Empty.absurd({True{} == False{} : Bool}, N.not_succ_le(List.length(&2, U32, rest),
    (%e : N.Le(List.length(&2, U32, _), List.length(&2, U32, rest)); hl)))

# the head of a chain is not in its rest: else the rest from there would be the chain, and longer than itself
def chain.out(+b: Bool, +x: U32, +rest: List<&2, U32>, +m: Cr.Cir.Cells, +p: U32, +eb: {S.Has(rest, x) == b : Bool},
  +h: D.Chain(Con{x, rest}, m, p)) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      (h1, h2) = h
      (h3, h4) = h2
      chain.loop(x, rest, m, chain.at(rest, m, D.Fd(1n, m, x), x, h4, eb), (%h1 : D.Chain(Con{x, rest}, m, _); h))

# a chain holds each cell once
def chain.nodup(+xs: List<&2, U32>, +m: Cr.Cir.Cells, +p: U32, +h: D.Chain(xs, m, p)) -> {S.Nodup(xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      (h1, h2) = h
      (h3, h4) = h2
      CK.Bo.and_i(Bool.not(S.Has(rest, x)), S.Nodup(rest), CK.Bo.not_i(S.Has(rest, x), chain.out(S.Has(rest, x), x, rest, m, p, {==}, h)),
        chain.nodup(rest, m, D.Fd(1n, m, x), h4))

# The locals
# ----------

# the K.arg cells of the chain from a
def Ag.links(+xs: List<&2, El.Arg>, +m: Cr.Cir.Cells, +a: U32) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{_, +rest}:
      Con{a, Ag.links(rest, m, D.Fd(1n, m, a))}

# the chain of K.args is a chain, of the machine's own cells
def ag.chain(+xs: List<&2, El.Arg>, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +os: List<&2, D.Rt>, +vs: List<&2, U32>, +a: U32,
  +h: D.Ag(ds, m, im, fi, nx, ks, img, ps, os, vs, a, xs)) -> D.Chain(Ag.links(xs, m, a), m, a):
  match xs:
    case Nil{}:
      h
    case Con{El.Arg{+q, +x}, +rest}:
      (e0, r0) = h
      (e1, r1) = r0
      (e2, r2) = r1
      (e3, r3) = r2
      (e4, r4) = r3
      (e5, r5) = r4
      (e6, r6) = r5
      (e7, r7) = r6
      (e8, r8) = r7
      (e9, r9) = r8
      (e10, r10) = r9
      (e11, h2) = r10
      ({==}, (e0, ag.chain(rest, ds, m, im, fi, nx, ks, img, ps, os, vs, D.Fd(1n, m, a), h2)))

def ag.lt(+xs: List<&2, El.Arg>, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +os: List<&2, D.Rt>, +vs: List<&2, U32>, +a: U32,
  +h: D.Ag(ds, m, im, fi, nx, ks, img, ps, os, vs, a, xs)) -> {S.All.lt(Ag.links(xs, m, a), nx) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{El.Arg{+q, +x}, +rest}:
      (e0, r0) = h
      (e1, r1) = r0
      (e2, r2) = r1
      (e3, r3) = r2
      (e4, r4) = r3
      (e5, r5) = r4
      (e6, r6) = r5
      (e7, r7) = r6
      (e8, r8) = r7
      (e9, r9) = r8
      (e10, r10) = r9
      (e11, h2) = r10
      CK.Bo.and_i(U32.is_lt(a, nx), S.All.lt(Ag.links(rest, m, D.Fd(1n, m, a)), nx), CK.Bo.and_r(U32.is_le(fi, a), U32.is_lt(a, nx), e2),
        ag.lt(rest, ds, m, im, fi, nx, ks, img, ps, os, vs, D.Fd(1n, m, a), h2))

def links.len(+xs: List<&2, El.Arg>, +m: Cr.Cir.Cells, +a: U32) -> {List.length(&2, U32, Ag.links(xs, m, a)) == List.length(&2, El.Arg, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{_, +rest}:
      Equal.cong(Nat, Nat, k => 1n+k, List.length(&2, U32, Ag.links(rest, m, D.Fd(1n, m, a))), List.length(&2, El.Arg, rest),
        links.len(rest, m, D.Fd(1n, m, a)))

def terms.len(+xs: List<&2, El.Arg>) -> {List.length(&2, Bk.Term, D.Arg.terms(xs)) == List.length(&2, El.Arg, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{El.Arg{_, x}, +rest}:
      Equal.cong(Nat, Nat, k => 1n+k, List.length(&2, Bk.Term, D.Arg.terms(rest)), List.length(&2, El.Arg, rest), terms.len(rest))

# Distinct numbers below n are at most n
# --------------------------------------

def Has.n(+xs: List<&2, Nat>, +k: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{+x, rest}:
      Bool.or(Nat.is_eq(x, k), Has.n(rest, k))

def Nodup.n(+xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, +rest}:
      Bool.and(Bool.not(Has.n(rest, x)), Nodup.n(rest))

def Lt.n(+xs: List<&2, Nat>, +n: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, rest}:
      Bool.and(Nat.is_lt(x, n), Lt.n(rest, n))

# xs but the numbers k
def Del.n(+xs: List<&2, Nat>, +k: Nat) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, +rest}:
      Bool.pick(List<&2, Nat>, Nat.is_eq(x, k), Del.n(rest, k), Con{x, Del.n(rest, k)})

# x < 1 + p and x is not p: x < p
def lt.pred(+x: Nat, +p: Nat, +h1: {Nat.is_lt(x, 1n+p) == True{} : Bool}, +h2: {Nat.is_eq(x, p) == False{} : Bool}) ->
  {Nat.is_lt(x, p) == True{} : Bool}:
  match x p:
    case 0n 0n:
      CK.Bo.ft({Nat.is_lt(0n, 0n) == True{} : Bool}, h2)
    case 0n 1n+pp:
      {==}
    case 1n+xp 0n:
      CT.Tz.lt0.no(xp, {Nat.is_lt(1n+xp, 0n) == True{} : Bool}, h1)
    case 1n+xp 1n+pp:
      lt.pred(xp, pp, h1, h2)

def del.lt.b(+b: Bool, +x: Nat, +p: Nat, +rest: List<&2, Nat>, +eb: {Nat.is_eq(x, p) == b : Bool}, +hx: {Nat.is_lt(x, 1n+p) == True{} : Bool},
  +hr: {Lt.n(Del.n(rest, p), p) == True{} : Bool}) -> {Lt.n(Bool.pick(List<&2, Nat>, b, Del.n(rest, p), Con{x, Del.n(rest, p)}), p) == True{} : Bool}:
  match b:
    case True{}:
      hr
    case False{}:
      CK.Bo.and_i(Nat.is_lt(x, p), Lt.n(Del.n(rest, p), p), lt.pred(x, p, hx, eb), hr)

# the numbers of xs below 1 + p but p are below p
def del.lt(+xs: List<&2, Nat>, +p: Nat, +h: {Lt.n(xs, 1n+p) == True{} : Bool}) -> {Lt.n(Del.n(xs, p), p) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      del.lt.b(Nat.is_eq(x, p), x, p, rest, {==}, CK.Bo.and_l(Nat.is_lt(x, 1n+p), Lt.n(rest, 1n+p), h),
        del.lt(rest, p, CK.Bo.and_r(Nat.is_lt(x, 1n+p), Lt.n(rest, 1n+p), h)))

def del.has.c(+a: Bool, +d: Bool, +r: Bool, +h: {Bool.or(a, d) == True{} : Bool}, hr: {d == True{} : Bool} -> {r == True{} : Bool}) ->
  {Bool.or(a, r) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      hr(h)

def del.has.b(+b: Bool, +x: Nat, +p: Nat, +k: Nat, +rest: List<&2, Nat>,
  hr: {Has.n(Del.n(rest, p), k) == True{} : Bool} -> {Has.n(rest, k) == True{} : Bool},
  h: {Has.n(Bool.pick(List<&2, Nat>, b, Del.n(rest, p), Con{x, Del.n(rest, p)}), k) == True{} : Bool}) ->
  {Bool.or(Nat.is_eq(x, k), Has.n(rest, k)) == True{} : Bool}:
  match b:
    case True{}:
      CK.Bo.or_ir(Nat.is_eq(x, k), Has.n(rest, k), hr(h))
    case False{}:
      del.has.c(Nat.is_eq(x, k), Has.n(Del.n(rest, p), k), Has.n(rest, k), h, hr)

# a number of xs but the numbers p is one of xs
def del.has(+xs: List<&2, Nat>, +p: Nat, +k: Nat, +h: {Has.n(Del.n(xs, p), k) == True{} : Bool}) -> {Has.n(xs, k) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case Con{+x, +rest}:
      del.has.b(Nat.is_eq(x, p), x, p, k, rest, e => del.has(rest, p, k, e), h)

def not.has.b(+b: Bool, +xs: List<&2, Nat>, +p: Nat, +k: Nat, +eb: {Has.n(Del.n(xs, p), k) == b : Bool}, +h: {Has.n(xs, k) == False{} : Bool}) ->
  {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      CK.Bo.tf({True{} == False{} : Bool}, Equal.trans(Bool, False{}, Has.n(xs, k), True{}, Equal.sym(Bool, Has.n(xs, k), False{}, h),
        del.has(xs, p, k, eb)))

def not.has(+xs: List<&2, Nat>, +p: Nat, +k: Nat, +h: {Has.n(xs, k) == False{} : Bool}) -> {Has.n(Del.n(xs, p), k) == False{} : Bool}:
  not.has.b(Has.n(Del.n(xs, p), k), xs, p, k, {==}, h)

def del.nd.b(+b: Bool, +x: Nat, +p: Nat, +rest: List<&2, Nat>, +hx: {Has.n(rest, x) == False{} : Bool}, +hr: {Nodup.n(Del.n(rest, p)) == True{} : Bool}) ->
  {Nodup.n(Bool.pick(List<&2, Nat>, b, Del.n(rest, p), Con{x, Del.n(rest, p)})) == True{} : Bool}:
  match b:
    case True{}:
      hr
    case False{}:
      CK.Bo.and_i(Bool.not(Has.n(Del.n(rest, p), x)), Nodup.n(Del.n(rest, p)), CK.Bo.not_i(Has.n(Del.n(rest, p), x), not.has(rest, p, x, hx)), hr)

# xs but the numbers p hold each number once
def del.nd(+xs: List<&2, Nat>, +p: Nat, +h: {Nodup.n(xs) == True{} : Bool}) -> {Nodup.n(Del.n(xs, p)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      del.nd.b(Nat.is_eq(x, p), x, p, rest, CK.Bo.not_t(Has.n(rest, x), CK.Bo.and_l(Bool.not(Has.n(rest, x)), Nodup.n(rest), h)),
        del.nd(rest, p, CK.Bo.and_r(Bool.not(Has.n(rest, x)), Nodup.n(rest), h)))

def heap.or.r(+a: Bool, +b: Bool, +h: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      CK.Bo.ft({b == False{} : Bool}, h)
    case False{}:
      h

def del.none.b(+b: Bool, +x: Nat, +p: Nat, +rest: List<&2, Nat>, +eb: {Nat.is_eq(x, p) == b : Bool}, +h: {Bool.or(b, Has.n(rest, p)) == False{} : Bool},
  +hr: {List.length(&2, Nat, Del.n(rest, p)) == List.length(&2, Nat, rest) : Nat}) ->
  {List.length(&2, Nat, Bool.pick(List<&2, Nat>, b, Del.n(rest, p), Con{x, Del.n(rest, p)})) == 1n+List.length(&2, Nat, rest) : Nat}:
  match b:
    case True{}:
      CK.Bo.ft({List.length(&2, Nat, Del.n(rest, p)) == 1n+List.length(&2, Nat, rest) : Nat}, h)
    case False{}:
      Equal.cong(Nat, Nat, k => 1n+k, List.length(&2, Nat, Del.n(rest, p)), List.length(&2, Nat, rest), hr)

# with no p in xs, xs but the numbers p is xs
def del.none(+xs: List<&2, Nat>, +p: Nat, +h: {Has.n(xs, p) == False{} : Bool}) -> {List.length(&2, Nat, Del.n(xs, p)) == List.length(&2, Nat, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      del.none.b(Nat.is_eq(x, p), x, p, rest, {==}, h, del.none(rest, p, heap.or.r(Nat.is_eq(x, p), Has.n(rest, p), h)))

def del.len.b(+b: Bool, +x: Nat, +p: Nat, +rest: List<&2, Nat>, +eb: {Nat.is_eq(x, p) == b : Bool}, +hx: {Has.n(rest, x) == False{} : Bool},
  +hr: N.Le(List.length(&2, Nat, rest), 1n+List.length(&2, Nat, Del.n(rest, p)))) ->
  N.Le(1n+List.length(&2, Nat, rest), 1n+List.length(&2, Nat, Bool.pick(List<&2, Nat>, b, Del.n(rest, p), Con{x, Del.n(rest, p)}))):
  match b:
    case True{}:
      +e = nat.eq(x, p, eb)
      N.le_rw_r(1n+List.length(&2, Nat, rest), 1n+List.length(&2, Nat, rest), 1n+List.length(&2, Nat, Del.n(rest, p)),
        Equal.cong(Nat, Nat, k => 1n+k, List.length(&2, Nat, rest), List.length(&2, Nat, Del.n(rest, p)),
          Equal.sym(Nat, List.length(&2, Nat, Del.n(rest, p)), List.length(&2, Nat, rest),
            del.none(rest, p, (%e : {Has.n(rest, _) == False{} : Bool}; hx)))),
        N.le_refl(1n+List.length(&2, Nat, rest)))
    case False{}:
      hr

# p is at most once in xs: xs is at most 1 + xs but p
def del.len(+xs: List<&2, Nat>, +p: Nat, +h: {Nodup.n(xs) == True{} : Bool}) -> N.Le(List.length(&2, Nat, xs), 1n+List.length(&2, Nat, Del.n(xs, p))):
  match xs:
    case Nil{}:
      Unit{}
    case Con{+x, +rest}:
      del.len.b(Nat.is_eq(x, p), x, p, rest, {==}, CK.Bo.not_t(Has.n(rest, x), CK.Bo.and_l(Bool.not(Has.n(rest, x)), Nodup.n(rest), h)),
        del.len(rest, p, CK.Bo.and_r(Bool.not(Has.n(rest, x)), Nodup.n(rest), h)))

# distinct numbers below n are at most n
def ph(+n: Nat, +xs: List<&2, Nat>, +hd: {Nodup.n(xs) == True{} : Bool}, +hl: {Lt.n(xs, n) == True{} : Bool}) -> N.Le(List.length(&2, Nat, xs), n):
  match n:
    case 0n:
      match xs:
        case Nil{}:
          Unit{}
        case Con{+x, +rest}:
          CT.Tz.lt0.no(x, N.Le(1n+List.length(&2, Nat, rest), 0n), CK.Bo.and_l(Nat.is_lt(x, 0n), Lt.n(rest, 0n), hl))
    case 1n+(+p):
      N.le_trans(List.length(&2, Nat, xs), 1n+List.length(&2, Nat, Del.n(xs, p)), 1n+p, del.len(xs, p, hd),
        ph(p, Del.n(xs, p), del.nd(xs, p, hd), del.lt(xs, p, hl)))

# The cells as numbers
# --------------------

def Nats(+xs: List<&2, U32>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, rest}:
      Con{U32.to_nat(x), Nats(rest)}

def nats.len(+xs: List<&2, U32>) -> {List.length(&2, Nat, Nats(xs)) == List.length(&2, U32, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Equal.cong(Nat, Nat, k => 1n+k, List.length(&2, Nat, Nats(rest)), List.length(&2, U32, rest), nats.len(rest))

# both false: the disjunction is false
def or.ff(+a: Bool, -b: Bool, +ha: {a == False{} : Bool}, +hb: {b == False{} : Bool}) -> {Bool.or(a, b) == False{} : Bool}:
  %Equal.sym(Bool, a, False{}, ha) : {Bool.or(_, b) == False{} : Bool}
  hb

def of.or.l(+a: Bool, +b: Bool, +h: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      CK.Bo.ft({True{} == False{} : Bool}, h)
    case False{}:
      {==}

def nats.ne.b(+b: Bool, +y: U32, +x: U32, +eb: {Nat.is_eq(U32.to_nat(y), U32.to_nat(x)) == b : Bool}, +h: {U32.is_eq(y, x) == False{} : Bool}) ->
  {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      CK.Bo.tf({True{} == False{} : Bool}, Equal.trans(Bool, False{}, U32.is_eq(y, x), True{}, Equal.sym(Bool, U32.is_eq(y, x), False{}, h),
        D.u.nat.eq(y, x, nat.eq(U32.to_nat(y), U32.to_nat(x), eb))))

# a cell not in xs: its number not in their numbers
def nats.has(+xs: List<&2, U32>, +x: U32, +h: {S.Has(xs, x) == False{} : Bool}) -> {Has.n(Nats(xs), U32.to_nat(x)) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      or.ff(Nat.is_eq(U32.to_nat(y), U32.to_nat(x)), Has.n(Nats(rest), U32.to_nat(x)),
        nats.ne.b(Nat.is_eq(U32.to_nat(y), U32.to_nat(x)), y, x, {==}, of.or.l(U32.is_eq(y, x), S.Has(rest, x), h)),
        nats.has(rest, x, heap.or.r(U32.is_eq(y, x), S.Has(rest, x), h)))

def nats.nd(+xs: List<&2, U32>, +h: {S.Nodup(xs) == True{} : Bool}) -> {Nodup.n(Nats(xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      CK.Bo.and_i(Bool.not(Has.n(Nats(rest), U32.to_nat(x))), Nodup.n(Nats(rest)),
        CK.Bo.not_i(Has.n(Nats(rest), U32.to_nat(x)), nats.has(rest, x, CK.Bo.not_t(S.Has(rest, x), CK.Bo.and_l(Bool.not(S.Has(rest, x)), S.Nodup(rest), h)))),
        nats.nd(rest, CK.Bo.and_r(Bool.not(S.Has(rest, x)), S.Nodup(rest), h)))

# 1 + a <= b: a < b
def le.lt(+a: Nat, +b: Nat, +h: N.Le(1n+a, b)) -> {Nat.is_lt(a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, h)
    case 0n 1n+bp:
      {==}
    case 1n+ap 0n:
      Empty.absurd({Nat.is_lt(1n+ap, 0n) == True{} : Bool}, h)
    case 1n+ap 1n+bp:
      le.lt(ap, bp, h)

def nats.lt(+xs: List<&2, U32>, +N0: U32, +h: {S.All.lt(xs, N0) == True{} : Bool}) -> {Lt.n(Nats(xs), U32.to_nat(N0)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      CK.Bo.and_i(Nat.is_lt(U32.to_nat(x), U32.to_nat(N0)), Lt.n(Nats(rest), U32.to_nat(N0)),
        le.lt(U32.to_nat(x), U32.to_nat(N0), CK.U.lt(x, N0, CK.Bo.and_l(U32.is_lt(x, N0), S.All.lt(rest, N0), h))),
        nats.lt(rest, N0, CK.Bo.and_r(U32.is_lt(x, N0), S.All.lt(rest, N0), h)))

# the number of n, as a U32, is n, when n is at most a U32's
def to.from(+n: Nat, +M: U32, +h: N.Le(n, U32.to_nat(M))) -> {U32.to_nat(U32.from_nat(n)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      +ih = to.from(p, M, N.weaken(p, U32.to_nat(M), h))
      +h2 : N.Le(1n+U32.to_nat(U32.from_nat(p)), U32.to_nat(M)) = (%Equal.sym(Nat, U32.to_nat(U32.from_nat(p)), p, ih) : N.Le(1n+_, U32.to_nat(M)); h)
      Equal.trans(Nat, U32.to_nat(U32.inc(U32.from_nat(p))), 1n+U32.to_nat(U32.from_nat(p)), 1n+p, D.u.inc(U32.from_nat(p), M, h2),
        Equal.cong(Nat, Nat, k => 1n+k, U32.to_nat(U32.from_nat(p)), p, ih))

# the locals are at most the cells before next: their K.args are distinct cells below next
def ag.len(+xs: List<&2, El.Arg>, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +os: List<&2, D.Rt>, +vs: List<&2, U32>, +a: U32,
  +h: D.Ag(ds, m, im, fi, nx, ks, img, ps, os, vs, a, xs)) -> N.Le(List.length(&2, El.Arg, xs), U32.to_nat(nx)):
  +ls = Ag.links(xs, m, a)
  +b = ph(U32.to_nat(nx), Nats(ls), nats.nd(ls, chain.nodup(ls, m, a, ag.chain(xs, ds, m, im, fi, nx, ks, img, ps, os, vs, a, h))),
    nats.lt(ls, nx, ag.lt(xs, ds, m, im, fi, nx, ks, img, ps, os, vs, a, h)))
  %Equal.trans(Nat, List.length(&2, Nat, Nats(ls)), List.length(&2, U32, ls), List.length(&2, El.Arg, xs), nats.len(ls), links.len(xs, m, a)) :
    N.Le(_, U32.to_nat(nx))
  b

# register clen holds the locals' number: Cp.ok's hl
def clen.ok(+xs: List<&2, El.Arg>, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +os: List<&2, D.Rt>, +vs: List<&2, U32>, +a: U32,
  +regs: List<&2, U32>, +h: D.Ag(ds, m, im, fi, nx, ks, img, ps, os, vs, a, xs),
  +hn: {List.get(&2, U32, regs, 37n) == Some{U32.from_nat(List.length(&2, El.Arg, xs))} : Maybe<&2, U32>}) ->
  {U32.to_nat(T.tm.reg(regs, 37n)) == List.length(&2, Bk.Term, D.Arg.terms(xs)) : Nat}:
  %Equal.sym(Maybe<&2, U32>, List.get(&2, U32, regs, 37n), Some{U32.from_nat(List.length(&2, El.Arg, xs))}, hn) :
    {U32.to_nat(Maybe.default(&2, U32, _, 0)) == List.length(&2, Bk.Term, D.Arg.terms(xs)) : Nat}
  %Equal.sym(Nat, List.length(&2, Bk.Term, D.Arg.terms(xs)), List.length(&2, El.Arg, xs), terms.len(xs)) :
    {U32.to_nat(U32.from_nat(List.length(&2, El.Arg, xs))) == _ : Nat}
  to.from(List.length(&2, El.Arg, xs), nx, ag.len(xs, ds, m, im, fi, nx, ks, img, ps, os, vs, a, h))

# a K.arg's tag, 41, is the machine's own kind
def tag.karg(+m: Cr.Cir.Cells, +a: U32, +e: {D.Tg(m, a) == 41 : U32}) -> {Nat.is_le(19n, U32.to_nat(U32.and(S.Fd(0n, m, a), 63))) == True{} : Bool}:
  %Equal.sym(U32, D.Tg(m, a), 41, e) : {Nat.is_le(19n, U32.to_nat(_)) == True{} : Bool}
  {==}

# the K.args and their terms that the run may read
def Env.rx(+xs: List<&2, El.Arg>, +m: Cr.Cir.Cells, +a: U32, +X: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{El.Arg{_, x}, +rest}:
      Bool.and(Rx(X, a), Bool.and(Rx.all(x, m, D.Fd(2n, m, a), X), Env.rx(rest, m, D.Fd(1n, m, a), X)))

# the chain of K.args (Ag) is Env's list of the locals, when the run may read them
def ag.env(+xs: List<&2, El.Arg>, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +os: List<&2, D.Rt>, +vs: List<&2, U32>, +a: U32,
  +X: List<&2, U32>, +h: D.Ag(ds, m, im, fi, nx, ks, img, ps, os, vs, a, xs), +hx: {Env.rx(xs, m, a, X) == True{} : Bool}) ->
  S.Env(m, ks, img, im, fi, X, nx, a, D.Arg.terms(xs)):
  match xs:
    case Nil{}:
      Unit{}
    case Con{El.Arg{+q, +x}, +rest}:
      (e0, r0) = h
      (e1, r1) = r0
      (e2, r2) = r1
      (e3, r3) = r2
      (e4, r4) = r3
      (e5, r5) = r4
      (e6, r6) = r5
      (e7, r7) = r6
      (e8, r8) = r7
      (e9, r9) = r8
      (e10, r10) = r9
      (e11, h2) = r10
      +rr = CK.Bo.and_r(Rx(X, a), Bool.and(Rx.all(x, m, D.Fd(2n, m, a), X), Env.rx(rest, m, D.Fd(1n, m, a), X)), hx)
      (CK.Bo.and_i(Cr.Cir.is_cell(a, im, fi, nx), Rx(X, a), e1, CK.Bo.and_l(Rx(X, a), Bool.and(Rx.all(x, m, D.Fd(2n, m, a), X), Env.rx(rest, m, D.Fd(1n, m, a), X)), hx)),
       (tag.karg(m, a, e5),
       ((Pg.Term.size(x), tm.is.at(Pg.Term.size(x), True{}, ds, m, im, fi, nx, ks, img, X, D.Fd(2n, m, a), x, N.le_refl(Pg.Term.size(x)), e9,
          CK.Bo.and_l(Rx.all(x, m, D.Fd(2n, m, a), X), Env.rx(rest, m, D.Fd(1n, m, a), X), rr))),
        ag.env(rest, ds, m, im, fi, nx, ks, img, ps, os, vs, D.Fd(1n, m, a), X, h2,
          CK.Bo.and_r(Rx.all(x, m, D.Fd(2n, m, a), X), Env.rx(rest, m, D.Fd(1n, m, a), X), rr)))))

# Terms in the heap
# -----------------
#
# A node of a term (IsK at its root) stands for a subterm, no larger (node.sub),
# and one other than the root has a parent, a node whose pointers (Fs) hold
# it (node.par).

# a or b or c: G from any
def or3.case(a: Bool, b: Bool, c: Bool, -G: Type, h: {Bool.or(a, Bool.or(b, c)) == True{} : Bool}, ka: {a == True{} : Bool} -> G,
  kb: {b == True{} : Bool} -> G, kc: {c == True{} : Bool} -> G) -> G:
  match a:
    case True{}:
      ka({==})
    case False{}:
      match b:
        case True{}:
          kb({==})
        case False{}:
          kc(h)

# a or b or c or d: G from any
def or4.case(a: Bool, b: Bool, c: Bool, d: Bool, -G: Type, h: {Bool.or(a, Bool.or(b, Bool.or(c, d))) == True{} : Bool},
  ka: {a == True{} : Bool} -> G, kb: {b == True{} : Bool} -> G, kc: {c == True{} : Bool} -> G, kd: {d == True{} : Bool} -> G) -> G:
  match a:
    case True{}:
      ka({==})
    case False{}:
      or3.case(b, c, d, G, h, kb, kc, kd)

# a is false: b, from a or b
def or.drop(a: Bool, -b: Bool, h: {Bool.or(a, b) == True{} : Bool}, ha: {a == False{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      CK.Bo.ft({b == True{} : Bool}, ha)
    case False{}:
      h

# G from either value of x (b, by eb)
def bool.case(b: Bool, -x: Bool, -G: Type, eb: {x == b : Bool}, kt: {x == True{} : Bool} -> G, kf: {x == False{} : Bool} -> G) -> G:
  match b:
    case True{}:
      kt(eb)
    case False{}:
      kf(eb)

# the one case
def par.one(-x: Bool, -G: Type, h: {x == True{} : Bool}, k: {x == True{} : Bool} -> G) -> G:
  k(h)

# a node of the first part of two, or of the second, is a node of the whole
def in.l(a: Bool, b: Bool, d: Bool, h: {b == True{} : Bool}) -> {Bool.or(a, Bool.or(b, d)) == True{} : Bool}:
  CK.Bo.or_ir(a, Bool.or(b, d), CK.Bo.or_il(b, d, h))

def in.r(a: Bool, b: Bool, d: Bool, h: {d == True{} : Bool}) -> {Bool.or(a, Bool.or(b, d)) == True{} : Bool}:
  CK.Bo.or_ir(a, Bool.or(b, d), CK.Bo.or_ir(b, d, h))

# a node of the first, second or third part of three is a node of the whole
def in.a(a: Bool, b: Bool, d: Bool, e: Bool, h: {b == True{} : Bool}) -> {Bool.or(a, Bool.or(b, Bool.or(d, e))) == True{} : Bool}:
  CK.Bo.or_ir(a, Bool.or(b, Bool.or(d, e)), CK.Bo.or_il(b, Bool.or(d, e), h))

def in.b(a: Bool, b: Bool, d: Bool, e: Bool, h: {d == True{} : Bool}) -> {Bool.or(a, Bool.or(b, Bool.or(d, e))) == True{} : Bool}:
  CK.Bo.or_ir(a, Bool.or(b, Bool.or(d, e)), CK.Bo.or_ir(b, Bool.or(d, e), CK.Bo.or_il(d, e, h)))

def in.c(a: Bool, b: Bool, d: Bool, e: Bool, h: {e == True{} : Bool}) -> {Bool.or(a, Bool.or(b, Bool.or(d, e))) == True{} : Bool}:
  CK.Bo.or_ir(a, Bool.or(b, Bool.or(d, e)), CK.Bo.or_ir(b, Bool.or(d, e), CK.Bo.or_ir(d, e, h)))

# the root is the node c: it stands for t
def sub.root(+t: Bk.Term, +dk: Bool, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +r: U32, +c: U32, h: D.IsK(dk, ds, m, im, fi, nx, ks, img, r, t),
  e: {r == c : U32}) -> D.Ex(Bk.Term, v => D.P2(D.IsK(dk, ds, m, im, fi, nx, ks, img, c, v), N.Le(Pg.Term.size(v), Pg.Term.size(t)))):
  (t, ((%e : D.IsK(dk, ds, m, im, fi, nx, ks, img, _, t); h), N.le_refl(Pg.Term.size(t))))

# a node's term no larger than a part of t is no larger than t
def sub.up(+y: Bk.Term, +t: Bk.Term, -dk: Bool, -ds: List<&2, Bk.Def>, -m: Cr.Cir.Cells, -im: U32, -fi: U32, -nx: U32,
  -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -c: U32,
  r: D.Ex(Bk.Term, v => D.P2(D.IsK(dk, ds, m, im, fi, nx, ks, img, c, v), N.Le(Pg.Term.size(v), Pg.Term.size(y)))),
  +le: N.Le(Pg.Term.size(y), Pg.Term.size(t))) ->
  D.Ex(Bk.Term, v => D.P2(D.IsK(dk, ds, m, im, fi, nx, ks, img, c, v), N.Le(Pg.Term.size(v), Pg.Term.size(t)))):
  (+v, rr) = r
  (hv, hl) = rr
  (v, (hv, N.le_trans(Pg.Term.size(v), Pg.Term.size(y), Pg.Term.size(t), hl, le)))

# r is a node of the term t at r
def node.root(t: Bk.Term, +m: Cr.Cir.Cells, +r: U32) -> {D.Node(t, m, r, r) == True{} : Bool}:
  match t:
    case Bk.Term.Var{_}:
      CK.U.eq_refl(r)
    case Bk.Term.Ref{_}:
      CK.U.eq_refl(r)
    case Bk.Term.Ann{y, z}:
      CK.Bo.or_il(U32.is_eq(r, r), Bool.or(D.Node(y, m, D.Fd(2n, m, r), r), D.Node(z, m, D.Fd(3n, m, r), r)), CK.U.eq_refl(r))
    case Bk.Term.Let{_, y, z}:
      CK.Bo.or_il(U32.is_eq(r, r), Bool.or(D.Node(y, m, D.Fd(2n, m, r), r), D.Node(z, m, D.Fd(3n, m, r), r)), CK.U.eq_refl(r))
    case Bk.Term.Typ{y}:
      CK.Bo.or_il(U32.is_eq(r, r), D.Node(y, m, D.Fd(2n, m, r), r), CK.U.eq_refl(r))
    case Bk.Term.Min{y, z}:
      CK.Bo.or_il(U32.is_eq(r, r), Bool.or(D.Node(y, m, D.Fd(2n, m, r), r), D.Node(z, m, D.Fd(3n, m, r), r)), CK.U.eq_refl(r))
    case Bk.Term.All{_, y, z}:
      CK.Bo.or_il(U32.is_eq(r, r), Bool.or(D.Node(y, m, D.Fd(2n, m, r), r), D.Node(z, m, D.Fd(3n, m, r), r)), CK.U.eq_refl(r))
    case Bk.Term.Lam{_, y}:
      CK.Bo.or_il(U32.is_eq(r, r), D.Node(y, m, D.Fd(2n, m, r), r), CK.U.eq_refl(r))
    case Bk.Term.App{_, y, z}:
      CK.Bo.or_il(U32.is_eq(r, r), Bool.or(D.Node(y, m, D.Fd(2n, m, r), r), D.Node(z, m, D.Fd(3n, m, r), r)), CK.U.eq_refl(r))
    case Bk.Term.Sig{_, y, z}:
      CK.Bo.or_il(U32.is_eq(r, r), Bool.or(D.Node(y, m, D.Fd(2n, m, r), r), D.Node(z, m, D.Fd(3n, m, r), r)), CK.U.eq_refl(r))
    case Bk.Term.Tup{_, y, z}:
      CK.Bo.or_il(U32.is_eq(r, r), Bool.or(D.Node(y, m, D.Fd(2n, m, r), r), D.Node(z, m, D.Fd(3n, m, r), r)), CK.U.eq_refl(r))
    case Bk.Term.Prj{y}:
      CK.Bo.or_il(U32.is_eq(r, r), D.Node(y, m, D.Fd(2n, m, r), r), CK.U.eq_refl(r))
    case Bk.Term.Enu{_}:
      CK.U.eq_refl(r)
    case Bk.Term.Lab{_}:
      CK.U.eq_refl(r)
    case Bk.Term.Mat{_, y, z}:
      CK.Bo.or_il(U32.is_eq(r, r), Bool.or(D.Node(y, m, D.Fd(3n, m, r), r), D.Node(z, m, D.Fd(4n, m, r), r)), CK.U.eq_refl(r))
    case Bk.Term.Efq{}:
      CK.U.eq_refl(r)
    case Bk.Term.Eql{y, z, w}:
      CK.Bo.or_il(U32.is_eq(r, r), Bool.or(D.Node(y, m, D.Fd(2n, m, r), r), Bool.or(D.Node(z, m, D.Fd(3n, m, r), r), D.Node(w, m, D.Fd(4n, m, r), r))), CK.U.eq_refl(r))
    case Bk.Term.Rfl{}:
      CK.U.eq_refl(r)
    case Bk.Term.Rwt{y, z, w}:
      CK.Bo.or_il(U32.is_eq(r, r), Bool.or(D.Node(y, m, D.Fd(2n, m, r), r), Bool.or(D.Node(z, m, D.Fd(3n, m, r), r), D.Node(w, m, D.Fd(4n, m, r), r))), CK.U.eq_refl(r))

# the parent is the root r, whose pointers by its tag's mask hold c
def par.here(+t: Bk.Term, +m: Cr.Cir.Cells, +ps: List<&2, U32>, +r: U32, +c: U32, +tg: U32, +mask: U32,
  etag: {D.TgW(D.Fd(0n, m, r)) == tg : U32}, hlt: {U32.is_lt(tg, 19) == True{} : Bool}, emask: {D.Fd(2n, m, U32.add(272, tg)) == mask : U32},
  hy: {D.Mem(D.Fs.term(mask, D.Fd(2n, m, r), D.Fd(3n, m, r), D.Fd(4n, m, r)), c) == True{} : Bool}) ->
  D.Ex(U32, g => D.P2({D.Node(t, m, r, g) == True{} : Bool}, {D.Mem(D.Fs(m, ps, g), c) == True{} : Bool})):
  (r, (node.root(t, m, r), D.hm.at(m, ps, r, tg, mask, c, etag, hlt, emask, hy)))

# the parent in a part y (at pr) is a parent in t
def par.up(-y: Bk.Term, -pr: U32, -t: Bk.Term, -m: Cr.Cir.Cells, -ps: List<&2, U32>, -r: U32, -c: U32,
  rec: D.Ex(U32, g => D.P2({D.Node(y, m, pr, g) == True{} : Bool}, {D.Mem(D.Fs(m, ps, g), c) == True{} : Bool})),
  lift: @g: U32 -> {D.Node(y, m, pr, g) == True{} : Bool} -> {D.Node(t, m, r, g) == True{} : Bool}) ->
  D.Ex(U32, g => D.P2({D.Node(t, m, r, g) == True{} : Bool}, {D.Mem(D.Fs(m, ps, g), c) == True{} : Bool})):
  (+g, rr) = rec
  (hg, hm) = rr
  (g, (lift(g, hg), hm))

# a node c of the term t at r stands for a term, no larger than t
def node.sub(t: Bk.Term, +dk: Bool, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +r: U32, +c: U32, +h: D.IsK(dk, ds, m, im, fi, nx, ks, img, r, t),
  hn: {D.Node(t, m, r, c) == True{} : Bool}) ->
  D.Ex(Bk.Term, v => D.P2(D.IsK(dk, ds, m, im, fi, nx, ks, img, c, v), N.Le(Pg.Term.size(v), Pg.Term.size(t)))):
  match t:
    case Bk.Term.Var{+i}:
      sub.root(Bk.Term.Var{i}, dk, ds, m, im, fi, nx, ks, img, r, c, h, CK.U.eq(r, c, hn))
    case Bk.Term.Ref{+k}:
      sub.root(Bk.Term.Ref{k}, dk, ds, m, im, fi, nx, ks, img, r, c, h, CK.U.eq(r, c, hn))
    case Bk.Term.Ann{+y, +z}:
      (+nd, w0) = h
      (py, pz) = w0
      (sy, hy) = py
      (sz, hz) = pz
      or3.case(U32.is_eq(r, c), D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c), D.Ex(Bk.Term, v => D.P2(D.IsK(dk, ds, m, im, fi, nx, ks, img, c, v), N.Le(Pg.Term.size(v), Pg.Term.size(Bk.Term.Ann{y, z})))), hn,
        e => sub.root(Bk.Term.Ann{y, z}, dk, ds, m, im, fi, nx, ks, img, r, c, h, CK.U.eq(r, c, e)),
        e => sub.up(y, Bk.Term.Ann{y, z}, dk, ds, m, im, fi, nx, ks, img, c, node.sub(y, dk, ds, m, im, fi, nx, ks, img, D.Fd(2n, m, r), c, hy, e), N.le_succ(Pg.Term.size(y), Nat.add(Pg.Term.size(y), Pg.Term.size(z)), N.le_add_r(Pg.Term.size(y), Pg.Term.size(z)))),
        e => sub.up(z, Bk.Term.Ann{y, z}, dk, ds, m, im, fi, nx, ks, img, c, node.sub(z, dk, ds, m, im, fi, nx, ks, img, D.Fd(3n, m, r), c, hz, e), N.le_succ(Pg.Term.size(z), Nat.add(Pg.Term.size(y), Pg.Term.size(z)), N.le_add_l(Pg.Term.size(y), Pg.Term.size(z)))))
    case Bk.Term.Let{+q, +y, +z}:
      (+nd, w0) = h
      (hq, w2) = w0
      (py, pz) = w2
      (sy, hy) = py
      (sz, hz) = pz
      or3.case(U32.is_eq(r, c), D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c), D.Ex(Bk.Term, v => D.P2(D.IsK(dk, ds, m, im, fi, nx, ks, img, c, v), N.Le(Pg.Term.size(v), Pg.Term.size(Bk.Term.Let{q, y, z})))), hn,
        e => sub.root(Bk.Term.Let{q, y, z}, dk, ds, m, im, fi, nx, ks, img, r, c, h, CK.U.eq(r, c, e)),
        e => sub.up(y, Bk.Term.Let{q, y, z}, dk, ds, m, im, fi, nx, ks, img, c, node.sub(y, dk, ds, m, im, fi, nx, ks, img, D.Fd(2n, m, r), c, hy, e), N.le_succ(Pg.Term.size(y), Nat.add(Pg.Term.size(y), Pg.Term.size(z)), N.le_add_r(Pg.Term.size(y), Pg.Term.size(z)))),
        e => sub.up(z, Bk.Term.Let{q, y, z}, dk, ds, m, im, fi, nx, ks, img, c, node.sub(z, dk, ds, m, im, fi, nx, ks, img, D.Fd(3n, m, r), c, hz, e), N.le_succ(Pg.Term.size(z), Nat.add(Pg.Term.size(y), Pg.Term.size(z)), N.le_add_l(Pg.Term.size(y), Pg.Term.size(z)))))
    case Bk.Term.Typ{+y}:
      (+nd, w0) = h
      (sy, hy) = w0
      D.or.cases(U32.is_eq(r, c), D.Node(y, m, D.Fd(2n, m, r), c), D.Ex(Bk.Term, v => D.P2(D.IsK(dk, ds, m, im, fi, nx, ks, img, c, v), N.Le(Pg.Term.size(v), Pg.Term.size(Bk.Term.Typ{y})))), hn,
        e => sub.root(Bk.Term.Typ{y}, dk, ds, m, im, fi, nx, ks, img, r, c, h, CK.U.eq(r, c, e)),
        e => sub.up(y, Bk.Term.Typ{y}, dk, ds, m, im, fi, nx, ks, img, c, node.sub(y, dk, ds, m, im, fi, nx, ks, img, D.Fd(2n, m, r), c, hy, e), N.le_succ(Pg.Term.size(y), Pg.Term.size(y), N.le_refl(Pg.Term.size(y)))))
    case Bk.Term.Min{+y, +z}:
      (+nd, w0) = h
      (py, pz) = w0
      (sy, hy) = py
      (sz, hz) = pz
      or3.case(U32.is_eq(r, c), D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c), D.Ex(Bk.Term, v => D.P2(D.IsK(dk, ds, m, im, fi, nx, ks, img, c, v), N.Le(Pg.Term.size(v), Pg.Term.size(Bk.Term.Min{y, z})))), hn,
        e => sub.root(Bk.Term.Min{y, z}, dk, ds, m, im, fi, nx, ks, img, r, c, h, CK.U.eq(r, c, e)),
        e => sub.up(y, Bk.Term.Min{y, z}, dk, ds, m, im, fi, nx, ks, img, c, node.sub(y, dk, ds, m, im, fi, nx, ks, img, D.Fd(2n, m, r), c, hy, e), N.le_succ(Pg.Term.size(y), Nat.add(Pg.Term.size(y), Pg.Term.size(z)), N.le_add_r(Pg.Term.size(y), Pg.Term.size(z)))),
        e => sub.up(z, Bk.Term.Min{y, z}, dk, ds, m, im, fi, nx, ks, img, c, node.sub(z, dk, ds, m, im, fi, nx, ks, img, D.Fd(3n, m, r), c, hz, e), N.le_succ(Pg.Term.size(z), Nat.add(Pg.Term.size(y), Pg.Term.size(z)), N.le_add_l(Pg.Term.size(y), Pg.Term.size(z)))))
    case Bk.Term.All{+q, +y, +z}:
      (+nd, w0) = h
      (hq, w2) = w0
      (py, pz) = w2
      (sy, hy) = py
      (sz, hz) = pz
      or3.case(U32.is_eq(r, c), D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c), D.Ex(Bk.Term, v => D.P2(D.IsK(dk, ds, m, im, fi, nx, ks, img, c, v), N.Le(Pg.Term.size(v), Pg.Term.size(Bk.Term.All{q, y, z})))), hn,
        e => sub.root(Bk.Term.All{q, y, z}, dk, ds, m, im, fi, nx, ks, img, r, c, h, CK.U.eq(r, c, e)),
        e => sub.up(y, Bk.Term.All{q, y, z}, dk, ds, m, im, fi, nx, ks, img, c, node.sub(y, dk, ds, m, im, fi, nx, ks, img, D.Fd(2n, m, r), c, hy, e), N.le_succ(Pg.Term.size(y), Nat.add(Pg.Term.size(y), Pg.Term.size(z)), N.le_add_r(Pg.Term.size(y), Pg.Term.size(z)))),
        e => sub.up(z, Bk.Term.All{q, y, z}, dk, ds, m, im, fi, nx, ks, img, c, node.sub(z, dk, ds, m, im, fi, nx, ks, img, D.Fd(3n, m, r), c, hz, e), N.le_succ(Pg.Term.size(z), Nat.add(Pg.Term.size(y), Pg.Term.size(z)), N.le_add_l(Pg.Term.size(y), Pg.Term.size(z)))))
    case Bk.Term.Lam{+q, +y}:
      (+nd, w0) = h
      (hq, w2) = w0
      (sy, hy) = w2
      D.or.cases(U32.is_eq(r, c), D.Node(y, m, D.Fd(2n, m, r), c), D.Ex(Bk.Term, v => D.P2(D.IsK(dk, ds, m, im, fi, nx, ks, img, c, v), N.Le(Pg.Term.size(v), Pg.Term.size(Bk.Term.Lam{q, y})))), hn,
        e => sub.root(Bk.Term.Lam{q, y}, dk, ds, m, im, fi, nx, ks, img, r, c, h, CK.U.eq(r, c, e)),
        e => sub.up(y, Bk.Term.Lam{q, y}, dk, ds, m, im, fi, nx, ks, img, c, node.sub(y, dk, ds, m, im, fi, nx, ks, img, D.Fd(2n, m, r), c, hy, e), N.le_succ(Pg.Term.size(y), Pg.Term.size(y), N.le_refl(Pg.Term.size(y)))))
    case Bk.Term.App{+q, +y, +z}:
      (+nd, w0) = h
      (hq, w2) = w0
      (py, pz) = w2
      (sy, hy) = py
      (sz, hz) = pz
      or3.case(U32.is_eq(r, c), D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c), D.Ex(Bk.Term, v => D.P2(D.IsK(dk, ds, m, im, fi, nx, ks, img, c, v), N.Le(Pg.Term.size(v), Pg.Term.size(Bk.Term.App{q, y, z})))), hn,
        e => sub.root(Bk.Term.App{q, y, z}, dk, ds, m, im, fi, nx, ks, img, r, c, h, CK.U.eq(r, c, e)),
        e => sub.up(y, Bk.Term.App{q, y, z}, dk, ds, m, im, fi, nx, ks, img, c, node.sub(y, dk, ds, m, im, fi, nx, ks, img, D.Fd(2n, m, r), c, hy, e), N.le_succ(Pg.Term.size(y), Nat.add(Pg.Term.size(y), Pg.Term.size(z)), N.le_add_r(Pg.Term.size(y), Pg.Term.size(z)))),
        e => sub.up(z, Bk.Term.App{q, y, z}, dk, ds, m, im, fi, nx, ks, img, c, node.sub(z, dk, ds, m, im, fi, nx, ks, img, D.Fd(3n, m, r), c, hz, e), N.le_succ(Pg.Term.size(z), Nat.add(Pg.Term.size(y), Pg.Term.size(z)), N.le_add_l(Pg.Term.size(y), Pg.Term.size(z)))))
    case Bk.Term.Sig{+q, +y, +z}:
      (+nd, w0) = h
      (hq, w2) = w0
      (py, pz) = w2
      (sy, hy) = py
      (sz, hz) = pz
      or3.case(U32.is_eq(r, c), D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c), D.Ex(Bk.Term, v => D.P2(D.IsK(dk, ds, m, im, fi, nx, ks, img, c, v), N.Le(Pg.Term.size(v), Pg.Term.size(Bk.Term.Sig{q, y, z})))), hn,
        e => sub.root(Bk.Term.Sig{q, y, z}, dk, ds, m, im, fi, nx, ks, img, r, c, h, CK.U.eq(r, c, e)),
        e => sub.up(y, Bk.Term.Sig{q, y, z}, dk, ds, m, im, fi, nx, ks, img, c, node.sub(y, dk, ds, m, im, fi, nx, ks, img, D.Fd(2n, m, r), c, hy, e), N.le_succ(Pg.Term.size(y), Nat.add(Pg.Term.size(y), Pg.Term.size(z)), N.le_add_r(Pg.Term.size(y), Pg.Term.size(z)))),
        e => sub.up(z, Bk.Term.Sig{q, y, z}, dk, ds, m, im, fi, nx, ks, img, c, node.sub(z, dk, ds, m, im, fi, nx, ks, img, D.Fd(3n, m, r), c, hz, e), N.le_succ(Pg.Term.size(z), Nat.add(Pg.Term.size(y), Pg.Term.size(z)), N.le_add_l(Pg.Term.size(y), Pg.Term.size(z)))))
    case Bk.Term.Tup{+q, +y, +z}:
      (+nd, w0) = h
      (hq, w2) = w0
      (py, pz) = w2
      (sy, hy) = py
      (sz, hz) = pz
      or3.case(U32.is_eq(r, c), D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c), D.Ex(Bk.Term, v => D.P2(D.IsK(dk, ds, m, im, fi, nx, ks, img, c, v), N.Le(Pg.Term.size(v), Pg.Term.size(Bk.Term.Tup{q, y, z})))), hn,
        e => sub.root(Bk.Term.Tup{q, y, z}, dk, ds, m, im, fi, nx, ks, img, r, c, h, CK.U.eq(r, c, e)),
        e => sub.up(y, Bk.Term.Tup{q, y, z}, dk, ds, m, im, fi, nx, ks, img, c, node.sub(y, dk, ds, m, im, fi, nx, ks, img, D.Fd(2n, m, r), c, hy, e), N.le_succ(Pg.Term.size(y), Nat.add(Pg.Term.size(y), Pg.Term.size(z)), N.le_add_r(Pg.Term.size(y), Pg.Term.size(z)))),
        e => sub.up(z, Bk.Term.Tup{q, y, z}, dk, ds, m, im, fi, nx, ks, img, c, node.sub(z, dk, ds, m, im, fi, nx, ks, img, D.Fd(3n, m, r), c, hz, e), N.le_succ(Pg.Term.size(z), Nat.add(Pg.Term.size(y), Pg.Term.size(z)), N.le_add_l(Pg.Term.size(y), Pg.Term.size(z)))))
    case Bk.Term.Prj{+y}:
      (+nd, w0) = h
      (sy, hy) = w0
      D.or.cases(U32.is_eq(r, c), D.Node(y, m, D.Fd(2n, m, r), c), D.Ex(Bk.Term, v => D.P2(D.IsK(dk, ds, m, im, fi, nx, ks, img, c, v), N.Le(Pg.Term.size(v), Pg.Term.size(Bk.Term.Prj{y})))), hn,
        e => sub.root(Bk.Term.Prj{y}, dk, ds, m, im, fi, nx, ks, img, r, c, h, CK.U.eq(r, c, e)),
        e => sub.up(y, Bk.Term.Prj{y}, dk, ds, m, im, fi, nx, ks, img, c, node.sub(y, dk, ds, m, im, fi, nx, ks, img, D.Fd(2n, m, r), c, hy, e), N.le_succ(Pg.Term.size(y), Pg.Term.size(y), N.le_refl(Pg.Term.size(y)))))
    case Bk.Term.Enu{+e}:
      sub.root(Bk.Term.Enu{e}, dk, ds, m, im, fi, nx, ks, img, r, c, h, CK.U.eq(r, c, hn))
    case Bk.Term.Lab{+k}:
      sub.root(Bk.Term.Lab{k}, dk, ds, m, im, fi, nx, ks, img, r, c, h, CK.U.eq(r, c, hn))
    case Bk.Term.Mat{+k, +y, +z}:
      (+nd, w0) = h
      (nm, w2) = w0
      (py, pz) = w2
      (sy, hy) = py
      (sz, hz) = pz
      or3.case(U32.is_eq(r, c), D.Node(y, m, D.Fd(3n, m, r), c), D.Node(z, m, D.Fd(4n, m, r), c), D.Ex(Bk.Term, v => D.P2(D.IsK(dk, ds, m, im, fi, nx, ks, img, c, v), N.Le(Pg.Term.size(v), Pg.Term.size(Bk.Term.Mat{k, y, z})))), hn,
        e => sub.root(Bk.Term.Mat{k, y, z}, dk, ds, m, im, fi, nx, ks, img, r, c, h, CK.U.eq(r, c, e)),
        e => sub.up(y, Bk.Term.Mat{k, y, z}, dk, ds, m, im, fi, nx, ks, img, c, node.sub(y, dk, ds, m, im, fi, nx, ks, img, D.Fd(3n, m, r), c, hy, e), N.le_succ(Pg.Term.size(y), Nat.add(Pg.Term.size(y), Pg.Term.size(z)), N.le_add_r(Pg.Term.size(y), Pg.Term.size(z)))),
        e => sub.up(z, Bk.Term.Mat{k, y, z}, dk, ds, m, im, fi, nx, ks, img, c, node.sub(z, dk, ds, m, im, fi, nx, ks, img, D.Fd(4n, m, r), c, hz, e), N.le_succ(Pg.Term.size(z), Nat.add(Pg.Term.size(y), Pg.Term.size(z)), N.le_add_l(Pg.Term.size(y), Pg.Term.size(z)))))
    case Bk.Term.Efq{}:
      sub.root(Bk.Term.Efq{}, dk, ds, m, im, fi, nx, ks, img, r, c, h, CK.U.eq(r, c, hn))
    case Bk.Term.Eql{+y, +z, +w}:
      (+nd, w0) = h
      (py, w2) = w0
      (sy, hy) = py
      (pz, pw) = w2
      (sz, hz) = pz
      (sw, hw) = pw
      or4.case(U32.is_eq(r, c), D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c), D.Node(w, m, D.Fd(4n, m, r), c), D.Ex(Bk.Term, v => D.P2(D.IsK(dk, ds, m, im, fi, nx, ks, img, c, v), N.Le(Pg.Term.size(v), Pg.Term.size(Bk.Term.Eql{y, z, w})))), hn,
        e => sub.root(Bk.Term.Eql{y, z, w}, dk, ds, m, im, fi, nx, ks, img, r, c, h, CK.U.eq(r, c, e)),
        e => sub.up(y, Bk.Term.Eql{y, z, w}, dk, ds, m, im, fi, nx, ks, img, c, node.sub(y, dk, ds, m, im, fi, nx, ks, img, D.Fd(2n, m, r), c, hy, e), N.le_succ(Pg.Term.size(y), Nat.add(Pg.Term.size(y), Nat.add(Pg.Term.size(z), Pg.Term.size(w))), N.le_add_r(Pg.Term.size(y), Nat.add(Pg.Term.size(z), Pg.Term.size(w))))),
        e => sub.up(z, Bk.Term.Eql{y, z, w}, dk, ds, m, im, fi, nx, ks, img, c, node.sub(z, dk, ds, m, im, fi, nx, ks, img, D.Fd(3n, m, r), c, hz, e), N.le_succ(Pg.Term.size(z), Nat.add(Pg.Term.size(y), Nat.add(Pg.Term.size(z), Pg.Term.size(w))), N.le_trans(Pg.Term.size(z), Nat.add(Pg.Term.size(z), Pg.Term.size(w)), Nat.add(Pg.Term.size(y), Nat.add(Pg.Term.size(z), Pg.Term.size(w))), N.le_add_r(Pg.Term.size(z), Pg.Term.size(w)), N.le_add_l(Pg.Term.size(y), Nat.add(Pg.Term.size(z), Pg.Term.size(w)))))),
        e => sub.up(w, Bk.Term.Eql{y, z, w}, dk, ds, m, im, fi, nx, ks, img, c, node.sub(w, dk, ds, m, im, fi, nx, ks, img, D.Fd(4n, m, r), c, hw, e), N.le_succ(Pg.Term.size(w), Nat.add(Pg.Term.size(y), Nat.add(Pg.Term.size(z), Pg.Term.size(w))), N.le_trans(Pg.Term.size(w), Nat.add(Pg.Term.size(z), Pg.Term.size(w)), Nat.add(Pg.Term.size(y), Nat.add(Pg.Term.size(z), Pg.Term.size(w))), N.le_add_l(Pg.Term.size(z), Pg.Term.size(w)), N.le_add_l(Pg.Term.size(y), Nat.add(Pg.Term.size(z), Pg.Term.size(w)))))))
    case Bk.Term.Rfl{}:
      sub.root(Bk.Term.Rfl{}, dk, ds, m, im, fi, nx, ks, img, r, c, h, CK.U.eq(r, c, hn))
    case Bk.Term.Rwt{+y, +z, +w}:
      (+nd, w0) = h
      (py, w2) = w0
      (sy, hy) = py
      (pz, pw) = w2
      (sz, hz) = pz
      (sw, hw) = pw
      or4.case(U32.is_eq(r, c), D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c), D.Node(w, m, D.Fd(4n, m, r), c), D.Ex(Bk.Term, v => D.P2(D.IsK(dk, ds, m, im, fi, nx, ks, img, c, v), N.Le(Pg.Term.size(v), Pg.Term.size(Bk.Term.Rwt{y, z, w})))), hn,
        e => sub.root(Bk.Term.Rwt{y, z, w}, dk, ds, m, im, fi, nx, ks, img, r, c, h, CK.U.eq(r, c, e)),
        e => sub.up(y, Bk.Term.Rwt{y, z, w}, dk, ds, m, im, fi, nx, ks, img, c, node.sub(y, dk, ds, m, im, fi, nx, ks, img, D.Fd(2n, m, r), c, hy, e), N.le_succ(Pg.Term.size(y), Nat.add(Pg.Term.size(y), Nat.add(Pg.Term.size(z), Pg.Term.size(w))), N.le_add_r(Pg.Term.size(y), Nat.add(Pg.Term.size(z), Pg.Term.size(w))))),
        e => sub.up(z, Bk.Term.Rwt{y, z, w}, dk, ds, m, im, fi, nx, ks, img, c, node.sub(z, dk, ds, m, im, fi, nx, ks, img, D.Fd(3n, m, r), c, hz, e), N.le_succ(Pg.Term.size(z), Nat.add(Pg.Term.size(y), Nat.add(Pg.Term.size(z), Pg.Term.size(w))), N.le_trans(Pg.Term.size(z), Nat.add(Pg.Term.size(z), Pg.Term.size(w)), Nat.add(Pg.Term.size(y), Nat.add(Pg.Term.size(z), Pg.Term.size(w))), N.le_add_r(Pg.Term.size(z), Pg.Term.size(w)), N.le_add_l(Pg.Term.size(y), Nat.add(Pg.Term.size(z), Pg.Term.size(w)))))),
        e => sub.up(w, Bk.Term.Rwt{y, z, w}, dk, ds, m, im, fi, nx, ks, img, c, node.sub(w, dk, ds, m, im, fi, nx, ks, img, D.Fd(4n, m, r), c, hw, e), N.le_succ(Pg.Term.size(w), Nat.add(Pg.Term.size(y), Nat.add(Pg.Term.size(z), Pg.Term.size(w))), N.le_trans(Pg.Term.size(w), Nat.add(Pg.Term.size(z), Pg.Term.size(w)), Nat.add(Pg.Term.size(y), Nat.add(Pg.Term.size(z), Pg.Term.size(w))), N.le_add_l(Pg.Term.size(z), Pg.Term.size(w)), N.le_add_l(Pg.Term.size(y), Nat.add(Pg.Term.size(z), Pg.Term.size(w)))))))

# a node c of the term t at r, other than r, has a parent: a node of t whose pointers hold c
def node.par(t: Bk.Term, +dk: Bool, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +tbl: D.Tbl(m, im, fi, nx), +r: U32, +c: U32,
  h: D.IsK(dk, ds, m, im, fi, nx, ks, img, r, t), hn: {D.Node(t, m, r, c) == True{} : Bool}, +hne: {U32.is_eq(r, c) == False{} : Bool}) ->
  D.Ex(U32, g => D.P2({D.Node(t, m, r, g) == True{} : Bool}, {D.Mem(D.Fs(m, ps, g), c) == True{} : Bool})):
  match t:
    case Bk.Term.Var{+i}:
      CK.Bo.tf(D.Ex(U32, g => D.P2({D.Node(Bk.Term.Var{i}, m, r, g) == True{} : Bool}, {D.Mem(D.Fs(m, ps, g), c) == True{} : Bool})), Equal.trans(Bool, False{}, U32.is_eq(r, c), True{}, Equal.sym(Bool, U32.is_eq(r, c), False{}, hne), hn))
    case Bk.Term.Ref{+k}:
      CK.Bo.tf(D.Ex(U32, g => D.P2({D.Node(Bk.Term.Ref{k}, m, r, g) == True{} : Bool}, {D.Mem(D.Fs(m, ps, g), c) == True{} : Bool})), Equal.trans(Bool, False{}, U32.is_eq(r, c), True{}, Equal.sym(Bool, U32.is_eq(r, c), False{}, hne), hn))
    case Bk.Term.Ann{+y, +z}:
      (+nd, w0) = h
      (py, pz) = w0
      (sy, hy) = py
      (sz, hz) = pz
      D.or.cases(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Ann{y, z}, m, r, g) == True{} : Bool}, {D.Mem(D.Fs(m, ps, g), c) == True{} : Bool})), or.drop(U32.is_eq(r, c), Bool.or(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c)), hn, hne),
        e => bool.case(U32.is_eq(D.Fd(2n, m, r), c), U32.is_eq(D.Fd(2n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Ann{y, z}, m, r, g) == True{} : Bool}, {D.Mem(D.Fs(m, ps, g), c) == True{} : Bool})), {==},
          eb => par.here(Bk.Term.Ann{y, z}, m, ps, r, c, 2, 3, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Ann{y, z}, 2, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Ann{y, z}, tbl), CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, r), c), Bool.or(U32.is_eq(D.Fd(3n, m, r), c), False{}), eb)),
          eb => par.up(y, D.Fd(2n, m, r), Bk.Term.Ann{y, z}, m, ps, r, c, node.par(y, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(2n, m, r), c, hy, e, eb), +g => hg => in.l(U32.is_eq(r, g), D.Node(y, m, D.Fd(2n, m, r), g), D.Node(z, m, D.Fd(3n, m, r), g), hg))),
        e => bool.case(U32.is_eq(D.Fd(3n, m, r), c), U32.is_eq(D.Fd(3n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Ann{y, z}, m, r, g) == True{} : Bool}, {D.Mem(D.Fs(m, ps, g), c) == True{} : Bool})), {==},
          eb => par.here(Bk.Term.Ann{y, z}, m, ps, r, c, 2, 3, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Ann{y, z}, 2, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Ann{y, z}, tbl), CK.Bo.or_ir(U32.is_eq(D.Fd(2n, m, r), c), Bool.or(U32.is_eq(D.Fd(3n, m, r), c), False{}), CK.Bo.or_il(U32.is_eq(D.Fd(3n, m, r), c), False{}, eb))),
          eb => par.up(z, D.Fd(3n, m, r), Bk.Term.Ann{y, z}, m, ps, r, c, node.par(z, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(3n, m, r), c, hz, e, eb), +g => hg => in.r(U32.is_eq(r, g), D.Node(y, m, D.Fd(2n, m, r), g), D.Node(z, m, D.Fd(3n, m, r), g), hg))))
    case Bk.Term.Let{+q, +y, +z}:
      (+nd, w0) = h
      (hq, w2) = w0
      (py, pz) = w2
      (sy, hy) = py
      (sz, hz) = pz
      D.or.cases(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Let{q, y, z}, m, r, g) == True{} : Bool}, {D.Mem(D.Fs(m, ps, g), c) == True{} : Bool})), or.drop(U32.is_eq(r, c), Bool.or(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c)), hn, hne),
        e => bool.case(U32.is_eq(D.Fd(2n, m, r), c), U32.is_eq(D.Fd(2n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Let{q, y, z}, m, r, g) == True{} : Bool}, {D.Mem(D.Fs(m, ps, g), c) == True{} : Bool})), {==},
          eb => par.here(Bk.Term.Let{q, y, z}, m, ps, r, c, 3, 3, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Let{q, y, z}, 3, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Let{q, y, z}, tbl), CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, r), c), Bool.or(U32.is_eq(D.Fd(3n, m, r), c), False{}), eb)),
          eb => par.up(y, D.Fd(2n, m, r), Bk.Term.Let{q, y, z}, m, ps, r, c, node.par(y, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(2n, m, r), c, hy, e, eb), +g => hg => in.l(U32.is_eq(r, g), D.Node(y, m, D.Fd(2n, m, r), g), D.Node(z, m, D.Fd(3n, m, r), g), hg))),
        e => bool.case(U32.is_eq(D.Fd(3n, m, r), c), U32.is_eq(D.Fd(3n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Let{q, y, z}, m, r, g) == True{} : Bool}, {D.Mem(D.Fs(m, ps, g), c) == True{} : Bool})), {==},
          eb => par.here(Bk.Term.Let{q, y, z}, m, ps, r, c, 3, 3, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Let{q, y, z}, 3, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Let{q, y, z}, tbl), CK.Bo.or_ir(U32.is_eq(D.Fd(2n, m, r), c), Bool.or(U32.is_eq(D.Fd(3n, m, r), c), False{}), CK.Bo.or_il(U32.is_eq(D.Fd(3n, m, r), c), False{}, eb))),
          eb => par.up(z, D.Fd(3n, m, r), Bk.Term.Let{q, y, z}, m, ps, r, c, node.par(z, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(3n, m, r), c, hz, e, eb), +g => hg => in.r(U32.is_eq(r, g), D.Node(y, m, D.Fd(2n, m, r), g), D.Node(z, m, D.Fd(3n, m, r), g), hg))))
    case Bk.Term.Typ{+y}:
      (+nd, w0) = h
      (sy, hy) = w0
      par.one(D.Node(y, m, D.Fd(2n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Typ{y}, m, r, g) == True{} : Bool}, {D.Mem(D.Fs(m, ps, g), c) == True{} : Bool})), or.drop(U32.is_eq(r, c), D.Node(y, m, D.Fd(2n, m, r), c), hn, hne),
        e => bool.case(U32.is_eq(D.Fd(2n, m, r), c), U32.is_eq(D.Fd(2n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Typ{y}, m, r, g) == True{} : Bool}, {D.Mem(D.Fs(m, ps, g), c) == True{} : Bool})), {==},
          eb => par.here(Bk.Term.Typ{y}, m, ps, r, c, 4, 1, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Typ{y}, 4, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Typ{y}, tbl), CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, r), c), False{}, eb)),
          eb => par.up(y, D.Fd(2n, m, r), Bk.Term.Typ{y}, m, ps, r, c, node.par(y, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(2n, m, r), c, hy, e, eb), +g => hg => CK.Bo.or_ir(U32.is_eq(r, g), D.Node(y, m, D.Fd(2n, m, r), g), hg))))
    case Bk.Term.Min{+y, +z}:
      (+nd, w0) = h
      (py, pz) = w0
      (sy, hy) = py
      (sz, hz) = pz
      D.or.cases(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Min{y, z}, m, r, g) == True{} : Bool}, {D.Mem(D.Fs(m, ps, g), c) == True{} : Bool})), or.drop(U32.is_eq(r, c), Bool.or(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c)), hn, hne),
        e => bool.case(U32.is_eq(D.Fd(2n, m, r), c), U32.is_eq(D.Fd(2n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Min{y, z}, m, r, g) == True{} : Bool}, {D.Mem(D.Fs(m, ps, g), c) == True{} : Bool})), {==},
          eb => par.here(Bk.Term.Min{y, z}, m, ps, r, c, 5, 3, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Min{y, z}, 5, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Min{y, z}, tbl), CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, r), c), Bool.or(U32.is_eq(D.Fd(3n, m, r), c), False{}), eb)),
          eb => par.up(y, D.Fd(2n, m, r), Bk.Term.Min{y, z}, m, ps, r, c, node.par(y, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(2n, m, r), c, hy, e, eb), +g => hg => in.l(U32.is_eq(r, g), D.Node(y, m, D.Fd(2n, m, r), g), D.Node(z, m, D.Fd(3n, m, r), g), hg))),
        e => bool.case(U32.is_eq(D.Fd(3n, m, r), c), U32.is_eq(D.Fd(3n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Min{y, z}, m, r, g) == True{} : Bool}, {D.Mem(D.Fs(m, ps, g), c) == True{} : Bool})), {==},
          eb => par.here(Bk.Term.Min{y, z}, m, ps, r, c, 5, 3, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Min{y, z}, 5, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Min{y, z}, tbl), CK.Bo.or_ir(U32.is_eq(D.Fd(2n, m, r), c), Bool.or(U32.is_eq(D.Fd(3n, m, r), c), False{}), CK.Bo.or_il(U32.is_eq(D.Fd(3n, m, r), c), False{}, eb))),
          eb => par.up(z, D.Fd(3n, m, r), Bk.Term.Min{y, z}, m, ps, r, c, node.par(z, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(3n, m, r), c, hz, e, eb), +g => hg => in.r(U32.is_eq(r, g), D.Node(y, m, D.Fd(2n, m, r), g), D.Node(z, m, D.Fd(3n, m, r), g), hg))))
    case Bk.Term.All{+q, +y, +z}:
      (+nd, w0) = h
      (hq, w2) = w0
      (py, pz) = w2
      (sy, hy) = py
      (sz, hz) = pz
      D.or.cases(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.All{q, y, z}, m, r, g) == True{} : Bool}, {D.Mem(D.Fs(m, ps, g), c) == True{} : Bool})), or.drop(U32.is_eq(r, c), Bool.or(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c)), hn, hne),
        e => bool.case(U32.is_eq(D.Fd(2n, m, r), c), U32.is_eq(D.Fd(2n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.All{q, y, z}, m, r, g) == True{} : Bool}, {D.Mem(D.Fs(m, ps, g), c) == True{} : Bool})), {==},
          eb => par.here(Bk.Term.All{q, y, z}, m, ps, r, c, 6, 3, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.All{q, y, z}, 6, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.All{q, y, z}, tbl), CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, r), c), Bool.or(U32.is_eq(D.Fd(3n, m, r), c), False{}), eb)),
          eb => par.up(y, D.Fd(2n, m, r), Bk.Term.All{q, y, z}, m, ps, r, c, node.par(y, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(2n, m, r), c, hy, e, eb), +g => hg => in.l(U32.is_eq(r, g), D.Node(y, m, D.Fd(2n, m, r), g), D.Node(z, m, D.Fd(3n, m, r), g), hg))),
        e => bool.case(U32.is_eq(D.Fd(3n, m, r), c), U32.is_eq(D.Fd(3n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.All{q, y, z}, m, r, g) == True{} : Bool}, {D.Mem(D.Fs(m, ps, g), c) == True{} : Bool})), {==},
          eb => par.here(Bk.Term.All{q, y, z}, m, ps, r, c, 6, 3, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.All{q, y, z}, 6, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.All{q, y, z}, tbl), CK.Bo.or_ir(U32.is_eq(D.Fd(2n, m, r), c), Bool.or(U32.is_eq(D.Fd(3n, m, r), c), False{}), CK.Bo.or_il(U32.is_eq(D.Fd(3n, m, r), c), False{}, eb))),
          eb => par.up(z, D.Fd(3n, m, r), Bk.Term.All{q, y, z}, m, ps, r, c, node.par(z, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(3n, m, r), c, hz, e, eb), +g => hg => in.r(U32.is_eq(r, g), D.Node(y, m, D.Fd(2n, m, r), g), D.Node(z, m, D.Fd(3n, m, r), g), hg))))
    case Bk.Term.Lam{+q, +y}:
      (+nd, w0) = h
      (hq, w2) = w0
      (sy, hy) = w2
      par.one(D.Node(y, m, D.Fd(2n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Lam{q, y}, m, r, g) == True{} : Bool}, {D.Mem(D.Fs(m, ps, g), c) == True{} : Bool})), or.drop(U32.is_eq(r, c), D.Node(y, m, D.Fd(2n, m, r), c), hn, hne),
        e => bool.case(U32.is_eq(D.Fd(2n, m, r), c), U32.is_eq(D.Fd(2n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Lam{q, y}, m, r, g) == True{} : Bool}, {D.Mem(D.Fs(m, ps, g), c) == True{} : Bool})), {==},
          eb => par.here(Bk.Term.Lam{q, y}, m, ps, r, c, 7, 1, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Lam{q, y}, 7, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Lam{q, y}, tbl), CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, r), c), False{}, eb)),
          eb => par.up(y, D.Fd(2n, m, r), Bk.Term.Lam{q, y}, m, ps, r, c, node.par(y, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(2n, m, r), c, hy, e, eb), +g => hg => CK.Bo.or_ir(U32.is_eq(r, g), D.Node(y, m, D.Fd(2n, m, r), g), hg))))
    case Bk.Term.App{+q, +y, +z}:
      (+nd, w0) = h
      (hq, w2) = w0
      (py, pz) = w2
      (sy, hy) = py
      (sz, hz) = pz
      D.or.cases(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.App{q, y, z}, m, r, g) == True{} : Bool}, {D.Mem(D.Fs(m, ps, g), c) == True{} : Bool})), or.drop(U32.is_eq(r, c), Bool.or(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c)), hn, hne),
        e => bool.case(U32.is_eq(D.Fd(2n, m, r), c), U32.is_eq(D.Fd(2n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.App{q, y, z}, m, r, g) == True{} : Bool}, {D.Mem(D.Fs(m, ps, g), c) == True{} : Bool})), {==},
          eb => par.here(Bk.Term.App{q, y, z}, m, ps, r, c, 8, 3, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.App{q, y, z}, 8, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.App{q, y, z}, tbl), CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, r), c), Bool.or(U32.is_eq(D.Fd(3n, m, r), c), False{}), eb)),
          eb => par.up(y, D.Fd(2n, m, r), Bk.Term.App{q, y, z}, m, ps, r, c, node.par(y, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(2n, m, r), c, hy, e, eb), +g => hg => in.l(U32.is_eq(r, g), D.Node(y, m, D.Fd(2n, m, r), g), D.Node(z, m, D.Fd(3n, m, r), g), hg))),
        e => bool.case(U32.is_eq(D.Fd(3n, m, r), c), U32.is_eq(D.Fd(3n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.App{q, y, z}, m, r, g) == True{} : Bool}, {D.Mem(D.Fs(m, ps, g), c) == True{} : Bool})), {==},
          eb => par.here(Bk.Term.App{q, y, z}, m, ps, r, c, 8, 3, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.App{q, y, z}, 8, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.App{q, y, z}, tbl), CK.Bo.or_ir(U32.is_eq(D.Fd(2n, m, r), c), Bool.or(U32.is_eq(D.Fd(3n, m, r), c), False{}), CK.Bo.or_il(U32.is_eq(D.Fd(3n, m, r), c), False{}, eb))),
          eb => par.up(z, D.Fd(3n, m, r), Bk.Term.App{q, y, z}, m, ps, r, c, node.par(z, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(3n, m, r), c, hz, e, eb), +g => hg => in.r(U32.is_eq(r, g), D.Node(y, m, D.Fd(2n, m, r), g), D.Node(z, m, D.Fd(3n, m, r), g), hg))))
    case Bk.Term.Sig{+q, +y, +z}:
      (+nd, w0) = h
      (hq, w2) = w0
      (py, pz) = w2
      (sy, hy) = py
      (sz, hz) = pz
      D.or.cases(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Sig{q, y, z}, m, r, g) == True{} : Bool}, {D.Mem(D.Fs(m, ps, g), c) == True{} : Bool})), or.drop(U32.is_eq(r, c), Bool.or(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c)), hn, hne),
        e => bool.case(U32.is_eq(D.Fd(2n, m, r), c), U32.is_eq(D.Fd(2n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Sig{q, y, z}, m, r, g) == True{} : Bool}, {D.Mem(D.Fs(m, ps, g), c) == True{} : Bool})), {==},
          eb => par.here(Bk.Term.Sig{q, y, z}, m, ps, r, c, 9, 3, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Sig{q, y, z}, 9, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Sig{q, y, z}, tbl), CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, r), c), Bool.or(U32.is_eq(D.Fd(3n, m, r), c), False{}), eb)),
          eb => par.up(y, D.Fd(2n, m, r), Bk.Term.Sig{q, y, z}, m, ps, r, c, node.par(y, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(2n, m, r), c, hy, e, eb), +g => hg => in.l(U32.is_eq(r, g), D.Node(y, m, D.Fd(2n, m, r), g), D.Node(z, m, D.Fd(3n, m, r), g), hg))),
        e => bool.case(U32.is_eq(D.Fd(3n, m, r), c), U32.is_eq(D.Fd(3n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Sig{q, y, z}, m, r, g) == True{} : Bool}, {D.Mem(D.Fs(m, ps, g), c) == True{} : Bool})), {==},
          eb => par.here(Bk.Term.Sig{q, y, z}, m, ps, r, c, 9, 3, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Sig{q, y, z}, 9, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Sig{q, y, z}, tbl), CK.Bo.or_ir(U32.is_eq(D.Fd(2n, m, r), c), Bool.or(U32.is_eq(D.Fd(3n, m, r), c), False{}), CK.Bo.or_il(U32.is_eq(D.Fd(3n, m, r), c), False{}, eb))),
          eb => par.up(z, D.Fd(3n, m, r), Bk.Term.Sig{q, y, z}, m, ps, r, c, node.par(z, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(3n, m, r), c, hz, e, eb), +g => hg => in.r(U32.is_eq(r, g), D.Node(y, m, D.Fd(2n, m, r), g), D.Node(z, m, D.Fd(3n, m, r), g), hg))))
    case Bk.Term.Tup{+q, +y, +z}:
      (+nd, w0) = h
      (hq, w2) = w0
      (py, pz) = w2
      (sy, hy) = py
      (sz, hz) = pz
      D.or.cases(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Tup{q, y, z}, m, r, g) == True{} : Bool}, {D.Mem(D.Fs(m, ps, g), c) == True{} : Bool})), or.drop(U32.is_eq(r, c), Bool.or(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c)), hn, hne),
        e => bool.case(U32.is_eq(D.Fd(2n, m, r), c), U32.is_eq(D.Fd(2n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Tup{q, y, z}, m, r, g) == True{} : Bool}, {D.Mem(D.Fs(m, ps, g), c) == True{} : Bool})), {==},
          eb => par.here(Bk.Term.Tup{q, y, z}, m, ps, r, c, 10, 3, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Tup{q, y, z}, 10, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Tup{q, y, z}, tbl), CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, r), c), Bool.or(U32.is_eq(D.Fd(3n, m, r), c), False{}), eb)),
          eb => par.up(y, D.Fd(2n, m, r), Bk.Term.Tup{q, y, z}, m, ps, r, c, node.par(y, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(2n, m, r), c, hy, e, eb), +g => hg => in.l(U32.is_eq(r, g), D.Node(y, m, D.Fd(2n, m, r), g), D.Node(z, m, D.Fd(3n, m, r), g), hg))),
        e => bool.case(U32.is_eq(D.Fd(3n, m, r), c), U32.is_eq(D.Fd(3n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Tup{q, y, z}, m, r, g) == True{} : Bool}, {D.Mem(D.Fs(m, ps, g), c) == True{} : Bool})), {==},
          eb => par.here(Bk.Term.Tup{q, y, z}, m, ps, r, c, 10, 3, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Tup{q, y, z}, 10, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Tup{q, y, z}, tbl), CK.Bo.or_ir(U32.is_eq(D.Fd(2n, m, r), c), Bool.or(U32.is_eq(D.Fd(3n, m, r), c), False{}), CK.Bo.or_il(U32.is_eq(D.Fd(3n, m, r), c), False{}, eb))),
          eb => par.up(z, D.Fd(3n, m, r), Bk.Term.Tup{q, y, z}, m, ps, r, c, node.par(z, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(3n, m, r), c, hz, e, eb), +g => hg => in.r(U32.is_eq(r, g), D.Node(y, m, D.Fd(2n, m, r), g), D.Node(z, m, D.Fd(3n, m, r), g), hg))))
    case Bk.Term.Prj{+y}:
      (+nd, w0) = h
      (sy, hy) = w0
      par.one(D.Node(y, m, D.Fd(2n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Prj{y}, m, r, g) == True{} : Bool}, {D.Mem(D.Fs(m, ps, g), c) == True{} : Bool})), or.drop(U32.is_eq(r, c), D.Node(y, m, D.Fd(2n, m, r), c), hn, hne),
        e => bool.case(U32.is_eq(D.Fd(2n, m, r), c), U32.is_eq(D.Fd(2n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Prj{y}, m, r, g) == True{} : Bool}, {D.Mem(D.Fs(m, ps, g), c) == True{} : Bool})), {==},
          eb => par.here(Bk.Term.Prj{y}, m, ps, r, c, 11, 1, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Prj{y}, 11, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Prj{y}, tbl), CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, r), c), False{}, eb)),
          eb => par.up(y, D.Fd(2n, m, r), Bk.Term.Prj{y}, m, ps, r, c, node.par(y, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(2n, m, r), c, hy, e, eb), +g => hg => CK.Bo.or_ir(U32.is_eq(r, g), D.Node(y, m, D.Fd(2n, m, r), g), hg))))
    case Bk.Term.Enu{+e}:
      CK.Bo.tf(D.Ex(U32, g => D.P2({D.Node(Bk.Term.Enu{e}, m, r, g) == True{} : Bool}, {D.Mem(D.Fs(m, ps, g), c) == True{} : Bool})), Equal.trans(Bool, False{}, U32.is_eq(r, c), True{}, Equal.sym(Bool, U32.is_eq(r, c), False{}, hne), hn))
    case Bk.Term.Lab{+k}:
      CK.Bo.tf(D.Ex(U32, g => D.P2({D.Node(Bk.Term.Lab{k}, m, r, g) == True{} : Bool}, {D.Mem(D.Fs(m, ps, g), c) == True{} : Bool})), Equal.trans(Bool, False{}, U32.is_eq(r, c), True{}, Equal.sym(Bool, U32.is_eq(r, c), False{}, hne), hn))
    case Bk.Term.Mat{+k, +y, +z}:
      (+nd, w0) = h
      (nm, w2) = w0
      (py, pz) = w2
      (sy, hy) = py
      (sz, hz) = pz
      D.or.cases(D.Node(y, m, D.Fd(3n, m, r), c), D.Node(z, m, D.Fd(4n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Mat{k, y, z}, m, r, g) == True{} : Bool}, {D.Mem(D.Fs(m, ps, g), c) == True{} : Bool})), or.drop(U32.is_eq(r, c), Bool.or(D.Node(y, m, D.Fd(3n, m, r), c), D.Node(z, m, D.Fd(4n, m, r), c)), hn, hne),
        e => bool.case(U32.is_eq(D.Fd(3n, m, r), c), U32.is_eq(D.Fd(3n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Mat{k, y, z}, m, r, g) == True{} : Bool}, {D.Mem(D.Fs(m, ps, g), c) == True{} : Bool})), {==},
          eb => par.here(Bk.Term.Mat{k, y, z}, m, ps, r, c, 14, 6, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Mat{k, y, z}, 14, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Mat{k, y, z}, tbl), CK.Bo.or_il(U32.is_eq(D.Fd(3n, m, r), c), Bool.or(U32.is_eq(D.Fd(4n, m, r), c), False{}), eb)),
          eb => par.up(y, D.Fd(3n, m, r), Bk.Term.Mat{k, y, z}, m, ps, r, c, node.par(y, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(3n, m, r), c, hy, e, eb), +g => hg => in.l(U32.is_eq(r, g), D.Node(y, m, D.Fd(3n, m, r), g), D.Node(z, m, D.Fd(4n, m, r), g), hg))),
        e => bool.case(U32.is_eq(D.Fd(4n, m, r), c), U32.is_eq(D.Fd(4n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Mat{k, y, z}, m, r, g) == True{} : Bool}, {D.Mem(D.Fs(m, ps, g), c) == True{} : Bool})), {==},
          eb => par.here(Bk.Term.Mat{k, y, z}, m, ps, r, c, 14, 6, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Mat{k, y, z}, 14, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Mat{k, y, z}, tbl), CK.Bo.or_ir(U32.is_eq(D.Fd(3n, m, r), c), Bool.or(U32.is_eq(D.Fd(4n, m, r), c), False{}), CK.Bo.or_il(U32.is_eq(D.Fd(4n, m, r), c), False{}, eb))),
          eb => par.up(z, D.Fd(4n, m, r), Bk.Term.Mat{k, y, z}, m, ps, r, c, node.par(z, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(4n, m, r), c, hz, e, eb), +g => hg => in.r(U32.is_eq(r, g), D.Node(y, m, D.Fd(3n, m, r), g), D.Node(z, m, D.Fd(4n, m, r), g), hg))))
    case Bk.Term.Efq{}:
      CK.Bo.tf(D.Ex(U32, g => D.P2({D.Node(Bk.Term.Efq{}, m, r, g) == True{} : Bool}, {D.Mem(D.Fs(m, ps, g), c) == True{} : Bool})), Equal.trans(Bool, False{}, U32.is_eq(r, c), True{}, Equal.sym(Bool, U32.is_eq(r, c), False{}, hne), hn))
    case Bk.Term.Eql{+y, +z, +w}:
      (+nd, w0) = h
      (py, w2) = w0
      (sy, hy) = py
      (pz, pw) = w2
      (sz, hz) = pz
      (sw, hw) = pw
      or3.case(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c), D.Node(w, m, D.Fd(4n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Eql{y, z, w}, m, r, g) == True{} : Bool}, {D.Mem(D.Fs(m, ps, g), c) == True{} : Bool})), or.drop(U32.is_eq(r, c), Bool.or(D.Node(y, m, D.Fd(2n, m, r), c), Bool.or(D.Node(z, m, D.Fd(3n, m, r), c), D.Node(w, m, D.Fd(4n, m, r), c))), hn, hne),
        e => bool.case(U32.is_eq(D.Fd(2n, m, r), c), U32.is_eq(D.Fd(2n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Eql{y, z, w}, m, r, g) == True{} : Bool}, {D.Mem(D.Fs(m, ps, g), c) == True{} : Bool})), {==},
          eb => par.here(Bk.Term.Eql{y, z, w}, m, ps, r, c, 16, 7, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Eql{y, z, w}, 16, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Eql{y, z, w}, tbl), CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, r), c), Bool.or(U32.is_eq(D.Fd(3n, m, r), c), Bool.or(U32.is_eq(D.Fd(4n, m, r), c), False{})), eb)),
          eb => par.up(y, D.Fd(2n, m, r), Bk.Term.Eql{y, z, w}, m, ps, r, c, node.par(y, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(2n, m, r), c, hy, e, eb), +g => hg => in.a(U32.is_eq(r, g), D.Node(y, m, D.Fd(2n, m, r), g), D.Node(z, m, D.Fd(3n, m, r), g), D.Node(w, m, D.Fd(4n, m, r), g), hg))),
        e => bool.case(U32.is_eq(D.Fd(3n, m, r), c), U32.is_eq(D.Fd(3n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Eql{y, z, w}, m, r, g) == True{} : Bool}, {D.Mem(D.Fs(m, ps, g), c) == True{} : Bool})), {==},
          eb => par.here(Bk.Term.Eql{y, z, w}, m, ps, r, c, 16, 7, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Eql{y, z, w}, 16, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Eql{y, z, w}, tbl), CK.Bo.or_ir(U32.is_eq(D.Fd(2n, m, r), c), Bool.or(U32.is_eq(D.Fd(3n, m, r), c), Bool.or(U32.is_eq(D.Fd(4n, m, r), c), False{})), CK.Bo.or_il(U32.is_eq(D.Fd(3n, m, r), c), Bool.or(U32.is_eq(D.Fd(4n, m, r), c), False{}), eb))),
          eb => par.up(z, D.Fd(3n, m, r), Bk.Term.Eql{y, z, w}, m, ps, r, c, node.par(z, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(3n, m, r), c, hz, e, eb), +g => hg => in.b(U32.is_eq(r, g), D.Node(y, m, D.Fd(2n, m, r), g), D.Node(z, m, D.Fd(3n, m, r), g), D.Node(w, m, D.Fd(4n, m, r), g), hg))),
        e => bool.case(U32.is_eq(D.Fd(4n, m, r), c), U32.is_eq(D.Fd(4n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Eql{y, z, w}, m, r, g) == True{} : Bool}, {D.Mem(D.Fs(m, ps, g), c) == True{} : Bool})), {==},
          eb => par.here(Bk.Term.Eql{y, z, w}, m, ps, r, c, 16, 7, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Eql{y, z, w}, 16, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Eql{y, z, w}, tbl), CK.Bo.or_ir(U32.is_eq(D.Fd(2n, m, r), c), Bool.or(U32.is_eq(D.Fd(3n, m, r), c), Bool.or(U32.is_eq(D.Fd(4n, m, r), c), False{})), CK.Bo.or_ir(U32.is_eq(D.Fd(3n, m, r), c), Bool.or(U32.is_eq(D.Fd(4n, m, r), c), False{}), CK.Bo.or_il(U32.is_eq(D.Fd(4n, m, r), c), False{}, eb)))),
          eb => par.up(w, D.Fd(4n, m, r), Bk.Term.Eql{y, z, w}, m, ps, r, c, node.par(w, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(4n, m, r), c, hw, e, eb), +g => hg => in.c(U32.is_eq(r, g), D.Node(y, m, D.Fd(2n, m, r), g), D.Node(z, m, D.Fd(3n, m, r), g), D.Node(w, m, D.Fd(4n, m, r), g), hg))))
    case Bk.Term.Rfl{}:
      CK.Bo.tf(D.Ex(U32, g => D.P2({D.Node(Bk.Term.Rfl{}, m, r, g) == True{} : Bool}, {D.Mem(D.Fs(m, ps, g), c) == True{} : Bool})), Equal.trans(Bool, False{}, U32.is_eq(r, c), True{}, Equal.sym(Bool, U32.is_eq(r, c), False{}, hne), hn))
    case Bk.Term.Rwt{+y, +z, +w}:
      (+nd, w0) = h
      (py, w2) = w0
      (sy, hy) = py
      (pz, pw) = w2
      (sz, hz) = pz
      (sw, hw) = pw
      or3.case(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c), D.Node(w, m, D.Fd(4n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Rwt{y, z, w}, m, r, g) == True{} : Bool}, {D.Mem(D.Fs(m, ps, g), c) == True{} : Bool})), or.drop(U32.is_eq(r, c), Bool.or(D.Node(y, m, D.Fd(2n, m, r), c), Bool.or(D.Node(z, m, D.Fd(3n, m, r), c), D.Node(w, m, D.Fd(4n, m, r), c))), hn, hne),
        e => bool.case(U32.is_eq(D.Fd(2n, m, r), c), U32.is_eq(D.Fd(2n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Rwt{y, z, w}, m, r, g) == True{} : Bool}, {D.Mem(D.Fs(m, ps, g), c) == True{} : Bool})), {==},
          eb => par.here(Bk.Term.Rwt{y, z, w}, m, ps, r, c, 18, 7, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Rwt{y, z, w}, 18, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Rwt{y, z, w}, tbl), CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, r), c), Bool.or(U32.is_eq(D.Fd(3n, m, r), c), Bool.or(U32.is_eq(D.Fd(4n, m, r), c), False{})), eb)),
          eb => par.up(y, D.Fd(2n, m, r), Bk.Term.Rwt{y, z, w}, m, ps, r, c, node.par(y, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(2n, m, r), c, hy, e, eb), +g => hg => in.a(U32.is_eq(r, g), D.Node(y, m, D.Fd(2n, m, r), g), D.Node(z, m, D.Fd(3n, m, r), g), D.Node(w, m, D.Fd(4n, m, r), g), hg))),
        e => bool.case(U32.is_eq(D.Fd(3n, m, r), c), U32.is_eq(D.Fd(3n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Rwt{y, z, w}, m, r, g) == True{} : Bool}, {D.Mem(D.Fs(m, ps, g), c) == True{} : Bool})), {==},
          eb => par.here(Bk.Term.Rwt{y, z, w}, m, ps, r, c, 18, 7, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Rwt{y, z, w}, 18, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Rwt{y, z, w}, tbl), CK.Bo.or_ir(U32.is_eq(D.Fd(2n, m, r), c), Bool.or(U32.is_eq(D.Fd(3n, m, r), c), Bool.or(U32.is_eq(D.Fd(4n, m, r), c), False{})), CK.Bo.or_il(U32.is_eq(D.Fd(3n, m, r), c), Bool.or(U32.is_eq(D.Fd(4n, m, r), c), False{}), eb))),
          eb => par.up(z, D.Fd(3n, m, r), Bk.Term.Rwt{y, z, w}, m, ps, r, c, node.par(z, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(3n, m, r), c, hz, e, eb), +g => hg => in.b(U32.is_eq(r, g), D.Node(y, m, D.Fd(2n, m, r), g), D.Node(z, m, D.Fd(3n, m, r), g), D.Node(w, m, D.Fd(4n, m, r), g), hg))),
        e => bool.case(U32.is_eq(D.Fd(4n, m, r), c), U32.is_eq(D.Fd(4n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Rwt{y, z, w}, m, r, g) == True{} : Bool}, {D.Mem(D.Fs(m, ps, g), c) == True{} : Bool})), {==},
          eb => par.here(Bk.Term.Rwt{y, z, w}, m, ps, r, c, 18, 7, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Rwt{y, z, w}, 18, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Rwt{y, z, w}, tbl), CK.Bo.or_ir(U32.is_eq(D.Fd(2n, m, r), c), Bool.or(U32.is_eq(D.Fd(3n, m, r), c), Bool.or(U32.is_eq(D.Fd(4n, m, r), c), False{})), CK.Bo.or_ir(U32.is_eq(D.Fd(3n, m, r), c), Bool.or(U32.is_eq(D.Fd(4n, m, r), c), False{}), CK.Bo.or_il(U32.is_eq(D.Fd(4n, m, r), c), False{}, eb)))),
          eb => par.up(w, D.Fd(4n, m, r), Bk.Term.Rwt{y, z, w}, m, ps, r, c, node.par(w, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(4n, m, r), c, hw, e, eb), +g => hg => in.c(U32.is_eq(r, g), D.Node(y, m, D.Fd(2n, m, r), g), D.Node(z, m, D.Fd(3n, m, r), g), D.Node(w, m, D.Fd(4n, m, r), g), hg))))

# The laws
# --------

def K.copy.post(f, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, wt, keep, os, bs, fs, sp, pend, ps, c, t, ce, es, xs, zs, hs, hac, hl, hc, hp, he, hn, env, ho, hv, hk):
  ?TODO

def K.copy.done(ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, wt, os, bs, fs, sp, pend, ps, c, t, ce, es, xs, zs, hs, hac, hl, hc, hp, he, hn, env, ho, hv):
  ?TODO
