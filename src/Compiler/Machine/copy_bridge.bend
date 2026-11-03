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
import ./accounting.bend as AC

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

# the K.args of the chain are below next
def ag.lt(+xs: List<&2, El.Arg>, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +os: List<&2, D.Rt>, +vs: List<&2, U32>, +a: U32,
  +h: D.Ag(ds, m, im, fi, nx, ks, img, ps, os, vs, a, xs)) -> {Lt.n(Nats(Ag.links(xs, m, a)), U32.to_nat(nx)) == True{} : Bool}:
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
      CK.Bo.and_i(Nat.is_lt(U32.to_nat(a), U32.to_nat(nx)), Lt.n(Nats(Ag.links(rest, m, D.Fd(1n, m, a))), U32.to_nat(nx)),
        le.lt(U32.to_nat(a), U32.to_nat(nx), CK.U.lt(a, nx, CK.Bo.and_r(U32.is_le(fi, a), U32.is_lt(a, nx), e2))),
        ag.lt(rest, ds, m, im, fi, nx, ks, img, ps, os, vs, D.Fd(1n, m, a), h2))

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
    ag.lt(xs, ds, m, im, fi, nx, ks, img, ps, os, vs, a, h))
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

# Cells in a range
# ----------------

# the cell p, at or after o and before 1 + k cells from o, but not o: at or
# after o + 1 (rng.lo) and before k cells from it (rng.hi)
def rng.lo(+k: Nat, +o: U32, +p: U32, eb: {U32.is_eq(o, p) == False{} : Bool},
  h1: N.Le(U32.to_nat(o), U32.to_nat(p))) -> N.Le(U32.to_nat(U32.inc(o)), U32.to_nat(p)):
  +lt = D.lt.ne(U32.cmp(o, p), U32.to_nat(o), U32.to_nat(p), N.U32.rel(o, p), eb, h1)
  N.le_rw_l(1n+U32.to_nat(o), U32.to_nat(U32.inc(o)), U32.to_nat(p), Equal.sym(Nat, U32.to_nat(U32.inc(o)), 1n+U32.to_nat(o), D.u.inc(o, p, lt)), lt)

def rng.hi(+k: Nat, +o: U32, +p: U32, eb: {U32.is_eq(o, p) == False{} : Bool},
  h1: N.Le(U32.to_nat(o), U32.to_nat(p)), h2: N.Le(1n+U32.to_nat(p), Nat.add(U32.to_nat(o), 1n+k))) ->
  N.Le(1n+U32.to_nat(p), Nat.add(U32.to_nat(U32.inc(o)), k)):
  +lt = D.lt.ne(U32.cmp(o, p), U32.to_nat(o), U32.to_nat(p), N.U32.rel(o, p), eb, h1)
  +ei = D.u.inc(o, p, lt)
  N.le_rw_r(1n+U32.to_nat(p), Nat.add(U32.to_nat(o), 1n+k), Nat.add(U32.to_nat(U32.inc(o)), k),
    Equal.trans(Nat, Nat.add(U32.to_nat(o), 1n+k), 1n+Nat.add(U32.to_nat(o), k), Nat.add(U32.to_nat(U32.inc(o)), k),
      N.add_succ_r(U32.to_nat(o), k),
      Equal.sym(Nat, Nat.add(U32.to_nat(U32.inc(o)), k), 1n+Nat.add(U32.to_nat(o), k),
        Equal.cong(Nat, Nat, x => Nat.add(x, k), U32.to_nat(U32.inc(o)), 1n+U32.to_nat(o), ei))), h2)

# no cell is at or after o and before 0 cells from o
def rng.none(-G: Type, +o: U32, +p: U32, h1: N.Le(U32.to_nat(o), U32.to_nat(p)), h2: N.Le(1n+U32.to_nat(p), Nat.add(U32.to_nat(o), 0n))) -> G:
  Empty.absurd(G, N.not_succ_le(U32.to_nat(p), N.le_trans(1n+U32.to_nat(p), U32.to_nat(o), U32.to_nat(p),
    N.le_rw_r(1n+U32.to_nat(p), Nat.add(U32.to_nat(o), 0n), U32.to_nat(o), N.add_zero(U32.to_nat(o)), h2), h1)))

# a cell of the machine's own is in the range of its cells, from fi
def own.lo(+fi: U32, +nx: U32, +r: U32, own: {D.Own(fi, nx, r) == True{} : Bool}) -> N.Le(U32.to_nat(fi), U32.to_nat(r)):
  D.u.le(fi, r, D.and.l(U32.is_le(fi, r), U32.is_lt(r, nx), own))

def own.hi(+fi: U32, +nx: U32, +r: U32, own: {D.Own(fi, nx, r) == True{} : Bool}) ->
  N.Le(1n+U32.to_nat(r), Nat.add(U32.to_nat(fi), Nat.sub(U32.to_nat(nx), U32.to_nat(fi)))):
  +o2 = own
  +h1 = D.u.le(fi, r, D.and.l(U32.is_le(fi, r), U32.is_lt(r, nx), o2))
  +hl = D.u.lt(r, nx, D.and.r(U32.is_le(fi, r), U32.is_lt(r, nx), o2))
  +es = D.add.sub(U32.to_nat(fi), U32.to_nat(nx), N.le_trans(U32.to_nat(fi), U32.to_nat(r), U32.to_nat(nx), h1, N.weaken(U32.to_nat(r), U32.to_nat(nx), hl)))
  N.le_rw_r(1n+U32.to_nat(r), U32.to_nat(nx), Nat.add(U32.to_nat(fi), Nat.sub(U32.to_nat(nx), U32.to_nat(fi))),
    Equal.sym(Nat, Nat.add(U32.to_nat(fi), Nat.sub(U32.to_nat(nx), U32.to_nat(fi))), U32.to_nat(nx), es), hl)

# Clo at the cell p of the n cells from o
def clo.get.b(b: Bool, +k: Nat, +m: Cr.Cir.Cells, +o: U32, +p: U32, +ps: List<&2, U32>, +cs: List<&2, U32>, +hc: List<&2, U32>,
  eb: {U32.is_eq(o, p) == b : Bool}, h1: N.Le(U32.to_nat(o), U32.to_nat(p)), h2: N.Le(1n+U32.to_nat(p), Nat.add(U32.to_nat(o), 1n+k)),
  hcl: {D.Clo(1n+k, m, o, ps, cs, hc) == True{} : Bool},
  ih: N.Le(U32.to_nat(U32.inc(o)), U32.to_nat(p)) -> N.Le(1n+U32.to_nat(p), Nat.add(U32.to_nat(U32.inc(o)), k)) ->
    {D.Clo(k, m, U32.inc(o), ps, cs, hc) == True{} : Bool} -> {D.Clo.at(m, p, ps, cs, hc) == True{} : Bool}) ->
  {D.Clo.at(m, p, ps, cs, hc) == True{} : Bool}:
  match b:
    case True{}:
      %D.u32.eq(o, p, eb) : {D.Clo.at(m, _, ps, cs, hc) == True{} : Bool}
      D.and.l(D.Clo.at(m, o, ps, cs, hc), D.Clo(k, m, U32.inc(o), ps, cs, hc), hcl)
    case False{}:
      +eb2 = eb
      +h12 = h1
      ih(rng.lo(k, o, p, eb2, h12), rng.hi(k, o, p, eb2, h12, h2), D.and.r(D.Clo.at(m, o, ps, cs, hc), D.Clo(k, m, U32.inc(o), ps, cs, hc), hcl))

def clo.get(n: Nat, +m: Cr.Cir.Cells, +o: U32, +p: U32, +ps: List<&2, U32>, +cs: List<&2, U32>, +hc: List<&2, U32>,
  h1: N.Le(U32.to_nat(o), U32.to_nat(p)), h2: N.Le(1n+U32.to_nat(p), Nat.add(U32.to_nat(o), n)),
  hcl: {D.Clo(n, m, o, ps, cs, hc) == True{} : Bool}) -> {D.Clo.at(m, p, ps, cs, hc) == True{} : Bool}:
  match n:
    case 0n:
      rng.none({D.Clo.at(m, p, ps, cs, hc) == True{} : Bool}, o, p, h1, h2)
    case 1n+(+k):
      clo.get.b(U32.is_eq(o, p), k, m, o, p, ps, cs, hc, {==}, h1, h2, hcl, x => y => z => clo.get(k, m, U32.inc(o), p, ps, cs, hc, x, y, z))

# a STATIC cell of the machine's own points to STATIC cells (Clo)
def clo.st(+m: Cr.Cir.Cells, +fi: U32, +nx: U32, +ps: List<&2, U32>, +cs: List<&2, U32>, +hc: List<&2, U32>, +r: U32,
  own: {D.Own(fi, nx, r) == True{} : Bool}, hs: {D.Fl(m, r, 1024) == True{} : Bool},
  hcl: {D.Clo(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, cs, hc) == True{} : Bool}) ->
  {D.All.static(D.Fs(m, ps, r), m) == True{} : Bool}:
  +own2 = own
  +ca = clo.get(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, r, ps, cs, hc, own.lo(fi, nx, r, own2), own.hi(fi, nx, r, own2), hcl)
  CK.Bo.or_r(Bool.not(D.Fl(m, r, 1024)), D.All.static(D.Fs(m, ps, r), m),
    CK.Bo.and_l(Bool.or(Bool.not(D.Fl(m, r, 1024)), D.All.static(D.Fs(m, ps, r), m)),
      Bool.or(Bool.not(D.Mem(cs, r)), D.All.held(D.Fs(m, ps, r), m, cs, hc)), ca),
    (%Equal.sym(Bool, D.Fl(m, r, 1024), True{}, hs) : {Bool.not(_) == False{} : Bool}; {==}))

# a leaf (mask 0) has no pointer
def fs.leaf(-G: Type, -dk: Bool, -ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, -im: U32, -fi: U32, -nx: U32, +ps: List<&2, U32>,
  +r: U32, +c: U32, +v: U32, -t: Bk.Term, +tag: U32, nd: D.NdK(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), t, tag),
  hlt: {U32.is_lt(tag, 19) == True{} : Bool}, emask: {D.Fd(2n, m, U32.add(272, tag)) == 0 : U32},
  hn: {U32.is_eq(r, c) == True{} : Bool}, hv: {D.Mem(D.Fs(m, ps, c), v) == True{} : Bool}) -> G:
  CK.Bo.tf(G, (%D.fs.term(m, ps, r, tag, 0, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), t, tag, nd), hlt, emask) :
    {D.Mem(_, v) == True{} : Bool}; (%Equal.sym(U32, r, c, CK.U.eq(r, c, hn)) : {D.Mem(D.Fs(m, ps, _), v) == True{} : Bool}; hv)))

# a cell of xs, which are all STATIC, is STATIC
def static.mem(xs: List<&2, U32>, +m: Cr.Cir.Cells, +y: U32, +h: {D.All.static(xs, m) == True{} : Bool},
  hm: {D.Mem(xs, y) == True{} : Bool}) -> {D.Fl(m, y, 1024) == True{} : Bool}:
  match xs:
    case Nil{}:
      CK.Bo.tf({D.Fl(m, y, 1024) == True{} : Bool}, hm)
    case Con{+x, +rest}:
      D.or.cases(U32.is_eq(x, y), D.Mem(rest, y), {D.Fl(m, y, 1024) == True{} : Bool}, hm,
        e => (%CK.U.eq(x, y, e) : {D.Fl(m, _, 1024) == True{} : Bool}; CK.Bo.and_l(D.Fl(m, x, 1024), D.All.static(rest, m), h)),
        e => static.mem(rest, m, y, CK.Bo.and_r(D.Fl(m, x, 1024), D.All.static(rest, m), h), e))

# a part y, among the pointers of the STATIC cell r: STATIC, by Clo when r is
# one of the machine's own (o), by Sp when not
def part.st(o: Bool, +m: Cr.Cir.Cells, +ps: List<&2, U32>, +fi: U32, +nx: U32, +cs: List<&2, U32>, +hc: List<&2, U32>, +r: U32, +y: U32,
  eo: {D.Own(fi, nx, r) == o : Bool}, hs: {D.Fl(m, r, 1024) == True{} : Bool},
  hcl: {D.Clo(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, cs, hc) == True{} : Bool},
  sp: D.Sp(fi, nx, r, Cr.Cir.Cells.get(m, y)), hm: {D.Mem(D.Fs(m, ps, r), y) == True{} : Bool}) -> {D.Fl(m, y, 1024) == True{} : Bool}:
  match o:
    case True{}:
      static.mem(D.Fs(m, ps, r), m, y, clo.st(m, fi, nx, ps, cs, hc, r, eo, hs, hcl), hm)
    case False{}:
      %eo : {Bool.or(_, D.FlW(Cr.Cir.Cell.get(0n, Cr.Cir.Cells.get(m, y)), 1024)) == True{} : Bool}
      sp

# the parent is the root r, whose pointers by its tag's mask hold c (the part
# y of r, which Sp says is STATIC or r one of the machine's own)
def par.here(+t: Bk.Term, +m: Cr.Cir.Cells, +ps: List<&2, U32>, +fi: U32, +nx: U32, +r: U32, +c: U32, +y: U32, +tg: U32, +mask: U32,
  etag: {D.TgW(D.Fd(0n, m, r)) == tg : U32}, hlt: {U32.is_lt(tg, 19) == True{} : Bool}, emask: {D.Fd(2n, m, U32.add(272, tg)) == mask : U32},
  hy: {D.Mem(D.Fs.term(mask, D.Fd(2n, m, r), D.Fd(3n, m, r), D.Fd(4n, m, r)), c) == True{} : Bool},
  sp: D.Sp(fi, nx, r, Cr.Cir.Cells.get(m, y)), ey: {U32.is_eq(y, c) == True{} : Bool}) ->
  D.Ex(U32, g => D.P2({D.Node(t, m, r, g) == True{} : Bool}, D.P2({D.Mem(D.Fs(m, ps, g), c) == True{} : Bool}, D.Sp(fi, nx, g, Cr.Cir.Cells.get(m, c))))):
  (r, (node.root(t, m, r), (D.hm.at(m, ps, r, tg, mask, c, etag, hlt, emask, hy), (%CK.U.eq(y, c, ey) : D.Sp(fi, nx, r, Cr.Cir.Cells.get(m, _)); sp))))

# the parent in a part y (at pr) is a parent in t
def par.up(-y: Bk.Term, -pr: U32, -t: Bk.Term, -m: Cr.Cir.Cells, -ps: List<&2, U32>, -fi: U32, -nx: U32, -r: U32, -c: U32,
  rec: D.Ex(U32, g => D.P2({D.Node(y, m, pr, g) == True{} : Bool}, D.P2({D.Mem(D.Fs(m, ps, g), c) == True{} : Bool}, D.Sp(fi, nx, g, Cr.Cir.Cells.get(m, c))))),
  lift: @g: U32 -> {D.Node(y, m, pr, g) == True{} : Bool} -> {D.Node(t, m, r, g) == True{} : Bool}) ->
  D.Ex(U32, g => D.P2({D.Node(t, m, r, g) == True{} : Bool}, D.P2({D.Mem(D.Fs(m, ps, g), c) == True{} : Bool}, D.Sp(fi, nx, g, Cr.Cir.Cells.get(m, c))))):
  (+g, rr) = rec
  (hg, hrest) = rr
  (g, (lift(g, hg), hrest))

# a node c of the term t at r, other than r, has a parent: a node of t whose
# pointers hold c, and which is one of the machine's own, or c is STATIC (Sp)
def node.par(t: Bk.Term, +dk: Bool, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +tbl: D.Tbl(m, im, fi, nx), +r: U32, +c: U32,
  h: D.IsK(dk, ds, m, im, fi, nx, ks, img, r, t), hn: {D.Node(t, m, r, c) == True{} : Bool}, +hne: {U32.is_eq(r, c) == False{} : Bool}) ->
  D.Ex(U32, g => D.P2({D.Node(t, m, r, g) == True{} : Bool}, D.P2({D.Mem(D.Fs(m, ps, g), c) == True{} : Bool}, D.Sp(fi, nx, g, Cr.Cir.Cells.get(m, c))))):
  match t:
    case Bk.Term.Var{+i}:
      CK.Bo.tf(D.Ex(U32, g => D.P2({D.Node(Bk.Term.Var{i}, m, r, g) == True{} : Bool}, D.P2({D.Mem(D.Fs(m, ps, g), c) == True{} : Bool}, D.Sp(fi, nx, g, Cr.Cir.Cells.get(m, c))))), Equal.trans(Bool, False{}, U32.is_eq(r, c), True{}, Equal.sym(Bool, U32.is_eq(r, c), False{}, hne), hn))
    case Bk.Term.Ref{+k}:
      CK.Bo.tf(D.Ex(U32, g => D.P2({D.Node(Bk.Term.Ref{k}, m, r, g) == True{} : Bool}, D.P2({D.Mem(D.Fs(m, ps, g), c) == True{} : Bool}, D.Sp(fi, nx, g, Cr.Cir.Cells.get(m, c))))), Equal.trans(Bool, False{}, U32.is_eq(r, c), True{}, Equal.sym(Bool, U32.is_eq(r, c), False{}, hne), hn))
    case Bk.Term.Ann{+y, +z}:
      (+nd, w0) = h
      (py, pz) = w0
      (sy, hy) = py
      (sz, hz) = pz
      D.or.cases(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Ann{y, z}, m, r, g) == True{} : Bool}, D.P2({D.Mem(D.Fs(m, ps, g), c) == True{} : Bool}, D.Sp(fi, nx, g, Cr.Cir.Cells.get(m, c))))), or.drop(U32.is_eq(r, c), Bool.or(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c)), hn, hne),
        e => bool.case(U32.is_eq(D.Fd(2n, m, r), c), U32.is_eq(D.Fd(2n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Ann{y, z}, m, r, g) == True{} : Bool}, D.P2({D.Mem(D.Fs(m, ps, g), c) == True{} : Bool}, D.Sp(fi, nx, g, Cr.Cir.Cells.get(m, c))))), {==},
          +eb => par.here(Bk.Term.Ann{y, z}, m, ps, fi, nx, r, c, D.Fd(2n, m, r), 2, 3, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Ann{y, z}, 2, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Ann{y, z}, tbl), CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, r), c), Bool.or(U32.is_eq(D.Fd(3n, m, r), c), False{}), eb), sy, eb),
          eb => par.up(y, D.Fd(2n, m, r), Bk.Term.Ann{y, z}, m, ps, fi, nx, r, c, node.par(y, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(2n, m, r), c, hy, e, eb), +g => hg => in.l(U32.is_eq(r, g), D.Node(y, m, D.Fd(2n, m, r), g), D.Node(z, m, D.Fd(3n, m, r), g), hg))),
        e => bool.case(U32.is_eq(D.Fd(3n, m, r), c), U32.is_eq(D.Fd(3n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Ann{y, z}, m, r, g) == True{} : Bool}, D.P2({D.Mem(D.Fs(m, ps, g), c) == True{} : Bool}, D.Sp(fi, nx, g, Cr.Cir.Cells.get(m, c))))), {==},
          +eb => par.here(Bk.Term.Ann{y, z}, m, ps, fi, nx, r, c, D.Fd(3n, m, r), 2, 3, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Ann{y, z}, 2, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Ann{y, z}, tbl), CK.Bo.or_ir(U32.is_eq(D.Fd(2n, m, r), c), Bool.or(U32.is_eq(D.Fd(3n, m, r), c), False{}), CK.Bo.or_il(U32.is_eq(D.Fd(3n, m, r), c), False{}, eb)), sz, eb),
          eb => par.up(z, D.Fd(3n, m, r), Bk.Term.Ann{y, z}, m, ps, fi, nx, r, c, node.par(z, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(3n, m, r), c, hz, e, eb), +g => hg => in.r(U32.is_eq(r, g), D.Node(y, m, D.Fd(2n, m, r), g), D.Node(z, m, D.Fd(3n, m, r), g), hg))))
    case Bk.Term.Let{+q, +y, +z}:
      (+nd, w0) = h
      (hq, w2) = w0
      (py, pz) = w2
      (sy, hy) = py
      (sz, hz) = pz
      D.or.cases(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Let{q, y, z}, m, r, g) == True{} : Bool}, D.P2({D.Mem(D.Fs(m, ps, g), c) == True{} : Bool}, D.Sp(fi, nx, g, Cr.Cir.Cells.get(m, c))))), or.drop(U32.is_eq(r, c), Bool.or(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c)), hn, hne),
        e => bool.case(U32.is_eq(D.Fd(2n, m, r), c), U32.is_eq(D.Fd(2n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Let{q, y, z}, m, r, g) == True{} : Bool}, D.P2({D.Mem(D.Fs(m, ps, g), c) == True{} : Bool}, D.Sp(fi, nx, g, Cr.Cir.Cells.get(m, c))))), {==},
          +eb => par.here(Bk.Term.Let{q, y, z}, m, ps, fi, nx, r, c, D.Fd(2n, m, r), 3, 3, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Let{q, y, z}, 3, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Let{q, y, z}, tbl), CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, r), c), Bool.or(U32.is_eq(D.Fd(3n, m, r), c), False{}), eb), sy, eb),
          eb => par.up(y, D.Fd(2n, m, r), Bk.Term.Let{q, y, z}, m, ps, fi, nx, r, c, node.par(y, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(2n, m, r), c, hy, e, eb), +g => hg => in.l(U32.is_eq(r, g), D.Node(y, m, D.Fd(2n, m, r), g), D.Node(z, m, D.Fd(3n, m, r), g), hg))),
        e => bool.case(U32.is_eq(D.Fd(3n, m, r), c), U32.is_eq(D.Fd(3n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Let{q, y, z}, m, r, g) == True{} : Bool}, D.P2({D.Mem(D.Fs(m, ps, g), c) == True{} : Bool}, D.Sp(fi, nx, g, Cr.Cir.Cells.get(m, c))))), {==},
          +eb => par.here(Bk.Term.Let{q, y, z}, m, ps, fi, nx, r, c, D.Fd(3n, m, r), 3, 3, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Let{q, y, z}, 3, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Let{q, y, z}, tbl), CK.Bo.or_ir(U32.is_eq(D.Fd(2n, m, r), c), Bool.or(U32.is_eq(D.Fd(3n, m, r), c), False{}), CK.Bo.or_il(U32.is_eq(D.Fd(3n, m, r), c), False{}, eb)), sz, eb),
          eb => par.up(z, D.Fd(3n, m, r), Bk.Term.Let{q, y, z}, m, ps, fi, nx, r, c, node.par(z, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(3n, m, r), c, hz, e, eb), +g => hg => in.r(U32.is_eq(r, g), D.Node(y, m, D.Fd(2n, m, r), g), D.Node(z, m, D.Fd(3n, m, r), g), hg))))
    case Bk.Term.Typ{+y}:
      (+nd, w0) = h
      (sy, hy) = w0
      par.one(D.Node(y, m, D.Fd(2n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Typ{y}, m, r, g) == True{} : Bool}, D.P2({D.Mem(D.Fs(m, ps, g), c) == True{} : Bool}, D.Sp(fi, nx, g, Cr.Cir.Cells.get(m, c))))), or.drop(U32.is_eq(r, c), D.Node(y, m, D.Fd(2n, m, r), c), hn, hne),
        e => bool.case(U32.is_eq(D.Fd(2n, m, r), c), U32.is_eq(D.Fd(2n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Typ{y}, m, r, g) == True{} : Bool}, D.P2({D.Mem(D.Fs(m, ps, g), c) == True{} : Bool}, D.Sp(fi, nx, g, Cr.Cir.Cells.get(m, c))))), {==},
          +eb => par.here(Bk.Term.Typ{y}, m, ps, fi, nx, r, c, D.Fd(2n, m, r), 4, 1, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Typ{y}, 4, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Typ{y}, tbl), CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, r), c), False{}, eb), sy, eb),
          eb => par.up(y, D.Fd(2n, m, r), Bk.Term.Typ{y}, m, ps, fi, nx, r, c, node.par(y, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(2n, m, r), c, hy, e, eb), +g => hg => CK.Bo.or_ir(U32.is_eq(r, g), D.Node(y, m, D.Fd(2n, m, r), g), hg))))
    case Bk.Term.Min{+y, +z}:
      (+nd, w0) = h
      (py, pz) = w0
      (sy, hy) = py
      (sz, hz) = pz
      D.or.cases(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Min{y, z}, m, r, g) == True{} : Bool}, D.P2({D.Mem(D.Fs(m, ps, g), c) == True{} : Bool}, D.Sp(fi, nx, g, Cr.Cir.Cells.get(m, c))))), or.drop(U32.is_eq(r, c), Bool.or(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c)), hn, hne),
        e => bool.case(U32.is_eq(D.Fd(2n, m, r), c), U32.is_eq(D.Fd(2n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Min{y, z}, m, r, g) == True{} : Bool}, D.P2({D.Mem(D.Fs(m, ps, g), c) == True{} : Bool}, D.Sp(fi, nx, g, Cr.Cir.Cells.get(m, c))))), {==},
          +eb => par.here(Bk.Term.Min{y, z}, m, ps, fi, nx, r, c, D.Fd(2n, m, r), 5, 3, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Min{y, z}, 5, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Min{y, z}, tbl), CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, r), c), Bool.or(U32.is_eq(D.Fd(3n, m, r), c), False{}), eb), sy, eb),
          eb => par.up(y, D.Fd(2n, m, r), Bk.Term.Min{y, z}, m, ps, fi, nx, r, c, node.par(y, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(2n, m, r), c, hy, e, eb), +g => hg => in.l(U32.is_eq(r, g), D.Node(y, m, D.Fd(2n, m, r), g), D.Node(z, m, D.Fd(3n, m, r), g), hg))),
        e => bool.case(U32.is_eq(D.Fd(3n, m, r), c), U32.is_eq(D.Fd(3n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Min{y, z}, m, r, g) == True{} : Bool}, D.P2({D.Mem(D.Fs(m, ps, g), c) == True{} : Bool}, D.Sp(fi, nx, g, Cr.Cir.Cells.get(m, c))))), {==},
          +eb => par.here(Bk.Term.Min{y, z}, m, ps, fi, nx, r, c, D.Fd(3n, m, r), 5, 3, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Min{y, z}, 5, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Min{y, z}, tbl), CK.Bo.or_ir(U32.is_eq(D.Fd(2n, m, r), c), Bool.or(U32.is_eq(D.Fd(3n, m, r), c), False{}), CK.Bo.or_il(U32.is_eq(D.Fd(3n, m, r), c), False{}, eb)), sz, eb),
          eb => par.up(z, D.Fd(3n, m, r), Bk.Term.Min{y, z}, m, ps, fi, nx, r, c, node.par(z, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(3n, m, r), c, hz, e, eb), +g => hg => in.r(U32.is_eq(r, g), D.Node(y, m, D.Fd(2n, m, r), g), D.Node(z, m, D.Fd(3n, m, r), g), hg))))
    case Bk.Term.All{+q, +y, +z}:
      (+nd, w0) = h
      (hq, w2) = w0
      (py, pz) = w2
      (sy, hy) = py
      (sz, hz) = pz
      D.or.cases(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.All{q, y, z}, m, r, g) == True{} : Bool}, D.P2({D.Mem(D.Fs(m, ps, g), c) == True{} : Bool}, D.Sp(fi, nx, g, Cr.Cir.Cells.get(m, c))))), or.drop(U32.is_eq(r, c), Bool.or(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c)), hn, hne),
        e => bool.case(U32.is_eq(D.Fd(2n, m, r), c), U32.is_eq(D.Fd(2n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.All{q, y, z}, m, r, g) == True{} : Bool}, D.P2({D.Mem(D.Fs(m, ps, g), c) == True{} : Bool}, D.Sp(fi, nx, g, Cr.Cir.Cells.get(m, c))))), {==},
          +eb => par.here(Bk.Term.All{q, y, z}, m, ps, fi, nx, r, c, D.Fd(2n, m, r), 6, 3, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.All{q, y, z}, 6, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.All{q, y, z}, tbl), CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, r), c), Bool.or(U32.is_eq(D.Fd(3n, m, r), c), False{}), eb), sy, eb),
          eb => par.up(y, D.Fd(2n, m, r), Bk.Term.All{q, y, z}, m, ps, fi, nx, r, c, node.par(y, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(2n, m, r), c, hy, e, eb), +g => hg => in.l(U32.is_eq(r, g), D.Node(y, m, D.Fd(2n, m, r), g), D.Node(z, m, D.Fd(3n, m, r), g), hg))),
        e => bool.case(U32.is_eq(D.Fd(3n, m, r), c), U32.is_eq(D.Fd(3n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.All{q, y, z}, m, r, g) == True{} : Bool}, D.P2({D.Mem(D.Fs(m, ps, g), c) == True{} : Bool}, D.Sp(fi, nx, g, Cr.Cir.Cells.get(m, c))))), {==},
          +eb => par.here(Bk.Term.All{q, y, z}, m, ps, fi, nx, r, c, D.Fd(3n, m, r), 6, 3, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.All{q, y, z}, 6, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.All{q, y, z}, tbl), CK.Bo.or_ir(U32.is_eq(D.Fd(2n, m, r), c), Bool.or(U32.is_eq(D.Fd(3n, m, r), c), False{}), CK.Bo.or_il(U32.is_eq(D.Fd(3n, m, r), c), False{}, eb)), sz, eb),
          eb => par.up(z, D.Fd(3n, m, r), Bk.Term.All{q, y, z}, m, ps, fi, nx, r, c, node.par(z, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(3n, m, r), c, hz, e, eb), +g => hg => in.r(U32.is_eq(r, g), D.Node(y, m, D.Fd(2n, m, r), g), D.Node(z, m, D.Fd(3n, m, r), g), hg))))
    case Bk.Term.Lam{+q, +y}:
      (+nd, w0) = h
      (hq, w2) = w0
      (sy, hy) = w2
      par.one(D.Node(y, m, D.Fd(2n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Lam{q, y}, m, r, g) == True{} : Bool}, D.P2({D.Mem(D.Fs(m, ps, g), c) == True{} : Bool}, D.Sp(fi, nx, g, Cr.Cir.Cells.get(m, c))))), or.drop(U32.is_eq(r, c), D.Node(y, m, D.Fd(2n, m, r), c), hn, hne),
        e => bool.case(U32.is_eq(D.Fd(2n, m, r), c), U32.is_eq(D.Fd(2n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Lam{q, y}, m, r, g) == True{} : Bool}, D.P2({D.Mem(D.Fs(m, ps, g), c) == True{} : Bool}, D.Sp(fi, nx, g, Cr.Cir.Cells.get(m, c))))), {==},
          +eb => par.here(Bk.Term.Lam{q, y}, m, ps, fi, nx, r, c, D.Fd(2n, m, r), 7, 1, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Lam{q, y}, 7, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Lam{q, y}, tbl), CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, r), c), False{}, eb), sy, eb),
          eb => par.up(y, D.Fd(2n, m, r), Bk.Term.Lam{q, y}, m, ps, fi, nx, r, c, node.par(y, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(2n, m, r), c, hy, e, eb), +g => hg => CK.Bo.or_ir(U32.is_eq(r, g), D.Node(y, m, D.Fd(2n, m, r), g), hg))))
    case Bk.Term.App{+q, +y, +z}:
      (+nd, w0) = h
      (hq, w2) = w0
      (py, pz) = w2
      (sy, hy) = py
      (sz, hz) = pz
      D.or.cases(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.App{q, y, z}, m, r, g) == True{} : Bool}, D.P2({D.Mem(D.Fs(m, ps, g), c) == True{} : Bool}, D.Sp(fi, nx, g, Cr.Cir.Cells.get(m, c))))), or.drop(U32.is_eq(r, c), Bool.or(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c)), hn, hne),
        e => bool.case(U32.is_eq(D.Fd(2n, m, r), c), U32.is_eq(D.Fd(2n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.App{q, y, z}, m, r, g) == True{} : Bool}, D.P2({D.Mem(D.Fs(m, ps, g), c) == True{} : Bool}, D.Sp(fi, nx, g, Cr.Cir.Cells.get(m, c))))), {==},
          +eb => par.here(Bk.Term.App{q, y, z}, m, ps, fi, nx, r, c, D.Fd(2n, m, r), 8, 3, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.App{q, y, z}, 8, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.App{q, y, z}, tbl), CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, r), c), Bool.or(U32.is_eq(D.Fd(3n, m, r), c), False{}), eb), sy, eb),
          eb => par.up(y, D.Fd(2n, m, r), Bk.Term.App{q, y, z}, m, ps, fi, nx, r, c, node.par(y, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(2n, m, r), c, hy, e, eb), +g => hg => in.l(U32.is_eq(r, g), D.Node(y, m, D.Fd(2n, m, r), g), D.Node(z, m, D.Fd(3n, m, r), g), hg))),
        e => bool.case(U32.is_eq(D.Fd(3n, m, r), c), U32.is_eq(D.Fd(3n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.App{q, y, z}, m, r, g) == True{} : Bool}, D.P2({D.Mem(D.Fs(m, ps, g), c) == True{} : Bool}, D.Sp(fi, nx, g, Cr.Cir.Cells.get(m, c))))), {==},
          +eb => par.here(Bk.Term.App{q, y, z}, m, ps, fi, nx, r, c, D.Fd(3n, m, r), 8, 3, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.App{q, y, z}, 8, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.App{q, y, z}, tbl), CK.Bo.or_ir(U32.is_eq(D.Fd(2n, m, r), c), Bool.or(U32.is_eq(D.Fd(3n, m, r), c), False{}), CK.Bo.or_il(U32.is_eq(D.Fd(3n, m, r), c), False{}, eb)), sz, eb),
          eb => par.up(z, D.Fd(3n, m, r), Bk.Term.App{q, y, z}, m, ps, fi, nx, r, c, node.par(z, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(3n, m, r), c, hz, e, eb), +g => hg => in.r(U32.is_eq(r, g), D.Node(y, m, D.Fd(2n, m, r), g), D.Node(z, m, D.Fd(3n, m, r), g), hg))))
    case Bk.Term.Sig{+q, +y, +z}:
      (+nd, w0) = h
      (hq, w2) = w0
      (py, pz) = w2
      (sy, hy) = py
      (sz, hz) = pz
      D.or.cases(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Sig{q, y, z}, m, r, g) == True{} : Bool}, D.P2({D.Mem(D.Fs(m, ps, g), c) == True{} : Bool}, D.Sp(fi, nx, g, Cr.Cir.Cells.get(m, c))))), or.drop(U32.is_eq(r, c), Bool.or(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c)), hn, hne),
        e => bool.case(U32.is_eq(D.Fd(2n, m, r), c), U32.is_eq(D.Fd(2n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Sig{q, y, z}, m, r, g) == True{} : Bool}, D.P2({D.Mem(D.Fs(m, ps, g), c) == True{} : Bool}, D.Sp(fi, nx, g, Cr.Cir.Cells.get(m, c))))), {==},
          +eb => par.here(Bk.Term.Sig{q, y, z}, m, ps, fi, nx, r, c, D.Fd(2n, m, r), 9, 3, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Sig{q, y, z}, 9, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Sig{q, y, z}, tbl), CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, r), c), Bool.or(U32.is_eq(D.Fd(3n, m, r), c), False{}), eb), sy, eb),
          eb => par.up(y, D.Fd(2n, m, r), Bk.Term.Sig{q, y, z}, m, ps, fi, nx, r, c, node.par(y, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(2n, m, r), c, hy, e, eb), +g => hg => in.l(U32.is_eq(r, g), D.Node(y, m, D.Fd(2n, m, r), g), D.Node(z, m, D.Fd(3n, m, r), g), hg))),
        e => bool.case(U32.is_eq(D.Fd(3n, m, r), c), U32.is_eq(D.Fd(3n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Sig{q, y, z}, m, r, g) == True{} : Bool}, D.P2({D.Mem(D.Fs(m, ps, g), c) == True{} : Bool}, D.Sp(fi, nx, g, Cr.Cir.Cells.get(m, c))))), {==},
          +eb => par.here(Bk.Term.Sig{q, y, z}, m, ps, fi, nx, r, c, D.Fd(3n, m, r), 9, 3, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Sig{q, y, z}, 9, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Sig{q, y, z}, tbl), CK.Bo.or_ir(U32.is_eq(D.Fd(2n, m, r), c), Bool.or(U32.is_eq(D.Fd(3n, m, r), c), False{}), CK.Bo.or_il(U32.is_eq(D.Fd(3n, m, r), c), False{}, eb)), sz, eb),
          eb => par.up(z, D.Fd(3n, m, r), Bk.Term.Sig{q, y, z}, m, ps, fi, nx, r, c, node.par(z, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(3n, m, r), c, hz, e, eb), +g => hg => in.r(U32.is_eq(r, g), D.Node(y, m, D.Fd(2n, m, r), g), D.Node(z, m, D.Fd(3n, m, r), g), hg))))
    case Bk.Term.Tup{+q, +y, +z}:
      (+nd, w0) = h
      (hq, w2) = w0
      (py, pz) = w2
      (sy, hy) = py
      (sz, hz) = pz
      D.or.cases(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Tup{q, y, z}, m, r, g) == True{} : Bool}, D.P2({D.Mem(D.Fs(m, ps, g), c) == True{} : Bool}, D.Sp(fi, nx, g, Cr.Cir.Cells.get(m, c))))), or.drop(U32.is_eq(r, c), Bool.or(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c)), hn, hne),
        e => bool.case(U32.is_eq(D.Fd(2n, m, r), c), U32.is_eq(D.Fd(2n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Tup{q, y, z}, m, r, g) == True{} : Bool}, D.P2({D.Mem(D.Fs(m, ps, g), c) == True{} : Bool}, D.Sp(fi, nx, g, Cr.Cir.Cells.get(m, c))))), {==},
          +eb => par.here(Bk.Term.Tup{q, y, z}, m, ps, fi, nx, r, c, D.Fd(2n, m, r), 10, 3, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Tup{q, y, z}, 10, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Tup{q, y, z}, tbl), CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, r), c), Bool.or(U32.is_eq(D.Fd(3n, m, r), c), False{}), eb), sy, eb),
          eb => par.up(y, D.Fd(2n, m, r), Bk.Term.Tup{q, y, z}, m, ps, fi, nx, r, c, node.par(y, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(2n, m, r), c, hy, e, eb), +g => hg => in.l(U32.is_eq(r, g), D.Node(y, m, D.Fd(2n, m, r), g), D.Node(z, m, D.Fd(3n, m, r), g), hg))),
        e => bool.case(U32.is_eq(D.Fd(3n, m, r), c), U32.is_eq(D.Fd(3n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Tup{q, y, z}, m, r, g) == True{} : Bool}, D.P2({D.Mem(D.Fs(m, ps, g), c) == True{} : Bool}, D.Sp(fi, nx, g, Cr.Cir.Cells.get(m, c))))), {==},
          +eb => par.here(Bk.Term.Tup{q, y, z}, m, ps, fi, nx, r, c, D.Fd(3n, m, r), 10, 3, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Tup{q, y, z}, 10, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Tup{q, y, z}, tbl), CK.Bo.or_ir(U32.is_eq(D.Fd(2n, m, r), c), Bool.or(U32.is_eq(D.Fd(3n, m, r), c), False{}), CK.Bo.or_il(U32.is_eq(D.Fd(3n, m, r), c), False{}, eb)), sz, eb),
          eb => par.up(z, D.Fd(3n, m, r), Bk.Term.Tup{q, y, z}, m, ps, fi, nx, r, c, node.par(z, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(3n, m, r), c, hz, e, eb), +g => hg => in.r(U32.is_eq(r, g), D.Node(y, m, D.Fd(2n, m, r), g), D.Node(z, m, D.Fd(3n, m, r), g), hg))))
    case Bk.Term.Prj{+y}:
      (+nd, w0) = h
      (sy, hy) = w0
      par.one(D.Node(y, m, D.Fd(2n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Prj{y}, m, r, g) == True{} : Bool}, D.P2({D.Mem(D.Fs(m, ps, g), c) == True{} : Bool}, D.Sp(fi, nx, g, Cr.Cir.Cells.get(m, c))))), or.drop(U32.is_eq(r, c), D.Node(y, m, D.Fd(2n, m, r), c), hn, hne),
        e => bool.case(U32.is_eq(D.Fd(2n, m, r), c), U32.is_eq(D.Fd(2n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Prj{y}, m, r, g) == True{} : Bool}, D.P2({D.Mem(D.Fs(m, ps, g), c) == True{} : Bool}, D.Sp(fi, nx, g, Cr.Cir.Cells.get(m, c))))), {==},
          +eb => par.here(Bk.Term.Prj{y}, m, ps, fi, nx, r, c, D.Fd(2n, m, r), 11, 1, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Prj{y}, 11, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Prj{y}, tbl), CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, r), c), False{}, eb), sy, eb),
          eb => par.up(y, D.Fd(2n, m, r), Bk.Term.Prj{y}, m, ps, fi, nx, r, c, node.par(y, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(2n, m, r), c, hy, e, eb), +g => hg => CK.Bo.or_ir(U32.is_eq(r, g), D.Node(y, m, D.Fd(2n, m, r), g), hg))))
    case Bk.Term.Enu{+e}:
      CK.Bo.tf(D.Ex(U32, g => D.P2({D.Node(Bk.Term.Enu{e}, m, r, g) == True{} : Bool}, D.P2({D.Mem(D.Fs(m, ps, g), c) == True{} : Bool}, D.Sp(fi, nx, g, Cr.Cir.Cells.get(m, c))))), Equal.trans(Bool, False{}, U32.is_eq(r, c), True{}, Equal.sym(Bool, U32.is_eq(r, c), False{}, hne), hn))
    case Bk.Term.Lab{+k}:
      CK.Bo.tf(D.Ex(U32, g => D.P2({D.Node(Bk.Term.Lab{k}, m, r, g) == True{} : Bool}, D.P2({D.Mem(D.Fs(m, ps, g), c) == True{} : Bool}, D.Sp(fi, nx, g, Cr.Cir.Cells.get(m, c))))), Equal.trans(Bool, False{}, U32.is_eq(r, c), True{}, Equal.sym(Bool, U32.is_eq(r, c), False{}, hne), hn))
    case Bk.Term.Mat{+k, +y, +z}:
      (+nd, w0) = h
      (nm, w2) = w0
      (py, pz) = w2
      (sy, hy) = py
      (sz, hz) = pz
      D.or.cases(D.Node(y, m, D.Fd(3n, m, r), c), D.Node(z, m, D.Fd(4n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Mat{k, y, z}, m, r, g) == True{} : Bool}, D.P2({D.Mem(D.Fs(m, ps, g), c) == True{} : Bool}, D.Sp(fi, nx, g, Cr.Cir.Cells.get(m, c))))), or.drop(U32.is_eq(r, c), Bool.or(D.Node(y, m, D.Fd(3n, m, r), c), D.Node(z, m, D.Fd(4n, m, r), c)), hn, hne),
        e => bool.case(U32.is_eq(D.Fd(3n, m, r), c), U32.is_eq(D.Fd(3n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Mat{k, y, z}, m, r, g) == True{} : Bool}, D.P2({D.Mem(D.Fs(m, ps, g), c) == True{} : Bool}, D.Sp(fi, nx, g, Cr.Cir.Cells.get(m, c))))), {==},
          +eb => par.here(Bk.Term.Mat{k, y, z}, m, ps, fi, nx, r, c, D.Fd(3n, m, r), 14, 6, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Mat{k, y, z}, 14, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Mat{k, y, z}, tbl), CK.Bo.or_il(U32.is_eq(D.Fd(3n, m, r), c), Bool.or(U32.is_eq(D.Fd(4n, m, r), c), False{}), eb), sy, eb),
          eb => par.up(y, D.Fd(3n, m, r), Bk.Term.Mat{k, y, z}, m, ps, fi, nx, r, c, node.par(y, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(3n, m, r), c, hy, e, eb), +g => hg => in.l(U32.is_eq(r, g), D.Node(y, m, D.Fd(3n, m, r), g), D.Node(z, m, D.Fd(4n, m, r), g), hg))),
        e => bool.case(U32.is_eq(D.Fd(4n, m, r), c), U32.is_eq(D.Fd(4n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Mat{k, y, z}, m, r, g) == True{} : Bool}, D.P2({D.Mem(D.Fs(m, ps, g), c) == True{} : Bool}, D.Sp(fi, nx, g, Cr.Cir.Cells.get(m, c))))), {==},
          +eb => par.here(Bk.Term.Mat{k, y, z}, m, ps, fi, nx, r, c, D.Fd(4n, m, r), 14, 6, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Mat{k, y, z}, 14, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Mat{k, y, z}, tbl), CK.Bo.or_ir(U32.is_eq(D.Fd(3n, m, r), c), Bool.or(U32.is_eq(D.Fd(4n, m, r), c), False{}), CK.Bo.or_il(U32.is_eq(D.Fd(4n, m, r), c), False{}, eb)), sz, eb),
          eb => par.up(z, D.Fd(4n, m, r), Bk.Term.Mat{k, y, z}, m, ps, fi, nx, r, c, node.par(z, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(4n, m, r), c, hz, e, eb), +g => hg => in.r(U32.is_eq(r, g), D.Node(y, m, D.Fd(3n, m, r), g), D.Node(z, m, D.Fd(4n, m, r), g), hg))))
    case Bk.Term.Efq{}:
      CK.Bo.tf(D.Ex(U32, g => D.P2({D.Node(Bk.Term.Efq{}, m, r, g) == True{} : Bool}, D.P2({D.Mem(D.Fs(m, ps, g), c) == True{} : Bool}, D.Sp(fi, nx, g, Cr.Cir.Cells.get(m, c))))), Equal.trans(Bool, False{}, U32.is_eq(r, c), True{}, Equal.sym(Bool, U32.is_eq(r, c), False{}, hne), hn))
    case Bk.Term.Eql{+y, +z, +w}:
      (+nd, w0) = h
      (py, w2) = w0
      (sy, hy) = py
      (pz, pw) = w2
      (sz, hz) = pz
      (sw, hw) = pw
      or3.case(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c), D.Node(w, m, D.Fd(4n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Eql{y, z, w}, m, r, g) == True{} : Bool}, D.P2({D.Mem(D.Fs(m, ps, g), c) == True{} : Bool}, D.Sp(fi, nx, g, Cr.Cir.Cells.get(m, c))))), or.drop(U32.is_eq(r, c), Bool.or(D.Node(y, m, D.Fd(2n, m, r), c), Bool.or(D.Node(z, m, D.Fd(3n, m, r), c), D.Node(w, m, D.Fd(4n, m, r), c))), hn, hne),
        e => bool.case(U32.is_eq(D.Fd(2n, m, r), c), U32.is_eq(D.Fd(2n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Eql{y, z, w}, m, r, g) == True{} : Bool}, D.P2({D.Mem(D.Fs(m, ps, g), c) == True{} : Bool}, D.Sp(fi, nx, g, Cr.Cir.Cells.get(m, c))))), {==},
          +eb => par.here(Bk.Term.Eql{y, z, w}, m, ps, fi, nx, r, c, D.Fd(2n, m, r), 16, 7, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Eql{y, z, w}, 16, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Eql{y, z, w}, tbl), CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, r), c), Bool.or(U32.is_eq(D.Fd(3n, m, r), c), Bool.or(U32.is_eq(D.Fd(4n, m, r), c), False{})), eb), sy, eb),
          eb => par.up(y, D.Fd(2n, m, r), Bk.Term.Eql{y, z, w}, m, ps, fi, nx, r, c, node.par(y, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(2n, m, r), c, hy, e, eb), +g => hg => in.a(U32.is_eq(r, g), D.Node(y, m, D.Fd(2n, m, r), g), D.Node(z, m, D.Fd(3n, m, r), g), D.Node(w, m, D.Fd(4n, m, r), g), hg))),
        e => bool.case(U32.is_eq(D.Fd(3n, m, r), c), U32.is_eq(D.Fd(3n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Eql{y, z, w}, m, r, g) == True{} : Bool}, D.P2({D.Mem(D.Fs(m, ps, g), c) == True{} : Bool}, D.Sp(fi, nx, g, Cr.Cir.Cells.get(m, c))))), {==},
          +eb => par.here(Bk.Term.Eql{y, z, w}, m, ps, fi, nx, r, c, D.Fd(3n, m, r), 16, 7, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Eql{y, z, w}, 16, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Eql{y, z, w}, tbl), CK.Bo.or_ir(U32.is_eq(D.Fd(2n, m, r), c), Bool.or(U32.is_eq(D.Fd(3n, m, r), c), Bool.or(U32.is_eq(D.Fd(4n, m, r), c), False{})), CK.Bo.or_il(U32.is_eq(D.Fd(3n, m, r), c), Bool.or(U32.is_eq(D.Fd(4n, m, r), c), False{}), eb)), sz, eb),
          eb => par.up(z, D.Fd(3n, m, r), Bk.Term.Eql{y, z, w}, m, ps, fi, nx, r, c, node.par(z, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(3n, m, r), c, hz, e, eb), +g => hg => in.b(U32.is_eq(r, g), D.Node(y, m, D.Fd(2n, m, r), g), D.Node(z, m, D.Fd(3n, m, r), g), D.Node(w, m, D.Fd(4n, m, r), g), hg))),
        e => bool.case(U32.is_eq(D.Fd(4n, m, r), c), U32.is_eq(D.Fd(4n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Eql{y, z, w}, m, r, g) == True{} : Bool}, D.P2({D.Mem(D.Fs(m, ps, g), c) == True{} : Bool}, D.Sp(fi, nx, g, Cr.Cir.Cells.get(m, c))))), {==},
          +eb => par.here(Bk.Term.Eql{y, z, w}, m, ps, fi, nx, r, c, D.Fd(4n, m, r), 16, 7, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Eql{y, z, w}, 16, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Eql{y, z, w}, tbl), CK.Bo.or_ir(U32.is_eq(D.Fd(2n, m, r), c), Bool.or(U32.is_eq(D.Fd(3n, m, r), c), Bool.or(U32.is_eq(D.Fd(4n, m, r), c), False{})), CK.Bo.or_ir(U32.is_eq(D.Fd(3n, m, r), c), Bool.or(U32.is_eq(D.Fd(4n, m, r), c), False{}), CK.Bo.or_il(U32.is_eq(D.Fd(4n, m, r), c), False{}, eb))), sw, eb),
          eb => par.up(w, D.Fd(4n, m, r), Bk.Term.Eql{y, z, w}, m, ps, fi, nx, r, c, node.par(w, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(4n, m, r), c, hw, e, eb), +g => hg => in.c(U32.is_eq(r, g), D.Node(y, m, D.Fd(2n, m, r), g), D.Node(z, m, D.Fd(3n, m, r), g), D.Node(w, m, D.Fd(4n, m, r), g), hg))))
    case Bk.Term.Rfl{}:
      CK.Bo.tf(D.Ex(U32, g => D.P2({D.Node(Bk.Term.Rfl{}, m, r, g) == True{} : Bool}, D.P2({D.Mem(D.Fs(m, ps, g), c) == True{} : Bool}, D.Sp(fi, nx, g, Cr.Cir.Cells.get(m, c))))), Equal.trans(Bool, False{}, U32.is_eq(r, c), True{}, Equal.sym(Bool, U32.is_eq(r, c), False{}, hne), hn))
    case Bk.Term.Rwt{+y, +z, +w}:
      (+nd, w0) = h
      (py, w2) = w0
      (sy, hy) = py
      (pz, pw) = w2
      (sz, hz) = pz
      (sw, hw) = pw
      or3.case(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c), D.Node(w, m, D.Fd(4n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Rwt{y, z, w}, m, r, g) == True{} : Bool}, D.P2({D.Mem(D.Fs(m, ps, g), c) == True{} : Bool}, D.Sp(fi, nx, g, Cr.Cir.Cells.get(m, c))))), or.drop(U32.is_eq(r, c), Bool.or(D.Node(y, m, D.Fd(2n, m, r), c), Bool.or(D.Node(z, m, D.Fd(3n, m, r), c), D.Node(w, m, D.Fd(4n, m, r), c))), hn, hne),
        e => bool.case(U32.is_eq(D.Fd(2n, m, r), c), U32.is_eq(D.Fd(2n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Rwt{y, z, w}, m, r, g) == True{} : Bool}, D.P2({D.Mem(D.Fs(m, ps, g), c) == True{} : Bool}, D.Sp(fi, nx, g, Cr.Cir.Cells.get(m, c))))), {==},
          +eb => par.here(Bk.Term.Rwt{y, z, w}, m, ps, fi, nx, r, c, D.Fd(2n, m, r), 18, 7, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Rwt{y, z, w}, 18, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Rwt{y, z, w}, tbl), CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, r), c), Bool.or(U32.is_eq(D.Fd(3n, m, r), c), Bool.or(U32.is_eq(D.Fd(4n, m, r), c), False{})), eb), sy, eb),
          eb => par.up(y, D.Fd(2n, m, r), Bk.Term.Rwt{y, z, w}, m, ps, fi, nx, r, c, node.par(y, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(2n, m, r), c, hy, e, eb), +g => hg => in.a(U32.is_eq(r, g), D.Node(y, m, D.Fd(2n, m, r), g), D.Node(z, m, D.Fd(3n, m, r), g), D.Node(w, m, D.Fd(4n, m, r), g), hg))),
        e => bool.case(U32.is_eq(D.Fd(3n, m, r), c), U32.is_eq(D.Fd(3n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Rwt{y, z, w}, m, r, g) == True{} : Bool}, D.P2({D.Mem(D.Fs(m, ps, g), c) == True{} : Bool}, D.Sp(fi, nx, g, Cr.Cir.Cells.get(m, c))))), {==},
          +eb => par.here(Bk.Term.Rwt{y, z, w}, m, ps, fi, nx, r, c, D.Fd(3n, m, r), 18, 7, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Rwt{y, z, w}, 18, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Rwt{y, z, w}, tbl), CK.Bo.or_ir(U32.is_eq(D.Fd(2n, m, r), c), Bool.or(U32.is_eq(D.Fd(3n, m, r), c), Bool.or(U32.is_eq(D.Fd(4n, m, r), c), False{})), CK.Bo.or_il(U32.is_eq(D.Fd(3n, m, r), c), Bool.or(U32.is_eq(D.Fd(4n, m, r), c), False{}), eb)), sz, eb),
          eb => par.up(z, D.Fd(3n, m, r), Bk.Term.Rwt{y, z, w}, m, ps, fi, nx, r, c, node.par(z, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(3n, m, r), c, hz, e, eb), +g => hg => in.b(U32.is_eq(r, g), D.Node(y, m, D.Fd(2n, m, r), g), D.Node(z, m, D.Fd(3n, m, r), g), D.Node(w, m, D.Fd(4n, m, r), g), hg))),
        e => bool.case(U32.is_eq(D.Fd(4n, m, r), c), U32.is_eq(D.Fd(4n, m, r), c), D.Ex(U32, g => D.P2({D.Node(Bk.Term.Rwt{y, z, w}, m, r, g) == True{} : Bool}, D.P2({D.Mem(D.Fs(m, ps, g), c) == True{} : Bool}, D.Sp(fi, nx, g, Cr.Cir.Cells.get(m, c))))), {==},
          +eb => par.here(Bk.Term.Rwt{y, z, w}, m, ps, fi, nx, r, c, D.Fd(4n, m, r), 18, 7, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Rwt{y, z, w}, 18, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Rwt{y, z, w}, tbl), CK.Bo.or_ir(U32.is_eq(D.Fd(2n, m, r), c), Bool.or(U32.is_eq(D.Fd(3n, m, r), c), Bool.or(U32.is_eq(D.Fd(4n, m, r), c), False{})), CK.Bo.or_ir(U32.is_eq(D.Fd(3n, m, r), c), Bool.or(U32.is_eq(D.Fd(4n, m, r), c), False{}), CK.Bo.or_il(U32.is_eq(D.Fd(4n, m, r), c), False{}, eb))), sw, eb),
          eb => par.up(w, D.Fd(4n, m, r), Bk.Term.Rwt{y, z, w}, m, ps, fi, nx, r, c, node.par(w, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(4n, m, r), c, hw, e, eb), +g => hg => in.c(U32.is_eq(r, g), D.Node(y, m, D.Fd(2n, m, r), g), D.Node(z, m, D.Fd(3n, m, r), g), D.Node(w, m, D.Fd(4n, m, r), g), hg))))

# a pointer v of a node c of the term t at r is a node of t: its pointers are
# its parts, by its tag's mask
def node.fs(t: Bk.Term, +dk: Bool, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +tbl: D.Tbl(m, im, fi, nx), +r: U32, +c: U32, +v: U32,
  h: D.IsK(dk, ds, m, im, fi, nx, ks, img, r, t), hn: {D.Node(t, m, r, c) == True{} : Bool},
  +hv: {D.Mem(D.Fs(m, ps, c), v) == True{} : Bool}) -> {D.Node(t, m, r, v) == True{} : Bool}:
  match t:
    case Bk.Term.Var{+i}:
      (+nd, w0) = h
      fs.leaf({D.Node(Bk.Term.Var{i}, m, r, v) == True{} : Bool}, dk, ds, m, im, fi, nx, ps, r, c, v, Bk.Term.Var{i}, 0, nd, {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Var{i}, tbl), hn, hv)
    case Bk.Term.Ref{+k}:
      (+nd, w0) = h
      fs.leaf({D.Node(Bk.Term.Ref{k}, m, r, v) == True{} : Bool}, dk, ds, m, im, fi, nx, ps, r, c, v, Bk.Term.Ref{k}, 1, nd, {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Ref{k}, tbl), hn, hv)
    case Bk.Term.Ann{+y, +z}:
      (+nd, w0) = h
      (py, pz) = w0
      (sy, hy) = py
      (sz, hz) = pz
      or3.case(U32.is_eq(r, c), D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c), {D.Node(Bk.Term.Ann{y, z}, m, r, v) == True{} : Bool}, hn,
        e => D.or.cases(U32.is_eq(D.Fd(2n, m, r), v), Bool.or(U32.is_eq(D.Fd(3n, m, r), v), False{}), {D.Node(Bk.Term.Ann{y, z}, m, r, v) == True{} : Bool}, (%D.fs.term(m, ps, r, 2, 3, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Ann{y, z}, 2, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Ann{y, z}, tbl)) : {D.Mem(_, v) == True{} : Bool}; (%Equal.sym(U32, r, c, CK.U.eq(r, c, e)) : {D.Mem(D.Fs(m, ps, _), v) == True{} : Bool}; hv)), e0 => in.l(U32.is_eq(r, v), D.Node(y, m, D.Fd(2n, m, r), v), D.Node(z, m, D.Fd(3n, m, r), v), (%CK.U.eq(D.Fd(2n, m, r), v, e0) : {D.Node(y, m, D.Fd(2n, m, r), _) == True{} : Bool}; node.root(y, m, D.Fd(2n, m, r)))), e0 => D.or.cases(U32.is_eq(D.Fd(3n, m, r), v), False{}, {D.Node(Bk.Term.Ann{y, z}, m, r, v) == True{} : Bool}, e0, e1 => in.r(U32.is_eq(r, v), D.Node(y, m, D.Fd(2n, m, r), v), D.Node(z, m, D.Fd(3n, m, r), v), (%CK.U.eq(D.Fd(3n, m, r), v, e1) : {D.Node(z, m, D.Fd(3n, m, r), _) == True{} : Bool}; node.root(z, m, D.Fd(3n, m, r)))), e1 => CK.Bo.tf({D.Node(Bk.Term.Ann{y, z}, m, r, v) == True{} : Bool}, e1))),
        e => in.l(U32.is_eq(r, v), D.Node(y, m, D.Fd(2n, m, r), v), D.Node(z, m, D.Fd(3n, m, r), v), node.fs(y, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(2n, m, r), c, v, hy, e, hv)),
        e => in.r(U32.is_eq(r, v), D.Node(y, m, D.Fd(2n, m, r), v), D.Node(z, m, D.Fd(3n, m, r), v), node.fs(z, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(3n, m, r), c, v, hz, e, hv)))
    case Bk.Term.Let{+q, +y, +z}:
      (+nd, w0) = h
      (hq, w2) = w0
      (py, pz) = w2
      (sy, hy) = py
      (sz, hz) = pz
      or3.case(U32.is_eq(r, c), D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c), {D.Node(Bk.Term.Let{q, y, z}, m, r, v) == True{} : Bool}, hn,
        e => D.or.cases(U32.is_eq(D.Fd(2n, m, r), v), Bool.or(U32.is_eq(D.Fd(3n, m, r), v), False{}), {D.Node(Bk.Term.Let{q, y, z}, m, r, v) == True{} : Bool}, (%D.fs.term(m, ps, r, 3, 3, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Let{q, y, z}, 3, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Let{q, y, z}, tbl)) : {D.Mem(_, v) == True{} : Bool}; (%Equal.sym(U32, r, c, CK.U.eq(r, c, e)) : {D.Mem(D.Fs(m, ps, _), v) == True{} : Bool}; hv)), e0 => in.l(U32.is_eq(r, v), D.Node(y, m, D.Fd(2n, m, r), v), D.Node(z, m, D.Fd(3n, m, r), v), (%CK.U.eq(D.Fd(2n, m, r), v, e0) : {D.Node(y, m, D.Fd(2n, m, r), _) == True{} : Bool}; node.root(y, m, D.Fd(2n, m, r)))), e0 => D.or.cases(U32.is_eq(D.Fd(3n, m, r), v), False{}, {D.Node(Bk.Term.Let{q, y, z}, m, r, v) == True{} : Bool}, e0, e1 => in.r(U32.is_eq(r, v), D.Node(y, m, D.Fd(2n, m, r), v), D.Node(z, m, D.Fd(3n, m, r), v), (%CK.U.eq(D.Fd(3n, m, r), v, e1) : {D.Node(z, m, D.Fd(3n, m, r), _) == True{} : Bool}; node.root(z, m, D.Fd(3n, m, r)))), e1 => CK.Bo.tf({D.Node(Bk.Term.Let{q, y, z}, m, r, v) == True{} : Bool}, e1))),
        e => in.l(U32.is_eq(r, v), D.Node(y, m, D.Fd(2n, m, r), v), D.Node(z, m, D.Fd(3n, m, r), v), node.fs(y, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(2n, m, r), c, v, hy, e, hv)),
        e => in.r(U32.is_eq(r, v), D.Node(y, m, D.Fd(2n, m, r), v), D.Node(z, m, D.Fd(3n, m, r), v), node.fs(z, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(3n, m, r), c, v, hz, e, hv)))
    case Bk.Term.Typ{+y}:
      (+nd, w0) = h
      (sy, hy) = w0
      D.or.cases(U32.is_eq(r, c), D.Node(y, m, D.Fd(2n, m, r), c), {D.Node(Bk.Term.Typ{y}, m, r, v) == True{} : Bool}, hn,
        e => D.or.cases(U32.is_eq(D.Fd(2n, m, r), v), False{}, {D.Node(Bk.Term.Typ{y}, m, r, v) == True{} : Bool}, (%D.fs.term(m, ps, r, 4, 1, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Typ{y}, 4, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Typ{y}, tbl)) : {D.Mem(_, v) == True{} : Bool}; (%Equal.sym(U32, r, c, CK.U.eq(r, c, e)) : {D.Mem(D.Fs(m, ps, _), v) == True{} : Bool}; hv)), e0 => CK.Bo.or_ir(U32.is_eq(r, v), D.Node(y, m, D.Fd(2n, m, r), v), (%CK.U.eq(D.Fd(2n, m, r), v, e0) : {D.Node(y, m, D.Fd(2n, m, r), _) == True{} : Bool}; node.root(y, m, D.Fd(2n, m, r)))), e0 => CK.Bo.tf({D.Node(Bk.Term.Typ{y}, m, r, v) == True{} : Bool}, e0)),
        e => CK.Bo.or_ir(U32.is_eq(r, v), D.Node(y, m, D.Fd(2n, m, r), v), node.fs(y, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(2n, m, r), c, v, hy, e, hv)))
    case Bk.Term.Min{+y, +z}:
      (+nd, w0) = h
      (py, pz) = w0
      (sy, hy) = py
      (sz, hz) = pz
      or3.case(U32.is_eq(r, c), D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c), {D.Node(Bk.Term.Min{y, z}, m, r, v) == True{} : Bool}, hn,
        e => D.or.cases(U32.is_eq(D.Fd(2n, m, r), v), Bool.or(U32.is_eq(D.Fd(3n, m, r), v), False{}), {D.Node(Bk.Term.Min{y, z}, m, r, v) == True{} : Bool}, (%D.fs.term(m, ps, r, 5, 3, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Min{y, z}, 5, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Min{y, z}, tbl)) : {D.Mem(_, v) == True{} : Bool}; (%Equal.sym(U32, r, c, CK.U.eq(r, c, e)) : {D.Mem(D.Fs(m, ps, _), v) == True{} : Bool}; hv)), e0 => in.l(U32.is_eq(r, v), D.Node(y, m, D.Fd(2n, m, r), v), D.Node(z, m, D.Fd(3n, m, r), v), (%CK.U.eq(D.Fd(2n, m, r), v, e0) : {D.Node(y, m, D.Fd(2n, m, r), _) == True{} : Bool}; node.root(y, m, D.Fd(2n, m, r)))), e0 => D.or.cases(U32.is_eq(D.Fd(3n, m, r), v), False{}, {D.Node(Bk.Term.Min{y, z}, m, r, v) == True{} : Bool}, e0, e1 => in.r(U32.is_eq(r, v), D.Node(y, m, D.Fd(2n, m, r), v), D.Node(z, m, D.Fd(3n, m, r), v), (%CK.U.eq(D.Fd(3n, m, r), v, e1) : {D.Node(z, m, D.Fd(3n, m, r), _) == True{} : Bool}; node.root(z, m, D.Fd(3n, m, r)))), e1 => CK.Bo.tf({D.Node(Bk.Term.Min{y, z}, m, r, v) == True{} : Bool}, e1))),
        e => in.l(U32.is_eq(r, v), D.Node(y, m, D.Fd(2n, m, r), v), D.Node(z, m, D.Fd(3n, m, r), v), node.fs(y, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(2n, m, r), c, v, hy, e, hv)),
        e => in.r(U32.is_eq(r, v), D.Node(y, m, D.Fd(2n, m, r), v), D.Node(z, m, D.Fd(3n, m, r), v), node.fs(z, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(3n, m, r), c, v, hz, e, hv)))
    case Bk.Term.All{+q, +y, +z}:
      (+nd, w0) = h
      (hq, w2) = w0
      (py, pz) = w2
      (sy, hy) = py
      (sz, hz) = pz
      or3.case(U32.is_eq(r, c), D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c), {D.Node(Bk.Term.All{q, y, z}, m, r, v) == True{} : Bool}, hn,
        e => D.or.cases(U32.is_eq(D.Fd(2n, m, r), v), Bool.or(U32.is_eq(D.Fd(3n, m, r), v), False{}), {D.Node(Bk.Term.All{q, y, z}, m, r, v) == True{} : Bool}, (%D.fs.term(m, ps, r, 6, 3, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.All{q, y, z}, 6, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.All{q, y, z}, tbl)) : {D.Mem(_, v) == True{} : Bool}; (%Equal.sym(U32, r, c, CK.U.eq(r, c, e)) : {D.Mem(D.Fs(m, ps, _), v) == True{} : Bool}; hv)), e0 => in.l(U32.is_eq(r, v), D.Node(y, m, D.Fd(2n, m, r), v), D.Node(z, m, D.Fd(3n, m, r), v), (%CK.U.eq(D.Fd(2n, m, r), v, e0) : {D.Node(y, m, D.Fd(2n, m, r), _) == True{} : Bool}; node.root(y, m, D.Fd(2n, m, r)))), e0 => D.or.cases(U32.is_eq(D.Fd(3n, m, r), v), False{}, {D.Node(Bk.Term.All{q, y, z}, m, r, v) == True{} : Bool}, e0, e1 => in.r(U32.is_eq(r, v), D.Node(y, m, D.Fd(2n, m, r), v), D.Node(z, m, D.Fd(3n, m, r), v), (%CK.U.eq(D.Fd(3n, m, r), v, e1) : {D.Node(z, m, D.Fd(3n, m, r), _) == True{} : Bool}; node.root(z, m, D.Fd(3n, m, r)))), e1 => CK.Bo.tf({D.Node(Bk.Term.All{q, y, z}, m, r, v) == True{} : Bool}, e1))),
        e => in.l(U32.is_eq(r, v), D.Node(y, m, D.Fd(2n, m, r), v), D.Node(z, m, D.Fd(3n, m, r), v), node.fs(y, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(2n, m, r), c, v, hy, e, hv)),
        e => in.r(U32.is_eq(r, v), D.Node(y, m, D.Fd(2n, m, r), v), D.Node(z, m, D.Fd(3n, m, r), v), node.fs(z, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(3n, m, r), c, v, hz, e, hv)))
    case Bk.Term.Lam{+q, +y}:
      (+nd, w0) = h
      (hq, w2) = w0
      (sy, hy) = w2
      D.or.cases(U32.is_eq(r, c), D.Node(y, m, D.Fd(2n, m, r), c), {D.Node(Bk.Term.Lam{q, y}, m, r, v) == True{} : Bool}, hn,
        e => D.or.cases(U32.is_eq(D.Fd(2n, m, r), v), False{}, {D.Node(Bk.Term.Lam{q, y}, m, r, v) == True{} : Bool}, (%D.fs.term(m, ps, r, 7, 1, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Lam{q, y}, 7, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Lam{q, y}, tbl)) : {D.Mem(_, v) == True{} : Bool}; (%Equal.sym(U32, r, c, CK.U.eq(r, c, e)) : {D.Mem(D.Fs(m, ps, _), v) == True{} : Bool}; hv)), e0 => CK.Bo.or_ir(U32.is_eq(r, v), D.Node(y, m, D.Fd(2n, m, r), v), (%CK.U.eq(D.Fd(2n, m, r), v, e0) : {D.Node(y, m, D.Fd(2n, m, r), _) == True{} : Bool}; node.root(y, m, D.Fd(2n, m, r)))), e0 => CK.Bo.tf({D.Node(Bk.Term.Lam{q, y}, m, r, v) == True{} : Bool}, e0)),
        e => CK.Bo.or_ir(U32.is_eq(r, v), D.Node(y, m, D.Fd(2n, m, r), v), node.fs(y, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(2n, m, r), c, v, hy, e, hv)))
    case Bk.Term.App{+q, +y, +z}:
      (+nd, w0) = h
      (hq, w2) = w0
      (py, pz) = w2
      (sy, hy) = py
      (sz, hz) = pz
      or3.case(U32.is_eq(r, c), D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c), {D.Node(Bk.Term.App{q, y, z}, m, r, v) == True{} : Bool}, hn,
        e => D.or.cases(U32.is_eq(D.Fd(2n, m, r), v), Bool.or(U32.is_eq(D.Fd(3n, m, r), v), False{}), {D.Node(Bk.Term.App{q, y, z}, m, r, v) == True{} : Bool}, (%D.fs.term(m, ps, r, 8, 3, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.App{q, y, z}, 8, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.App{q, y, z}, tbl)) : {D.Mem(_, v) == True{} : Bool}; (%Equal.sym(U32, r, c, CK.U.eq(r, c, e)) : {D.Mem(D.Fs(m, ps, _), v) == True{} : Bool}; hv)), e0 => in.l(U32.is_eq(r, v), D.Node(y, m, D.Fd(2n, m, r), v), D.Node(z, m, D.Fd(3n, m, r), v), (%CK.U.eq(D.Fd(2n, m, r), v, e0) : {D.Node(y, m, D.Fd(2n, m, r), _) == True{} : Bool}; node.root(y, m, D.Fd(2n, m, r)))), e0 => D.or.cases(U32.is_eq(D.Fd(3n, m, r), v), False{}, {D.Node(Bk.Term.App{q, y, z}, m, r, v) == True{} : Bool}, e0, e1 => in.r(U32.is_eq(r, v), D.Node(y, m, D.Fd(2n, m, r), v), D.Node(z, m, D.Fd(3n, m, r), v), (%CK.U.eq(D.Fd(3n, m, r), v, e1) : {D.Node(z, m, D.Fd(3n, m, r), _) == True{} : Bool}; node.root(z, m, D.Fd(3n, m, r)))), e1 => CK.Bo.tf({D.Node(Bk.Term.App{q, y, z}, m, r, v) == True{} : Bool}, e1))),
        e => in.l(U32.is_eq(r, v), D.Node(y, m, D.Fd(2n, m, r), v), D.Node(z, m, D.Fd(3n, m, r), v), node.fs(y, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(2n, m, r), c, v, hy, e, hv)),
        e => in.r(U32.is_eq(r, v), D.Node(y, m, D.Fd(2n, m, r), v), D.Node(z, m, D.Fd(3n, m, r), v), node.fs(z, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(3n, m, r), c, v, hz, e, hv)))
    case Bk.Term.Sig{+q, +y, +z}:
      (+nd, w0) = h
      (hq, w2) = w0
      (py, pz) = w2
      (sy, hy) = py
      (sz, hz) = pz
      or3.case(U32.is_eq(r, c), D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c), {D.Node(Bk.Term.Sig{q, y, z}, m, r, v) == True{} : Bool}, hn,
        e => D.or.cases(U32.is_eq(D.Fd(2n, m, r), v), Bool.or(U32.is_eq(D.Fd(3n, m, r), v), False{}), {D.Node(Bk.Term.Sig{q, y, z}, m, r, v) == True{} : Bool}, (%D.fs.term(m, ps, r, 9, 3, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Sig{q, y, z}, 9, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Sig{q, y, z}, tbl)) : {D.Mem(_, v) == True{} : Bool}; (%Equal.sym(U32, r, c, CK.U.eq(r, c, e)) : {D.Mem(D.Fs(m, ps, _), v) == True{} : Bool}; hv)), e0 => in.l(U32.is_eq(r, v), D.Node(y, m, D.Fd(2n, m, r), v), D.Node(z, m, D.Fd(3n, m, r), v), (%CK.U.eq(D.Fd(2n, m, r), v, e0) : {D.Node(y, m, D.Fd(2n, m, r), _) == True{} : Bool}; node.root(y, m, D.Fd(2n, m, r)))), e0 => D.or.cases(U32.is_eq(D.Fd(3n, m, r), v), False{}, {D.Node(Bk.Term.Sig{q, y, z}, m, r, v) == True{} : Bool}, e0, e1 => in.r(U32.is_eq(r, v), D.Node(y, m, D.Fd(2n, m, r), v), D.Node(z, m, D.Fd(3n, m, r), v), (%CK.U.eq(D.Fd(3n, m, r), v, e1) : {D.Node(z, m, D.Fd(3n, m, r), _) == True{} : Bool}; node.root(z, m, D.Fd(3n, m, r)))), e1 => CK.Bo.tf({D.Node(Bk.Term.Sig{q, y, z}, m, r, v) == True{} : Bool}, e1))),
        e => in.l(U32.is_eq(r, v), D.Node(y, m, D.Fd(2n, m, r), v), D.Node(z, m, D.Fd(3n, m, r), v), node.fs(y, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(2n, m, r), c, v, hy, e, hv)),
        e => in.r(U32.is_eq(r, v), D.Node(y, m, D.Fd(2n, m, r), v), D.Node(z, m, D.Fd(3n, m, r), v), node.fs(z, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(3n, m, r), c, v, hz, e, hv)))
    case Bk.Term.Tup{+q, +y, +z}:
      (+nd, w0) = h
      (hq, w2) = w0
      (py, pz) = w2
      (sy, hy) = py
      (sz, hz) = pz
      or3.case(U32.is_eq(r, c), D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c), {D.Node(Bk.Term.Tup{q, y, z}, m, r, v) == True{} : Bool}, hn,
        e => D.or.cases(U32.is_eq(D.Fd(2n, m, r), v), Bool.or(U32.is_eq(D.Fd(3n, m, r), v), False{}), {D.Node(Bk.Term.Tup{q, y, z}, m, r, v) == True{} : Bool}, (%D.fs.term(m, ps, r, 10, 3, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Tup{q, y, z}, 10, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Tup{q, y, z}, tbl)) : {D.Mem(_, v) == True{} : Bool}; (%Equal.sym(U32, r, c, CK.U.eq(r, c, e)) : {D.Mem(D.Fs(m, ps, _), v) == True{} : Bool}; hv)), e0 => in.l(U32.is_eq(r, v), D.Node(y, m, D.Fd(2n, m, r), v), D.Node(z, m, D.Fd(3n, m, r), v), (%CK.U.eq(D.Fd(2n, m, r), v, e0) : {D.Node(y, m, D.Fd(2n, m, r), _) == True{} : Bool}; node.root(y, m, D.Fd(2n, m, r)))), e0 => D.or.cases(U32.is_eq(D.Fd(3n, m, r), v), False{}, {D.Node(Bk.Term.Tup{q, y, z}, m, r, v) == True{} : Bool}, e0, e1 => in.r(U32.is_eq(r, v), D.Node(y, m, D.Fd(2n, m, r), v), D.Node(z, m, D.Fd(3n, m, r), v), (%CK.U.eq(D.Fd(3n, m, r), v, e1) : {D.Node(z, m, D.Fd(3n, m, r), _) == True{} : Bool}; node.root(z, m, D.Fd(3n, m, r)))), e1 => CK.Bo.tf({D.Node(Bk.Term.Tup{q, y, z}, m, r, v) == True{} : Bool}, e1))),
        e => in.l(U32.is_eq(r, v), D.Node(y, m, D.Fd(2n, m, r), v), D.Node(z, m, D.Fd(3n, m, r), v), node.fs(y, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(2n, m, r), c, v, hy, e, hv)),
        e => in.r(U32.is_eq(r, v), D.Node(y, m, D.Fd(2n, m, r), v), D.Node(z, m, D.Fd(3n, m, r), v), node.fs(z, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(3n, m, r), c, v, hz, e, hv)))
    case Bk.Term.Prj{+y}:
      (+nd, w0) = h
      (sy, hy) = w0
      D.or.cases(U32.is_eq(r, c), D.Node(y, m, D.Fd(2n, m, r), c), {D.Node(Bk.Term.Prj{y}, m, r, v) == True{} : Bool}, hn,
        e => D.or.cases(U32.is_eq(D.Fd(2n, m, r), v), False{}, {D.Node(Bk.Term.Prj{y}, m, r, v) == True{} : Bool}, (%D.fs.term(m, ps, r, 11, 1, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Prj{y}, 11, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Prj{y}, tbl)) : {D.Mem(_, v) == True{} : Bool}; (%Equal.sym(U32, r, c, CK.U.eq(r, c, e)) : {D.Mem(D.Fs(m, ps, _), v) == True{} : Bool}; hv)), e0 => CK.Bo.or_ir(U32.is_eq(r, v), D.Node(y, m, D.Fd(2n, m, r), v), (%CK.U.eq(D.Fd(2n, m, r), v, e0) : {D.Node(y, m, D.Fd(2n, m, r), _) == True{} : Bool}; node.root(y, m, D.Fd(2n, m, r)))), e0 => CK.Bo.tf({D.Node(Bk.Term.Prj{y}, m, r, v) == True{} : Bool}, e0)),
        e => CK.Bo.or_ir(U32.is_eq(r, v), D.Node(y, m, D.Fd(2n, m, r), v), node.fs(y, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(2n, m, r), c, v, hy, e, hv)))
    case Bk.Term.Enu{+e}:
      (+nd, w0) = h
      fs.leaf({D.Node(Bk.Term.Enu{e}, m, r, v) == True{} : Bool}, dk, ds, m, im, fi, nx, ps, r, c, v, Bk.Term.Enu{e}, 12, nd, {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Enu{e}, tbl), hn, hv)
    case Bk.Term.Lab{+k}:
      (+nd, w0) = h
      fs.leaf({D.Node(Bk.Term.Lab{k}, m, r, v) == True{} : Bool}, dk, ds, m, im, fi, nx, ps, r, c, v, Bk.Term.Lab{k}, 13, nd, {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Lab{k}, tbl), hn, hv)
    case Bk.Term.Mat{+k, +y, +z}:
      (+nd, w0) = h
      (nm, w2) = w0
      (py, pz) = w2
      (sy, hy) = py
      (sz, hz) = pz
      or3.case(U32.is_eq(r, c), D.Node(y, m, D.Fd(3n, m, r), c), D.Node(z, m, D.Fd(4n, m, r), c), {D.Node(Bk.Term.Mat{k, y, z}, m, r, v) == True{} : Bool}, hn,
        e => D.or.cases(U32.is_eq(D.Fd(3n, m, r), v), Bool.or(U32.is_eq(D.Fd(4n, m, r), v), False{}), {D.Node(Bk.Term.Mat{k, y, z}, m, r, v) == True{} : Bool}, (%D.fs.term(m, ps, r, 14, 6, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Mat{k, y, z}, 14, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Mat{k, y, z}, tbl)) : {D.Mem(_, v) == True{} : Bool}; (%Equal.sym(U32, r, c, CK.U.eq(r, c, e)) : {D.Mem(D.Fs(m, ps, _), v) == True{} : Bool}; hv)), e0 => in.l(U32.is_eq(r, v), D.Node(y, m, D.Fd(3n, m, r), v), D.Node(z, m, D.Fd(4n, m, r), v), (%CK.U.eq(D.Fd(3n, m, r), v, e0) : {D.Node(y, m, D.Fd(3n, m, r), _) == True{} : Bool}; node.root(y, m, D.Fd(3n, m, r)))), e0 => D.or.cases(U32.is_eq(D.Fd(4n, m, r), v), False{}, {D.Node(Bk.Term.Mat{k, y, z}, m, r, v) == True{} : Bool}, e0, e1 => in.r(U32.is_eq(r, v), D.Node(y, m, D.Fd(3n, m, r), v), D.Node(z, m, D.Fd(4n, m, r), v), (%CK.U.eq(D.Fd(4n, m, r), v, e1) : {D.Node(z, m, D.Fd(4n, m, r), _) == True{} : Bool}; node.root(z, m, D.Fd(4n, m, r)))), e1 => CK.Bo.tf({D.Node(Bk.Term.Mat{k, y, z}, m, r, v) == True{} : Bool}, e1))),
        e => in.l(U32.is_eq(r, v), D.Node(y, m, D.Fd(3n, m, r), v), D.Node(z, m, D.Fd(4n, m, r), v), node.fs(y, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(3n, m, r), c, v, hy, e, hv)),
        e => in.r(U32.is_eq(r, v), D.Node(y, m, D.Fd(3n, m, r), v), D.Node(z, m, D.Fd(4n, m, r), v), node.fs(z, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(4n, m, r), c, v, hz, e, hv)))
    case Bk.Term.Efq{}:
      fs.leaf({D.Node(Bk.Term.Efq{}, m, r, v) == True{} : Bool}, dk, ds, m, im, fi, nx, ps, r, c, v, Bk.Term.Efq{}, 15, h, {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Efq{}, tbl), hn, hv)
    case Bk.Term.Eql{+y, +z, +w}:
      (+nd, w0) = h
      (py, w2) = w0
      (sy, hy) = py
      (pz, pw) = w2
      (sz, hz) = pz
      (sw, hw) = pw
      or4.case(U32.is_eq(r, c), D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c), D.Node(w, m, D.Fd(4n, m, r), c), {D.Node(Bk.Term.Eql{y, z, w}, m, r, v) == True{} : Bool}, hn,
        e => D.or.cases(U32.is_eq(D.Fd(2n, m, r), v), Bool.or(U32.is_eq(D.Fd(3n, m, r), v), Bool.or(U32.is_eq(D.Fd(4n, m, r), v), False{})), {D.Node(Bk.Term.Eql{y, z, w}, m, r, v) == True{} : Bool}, (%D.fs.term(m, ps, r, 16, 7, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Eql{y, z, w}, 16, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Eql{y, z, w}, tbl)) : {D.Mem(_, v) == True{} : Bool}; (%Equal.sym(U32, r, c, CK.U.eq(r, c, e)) : {D.Mem(D.Fs(m, ps, _), v) == True{} : Bool}; hv)), e0 => in.a(U32.is_eq(r, v), D.Node(y, m, D.Fd(2n, m, r), v), D.Node(z, m, D.Fd(3n, m, r), v), D.Node(w, m, D.Fd(4n, m, r), v), (%CK.U.eq(D.Fd(2n, m, r), v, e0) : {D.Node(y, m, D.Fd(2n, m, r), _) == True{} : Bool}; node.root(y, m, D.Fd(2n, m, r)))), e0 => D.or.cases(U32.is_eq(D.Fd(3n, m, r), v), Bool.or(U32.is_eq(D.Fd(4n, m, r), v), False{}), {D.Node(Bk.Term.Eql{y, z, w}, m, r, v) == True{} : Bool}, e0, e1 => in.b(U32.is_eq(r, v), D.Node(y, m, D.Fd(2n, m, r), v), D.Node(z, m, D.Fd(3n, m, r), v), D.Node(w, m, D.Fd(4n, m, r), v), (%CK.U.eq(D.Fd(3n, m, r), v, e1) : {D.Node(z, m, D.Fd(3n, m, r), _) == True{} : Bool}; node.root(z, m, D.Fd(3n, m, r)))), e1 => D.or.cases(U32.is_eq(D.Fd(4n, m, r), v), False{}, {D.Node(Bk.Term.Eql{y, z, w}, m, r, v) == True{} : Bool}, e1, e2 => in.c(U32.is_eq(r, v), D.Node(y, m, D.Fd(2n, m, r), v), D.Node(z, m, D.Fd(3n, m, r), v), D.Node(w, m, D.Fd(4n, m, r), v), (%CK.U.eq(D.Fd(4n, m, r), v, e2) : {D.Node(w, m, D.Fd(4n, m, r), _) == True{} : Bool}; node.root(w, m, D.Fd(4n, m, r)))), e2 => CK.Bo.tf({D.Node(Bk.Term.Eql{y, z, w}, m, r, v) == True{} : Bool}, e2)))),
        e => in.a(U32.is_eq(r, v), D.Node(y, m, D.Fd(2n, m, r), v), D.Node(z, m, D.Fd(3n, m, r), v), D.Node(w, m, D.Fd(4n, m, r), v), node.fs(y, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(2n, m, r), c, v, hy, e, hv)),
        e => in.b(U32.is_eq(r, v), D.Node(y, m, D.Fd(2n, m, r), v), D.Node(z, m, D.Fd(3n, m, r), v), D.Node(w, m, D.Fd(4n, m, r), v), node.fs(z, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(3n, m, r), c, v, hz, e, hv)),
        e => in.c(U32.is_eq(r, v), D.Node(y, m, D.Fd(2n, m, r), v), D.Node(z, m, D.Fd(3n, m, r), v), D.Node(w, m, D.Fd(4n, m, r), v), node.fs(w, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(4n, m, r), c, v, hw, e, hv)))
    case Bk.Term.Rfl{}:
      fs.leaf({D.Node(Bk.Term.Rfl{}, m, r, v) == True{} : Bool}, dk, ds, m, im, fi, nx, ps, r, c, v, Bk.Term.Rfl{}, 17, h, {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Rfl{}, tbl), hn, hv)
    case Bk.Term.Rwt{+y, +z, +w}:
      (+nd, w0) = h
      (py, w2) = w0
      (sy, hy) = py
      (pz, pw) = w2
      (sz, hz) = pz
      (sw, hw) = pw
      or4.case(U32.is_eq(r, c), D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c), D.Node(w, m, D.Fd(4n, m, r), c), {D.Node(Bk.Term.Rwt{y, z, w}, m, r, v) == True{} : Bool}, hn,
        e => D.or.cases(U32.is_eq(D.Fd(2n, m, r), v), Bool.or(U32.is_eq(D.Fd(3n, m, r), v), Bool.or(U32.is_eq(D.Fd(4n, m, r), v), False{})), {D.Node(Bk.Term.Rwt{y, z, w}, m, r, v) == True{} : Bool}, (%D.fs.term(m, ps, r, 18, 7, D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Rwt{y, z, w}, 18, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Rwt{y, z, w}, tbl)) : {D.Mem(_, v) == True{} : Bool}; (%Equal.sym(U32, r, c, CK.U.eq(r, c, e)) : {D.Mem(D.Fs(m, ps, _), v) == True{} : Bool}; hv)), e0 => in.a(U32.is_eq(r, v), D.Node(y, m, D.Fd(2n, m, r), v), D.Node(z, m, D.Fd(3n, m, r), v), D.Node(w, m, D.Fd(4n, m, r), v), (%CK.U.eq(D.Fd(2n, m, r), v, e0) : {D.Node(y, m, D.Fd(2n, m, r), _) == True{} : Bool}; node.root(y, m, D.Fd(2n, m, r)))), e0 => D.or.cases(U32.is_eq(D.Fd(3n, m, r), v), Bool.or(U32.is_eq(D.Fd(4n, m, r), v), False{}), {D.Node(Bk.Term.Rwt{y, z, w}, m, r, v) == True{} : Bool}, e0, e1 => in.b(U32.is_eq(r, v), D.Node(y, m, D.Fd(2n, m, r), v), D.Node(z, m, D.Fd(3n, m, r), v), D.Node(w, m, D.Fd(4n, m, r), v), (%CK.U.eq(D.Fd(3n, m, r), v, e1) : {D.Node(z, m, D.Fd(3n, m, r), _) == True{} : Bool}; node.root(z, m, D.Fd(3n, m, r)))), e1 => D.or.cases(U32.is_eq(D.Fd(4n, m, r), v), False{}, {D.Node(Bk.Term.Rwt{y, z, w}, m, r, v) == True{} : Bool}, e1, e2 => in.c(U32.is_eq(r, v), D.Node(y, m, D.Fd(2n, m, r), v), D.Node(z, m, D.Fd(3n, m, r), v), D.Node(w, m, D.Fd(4n, m, r), v), (%CK.U.eq(D.Fd(4n, m, r), v, e2) : {D.Node(w, m, D.Fd(4n, m, r), _) == True{} : Bool}; node.root(w, m, D.Fd(4n, m, r)))), e2 => CK.Bo.tf({D.Node(Bk.Term.Rwt{y, z, w}, m, r, v) == True{} : Bool}, e2)))),
        e => in.a(U32.is_eq(r, v), D.Node(y, m, D.Fd(2n, m, r), v), D.Node(z, m, D.Fd(3n, m, r), v), D.Node(w, m, D.Fd(4n, m, r), v), node.fs(y, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(2n, m, r), c, v, hy, e, hv)),
        e => in.b(U32.is_eq(r, v), D.Node(y, m, D.Fd(2n, m, r), v), D.Node(z, m, D.Fd(3n, m, r), v), D.Node(w, m, D.Fd(4n, m, r), v), node.fs(z, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(3n, m, r), c, v, hz, e, hv)),
        e => in.c(U32.is_eq(r, v), D.Node(y, m, D.Fd(2n, m, r), v), D.Node(z, m, D.Fd(3n, m, r), v), D.Node(w, m, D.Fd(4n, m, r), v), node.fs(w, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(4n, m, r), c, v, hw, e, hv)))

# a pointer v of a node c of a term of L is a node of a term of L
def nodes.fs(L: List<&2, D.Rt>, +dk: Bool, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +tbl: D.Tbl(m, im, fi, nx), +c: U32, +v: U32,
  +hL: D.RtsK(dk, ds, m, im, fi, nx, ks, img, L), +hc: {D.Nodes(L, m, c) == True{} : Bool},
  +hv: {D.Mem(D.Fs(m, ps, c), v) == True{} : Bool}) -> {D.Nodes(L, m, v) == True{} : Bool}:
  match L:
    case Nil{}:
      CK.Bo.tf({D.Nodes(Nil{}, m, v) == True{} : Bool}, hc)
    case Con{D.Rt{+r, +u}, +rest}:
      (hu, hrest) = hL
      D.or.cases(D.Node(u, m, r, c), D.Nodes(rest, m, c), {D.Nodes(Con{D.Rt{r, u}, rest}, m, v) == True{} : Bool}, hc,
        e => CK.Bo.or_il(D.Node(u, m, r, v), D.Nodes(rest, m, v), node.fs(u, dk, ds, m, im, fi, nx, ks, img, ps, tbl, r, c, v, hu, e, hv)),
        e => CK.Bo.or_ir(D.Node(u, m, r, v), D.Nodes(rest, m, v), nodes.fs(rest, dk, ds, m, im, fi, nx, ks, img, ps, tbl, c, v, hrest, e, hv)))

# the part in field 2 of a cell c that stands for v, when v's mask has bit 1:
# it stands for a term smaller than v, and it is among c's pointers
def part.s2(v: Bk.Term, +dk: Bool, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +tbl: D.Tbl(m, im, fi, nx), +c: U32,
  h: D.IsK(dk, ds, m, im, fi, nx, ks, img, c, v), hb: {U32.is_zero(U32.and(D.Mask(v), 1)) == False{} : Bool}) ->
  D.Ex(Bk.Term, u0 => D.P2(D.IsK(dk, ds, m, im, fi, nx, ks, img, D.Fd(2n, m, c), u0), D.P2(N.Le(1n+Pg.Term.size(u0), Pg.Term.size(v)), {D.Mem(D.Fs(m, ps, c), D.Fd(2n, m, c)) == True{} : Bool}))):
  match v:
    case Bk.Term.Var{+i}:
      CK.Bo.ft(D.Ex(Bk.Term, u0 => D.P2(D.IsK(dk, ds, m, im, fi, nx, ks, img, D.Fd(2n, m, c), u0), D.P2(N.Le(1n+Pg.Term.size(u0), Pg.Term.size(Bk.Term.Var{i})), {D.Mem(D.Fs(m, ps, c), D.Fd(2n, m, c)) == True{} : Bool}))), hb)
    case Bk.Term.Ref{+k}:
      CK.Bo.ft(D.Ex(Bk.Term, u0 => D.P2(D.IsK(dk, ds, m, im, fi, nx, ks, img, D.Fd(2n, m, c), u0), D.P2(N.Le(1n+Pg.Term.size(u0), Pg.Term.size(Bk.Term.Ref{k})), {D.Mem(D.Fs(m, ps, c), D.Fd(2n, m, c)) == True{} : Bool}))), hb)
    case Bk.Term.Ann{+y, +z}:
      (+nd, w0) = h
      (py, pz) = w0
      (sy, hy) = py
      (sz, hz) = pz
      (y, (hy, (N.le_add_r(Pg.Term.size(y), Pg.Term.size(z)), D.hm.at(m, ps, c, 2, 3, D.Fd(2n, m, c), D.nd.tgk(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Ann{y, z}, 2, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Ann{y, z}, tbl), CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, c), D.Fd(2n, m, c)), Bool.or(U32.is_eq(D.Fd(3n, m, c), D.Fd(2n, m, c)), False{}), CK.U.eq_refl(D.Fd(2n, m, c)))))))
    case Bk.Term.Let{+q, +y, +z}:
      (+nd, w0) = h
      (hq, w2) = w0
      (py, pz) = w2
      (sy, hy) = py
      (sz, hz) = pz
      (y, (hy, (N.le_add_r(Pg.Term.size(y), Pg.Term.size(z)), D.hm.at(m, ps, c, 3, 3, D.Fd(2n, m, c), D.nd.tgk(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Let{q, y, z}, 3, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Let{q, y, z}, tbl), CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, c), D.Fd(2n, m, c)), Bool.or(U32.is_eq(D.Fd(3n, m, c), D.Fd(2n, m, c)), False{}), CK.U.eq_refl(D.Fd(2n, m, c)))))))
    case Bk.Term.Typ{+y}:
      (+nd, w0) = h
      (sy, hy) = w0
      (y, (hy, (N.le_refl(Pg.Term.size(y)), D.hm.at(m, ps, c, 4, 1, D.Fd(2n, m, c), D.nd.tgk(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Typ{y}, 4, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Typ{y}, tbl), CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, c), D.Fd(2n, m, c)), False{}, CK.U.eq_refl(D.Fd(2n, m, c)))))))
    case Bk.Term.Min{+y, +z}:
      (+nd, w0) = h
      (py, pz) = w0
      (sy, hy) = py
      (sz, hz) = pz
      (y, (hy, (N.le_add_r(Pg.Term.size(y), Pg.Term.size(z)), D.hm.at(m, ps, c, 5, 3, D.Fd(2n, m, c), D.nd.tgk(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Min{y, z}, 5, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Min{y, z}, tbl), CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, c), D.Fd(2n, m, c)), Bool.or(U32.is_eq(D.Fd(3n, m, c), D.Fd(2n, m, c)), False{}), CK.U.eq_refl(D.Fd(2n, m, c)))))))
    case Bk.Term.All{+q, +y, +z}:
      (+nd, w0) = h
      (hq, w2) = w0
      (py, pz) = w2
      (sy, hy) = py
      (sz, hz) = pz
      (y, (hy, (N.le_add_r(Pg.Term.size(y), Pg.Term.size(z)), D.hm.at(m, ps, c, 6, 3, D.Fd(2n, m, c), D.nd.tgk(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.All{q, y, z}, 6, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.All{q, y, z}, tbl), CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, c), D.Fd(2n, m, c)), Bool.or(U32.is_eq(D.Fd(3n, m, c), D.Fd(2n, m, c)), False{}), CK.U.eq_refl(D.Fd(2n, m, c)))))))
    case Bk.Term.Lam{+q, +y}:
      (+nd, w0) = h
      (hq, w2) = w0
      (sy, hy) = w2
      (y, (hy, (N.le_refl(Pg.Term.size(y)), D.hm.at(m, ps, c, 7, 1, D.Fd(2n, m, c), D.nd.tgk(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Lam{q, y}, 7, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Lam{q, y}, tbl), CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, c), D.Fd(2n, m, c)), False{}, CK.U.eq_refl(D.Fd(2n, m, c)))))))
    case Bk.Term.App{+q, +y, +z}:
      (+nd, w0) = h
      (hq, w2) = w0
      (py, pz) = w2
      (sy, hy) = py
      (sz, hz) = pz
      (y, (hy, (N.le_add_r(Pg.Term.size(y), Pg.Term.size(z)), D.hm.at(m, ps, c, 8, 3, D.Fd(2n, m, c), D.nd.tgk(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.App{q, y, z}, 8, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.App{q, y, z}, tbl), CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, c), D.Fd(2n, m, c)), Bool.or(U32.is_eq(D.Fd(3n, m, c), D.Fd(2n, m, c)), False{}), CK.U.eq_refl(D.Fd(2n, m, c)))))))
    case Bk.Term.Sig{+q, +y, +z}:
      (+nd, w0) = h
      (hq, w2) = w0
      (py, pz) = w2
      (sy, hy) = py
      (sz, hz) = pz
      (y, (hy, (N.le_add_r(Pg.Term.size(y), Pg.Term.size(z)), D.hm.at(m, ps, c, 9, 3, D.Fd(2n, m, c), D.nd.tgk(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Sig{q, y, z}, 9, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Sig{q, y, z}, tbl), CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, c), D.Fd(2n, m, c)), Bool.or(U32.is_eq(D.Fd(3n, m, c), D.Fd(2n, m, c)), False{}), CK.U.eq_refl(D.Fd(2n, m, c)))))))
    case Bk.Term.Tup{+q, +y, +z}:
      (+nd, w0) = h
      (hq, w2) = w0
      (py, pz) = w2
      (sy, hy) = py
      (sz, hz) = pz
      (y, (hy, (N.le_add_r(Pg.Term.size(y), Pg.Term.size(z)), D.hm.at(m, ps, c, 10, 3, D.Fd(2n, m, c), D.nd.tgk(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Tup{q, y, z}, 10, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Tup{q, y, z}, tbl), CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, c), D.Fd(2n, m, c)), Bool.or(U32.is_eq(D.Fd(3n, m, c), D.Fd(2n, m, c)), False{}), CK.U.eq_refl(D.Fd(2n, m, c)))))))
    case Bk.Term.Prj{+y}:
      (+nd, w0) = h
      (sy, hy) = w0
      (y, (hy, (N.le_refl(Pg.Term.size(y)), D.hm.at(m, ps, c, 11, 1, D.Fd(2n, m, c), D.nd.tgk(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Prj{y}, 11, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Prj{y}, tbl), CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, c), D.Fd(2n, m, c)), False{}, CK.U.eq_refl(D.Fd(2n, m, c)))))))
    case Bk.Term.Enu{+e}:
      CK.Bo.ft(D.Ex(Bk.Term, u0 => D.P2(D.IsK(dk, ds, m, im, fi, nx, ks, img, D.Fd(2n, m, c), u0), D.P2(N.Le(1n+Pg.Term.size(u0), Pg.Term.size(Bk.Term.Enu{e})), {D.Mem(D.Fs(m, ps, c), D.Fd(2n, m, c)) == True{} : Bool}))), hb)
    case Bk.Term.Lab{+k}:
      CK.Bo.ft(D.Ex(Bk.Term, u0 => D.P2(D.IsK(dk, ds, m, im, fi, nx, ks, img, D.Fd(2n, m, c), u0), D.P2(N.Le(1n+Pg.Term.size(u0), Pg.Term.size(Bk.Term.Lab{k})), {D.Mem(D.Fs(m, ps, c), D.Fd(2n, m, c)) == True{} : Bool}))), hb)
    case Bk.Term.Mat{+k, +y, +z}:
      CK.Bo.ft(D.Ex(Bk.Term, u0 => D.P2(D.IsK(dk, ds, m, im, fi, nx, ks, img, D.Fd(2n, m, c), u0), D.P2(N.Le(1n+Pg.Term.size(u0), Pg.Term.size(Bk.Term.Mat{k, y, z})), {D.Mem(D.Fs(m, ps, c), D.Fd(2n, m, c)) == True{} : Bool}))), hb)
    case Bk.Term.Efq{}:
      CK.Bo.ft(D.Ex(Bk.Term, u0 => D.P2(D.IsK(dk, ds, m, im, fi, nx, ks, img, D.Fd(2n, m, c), u0), D.P2(N.Le(1n+Pg.Term.size(u0), Pg.Term.size(Bk.Term.Efq{})), {D.Mem(D.Fs(m, ps, c), D.Fd(2n, m, c)) == True{} : Bool}))), hb)
    case Bk.Term.Eql{+y, +z, +w}:
      (+nd, w0) = h
      (py, w2) = w0
      (sy, hy) = py
      (pz, pw) = w2
      (sz, hz) = pz
      (sw, hw) = pw
      (y, (hy, (N.le_add_r(Pg.Term.size(y), Nat.add(Pg.Term.size(z), Pg.Term.size(w))), D.hm.at(m, ps, c, 16, 7, D.Fd(2n, m, c), D.nd.tgk(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Eql{y, z, w}, 16, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Eql{y, z, w}, tbl), CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, c), D.Fd(2n, m, c)), Bool.or(U32.is_eq(D.Fd(3n, m, c), D.Fd(2n, m, c)), Bool.or(U32.is_eq(D.Fd(4n, m, c), D.Fd(2n, m, c)), False{})), CK.U.eq_refl(D.Fd(2n, m, c)))))))
    case Bk.Term.Rfl{}:
      CK.Bo.ft(D.Ex(Bk.Term, u0 => D.P2(D.IsK(dk, ds, m, im, fi, nx, ks, img, D.Fd(2n, m, c), u0), D.P2(N.Le(1n+Pg.Term.size(u0), Pg.Term.size(Bk.Term.Rfl{})), {D.Mem(D.Fs(m, ps, c), D.Fd(2n, m, c)) == True{} : Bool}))), hb)
    case Bk.Term.Rwt{+y, +z, +w}:
      (+nd, w0) = h
      (py, w2) = w0
      (sy, hy) = py
      (pz, pw) = w2
      (sz, hz) = pz
      (sw, hw) = pw
      (y, (hy, (N.le_add_r(Pg.Term.size(y), Nat.add(Pg.Term.size(z), Pg.Term.size(w))), D.hm.at(m, ps, c, 18, 7, D.Fd(2n, m, c), D.nd.tgk(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Rwt{y, z, w}, 18, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Rwt{y, z, w}, tbl), CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, c), D.Fd(2n, m, c)), Bool.or(U32.is_eq(D.Fd(3n, m, c), D.Fd(2n, m, c)), Bool.or(U32.is_eq(D.Fd(4n, m, c), D.Fd(2n, m, c)), False{})), CK.U.eq_refl(D.Fd(2n, m, c)))))))

# the part in field 3 of a cell c that stands for v, when v's mask has bit 2:
# it stands for a term smaller than v, and it is among c's pointers
def part.s3(v: Bk.Term, +dk: Bool, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +tbl: D.Tbl(m, im, fi, nx), +c: U32,
  h: D.IsK(dk, ds, m, im, fi, nx, ks, img, c, v), hb: {U32.is_zero(U32.and(D.Mask(v), 2)) == False{} : Bool}) ->
  D.Ex(Bk.Term, u0 => D.P2(D.IsK(dk, ds, m, im, fi, nx, ks, img, D.Fd(3n, m, c), u0), D.P2(N.Le(1n+Pg.Term.size(u0), Pg.Term.size(v)), {D.Mem(D.Fs(m, ps, c), D.Fd(3n, m, c)) == True{} : Bool}))):
  match v:
    case Bk.Term.Var{+i}:
      CK.Bo.ft(D.Ex(Bk.Term, u0 => D.P2(D.IsK(dk, ds, m, im, fi, nx, ks, img, D.Fd(3n, m, c), u0), D.P2(N.Le(1n+Pg.Term.size(u0), Pg.Term.size(Bk.Term.Var{i})), {D.Mem(D.Fs(m, ps, c), D.Fd(3n, m, c)) == True{} : Bool}))), hb)
    case Bk.Term.Ref{+k}:
      CK.Bo.ft(D.Ex(Bk.Term, u0 => D.P2(D.IsK(dk, ds, m, im, fi, nx, ks, img, D.Fd(3n, m, c), u0), D.P2(N.Le(1n+Pg.Term.size(u0), Pg.Term.size(Bk.Term.Ref{k})), {D.Mem(D.Fs(m, ps, c), D.Fd(3n, m, c)) == True{} : Bool}))), hb)
    case Bk.Term.Ann{+y, +z}:
      (+nd, w0) = h
      (py, pz) = w0
      (sy, hy) = py
      (sz, hz) = pz
      (z, (hz, (N.le_add_l(Pg.Term.size(y), Pg.Term.size(z)), D.hm.at(m, ps, c, 2, 3, D.Fd(3n, m, c), D.nd.tgk(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Ann{y, z}, 2, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Ann{y, z}, tbl), CK.Bo.or_ir(U32.is_eq(D.Fd(2n, m, c), D.Fd(3n, m, c)), Bool.or(U32.is_eq(D.Fd(3n, m, c), D.Fd(3n, m, c)), False{}), CK.Bo.or_il(U32.is_eq(D.Fd(3n, m, c), D.Fd(3n, m, c)), False{}, CK.U.eq_refl(D.Fd(3n, m, c))))))))
    case Bk.Term.Let{+q, +y, +z}:
      (+nd, w0) = h
      (hq, w2) = w0
      (py, pz) = w2
      (sy, hy) = py
      (sz, hz) = pz
      (z, (hz, (N.le_add_l(Pg.Term.size(y), Pg.Term.size(z)), D.hm.at(m, ps, c, 3, 3, D.Fd(3n, m, c), D.nd.tgk(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Let{q, y, z}, 3, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Let{q, y, z}, tbl), CK.Bo.or_ir(U32.is_eq(D.Fd(2n, m, c), D.Fd(3n, m, c)), Bool.or(U32.is_eq(D.Fd(3n, m, c), D.Fd(3n, m, c)), False{}), CK.Bo.or_il(U32.is_eq(D.Fd(3n, m, c), D.Fd(3n, m, c)), False{}, CK.U.eq_refl(D.Fd(3n, m, c))))))))
    case Bk.Term.Typ{+y}:
      CK.Bo.ft(D.Ex(Bk.Term, u0 => D.P2(D.IsK(dk, ds, m, im, fi, nx, ks, img, D.Fd(3n, m, c), u0), D.P2(N.Le(1n+Pg.Term.size(u0), Pg.Term.size(Bk.Term.Typ{y})), {D.Mem(D.Fs(m, ps, c), D.Fd(3n, m, c)) == True{} : Bool}))), hb)
    case Bk.Term.Min{+y, +z}:
      (+nd, w0) = h
      (py, pz) = w0
      (sy, hy) = py
      (sz, hz) = pz
      (z, (hz, (N.le_add_l(Pg.Term.size(y), Pg.Term.size(z)), D.hm.at(m, ps, c, 5, 3, D.Fd(3n, m, c), D.nd.tgk(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Min{y, z}, 5, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Min{y, z}, tbl), CK.Bo.or_ir(U32.is_eq(D.Fd(2n, m, c), D.Fd(3n, m, c)), Bool.or(U32.is_eq(D.Fd(3n, m, c), D.Fd(3n, m, c)), False{}), CK.Bo.or_il(U32.is_eq(D.Fd(3n, m, c), D.Fd(3n, m, c)), False{}, CK.U.eq_refl(D.Fd(3n, m, c))))))))
    case Bk.Term.All{+q, +y, +z}:
      (+nd, w0) = h
      (hq, w2) = w0
      (py, pz) = w2
      (sy, hy) = py
      (sz, hz) = pz
      (z, (hz, (N.le_add_l(Pg.Term.size(y), Pg.Term.size(z)), D.hm.at(m, ps, c, 6, 3, D.Fd(3n, m, c), D.nd.tgk(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.All{q, y, z}, 6, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.All{q, y, z}, tbl), CK.Bo.or_ir(U32.is_eq(D.Fd(2n, m, c), D.Fd(3n, m, c)), Bool.or(U32.is_eq(D.Fd(3n, m, c), D.Fd(3n, m, c)), False{}), CK.Bo.or_il(U32.is_eq(D.Fd(3n, m, c), D.Fd(3n, m, c)), False{}, CK.U.eq_refl(D.Fd(3n, m, c))))))))
    case Bk.Term.Lam{+q, +y}:
      CK.Bo.ft(D.Ex(Bk.Term, u0 => D.P2(D.IsK(dk, ds, m, im, fi, nx, ks, img, D.Fd(3n, m, c), u0), D.P2(N.Le(1n+Pg.Term.size(u0), Pg.Term.size(Bk.Term.Lam{q, y})), {D.Mem(D.Fs(m, ps, c), D.Fd(3n, m, c)) == True{} : Bool}))), hb)
    case Bk.Term.App{+q, +y, +z}:
      (+nd, w0) = h
      (hq, w2) = w0
      (py, pz) = w2
      (sy, hy) = py
      (sz, hz) = pz
      (z, (hz, (N.le_add_l(Pg.Term.size(y), Pg.Term.size(z)), D.hm.at(m, ps, c, 8, 3, D.Fd(3n, m, c), D.nd.tgk(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.App{q, y, z}, 8, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.App{q, y, z}, tbl), CK.Bo.or_ir(U32.is_eq(D.Fd(2n, m, c), D.Fd(3n, m, c)), Bool.or(U32.is_eq(D.Fd(3n, m, c), D.Fd(3n, m, c)), False{}), CK.Bo.or_il(U32.is_eq(D.Fd(3n, m, c), D.Fd(3n, m, c)), False{}, CK.U.eq_refl(D.Fd(3n, m, c))))))))
    case Bk.Term.Sig{+q, +y, +z}:
      (+nd, w0) = h
      (hq, w2) = w0
      (py, pz) = w2
      (sy, hy) = py
      (sz, hz) = pz
      (z, (hz, (N.le_add_l(Pg.Term.size(y), Pg.Term.size(z)), D.hm.at(m, ps, c, 9, 3, D.Fd(3n, m, c), D.nd.tgk(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Sig{q, y, z}, 9, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Sig{q, y, z}, tbl), CK.Bo.or_ir(U32.is_eq(D.Fd(2n, m, c), D.Fd(3n, m, c)), Bool.or(U32.is_eq(D.Fd(3n, m, c), D.Fd(3n, m, c)), False{}), CK.Bo.or_il(U32.is_eq(D.Fd(3n, m, c), D.Fd(3n, m, c)), False{}, CK.U.eq_refl(D.Fd(3n, m, c))))))))
    case Bk.Term.Tup{+q, +y, +z}:
      (+nd, w0) = h
      (hq, w2) = w0
      (py, pz) = w2
      (sy, hy) = py
      (sz, hz) = pz
      (z, (hz, (N.le_add_l(Pg.Term.size(y), Pg.Term.size(z)), D.hm.at(m, ps, c, 10, 3, D.Fd(3n, m, c), D.nd.tgk(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Tup{q, y, z}, 10, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Tup{q, y, z}, tbl), CK.Bo.or_ir(U32.is_eq(D.Fd(2n, m, c), D.Fd(3n, m, c)), Bool.or(U32.is_eq(D.Fd(3n, m, c), D.Fd(3n, m, c)), False{}), CK.Bo.or_il(U32.is_eq(D.Fd(3n, m, c), D.Fd(3n, m, c)), False{}, CK.U.eq_refl(D.Fd(3n, m, c))))))))
    case Bk.Term.Prj{+y}:
      CK.Bo.ft(D.Ex(Bk.Term, u0 => D.P2(D.IsK(dk, ds, m, im, fi, nx, ks, img, D.Fd(3n, m, c), u0), D.P2(N.Le(1n+Pg.Term.size(u0), Pg.Term.size(Bk.Term.Prj{y})), {D.Mem(D.Fs(m, ps, c), D.Fd(3n, m, c)) == True{} : Bool}))), hb)
    case Bk.Term.Enu{+e}:
      CK.Bo.ft(D.Ex(Bk.Term, u0 => D.P2(D.IsK(dk, ds, m, im, fi, nx, ks, img, D.Fd(3n, m, c), u0), D.P2(N.Le(1n+Pg.Term.size(u0), Pg.Term.size(Bk.Term.Enu{e})), {D.Mem(D.Fs(m, ps, c), D.Fd(3n, m, c)) == True{} : Bool}))), hb)
    case Bk.Term.Lab{+k}:
      CK.Bo.ft(D.Ex(Bk.Term, u0 => D.P2(D.IsK(dk, ds, m, im, fi, nx, ks, img, D.Fd(3n, m, c), u0), D.P2(N.Le(1n+Pg.Term.size(u0), Pg.Term.size(Bk.Term.Lab{k})), {D.Mem(D.Fs(m, ps, c), D.Fd(3n, m, c)) == True{} : Bool}))), hb)
    case Bk.Term.Mat{+k, +y, +z}:
      (+nd, w0) = h
      (nm, w2) = w0
      (py, pz) = w2
      (sy, hy) = py
      (sz, hz) = pz
      (y, (hy, (N.le_add_r(Pg.Term.size(y), Pg.Term.size(z)), D.hm.at(m, ps, c, 14, 6, D.Fd(3n, m, c), D.nd.tgk(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Mat{k, y, z}, 14, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Mat{k, y, z}, tbl), CK.Bo.or_il(U32.is_eq(D.Fd(3n, m, c), D.Fd(3n, m, c)), Bool.or(U32.is_eq(D.Fd(4n, m, c), D.Fd(3n, m, c)), False{}), CK.U.eq_refl(D.Fd(3n, m, c)))))))
    case Bk.Term.Efq{}:
      CK.Bo.ft(D.Ex(Bk.Term, u0 => D.P2(D.IsK(dk, ds, m, im, fi, nx, ks, img, D.Fd(3n, m, c), u0), D.P2(N.Le(1n+Pg.Term.size(u0), Pg.Term.size(Bk.Term.Efq{})), {D.Mem(D.Fs(m, ps, c), D.Fd(3n, m, c)) == True{} : Bool}))), hb)
    case Bk.Term.Eql{+y, +z, +w}:
      (+nd, w0) = h
      (py, w2) = w0
      (sy, hy) = py
      (pz, pw) = w2
      (sz, hz) = pz
      (sw, hw) = pw
      (z, (hz, (N.le_trans(Pg.Term.size(z), Nat.add(Pg.Term.size(z), Pg.Term.size(w)), Nat.add(Pg.Term.size(y), Nat.add(Pg.Term.size(z), Pg.Term.size(w))), N.le_add_r(Pg.Term.size(z), Pg.Term.size(w)), N.le_add_l(Pg.Term.size(y), Nat.add(Pg.Term.size(z), Pg.Term.size(w)))), D.hm.at(m, ps, c, 16, 7, D.Fd(3n, m, c), D.nd.tgk(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Eql{y, z, w}, 16, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Eql{y, z, w}, tbl), CK.Bo.or_ir(U32.is_eq(D.Fd(2n, m, c), D.Fd(3n, m, c)), Bool.or(U32.is_eq(D.Fd(3n, m, c), D.Fd(3n, m, c)), Bool.or(U32.is_eq(D.Fd(4n, m, c), D.Fd(3n, m, c)), False{})), CK.Bo.or_il(U32.is_eq(D.Fd(3n, m, c), D.Fd(3n, m, c)), Bool.or(U32.is_eq(D.Fd(4n, m, c), D.Fd(3n, m, c)), False{}), CK.U.eq_refl(D.Fd(3n, m, c))))))))
    case Bk.Term.Rfl{}:
      CK.Bo.ft(D.Ex(Bk.Term, u0 => D.P2(D.IsK(dk, ds, m, im, fi, nx, ks, img, D.Fd(3n, m, c), u0), D.P2(N.Le(1n+Pg.Term.size(u0), Pg.Term.size(Bk.Term.Rfl{})), {D.Mem(D.Fs(m, ps, c), D.Fd(3n, m, c)) == True{} : Bool}))), hb)
    case Bk.Term.Rwt{+y, +z, +w}:
      (+nd, w0) = h
      (py, w2) = w0
      (sy, hy) = py
      (pz, pw) = w2
      (sz, hz) = pz
      (sw, hw) = pw
      (z, (hz, (N.le_trans(Pg.Term.size(z), Nat.add(Pg.Term.size(z), Pg.Term.size(w)), Nat.add(Pg.Term.size(y), Nat.add(Pg.Term.size(z), Pg.Term.size(w))), N.le_add_r(Pg.Term.size(z), Pg.Term.size(w)), N.le_add_l(Pg.Term.size(y), Nat.add(Pg.Term.size(z), Pg.Term.size(w)))), D.hm.at(m, ps, c, 18, 7, D.Fd(3n, m, c), D.nd.tgk(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Rwt{y, z, w}, 18, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Rwt{y, z, w}, tbl), CK.Bo.or_ir(U32.is_eq(D.Fd(2n, m, c), D.Fd(3n, m, c)), Bool.or(U32.is_eq(D.Fd(3n, m, c), D.Fd(3n, m, c)), Bool.or(U32.is_eq(D.Fd(4n, m, c), D.Fd(3n, m, c)), False{})), CK.Bo.or_il(U32.is_eq(D.Fd(3n, m, c), D.Fd(3n, m, c)), Bool.or(U32.is_eq(D.Fd(4n, m, c), D.Fd(3n, m, c)), False{}), CK.U.eq_refl(D.Fd(3n, m, c))))))))

# the part in field 4 of a cell c that stands for v, when v's mask has bit 4:
# it stands for a term smaller than v, and it is among c's pointers
def part.s4(v: Bk.Term, +dk: Bool, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +tbl: D.Tbl(m, im, fi, nx), +c: U32,
  h: D.IsK(dk, ds, m, im, fi, nx, ks, img, c, v), hb: {U32.is_zero(U32.and(D.Mask(v), 4)) == False{} : Bool}) ->
  D.Ex(Bk.Term, u0 => D.P2(D.IsK(dk, ds, m, im, fi, nx, ks, img, D.Fd(4n, m, c), u0), D.P2(N.Le(1n+Pg.Term.size(u0), Pg.Term.size(v)), {D.Mem(D.Fs(m, ps, c), D.Fd(4n, m, c)) == True{} : Bool}))):
  match v:
    case Bk.Term.Var{+i}:
      CK.Bo.ft(D.Ex(Bk.Term, u0 => D.P2(D.IsK(dk, ds, m, im, fi, nx, ks, img, D.Fd(4n, m, c), u0), D.P2(N.Le(1n+Pg.Term.size(u0), Pg.Term.size(Bk.Term.Var{i})), {D.Mem(D.Fs(m, ps, c), D.Fd(4n, m, c)) == True{} : Bool}))), hb)
    case Bk.Term.Ref{+k}:
      CK.Bo.ft(D.Ex(Bk.Term, u0 => D.P2(D.IsK(dk, ds, m, im, fi, nx, ks, img, D.Fd(4n, m, c), u0), D.P2(N.Le(1n+Pg.Term.size(u0), Pg.Term.size(Bk.Term.Ref{k})), {D.Mem(D.Fs(m, ps, c), D.Fd(4n, m, c)) == True{} : Bool}))), hb)
    case Bk.Term.Ann{+y, +z}:
      CK.Bo.ft(D.Ex(Bk.Term, u0 => D.P2(D.IsK(dk, ds, m, im, fi, nx, ks, img, D.Fd(4n, m, c), u0), D.P2(N.Le(1n+Pg.Term.size(u0), Pg.Term.size(Bk.Term.Ann{y, z})), {D.Mem(D.Fs(m, ps, c), D.Fd(4n, m, c)) == True{} : Bool}))), hb)
    case Bk.Term.Let{+q, +y, +z}:
      CK.Bo.ft(D.Ex(Bk.Term, u0 => D.P2(D.IsK(dk, ds, m, im, fi, nx, ks, img, D.Fd(4n, m, c), u0), D.P2(N.Le(1n+Pg.Term.size(u0), Pg.Term.size(Bk.Term.Let{q, y, z})), {D.Mem(D.Fs(m, ps, c), D.Fd(4n, m, c)) == True{} : Bool}))), hb)
    case Bk.Term.Typ{+y}:
      CK.Bo.ft(D.Ex(Bk.Term, u0 => D.P2(D.IsK(dk, ds, m, im, fi, nx, ks, img, D.Fd(4n, m, c), u0), D.P2(N.Le(1n+Pg.Term.size(u0), Pg.Term.size(Bk.Term.Typ{y})), {D.Mem(D.Fs(m, ps, c), D.Fd(4n, m, c)) == True{} : Bool}))), hb)
    case Bk.Term.Min{+y, +z}:
      CK.Bo.ft(D.Ex(Bk.Term, u0 => D.P2(D.IsK(dk, ds, m, im, fi, nx, ks, img, D.Fd(4n, m, c), u0), D.P2(N.Le(1n+Pg.Term.size(u0), Pg.Term.size(Bk.Term.Min{y, z})), {D.Mem(D.Fs(m, ps, c), D.Fd(4n, m, c)) == True{} : Bool}))), hb)
    case Bk.Term.All{+q, +y, +z}:
      CK.Bo.ft(D.Ex(Bk.Term, u0 => D.P2(D.IsK(dk, ds, m, im, fi, nx, ks, img, D.Fd(4n, m, c), u0), D.P2(N.Le(1n+Pg.Term.size(u0), Pg.Term.size(Bk.Term.All{q, y, z})), {D.Mem(D.Fs(m, ps, c), D.Fd(4n, m, c)) == True{} : Bool}))), hb)
    case Bk.Term.Lam{+q, +y}:
      CK.Bo.ft(D.Ex(Bk.Term, u0 => D.P2(D.IsK(dk, ds, m, im, fi, nx, ks, img, D.Fd(4n, m, c), u0), D.P2(N.Le(1n+Pg.Term.size(u0), Pg.Term.size(Bk.Term.Lam{q, y})), {D.Mem(D.Fs(m, ps, c), D.Fd(4n, m, c)) == True{} : Bool}))), hb)
    case Bk.Term.App{+q, +y, +z}:
      CK.Bo.ft(D.Ex(Bk.Term, u0 => D.P2(D.IsK(dk, ds, m, im, fi, nx, ks, img, D.Fd(4n, m, c), u0), D.P2(N.Le(1n+Pg.Term.size(u0), Pg.Term.size(Bk.Term.App{q, y, z})), {D.Mem(D.Fs(m, ps, c), D.Fd(4n, m, c)) == True{} : Bool}))), hb)
    case Bk.Term.Sig{+q, +y, +z}:
      CK.Bo.ft(D.Ex(Bk.Term, u0 => D.P2(D.IsK(dk, ds, m, im, fi, nx, ks, img, D.Fd(4n, m, c), u0), D.P2(N.Le(1n+Pg.Term.size(u0), Pg.Term.size(Bk.Term.Sig{q, y, z})), {D.Mem(D.Fs(m, ps, c), D.Fd(4n, m, c)) == True{} : Bool}))), hb)
    case Bk.Term.Tup{+q, +y, +z}:
      CK.Bo.ft(D.Ex(Bk.Term, u0 => D.P2(D.IsK(dk, ds, m, im, fi, nx, ks, img, D.Fd(4n, m, c), u0), D.P2(N.Le(1n+Pg.Term.size(u0), Pg.Term.size(Bk.Term.Tup{q, y, z})), {D.Mem(D.Fs(m, ps, c), D.Fd(4n, m, c)) == True{} : Bool}))), hb)
    case Bk.Term.Prj{+y}:
      CK.Bo.ft(D.Ex(Bk.Term, u0 => D.P2(D.IsK(dk, ds, m, im, fi, nx, ks, img, D.Fd(4n, m, c), u0), D.P2(N.Le(1n+Pg.Term.size(u0), Pg.Term.size(Bk.Term.Prj{y})), {D.Mem(D.Fs(m, ps, c), D.Fd(4n, m, c)) == True{} : Bool}))), hb)
    case Bk.Term.Enu{+e}:
      CK.Bo.ft(D.Ex(Bk.Term, u0 => D.P2(D.IsK(dk, ds, m, im, fi, nx, ks, img, D.Fd(4n, m, c), u0), D.P2(N.Le(1n+Pg.Term.size(u0), Pg.Term.size(Bk.Term.Enu{e})), {D.Mem(D.Fs(m, ps, c), D.Fd(4n, m, c)) == True{} : Bool}))), hb)
    case Bk.Term.Lab{+k}:
      CK.Bo.ft(D.Ex(Bk.Term, u0 => D.P2(D.IsK(dk, ds, m, im, fi, nx, ks, img, D.Fd(4n, m, c), u0), D.P2(N.Le(1n+Pg.Term.size(u0), Pg.Term.size(Bk.Term.Lab{k})), {D.Mem(D.Fs(m, ps, c), D.Fd(4n, m, c)) == True{} : Bool}))), hb)
    case Bk.Term.Mat{+k, +y, +z}:
      (+nd, w0) = h
      (nm, w2) = w0
      (py, pz) = w2
      (sy, hy) = py
      (sz, hz) = pz
      (z, (hz, (N.le_add_l(Pg.Term.size(y), Pg.Term.size(z)), D.hm.at(m, ps, c, 14, 6, D.Fd(4n, m, c), D.nd.tgk(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Mat{k, y, z}, 14, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Mat{k, y, z}, tbl), CK.Bo.or_ir(U32.is_eq(D.Fd(3n, m, c), D.Fd(4n, m, c)), Bool.or(U32.is_eq(D.Fd(4n, m, c), D.Fd(4n, m, c)), False{}), CK.Bo.or_il(U32.is_eq(D.Fd(4n, m, c), D.Fd(4n, m, c)), False{}, CK.U.eq_refl(D.Fd(4n, m, c))))))))
    case Bk.Term.Efq{}:
      CK.Bo.ft(D.Ex(Bk.Term, u0 => D.P2(D.IsK(dk, ds, m, im, fi, nx, ks, img, D.Fd(4n, m, c), u0), D.P2(N.Le(1n+Pg.Term.size(u0), Pg.Term.size(Bk.Term.Efq{})), {D.Mem(D.Fs(m, ps, c), D.Fd(4n, m, c)) == True{} : Bool}))), hb)
    case Bk.Term.Eql{+y, +z, +w}:
      (+nd, w0) = h
      (py, w2) = w0
      (sy, hy) = py
      (pz, pw) = w2
      (sz, hz) = pz
      (sw, hw) = pw
      (w, (hw, (N.le_trans(Pg.Term.size(w), Nat.add(Pg.Term.size(z), Pg.Term.size(w)), Nat.add(Pg.Term.size(y), Nat.add(Pg.Term.size(z), Pg.Term.size(w))), N.le_add_l(Pg.Term.size(z), Pg.Term.size(w)), N.le_add_l(Pg.Term.size(y), Nat.add(Pg.Term.size(z), Pg.Term.size(w)))), D.hm.at(m, ps, c, 16, 7, D.Fd(4n, m, c), D.nd.tgk(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Eql{y, z, w}, 16, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Eql{y, z, w}, tbl), CK.Bo.or_ir(U32.is_eq(D.Fd(2n, m, c), D.Fd(4n, m, c)), Bool.or(U32.is_eq(D.Fd(3n, m, c), D.Fd(4n, m, c)), Bool.or(U32.is_eq(D.Fd(4n, m, c), D.Fd(4n, m, c)), False{})), CK.Bo.or_ir(U32.is_eq(D.Fd(3n, m, c), D.Fd(4n, m, c)), Bool.or(U32.is_eq(D.Fd(4n, m, c), D.Fd(4n, m, c)), False{}), CK.Bo.or_il(U32.is_eq(D.Fd(4n, m, c), D.Fd(4n, m, c)), False{}, CK.U.eq_refl(D.Fd(4n, m, c)))))))))
    case Bk.Term.Rfl{}:
      CK.Bo.ft(D.Ex(Bk.Term, u0 => D.P2(D.IsK(dk, ds, m, im, fi, nx, ks, img, D.Fd(4n, m, c), u0), D.P2(N.Le(1n+Pg.Term.size(u0), Pg.Term.size(Bk.Term.Rfl{})), {D.Mem(D.Fs(m, ps, c), D.Fd(4n, m, c)) == True{} : Bool}))), hb)
    case Bk.Term.Rwt{+y, +z, +w}:
      (+nd, w0) = h
      (py, w2) = w0
      (sy, hy) = py
      (pz, pw) = w2
      (sz, hz) = pz
      (sw, hw) = pw
      (w, (hw, (N.le_trans(Pg.Term.size(w), Nat.add(Pg.Term.size(z), Pg.Term.size(w)), Nat.add(Pg.Term.size(y), Nat.add(Pg.Term.size(z), Pg.Term.size(w))), N.le_add_l(Pg.Term.size(z), Pg.Term.size(w)), N.le_add_l(Pg.Term.size(y), Nat.add(Pg.Term.size(z), Pg.Term.size(w)))), D.hm.at(m, ps, c, 18, 7, D.Fd(4n, m, c), D.nd.tgk(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Rwt{y, z, w}, 18, nd), {==}, D.tbl.mask(m, im, fi, nx, Bk.Term.Rwt{y, z, w}, tbl), CK.Bo.or_ir(U32.is_eq(D.Fd(2n, m, c), D.Fd(4n, m, c)), Bool.or(U32.is_eq(D.Fd(3n, m, c), D.Fd(4n, m, c)), Bool.or(U32.is_eq(D.Fd(4n, m, c), D.Fd(4n, m, c)), False{})), CK.Bo.or_ir(U32.is_eq(D.Fd(3n, m, c), D.Fd(4n, m, c)), Bool.or(U32.is_eq(D.Fd(4n, m, c), D.Fd(4n, m, c)), False{}), CK.Bo.or_il(U32.is_eq(D.Fd(4n, m, c), D.Fd(4n, m, c)), False{}, CK.U.eq_refl(D.Fd(4n, m, c)))))))))

# the tag of a cell that stands for v is v's
def isk.atag(v: Bk.Term, -dk: Bool, -ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, -im: U32, -fi: U32, -nx: U32,
  -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, +c: U32, h: D.IsK(dk, ds, m, im, fi, nx, ks, img, c, v)) ->
  {D.Tg(m, c) == D.A.tag(v) : U32}:
  match v:
    case Bk.Term.Var{+i}:
      (+nd, w0) = h
      D.nd.tgk(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Var{i}, 0, nd)
    case Bk.Term.Ref{+k}:
      (+nd, w0) = h
      D.nd.tgk(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Ref{k}, 1, nd)
    case Bk.Term.Ann{+y, +z}:
      (+nd, w0) = h
      D.nd.tgk(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Ann{y, z}, 2, nd)
    case Bk.Term.Let{+q, +y, +z}:
      (+nd, w0) = h
      D.nd.tgk(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Let{q, y, z}, 3, nd)
    case Bk.Term.Typ{+y}:
      (+nd, w0) = h
      D.nd.tgk(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Typ{y}, 4, nd)
    case Bk.Term.Min{+y, +z}:
      (+nd, w0) = h
      D.nd.tgk(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Min{y, z}, 5, nd)
    case Bk.Term.All{+q, +y, +z}:
      (+nd, w0) = h
      D.nd.tgk(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.All{q, y, z}, 6, nd)
    case Bk.Term.Lam{+q, +y}:
      (+nd, w0) = h
      D.nd.tgk(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Lam{q, y}, 7, nd)
    case Bk.Term.App{+q, +y, +z}:
      (+nd, w0) = h
      D.nd.tgk(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.App{q, y, z}, 8, nd)
    case Bk.Term.Sig{+q, +y, +z}:
      (+nd, w0) = h
      D.nd.tgk(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Sig{q, y, z}, 9, nd)
    case Bk.Term.Tup{+q, +y, +z}:
      (+nd, w0) = h
      D.nd.tgk(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Tup{q, y, z}, 10, nd)
    case Bk.Term.Prj{+y}:
      (+nd, w0) = h
      D.nd.tgk(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Prj{y}, 11, nd)
    case Bk.Term.Enu{+e}:
      (+nd, w0) = h
      D.nd.tgk(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Enu{e}, 12, nd)
    case Bk.Term.Lab{+k}:
      (+nd, w0) = h
      D.nd.tgk(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Lab{k}, 13, nd)
    case Bk.Term.Mat{+k, +y, +z}:
      (+nd, w0) = h
      D.nd.tgk(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Mat{k, y, z}, 14, nd)
    case Bk.Term.Efq{}:
      D.nd.tgk(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Efq{}, 15, h)
    case Bk.Term.Eql{+y, +z, +w}:
      (+nd, w0) = h
      D.nd.tgk(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Eql{y, z, w}, 16, nd)
    case Bk.Term.Rfl{}:
      D.nd.tgk(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Rfl{}, 17, h)
    case Bk.Term.Rwt{+y, +z, +w}:
      (+nd, w0) = h
      D.nd.tgk(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Rwt{y, z, w}, 18, nd)

# a term's tag is below 19
def atag.lt(v: Bk.Term) -> {U32.is_lt(D.A.tag(v), 19) == True{} : Bool}:
  match v:
    case Bk.Term.Var{_}:
      {==}
    case Bk.Term.Ref{_}:
      {==}
    case Bk.Term.Ann{y, z}:
      {==}
    case Bk.Term.Let{_, y, z}:
      {==}
    case Bk.Term.Typ{y}:
      {==}
    case Bk.Term.Min{y, z}:
      {==}
    case Bk.Term.All{_, y, z}:
      {==}
    case Bk.Term.Lam{_, y}:
      {==}
    case Bk.Term.App{_, y, z}:
      {==}
    case Bk.Term.Sig{_, y, z}:
      {==}
    case Bk.Term.Tup{_, y, z}:
      {==}
    case Bk.Term.Prj{y}:
      {==}
    case Bk.Term.Enu{_}:
      {==}
    case Bk.Term.Lab{_}:
      {==}
    case Bk.Term.Mat{_, y, z}:
      {==}
    case Bk.Term.Efq{}:
      {==}
    case Bk.Term.Eql{y, z, w}:
      {==}
    case Bk.Term.Rfl{}:
      {==}
    case Bk.Term.Rwt{y, z, w}:
      {==}


# x is STATIC or a node of a term of the live roots L
def Lv0(+m: Cr.Cir.Cells, +L: List<&2, D.Rt>, +x: U32) -> Bool:
  Bool.or(D.Fl(m, x, 1024), D.Nodes(L, m, x))

# every node of the term t at r is STATIC or a node of a term of L (Lv0)
def Ln(t: Bk.Term, +m: Cr.Cir.Cells, +r: U32, +L: List<&2, D.Rt>) -> Bool:
  match t:
    case Bk.Term.Var{_}:
      Lv0(m, L, r)
    case Bk.Term.Ref{_}:
      Lv0(m, L, r)
    case Bk.Term.Ann{y, z}:
      Bool.and(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L)))
    case Bk.Term.Let{_, y, z}:
      Bool.and(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L)))
    case Bk.Term.Typ{y}:
      Bool.and(Lv0(m, L, r), Ln(y, m, D.Fd(2n, m, r), L))
    case Bk.Term.Min{y, z}:
      Bool.and(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L)))
    case Bk.Term.All{_, y, z}:
      Bool.and(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L)))
    case Bk.Term.Lam{_, y}:
      Bool.and(Lv0(m, L, r), Ln(y, m, D.Fd(2n, m, r), L))
    case Bk.Term.App{_, y, z}:
      Bool.and(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L)))
    case Bk.Term.Sig{_, y, z}:
      Bool.and(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L)))
    case Bk.Term.Tup{_, y, z}:
      Bool.and(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L)))
    case Bk.Term.Prj{y}:
      Bool.and(Lv0(m, L, r), Ln(y, m, D.Fd(2n, m, r), L))
    case Bk.Term.Enu{_}:
      Lv0(m, L, r)
    case Bk.Term.Lab{_}:
      Lv0(m, L, r)
    case Bk.Term.Mat{_, y, z}:
      Bool.and(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(3n, m, r), L), Ln(z, m, D.Fd(4n, m, r), L)))
    case Bk.Term.Efq{}:
      Lv0(m, L, r)
    case Bk.Term.Eql{y, z, w}:
      Bool.and(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(2n, m, r), L), Bool.and(Ln(z, m, D.Fd(3n, m, r), L), Ln(w, m, D.Fd(4n, m, r), L))))
    case Bk.Term.Rfl{}:
      Lv0(m, L, r)
    case Bk.Term.Rwt{y, z, w}:
      Bool.and(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(2n, m, r), L), Bool.and(Ln(z, m, D.Fd(3n, m, r), L), Ln(w, m, D.Fd(4n, m, r), L))))

# the term t at a node r of a term of L: every node is a node of a term of L
def ln.live(t: Bk.Term, +dk: Bool, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +tbl: D.Tbl(m, im, fi, nx), +L: List<&2, D.Rt>,
  +hL: D.RtsK(dk, ds, m, im, fi, nx, ks, img, L), +r: U32, h: D.IsK(dk, ds, m, im, fi, nx, ks, img, r, t),
  +hr: {D.Nodes(L, m, r) == True{} : Bool}) -> {Ln(t, m, r, L) == True{} : Bool}:
  match t:
    case Bk.Term.Var{+i}:
      CK.Bo.or_ir(D.Fl(m, r, 1024), D.Nodes(L, m, r), hr)
    case Bk.Term.Ref{+k}:
      CK.Bo.or_ir(D.Fl(m, r, 1024), D.Nodes(L, m, r), hr)
    case Bk.Term.Ann{+y, +z}:
      (+nd, w0) = h
      (py, pz) = w0
      (sy, hy) = py
      (sz, hz) = pz
      +et = D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Ann{y, z}, 2, nd)
      +em = D.tbl.mask(m, im, fi, nx, Bk.Term.Ann{y, z}, tbl)
      CK.Bo.and_i(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L)), CK.Bo.or_ir(D.Fl(m, r, 1024), D.Nodes(L, m, r), hr),
        CK.Bo.and_i(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L), ln.live(y, dk, ds, m, im, fi, nx, ks, img, ps, tbl, L, hL, D.Fd(2n, m, r), hy, nodes.fs(L, dk, ds, m, im, fi, nx, ks, img, ps, tbl, r, D.Fd(2n, m, r), hL, hr, D.hm.at(m, ps, r, 2, 3, D.Fd(2n, m, r), et, {==}, em, CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, r), D.Fd(2n, m, r)), Bool.or(U32.is_eq(D.Fd(3n, m, r), D.Fd(2n, m, r)), False{}), CK.U.eq_refl(D.Fd(2n, m, r)))))), ln.live(z, dk, ds, m, im, fi, nx, ks, img, ps, tbl, L, hL, D.Fd(3n, m, r), hz, nodes.fs(L, dk, ds, m, im, fi, nx, ks, img, ps, tbl, r, D.Fd(3n, m, r), hL, hr, D.hm.at(m, ps, r, 2, 3, D.Fd(3n, m, r), et, {==}, em, CK.Bo.or_ir(U32.is_eq(D.Fd(2n, m, r), D.Fd(3n, m, r)), Bool.or(U32.is_eq(D.Fd(3n, m, r), D.Fd(3n, m, r)), False{}), CK.Bo.or_il(U32.is_eq(D.Fd(3n, m, r), D.Fd(3n, m, r)), False{}, CK.U.eq_refl(D.Fd(3n, m, r)))))))))
    case Bk.Term.Let{+q, +y, +z}:
      (+nd, w0) = h
      (hq, w2) = w0
      (py, pz) = w2
      (sy, hy) = py
      (sz, hz) = pz
      +et = D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Let{q, y, z}, 3, nd)
      +em = D.tbl.mask(m, im, fi, nx, Bk.Term.Let{q, y, z}, tbl)
      CK.Bo.and_i(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L)), CK.Bo.or_ir(D.Fl(m, r, 1024), D.Nodes(L, m, r), hr),
        CK.Bo.and_i(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L), ln.live(y, dk, ds, m, im, fi, nx, ks, img, ps, tbl, L, hL, D.Fd(2n, m, r), hy, nodes.fs(L, dk, ds, m, im, fi, nx, ks, img, ps, tbl, r, D.Fd(2n, m, r), hL, hr, D.hm.at(m, ps, r, 3, 3, D.Fd(2n, m, r), et, {==}, em, CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, r), D.Fd(2n, m, r)), Bool.or(U32.is_eq(D.Fd(3n, m, r), D.Fd(2n, m, r)), False{}), CK.U.eq_refl(D.Fd(2n, m, r)))))), ln.live(z, dk, ds, m, im, fi, nx, ks, img, ps, tbl, L, hL, D.Fd(3n, m, r), hz, nodes.fs(L, dk, ds, m, im, fi, nx, ks, img, ps, tbl, r, D.Fd(3n, m, r), hL, hr, D.hm.at(m, ps, r, 3, 3, D.Fd(3n, m, r), et, {==}, em, CK.Bo.or_ir(U32.is_eq(D.Fd(2n, m, r), D.Fd(3n, m, r)), Bool.or(U32.is_eq(D.Fd(3n, m, r), D.Fd(3n, m, r)), False{}), CK.Bo.or_il(U32.is_eq(D.Fd(3n, m, r), D.Fd(3n, m, r)), False{}, CK.U.eq_refl(D.Fd(3n, m, r)))))))))
    case Bk.Term.Typ{+y}:
      (+nd, w0) = h
      (sy, hy) = w0
      +et = D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Typ{y}, 4, nd)
      +em = D.tbl.mask(m, im, fi, nx, Bk.Term.Typ{y}, tbl)
      CK.Bo.and_i(Lv0(m, L, r), Ln(y, m, D.Fd(2n, m, r), L), CK.Bo.or_ir(D.Fl(m, r, 1024), D.Nodes(L, m, r), hr),
        ln.live(y, dk, ds, m, im, fi, nx, ks, img, ps, tbl, L, hL, D.Fd(2n, m, r), hy, nodes.fs(L, dk, ds, m, im, fi, nx, ks, img, ps, tbl, r, D.Fd(2n, m, r), hL, hr, D.hm.at(m, ps, r, 4, 1, D.Fd(2n, m, r), et, {==}, em, CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, r), D.Fd(2n, m, r)), False{}, CK.U.eq_refl(D.Fd(2n, m, r)))))))
    case Bk.Term.Min{+y, +z}:
      (+nd, w0) = h
      (py, pz) = w0
      (sy, hy) = py
      (sz, hz) = pz
      +et = D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Min{y, z}, 5, nd)
      +em = D.tbl.mask(m, im, fi, nx, Bk.Term.Min{y, z}, tbl)
      CK.Bo.and_i(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L)), CK.Bo.or_ir(D.Fl(m, r, 1024), D.Nodes(L, m, r), hr),
        CK.Bo.and_i(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L), ln.live(y, dk, ds, m, im, fi, nx, ks, img, ps, tbl, L, hL, D.Fd(2n, m, r), hy, nodes.fs(L, dk, ds, m, im, fi, nx, ks, img, ps, tbl, r, D.Fd(2n, m, r), hL, hr, D.hm.at(m, ps, r, 5, 3, D.Fd(2n, m, r), et, {==}, em, CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, r), D.Fd(2n, m, r)), Bool.or(U32.is_eq(D.Fd(3n, m, r), D.Fd(2n, m, r)), False{}), CK.U.eq_refl(D.Fd(2n, m, r)))))), ln.live(z, dk, ds, m, im, fi, nx, ks, img, ps, tbl, L, hL, D.Fd(3n, m, r), hz, nodes.fs(L, dk, ds, m, im, fi, nx, ks, img, ps, tbl, r, D.Fd(3n, m, r), hL, hr, D.hm.at(m, ps, r, 5, 3, D.Fd(3n, m, r), et, {==}, em, CK.Bo.or_ir(U32.is_eq(D.Fd(2n, m, r), D.Fd(3n, m, r)), Bool.or(U32.is_eq(D.Fd(3n, m, r), D.Fd(3n, m, r)), False{}), CK.Bo.or_il(U32.is_eq(D.Fd(3n, m, r), D.Fd(3n, m, r)), False{}, CK.U.eq_refl(D.Fd(3n, m, r)))))))))
    case Bk.Term.All{+q, +y, +z}:
      (+nd, w0) = h
      (hq, w2) = w0
      (py, pz) = w2
      (sy, hy) = py
      (sz, hz) = pz
      +et = D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.All{q, y, z}, 6, nd)
      +em = D.tbl.mask(m, im, fi, nx, Bk.Term.All{q, y, z}, tbl)
      CK.Bo.and_i(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L)), CK.Bo.or_ir(D.Fl(m, r, 1024), D.Nodes(L, m, r), hr),
        CK.Bo.and_i(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L), ln.live(y, dk, ds, m, im, fi, nx, ks, img, ps, tbl, L, hL, D.Fd(2n, m, r), hy, nodes.fs(L, dk, ds, m, im, fi, nx, ks, img, ps, tbl, r, D.Fd(2n, m, r), hL, hr, D.hm.at(m, ps, r, 6, 3, D.Fd(2n, m, r), et, {==}, em, CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, r), D.Fd(2n, m, r)), Bool.or(U32.is_eq(D.Fd(3n, m, r), D.Fd(2n, m, r)), False{}), CK.U.eq_refl(D.Fd(2n, m, r)))))), ln.live(z, dk, ds, m, im, fi, nx, ks, img, ps, tbl, L, hL, D.Fd(3n, m, r), hz, nodes.fs(L, dk, ds, m, im, fi, nx, ks, img, ps, tbl, r, D.Fd(3n, m, r), hL, hr, D.hm.at(m, ps, r, 6, 3, D.Fd(3n, m, r), et, {==}, em, CK.Bo.or_ir(U32.is_eq(D.Fd(2n, m, r), D.Fd(3n, m, r)), Bool.or(U32.is_eq(D.Fd(3n, m, r), D.Fd(3n, m, r)), False{}), CK.Bo.or_il(U32.is_eq(D.Fd(3n, m, r), D.Fd(3n, m, r)), False{}, CK.U.eq_refl(D.Fd(3n, m, r)))))))))
    case Bk.Term.Lam{+q, +y}:
      (+nd, w0) = h
      (hq, w2) = w0
      (sy, hy) = w2
      +et = D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Lam{q, y}, 7, nd)
      +em = D.tbl.mask(m, im, fi, nx, Bk.Term.Lam{q, y}, tbl)
      CK.Bo.and_i(Lv0(m, L, r), Ln(y, m, D.Fd(2n, m, r), L), CK.Bo.or_ir(D.Fl(m, r, 1024), D.Nodes(L, m, r), hr),
        ln.live(y, dk, ds, m, im, fi, nx, ks, img, ps, tbl, L, hL, D.Fd(2n, m, r), hy, nodes.fs(L, dk, ds, m, im, fi, nx, ks, img, ps, tbl, r, D.Fd(2n, m, r), hL, hr, D.hm.at(m, ps, r, 7, 1, D.Fd(2n, m, r), et, {==}, em, CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, r), D.Fd(2n, m, r)), False{}, CK.U.eq_refl(D.Fd(2n, m, r)))))))
    case Bk.Term.App{+q, +y, +z}:
      (+nd, w0) = h
      (hq, w2) = w0
      (py, pz) = w2
      (sy, hy) = py
      (sz, hz) = pz
      +et = D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.App{q, y, z}, 8, nd)
      +em = D.tbl.mask(m, im, fi, nx, Bk.Term.App{q, y, z}, tbl)
      CK.Bo.and_i(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L)), CK.Bo.or_ir(D.Fl(m, r, 1024), D.Nodes(L, m, r), hr),
        CK.Bo.and_i(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L), ln.live(y, dk, ds, m, im, fi, nx, ks, img, ps, tbl, L, hL, D.Fd(2n, m, r), hy, nodes.fs(L, dk, ds, m, im, fi, nx, ks, img, ps, tbl, r, D.Fd(2n, m, r), hL, hr, D.hm.at(m, ps, r, 8, 3, D.Fd(2n, m, r), et, {==}, em, CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, r), D.Fd(2n, m, r)), Bool.or(U32.is_eq(D.Fd(3n, m, r), D.Fd(2n, m, r)), False{}), CK.U.eq_refl(D.Fd(2n, m, r)))))), ln.live(z, dk, ds, m, im, fi, nx, ks, img, ps, tbl, L, hL, D.Fd(3n, m, r), hz, nodes.fs(L, dk, ds, m, im, fi, nx, ks, img, ps, tbl, r, D.Fd(3n, m, r), hL, hr, D.hm.at(m, ps, r, 8, 3, D.Fd(3n, m, r), et, {==}, em, CK.Bo.or_ir(U32.is_eq(D.Fd(2n, m, r), D.Fd(3n, m, r)), Bool.or(U32.is_eq(D.Fd(3n, m, r), D.Fd(3n, m, r)), False{}), CK.Bo.or_il(U32.is_eq(D.Fd(3n, m, r), D.Fd(3n, m, r)), False{}, CK.U.eq_refl(D.Fd(3n, m, r)))))))))
    case Bk.Term.Sig{+q, +y, +z}:
      (+nd, w0) = h
      (hq, w2) = w0
      (py, pz) = w2
      (sy, hy) = py
      (sz, hz) = pz
      +et = D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Sig{q, y, z}, 9, nd)
      +em = D.tbl.mask(m, im, fi, nx, Bk.Term.Sig{q, y, z}, tbl)
      CK.Bo.and_i(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L)), CK.Bo.or_ir(D.Fl(m, r, 1024), D.Nodes(L, m, r), hr),
        CK.Bo.and_i(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L), ln.live(y, dk, ds, m, im, fi, nx, ks, img, ps, tbl, L, hL, D.Fd(2n, m, r), hy, nodes.fs(L, dk, ds, m, im, fi, nx, ks, img, ps, tbl, r, D.Fd(2n, m, r), hL, hr, D.hm.at(m, ps, r, 9, 3, D.Fd(2n, m, r), et, {==}, em, CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, r), D.Fd(2n, m, r)), Bool.or(U32.is_eq(D.Fd(3n, m, r), D.Fd(2n, m, r)), False{}), CK.U.eq_refl(D.Fd(2n, m, r)))))), ln.live(z, dk, ds, m, im, fi, nx, ks, img, ps, tbl, L, hL, D.Fd(3n, m, r), hz, nodes.fs(L, dk, ds, m, im, fi, nx, ks, img, ps, tbl, r, D.Fd(3n, m, r), hL, hr, D.hm.at(m, ps, r, 9, 3, D.Fd(3n, m, r), et, {==}, em, CK.Bo.or_ir(U32.is_eq(D.Fd(2n, m, r), D.Fd(3n, m, r)), Bool.or(U32.is_eq(D.Fd(3n, m, r), D.Fd(3n, m, r)), False{}), CK.Bo.or_il(U32.is_eq(D.Fd(3n, m, r), D.Fd(3n, m, r)), False{}, CK.U.eq_refl(D.Fd(3n, m, r)))))))))
    case Bk.Term.Tup{+q, +y, +z}:
      (+nd, w0) = h
      (hq, w2) = w0
      (py, pz) = w2
      (sy, hy) = py
      (sz, hz) = pz
      +et = D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Tup{q, y, z}, 10, nd)
      +em = D.tbl.mask(m, im, fi, nx, Bk.Term.Tup{q, y, z}, tbl)
      CK.Bo.and_i(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L)), CK.Bo.or_ir(D.Fl(m, r, 1024), D.Nodes(L, m, r), hr),
        CK.Bo.and_i(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L), ln.live(y, dk, ds, m, im, fi, nx, ks, img, ps, tbl, L, hL, D.Fd(2n, m, r), hy, nodes.fs(L, dk, ds, m, im, fi, nx, ks, img, ps, tbl, r, D.Fd(2n, m, r), hL, hr, D.hm.at(m, ps, r, 10, 3, D.Fd(2n, m, r), et, {==}, em, CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, r), D.Fd(2n, m, r)), Bool.or(U32.is_eq(D.Fd(3n, m, r), D.Fd(2n, m, r)), False{}), CK.U.eq_refl(D.Fd(2n, m, r)))))), ln.live(z, dk, ds, m, im, fi, nx, ks, img, ps, tbl, L, hL, D.Fd(3n, m, r), hz, nodes.fs(L, dk, ds, m, im, fi, nx, ks, img, ps, tbl, r, D.Fd(3n, m, r), hL, hr, D.hm.at(m, ps, r, 10, 3, D.Fd(3n, m, r), et, {==}, em, CK.Bo.or_ir(U32.is_eq(D.Fd(2n, m, r), D.Fd(3n, m, r)), Bool.or(U32.is_eq(D.Fd(3n, m, r), D.Fd(3n, m, r)), False{}), CK.Bo.or_il(U32.is_eq(D.Fd(3n, m, r), D.Fd(3n, m, r)), False{}, CK.U.eq_refl(D.Fd(3n, m, r)))))))))
    case Bk.Term.Prj{+y}:
      (+nd, w0) = h
      (sy, hy) = w0
      +et = D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Prj{y}, 11, nd)
      +em = D.tbl.mask(m, im, fi, nx, Bk.Term.Prj{y}, tbl)
      CK.Bo.and_i(Lv0(m, L, r), Ln(y, m, D.Fd(2n, m, r), L), CK.Bo.or_ir(D.Fl(m, r, 1024), D.Nodes(L, m, r), hr),
        ln.live(y, dk, ds, m, im, fi, nx, ks, img, ps, tbl, L, hL, D.Fd(2n, m, r), hy, nodes.fs(L, dk, ds, m, im, fi, nx, ks, img, ps, tbl, r, D.Fd(2n, m, r), hL, hr, D.hm.at(m, ps, r, 11, 1, D.Fd(2n, m, r), et, {==}, em, CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, r), D.Fd(2n, m, r)), False{}, CK.U.eq_refl(D.Fd(2n, m, r)))))))
    case Bk.Term.Enu{+e}:
      CK.Bo.or_ir(D.Fl(m, r, 1024), D.Nodes(L, m, r), hr)
    case Bk.Term.Lab{+k}:
      CK.Bo.or_ir(D.Fl(m, r, 1024), D.Nodes(L, m, r), hr)
    case Bk.Term.Mat{+k, +y, +z}:
      (+nd, w0) = h
      (nm, w2) = w0
      (py, pz) = w2
      (sy, hy) = py
      (sz, hz) = pz
      +et = D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Mat{k, y, z}, 14, nd)
      +em = D.tbl.mask(m, im, fi, nx, Bk.Term.Mat{k, y, z}, tbl)
      CK.Bo.and_i(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(3n, m, r), L), Ln(z, m, D.Fd(4n, m, r), L)), CK.Bo.or_ir(D.Fl(m, r, 1024), D.Nodes(L, m, r), hr),
        CK.Bo.and_i(Ln(y, m, D.Fd(3n, m, r), L), Ln(z, m, D.Fd(4n, m, r), L), ln.live(y, dk, ds, m, im, fi, nx, ks, img, ps, tbl, L, hL, D.Fd(3n, m, r), hy, nodes.fs(L, dk, ds, m, im, fi, nx, ks, img, ps, tbl, r, D.Fd(3n, m, r), hL, hr, D.hm.at(m, ps, r, 14, 6, D.Fd(3n, m, r), et, {==}, em, CK.Bo.or_il(U32.is_eq(D.Fd(3n, m, r), D.Fd(3n, m, r)), Bool.or(U32.is_eq(D.Fd(4n, m, r), D.Fd(3n, m, r)), False{}), CK.U.eq_refl(D.Fd(3n, m, r)))))), ln.live(z, dk, ds, m, im, fi, nx, ks, img, ps, tbl, L, hL, D.Fd(4n, m, r), hz, nodes.fs(L, dk, ds, m, im, fi, nx, ks, img, ps, tbl, r, D.Fd(4n, m, r), hL, hr, D.hm.at(m, ps, r, 14, 6, D.Fd(4n, m, r), et, {==}, em, CK.Bo.or_ir(U32.is_eq(D.Fd(3n, m, r), D.Fd(4n, m, r)), Bool.or(U32.is_eq(D.Fd(4n, m, r), D.Fd(4n, m, r)), False{}), CK.Bo.or_il(U32.is_eq(D.Fd(4n, m, r), D.Fd(4n, m, r)), False{}, CK.U.eq_refl(D.Fd(4n, m, r)))))))))
    case Bk.Term.Efq{}:
      CK.Bo.or_ir(D.Fl(m, r, 1024), D.Nodes(L, m, r), hr)
    case Bk.Term.Eql{+y, +z, +w}:
      (+nd, w0) = h
      (py, w2) = w0
      (sy, hy) = py
      (pz, pw) = w2
      (sz, hz) = pz
      (sw, hw) = pw
      +et = D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Eql{y, z, w}, 16, nd)
      +em = D.tbl.mask(m, im, fi, nx, Bk.Term.Eql{y, z, w}, tbl)
      CK.Bo.and_i(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(2n, m, r), L), Bool.and(Ln(z, m, D.Fd(3n, m, r), L), Ln(w, m, D.Fd(4n, m, r), L))), CK.Bo.or_ir(D.Fl(m, r, 1024), D.Nodes(L, m, r), hr),
        CK.Bo.and_i(Ln(y, m, D.Fd(2n, m, r), L), Bool.and(Ln(z, m, D.Fd(3n, m, r), L), Ln(w, m, D.Fd(4n, m, r), L)), ln.live(y, dk, ds, m, im, fi, nx, ks, img, ps, tbl, L, hL, D.Fd(2n, m, r), hy, nodes.fs(L, dk, ds, m, im, fi, nx, ks, img, ps, tbl, r, D.Fd(2n, m, r), hL, hr, D.hm.at(m, ps, r, 16, 7, D.Fd(2n, m, r), et, {==}, em, CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, r), D.Fd(2n, m, r)), Bool.or(U32.is_eq(D.Fd(3n, m, r), D.Fd(2n, m, r)), Bool.or(U32.is_eq(D.Fd(4n, m, r), D.Fd(2n, m, r)), False{})), CK.U.eq_refl(D.Fd(2n, m, r)))))), CK.Bo.and_i(Ln(z, m, D.Fd(3n, m, r), L), Ln(w, m, D.Fd(4n, m, r), L), ln.live(z, dk, ds, m, im, fi, nx, ks, img, ps, tbl, L, hL, D.Fd(3n, m, r), hz, nodes.fs(L, dk, ds, m, im, fi, nx, ks, img, ps, tbl, r, D.Fd(3n, m, r), hL, hr, D.hm.at(m, ps, r, 16, 7, D.Fd(3n, m, r), et, {==}, em, CK.Bo.or_ir(U32.is_eq(D.Fd(2n, m, r), D.Fd(3n, m, r)), Bool.or(U32.is_eq(D.Fd(3n, m, r), D.Fd(3n, m, r)), Bool.or(U32.is_eq(D.Fd(4n, m, r), D.Fd(3n, m, r)), False{})), CK.Bo.or_il(U32.is_eq(D.Fd(3n, m, r), D.Fd(3n, m, r)), Bool.or(U32.is_eq(D.Fd(4n, m, r), D.Fd(3n, m, r)), False{}), CK.U.eq_refl(D.Fd(3n, m, r))))))), ln.live(w, dk, ds, m, im, fi, nx, ks, img, ps, tbl, L, hL, D.Fd(4n, m, r), hw, nodes.fs(L, dk, ds, m, im, fi, nx, ks, img, ps, tbl, r, D.Fd(4n, m, r), hL, hr, D.hm.at(m, ps, r, 16, 7, D.Fd(4n, m, r), et, {==}, em, CK.Bo.or_ir(U32.is_eq(D.Fd(2n, m, r), D.Fd(4n, m, r)), Bool.or(U32.is_eq(D.Fd(3n, m, r), D.Fd(4n, m, r)), Bool.or(U32.is_eq(D.Fd(4n, m, r), D.Fd(4n, m, r)), False{})), CK.Bo.or_ir(U32.is_eq(D.Fd(3n, m, r), D.Fd(4n, m, r)), Bool.or(U32.is_eq(D.Fd(4n, m, r), D.Fd(4n, m, r)), False{}), CK.Bo.or_il(U32.is_eq(D.Fd(4n, m, r), D.Fd(4n, m, r)), False{}, CK.U.eq_refl(D.Fd(4n, m, r)))))))))))
    case Bk.Term.Rfl{}:
      CK.Bo.or_ir(D.Fl(m, r, 1024), D.Nodes(L, m, r), hr)
    case Bk.Term.Rwt{+y, +z, +w}:
      (+nd, w0) = h
      (py, w2) = w0
      (sy, hy) = py
      (pz, pw) = w2
      (sz, hz) = pz
      (sw, hw) = pw
      +et = D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Rwt{y, z, w}, 18, nd)
      +em = D.tbl.mask(m, im, fi, nx, Bk.Term.Rwt{y, z, w}, tbl)
      CK.Bo.and_i(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(2n, m, r), L), Bool.and(Ln(z, m, D.Fd(3n, m, r), L), Ln(w, m, D.Fd(4n, m, r), L))), CK.Bo.or_ir(D.Fl(m, r, 1024), D.Nodes(L, m, r), hr),
        CK.Bo.and_i(Ln(y, m, D.Fd(2n, m, r), L), Bool.and(Ln(z, m, D.Fd(3n, m, r), L), Ln(w, m, D.Fd(4n, m, r), L)), ln.live(y, dk, ds, m, im, fi, nx, ks, img, ps, tbl, L, hL, D.Fd(2n, m, r), hy, nodes.fs(L, dk, ds, m, im, fi, nx, ks, img, ps, tbl, r, D.Fd(2n, m, r), hL, hr, D.hm.at(m, ps, r, 18, 7, D.Fd(2n, m, r), et, {==}, em, CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, r), D.Fd(2n, m, r)), Bool.or(U32.is_eq(D.Fd(3n, m, r), D.Fd(2n, m, r)), Bool.or(U32.is_eq(D.Fd(4n, m, r), D.Fd(2n, m, r)), False{})), CK.U.eq_refl(D.Fd(2n, m, r)))))), CK.Bo.and_i(Ln(z, m, D.Fd(3n, m, r), L), Ln(w, m, D.Fd(4n, m, r), L), ln.live(z, dk, ds, m, im, fi, nx, ks, img, ps, tbl, L, hL, D.Fd(3n, m, r), hz, nodes.fs(L, dk, ds, m, im, fi, nx, ks, img, ps, tbl, r, D.Fd(3n, m, r), hL, hr, D.hm.at(m, ps, r, 18, 7, D.Fd(3n, m, r), et, {==}, em, CK.Bo.or_ir(U32.is_eq(D.Fd(2n, m, r), D.Fd(3n, m, r)), Bool.or(U32.is_eq(D.Fd(3n, m, r), D.Fd(3n, m, r)), Bool.or(U32.is_eq(D.Fd(4n, m, r), D.Fd(3n, m, r)), False{})), CK.Bo.or_il(U32.is_eq(D.Fd(3n, m, r), D.Fd(3n, m, r)), Bool.or(U32.is_eq(D.Fd(4n, m, r), D.Fd(3n, m, r)), False{}), CK.U.eq_refl(D.Fd(3n, m, r))))))), ln.live(w, dk, ds, m, im, fi, nx, ks, img, ps, tbl, L, hL, D.Fd(4n, m, r), hw, nodes.fs(L, dk, ds, m, im, fi, nx, ks, img, ps, tbl, r, D.Fd(4n, m, r), hL, hr, D.hm.at(m, ps, r, 18, 7, D.Fd(4n, m, r), et, {==}, em, CK.Bo.or_ir(U32.is_eq(D.Fd(2n, m, r), D.Fd(4n, m, r)), Bool.or(U32.is_eq(D.Fd(3n, m, r), D.Fd(4n, m, r)), Bool.or(U32.is_eq(D.Fd(4n, m, r), D.Fd(4n, m, r)), False{})), CK.Bo.or_ir(U32.is_eq(D.Fd(3n, m, r), D.Fd(4n, m, r)), Bool.or(U32.is_eq(D.Fd(4n, m, r), D.Fd(4n, m, r)), False{}), CK.Bo.or_il(U32.is_eq(D.Fd(4n, m, r), D.Fd(4n, m, r)), False{}, CK.U.eq_refl(D.Fd(4n, m, r)))))))))))

# the term t at a STATIC cell r: every node is STATIC (Clo, Sp)
def ln.stat(t: Bk.Term, +dk: Bool, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +cs: List<&2, U32>, +hc: List<&2, U32>,
  +tbl: D.Tbl(m, im, fi, nx), +L: List<&2, D.Rt>, +r: U32, h: D.IsK(dk, ds, m, im, fi, nx, ks, img, r, t),
  +hs: {D.Fl(m, r, 1024) == True{} : Bool},
  +hcl: {D.Clo(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, cs, hc) == True{} : Bool}) -> {Ln(t, m, r, L) == True{} : Bool}:
  match t:
    case Bk.Term.Var{+i}:
      CK.Bo.or_il(D.Fl(m, r, 1024), D.Nodes(L, m, r), hs)
    case Bk.Term.Ref{+k}:
      CK.Bo.or_il(D.Fl(m, r, 1024), D.Nodes(L, m, r), hs)
    case Bk.Term.Ann{+y, +z}:
      (+nd, w0) = h
      (py, pz) = w0
      (sy, hy) = py
      (sz, hz) = pz
      +et = D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Ann{y, z}, 2, nd)
      +em = D.tbl.mask(m, im, fi, nx, Bk.Term.Ann{y, z}, tbl)
      CK.Bo.and_i(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L)), CK.Bo.or_il(D.Fl(m, r, 1024), D.Nodes(L, m, r), hs),
        CK.Bo.and_i(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L), ln.stat(y, dk, ds, m, im, fi, nx, ks, img, ps, cs, hc, tbl, L, D.Fd(2n, m, r), hy, part.st(D.Own(fi, nx, r), m, ps, fi, nx, cs, hc, r, D.Fd(2n, m, r), {==}, hs, hcl, sy, D.hm.at(m, ps, r, 2, 3, D.Fd(2n, m, r), et, {==}, em, CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, r), D.Fd(2n, m, r)), Bool.or(U32.is_eq(D.Fd(3n, m, r), D.Fd(2n, m, r)), False{}), CK.U.eq_refl(D.Fd(2n, m, r))))), hcl), ln.stat(z, dk, ds, m, im, fi, nx, ks, img, ps, cs, hc, tbl, L, D.Fd(3n, m, r), hz, part.st(D.Own(fi, nx, r), m, ps, fi, nx, cs, hc, r, D.Fd(3n, m, r), {==}, hs, hcl, sz, D.hm.at(m, ps, r, 2, 3, D.Fd(3n, m, r), et, {==}, em, CK.Bo.or_ir(U32.is_eq(D.Fd(2n, m, r), D.Fd(3n, m, r)), Bool.or(U32.is_eq(D.Fd(3n, m, r), D.Fd(3n, m, r)), False{}), CK.Bo.or_il(U32.is_eq(D.Fd(3n, m, r), D.Fd(3n, m, r)), False{}, CK.U.eq_refl(D.Fd(3n, m, r)))))), hcl)))
    case Bk.Term.Let{+q, +y, +z}:
      (+nd, w0) = h
      (hq, w2) = w0
      (py, pz) = w2
      (sy, hy) = py
      (sz, hz) = pz
      +et = D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Let{q, y, z}, 3, nd)
      +em = D.tbl.mask(m, im, fi, nx, Bk.Term.Let{q, y, z}, tbl)
      CK.Bo.and_i(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L)), CK.Bo.or_il(D.Fl(m, r, 1024), D.Nodes(L, m, r), hs),
        CK.Bo.and_i(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L), ln.stat(y, dk, ds, m, im, fi, nx, ks, img, ps, cs, hc, tbl, L, D.Fd(2n, m, r), hy, part.st(D.Own(fi, nx, r), m, ps, fi, nx, cs, hc, r, D.Fd(2n, m, r), {==}, hs, hcl, sy, D.hm.at(m, ps, r, 3, 3, D.Fd(2n, m, r), et, {==}, em, CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, r), D.Fd(2n, m, r)), Bool.or(U32.is_eq(D.Fd(3n, m, r), D.Fd(2n, m, r)), False{}), CK.U.eq_refl(D.Fd(2n, m, r))))), hcl), ln.stat(z, dk, ds, m, im, fi, nx, ks, img, ps, cs, hc, tbl, L, D.Fd(3n, m, r), hz, part.st(D.Own(fi, nx, r), m, ps, fi, nx, cs, hc, r, D.Fd(3n, m, r), {==}, hs, hcl, sz, D.hm.at(m, ps, r, 3, 3, D.Fd(3n, m, r), et, {==}, em, CK.Bo.or_ir(U32.is_eq(D.Fd(2n, m, r), D.Fd(3n, m, r)), Bool.or(U32.is_eq(D.Fd(3n, m, r), D.Fd(3n, m, r)), False{}), CK.Bo.or_il(U32.is_eq(D.Fd(3n, m, r), D.Fd(3n, m, r)), False{}, CK.U.eq_refl(D.Fd(3n, m, r)))))), hcl)))
    case Bk.Term.Typ{+y}:
      (+nd, w0) = h
      (sy, hy) = w0
      +et = D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Typ{y}, 4, nd)
      +em = D.tbl.mask(m, im, fi, nx, Bk.Term.Typ{y}, tbl)
      CK.Bo.and_i(Lv0(m, L, r), Ln(y, m, D.Fd(2n, m, r), L), CK.Bo.or_il(D.Fl(m, r, 1024), D.Nodes(L, m, r), hs),
        ln.stat(y, dk, ds, m, im, fi, nx, ks, img, ps, cs, hc, tbl, L, D.Fd(2n, m, r), hy, part.st(D.Own(fi, nx, r), m, ps, fi, nx, cs, hc, r, D.Fd(2n, m, r), {==}, hs, hcl, sy, D.hm.at(m, ps, r, 4, 1, D.Fd(2n, m, r), et, {==}, em, CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, r), D.Fd(2n, m, r)), False{}, CK.U.eq_refl(D.Fd(2n, m, r))))), hcl))
    case Bk.Term.Min{+y, +z}:
      (+nd, w0) = h
      (py, pz) = w0
      (sy, hy) = py
      (sz, hz) = pz
      +et = D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Min{y, z}, 5, nd)
      +em = D.tbl.mask(m, im, fi, nx, Bk.Term.Min{y, z}, tbl)
      CK.Bo.and_i(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L)), CK.Bo.or_il(D.Fl(m, r, 1024), D.Nodes(L, m, r), hs),
        CK.Bo.and_i(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L), ln.stat(y, dk, ds, m, im, fi, nx, ks, img, ps, cs, hc, tbl, L, D.Fd(2n, m, r), hy, part.st(D.Own(fi, nx, r), m, ps, fi, nx, cs, hc, r, D.Fd(2n, m, r), {==}, hs, hcl, sy, D.hm.at(m, ps, r, 5, 3, D.Fd(2n, m, r), et, {==}, em, CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, r), D.Fd(2n, m, r)), Bool.or(U32.is_eq(D.Fd(3n, m, r), D.Fd(2n, m, r)), False{}), CK.U.eq_refl(D.Fd(2n, m, r))))), hcl), ln.stat(z, dk, ds, m, im, fi, nx, ks, img, ps, cs, hc, tbl, L, D.Fd(3n, m, r), hz, part.st(D.Own(fi, nx, r), m, ps, fi, nx, cs, hc, r, D.Fd(3n, m, r), {==}, hs, hcl, sz, D.hm.at(m, ps, r, 5, 3, D.Fd(3n, m, r), et, {==}, em, CK.Bo.or_ir(U32.is_eq(D.Fd(2n, m, r), D.Fd(3n, m, r)), Bool.or(U32.is_eq(D.Fd(3n, m, r), D.Fd(3n, m, r)), False{}), CK.Bo.or_il(U32.is_eq(D.Fd(3n, m, r), D.Fd(3n, m, r)), False{}, CK.U.eq_refl(D.Fd(3n, m, r)))))), hcl)))
    case Bk.Term.All{+q, +y, +z}:
      (+nd, w0) = h
      (hq, w2) = w0
      (py, pz) = w2
      (sy, hy) = py
      (sz, hz) = pz
      +et = D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.All{q, y, z}, 6, nd)
      +em = D.tbl.mask(m, im, fi, nx, Bk.Term.All{q, y, z}, tbl)
      CK.Bo.and_i(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L)), CK.Bo.or_il(D.Fl(m, r, 1024), D.Nodes(L, m, r), hs),
        CK.Bo.and_i(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L), ln.stat(y, dk, ds, m, im, fi, nx, ks, img, ps, cs, hc, tbl, L, D.Fd(2n, m, r), hy, part.st(D.Own(fi, nx, r), m, ps, fi, nx, cs, hc, r, D.Fd(2n, m, r), {==}, hs, hcl, sy, D.hm.at(m, ps, r, 6, 3, D.Fd(2n, m, r), et, {==}, em, CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, r), D.Fd(2n, m, r)), Bool.or(U32.is_eq(D.Fd(3n, m, r), D.Fd(2n, m, r)), False{}), CK.U.eq_refl(D.Fd(2n, m, r))))), hcl), ln.stat(z, dk, ds, m, im, fi, nx, ks, img, ps, cs, hc, tbl, L, D.Fd(3n, m, r), hz, part.st(D.Own(fi, nx, r), m, ps, fi, nx, cs, hc, r, D.Fd(3n, m, r), {==}, hs, hcl, sz, D.hm.at(m, ps, r, 6, 3, D.Fd(3n, m, r), et, {==}, em, CK.Bo.or_ir(U32.is_eq(D.Fd(2n, m, r), D.Fd(3n, m, r)), Bool.or(U32.is_eq(D.Fd(3n, m, r), D.Fd(3n, m, r)), False{}), CK.Bo.or_il(U32.is_eq(D.Fd(3n, m, r), D.Fd(3n, m, r)), False{}, CK.U.eq_refl(D.Fd(3n, m, r)))))), hcl)))
    case Bk.Term.Lam{+q, +y}:
      (+nd, w0) = h
      (hq, w2) = w0
      (sy, hy) = w2
      +et = D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Lam{q, y}, 7, nd)
      +em = D.tbl.mask(m, im, fi, nx, Bk.Term.Lam{q, y}, tbl)
      CK.Bo.and_i(Lv0(m, L, r), Ln(y, m, D.Fd(2n, m, r), L), CK.Bo.or_il(D.Fl(m, r, 1024), D.Nodes(L, m, r), hs),
        ln.stat(y, dk, ds, m, im, fi, nx, ks, img, ps, cs, hc, tbl, L, D.Fd(2n, m, r), hy, part.st(D.Own(fi, nx, r), m, ps, fi, nx, cs, hc, r, D.Fd(2n, m, r), {==}, hs, hcl, sy, D.hm.at(m, ps, r, 7, 1, D.Fd(2n, m, r), et, {==}, em, CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, r), D.Fd(2n, m, r)), False{}, CK.U.eq_refl(D.Fd(2n, m, r))))), hcl))
    case Bk.Term.App{+q, +y, +z}:
      (+nd, w0) = h
      (hq, w2) = w0
      (py, pz) = w2
      (sy, hy) = py
      (sz, hz) = pz
      +et = D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.App{q, y, z}, 8, nd)
      +em = D.tbl.mask(m, im, fi, nx, Bk.Term.App{q, y, z}, tbl)
      CK.Bo.and_i(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L)), CK.Bo.or_il(D.Fl(m, r, 1024), D.Nodes(L, m, r), hs),
        CK.Bo.and_i(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L), ln.stat(y, dk, ds, m, im, fi, nx, ks, img, ps, cs, hc, tbl, L, D.Fd(2n, m, r), hy, part.st(D.Own(fi, nx, r), m, ps, fi, nx, cs, hc, r, D.Fd(2n, m, r), {==}, hs, hcl, sy, D.hm.at(m, ps, r, 8, 3, D.Fd(2n, m, r), et, {==}, em, CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, r), D.Fd(2n, m, r)), Bool.or(U32.is_eq(D.Fd(3n, m, r), D.Fd(2n, m, r)), False{}), CK.U.eq_refl(D.Fd(2n, m, r))))), hcl), ln.stat(z, dk, ds, m, im, fi, nx, ks, img, ps, cs, hc, tbl, L, D.Fd(3n, m, r), hz, part.st(D.Own(fi, nx, r), m, ps, fi, nx, cs, hc, r, D.Fd(3n, m, r), {==}, hs, hcl, sz, D.hm.at(m, ps, r, 8, 3, D.Fd(3n, m, r), et, {==}, em, CK.Bo.or_ir(U32.is_eq(D.Fd(2n, m, r), D.Fd(3n, m, r)), Bool.or(U32.is_eq(D.Fd(3n, m, r), D.Fd(3n, m, r)), False{}), CK.Bo.or_il(U32.is_eq(D.Fd(3n, m, r), D.Fd(3n, m, r)), False{}, CK.U.eq_refl(D.Fd(3n, m, r)))))), hcl)))
    case Bk.Term.Sig{+q, +y, +z}:
      (+nd, w0) = h
      (hq, w2) = w0
      (py, pz) = w2
      (sy, hy) = py
      (sz, hz) = pz
      +et = D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Sig{q, y, z}, 9, nd)
      +em = D.tbl.mask(m, im, fi, nx, Bk.Term.Sig{q, y, z}, tbl)
      CK.Bo.and_i(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L)), CK.Bo.or_il(D.Fl(m, r, 1024), D.Nodes(L, m, r), hs),
        CK.Bo.and_i(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L), ln.stat(y, dk, ds, m, im, fi, nx, ks, img, ps, cs, hc, tbl, L, D.Fd(2n, m, r), hy, part.st(D.Own(fi, nx, r), m, ps, fi, nx, cs, hc, r, D.Fd(2n, m, r), {==}, hs, hcl, sy, D.hm.at(m, ps, r, 9, 3, D.Fd(2n, m, r), et, {==}, em, CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, r), D.Fd(2n, m, r)), Bool.or(U32.is_eq(D.Fd(3n, m, r), D.Fd(2n, m, r)), False{}), CK.U.eq_refl(D.Fd(2n, m, r))))), hcl), ln.stat(z, dk, ds, m, im, fi, nx, ks, img, ps, cs, hc, tbl, L, D.Fd(3n, m, r), hz, part.st(D.Own(fi, nx, r), m, ps, fi, nx, cs, hc, r, D.Fd(3n, m, r), {==}, hs, hcl, sz, D.hm.at(m, ps, r, 9, 3, D.Fd(3n, m, r), et, {==}, em, CK.Bo.or_ir(U32.is_eq(D.Fd(2n, m, r), D.Fd(3n, m, r)), Bool.or(U32.is_eq(D.Fd(3n, m, r), D.Fd(3n, m, r)), False{}), CK.Bo.or_il(U32.is_eq(D.Fd(3n, m, r), D.Fd(3n, m, r)), False{}, CK.U.eq_refl(D.Fd(3n, m, r)))))), hcl)))
    case Bk.Term.Tup{+q, +y, +z}:
      (+nd, w0) = h
      (hq, w2) = w0
      (py, pz) = w2
      (sy, hy) = py
      (sz, hz) = pz
      +et = D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Tup{q, y, z}, 10, nd)
      +em = D.tbl.mask(m, im, fi, nx, Bk.Term.Tup{q, y, z}, tbl)
      CK.Bo.and_i(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L)), CK.Bo.or_il(D.Fl(m, r, 1024), D.Nodes(L, m, r), hs),
        CK.Bo.and_i(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L), ln.stat(y, dk, ds, m, im, fi, nx, ks, img, ps, cs, hc, tbl, L, D.Fd(2n, m, r), hy, part.st(D.Own(fi, nx, r), m, ps, fi, nx, cs, hc, r, D.Fd(2n, m, r), {==}, hs, hcl, sy, D.hm.at(m, ps, r, 10, 3, D.Fd(2n, m, r), et, {==}, em, CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, r), D.Fd(2n, m, r)), Bool.or(U32.is_eq(D.Fd(3n, m, r), D.Fd(2n, m, r)), False{}), CK.U.eq_refl(D.Fd(2n, m, r))))), hcl), ln.stat(z, dk, ds, m, im, fi, nx, ks, img, ps, cs, hc, tbl, L, D.Fd(3n, m, r), hz, part.st(D.Own(fi, nx, r), m, ps, fi, nx, cs, hc, r, D.Fd(3n, m, r), {==}, hs, hcl, sz, D.hm.at(m, ps, r, 10, 3, D.Fd(3n, m, r), et, {==}, em, CK.Bo.or_ir(U32.is_eq(D.Fd(2n, m, r), D.Fd(3n, m, r)), Bool.or(U32.is_eq(D.Fd(3n, m, r), D.Fd(3n, m, r)), False{}), CK.Bo.or_il(U32.is_eq(D.Fd(3n, m, r), D.Fd(3n, m, r)), False{}, CK.U.eq_refl(D.Fd(3n, m, r)))))), hcl)))
    case Bk.Term.Prj{+y}:
      (+nd, w0) = h
      (sy, hy) = w0
      +et = D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Prj{y}, 11, nd)
      +em = D.tbl.mask(m, im, fi, nx, Bk.Term.Prj{y}, tbl)
      CK.Bo.and_i(Lv0(m, L, r), Ln(y, m, D.Fd(2n, m, r), L), CK.Bo.or_il(D.Fl(m, r, 1024), D.Nodes(L, m, r), hs),
        ln.stat(y, dk, ds, m, im, fi, nx, ks, img, ps, cs, hc, tbl, L, D.Fd(2n, m, r), hy, part.st(D.Own(fi, nx, r), m, ps, fi, nx, cs, hc, r, D.Fd(2n, m, r), {==}, hs, hcl, sy, D.hm.at(m, ps, r, 11, 1, D.Fd(2n, m, r), et, {==}, em, CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, r), D.Fd(2n, m, r)), False{}, CK.U.eq_refl(D.Fd(2n, m, r))))), hcl))
    case Bk.Term.Enu{+e}:
      CK.Bo.or_il(D.Fl(m, r, 1024), D.Nodes(L, m, r), hs)
    case Bk.Term.Lab{+k}:
      CK.Bo.or_il(D.Fl(m, r, 1024), D.Nodes(L, m, r), hs)
    case Bk.Term.Mat{+k, +y, +z}:
      (+nd, w0) = h
      (nm, w2) = w0
      (py, pz) = w2
      (sy, hy) = py
      (sz, hz) = pz
      +et = D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Mat{k, y, z}, 14, nd)
      +em = D.tbl.mask(m, im, fi, nx, Bk.Term.Mat{k, y, z}, tbl)
      CK.Bo.and_i(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(3n, m, r), L), Ln(z, m, D.Fd(4n, m, r), L)), CK.Bo.or_il(D.Fl(m, r, 1024), D.Nodes(L, m, r), hs),
        CK.Bo.and_i(Ln(y, m, D.Fd(3n, m, r), L), Ln(z, m, D.Fd(4n, m, r), L), ln.stat(y, dk, ds, m, im, fi, nx, ks, img, ps, cs, hc, tbl, L, D.Fd(3n, m, r), hy, part.st(D.Own(fi, nx, r), m, ps, fi, nx, cs, hc, r, D.Fd(3n, m, r), {==}, hs, hcl, sy, D.hm.at(m, ps, r, 14, 6, D.Fd(3n, m, r), et, {==}, em, CK.Bo.or_il(U32.is_eq(D.Fd(3n, m, r), D.Fd(3n, m, r)), Bool.or(U32.is_eq(D.Fd(4n, m, r), D.Fd(3n, m, r)), False{}), CK.U.eq_refl(D.Fd(3n, m, r))))), hcl), ln.stat(z, dk, ds, m, im, fi, nx, ks, img, ps, cs, hc, tbl, L, D.Fd(4n, m, r), hz, part.st(D.Own(fi, nx, r), m, ps, fi, nx, cs, hc, r, D.Fd(4n, m, r), {==}, hs, hcl, sz, D.hm.at(m, ps, r, 14, 6, D.Fd(4n, m, r), et, {==}, em, CK.Bo.or_ir(U32.is_eq(D.Fd(3n, m, r), D.Fd(4n, m, r)), Bool.or(U32.is_eq(D.Fd(4n, m, r), D.Fd(4n, m, r)), False{}), CK.Bo.or_il(U32.is_eq(D.Fd(4n, m, r), D.Fd(4n, m, r)), False{}, CK.U.eq_refl(D.Fd(4n, m, r)))))), hcl)))
    case Bk.Term.Efq{}:
      CK.Bo.or_il(D.Fl(m, r, 1024), D.Nodes(L, m, r), hs)
    case Bk.Term.Eql{+y, +z, +w}:
      (+nd, w0) = h
      (py, w2) = w0
      (sy, hy) = py
      (pz, pw) = w2
      (sz, hz) = pz
      (sw, hw) = pw
      +et = D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Eql{y, z, w}, 16, nd)
      +em = D.tbl.mask(m, im, fi, nx, Bk.Term.Eql{y, z, w}, tbl)
      CK.Bo.and_i(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(2n, m, r), L), Bool.and(Ln(z, m, D.Fd(3n, m, r), L), Ln(w, m, D.Fd(4n, m, r), L))), CK.Bo.or_il(D.Fl(m, r, 1024), D.Nodes(L, m, r), hs),
        CK.Bo.and_i(Ln(y, m, D.Fd(2n, m, r), L), Bool.and(Ln(z, m, D.Fd(3n, m, r), L), Ln(w, m, D.Fd(4n, m, r), L)), ln.stat(y, dk, ds, m, im, fi, nx, ks, img, ps, cs, hc, tbl, L, D.Fd(2n, m, r), hy, part.st(D.Own(fi, nx, r), m, ps, fi, nx, cs, hc, r, D.Fd(2n, m, r), {==}, hs, hcl, sy, D.hm.at(m, ps, r, 16, 7, D.Fd(2n, m, r), et, {==}, em, CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, r), D.Fd(2n, m, r)), Bool.or(U32.is_eq(D.Fd(3n, m, r), D.Fd(2n, m, r)), Bool.or(U32.is_eq(D.Fd(4n, m, r), D.Fd(2n, m, r)), False{})), CK.U.eq_refl(D.Fd(2n, m, r))))), hcl), CK.Bo.and_i(Ln(z, m, D.Fd(3n, m, r), L), Ln(w, m, D.Fd(4n, m, r), L), ln.stat(z, dk, ds, m, im, fi, nx, ks, img, ps, cs, hc, tbl, L, D.Fd(3n, m, r), hz, part.st(D.Own(fi, nx, r), m, ps, fi, nx, cs, hc, r, D.Fd(3n, m, r), {==}, hs, hcl, sz, D.hm.at(m, ps, r, 16, 7, D.Fd(3n, m, r), et, {==}, em, CK.Bo.or_ir(U32.is_eq(D.Fd(2n, m, r), D.Fd(3n, m, r)), Bool.or(U32.is_eq(D.Fd(3n, m, r), D.Fd(3n, m, r)), Bool.or(U32.is_eq(D.Fd(4n, m, r), D.Fd(3n, m, r)), False{})), CK.Bo.or_il(U32.is_eq(D.Fd(3n, m, r), D.Fd(3n, m, r)), Bool.or(U32.is_eq(D.Fd(4n, m, r), D.Fd(3n, m, r)), False{}), CK.U.eq_refl(D.Fd(3n, m, r)))))), hcl), ln.stat(w, dk, ds, m, im, fi, nx, ks, img, ps, cs, hc, tbl, L, D.Fd(4n, m, r), hw, part.st(D.Own(fi, nx, r), m, ps, fi, nx, cs, hc, r, D.Fd(4n, m, r), {==}, hs, hcl, sw, D.hm.at(m, ps, r, 16, 7, D.Fd(4n, m, r), et, {==}, em, CK.Bo.or_ir(U32.is_eq(D.Fd(2n, m, r), D.Fd(4n, m, r)), Bool.or(U32.is_eq(D.Fd(3n, m, r), D.Fd(4n, m, r)), Bool.or(U32.is_eq(D.Fd(4n, m, r), D.Fd(4n, m, r)), False{})), CK.Bo.or_ir(U32.is_eq(D.Fd(3n, m, r), D.Fd(4n, m, r)), Bool.or(U32.is_eq(D.Fd(4n, m, r), D.Fd(4n, m, r)), False{}), CK.Bo.or_il(U32.is_eq(D.Fd(4n, m, r), D.Fd(4n, m, r)), False{}, CK.U.eq_refl(D.Fd(4n, m, r))))))), hcl))))
    case Bk.Term.Rfl{}:
      CK.Bo.or_il(D.Fl(m, r, 1024), D.Nodes(L, m, r), hs)
    case Bk.Term.Rwt{+y, +z, +w}:
      (+nd, w0) = h
      (py, w2) = w0
      (sy, hy) = py
      (pz, pw) = w2
      (sz, hz) = pz
      (sw, hw) = pw
      +et = D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Rwt{y, z, w}, 18, nd)
      +em = D.tbl.mask(m, im, fi, nx, Bk.Term.Rwt{y, z, w}, tbl)
      CK.Bo.and_i(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(2n, m, r), L), Bool.and(Ln(z, m, D.Fd(3n, m, r), L), Ln(w, m, D.Fd(4n, m, r), L))), CK.Bo.or_il(D.Fl(m, r, 1024), D.Nodes(L, m, r), hs),
        CK.Bo.and_i(Ln(y, m, D.Fd(2n, m, r), L), Bool.and(Ln(z, m, D.Fd(3n, m, r), L), Ln(w, m, D.Fd(4n, m, r), L)), ln.stat(y, dk, ds, m, im, fi, nx, ks, img, ps, cs, hc, tbl, L, D.Fd(2n, m, r), hy, part.st(D.Own(fi, nx, r), m, ps, fi, nx, cs, hc, r, D.Fd(2n, m, r), {==}, hs, hcl, sy, D.hm.at(m, ps, r, 18, 7, D.Fd(2n, m, r), et, {==}, em, CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, r), D.Fd(2n, m, r)), Bool.or(U32.is_eq(D.Fd(3n, m, r), D.Fd(2n, m, r)), Bool.or(U32.is_eq(D.Fd(4n, m, r), D.Fd(2n, m, r)), False{})), CK.U.eq_refl(D.Fd(2n, m, r))))), hcl), CK.Bo.and_i(Ln(z, m, D.Fd(3n, m, r), L), Ln(w, m, D.Fd(4n, m, r), L), ln.stat(z, dk, ds, m, im, fi, nx, ks, img, ps, cs, hc, tbl, L, D.Fd(3n, m, r), hz, part.st(D.Own(fi, nx, r), m, ps, fi, nx, cs, hc, r, D.Fd(3n, m, r), {==}, hs, hcl, sz, D.hm.at(m, ps, r, 18, 7, D.Fd(3n, m, r), et, {==}, em, CK.Bo.or_ir(U32.is_eq(D.Fd(2n, m, r), D.Fd(3n, m, r)), Bool.or(U32.is_eq(D.Fd(3n, m, r), D.Fd(3n, m, r)), Bool.or(U32.is_eq(D.Fd(4n, m, r), D.Fd(3n, m, r)), False{})), CK.Bo.or_il(U32.is_eq(D.Fd(3n, m, r), D.Fd(3n, m, r)), Bool.or(U32.is_eq(D.Fd(4n, m, r), D.Fd(3n, m, r)), False{}), CK.U.eq_refl(D.Fd(3n, m, r)))))), hcl), ln.stat(w, dk, ds, m, im, fi, nx, ks, img, ps, cs, hc, tbl, L, D.Fd(4n, m, r), hw, part.st(D.Own(fi, nx, r), m, ps, fi, nx, cs, hc, r, D.Fd(4n, m, r), {==}, hs, hcl, sw, D.hm.at(m, ps, r, 18, 7, D.Fd(4n, m, r), et, {==}, em, CK.Bo.or_ir(U32.is_eq(D.Fd(2n, m, r), D.Fd(4n, m, r)), Bool.or(U32.is_eq(D.Fd(3n, m, r), D.Fd(4n, m, r)), Bool.or(U32.is_eq(D.Fd(4n, m, r), D.Fd(4n, m, r)), False{})), CK.Bo.or_ir(U32.is_eq(D.Fd(3n, m, r), D.Fd(4n, m, r)), Bool.or(U32.is_eq(D.Fd(4n, m, r), D.Fd(4n, m, r)), False{}), CK.Bo.or_il(U32.is_eq(D.Fd(4n, m, r), D.Fd(4n, m, r)), False{}, CK.U.eq_refl(D.Fd(4n, m, r))))))), hcl))))


# The garbage
# -----------
#
# The copy's garbage P: the machine's own cells, from fi, that are not live
# (Lv: STATIC, a node of a term of the live roots L, or one of the cells Y,
# the frames and the temporaries), in order (Gb.of). Its zombie sizes are the
# sizes of the terms that T.tm.of reads from its cells (Zsz). The pointers to
# a cell are the garbage's and the live cells' (pc.split).

# x is live: STATIC, a node of a term of L, or one of the cells Y
def Lv(+m: Cr.Cir.Cells, +L: List<&2, D.Rt>, +Y: List<&2, U32>, +x: U32) -> Bool:
  Bool.or(Lv0(m, L, x), D.Mem(Y, x))

# the cells that are not live, of the k cells from c
def Gb.of(k: Nat, +m: Cr.Cir.Cells, +c: U32, +L: List<&2, D.Rt>, +Y: List<&2, U32>) -> List<&2, U32>:
  match k:
    case 0n:
      Nil{}
    case 1n+(+p):
      Bool.pick(List<&2, U32>, Lv(m, L, Y, c), Gb.of(p, m, U32.inc(c), L, Y), Con{c, Gb.of(p, m, U32.inc(c), L, Y)})

# a cell that is not live is not one that is
def lv.ne(+m: Cr.Cir.Cells, +L: List<&2, D.Rt>, +Y: List<&2, U32>, +c: U32, +x: U32, ec: {Lv(m, L, Y, c) == False{} : Bool},
  hx: {Lv(m, L, Y, x) == True{} : Bool}) -> {U32.is_eq(c, x) == False{} : Bool}:
  bool.case(U32.is_eq(c, x), U32.is_eq(c, x), {U32.is_eq(c, x) == False{} : Bool}, {==},
    e => CK.Bo.tf({U32.is_eq(c, x) == False{} : Bool}, Equal.trans(Bool, False{}, Lv(m, L, Y, c), True{}, Equal.sym(Bool, Lv(m, L, Y, c), False{}, ec),
      (%Equal.sym(U32, c, x, CK.U.eq(c, x, e)) : {Lv(m, L, Y, _) == True{} : Bool}; hx))),
    e => e)

def lv.ne2(+m: Cr.Cir.Cells, +L: List<&2, D.Rt>, +Y: List<&2, U32>, +c: U32, +x: U32, ec: {Lv(m, L, Y, c) == True{} : Bool},
  hx: {Lv(m, L, Y, x) == False{} : Bool}) -> {U32.is_eq(c, x) == False{} : Bool}:
  bool.case(U32.is_eq(c, x), U32.is_eq(c, x), {U32.is_eq(c, x) == False{} : Bool}, {==},
    e => CK.Bo.tf({U32.is_eq(c, x) == False{} : Bool}, Equal.trans(Bool, False{}, Lv(m, L, Y, x), True{}, Equal.sym(Bool, Lv(m, L, Y, x), False{}, hx),
      (%CK.U.eq(c, x, e) : {Lv(m, L, Y, _) == True{} : Bool}; ec))),
    e => e)

# a live cell is not in the garbage
def gb.not.b(b: Bool, +p: Nat, +m: Cr.Cir.Cells, +c: U32, +L: List<&2, D.Rt>, +Y: List<&2, U32>, +x: U32,
  eb: {Lv(m, L, Y, c) == b : Bool}, hx: {Lv(m, L, Y, x) == True{} : Bool},
  ih: {S.Has(Gb.of(p, m, U32.inc(c), L, Y), x) == False{} : Bool}) ->
  {S.Has(Bool.pick(List<&2, U32>, b, Gb.of(p, m, U32.inc(c), L, Y), Con{c, Gb.of(p, m, U32.inc(c), L, Y)}), x) == False{} : Bool}:
  match b:
    case True{}:
      ih
    case False{}:
      %Equal.sym(Bool, U32.is_eq(c, x), False{}, lv.ne(m, L, Y, c, x, eb, hx)) : {Bool.or(_, S.Has(Gb.of(p, m, U32.inc(c), L, Y), x)) == False{} : Bool}
      ih

def gb.not(k: Nat, +m: Cr.Cir.Cells, +c: U32, +L: List<&2, D.Rt>, +Y: List<&2, U32>, +x: U32, +hx: {Lv(m, L, Y, x) == True{} : Bool}) ->
  {S.Has(Gb.of(k, m, c, L, Y), x) == False{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+(+p):
      gb.not.b(Lv(m, L, Y, c), p, m, c, L, Y, x, {==}, hx, gb.not(p, m, U32.inc(c), L, Y, x, hx))

# a cell of the garbage is not live
def gb.lv(+k: Nat, +m: Cr.Cir.Cells, +c: U32, +L: List<&2, D.Rt>, +Y: List<&2, U32>, +x: U32,
  +hx: {S.Has(Gb.of(k, m, c, L, Y), x) == True{} : Bool}) -> {Lv(m, L, Y, x) == False{} : Bool}:
  bool.case(Lv(m, L, Y, x), Lv(m, L, Y, x), {Lv(m, L, Y, x) == False{} : Bool}, {==},
    e => CK.Bo.tf({Lv(m, L, Y, x) == False{} : Bool}, Equal.trans(Bool, False{}, S.Has(Gb.of(k, m, c, L, Y), x), True{},
      Equal.sym(Bool, S.Has(Gb.of(k, m, c, L, Y), x), False{}, gb.not(k, m, c, L, Y, x, e)), hx)),
    e => e)

# a cell from c on, before k cells from c, that is not live, is in the garbage
def gb.has.b(b: Bool, +p: Nat, +m: Cr.Cir.Cells, +c: U32, +L: List<&2, D.Rt>, +Y: List<&2, U32>, +x: U32,
  eb: {Lv(m, L, Y, c) == b : Bool}, +hx: {Lv(m, L, Y, x) == False{} : Bool},
  +h1: N.Le(U32.to_nat(c), U32.to_nat(x)), +h2: N.Le(1n+U32.to_nat(x), Nat.add(U32.to_nat(c), 1n+p)),
  ih: N.Le(U32.to_nat(U32.inc(c)), U32.to_nat(x)) -> N.Le(1n+U32.to_nat(x), Nat.add(U32.to_nat(U32.inc(c)), p)) ->
    {S.Has(Gb.of(p, m, U32.inc(c), L, Y), x) == True{} : Bool}) ->
  {S.Has(Bool.pick(List<&2, U32>, b, Gb.of(p, m, U32.inc(c), L, Y), Con{c, Gb.of(p, m, U32.inc(c), L, Y)}), x) == True{} : Bool}:
  match b:
    case True{}:
      +ne = lv.ne2(m, L, Y, c, x, eb, hx)
      ih(rng.lo(p, c, x, ne, h1), rng.hi(p, c, x, ne, h1, h2))
    case False{}:
      bool.case(U32.is_eq(c, x), U32.is_eq(c, x), {Bool.or(U32.is_eq(c, x), S.Has(Gb.of(p, m, U32.inc(c), L, Y), x)) == True{} : Bool}, {==},
        e => CK.Bo.or_il(U32.is_eq(c, x), S.Has(Gb.of(p, m, U32.inc(c), L, Y), x), e),
        +e => CK.Bo.or_ir(U32.is_eq(c, x), S.Has(Gb.of(p, m, U32.inc(c), L, Y), x), ih(rng.lo(p, c, x, e, h1), rng.hi(p, c, x, e, h1, h2))))

def gb.has(k: Nat, +m: Cr.Cir.Cells, +c: U32, +L: List<&2, D.Rt>, +Y: List<&2, U32>, +x: U32, +hx: {Lv(m, L, Y, x) == False{} : Bool},
  h1: N.Le(U32.to_nat(c), U32.to_nat(x)), h2: N.Le(1n+U32.to_nat(x), Nat.add(U32.to_nat(c), k))) ->
  {S.Has(Gb.of(k, m, c, L, Y), x) == True{} : Bool}:
  match k:
    case 0n:
      rng.none({S.Has(Gb.of(0n, m, c, L, Y), x) == True{} : Bool}, c, x, h1, h2)
    case 1n+(+p):
      gb.has.b(Lv(m, L, Y, c), p, m, c, L, Y, x, {==}, hx, h1, h2, a => b => gb.has(p, m, U32.inc(c), L, Y, x, hx, a, b))

# with c + 1 + p cells before e: c is below e
def w.lt(+c: U32, +p: Nat, +e: U32, hw: N.Le(Nat.add(U32.to_nat(c), 1n+p), U32.to_nat(e))) -> N.Le(1n+U32.to_nat(c), U32.to_nat(e)):
  N.le_trans(1n+U32.to_nat(c), Nat.add(U32.to_nat(c), 1n+p), U32.to_nat(e),
    N.le_rw_r(1n+U32.to_nat(c), 1n+Nat.add(U32.to_nat(c), p), Nat.add(U32.to_nat(c), 1n+p),
      Equal.sym(Nat, Nat.add(U32.to_nat(c), 1n+p), 1n+Nat.add(U32.to_nat(c), p), N.add_succ_r(U32.to_nat(c), p)),
      N.le_add_r(U32.to_nat(c), p)), hw)

# and from c + 1, p cells before e
def w.next(+c: U32, +p: Nat, +e: U32, +hw: N.Le(Nat.add(U32.to_nat(c), 1n+p), U32.to_nat(e))) -> N.Le(Nat.add(U32.to_nat(U32.inc(c)), p), U32.to_nat(e)):
  +ei = D.u.inc(c, e, w.lt(c, p, e, hw))
  N.le_rw_l(Nat.add(U32.to_nat(c), 1n+p), Nat.add(U32.to_nat(U32.inc(c)), p), U32.to_nat(e),
    Equal.trans(Nat, Nat.add(U32.to_nat(c), 1n+p), 1n+Nat.add(U32.to_nat(c), p), Nat.add(U32.to_nat(U32.inc(c)), p),
      N.add_succ_r(U32.to_nat(c), p),
      Equal.sym(Nat, Nat.add(U32.to_nat(U32.inc(c)), p), 1n+Nat.add(U32.to_nat(c), p),
        Equal.cong(Nat, Nat, x => Nat.add(x, p), U32.to_nat(U32.inc(c)), 1n+U32.to_nat(c), ei))), hw)

# the garbage from c holds cells from c on (with no wrap: c + k <= e)
def gb.lo.b(b: Bool, +p: Nat, +m: Cr.Cir.Cells, +c: U32, +L: List<&2, D.Rt>, +Y: List<&2, U32>, +x: U32, +e: U32,
  hw: N.Le(Nat.add(U32.to_nat(c), 1n+p), U32.to_nat(e)),
  hx: {S.Has(Bool.pick(List<&2, U32>, b, Gb.of(p, m, U32.inc(c), L, Y), Con{c, Gb.of(p, m, U32.inc(c), L, Y)}), x) == True{} : Bool},
  ih: {S.Has(Gb.of(p, m, U32.inc(c), L, Y), x) == True{} : Bool} -> N.Le(U32.to_nat(U32.inc(c)), U32.to_nat(x))) ->
  N.Le(U32.to_nat(c), U32.to_nat(x)):
  match b:
    case True{}:
      N.weaken(U32.to_nat(c), U32.to_nat(x), N.le_rw_l(U32.to_nat(U32.inc(c)), 1n+U32.to_nat(c), U32.to_nat(x), D.u.inc(c, e, w.lt(c, p, e, hw)), ih(hx)))
    case False{}:
      D.or.cases(U32.is_eq(c, x), S.Has(Gb.of(p, m, U32.inc(c), L, Y), x), N.Le(U32.to_nat(c), U32.to_nat(x)), hx,
        e2 => (%CK.U.eq(c, x, e2) : N.Le(U32.to_nat(c), U32.to_nat(_)); N.le_refl(U32.to_nat(c))),
        e2 => N.weaken(U32.to_nat(c), U32.to_nat(x), N.le_rw_l(U32.to_nat(U32.inc(c)), 1n+U32.to_nat(c), U32.to_nat(x), D.u.inc(c, e, w.lt(c, p, e, hw)), ih(e2))))

def gb.lo(k: Nat, +m: Cr.Cir.Cells, +c: U32, +L: List<&2, D.Rt>, +Y: List<&2, U32>, +x: U32, +e: U32,
  +hw: N.Le(Nat.add(U32.to_nat(c), k), U32.to_nat(e)), hx: {S.Has(Gb.of(k, m, c, L, Y), x) == True{} : Bool}) ->
  N.Le(U32.to_nat(c), U32.to_nat(x)):
  match k:
    case 0n:
      CK.Bo.tf(N.Le(U32.to_nat(c), U32.to_nat(x)), hx)
    case 1n+(+p):
      gb.lo.b(Lv(m, L, Y, c), p, m, c, L, Y, x, e, hw, hx, h => gb.lo(p, m, U32.inc(c), L, Y, x, e, w.next(c, p, e, hw), h))

# the garbage holds each cell once
def gb.nodup.b(b: Bool, +p: Nat, +m: Cr.Cir.Cells, +c: U32, +L: List<&2, D.Rt>, +Y: List<&2, U32>, +e: U32,
  +hw: N.Le(Nat.add(U32.to_nat(c), 1n+p), U32.to_nat(e)), ih: {S.Nodup(Gb.of(p, m, U32.inc(c), L, Y)) == True{} : Bool}) ->
  {S.Nodup(Bool.pick(List<&2, U32>, b, Gb.of(p, m, U32.inc(c), L, Y), Con{c, Gb.of(p, m, U32.inc(c), L, Y)})) == True{} : Bool}:
  match b:
    case True{}:
      ih
    case False{}:
      +ei = D.u.inc(c, e, w.lt(c, p, e, hw))
      CK.Bo.and_i(Bool.not(S.Has(Gb.of(p, m, U32.inc(c), L, Y), c)), S.Nodup(Gb.of(p, m, U32.inc(c), L, Y)),
        CK.Bo.not_i(S.Has(Gb.of(p, m, U32.inc(c), L, Y), c),
          bool.case(S.Has(Gb.of(p, m, U32.inc(c), L, Y), c), S.Has(Gb.of(p, m, U32.inc(c), L, Y), c),
            {S.Has(Gb.of(p, m, U32.inc(c), L, Y), c) == False{} : Bool}, {==},
            h => Empty.absurd({S.Has(Gb.of(p, m, U32.inc(c), L, Y), c) == False{} : Bool}, N.not_succ_le(U32.to_nat(c),
              N.le_rw_l(U32.to_nat(U32.inc(c)), 1n+U32.to_nat(c), U32.to_nat(c), ei, gb.lo(p, m, U32.inc(c), L, Y, c, e, w.next(c, p, e, hw), h)))),
            h => h)),
        ih)

def gb.nodup(k: Nat, +m: Cr.Cir.Cells, +c: U32, +L: List<&2, D.Rt>, +Y: List<&2, U32>, +e: U32,
  +hw: N.Le(Nat.add(U32.to_nat(c), k), U32.to_nat(e))) -> {S.Nodup(Gb.of(k, m, c, L, Y)) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+(+p):
      gb.nodup.b(Lv(m, L, Y, c), p, m, c, L, Y, e, hw, gb.nodup(p, m, U32.inc(c), L, Y, e, w.next(c, p, e, hw)))

# Zombie sizes
# ------------

def Zsz.of(r: Maybe<&2, Bk.Term>) -> Nat:
  match r:
    case None{}:
      0n
    case Some{v}:
      Pg.Term.size(v)

# the zombie size of the cell x: the nodes of the term that T.tm.of reads
# from it, with the fuel f
def Zsz(+f: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +x: U32) -> Nat:
  Zsz.of(T.tm.of(f, m, ks, img, x))

# the cells xs with their zombie sizes
def Zl(xs: List<&2, U32>, +f: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>) -> List<&2, S.Zs>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, rest}:
      Con{S.Zs{x, Zsz(f, m, ks, img, x)}, Zl(rest, f, m, ks, img)}

# a cell p of xs: its zombie size in Zl(xs) is Zsz's
def zz.of.b(b: Bool, +x: U32, +rest: List<&2, U32>, +f: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +p: U32, eb: {U32.is_eq(x, p) == b : Bool}, h: {Bool.or(b, S.Has(rest, p)) == True{} : Bool},
  ih: {S.Has(rest, p) == True{} : Bool} -> {S.Zz(Zl(rest, f, m, ks, img), p) == Zsz(f, m, ks, img, p) : Nat}) ->
  {Bool.pick(Nat, b, Zsz(f, m, ks, img, x), S.Zz(Zl(rest, f, m, ks, img), p)) == Zsz(f, m, ks, img, p) : Nat}:
  match b:
    case True{}:
      Equal.cong(U32, Nat, y => Zsz(f, m, ks, img, y), x, p, CK.U.eq(x, p, eb))
    case False{}:
      ih(h)

def zz.of(xs: List<&2, U32>, +f: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +p: U32,
  h: {S.Has(xs, p) == True{} : Bool}) -> {S.Zz(Zl(xs, f, m, ks, img), p) == Zsz(f, m, ks, img, p) : Nat}:
  match xs:
    case Nil{}:
      CK.Bo.tf({S.Zz(Zl(Nil{}, f, m, ks, img), p) == Zsz(f, m, ks, img, p) : Nat}, h)
    case Con{+x, +rest}:
      zz.of.b(U32.is_eq(x, p), x, rest, f, m, ks, img, p, {==}, h, hh => zz.of(rest, f, m, ks, img, p, hh))

# a cell that stands for v, with the fuel f >= its size: its zombie size is v's size
def zsz.at(+f: Nat, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +x: U32, +v: Bk.Term, le: N.Le(Pg.Term.size(v), f), h: D.Is(ds, m, im, fi, nx, ks, img, x, v)) ->
  {Zsz(f, m, ks, img, x) == Pg.Term.size(v) : Nat}:
  %Equal.sym(Maybe<&2, Bk.Term>, T.tm.of(f, m, ks, img, x), Some{v}, CF.is.tm.at(f, ds, m, im, fi, nx, ks, img, x, v, le, h)) :
    {Zsz.of(_) == Pg.Term.size(v) : Nat}
  {==}

# The pointers to a cell
# ----------------------

# the pointers to p of the cells G
def PcG(G: List<&2, U32>, +m: Cr.Cir.Cells, +ps: List<&2, U32>, +p: U32) -> Nat:
  match G:
    case Nil{}:
      0n
    case Con{+o, rest}:
      Nat.add(D.RcL(D.Fs(m, ps, o), p), PcG(rest, m, ps, p))

# the pointers to p of the live cells of the k cells from c
def PcN(k: Nat, +m: Cr.Cir.Cells, +ps: List<&2, U32>, +c: U32, +p: U32, +L: List<&2, D.Rt>, +Y: List<&2, U32>) -> Nat:
  match k:
    case 0n:
      0n
    case 1n+q:
      Nat.add(Bool.pick(Nat, Lv(m, L, Y, c), D.RcL(D.Fs(m, ps, c), p), 0n), PcN(q, m, ps, U32.inc(c), p, L, Y))

# the pointers to p of the k cells from c: the garbage's and the live cells'
def pc.split.b(b: Bool, +q: Nat, +m: Cr.Cir.Cells, +ps: List<&2, U32>, +c: U32, +p: U32, +L: List<&2, D.Rt>, +Y: List<&2, U32>,
  ih: {D.Pc(q, m, ps, U32.inc(c), p) == Nat.add(PcG(Gb.of(q, m, U32.inc(c), L, Y), m, ps, p), PcN(q, m, ps, U32.inc(c), p, L, Y)) : Nat}) ->
  {Nat.add(D.RcL(D.Fs(m, ps, c), p), D.Pc(q, m, ps, U32.inc(c), p)) ==
    Nat.add(PcG(Bool.pick(List<&2, U32>, b, Gb.of(q, m, U32.inc(c), L, Y), Con{c, Gb.of(q, m, U32.inc(c), L, Y)}), m, ps, p),
      Nat.add(Bool.pick(Nat, b, D.RcL(D.Fs(m, ps, c), p), 0n), PcN(q, m, ps, U32.inc(c), p, L, Y))) : Nat}:
  match b:
    case True{}:
      %Equal.sym(Nat, D.Pc(q, m, ps, U32.inc(c), p), Nat.add(PcG(Gb.of(q, m, U32.inc(c), L, Y), m, ps, p), PcN(q, m, ps, U32.inc(c), p, L, Y)), ih) :
        {Nat.add(D.RcL(D.Fs(m, ps, c), p), _) == Nat.add(PcG(Gb.of(q, m, U32.inc(c), L, Y), m, ps, p),
          Nat.add(D.RcL(D.Fs(m, ps, c), p), PcN(q, m, ps, U32.inc(c), p, L, Y))) : Nat}
      Equal.trans(Nat, Nat.add(D.RcL(D.Fs(m, ps, c), p), Nat.add(PcG(Gb.of(q, m, U32.inc(c), L, Y), m, ps, p), PcN(q, m, ps, U32.inc(c), p, L, Y))),
        Nat.add(Nat.add(PcG(Gb.of(q, m, U32.inc(c), L, Y), m, ps, p), D.RcL(D.Fs(m, ps, c), p)), PcN(q, m, ps, U32.inc(c), p, L, Y)),
        Nat.add(PcG(Gb.of(q, m, U32.inc(c), L, Y), m, ps, p), Nat.add(D.RcL(D.Fs(m, ps, c), p), PcN(q, m, ps, U32.inc(c), p, L, Y))),
        N.add_comm3(D.RcL(D.Fs(m, ps, c), p), PcG(Gb.of(q, m, U32.inc(c), L, Y), m, ps, p), PcN(q, m, ps, U32.inc(c), p, L, Y)),
        N.add_assoc(PcG(Gb.of(q, m, U32.inc(c), L, Y), m, ps, p), D.RcL(D.Fs(m, ps, c), p), PcN(q, m, ps, U32.inc(c), p, L, Y)))
    case False{}:
      %Equal.sym(Nat, D.Pc(q, m, ps, U32.inc(c), p), Nat.add(PcG(Gb.of(q, m, U32.inc(c), L, Y), m, ps, p), PcN(q, m, ps, U32.inc(c), p, L, Y)), ih) :
        {Nat.add(D.RcL(D.Fs(m, ps, c), p), _) == Nat.add(Nat.add(D.RcL(D.Fs(m, ps, c), p), PcG(Gb.of(q, m, U32.inc(c), L, Y), m, ps, p)),
          PcN(q, m, ps, U32.inc(c), p, L, Y)) : Nat}
      Equal.sym(Nat, Nat.add(Nat.add(D.RcL(D.Fs(m, ps, c), p), PcG(Gb.of(q, m, U32.inc(c), L, Y), m, ps, p)), PcN(q, m, ps, U32.inc(c), p, L, Y)),
        Nat.add(D.RcL(D.Fs(m, ps, c), p), Nat.add(PcG(Gb.of(q, m, U32.inc(c), L, Y), m, ps, p), PcN(q, m, ps, U32.inc(c), p, L, Y))),
        N.add_assoc(D.RcL(D.Fs(m, ps, c), p), PcG(Gb.of(q, m, U32.inc(c), L, Y), m, ps, p), PcN(q, m, ps, U32.inc(c), p, L, Y)))

def pc.split(k: Nat, +m: Cr.Cir.Cells, +ps: List<&2, U32>, +c: U32, +p: U32, +L: List<&2, D.Rt>, +Y: List<&2, U32>) ->
  {D.Pc(k, m, ps, c, p) == Nat.add(PcG(Gb.of(k, m, c, L, Y), m, ps, p), PcN(k, m, ps, c, p, L, Y)) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+(+q):
      pc.split.b(Lv(m, L, Y, c), q, m, ps, c, p, L, Y, pc.split(q, m, ps, U32.inc(c), p, L, Y))

# The garbage's pointers (Pp) by the heap's (Fs)
# --------------------------------------------

# the pointer v in the list, when b holds: counted when it is c
def rcl.opt(b: Bool, +v: U32, +rest: List<&2, U32>, +c: U32) ->
  {D.RcL(D.Fs.opt(b, v, rest), c) == Nat.add(S.Nat.of(Bool.and(b, U32.is_eq(v, c))), D.RcL(rest, c)) : Nat}:
  match b:
    case True{}:
      Equal.cong(Nat, Nat, w => Nat.add(w, D.RcL(rest, c)), D.Nat.of(U32.is_eq(v, c)), S.Nat.of(U32.is_eq(v, c)), nat.of.eq(U32.is_eq(v, c)))
    case False{}:
      {==}

# the parts of a term cell of the mask a that are c
def rcl.term(+a: U32, +x2: U32, +x3: U32, +x4: U32, +c: U32) ->
  {D.RcL(D.Fs.term(a, x2, x3, x4), c) == Nat.add(S.Nat.of(Bool.and(U32.is_ne(U32.and(a, 1), 0), U32.is_eq(x2, c))),
    Nat.add(S.Nat.of(Bool.and(U32.is_ne(U32.and(a, 2), 0), U32.is_eq(x3, c))), S.Nat.of(Bool.and(U32.is_ne(U32.and(a, 4), 0), U32.is_eq(x4, c))))) : Nat}:
  +b1 = U32.is_ne(U32.and(a, 1), 0)
  +b2 = U32.is_ne(U32.and(a, 2), 0)
  +b4 = U32.is_ne(U32.and(a, 4), 0)
  +A1 = S.Nat.of(Bool.and(b1, U32.is_eq(x2, c)))
  +A2 = S.Nat.of(Bool.and(b2, U32.is_eq(x3, c)))
  +A4 = S.Nat.of(Bool.and(b4, U32.is_eq(x4, c)))
  +e3 = Equal.trans(Nat, D.RcL(D.Fs.opt(b4, x4, Nil{}), c), Nat.add(A4, 0n), A4, rcl.opt(b4, x4, Nil{}, c), N.add_zero(A4))
  +e2 = Equal.trans(Nat, D.RcL(D.Fs.opt(b2, x3, D.Fs.opt(b4, x4, Nil{})), c), Nat.add(A2, D.RcL(D.Fs.opt(b4, x4, Nil{}), c)), Nat.add(A2, A4),
    rcl.opt(b2, x3, D.Fs.opt(b4, x4, Nil{}), c), Equal.cong(Nat, Nat, w => Nat.add(A2, w), D.RcL(D.Fs.opt(b4, x4, Nil{}), c), A4, e3))
  Equal.trans(Nat, D.RcL(D.Fs.opt(b1, x2, D.Fs.opt(b2, x3, D.Fs.opt(b4, x4, Nil{}))), c),
    Nat.add(A1, D.RcL(D.Fs.opt(b2, x3, D.Fs.opt(b4, x4, Nil{})), c)), Nat.add(A1, Nat.add(A2, A4)),
    rcl.opt(b1, x2, D.Fs.opt(b2, x3, D.Fs.opt(b4, x4, Nil{})), c),
    Equal.cong(Nat, Nat, w => Nat.add(A1, w), D.RcL(D.Fs.opt(b2, x3, D.Fs.opt(b4, x4, Nil{})), c), Nat.add(A2, A4), e2))

def and.f(a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# a cell of the pend list of a tag of 19 or more holds no pointer
def fs.nil(+m: Cr.Cir.Cells, +ps: List<&2, U32>, +o: U32, h19: {U32.is_lt(D.Tg(m, o), 19) == False{} : Bool},
  hm: {D.Mem(ps, o) == True{} : Bool}) -> {D.Fs(m, ps, o) == Nil{} : List<&2, U32>}:
  +tg = D.Tg(m, o)
  +A1 = Bool.and(U32.is_le(32, tg), U32.is_le(tg, 40))
  +A2 = Bool.and(U32.is_eq(tg, 41), D.FlW(D.Fd(0n, m, o), 4096))
  %Equal.sym(Bool, U32.is_lt(tg, 19), False{}, h19) : {D.FsP(_, m, ps, o, tg) == Nil{} : List<&2, U32>}
  %Equal.sym(Bool, D.Mem(ps, o), True{}, hm) : {Bool.pick(List<&2, U32>, Bool.and(A1, Bool.not(_)), Con{D.Fd(2n, m, o), D.Fs.opt(U32.is_eq(tg, 38), D.Fd(3n, m, o), Nil{})},
    Bool.pick(List<&2, U32>, Bool.and(A2, Bool.not(_)), [D.Fd(2n, m, o)], Nil{})) == Nil{} : List<&2, U32>}
  %Equal.sym(Bool, Bool.and(A1, False{}), False{}, and.f(A1)) : {Bool.pick(List<&2, U32>, _, Con{D.Fd(2n, m, o), D.Fs.opt(U32.is_eq(tg, 38), D.Fd(3n, m, o), Nil{})},
    Bool.pick(List<&2, U32>, Bool.and(A2, False{}), [D.Fd(2n, m, o)], Nil{})) == Nil{} : List<&2, U32>}
  %Equal.sym(Bool, Bool.and(A2, False{}), False{}, and.f(A2)) : {Bool.pick(List<&2, U32>, _, [D.Fd(2n, m, o)], Nil{}) == Nil{} : List<&2, U32>}
  {==}

# the mask that a reuse drops, of a term cell: its table entry's
def am.lt(+m: Cr.Cir.Cells, +o: U32, h: {U32.is_lt(D.Tg(m, o), 32) == True{} : Bool}) ->
  {S.Am(m, o) == D.Fd(2n, m, U32.add(272, D.Tg(m, o))) : U32}:
  %Equal.sym(Bool, U32.is_lt(D.Tg(m, o), 32), True{}, h) : {Bool.pick(U32, _, D.Fd(2n, m, U32.add(272, D.Tg(m, o))), 0) == D.Fd(2n, m, U32.add(272, D.Tg(m, o))) : U32}
  {==}

# and of a cell of the machine's own kinds: none
def am.ge(+m: Cr.Cir.Cells, +o: U32, h: {U32.is_lt(D.Tg(m, o), 32) == False{} : Bool}) -> {S.Am(m, o) == 0 : U32}:
  %Equal.sym(Bool, U32.is_lt(D.Tg(m, o), 32), False{}, h) : {Bool.pick(U32, _, D.Fd(2n, m, U32.add(272, D.Tg(m, o))), 0) == 0 : U32}
  {==}

# the garbage's pointers by the mask of a reuse (Ow), with the mask a
def OwA(+a: U32, +m: Cr.Cir.Cells, +o: U32, +c: U32) -> Nat:
  Nat.add(S.Nat.of(Bool.and(U32.is_ne(U32.and(a, 1), 0), U32.is_eq(D.Fd(2n, m, o), c))),
    Nat.add(S.Nat.of(Bool.and(U32.is_ne(U32.and(a, 2), 0), U32.is_eq(D.Fd(3n, m, o), c))),
      S.Nat.of(Bool.and(U32.is_ne(U32.and(a, 4), 0), U32.is_eq(D.Fd(4n, m, o), c)))))

# a cell of the pend list of the machine's own kinds: its reuse drops none
def ow.pend(+m: Cr.Cir.Cells, +ps: List<&2, U32>, +o: U32, +c: U32, +h32: {U32.is_le(32, D.Tg(m, o)) == True{} : Bool},
  hm: {D.Mem(ps, o) == True{} : Bool}) -> {S.Ow(m, o, c) == D.RcL(D.Fs(m, ps, o), c) : Nat}:
  +tg = D.Tg(m, o)
  +nlt = bool.case(U32.is_lt(tg, 32), U32.is_lt(tg, 32), {U32.is_lt(tg, 32) == False{} : Bool}, {==},
    e => CK.U.lt_ge(tg, 32, {U32.is_lt(tg, 32) == False{} : Bool}, e, h32), e => e)
  +n19 = bool.case(U32.is_lt(tg, 19), U32.is_lt(tg, 19), {U32.is_lt(tg, 19) == False{} : Bool}, {==},
    e => CK.U.lt_ge(tg, 32, {U32.is_lt(tg, 19) == False{} : Bool}, CK.U.lt_le(tg, 19, 32, e, {==}), h32), e => e)
  Equal.trans(Nat, S.Ow(m, o, c), OwA(0, m, o, c), D.RcL(D.Fs(m, ps, o), c),
    Equal.cong(U32, Nat, a => OwA(a, m, o, c), S.Am(m, o), 0, am.ge(m, o, nlt)),
    Equal.cong(List<&2, U32>, Nat, xs => D.RcL(xs, c), Nil{}, D.Fs(m, ps, o), Equal.sym(List<&2, U32>, D.Fs(m, ps, o), Nil{}, fs.nil(m, ps, o, n19, hm))))

# a term cell, or one of the pend list of the machine's own kinds: the
# pointers that its reuse drops (Ow) are the heap's (Fs)
def ow.fs(+m: Cr.Cir.Cells, +ps: List<&2, U32>, +o: U32, +c: U32,
  h: {Bool.or(U32.is_lt(D.Tg(m, o), 19), Bool.and(U32.is_le(32, D.Tg(m, o)), D.Mem(ps, o))) == True{} : Bool}) ->
  {S.Ow(m, o, c) == D.RcL(D.Fs(m, ps, o), c) : Nat}:
  +tg = D.Tg(m, o)
  +mask = D.Fd(2n, m, U32.add(272, tg))
  D.or.cases(U32.is_lt(tg, 19), Bool.and(U32.is_le(32, tg), D.Mem(ps, o)), {S.Ow(m, o, c) == D.RcL(D.Fs(m, ps, o), c) : Nat}, h,
    +e => Equal.trans(Nat, S.Ow(m, o, c), OwA(mask, m, o, c), D.RcL(D.Fs(m, ps, o), c),
      Equal.cong(U32, Nat, a => OwA(a, m, o, c), S.Am(m, o), mask, am.lt(m, o, CK.U.lt_le(tg, 19, 32, e, {==}))),
      Equal.trans(Nat, OwA(mask, m, o, c), D.RcL(D.Fs.term(mask, D.Fd(2n, m, o), D.Fd(3n, m, o), D.Fd(4n, m, o)), c), D.RcL(D.Fs(m, ps, o), c),
        Equal.sym(Nat, D.RcL(D.Fs.term(mask, D.Fd(2n, m, o), D.Fd(3n, m, o), D.Fd(4n, m, o)), c), OwA(mask, m, o, c),
          rcl.term(mask, D.Fd(2n, m, o), D.Fd(3n, m, o), D.Fd(4n, m, o), c)),
        Equal.cong(List<&2, U32>, Nat, xs => D.RcL(xs, c), D.Fs.term(mask, D.Fd(2n, m, o), D.Fd(3n, m, o), D.Fd(4n, m, o)), D.Fs(m, ps, o),
          Equal.sym(List<&2, U32>, D.Fs(m, ps, o), D.Fs.term(mask, D.Fd(2n, m, o), D.Fd(3n, m, o), D.Fd(4n, m, o)),
            D.fs.term(m, ps, o, tg, mask, {==}, e, {==}))))),
    +e => ow.pend(m, ps, o, c, CK.Bo.and_l(U32.is_le(32, tg), D.Mem(ps, o), e), CK.Bo.and_r(U32.is_le(32, tg), D.Mem(ps, o), e)))

# each cell of G is a term cell, or one of the pend list of the machine's own kinds
def GTs(G: List<&2, U32>, +m: Cr.Cir.Cells, +ps: List<&2, U32>) -> Bool:
  match G:
    case Nil{}:
      True{}
    case Con{+o, rest}:
      Bool.and(Bool.or(U32.is_lt(D.Tg(m, o), 19), Bool.and(U32.is_le(32, D.Tg(m, o)), D.Mem(ps, o))), GTs(rest, m, ps))

# the garbage's pointers to p are the heap's (PcG)
def pp.pcg(G: List<&2, U32>, +m: Cr.Cir.Cells, +ps: List<&2, U32>, +p: U32, h: {GTs(G, m, ps) == True{} : Bool}) ->
  {S.Pp(G, m, p) == PcG(G, m, ps, p) : Nat}:
  match G:
    case Nil{}:
      {==}
    case Con{+o, +rest}:
      +h2 = h
      add.cong(S.Ow(m, o, p), D.RcL(D.Fs(m, ps, o), p), S.Pp(rest, m, p), PcG(rest, m, ps, p),
        ow.fs(m, ps, o, p, CK.Bo.and_l(Bool.or(U32.is_lt(D.Tg(m, o), 19), Bool.and(U32.is_le(32, D.Tg(m, o)), D.Mem(ps, o))), GTs(rest, m, ps), h2)),
        pp.pcg(rest, m, ps, p, CK.Bo.and_r(Bool.or(U32.is_lt(D.Tg(m, o), 19), Bool.and(U32.is_le(32, D.Tg(m, o)), D.Mem(ps, o))), GTs(rest, m, ps), h2)))

# Live cells and their pointers
# -----------------------------
#
# With the live roots L = os ++ (hl ++ frt) (the owned roots, the terms that
# the temporaries hold, the frames' terms) and the cells Y = frc ++ cs (the
# frames, the temporaries): a pointer of a live cell is live (lv.fs), so no
# live cell points to the garbage (pcn.zero); and a live node that is not
# STATIC has a live pointer, or is an owned root (live.ptr).

# a or b, not b: a
def or.l2(a: Bool, -b: Bool, h: {Bool.or(a, b) == True{} : Bool}, hb: {b == False{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      CK.Bo.ft({False{} == True{} : Bool}, Equal.trans(Bool, True{}, b, False{}, Equal.sym(Bool, b, True{}, h), hb))

# a cell of xs, which are all among ys, is among ys
def allin.mem(xs: List<&2, U32>, +ys: List<&2, U32>, +p: U32, +h: {D.AllIn(xs, ys) == True{} : Bool},
  hp: {D.Mem(xs, p) == True{} : Bool}) -> {D.Mem(ys, p) == True{} : Bool}:
  match xs:
    case Nil{}:
      CK.Bo.tf({D.Mem(ys, p) == True{} : Bool}, hp)
    case Con{+x, +rest}:
      D.or.cases(U32.is_eq(x, p), D.Mem(rest, p), {D.Mem(ys, p) == True{} : Bool}, hp,
        e => (%CK.U.eq(x, p, e) : {D.Mem(ys, _) == True{} : Bool}; CK.Bo.and_l(D.Mem(ys, x), D.AllIn(rest, ys), h)),
        e => allin.mem(rest, ys, p, CK.Bo.and_r(D.Mem(ys, x), D.AllIn(rest, ys), h), e))

# the cells of the roots A ++ B
def rt.cells.app(A: List<&2, D.Rt>, +B: List<&2, D.Rt>) ->
  {D.Rt.cells(List.append(&2, D.Rt, A, B)) == List.append(&2, U32, D.Rt.cells(A), D.Rt.cells(B)) : List<&2, U32>}:
  match A:
    case Nil{}:
      {==}
    case Con{D.Rt{+c, +u}, +rest}:
      Equal.cong(List<&2, U32>, List<&2, U32>, xs => Con{c, xs}, D.Rt.cells(List.append(&2, D.Rt, rest, B)),
        List.append(&2, U32, D.Rt.cells(rest), D.Rt.cells(B)), rt.cells.app(rest, B))

# a root's cell is a node of its term
def root.nodes(rs: List<&2, D.Rt>, +m: Cr.Cir.Cells, +c: U32, h: {D.Mem(D.Rt.cells(rs), c) == True{} : Bool}) ->
  {D.Nodes(rs, m, c) == True{} : Bool}:
  match rs:
    case Nil{}:
      CK.Bo.tf({D.Nodes(Nil{}, m, c) == True{} : Bool}, h)
    case Con{D.Rt{+r, +u}, +rest}:
      D.or.cases(U32.is_eq(r, c), D.Mem(D.Rt.cells(rest), c), {D.Nodes(Con{D.Rt{r, u}, rest}, m, c) == True{} : Bool}, h,
        e => CK.Bo.or_il(D.Node(u, m, r, c), D.Nodes(rest, m, c), (%CK.U.eq(r, c, e) : {D.Node(u, m, r, _) == True{} : Bool}; node.root(u, m, r))),
        e => CK.Bo.or_ir(D.Node(u, m, r, c), D.Nodes(rest, m, c), root.nodes(rest, m, c, e)))

# a cell of xs, all STATIC, temporaries (cs) or roots of their terms (hc)
def held.mem(xs: List<&2, U32>, +m: Cr.Cir.Cells, +cs: List<&2, U32>, +hc: List<&2, U32>, +c: U32,
  +h: {D.All.held(xs, m, cs, hc) == True{} : Bool}, hm: {D.Mem(xs, c) == True{} : Bool}) ->
  {Bool.or(D.Fl(m, c, 1024), Bool.or(D.Mem(cs, c), D.Mem(hc, c))) == True{} : Bool}:
  match xs:
    case Nil{}:
      CK.Bo.tf({Bool.or(D.Fl(m, c, 1024), Bool.or(D.Mem(cs, c), D.Mem(hc, c))) == True{} : Bool}, hm)
    case Con{+x, +rest}:
      D.or.cases(U32.is_eq(x, c), D.Mem(rest, c), {Bool.or(D.Fl(m, c, 1024), Bool.or(D.Mem(cs, c), D.Mem(hc, c))) == True{} : Bool}, hm,
        e => (%CK.U.eq(x, c, e) : {Bool.or(D.Fl(m, _, 1024), Bool.or(D.Mem(cs, _), D.Mem(hc, _))) == True{} : Bool};
          CK.Bo.and_l(Bool.or(D.Fl(m, x, 1024), Bool.or(D.Mem(cs, x), D.Mem(hc, x))), D.All.held(rest, m, cs, hc), h)),
        e => held.mem(rest, m, cs, hc, c, CK.Bo.and_r(Bool.or(D.Fl(m, x, 1024), Bool.or(D.Mem(cs, x), D.Mem(hc, x))), D.All.held(rest, m, cs, hc), h), e))

# not among xs: counted none
def rcl.zero(xs: List<&2, U32>, +c: U32, h: {D.Mem(xs, c) == False{} : Bool}) -> {D.RcL(xs, c) == 0n : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      +h2 = h
      %Equal.sym(Bool, U32.is_eq(x, c), False{}, D.or.f.l(U32.is_eq(x, c), D.Mem(rest, c), h2)) :
        {Nat.add(D.Nat.of(_), D.RcL(rest, c)) == 0n : Nat}
      rcl.zero(rest, c, D.or.f.r(U32.is_eq(x, c), D.Mem(rest, c), h2))

# the part b of a frame of the kind (field 3, for Rwt): a pointer of it is the root of b
def fr.b.fs(kind: D.FK, +m: Cr.Cir.Cells, +fr: U32, +b: Bk.Term, +R: List<&2, D.Rt>, +c: U32,
  h: {D.Mem(D.Fs.opt(U32.is_eq(D.FK.tag(kind), 38), D.Fd(3n, m, fr), Nil{}), c) == True{} : Bool}) ->
  {D.Nodes(List.append(&2, D.Rt, D.Fr.rts.b(m, fr, kind, b), R), m, c) == True{} : Bool}:
  match kind:
    case D.FK.rwt{}:
      CK.Bo.or_il(D.Node(b, m, D.Fd(3n, m, fr), c), D.Nodes(R, m, c),
        (%CK.U.eq(D.Fd(3n, m, fr), c, or.l2(U32.is_eq(D.Fd(3n, m, fr), c), False{}, h, {==})) : {D.Node(b, m, D.Fd(3n, m, fr), _) == True{} : Bool}; node.root(b, m, D.Fd(3n, m, fr))))
    case D.FK.arg{}:
      CK.Bo.tf({D.Nodes(R, m, c) == True{} : Bool}, h)
    case D.FK.val{}:
      CK.Bo.tf({D.Nodes(R, m, c) == True{} : Bool}, h)
    case D.FK.fun{}:
      CK.Bo.tf({D.Nodes(R, m, c) == True{} : Bool}, h)
    case D.FK.let{}:
      CK.Bo.tf({D.Nodes(R, m, c) == True{} : Bool}, h)
    case D.FK.tupb{}:
      CK.Bo.tf({D.Nodes(R, m, c) == True{} : Bool}, h)
    case D.FK.tupa{}:
      CK.Bo.tf({D.Nodes(R, m, c) == True{} : Bool}, h)
    case D.FK.minb{}:
      CK.Bo.tf({D.Nodes(R, m, c) == True{} : Bool}, h)
    case D.FK.mina{}:
      CK.Bo.tf({D.Nodes(R, m, c) == True{} : Bool}, h)

# a node of a term of B, or of A, is one of A ++ B; a cell of A ++ B is one of A or of B
def nodes.in.l(+A: List<&2, D.Rt>, +B: List<&2, D.Rt>, +m: Cr.Cir.Cells, +x: U32, h: {D.Nodes(A, m, x) == True{} : Bool}) ->
  {D.Nodes(List.append(&2, D.Rt, A, B), m, x) == True{} : Bool}:
  %Equal.sym(Bool, D.Nodes(List.append(&2, D.Rt, A, B), m, x), Bool.or(D.Nodes(A, m, x), D.Nodes(B, m, x)), AC.nodes.app(A, B, m, x)) : {_ == True{} : Bool}
  CK.Bo.or_il(D.Nodes(A, m, x), D.Nodes(B, m, x), h)

def nodes.in.r(+A: List<&2, D.Rt>, +B: List<&2, D.Rt>, +m: Cr.Cir.Cells, +x: U32, h: {D.Nodes(B, m, x) == True{} : Bool}) ->
  {D.Nodes(List.append(&2, D.Rt, A, B), m, x) == True{} : Bool}:
  %Equal.sym(Bool, D.Nodes(List.append(&2, D.Rt, A, B), m, x), Bool.or(D.Nodes(A, m, x), D.Nodes(B, m, x)), AC.nodes.app(A, B, m, x)) : {_ == True{} : Bool}
  CK.Bo.or_ir(D.Nodes(A, m, x), D.Nodes(B, m, x), h)

def nodes.split(+A: List<&2, D.Rt>, +B: List<&2, D.Rt>, +m: Cr.Cir.Cells, +x: U32, h: {D.Nodes(List.append(&2, D.Rt, A, B), m, x) == True{} : Bool}) ->
  {Bool.or(D.Nodes(A, m, x), D.Nodes(B, m, x)) == True{} : Bool}:
  %AC.nodes.app(A, B, m, x) : {_ == True{} : Bool}
  h

def mem.in.l(+A: List<&2, U32>, +B: List<&2, U32>, +x: U32, h: {D.Mem(A, x) == True{} : Bool}) -> {D.Mem(List.append(&2, U32, A, B), x) == True{} : Bool}:
  %Equal.sym(Bool, D.Mem(List.append(&2, U32, A, B), x), Bool.or(D.Mem(A, x), D.Mem(B, x)), AC.mem.app(A, B, x)) : {_ == True{} : Bool}
  CK.Bo.or_il(D.Mem(A, x), D.Mem(B, x), h)

def mem.in.r(+A: List<&2, U32>, +B: List<&2, U32>, +x: U32, h: {D.Mem(B, x) == True{} : Bool}) -> {D.Mem(List.append(&2, U32, A, B), x) == True{} : Bool}:
  %Equal.sym(Bool, D.Mem(List.append(&2, U32, A, B), x), Bool.or(D.Mem(A, x), D.Mem(B, x)), AC.mem.app(A, B, x)) : {_ == True{} : Bool}
  CK.Bo.or_ir(D.Mem(A, x), D.Mem(B, x), h)

def mem.split(+A: List<&2, U32>, +B: List<&2, U32>, +x: U32, h: {D.Mem(List.append(&2, U32, A, B), x) == True{} : Bool}) ->
  {Bool.or(D.Mem(A, x), D.Mem(B, x)) == True{} : Bool}:
  %AC.mem.app(A, B, x) : {_ == True{} : Bool}
  h

# the live roots and cells of a move: the owned roots, the terms that the
# temporaries hold and the frames' terms; the frames and the temporaries
def Lst(+os: List<&2, D.Rt>, +hl: List<&2, D.Rt>, +fs: List<&2, D.AF>, +m: Cr.Cir.Cells, +sp: U32) -> List<&2, D.Rt>:
  List.append(&2, D.Rt, os, List.append(&2, D.Rt, hl, D.Fr.rts(fs, m, sp)))

def Yc(+fs: List<&2, D.AF>, +m: Cr.Cir.Cells, +sp: U32, +cs: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, D.Fr.cells(fs, m, sp), cs)

def lv.st(+m: Cr.Cir.Cells, +L: List<&2, D.Rt>, +Y: List<&2, U32>, +c: U32, h: {D.Fl(m, c, 1024) == True{} : Bool}) -> {Lv(m, L, Y, c) == True{} : Bool}:
  CK.Bo.or_il(Lv0(m, L, c), D.Mem(Y, c), CK.Bo.or_il(D.Fl(m, c, 1024), D.Nodes(L, m, c), h))

def lv.nd(+m: Cr.Cir.Cells, +L: List<&2, D.Rt>, +Y: List<&2, U32>, +c: U32, h: {D.Nodes(L, m, c) == True{} : Bool}) -> {Lv(m, L, Y, c) == True{} : Bool}:
  CK.Bo.or_il(Lv0(m, L, c), D.Mem(Y, c), CK.Bo.or_ir(D.Fl(m, c, 1024), D.Nodes(L, m, c), h))

def lv.y(+m: Cr.Cir.Cells, +L: List<&2, D.Rt>, +Y: List<&2, U32>, +c: U32, h: {D.Mem(Y, c) == True{} : Bool}) -> {Lv(m, L, Y, c) == True{} : Bool}:
  CK.Bo.or_ir(Lv0(m, L, c), D.Mem(Y, c), h)

# a node of a frame's term, the owned roots' or the temporaries' is live
def lv.os(+os: List<&2, D.Rt>, +hl: List<&2, D.Rt>, +fs: List<&2, D.AF>, +m: Cr.Cir.Cells, +sp: U32, +cs: List<&2, U32>, +c: U32,
  h: {D.Nodes(os, m, c) == True{} : Bool}) -> {Lv(m, Lst(os, hl, fs, m, sp), Yc(fs, m, sp, cs), c) == True{} : Bool}:
  lv.nd(m, Lst(os, hl, fs, m, sp), Yc(fs, m, sp, cs), c, nodes.in.l(os, List.append(&2, D.Rt, hl, D.Fr.rts(fs, m, sp)), m, c, h))

def lv.hl(+os: List<&2, D.Rt>, +hl: List<&2, D.Rt>, +fs: List<&2, D.AF>, +m: Cr.Cir.Cells, +sp: U32, +cs: List<&2, U32>, +c: U32,
  h: {D.Nodes(hl, m, c) == True{} : Bool}) -> {Lv(m, Lst(os, hl, fs, m, sp), Yc(fs, m, sp, cs), c) == True{} : Bool}:
  lv.nd(m, Lst(os, hl, fs, m, sp), Yc(fs, m, sp, cs), c, nodes.in.r(os, List.append(&2, D.Rt, hl, D.Fr.rts(fs, m, sp)), m, c,
    nodes.in.l(hl, D.Fr.rts(fs, m, sp), m, c, h)))

def lv.fr(+os: List<&2, D.Rt>, +hl: List<&2, D.Rt>, +fs: List<&2, D.AF>, +m: Cr.Cir.Cells, +sp: U32, +cs: List<&2, U32>, +c: U32,
  h: {D.Nodes(D.Fr.rts(fs, m, sp), m, c) == True{} : Bool}) -> {Lv(m, Lst(os, hl, fs, m, sp), Yc(fs, m, sp, cs), c) == True{} : Bool}:
  lv.nd(m, Lst(os, hl, fs, m, sp), Yc(fs, m, sp, cs), c, nodes.in.r(os, List.append(&2, D.Rt, hl, D.Fr.rts(fs, m, sp)), m, c,
    nodes.in.r(hl, D.Fr.rts(fs, m, sp), m, c, h)))

# a frame g points to the roots of the frames' terms
def fr.here(+kind: D.FK, +m: Cr.Cir.Cells, +ps: List<&2, U32>, +fr: U32, +c: U32, +a: Bk.Term, +b: Bk.Term, +R: List<&2, D.Rt>,
  htg: {D.Tg(m, fr) == D.FK.tag(kind) : U32}, hps: {D.Mem(ps, fr) == False{} : Bool}, hc: {D.Mem(D.Fs(m, ps, fr), c) == True{} : Bool}) ->
  {Bool.or(D.Node(a, m, D.Fd(2n, m, fr), c), D.Nodes(List.append(&2, D.Rt, D.Fr.rts.b(m, fr, kind, b), R), m, c)) == True{} : Bool}:
  +hc2 = {(%D.fs.frame(m, ps, fr, D.FK.tag(kind), htg, D.fk.lt(kind), D.fk.ge(kind), D.fk.le(kind), hps) : {D.Mem(_, c) == True{} : Bool}; hc) :
    {D.Mem(Con{D.Fd(2n, m, fr), D.Fs.opt(U32.is_eq(D.FK.tag(kind), 38), D.Fd(3n, m, fr), Nil{})}, c) == True{} : Bool}}
  D.or.cases(U32.is_eq(D.Fd(2n, m, fr), c), D.Mem(D.Fs.opt(U32.is_eq(D.FK.tag(kind), 38), D.Fd(3n, m, fr), Nil{}), c),
    {Bool.or(D.Node(a, m, D.Fd(2n, m, fr), c), D.Nodes(List.append(&2, D.Rt, D.Fr.rts.b(m, fr, kind, b), R), m, c)) == True{} : Bool}, hc2,
    e => CK.Bo.or_il(D.Node(a, m, D.Fd(2n, m, fr), c), D.Nodes(List.append(&2, D.Rt, D.Fr.rts.b(m, fr, kind, b), R), m, c),
      (%CK.U.eq(D.Fd(2n, m, fr), c, e) : {D.Node(a, m, D.Fd(2n, m, fr), _) == True{} : Bool}; node.root(a, m, D.Fd(2n, m, fr)))),
    e => CK.Bo.or_ir(D.Node(a, m, D.Fd(2n, m, fr), c), D.Nodes(List.append(&2, D.Rt, D.Fr.rts.b(m, fr, kind, b), R), m, c),
      fr.b.fs(kind, m, fr, b, R, c, e)))

# a pointer of a frame is the root of a frame's term
def fr.fs(fs: List<&2, D.AF>, +dk: Bool, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +fr: U32, +g: U32, +c: U32,
  h: D.FrsK(dk, ds, m, im, fi, nx, ks, img, ps, fr, fs), hg: {D.Mem(D.Fr.cells(fs, m, fr), g) == True{} : Bool},
  +hc: {D.Mem(D.Fs(m, ps, g), c) == True{} : Bool}) -> {D.Nodes(D.Fr.rts(fs, m, fr), m, c) == True{} : Bool}:
  match fs:
    case Nil{}:
      CK.Bo.tf({D.Nodes(D.Fr.rts(Nil{}, m, fr), m, c) == True{} : Bool}, hg)
    case Con{D.AF{+kind, +q, +k, +a, +b}, +rest}:
      (h0, w1) = h
      (h1, w2) = w1
      (hown, w3) = w2
      (hst, w4) = w3
      (hps, w5) = w4
      (htg, w6) = w5
      (hq, w7) = w6
      (hk, w8) = w7
      (ia, w9) = w8
      (ib, hr) = w9
      D.or.cases(U32.is_eq(fr, g), D.Mem(D.Fr.cells(rest, m, D.Fd(1n, m, fr)), g),
        {D.Nodes(D.Fr.rts(Con{D.AF{kind, q, k, a, b}, rest}, m, fr), m, c) == True{} : Bool}, hg,
        e => fr.here(kind, m, ps, fr, c, a, b, D.Fr.rts(rest, m, D.Fd(1n, m, fr)), htg, hps,
          (%Equal.sym(U32, fr, g, CK.U.eq(fr, g, e)) : {D.Mem(D.Fs(m, ps, _), c) == True{} : Bool}; hc)),
        e => CK.Bo.or_ir(D.Node(a, m, D.Fd(2n, m, fr), c), D.Nodes(List.append(&2, D.Rt, D.Fr.rts.b(m, fr, kind, b), D.Fr.rts(rest, m, D.Fd(1n, m, fr))), m, c),
          nodes.in.r(D.Fr.rts.b(m, fr, kind, b), D.Fr.rts(rest, m, D.Fd(1n, m, fr)), m, c,
            fr.fs(rest, dk, ds, m, im, fi, nx, ks, img, ps, D.Fd(1n, m, fr), g, c, hr, e, hc))))

# a pointer of a temporary: STATIC, a temporary or a root of a held term: live
def lv.tmp(+os: List<&2, D.Rt>, +hl: List<&2, D.Rt>, +fs: List<&2, D.AF>, +m: Cr.Cir.Cells, +sp: U32, +cs: List<&2, U32>, +c: U32,
  h: {Bool.or(D.Fl(m, c, 1024), Bool.or(D.Mem(cs, c), D.Mem(D.Rt.cells(hl), c))) == True{} : Bool}) ->
  {Lv(m, Lst(os, hl, fs, m, sp), Yc(fs, m, sp, cs), c) == True{} : Bool}:
  or3.case(D.Fl(m, c, 1024), D.Mem(cs, c), D.Mem(D.Rt.cells(hl), c), {Lv(m, Lst(os, hl, fs, m, sp), Yc(fs, m, sp, cs), c) == True{} : Bool}, h,
    e => lv.st(m, Lst(os, hl, fs, m, sp), Yc(fs, m, sp, cs), c, e),
    e => lv.y(m, Lst(os, hl, fs, m, sp), Yc(fs, m, sp, cs), c, mem.in.r(D.Fr.cells(fs, m, sp), cs, c, e)),
    e => lv.hl(os, hl, fs, m, sp, cs, c, root.nodes(hl, m, c, e)))

# a pointer c of a live cell g of the machine's own is live: by Clo when g is
# STATIC or a temporary, by its term when g is a node, by its frame when g is
# a frame
def lv.fs(+dk: Bool, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +tbl: D.Tbl(m, im, fi, nx), +os: List<&2, D.Rt>, +hl: List<&2, D.Rt>, +fs: List<&2, D.AF>,
  +sp: U32, +cs: List<&2, U32>, +g: U32, +c: U32, +hL: D.RtsK(dk, ds, m, im, fi, nx, ks, img, Lst(os, hl, fs, m, sp)),
  +hF: D.FrsK(dk, ds, m, im, fi, nx, ks, img, ps, sp, fs), hlv: {Lv(m, Lst(os, hl, fs, m, sp), Yc(fs, m, sp, cs), g) == True{} : Bool},
  +hca: {D.Clo.at(m, g, ps, cs, D.Rt.cells(hl)) == True{} : Bool}, +hm: {D.Mem(D.Fs(m, ps, g), c) == True{} : Bool}) ->
  {Lv(m, Lst(os, hl, fs, m, sp), Yc(fs, m, sp, cs), c) == True{} : Bool}:
  +L = Lst(os, hl, fs, m, sp)
  +Y = Yc(fs, m, sp, cs)
  +C1 = Bool.or(Bool.not(D.Fl(m, g, 1024)), D.All.static(D.Fs(m, ps, g), m))
  +C2 = Bool.or(Bool.not(D.Mem(cs, g)), D.All.held(D.Fs(m, ps, g), m, cs, D.Rt.cells(hl)))
  D.or.cases(Lv0(m, L, g), D.Mem(Y, g), {Lv(m, Lst(os, hl, fs, m, sp), Yc(fs, m, sp, cs), c) == True{} : Bool}, hlv,
    e => D.or.cases(D.Fl(m, g, 1024), D.Nodes(L, m, g), {Lv(m, Lst(os, hl, fs, m, sp), Yc(fs, m, sp, cs), c) == True{} : Bool}, e,
      e1 => lv.st(m, L, Y, c, static.mem(D.Fs(m, ps, g), m, c, CK.Bo.or_r(Bool.not(D.Fl(m, g, 1024)), D.All.static(D.Fs(m, ps, g), m),
        CK.Bo.and_l(C1, C2, hca), (%Equal.sym(Bool, D.Fl(m, g, 1024), True{}, e1) : {Bool.not(_) == False{} : Bool}; {==})), hm)),
      e1 => lv.nd(m, L, Y, c, nodes.fs(L, dk, ds, m, im, fi, nx, ks, img, ps, tbl, g, c, hL, e1, hm))),
    e => D.or.cases(D.Mem(D.Fr.cells(fs, m, sp), g), D.Mem(cs, g), {Lv(m, Lst(os, hl, fs, m, sp), Yc(fs, m, sp, cs), c) == True{} : Bool}, mem.split(D.Fr.cells(fs, m, sp), cs, g, e),
      e1 => lv.fr(os, hl, fs, m, sp, cs, c, fr.fs(fs, dk, ds, m, im, fi, nx, ks, img, ps, sp, g, c, hF, e1, hm)),
      +e1 => lv.tmp(os, hl, fs, m, sp, cs, c, held.mem(D.Fs(m, ps, g), m, cs, D.Rt.cells(hl), c,
        CK.Bo.or_r(Bool.not(D.Mem(cs, g)), D.All.held(D.Fs(m, ps, g), m, cs, D.Rt.cells(hl)), CK.Bo.and_r(C1, C2, hca),
          (%Equal.sym(Bool, D.Mem(cs, g), True{}, e1) : {Bool.not(_) == False{} : Bool}; {==})), hm))))

# no live cell of the k cells from o points to the garbage cell c
def pcn.zero.b(b: Bool, +k: Nat, +dk: Bool, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +tbl: D.Tbl(m, im, fi, nx), +os: List<&2, D.Rt>,
  +hl: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +cs: List<&2, U32>, +o: U32, +c: U32,
  +hL: D.RtsK(dk, ds, m, im, fi, nx, ks, img, Lst(os, hl, fs, m, sp)), +hF: D.FrsK(dk, ds, m, im, fi, nx, ks, img, ps, sp, fs),
  eb: {Lv(m, Lst(os, hl, fs, m, sp), Yc(fs, m, sp, cs), o) == b : Bool}, +hc: {Lv(m, Lst(os, hl, fs, m, sp), Yc(fs, m, sp, cs), c) == False{} : Bool},
  +hca: {D.Clo.at(m, o, ps, cs, D.Rt.cells(hl)) == True{} : Bool},
  ih: {PcN(k, m, ps, U32.inc(o), c, Lst(os, hl, fs, m, sp), Yc(fs, m, sp, cs)) == 0n : Nat}) ->
  {Nat.add(Bool.pick(Nat, b, D.RcL(D.Fs(m, ps, o), c), 0n), PcN(k, m, ps, U32.inc(o), c, Lst(os, hl, fs, m, sp), Yc(fs, m, sp, cs))) == 0n : Nat}:
  match b:
    case True{}:
      +nm = bool.case(D.Mem(D.Fs(m, ps, o), c), D.Mem(D.Fs(m, ps, o), c), {D.Mem(D.Fs(m, ps, o), c) == False{} : Bool}, {==},
        e => CK.Bo.tf({D.Mem(D.Fs(m, ps, o), c) == False{} : Bool}, Equal.trans(Bool, False{}, Lv(m, Lst(os, hl, fs, m, sp), Yc(fs, m, sp, cs), c), True{},
          Equal.sym(Bool, Lv(m, Lst(os, hl, fs, m, sp), Yc(fs, m, sp, cs), c), False{}, hc),
          lv.fs(dk, ds, m, im, fi, nx, ks, img, ps, tbl, os, hl, fs, sp, cs, o, c, hL, hF, eb, hca, e))),
        e => e)
      %Equal.sym(Nat, D.RcL(D.Fs(m, ps, o), c), 0n, rcl.zero(D.Fs(m, ps, o), c, nm)) :
        {Nat.add(_, PcN(k, m, ps, U32.inc(o), c, Lst(os, hl, fs, m, sp), Yc(fs, m, sp, cs))) == 0n : Nat}
      ih
    case False{}:
      ih

def pcn.zero(k: Nat, +dk: Bool, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +tbl: D.Tbl(m, im, fi, nx), +os: List<&2, D.Rt>,
  +hl: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +cs: List<&2, U32>, +o: U32, +c: U32,
  +hL: D.RtsK(dk, ds, m, im, fi, nx, ks, img, Lst(os, hl, fs, m, sp)), +hF: D.FrsK(dk, ds, m, im, fi, nx, ks, img, ps, sp, fs),
  +hc: {Lv(m, Lst(os, hl, fs, m, sp), Yc(fs, m, sp, cs), c) == False{} : Bool},
  hcl: {D.Clo(k, m, o, ps, cs, D.Rt.cells(hl)) == True{} : Bool}) ->
  {PcN(k, m, ps, o, c, Lst(os, hl, fs, m, sp), Yc(fs, m, sp, cs)) == 0n : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+(+q):
      +h2 = hcl
      pcn.zero.b(Lv(m, Lst(os, hl, fs, m, sp), Yc(fs, m, sp, cs), o), q, dk, ds, m, im, fi, nx, ks, img, ps, tbl, os, hl, fs, sp, cs, o, c, hL, hF,
        {==}, hc, D.and.l(D.Clo.at(m, o, ps, cs, D.Rt.cells(hl)), D.Clo(q, m, U32.inc(o), ps, cs, D.Rt.cells(hl)), h2),
        pcn.zero(q, dk, ds, m, im, fi, nx, ks, img, ps, tbl, os, hl, fs, sp, cs, U32.inc(o), c, hL, hF, hc,
          D.and.r(D.Clo.at(m, o, ps, cs, D.Rt.cells(hl)), D.Clo(q, m, U32.inc(o), ps, cs, D.Rt.cells(hl)), h2)))

# a live cell g of the k cells from o: its pointers to c are among the live cells'
def pcn.at.b(b: Bool, +k: Nat, +m: Cr.Cir.Cells, +ps: List<&2, U32>, +o: U32, +g: U32, +c: U32, +L: List<&2, D.Rt>, +Y: List<&2, U32>,
  +eb: {U32.is_eq(o, g) == b : Bool}, +h1: N.Le(U32.to_nat(o), U32.to_nat(g)), +h2: N.Le(1n+U32.to_nat(g), Nat.add(U32.to_nat(o), 1n+k)),
  +hlv: {Lv(m, L, Y, g) == True{} : Bool},
  ih: N.Le(U32.to_nat(U32.inc(o)), U32.to_nat(g)) -> N.Le(1n+U32.to_nat(g), Nat.add(U32.to_nat(U32.inc(o)), k)) ->
    N.Le(D.RcL(D.Fs(m, ps, g), c), PcN(k, m, ps, U32.inc(o), c, L, Y))) ->
  N.Le(D.RcL(D.Fs(m, ps, g), c), Nat.add(Bool.pick(Nat, Lv(m, L, Y, o), D.RcL(D.Fs(m, ps, o), c), 0n), PcN(k, m, ps, U32.inc(o), c, L, Y))):
  match b:
    case True{}:
      %Equal.sym(U32, o, g, D.u32.eq(o, g, eb)) :
        N.Le(D.RcL(D.Fs(m, ps, g), c), Nat.add(Bool.pick(Nat, Lv(m, L, Y, _), D.RcL(D.Fs(m, ps, _), c), 0n), PcN(k, m, ps, U32.inc(o), c, L, Y)))
      %Equal.sym(Bool, Lv(m, L, Y, g), True{}, hlv) :
        N.Le(D.RcL(D.Fs(m, ps, g), c), Nat.add(Bool.pick(Nat, _, D.RcL(D.Fs(m, ps, g), c), 0n), PcN(k, m, ps, U32.inc(o), c, L, Y)))
      N.le_add_r(D.RcL(D.Fs(m, ps, g), c), PcN(k, m, ps, U32.inc(o), c, L, Y))
    case False{}:
      N.le_trans(D.RcL(D.Fs(m, ps, g), c), PcN(k, m, ps, U32.inc(o), c, L, Y),
        Nat.add(Bool.pick(Nat, Lv(m, L, Y, o), D.RcL(D.Fs(m, ps, o), c), 0n), PcN(k, m, ps, U32.inc(o), c, L, Y)),
        ih(rng.lo(k, o, g, eb, h1), rng.hi(k, o, g, eb, h1, h2)),
        N.le_add_l(Bool.pick(Nat, Lv(m, L, Y, o), D.RcL(D.Fs(m, ps, o), c), 0n), PcN(k, m, ps, U32.inc(o), c, L, Y)))

def pcn.at(n: Nat, +m: Cr.Cir.Cells, +ps: List<&2, U32>, +o: U32, +g: U32, +c: U32, +L: List<&2, D.Rt>, +Y: List<&2, U32>,
  h1: N.Le(U32.to_nat(o), U32.to_nat(g)), h2: N.Le(1n+U32.to_nat(g), Nat.add(U32.to_nat(o), n)), +hlv: {Lv(m, L, Y, g) == True{} : Bool}) ->
  N.Le(D.RcL(D.Fs(m, ps, g), c), PcN(n, m, ps, o, c, L, Y)):
  match n:
    case 0n:
      rng.none(N.Le(D.RcL(D.Fs(m, ps, g), c), 0n), o, g, h1, h2)
    case 1n+(+k):
      pcn.at.b(U32.is_eq(o, g), k, m, ps, o, g, c, L, Y, {==}, h1, h2, hlv, x => y => pcn.at(k, m, ps, U32.inc(o), g, c, L, Y, x, y, hlv))

# a live cell g of the machine's own that points to c: the live cells' pointers to c are at least 1
def pcn.one(+m: Cr.Cir.Cells, +ps: List<&2, U32>, +fi: U32, +nx: U32, +g: U32, +c: U32, +L: List<&2, D.Rt>, +Y: List<&2, U32>,
  +own: {D.Own(fi, nx, g) == True{} : Bool}, +hlv: {Lv(m, L, Y, g) == True{} : Bool}, hm: {D.Mem(D.Fs(m, ps, g), c) == True{} : Bool}) ->
  N.Le(1n, PcN(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, ps, fi, c, L, Y)):
  N.le_trans(1n, D.RcL(D.Fs(m, ps, g), c), PcN(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, ps, fi, c, L, Y), D.rcl.mem(D.Fs(m, ps, g), c, hm),
    pcn.at(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, ps, fi, g, c, L, Y, own.lo(fi, nx, g, own), own.hi(fi, nx, g, own), hlv))

# a node p, not STATIC, of a term of the roots A: a root of A, or a node of
# their terms of the machine's own points to it (G by either)
def lptr.par(+rest: List<&2, D.Rt>, -dk: Bool, +m: Cr.Cir.Cells, +ps: List<&2, U32>, +fi: U32, +nx: U32, +r: U32, +u: Bk.Term, +p: U32,
  ex: D.Ex(U32, g => D.P2({D.Node(u, m, r, g) == True{} : Bool}, D.P2({D.Mem(D.Fs(m, ps, g), p) == True{} : Bool}, D.Sp(fi, nx, g, Cr.Cir.Cells.get(m, p))))),
  +hst: {D.Fl(m, p, 1024) == False{} : Bool}, -G: Type,
  kpar: @g: U32 -> {D.Own(fi, nx, g) == True{} : Bool} -> {D.Nodes(Con{D.Rt{r, u}, rest}, m, g) == True{} : Bool} -> {D.Mem(D.Fs(m, ps, g), p) == True{} : Bool} -> G) -> G:
  (+g, rr) = ex
  (hn, rr2) = rr
  (hm, hsp) = rr2
  kpar(g, or.l2(D.Own(fi, nx, g), D.FlW(Cr.Cir.Cell.get(0n, Cr.Cir.Cells.get(m, p)), 1024), hsp, hst),
    CK.Bo.or_il(D.Node(u, m, r, g), D.Nodes(rest, m, g), hn), hm)

def lptr.nd(c: Bool, +rest: List<&2, D.Rt>, +dk: Bool, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +tbl: D.Tbl(m, im, fi, nx), +r: U32, +u: Bk.Term, +p: U32,
  ec: {U32.is_eq(r, p) == c : Bool}, en: {D.Node(u, m, r, p) == True{} : Bool}, hu: D.IsK(dk, ds, m, im, fi, nx, ks, img, r, u),
  +hst: {D.Fl(m, p, 1024) == False{} : Bool}, -G: Type,
  kroot: {D.Mem(D.Rt.cells(Con{D.Rt{r, u}, rest}), p) == True{} : Bool} -> G,
  kpar: @g: U32 -> {D.Own(fi, nx, g) == True{} : Bool} -> {D.Nodes(Con{D.Rt{r, u}, rest}, m, g) == True{} : Bool} -> {D.Mem(D.Fs(m, ps, g), p) == True{} : Bool} -> G) -> G:
  match c:
    case True{}:
      kroot(CK.Bo.or_il(U32.is_eq(r, p), D.Mem(D.Rt.cells(rest), p), ec))
    case False{}:
      lptr.par(rest, dk, m, ps, fi, nx, r, u, p, node.par(u, dk, ds, m, im, fi, nx, ks, img, ps, tbl, r, p, hu, en, ec), hst, G, kpar)

def lptr.b(b: Bool, +rest: List<&2, D.Rt>, +dk: Bool, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +tbl: D.Tbl(m, im, fi, nx), +r: U32, +u: Bk.Term, +p: U32,
  eb: {D.Node(u, m, r, p) == b : Bool}, h: {Bool.or(b, D.Nodes(rest, m, p)) == True{} : Bool}, hu: D.IsK(dk, ds, m, im, fi, nx, ks, img, r, u),
  +hst: {D.Fl(m, p, 1024) == False{} : Bool}, -G: Type,
  kroot: {D.Mem(D.Rt.cells(Con{D.Rt{r, u}, rest}), p) == True{} : Bool} -> G,
  kpar: @g: U32 -> {D.Own(fi, nx, g) == True{} : Bool} -> {D.Nodes(Con{D.Rt{r, u}, rest}, m, g) == True{} : Bool} -> {D.Mem(D.Fs(m, ps, g), p) == True{} : Bool} -> G,
  ih: {D.Nodes(rest, m, p) == True{} : Bool} -> ({D.Mem(D.Rt.cells(rest), p) == True{} : Bool} -> G) -> (@g: U32 -> {D.Own(fi, nx, g) == True{} : Bool} -> {D.Nodes(rest, m, g) == True{} : Bool} -> {D.Mem(D.Fs(m, ps, g), p) == True{} : Bool} -> G) -> G) -> G:
  match b:
    case True{}:
      lptr.nd(U32.is_eq(r, p), rest, dk, ds, m, im, fi, nx, ks, img, ps, tbl, r, u, p, {==}, eb, hu, hst, G, kroot, kpar)
    case False{}:
      ih(h, hh => kroot(CK.Bo.or_ir(U32.is_eq(r, p), D.Mem(D.Rt.cells(rest), p), hh)),
        +g => o => n => mm => kpar(g, o, CK.Bo.or_ir(D.Node(u, m, r, g), D.Nodes(rest, m, g), n), mm))

def lptr(A: List<&2, D.Rt>, +dk: Bool, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +tbl: D.Tbl(m, im, fi, nx), +p: U32,
  hA: D.RtsK(dk, ds, m, im, fi, nx, ks, img, A), h: {D.Nodes(A, m, p) == True{} : Bool}, +hst: {D.Fl(m, p, 1024) == False{} : Bool}, -G: Type,
  kroot: {D.Mem(D.Rt.cells(A), p) == True{} : Bool} -> G,
  kpar: @g: U32 -> {D.Own(fi, nx, g) == True{} : Bool} -> {D.Nodes(A, m, g) == True{} : Bool} -> {D.Mem(D.Fs(m, ps, g), p) == True{} : Bool} -> G) -> G:
  match A:
    case Nil{}:
      CK.Bo.tf(G, h)
    case Con{D.Rt{+r, +u}, +rest}:
      (hu, hrest) = hA
      lptr.b(D.Node(u, m, r, p), rest, dk, ds, m, im, fi, nx, ks, img, ps, tbl, r, u, p, {==}, h, hu, hst, G, kroot, kpar,
        hh => kr => kp => lptr(rest, dk, ds, m, im, fi, nx, ks, img, ps, tbl, p, hrest, hh, hst, G, kr, kp))

# a root p of a term that a temporary holds: the temporary, of the machine's own, points to it
def tmp.ptr.b(b: Bool, +c: U32, +h: List<&2, D.Rt>, +rest: List<&2, D.TmpE>, +m: Cr.Cir.Cells, +fi: U32, +nx: U32, +ps: List<&2, U32>,
  +rs: List<&2, D.Rt>, +p: U32, eb: {D.Mem(D.Rt.cells(h), p) == b : Bool},
  hor: {Bool.or(b, D.Mem(D.Rt.cells(D.Tmp.held(rest)), p)) == True{} : Bool}, own: {D.Own(fi, nx, c) == True{} : Bool},
  allin: {D.AllIn(D.Rt.cells(h), D.Fs(m, ps, c)) == True{} : Bool}, -G: Type,
  k: @g: U32 -> {D.Mem(D.Tmp.cells(Con{D.TmpE{c, h}, rest}), g) == True{} : Bool} -> {D.Own(fi, nx, g) == True{} : Bool} ->
    {D.Mem(D.Fs(m, ps, g), p) == True{} : Bool} -> G,
  ih: {D.Mem(D.Rt.cells(D.Tmp.held(rest)), p) == True{} : Bool} -> (@g: U32 -> {D.Mem(D.Tmp.cells(rest), g) == True{} : Bool} -> {D.Own(fi, nx, g) == True{} : Bool} -> {D.Mem(D.Fs(m, ps, g), p) == True{} : Bool} -> G) -> G) -> G:
  match b:
    case True{}:
      k(c, CK.Bo.or_il(U32.is_eq(c, c), D.Mem(D.Tmp.cells(rest), c), CK.U.eq_refl(c)), own, allin.mem(D.Rt.cells(h), D.Fs(m, ps, c), p, allin, eb))
    case False{}:
      ih(hor, +g => hg => ho => hm => k(g, CK.Bo.or_ir(U32.is_eq(c, g), D.Mem(D.Tmp.cells(rest), g), hg), ho, hm))

def tmp.ptr(xs: List<&2, D.TmpE>, +m: Cr.Cir.Cells, +fi: U32, +nx: U32, +ps: List<&2, U32>, +rs: List<&2, D.Rt>, +p: U32,
  hok: {D.Tmp.ok(xs, m, fi, nx, ps, rs) == True{} : Bool}, hp: {D.Mem(D.Rt.cells(D.Tmp.held(xs)), p) == True{} : Bool}, -G: Type,
  k: @g: U32 -> {D.Mem(D.Tmp.cells(xs), g) == True{} : Bool} -> {D.Own(fi, nx, g) == True{} : Bool} -> {D.Mem(D.Fs(m, ps, g), p) == True{} : Bool} -> G) -> G:
  match xs:
    case Nil{}:
      CK.Bo.tf(G, hp)
    case Con{D.TmpE{+c, +h}, +rest}:
      +A0 = D.Own(fi, nx, c)
      +A1 = Bool.not(D.Fl(m, c, 1024))
      +A2 = Bool.not(D.Mem(ps, c))
      +A3 = Bool.not(D.Mem(D.Tmp.cells(rest), c))
      +A4 = Bool.not(D.Nodes(rs, m, c))
      +A5 = D.AllIn(D.Rt.cells(h), D.Fs(m, ps, c))
      +A6 = D.Tmp.ok(rest, m, fi, nx, ps, rs)
      +ok = hok
      +r1 = CK.Bo.and_r(A0, Bool.and(A1, Bool.and(A2, Bool.and(A3, Bool.and(A4, Bool.and(A5, A6))))), ok)
      +r2 = CK.Bo.and_r(A1, Bool.and(A2, Bool.and(A3, Bool.and(A4, Bool.and(A5, A6)))), r1)
      +r3 = CK.Bo.and_r(A2, Bool.and(A3, Bool.and(A4, Bool.and(A5, A6))), r2)
      +r4 = CK.Bo.and_r(A3, Bool.and(A4, Bool.and(A5, A6)), r3)
      +r5 = CK.Bo.and_r(A4, Bool.and(A5, A6), r4)
      tmp.ptr.b(D.Mem(D.Rt.cells(h), p), c, h, rest, m, fi, nx, ps, rs, p, {==},
        mem.split(D.Rt.cells(h), D.Rt.cells(D.Tmp.held(rest)), p, (%rt.cells.app(h, D.Tmp.held(rest)) : {D.Mem(_, p) == True{} : Bool}; hp)),
        CK.Bo.and_l(A0, Bool.and(A1, Bool.and(A2, Bool.and(A3, Bool.and(A4, Bool.and(A5, A6))))), ok),
        CK.Bo.and_l(A5, A6, r5), G, k, hh => kk => tmp.ptr(rest, m, fi, nx, ps, rs, p, CK.Bo.and_r(A5, A6, r5), hh, G, kk))

# the root p of a frame's b term (field 3, Rwt) is among the frame's pointers
def fr.b.ptr(kind: D.FK, +m: Cr.Cir.Cells, +fr: U32, +b: Bk.Term, +p: U32, h: {D.Mem(D.Rt.cells(D.Fr.rts.b(m, fr, kind, b)), p) == True{} : Bool}) ->
  {D.Mem(Con{D.Fd(2n, m, fr), D.Fs.opt(U32.is_eq(D.FK.tag(kind), 38), D.Fd(3n, m, fr), Nil{})}, p) == True{} : Bool}:
  match kind:
    case D.FK.rwt{}:
      CK.Bo.or_ir(U32.is_eq(D.Fd(2n, m, fr), p), Bool.or(U32.is_eq(D.Fd(3n, m, fr), p), False{}), h)
    case D.FK.arg{}:
      CK.Bo.tf({Bool.or(U32.is_eq(D.Fd(2n, m, fr), p), False{}) == True{} : Bool}, h)
    case D.FK.val{}:
      CK.Bo.tf({Bool.or(U32.is_eq(D.Fd(2n, m, fr), p), False{}) == True{} : Bool}, h)
    case D.FK.fun{}:
      CK.Bo.tf({Bool.or(U32.is_eq(D.Fd(2n, m, fr), p), False{}) == True{} : Bool}, h)
    case D.FK.let{}:
      CK.Bo.tf({Bool.or(U32.is_eq(D.Fd(2n, m, fr), p), False{}) == True{} : Bool}, h)
    case D.FK.tupb{}:
      CK.Bo.tf({Bool.or(U32.is_eq(D.Fd(2n, m, fr), p), False{}) == True{} : Bool}, h)
    case D.FK.tupa{}:
      CK.Bo.tf({Bool.or(U32.is_eq(D.Fd(2n, m, fr), p), False{}) == True{} : Bool}, h)
    case D.FK.minb{}:
      CK.Bo.tf({Bool.or(U32.is_eq(D.Fd(2n, m, fr), p), False{}) == True{} : Bool}, h)
    case D.FK.mina{}:
      CK.Bo.tf({Bool.or(U32.is_eq(D.Fd(2n, m, fr), p), False{}) == True{} : Bool}, h)

# a root p of a frame's term: the frame, of the machine's own, points to it
def frt.ptr.c(cc: Bool, +rest: List<&2, D.AF>, +dk: Bool, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +kind: D.FK, +b: Bk.Term, +fr: U32, +p: U32,
  ec: {D.Mem(D.Rt.cells(D.Fr.rts.b(m, fr, kind, b)), p) == cc : Bool},
  hor: {Bool.or(cc, D.Mem(D.Rt.cells(D.Fr.rts(rest, m, D.Fd(1n, m, fr))), p)) == True{} : Bool}, hown: {D.Own(fi, nx, fr) == True{} : Bool},
  hps: {D.Mem(ps, fr) == False{} : Bool}, htg: {D.Tg(m, fr) == D.FK.tag(kind) : U32}, -G: Type,
  k: @g: U32 -> {D.Mem(Con{fr, D.Fr.cells(rest, m, D.Fd(1n, m, fr))}, g) == True{} : Bool} -> {D.Own(fi, nx, g) == True{} : Bool} ->
    {D.Mem(D.Fs(m, ps, g), p) == True{} : Bool} -> G, ih: {D.Mem(D.Rt.cells(D.Fr.rts(rest, m, D.Fd(1n, m, fr))), p) == True{} : Bool} -> (@g: U32 -> {D.Mem(D.Fr.cells(rest, m, D.Fd(1n, m, fr)), g) == True{} : Bool} -> {D.Own(fi, nx, g) == True{} : Bool} -> {D.Mem(D.Fs(m, ps, g), p) == True{} : Bool} -> G) -> G) -> G:
  match cc:
    case True{}:
      k(fr, CK.Bo.or_il(U32.is_eq(fr, fr), D.Mem(D.Fr.cells(rest, m, D.Fd(1n, m, fr)), fr), CK.U.eq_refl(fr)), hown,
        (%Equal.sym(List<&2, U32>, D.Fs(m, ps, fr), Con{D.Fd(2n, m, fr), D.Fs.opt(U32.is_eq(D.FK.tag(kind), 38), D.Fd(3n, m, fr), Nil{})},
          D.fs.frame(m, ps, fr, D.FK.tag(kind), htg, D.fk.lt(kind), D.fk.ge(kind), D.fk.le(kind), hps)) : {D.Mem(_, p) == True{} : Bool};
          fr.b.ptr(kind, m, fr, b, p, ec)))
    case False{}:
      ih(hor, +g => hg => ho => hm => k(g, CK.Bo.or_ir(U32.is_eq(fr, g), D.Mem(D.Fr.cells(rest, m, D.Fd(1n, m, fr)), g), hg), ho, hm))

def frt.ptr.b(bb: Bool, +rest: List<&2, D.AF>, +dk: Bool, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +kind: D.FK, +b: Bk.Term, +fr: U32, +p: U32,
  eb: {U32.is_eq(D.Fd(2n, m, fr), p) == bb : Bool},
  hp: {Bool.or(bb, D.Mem(D.Rt.cells(List.append(&2, D.Rt, D.Fr.rts.b(m, fr, kind, b), D.Fr.rts(rest, m, D.Fd(1n, m, fr)))), p)) == True{} : Bool},
  hown: {D.Own(fi, nx, fr) == True{} : Bool}, hps: {D.Mem(ps, fr) == False{} : Bool}, htg: {D.Tg(m, fr) == D.FK.tag(kind) : U32}, -G: Type,
  k: @g: U32 -> {D.Mem(Con{fr, D.Fr.cells(rest, m, D.Fd(1n, m, fr))}, g) == True{} : Bool} -> {D.Own(fi, nx, g) == True{} : Bool} ->
    {D.Mem(D.Fs(m, ps, g), p) == True{} : Bool} -> G, ih: {D.Mem(D.Rt.cells(D.Fr.rts(rest, m, D.Fd(1n, m, fr))), p) == True{} : Bool} -> (@g: U32 -> {D.Mem(D.Fr.cells(rest, m, D.Fd(1n, m, fr)), g) == True{} : Bool} -> {D.Own(fi, nx, g) == True{} : Bool} -> {D.Mem(D.Fs(m, ps, g), p) == True{} : Bool} -> G) -> G) -> G:
  match bb:
    case True{}:
      k(fr, CK.Bo.or_il(U32.is_eq(fr, fr), D.Mem(D.Fr.cells(rest, m, D.Fd(1n, m, fr)), fr), CK.U.eq_refl(fr)), hown,
        (%Equal.sym(List<&2, U32>, D.Fs(m, ps, fr), Con{D.Fd(2n, m, fr), D.Fs.opt(U32.is_eq(D.FK.tag(kind), 38), D.Fd(3n, m, fr), Nil{})},
          D.fs.frame(m, ps, fr, D.FK.tag(kind), htg, D.fk.lt(kind), D.fk.ge(kind), D.fk.le(kind), hps)) : {D.Mem(_, p) == True{} : Bool};
          CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, fr), p), D.Mem(D.Fs.opt(U32.is_eq(D.FK.tag(kind), 38), D.Fd(3n, m, fr), Nil{}), p), eb)))
    case False{}:
      frt.ptr.c(D.Mem(D.Rt.cells(D.Fr.rts.b(m, fr, kind, b)), p), rest, dk, ds, m, im, fi, nx, ks, img, ps, kind, b, fr, p, {==},
        mem.split(D.Rt.cells(D.Fr.rts.b(m, fr, kind, b)), D.Rt.cells(D.Fr.rts(rest, m, D.Fd(1n, m, fr))), p,
          (%rt.cells.app(D.Fr.rts.b(m, fr, kind, b), D.Fr.rts(rest, m, D.Fd(1n, m, fr))) : {D.Mem(_, p) == True{} : Bool}; hp)),
        hown, hps, htg, G, k, ih)

def frt.ptr(fs: List<&2, D.AF>, +dk: Bool, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +fr: U32, +p: U32,
  h: D.FrsK(dk, ds, m, im, fi, nx, ks, img, ps, fr, fs), hp: {D.Mem(D.Rt.cells(D.Fr.rts(fs, m, fr)), p) == True{} : Bool}, -G: Type,
  k: @g: U32 -> {D.Mem(D.Fr.cells(fs, m, fr), g) == True{} : Bool} -> {D.Own(fi, nx, g) == True{} : Bool} -> {D.Mem(D.Fs(m, ps, g), p) == True{} : Bool} -> G) -> G:
  match fs:
    case Nil{}:
      CK.Bo.tf(G, hp)
    case Con{D.AF{+kind, +q, +kk, +a, +b}, +rest}:
      (h0, w1) = h
      (h1, w2) = w1
      (hown, w3) = w2
      (hst, w4) = w3
      (hps, w5) = w4
      (htg, w6) = w5
      (hq, w7) = w6
      (hk, w8) = w7
      (ia, w9) = w8
      (ib, hr) = w9
      frt.ptr.b(U32.is_eq(D.Fd(2n, m, fr), p), rest, dk, ds, m, im, fi, nx, ks, img, ps, kind, b, fr, p, {==}, hp, hown, hps, htg, G, k,
        hh => kk => frt.ptr(rest, dk, ds, m, im, fi, nx, ks, img, ps, D.Fd(1n, m, fr), p, hr, hh, G, kk))

# a live node p, not STATIC: the live cells' pointers to it and the owned
# roots that are p are at least 1
def live.ptr(+dk: Bool, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +tbl: D.Tbl(m, im, fi, nx), +os: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +fs: List<&2, D.AF>,
  +sp: U32, +rs: List<&2, D.Rt>, +p: U32, +hos: D.RtsK(dk, ds, m, im, fi, nx, ks, img, os),
  +hhl: D.RtsK(dk, ds, m, im, fi, nx, ks, img, D.Tmp.held(xs)), +hF: D.FrsK(dk, ds, m, im, fi, nx, ks, img, ps, sp, fs),
  +hok: {D.Tmp.ok(xs, m, fi, nx, ps, rs) == True{} : Bool},
  hn: {D.Nodes(Lst(os, D.Tmp.held(xs), fs, m, sp), m, p) == True{} : Bool}, +hst: {D.Fl(m, p, 1024) == False{} : Bool}) ->
  N.Le(1n, Nat.add(PcN(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, ps, fi, p, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))),
    D.RcL(D.Rt.cells(os), p))):
  +hl = D.Tmp.held(xs)
  +cs = D.Tmp.cells(xs)
  +frt = D.Fr.rts(fs, m, sp)
  +frc = D.Fr.cells(fs, m, sp)
  +L = Lst(os, hl, fs, m, sp)
  +Y = Yc(fs, m, sp, cs)
  +n0 = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
  +P0 = PcN(n0, m, ps, fi, p, L, Y)
  +R0 = D.RcL(D.Rt.cells(os), p)
  D.or.cases(D.Nodes(os, m, p), D.Nodes(List.append(&2, D.Rt, hl, frt), m, p), N.Le(1n, Nat.add(P0, R0)),
    nodes.split(os, List.append(&2, D.Rt, hl, frt), m, p, hn),
    e => lptr(os, dk, ds, m, im, fi, nx, ks, img, ps, tbl, p, hos, e, hst, N.Le(1n, Nat.add(P0, R0)),
      hr => N.le_trans(1n, R0, Nat.add(P0, R0), D.rcl.mem(D.Rt.cells(os), p, hr), N.le_add_l(P0, R0)),
      +g => ho => hn2 => hm => N.le_trans(1n, P0, Nat.add(P0, R0), pcn.one(m, ps, fi, nx, g, p, L, Y, ho, lv.os(os, hl, fs, m, sp, cs, g, hn2), hm),
        N.le_add_r(P0, R0))),
    e => D.or.cases(D.Nodes(hl, m, p), D.Nodes(frt, m, p), N.Le(1n, Nat.add(P0, R0)), nodes.split(hl, frt, m, p, e),
      e2 => lptr(hl, dk, ds, m, im, fi, nx, ks, img, ps, tbl, p, hhl, e2, hst, N.Le(1n, Nat.add(P0, R0)),
        hr => tmp.ptr(xs, m, fi, nx, ps, rs, p, hok, hr, N.Le(1n, Nat.add(P0, R0)),
          +g => hg => ho => hm => N.le_trans(1n, P0, Nat.add(P0, R0),
            pcn.one(m, ps, fi, nx, g, p, L, Y, ho, lv.y(m, L, Y, g, mem.in.r(frc, cs, g, hg)), hm), N.le_add_r(P0, R0))),
        +g => ho => hn2 => hm => N.le_trans(1n, P0, Nat.add(P0, R0), pcn.one(m, ps, fi, nx, g, p, L, Y, ho, lv.hl(os, hl, fs, m, sp, cs, g, hn2), hm),
          N.le_add_r(P0, R0))),
      e2 => lptr(frt, dk, ds, m, im, fi, nx, ks, img, ps, tbl, p, AC.frs.rtsk(dk, ds, m, im, fi, nx, ks, img, ps, fs, sp, hF), e2, hst,
        N.Le(1n, Nat.add(P0, R0)),
        hr => frt.ptr(fs, dk, ds, m, im, fi, nx, ks, img, ps, sp, p, hF, hr, N.Le(1n, Nat.add(P0, R0)),
          +g => hg => ho => hm => N.le_trans(1n, P0, Nat.add(P0, R0),
            pcn.one(m, ps, fi, nx, g, p, L, Y, ho, lv.y(m, L, Y, g, mem.in.l(frc, cs, g, hg)), hm), N.le_add_r(P0, R0))),
        +g => ho => hn2 => hm => N.le_trans(1n, P0, Nat.add(P0, R0), pcn.one(m, ps, fi, nx, g, p, L, Y, ho, lv.fr(os, hl, fs, m, sp, cs, g, hn2), hm),
          N.le_add_r(P0, R0)))))

# The allocation's invariant (AL)
# -------------------------------
#
# The facts of HS and AccK that AL needs (GC), of the owned roots os, the
# temporaries xs, the frames fs from sp, the pend list ps and the zombies zs;
# the live roots and cells (GL, GY) and the garbage (GP) of them.

def GL(+m: Cr.Cir.Cells, +os: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +fs: List<&2, D.AF>, +sp: U32) -> List<&2, D.Rt>:
  Lst(os, D.Tmp.held(xs), fs, m, sp)

def GY(+m: Cr.Cir.Cells, +xs: List<&2, D.TmpE>, +fs: List<&2, D.AF>, +sp: U32) -> List<&2, U32>:
  Yc(fs, m, sp, D.Tmp.cells(xs))

def GP(+m: Cr.Cir.Cells, +nx: U32, +fi: U32, +os: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +fs: List<&2, D.AF>, +sp: U32) -> List<&2, U32>:
  Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, GL(m, os, xs, fs, sp), GY(m, xs, fs, sp))

# the cover's condition at a cell
def CovAt(+m: Cr.Cir.Cells, +c: U32, +rs: List<&2, D.Rt>, +xs: List<&2, U32>) -> Bool:
  Bool.or(D.Fl(m, c, 1024), Bool.or(D.Nodes(rs, m, c), D.Mem(xs, c)))

# every own cell is live, or one of the garbage cells
def cov.live(k: Nat, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +os: List<&2, D.Rt>, +xs: List<&2, D.TmpE>,
  +fs: List<&2, D.AF>, +sp: U32, +hfn: {U32.is_le(fi, nx) == True{} : Bool}, +c: U32,
  +h1: N.Le(U32.to_nat(fi), U32.to_nat(c)), +hw: N.Le(Nat.add(U32.to_nat(c), k), U32.to_nat(nx))) ->
  {D.Cov(k, m, c, GL(m, os, xs, fs, sp), List.append(&2, U32, GY(m, xs, fs, sp), GP(m, nx, fi, os, xs, fs, sp))) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+(+q):
      +h2 = w.lt(c, q, nx, hw)
      +ei = D.u.inc(c, nx, h2)
      +efn = D.add.sub(U32.to_nat(fi), U32.to_nat(nx), CK.U.le(fi, nx, hfn))
      +h2f = N.le_rw_r(1n+U32.to_nat(c), U32.to_nat(nx), Nat.add(U32.to_nat(fi), Nat.sub(U32.to_nat(nx), U32.to_nat(fi))),
        Equal.sym(Nat, Nat.add(U32.to_nat(fi), Nat.sub(U32.to_nat(nx), U32.to_nat(fi))), U32.to_nat(nx), efn), h2)
      +cv = bool.case(Lv(m, GL(m, os, xs, fs, sp), GY(m, xs, fs, sp), c), Lv(m, GL(m, os, xs, fs, sp), GY(m, xs, fs, sp), c),
        {CovAt(m, c, GL(m, os, xs, fs, sp), List.append(&2, U32, GY(m, xs, fs, sp), GP(m, nx, fi, os, xs, fs, sp))) == True{} : Bool}, {==},
        e => D.or.cases(Lv0(m, GL(m, os, xs, fs, sp), c), D.Mem(GY(m, xs, fs, sp), c),
          {CovAt(m, c, GL(m, os, xs, fs, sp), List.append(&2, U32, GY(m, xs, fs, sp), GP(m, nx, fi, os, xs, fs, sp))) == True{} : Bool}, e,
          e0 => D.or.cases(D.Fl(m, c, 1024), D.Nodes(GL(m, os, xs, fs, sp), m, c),
            {CovAt(m, c, GL(m, os, xs, fs, sp), List.append(&2, U32, GY(m, xs, fs, sp), GP(m, nx, fi, os, xs, fs, sp))) == True{} : Bool}, e0,
            est => D.or.l(D.Fl(m, c, 1024), Bool.or(D.Nodes(GL(m, os, xs, fs, sp), m, c), D.Mem(List.append(&2, U32, GY(m, xs, fs, sp), GP(m, nx, fi, os, xs, fs, sp)), c)), est),
            end => D.or.r(D.Fl(m, c, 1024), Bool.or(D.Nodes(GL(m, os, xs, fs, sp), m, c), D.Mem(List.append(&2, U32, GY(m, xs, fs, sp), GP(m, nx, fi, os, xs, fs, sp)), c)),
              D.or.l(D.Nodes(GL(m, os, xs, fs, sp), m, c), D.Mem(List.append(&2, U32, GY(m, xs, fs, sp), GP(m, nx, fi, os, xs, fs, sp)), c), end))),
          ey => D.or.r(D.Fl(m, c, 1024), Bool.or(D.Nodes(GL(m, os, xs, fs, sp), m, c), D.Mem(List.append(&2, U32, GY(m, xs, fs, sp), GP(m, nx, fi, os, xs, fs, sp)), c)),
            D.or.r(D.Nodes(GL(m, os, xs, fs, sp), m, c), D.Mem(List.append(&2, U32, GY(m, xs, fs, sp), GP(m, nx, fi, os, xs, fs, sp)), c),
              mem.in.l(GY(m, xs, fs, sp), GP(m, nx, fi, os, xs, fs, sp), c, ey)))),
        e => D.or.r(D.Fl(m, c, 1024), Bool.or(D.Nodes(GL(m, os, xs, fs, sp), m, c), D.Mem(List.append(&2, U32, GY(m, xs, fs, sp), GP(m, nx, fi, os, xs, fs, sp)), c)),
          D.or.r(D.Nodes(GL(m, os, xs, fs, sp), m, c), D.Mem(List.append(&2, U32, GY(m, xs, fs, sp), GP(m, nx, fi, os, xs, fs, sp)), c),
            mem.in.r(GY(m, xs, fs, sp), GP(m, nx, fi, os, xs, fs, sp), c,
              Equal.trans(Bool, D.Mem(GP(m, nx, fi, os, xs, fs, sp), c), S.Has(GP(m, nx, fi, os, xs, fs, sp), c), True{},
                mem.has(GP(m, nx, fi, os, xs, fs, sp), c),
                gb.has(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, GL(m, os, xs, fs, sp), GY(m, xs, fs, sp), c, e, h1, h2f))))))
      CK.Bo.and_i(CovAt(m, c, GL(m, os, xs, fs, sp), List.append(&2, U32, GY(m, xs, fs, sp), GP(m, nx, fi, os, xs, fs, sp))),
        D.Cov(q, m, U32.inc(c), GL(m, os, xs, fs, sp), List.append(&2, U32, GY(m, xs, fs, sp), GP(m, nx, fi, os, xs, fs, sp))), cv,
        cov.live(q, m, nx, fi, os, xs, fs, sp, hfn, U32.inc(c),
          N.le_trans(U32.to_nat(fi), U32.to_nat(c), U32.to_nat(U32.inc(c)), h1,
            N.le_rw_r(U32.to_nat(c), 1n+U32.to_nat(c), U32.to_nat(U32.inc(c)), Equal.sym(Nat, U32.to_nat(U32.inc(c)), 1n+U32.to_nat(c), ei),
              N.le_succ(U32.to_nat(c), U32.to_nat(c), N.le_refl(U32.to_nat(c))))),
          w.next(c, q, nx, hw)))

# AccK's roots: the owned ones, the temporaries' terms, the frames' terms, the zombies
def GRS(+m: Cr.Cir.Cells, +os: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +fs: List<&2, D.AF>, +sp: U32, +zs: List<&2, D.Rt>) -> List<&2, D.Rt>:
  List.append(&2, D.Rt, os, List.append(&2, D.Rt, D.Tmp.held(xs), List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)))

def GC(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +os: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +zs: List<&2, D.Rt>) -> Data:
  +n0 = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
  D.P2(D.Tbl(m, im, fi, nx),
  D.P2(D.RtsK(True{}, ds, m, im, fi, nx, ks, img, os),
  D.P2(D.RtsK(True{}, ds, m, im, fi, nx, ks, img, D.Tmp.held(xs)),
  D.P2(D.FrsK(True{}, ds, m, im, fi, nx, ks, img, ps, sp, fs),
  D.P2({D.Tmp.ok(xs, m, fi, nx, ps, GRS(m, os, xs, fs, sp, zs)) == True{} : Bool},
  D.P2(D.RtsK(True{}, ds, m, im, fi, nx, ks, img, zs),
  D.P2({D.Rt.cells(zs) == D.Pend.terms(ps, m) : List<&2, U32>},
  D.P2(D.PendOK(ps, ps, m, fi, nx, D.Rt.cells(os)),
  D.P2({D.Cnt(n0, m, fi, n0, fi, ps, D.Rt.cells(os)) == True{} : Bool},
  D.P2({D.Clo(n0, m, fi, ps, D.Tmp.cells(xs), D.Rt.cells(D.Tmp.held(xs))) == True{} : Bool},
    {U32.is_le(fi, nx) == True{} : Bool}))))))))))

# HS and AccK supply the facts that the copy's allocation invariant needs
def gc.of(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +xs: List<&2, D.TmpE>,
  +fs: List<&2, D.AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  hs: D.HS(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps),
  hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, os, xs, sp, fs, ps, zs)) ->
  GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs):
  (ho, hs1) = hs
  (_, hs2) = hs1
  (_, hs3) = hs2
  (hf, hs4) = hs3
  (hh, hi) = hs4
  (_, hh1) = hh
  (hp, hh2) = hh1
  (hc, hh3) = hh2
  (_, hh4) = hh3
  (_, hfn) = hh4
  (ht, _) = hi
  (hz, ha1) = hac
  (hhl, ha2) = ha1
  (hzc, ha3) = ha2
  (_, ha4) = ha3
  (hclo, htmp) = ha4
  (ht, (ho, (hhl, (hf, (htmp, (hz, (hzc, (hp, (hc, (hclo, hfn))))))))))

def gc.tbl(-ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -m: Cr.Cir.Cells, -nx: U32, -fi: U32, -im: U32,
  -os: List<&2, D.Rt>, -xs: List<&2, D.TmpE>, -fs: List<&2, D.AF>, -sp: U32, -ps: List<&2, U32>, -zs: List<&2, D.Rt>,
  g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs)) -> D.Tbl(m, im, fi, nx):
  (a, _) = g
  a

def gc.os(-ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -m: Cr.Cir.Cells, -nx: U32, -fi: U32, -im: U32,
  -os: List<&2, D.Rt>, -xs: List<&2, D.TmpE>, -fs: List<&2, D.AF>, -sp: U32, -ps: List<&2, U32>, -zs: List<&2, D.Rt>,
  g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs)) -> D.RtsK(True{}, ds, m, im, fi, nx, ks, img, os):
  (_, g1) = g
  (a, _) = g1
  a

def gc.hl(-ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -m: Cr.Cir.Cells, -nx: U32, -fi: U32, -im: U32,
  -os: List<&2, D.Rt>, -xs: List<&2, D.TmpE>, -fs: List<&2, D.AF>, -sp: U32, -ps: List<&2, U32>, -zs: List<&2, D.Rt>,
  g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs)) -> D.RtsK(True{}, ds, m, im, fi, nx, ks, img, D.Tmp.held(xs)):
  (_, g1) = g
  (_, g2) = g1
  (a, _) = g2
  a

def gc.frs(-ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -m: Cr.Cir.Cells, -nx: U32, -fi: U32, -im: U32,
  -os: List<&2, D.Rt>, -xs: List<&2, D.TmpE>, -fs: List<&2, D.AF>, -sp: U32, -ps: List<&2, U32>, -zs: List<&2, D.Rt>,
  g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs)) -> D.FrsK(True{}, ds, m, im, fi, nx, ks, img, ps, sp, fs):
  (_, g1) = g
  (_, g2) = g1
  (_, g3) = g2
  (a, _) = g3
  a

def gc.tmp(-ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -m: Cr.Cir.Cells, -nx: U32, -fi: U32, -im: U32,
  -os: List<&2, D.Rt>, -xs: List<&2, D.TmpE>, -fs: List<&2, D.AF>, -sp: U32, -ps: List<&2, U32>, -zs: List<&2, D.Rt>,
  g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs)) -> {D.Tmp.ok(xs, m, fi, nx, ps, GRS(m, os, xs, fs, sp, zs)) == True{} : Bool}:
  (_, g1) = g
  (_, g2) = g1
  (_, g3) = g2
  (_, g4) = g3
  (a, _) = g4
  a

def gc.zs(-ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -m: Cr.Cir.Cells, -nx: U32, -fi: U32, -im: U32,
  -os: List<&2, D.Rt>, -xs: List<&2, D.TmpE>, -fs: List<&2, D.AF>, -sp: U32, -ps: List<&2, U32>, -zs: List<&2, D.Rt>,
  g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs)) -> D.RtsK(True{}, ds, m, im, fi, nx, ks, img, zs):
  (_, g1) = g
  (_, g2) = g1
  (_, g3) = g2
  (_, g4) = g3
  (_, g5) = g4
  (a, _) = g5
  a

def gc.zc(-ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -m: Cr.Cir.Cells, -nx: U32, -fi: U32, -im: U32,
  -os: List<&2, D.Rt>, -xs: List<&2, D.TmpE>, -fs: List<&2, D.AF>, -sp: U32, -ps: List<&2, U32>, -zs: List<&2, D.Rt>,
  g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs)) -> {D.Rt.cells(zs) == D.Pend.terms(ps, m) : List<&2, U32>}:
  (_, g1) = g
  (_, g2) = g1
  (_, g3) = g2
  (_, g4) = g3
  (_, g5) = g4
  (_, g6) = g5
  (a, _) = g6
  a

def gc.pend(-ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -m: Cr.Cir.Cells, -nx: U32, -fi: U32, -im: U32,
  -os: List<&2, D.Rt>, -xs: List<&2, D.TmpE>, -fs: List<&2, D.AF>, -sp: U32, -ps: List<&2, U32>, -zs: List<&2, D.Rt>,
  g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs)) -> D.PendOK(ps, ps, m, fi, nx, D.Rt.cells(os)):
  (_, g1) = g
  (_, g2) = g1
  (_, g3) = g2
  (_, g4) = g3
  (_, g5) = g4
  (_, g6) = g5
  (_, g7) = g6
  (a, _) = g7
  a

def gc.cnt(-ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -m: Cr.Cir.Cells, -nx: U32, -fi: U32, -im: U32,
  -os: List<&2, D.Rt>, -xs: List<&2, D.TmpE>, -fs: List<&2, D.AF>, -sp: U32, -ps: List<&2, U32>, -zs: List<&2, D.Rt>,
  g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs)) ->
  {D.Cnt(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), fi, ps, D.Rt.cells(os)) == True{} : Bool}:
  (_, g1) = g
  (_, g2) = g1
  (_, g3) = g2
  (_, g4) = g3
  (_, g5) = g4
  (_, g6) = g5
  (_, g7) = g6
  (_, g8) = g7
  (a, _) = g8
  a

def gc.clo(-ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -m: Cr.Cir.Cells, -nx: U32, -fi: U32, -im: U32,
  -os: List<&2, D.Rt>, -xs: List<&2, D.TmpE>, -fs: List<&2, D.AF>, -sp: U32, -ps: List<&2, U32>, -zs: List<&2, D.Rt>,
  g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs)) ->
  {D.Clo(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, D.Tmp.cells(xs), D.Rt.cells(D.Tmp.held(xs))) == True{} : Bool}:
  (_, g1) = g
  (_, g2) = g1
  (_, g3) = g2
  (_, g4) = g3
  (_, g5) = g4
  (_, g6) = g5
  (_, g7) = g6
  (_, g8) = g7
  (_, g9) = g8
  (a, _) = g9
  a

def gc.fn(-ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -m: Cr.Cir.Cells, -nx: U32, -fi: U32, -im: U32,
  -os: List<&2, D.Rt>, -xs: List<&2, D.TmpE>, -fs: List<&2, D.AF>, -sp: U32, -ps: List<&2, U32>, -zs: List<&2, D.Rt>,
  g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs)) -> {U32.is_le(fi, nx) == True{} : Bool}:
  (_, g1) = g
  (_, g2) = g1
  (_, g3) = g2
  (_, g4) = g3
  (_, g5) = g4
  (_, g6) = g5
  (_, g7) = g6
  (_, g8) = g7
  (_, g9) = g8
  (_, a) = g9
  a

# Cnt at a cell p of the n cells from o
def CntAt(+m: Cr.Cir.Cells, +c: U32, +N0: Nat, +fi: U32, +ps: List<&2, U32>, +rs: List<&2, U32>) -> Bool:
  Bool.or(Bool.not(U32.is_lt(D.Tg(m, c), 19)), Bool.or(D.Fl(m, c, 1024), Bool.or(D.Mem(ps, c),
    Nat.is_eq(U32.to_nat(D.Fd(1n, m, c)), D.Ptr(N0, m, fi, ps, rs, c)))))

def cnt.get.b(b: Bool, +k: Nat, +m: Cr.Cir.Cells, +o: U32, +p: U32, +N0: Nat, +fi: U32, +ps: List<&2, U32>, +rs: List<&2, U32>,
  +eb: {U32.is_eq(o, p) == b : Bool}, +h1: N.Le(U32.to_nat(o), U32.to_nat(p)), h2: N.Le(1n+U32.to_nat(p), Nat.add(U32.to_nat(o), 1n+k)),
  hc: {D.Cnt(1n+k, m, o, N0, fi, ps, rs) == True{} : Bool},
  ih: N.Le(U32.to_nat(U32.inc(o)), U32.to_nat(p)) -> N.Le(1n+U32.to_nat(p), Nat.add(U32.to_nat(U32.inc(o)), k)) ->
    {D.Cnt(k, m, U32.inc(o), N0, fi, ps, rs) == True{} : Bool} -> {CntAt(m, p, N0, fi, ps, rs) == True{} : Bool}) ->
  {CntAt(m, p, N0, fi, ps, rs) == True{} : Bool}:
  match b:
    case True{}:
      %D.u32.eq(o, p, eb) : {CntAt(m, _, N0, fi, ps, rs) == True{} : Bool}
      D.and.l(CntAt(m, o, N0, fi, ps, rs), D.Cnt(k, m, U32.inc(o), N0, fi, ps, rs), hc)
    case False{}:
      ih(rng.lo(k, o, p, eb, h1), rng.hi(k, o, p, eb, h1, h2), D.and.r(CntAt(m, o, N0, fi, ps, rs), D.Cnt(k, m, U32.inc(o), N0, fi, ps, rs), hc))

def cnt.get(n: Nat, +m: Cr.Cir.Cells, +o: U32, +p: U32, +N0: Nat, +fi: U32, +ps: List<&2, U32>, +rs: List<&2, U32>,
  h1: N.Le(U32.to_nat(o), U32.to_nat(p)), h2: N.Le(1n+U32.to_nat(p), Nat.add(U32.to_nat(o), n)),
  hc: {D.Cnt(n, m, o, N0, fi, ps, rs) == True{} : Bool}) -> {CntAt(m, p, N0, fi, ps, rs) == True{} : Bool}:
  match n:
    case 0n:
      rng.none({CntAt(m, p, N0, fi, ps, rs) == True{} : Bool}, o, p, h1, h2)
    case 1n+(+k):
      cnt.get.b(U32.is_eq(o, p), k, m, o, p, N0, fi, ps, rs, {==}, h1, h2, hc, x => y => z => cnt.get(k, m, U32.inc(o), p, N0, fi, ps, rs, x, y, z))

# the facts of PendOK at a cell of the pend list
def PendC(+ps: List<&2, U32>, +m: Cr.Cir.Cells, +fi: U32, +nx: U32, +rs: List<&2, U32>, +q: U32) -> Data:
  D.P2({D.Own(fi, nx, q) == True{} : Bool},
  D.P2({D.Fl(m, q, 1024) == False{} : Bool},
  D.P2({Bool.or(U32.is_lt(D.Tg(m, q), 19), U32.is_le(32, D.Tg(m, q))) == True{} : Bool},
    {D.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, rs, q) == 0n : Nat})))

def pend.get(qs: List<&2, U32>, +ps: List<&2, U32>, +m: Cr.Cir.Cells, +fi: U32, +nx: U32, +rs: List<&2, U32>, +q: U32,
  h: D.PendOK(qs, ps, m, fi, nx, rs), hq: {D.Mem(qs, q) == True{} : Bool}) -> PendC(ps, m, fi, nx, rs, q):
  match qs:
    case Nil{}:
      CK.Bo.tf(PendC(ps, m, fi, nx, rs, q), hq)
    case Con{+x, +rest}:
      (ho, w1) = h
      (hs, w2) = w1
      (ht, w3) = w2
      (hp, hr) = w3
      D.or.cases(U32.is_eq(x, q), D.Mem(rest, q), PendC(ps, m, fi, nx, rs, q), hq,
        e => (%CK.U.eq(x, q, e) : PendC(ps, m, fi, nx, rs, _); (ho, (hs, (ht, hp)))),
        e => pend.get(rest, ps, m, fi, nx, rs, q, hr, e))

def pc.own(-ps: List<&2, U32>, -m: Cr.Cir.Cells, -fi: U32, -nx: U32, -rs: List<&2, U32>, -q: U32, b: PendC(ps, m, fi, nx, rs, q)) ->
  {D.Own(fi, nx, q) == True{} : Bool}:
  (a, _) = b
  a

def pc.nst(-ps: List<&2, U32>, -m: Cr.Cir.Cells, -fi: U32, -nx: U32, -rs: List<&2, U32>, -q: U32, b: PendC(ps, m, fi, nx, rs, q)) ->
  {D.Fl(m, q, 1024) == False{} : Bool}:
  (_, b1) = b
  (a, _) = b1
  a

def pc.tag(-ps: List<&2, U32>, -m: Cr.Cir.Cells, -fi: U32, -nx: U32, -rs: List<&2, U32>, -q: U32, b: PendC(ps, m, fi, nx, rs, q)) ->
  {Bool.or(U32.is_lt(D.Tg(m, q), 19), U32.is_le(32, D.Tg(m, q))) == True{} : Bool}:
  (_, b1) = b
  (_, b2) = b1
  (a, _) = b2
  a

def pc.ptr(-ps: List<&2, U32>, -m: Cr.Cir.Cells, -fi: U32, -nx: U32, -rs: List<&2, U32>, -q: U32, b: PendC(ps, m, fi, nx, rs, q)) ->
  {D.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, rs, q) == 0n : Nat}:
  (_, b1) = b
  (_, b2) = b1
  (_, a) = b2
  a

# a weaker bound on the size of the term a cell stands for
def ex.weak(-dk: Bool, -ds: List<&2, Bk.Def>, -m: Cr.Cir.Cells, -im: U32, -fi: U32, -nx: U32, -ks: List<&2, List<&2, Word(8n)>>,
  -img: List<&2, Bk.Term>, -c: U32, +a: Nat, +b: Nat,
  r: D.Ex(Bk.Term, v => D.P2(D.IsK(dk, ds, m, im, fi, nx, ks, img, c, v), N.Le(Pg.Term.size(v), a))), +le: N.Le(a, b)) ->
  D.Ex(Bk.Term, v => D.P2(D.IsK(dk, ds, m, im, fi, nx, ks, img, c, v), N.Le(Pg.Term.size(v), b))):
  (+v, rr) = r
  (hv, hl) = rr
  (v, (hv, N.le_trans(Pg.Term.size(v), a, b, hl, le)))

# a node of a term of zs stands for a term no larger than zs's
def nodes.sub(zs: List<&2, D.Rt>, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, hz: D.RtsK(True{}, ds, m, im, fi, nx, ks, img, zs),
  h: {D.Nodes(zs, m, c) == True{} : Bool}) ->
  D.Ex(Bk.Term, v => D.P2(D.IsK(True{}, ds, m, im, fi, nx, ks, img, c, v), N.Le(Pg.Term.size(v), D.Rts.size(zs)))):
  match zs:
    case Nil{}:
      CK.Bo.tf(D.Ex(Bk.Term, v => D.P2(D.IsK(True{}, ds, m, im, fi, nx, ks, img, c, v), N.Le(Pg.Term.size(v), 0n))), h)
    case Con{D.Rt{+r, +u}, +rest}:
      (hu, hrest) = hz
      D.or.cases(D.Node(u, m, r, c), D.Nodes(rest, m, c),
        D.Ex(Bk.Term, v => D.P2(D.IsK(True{}, ds, m, im, fi, nx, ks, img, c, v), N.Le(Pg.Term.size(v), Nat.add(Pg.Term.size(u), D.Rts.size(rest))))), h,
        e => ex.weak(True{}, ds, m, im, fi, nx, ks, img, c, Pg.Term.size(u), Nat.add(Pg.Term.size(u), D.Rts.size(rest)),
          node.sub(u, True{}, ds, m, im, fi, nx, ks, img, r, c, hu, e), N.le_add_r(Pg.Term.size(u), D.Rts.size(rest))),
        e => ex.weak(True{}, ds, m, im, fi, nx, ks, img, c, D.Rts.size(rest), Nat.add(Pg.Term.size(u), D.Rts.size(rest)),
          nodes.sub(rest, ds, m, im, fi, nx, ks, img, c, hrest, e), N.le_add_l(Pg.Term.size(u), D.Rts.size(rest))))

# a term cell of the pend list is among Pend.terms, and those are in the pend list
def pt.sub.b(b: Bool, +p: U32, +rest: List<&2, U32>, +m: Cr.Cir.Cells, +c: U32,
  h: {D.Mem(Bool.pick(List<&2, U32>, b, Con{p, D.Pend.terms(rest, m)}, D.Pend.terms(rest, m)), c) == True{} : Bool},
  ih: {D.Mem(D.Pend.terms(rest, m), c) == True{} : Bool} -> {D.Mem(rest, c) == True{} : Bool}) ->
  {Bool.or(U32.is_eq(p, c), D.Mem(rest, c)) == True{} : Bool}:
  match b:
    case True{}:
      D.or.cases(U32.is_eq(p, c), D.Mem(D.Pend.terms(rest, m), c), {Bool.or(U32.is_eq(p, c), D.Mem(rest, c)) == True{} : Bool}, h,
        e => CK.Bo.or_il(U32.is_eq(p, c), D.Mem(rest, c), e),
        e => CK.Bo.or_ir(U32.is_eq(p, c), D.Mem(rest, c), ih(e)))
    case False{}:
      CK.Bo.or_ir(U32.is_eq(p, c), D.Mem(rest, c), ih(h))

def pt.sub(ps: List<&2, U32>, +m: Cr.Cir.Cells, +c: U32, h: {D.Mem(D.Pend.terms(ps, m), c) == True{} : Bool}) -> {D.Mem(ps, c) == True{} : Bool}:
  match ps:
    case Nil{}:
      CK.Bo.tf({D.Mem(Nil{}, c) == True{} : Bool}, h)
    case Con{+p, +rest}:
      pt.sub.b(U32.is_lt(D.Tg(m, p), 19), p, rest, m, c, h, hh => pt.sub(rest, m, c, hh))

def pend.term.b(b: Bool, +p: U32, +rest: List<&2, U32>, +m: Cr.Cir.Cells, +c: U32, eb: {U32.is_lt(D.Tg(m, p), 19) == b : Bool},
  +hc19: {U32.is_lt(D.Tg(m, c), 19) == True{} : Bool}, h: {Bool.or(U32.is_eq(p, c), D.Mem(rest, c)) == True{} : Bool},
  ih: {D.Mem(rest, c) == True{} : Bool} -> {D.Mem(D.Pend.terms(rest, m), c) == True{} : Bool}) ->
  {D.Mem(Bool.pick(List<&2, U32>, b, Con{p, D.Pend.terms(rest, m)}, D.Pend.terms(rest, m)), c) == True{} : Bool}:
  match b:
    case True{}:
      D.or.cases(U32.is_eq(p, c), D.Mem(rest, c), {Bool.or(U32.is_eq(p, c), D.Mem(D.Pend.terms(rest, m), c)) == True{} : Bool}, h,
        e => CK.Bo.or_il(U32.is_eq(p, c), D.Mem(D.Pend.terms(rest, m), c), e),
        e => CK.Bo.or_ir(U32.is_eq(p, c), D.Mem(D.Pend.terms(rest, m), c), ih(e)))
    case False{}:
      D.or.cases(U32.is_eq(p, c), D.Mem(rest, c), {D.Mem(D.Pend.terms(rest, m), c) == True{} : Bool}, h,
        e => CK.Bo.tf({D.Mem(D.Pend.terms(rest, m), c) == True{} : Bool}, Equal.trans(Bool, False{}, U32.is_lt(D.Tg(m, p), 19), True{},
          Equal.sym(Bool, U32.is_lt(D.Tg(m, p), 19), False{}, eb), (%Equal.sym(U32, p, c, CK.U.eq(p, c, e)) : {U32.is_lt(D.Tg(m, _), 19) == True{} : Bool}; hc19))),
        e => ih(e))

def pend.term(ps: List<&2, U32>, +m: Cr.Cir.Cells, +c: U32, h: {D.Mem(ps, c) == True{} : Bool}, +hc19: {U32.is_lt(D.Tg(m, c), 19) == True{} : Bool}) ->
  {D.Mem(D.Pend.terms(ps, m), c) == True{} : Bool}:
  match ps:
    case Nil{}:
      CK.Bo.tf({D.Mem(D.Pend.terms(Nil{}, m), c) == True{} : Bool}, h)
    case Con{+p, +rest}:
      pend.term.b(U32.is_lt(D.Tg(m, p), 19), p, rest, m, c, {==}, hc19, h, hh => pend.term(rest, m, c, hh, hc19))

# a frame is not in the pend list, is one of the machine's own, of a tag of 32 or more
def fr.nps(fs: List<&2, D.AF>, +dk: Bool, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +fr: U32, +q: U32,
  h: D.FrsK(dk, ds, m, im, fi, nx, ks, img, ps, fr, fs), hq: {D.Mem(D.Fr.cells(fs, m, fr), q) == True{} : Bool}) ->
  D.P2({D.Mem(ps, q) == False{} : Bool}, D.P2({D.Own(fi, nx, q) == True{} : Bool}, {U32.is_le(32, D.Tg(m, q)) == True{} : Bool})):
  match fs:
    case Nil{}:
      CK.Bo.tf(D.P2({D.Mem(ps, q) == False{} : Bool}, D.P2({D.Own(fi, nx, q) == True{} : Bool}, {U32.is_le(32, D.Tg(m, q)) == True{} : Bool})), hq)
    case Con{D.AF{+kind, +qq, +k, +a, +b}, +rest}:
      (h0, w1) = h
      (h1, w2) = w1
      (hown, w3) = w2
      (hst, w4) = w3
      (hps, w5) = w4
      (htg, w6) = w5
      (hq2, w7) = w6
      (hk, w8) = w7
      (ia, w9) = w8
      (ib, hr) = w9
      D.or.cases(U32.is_eq(fr, q), D.Mem(D.Fr.cells(rest, m, D.Fd(1n, m, fr)), q),
        D.P2({D.Mem(ps, q) == False{} : Bool}, D.P2({D.Own(fi, nx, q) == True{} : Bool}, {U32.is_le(32, D.Tg(m, q)) == True{} : Bool})), hq,
        e => (%CK.U.eq(fr, q, e) : D.P2({D.Mem(ps, _) == False{} : Bool}, D.P2({D.Own(fi, nx, _) == True{} : Bool}, {U32.is_le(32, D.Tg(m, _)) == True{} : Bool}));
          (hps, (hown, (%Equal.sym(U32, D.Tg(m, fr), D.FK.tag(kind), htg) : {U32.is_le(32, _) == True{} : Bool}; D.fk.ge(kind))))),
        e => fr.nps(rest, dk, ds, m, im, fi, nx, ks, img, ps, D.Fd(1n, m, fr), q, hr, e))

def frn.nps(-ps: List<&2, U32>, -fi: U32, -nx: U32, -m: Cr.Cir.Cells, -q: U32,
  h: D.P2({D.Mem(ps, q) == False{} : Bool}, D.P2({D.Own(fi, nx, q) == True{} : Bool}, {U32.is_le(32, D.Tg(m, q)) == True{} : Bool}))) ->
  {D.Mem(ps, q) == False{} : Bool}:
  (a, _) = h
  a

def frn.own(-ps: List<&2, U32>, -fi: U32, -nx: U32, -m: Cr.Cir.Cells, -q: U32,
  h: D.P2({D.Mem(ps, q) == False{} : Bool}, D.P2({D.Own(fi, nx, q) == True{} : Bool}, {U32.is_le(32, D.Tg(m, q)) == True{} : Bool}))) ->
  {D.Own(fi, nx, q) == True{} : Bool}:
  (_, h1) = h
  (a, _) = h1
  a

def frn.tag(-ps: List<&2, U32>, -fi: U32, -nx: U32, -m: Cr.Cir.Cells, -q: U32,
  h: D.P2({D.Mem(ps, q) == False{} : Bool}, D.P2({D.Own(fi, nx, q) == True{} : Bool}, {U32.is_le(32, D.Tg(m, q)) == True{} : Bool}))) ->
  {U32.is_le(32, D.Tg(m, q)) == True{} : Bool}:
  (_, h1) = h
  (_, a) = h1
  a

# a temporary is one of the machine's own, out of the pend list, and no node of the roots rs
def TmpC(+m: Cr.Cir.Cells, +fi: U32, +nx: U32, +ps: List<&2, U32>, +rs: List<&2, D.Rt>, +q: U32) -> Data:
  D.P2({D.Own(fi, nx, q) == True{} : Bool}, D.P2({D.Mem(ps, q) == False{} : Bool}, {D.Nodes(rs, m, q) == False{} : Bool}))

def tmp.get(xs: List<&2, D.TmpE>, +m: Cr.Cir.Cells, +fi: U32, +nx: U32, +ps: List<&2, U32>, +rs: List<&2, D.Rt>, +q: U32,
  hok: {D.Tmp.ok(xs, m, fi, nx, ps, rs) == True{} : Bool}, hq: {D.Mem(D.Tmp.cells(xs), q) == True{} : Bool}) -> TmpC(m, fi, nx, ps, rs, q):
  match xs:
    case Nil{}:
      CK.Bo.tf(TmpC(m, fi, nx, ps, rs, q), hq)
    case Con{D.TmpE{+c, +h}, +rest}:
      +A0 = D.Own(fi, nx, c)
      +A1 = Bool.not(D.Fl(m, c, 1024))
      +A2 = Bool.not(D.Mem(ps, c))
      +A3 = Bool.not(D.Mem(D.Tmp.cells(rest), c))
      +A4 = Bool.not(D.Nodes(rs, m, c))
      +A5 = D.AllIn(D.Rt.cells(h), D.Fs(m, ps, c))
      +A6 = D.Tmp.ok(rest, m, fi, nx, ps, rs)
      +ok = hok
      +r1 = CK.Bo.and_r(A0, Bool.and(A1, Bool.and(A2, Bool.and(A3, Bool.and(A4, Bool.and(A5, A6))))), ok)
      +r2 = CK.Bo.and_r(A1, Bool.and(A2, Bool.and(A3, Bool.and(A4, Bool.and(A5, A6)))), r1)
      +r3 = CK.Bo.and_r(A2, Bool.and(A3, Bool.and(A4, Bool.and(A5, A6))), r2)
      +r4 = CK.Bo.and_r(A3, Bool.and(A4, Bool.and(A5, A6)), r3)
      +r5 = CK.Bo.and_r(A4, Bool.and(A5, A6), r4)
      D.or.cases(U32.is_eq(c, q), D.Mem(D.Tmp.cells(rest), q), TmpC(m, fi, nx, ps, rs, q), hq,
        e => (%CK.U.eq(c, q, e) : TmpC(m, fi, nx, ps, rs, _);
          (CK.Bo.and_l(A0, Bool.and(A1, Bool.and(A2, Bool.and(A3, Bool.and(A4, Bool.and(A5, A6))))), ok),
           (CK.Bo.not_t(D.Mem(ps, c), CK.Bo.and_l(A2, Bool.and(A3, Bool.and(A4, Bool.and(A5, A6))), r2)),
            CK.Bo.not_t(D.Nodes(rs, m, c), CK.Bo.and_l(A4, Bool.and(A5, A6), r4))))),
        e => tmp.get(rest, m, fi, nx, ps, rs, q, CK.Bo.and_r(A5, A6, r5), e))

def tc.own(-m: Cr.Cir.Cells, -fi: U32, -nx: U32, -ps: List<&2, U32>, -rs: List<&2, D.Rt>, -q: U32, h: TmpC(m, fi, nx, ps, rs, q)) ->
  {D.Own(fi, nx, q) == True{} : Bool}:
  (a, _) = h
  a

def tc.nps(-m: Cr.Cir.Cells, -fi: U32, -nx: U32, -ps: List<&2, U32>, -rs: List<&2, D.Rt>, -q: U32, h: TmpC(m, fi, nx, ps, rs, q)) ->
  {D.Mem(ps, q) == False{} : Bool}:
  (_, h1) = h
  (a, _) = h1
  a

def tc.nnd(-m: Cr.Cir.Cells, -fi: U32, -nx: U32, -ps: List<&2, U32>, -rs: List<&2, D.Rt>, -q: U32, h: TmpC(m, fi, nx, ps, rs, q)) ->
  {D.Nodes(rs, m, q) == False{} : Bool}:
  (_, h1) = h
  (_, a) = h1
  a

# what NdK says of a node: one of the machine's own, or STATIC
def nk.own2(-dk: Bool, -ds: List<&2, Bk.Def>, -im: U32, -fi: U32, -nx: U32, -c: U32, -x: Cr.Cir.Cell, -t: Bk.Term, -tag: U32,
  h: D.NdK(dk, ds, im, fi, nx, c, x, t, tag)) -> {Bool.or(D.Own(fi, nx, c), D.FlW(Cr.Cir.Cell.get(0n, x), 1024)) == True{} : Bool}:
  (e0, r0) = h
  (e1, r1) = r0
  e1

# a cell that stands for a term is a cell, one of the machine's own or STATIC
def isk.cell(v: Bk.Term, -dk: Bool, -ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, -im: U32, -fi: U32, -nx: U32,
  -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, +c: U32, h: D.IsK(dk, ds, m, im, fi, nx, ks, img, c, v)) ->
  {Cr.Cir.is_cell(c, im, fi, nx) == True{} : Bool}:
  match v:
    case Bk.Term.Var{+i}:
      (+nd, w0) = h
      nk.cell(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Var{i}, 0, nd)
    case Bk.Term.Ref{+k}:
      (+nd, w0) = h
      nk.cell(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Ref{k}, 1, nd)
    case Bk.Term.Ann{+y, +z}:
      (+nd, w0) = h
      nk.cell(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Ann{y, z}, 2, nd)
    case Bk.Term.Let{+q, +y, +z}:
      (+nd, w0) = h
      nk.cell(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Let{q, y, z}, 3, nd)
    case Bk.Term.Typ{+y}:
      (+nd, w0) = h
      nk.cell(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Typ{y}, 4, nd)
    case Bk.Term.Min{+y, +z}:
      (+nd, w0) = h
      nk.cell(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Min{y, z}, 5, nd)
    case Bk.Term.All{+q, +y, +z}:
      (+nd, w0) = h
      nk.cell(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.All{q, y, z}, 6, nd)
    case Bk.Term.Lam{+q, +y}:
      (+nd, w0) = h
      nk.cell(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Lam{q, y}, 7, nd)
    case Bk.Term.App{+q, +y, +z}:
      (+nd, w0) = h
      nk.cell(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.App{q, y, z}, 8, nd)
    case Bk.Term.Sig{+q, +y, +z}:
      (+nd, w0) = h
      nk.cell(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Sig{q, y, z}, 9, nd)
    case Bk.Term.Tup{+q, +y, +z}:
      (+nd, w0) = h
      nk.cell(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Tup{q, y, z}, 10, nd)
    case Bk.Term.Prj{+y}:
      (+nd, w0) = h
      nk.cell(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Prj{y}, 11, nd)
    case Bk.Term.Enu{+e}:
      (+nd, w0) = h
      nk.cell(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Enu{e}, 12, nd)
    case Bk.Term.Lab{+k}:
      (+nd, w0) = h
      nk.cell(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Lab{k}, 13, nd)
    case Bk.Term.Mat{+k, +y, +z}:
      (+nd, w0) = h
      nk.cell(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Mat{k, y, z}, 14, nd)
    case Bk.Term.Efq{}:
      nk.cell(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Efq{}, 15, h)
    case Bk.Term.Eql{+y, +z, +w}:
      (+nd, w0) = h
      nk.cell(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Eql{y, z, w}, 16, nd)
    case Bk.Term.Rfl{}:
      nk.cell(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Rfl{}, 17, h)
    case Bk.Term.Rwt{+y, +z, +w}:
      (+nd, w0) = h
      nk.cell(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Rwt{y, z, w}, 18, nd)

def isk.own(v: Bk.Term, -dk: Bool, -ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, -im: U32, -fi: U32, -nx: U32,
  -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, +c: U32, h: D.IsK(dk, ds, m, im, fi, nx, ks, img, c, v)) ->
  {Bool.or(D.Own(fi, nx, c), D.FlW(Cr.Cir.Cell.get(0n, Cr.Cir.Cells.get(m, c)), 1024)) == True{} : Bool}:
  match v:
    case Bk.Term.Var{+i}:
      (+nd, w0) = h
      nk.own2(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Var{i}, 0, nd)
    case Bk.Term.Ref{+k}:
      (+nd, w0) = h
      nk.own2(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Ref{k}, 1, nd)
    case Bk.Term.Ann{+y, +z}:
      (+nd, w0) = h
      nk.own2(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Ann{y, z}, 2, nd)
    case Bk.Term.Let{+q, +y, +z}:
      (+nd, w0) = h
      nk.own2(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Let{q, y, z}, 3, nd)
    case Bk.Term.Typ{+y}:
      (+nd, w0) = h
      nk.own2(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Typ{y}, 4, nd)
    case Bk.Term.Min{+y, +z}:
      (+nd, w0) = h
      nk.own2(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Min{y, z}, 5, nd)
    case Bk.Term.All{+q, +y, +z}:
      (+nd, w0) = h
      nk.own2(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.All{q, y, z}, 6, nd)
    case Bk.Term.Lam{+q, +y}:
      (+nd, w0) = h
      nk.own2(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Lam{q, y}, 7, nd)
    case Bk.Term.App{+q, +y, +z}:
      (+nd, w0) = h
      nk.own2(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.App{q, y, z}, 8, nd)
    case Bk.Term.Sig{+q, +y, +z}:
      (+nd, w0) = h
      nk.own2(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Sig{q, y, z}, 9, nd)
    case Bk.Term.Tup{+q, +y, +z}:
      (+nd, w0) = h
      nk.own2(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Tup{q, y, z}, 10, nd)
    case Bk.Term.Prj{+y}:
      (+nd, w0) = h
      nk.own2(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Prj{y}, 11, nd)
    case Bk.Term.Enu{+e}:
      (+nd, w0) = h
      nk.own2(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Enu{e}, 12, nd)
    case Bk.Term.Lab{+k}:
      (+nd, w0) = h
      nk.own2(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Lab{k}, 13, nd)
    case Bk.Term.Mat{+k, +y, +z}:
      (+nd, w0) = h
      nk.own2(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Mat{k, y, z}, 14, nd)
    case Bk.Term.Efq{}:
      nk.own2(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Efq{}, 15, h)
    case Bk.Term.Eql{+y, +z, +w}:
      (+nd, w0) = h
      nk.own2(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Eql{y, z, w}, 16, nd)
    case Bk.Term.Rfl{}:
      nk.own2(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Rfl{}, 17, h)
    case Bk.Term.Rwt{+y, +z, +w}:
      (+nd, w0) = h
      nk.own2(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Rwt{y, z, w}, 18, nd)


# the live roots' terms stand for their terms
def gc.L(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +os: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  +g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs)) -> D.RtsK(True{}, ds, m, im, fi, nx, ks, img, Lst(os, D.Tmp.held(xs), fs, m, sp)):
  AC.rtsk.app(True{}, os, List.append(&2, D.Rt, D.Tmp.held(xs), D.Fr.rts(fs, m, sp)), ds, m, im, fi, nx, ks, img, gc.os(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g),
    AC.rtsk.app(True{}, D.Tmp.held(xs), D.Fr.rts(fs, m, sp), ds, m, im, fi, nx, ks, img, gc.hl(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g),
      AC.frs.rtsk(True{}, ds, m, im, fi, nx, ks, img, ps, fs, sp, gc.frs(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g))))

# the live cells' pointers and the owned roots are among the pointers (Ptr)
def ptr.ge(+m: Cr.Cir.Cells, +nx: U32, +fi: U32, +ps: List<&2, U32>, +rs: List<&2, U32>, +q: U32, +L: List<&2, D.Rt>, +Y: List<&2, U32>) ->
  N.Le(Nat.add(PcN(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, ps, fi, q, L, Y), D.RcL(rs, q)), D.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, rs, q)):
  +A = PcG(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, L, Y), m, ps, q)
  +B = PcN(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, ps, fi, q, L, Y)
  N.add_mono(B, D.Pc(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, ps, fi, q), D.RcL(rs, q), D.RcL(rs, q),
    N.le_rw_r(B, Nat.add(A, B), D.Pc(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, ps, fi, q), Equal.sym(Nat, D.Pc(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, ps, fi, q), Nat.add(A, B), pc.split(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, ps, fi, q, L, Y)),
      N.le_add_l(A, B)),
    N.le_refl(D.RcL(rs, q)))

# a cell of the pend list is garbage: not STATIC, no node of a live term (it
# has no pointer, and a live node has one, or is a root), no frame nor temporary
def pend.lv(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +os: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  +g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs), +q: U32, +hq: {D.Mem(ps, q) == True{} : Bool}) -> {Lv(m, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs)), q) == False{} : Bool}:
  +pc = pend.get(ps, ps, m, fi, nx, D.Rt.cells(os), q, gc.pend(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g), hq)
  +nst = pc.nst(ps, m, fi, nx, D.Rt.cells(os), q, pc)
  +nnd = bool.case(D.Nodes(Lst(os, D.Tmp.held(xs), fs, m, sp), m, q), D.Nodes(Lst(os, D.Tmp.held(xs), fs, m, sp), m, q), {D.Nodes(Lst(os, D.Tmp.held(xs), fs, m, sp), m, q) == False{} : Bool}, {==},
    e => Empty.absurd({D.Nodes(Lst(os, D.Tmp.held(xs), fs, m, sp), m, q) == False{} : Bool},
      N.le_rw_r(1n, D.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, D.Rt.cells(os), q), 0n, pc.ptr(ps, m, fi, nx, D.Rt.cells(os), q, pc),
        N.le_trans(1n, Nat.add(PcN(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, ps, fi, q, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.RcL(D.Rt.cells(os), q)), D.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, D.Rt.cells(os), q),
          live.ptr(True{}, ds, m, im, fi, nx, ks, img, ps, gc.tbl(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g), os, xs, fs, sp, GRS(m, os, xs, fs, sp, zs), q,
            gc.os(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g), gc.hl(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g), gc.frs(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g), gc.tmp(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g), e, nst),
          ptr.ge(m, nx, fi, ps, D.Rt.cells(os), q, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs)))))),
    e => e)
  +nfr = bool.case(D.Mem(D.Fr.cells(fs, m, sp), q), D.Mem(D.Fr.cells(fs, m, sp), q), {D.Mem(D.Fr.cells(fs, m, sp), q) == False{} : Bool}, {==},
    e => CK.Bo.tf({D.Mem(D.Fr.cells(fs, m, sp), q) == False{} : Bool}, Equal.trans(Bool, False{}, D.Mem(ps, q), True{},
      Equal.sym(Bool, D.Mem(ps, q), False{}, frn.nps(ps, fi, nx, m, q, fr.nps(fs, True{}, ds, m, im, fi, nx, ks, img, ps, sp, q, gc.frs(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g), e))), hq)),
    e => e)
  +ntm = bool.case(D.Mem(D.Tmp.cells(xs), q), D.Mem(D.Tmp.cells(xs), q), {D.Mem(D.Tmp.cells(xs), q) == False{} : Bool}, {==},
    e => CK.Bo.tf({D.Mem(D.Tmp.cells(xs), q) == False{} : Bool}, Equal.trans(Bool, False{}, D.Mem(ps, q), True{},
      Equal.sym(Bool, D.Mem(ps, q), False{}, tc.nps(m, fi, nx, ps, GRS(m, os, xs, fs, sp, zs), q,
        tmp.get(xs, m, fi, nx, ps, GRS(m, os, xs, fs, sp, zs), q, gc.tmp(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g), e))), hq)),
    e => e)
  or.ff(Lv0(m, Lst(os, D.Tmp.held(xs), fs, m, sp), q), D.Mem(Yc(fs, m, sp, D.Tmp.cells(xs)), q), or.ff(D.Fl(m, q, 1024), D.Nodes(Lst(os, D.Tmp.held(xs), fs, m, sp), m, q), nst, nnd),
    (%Equal.sym(Bool, D.Mem(Yc(fs, m, sp, D.Tmp.cells(xs)), q), Bool.or(D.Mem(D.Fr.cells(fs, m, sp), q), D.Mem(D.Tmp.cells(xs), q)), AC.mem.app(D.Fr.cells(fs, m, sp), D.Tmp.cells(xs), q)) :
      {_ == False{} : Bool}; or.ff(D.Mem(D.Fr.cells(fs, m, sp), q), D.Mem(D.Tmp.cells(xs), q), nfr, ntm)))

# the pend list is part of the garbage
def sub.qp(qs: List<&2, U32>, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +os: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  +g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs), +hin: {D.AllIn(qs, ps) == True{} : Bool}) -> {S.Sub(qs, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs)))) == True{} : Bool}:
  match qs:
    case Nil{}:
      {==}
    case Con{+q, +rest}:
      +hq = D.and.l(D.Mem(ps, q), D.AllIn(rest, ps), hin)
      +own = pc.own(ps, m, fi, nx, D.Rt.cells(os), q, pend.get(ps, ps, m, fi, nx, D.Rt.cells(os), q, gc.pend(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g), hq))
      CK.Bo.and_i(S.Has(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), q), S.Sub(rest, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs)))),
        gb.has(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs)), q, pend.lv(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, q, hq), own.lo(fi, nx, q, own), own.hi(fi, nx, q, own)),
        sub.qp(rest, ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, D.and.r(D.Mem(ps, q), D.AllIn(rest, ps), hin)))

# a garbage cell that the cover covers is a node of a zombie's term or pending
def bool.cls(F: Bool, No: Bool, Nh: Bool, Nf: Bool, +Nz: Bool, Mf: Bool, Mc: Bool, +Mp: Bool,
  h: {Bool.or(F, Bool.or(Bool.or(No, Bool.or(Nh, Bool.or(Nf, Nz))), Bool.or(Mf, Bool.or(Mc, Mp)))) == True{} : Bool},
  hl: {Bool.or(Bool.or(F, Bool.or(No, Bool.or(Nh, Nf))), Bool.or(Mf, Mc)) == False{} : Bool}) -> {Bool.or(Nz, Mp) == True{} : Bool}:
  match F:
    case True{}:
      CK.Bo.ft({Bool.or(Nz, Mp) == True{} : Bool}, hl)
    case False{}:
      match No:
        case True{}:
          CK.Bo.ft({Bool.or(Nz, Mp) == True{} : Bool}, hl)
        case False{}:
          match Nh:
            case True{}:
              CK.Bo.ft({Bool.or(Nz, Mp) == True{} : Bool}, hl)
            case False{}:
              match Nf:
                case True{}:
                  CK.Bo.ft({Bool.or(Nz, Mp) == True{} : Bool}, hl)
                case False{}:
                  match Mf:
                    case True{}:
                      CK.Bo.ft({Bool.or(Nz, Mp) == True{} : Bool}, hl)
                    case False{}:
                      match Mc:
                        case True{}:
                          CK.Bo.ft({Bool.or(Nz, Mp) == True{} : Bool}, hl)
                        case False{}:
                          h

def gb.cls(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +os: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  +g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs), +c: U32,
  hcv: {Bool.or(D.Fl(m, c, 1024), Bool.or(D.Nodes(GRS(m, os, xs, fs, sp, zs), m, c), D.Mem(List.append(&2, U32, D.Fr.cells(fs, m, sp), List.append(&2, U32, D.Tmp.cells(xs), ps)), c))) == True{} : Bool},
  hlv: {Lv(m, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs)), c) == False{} : Bool}) -> {Bool.or(D.Nodes(zs, m, c), D.Mem(ps, c)) == True{} : Bool}:
  +No = D.Nodes(os, m, c)
  +Nh = D.Nodes(D.Tmp.held(xs), m, c)
  +Nf = D.Nodes(D.Fr.rts(fs, m, sp), m, c)
  +Nz = D.Nodes(zs, m, c)
  +Mf = D.Mem(D.Fr.cells(fs, m, sp), c)
  +Mc = D.Mem(D.Tmp.cells(xs), c)
  +Mp = D.Mem(ps, c)
  +eN = Equal.trans(Bool, D.Nodes(GRS(m, os, xs, fs, sp, zs), m, c),
    Bool.or(No, D.Nodes(List.append(&2, D.Rt, D.Tmp.held(xs), List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)), m, c)), Bool.or(No, Bool.or(Nh, Bool.or(Nf, Nz))),
    AC.nodes.app(os, List.append(&2, D.Rt, D.Tmp.held(xs), List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)), m, c),
    Equal.cong(Bool, Bool, w => Bool.or(No, w), D.Nodes(List.append(&2, D.Rt, D.Tmp.held(xs), List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)), m, c),
      Bool.or(Nh, Bool.or(Nf, Nz)),
      Equal.trans(Bool, D.Nodes(List.append(&2, D.Rt, D.Tmp.held(xs), List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)), m, c),
        Bool.or(Nh, D.Nodes(List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs), m, c)), Bool.or(Nh, Bool.or(Nf, Nz)),
        AC.nodes.app(D.Tmp.held(xs), List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs), m, c),
        Equal.cong(Bool, Bool, w => Bool.or(Nh, w), D.Nodes(List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs), m, c), Bool.or(Nf, Nz),
          AC.nodes.app(D.Fr.rts(fs, m, sp), zs, m, c)))))
  +eM = Equal.trans(Bool, D.Mem(List.append(&2, U32, D.Fr.cells(fs, m, sp), List.append(&2, U32, D.Tmp.cells(xs), ps)), c), Bool.or(Mf, D.Mem(List.append(&2, U32, D.Tmp.cells(xs), ps), c)), Bool.or(Mf, Bool.or(Mc, Mp)),
    AC.mem.app(D.Fr.cells(fs, m, sp), List.append(&2, U32, D.Tmp.cells(xs), ps), c),
    Equal.cong(Bool, Bool, w => Bool.or(Mf, w), D.Mem(List.append(&2, U32, D.Tmp.cells(xs), ps), c), Bool.or(Mc, Mp), AC.mem.app(D.Tmp.cells(xs), ps, c)))
  +eNL = Equal.trans(Bool, D.Nodes(Lst(os, D.Tmp.held(xs), fs, m, sp), m, c), Bool.or(No, D.Nodes(List.append(&2, D.Rt, D.Tmp.held(xs), D.Fr.rts(fs, m, sp)), m, c)), Bool.or(No, Bool.or(Nh, Nf)),
    AC.nodes.app(os, List.append(&2, D.Rt, D.Tmp.held(xs), D.Fr.rts(fs, m, sp)), m, c),
    Equal.cong(Bool, Bool, w => Bool.or(No, w), D.Nodes(List.append(&2, D.Rt, D.Tmp.held(xs), D.Fr.rts(fs, m, sp)), m, c), Bool.or(Nh, Nf),
      AC.nodes.app(D.Tmp.held(xs), D.Fr.rts(fs, m, sp), m, c)))
  +eMY = AC.mem.app(D.Fr.cells(fs, m, sp), D.Tmp.cells(xs), c)
  bool.cls(D.Fl(m, c, 1024), No, Nh, Nf, Nz, Mf, Mc, Mp,
    (%eM : {Bool.or(D.Fl(m, c, 1024), Bool.or(Bool.or(No, Bool.or(Nh, Bool.or(Nf, Nz))), _)) == True{} : Bool};
      (%eN : {Bool.or(D.Fl(m, c, 1024), Bool.or(_, D.Mem(List.append(&2, U32, D.Fr.cells(fs, m, sp), List.append(&2, U32, D.Tmp.cells(xs), ps)), c))) == True{} : Bool}; hcv)),
    (%eMY : {Bool.or(Bool.or(D.Fl(m, c, 1024), Bool.or(No, Bool.or(Nh, Nf))), _) == False{} : Bool};
      (%eNL : {Bool.or(Bool.or(D.Fl(m, c, 1024), _), D.Mem(Yc(fs, m, sp, D.Tmp.cells(xs)), c)) == False{} : Bool}; hlv)))

# and so a node of a zombie's term, or a cell of the pend list of the machine's own kinds
def gb.cls2(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +os: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  +g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs), +c: U32,
  hcv: {Bool.or(D.Fl(m, c, 1024), Bool.or(D.Nodes(GRS(m, os, xs, fs, sp, zs), m, c), D.Mem(List.append(&2, U32, D.Fr.cells(fs, m, sp), List.append(&2, U32, D.Tmp.cells(xs), ps)), c))) == True{} : Bool},
  hlv: {Lv(m, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs)), c) == False{} : Bool}) ->
  {Bool.or(D.Nodes(zs, m, c), Bool.and(D.Mem(ps, c), U32.is_le(32, D.Tg(m, c)))) == True{} : Bool}:
  D.or.cases(D.Nodes(zs, m, c), D.Mem(ps, c), {Bool.or(D.Nodes(zs, m, c), Bool.and(D.Mem(ps, c), U32.is_le(32, D.Tg(m, c)))) == True{} : Bool},
    gb.cls(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, c, hcv, hlv),
    e => CK.Bo.or_il(D.Nodes(zs, m, c), Bool.and(D.Mem(ps, c), U32.is_le(32, D.Tg(m, c))), e),
    +e => D.or.cases(U32.is_lt(D.Tg(m, c), 19), U32.is_le(32, D.Tg(m, c)),
      {Bool.or(D.Nodes(zs, m, c), Bool.and(D.Mem(ps, c), U32.is_le(32, D.Tg(m, c)))) == True{} : Bool},
      pc.tag(ps, m, fi, nx, D.Rt.cells(os), c, pend.get(ps, ps, m, fi, nx, D.Rt.cells(os), c, gc.pend(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g), e)),
      e2 => CK.Bo.or_il(D.Nodes(zs, m, c), Bool.and(D.Mem(ps, c), U32.is_le(32, D.Tg(m, c))),
        root.nodes(zs, m, c, (%Equal.sym(List<&2, U32>, D.Rt.cells(zs), D.Pend.terms(ps, m), gc.zc(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g)) : {D.Mem(_, c) == True{} : Bool};
          pend.term(ps, m, c, e, e2)))),
      e2 => CK.Bo.or_ir(D.Nodes(zs, m, c), Bool.and(D.Mem(ps, c), U32.is_le(32, D.Tg(m, c))), CK.Bo.and_i(D.Mem(ps, c), U32.is_le(32, D.Tg(m, c)), e, e2))))


# a node of a zombie's term is a term cell
def zom.ex(-ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, -im: U32, -fi: U32, -nx: U32, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>,
  -b: Nat, +c: U32, ex: D.Ex(Bk.Term, v => D.P2(D.IsK(True{}, ds, m, im, fi, nx, ks, img, c, v), N.Le(Pg.Term.size(v), b)))) ->
  {U32.is_lt(D.Tg(m, c), 19) == True{} : Bool}:
  (+v, rr) = ex
  (hv, hl) = rr
  %Equal.sym(U32, D.Tg(m, c), D.A.tag(v), isk.atag(v, True{}, ds, m, im, fi, nx, ks, img, c, hv)) : {U32.is_lt(_, 19) == True{} : Bool}
  atag.lt(v)

def zom.lt19(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +os: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  +g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs), +c: U32, hz: {D.Nodes(zs, m, c) == True{} : Bool}) -> {U32.is_lt(D.Tg(m, c), 19) == True{} : Bool}:
  zom.ex(ds, m, im, fi, nx, ks, img, D.Rts.size(zs), c, nodes.sub(zs, ds, m, im, fi, nx, ks, img, c, gc.zs(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g), hz))

# a garbage cell is a term cell, or of the pend list of the machine's own kinds (GTs)
def gt.at(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +os: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  +g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs), +c: U32, hcv: {CovAt(m, c, GRS(m, os, xs, fs, sp, zs), List.append(&2, U32, D.Fr.cells(fs, m, sp), List.append(&2, U32, D.Tmp.cells(xs), ps))) == True{} : Bool}, hlv: {Lv(m, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs)), c) == False{} : Bool}) ->
  {Bool.or(U32.is_lt(D.Tg(m, c), 19), Bool.and(U32.is_le(32, D.Tg(m, c)), D.Mem(ps, c))) == True{} : Bool}:
  D.or.cases(D.Nodes(zs, m, c), Bool.and(D.Mem(ps, c), U32.is_le(32, D.Tg(m, c))),
    {Bool.or(U32.is_lt(D.Tg(m, c), 19), Bool.and(U32.is_le(32, D.Tg(m, c)), D.Mem(ps, c))) == True{} : Bool},
    gb.cls2(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, c, hcv, hlv),
    e => CK.Bo.or_il(U32.is_lt(D.Tg(m, c), 19), Bool.and(U32.is_le(32, D.Tg(m, c)), D.Mem(ps, c)), zom.lt19(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, c, e)),
    +e => CK.Bo.or_ir(U32.is_lt(D.Tg(m, c), 19), Bool.and(U32.is_le(32, D.Tg(m, c)), D.Mem(ps, c)),
      CK.Bo.and_i(U32.is_le(32, D.Tg(m, c)), D.Mem(ps, c), CK.Bo.and_r(D.Mem(ps, c), U32.is_le(32, D.Tg(m, c)), e),
        CK.Bo.and_l(D.Mem(ps, c), U32.is_le(32, D.Tg(m, c)), e))))

def gts.gb.b(b: Bool, +q: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +os: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  +g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs), +c: U32, eb: {Lv(m, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs)), c) == b : Bool},
  hcv: {CovAt(m, c, GRS(m, os, xs, fs, sp, zs), List.append(&2, U32, D.Fr.cells(fs, m, sp), List.append(&2, U32, D.Tmp.cells(xs), ps))) == True{} : Bool},
  ih: {GTs(Gb.of(q, m, U32.inc(c), Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, ps) == True{} : Bool}) ->
  {GTs(Bool.pick(List<&2, U32>, b, Gb.of(q, m, U32.inc(c), Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), Con{c, Gb.of(q, m, U32.inc(c), Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs)))}), m, ps) == True{} : Bool}:
  match b:
    case True{}:
      ih
    case False{}:
      CK.Bo.and_i(Bool.or(U32.is_lt(D.Tg(m, c), 19), Bool.and(U32.is_le(32, D.Tg(m, c)), D.Mem(ps, c))), GTs(Gb.of(q, m, U32.inc(c), Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, ps),
        gt.at(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, c, hcv, eb), ih)

def gts.gb(k: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +os: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  +g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs), +c: U32, hcov: {D.Cov(k, m, c, GRS(m, os, xs, fs, sp, zs), List.append(&2, U32, D.Fr.cells(fs, m, sp), List.append(&2, U32, D.Tmp.cells(xs), ps))) == True{} : Bool}) ->
  {GTs(Gb.of(k, m, c, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, ps) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+(+q):
      +hc2 = hcov
      gts.gb.b(Lv(m, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs)), c), q, ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, c, {==},
        D.and.l(CovAt(m, c, GRS(m, os, xs, fs, sp, zs), List.append(&2, U32, D.Fr.cells(fs, m, sp), List.append(&2, U32, D.Tmp.cells(xs), ps))), D.Cov(q, m, U32.inc(c), GRS(m, os, xs, fs, sp, zs), List.append(&2, U32, D.Fr.cells(fs, m, sp), List.append(&2, U32, D.Tmp.cells(xs), ps))), hc2),
        gts.gb(q, ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, U32.inc(c), D.and.r(CovAt(m, c, GRS(m, os, xs, fs, sp, zs), List.append(&2, U32, D.Fr.cells(fs, m, sp), List.append(&2, U32, D.Tmp.cells(xs), ps))), D.Cov(q, m, U32.inc(c), GRS(m, os, xs, fs, sp, zs), List.append(&2, U32, D.Fr.cells(fs, m, sp), List.append(&2, U32, D.Tmp.cells(xs), ps))), hc2)))

# Nat equality as is_eq
def is_eq.refl(a: Nat) -> {Nat.is_eq(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      is_eq.refl(p)

def nat.is_eq.of(+a: Nat, -b: Nat, e: {a == b : Nat}) -> {Nat.is_eq(a, b) == True{} : Bool}:
  %e : {Nat.is_eq(a, _) == True{} : Bool}
  is_eq.refl(a)

# a live node p, not STATIC, a term cell out of the pend list: the garbage's
# pointers to it are fewer than its count
def live.cnt(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +os: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  +g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs), +p: U32, +hst: {D.Fl(m, p, 1024) == False{} : Bool}, hnd: {D.Nodes(Lst(os, D.Tmp.held(xs), fs, m, sp), m, p) == True{} : Bool},
  +own: {D.Own(fi, nx, p) == True{} : Bool}, +h19: {U32.is_lt(D.Tg(m, p), 19) == True{} : Bool}, +hnps: {D.Mem(ps, p) == False{} : Bool},
  +hgt: {GTs(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, ps) == True{} : Bool}) -> {Nat.is_lt(S.Pp(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, p), U32.to_nat(S.Fd(1n, m, p))) == True{} : Bool}:
  +NE = Nat.is_eq(U32.to_nat(D.Fd(1n, m, p)), D.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, D.Rt.cells(os), p))
  +ca = cnt.get(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, p, Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), fi, ps, D.Rt.cells(os), own.lo(fi, nx, p, own), own.hi(fi, nx, p, own), gc.cnt(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g))
  +c1 = {(%h19 : {Bool.or(Bool.not(_), Bool.or(D.Fl(m, p, 1024), Bool.or(D.Mem(ps, p), NE))) == True{} : Bool}; ca) :
    {Bool.or(False{}, Bool.or(D.Fl(m, p, 1024), Bool.or(D.Mem(ps, p), NE))) == True{} : Bool}}
  +c2 = {(%hst : {Bool.or(False{}, Bool.or(_, Bool.or(D.Mem(ps, p), NE))) == True{} : Bool}; c1) :
    {Bool.or(False{}, Bool.or(False{}, Bool.or(D.Mem(ps, p), NE))) == True{} : Bool}}
  +c3 = {(%hnps : {Bool.or(False{}, Bool.or(False{}, Bool.or(_, NE))) == True{} : Bool}; c2) : {NE == True{} : Bool}}
  +eq = nat.eq(U32.to_nat(D.Fd(1n, m, p)), D.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, D.Rt.cells(os), p), c3)
  +A = PcG(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, ps, p)
  +B = PcN(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, ps, fi, p, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs)))
  +R = D.RcL(D.Rt.cells(os), p)
  +lp = live.ptr(True{}, ds, m, im, fi, nx, ks, img, ps, gc.tbl(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g), os, xs, fs, sp, GRS(m, os, xs, fs, sp, zs), p,
    gc.os(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g), gc.hl(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g), gc.frs(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g), gc.tmp(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g), hnd, hst)
  +le1 = N.le_rw_r(1n+A, Nat.add(Nat.add(B, R), A), Nat.add(A, Nat.add(B, R)), add.comm(Nat.add(B, R), A),
    N.add_mono(1n, Nat.add(B, R), A, A, lp, N.le_refl(A)))
  +eptr = Equal.trans(Nat, Nat.add(A, Nat.add(B, R)), Nat.add(Nat.add(A, B), R), U32.to_nat(D.Fd(1n, m, p)),
    Equal.sym(Nat, Nat.add(Nat.add(A, B), R), Nat.add(A, Nat.add(B, R)), N.add_assoc(A, B, R)),
    Equal.trans(Nat, Nat.add(Nat.add(A, B), R), Nat.add(D.Pc(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, ps, fi, p), R), U32.to_nat(D.Fd(1n, m, p)),
      Equal.cong(Nat, Nat, w => Nat.add(w, R), Nat.add(A, B), D.Pc(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, ps, fi, p),
        Equal.sym(Nat, D.Pc(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, ps, fi, p), Nat.add(A, B), pc.split(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, ps, fi, p, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))))),
      Equal.sym(Nat, U32.to_nat(D.Fd(1n, m, p)), D.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, D.Rt.cells(os), p), eq)))
  %Equal.sym(Nat, S.Pp(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, p), A, pp.pcg(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, ps, p, hgt)) : {Nat.is_lt(_, U32.to_nat(S.Fd(1n, m, p))) == True{} : Bool}
  le.lt(A, U32.to_nat(D.Fd(1n, m, p)), N.le_rw_r(1n+A, Nat.add(A, Nat.add(B, R)), U32.to_nat(D.Fd(1n, m, p)), eptr, le1))

# a part p of a garbage zombie node c (the cell of a term of size sv), standing for w: STATIC, garbage of
# a smaller zombie size, or live, with more pointers than the garbage's
def al.live.f(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +os: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  +g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs), +p: U32, +w: Bk.Term, +sv: Nat, +hw: D.IsK(True{}, ds, m, im, fi, nx, ks, img, p, w),
  +hle: N.Le(1n+Pg.Term.size(w), sv), +hvf: N.Le(sv, D.Rts.size(zs)), +e: {Lv(m, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs)), p) == False{} : Bool}) ->
  {Bool.or(S.Stc(m, p), Bool.or(Bool.and(S.Has(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), p), Nat.is_lt(S.Zz(Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), p), sv)), Nat.is_lt(S.Pp(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, p), U32.to_nat(S.Fd(1n, m, p))))) == True{} : Bool}:
  +nst = D.or.f.l(D.Fl(m, p, 1024), D.Nodes(Lst(os, D.Tmp.held(xs), fs, m, sp), m, p), D.or.f.l(Lv0(m, Lst(os, D.Tmp.held(xs), fs, m, sp), p), D.Mem(Yc(fs, m, sp, D.Tmp.cells(xs)), p), e))
  +own = or.l2(D.Own(fi, nx, p), D.FlW(Cr.Cir.Cell.get(0n, Cr.Cir.Cells.get(m, p)), 1024), isk.own(w, True{}, ds, m, im, fi, nx, ks, img, p, hw), nst)
  +has = gb.has(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs)), p, e, own.lo(fi, nx, p, own), own.hi(fi, nx, p, own))
  +lew = N.le_trans(Pg.Term.size(w), sv, D.Rts.size(zs), N.weaken(Pg.Term.size(w), sv, hle), hvf)
  +ez = Equal.trans(Nat, S.Zz(Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), p), Zsz(D.Rts.size(zs), m, ks, img, p), Pg.Term.size(w),
    zz.of(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img, p, has), zsz.at(D.Rts.size(zs), ds, m, im, fi, nx, ks, img, p, w, lew, hw))
  CK.Bo.or_ir(S.Stc(m, p), Bool.or(Bool.and(S.Has(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), p), Nat.is_lt(S.Zz(Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), p), sv)), Nat.is_lt(S.Pp(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, p), U32.to_nat(S.Fd(1n, m, p)))),
    CK.Bo.or_il(Bool.and(S.Has(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), p), Nat.is_lt(S.Zz(Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), p), sv)), Nat.is_lt(S.Pp(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, p), U32.to_nat(S.Fd(1n, m, p))),
      CK.Bo.and_i(S.Has(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), p), Nat.is_lt(S.Zz(Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), p), sv), has,
        (%Equal.sym(Nat, S.Zz(Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), p), Pg.Term.size(w), ez) : {Nat.is_lt(_, sv) == True{} : Bool}; le.lt(Pg.Term.size(w), sv, hle)))))

def al.live.nd(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +os: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  +g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs), +p: U32, +w: Bk.Term, +sv: Nat, +hw: D.IsK(True{}, ds, m, im, fi, nx, ks, img, p, w),
  +h19: {U32.is_lt(D.Tg(m, p), 19) == True{} : Bool}, +hst: {D.Fl(m, p, 1024) == False{} : Bool}, hnd: {D.Nodes(Lst(os, D.Tmp.held(xs), fs, m, sp), m, p) == True{} : Bool},
  +elv: {Lv(m, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs)), p) == True{} : Bool}, +hgt: {GTs(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, ps) == True{} : Bool}) ->
  {Bool.or(S.Stc(m, p), Bool.or(Bool.and(S.Has(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), p), Nat.is_lt(S.Zz(Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), p), sv)), Nat.is_lt(S.Pp(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, p), U32.to_nat(S.Fd(1n, m, p))))) == True{} : Bool}:
  +own = or.l2(D.Own(fi, nx, p), D.FlW(Cr.Cir.Cell.get(0n, Cr.Cir.Cells.get(m, p)), 1024), isk.own(w, True{}, ds, m, im, fi, nx, ks, img, p, hw), hst)
  +hnps = bool.case(D.Mem(ps, p), D.Mem(ps, p), {D.Mem(ps, p) == False{} : Bool}, {==},
    e => CK.Bo.tf({D.Mem(ps, p) == False{} : Bool}, Equal.trans(Bool, False{}, Lv(m, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs)), p), True{},
      Equal.sym(Bool, Lv(m, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs)), p), False{}, pend.lv(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, p, e)), elv)),
    e => e)
  CK.Bo.or_ir(S.Stc(m, p), Bool.or(Bool.and(S.Has(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), p), Nat.is_lt(S.Zz(Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), p), sv)), Nat.is_lt(S.Pp(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, p), U32.to_nat(S.Fd(1n, m, p)))),
    CK.Bo.or_ir(Bool.and(S.Has(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), p), Nat.is_lt(S.Zz(Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), p), sv)), Nat.is_lt(S.Pp(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, p), U32.to_nat(S.Fd(1n, m, p))),
      live.cnt(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, p, hst, hnd, own, h19, hnps, hgt)))

def al.live.y(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +os: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  +g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs), +c: U32, +p: U32, +sv: Nat, +hzc: {D.Nodes(zs, m, c) == True{} : Bool}, +hmem: {D.Mem(D.Fs(m, ps, c), p) == True{} : Bool},
  +h19: {U32.is_lt(D.Tg(m, p), 19) == True{} : Bool}, hy: {Bool.or(D.Mem(D.Fr.cells(fs, m, sp), p), D.Mem(D.Tmp.cells(xs), p)) == True{} : Bool}) ->
  {Bool.or(S.Stc(m, p), Bool.or(Bool.and(S.Has(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), p), Nat.is_lt(S.Zz(Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), p), sv)), Nat.is_lt(S.Pp(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, p), U32.to_nat(S.Fd(1n, m, p))))) == True{} : Bool}:
  D.or.cases(D.Mem(D.Fr.cells(fs, m, sp), p), D.Mem(D.Tmp.cells(xs), p),
    {Bool.or(S.Stc(m, p), Bool.or(Bool.and(S.Has(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), p), Nat.is_lt(S.Zz(Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), p), sv)), Nat.is_lt(S.Pp(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, p), U32.to_nat(S.Fd(1n, m, p))))) == True{} : Bool}, hy,
    e => CK.U.lt_ge(D.Tg(m, p), 32,
      {Bool.or(S.Stc(m, p), Bool.or(Bool.and(S.Has(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), p), Nat.is_lt(S.Zz(Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), p), sv)), Nat.is_lt(S.Pp(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, p), U32.to_nat(S.Fd(1n, m, p))))) == True{} : Bool},
      CK.U.lt_le(D.Tg(m, p), 19, 32, h19, {==}),
      frn.tag(ps, fi, nx, m, p, fr.nps(fs, True{}, ds, m, im, fi, nx, ks, img, ps, sp, p, gc.frs(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g), e))),
    e => CK.Bo.tf({Bool.or(S.Stc(m, p), Bool.or(Bool.and(S.Has(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), p), Nat.is_lt(S.Zz(Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), p), sv)), Nat.is_lt(S.Pp(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, p), U32.to_nat(S.Fd(1n, m, p))))) == True{} : Bool},
      Equal.trans(Bool, False{}, D.Nodes(GRS(m, os, xs, fs, sp, zs), m, p), True{},
        Equal.sym(Bool, D.Nodes(GRS(m, os, xs, fs, sp, zs), m, p), False{},
          tc.nnd(m, fi, nx, ps, GRS(m, os, xs, fs, sp, zs), p, tmp.get(xs, m, fi, nx, ps, GRS(m, os, xs, fs, sp, zs), p, gc.tmp(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g), e))),
        nodes.in.r(os, List.append(&2, D.Rt, D.Tmp.held(xs), List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)), m, p,
          nodes.in.r(D.Tmp.held(xs), List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs), m, p,
            nodes.in.r(D.Fr.rts(fs, m, sp), zs, m, p,
              nodes.fs(zs, True{}, ds, m, im, fi, nx, ks, img, ps, gc.tbl(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g), c, p, gc.zs(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g), hzc, hmem)))))))

def al.live(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +os: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  +g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs), +c: U32, +p: U32, +w: Bk.Term, +sv: Nat, +hzc: {D.Nodes(zs, m, c) == True{} : Bool},
  +hmem: {D.Mem(D.Fs(m, ps, c), p) == True{} : Bool}, +hw: D.IsK(True{}, ds, m, im, fi, nx, ks, img, p, w),
  +hle: N.Le(1n+Pg.Term.size(w), sv), +hvf: N.Le(sv, D.Rts.size(zs)), +hgt: {GTs(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, ps) == True{} : Bool}) ->
  {Bool.or(S.Stc(m, p), Bool.or(Bool.and(S.Has(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), p), Nat.is_lt(S.Zz(Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), p), sv)), Nat.is_lt(S.Pp(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, p), U32.to_nat(S.Fd(1n, m, p))))) == True{} : Bool}:
  +h19 = {(%Equal.sym(U32, D.Tg(m, p), D.A.tag(w), isk.atag(w, True{}, ds, m, im, fi, nx, ks, img, p, hw)) : {U32.is_lt(_, 19) == True{} : Bool}; atag.lt(w)) :
    {U32.is_lt(D.Tg(m, p), 19) == True{} : Bool}}
  bool.case(Lv(m, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs)), p), Lv(m, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs)), p),
    {Bool.or(S.Stc(m, p), Bool.or(Bool.and(S.Has(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), p), Nat.is_lt(S.Zz(Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), p), sv)), Nat.is_lt(S.Pp(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, p), U32.to_nat(S.Fd(1n, m, p))))) == True{} : Bool}, {==},
    +e => D.or.cases(Lv0(m, Lst(os, D.Tmp.held(xs), fs, m, sp), p), D.Mem(Yc(fs, m, sp, D.Tmp.cells(xs)), p),
      {Bool.or(S.Stc(m, p), Bool.or(Bool.and(S.Has(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), p), Nat.is_lt(S.Zz(Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), p), sv)), Nat.is_lt(S.Pp(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, p), U32.to_nat(S.Fd(1n, m, p))))) == True{} : Bool}, e,
      +e1 => bool.case(D.Fl(m, p, 1024), D.Fl(m, p, 1024),
        {Bool.or(S.Stc(m, p), Bool.or(Bool.and(S.Has(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), p), Nat.is_lt(S.Zz(Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), p), sv)), Nat.is_lt(S.Pp(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, p), U32.to_nat(S.Fd(1n, m, p))))) == True{} : Bool}, {==},
        e2 => CK.Bo.or_il(S.Stc(m, p), Bool.or(Bool.and(S.Has(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), p), Nat.is_lt(S.Zz(Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), p), sv)), Nat.is_lt(S.Pp(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, p), U32.to_nat(S.Fd(1n, m, p)))), e2),
        +e2 => al.live.nd(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, p, w, sv, hw, h19, e2, or.drop(D.Fl(m, p, 1024), D.Nodes(Lst(os, D.Tmp.held(xs), fs, m, sp), m, p), e1, e2), e, hgt)),
      e1 => al.live.y(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, c, p, sv, hzc, hmem, h19, mem.split(D.Fr.cells(fs, m, sp), D.Tmp.cells(xs), p, e1))),
    e => al.live.f(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, p, w, sv, hw, hle, hvf, e))

# a part p, by the mask, of the zombie node c of a term of size sv
def al.pw(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +os: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  +g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs), +c: U32, +p: U32, +sv: Nat, +hzc: {D.Nodes(zs, m, c) == True{} : Bool}, +hvf: N.Le(sv, D.Rts.size(zs)),
  +hgt: {GTs(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, ps) == True{} : Bool},
  ex: D.Ex(Bk.Term, u0 => D.P2(D.IsK(True{}, ds, m, im, fi, nx, ks, img, p, u0), D.P2(N.Le(1n+Pg.Term.size(u0), sv), {D.Mem(D.Fs(m, ps, c), p) == True{} : Bool})))) ->
  {Bool.or(U32.is_zero(p), Bool.and(Cr.Cir.is_cell(p, im, fi, nx), Bool.or(S.Stc(m, p), Bool.or(Bool.and(S.Has(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), p), Nat.is_lt(S.Zz(Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), p), sv)),
    Nat.is_lt(S.Pp(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, p), U32.to_nat(S.Fd(1n, m, p))))))) == True{} : Bool}:
  (+w, r1) = ex
  (hw0, r2) = r1
  (hle0, hmem0) = r2
  +hw = hw0
  +hle = {hle0 : N.Le(1n+Pg.Term.size(w), sv)}
  +hmem = {hmem0 : {D.Mem(D.Fs(m, ps, c), p) == True{} : Bool}}
  CK.Bo.or_ir(U32.is_zero(p), Bool.and(Cr.Cir.is_cell(p, im, fi, nx), Bool.or(S.Stc(m, p), Bool.or(Bool.and(S.Has(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), p), Nat.is_lt(S.Zz(Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), p), sv)),
    Nat.is_lt(S.Pp(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, p), U32.to_nat(S.Fd(1n, m, p)))))),
    CK.Bo.and_i(Cr.Cir.is_cell(p, im, fi, nx), Bool.or(S.Stc(m, p), Bool.or(Bool.and(S.Has(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), p), Nat.is_lt(S.Zz(Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), p), sv)),
      Nat.is_lt(S.Pp(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, p), U32.to_nat(S.Fd(1n, m, p))))),
      isk.cell(w, True{}, ds, m, im, fi, nx, ks, img, p, hw), al.live(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, c, p, w, sv, hzc, hmem, hw, hle, hvf, hgt)))

# AL.part at a bit of the mask of the zombie node c, which stands for v
def al.bit(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +os: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  +g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs), +c: U32, +v: Bk.Term, +bit: U32, +p: U32, +hzc: {D.Nodes(zs, m, c) == True{} : Bool},
  +hvf: N.Le(Pg.Term.size(v), D.Rts.size(zs)), +hgt: {GTs(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, ps) == True{} : Bool},
  mk: {U32.is_zero(U32.and(D.Mask(v), bit)) == False{} : Bool} ->
    D.Ex(Bk.Term, u0 => D.P2(D.IsK(True{}, ds, m, im, fi, nx, ks, img, p, u0), D.P2(N.Le(1n+Pg.Term.size(u0), Pg.Term.size(v)), {D.Mem(D.Fs(m, ps, c), p) == True{} : Bool})))) ->
  {S.AL.part(m, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), Pg.Term.size(v), D.Mask(v), bit, p, im, fi, nx) == True{} : Bool}:
  bool.case(U32.is_zero(U32.and(D.Mask(v), bit)), U32.is_zero(U32.and(D.Mask(v), bit)),
    {S.AL.part(m, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), Pg.Term.size(v), D.Mask(v), bit, p, im, fi, nx) == True{} : Bool}, {==},
    e => CK.Bo.or_il(U32.is_zero(U32.and(D.Mask(v), bit)), Bool.or(U32.is_zero(p), Bool.and(Cr.Cir.is_cell(p, im, fi, nx), Bool.or(S.Stc(m, p),
      Bool.or(Bool.and(S.Has(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), p), Nat.is_lt(S.Zz(Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), p), Pg.Term.size(v))), Nat.is_lt(S.Pp(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, p), U32.to_nat(S.Fd(1n, m, p))))))), e),
    e => CK.Bo.or_ir(U32.is_zero(U32.and(D.Mask(v), bit)), Bool.or(U32.is_zero(p), Bool.and(Cr.Cir.is_cell(p, im, fi, nx), Bool.or(S.Stc(m, p),
      Bool.or(Bool.and(S.Has(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), p), Nat.is_lt(S.Zz(Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), p), Pg.Term.size(v))), Nat.is_lt(S.Pp(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, p), U32.to_nat(S.Fd(1n, m, p))))))),
      al.pw(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, c, p, Pg.Term.size(v), hzc, hvf, hgt, mk(e))))


# AL.cells at a garbage cell c: its place and tag, its parts, its count
def ALpl(+m: Cr.Cir.Cells, +c: U32, +ps: List<&2, U32>, +F: U32, +N: U32) -> Bool:
  Bool.and(Bool.and(Bool.and(U32.is_le(F, c), U32.is_lt(c, N)), Bool.not(S.Stc(m, c))),
    Bool.or(U32.is_le(U32.and(S.Fd(0n, m, c), 63), 18), Bool.and(U32.is_le(32, U32.and(S.Fd(0n, m, c), 63)), S.Has(ps, c))))

def ALpa(+m: Cr.Cir.Cells, +P: List<&2, U32>, +zs: List<&2, S.Zs>, +z: Nat, +am: U32, +c: U32, +K: U32, +F: U32, +N: U32) -> Bool:
  Bool.and(S.AL.part(m, P, zs, z, am, 1, S.Fd(2n, m, c), K, F, N),
    Bool.and(S.AL.part(m, P, zs, z, am, 2, S.Fd(3n, m, c), K, F, N), S.AL.part(m, P, zs, z, am, 4, S.Fd(4n, m, c), K, F, N)))

def ALco(+m: Cr.Cir.Cells, +P: List<&2, U32>, +ps: List<&2, U32>, +c: U32, +F: U32, +N: U32) -> Bool:
  Bool.and(Nat.is_eq(S.Pc(Nat.sub(U32.to_nat(N), U32.to_nat(F)), m, ps, F, c), S.Pp(P, m, c)),
    Bool.pick(Bool, S.Has(ps, c), Nat.is_eq(S.Pp(P, m, c), 0n),
      Bool.and(Nat.is_eq(S.Pp(P, m, c), U32.to_nat(S.Fd(1n, m, c))), Nat.is_lt(0n, S.Pp(P, m, c)))))

def lt19.le18(+t: U32, h: {U32.is_lt(t, 19) == True{} : Bool}) -> {U32.is_le(t, 18) == True{} : Bool}:
  CK.U.le_t(t, 18, CK.U.lt(t, 19, h))

def al.tag(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +os: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  +g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs), +c: U32, hcls: {Bool.or(D.Nodes(zs, m, c), Bool.and(D.Mem(ps, c), U32.is_le(32, D.Tg(m, c)))) == True{} : Bool}) ->
  {Bool.or(U32.is_le(U32.and(S.Fd(0n, m, c), 63), 18), Bool.and(U32.is_le(32, U32.and(S.Fd(0n, m, c), 63)), S.Has(ps, c))) == True{} : Bool}:
  D.or.cases(D.Nodes(zs, m, c), Bool.and(D.Mem(ps, c), U32.is_le(32, D.Tg(m, c))),
    {Bool.or(U32.is_le(U32.and(S.Fd(0n, m, c), 63), 18), Bool.and(U32.is_le(32, U32.and(S.Fd(0n, m, c), 63)), S.Has(ps, c))) == True{} : Bool}, hcls,
    e => CK.Bo.or_il(U32.is_le(U32.and(S.Fd(0n, m, c), 63), 18), Bool.and(U32.is_le(32, U32.and(S.Fd(0n, m, c), 63)), S.Has(ps, c)),
      lt19.le18(D.Tg(m, c), zom.lt19(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, c, e))),
    +e => CK.Bo.or_ir(U32.is_le(U32.and(S.Fd(0n, m, c), 63), 18), Bool.and(U32.is_le(32, U32.and(S.Fd(0n, m, c), 63)), S.Has(ps, c)),
      CK.Bo.and_i(U32.is_le(32, U32.and(S.Fd(0n, m, c), 63)), S.Has(ps, c), CK.Bo.and_r(D.Mem(ps, c), U32.is_le(32, D.Tg(m, c)), e),
        (%mem.has(ps, c) : {_ == True{} : Bool}; CK.Bo.and_l(D.Mem(ps, c), U32.is_le(32, D.Tg(m, c)), e)))))

def al.place(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +os: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  +g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs), +c: U32, +h1: N.Le(U32.to_nat(fi), U32.to_nat(c)), +h2: N.Le(1n+U32.to_nat(c), U32.to_nat(nx)),
  +nst: {D.Fl(m, c, 1024) == False{} : Bool}, +hcls: {Bool.or(D.Nodes(zs, m, c), Bool.and(D.Mem(ps, c), U32.is_le(32, D.Tg(m, c)))) == True{} : Bool}) ->
  {ALpl(m, c, ps, fi, nx) == True{} : Bool}:
  CK.Bo.and_i(Bool.and(Bool.and(U32.is_le(fi, c), U32.is_lt(c, nx)), Bool.not(S.Stc(m, c))),
    Bool.or(U32.is_le(U32.and(S.Fd(0n, m, c), 63), 18), Bool.and(U32.is_le(32, U32.and(S.Fd(0n, m, c), 63)), S.Has(ps, c))),
    CK.Bo.and_i(Bool.and(U32.is_le(fi, c), U32.is_lt(c, nx)), Bool.not(S.Stc(m, c)),
      CK.Bo.and_i(U32.is_le(fi, c), U32.is_lt(c, nx), CK.U.le_t(fi, c, h1), CK.U.lt_t(c, nx, h2)), CK.Bo.not_i(S.Stc(m, c), nst)),
    al.tag(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, c, hcls))

# the mask that a reuse of a cell that stands for v drops is v's
def am.mask(+ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +c: U32, +v: Bk.Term, +tbl: D.Tbl(m, im, fi, nx), +hv: D.IsK(True{}, ds, m, im, fi, nx, ks, img, c, v)) -> {S.Am(m, c) == D.Mask(v) : U32}:
  +ea = isk.atag(v, True{}, ds, m, im, fi, nx, ks, img, c, hv)
  +h19 = {(%Equal.sym(U32, D.Tg(m, c), D.A.tag(v), ea) : {U32.is_lt(_, 19) == True{} : Bool}; atag.lt(v)) : {U32.is_lt(D.Tg(m, c), 19) == True{} : Bool}}
  Equal.trans(U32, S.Am(m, c), D.Fd(2n, m, U32.add(272, D.Tg(m, c))), D.Mask(v), am.lt(m, c, CK.U.lt_le(D.Tg(m, c), 19, 32, h19, {==})),
    Equal.trans(U32, D.Fd(2n, m, U32.add(272, D.Tg(m, c))), D.Fd(2n, m, U32.add(272, D.A.tag(v))), D.Mask(v),
      Equal.cong(U32, U32, t => D.Fd(2n, m, U32.add(272, t)), D.Tg(m, c), D.A.tag(v), ea),
      D.tbl.mask(m, im, fi, nx, v, tbl)))

# the parts of a zombie node c, of the term v
def al.pz.ex(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +os: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  +g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs), +c: U32, +hzc: {D.Nodes(zs, m, c) == True{} : Bool}, +hgt: {GTs(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, ps) == True{} : Bool},
  +hasc: {S.Has(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), c) == True{} : Bool},
  ex: D.Ex(Bk.Term, v => D.P2(D.IsK(True{}, ds, m, im, fi, nx, ks, img, c, v), N.Le(Pg.Term.size(v), D.Rts.size(zs))))) ->
  {ALpa(m, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), S.Zz(Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), c), S.Am(m, c), c, im, fi, nx) == True{} : Bool}:
  (+v, rr) = ex
  (hv0, hvf0) = rr
  +hv = {hv0 : D.IsK(True{}, ds, m, im, fi, nx, ks, img, c, v)}
  +hvf = {hvf0 : N.Le(Pg.Term.size(v), D.Rts.size(zs))}
  +ez = Equal.trans(Nat, S.Zz(Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), c), Zsz(D.Rts.size(zs), m, ks, img, c), Pg.Term.size(v),
    zz.of(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img, c, hasc), zsz.at(D.Rts.size(zs), ds, m, im, fi, nx, ks, img, c, v, hvf, hv))
  +ea = am.mask(ds, m, im, fi, nx, ks, img, c, v, gc.tbl(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g), hv)
  %Equal.sym(U32, S.Am(m, c), D.Mask(v), ea) : {ALpa(m, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), S.Zz(Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), c), _, c, im, fi, nx) == True{} : Bool}
  %Equal.sym(Nat, S.Zz(Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), c), Pg.Term.size(v), ez) : {ALpa(m, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), _, D.Mask(v), c, im, fi, nx) == True{} : Bool}
  CK.Bo.and_i(S.AL.part(m, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), Pg.Term.size(v), D.Mask(v), 1, S.Fd(2n, m, c), im, fi, nx),
    Bool.and(S.AL.part(m, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), Pg.Term.size(v), D.Mask(v), 2, S.Fd(3n, m, c), im, fi, nx), S.AL.part(m, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), Pg.Term.size(v), D.Mask(v), 4, S.Fd(4n, m, c), im, fi, nx)),
    al.bit(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, c, v, 1, D.Fd(2n, m, c), hzc, hvf, hgt, e => part.s2(v, True{}, ds, m, im, fi, nx, ks, img, ps, gc.tbl(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g), c, hv, e)),
    CK.Bo.and_i(S.AL.part(m, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), Pg.Term.size(v), D.Mask(v), 2, S.Fd(3n, m, c), im, fi, nx), S.AL.part(m, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), Pg.Term.size(v), D.Mask(v), 4, S.Fd(4n, m, c), im, fi, nx),
      al.bit(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, c, v, 2, D.Fd(3n, m, c), hzc, hvf, hgt, e => part.s3(v, True{}, ds, m, im, fi, nx, ks, img, ps, gc.tbl(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g), c, hv, e)),
      al.bit(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, c, v, 4, D.Fd(4n, m, c), hzc, hvf, hgt, e => part.s4(v, True{}, ds, m, im, fi, nx, ks, img, ps, gc.tbl(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g), c, hv, e))))

# the parts of a pending cell of the machine's own kinds: none (its reuse drops none)
def al.pk(+m: Cr.Cir.Cells, +P: List<&2, U32>, +zs: List<&2, S.Zs>, +z: Nat, +c: U32, +im: U32, +fi: U32, +nx: U32,
  +h32: {U32.is_le(32, D.Tg(m, c)) == True{} : Bool}) -> {ALpa(m, P, zs, z, S.Am(m, c), c, im, fi, nx) == True{} : Bool}:
  +nlt = bool.case(U32.is_lt(D.Tg(m, c), 32), U32.is_lt(D.Tg(m, c), 32), {U32.is_lt(D.Tg(m, c), 32) == False{} : Bool}, {==},
    e => CK.U.lt_ge(D.Tg(m, c), 32, {U32.is_lt(D.Tg(m, c), 32) == False{} : Bool}, e, h32), e => e)
  %Equal.sym(U32, S.Am(m, c), 0, am.ge(m, c, nlt)) : {ALpa(m, P, zs, z, _, c, im, fi, nx) == True{} : Bool}
  {==}

def al.parts(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +os: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  +g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs), +c: U32, +hcls: {Bool.or(D.Nodes(zs, m, c), Bool.and(D.Mem(ps, c), U32.is_le(32, D.Tg(m, c)))) == True{} : Bool},
  +hgt: {GTs(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, ps) == True{} : Bool}, +hasc: {S.Has(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), c) == True{} : Bool}) ->
  {ALpa(m, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), S.Zz(Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), c), S.Am(m, c), c, im, fi, nx) == True{} : Bool}:
  D.or.cases(D.Nodes(zs, m, c), Bool.and(D.Mem(ps, c), U32.is_le(32, D.Tg(m, c))),
    {ALpa(m, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), S.Zz(Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), c), S.Am(m, c), c, im, fi, nx) == True{} : Bool}, hcls,
    +e => al.pz.ex(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, c, e, hgt, hasc, nodes.sub(zs, ds, m, im, fi, nx, ks, img, c, gc.zs(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g), e)),
    e => al.pk(m, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), S.Zz(Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), c), c, im, fi, nx, CK.Bo.and_r(D.Mem(ps, c), U32.is_le(32, D.Tg(m, c)), e)))

# the pointers to a garbage cell c are the garbage's
def al.epc(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +os: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  +g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs), +c: U32, +hlv: {Lv(m, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs)), c) == False{} : Bool}, +hgt: {GTs(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, ps) == True{} : Bool}) ->
  {S.Pc(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, ps, fi, c) == S.Pp(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, c) : Nat}:
  +A = PcG(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, ps, c)
  +B = PcN(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, ps, fi, c, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs)))
  Equal.trans(Nat, S.Pc(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, ps, fi, c), D.Pc(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, ps, fi, c), S.Pp(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, c),
    Equal.sym(Nat, D.Pc(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, ps, fi, c), S.Pc(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, ps, fi, c), pc.eq(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, ps, fi, c)),
    Equal.trans(Nat, D.Pc(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, ps, fi, c), Nat.add(A, B), S.Pp(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, c), pc.split(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, ps, fi, c, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))),
      Equal.trans(Nat, Nat.add(A, B), Nat.add(A, 0n), S.Pp(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, c),
        Equal.cong(Nat, Nat, w => Nat.add(A, w), B, 0n,
          pcn.zero(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), True{}, ds, m, im, fi, nx, ks, img, ps, gc.tbl(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g), os, D.Tmp.held(xs), fs, sp, D.Tmp.cells(xs), fi, c,
            gc.L(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g), gc.frs(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g), hlv, gc.clo(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g))),
        Equal.trans(Nat, Nat.add(A, 0n), A, S.Pp(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, c), N.add_zero(A), Equal.sym(Nat, S.Pp(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, c), A, pp.pcg(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, ps, c, hgt))))))

# a garbage cell of the pend list: no pointer
def al.cnt.p(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +os: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  +g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs), +c: U32, +epc: {S.Pc(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, ps, fi, c) == S.Pp(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, c) : Nat}, e: {S.Has(ps, c) == True{} : Bool}) ->
  {Nat.is_eq(S.Pp(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, c), 0n) == True{} : Bool}:
  +hm = {(%Equal.sym(Bool, D.Mem(ps, c), S.Has(ps, c), mem.has(ps, c)) : {_ == True{} : Bool}; e) : {D.Mem(ps, c) == True{} : Bool}}
  +ptr0 = pc.ptr(ps, m, fi, nx, D.Rt.cells(os), c, pend.get(ps, ps, m, fi, nx, D.Rt.cells(os), c, gc.pend(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g), hm))
  +pc0 = D.add0.l(D.Pc(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, ps, fi, c), D.RcL(D.Rt.cells(os), c), ptr0)
  nat.is_eq.of(S.Pp(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, c), 0n, Equal.trans(Nat, S.Pp(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, c), S.Pc(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, ps, fi, c), 0n,
    Equal.sym(Nat, S.Pc(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, ps, fi, c), S.Pp(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, c), epc),
    Equal.trans(Nat, S.Pc(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, ps, fi, c), D.Pc(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, ps, fi, c), 0n,
      Equal.sym(Nat, D.Pc(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, ps, fi, c), S.Pc(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, ps, fi, c), pc.eq(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, ps, fi, c)), pc0)))

# a garbage cell out of the pend list: a zombie node, of a parent in its zombie's term; it counts its pointers
def al.cnt.n(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +os: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  +g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs), +c: U32, +epc: {S.Pc(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, ps, fi, c) == S.Pp(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, c) : Nat}, +hlv: {Lv(m, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs)), c) == False{} : Bool},
  +hcls: {Bool.or(D.Nodes(zs, m, c), Bool.and(D.Mem(ps, c), U32.is_le(32, D.Tg(m, c)))) == True{} : Bool},
  hcn: {CntAt(m, c, Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), fi, ps, D.Rt.cells(os)) == True{} : Bool}, e: {S.Has(ps, c) == False{} : Bool}) ->
  {Bool.and(Nat.is_eq(S.Pp(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, c), U32.to_nat(S.Fd(1n, m, c))), Nat.is_lt(0n, S.Pp(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, c))) == True{} : Bool}:
  +PP = S.Pp(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, c)
  +Pc0 = D.Pc(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, ps, fi, c)
  +hmf = {(%Equal.sym(Bool, D.Mem(ps, c), S.Has(ps, c), mem.has(ps, c)) : {_ == False{} : Bool}; e) : {D.Mem(ps, c) == False{} : Bool}}
  +hz = D.or.cases(D.Nodes(zs, m, c), Bool.and(D.Mem(ps, c), U32.is_le(32, D.Tg(m, c))), {D.Nodes(zs, m, c) == True{} : Bool}, hcls,
    e2 => e2,
    e2 => CK.Bo.tf({D.Nodes(zs, m, c) == True{} : Bool}, Equal.trans(Bool, False{}, D.Mem(ps, c), True{}, Equal.sym(Bool, D.Mem(ps, c), False{}, hmf),
      CK.Bo.and_l(D.Mem(ps, c), U32.is_le(32, D.Tg(m, c)), e2))))
  +h19 = zom.lt19(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, c, hz)
  +nst = D.or.f.l(D.Fl(m, c, 1024), D.Nodes(Lst(os, D.Tmp.held(xs), fs, m, sp), m, c), D.or.f.l(Lv0(m, Lst(os, D.Tmp.held(xs), fs, m, sp), c), D.Mem(Yc(fs, m, sp, D.Tmp.cells(xs)), c), hlv))
  +NE = Nat.is_eq(U32.to_nat(D.Fd(1n, m, c)), D.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, D.Rt.cells(os), c))
  +c1 = {(%h19 : {Bool.or(Bool.not(_), Bool.or(D.Fl(m, c, 1024), Bool.or(D.Mem(ps, c), NE))) == True{} : Bool}; hcn) :
    {Bool.or(False{}, Bool.or(D.Fl(m, c, 1024), Bool.or(D.Mem(ps, c), NE))) == True{} : Bool}}
  +c2 = {(%nst : {Bool.or(False{}, Bool.or(_, Bool.or(D.Mem(ps, c), NE))) == True{} : Bool}; c1) :
    {Bool.or(False{}, Bool.or(False{}, Bool.or(D.Mem(ps, c), NE))) == True{} : Bool}}
  +c3 = {(%hmf : {Bool.or(False{}, Bool.or(False{}, Bool.or(_, NE))) == True{} : Bool}; c2) : {NE == True{} : Bool}}
  +eqc = nat.eq(U32.to_nat(D.Fd(1n, m, c)), D.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, D.Rt.cells(os), c), c3)
  +nro = bool.case(D.Mem(D.Rt.cells(os), c), D.Mem(D.Rt.cells(os), c), {D.Mem(D.Rt.cells(os), c) == False{} : Bool}, {==},
    e3 => CK.Bo.tf({D.Mem(D.Rt.cells(os), c) == False{} : Bool}, Equal.trans(Bool, False{}, Lv(m, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs)), c), True{},
      Equal.sym(Bool, Lv(m, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs)), c), False{}, hlv), lv.os(os, D.Tmp.held(xs), fs, m, sp, D.Tmp.cells(xs), c, root.nodes(os, m, c, e3)))),
    e3 => e3)
  +rz = rcl.zero(D.Rt.cells(os), c, nro)
  +ePc = Equal.trans(Nat, Pc0, S.Pc(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, ps, fi, c), PP, pc.eq(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, ps, fi, c), epc)
  +ecnt = Equal.trans(Nat, PP, Pc0, U32.to_nat(D.Fd(1n, m, c)), Equal.sym(Nat, Pc0, PP, ePc),
    Equal.trans(Nat, Pc0, Nat.add(Pc0, 0n), U32.to_nat(D.Fd(1n, m, c)), Equal.sym(Nat, Nat.add(Pc0, 0n), Pc0, N.add_zero(Pc0)),
      Equal.trans(Nat, Nat.add(Pc0, 0n), Nat.add(Pc0, D.RcL(D.Rt.cells(os), c)), U32.to_nat(D.Fd(1n, m, c)),
        Equal.cong(Nat, Nat, w => Nat.add(Pc0, w), 0n, D.RcL(D.Rt.cells(os), c), Equal.sym(Nat, D.RcL(D.Rt.cells(os), c), 0n, rz)),
        Equal.sym(Nat, U32.to_nat(D.Fd(1n, m, c)), D.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, D.Rt.cells(os), c), eqc))))
  +lp1 = lptr(zs, True{}, ds, m, im, fi, nx, ks, img, ps, gc.tbl(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g), c, gc.zs(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g), hz, nst, N.Le(1n, Pc0),
    hr => CK.Bo.tf(N.Le(1n, Pc0), Equal.trans(Bool, False{}, D.Mem(ps, c), True{}, Equal.sym(Bool, D.Mem(ps, c), False{}, hmf),
      pt.sub(ps, m, c, (%gc.zc(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g) : {D.Mem(_, c) == True{} : Bool}; hr)))),
    +gp => +ho => hn => hm => N.le_trans(1n, D.RcL(D.Fs(m, ps, gp), c), Pc0, D.rcl.mem(D.Fs(m, ps, gp), c, hm),
      D.Pc.at(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, ps, fi, gp, c, own.lo(fi, nx, gp, ho), own.hi(fi, nx, gp, ho))))
  CK.Bo.and_i(Nat.is_eq(PP, U32.to_nat(S.Fd(1n, m, c))), Nat.is_lt(0n, PP), nat.is_eq.of(PP, U32.to_nat(D.Fd(1n, m, c)), ecnt),
    D.le1.lt(PP, N.le_rw_r(1n, Pc0, PP, ePc, lp1)))

def al.count(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +os: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  +g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs), +c: U32, +hlv: {Lv(m, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs)), c) == False{} : Bool},
  +hcls: {Bool.or(D.Nodes(zs, m, c), Bool.and(D.Mem(ps, c), U32.is_le(32, D.Tg(m, c)))) == True{} : Bool},
  +hcn: {CntAt(m, c, Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), fi, ps, D.Rt.cells(os)) == True{} : Bool}, +hgt: {GTs(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, ps) == True{} : Bool}) ->
  {ALco(m, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), ps, c, fi, nx) == True{} : Bool}:
  +PP = S.Pp(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, c)
  +X0 = Nat.is_eq(PP, 0n)
  +X1 = Bool.and(Nat.is_eq(PP, U32.to_nat(S.Fd(1n, m, c))), Nat.is_lt(0n, PP))
  +epc = al.epc(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, c, hlv, hgt)
  CK.Bo.and_i(Nat.is_eq(S.Pc(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, ps, fi, c), PP), Bool.pick(Bool, S.Has(ps, c), X0, X1),
    nat.is_eq.of(S.Pc(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, ps, fi, c), PP, epc),
    bool.case(S.Has(ps, c), S.Has(ps, c), {Bool.pick(Bool, S.Has(ps, c), X0, X1) == True{} : Bool}, {==},
      +e => (%Equal.sym(Bool, S.Has(ps, c), True{}, e) : {Bool.pick(Bool, _, X0, X1) == True{} : Bool}; al.cnt.p(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, c, epc, e)),
      +e => (%Equal.sym(Bool, S.Has(ps, c), False{}, e) : {Bool.pick(Bool, _, X0, X1) == True{} : Bool}; al.cnt.n(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, c, epc, hlv, hcls, hcn, e))))

# AL.cells of the garbage of the k cells from c
def al.cells.b(b: Bool, +q: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +os: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  +g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs), +c: U32, eb: {Lv(m, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs)), c) == b : Bool},
  +hcv: {CovAt(m, c, GRS(m, os, xs, fs, sp, zs), List.append(&2, U32, D.Fr.cells(fs, m, sp), List.append(&2, U32, D.Tmp.cells(xs), ps))) == True{} : Bool}, +hcn: {CntAt(m, c, Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), fi, ps, D.Rt.cells(os)) == True{} : Bool},
  +h1: N.Le(U32.to_nat(fi), U32.to_nat(c)), +hw: N.Le(Nat.add(U32.to_nat(c), 1n+q), U32.to_nat(nx)), +hgt: {GTs(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, ps) == True{} : Bool},
  ih: {S.AL.cells(Gb.of(q, m, U32.inc(c), Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), ps, Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), im, fi, nx) == True{} : Bool}) ->
  {S.AL.cells(Bool.pick(List<&2, U32>, b, Gb.of(q, m, U32.inc(c), Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), Con{c, Gb.of(q, m, U32.inc(c), Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs)))}), m, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), ps, Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), im, fi, nx) == True{} : Bool}:
  match b:
    case True{}:
      ih
    case False{}:
      +hlv = eb
      +hcls = gb.cls2(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, c, hcv, hlv)
      +h2 = w.lt(c, q, nx, hw)
      +nst = D.or.f.l(D.Fl(m, c, 1024), D.Nodes(Lst(os, D.Tmp.held(xs), fs, m, sp), m, c), D.or.f.l(Lv0(m, Lst(os, D.Tmp.held(xs), fs, m, sp), c), D.Mem(Yc(fs, m, sp, D.Tmp.cells(xs)), c), hlv))
      +efn = D.add.sub(U32.to_nat(fi), U32.to_nat(nx), CK.U.le(fi, nx, gc.fn(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g)))
      +hasc = gb.has(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs)), c, hlv, h1,
        N.le_rw_r(1n+U32.to_nat(c), U32.to_nat(nx), Nat.add(U32.to_nat(fi), Nat.sub(U32.to_nat(nx), U32.to_nat(fi))), Equal.sym(Nat, Nat.add(U32.to_nat(fi), Nat.sub(U32.to_nat(nx), U32.to_nat(fi))), U32.to_nat(nx), efn), h2))
      +G1 = Gb.of(q, m, U32.inc(c), Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs)))
      CK.Bo.and_i(ALpl(m, c, ps, fi, nx), Bool.and(ALpa(m, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), S.Zz(Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), c), S.Am(m, c), c, im, fi, nx),
          Bool.and(ALco(m, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), ps, c, fi, nx), S.AL.cells(G1, m, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), ps, Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), im, fi, nx))),
        al.place(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, c, h1, h2, nst, hcls),
        CK.Bo.and_i(ALpa(m, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), S.Zz(Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), c), S.Am(m, c), c, im, fi, nx), Bool.and(ALco(m, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), ps, c, fi, nx), S.AL.cells(G1, m, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), ps, Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), im, fi, nx)),
          al.parts(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, c, hcls, hgt, hasc),
          CK.Bo.and_i(ALco(m, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), ps, c, fi, nx), S.AL.cells(G1, m, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), ps, Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), im, fi, nx), al.count(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, c, hlv, hcls, hcn, hgt), ih)))

def al.cells(k: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +os: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  +g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs), +c: U32, hcov: {D.Cov(k, m, c, GRS(m, os, xs, fs, sp, zs), List.append(&2, U32, D.Fr.cells(fs, m, sp), List.append(&2, U32, D.Tmp.cells(xs), ps))) == True{} : Bool},
  hcnt: {D.Cnt(k, m, c, Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), fi, ps, D.Rt.cells(os)) == True{} : Bool}, +h1: N.Le(U32.to_nat(fi), U32.to_nat(c)),
  +hw: N.Le(Nat.add(U32.to_nat(c), k), U32.to_nat(nx)), +hgt: {GTs(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, ps) == True{} : Bool}) ->
  {S.AL.cells(Gb.of(k, m, c, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), ps, Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), im, fi, nx) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+(+q):
      +hc2 = hcov
      +hn2 = hcnt
      +ei = D.u.inc(c, nx, w.lt(c, q, nx, hw))
      al.cells.b(Lv(m, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs)), c), q, ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, c, {==},
        D.and.l(CovAt(m, c, GRS(m, os, xs, fs, sp, zs), List.append(&2, U32, D.Fr.cells(fs, m, sp), List.append(&2, U32, D.Tmp.cells(xs), ps))), D.Cov(q, m, U32.inc(c), GRS(m, os, xs, fs, sp, zs), List.append(&2, U32, D.Fr.cells(fs, m, sp), List.append(&2, U32, D.Tmp.cells(xs), ps))), hc2),
        D.and.l(CntAt(m, c, Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), fi, ps, D.Rt.cells(os)), D.Cnt(q, m, U32.inc(c), Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), fi, ps, D.Rt.cells(os)), hn2), h1, hw, hgt,
        al.cells(q, ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, U32.inc(c),
          D.and.r(CovAt(m, c, GRS(m, os, xs, fs, sp, zs), List.append(&2, U32, D.Fr.cells(fs, m, sp), List.append(&2, U32, D.Tmp.cells(xs), ps))), D.Cov(q, m, U32.inc(c), GRS(m, os, xs, fs, sp, zs), List.append(&2, U32, D.Fr.cells(fs, m, sp), List.append(&2, U32, D.Tmp.cells(xs), ps))), hc2),
          D.and.r(CntAt(m, c, Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), fi, ps, D.Rt.cells(os)), D.Cnt(q, m, U32.inc(c), Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), fi, ps, D.Rt.cells(os)), hn2),
          N.le_trans(U32.to_nat(fi), U32.to_nat(c), U32.to_nat(U32.inc(c)), h1,
            N.le_rw_r(U32.to_nat(c), 1n+U32.to_nat(c), U32.to_nat(U32.inc(c)), Equal.sym(Nat, U32.to_nat(U32.inc(c)), 1n+U32.to_nat(c), ei),
              N.le_succ(U32.to_nat(c), U32.to_nat(c), N.le_refl(U32.to_nat(c))))),
          w.next(c, q, nx, hw), hgt))

# every pointer of an own cell is below next, to a term cell (the heap's Pts
# gives the copy's Lt)
def lt.all.lt(xs: List<&2, U32>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, h: {D.Lt.all(xs, m, im, fi, nx) == True{} : Bool}) ->
  {S.All.lt(xs, m, nx) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      +h2 = h
      +f0 = Cr.Cir.Cell.get(0n, Cr.Cir.Cells.get(m, x))
      +A = Bool.and(U32.is_lt(x, nx), U32.is_lt(D.TgW(f0), 19))
      +B = Bool.and(Cr.Cir.is_cell(x, im, fi, nx), Bool.or(D.Own(fi, nx, x), D.FlW(f0, 1024)))
      +ha = CK.Bo.and_l(A, B, CK.Bo.and_l(Bool.and(A, B), D.Lt.all(rest, m, im, fi, nx), h2))
      +T18 = U32.is_le(U32.and(S.Fd(0n, m, x), 63), 18)
      CK.Bo.and_i(Bool.and(U32.is_lt(x, nx), Bool.or(U32.is_zero(x), T18)), S.All.lt(rest, m, nx),
        CK.Bo.and_i(U32.is_lt(x, nx), Bool.or(U32.is_zero(x), T18), CK.Bo.and_l(U32.is_lt(x, nx), U32.is_lt(D.TgW(f0), 19), ha),
          CK.Bo.or_ir(U32.is_zero(x), T18, lt19.le18(U32.and(S.Fd(0n, m, x), 63), CK.Bo.and_r(U32.is_lt(x, nx), U32.is_lt(D.TgW(f0), 19), ha)))),
        lt.all.lt(rest, m, im, fi, nx, CK.Bo.and_r(Bool.and(A, B), D.Lt.all(rest, m, im, fi, nx), h2)))

def lt.of(n: Nat, +m: Cr.Cir.Cells, +ps: List<&2, U32>, +o: U32, +im: U32, +fi: U32, +nx: U32,
  h: {D.Pts(n, m, ps, o, im, fi, nx) == True{} : Bool}) -> {S.Lt(n, m, ps, o, nx) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      +h2 = h
      CK.Bo.and_i(S.All.lt(S.Ps(m, ps, o), m, nx), S.Lt(p, m, ps, U32.inc(o), nx),
        (%fs.ps(m, ps, o) : {S.All.lt(_, m, nx) == True{} : Bool};
          lt.all.lt(D.Fs(m, ps, o), m, im, fi, nx, CK.Bo.and_l(D.Lt.all(D.Fs(m, ps, o), m, im, fi, nx), D.Pts(p, m, ps, U32.inc(o), im, fi, nx), h2))),
        lt.of(p, m, ps, U32.inc(o), im, fi, nx, CK.Bo.and_r(D.Lt.all(D.Fs(m, ps, o), m, im, fi, nx), D.Pts(p, m, ps, U32.inc(o), im, fi, nx), h2)))

# the allocation's invariant of the copy's garbage, its pend list (the machine's) and its zombie sizes
def al.all(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +os: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  +g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs), +pend: U32, +regs: List<&2, U32>, hp: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>}, +hch: D.Chain(ps, m, pend),
  +hcov: {D.Cov(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, GRS(m, os, xs, fs, sp, zs), List.append(&2, U32, D.Fr.cells(fs, m, sp), List.append(&2, U32, D.Tmp.cells(xs), ps))) == True{} : Bool}, hpts: {D.Pts(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, ps, fi, im, fi, nx) == True{} : Bool}) ->
  {S.AL(m, T.tm.reg(regs, 3n), Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), ps, Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), im, fi, nx) == True{} : Bool}:
  +efn = D.add.sub(U32.to_nat(fi), U32.to_nat(nx), CK.U.le(fi, nx, gc.fn(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g)))
  +hw0 = N.le_rw_l(U32.to_nat(nx), Nat.add(U32.to_nat(fi), Nat.sub(U32.to_nat(nx), U32.to_nat(fi))), U32.to_nat(nx), Equal.sym(Nat, Nat.add(U32.to_nat(fi), Nat.sub(U32.to_nat(nx), U32.to_nat(fi))), U32.to_nat(nx), efn),
    N.le_refl(U32.to_nat(nx)))
  +hgt = gts.gb(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, fi, hcov)
  %Equal.sym(Maybe<&2, U32>, List.get(&2, U32, regs, 3n), Some{pend}, hp) : {S.AL(m, Maybe.default(&2, U32, _, 0), Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), ps, Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), im, fi, nx) == True{} : Bool}
  CK.Bo.and_i(Bool.and(S.Chain(ps, m, pend), S.Nodup(ps)),
    Bool.and(Bool.and(S.Sub(ps, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs)))), S.Nodup(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))))), Bool.and(S.AL.cells(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), ps, Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), im, fi, nx), S.Lt(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, ps, fi, nx))),
    CK.Bo.and_i(S.Chain(ps, m, pend), S.Nodup(ps), chain.of(ps, m, pend, hch), chain.nodup(ps, m, pend, hch)),
    CK.Bo.and_i(Bool.and(S.Sub(ps, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs)))), S.Nodup(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))))), Bool.and(S.AL.cells(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), ps, Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), im, fi, nx), S.Lt(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, ps, fi, nx)),
      CK.Bo.and_i(S.Sub(ps, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs)))), S.Nodup(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs)))), sub.qp(ps, ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, D.allin.refl(ps)), gb.nodup(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs)), nx, hw0)),
      CK.Bo.and_i(S.AL.cells(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), m, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), ps, Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img), im, fi, nx), S.Lt(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, ps, fi, nx),
        al.cells(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, fi, hcov, gc.cnt(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g), N.le_refl(U32.to_nat(fi)), hw0, hgt),
        lt.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, ps, fi, im, fi, nx, hpts))))


# Pre's other facts
# -----------------
#
# The copy's view: the cells it may not read are the garbage P and the frames
# (E); its roots are the owned ones and the frames' terms, its temporaries the
# move's, holding their terms; its kept cells the own cells of the machine's
# own kinds out of the pend list (Kl); its bound the cells that Acc counts.

# a cell of A ++ B is one of A or of B (the copy's Has)
def has.app(A: List<&2, U32>, +B: List<&2, U32>, +x: U32) ->
  {S.Has(List.append(&2, U32, A, B), x) == Bool.or(S.Has(A, x), S.Has(B, x)) : Bool}:
  match A:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      %Equal.sym(Bool, S.Has(List.append(&2, U32, rest, B), x), Bool.or(S.Has(rest, x), S.Has(B, x)), has.app(rest, B, x)) :
        {Bool.or(U32.is_eq(y, x), _) == Bool.or(Bool.or(U32.is_eq(y, x), S.Has(rest, x)), S.Has(B, x)) : Bool}
      Equal.sym(Bool, Bool.or(Bool.or(U32.is_eq(y, x), S.Has(rest, x)), S.Has(B, x)),
        Bool.or(U32.is_eq(y, x), Bool.or(S.Has(rest, x), S.Has(B, x))), AC.or.assoc(U32.is_eq(y, x), S.Has(rest, x), S.Has(B, x)))

# the table's cells hold no STATIC flag
def NoSt(cs: List<&2, Cr.Cir.Cell>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{c, rest}:
      Bool.and(U32.is_zero(U32.and(Cr.Cir.Cell.get(0n, c), 1024)), NoSt(rest))

def tbl.nost() -> {NoSt(Mc.Img.table([])) == True{} : Bool}:
  {==}

def tbl.len() -> {Nat.add(U32.to_nat(272), List.length(&2, Cr.Cir.Cell, Mc.Img.table([]))) == 291n : Nat}:
  {==}

def tbl.st.b(b: Bool, +c: Cr.Cir.Cell, +rest: List<&2, Cr.Cir.Cell>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +at: U32, +x: U32,
  +eb: {U32.is_eq(at, x) == b : Bool}, h: D.Tbl.go(Con{c, rest}, m, im, fi, nx, at), hcs: {NoSt(Con{c, rest}) == True{} : Bool},
  +h1: N.Le(U32.to_nat(at), U32.to_nat(x)), +h2: N.Le(1n+U32.to_nat(x), Nat.add(U32.to_nat(at), 1n+List.length(&2, Cr.Cir.Cell, rest))),
  ih: D.Tbl.go(rest, m, im, fi, nx, U32.inc(at)) -> {NoSt(rest) == True{} : Bool} -> N.Le(U32.to_nat(U32.inc(at)), U32.to_nat(x)) ->
    N.Le(1n+U32.to_nat(x), Nat.add(U32.to_nat(U32.inc(at)), List.length(&2, Cr.Cir.Cell, rest))) -> {D.Fl(m, x, 1024) == False{} : Bool}) ->
  {D.Fl(m, x, 1024) == False{} : Bool}:
  match b:
    case True{}:
      (hc0, w1) = h
      (hget, hrest) = w1
      %D.u32.eq(at, x, eb) : {D.Fl(m, _, 1024) == False{} : Bool}
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(m, at), c, hget) : {U32.is_ne(U32.and(Cr.Cir.Cell.get(0n, _), 1024), 0) == False{} : Bool}
      %Equal.sym(Bool, U32.is_zero(U32.and(Cr.Cir.Cell.get(0n, c), 1024)), True{}, CK.Bo.and_l(U32.is_zero(U32.and(Cr.Cir.Cell.get(0n, c), 1024)), NoSt(rest), hcs)) :
        {Bool.not(_) == False{} : Bool}
      {==}
    case False{}:
      (hc0, w1) = h
      (hget, hrest) = w1
      ih(hrest, CK.Bo.and_r(U32.is_zero(U32.and(Cr.Cir.Cell.get(0n, c), 1024)), NoSt(rest), hcs), rng.lo(List.length(&2, Cr.Cir.Cell, rest), at, x, eb, h1),
        rng.hi(List.length(&2, Cr.Cir.Cell, rest), at, x, eb, h1, h2))

def tbl.st(cs: List<&2, Cr.Cir.Cell>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +at: U32, +x: U32, h: D.Tbl.go(cs, m, im, fi, nx, at),
  hcs: {NoSt(cs) == True{} : Bool}, h1: N.Le(U32.to_nat(at), U32.to_nat(x)), h2: N.Le(1n+U32.to_nat(x), Nat.add(U32.to_nat(at), List.length(&2, Cr.Cir.Cell, cs)))) ->
  {D.Fl(m, x, 1024) == False{} : Bool}:
  match cs:
    case Nil{}:
      rng.none({D.Fl(m, x, 1024) == False{} : Bool}, at, x, h1, h2)
    case Con{+c, +rest}:
      tbl.st.b(U32.is_eq(at, x), c, rest, m, im, fi, nx, at, x, {==}, h, hcs, h1, h2,
        a => b => d => e => tbl.st(rest, m, im, fi, nx, U32.inc(at), x, a, b, d, e))

# a cell of the table is not STATIC
def tbc.st(+m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +x: U32, h: D.Tbl(m, im, fi, nx), +ht: {S.Tbc(x) == True{} : Bool}) ->
  {D.Fl(m, x, 1024) == False{} : Bool}:
  tbl.st(Mc.Img.table([]), m, im, fi, nx, 272, x, h, tbl.nost(), CK.U.le(272, x, CK.Bo.and_l(U32.is_le(272, x), U32.is_le(x, 290), ht)),
    N.le_rw_r(1n+U32.to_nat(x), 291n, Nat.add(U32.to_nat(272), List.length(&2, Cr.Cir.Cell, Mc.Img.table([]))), Equal.sym(Nat, Nat.add(U32.to_nat(272), List.length(&2, Cr.Cir.Cell, Mc.Img.table([]))), 291n, tbl.len()),
      CK.U.le(x, 290, CK.Bo.and_r(U32.is_le(272, x), U32.is_le(x, 290), ht))))

# a live node may be read: no garbage, no frame (its tag is below 19), no table cell
def rx.at(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +os: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  +g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs), +hK: {U32.is_le(290, im) == True{} : Bool}, +hKF: {U32.is_lt(im, fi) == True{} : Bool}, +x: U32, +v: Bk.Term,
  +h: D.IsK(True{}, ds, m, im, fi, nx, ks, img, x, v), hl: {Lv0(m, Lst(os, D.Tmp.held(xs), fs, m, sp), x) == True{} : Bool}) -> {Rx(List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp)), x) == True{} : Bool}:
  +h19 = {(%Equal.sym(U32, D.Tg(m, x), D.A.tag(v), isk.atag(v, True{}, ds, m, im, fi, nx, ks, img, x, h)) : {U32.is_lt(_, 19) == True{} : Bool}; atag.lt(v)) :
    {U32.is_lt(D.Tg(m, x), 19) == True{} : Bool}}
  +np = gb.not(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs)), x, CK.Bo.or_il(Lv0(m, Lst(os, D.Tmp.held(xs), fs, m, sp), x), D.Mem(Yc(fs, m, sp, D.Tmp.cells(xs)), x), hl))
  +nf = bool.case(D.Mem(D.Fr.cells(fs, m, sp), x), D.Mem(D.Fr.cells(fs, m, sp), x), {D.Mem(D.Fr.cells(fs, m, sp), x) == False{} : Bool}, {==},
    e => CK.U.lt_ge(D.Tg(m, x), 32, {D.Mem(D.Fr.cells(fs, m, sp), x) == False{} : Bool}, CK.U.lt_le(D.Tg(m, x), 19, 32, h19, {==}),
      frn.tag(ps, fi, nx, m, x, fr.nps(fs, True{}, ds, m, im, fi, nx, ks, img, ps, sp, x, gc.frs(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g), e))),
    e => e)
  +nfs = {(%mem.has(D.Fr.cells(fs, m, sp), x) : {_ == False{} : Bool}; nf) : {S.Has(D.Fr.cells(fs, m, sp), x) == False{} : Bool}}
  +ntb = bool.case(S.Tbc(x), S.Tbc(x), {S.Tbc(x) == False{} : Bool}, {==},
    +e => CK.Bo.tf({S.Tbc(x) == False{} : Bool}, Equal.trans(Bool, False{}, D.Fl(m, x, 1024), True{},
      Equal.sym(Bool, D.Fl(m, x, 1024), False{}, tbc.st(m, im, fi, nx, x, gc.tbl(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g), e)),
      or.drop(D.Own(fi, nx, x), D.Fl(m, x, 1024), isk.own(v, True{}, ds, m, im, fi, nx, ks, img, x, h),
        bool.case(U32.is_le(fi, x), U32.is_le(fi, x), {D.Own(fi, nx, x) == False{} : Bool}, {==},
          e2 => CK.U.lt_ge(x, fi, {D.Own(fi, nx, x) == False{} : Bool},
            CK.U.le_lt(x, im, fi, CK.U.le_t(x, im, N.le_trans(U32.to_nat(x), U32.to_nat(290), U32.to_nat(im),
              CK.U.le(x, 290, CK.Bo.and_r(U32.is_le(272, x), U32.is_le(x, 290), e)), CK.U.le(290, im, hK))), hKF), e2),
          e2 => (%Equal.sym(Bool, U32.is_le(fi, x), False{}, e2) : {Bool.and(_, U32.is_lt(x, nx)) == False{} : Bool}; {==}))))),
    e => e)
  CK.Bo.and_i(Bool.not(S.Has(List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp)), x)), Bool.not(S.Tbc(x)),
    CK.Bo.not_i(S.Has(List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp)), x), (%Equal.sym(Bool, S.Has(List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp)), x), Bool.or(S.Has(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), x), S.Has(D.Fr.cells(fs, m, sp), x)), has.app(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp), x)) :
      {_ == False{} : Bool}; or.ff(S.Has(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), x), S.Has(D.Fr.cells(fs, m, sp), x), np, nfs))),
    CK.Bo.not_i(S.Tbc(x), ntb))
# every node of a term at r, live (Ln), may be read: Rx.all
def rx.ln(t: Bk.Term, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +os: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  +g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs), +hK: {U32.is_le(290, im) == True{} : Bool}, +hKF: {U32.is_lt(im, fi) == True{} : Bool},
  +r: U32, +h: D.IsK(True{}, ds, m, im, fi, nx, ks, img, r, t), hln: {Ln(t, m, r, Lst(os, D.Tmp.held(xs), fs, m, sp)) == True{} : Bool}) ->
  {Rx.all(t, m, r, List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp))) == True{} : Bool}:
  match t:
    case Bk.Term.Var{+i}:
      rx.at(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, hK, hKF, r, Bk.Term.Var{i}, h, hln)
    case Bk.Term.Ref{+k}:
      rx.at(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, hK, hKF, r, Bk.Term.Ref{k}, h, hln)
    case Bk.Term.Ann{+y, +z}:
      (+nd, w0) = h
      (py, pz) = w0
      (sy, hy) = py
      (sz, hz) = pz
      +hl2 = hln
      +hp = CK.Bo.and_r(Lv0(m, Lst(os, D.Tmp.held(xs), fs, m, sp), r), Bool.and(Ln(y, m, D.Fd(2n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), Ln(z, m, D.Fd(3n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp))), hl2)
      CK.Bo.and_i(Rx(List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp)), r), Bool.and(Rx.all(y, m, D.Fd(2n, m, r), List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp))), Rx.all(z, m, D.Fd(3n, m, r), List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp)))), rx.at(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, hK, hKF, r, Bk.Term.Ann{y, z}, h, CK.Bo.and_l(Lv0(m, Lst(os, D.Tmp.held(xs), fs, m, sp), r), Bool.and(Ln(y, m, D.Fd(2n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), Ln(z, m, D.Fd(3n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp))), hl2)),
        CK.Bo.and_i(Rx.all(y, m, D.Fd(2n, m, r), List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp))), Rx.all(z, m, D.Fd(3n, m, r), List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp))), rx.ln(y, ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, hK, hKF, D.Fd(2n, m, r), hy, CK.Bo.and_l(Ln(y, m, D.Fd(2n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), Ln(z, m, D.Fd(3n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), hp)), rx.ln(z, ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, hK, hKF, D.Fd(3n, m, r), hz, CK.Bo.and_r(Ln(y, m, D.Fd(2n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), Ln(z, m, D.Fd(3n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), hp))))
    case Bk.Term.Let{+q, +y, +z}:
      (+nd, w0) = h
      (hq, w2) = w0
      (py, pz) = w2
      (sy, hy) = py
      (sz, hz) = pz
      +hl2 = hln
      +hp = CK.Bo.and_r(Lv0(m, Lst(os, D.Tmp.held(xs), fs, m, sp), r), Bool.and(Ln(y, m, D.Fd(2n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), Ln(z, m, D.Fd(3n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp))), hl2)
      CK.Bo.and_i(Rx(List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp)), r), Bool.and(Rx.all(y, m, D.Fd(2n, m, r), List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp))), Rx.all(z, m, D.Fd(3n, m, r), List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp)))), rx.at(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, hK, hKF, r, Bk.Term.Let{q, y, z}, h, CK.Bo.and_l(Lv0(m, Lst(os, D.Tmp.held(xs), fs, m, sp), r), Bool.and(Ln(y, m, D.Fd(2n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), Ln(z, m, D.Fd(3n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp))), hl2)),
        CK.Bo.and_i(Rx.all(y, m, D.Fd(2n, m, r), List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp))), Rx.all(z, m, D.Fd(3n, m, r), List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp))), rx.ln(y, ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, hK, hKF, D.Fd(2n, m, r), hy, CK.Bo.and_l(Ln(y, m, D.Fd(2n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), Ln(z, m, D.Fd(3n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), hp)), rx.ln(z, ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, hK, hKF, D.Fd(3n, m, r), hz, CK.Bo.and_r(Ln(y, m, D.Fd(2n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), Ln(z, m, D.Fd(3n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), hp))))
    case Bk.Term.Typ{+y}:
      (+nd, w0) = h
      (sy, hy) = w0
      +hl2 = hln
      +hp = CK.Bo.and_r(Lv0(m, Lst(os, D.Tmp.held(xs), fs, m, sp), r), Ln(y, m, D.Fd(2n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), hl2)
      CK.Bo.and_i(Rx(List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp)), r), Rx.all(y, m, D.Fd(2n, m, r), List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp))), rx.at(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, hK, hKF, r, Bk.Term.Typ{y}, h, CK.Bo.and_l(Lv0(m, Lst(os, D.Tmp.held(xs), fs, m, sp), r), Ln(y, m, D.Fd(2n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), hl2)),
        rx.ln(y, ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, hK, hKF, D.Fd(2n, m, r), hy, hp))
    case Bk.Term.Min{+y, +z}:
      (+nd, w0) = h
      (py, pz) = w0
      (sy, hy) = py
      (sz, hz) = pz
      +hl2 = hln
      +hp = CK.Bo.and_r(Lv0(m, Lst(os, D.Tmp.held(xs), fs, m, sp), r), Bool.and(Ln(y, m, D.Fd(2n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), Ln(z, m, D.Fd(3n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp))), hl2)
      CK.Bo.and_i(Rx(List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp)), r), Bool.and(Rx.all(y, m, D.Fd(2n, m, r), List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp))), Rx.all(z, m, D.Fd(3n, m, r), List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp)))), rx.at(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, hK, hKF, r, Bk.Term.Min{y, z}, h, CK.Bo.and_l(Lv0(m, Lst(os, D.Tmp.held(xs), fs, m, sp), r), Bool.and(Ln(y, m, D.Fd(2n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), Ln(z, m, D.Fd(3n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp))), hl2)),
        CK.Bo.and_i(Rx.all(y, m, D.Fd(2n, m, r), List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp))), Rx.all(z, m, D.Fd(3n, m, r), List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp))), rx.ln(y, ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, hK, hKF, D.Fd(2n, m, r), hy, CK.Bo.and_l(Ln(y, m, D.Fd(2n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), Ln(z, m, D.Fd(3n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), hp)), rx.ln(z, ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, hK, hKF, D.Fd(3n, m, r), hz, CK.Bo.and_r(Ln(y, m, D.Fd(2n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), Ln(z, m, D.Fd(3n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), hp))))
    case Bk.Term.All{+q, +y, +z}:
      (+nd, w0) = h
      (hq, w2) = w0
      (py, pz) = w2
      (sy, hy) = py
      (sz, hz) = pz
      +hl2 = hln
      +hp = CK.Bo.and_r(Lv0(m, Lst(os, D.Tmp.held(xs), fs, m, sp), r), Bool.and(Ln(y, m, D.Fd(2n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), Ln(z, m, D.Fd(3n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp))), hl2)
      CK.Bo.and_i(Rx(List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp)), r), Bool.and(Rx.all(y, m, D.Fd(2n, m, r), List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp))), Rx.all(z, m, D.Fd(3n, m, r), List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp)))), rx.at(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, hK, hKF, r, Bk.Term.All{q, y, z}, h, CK.Bo.and_l(Lv0(m, Lst(os, D.Tmp.held(xs), fs, m, sp), r), Bool.and(Ln(y, m, D.Fd(2n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), Ln(z, m, D.Fd(3n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp))), hl2)),
        CK.Bo.and_i(Rx.all(y, m, D.Fd(2n, m, r), List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp))), Rx.all(z, m, D.Fd(3n, m, r), List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp))), rx.ln(y, ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, hK, hKF, D.Fd(2n, m, r), hy, CK.Bo.and_l(Ln(y, m, D.Fd(2n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), Ln(z, m, D.Fd(3n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), hp)), rx.ln(z, ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, hK, hKF, D.Fd(3n, m, r), hz, CK.Bo.and_r(Ln(y, m, D.Fd(2n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), Ln(z, m, D.Fd(3n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), hp))))
    case Bk.Term.Lam{+q, +y}:
      (+nd, w0) = h
      (hq, w2) = w0
      (sy, hy) = w2
      +hl2 = hln
      +hp = CK.Bo.and_r(Lv0(m, Lst(os, D.Tmp.held(xs), fs, m, sp), r), Ln(y, m, D.Fd(2n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), hl2)
      CK.Bo.and_i(Rx(List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp)), r), Rx.all(y, m, D.Fd(2n, m, r), List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp))), rx.at(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, hK, hKF, r, Bk.Term.Lam{q, y}, h, CK.Bo.and_l(Lv0(m, Lst(os, D.Tmp.held(xs), fs, m, sp), r), Ln(y, m, D.Fd(2n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), hl2)),
        rx.ln(y, ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, hK, hKF, D.Fd(2n, m, r), hy, hp))
    case Bk.Term.App{+q, +y, +z}:
      (+nd, w0) = h
      (hq, w2) = w0
      (py, pz) = w2
      (sy, hy) = py
      (sz, hz) = pz
      +hl2 = hln
      +hp = CK.Bo.and_r(Lv0(m, Lst(os, D.Tmp.held(xs), fs, m, sp), r), Bool.and(Ln(y, m, D.Fd(2n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), Ln(z, m, D.Fd(3n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp))), hl2)
      CK.Bo.and_i(Rx(List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp)), r), Bool.and(Rx.all(y, m, D.Fd(2n, m, r), List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp))), Rx.all(z, m, D.Fd(3n, m, r), List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp)))), rx.at(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, hK, hKF, r, Bk.Term.App{q, y, z}, h, CK.Bo.and_l(Lv0(m, Lst(os, D.Tmp.held(xs), fs, m, sp), r), Bool.and(Ln(y, m, D.Fd(2n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), Ln(z, m, D.Fd(3n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp))), hl2)),
        CK.Bo.and_i(Rx.all(y, m, D.Fd(2n, m, r), List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp))), Rx.all(z, m, D.Fd(3n, m, r), List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp))), rx.ln(y, ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, hK, hKF, D.Fd(2n, m, r), hy, CK.Bo.and_l(Ln(y, m, D.Fd(2n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), Ln(z, m, D.Fd(3n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), hp)), rx.ln(z, ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, hK, hKF, D.Fd(3n, m, r), hz, CK.Bo.and_r(Ln(y, m, D.Fd(2n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), Ln(z, m, D.Fd(3n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), hp))))
    case Bk.Term.Sig{+q, +y, +z}:
      (+nd, w0) = h
      (hq, w2) = w0
      (py, pz) = w2
      (sy, hy) = py
      (sz, hz) = pz
      +hl2 = hln
      +hp = CK.Bo.and_r(Lv0(m, Lst(os, D.Tmp.held(xs), fs, m, sp), r), Bool.and(Ln(y, m, D.Fd(2n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), Ln(z, m, D.Fd(3n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp))), hl2)
      CK.Bo.and_i(Rx(List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp)), r), Bool.and(Rx.all(y, m, D.Fd(2n, m, r), List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp))), Rx.all(z, m, D.Fd(3n, m, r), List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp)))), rx.at(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, hK, hKF, r, Bk.Term.Sig{q, y, z}, h, CK.Bo.and_l(Lv0(m, Lst(os, D.Tmp.held(xs), fs, m, sp), r), Bool.and(Ln(y, m, D.Fd(2n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), Ln(z, m, D.Fd(3n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp))), hl2)),
        CK.Bo.and_i(Rx.all(y, m, D.Fd(2n, m, r), List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp))), Rx.all(z, m, D.Fd(3n, m, r), List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp))), rx.ln(y, ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, hK, hKF, D.Fd(2n, m, r), hy, CK.Bo.and_l(Ln(y, m, D.Fd(2n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), Ln(z, m, D.Fd(3n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), hp)), rx.ln(z, ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, hK, hKF, D.Fd(3n, m, r), hz, CK.Bo.and_r(Ln(y, m, D.Fd(2n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), Ln(z, m, D.Fd(3n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), hp))))
    case Bk.Term.Tup{+q, +y, +z}:
      (+nd, w0) = h
      (hq, w2) = w0
      (py, pz) = w2
      (sy, hy) = py
      (sz, hz) = pz
      +hl2 = hln
      +hp = CK.Bo.and_r(Lv0(m, Lst(os, D.Tmp.held(xs), fs, m, sp), r), Bool.and(Ln(y, m, D.Fd(2n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), Ln(z, m, D.Fd(3n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp))), hl2)
      CK.Bo.and_i(Rx(List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp)), r), Bool.and(Rx.all(y, m, D.Fd(2n, m, r), List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp))), Rx.all(z, m, D.Fd(3n, m, r), List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp)))), rx.at(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, hK, hKF, r, Bk.Term.Tup{q, y, z}, h, CK.Bo.and_l(Lv0(m, Lst(os, D.Tmp.held(xs), fs, m, sp), r), Bool.and(Ln(y, m, D.Fd(2n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), Ln(z, m, D.Fd(3n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp))), hl2)),
        CK.Bo.and_i(Rx.all(y, m, D.Fd(2n, m, r), List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp))), Rx.all(z, m, D.Fd(3n, m, r), List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp))), rx.ln(y, ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, hK, hKF, D.Fd(2n, m, r), hy, CK.Bo.and_l(Ln(y, m, D.Fd(2n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), Ln(z, m, D.Fd(3n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), hp)), rx.ln(z, ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, hK, hKF, D.Fd(3n, m, r), hz, CK.Bo.and_r(Ln(y, m, D.Fd(2n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), Ln(z, m, D.Fd(3n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), hp))))
    case Bk.Term.Prj{+y}:
      (+nd, w0) = h
      (sy, hy) = w0
      +hl2 = hln
      +hp = CK.Bo.and_r(Lv0(m, Lst(os, D.Tmp.held(xs), fs, m, sp), r), Ln(y, m, D.Fd(2n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), hl2)
      CK.Bo.and_i(Rx(List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp)), r), Rx.all(y, m, D.Fd(2n, m, r), List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp))), rx.at(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, hK, hKF, r, Bk.Term.Prj{y}, h, CK.Bo.and_l(Lv0(m, Lst(os, D.Tmp.held(xs), fs, m, sp), r), Ln(y, m, D.Fd(2n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), hl2)),
        rx.ln(y, ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, hK, hKF, D.Fd(2n, m, r), hy, hp))
    case Bk.Term.Enu{+e}:
      rx.at(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, hK, hKF, r, Bk.Term.Enu{e}, h, hln)
    case Bk.Term.Lab{+k}:
      rx.at(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, hK, hKF, r, Bk.Term.Lab{k}, h, hln)
    case Bk.Term.Mat{+k, +y, +z}:
      (+nd, w0) = h
      (nm, w2) = w0
      (py, pz) = w2
      (sy, hy) = py
      (sz, hz) = pz
      +hl2 = hln
      +hp = CK.Bo.and_r(Lv0(m, Lst(os, D.Tmp.held(xs), fs, m, sp), r), Bool.and(Ln(y, m, D.Fd(3n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), Ln(z, m, D.Fd(4n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp))), hl2)
      CK.Bo.and_i(Rx(List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp)), r), Bool.and(Rx.all(y, m, D.Fd(3n, m, r), List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp))), Rx.all(z, m, D.Fd(4n, m, r), List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp)))), rx.at(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, hK, hKF, r, Bk.Term.Mat{k, y, z}, h, CK.Bo.and_l(Lv0(m, Lst(os, D.Tmp.held(xs), fs, m, sp), r), Bool.and(Ln(y, m, D.Fd(3n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), Ln(z, m, D.Fd(4n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp))), hl2)),
        CK.Bo.and_i(Rx.all(y, m, D.Fd(3n, m, r), List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp))), Rx.all(z, m, D.Fd(4n, m, r), List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp))), rx.ln(y, ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, hK, hKF, D.Fd(3n, m, r), hy, CK.Bo.and_l(Ln(y, m, D.Fd(3n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), Ln(z, m, D.Fd(4n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), hp)), rx.ln(z, ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, hK, hKF, D.Fd(4n, m, r), hz, CK.Bo.and_r(Ln(y, m, D.Fd(3n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), Ln(z, m, D.Fd(4n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), hp))))
    case Bk.Term.Efq{}:
      rx.at(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, hK, hKF, r, Bk.Term.Efq{}, h, hln)
    case Bk.Term.Eql{+y, +z, +w}:
      (+nd, w0) = h
      (py, w2) = w0
      (sy, hy) = py
      (pz, pw) = w2
      (sz, hz) = pz
      (sw, hw) = pw
      +hl2 = hln
      +hp = CK.Bo.and_r(Lv0(m, Lst(os, D.Tmp.held(xs), fs, m, sp), r), Bool.and(Ln(y, m, D.Fd(2n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), Bool.and(Ln(z, m, D.Fd(3n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), Ln(w, m, D.Fd(4n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)))), hl2)
      CK.Bo.and_i(Rx(List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp)), r), Bool.and(Rx.all(y, m, D.Fd(2n, m, r), List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp))), Bool.and(Rx.all(z, m, D.Fd(3n, m, r), List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp))), Rx.all(w, m, D.Fd(4n, m, r), List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp))))), rx.at(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, hK, hKF, r, Bk.Term.Eql{y, z, w}, h, CK.Bo.and_l(Lv0(m, Lst(os, D.Tmp.held(xs), fs, m, sp), r), Bool.and(Ln(y, m, D.Fd(2n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), Bool.and(Ln(z, m, D.Fd(3n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), Ln(w, m, D.Fd(4n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)))), hl2)),
        CK.Bo.and_i(Rx.all(y, m, D.Fd(2n, m, r), List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp))), Bool.and(Rx.all(z, m, D.Fd(3n, m, r), List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp))), Rx.all(w, m, D.Fd(4n, m, r), List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp)))), rx.ln(y, ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, hK, hKF, D.Fd(2n, m, r), hy, CK.Bo.and_l(Ln(y, m, D.Fd(2n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), Bool.and(Ln(z, m, D.Fd(3n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), Ln(w, m, D.Fd(4n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp))), hp)), CK.Bo.and_i(Rx.all(z, m, D.Fd(3n, m, r), List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp))), Rx.all(w, m, D.Fd(4n, m, r), List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp))), rx.ln(z, ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, hK, hKF, D.Fd(3n, m, r), hz, CK.Bo.and_l(Ln(z, m, D.Fd(3n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), Ln(w, m, D.Fd(4n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), CK.Bo.and_r(Ln(y, m, D.Fd(2n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), Bool.and(Ln(z, m, D.Fd(3n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), Ln(w, m, D.Fd(4n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp))), hp))), rx.ln(w, ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, hK, hKF, D.Fd(4n, m, r), hw, CK.Bo.and_r(Ln(z, m, D.Fd(3n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), Ln(w, m, D.Fd(4n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), CK.Bo.and_r(Ln(y, m, D.Fd(2n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), Bool.and(Ln(z, m, D.Fd(3n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), Ln(w, m, D.Fd(4n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp))), hp))))))
    case Bk.Term.Rfl{}:
      rx.at(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, hK, hKF, r, Bk.Term.Rfl{}, h, hln)
    case Bk.Term.Rwt{+y, +z, +w}:
      (+nd, w0) = h
      (py, w2) = w0
      (sy, hy) = py
      (pz, pw) = w2
      (sz, hz) = pz
      (sw, hw) = pw
      +hl2 = hln
      +hp = CK.Bo.and_r(Lv0(m, Lst(os, D.Tmp.held(xs), fs, m, sp), r), Bool.and(Ln(y, m, D.Fd(2n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), Bool.and(Ln(z, m, D.Fd(3n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), Ln(w, m, D.Fd(4n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)))), hl2)
      CK.Bo.and_i(Rx(List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp)), r), Bool.and(Rx.all(y, m, D.Fd(2n, m, r), List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp))), Bool.and(Rx.all(z, m, D.Fd(3n, m, r), List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp))), Rx.all(w, m, D.Fd(4n, m, r), List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp))))), rx.at(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, hK, hKF, r, Bk.Term.Rwt{y, z, w}, h, CK.Bo.and_l(Lv0(m, Lst(os, D.Tmp.held(xs), fs, m, sp), r), Bool.and(Ln(y, m, D.Fd(2n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), Bool.and(Ln(z, m, D.Fd(3n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), Ln(w, m, D.Fd(4n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)))), hl2)),
        CK.Bo.and_i(Rx.all(y, m, D.Fd(2n, m, r), List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp))), Bool.and(Rx.all(z, m, D.Fd(3n, m, r), List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp))), Rx.all(w, m, D.Fd(4n, m, r), List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp)))), rx.ln(y, ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, hK, hKF, D.Fd(2n, m, r), hy, CK.Bo.and_l(Ln(y, m, D.Fd(2n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), Bool.and(Ln(z, m, D.Fd(3n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), Ln(w, m, D.Fd(4n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp))), hp)), CK.Bo.and_i(Rx.all(z, m, D.Fd(3n, m, r), List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp))), Rx.all(w, m, D.Fd(4n, m, r), List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp))), rx.ln(z, ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, hK, hKF, D.Fd(3n, m, r), hz, CK.Bo.and_l(Ln(z, m, D.Fd(3n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), Ln(w, m, D.Fd(4n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), CK.Bo.and_r(Ln(y, m, D.Fd(2n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), Bool.and(Ln(z, m, D.Fd(3n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), Ln(w, m, D.Fd(4n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp))), hp))), rx.ln(w, ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, hK, hKF, D.Fd(4n, m, r), hw, CK.Bo.and_r(Ln(z, m, D.Fd(3n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), Ln(w, m, D.Fd(4n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), CK.Bo.and_r(Ln(y, m, D.Fd(2n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), Bool.and(Ln(z, m, D.Fd(3n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp)), Ln(w, m, D.Fd(4n, m, r), Lst(os, D.Tmp.held(xs), fs, m, sp))), hp))))))



# each of the cells ys is a node of a term of L
def NdAll(ys: List<&2, U32>, +L: List<&2, D.Rt>, +m: Cr.Cir.Cells) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case Con{+y, rest}:
      Bool.and(D.Nodes(L, m, y), NdAll(rest, L, m))

def ndall.app(A: List<&2, U32>, +B: List<&2, U32>, +L: List<&2, D.Rt>, +m: Cr.Cir.Cells, ha: {NdAll(A, L, m) == True{} : Bool},
  +hb: {NdAll(B, L, m) == True{} : Bool}) -> {NdAll(List.append(&2, U32, A, B), L, m) == True{} : Bool}:
  match A:
    case Nil{}:
      hb
    case Con{+y, +rest}:
      +h2 = ha
      CK.Bo.and_i(D.Nodes(L, m, y), NdAll(List.append(&2, U32, rest, B), L, m), CK.Bo.and_l(D.Nodes(L, m, y), NdAll(rest, L, m), h2),
        ndall.app(rest, B, L, m, CK.Bo.and_r(D.Nodes(L, m, y), NdAll(rest, L, m), h2), hb))

# the roots of the owned terms, of the temporaries' terms and of the frames' terms are live nodes
def ndall.os(ys: List<&2, U32>, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +os: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  +g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs), hin: {D.AllIn(ys, D.Rt.cells(os)) == True{} : Bool}) -> {NdAll(ys, Lst(os, D.Tmp.held(xs), fs, m, sp), m) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      +h2 = hin
      CK.Bo.and_i(D.Nodes(Lst(os, D.Tmp.held(xs), fs, m, sp), m, y), NdAll(rest, Lst(os, D.Tmp.held(xs), fs, m, sp), m),
        nodes.in.l(os, List.append(&2, D.Rt, D.Tmp.held(xs), D.Fr.rts(fs, m, sp)), m, y,
          root.nodes(os, m, y, D.and.l(D.Mem(D.Rt.cells(os), y), D.AllIn(rest, D.Rt.cells(os)), h2))),
        ndall.os(rest, ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, D.and.r(D.Mem(D.Rt.cells(os), y), D.AllIn(rest, D.Rt.cells(os)), h2)))

def ndall.hl(ys: List<&2, U32>, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +os: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  +g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs), hin: {D.AllIn(ys, D.Rt.cells(D.Tmp.held(xs))) == True{} : Bool}) -> {NdAll(ys, Lst(os, D.Tmp.held(xs), fs, m, sp), m) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      +h2 = hin
      CK.Bo.and_i(D.Nodes(Lst(os, D.Tmp.held(xs), fs, m, sp), m, y), NdAll(rest, Lst(os, D.Tmp.held(xs), fs, m, sp), m),
        nodes.in.r(os, List.append(&2, D.Rt, D.Tmp.held(xs), D.Fr.rts(fs, m, sp)), m, y,
          nodes.in.l(D.Tmp.held(xs), D.Fr.rts(fs, m, sp), m, y,
            root.nodes(D.Tmp.held(xs), m, y, D.and.l(D.Mem(D.Rt.cells(D.Tmp.held(xs)), y), D.AllIn(rest, D.Rt.cells(D.Tmp.held(xs))), h2)))),
        ndall.hl(rest, ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, D.and.r(D.Mem(D.Rt.cells(D.Tmp.held(xs)), y), D.AllIn(rest, D.Rt.cells(D.Tmp.held(xs))), h2)))

def ndall.fr(ys: List<&2, U32>, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +os: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  +g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs), hin: {D.AllIn(ys, D.Rt.cells(D.Fr.rts(fs, m, sp))) == True{} : Bool}) -> {NdAll(ys, Lst(os, D.Tmp.held(xs), fs, m, sp), m) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      +h2 = hin
      CK.Bo.and_i(D.Nodes(Lst(os, D.Tmp.held(xs), fs, m, sp), m, y), NdAll(rest, Lst(os, D.Tmp.held(xs), fs, m, sp), m),
        nodes.in.r(os, List.append(&2, D.Rt, D.Tmp.held(xs), D.Fr.rts(fs, m, sp)), m, y,
          nodes.in.r(D.Tmp.held(xs), D.Fr.rts(fs, m, sp), m, y,
            root.nodes(D.Fr.rts(fs, m, sp), m, y, D.and.l(D.Mem(D.Rt.cells(D.Fr.rts(fs, m, sp)), y), D.AllIn(rest, D.Rt.cells(D.Fr.rts(fs, m, sp))), h2)))),
        ndall.fr(rest, ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, D.and.r(D.Mem(D.Rt.cells(D.Fr.rts(fs, m, sp)), y), D.AllIn(rest, D.Rt.cells(D.Fr.rts(fs, m, sp))), h2)))

# the live roots' terms, as the copy's roots, keep their checked terms
def rts.of(R: List<&2, D.Rt>, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +os: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  +g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs), +hK: {U32.is_le(290, im) == True{} : Bool}, +hKF: {U32.is_lt(im, fi) == True{} : Bool},
  hR: D.RtsK(True{}, ds, m, im, fi, nx, ks, img, R), hN: {NdAll(D.Rt.cells(R), Lst(os, D.Tmp.held(xs), fs, m, sp), m) == True{} : Bool}) ->
  S.Rts(m, ks, img, im, fi, List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp)), nx, Rs.of(R)):
  match R:
    case Nil{}:
      Unit{}
    case Con{D.Rt{+c, +t}, +rest}:
      (hc0, hr) = hR
      +hc = {hc0 : D.IsK(True{}, ds, m, im, fi, nx, ks, img, c, t)}
      +hn2 = hN
      (tm.is.at(Pg.Term.size(t), True{}, ds, m, im, fi, nx, ks, img, List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp)), c, t, N.le_refl(Pg.Term.size(t)), hc,
         rx.ln(t, ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, hK, hKF, c, hc, ln.live(t, True{}, ds, m, im, fi, nx, ks, img, ps, gc.tbl(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g), Lst(os, D.Tmp.held(xs), fs, m, sp), gc.L(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g), c, hc,
           CK.Bo.and_l(D.Nodes(Lst(os, D.Tmp.held(xs), fs, m, sp), m, c), NdAll(D.Rt.cells(rest), Lst(os, D.Tmp.held(xs), fs, m, sp), m), hn2)))),
       rts.of(rest, ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, hK, hKF, hr, CK.Bo.and_r(D.Nodes(Lst(os, D.Tmp.held(xs), fs, m, sp), m, c), NdAll(D.Rt.cells(rest), Lst(os, D.Tmp.held(xs), fs, m, sp), m), hn2)))

# the temporaries, as the copy's
def Tmps.of(ts: List<&2, D.TmpE>) -> List<&2, S.Tmp>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{D.TmpE{c, h}, rest}:
      Con{S.Tmp{c, Rs.of(h)}, Tmps.of(rest)}

def tmps.cells(ts: List<&2, D.TmpE>) -> {S.Tmp.cells(Tmps.of(ts)) == D.Tmp.cells(ts) : List<&2, U32>}:
  match ts:
    case Nil{}:
      {==}
    case Con{D.TmpE{+c, +h}, +rest}:
      Equal.cong(List<&2, U32>, List<&2, U32>, l => Con{c, l}, S.Tmp.cells(Tmps.of(rest)), D.Tmp.cells(rest), tmps.cells(rest))

def rs.of.app(A: List<&2, D.Rt>, +B: List<&2, D.Rt>) -> {Rs.of(List.append(&2, D.Rt, A, B)) == List.append(&2, S.Rt, Rs.of(A), Rs.of(B)) : List<&2, S.Rt>}:
  match A:
    case Nil{}:
      {==}
    case Con{D.Rt{+c, +t}, +rest}:
      Equal.cong(List<&2, S.Rt>, List<&2, S.Rt>, l => Con{S.Rt{Pg.Term.size(t), c, t}, l}, Rs.of(List.append(&2, D.Rt, rest, B)),
        List.append(&2, S.Rt, Rs.of(rest), Rs.of(B)), rs.of.app(rest, B))

def tmps.held(ts: List<&2, D.TmpE>) -> {S.Tmp.held(Tmps.of(ts)) == Rs.of(D.Tmp.held(ts)) : List<&2, S.Rt>}:
  match ts:
    case Nil{}:
      {==}
    case Con{D.TmpE{+c, +h}, +rest}:
      Equal.trans(List<&2, S.Rt>, List.append(&2, S.Rt, Rs.of(h), S.Tmp.held(Tmps.of(rest))), List.append(&2, S.Rt, Rs.of(h), Rs.of(D.Tmp.held(rest))),
        Rs.of(List.append(&2, D.Rt, h, D.Tmp.held(rest))),
        Equal.cong(List<&2, S.Rt>, List<&2, S.Rt>, l => List.append(&2, S.Rt, Rs.of(h), l), S.Tmp.held(Tmps.of(rest)), Rs.of(D.Tmp.held(rest)), tmps.held(rest)),
        Equal.sym(List<&2, S.Rt>, Rs.of(List.append(&2, D.Rt, h, D.Tmp.held(rest))), List.append(&2, S.Rt, Rs.of(h), Rs.of(D.Tmp.held(rest))), rs.of.app(h, D.Tmp.held(rest))))

def rs.of.cells(R: List<&2, D.Rt>) -> {S.Rt.cells(Rs.of(R)) == D.Rt.cells(R) : List<&2, U32>}:
  match R:
    case Nil{}:
      {==}
    case Con{D.Rt{+c, +t}, +rest}:
      Equal.cong(List<&2, U32>, List<&2, U32>, l => Con{c, l}, S.Rt.cells(Rs.of(rest)), D.Rt.cells(rest), rs.of.cells(rest))

# The kept cells: the own cells of the machine's own kinds out of the pend list
# -----------------------------------------------------------------------------

def KlC(+m: Cr.Cir.Cells, +ps: List<&2, U32>, +c: U32) -> Bool:
  Bool.and(Nat.is_le(19n, U32.to_nat(U32.and(S.Fd(0n, m, c), 63))), Bool.not(D.Mem(ps, c)))

def Kl(k: Nat, +m: Cr.Cir.Cells, +c: U32, +ps: List<&2, U32>) -> List<&2, S.Kc>:
  match k:
    case 0n:
      Nil{}
    case 1n+(+p):
      Bool.pick(List<&2, S.Kc>, KlC(m, ps, c), Con{S.Kc{c, Cr.Cir.Cells.get(m, c)}, Kl(p, m, U32.inc(c), ps)}, Kl(p, m, U32.inc(c), ps))

# AccK's roots stand for their terms
def gc.RS(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +os: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  +g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs)) -> D.RtsK(True{}, ds, m, im, fi, nx, ks, img, GRS(m, os, xs, fs, sp, zs)):
  AC.rtsk.app(True{}, os, List.append(&2, D.Rt, D.Tmp.held(xs), List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)), ds, m, im, fi, nx, ks, img, gc.os(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g),
    AC.rtsk.app(True{}, D.Tmp.held(xs), List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs), ds, m, im, fi, nx, ks, img, gc.hl(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g),
      AC.rtsk.app(True{}, D.Fr.rts(fs, m, sp), zs, ds, m, im, fi, nx, ks, img, AC.frs.rtsk(True{}, ds, m, im, fi, nx, ks, img, ps, fs, sp, gc.frs(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g)),
        gc.zs(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g))))

# a node of a term is no cell of the machine's own kinds
def nd.k19(-ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, -im: U32, -fi: U32, -nx: U32, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>,
  -b: Nat, +c: U32, -G: Type, ex: D.Ex(Bk.Term, v => D.P2(D.IsK(True{}, ds, m, im, fi, nx, ks, img, c, v), N.Le(Pg.Term.size(v), b))),
  h: {Nat.is_le(19n, U32.to_nat(U32.and(S.Fd(0n, m, c), 63))) == True{} : Bool}) -> G:
  +h19 = zom.ex(ds, m, im, fi, nx, ks, img, b, c, ex)
  Empty.absurd(G, N.not_succ_le(U32.to_nat(D.Tg(m, c)), N.le_trans(1n+U32.to_nat(D.Tg(m, c)), 19n, U32.to_nat(D.Tg(m, c)), CK.U.lt(D.Tg(m, c), 19, h19),
    (%Equal.sym(Bool, Nat.is_le(19n, U32.to_nat(U32.and(S.Fd(0n, m, c), 63))), True{}, h) : N.T(_); Unit{}))))

# a kept cell is live
def kc.lv(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +os: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  +g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs), +c: U32, hcv: {CovAt(m, c, GRS(m, os, xs, fs, sp, zs), List.append(&2, U32, D.Fr.cells(fs, m, sp), List.append(&2, U32, D.Tmp.cells(xs), ps))) == True{} : Bool}, +hkl: {KlC(m, ps, c) == True{} : Bool},
  +hnf: {D.Mem(D.Fr.cells(fs, m, sp), c) == False{} : Bool}) -> {Lv(m, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs)), c) == True{} : Bool}:
  D.or.cases(D.Fl(m, c, 1024), Bool.or(D.Nodes(GRS(m, os, xs, fs, sp, zs), m, c), D.Mem(List.append(&2, U32, D.Fr.cells(fs, m, sp), List.append(&2, U32, D.Tmp.cells(xs), ps)), c)), {Lv(m, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs)), c) == True{} : Bool}, hcv,
    e => lv.st(m, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs)), c, e),
    e => D.or.cases(D.Nodes(GRS(m, os, xs, fs, sp, zs), m, c), D.Mem(List.append(&2, U32, D.Fr.cells(fs, m, sp), List.append(&2, U32, D.Tmp.cells(xs), ps)), c), {Lv(m, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs)), c) == True{} : Bool}, e,
      e1 => nd.k19(ds, m, im, fi, nx, ks, img, D.Rts.size(GRS(m, os, xs, fs, sp, zs)), c, {Lv(m, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs)), c) == True{} : Bool},
        nodes.sub(GRS(m, os, xs, fs, sp, zs), ds, m, im, fi, nx, ks, img, c, gc.RS(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g), e1),
        CK.Bo.and_l(Nat.is_le(19n, U32.to_nat(U32.and(S.Fd(0n, m, c), 63))), Bool.not(D.Mem(ps, c)), hkl)),
      e1 => D.or.cases(D.Mem(D.Fr.cells(fs, m, sp), c), D.Mem(List.append(&2, U32, D.Tmp.cells(xs), ps), c), {Lv(m, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs)), c) == True{} : Bool},
        mem.split(D.Fr.cells(fs, m, sp), List.append(&2, U32, D.Tmp.cells(xs), ps), c, e1),
        e2 => CK.Bo.tf({Lv(m, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs)), c) == True{} : Bool}, Equal.trans(Bool, False{}, D.Mem(D.Fr.cells(fs, m, sp), c), True{},
          Equal.sym(Bool, D.Mem(D.Fr.cells(fs, m, sp), c), False{}, hnf), e2)),
        e2 => D.or.cases(D.Mem(D.Tmp.cells(xs), c), D.Mem(ps, c), {Lv(m, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs)), c) == True{} : Bool}, mem.split(D.Tmp.cells(xs), ps, c, e2),
          e3 => lv.y(m, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs)), c, mem.in.r(D.Fr.cells(fs, m, sp), D.Tmp.cells(xs), c, e3)),
          e3 => CK.Bo.tf({Lv(m, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs)), c) == True{} : Bool}, Equal.trans(Bool, False{}, D.Mem(ps, c), True{},
            Equal.sym(Bool, D.Mem(ps, c), False{}, CK.Bo.not_t(D.Mem(ps, c), CK.Bo.and_r(Nat.is_le(19n, U32.to_nat(U32.and(S.Fd(0n, m, c), 63))), Bool.not(D.Mem(ps, c)), hkl))), e3))))))

# an own cell is a cell, and no table cell (it is past the image, past 290)
def own.cell(+c: U32, +im: U32, +fi: U32, +nx: U32, +h1: N.Le(U32.to_nat(fi), U32.to_nat(c)), +h2: N.Le(1n+U32.to_nat(c), U32.to_nat(nx))) ->
  {Cr.Cir.is_cell(c, im, fi, nx) == True{} : Bool}:
  CK.Bo.or_ir(Bool.and(Bool.not(U32.is_zero(c)), U32.is_le(c, im)), Bool.and(U32.is_le(fi, c), U32.is_lt(c, nx)),
    CK.Bo.and_i(U32.is_le(fi, c), U32.is_lt(c, nx), CK.U.le_t(fi, c, h1), CK.U.lt_t(c, nx, h2)))

def own.ntb(+c: U32, +im: U32, +fi: U32, +h1: N.Le(U32.to_nat(fi), U32.to_nat(c)), +hK: {U32.is_le(290, im) == True{} : Bool},
  +hKF: {U32.is_lt(im, fi) == True{} : Bool}) -> {S.Tbc(c) == False{} : Bool}:
  +n290 = bool.case(U32.is_le(c, 290), U32.is_le(c, 290), {U32.is_le(c, 290) == False{} : Bool}, {==},
    e => CK.U.lt_ge(c, fi, {U32.is_le(c, 290) == False{} : Bool},
      CK.U.le_lt(c, im, fi, CK.U.le_t(c, im, N.le_trans(U32.to_nat(c), U32.to_nat(290), U32.to_nat(im), CK.U.le(c, 290, e), CK.U.le(290, im, hK))), hKF),
      CK.U.le_t(fi, c, h1)),
    e => e)
  %Equal.sym(Bool, U32.is_le(c, 290), False{}, n290) : {Bool.and(U32.is_le(272, c), _) == False{} : Bool}
  and.f(U32.is_le(272, c))

def kc.ok(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +os: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  +g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs), +hK: {U32.is_le(290, im) == True{} : Bool}, +hKF: {U32.is_lt(im, fi) == True{} : Bool}, +c: U32,
  +hcv: {CovAt(m, c, GRS(m, os, xs, fs, sp, zs), List.append(&2, U32, D.Fr.cells(fs, m, sp), List.append(&2, U32, D.Tmp.cells(xs), ps))) == True{} : Bool}, +hkl: {KlC(m, ps, c) == True{} : Bool},
  +h1: N.Le(U32.to_nat(fi), U32.to_nat(c)), +h2: N.Le(1n+U32.to_nat(c), U32.to_nat(nx)), +h2f: N.Le(1n+U32.to_nat(c), Nat.add(U32.to_nat(fi), Nat.sub(U32.to_nat(nx), U32.to_nat(fi))))) ->
  {S.Kc.ok(im, fi, List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp)), nx, D.Fr.cells(fs, m, sp), c, Cr.Cir.Cells.get(m, c)) == True{} : Bool}:
  +K19 = Nat.is_le(19n, U32.to_nat(U32.and(Cr.Cir.Cell.get(0n, Cr.Cir.Cells.get(m, c)), 63)))
  +A1 = Bool.and(S.Al(im, fi, List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp)), nx, c), K19)
  +B1 = Bool.and(S.Has(D.Fr.cells(fs, m, sp), c), Bool.and(Bool.and(U32.is_le(fi, c), U32.is_lt(c, nx)), K19))
  +h19 = CK.Bo.and_l(Nat.is_le(19n, U32.to_nat(U32.and(S.Fd(0n, m, c), 63))), Bool.not(D.Mem(ps, c)), hkl)
  bool.case(S.Has(D.Fr.cells(fs, m, sp), c), S.Has(D.Fr.cells(fs, m, sp), c), {Bool.or(A1, B1) == True{} : Bool}, {==},
    e => CK.Bo.or_ir(A1, B1, CK.Bo.and_i(S.Has(D.Fr.cells(fs, m, sp), c), Bool.and(Bool.and(U32.is_le(fi, c), U32.is_lt(c, nx)), K19), e,
      CK.Bo.and_i(Bool.and(U32.is_le(fi, c), U32.is_lt(c, nx)), K19,
        CK.Bo.and_i(U32.is_le(fi, c), U32.is_lt(c, nx), CK.U.le_t(fi, c, h1), CK.U.lt_t(c, nx, h2)), h19))),
    +e => CK.Bo.or_il(A1, B1, CK.Bo.and_i(S.Al(im, fi, List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp)), nx, c), K19,
      CK.Bo.and_i(Cr.Cir.is_cell(c, im, fi, nx), Bool.and(Bool.not(S.Has(List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp)), c)), Bool.not(S.Tbc(c))), own.cell(c, im, fi, nx, h1, h2),
        CK.Bo.and_i(Bool.not(S.Has(List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp)), c)), Bool.not(S.Tbc(c)),
          CK.Bo.not_i(S.Has(List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp)), c), (%Equal.sym(Bool, S.Has(List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp)), c), Bool.or(S.Has(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), c), S.Has(D.Fr.cells(fs, m, sp), c)), has.app(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp), c)) :
            {_ == False{} : Bool}; or.ff(S.Has(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), c), S.Has(D.Fr.cells(fs, m, sp), c),
              gb.not(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs)), c, kc.lv(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, c, hcv, hkl,
                {(%Equal.sym(Bool, D.Mem(D.Fr.cells(fs, m, sp), c), S.Has(D.Fr.cells(fs, m, sp), c), mem.has(D.Fr.cells(fs, m, sp), c)) : {_ == False{} : Bool}; e) :
                  {D.Mem(D.Fr.cells(fs, m, sp), c) == False{} : Bool}})), e))),
          CK.Bo.not_i(S.Tbc(c), own.ntb(c, im, fi, h1, hK, hKF)))),
      h19)))

def kcs.kl.b(b: Bool, +q: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +os: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  +g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs), +hK: {U32.is_le(290, im) == True{} : Bool}, +hKF: {U32.is_lt(im, fi) == True{} : Bool}, +c: U32,
  eb: {KlC(m, ps, c) == b : Bool}, +hcv: {CovAt(m, c, GRS(m, os, xs, fs, sp, zs), List.append(&2, U32, D.Fr.cells(fs, m, sp), List.append(&2, U32, D.Tmp.cells(xs), ps))) == True{} : Bool},
  +h1: N.Le(U32.to_nat(fi), U32.to_nat(c)), +hw: N.Le(Nat.add(U32.to_nat(c), 1n+q), U32.to_nat(nx)),
  ih: S.Kcs(m, im, fi, List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp)), nx, D.Fr.cells(fs, m, sp), Kl(q, m, U32.inc(c), ps))) ->
  S.Kcs(m, im, fi, List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp)), nx, D.Fr.cells(fs, m, sp),
    Bool.pick(List<&2, S.Kc>, b, Con{S.Kc{c, Cr.Cir.Cells.get(m, c)}, Kl(q, m, U32.inc(c), ps)}, Kl(q, m, U32.inc(c), ps))):
  match b:
    case True{}:
      +h2 = w.lt(c, q, nx, hw)
      +efn = D.add.sub(U32.to_nat(fi), U32.to_nat(nx), CK.U.le(fi, nx, gc.fn(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g)))
      ({==}, (kc.ok(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, hK, hKF, c, hcv, eb, h1, h2,
        N.le_rw_r(1n+U32.to_nat(c), U32.to_nat(nx), Nat.add(U32.to_nat(fi), Nat.sub(U32.to_nat(nx), U32.to_nat(fi))), Equal.sym(Nat, Nat.add(U32.to_nat(fi), Nat.sub(U32.to_nat(nx), U32.to_nat(fi))), U32.to_nat(nx), efn), h2)), ih))
    case False{}:
      ih

def kcs.kl(k: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +os: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  +g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs), +hK: {U32.is_le(290, im) == True{} : Bool}, +hKF: {U32.is_lt(im, fi) == True{} : Bool}, +c: U32,
  hcov: {D.Cov(k, m, c, GRS(m, os, xs, fs, sp, zs), List.append(&2, U32, D.Fr.cells(fs, m, sp), List.append(&2, U32, D.Tmp.cells(xs), ps))) == True{} : Bool}, +h1: N.Le(U32.to_nat(fi), U32.to_nat(c)),
  +hw: N.Le(Nat.add(U32.to_nat(c), k), U32.to_nat(nx))) -> S.Kcs(m, im, fi, List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp)), nx, D.Fr.cells(fs, m, sp), Kl(k, m, c, ps)):
  match k:
    case 0n:
      Unit{}
    case 1n+(+q):
      +hc2 = hcov
      +ei = D.u.inc(c, nx, w.lt(c, q, nx, hw))
      kcs.kl.b(KlC(m, ps, c), q, ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, hK, hKF, c, {==},
        D.and.l(CovAt(m, c, GRS(m, os, xs, fs, sp, zs), List.append(&2, U32, D.Fr.cells(fs, m, sp), List.append(&2, U32, D.Tmp.cells(xs), ps))), D.Cov(q, m, U32.inc(c), GRS(m, os, xs, fs, sp, zs), List.append(&2, U32, D.Fr.cells(fs, m, sp), List.append(&2, U32, D.Tmp.cells(xs), ps))), hc2), h1, hw,
        kcs.kl(q, ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, hK, hKF, U32.inc(c),
          D.and.r(CovAt(m, c, GRS(m, os, xs, fs, sp, zs), List.append(&2, U32, D.Fr.cells(fs, m, sp), List.append(&2, U32, D.Tmp.cells(xs), ps))), D.Cov(q, m, U32.inc(c), GRS(m, os, xs, fs, sp, zs), List.append(&2, U32, D.Fr.cells(fs, m, sp), List.append(&2, U32, D.Tmp.cells(xs), ps))), hc2),
          N.le_trans(U32.to_nat(fi), U32.to_nat(c), U32.to_nat(U32.inc(c)), h1,
            N.le_rw_r(U32.to_nat(c), 1n+U32.to_nat(c), U32.to_nat(U32.inc(c)), Equal.sym(Nat, U32.to_nat(U32.inc(c)), 1n+U32.to_nat(c), ei),
              N.le_succ(U32.to_nat(c), U32.to_nat(c), N.le_refl(U32.to_nat(c))))),
          w.next(c, q, nx, hw)))

# a register below the list's length holds its defaulting read
def get.some(xs: List<&2, U32>, r: Nat, h: {Nat.is_lt(r, List.length(&2, U32, xs)) == True{} : Bool}) ->
  {List.get(&2, U32, xs, r) == Some{T.tm.reg(xs, r)} : Maybe<&2, U32>}:
  match xs r:
    case Nil{} 0n:
      CK.Bo.tf({None{} == Some{0} : Maybe<&2, U32>}, h)
    case Nil{} 1n+p:
      CK.Bo.tf({None{} == Some{0} : Maybe<&2, U32>}, h)
    case Con{x, rest} 0n:
      {==}
    case Con{x, rest} 1n+p:
      get.some(rest, p, h)

def reg.of(+rg: List<&2, U32>, +r: Nat, +v: U32, +hlen: {List.length(&2, U32, rg) == 63n : Nat},
  +hr: {Nat.is_lt(r, 63n) == True{} : Bool}, er: {T.tm.reg(rg, r) == v : U32}) ->
  {List.get(&2, U32, rg, r) == Some{v} : Maybe<&2, U32>}:
  +h = {(%Equal.sym(Nat, List.length(&2, U32, rg), 63n, hlen) : {Nat.is_lt(r, _) == True{} : Bool}; hr) : {Nat.is_lt(r, List.length(&2, U32, rg)) == True{} : Bool}}
  Equal.trans(Maybe<&2, U32>, List.get(&2, U32, rg, r), Some{T.tm.reg(rg, r)}, Some{v}, get.some(rg, r, h),
    Equal.cong(U32, Maybe<&2, U32>, x => Some{x}, T.tm.reg(rg, r), v, er))

# the register writes of a copy give the machine's Same
def same.output(+regs: List<&2, U32>, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, keep: List<&2, Nat>,
  +rg: List<&2, U32>, +ms: Cr.Cir.Cells, +nx: U32, +pg: U32, +ups: List<&2, S.Up>, +scr: List<&2, Nat>, +ys: List<&2, Nat>,
  +hl: {List.length(&2, U32, regs) == 63n : Nat}, +hu: {S.Ups.in(ups, scr) == True{} : Bool},
  +hs: {Sub.nat(scr, ys) == True{} : Bool}, +hk: {D.Disj(keep, ys) == True{} : Bool},
  erg: {rg == S.Ups(ups, S.Rg.ex(63n, regs, 0n)) : List<&2, U32>}) ->
  D.Same(regs, fi, im, lim, inp, keep, S.S(rg, ms, nx, fi, im, pg, lim, inp)):
  +er = Equal.cong(List<&2, U32>, List<&2, U32>, xs => S.Ups(ups, xs), S.Rg.ex(63n, regs, 0n), regs, rg.ex.all(regs, hl))
  +erg2 = Equal.trans(List<&2, U32>, rg, S.Ups(ups, S.Rg.ex(63n, regs, 0n)), S.Ups(ups, regs), erg, er)
  +hl2 = Equal.trans(Nat, List.length(&2, U32, rg), List.length(&2, U32, S.Ups(ups, regs)), 63n,
    Equal.cong(List<&2, U32>, Nat, xs => List.length(&2, U32, xs), rg, S.Ups(ups, regs), erg2),
    Equal.trans(Nat, List.length(&2, U32, S.Ups(ups, regs)), List.length(&2, U32, regs), 63n, ups.len(ups, regs), hl))
  +hk2 = {(%Equal.sym(List<&2, U32>, rg, S.Ups(ups, regs), erg2) : D.Kept(regs, _, keep); kept.ups(keep, regs, ups, scr, ys, hu, hs, hk)) : D.Kept(regs, rg, keep)}
  ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, (hl2, hk2)))))))

# an outcome that Ok allows has ended
def ok.ends(o: Cr.Cir.Out, +F: U32, +K: U32, +L: U32, +I: List<&2, Word(8n)>, +B: Nat,
  -Q: List<&2, U32> -> Cr.Cir.Cells -> U32 -> U32 -> Type, h: S.Ok(o, F, K, L, I, B, Q)) -> D.Ends(o):
  match o:
    case Cr.Cir.Out.next{st}:
      Unit{}
    case Cr.Cir.Out.halt{s, st}:
      Empty.absurd(D.Ends(Cr.Cir.Out.halt{s, st}), h)
    case Cr.Cir.Out.out_of_memory{}:
      Unit{}
    case Cr.Cir.Out.trap{}:
      Empty.absurd(D.Ends(Cr.Cir.Out.trap{}), h)
    case Cr.Cir.Out.not_done{}:
      Empty.absurd(D.Ends(Cr.Cir.Out.not_done{}), h)

# Pre, from HS and AccK
# ---------------------
#
# The copy's view of a move's state: the garbage P = GP (the own cells that
# are not live), the pend list ps and the zombie sizes Zl; the cells E that it
# may not read, the frames; the roots, the owned ones and the frames' terms;
# the temporaries, the move's (Tmps.of); the kept cells Kl; the bound
# B0 = Acc.need.

# the table's cells, whole (Tbl), as the copy reads them (Tb)
def tb.go(cs: List<&2, Cr.Cir.Cell>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +at: U32, h: D.Tbl.go(cs, m, im, fi, nx, at)) ->
  S.Tb.go(m, at, cs):
  match cs:
    case Nil{}:
      Unit{}
    case Con{+c, +rest}:
      (_, h1) = h
      (hg, hr) = h1
      (hg, tb.go(rest, m, im, fi, nx, U32.inc(at), hr))

def tb.of(+m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, h: D.Tbl(m, im, fi, nx)) -> S.Tb(m):
  tb.go(Mc.Img.table([]), m, im, fi, nx, 272, h)

# a cell of Y (a frame or a temporary) is one of the machine's own
def y.own(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +os: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  +g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs), +q: U32, hq: {D.Mem(Yc(fs, m, sp, D.Tmp.cells(xs)), q) == True{} : Bool}) ->
  {D.Own(fi, nx, q) == True{} : Bool}:
  D.or.cases(D.Mem(D.Fr.cells(fs, m, sp), q), D.Mem(D.Tmp.cells(xs), q), {D.Own(fi, nx, q) == True{} : Bool},
    mem.split(D.Fr.cells(fs, m, sp), D.Tmp.cells(xs), q, hq),
    e => frn.own(ps, fi, nx, m, q, fr.nps(fs, True{}, ds, m, im, fi, nx, ks, img, ps, sp, q, gc.frs(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g), e)),
    e => tc.own(m, fi, nx, ps, GRS(m, os, xs, fs, sp, zs), q,
      tmp.get(xs, m, fi, nx, ps, GRS(m, os, xs, fs, sp, zs), q, gc.tmp(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g), e)))

# A ++ B holds each cell of A, and each of B
def allin.l(A: List<&2, U32>, +B: List<&2, U32>) -> {D.AllIn(A, List.append(&2, U32, A, B)) == True{} : Bool}:
  match A:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      CK.Bo.and_i(D.Mem(Con{x, List.append(&2, U32, rest, B)}, x), D.AllIn(rest, Con{x, List.append(&2, U32, rest, B)}),
        CK.Bo.or_il(U32.is_eq(x, x), D.Mem(List.append(&2, U32, rest, B), x), CK.U.eq_refl(x)),
        D.allin.cons(rest, x, List.append(&2, U32, rest, B), allin.l(rest, B)))

def allin.r(A: List<&2, U32>, +B: List<&2, U32>) -> {D.AllIn(B, List.append(&2, U32, A, B)) == True{} : Bool}:
  match A:
    case Nil{}:
      D.allin.refl(B)
    case Con{+x, +rest}:
      D.allin.cons(B, x, List.append(&2, U32, rest, B), allin.r(rest, B))

# own cells, each a frame or a temporary (live): out of the garbage, as Ex.ok asks
def exok.y(ys: List<&2, U32>, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +os: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  +g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs), hin: {D.AllIn(ys, Yc(fs, m, sp, D.Tmp.cells(xs))) == True{} : Bool}) ->
  {S.Ex.ok(ys, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), fi, nx) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      +P = Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs)))
      +Y = Yc(fs, m, sp, D.Tmp.cells(xs))
      +h2 = hin
      +hy = CK.Bo.and_l(D.Mem(Y, y), D.AllIn(rest, Y), h2)
      CK.Bo.and_i(Bool.and(Bool.not(S.Has(P, y)), Bool.and(U32.is_le(fi, y), U32.is_lt(y, nx))), S.Ex.ok(rest, P, fi, nx),
        CK.Bo.and_i(Bool.not(S.Has(P, y)), Bool.and(U32.is_le(fi, y), U32.is_lt(y, nx)),
          CK.Bo.not_i(S.Has(P, y), gb.not(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Y, y,
            lv.y(m, Lst(os, D.Tmp.held(xs), fs, m, sp), Y, y, hy))),
          y.own(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, y, hy)),
        exok.y(rest, ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, CK.Bo.and_r(D.Mem(Y, y), D.AllIn(rest, Y), h2)))

# a node of the live roots os ++ (H ++ frt) is a node of the copy's roots (os ++ frt) ++ H
def nd.perm(+os: List<&2, D.Rt>, +H: List<&2, D.Rt>, +frt: List<&2, D.Rt>, +m: Cr.Cir.Cells, +x: U32,
  h: {D.Nodes(List.append(&2, D.Rt, os, List.append(&2, D.Rt, H, frt)), m, x) == True{} : Bool}) ->
  {S.Nodes(Rs.of(List.append(&2, D.Rt, List.append(&2, D.Rt, os, frt), H)), m, x) == True{} : Bool}:
  %nodes.eq(List.append(&2, D.Rt, List.append(&2, D.Rt, os, frt), H), m, x) : {_ == True{} : Bool}
  D.or.cases(D.Nodes(os, m, x), D.Nodes(List.append(&2, D.Rt, H, frt), m, x), {D.Nodes(List.append(&2, D.Rt, List.append(&2, D.Rt, os, frt), H), m, x) == True{} : Bool},
    nodes.split(os, List.append(&2, D.Rt, H, frt), m, x, h),
    e => nodes.in.l(List.append(&2, D.Rt, os, frt), H, m, x, nodes.in.l(os, frt, m, x, e)),
    e => D.or.cases(D.Nodes(H, m, x), D.Nodes(frt, m, x), {D.Nodes(List.append(&2, D.Rt, List.append(&2, D.Rt, os, frt), H), m, x) == True{} : Bool},
      nodes.split(H, frt, m, x, e),
      e1 => nodes.in.r(List.append(&2, D.Rt, os, frt), H, m, x, e1),
      e1 => nodes.in.l(List.append(&2, D.Rt, os, frt), H, m, x, nodes.in.r(os, frt, m, x, e1))))

# a cell of frc ++ cs is one of cs ++ frc
def my.perm(+frc: List<&2, U32>, +cs: List<&2, U32>, +x: U32, h: {D.Mem(List.append(&2, U32, frc, cs), x) == True{} : Bool}) ->
  {S.Has(List.append(&2, U32, cs, frc), x) == True{} : Bool}:
  %mem.has(List.append(&2, U32, cs, frc), x) : {_ == True{} : Bool}
  D.or.cases(D.Mem(frc, x), D.Mem(cs, x), {D.Mem(List.append(&2, U32, cs, frc), x) == True{} : Bool}, mem.split(frc, cs, x, h),
    e => mem.in.r(cs, frc, x, e),
    e => mem.in.l(cs, frc, x, e))

# the live roots and cells (os ++ (H ++ frt), frc ++ cs) and the garbage P
# cover the own cells: so do the copy's roots (os ++ frt) ++ H, its garbage
# and its cells cs ++ frc
def cv.of(k: Nat, +m: Cr.Cir.Cells, +c: U32, +os: List<&2, D.Rt>, +H: List<&2, D.Rt>, +frt: List<&2, D.Rt>, +frc: List<&2, U32>,
  +cs: List<&2, U32>, +P: List<&2, U32>,
  h: {D.Cov(k, m, c, List.append(&2, D.Rt, os, List.append(&2, D.Rt, H, frt)), List.append(&2, U32, List.append(&2, U32, frc, cs), P)) == True{} : Bool}) ->
  {S.Cv(k, m, c, P, Rs.of(List.append(&2, D.Rt, List.append(&2, D.Rt, os, frt), H)), List.append(&2, U32, cs, frc)) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+(+q):
      +L = List.append(&2, D.Rt, os, List.append(&2, D.Rt, H, frt))
      +Y = List.append(&2, U32, frc, cs)
      +A = Rs.of(List.append(&2, D.Rt, List.append(&2, D.Rt, os, frt), H))
      +Z = List.append(&2, U32, cs, frc)
      +h2 = h
      +R = Bool.or(S.Has(P, c), Bool.or(S.Nodes(A, m, c), S.Has(Z, c)))
      +hc = CK.Bo.and_l(CovAt(m, c, L, List.append(&2, U32, Y, P)), D.Cov(q, m, U32.inc(c), L, List.append(&2, U32, Y, P)), h2)
      +cell = D.or.cases(D.Fl(m, c, 1024), Bool.or(D.Nodes(L, m, c), D.Mem(List.append(&2, U32, Y, P), c)), {Bool.or(S.Stc(m, c), R) == True{} : Bool}, hc,
        e => CK.Bo.or_il(S.Stc(m, c), R, e),
        e => CK.Bo.or_ir(S.Stc(m, c), R, D.or.cases(D.Nodes(L, m, c), D.Mem(List.append(&2, U32, Y, P), c), {R == True{} : Bool}, e,
          e1 => CK.Bo.or_ir(S.Has(P, c), Bool.or(S.Nodes(A, m, c), S.Has(Z, c)), CK.Bo.or_il(S.Nodes(A, m, c), S.Has(Z, c), nd.perm(os, H, frt, m, c, e1))),
          e1 => D.or.cases(D.Mem(Y, c), D.Mem(P, c), {R == True{} : Bool}, mem.split(Y, P, c, e1),
            e2 => CK.Bo.or_ir(S.Has(P, c), Bool.or(S.Nodes(A, m, c), S.Has(Z, c)), CK.Bo.or_ir(S.Nodes(A, m, c), S.Has(Z, c), my.perm(frc, cs, c, e2))),
            e2 => CK.Bo.or_il(S.Has(P, c), Bool.or(S.Nodes(A, m, c), S.Has(Z, c)), (%mem.has(P, c) : {_ == True{} : Bool}; e2))))))
      CK.Bo.and_i(Bool.or(S.Stc(m, c), R), S.Cv(q, m, U32.inc(c), P, A, Z), cell,
        cv.of(q, m, U32.inc(c), os, H, frt, frc, cs, P, CK.Bo.and_r(CovAt(m, c, L, List.append(&2, U32, Y, P)), D.Cov(q, m, U32.inc(c), L, List.append(&2, U32, Y, P)), h2)))

# the two kits' closures agree
def static.eq(ys: List<&2, U32>, +m: Cr.Cir.Cells) -> {D.All.static(ys, m) == S.All.static(ys, m) : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      %static.eq(rest, m) : {Bool.and(D.Fl(m, y, 1024), D.All.static(rest, m)) == Bool.and(S.Stc(m, y), _) : Bool}
      {==}

def held.eq(ys: List<&2, U32>, +m: Cr.Cir.Cells, +cs: List<&2, U32>, +hc: List<&2, U32>) ->
  {D.All.held(ys, m, cs, hc) == S.All.held(ys, m, cs, hc) : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      %held.eq(rest, m, cs, hc) : {Bool.and(Bool.or(D.Fl(m, y, 1024), Bool.or(D.Mem(cs, y), D.Mem(hc, y))), D.All.held(rest, m, cs, hc)) ==
        Bool.and(Bool.or(S.Stc(m, y), Bool.or(S.Has(cs, y), S.Has(hc, y))), _) : Bool}
      %mem.has(cs, y) : {Bool.and(Bool.or(D.Fl(m, y, 1024), Bool.or(D.Mem(cs, y), D.Mem(hc, y))), D.All.held(rest, m, cs, hc)) ==
        Bool.and(Bool.or(S.Stc(m, y), Bool.or(_, S.Has(hc, y))), D.All.held(rest, m, cs, hc)) : Bool}
      %mem.has(hc, y) : {Bool.and(Bool.or(D.Fl(m, y, 1024), Bool.or(D.Mem(cs, y), D.Mem(hc, y))), D.All.held(rest, m, cs, hc)) ==
        Bool.and(Bool.or(S.Stc(m, y), Bool.or(D.Mem(cs, y), _)), D.All.held(rest, m, cs, hc)) : Bool}
      {==}

def clo.at.eq(+m: Cr.Cir.Cells, +c: U32, +ps: List<&2, U32>, +cs: List<&2, U32>, +hc: List<&2, U32>) ->
  {D.Clo.at(m, c, ps, cs, hc) == S.Clo.at(m, c, ps, cs, hc) : Bool}:
  %fs.ps(m, ps, c) : {D.Clo.at(m, c, ps, cs, hc) ==
    Bool.and(Bool.or(Bool.not(S.Stc(m, c)), S.All.static(_, m)), Bool.or(Bool.not(S.Has(cs, c)), S.All.held(_, m, cs, hc))) : Bool}
  %static.eq(D.Fs(m, ps, c), m) : {D.Clo.at(m, c, ps, cs, hc) ==
    Bool.and(Bool.or(Bool.not(S.Stc(m, c)), _), Bool.or(Bool.not(S.Has(cs, c)), S.All.held(D.Fs(m, ps, c), m, cs, hc))) : Bool}
  %held.eq(D.Fs(m, ps, c), m, cs, hc) : {D.Clo.at(m, c, ps, cs, hc) ==
    Bool.and(Bool.or(Bool.not(S.Stc(m, c)), D.All.static(D.Fs(m, ps, c), m)), Bool.or(Bool.not(S.Has(cs, c)), _)) : Bool}
  %mem.has(cs, c) : {D.Clo.at(m, c, ps, cs, hc) ==
    Bool.and(Bool.or(Bool.not(S.Stc(m, c)), D.All.static(D.Fs(m, ps, c), m)), Bool.or(Bool.not(_), D.All.held(D.Fs(m, ps, c), m, cs, hc))) : Bool}
  {==}

# AccK's closure is the copy's, for any cells E
def clo.of(n: Nat, +m: Cr.Cir.Cells, +c: U32, +ps: List<&2, U32>, +cs: List<&2, U32>, +hc: List<&2, U32>, +E: List<&2, U32>,
  h: {D.Clo(n, m, c, ps, cs, hc) == True{} : Bool}) -> {S.Clo(n, m, c, ps, cs, hc, E) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      +h2 = h
      CK.Bo.and_i(Bool.or(S.Has(E, c), S.Clo.at(m, c, ps, cs, hc)), S.Clo(p, m, U32.inc(c), ps, cs, hc, E),
        CK.Bo.or_ir(S.Has(E, c), S.Clo.at(m, c, ps, cs, hc),
          (%clo.at.eq(m, c, ps, cs, hc) : {_ == True{} : Bool}; CK.Bo.and_l(D.Clo.at(m, c, ps, cs, hc), D.Clo(p, m, U32.inc(c), ps, cs, hc), h2))),
        clo.of(p, m, U32.inc(c), ps, cs, hc, E, CK.Bo.and_r(D.Clo.at(m, c, ps, cs, hc), D.Clo(p, m, U32.inc(c), ps, cs, hc), h2)))

# S + ((A + (B + C)) + ((F + X) + P)) = (S + (A + (B + (C + (F + X))))) + P
def bound.arith(+S0: Nat, +A: Nat, +B: Nat, +C: Nat, +F: Nat, +X: Nat, +P: Nat) ->
  {Nat.add(S0, Nat.add(Nat.add(A, Nat.add(B, C)), Nat.add(Nat.add(F, X), P))) == Nat.add(Nat.add(S0, Nat.add(A, Nat.add(B, Nat.add(C, Nat.add(F, X))))), P) : Nat}:
  +FX = Nat.add(F, X)
  +RHS = Nat.add(Nat.add(S0, Nat.add(A, Nat.add(B, Nat.add(C, FX)))), P)
  %Equal.sym(Nat, Nat.add(Nat.add(A, Nat.add(B, C)), Nat.add(FX, P)), Nat.add(A, Nat.add(Nat.add(B, C), Nat.add(FX, P))), N.add_assoc(A, Nat.add(B, C), Nat.add(FX, P))) :
    {Nat.add(S0, _) == RHS : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(B, C), Nat.add(FX, P)), Nat.add(B, Nat.add(C, Nat.add(FX, P))), N.add_assoc(B, C, Nat.add(FX, P))) :
    {Nat.add(S0, Nat.add(A, _)) == RHS : Nat}
  %N.add_assoc(C, FX, P) : {Nat.add(S0, Nat.add(A, Nat.add(B, _))) == RHS : Nat}
  %N.add_assoc(B, Nat.add(C, FX), P) : {Nat.add(S0, Nat.add(A, _)) == RHS : Nat}
  %N.add_assoc(A, Nat.add(B, Nat.add(C, FX)), P) : {Nat.add(S0, _) == RHS : Nat}
  Equal.sym(Nat, Nat.add(Nat.add(S0, Nat.add(A, Nat.add(B, Nat.add(C, FX)))), P), Nat.add(S0, Nat.add(Nat.add(A, Nat.add(B, Nat.add(C, FX))), P)),
    N.add_assoc(S0, Nat.add(A, Nat.add(B, Nat.add(C, FX))), P))

# the own cells are at most what Acc counts, and the garbage
def pre.bound(+m: Cr.Cir.Cells, +nx: U32, +fi: U32, +os: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +fs: List<&2, D.AF>, +sp: U32,
  +hfn: {U32.is_le(fi, nx) == True{} : Bool}) ->
  N.Le(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), Nat.add(D.Acc.need(m, nx, fi, os, xs, sp, fs), List.length(&2, U32, GP(m, nx, fi, os, xs, fs, sp)))):
  +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
  +hl = D.Tmp.held(xs)
  +frt = D.Fr.rts(fs, m, sp)
  +frc = D.Fr.cells(fs, m, sp)
  +cs = D.Tmp.cells(xs)
  +P = GP(m, nx, fi, os, xs, fs, sp)
  +efn = D.add.sub(U32.to_nat(fi), U32.to_nat(nx), CK.U.le(fi, nx, hfn))
  +hw = N.le_rw_l(U32.to_nat(nx), Nat.add(U32.to_nat(fi), n), U32.to_nat(nx), Equal.sym(Nat, Nat.add(U32.to_nat(fi), n), U32.to_nat(nx), efn), N.le_refl(U32.to_nat(nx)))
  +c1 = AC.cov.count(n, m, fi, GL(m, os, xs, fs, sp), List.append(&2, U32, GY(m, xs, fs, sp), P), nx,
    cov.live(n, m, nx, fi, os, xs, fs, sp, hfn, fi, N.le_refl(U32.to_nat(fi)), hw), hw)
  +eR = Equal.trans(Nat, D.Rts.size(List.append(&2, D.Rt, os, List.append(&2, D.Rt, hl, frt))), Nat.add(D.Rts.size(os), D.Rts.size(List.append(&2, D.Rt, hl, frt))),
    Nat.add(D.Rts.size(os), Nat.add(D.Rts.size(hl), D.Rts.size(frt))), AC.rts.size.app(os, List.append(&2, D.Rt, hl, frt)),
    Equal.cong(Nat, Nat, w => Nat.add(D.Rts.size(os), w), D.Rts.size(List.append(&2, D.Rt, hl, frt)), Nat.add(D.Rts.size(hl), D.Rts.size(frt)), AC.rts.size.app(hl, frt)))
  +eL = Equal.trans(Nat, List.length(&2, U32, List.append(&2, U32, List.append(&2, U32, frc, cs), P)),
    Nat.add(List.length(&2, U32, List.append(&2, U32, frc, cs)), List.length(&2, U32, P)),
    Nat.add(Nat.add(List.length(&2, U32, frc), List.length(&2, D.TmpE, xs)), List.length(&2, U32, P)),
    AC.len.app(List.append(&2, U32, frc, cs), P),
    Equal.cong(Nat, Nat, w => Nat.add(w, List.length(&2, U32, P)), List.length(&2, U32, List.append(&2, U32, frc, cs)),
      Nat.add(List.length(&2, U32, frc), List.length(&2, D.TmpE, xs)),
      Equal.trans(Nat, List.length(&2, U32, List.append(&2, U32, frc, cs)), Nat.add(List.length(&2, U32, frc), List.length(&2, U32, cs)),
        Nat.add(List.length(&2, U32, frc), List.length(&2, D.TmpE, xs)), AC.len.app(frc, cs),
        Equal.cong(Nat, Nat, w => Nat.add(List.length(&2, U32, frc), w), List.length(&2, U32, cs), List.length(&2, D.TmpE, xs), AC.tmp.cells.len(xs)))))
  +RG = D.Rts.size(List.append(&2, D.Rt, os, List.append(&2, D.Rt, hl, frt)))
  +LY = List.length(&2, U32, List.append(&2, U32, List.append(&2, U32, frc, cs), P))
  +R3 = Nat.add(D.Rts.size(os), Nat.add(D.Rts.size(hl), D.Rts.size(frt)))
  +L3 = Nat.add(Nat.add(List.length(&2, U32, frc), List.length(&2, D.TmpE, xs)), List.length(&2, U32, P))
  +e1 = Equal.trans(Nat, Nat.add(D.Stat(n, m, fi), Nat.add(RG, LY)), Nat.add(D.Stat(n, m, fi), Nat.add(R3, LY)), Nat.add(D.Stat(n, m, fi), Nat.add(R3, L3)),
    Equal.cong(Nat, Nat, w => Nat.add(D.Stat(n, m, fi), Nat.add(w, LY)), RG, R3, eR),
    Equal.cong(Nat, Nat, w => Nat.add(D.Stat(n, m, fi), Nat.add(R3, w)), LY, L3, eL))
  N.le_rw_r(n, Nat.add(D.Stat(n, m, fi), Nat.add(R3, L3)), Nat.add(D.Acc.need(m, nx, fi, os, xs, sp, fs), List.length(&2, U32, P)),
    bound.arith(D.Stat(n, m, fi), D.Rts.size(os), D.Rts.size(hl), D.Rts.size(frt), List.length(&2, U32, frc), List.length(&2, D.TmpE, xs), List.length(&2, U32, P)),
    N.le_rw_r(n, Nat.add(D.Stat(n, m, fi), Nat.add(RG, LY)), Nat.add(D.Stat(n, m, fi), Nat.add(R3, L3)), e1, c1))

# the temporaries' cells and held terms of A ++ B
def tmp.cells.app(A: List<&2, D.TmpE>, +B: List<&2, D.TmpE>) ->
  {D.Tmp.cells(List.append(&2, D.TmpE, A, B)) == List.append(&2, U32, D.Tmp.cells(A), D.Tmp.cells(B)) : List<&2, U32>}:
  match A:
    case Nil{}:
      {==}
    case Con{D.TmpE{+c, +h}, +rest}:
      Equal.cong(List<&2, U32>, List<&2, U32>, l => Con{c, l}, D.Tmp.cells(List.append(&2, D.TmpE, rest, B)),
        List.append(&2, U32, D.Tmp.cells(rest), D.Tmp.cells(B)), tmp.cells.app(rest, B))

def tmp.held.app(A: List<&2, D.TmpE>, +B: List<&2, D.TmpE>) ->
  {D.Tmp.held(List.append(&2, D.TmpE, A, B)) == List.append(&2, D.Rt, D.Tmp.held(A), D.Tmp.held(B)) : List<&2, D.Rt>}:
  match A:
    case Nil{}:
      {==}
    case Con{D.TmpE{+c, +h}, +rest}:
      %Equal.sym(List<&2, D.Rt>, List.append(&2, D.Rt, List.append(&2, D.Rt, h, D.Tmp.held(rest)), D.Tmp.held(B)),
        List.append(&2, D.Rt, h, List.append(&2, D.Rt, D.Tmp.held(rest), D.Tmp.held(B))), AC.app.assoc(h, D.Tmp.held(rest), D.Tmp.held(B))) :
        {List.append(&2, D.Rt, h, D.Tmp.held(List.append(&2, D.TmpE, rest, B))) == _ : List<&2, D.Rt>}
      Equal.cong(List<&2, D.Rt>, List<&2, D.Rt>, l => List.append(&2, D.Rt, h, l), D.Tmp.held(List.append(&2, D.TmpE, rest, B)),
        List.append(&2, D.Rt, D.Tmp.held(rest), D.Tmp.held(B)), tmp.held.app(rest, B))

# a K.arg cell (tag 41) is no frame (tags 32 to 40)
def karg.nfr(fs: List<&2, D.AF>, +dk: Bool, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +fr: U32, +a: U32,
  h: D.FrsK(dk, ds, m, im, fi, nx, ks, img, ps, fr, fs), +e41: {D.Tg(m, a) == 41 : U32}) -> {D.Mem(D.Fr.cells(fs, m, fr), a) == False{} : Bool}:
  match fs:
    case Nil{}:
      {==}
    case Con{D.AF{+kind, +qq, +k, +aa, +b}, +rest}:
      (h0, w1) = h
      (h1, w2) = w1
      (hown, w3) = w2
      (hst, w4) = w3
      (hps, w5) = w4
      (htg, w6) = w5
      (hq2, w7) = w6
      (hk, w8) = w7
      (ia, w9) = w8
      (ib, hr) = w9
      +ne = bool.case(U32.is_eq(fr, a), U32.is_eq(fr, a), {U32.is_eq(fr, a) == False{} : Bool}, {==},
        e => CK.Bo.tf({U32.is_eq(fr, a) == False{} : Bool},
          (%e41 : {U32.is_le(_, 40) == True{} : Bool};
            (%CK.U.eq(fr, a, e) : {U32.is_le(D.Tg(m, _), 40) == True{} : Bool};
              (%Equal.sym(U32, D.Tg(m, fr), D.FK.tag(kind), htg) : {U32.is_le(_, 40) == True{} : Bool}; D.fk.le(kind))))),
        e => e)
      or.ff(U32.is_eq(fr, a), D.Mem(D.Fr.cells(rest, m, D.Fd(1n, m, fr)), a), ne,
        karg.nfr(rest, dk, ds, m, im, fi, nx, ks, img, ps, D.Fd(1n, m, fr), a, hr, e41))

# the Var cells that the OWNED K.args of a chain own are the roots of its held terms
def vars.held.b(b: Bool, +x: Bk.Term, +rest: List<&2, El.Arg>, +m: Cr.Cir.Cells, +a: U32, +y: U32,
  h: {D.Mem(Bool.pick(List<&2, U32>, b, Con{D.Fd(2n, m, a), D.Ag.vars(rest, m, D.Fd(1n, m, a))}, D.Ag.vars(rest, m, D.Fd(1n, m, a))), y) == True{} : Bool},
  ih: {D.Mem(D.Ag.vars(rest, m, D.Fd(1n, m, a)), y) == True{} : Bool} -> {D.Mem(D.Rt.cells(D.Tmp.held(D.Ag.cells(rest, m, D.Fd(1n, m, a)))), y) == True{} : Bool}) ->
  {D.Mem(D.Rt.cells(List.append(&2, D.Rt, Bool.pick(List<&2, D.Rt>, b, [D.Rt{D.Fd(2n, m, a), x}], Nil{}), D.Tmp.held(D.Ag.cells(rest, m, D.Fd(1n, m, a))))), y) == True{} : Bool}:
  match b:
    case True{}:
      D.or.cases(U32.is_eq(D.Fd(2n, m, a), y), D.Mem(D.Ag.vars(rest, m, D.Fd(1n, m, a)), y),
        {Bool.or(U32.is_eq(D.Fd(2n, m, a), y), D.Mem(D.Rt.cells(D.Tmp.held(D.Ag.cells(rest, m, D.Fd(1n, m, a)))), y)) == True{} : Bool}, h,
        e => CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, a), y), D.Mem(D.Rt.cells(D.Tmp.held(D.Ag.cells(rest, m, D.Fd(1n, m, a)))), y), e),
        e => CK.Bo.or_ir(U32.is_eq(D.Fd(2n, m, a), y), D.Mem(D.Rt.cells(D.Tmp.held(D.Ag.cells(rest, m, D.Fd(1n, m, a)))), y), ih(e)))
    case False{}:
      ih(h)

def vars.held(xs: List<&2, El.Arg>, +m: Cr.Cir.Cells, +a: U32, +y: U32, h: {D.Mem(D.Ag.vars(xs, m, a), y) == True{} : Bool}) ->
  {D.Mem(D.Rt.cells(D.Tmp.held(D.Ag.cells(xs, m, a))), y) == True{} : Bool}:
  match xs:
    case Nil{}:
      CK.Bo.tf({D.Mem(D.Rt.cells(D.Tmp.held(D.Ag.cells(Nil{}, m, a))), y) == True{} : Bool}, h)
    case Con{El.Arg{+q, +x}, +rest}:
      vars.held.b(D.Fl(m, a, 4096), x, rest, m, a, y, h, e => vars.held(rest, m, D.Fd(1n, m, a), y, e))

# an OWNED K.arg's temporary holds its term, at its field 2
def own.held(+q: Bk.Quan, +x: Bk.Term, +rest: List<&2, El.Arg>, +m: Cr.Cir.Cells, +a: U32, e: {D.Fl(m, a, 4096) == True{} : Bool}) ->
  {D.Mem(D.Rt.cells(D.Tmp.held(D.Ag.cells(Con{El.Arg{q, x}, rest}, m, a))), D.Fd(2n, m, a)) == True{} : Bool}:
  %Equal.sym(Bool, D.Fl(m, a, 4096), True{}, e) :
    {D.Mem(D.Rt.cells(List.append(&2, D.Rt, Bool.pick(List<&2, D.Rt>, _, [D.Rt{D.Fd(2n, m, a), x}], Nil{}), D.Tmp.held(D.Ag.cells(rest, m, D.Fd(1n, m, a))))), D.Fd(2n, m, a)) == True{} : Bool}
  CK.Bo.or_il(U32.is_eq(D.Fd(2n, m, a), D.Fd(2n, m, a)), D.Mem(D.Rt.cells(D.Tmp.held(D.Ag.cells(rest, m, D.Fd(1n, m, a)))), D.Fd(2n, m, a)), CK.U.eq_refl(D.Fd(2n, m, a)))

# a root of the held terms of a part of the temporaries is a live node
def held.ln(+ys: List<&2, U32>, +os: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +fs: List<&2, D.AF>, +m: Cr.Cir.Cells, +sp: U32, +y: U32,
  +hsh: {D.AllIn(ys, D.Rt.cells(D.Tmp.held(xs))) == True{} : Bool}, hm: {D.Mem(ys, y) == True{} : Bool}) ->
  {D.Nodes(Lst(os, D.Tmp.held(xs), fs, m, sp), m, y) == True{} : Bool}:
  nodes.in.r(os, List.append(&2, D.Rt, D.Tmp.held(xs), D.Fr.rts(fs, m, sp)), m, y,
    nodes.in.l(D.Tmp.held(xs), D.Fr.rts(fs, m, sp), m, y,
      root.nodes(D.Tmp.held(xs), m, y, allin.mem(ys, D.Rt.cells(D.Tmp.held(xs)), y, hsh, hm))))

# the term of a K.arg of the locals' chain is live (Ln): an OWNED one's is
# held by its temporary; a borrowed one's is STATIC, a node of an owned
# root's term, or the Var of an OWNED K.arg after it
def ln.arg(+q: Bk.Quan, +x: Bk.Term, +rest: List<&2, El.Arg>, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +os: List<&2, D.Rt>, +xs: List<&2, D.TmpE>,
  +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +zs: List<&2, D.Rt>, +g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs), +a: U32,
  +hsh: {D.AllIn(D.Rt.cells(D.Tmp.held(D.Ag.cells(Con{El.Arg{q, x}, rest}, m, a))), D.Rt.cells(D.Tmp.held(xs))) == True{} : Bool},
  +hi: D.Is(ds, m, im, fi, nx, ks, img, D.Fd(2n, m, a), x),
  h: {Bool.or(D.Fl(m, a, 4096), Bool.or(D.Fl(m, D.Fd(2n, m, a), 1024), Bool.or(D.Nodes(os, m, D.Fd(2n, m, a)),
    Bool.or(D.Mem(Nil{}, D.Fd(2n, m, a)), D.Mem(D.Ag.vars(rest, m, D.Fd(1n, m, a)), D.Fd(2n, m, a)))))) == True{} : Bool}) ->
  {Ln(x, m, D.Fd(2n, m, a), Lst(os, D.Tmp.held(xs), fs, m, sp)) == True{} : Bool}:
  +y = D.Fd(2n, m, a)
  +HA = D.Rt.cells(D.Tmp.held(D.Ag.cells(Con{El.Arg{q, x}, rest}, m, a)))
  +PK = Bool.pick(List<&2, D.Rt>, D.Fl(m, a, 4096), [D.Rt{y, x}], Nil{})
  +HR = D.Tmp.held(D.Ag.cells(rest, m, D.Fd(1n, m, a)))
  D.or.cases(D.Fl(m, a, 4096), Bool.or(D.Fl(m, y, 1024), Bool.or(D.Nodes(os, m, y), Bool.or(D.Mem(Nil{}, y), D.Mem(D.Ag.vars(rest, m, D.Fd(1n, m, a)), y)))),
    {Ln(x, m, y, Lst(os, D.Tmp.held(xs), fs, m, sp)) == True{} : Bool}, h,
    e => ln.live(x, True{}, ds, m, im, fi, nx, ks, img, ps, gc.tbl(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g), Lst(os, D.Tmp.held(xs), fs, m, sp),
      gc.L(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g), y, hi, held.ln(HA, os, xs, fs, m, sp, y, hsh, own.held(q, x, rest, m, a, e))),
    e => or4.case(D.Fl(m, y, 1024), D.Nodes(os, m, y), D.Mem(Nil{}, y), D.Mem(D.Ag.vars(rest, m, D.Fd(1n, m, a)), y),
      {Ln(x, m, y, Lst(os, D.Tmp.held(xs), fs, m, sp)) == True{} : Bool}, e,
      e1 => ln.stat(x, True{}, ds, m, im, fi, nx, ks, img, ps, D.Tmp.cells(xs), D.Rt.cells(D.Tmp.held(xs)), gc.tbl(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g),
        Lst(os, D.Tmp.held(xs), fs, m, sp), y, hi, e1, gc.clo(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g)),
      e1 => ln.live(x, True{}, ds, m, im, fi, nx, ks, img, ps, gc.tbl(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g), Lst(os, D.Tmp.held(xs), fs, m, sp),
        gc.L(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g), y, hi, nodes.in.l(os, List.append(&2, D.Rt, D.Tmp.held(xs), D.Fr.rts(fs, m, sp)), m, y, e1)),
      e1 => CK.Bo.tf({Ln(x, m, y, Lst(os, D.Tmp.held(xs), fs, m, sp)) == True{} : Bool}, e1),
      e1 => ln.live(x, True{}, ds, m, im, fi, nx, ks, img, ps, gc.tbl(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g), Lst(os, D.Tmp.held(xs), fs, m, sp),
        gc.L(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g), y, hi,
        held.ln(HA, os, xs, fs, m, sp, y, hsh,
          (%Equal.sym(List<&2, U32>, D.Rt.cells(List.append(&2, D.Rt, PK, HR)), List.append(&2, U32, D.Rt.cells(PK), D.Rt.cells(HR)), rt.cells.app(PK, HR)) :
            {D.Mem(_, y) == True{} : Bool};
            mem.in.r(D.Rt.cells(PK), D.Rt.cells(HR), y, vars.held(rest, m, D.Fd(1n, m, a), y, e1)))))))

# the locals' K.args, and their terms, may be read (Env.rx): the K.args are
# temporaries (no garbage), no frames (tag 41) and no table cells; their
# terms are live
def env.rx(es: List<&2, El.Arg>, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +os: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>,
  +zs: List<&2, D.Rt>, +g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs), +hK: {U32.is_le(290, im) == True{} : Bool},
  +hKF: {U32.is_lt(im, fi) == True{} : Bool}, +a: U32, +hag: D.Ag(ds, m, im, fi, nx, ks, img, ps, os, Nil{}, a, es),
  +hsh: {D.AllIn(D.Rt.cells(D.Tmp.held(D.Ag.cells(es, m, a))), D.Rt.cells(D.Tmp.held(xs))) == True{} : Bool},
  +hsc: {D.AllIn(D.Tmp.cells(D.Ag.cells(es, m, a)), D.Tmp.cells(xs)) == True{} : Bool}) ->
  {Env.rx(es, m, a, List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp))) == True{} : Bool}:
  match es:
    case Nil{}:
      {==}
    case Con{El.Arg{+q, +x}, +rest}:
      (e0, r0) = hag
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
      +P = Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs)))
      +E = D.Fr.cells(fs, m, sp)
      +X = List.append(&2, U32, P, E)
      +PK = Bool.pick(List<&2, D.Rt>, D.Fl(m, a, 4096), [D.Rt{D.Fd(2n, m, a), x}], Nil{})
      +HR = D.Tmp.held(D.Ag.cells(rest, m, D.Fd(1n, m, a)))
      +hsc2 = hsc
      +hsh2 = hsh
      +ha = CK.Bo.and_l(D.Mem(D.Tmp.cells(xs), a), D.AllIn(D.Tmp.cells(D.Ag.cells(rest, m, D.Fd(1n, m, a))), D.Tmp.cells(xs)), hsc2)
      +np = gb.not(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs)), a,
        lv.y(m, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs)), a, mem.in.r(E, D.Tmp.cells(xs), a, ha)))
      +ne = {(%mem.has(E, a) : {_ == False{} : Bool}; karg.nfr(fs, True{}, ds, m, im, fi, nx, ks, img, ps, sp, a, gc.frs(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g), e5)) :
        {S.Has(E, a) == False{} : Bool}}
      +hrx = CK.Bo.and_i(Bool.not(S.Has(X, a)), Bool.not(S.Tbc(a)),
        CK.Bo.not_i(S.Has(X, a), (%Equal.sym(Bool, S.Has(X, a), Bool.or(S.Has(P, a), S.Has(E, a)), has.app(P, E, a)) : {_ == False{} : Bool};
          or.ff(S.Has(P, a), S.Has(E, a), np, ne))),
        CK.Bo.not_i(S.Tbc(a), own.ntb(a, im, fi, CK.U.le(fi, a, CK.Bo.and_l(U32.is_le(fi, a), U32.is_lt(a, nx), e2)), hK, hKF)))
      +hsh3 = AC.allin.trans(D.Rt.cells(HR), D.Rt.cells(List.append(&2, D.Rt, PK, HR)), D.Rt.cells(D.Tmp.held(xs)),
        (%Equal.sym(List<&2, U32>, D.Rt.cells(List.append(&2, D.Rt, PK, HR)), List.append(&2, U32, D.Rt.cells(PK), D.Rt.cells(HR)), rt.cells.app(PK, HR)) :
          {D.AllIn(D.Rt.cells(HR), _) == True{} : Bool}; allin.r(D.Rt.cells(PK), D.Rt.cells(HR))), hsh2)
      CK.Bo.and_i(Rx(X, a), Bool.and(Rx.all(x, m, D.Fd(2n, m, a), X), Env.rx(rest, m, D.Fd(1n, m, a), X)), hrx,
        CK.Bo.and_i(Rx.all(x, m, D.Fd(2n, m, a), X), Env.rx(rest, m, D.Fd(1n, m, a), X),
          rx.ln(x, ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, hK, hKF, D.Fd(2n, m, a), e9,
            ln.arg(q, x, rest, ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, a, hsh2, e9, e10)),
          env.rx(rest, ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, hK, hKF, D.Fd(1n, m, a), h2, hsh3,
            CK.Bo.and_r(D.Mem(D.Tmp.cells(xs), a), D.AllIn(D.Tmp.cells(D.Ag.cells(rest, m, D.Fd(1n, m, a))), D.Tmp.cells(xs)), hsc2))))

# the source c, borrowed (Held: STATIC or a node of an owned root's term),
# has t as its checked term
def src.tm(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +os: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  +g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs), +hK: {U32.is_le(290, im) == True{} : Bool}, +hKF: {U32.is_lt(im, fi) == True{} : Bool},
  +c: U32, +t: Bk.Term, +hi: D.IsK(True{}, ds, m, im, fi, nx, ks, img, c, t), hh: {Bool.or(D.Fl(m, c, 1024), D.Nodes(os, m, c)) == True{} : Bool}) ->
  {S.Tm(Pg.Term.size(t), m, ks, img, im, fi, List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp)), nx, c) == Some{t} : Maybe<&2, Bk.Term>}:
  tm.is.at(Pg.Term.size(t), True{}, ds, m, im, fi, nx, ks, img,
    List.append(&2, U32, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Fr.cells(fs, m, sp)),
    c, t, N.le_refl(Pg.Term.size(t)), hi,
    rx.ln(t, ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, hK, hKF, c, hi,
      D.or.cases(D.Fl(m, c, 1024), D.Nodes(os, m, c), {Ln(t, m, c, Lst(os, D.Tmp.held(xs), fs, m, sp)) == True{} : Bool}, hh,
        e => ln.stat(t, True{}, ds, m, im, fi, nx, ks, img, ps, D.Tmp.cells(xs), D.Rt.cells(D.Tmp.held(xs)), gc.tbl(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g),
          Lst(os, D.Tmp.held(xs), fs, m, sp), c, hi, e, gc.clo(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g)),
        e => ln.live(t, True{}, ds, m, im, fi, nx, ks, img, ps, gc.tbl(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g), Lst(os, D.Tmp.held(xs), fs, m, sp),
          gc.L(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g), c, hi, nodes.in.l(os, List.append(&2, D.Rt, D.Tmp.held(xs), D.Fr.rts(fs, m, sp)), m, c, e)))))

# HS and AccK give the start's facts of the copy (Pre), with the copy's view
# of the state (above)
def pre.of(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +fs: List<&2, D.AF>, +sp: U32,
  +pend: U32, +ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  +hs: D.HS(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps), +hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, os, xs, sp, fs, ps, zs),
  +hl: {List.length(&2, U32, regs) == 63n : Nat}, +hp: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>},
  +ho: N.Le(List.length(&2, D.Rt, os), 64n)) ->
  S.Pre(regs, m, nx, fi, im, ks, img,
    Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), ps,
    Zl(Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs))), D.Rts.size(zs), m, ks, img),
    D.Fr.cells(fs, m, sp), Rs.of(List.append(&2, D.Rt, os, D.Fr.rts(fs, m, sp))), Tmps.of(xs),
    Kl(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps), D.Acc.need(m, nx, fi, os, xs, sp, fs)):
  (_, hs1) = hs
  (_, hs2) = hs1
  (_, hs3) = hs2
  (_, hs4) = hs3
  (hh, hi) = hs4
  (hch, hh1) = hh
  (_, hh2) = hh1
  (hcnt, hh3) = hh2
  (hpts, hh4) = hh3
  (hroom, hfn) = hh4
  (htbl, hi1) = hi
  (_, hi2) = hi1
  (_, hi3) = hi2
  (_, hi4) = hi3
  (_, hi5) = hi4
  (_, hi6) = hi5
  (hK, hKF) = hi6
  (_, ha1) = hac
  (_, ha2) = ha1
  (_, ha3) = ha2
  (hcov, _) = ha3
  +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
  +L = Lst(os, D.Tmp.held(xs), fs, m, sp)
  +P = Gb.of(n, m, fi, L, Yc(fs, m, sp, D.Tmp.cells(xs)))
  +E = D.Fr.cells(fs, m, sp)
  +frt = D.Fr.rts(fs, m, sp)
  +hld = D.Tmp.held(xs)
  +cs = D.Tmp.cells(xs)
  +g = gc.of(ds, ks, img, m, nx, fi, im, os, bs, xs, fs, sp, pend, ps, zs, hs, hac)
  +efn = D.add.sub(U32.to_nat(fi), U32.to_nat(nx), CK.U.le(fi, nx, hfn))
  +hw = N.le_rw_l(U32.to_nat(nx), Nat.add(U32.to_nat(fi), n), U32.to_nat(nx), Equal.sym(Nat, Nat.add(U32.to_nat(fi), n), U32.to_nat(nx), efn), N.le_refl(U32.to_nat(nx)))
  +R = List.append(&2, D.Rt, List.append(&2, D.Rt, os, frt), hld)
  +hR = AC.rtsk.app(True{}, List.append(&2, D.Rt, os, frt), hld, ds, m, im, fi, nx, ks, img,
    AC.rtsk.app(True{}, os, frt, ds, m, im, fi, nx, ks, img, gc.os(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g),
      AC.frs.rtsk(True{}, ds, m, im, fi, nx, ks, img, ps, fs, sp, gc.frs(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g))),
    gc.hl(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g))
  +hN = {(%Equal.sym(List<&2, U32>, D.Rt.cells(R), List.append(&2, U32, D.Rt.cells(List.append(&2, D.Rt, os, frt)), D.Rt.cells(hld)),
      rt.cells.app(List.append(&2, D.Rt, os, frt), hld)) : {NdAll(_, L, m) == True{} : Bool};
    ndall.app(D.Rt.cells(List.append(&2, D.Rt, os, frt)), D.Rt.cells(hld), L, m,
      (%Equal.sym(List<&2, U32>, D.Rt.cells(List.append(&2, D.Rt, os, frt)), List.append(&2, U32, D.Rt.cells(os), D.Rt.cells(frt)), rt.cells.app(os, frt)) :
        {NdAll(_, L, m) == True{} : Bool};
        ndall.app(D.Rt.cells(os), D.Rt.cells(frt), L, m,
          ndall.os(D.Rt.cells(os), ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, D.allin.refl(D.Rt.cells(os))),
          ndall.fr(D.Rt.cells(frt), ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, D.allin.refl(D.Rt.cells(frt))))),
      ndall.hl(D.Rt.cells(hld), ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, D.allin.refl(D.Rt.cells(hld))))) :
    {NdAll(D.Rt.cells(R), L, m) == True{} : Bool}}
  +c_cb = cnt.cb(n, m, fi, n, fi, ps, D.Rt.cells(os), hcnt,
    (%Equal.sym(Nat, List.length(&2, U32, D.Rt.cells(os)), List.length(&2, D.Rt, os), cells.len(os)) : N.Le(_, 64n); ho))
  +c_ex2 = {(%Equal.sym(List<&2, U32>, S.Tmp.cells(Tmps.of(xs)), cs, tmps.cells(xs)) : {S.Ex.ok(_, P, fi, nx) == True{} : Bool};
      exok.y(cs, ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, allin.r(E, cs))) :
    {S.Ex.ok(S.Tmp.cells(Tmps.of(xs)), P, fi, nx) == True{} : Bool}}
  +c_rts = {(%Equal.sym(List<&2, S.Rt>, S.Tmp.held(Tmps.of(xs)), Rs.of(hld), tmps.held(xs)) :
      S.Rts(m, ks, img, im, fi, List.append(&2, U32, P, E), nx, List.append(&2, S.Rt, Rs.of(List.append(&2, D.Rt, os, frt)), _));
      (%rs.of.app(List.append(&2, D.Rt, os, frt), hld) : S.Rts(m, ks, img, im, fi, List.append(&2, U32, P, E), nx, _);
        rts.of(R, ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, hK, hKF, hR, hN))) :
    S.Rts(m, ks, img, im, fi, List.append(&2, U32, P, E), nx, List.append(&2, S.Rt, Rs.of(List.append(&2, D.Rt, os, frt)), S.Tmp.held(Tmps.of(xs))))}
  +c_cv = {(%Equal.sym(List<&2, S.Rt>, S.Tmp.held(Tmps.of(xs)), Rs.of(hld), tmps.held(xs)) :
      {S.Cv(n, m, fi, P, List.append(&2, S.Rt, Rs.of(List.append(&2, D.Rt, os, frt)), _), List.append(&2, U32, S.Tmp.cells(Tmps.of(xs)), E)) == True{} : Bool};
      (%rs.of.app(List.append(&2, D.Rt, os, frt), hld) : {S.Cv(n, m, fi, P, _, List.append(&2, U32, S.Tmp.cells(Tmps.of(xs)), E)) == True{} : Bool};
        (%Equal.sym(List<&2, U32>, S.Tmp.cells(Tmps.of(xs)), cs, tmps.cells(xs)) : {S.Cv(n, m, fi, P, Rs.of(R), List.append(&2, U32, _, E)) == True{} : Bool};
          cv.of(n, m, fi, os, hld, frt, E, cs, P, cov.live(n, m, nx, fi, os, xs, fs, sp, hfn, fi, N.le_refl(U32.to_nat(fi)), hw))))) :
    {S.Cv(n, m, fi, P, List.append(&2, S.Rt, Rs.of(List.append(&2, D.Rt, os, frt)), S.Tmp.held(Tmps.of(xs))), List.append(&2, U32, S.Tmp.cells(Tmps.of(xs)), E)) == True{} : Bool}}
  +c_clo = {(%Equal.sym(List<&2, U32>, S.Tmp.cells(Tmps.of(xs)), cs, tmps.cells(xs)) : {S.Clo(n, m, fi, ps, _, S.Rt.cells(S.Tmp.held(Tmps.of(xs))), E) == True{} : Bool};
      (%Equal.sym(List<&2, S.Rt>, S.Tmp.held(Tmps.of(xs)), Rs.of(hld), tmps.held(xs)) : {S.Clo(n, m, fi, ps, cs, S.Rt.cells(_), E) == True{} : Bool};
        (%Equal.sym(List<&2, U32>, S.Rt.cells(Rs.of(hld)), D.Rt.cells(hld), rs.of.cells(hld)) : {S.Clo(n, m, fi, ps, cs, _, E) == True{} : Bool};
          clo.of(n, m, fi, ps, cs, D.Rt.cells(hld), E, gc.clo(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g))))) :
    {S.Clo(n, m, fi, ps, S.Tmp.cells(Tmps.of(xs)), S.Rt.cells(S.Tmp.held(Tmps.of(xs))), E) == True{} : Bool}}
  (hl, (hK, (hKF, (hfn, (hroom, (tb.of(m, im, fi, nx, htbl),
  (al.all(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, pend, regs, hp, hch, hcov, hpts),
  (c_cb,
  (exok.y(E, ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, allin.l(E, cs)),
  (c_ex2, (c_rts,
  (kcs.kl(n, ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, hK, hKF, fi, hcov, N.le_refl(U32.to_nat(fi)), hw),
  (c_cv, (c_clo, pre.bound(m, nx, fi, os, xs, fs, sp, hfn)))))))))))))))

# a run that Ok allows, for some fuel, has ended
def ok.ex(+s: Cr.Cir.Stmt, +st: Cr.Cir.State, +F: U32, +K: U32, +L: U32, +I: List<&2, Word(8n)>, +B: Nat,
  -Q: List<&2, U32> -> Cr.Cir.Cells -> U32 -> U32 -> Type, h: Exists(Nat, n => S.Ok(Cr.Cir.exec(n, s, st), F, K, L, I, B, Q))) ->
  D.Ex(Nat, f => D.Ends(Cr.Cir.exec(f, s, st))):
  (+n, ok) = h
  (n, ok.ends(Cr.Cir.exec(n, s, st), F, K, L, I, B, Q, ok))

# copy.done, from Cp.ok with the copy's view: with some fuel the copy ends
def copy.ends(+wt: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +os: List<&2, D.Rt>,
  +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>, +c: U32, +t: Bk.Term, +ce: U32,
  +es: List<&2, El.Arg>, +xs: List<&2, D.TmpE>, +zs: List<&2, D.Rt>,
  +hs: D.HS(ds, ks, img, m, nx, fi, im, os, Con{D.Rt{c, t}, bs}, fs, sp, pend, ps),
  +hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, os, List.append(&2, D.TmpE, D.Ag.cells(es, m, ce), xs), sp, fs, ps, zs),
  +hl: {List.length(&2, U32, regs) == 63n : Nat},
  +hc: {List.get(&2, U32, regs, S.Cp.src(wt)) == Some{c} : Maybe<&2, U32>},
  +hp: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>},
  +he: {List.get(&2, U32, regs, 36n) == Some{ce} : Maybe<&2, U32>},
  +hn: {List.get(&2, U32, regs, 37n) == Some{U32.from_nat(List.length(&2, El.Arg, es))} : Maybe<&2, U32>},
  +env: D.Ag(ds, m, im, fi, nx, ks, img, ps, os, Nil{}, ce, es),
  +ho: N.Le(List.length(&2, D.Rt, os), 64n)) ->
  D.Ex(Nat, f => D.Ends(Cr.Cir.exec(f, Mc.M.copy(Mc.R.n(), S.Cp.src(wt)), Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0}))):
  (_, hs1) = hs
  (hbs, hs2) = hs1
  (hi0, _) = hbs
  (hhd, hs3) = hs2
  (hh, _) = hhd
  (_, hs4) = hs3
  (_, hi) = hs4
  (_, hi1) = hi
  (_, hi2) = hi1
  (_, hi3) = hi2
  (_, hi4) = hi3
  (_, hi5) = hi4
  (_, hi6) = hi5
  (hK, hKF) = hi6
  +AC0 = D.Ag.cells(es, m, ce)
  +XS = List.append(&2, D.TmpE, AC0, xs)
  +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
  +P = Gb.of(n, m, fi, Lst(os, D.Tmp.held(XS), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(XS)))
  +E = D.Fr.cells(fs, m, sp)
  +X = List.append(&2, U32, P, E)
  +g = gc.of(ds, ks, img, m, nx, fi, im, os, Con{D.Rt{c, t}, bs}, XS, fs, sp, pend, ps, zs, hs, hac)
  +pre = pre.of(ds, ks, img, regs, m, nx, fi, im, os, Con{D.Rt{c, t}, bs}, XS, fs, sp, pend, ps, zs, hs, hac, hl, hp, ho)
  +hsrc = {(%Equal.sym(Maybe<&2, U32>, List.get(&2, U32, regs, S.Cp.src(wt)), Some{c}, hc) : {Maybe.default(&2, U32, _, 0) == c : U32}; {==}) :
    {T.tm.reg(regs, S.Cp.src(wt)) == c : U32}}
  +ht = {(%Equal.sym(U32, T.tm.reg(regs, S.Cp.src(wt)), c, hsrc) : {S.Tm(Pg.Term.size(t), m, ks, img, im, fi, X, nx, _) == Some{t} : Maybe<&2, Bk.Term>};
      src.tm(ds, ks, img, m, nx, fi, im, os, XS, fs, sp, ps, zs, g, hK, hKF, c, t, hi0, hh)) :
    {S.Tm(Pg.Term.size(t), m, ks, img, im, fi, X, nx, T.tm.reg(regs, S.Cp.src(wt))) == Some{t} : Maybe<&2, Bk.Term>}}
  +hsh0 = {(%Equal.sym(List<&2, U32>, D.Rt.cells(D.Tmp.held(XS)), List.append(&2, U32, D.Rt.cells(D.Tmp.held(AC0)), D.Rt.cells(D.Tmp.held(xs))),
        Equal.trans(List<&2, U32>, D.Rt.cells(D.Tmp.held(XS)), D.Rt.cells(List.append(&2, D.Rt, D.Tmp.held(AC0), D.Tmp.held(xs))),
          List.append(&2, U32, D.Rt.cells(D.Tmp.held(AC0)), D.Rt.cells(D.Tmp.held(xs))),
          Equal.cong(List<&2, D.Rt>, List<&2, U32>, l => D.Rt.cells(l), D.Tmp.held(XS), List.append(&2, D.Rt, D.Tmp.held(AC0), D.Tmp.held(xs)), tmp.held.app(AC0, xs)),
          rt.cells.app(D.Tmp.held(AC0), D.Tmp.held(xs)))) :
      {D.AllIn(D.Rt.cells(D.Tmp.held(AC0)), _) == True{} : Bool};
      allin.l(D.Rt.cells(D.Tmp.held(AC0)), D.Rt.cells(D.Tmp.held(xs)))) :
    {D.AllIn(D.Rt.cells(D.Tmp.held(AC0)), D.Rt.cells(D.Tmp.held(XS))) == True{} : Bool}}
  +hsc0 = {(%Equal.sym(List<&2, U32>, D.Tmp.cells(XS), List.append(&2, U32, D.Tmp.cells(AC0), D.Tmp.cells(xs)), tmp.cells.app(AC0, xs)) :
      {D.AllIn(D.Tmp.cells(AC0), _) == True{} : Bool};
      allin.l(D.Tmp.cells(AC0), D.Tmp.cells(xs))) :
    {D.AllIn(D.Tmp.cells(AC0), D.Tmp.cells(XS)) == True{} : Bool}}
  +h36 = {(%Equal.sym(Maybe<&2, U32>, List.get(&2, U32, regs, 36n), Some{ce}, he) : {Maybe.default(&2, U32, _, 0) == ce : U32}; {==}) :
    {T.tm.reg(regs, 36n) == ce : U32}}
  +henv = {(%Equal.sym(U32, T.tm.reg(regs, 36n), ce, h36) : S.Env(m, ks, img, im, fi, X, nx, _, D.Arg.terms(es));
      ag.env(es, ds, m, im, fi, nx, ks, img, ps, os, Nil{}, ce, X, env,
        env.rx(es, ds, ks, img, m, nx, fi, im, os, XS, fs, sp, ps, zs, g, hK, hKF, ce, env, hsh0, hsc0))) :
    S.Env(m, ks, img, im, fi, X, nx, T.tm.reg(regs, 36n), D.Arg.terms(es))}
  +es2 = D.Arg.terms(es)
  ok.ex(Mc.M.copy(Mc.R.n(), S.Cp.src(wt)), S.S(regs, m, nx, fi, im, pg, lim, inp), fi, im, lim, inp,
    S.Cells.bytes(fi, Nat.add(D.Acc.need(m, nx, fi, os, XS, sp, fs), 2n+Pg.Term.size(El.Term.subst(t, es2, 0n)))),
    rg => ms => nx2 => pg2 => S.Ex(S.Wt, w => S.Post(False{}, S.Mo.subst{es2}, t, regs, S.Cp.scratch(Mc.R.n()), Mc.R.n(), ks, img, im, fi,
      m, P, ps, E, nx, Nat.add(D.Acc.need(m, nx, fi, os, XS, sp, fs), 2n+Pg.Term.size(El.Term.subst(t, es2, 0n))),
      Rs.of(List.append(&2, D.Rt, os, D.Fr.rts(fs, m, sp))), Tmps.of(XS), Kl(n, m, fi, ps),
      Con{S.Rt{Pg.Term.size(t), T.tm.reg(regs, S.Cp.src(wt)), t}, S.Env.rts(es2, m, T.tm.reg(regs, 36n))}, w, rg, ms, nx2)),
    S.Cp.ok(wt, regs, m, nx, fi, im, pg, lim, inp, ks, img, P, ps, Zl(P, D.Rts.size(zs), m, ks, img), E,
      Rs.of(List.append(&2, D.Rt, os, D.Fr.rts(fs, m, sp))), Tmps.of(XS), Kl(n, m, fi, ps), D.Acc.need(m, nx, fi, os, XS, sp, fs),
      False{}, t, Pg.Term.size(t), D.Arg.terms(es), pre, ht, henv, clen.ok(es, ds, m, im, fi, nx, ks, img, ps, os, Nil{}, ce, regs, env, hn), Unit{}))

# CopyQ from Post
# ---------------
#
# Post (Cp.ok's end, with hx) says what the copy's state ms (next nx2, pend
# list Qn, garbage Pn) keeps of m: the taken cells T (Tk: the result's new
# nodes and the roots given back) hold no flag and were garbage or new; the
# others keep their fields 0 and 2 to 4 (Kept, Same) and, of the machine's own
# kinds, their values (Kcs of the kept cells Kl). CopyQ follows from it.

# The STATIC cells
# ----------------

def bit.and.assoc(a: Bool, -b: Bool, -c: Bool) -> {Bool.and(Bool.and(a, b), c) == Bool.and(a, Bool.and(b, c)) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def wand.assoc(n: Nat, a: Word(n), b: Word(n), c: Word(n)) -> {Word.and(n, Word.and(n, a, b), c) == Word.and(n, a, Word.and(n, b, c)) : Word(n)}:
  match n:
    case 0n:
      match a b c:
        case WNil{} WNil{} WNil{}:
          {==}
    case 1n+(+p):
      match a b c:
        case WCon{+ab, +at} WCon{+bb, +bt} WCon{+cb, +ct}:
          %Equal.sym(Bool, Bool.and(Bool.and(ab, bb), cb), Bool.and(ab, Bool.and(bb, cb)), bit.and.assoc(ab, bb, cb)) :
            {WCon{_, Word.and(p, Word.and(p, at, bt), ct)} == WCon{Bool.and(ab, Bool.and(bb, cb)), Word.and(p, at, Word.and(p, bt, ct))} : Word(1n+p)}
          %Equal.sym(Word(p), Word.and(p, Word.and(p, at, bt), ct), Word.and(p, at, Word.and(p, bt, ct)), wand.assoc(p, at, bt, ct)) :
            {WCon{Bool.and(ab, Bool.and(bb, cb)), _} == WCon{Bool.and(ab, Bool.and(bb, cb)), Word.and(p, at, Word.and(p, bt, ct))} : Word(1n+p)}
          {==}

def u32.and.assoc(+a: U32, +b: U32, +c: U32) -> {U32.and(U32.and(a, b), c) == U32.and(a, U32.and(b, c)) : U32}:
  match a b c:
    case U32{+x} U32{+y} U32{+z}:
      Equal.cong(Word(32n), U32, w => U32{w}, Word.and(32n, Word.and(32n, x, y), z), Word.and(32n, x, Word.and(32n, y, z)), wand.assoc(32n, x, y, z))

# STATIC (1024) is one of the flags (bits 8 to 12, 7936)
def and.nf.st() -> {U32.and(7936, 1024) == 1024 : U32}:
  {==}

# a field 0 with no flag has no STATIC
def nf.st(+x: U32, h: {U32.is_zero(U32.and(x, 7936)) == True{} : Bool}) -> {U32.is_ne(U32.and(x, 1024), 0) == False{} : Bool}:
  +e0 = CK.U.eq(U32.and(x, 7936), 0, h)
  +e1 = Equal.trans(U32, U32.and(x, 1024), U32.and(x, U32.and(7936, 1024)), 0,
    Equal.cong(U32, U32, w => U32.and(x, w), 1024, U32.and(7936, 1024), Equal.sym(U32, U32.and(7936, 1024), 1024, and.nf.st())),
    Equal.trans(U32, U32.and(x, U32.and(7936, 1024)), U32.and(U32.and(x, 7936), 1024), 0,
      Equal.sym(U32, U32.and(U32.and(x, 7936), 1024), U32.and(x, U32.and(7936, 1024)), u32.and.assoc(x, 7936, 1024)),
      Equal.cong(U32, U32, w => U32.and(w, 1024), U32.and(x, 7936), 0, e0)))
  %Equal.sym(U32, U32.and(x, 1024), 0, e1) : {U32.is_ne(_, 0) == False{} : Bool}
  {==}

# a taken cell (one of T) holds no flag
def nf.get(T: List<&2, U32>, +ms: Cr.Cir.Cells, +c: U32, hnf: {S.Nf(T, ms) == True{} : Bool}, hc: {S.Has(T, c) == True{} : Bool}) ->
  {U32.is_zero(U32.and(S.Fd(0n, ms, c), 7936)) == True{} : Bool}:
  match T:
    case Nil{}:
      CK.Bo.tf({U32.is_zero(U32.and(S.Fd(0n, ms, c), 7936)) == True{} : Bool}, hc)
    case Con{+y, +rest}:
      +h2 = hnf
      D.or.cases(U32.is_eq(y, c), S.Has(rest, c), {U32.is_zero(U32.and(S.Fd(0n, ms, c), 7936)) == True{} : Bool}, hc,
        e => (%CK.U.eq(y, c, e) : {U32.is_zero(U32.and(S.Fd(0n, ms, _), 7936)) == True{} : Bool};
          CK.Bo.and_l(U32.is_zero(U32.and(S.Fd(0n, ms, y), 7936)), S.Nf(rest, ms), h2)),
        e => nf.get(rest, ms, c, CK.Bo.and_r(U32.is_zero(U32.and(S.Fd(0n, ms, y), 7936)), S.Nf(rest, ms), h2), e))

# a taken cell is not STATIC
def nf.fl(+T: List<&2, U32>, +ms: Cr.Cir.Cells, +c: U32, +hnf: {S.Nf(T, ms) == True{} : Bool}, hc: {S.Has(T, c) == True{} : Bool}) ->
  {D.Fl(ms, c, 1024) == False{} : Bool}:
  nf.st(D.Fd(0n, ms, c), nf.get(T, ms, c, hnf, hc))

# n cells from c, each taken: none is STATIC
def stat.new(n: Nat, +ms: Cr.Cir.Cells, +c: U32, +T: List<&2, U32>, hin: {S.In.all(n, c, T) == True{} : Bool}, +hnf: {S.Nf(T, ms) == True{} : Bool}) ->
  {D.Stat(n, ms, c) == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      +h2 = hin
      %Equal.sym(Bool, D.Fl(ms, c, 1024), False{}, nf.fl(T, ms, c, hnf, CK.Bo.and_l(S.Has(T, c), S.In.all(p, U32.inc(c), T), h2))) :
        {Nat.add(D.Nat.of(_), D.Stat(p, ms, U32.inc(c))) == 0n : Nat}
      stat.new(p, ms, U32.inc(c), T, CK.Bo.and_r(S.Has(T, c), S.In.all(p, U32.inc(c), T), h2), hnf)

# a cell taken or kept (Kept's case): no more STATIC than it was
def stat.cell(+m: Cr.Cir.Cells, +ms: Cr.Cir.Cells, +c: U32, +T: List<&2, U32>, +R: Bool, +hnf: {S.Nf(T, ms) == True{} : Bool},
  h: {Bool.or(S.Has(T, c), Bool.and(S.Same.at(m, ms, c), R)) == True{} : Bool}) -> N.Le(D.Nat.of(D.Fl(ms, c, 1024)), D.Nat.of(D.Fl(m, c, 1024))):
  D.or.cases(S.Has(T, c), Bool.and(S.Same.at(m, ms, c), R), N.Le(D.Nat.of(D.Fl(ms, c, 1024)), D.Nat.of(D.Fl(m, c, 1024))), h,
    e => (%Equal.sym(Bool, D.Fl(ms, c, 1024), False{}, nf.fl(T, ms, c, hnf, e)) : N.Le(D.Nat.of(_), D.Nat.of(D.Fl(m, c, 1024)));
      N.le_zero(D.Nat.of(D.Fl(m, c, 1024)))),
    e => (%Equal.sym(U32, S.Fd(0n, ms, c), S.Fd(0n, m, c), CK.U.eq(S.Fd(0n, ms, c), S.Fd(0n, m, c),
        CK.Bo.and_l(U32.is_eq(S.Fd(0n, ms, c), S.Fd(0n, m, c)), Bool.and(U32.is_eq(S.Fd(2n, ms, c), S.Fd(2n, m, c)),
          Bool.and(U32.is_eq(S.Fd(3n, ms, c), S.Fd(3n, m, c)), U32.is_eq(S.Fd(4n, ms, c), S.Fd(4n, m, c)))),
          CK.Bo.and_l(S.Same.at(m, ms, c), R, e)))) : N.Le(D.Nat.of(U32.is_ne(U32.and(_, 1024), 0)), D.Nat.of(D.Fl(m, c, 1024)));
      N.le_refl(D.Nat.of(D.Fl(m, c, 1024)))))

# the k old cells from c (each taken or kept), then the j new ones from N
# (each taken), are no more STATIC than the k cells were
def stat.copy(k: Nat, +j: Nat, +m: Cr.Cir.Cells, +ms: Cr.Cir.Cells, +c: U32, +N: U32, +T: List<&2, U32>, +Pn: List<&2, U32>, +F: U32,
  +a: Nat, +b: Nat, +Q: List<&2, U32>, +Qn: List<&2, U32>, +x: List<&2, U32>, +y: List<&2, U32>,
  hk: {S.Kept(k, m, ms, c, T, Pn, F, a, b, Q, Qn, x, y) == True{} : Bool}, +hc: {Nat.add(U32.to_nat(c), k) == U32.to_nat(N) : Nat},
  +hin: {S.In.all(j, N, T) == True{} : Bool}, +hnf: {S.Nf(T, ms) == True{} : Bool}) ->
  N.Le(D.Stat(Nat.add(k, j), ms, c), D.Stat(k, m, c)):
  match k:
    case 0n:
      %Equal.sym(U32, c, N, AC.at.end(c, N, hc)) : N.Le(D.Stat(j, ms, _), 0n)
      N.le_rw_l(0n, D.Stat(j, ms, N), 0n, Equal.sym(Nat, D.Stat(j, ms, N), 0n, stat.new(j, ms, N, T, hin, hnf)), N.le_refl(0n))
    case 1n+(+q):
      +hk2 = hk
      +R = Bool.or(Bool.or(U32.is_le(19, U32.and(S.Fd(0n, m, c), 63)), Bool.or(S.Stc(m, c), S.Has(Pn, c))),
        Nat.is_eq(Nat.add(U32.to_nat(S.Fd(1n, ms, c)), Nat.add(S.Pc(a, m, Q, F, c), S.Occ(x, c))), Nat.add(U32.to_nat(S.Fd(1n, m, c)), Nat.add(S.Pc(b, ms, Qn, F, c), S.Occ(y, c)))))
      N.add_mono(D.Nat.of(D.Fl(ms, c, 1024)), D.Nat.of(D.Fl(m, c, 1024)), D.Stat(Nat.add(q, j), ms, U32.inc(c)), D.Stat(q, m, U32.inc(c)),
        stat.cell(m, ms, c, T, R, hnf, CK.Bo.and_l(Bool.or(S.Has(T, c), Bool.and(S.Same.at(m, ms, c), R)), S.Kept(q, m, ms, U32.inc(c), T, Pn, F, a, b, Q, Qn, x, y), hk2)),
        stat.copy(q, j, m, ms, U32.inc(c), N, T, Pn, F, a, b, Q, Qn, x, y,
          CK.Bo.and_r(Bool.or(S.Has(T, c), Bool.and(S.Same.at(m, ms, c), R)), S.Kept(q, m, ms, U32.inc(c), T, Pn, F, a, b, Q, Qn, x, y), hk2),
          AC.at.next(c, q, N, hc), hin, hnf))

# (a + b) - a = b
def sub.add.l(a: Nat, +b: Nat) -> {Nat.sub(Nat.add(a, b), a) == b : Nat}:
  match a:
    case 0n:
      match b:
        case 0n:
          {==}
        case 1n+(+p):
          {==}
    case 1n+(+p):
      sub.add.l(p, b)

# fi <= nx <= nx2: nx2 - fi = (nx - fi) + (nx2 - nx)
def sub.split(+fi: Nat, +nx: Nat, +nx2: Nat, h1: N.Le(fi, nx), h2: N.Le(nx, nx2)) ->
  {Nat.sub(nx2, fi) == Nat.add(Nat.sub(nx, fi), Nat.sub(nx2, nx)) : Nat}:
  +e1 = D.add.sub(fi, nx, h1)
  +e2 = D.add.sub(nx, nx2, h2)
  +e3 = Equal.trans(Nat, Nat.add(fi, Nat.add(Nat.sub(nx, fi), Nat.sub(nx2, nx))), Nat.add(Nat.add(fi, Nat.sub(nx, fi)), Nat.sub(nx2, nx)), nx2,
    Equal.sym(Nat, Nat.add(Nat.add(fi, Nat.sub(nx, fi)), Nat.sub(nx2, nx)), Nat.add(fi, Nat.add(Nat.sub(nx, fi), Nat.sub(nx2, nx))), N.add_assoc(fi, Nat.sub(nx, fi), Nat.sub(nx2, nx))),
    Equal.trans(Nat, Nat.add(Nat.add(fi, Nat.sub(nx, fi)), Nat.sub(nx2, nx)), Nat.add(nx, Nat.sub(nx2, nx)), nx2,
      Equal.cong(Nat, Nat, w => Nat.add(w, Nat.sub(nx2, nx)), Nat.add(fi, Nat.sub(nx, fi)), nx, e1), e2))
  %e3 : {Nat.sub(_, fi) == Nat.add(Nat.sub(nx, fi), Nat.sub(nx2, nx)) : Nat}
  sub.add.l(fi, Nat.add(Nat.sub(nx, fi), Nat.sub(nx2, nx)))

# the copy's state is no more STATIC than the start (CopyQ's Stat)
def stat.end(+m: Cr.Cir.Cells, +ms: Cr.Cir.Cells, +nx: U32, +nx2: U32, +fi: U32, +T: List<&2, U32>, +Pn: List<&2, U32>,
  +Q: List<&2, U32>, +Qn: List<&2, U32>, +r: U32,
  hkept: {S.Kept(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, ms, fi, T, Pn, fi, Nat.sub(U32.to_nat(nx), U32.to_nat(fi)),
    Nat.sub(U32.to_nat(nx2), U32.to_nat(fi)), Q, Qn, Nil{}, [r]) == True{} : Bool},
  +hin: {S.In.all(Nat.sub(U32.to_nat(nx2), U32.to_nat(nx)), nx, T) == True{} : Bool}, +hnf: {S.Nf(T, ms) == True{} : Bool},
  +hfn: {U32.is_le(fi, nx) == True{} : Bool}, +hn2: {U32.is_le(nx, nx2) == True{} : Bool}) ->
  N.Le(D.Stat(Nat.sub(U32.to_nat(nx2), U32.to_nat(fi)), ms, fi), D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi)):
  +n0 = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
  +j = Nat.sub(U32.to_nat(nx2), U32.to_nat(nx))
  %Equal.sym(Nat, Nat.sub(U32.to_nat(nx2), U32.to_nat(fi)), Nat.add(n0, j), sub.split(U32.to_nat(fi), U32.to_nat(nx), U32.to_nat(nx2), CK.U.le(fi, nx, hfn), CK.U.le(nx, nx2, hn2))) :
    N.Le(D.Stat(_, ms, fi), D.Stat(n0, m, fi))
  stat.copy(n0, j, m, ms, fi, nx, T, Pn, fi, n0, Nat.sub(U32.to_nat(nx2), U32.to_nat(fi)), Q, Qn, Nil{}, [r], hkept,
    D.add.sub(U32.to_nat(fi), U32.to_nat(nx), CK.U.le(fi, nx, hfn)), hin, hnf)

# What a copy keeps (Kept.cells)
# ------------------------------

# the facts of a list at one of its cells
def gb.at(Pn: List<&2, U32>, +P: List<&2, U32>, +T: List<&2, U32>, +Qn: List<&2, U32>, +ms: Cr.Cir.Cells, +q: U32,
  h: {S.Gb(Pn, P, T, Qn, ms) == True{} : Bool}, hq: {S.Has(Pn, q) == True{} : Bool}) ->
  {Bool.or(Bool.and(S.Has(P, q), Bool.not(S.Has(T, q))), Bool.and(S.Has(T, q), Bool.and(U32.is_eq(S.Fd(0n, ms, q), 45), S.Has(Qn, q)))) == True{} : Bool}:
  match Pn:
    case Nil{}:
      CK.Bo.tf({Bool.or(Bool.and(S.Has(P, q), Bool.not(S.Has(T, q))), Bool.and(S.Has(T, q), Bool.and(U32.is_eq(S.Fd(0n, ms, q), 45), S.Has(Qn, q)))) == True{} : Bool}, hq)
    case Con{+y, +rest}:
      +h2 = h
      +A = Bool.or(Bool.and(S.Has(P, y), Bool.not(S.Has(T, y))), Bool.and(S.Has(T, y), Bool.and(U32.is_eq(S.Fd(0n, ms, y), 45), S.Has(Qn, y))))
      D.or.cases(U32.is_eq(y, q), S.Has(rest, q),
        {Bool.or(Bool.and(S.Has(P, q), Bool.not(S.Has(T, q))), Bool.and(S.Has(T, q), Bool.and(U32.is_eq(S.Fd(0n, ms, q), 45), S.Has(Qn, q)))) == True{} : Bool}, hq,
        e => (%CK.U.eq(y, q, e) : {Bool.or(Bool.and(S.Has(P, _), Bool.not(S.Has(T, _))), Bool.and(S.Has(T, _), Bool.and(U32.is_eq(S.Fd(0n, ms, _), 45), S.Has(Qn, _)))) == True{} : Bool};
          CK.Bo.and_l(A, S.Gb(rest, P, T, Qn, ms), h2)),
        e => gb.at(rest, P, T, Qn, ms, q, CK.Bo.and_r(A, S.Gb(rest, P, T, Qn, ms), h2), e))

def gts.at(G: List<&2, U32>, +m: Cr.Cir.Cells, +ps: List<&2, U32>, +q: U32, h: {GTs(G, m, ps) == True{} : Bool}, hq: {S.Has(G, q) == True{} : Bool}) ->
  {Bool.or(U32.is_lt(D.Tg(m, q), 19), Bool.and(U32.is_le(32, D.Tg(m, q)), D.Mem(ps, q))) == True{} : Bool}:
  match G:
    case Nil{}:
      CK.Bo.tf({Bool.or(U32.is_lt(D.Tg(m, q), 19), Bool.and(U32.is_le(32, D.Tg(m, q)), D.Mem(ps, q))) == True{} : Bool}, hq)
    case Con{+y, +rest}:
      +h2 = h
      +A = Bool.or(U32.is_lt(D.Tg(m, y), 19), Bool.and(U32.is_le(32, D.Tg(m, y)), D.Mem(ps, y)))
      D.or.cases(U32.is_eq(y, q), S.Has(rest, q), {Bool.or(U32.is_lt(D.Tg(m, q), 19), Bool.and(U32.is_le(32, D.Tg(m, q)), D.Mem(ps, q))) == True{} : Bool}, hq,
        e => (%CK.U.eq(y, q, e) : {Bool.or(U32.is_lt(D.Tg(m, _), 19), Bool.and(U32.is_le(32, D.Tg(m, _)), D.Mem(ps, _))) == True{} : Bool};
          CK.Bo.and_l(A, GTs(rest, m, ps), h2)),
        e => gts.at(rest, m, ps, q, CK.Bo.and_r(A, GTs(rest, m, ps), h2), e))

# an old garbage cell is a term cell or pending
def gq.at(+m: Cr.Cir.Cells, +ps: List<&2, U32>, +P: List<&2, U32>, +q: U32, +hg: {GTs(P, m, ps) == True{} : Bool}, hq: {S.Has(P, q) == True{} : Bool}) ->
  {Bool.or(D.Mem(List.append(&2, U32, ps, Nil{}), q), U32.is_lt(D.Tg(m, q), 19)) == True{} : Bool}:
  D.or.cases(U32.is_lt(D.Tg(m, q), 19), Bool.and(U32.is_le(32, D.Tg(m, q)), D.Mem(ps, q)),
    {Bool.or(D.Mem(List.append(&2, U32, ps, Nil{}), q), U32.is_lt(D.Tg(m, q), 19)) == True{} : Bool}, gts.at(P, m, ps, q, hg, hq),
    e => CK.Bo.or_ir(D.Mem(List.append(&2, U32, ps, Nil{}), q), U32.is_lt(D.Tg(m, q), 19), e),
    e => CK.Bo.or_il(D.Mem(List.append(&2, U32, ps, Nil{}), q), U32.is_lt(D.Tg(m, q), 19),
      mem.in.l(ps, Nil{}, q, CK.Bo.and_r(U32.is_le(32, D.Tg(m, q)), D.Mem(ps, q), e))))

# each cell of the new pend list (of Qn, which Pn holds) below nx was
# pending or is a term cell: it was garbage (Gb), or taken and so garbage
# below nx (Incl.go)
def pssub(qs: List<&2, U32>, +m: Cr.Cir.Cells, +ms: Cr.Cir.Cells, +nx: U32, +ps: List<&2, U32>, +P: List<&2, U32>, +T: List<&2, U32>,
  +Pn: List<&2, U32>, +Qn: List<&2, U32>, hs: {S.Sub(qs, Pn) == True{} : Bool}, +hgb: {S.Gb(Pn, P, T, Qn, ms) == True{} : Bool},
  +hig: {S.Incl.go(T, P, nx) == True{} : Bool}, +hg: {GTs(P, m, ps) == True{} : Bool}) ->
  {D.PsSub.lt(qs, List.append(&2, U32, ps, Nil{}), m, nx) == True{} : Bool}:
  match qs:
    case Nil{}:
      {==}
    case Con{+q, +rest}:
      +hs2 = hs
      +G = Bool.or(D.Mem(List.append(&2, U32, ps, Nil{}), q), U32.is_lt(D.Tg(m, q), 19))
      +cell = bool.case(U32.is_lt(q, nx), U32.is_lt(q, nx), {Bool.or(Bool.not(U32.is_lt(q, nx)), G) == True{} : Bool}, {==},
        elt => CK.Bo.or_ir(Bool.not(U32.is_lt(q, nx)), G,
          D.or.cases(Bool.and(S.Has(P, q), Bool.not(S.Has(T, q))), Bool.and(S.Has(T, q), Bool.and(U32.is_eq(S.Fd(0n, ms, q), 45), S.Has(Qn, q))),
            {G == True{} : Bool}, gb.at(Pn, P, T, Qn, ms, q, hgb, CK.Bo.and_l(S.Has(Pn, q), S.Sub(rest, Pn), hs2)),
            e => gq.at(m, ps, P, q, hg, CK.Bo.and_l(S.Has(P, q), Bool.not(S.Has(T, q)), e)),
            e => D.or.cases(S.Has(P, q), U32.is_le(nx, q), {G == True{} : Bool},
              TS.Has.incl(T, P, nx, q, hig, CK.Bo.and_l(S.Has(T, q), Bool.and(U32.is_eq(S.Fd(0n, ms, q), 45), S.Has(Qn, q)), e)),
              e1 => gq.at(m, ps, P, q, hg, e1),
              e1 => CK.U.lt_ge(q, nx, {G == True{} : Bool}, elt, e1)))),
        elt => CK.Bo.or_il(Bool.not(U32.is_lt(q, nx)), G, (%Equal.sym(Bool, U32.is_lt(q, nx), False{}, elt) : {Bool.not(_) == True{} : Bool}; {==})))
      CK.Bo.and_i(Bool.or(Bool.not(U32.is_lt(q, nx)), G), D.PsSub.lt(rest, List.append(&2, U32, ps, Nil{}), m, nx), cell,
        pssub(rest, m, ms, nx, ps, P, T, Pn, Qn, CK.Bo.and_r(S.Has(Pn, q), S.Sub(rest, Pn), hs2), hgb, hig, hg))

# Terms that the copy keeps
# --------------------------
#
# A term whose every node keeps its fields 0, 2, 3 and 4 (Kp) stands for
# the same term after the copy, with the larger next (isk.keep; U1's isk.put1
# for stores to field 1 is the model).

# each part of the term t, in the cell x of m, keeps its fields 0, 2, 3 and 4
# in ms, and so do its parts
def KpX(t: Bk.Term, +m: Cr.Cir.Cells, +ms: Cr.Cir.Cells, +x: Cr.Cir.Cell) -> Bool:
  match t:
    case Bk.Term.Var{_}:
      True{}
    case Bk.Term.Ref{_}:
      True{}
    case Bk.Term.Ann{y, z}:
      Bool.and(Bool.and(S.Same.at(m, ms, Cr.Cir.Cell.get(2n, x)), KpX(y, m, ms, Cr.Cir.Cells.get(m, Cr.Cir.Cell.get(2n, x)))), Bool.and(S.Same.at(m, ms, Cr.Cir.Cell.get(3n, x)), KpX(z, m, ms, Cr.Cir.Cells.get(m, Cr.Cir.Cell.get(3n, x)))))
    case Bk.Term.Let{_, y, z}:
      Bool.and(Bool.and(S.Same.at(m, ms, Cr.Cir.Cell.get(2n, x)), KpX(y, m, ms, Cr.Cir.Cells.get(m, Cr.Cir.Cell.get(2n, x)))), Bool.and(S.Same.at(m, ms, Cr.Cir.Cell.get(3n, x)), KpX(z, m, ms, Cr.Cir.Cells.get(m, Cr.Cir.Cell.get(3n, x)))))
    case Bk.Term.Typ{y}:
      Bool.and(S.Same.at(m, ms, Cr.Cir.Cell.get(2n, x)), KpX(y, m, ms, Cr.Cir.Cells.get(m, Cr.Cir.Cell.get(2n, x))))
    case Bk.Term.Min{y, z}:
      Bool.and(Bool.and(S.Same.at(m, ms, Cr.Cir.Cell.get(2n, x)), KpX(y, m, ms, Cr.Cir.Cells.get(m, Cr.Cir.Cell.get(2n, x)))), Bool.and(S.Same.at(m, ms, Cr.Cir.Cell.get(3n, x)), KpX(z, m, ms, Cr.Cir.Cells.get(m, Cr.Cir.Cell.get(3n, x)))))
    case Bk.Term.All{_, y, z}:
      Bool.and(Bool.and(S.Same.at(m, ms, Cr.Cir.Cell.get(2n, x)), KpX(y, m, ms, Cr.Cir.Cells.get(m, Cr.Cir.Cell.get(2n, x)))), Bool.and(S.Same.at(m, ms, Cr.Cir.Cell.get(3n, x)), KpX(z, m, ms, Cr.Cir.Cells.get(m, Cr.Cir.Cell.get(3n, x)))))
    case Bk.Term.Lam{_, y}:
      Bool.and(S.Same.at(m, ms, Cr.Cir.Cell.get(2n, x)), KpX(y, m, ms, Cr.Cir.Cells.get(m, Cr.Cir.Cell.get(2n, x))))
    case Bk.Term.App{_, y, z}:
      Bool.and(Bool.and(S.Same.at(m, ms, Cr.Cir.Cell.get(2n, x)), KpX(y, m, ms, Cr.Cir.Cells.get(m, Cr.Cir.Cell.get(2n, x)))), Bool.and(S.Same.at(m, ms, Cr.Cir.Cell.get(3n, x)), KpX(z, m, ms, Cr.Cir.Cells.get(m, Cr.Cir.Cell.get(3n, x)))))
    case Bk.Term.Sig{_, y, z}:
      Bool.and(Bool.and(S.Same.at(m, ms, Cr.Cir.Cell.get(2n, x)), KpX(y, m, ms, Cr.Cir.Cells.get(m, Cr.Cir.Cell.get(2n, x)))), Bool.and(S.Same.at(m, ms, Cr.Cir.Cell.get(3n, x)), KpX(z, m, ms, Cr.Cir.Cells.get(m, Cr.Cir.Cell.get(3n, x)))))
    case Bk.Term.Tup{_, y, z}:
      Bool.and(Bool.and(S.Same.at(m, ms, Cr.Cir.Cell.get(2n, x)), KpX(y, m, ms, Cr.Cir.Cells.get(m, Cr.Cir.Cell.get(2n, x)))), Bool.and(S.Same.at(m, ms, Cr.Cir.Cell.get(3n, x)), KpX(z, m, ms, Cr.Cir.Cells.get(m, Cr.Cir.Cell.get(3n, x)))))
    case Bk.Term.Prj{y}:
      Bool.and(S.Same.at(m, ms, Cr.Cir.Cell.get(2n, x)), KpX(y, m, ms, Cr.Cir.Cells.get(m, Cr.Cir.Cell.get(2n, x))))
    case Bk.Term.Enu{_}:
      True{}
    case Bk.Term.Lab{_}:
      True{}
    case Bk.Term.Mat{_, y, z}:
      Bool.and(Bool.and(S.Same.at(m, ms, Cr.Cir.Cell.get(3n, x)), KpX(y, m, ms, Cr.Cir.Cells.get(m, Cr.Cir.Cell.get(3n, x)))), Bool.and(S.Same.at(m, ms, Cr.Cir.Cell.get(4n, x)), KpX(z, m, ms, Cr.Cir.Cells.get(m, Cr.Cir.Cell.get(4n, x)))))
    case Bk.Term.Efq{}:
      True{}
    case Bk.Term.Eql{y, z, w}:
      Bool.and(Bool.and(S.Same.at(m, ms, Cr.Cir.Cell.get(2n, x)), KpX(y, m, ms, Cr.Cir.Cells.get(m, Cr.Cir.Cell.get(2n, x)))), Bool.and(Bool.and(S.Same.at(m, ms, Cr.Cir.Cell.get(3n, x)), KpX(z, m, ms, Cr.Cir.Cells.get(m, Cr.Cir.Cell.get(3n, x)))), Bool.and(S.Same.at(m, ms, Cr.Cir.Cell.get(4n, x)), KpX(w, m, ms, Cr.Cir.Cells.get(m, Cr.Cir.Cell.get(4n, x))))))
    case Bk.Term.Rfl{}:
      True{}
    case Bk.Term.Rwt{y, z, w}:
      Bool.and(Bool.and(S.Same.at(m, ms, Cr.Cir.Cell.get(2n, x)), KpX(y, m, ms, Cr.Cir.Cells.get(m, Cr.Cir.Cell.get(2n, x)))), Bool.and(Bool.and(S.Same.at(m, ms, Cr.Cir.Cell.get(3n, x)), KpX(z, m, ms, Cr.Cir.Cells.get(m, Cr.Cir.Cell.get(3n, x)))), Bool.and(S.Same.at(m, ms, Cr.Cir.Cell.get(4n, x)), KpX(w, m, ms, Cr.Cir.Cells.get(m, Cr.Cir.Cell.get(4n, x))))))

# the term t at r keeps its nodes: r keeps its fields 0, 2, 3 and 4 from m to
# ms, and so do its parts
def Kp(+t: Bk.Term, +m: Cr.Cir.Cells, +ms: Cr.Cir.Cells, +r: U32) -> Bool:
  Bool.and(S.Same.at(m, ms, r), KpX(t, m, ms, Cr.Cir.Cells.get(m, r)))

# a cell that keeps its fields 0, 2, 3 and 4 is the old one with its field 1
def cell.eq1(x2: Cr.Cir.Cell, x: Cr.Cir.Cell, e0: {Cr.Cir.Cell.get(0n, x2) == Cr.Cir.Cell.get(0n, x) : U32},
  e2: {Cr.Cir.Cell.get(2n, x2) == Cr.Cir.Cell.get(2n, x) : U32}, e3: {Cr.Cir.Cell.get(3n, x2) == Cr.Cir.Cell.get(3n, x) : U32},
  e4: {Cr.Cir.Cell.get(4n, x2) == Cr.Cir.Cell.get(4n, x) : U32}) -> {x2 == Cr.Cir.Cell.set(1n, x, Cr.Cir.Cell.get(1n, x2)) : Cr.Cir.Cell}:
  match x2 x:
    case Cr.Cir.Cell{+a0, +a1, +a2, +a3, +a4} Cr.Cir.Cell{+b0, b1, +b2, +b3, +b4}:
      %e0 : {Cr.Cir.Cell{a0, a1, a2, a3, a4} == Cr.Cir.Cell{_, a1, b2, b3, b4} : Cr.Cir.Cell}
      %e2 : {Cr.Cir.Cell{a0, a1, a2, a3, a4} == Cr.Cir.Cell{a0, a1, _, b3, b4} : Cr.Cir.Cell}
      %e3 : {Cr.Cir.Cell{a0, a1, a2, a3, a4} == Cr.Cir.Cell{a0, a1, a2, _, b4} : Cr.Cir.Cell}
      %e4 : {Cr.Cir.Cell{a0, a1, a2, a3, a4} == Cr.Cir.Cell{a0, a1, a2, a3, _} : Cr.Cir.Cell}
      {==}

# a cell that keeps its fields 0, 2, 3 and 4 (Same.at), by its old value
def cell.k1(+m: Cr.Cir.Cells, +ms: Cr.Cir.Cells, +p: U32, h: {S.Same.at(m, ms, p) == True{} : Bool}) ->
  {Cr.Cir.Cells.get(ms, p) == Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, p), D.Fd(1n, ms, p)) : Cr.Cir.Cell}:
  +h2 = h
  +A0 = U32.is_eq(S.Fd(0n, ms, p), S.Fd(0n, m, p))
  +A2 = U32.is_eq(S.Fd(2n, ms, p), S.Fd(2n, m, p))
  +A3 = U32.is_eq(S.Fd(3n, ms, p), S.Fd(3n, m, p))
  +A4 = U32.is_eq(S.Fd(4n, ms, p), S.Fd(4n, m, p))
  +r1 = CK.Bo.and_r(A0, Bool.and(A2, Bool.and(A3, A4)), h2)
  +r2 = CK.Bo.and_r(A2, Bool.and(A3, A4), r1)
  cell.eq1(Cr.Cir.Cells.get(ms, p), Cr.Cir.Cells.get(m, p),
    CK.U.eq(S.Fd(0n, ms, p), S.Fd(0n, m, p), CK.Bo.and_l(A0, Bool.and(A2, Bool.and(A3, A4)), h2)),
    CK.U.eq(S.Fd(2n, ms, p), S.Fd(2n, m, p), CK.Bo.and_l(A2, Bool.and(A3, A4), r1)),
    CK.U.eq(S.Fd(3n, ms, p), S.Fd(3n, m, p), CK.Bo.and_l(A3, A4, r2)),
    CK.U.eq(S.Fd(4n, ms, p), S.Fd(4n, m, p), CK.Bo.and_r(A3, A4, r2)))

# the cells of the machine and its own cells only grow with next
def own.mono(+fi: U32, +nx: U32, +nx2: U32, +c: U32, h: {D.Own(fi, nx, c) == True{} : Bool}, +hn: {U32.is_le(nx, nx2) == True{} : Bool}) ->
  {D.Own(fi, nx2, c) == True{} : Bool}:
  +h2 = h
  CK.Bo.and_i(U32.is_le(fi, c), U32.is_lt(c, nx2), CK.Bo.and_l(U32.is_le(fi, c), U32.is_lt(c, nx), h2),
    AC.lt.mono(c, nx, nx2, CK.Bo.and_r(U32.is_le(fi, c), U32.is_lt(c, nx), h2), CK.U.le(nx, nx2, hn)))

def or.own.mono(+fi: U32, +nx: U32, +nx2: U32, +c: U32, +F: Bool, h: {Bool.or(D.Own(fi, nx, c), F) == True{} : Bool},
  +hn: {U32.is_le(nx, nx2) == True{} : Bool}) -> {Bool.or(D.Own(fi, nx2, c), F) == True{} : Bool}:
  D.or.cases(D.Own(fi, nx, c), F, {Bool.or(D.Own(fi, nx2, c), F) == True{} : Bool}, h,
    e => CK.Bo.or_il(D.Own(fi, nx2, c), F, own.mono(fi, nx, nx2, c, e, hn)),
    e => CK.Bo.or_ir(D.Own(fi, nx2, c), F, e))

def cell.mono(+c: U32, +K: U32, +F: U32, +N: U32, +N2: U32, h: {Cr.Cir.is_cell(c, K, F, N) == True{} : Bool},
  +hn: {U32.is_le(N, N2) == True{} : Bool}) -> {Cr.Cir.is_cell(c, K, F, N2) == True{} : Bool}:
  D.or.cases(Bool.and(Bool.not(U32.is_zero(c)), U32.is_le(c, K)), D.Own(F, N, c), {Cr.Cir.is_cell(c, K, F, N2) == True{} : Bool}, h,
    e => CK.Bo.or_il(Bool.and(Bool.not(U32.is_zero(c)), U32.is_le(c, K)), D.Own(F, N2, c), e),
    e => CK.Bo.or_ir(Bool.and(Bool.not(U32.is_zero(c)), U32.is_le(c, K)), D.Own(F, N2, c), own.mono(F, N, N2, c, e, hn)))

# what a node says of itself, with a larger next
def ndk.mono(+dk: Bool, +ds: List<&2, Bk.Def>, +im: U32, +fi: U32, +nx: U32, +nx2: U32, +c: U32, +x: Cr.Cir.Cell, +t: Bk.Term, +tag: U32,
  h: D.NdK(dk, ds, im, fi, nx, c, x, t, tag), +hn: {U32.is_le(nx, nx2) == True{} : Bool}) -> D.NdK(dk, ds, im, fi, nx2, c, x, t, tag):
  (h1, r1) = h
  (h2, r2) = r1
  (cell.mono(c, im, fi, nx, nx2, h1, hn), (or.own.mono(fi, nx, nx2, c, D.FlW(Cr.Cir.Cell.get(0n, x), 1024), h2, hn), r2))

# a part of a node after the copy, which keeps its fields 0, 2, 3 and 4: its
# STATIC flag, and its term (ih)
def part.keep(+dk: Bool, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +ms: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +nx2: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +p: U32, -y: Bk.Term, sp: D.Sp(fi, nx, c, Cr.Cir.Cells.get(m, p)),
  +hs: {S.Same.at(m, ms, p) == True{} : Bool}, +hn: {U32.is_le(nx, nx2) == True{} : Bool},
  ih: D.IsCK(dk, ds, ms, im, fi, nx2, ks, img, p, Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, p), D.Fd(1n, ms, p)), y)) ->
  D.P2(D.Sp(fi, nx2, c, Cr.Cir.Cells.get(ms, p)), D.IsCK(dk, ds, ms, im, fi, nx2, ks, img, p, Cr.Cir.Cells.get(ms, p), y)):
  +ek = cell.k1(m, ms, p, hs)
  +e0 = Equal.cong(Cr.Cir.Cell, U32, z => Cr.Cir.Cell.get(0n, z), Cr.Cir.Cells.get(ms, p), Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, p), D.Fd(1n, ms, p)), ek)
  (D.sp.at0(fi, nx2, c, Cr.Cir.Cells.get(ms, p), Cr.Cir.Cells.get(m, p),
     Equal.trans(U32, Cr.Cir.Cell.get(0n, Cr.Cir.Cells.get(ms, p)), Cr.Cir.Cell.get(0n, Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, p), D.Fd(1n, ms, p))),
       Cr.Cir.Cell.get(0n, Cr.Cir.Cells.get(m, p)), e0, D.cg0(Cr.Cir.Cells.get(m, p), D.Fd(1n, ms, p))),
     or.own.mono(fi, nx, nx2, c, D.FlW(Cr.Cir.Cell.get(0n, Cr.Cir.Cells.get(m, p)), 1024), sp, hn)),
   D.isc.atk(dk, ds, ms, im, fi, nx2, ks, img, p, Cr.Cir.Cells.get(ms, p), Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, p), D.Fd(1n, ms, p)), y, ek, ih))

# the copy keeps the term of a cell x whose parts keep their nodes (KpX),
# with field 1 changed to w and a larger next
def isk.keep(t: Bk.Term, +dk: Bool, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +ms: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +nx2: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, x: Cr.Cir.Cell, +w: U32,
  hx: D.IsCK(dk, ds, m, im, fi, nx, ks, img, c, x, t), hk: {KpX(t, m, ms, x) == True{} : Bool}, +hn: {U32.is_le(nx, nx2) == True{} : Bool}) ->
  D.IsCK(dk, ds, ms, im, fi, nx2, ks, img, c, Cr.Cir.Cell.set(1n, x, w), t):
  match t:
    case Bk.Term.Var{+i}:
      match x:
        case Cr.Cir.Cell{+c0, c1, +c2, +c3, +c4}:
          match hx:
            case Tuple{nd, r}:
              (ndk.mono(dk, ds, im, fi, nx, nx2, c, Cr.Cir.Cell{c0, c1, c2, c3, c4}, Bk.Term.Var{i}, 0, nd, hn), r)
    case Bk.Term.Ref{+k}:
      match x:
        case Cr.Cir.Cell{+c0, c1, +c2, +c3, +c4}:
          match hx:
            case Tuple{nd, r}:
              (ndk.mono(dk, ds, im, fi, nx, nx2, c, Cr.Cir.Cell{c0, c1, c2, c3, c4}, Bk.Term.Ref{k}, 1, nd, hn), r)
    case Bk.Term.Ann{+y, +z}:
      match x:
        case Cr.Cir.Cell{+c0, c1, +c2, +c3, +c4}:
          match hx:
            case Tuple{nd, Tuple{Tuple{sp1, h1}, Tuple{sp2, h2}}}:
              +hk2 = hk
              (ndk.mono(dk, ds, im, fi, nx, nx2, c, Cr.Cir.Cell{c0, c1, c2, c3, c4}, Bk.Term.Ann{y, z}, 2, nd, hn), (part.keep(dk, ds, m, ms, im, fi, nx, nx2, ks, img, c, c2, y, sp1, CK.Bo.and_l(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2)), CK.Bo.and_l(Bool.and(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2))), Bool.and(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3))), hk2)), hn,
                isk.keep(y, dk, ds, m, ms, im, fi, nx, nx2, ks, img, c2, Cr.Cir.Cells.get(m, c2), D.Fd(1n, ms, c2), h1,
                  CK.Bo.and_r(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2)), CK.Bo.and_l(Bool.and(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2))), Bool.and(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3))), hk2)), hn)),
              part.keep(dk, ds, m, ms, im, fi, nx, nx2, ks, img, c, c3, z, sp2, CK.Bo.and_l(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3)), CK.Bo.and_r(Bool.and(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2))), Bool.and(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3))), hk2)), hn,
                isk.keep(z, dk, ds, m, ms, im, fi, nx, nx2, ks, img, c3, Cr.Cir.Cells.get(m, c3), D.Fd(1n, ms, c3), h2,
                  CK.Bo.and_r(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3)), CK.Bo.and_r(Bool.and(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2))), Bool.and(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3))), hk2)), hn))))
    case Bk.Term.Let{+q, +y, +z}:
      match x:
        case Cr.Cir.Cell{+c0, c1, +c2, +c3, +c4}:
          match hx:
            case Tuple{nd, Tuple{qn, Tuple{Tuple{sp1, h1}, Tuple{sp2, h2}}}}:
              +hk2 = hk
              (ndk.mono(dk, ds, im, fi, nx, nx2, c, Cr.Cir.Cell{c0, c1, c2, c3, c4}, Bk.Term.Let{q, y, z}, 3, nd, hn), (qn, (part.keep(dk, ds, m, ms, im, fi, nx, nx2, ks, img, c, c2, y, sp1, CK.Bo.and_l(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2)), CK.Bo.and_l(Bool.and(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2))), Bool.and(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3))), hk2)), hn,
                isk.keep(y, dk, ds, m, ms, im, fi, nx, nx2, ks, img, c2, Cr.Cir.Cells.get(m, c2), D.Fd(1n, ms, c2), h1,
                  CK.Bo.and_r(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2)), CK.Bo.and_l(Bool.and(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2))), Bool.and(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3))), hk2)), hn)),
              part.keep(dk, ds, m, ms, im, fi, nx, nx2, ks, img, c, c3, z, sp2, CK.Bo.and_l(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3)), CK.Bo.and_r(Bool.and(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2))), Bool.and(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3))), hk2)), hn,
                isk.keep(z, dk, ds, m, ms, im, fi, nx, nx2, ks, img, c3, Cr.Cir.Cells.get(m, c3), D.Fd(1n, ms, c3), h2,
                  CK.Bo.and_r(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3)), CK.Bo.and_r(Bool.and(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2))), Bool.and(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3))), hk2)), hn)))))
    case Bk.Term.Typ{+y}:
      match x:
        case Cr.Cir.Cell{+c0, c1, +c2, +c3, +c4}:
          match hx:
            case Tuple{nd, Tuple{sp1, h1}}:
              +hk2 = hk
              (ndk.mono(dk, ds, im, fi, nx, nx2, c, Cr.Cir.Cell{c0, c1, c2, c3, c4}, Bk.Term.Typ{y}, 4, nd, hn), part.keep(dk, ds, m, ms, im, fi, nx, nx2, ks, img, c, c2, y, sp1, CK.Bo.and_l(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2)), hk2), hn,
                isk.keep(y, dk, ds, m, ms, im, fi, nx, nx2, ks, img, c2, Cr.Cir.Cells.get(m, c2), D.Fd(1n, ms, c2), h1,
                  CK.Bo.and_r(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2)), hk2), hn)))
    case Bk.Term.Min{+y, +z}:
      match x:
        case Cr.Cir.Cell{+c0, c1, +c2, +c3, +c4}:
          match hx:
            case Tuple{nd, Tuple{Tuple{sp1, h1}, Tuple{sp2, h2}}}:
              +hk2 = hk
              (ndk.mono(dk, ds, im, fi, nx, nx2, c, Cr.Cir.Cell{c0, c1, c2, c3, c4}, Bk.Term.Min{y, z}, 5, nd, hn), (part.keep(dk, ds, m, ms, im, fi, nx, nx2, ks, img, c, c2, y, sp1, CK.Bo.and_l(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2)), CK.Bo.and_l(Bool.and(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2))), Bool.and(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3))), hk2)), hn,
                isk.keep(y, dk, ds, m, ms, im, fi, nx, nx2, ks, img, c2, Cr.Cir.Cells.get(m, c2), D.Fd(1n, ms, c2), h1,
                  CK.Bo.and_r(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2)), CK.Bo.and_l(Bool.and(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2))), Bool.and(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3))), hk2)), hn)),
              part.keep(dk, ds, m, ms, im, fi, nx, nx2, ks, img, c, c3, z, sp2, CK.Bo.and_l(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3)), CK.Bo.and_r(Bool.and(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2))), Bool.and(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3))), hk2)), hn,
                isk.keep(z, dk, ds, m, ms, im, fi, nx, nx2, ks, img, c3, Cr.Cir.Cells.get(m, c3), D.Fd(1n, ms, c3), h2,
                  CK.Bo.and_r(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3)), CK.Bo.and_r(Bool.and(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2))), Bool.and(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3))), hk2)), hn))))
    case Bk.Term.All{+q, +y, +z}:
      match x:
        case Cr.Cir.Cell{+c0, c1, +c2, +c3, +c4}:
          match hx:
            case Tuple{nd, Tuple{qn, Tuple{Tuple{sp1, h1}, Tuple{sp2, h2}}}}:
              +hk2 = hk
              (ndk.mono(dk, ds, im, fi, nx, nx2, c, Cr.Cir.Cell{c0, c1, c2, c3, c4}, Bk.Term.All{q, y, z}, 6, nd, hn), (qn, (part.keep(dk, ds, m, ms, im, fi, nx, nx2, ks, img, c, c2, y, sp1, CK.Bo.and_l(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2)), CK.Bo.and_l(Bool.and(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2))), Bool.and(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3))), hk2)), hn,
                isk.keep(y, dk, ds, m, ms, im, fi, nx, nx2, ks, img, c2, Cr.Cir.Cells.get(m, c2), D.Fd(1n, ms, c2), h1,
                  CK.Bo.and_r(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2)), CK.Bo.and_l(Bool.and(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2))), Bool.and(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3))), hk2)), hn)),
              part.keep(dk, ds, m, ms, im, fi, nx, nx2, ks, img, c, c3, z, sp2, CK.Bo.and_l(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3)), CK.Bo.and_r(Bool.and(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2))), Bool.and(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3))), hk2)), hn,
                isk.keep(z, dk, ds, m, ms, im, fi, nx, nx2, ks, img, c3, Cr.Cir.Cells.get(m, c3), D.Fd(1n, ms, c3), h2,
                  CK.Bo.and_r(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3)), CK.Bo.and_r(Bool.and(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2))), Bool.and(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3))), hk2)), hn)))))
    case Bk.Term.Lam{+q, +y}:
      match x:
        case Cr.Cir.Cell{+c0, c1, +c2, +c3, +c4}:
          match hx:
            case Tuple{nd, Tuple{qn, Tuple{sp1, h1}}}:
              +hk2 = hk
              (ndk.mono(dk, ds, im, fi, nx, nx2, c, Cr.Cir.Cell{c0, c1, c2, c3, c4}, Bk.Term.Lam{q, y}, 7, nd, hn), (qn, part.keep(dk, ds, m, ms, im, fi, nx, nx2, ks, img, c, c2, y, sp1, CK.Bo.and_l(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2)), hk2), hn,
                isk.keep(y, dk, ds, m, ms, im, fi, nx, nx2, ks, img, c2, Cr.Cir.Cells.get(m, c2), D.Fd(1n, ms, c2), h1,
                  CK.Bo.and_r(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2)), hk2), hn))))
    case Bk.Term.App{+q, +y, +z}:
      match x:
        case Cr.Cir.Cell{+c0, c1, +c2, +c3, +c4}:
          match hx:
            case Tuple{nd, Tuple{qn, Tuple{Tuple{sp1, h1}, Tuple{sp2, h2}}}}:
              +hk2 = hk
              (ndk.mono(dk, ds, im, fi, nx, nx2, c, Cr.Cir.Cell{c0, c1, c2, c3, c4}, Bk.Term.App{q, y, z}, 8, nd, hn), (qn, (part.keep(dk, ds, m, ms, im, fi, nx, nx2, ks, img, c, c2, y, sp1, CK.Bo.and_l(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2)), CK.Bo.and_l(Bool.and(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2))), Bool.and(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3))), hk2)), hn,
                isk.keep(y, dk, ds, m, ms, im, fi, nx, nx2, ks, img, c2, Cr.Cir.Cells.get(m, c2), D.Fd(1n, ms, c2), h1,
                  CK.Bo.and_r(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2)), CK.Bo.and_l(Bool.and(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2))), Bool.and(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3))), hk2)), hn)),
              part.keep(dk, ds, m, ms, im, fi, nx, nx2, ks, img, c, c3, z, sp2, CK.Bo.and_l(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3)), CK.Bo.and_r(Bool.and(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2))), Bool.and(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3))), hk2)), hn,
                isk.keep(z, dk, ds, m, ms, im, fi, nx, nx2, ks, img, c3, Cr.Cir.Cells.get(m, c3), D.Fd(1n, ms, c3), h2,
                  CK.Bo.and_r(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3)), CK.Bo.and_r(Bool.and(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2))), Bool.and(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3))), hk2)), hn)))))
    case Bk.Term.Sig{+q, +y, +z}:
      match x:
        case Cr.Cir.Cell{+c0, c1, +c2, +c3, +c4}:
          match hx:
            case Tuple{nd, Tuple{qn, Tuple{Tuple{sp1, h1}, Tuple{sp2, h2}}}}:
              +hk2 = hk
              (ndk.mono(dk, ds, im, fi, nx, nx2, c, Cr.Cir.Cell{c0, c1, c2, c3, c4}, Bk.Term.Sig{q, y, z}, 9, nd, hn), (qn, (part.keep(dk, ds, m, ms, im, fi, nx, nx2, ks, img, c, c2, y, sp1, CK.Bo.and_l(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2)), CK.Bo.and_l(Bool.and(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2))), Bool.and(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3))), hk2)), hn,
                isk.keep(y, dk, ds, m, ms, im, fi, nx, nx2, ks, img, c2, Cr.Cir.Cells.get(m, c2), D.Fd(1n, ms, c2), h1,
                  CK.Bo.and_r(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2)), CK.Bo.and_l(Bool.and(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2))), Bool.and(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3))), hk2)), hn)),
              part.keep(dk, ds, m, ms, im, fi, nx, nx2, ks, img, c, c3, z, sp2, CK.Bo.and_l(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3)), CK.Bo.and_r(Bool.and(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2))), Bool.and(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3))), hk2)), hn,
                isk.keep(z, dk, ds, m, ms, im, fi, nx, nx2, ks, img, c3, Cr.Cir.Cells.get(m, c3), D.Fd(1n, ms, c3), h2,
                  CK.Bo.and_r(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3)), CK.Bo.and_r(Bool.and(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2))), Bool.and(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3))), hk2)), hn)))))
    case Bk.Term.Tup{+q, +y, +z}:
      match x:
        case Cr.Cir.Cell{+c0, c1, +c2, +c3, +c4}:
          match hx:
            case Tuple{nd, Tuple{qn, Tuple{Tuple{sp1, h1}, Tuple{sp2, h2}}}}:
              +hk2 = hk
              (ndk.mono(dk, ds, im, fi, nx, nx2, c, Cr.Cir.Cell{c0, c1, c2, c3, c4}, Bk.Term.Tup{q, y, z}, 10, nd, hn), (qn, (part.keep(dk, ds, m, ms, im, fi, nx, nx2, ks, img, c, c2, y, sp1, CK.Bo.and_l(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2)), CK.Bo.and_l(Bool.and(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2))), Bool.and(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3))), hk2)), hn,
                isk.keep(y, dk, ds, m, ms, im, fi, nx, nx2, ks, img, c2, Cr.Cir.Cells.get(m, c2), D.Fd(1n, ms, c2), h1,
                  CK.Bo.and_r(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2)), CK.Bo.and_l(Bool.and(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2))), Bool.and(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3))), hk2)), hn)),
              part.keep(dk, ds, m, ms, im, fi, nx, nx2, ks, img, c, c3, z, sp2, CK.Bo.and_l(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3)), CK.Bo.and_r(Bool.and(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2))), Bool.and(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3))), hk2)), hn,
                isk.keep(z, dk, ds, m, ms, im, fi, nx, nx2, ks, img, c3, Cr.Cir.Cells.get(m, c3), D.Fd(1n, ms, c3), h2,
                  CK.Bo.and_r(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3)), CK.Bo.and_r(Bool.and(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2))), Bool.and(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3))), hk2)), hn)))))
    case Bk.Term.Prj{+y}:
      match x:
        case Cr.Cir.Cell{+c0, c1, +c2, +c3, +c4}:
          match hx:
            case Tuple{nd, Tuple{sp1, h1}}:
              +hk2 = hk
              (ndk.mono(dk, ds, im, fi, nx, nx2, c, Cr.Cir.Cell{c0, c1, c2, c3, c4}, Bk.Term.Prj{y}, 11, nd, hn), part.keep(dk, ds, m, ms, im, fi, nx, nx2, ks, img, c, c2, y, sp1, CK.Bo.and_l(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2)), hk2), hn,
                isk.keep(y, dk, ds, m, ms, im, fi, nx, nx2, ks, img, c2, Cr.Cir.Cells.get(m, c2), D.Fd(1n, ms, c2), h1,
                  CK.Bo.and_r(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2)), hk2), hn)))
    case Bk.Term.Enu{+k}:
      match x:
        case Cr.Cir.Cell{+c0, c1, +c2, +c3, +c4}:
          match hx:
            case Tuple{nd, r}:
              (ndk.mono(dk, ds, im, fi, nx, nx2, c, Cr.Cir.Cell{c0, c1, c2, c3, c4}, Bk.Term.Enu{k}, 12, nd, hn), r)
    case Bk.Term.Lab{+k}:
      match x:
        case Cr.Cir.Cell{+c0, c1, +c2, +c3, +c4}:
          match hx:
            case Tuple{nd, r}:
              (ndk.mono(dk, ds, im, fi, nx, nx2, c, Cr.Cir.Cell{c0, c1, c2, c3, c4}, Bk.Term.Lab{k}, 13, nd, hn), r)
    case Bk.Term.Mat{+k, +y, +z}:
      match x:
        case Cr.Cir.Cell{+c0, c1, +c2, +c3, +c4}:
          match hx:
            case Tuple{nd, Tuple{qn, Tuple{Tuple{sp1, h1}, Tuple{sp2, h2}}}}:
              +hk2 = hk
              (ndk.mono(dk, ds, im, fi, nx, nx2, c, Cr.Cir.Cell{c0, c1, c2, c3, c4}, Bk.Term.Mat{k, y, z}, 14, nd, hn), (qn, (part.keep(dk, ds, m, ms, im, fi, nx, nx2, ks, img, c, c3, y, sp1, CK.Bo.and_l(S.Same.at(m, ms, c3), KpX(y, m, ms, Cr.Cir.Cells.get(m, c3)), CK.Bo.and_l(Bool.and(S.Same.at(m, ms, c3), KpX(y, m, ms, Cr.Cir.Cells.get(m, c3))), Bool.and(S.Same.at(m, ms, c4), KpX(z, m, ms, Cr.Cir.Cells.get(m, c4))), hk2)), hn,
                isk.keep(y, dk, ds, m, ms, im, fi, nx, nx2, ks, img, c3, Cr.Cir.Cells.get(m, c3), D.Fd(1n, ms, c3), h1,
                  CK.Bo.and_r(S.Same.at(m, ms, c3), KpX(y, m, ms, Cr.Cir.Cells.get(m, c3)), CK.Bo.and_l(Bool.and(S.Same.at(m, ms, c3), KpX(y, m, ms, Cr.Cir.Cells.get(m, c3))), Bool.and(S.Same.at(m, ms, c4), KpX(z, m, ms, Cr.Cir.Cells.get(m, c4))), hk2)), hn)),
              part.keep(dk, ds, m, ms, im, fi, nx, nx2, ks, img, c, c4, z, sp2, CK.Bo.and_l(S.Same.at(m, ms, c4), KpX(z, m, ms, Cr.Cir.Cells.get(m, c4)), CK.Bo.and_r(Bool.and(S.Same.at(m, ms, c3), KpX(y, m, ms, Cr.Cir.Cells.get(m, c3))), Bool.and(S.Same.at(m, ms, c4), KpX(z, m, ms, Cr.Cir.Cells.get(m, c4))), hk2)), hn,
                isk.keep(z, dk, ds, m, ms, im, fi, nx, nx2, ks, img, c4, Cr.Cir.Cells.get(m, c4), D.Fd(1n, ms, c4), h2,
                  CK.Bo.and_r(S.Same.at(m, ms, c4), KpX(z, m, ms, Cr.Cir.Cells.get(m, c4)), CK.Bo.and_r(Bool.and(S.Same.at(m, ms, c3), KpX(y, m, ms, Cr.Cir.Cells.get(m, c3))), Bool.and(S.Same.at(m, ms, c4), KpX(z, m, ms, Cr.Cir.Cells.get(m, c4))), hk2)), hn)))))
    case Bk.Term.Efq{}:
      match x:
        case Cr.Cir.Cell{+c0, c1, +c2, +c3, +c4}:
          ndk.mono(dk, ds, im, fi, nx, nx2, c, Cr.Cir.Cell{c0, c1, c2, c3, c4}, Bk.Term.Efq{}, 15, hx, hn)
    case Bk.Term.Eql{+y, +z, +w}:
      match x:
        case Cr.Cir.Cell{+c0, c1, +c2, +c3, +c4}:
          match hx:
            case Tuple{nd, Tuple{Tuple{sp1, h1}, Tuple{Tuple{sp2, h2}, Tuple{sp3, h3}}}}:
              +hk2 = hk
              (ndk.mono(dk, ds, im, fi, nx, nx2, c, Cr.Cir.Cell{c0, c1, c2, c3, c4}, Bk.Term.Eql{y, z, w}, 16, nd, hn), (part.keep(dk, ds, m, ms, im, fi, nx, nx2, ks, img, c, c2, y, sp1, CK.Bo.and_l(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2)), CK.Bo.and_l(Bool.and(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2))), Bool.and(Bool.and(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3))), Bool.and(S.Same.at(m, ms, c4), KpX(w, m, ms, Cr.Cir.Cells.get(m, c4)))), hk2)), hn,
                isk.keep(y, dk, ds, m, ms, im, fi, nx, nx2, ks, img, c2, Cr.Cir.Cells.get(m, c2), D.Fd(1n, ms, c2), h1,
                  CK.Bo.and_r(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2)), CK.Bo.and_l(Bool.and(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2))), Bool.and(Bool.and(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3))), Bool.and(S.Same.at(m, ms, c4), KpX(w, m, ms, Cr.Cir.Cells.get(m, c4)))), hk2)), hn)),
              (part.keep(dk, ds, m, ms, im, fi, nx, nx2, ks, img, c, c3, z, sp2, CK.Bo.and_l(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3)), CK.Bo.and_l(Bool.and(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3))), Bool.and(S.Same.at(m, ms, c4), KpX(w, m, ms, Cr.Cir.Cells.get(m, c4))), CK.Bo.and_r(Bool.and(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2))), Bool.and(Bool.and(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3))), Bool.and(S.Same.at(m, ms, c4), KpX(w, m, ms, Cr.Cir.Cells.get(m, c4)))), hk2))), hn,
                isk.keep(z, dk, ds, m, ms, im, fi, nx, nx2, ks, img, c3, Cr.Cir.Cells.get(m, c3), D.Fd(1n, ms, c3), h2,
                  CK.Bo.and_r(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3)), CK.Bo.and_l(Bool.and(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3))), Bool.and(S.Same.at(m, ms, c4), KpX(w, m, ms, Cr.Cir.Cells.get(m, c4))), CK.Bo.and_r(Bool.and(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2))), Bool.and(Bool.and(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3))), Bool.and(S.Same.at(m, ms, c4), KpX(w, m, ms, Cr.Cir.Cells.get(m, c4)))), hk2))), hn)),
              part.keep(dk, ds, m, ms, im, fi, nx, nx2, ks, img, c, c4, w, sp3, CK.Bo.and_l(S.Same.at(m, ms, c4), KpX(w, m, ms, Cr.Cir.Cells.get(m, c4)), CK.Bo.and_r(Bool.and(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3))), Bool.and(S.Same.at(m, ms, c4), KpX(w, m, ms, Cr.Cir.Cells.get(m, c4))), CK.Bo.and_r(Bool.and(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2))), Bool.and(Bool.and(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3))), Bool.and(S.Same.at(m, ms, c4), KpX(w, m, ms, Cr.Cir.Cells.get(m, c4)))), hk2))), hn,
                isk.keep(w, dk, ds, m, ms, im, fi, nx, nx2, ks, img, c4, Cr.Cir.Cells.get(m, c4), D.Fd(1n, ms, c4), h3,
                  CK.Bo.and_r(S.Same.at(m, ms, c4), KpX(w, m, ms, Cr.Cir.Cells.get(m, c4)), CK.Bo.and_r(Bool.and(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3))), Bool.and(S.Same.at(m, ms, c4), KpX(w, m, ms, Cr.Cir.Cells.get(m, c4))), CK.Bo.and_r(Bool.and(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2))), Bool.and(Bool.and(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3))), Bool.and(S.Same.at(m, ms, c4), KpX(w, m, ms, Cr.Cir.Cells.get(m, c4)))), hk2))), hn)))))
    case Bk.Term.Rfl{}:
      match x:
        case Cr.Cir.Cell{+c0, c1, +c2, +c3, +c4}:
          ndk.mono(dk, ds, im, fi, nx, nx2, c, Cr.Cir.Cell{c0, c1, c2, c3, c4}, Bk.Term.Rfl{}, 17, hx, hn)
    case Bk.Term.Rwt{+y, +z, +w}:
      match x:
        case Cr.Cir.Cell{+c0, c1, +c2, +c3, +c4}:
          match hx:
            case Tuple{nd, Tuple{Tuple{sp1, h1}, Tuple{Tuple{sp2, h2}, Tuple{sp3, h3}}}}:
              +hk2 = hk
              (ndk.mono(dk, ds, im, fi, nx, nx2, c, Cr.Cir.Cell{c0, c1, c2, c3, c4}, Bk.Term.Rwt{y, z, w}, 18, nd, hn), (part.keep(dk, ds, m, ms, im, fi, nx, nx2, ks, img, c, c2, y, sp1, CK.Bo.and_l(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2)), CK.Bo.and_l(Bool.and(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2))), Bool.and(Bool.and(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3))), Bool.and(S.Same.at(m, ms, c4), KpX(w, m, ms, Cr.Cir.Cells.get(m, c4)))), hk2)), hn,
                isk.keep(y, dk, ds, m, ms, im, fi, nx, nx2, ks, img, c2, Cr.Cir.Cells.get(m, c2), D.Fd(1n, ms, c2), h1,
                  CK.Bo.and_r(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2)), CK.Bo.and_l(Bool.and(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2))), Bool.and(Bool.and(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3))), Bool.and(S.Same.at(m, ms, c4), KpX(w, m, ms, Cr.Cir.Cells.get(m, c4)))), hk2)), hn)),
              (part.keep(dk, ds, m, ms, im, fi, nx, nx2, ks, img, c, c3, z, sp2, CK.Bo.and_l(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3)), CK.Bo.and_l(Bool.and(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3))), Bool.and(S.Same.at(m, ms, c4), KpX(w, m, ms, Cr.Cir.Cells.get(m, c4))), CK.Bo.and_r(Bool.and(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2))), Bool.and(Bool.and(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3))), Bool.and(S.Same.at(m, ms, c4), KpX(w, m, ms, Cr.Cir.Cells.get(m, c4)))), hk2))), hn,
                isk.keep(z, dk, ds, m, ms, im, fi, nx, nx2, ks, img, c3, Cr.Cir.Cells.get(m, c3), D.Fd(1n, ms, c3), h2,
                  CK.Bo.and_r(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3)), CK.Bo.and_l(Bool.and(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3))), Bool.and(S.Same.at(m, ms, c4), KpX(w, m, ms, Cr.Cir.Cells.get(m, c4))), CK.Bo.and_r(Bool.and(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2))), Bool.and(Bool.and(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3))), Bool.and(S.Same.at(m, ms, c4), KpX(w, m, ms, Cr.Cir.Cells.get(m, c4)))), hk2))), hn)),
              part.keep(dk, ds, m, ms, im, fi, nx, nx2, ks, img, c, c4, w, sp3, CK.Bo.and_l(S.Same.at(m, ms, c4), KpX(w, m, ms, Cr.Cir.Cells.get(m, c4)), CK.Bo.and_r(Bool.and(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3))), Bool.and(S.Same.at(m, ms, c4), KpX(w, m, ms, Cr.Cir.Cells.get(m, c4))), CK.Bo.and_r(Bool.and(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2))), Bool.and(Bool.and(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3))), Bool.and(S.Same.at(m, ms, c4), KpX(w, m, ms, Cr.Cir.Cells.get(m, c4)))), hk2))), hn,
                isk.keep(w, dk, ds, m, ms, im, fi, nx, nx2, ks, img, c4, Cr.Cir.Cells.get(m, c4), D.Fd(1n, ms, c4), h3,
                  CK.Bo.and_r(S.Same.at(m, ms, c4), KpX(w, m, ms, Cr.Cir.Cells.get(m, c4)), CK.Bo.and_r(Bool.and(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3))), Bool.and(S.Same.at(m, ms, c4), KpX(w, m, ms, Cr.Cir.Cells.get(m, c4))), CK.Bo.and_r(Bool.and(S.Same.at(m, ms, c2), KpX(y, m, ms, Cr.Cir.Cells.get(m, c2))), Bool.and(Bool.and(S.Same.at(m, ms, c3), KpX(z, m, ms, Cr.Cir.Cells.get(m, c3))), Bool.and(S.Same.at(m, ms, c4), KpX(w, m, ms, Cr.Cir.Cells.get(m, c4)))), hk2))), hn)))))

# the term t at r, whose nodes the copy keeps (Kp), stands for t after it
def isk.kept(+t: Bk.Term, +dk: Bool, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +ms: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +nx2: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +r: U32, h: D.IsK(dk, ds, m, im, fi, nx, ks, img, r, t),
  hk: {Kp(t, m, ms, r) == True{} : Bool}, +hn: {U32.is_le(nx, nx2) == True{} : Bool}) -> D.IsK(dk, ds, ms, im, fi, nx2, ks, img, r, t):
  +hk2 = hk
  D.isc.atk(dk, ds, ms, im, fi, nx2, ks, img, r, Cr.Cir.Cells.get(ms, r), Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, r), D.Fd(1n, ms, r)), t,
    cell.k1(m, ms, r, CK.Bo.and_l(S.Same.at(m, ms, r), KpX(t, m, ms, Cr.Cir.Cells.get(m, r)), hk2)),
    isk.keep(t, dk, ds, m, ms, im, fi, nx, nx2, ks, img, r, Cr.Cir.Cells.get(m, r), D.Fd(1n, ms, r), h,
      CK.Bo.and_r(S.Same.at(m, ms, r), KpX(t, m, ms, Cr.Cir.Cells.get(m, r)), hk2), hn))

# The live terms' nodes are kept
# -------------------------------
#
# A node of a live term is a cell below next that is not garbage (Lv), so the
# copy did not take it (Incl.go); it keeps its fields 0, 2, 3 and 4: an image
# cell by Same, an own cell by Kept.

# a cell among the k cells from c (Same): it keeps its fields 0, 2, 3 and 4
def same.get.b(b: Bool, +k: Nat, +m: Cr.Cir.Cells, +ms: Cr.Cir.Cells, +c: U32, +x: U32, +eb: {U32.is_eq(c, x) == b : Bool},
  h: {Bool.and(S.Same.at(m, ms, c), S.Same(k, m, ms, U32.inc(c))) == True{} : Bool},
  +h1: N.Le(U32.to_nat(c), U32.to_nat(x)), +h2: N.Le(1n+U32.to_nat(x), Nat.add(U32.to_nat(c), 1n+k)),
  ih: {S.Same(k, m, ms, U32.inc(c)) == True{} : Bool} -> N.Le(U32.to_nat(U32.inc(c)), U32.to_nat(x)) ->
    N.Le(1n+U32.to_nat(x), Nat.add(U32.to_nat(U32.inc(c)), k)) -> {S.Same.at(m, ms, x) == True{} : Bool}) ->
  {S.Same.at(m, ms, x) == True{} : Bool}:
  match b:
    case True{}:
      (%CK.U.eq(c, x, eb) : {S.Same.at(m, ms, _) == True{} : Bool}; CK.Bo.and_l(S.Same.at(m, ms, c), S.Same(k, m, ms, U32.inc(c)), h))
    case False{}:
      ih(CK.Bo.and_r(S.Same.at(m, ms, c), S.Same(k, m, ms, U32.inc(c)), h), rng.lo(k, c, x, eb, h1), rng.hi(k, c, x, eb, h1, h2))

def same.get(k: Nat, +m: Cr.Cir.Cells, +ms: Cr.Cir.Cells, +c: U32, +x: U32, h: {S.Same(k, m, ms, c) == True{} : Bool},
  h1: N.Le(U32.to_nat(c), U32.to_nat(x)), h2: N.Le(1n+U32.to_nat(x), Nat.add(U32.to_nat(c), k))) -> {S.Same.at(m, ms, x) == True{} : Bool}:
  match k:
    case 0n:
      rng.none({S.Same.at(m, ms, x) == True{} : Bool}, c, x, h1, h2)
    case 1n+(+q):
      same.get.b(U32.is_eq(c, x), q, m, ms, c, x, {==}, h, h1, h2, a => b => d => same.get(q, m, ms, U32.inc(c), x, a, b, d))

# what Kept says of a cell that the copy did not take, besides its fields
def KR(+m: Cr.Cir.Cells, +ms: Cr.Cir.Cells, +c: U32, +Pn: List<&2, U32>, +F: U32, +a: Nat, +b: Nat, +Q: List<&2, U32>, +Qn: List<&2, U32>,
  +x: List<&2, U32>, +y: List<&2, U32>) -> Bool:
  Bool.or(Bool.or(U32.is_le(19, U32.and(S.Fd(0n, m, c), 63)), Bool.or(S.Stc(m, c), S.Has(Pn, c))),
    Nat.is_eq(Nat.add(U32.to_nat(S.Fd(1n, ms, c)), Nat.add(S.Pc(a, m, Q, F, c), S.Occ(x, c))), Nat.add(U32.to_nat(S.Fd(1n, m, c)), Nat.add(S.Pc(b, ms, Qn, F, c), S.Occ(y, c)))))

# a cell among the k cells from c (Kept), not taken: it keeps its fields 0, 2, 3 and 4
def kept.get.b(bb: Bool, +k: Nat, +m: Cr.Cir.Cells, +ms: Cr.Cir.Cells, +c: U32, +x: U32, +T: List<&2, U32>, +Pn: List<&2, U32>, +F: U32,
  +a: Nat, +b: Nat, +Q: List<&2, U32>, +Qn: List<&2, U32>, +xs: List<&2, U32>, +ys: List<&2, U32>, +eb: {U32.is_eq(c, x) == bb : Bool},
  +hnt: {S.Has(T, x) == False{} : Bool},
  h: {Bool.and(Bool.or(S.Has(T, c), Bool.and(S.Same.at(m, ms, c), KR(m, ms, c, Pn, F, a, b, Q, Qn, xs, ys))), S.Kept(k, m, ms, U32.inc(c), T, Pn, F, a, b, Q, Qn, xs, ys)) == True{} : Bool},
  +h1: N.Le(U32.to_nat(c), U32.to_nat(x)), +h2: N.Le(1n+U32.to_nat(x), Nat.add(U32.to_nat(c), 1n+k)),
  ih: {S.Kept(k, m, ms, U32.inc(c), T, Pn, F, a, b, Q, Qn, xs, ys) == True{} : Bool} -> N.Le(U32.to_nat(U32.inc(c)), U32.to_nat(x)) ->
    N.Le(1n+U32.to_nat(x), Nat.add(U32.to_nat(U32.inc(c)), k)) -> {S.Same.at(m, ms, x) == True{} : Bool}) ->
  {S.Same.at(m, ms, x) == True{} : Bool}:
  match bb:
    case True{}:
      (%CK.U.eq(c, x, eb) : {S.Same.at(m, ms, _) == True{} : Bool};
        CK.Bo.and_l(S.Same.at(m, ms, c), KR(m, ms, c, Pn, F, a, b, Q, Qn, xs, ys),
          or.drop(S.Has(T, c), Bool.and(S.Same.at(m, ms, c), KR(m, ms, c, Pn, F, a, b, Q, Qn, xs, ys)),
            CK.Bo.and_l(Bool.or(S.Has(T, c), Bool.and(S.Same.at(m, ms, c), KR(m, ms, c, Pn, F, a, b, Q, Qn, xs, ys))), S.Kept(k, m, ms, U32.inc(c), T, Pn, F, a, b, Q, Qn, xs, ys), h),
            (%Equal.sym(U32, c, x, CK.U.eq(c, x, eb)) : {S.Has(T, _) == False{} : Bool}; hnt))))
    case False{}:
      ih(CK.Bo.and_r(Bool.or(S.Has(T, c), Bool.and(S.Same.at(m, ms, c), KR(m, ms, c, Pn, F, a, b, Q, Qn, xs, ys))), S.Kept(k, m, ms, U32.inc(c), T, Pn, F, a, b, Q, Qn, xs, ys), h),
        rng.lo(k, c, x, eb, h1), rng.hi(k, c, x, eb, h1, h2))

def kept.get(k: Nat, +m: Cr.Cir.Cells, +ms: Cr.Cir.Cells, +c: U32, +x: U32, +T: List<&2, U32>, +Pn: List<&2, U32>, +F: U32,
  +a: Nat, +b: Nat, +Q: List<&2, U32>, +Qn: List<&2, U32>, +xs: List<&2, U32>, +ys: List<&2, U32>, +hnt: {S.Has(T, x) == False{} : Bool},
  h: {S.Kept(k, m, ms, c, T, Pn, F, a, b, Q, Qn, xs, ys) == True{} : Bool},
  h1: N.Le(U32.to_nat(c), U32.to_nat(x)), h2: N.Le(1n+U32.to_nat(x), Nat.add(U32.to_nat(c), k))) -> {S.Same.at(m, ms, x) == True{} : Bool}:
  match k:
    case 0n:
      rng.none({S.Same.at(m, ms, x) == True{} : Bool}, c, x, h1, h2)
    case 1n+(+q):
      kept.get.b(U32.is_eq(c, x), q, m, ms, c, x, T, Pn, F, a, b, Q, Qn, xs, ys, {==}, hnt, h, h1, h2,
        d => e => f => kept.get(q, m, ms, U32.inc(c), x, T, Pn, F, a, b, Q, Qn, xs, ys, hnt, d, e, f))

# a cell below next is below next
def cell.lt(+x: U32, +im: U32, +fi: U32, +nx: U32, h: {Cr.Cir.is_cell(x, im, fi, nx) == True{} : Bool},
  +hKF: {U32.is_lt(im, fi) == True{} : Bool}, +hfn: {U32.is_le(fi, nx) == True{} : Bool}) -> {U32.is_lt(x, nx) == True{} : Bool}:
  D.or.cases(Bool.and(Bool.not(U32.is_zero(x)), U32.is_le(x, im)), D.Own(fi, nx, x), {U32.is_lt(x, nx) == True{} : Bool}, h,
    e => CK.U.lt_le(x, fi, nx, CK.U.le_lt(x, im, fi, CK.Bo.and_r(Bool.not(U32.is_zero(x)), U32.is_le(x, im), e), hKF), hfn),
    e => CK.Bo.and_r(U32.is_le(fi, x), U32.is_lt(x, nx), e))

# a cell below next, out of the garbage P, was not taken (Incl.go: every taken cell was garbage or new)
def nt.of(+T: List<&2, U32>, +P: List<&2, U32>, +nx: U32, +x: U32, +hig: {S.Incl.go(T, P, nx) == True{} : Bool},
  hnp: {S.Has(P, x) == False{} : Bool}, hlt: {U32.is_lt(x, nx) == True{} : Bool}) -> {S.Has(T, x) == False{} : Bool}:
  bool.case(S.Has(T, x), S.Has(T, x), {S.Has(T, x) == False{} : Bool}, {==},
    e => D.or.cases(S.Has(P, x), U32.is_le(nx, x), {S.Has(T, x) == False{} : Bool}, TS.Has.incl(T, P, nx, x, hig, e),
      e1 => CK.Bo.tf({S.Has(T, x) == False{} : Bool}, Equal.trans(Bool, False{}, S.Has(P, x), True{}, Equal.sym(Bool, S.Has(P, x), False{}, hnp), e1)),
      e1 => CK.U.lt_ge(x, nx, {S.Has(T, x) == False{} : Bool}, hlt, e1)),
    e => e)

# a cell below next, not taken, keeps its fields 0, 2, 3 and 4: an image cell
# by Same, an own cell by Kept
def same.of(+m: Cr.Cir.Cells, +ms: Cr.Cir.Cells, +x: U32, +im: U32, +fi: U32, +nx: U32, +T: List<&2, U32>, +Pn: List<&2, U32>, +n2: Nat,
  +Q: List<&2, U32>, +Qn: List<&2, U32>, +rr: U32, hx: {Cr.Cir.is_cell(x, im, fi, nx) == True{} : Bool}, +hnt: {S.Has(T, x) == False{} : Bool},
  +hkept: {S.Kept(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, ms, fi, T, Pn, fi, Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), n2, Q, Qn, Nil{}, [rr]) == True{} : Bool},
  +hsame: {S.Same(U32.to_nat(im), m, ms, 1) == True{} : Bool}, +hfn: {U32.is_le(fi, nx) == True{} : Bool}) -> {S.Same.at(m, ms, x) == True{} : Bool}:
  D.or.cases(Bool.and(Bool.not(U32.is_zero(x)), U32.is_le(x, im)), D.Own(fi, nx, x), {S.Same.at(m, ms, x) == True{} : Bool}, hx,
    +e => same.get(U32.to_nat(im), m, ms, 1, x, hsame,
      CK.U.pos(x, CK.Bo.not_t(U32.is_zero(x), CK.Bo.and_l(Bool.not(U32.is_zero(x)), U32.is_le(x, im), e))),
      N.le_rw_r(1n+U32.to_nat(x), 1n+U32.to_nat(im), Nat.add(U32.to_nat(1), U32.to_nat(im)), {==},
        CK.U.le(x, im, CK.Bo.and_r(Bool.not(U32.is_zero(x)), U32.is_le(x, im), e)))),
    +e => kept.get(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, ms, fi, x, T, Pn, fi, Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), n2, Q, Qn, Nil{}, [rr], hnt, hkept,
      own.lo(fi, nx, x, e),
      N.le_rw_r(1n+U32.to_nat(x), U32.to_nat(nx), Nat.add(U32.to_nat(fi), Nat.sub(U32.to_nat(nx), U32.to_nat(fi))),
        Equal.sym(Nat, Nat.add(U32.to_nat(fi), Nat.sub(U32.to_nat(nx), U32.to_nat(fi))), U32.to_nat(nx), D.add.sub(U32.to_nat(fi), U32.to_nat(nx), CK.U.le(fi, nx, hfn))),
        CK.U.lt(x, nx, CK.Bo.and_r(U32.is_le(fi, x), U32.is_lt(x, nx), e)))))

# a live node (Lv0), a cell below next, keeps its fields 0, 2, 3 and 4
def same.node(+m: Cr.Cir.Cells, +ms: Cr.Cir.Cells, +x: U32, +im: U32, +fi: U32, +nx: U32, +L: List<&2, D.Rt>, +Y: List<&2, U32>,
  +T: List<&2, U32>, +Pn: List<&2, U32>, +n2: Nat, +Q: List<&2, U32>, +Qn: List<&2, U32>, +rr: U32,
  +hx: {Cr.Cir.is_cell(x, im, fi, nx) == True{} : Bool}, hlv: {Lv0(m, L, x) == True{} : Bool},
  +hkept: {S.Kept(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, ms, fi, T, Pn, fi, Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), n2, Q, Qn, Nil{}, [rr]) == True{} : Bool},
  +hsame: {S.Same(U32.to_nat(im), m, ms, 1) == True{} : Bool},
  +hig: {S.Incl.go(T, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, L, Y), nx) == True{} : Bool},
  +hKF: {U32.is_lt(im, fi) == True{} : Bool}, +hfn: {U32.is_le(fi, nx) == True{} : Bool}) -> {S.Same.at(m, ms, x) == True{} : Bool}:
  same.of(m, ms, x, im, fi, nx, T, Pn, n2, Q, Qn, rr, hx,
    nt.of(T, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, L, Y), nx, x, hig,
      gb.not(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, L, Y, x, CK.Bo.or_il(Lv0(m, L, x), D.Mem(Y, x), hlv)),
      cell.lt(x, im, fi, nx, hx, hKF, hfn)),
    hkept, hsame, hfn)

# every node of a live term (Ln) is kept by the copy (Kp)
def kp.ln(t: Bk.Term, +dk: Bool, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +ms: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +L: List<&2, D.Rt>, +Y: List<&2, U32>, +T: List<&2, U32>, +Pn: List<&2, U32>,
  +n2: Nat, +Q: List<&2, U32>, +Qn: List<&2, U32>, +rr: U32, +r: U32, h: D.IsK(dk, ds, m, im, fi, nx, ks, img, r, t), hln: {Ln(t, m, r, L) == True{} : Bool},
  +hkept: {S.Kept(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, ms, fi, T, Pn, fi, Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), n2, Q, Qn, Nil{}, [rr]) == True{} : Bool},
  +hsame: {S.Same(U32.to_nat(im), m, ms, 1) == True{} : Bool},
  +hig: {S.Incl.go(T, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, L, Y), nx) == True{} : Bool},
  +hKF: {U32.is_lt(im, fi) == True{} : Bool}, +hfn: {U32.is_le(fi, nx) == True{} : Bool}) -> {Kp(t, m, ms, r) == True{} : Bool}:
  match t:
    case Bk.Term.Var{+i}:
      match h:
        case Tuple{nd, _}:
          CK.Bo.and_i(S.Same.at(m, ms, r), True{}, same.node(m, ms, r, im, fi, nx, L, Y, T, Pn, n2, Q, Qn, rr, nk.cell(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Var{i}, 0, nd), hln, hkept, hsame, hig, hKF, hfn), {==})
    case Bk.Term.Ref{+k}:
      match h:
        case Tuple{nd, _}:
          CK.Bo.and_i(S.Same.at(m, ms, r), True{}, same.node(m, ms, r, im, fi, nx, L, Y, T, Pn, n2, Q, Qn, rr, nk.cell(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Ref{k}, 1, nd), hln, hkept, hsame, hig, hKF, hfn), {==})
    case Bk.Term.Ann{+y, +z}:
      match h:
        case Tuple{nd, Tuple{Tuple{sp1, h1}, Tuple{sp2, h2}}}:
          +hl2 = hln
          +hp = CK.Bo.and_r(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L)), hl2)
          CK.Bo.and_i(S.Same.at(m, ms, r), Bool.and(Kp(y, m, ms, D.Fd(2n, m, r)), Kp(z, m, ms, D.Fd(3n, m, r))),
            same.node(m, ms, r, im, fi, nx, L, Y, T, Pn, n2, Q, Qn, rr, nk.cell(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Ann{y, z}, 2, nd), CK.Bo.and_l(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L)), hl2), hkept, hsame, hig, hKF, hfn),
            CK.Bo.and_i(Kp(y, m, ms, D.Fd(2n, m, r)), Kp(z, m, ms, D.Fd(3n, m, r)), kp.ln(y, dk, ds, m, ms, im, fi, nx, ks, img, L, Y, T, Pn, n2, Q, Qn, rr, D.Fd(2n, m, r), h1, CK.Bo.and_l(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L), hp), hkept, hsame, hig, hKF, hfn),
            kp.ln(z, dk, ds, m, ms, im, fi, nx, ks, img, L, Y, T, Pn, n2, Q, Qn, rr, D.Fd(3n, m, r), h2, CK.Bo.and_r(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L), hp), hkept, hsame, hig, hKF, hfn)))
    case Bk.Term.Let{+q, +y, +z}:
      match h:
        case Tuple{nd, Tuple{qn, Tuple{Tuple{sp1, h1}, Tuple{sp2, h2}}}}:
          +hl2 = hln
          +hp = CK.Bo.and_r(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L)), hl2)
          CK.Bo.and_i(S.Same.at(m, ms, r), Bool.and(Kp(y, m, ms, D.Fd(2n, m, r)), Kp(z, m, ms, D.Fd(3n, m, r))),
            same.node(m, ms, r, im, fi, nx, L, Y, T, Pn, n2, Q, Qn, rr, nk.cell(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Let{q, y, z}, 3, nd), CK.Bo.and_l(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L)), hl2), hkept, hsame, hig, hKF, hfn),
            CK.Bo.and_i(Kp(y, m, ms, D.Fd(2n, m, r)), Kp(z, m, ms, D.Fd(3n, m, r)), kp.ln(y, dk, ds, m, ms, im, fi, nx, ks, img, L, Y, T, Pn, n2, Q, Qn, rr, D.Fd(2n, m, r), h1, CK.Bo.and_l(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L), hp), hkept, hsame, hig, hKF, hfn),
            kp.ln(z, dk, ds, m, ms, im, fi, nx, ks, img, L, Y, T, Pn, n2, Q, Qn, rr, D.Fd(3n, m, r), h2, CK.Bo.and_r(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L), hp), hkept, hsame, hig, hKF, hfn)))
    case Bk.Term.Typ{+y}:
      match h:
        case Tuple{nd, Tuple{sp1, h1}}:
          +hl2 = hln
          +hp = CK.Bo.and_r(Lv0(m, L, r), Ln(y, m, D.Fd(2n, m, r), L), hl2)
          CK.Bo.and_i(S.Same.at(m, ms, r), Kp(y, m, ms, D.Fd(2n, m, r)),
            same.node(m, ms, r, im, fi, nx, L, Y, T, Pn, n2, Q, Qn, rr, nk.cell(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Typ{y}, 4, nd), CK.Bo.and_l(Lv0(m, L, r), Ln(y, m, D.Fd(2n, m, r), L), hl2), hkept, hsame, hig, hKF, hfn),
            kp.ln(y, dk, ds, m, ms, im, fi, nx, ks, img, L, Y, T, Pn, n2, Q, Qn, rr, D.Fd(2n, m, r), h1, hp, hkept, hsame, hig, hKF, hfn))
    case Bk.Term.Min{+y, +z}:
      match h:
        case Tuple{nd, Tuple{Tuple{sp1, h1}, Tuple{sp2, h2}}}:
          +hl2 = hln
          +hp = CK.Bo.and_r(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L)), hl2)
          CK.Bo.and_i(S.Same.at(m, ms, r), Bool.and(Kp(y, m, ms, D.Fd(2n, m, r)), Kp(z, m, ms, D.Fd(3n, m, r))),
            same.node(m, ms, r, im, fi, nx, L, Y, T, Pn, n2, Q, Qn, rr, nk.cell(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Min{y, z}, 5, nd), CK.Bo.and_l(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L)), hl2), hkept, hsame, hig, hKF, hfn),
            CK.Bo.and_i(Kp(y, m, ms, D.Fd(2n, m, r)), Kp(z, m, ms, D.Fd(3n, m, r)), kp.ln(y, dk, ds, m, ms, im, fi, nx, ks, img, L, Y, T, Pn, n2, Q, Qn, rr, D.Fd(2n, m, r), h1, CK.Bo.and_l(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L), hp), hkept, hsame, hig, hKF, hfn),
            kp.ln(z, dk, ds, m, ms, im, fi, nx, ks, img, L, Y, T, Pn, n2, Q, Qn, rr, D.Fd(3n, m, r), h2, CK.Bo.and_r(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L), hp), hkept, hsame, hig, hKF, hfn)))
    case Bk.Term.All{+q, +y, +z}:
      match h:
        case Tuple{nd, Tuple{qn, Tuple{Tuple{sp1, h1}, Tuple{sp2, h2}}}}:
          +hl2 = hln
          +hp = CK.Bo.and_r(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L)), hl2)
          CK.Bo.and_i(S.Same.at(m, ms, r), Bool.and(Kp(y, m, ms, D.Fd(2n, m, r)), Kp(z, m, ms, D.Fd(3n, m, r))),
            same.node(m, ms, r, im, fi, nx, L, Y, T, Pn, n2, Q, Qn, rr, nk.cell(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.All{q, y, z}, 6, nd), CK.Bo.and_l(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L)), hl2), hkept, hsame, hig, hKF, hfn),
            CK.Bo.and_i(Kp(y, m, ms, D.Fd(2n, m, r)), Kp(z, m, ms, D.Fd(3n, m, r)), kp.ln(y, dk, ds, m, ms, im, fi, nx, ks, img, L, Y, T, Pn, n2, Q, Qn, rr, D.Fd(2n, m, r), h1, CK.Bo.and_l(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L), hp), hkept, hsame, hig, hKF, hfn),
            kp.ln(z, dk, ds, m, ms, im, fi, nx, ks, img, L, Y, T, Pn, n2, Q, Qn, rr, D.Fd(3n, m, r), h2, CK.Bo.and_r(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L), hp), hkept, hsame, hig, hKF, hfn)))
    case Bk.Term.Lam{+q, +y}:
      match h:
        case Tuple{nd, Tuple{qn, Tuple{sp1, h1}}}:
          +hl2 = hln
          +hp = CK.Bo.and_r(Lv0(m, L, r), Ln(y, m, D.Fd(2n, m, r), L), hl2)
          CK.Bo.and_i(S.Same.at(m, ms, r), Kp(y, m, ms, D.Fd(2n, m, r)),
            same.node(m, ms, r, im, fi, nx, L, Y, T, Pn, n2, Q, Qn, rr, nk.cell(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Lam{q, y}, 7, nd), CK.Bo.and_l(Lv0(m, L, r), Ln(y, m, D.Fd(2n, m, r), L), hl2), hkept, hsame, hig, hKF, hfn),
            kp.ln(y, dk, ds, m, ms, im, fi, nx, ks, img, L, Y, T, Pn, n2, Q, Qn, rr, D.Fd(2n, m, r), h1, hp, hkept, hsame, hig, hKF, hfn))
    case Bk.Term.App{+q, +y, +z}:
      match h:
        case Tuple{nd, Tuple{qn, Tuple{Tuple{sp1, h1}, Tuple{sp2, h2}}}}:
          +hl2 = hln
          +hp = CK.Bo.and_r(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L)), hl2)
          CK.Bo.and_i(S.Same.at(m, ms, r), Bool.and(Kp(y, m, ms, D.Fd(2n, m, r)), Kp(z, m, ms, D.Fd(3n, m, r))),
            same.node(m, ms, r, im, fi, nx, L, Y, T, Pn, n2, Q, Qn, rr, nk.cell(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.App{q, y, z}, 8, nd), CK.Bo.and_l(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L)), hl2), hkept, hsame, hig, hKF, hfn),
            CK.Bo.and_i(Kp(y, m, ms, D.Fd(2n, m, r)), Kp(z, m, ms, D.Fd(3n, m, r)), kp.ln(y, dk, ds, m, ms, im, fi, nx, ks, img, L, Y, T, Pn, n2, Q, Qn, rr, D.Fd(2n, m, r), h1, CK.Bo.and_l(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L), hp), hkept, hsame, hig, hKF, hfn),
            kp.ln(z, dk, ds, m, ms, im, fi, nx, ks, img, L, Y, T, Pn, n2, Q, Qn, rr, D.Fd(3n, m, r), h2, CK.Bo.and_r(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L), hp), hkept, hsame, hig, hKF, hfn)))
    case Bk.Term.Sig{+q, +y, +z}:
      match h:
        case Tuple{nd, Tuple{qn, Tuple{Tuple{sp1, h1}, Tuple{sp2, h2}}}}:
          +hl2 = hln
          +hp = CK.Bo.and_r(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L)), hl2)
          CK.Bo.and_i(S.Same.at(m, ms, r), Bool.and(Kp(y, m, ms, D.Fd(2n, m, r)), Kp(z, m, ms, D.Fd(3n, m, r))),
            same.node(m, ms, r, im, fi, nx, L, Y, T, Pn, n2, Q, Qn, rr, nk.cell(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Sig{q, y, z}, 9, nd), CK.Bo.and_l(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L)), hl2), hkept, hsame, hig, hKF, hfn),
            CK.Bo.and_i(Kp(y, m, ms, D.Fd(2n, m, r)), Kp(z, m, ms, D.Fd(3n, m, r)), kp.ln(y, dk, ds, m, ms, im, fi, nx, ks, img, L, Y, T, Pn, n2, Q, Qn, rr, D.Fd(2n, m, r), h1, CK.Bo.and_l(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L), hp), hkept, hsame, hig, hKF, hfn),
            kp.ln(z, dk, ds, m, ms, im, fi, nx, ks, img, L, Y, T, Pn, n2, Q, Qn, rr, D.Fd(3n, m, r), h2, CK.Bo.and_r(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L), hp), hkept, hsame, hig, hKF, hfn)))
    case Bk.Term.Tup{+q, +y, +z}:
      match h:
        case Tuple{nd, Tuple{qn, Tuple{Tuple{sp1, h1}, Tuple{sp2, h2}}}}:
          +hl2 = hln
          +hp = CK.Bo.and_r(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L)), hl2)
          CK.Bo.and_i(S.Same.at(m, ms, r), Bool.and(Kp(y, m, ms, D.Fd(2n, m, r)), Kp(z, m, ms, D.Fd(3n, m, r))),
            same.node(m, ms, r, im, fi, nx, L, Y, T, Pn, n2, Q, Qn, rr, nk.cell(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Tup{q, y, z}, 10, nd), CK.Bo.and_l(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L)), hl2), hkept, hsame, hig, hKF, hfn),
            CK.Bo.and_i(Kp(y, m, ms, D.Fd(2n, m, r)), Kp(z, m, ms, D.Fd(3n, m, r)), kp.ln(y, dk, ds, m, ms, im, fi, nx, ks, img, L, Y, T, Pn, n2, Q, Qn, rr, D.Fd(2n, m, r), h1, CK.Bo.and_l(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L), hp), hkept, hsame, hig, hKF, hfn),
            kp.ln(z, dk, ds, m, ms, im, fi, nx, ks, img, L, Y, T, Pn, n2, Q, Qn, rr, D.Fd(3n, m, r), h2, CK.Bo.and_r(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L), hp), hkept, hsame, hig, hKF, hfn)))
    case Bk.Term.Prj{+y}:
      match h:
        case Tuple{nd, Tuple{sp1, h1}}:
          +hl2 = hln
          +hp = CK.Bo.and_r(Lv0(m, L, r), Ln(y, m, D.Fd(2n, m, r), L), hl2)
          CK.Bo.and_i(S.Same.at(m, ms, r), Kp(y, m, ms, D.Fd(2n, m, r)),
            same.node(m, ms, r, im, fi, nx, L, Y, T, Pn, n2, Q, Qn, rr, nk.cell(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Prj{y}, 11, nd), CK.Bo.and_l(Lv0(m, L, r), Ln(y, m, D.Fd(2n, m, r), L), hl2), hkept, hsame, hig, hKF, hfn),
            kp.ln(y, dk, ds, m, ms, im, fi, nx, ks, img, L, Y, T, Pn, n2, Q, Qn, rr, D.Fd(2n, m, r), h1, hp, hkept, hsame, hig, hKF, hfn))
    case Bk.Term.Enu{+k}:
      match h:
        case Tuple{nd, _}:
          CK.Bo.and_i(S.Same.at(m, ms, r), True{}, same.node(m, ms, r, im, fi, nx, L, Y, T, Pn, n2, Q, Qn, rr, nk.cell(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Enu{k}, 12, nd), hln, hkept, hsame, hig, hKF, hfn), {==})
    case Bk.Term.Lab{+k}:
      match h:
        case Tuple{nd, _}:
          CK.Bo.and_i(S.Same.at(m, ms, r), True{}, same.node(m, ms, r, im, fi, nx, L, Y, T, Pn, n2, Q, Qn, rr, nk.cell(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Lab{k}, 13, nd), hln, hkept, hsame, hig, hKF, hfn), {==})
    case Bk.Term.Mat{+k, +y, +z}:
      match h:
        case Tuple{nd, Tuple{qn, Tuple{Tuple{sp1, h1}, Tuple{sp2, h2}}}}:
          +hl2 = hln
          +hp = CK.Bo.and_r(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(3n, m, r), L), Ln(z, m, D.Fd(4n, m, r), L)), hl2)
          CK.Bo.and_i(S.Same.at(m, ms, r), Bool.and(Kp(y, m, ms, D.Fd(3n, m, r)), Kp(z, m, ms, D.Fd(4n, m, r))),
            same.node(m, ms, r, im, fi, nx, L, Y, T, Pn, n2, Q, Qn, rr, nk.cell(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Mat{k, y, z}, 14, nd), CK.Bo.and_l(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(3n, m, r), L), Ln(z, m, D.Fd(4n, m, r), L)), hl2), hkept, hsame, hig, hKF, hfn),
            CK.Bo.and_i(Kp(y, m, ms, D.Fd(3n, m, r)), Kp(z, m, ms, D.Fd(4n, m, r)), kp.ln(y, dk, ds, m, ms, im, fi, nx, ks, img, L, Y, T, Pn, n2, Q, Qn, rr, D.Fd(3n, m, r), h1, CK.Bo.and_l(Ln(y, m, D.Fd(3n, m, r), L), Ln(z, m, D.Fd(4n, m, r), L), hp), hkept, hsame, hig, hKF, hfn),
            kp.ln(z, dk, ds, m, ms, im, fi, nx, ks, img, L, Y, T, Pn, n2, Q, Qn, rr, D.Fd(4n, m, r), h2, CK.Bo.and_r(Ln(y, m, D.Fd(3n, m, r), L), Ln(z, m, D.Fd(4n, m, r), L), hp), hkept, hsame, hig, hKF, hfn)))
    case Bk.Term.Efq{}:
      CK.Bo.and_i(S.Same.at(m, ms, r), True{}, same.node(m, ms, r, im, fi, nx, L, Y, T, Pn, n2, Q, Qn, rr, nk.cell(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Efq{}, 15, h), hln, hkept, hsame, hig, hKF, hfn), {==})
    case Bk.Term.Eql{+y, +z, +w}:
      match h:
        case Tuple{nd, Tuple{Tuple{sp1, h1}, Tuple{Tuple{sp2, h2}, Tuple{sp3, h3}}}}:
          +hl2 = hln
          +hp = CK.Bo.and_r(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(2n, m, r), L), Bool.and(Ln(z, m, D.Fd(3n, m, r), L), Ln(w, m, D.Fd(4n, m, r), L))), hl2)
          CK.Bo.and_i(S.Same.at(m, ms, r), Bool.and(Kp(y, m, ms, D.Fd(2n, m, r)), Bool.and(Kp(z, m, ms, D.Fd(3n, m, r)), Kp(w, m, ms, D.Fd(4n, m, r)))),
            same.node(m, ms, r, im, fi, nx, L, Y, T, Pn, n2, Q, Qn, rr, nk.cell(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Eql{y, z, w}, 16, nd), CK.Bo.and_l(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(2n, m, r), L), Bool.and(Ln(z, m, D.Fd(3n, m, r), L), Ln(w, m, D.Fd(4n, m, r), L))), hl2), hkept, hsame, hig, hKF, hfn),
            CK.Bo.and_i(Kp(y, m, ms, D.Fd(2n, m, r)), Bool.and(Kp(z, m, ms, D.Fd(3n, m, r)), Kp(w, m, ms, D.Fd(4n, m, r))), kp.ln(y, dk, ds, m, ms, im, fi, nx, ks, img, L, Y, T, Pn, n2, Q, Qn, rr, D.Fd(2n, m, r), h1, CK.Bo.and_l(Ln(y, m, D.Fd(2n, m, r), L), Bool.and(Ln(z, m, D.Fd(3n, m, r), L), Ln(w, m, D.Fd(4n, m, r), L)), hp), hkept, hsame, hig, hKF, hfn),
            CK.Bo.and_i(Kp(z, m, ms, D.Fd(3n, m, r)), Kp(w, m, ms, D.Fd(4n, m, r)), kp.ln(z, dk, ds, m, ms, im, fi, nx, ks, img, L, Y, T, Pn, n2, Q, Qn, rr, D.Fd(3n, m, r), h2, CK.Bo.and_l(Ln(z, m, D.Fd(3n, m, r), L), Ln(w, m, D.Fd(4n, m, r), L), CK.Bo.and_r(Ln(y, m, D.Fd(2n, m, r), L), Bool.and(Ln(z, m, D.Fd(3n, m, r), L), Ln(w, m, D.Fd(4n, m, r), L)), hp)), hkept, hsame, hig, hKF, hfn),
            kp.ln(w, dk, ds, m, ms, im, fi, nx, ks, img, L, Y, T, Pn, n2, Q, Qn, rr, D.Fd(4n, m, r), h3, CK.Bo.and_r(Ln(z, m, D.Fd(3n, m, r), L), Ln(w, m, D.Fd(4n, m, r), L), CK.Bo.and_r(Ln(y, m, D.Fd(2n, m, r), L), Bool.and(Ln(z, m, D.Fd(3n, m, r), L), Ln(w, m, D.Fd(4n, m, r), L)), hp)), hkept, hsame, hig, hKF, hfn))))
    case Bk.Term.Rfl{}:
      CK.Bo.and_i(S.Same.at(m, ms, r), True{}, same.node(m, ms, r, im, fi, nx, L, Y, T, Pn, n2, Q, Qn, rr, nk.cell(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Rfl{}, 17, h), hln, hkept, hsame, hig, hKF, hfn), {==})
    case Bk.Term.Rwt{+y, +z, +w}:
      match h:
        case Tuple{nd, Tuple{Tuple{sp1, h1}, Tuple{Tuple{sp2, h2}, Tuple{sp3, h3}}}}:
          +hl2 = hln
          +hp = CK.Bo.and_r(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(2n, m, r), L), Bool.and(Ln(z, m, D.Fd(3n, m, r), L), Ln(w, m, D.Fd(4n, m, r), L))), hl2)
          CK.Bo.and_i(S.Same.at(m, ms, r), Bool.and(Kp(y, m, ms, D.Fd(2n, m, r)), Bool.and(Kp(z, m, ms, D.Fd(3n, m, r)), Kp(w, m, ms, D.Fd(4n, m, r)))),
            same.node(m, ms, r, im, fi, nx, L, Y, T, Pn, n2, Q, Qn, rr, nk.cell(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Rwt{y, z, w}, 18, nd), CK.Bo.and_l(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(2n, m, r), L), Bool.and(Ln(z, m, D.Fd(3n, m, r), L), Ln(w, m, D.Fd(4n, m, r), L))), hl2), hkept, hsame, hig, hKF, hfn),
            CK.Bo.and_i(Kp(y, m, ms, D.Fd(2n, m, r)), Bool.and(Kp(z, m, ms, D.Fd(3n, m, r)), Kp(w, m, ms, D.Fd(4n, m, r))), kp.ln(y, dk, ds, m, ms, im, fi, nx, ks, img, L, Y, T, Pn, n2, Q, Qn, rr, D.Fd(2n, m, r), h1, CK.Bo.and_l(Ln(y, m, D.Fd(2n, m, r), L), Bool.and(Ln(z, m, D.Fd(3n, m, r), L), Ln(w, m, D.Fd(4n, m, r), L)), hp), hkept, hsame, hig, hKF, hfn),
            CK.Bo.and_i(Kp(z, m, ms, D.Fd(3n, m, r)), Kp(w, m, ms, D.Fd(4n, m, r)), kp.ln(z, dk, ds, m, ms, im, fi, nx, ks, img, L, Y, T, Pn, n2, Q, Qn, rr, D.Fd(3n, m, r), h2, CK.Bo.and_l(Ln(z, m, D.Fd(3n, m, r), L), Ln(w, m, D.Fd(4n, m, r), L), CK.Bo.and_r(Ln(y, m, D.Fd(2n, m, r), L), Bool.and(Ln(z, m, D.Fd(3n, m, r), L), Ln(w, m, D.Fd(4n, m, r), L)), hp)), hkept, hsame, hig, hKF, hfn),
            kp.ln(w, dk, ds, m, ms, im, fi, nx, ks, img, L, Y, T, Pn, n2, Q, Qn, rr, D.Fd(4n, m, r), h3, CK.Bo.and_r(Ln(z, m, D.Fd(3n, m, r), L), Ln(w, m, D.Fd(4n, m, r), L), CK.Bo.and_r(Ln(y, m, D.Fd(2n, m, r), L), Bool.and(Ln(z, m, D.Fd(3n, m, r), L), Ln(w, m, D.Fd(4n, m, r), L)), hp)), hkept, hsame, hig, hKF, hfn))))

# The kept cells' values
# ----------------------

def kept.if.of(b: Bool, -X: Data, x: X) -> D.Kept.if(b, X):
  match b:
    case True{}:
      Unit{}
    case False{}:
      x

# a cell that is not kept (KlC false) is pending or a term cell
def kept.cond(+m: Cr.Cir.Cells, +ps: List<&2, U32>, +c: U32, eb: {KlC(m, ps, c) == False{} : Bool}) ->
  {Bool.or(D.Mem(List.append(&2, U32, ps, Nil{}), c), U32.is_lt(D.Tg(m, c), 19)) == True{} : Bool}:
  +G = Bool.or(D.Mem(List.append(&2, U32, ps, Nil{}), c), U32.is_lt(D.Tg(m, c), 19))
  bool.case(U32.is_lt(D.Tg(m, c), 19), U32.is_lt(D.Tg(m, c), 19), {G == True{} : Bool}, {==},
    e => CK.Bo.or_ir(D.Mem(List.append(&2, U32, ps, Nil{}), c), U32.is_lt(D.Tg(m, c), 19), e),
    e => CK.Bo.or_il(D.Mem(List.append(&2, U32, ps, Nil{}), c), U32.is_lt(D.Tg(m, c), 19),
      mem.in.l(ps, Nil{}, c, CK.Bo.not_f(D.Mem(ps, c),
        Equal.trans(Bool, Bool.not(D.Mem(ps, c)), KlC(m, ps, c), False{},
          Equal.cong(Bool, Bool, z => Bool.and(z, Bool.not(D.Mem(ps, c))), True{}, Nat.is_le(19n, U32.to_nat(U32.and(S.Fd(0n, m, c), 63))),
            Equal.sym(Bool, Nat.is_le(19n, U32.to_nat(U32.and(S.Fd(0n, m, c), 63))), True{},
              of.t(Nat.is_le(19n, U32.to_nat(U32.and(S.Fd(0n, m, c), 63))), CK.U.le(19, D.Tg(m, c), nlt.le(D.Tg(m, c), 19, e))))),
          eb)))))

# the copy keeps the value of each own cell of the machine's own kinds out of
# the pend list (Kcs of Kl): Kept.go
def kept.go.b(b: Bool, +q: Nat, +m: Cr.Cir.Cells, +ms: Cr.Cir.Cells, +c: U32, +ps: List<&2, U32>, +K: U32, +F: U32,
  +X: List<&2, U32>, +N: U32, +E: List<&2, U32>, eb: {KlC(m, ps, c) == b : Bool},
  h: S.Kcs(ms, K, F, X, N, E, Bool.pick(List<&2, S.Kc>, b, Con{S.Kc{c, Cr.Cir.Cells.get(m, c)}, Kl(q, m, U32.inc(c), ps)}, Kl(q, m, U32.inc(c), ps))),
  ih: S.Kcs(ms, K, F, X, N, E, Kl(q, m, U32.inc(c), ps)) -> D.Kept.go(q, m, ms, List.append(&2, U32, ps, Nil{}), U32.inc(c))) ->
  D.Kept.go(1n+q, m, ms, List.append(&2, U32, ps, Nil{}), c):
  match b:
    case True{}:
      (hg, h1) = h
      (_, hr) = h1
      (kept.if.of(Bool.or(D.Mem(List.append(&2, U32, ps, Nil{}), c), U32.is_lt(D.Tg(m, c), 19)), {Cr.Cir.Cells.get(ms, c) == Cr.Cir.Cells.get(m, c) : Cr.Cir.Cell}, hg),
       ih(hr))
    case False{}:
      ((%Equal.sym(Bool, Bool.or(D.Mem(List.append(&2, U32, ps, Nil{}), c), U32.is_lt(D.Tg(m, c), 19)), True{}, kept.cond(m, ps, c, eb)) :
          D.Kept.if(_, {Cr.Cir.Cells.get(ms, c) == Cr.Cir.Cells.get(m, c) : Cr.Cir.Cell}); Unit{}),
       ih(h))

def kept.go(k: Nat, +m: Cr.Cir.Cells, +ms: Cr.Cir.Cells, +c: U32, +ps: List<&2, U32>, +K: U32, +F: U32, +X: List<&2, U32>, +N: U32, +E: List<&2, U32>,
  h: S.Kcs(ms, K, F, X, N, E, Kl(k, m, c, ps))) -> D.Kept.go(k, m, ms, List.append(&2, U32, ps, Nil{}), c):
  match k:
    case 0n:
      Unit{}
    case 1n+(+q):
      kept.go.b(KlC(m, ps, c), q, m, ms, c, ps, K, F, X, N, E, {==}, h, hh => kept.go(q, m, ms, U32.inc(c), ps, K, F, X, N, E, hh))

# a kept cell among the k cells from c keeps its value
def kcs.get.b(b: Bool, +q: Nat, +m: Cr.Cir.Cells, +ms: Cr.Cir.Cells, +c: U32, +x: U32, +ps: List<&2, U32>, +K: U32, +F: U32,
  +X: List<&2, U32>, +N: U32, +E: List<&2, U32>, eb: {KlC(m, ps, c) == b : Bool}, +ex: {U32.is_eq(c, x) == True{} : Bool},
  +hkl: {KlC(m, ps, x) == True{} : Bool},
  h: S.Kcs(ms, K, F, X, N, E, Bool.pick(List<&2, S.Kc>, b, Con{S.Kc{c, Cr.Cir.Cells.get(m, c)}, Kl(q, m, U32.inc(c), ps)}, Kl(q, m, U32.inc(c), ps)))) ->
  {Cr.Cir.Cells.get(ms, x) == Cr.Cir.Cells.get(m, x) : Cr.Cir.Cell}:
  match b:
    case True{}:
      (hg, _) = h
      (%CK.U.eq(c, x, ex) : {Cr.Cir.Cells.get(ms, _) == Cr.Cir.Cells.get(m, _) : Cr.Cir.Cell}; hg)
    case False{}:
      CK.Bo.tf({Cr.Cir.Cells.get(ms, x) == Cr.Cir.Cells.get(m, x) : Cr.Cir.Cell},
        Equal.trans(Bool, False{}, KlC(m, ps, c), True{}, Equal.sym(Bool, KlC(m, ps, c), False{}, eb),
          (%Equal.sym(U32, c, x, CK.U.eq(c, x, ex)) : {KlC(m, ps, _) == True{} : Bool}; hkl)))

def kcs.get.n(b: Bool, +q: Nat, +m: Cr.Cir.Cells, +ms: Cr.Cir.Cells, +c: U32, +ps: List<&2, U32>, +K: U32, +F: U32,
  +X: List<&2, U32>, +N: U32, +E: List<&2, U32>,
  h: S.Kcs(ms, K, F, X, N, E, Bool.pick(List<&2, S.Kc>, b, Con{S.Kc{c, Cr.Cir.Cells.get(m, c)}, Kl(q, m, U32.inc(c), ps)}, Kl(q, m, U32.inc(c), ps)))) ->
  S.Kcs(ms, K, F, X, N, E, Kl(q, m, U32.inc(c), ps)):
  match b:
    case True{}:
      (_, h1) = h
      (_, hr) = h1
      hr
    case False{}:
      h

def kcs.get(k: Nat, +m: Cr.Cir.Cells, +ms: Cr.Cir.Cells, +c: U32, +x: U32, +ps: List<&2, U32>, +K: U32, +F: U32, +X: List<&2, U32>, +N: U32,
  +E: List<&2, U32>, +h: S.Kcs(ms, K, F, X, N, E, Kl(k, m, c, ps)), +hkl: {KlC(m, ps, x) == True{} : Bool},
  +h1: N.Le(U32.to_nat(c), U32.to_nat(x)), +h2: N.Le(1n+U32.to_nat(x), Nat.add(U32.to_nat(c), k))) ->
  {Cr.Cir.Cells.get(ms, x) == Cr.Cir.Cells.get(m, x) : Cr.Cir.Cell}:
  match k:
    case 0n:
      rng.none({Cr.Cir.Cells.get(ms, x) == Cr.Cir.Cells.get(m, x) : Cr.Cir.Cell}, c, x, h1, h2)
    case 1n+(+q):
      bool.case(U32.is_eq(c, x), U32.is_eq(c, x), {Cr.Cir.Cells.get(ms, x) == Cr.Cir.Cells.get(m, x) : Cr.Cir.Cell}, {==},
        e => kcs.get.b(KlC(m, ps, c), q, m, ms, c, x, ps, K, F, X, N, E, {==}, e, hkl, h),
        +e => kcs.get(q, m, ms, U32.inc(c), x, ps, K, F, X, N, E, kcs.get.n(KlC(m, ps, c), q, m, ms, c, ps, K, F, X, N, E, h), hkl,
          rng.lo(q, c, x, e, h1), rng.hi(q, c, x, e, h1, h2)))

# the fields 2 to 4 of a cell that keeps them
def same.fd2(+m: Cr.Cir.Cells, +ms: Cr.Cir.Cells, +p: U32, h: {S.Same.at(m, ms, p) == True{} : Bool}) -> {D.Fd(2n, ms, p) == D.Fd(2n, m, p) : U32}:
  CK.U.eq(S.Fd(2n, ms, p), S.Fd(2n, m, p), CK.Bo.and_l(U32.is_eq(S.Fd(2n, ms, p), S.Fd(2n, m, p)), Bool.and(U32.is_eq(S.Fd(3n, ms, p), S.Fd(3n, m, p)), U32.is_eq(S.Fd(4n, ms, p), S.Fd(4n, m, p))),
    CK.Bo.and_r(U32.is_eq(S.Fd(0n, ms, p), S.Fd(0n, m, p)), Bool.and(U32.is_eq(S.Fd(2n, ms, p), S.Fd(2n, m, p)), Bool.and(U32.is_eq(S.Fd(3n, ms, p), S.Fd(3n, m, p)), U32.is_eq(S.Fd(4n, ms, p), S.Fd(4n, m, p)))), h)))

def same.fd3(+m: Cr.Cir.Cells, +ms: Cr.Cir.Cells, +p: U32, h: {S.Same.at(m, ms, p) == True{} : Bool}) -> {D.Fd(3n, ms, p) == D.Fd(3n, m, p) : U32}:
  CK.U.eq(S.Fd(3n, ms, p), S.Fd(3n, m, p), CK.Bo.and_l(U32.is_eq(S.Fd(3n, ms, p), S.Fd(3n, m, p)), U32.is_eq(S.Fd(4n, ms, p), S.Fd(4n, m, p)),
    CK.Bo.and_r(U32.is_eq(S.Fd(2n, ms, p), S.Fd(2n, m, p)), Bool.and(U32.is_eq(S.Fd(3n, ms, p), S.Fd(3n, m, p)), U32.is_eq(S.Fd(4n, ms, p), S.Fd(4n, m, p))),
      CK.Bo.and_r(U32.is_eq(S.Fd(0n, ms, p), S.Fd(0n, m, p)), Bool.and(U32.is_eq(S.Fd(2n, ms, p), S.Fd(2n, m, p)), Bool.and(U32.is_eq(S.Fd(3n, ms, p), S.Fd(3n, m, p)), U32.is_eq(S.Fd(4n, ms, p), S.Fd(4n, m, p)))), h))))

def same.fd4(+m: Cr.Cir.Cells, +ms: Cr.Cir.Cells, +p: U32, h: {S.Same.at(m, ms, p) == True{} : Bool}) -> {D.Fd(4n, ms, p) == D.Fd(4n, m, p) : U32}:
  CK.U.eq(S.Fd(4n, ms, p), S.Fd(4n, m, p), CK.Bo.and_r(U32.is_eq(S.Fd(3n, ms, p), S.Fd(3n, m, p)), U32.is_eq(S.Fd(4n, ms, p), S.Fd(4n, m, p)),
    CK.Bo.and_r(U32.is_eq(S.Fd(2n, ms, p), S.Fd(2n, m, p)), Bool.and(U32.is_eq(S.Fd(3n, ms, p), S.Fd(3n, m, p)), U32.is_eq(S.Fd(4n, ms, p), S.Fd(4n, m, p))),
      CK.Bo.and_r(U32.is_eq(S.Fd(0n, ms, p), S.Fd(0n, m, p)), Bool.and(U32.is_eq(S.Fd(2n, ms, p), S.Fd(2n, m, p)), Bool.and(U32.is_eq(S.Fd(3n, ms, p), S.Fd(3n, m, p)), U32.is_eq(S.Fd(4n, ms, p), S.Fd(4n, m, p)))), h))))

# the nodes of a kept term are the same after the copy (Node reads fields 2 to 4)
def node.kp(t: Bk.Term, +m: Cr.Cir.Cells, +ms: Cr.Cir.Cells, +r: U32, +c: U32, hk: {Kp(t, m, ms, r) == True{} : Bool}) ->
  {D.Node(t, ms, r, c) == D.Node(t, m, r, c) : Bool}:
  match t:
    case Bk.Term.Var{+i}:
      {==}
    case Bk.Term.Ref{+k}:
      {==}
    case Bk.Term.Ann{+y, +z}:
      +hk2 = hk
      +hs = CK.Bo.and_l(S.Same.at(m, ms, r), Bool.and(Kp(y, m, ms, D.Fd(2n, m, r)), Kp(z, m, ms, D.Fd(3n, m, r))), hk2)
      +hx = CK.Bo.and_r(S.Same.at(m, ms, r), Bool.and(Kp(y, m, ms, D.Fd(2n, m, r)), Kp(z, m, ms, D.Fd(3n, m, r))), hk2)
      +e2 = same.fd2(m, ms, r, hs)
      +e3 = same.fd3(m, ms, r, hs)
      or.cong(U32.is_eq(r, c), U32.is_eq(r, c), Bool.or(D.Node(y, ms, D.Fd(2n, ms, r), c), D.Node(z, ms, D.Fd(3n, ms, r), c)), Bool.or(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c)), {==},
        or.cong(D.Node(y, ms, D.Fd(2n, ms, r), c), D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, ms, D.Fd(3n, ms, r), c), D.Node(z, m, D.Fd(3n, m, r), c),
          Equal.trans(Bool, D.Node(y, ms, D.Fd(2n, ms, r), c), D.Node(y, ms, D.Fd(2n, m, r), c), D.Node(y, m, D.Fd(2n, m, r), c), Equal.cong(U32, Bool, ad => D.Node(y, ms, ad, c), D.Fd(2n, ms, r), D.Fd(2n, m, r), e2), node.kp(y, m, ms, D.Fd(2n, m, r), c, CK.Bo.and_l(Kp(y, m, ms, D.Fd(2n, m, r)), Kp(z, m, ms, D.Fd(3n, m, r)), hx))),
          Equal.trans(Bool, D.Node(z, ms, D.Fd(3n, ms, r), c), D.Node(z, ms, D.Fd(3n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c), Equal.cong(U32, Bool, ad => D.Node(z, ms, ad, c), D.Fd(3n, ms, r), D.Fd(3n, m, r), e3), node.kp(z, m, ms, D.Fd(3n, m, r), c, CK.Bo.and_r(Kp(y, m, ms, D.Fd(2n, m, r)), Kp(z, m, ms, D.Fd(3n, m, r)), hx)))))
    case Bk.Term.Let{+q, +y, +z}:
      +hk2 = hk
      +hs = CK.Bo.and_l(S.Same.at(m, ms, r), Bool.and(Kp(y, m, ms, D.Fd(2n, m, r)), Kp(z, m, ms, D.Fd(3n, m, r))), hk2)
      +hx = CK.Bo.and_r(S.Same.at(m, ms, r), Bool.and(Kp(y, m, ms, D.Fd(2n, m, r)), Kp(z, m, ms, D.Fd(3n, m, r))), hk2)
      +e2 = same.fd2(m, ms, r, hs)
      +e3 = same.fd3(m, ms, r, hs)
      or.cong(U32.is_eq(r, c), U32.is_eq(r, c), Bool.or(D.Node(y, ms, D.Fd(2n, ms, r), c), D.Node(z, ms, D.Fd(3n, ms, r), c)), Bool.or(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c)), {==},
        or.cong(D.Node(y, ms, D.Fd(2n, ms, r), c), D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, ms, D.Fd(3n, ms, r), c), D.Node(z, m, D.Fd(3n, m, r), c),
          Equal.trans(Bool, D.Node(y, ms, D.Fd(2n, ms, r), c), D.Node(y, ms, D.Fd(2n, m, r), c), D.Node(y, m, D.Fd(2n, m, r), c), Equal.cong(U32, Bool, ad => D.Node(y, ms, ad, c), D.Fd(2n, ms, r), D.Fd(2n, m, r), e2), node.kp(y, m, ms, D.Fd(2n, m, r), c, CK.Bo.and_l(Kp(y, m, ms, D.Fd(2n, m, r)), Kp(z, m, ms, D.Fd(3n, m, r)), hx))),
          Equal.trans(Bool, D.Node(z, ms, D.Fd(3n, ms, r), c), D.Node(z, ms, D.Fd(3n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c), Equal.cong(U32, Bool, ad => D.Node(z, ms, ad, c), D.Fd(3n, ms, r), D.Fd(3n, m, r), e3), node.kp(z, m, ms, D.Fd(3n, m, r), c, CK.Bo.and_r(Kp(y, m, ms, D.Fd(2n, m, r)), Kp(z, m, ms, D.Fd(3n, m, r)), hx)))))
    case Bk.Term.Typ{+y}:
      +hk2 = hk
      +hs = CK.Bo.and_l(S.Same.at(m, ms, r), Kp(y, m, ms, D.Fd(2n, m, r)), hk2)
      +hx = CK.Bo.and_r(S.Same.at(m, ms, r), Kp(y, m, ms, D.Fd(2n, m, r)), hk2)
      +e2 = same.fd2(m, ms, r, hs)
      or.cong(U32.is_eq(r, c), U32.is_eq(r, c), D.Node(y, ms, D.Fd(2n, ms, r), c), D.Node(y, m, D.Fd(2n, m, r), c), {==},
        Equal.trans(Bool, D.Node(y, ms, D.Fd(2n, ms, r), c), D.Node(y, ms, D.Fd(2n, m, r), c), D.Node(y, m, D.Fd(2n, m, r), c), Equal.cong(U32, Bool, ad => D.Node(y, ms, ad, c), D.Fd(2n, ms, r), D.Fd(2n, m, r), e2), node.kp(y, m, ms, D.Fd(2n, m, r), c, hx)))
    case Bk.Term.Min{+y, +z}:
      +hk2 = hk
      +hs = CK.Bo.and_l(S.Same.at(m, ms, r), Bool.and(Kp(y, m, ms, D.Fd(2n, m, r)), Kp(z, m, ms, D.Fd(3n, m, r))), hk2)
      +hx = CK.Bo.and_r(S.Same.at(m, ms, r), Bool.and(Kp(y, m, ms, D.Fd(2n, m, r)), Kp(z, m, ms, D.Fd(3n, m, r))), hk2)
      +e2 = same.fd2(m, ms, r, hs)
      +e3 = same.fd3(m, ms, r, hs)
      or.cong(U32.is_eq(r, c), U32.is_eq(r, c), Bool.or(D.Node(y, ms, D.Fd(2n, ms, r), c), D.Node(z, ms, D.Fd(3n, ms, r), c)), Bool.or(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c)), {==},
        or.cong(D.Node(y, ms, D.Fd(2n, ms, r), c), D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, ms, D.Fd(3n, ms, r), c), D.Node(z, m, D.Fd(3n, m, r), c),
          Equal.trans(Bool, D.Node(y, ms, D.Fd(2n, ms, r), c), D.Node(y, ms, D.Fd(2n, m, r), c), D.Node(y, m, D.Fd(2n, m, r), c), Equal.cong(U32, Bool, ad => D.Node(y, ms, ad, c), D.Fd(2n, ms, r), D.Fd(2n, m, r), e2), node.kp(y, m, ms, D.Fd(2n, m, r), c, CK.Bo.and_l(Kp(y, m, ms, D.Fd(2n, m, r)), Kp(z, m, ms, D.Fd(3n, m, r)), hx))),
          Equal.trans(Bool, D.Node(z, ms, D.Fd(3n, ms, r), c), D.Node(z, ms, D.Fd(3n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c), Equal.cong(U32, Bool, ad => D.Node(z, ms, ad, c), D.Fd(3n, ms, r), D.Fd(3n, m, r), e3), node.kp(z, m, ms, D.Fd(3n, m, r), c, CK.Bo.and_r(Kp(y, m, ms, D.Fd(2n, m, r)), Kp(z, m, ms, D.Fd(3n, m, r)), hx)))))
    case Bk.Term.All{+q, +y, +z}:
      +hk2 = hk
      +hs = CK.Bo.and_l(S.Same.at(m, ms, r), Bool.and(Kp(y, m, ms, D.Fd(2n, m, r)), Kp(z, m, ms, D.Fd(3n, m, r))), hk2)
      +hx = CK.Bo.and_r(S.Same.at(m, ms, r), Bool.and(Kp(y, m, ms, D.Fd(2n, m, r)), Kp(z, m, ms, D.Fd(3n, m, r))), hk2)
      +e2 = same.fd2(m, ms, r, hs)
      +e3 = same.fd3(m, ms, r, hs)
      or.cong(U32.is_eq(r, c), U32.is_eq(r, c), Bool.or(D.Node(y, ms, D.Fd(2n, ms, r), c), D.Node(z, ms, D.Fd(3n, ms, r), c)), Bool.or(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c)), {==},
        or.cong(D.Node(y, ms, D.Fd(2n, ms, r), c), D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, ms, D.Fd(3n, ms, r), c), D.Node(z, m, D.Fd(3n, m, r), c),
          Equal.trans(Bool, D.Node(y, ms, D.Fd(2n, ms, r), c), D.Node(y, ms, D.Fd(2n, m, r), c), D.Node(y, m, D.Fd(2n, m, r), c), Equal.cong(U32, Bool, ad => D.Node(y, ms, ad, c), D.Fd(2n, ms, r), D.Fd(2n, m, r), e2), node.kp(y, m, ms, D.Fd(2n, m, r), c, CK.Bo.and_l(Kp(y, m, ms, D.Fd(2n, m, r)), Kp(z, m, ms, D.Fd(3n, m, r)), hx))),
          Equal.trans(Bool, D.Node(z, ms, D.Fd(3n, ms, r), c), D.Node(z, ms, D.Fd(3n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c), Equal.cong(U32, Bool, ad => D.Node(z, ms, ad, c), D.Fd(3n, ms, r), D.Fd(3n, m, r), e3), node.kp(z, m, ms, D.Fd(3n, m, r), c, CK.Bo.and_r(Kp(y, m, ms, D.Fd(2n, m, r)), Kp(z, m, ms, D.Fd(3n, m, r)), hx)))))
    case Bk.Term.Lam{+q, +y}:
      +hk2 = hk
      +hs = CK.Bo.and_l(S.Same.at(m, ms, r), Kp(y, m, ms, D.Fd(2n, m, r)), hk2)
      +hx = CK.Bo.and_r(S.Same.at(m, ms, r), Kp(y, m, ms, D.Fd(2n, m, r)), hk2)
      +e2 = same.fd2(m, ms, r, hs)
      or.cong(U32.is_eq(r, c), U32.is_eq(r, c), D.Node(y, ms, D.Fd(2n, ms, r), c), D.Node(y, m, D.Fd(2n, m, r), c), {==},
        Equal.trans(Bool, D.Node(y, ms, D.Fd(2n, ms, r), c), D.Node(y, ms, D.Fd(2n, m, r), c), D.Node(y, m, D.Fd(2n, m, r), c), Equal.cong(U32, Bool, ad => D.Node(y, ms, ad, c), D.Fd(2n, ms, r), D.Fd(2n, m, r), e2), node.kp(y, m, ms, D.Fd(2n, m, r), c, hx)))
    case Bk.Term.App{+q, +y, +z}:
      +hk2 = hk
      +hs = CK.Bo.and_l(S.Same.at(m, ms, r), Bool.and(Kp(y, m, ms, D.Fd(2n, m, r)), Kp(z, m, ms, D.Fd(3n, m, r))), hk2)
      +hx = CK.Bo.and_r(S.Same.at(m, ms, r), Bool.and(Kp(y, m, ms, D.Fd(2n, m, r)), Kp(z, m, ms, D.Fd(3n, m, r))), hk2)
      +e2 = same.fd2(m, ms, r, hs)
      +e3 = same.fd3(m, ms, r, hs)
      or.cong(U32.is_eq(r, c), U32.is_eq(r, c), Bool.or(D.Node(y, ms, D.Fd(2n, ms, r), c), D.Node(z, ms, D.Fd(3n, ms, r), c)), Bool.or(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c)), {==},
        or.cong(D.Node(y, ms, D.Fd(2n, ms, r), c), D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, ms, D.Fd(3n, ms, r), c), D.Node(z, m, D.Fd(3n, m, r), c),
          Equal.trans(Bool, D.Node(y, ms, D.Fd(2n, ms, r), c), D.Node(y, ms, D.Fd(2n, m, r), c), D.Node(y, m, D.Fd(2n, m, r), c), Equal.cong(U32, Bool, ad => D.Node(y, ms, ad, c), D.Fd(2n, ms, r), D.Fd(2n, m, r), e2), node.kp(y, m, ms, D.Fd(2n, m, r), c, CK.Bo.and_l(Kp(y, m, ms, D.Fd(2n, m, r)), Kp(z, m, ms, D.Fd(3n, m, r)), hx))),
          Equal.trans(Bool, D.Node(z, ms, D.Fd(3n, ms, r), c), D.Node(z, ms, D.Fd(3n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c), Equal.cong(U32, Bool, ad => D.Node(z, ms, ad, c), D.Fd(3n, ms, r), D.Fd(3n, m, r), e3), node.kp(z, m, ms, D.Fd(3n, m, r), c, CK.Bo.and_r(Kp(y, m, ms, D.Fd(2n, m, r)), Kp(z, m, ms, D.Fd(3n, m, r)), hx)))))
    case Bk.Term.Sig{+q, +y, +z}:
      +hk2 = hk
      +hs = CK.Bo.and_l(S.Same.at(m, ms, r), Bool.and(Kp(y, m, ms, D.Fd(2n, m, r)), Kp(z, m, ms, D.Fd(3n, m, r))), hk2)
      +hx = CK.Bo.and_r(S.Same.at(m, ms, r), Bool.and(Kp(y, m, ms, D.Fd(2n, m, r)), Kp(z, m, ms, D.Fd(3n, m, r))), hk2)
      +e2 = same.fd2(m, ms, r, hs)
      +e3 = same.fd3(m, ms, r, hs)
      or.cong(U32.is_eq(r, c), U32.is_eq(r, c), Bool.or(D.Node(y, ms, D.Fd(2n, ms, r), c), D.Node(z, ms, D.Fd(3n, ms, r), c)), Bool.or(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c)), {==},
        or.cong(D.Node(y, ms, D.Fd(2n, ms, r), c), D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, ms, D.Fd(3n, ms, r), c), D.Node(z, m, D.Fd(3n, m, r), c),
          Equal.trans(Bool, D.Node(y, ms, D.Fd(2n, ms, r), c), D.Node(y, ms, D.Fd(2n, m, r), c), D.Node(y, m, D.Fd(2n, m, r), c), Equal.cong(U32, Bool, ad => D.Node(y, ms, ad, c), D.Fd(2n, ms, r), D.Fd(2n, m, r), e2), node.kp(y, m, ms, D.Fd(2n, m, r), c, CK.Bo.and_l(Kp(y, m, ms, D.Fd(2n, m, r)), Kp(z, m, ms, D.Fd(3n, m, r)), hx))),
          Equal.trans(Bool, D.Node(z, ms, D.Fd(3n, ms, r), c), D.Node(z, ms, D.Fd(3n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c), Equal.cong(U32, Bool, ad => D.Node(z, ms, ad, c), D.Fd(3n, ms, r), D.Fd(3n, m, r), e3), node.kp(z, m, ms, D.Fd(3n, m, r), c, CK.Bo.and_r(Kp(y, m, ms, D.Fd(2n, m, r)), Kp(z, m, ms, D.Fd(3n, m, r)), hx)))))
    case Bk.Term.Tup{+q, +y, +z}:
      +hk2 = hk
      +hs = CK.Bo.and_l(S.Same.at(m, ms, r), Bool.and(Kp(y, m, ms, D.Fd(2n, m, r)), Kp(z, m, ms, D.Fd(3n, m, r))), hk2)
      +hx = CK.Bo.and_r(S.Same.at(m, ms, r), Bool.and(Kp(y, m, ms, D.Fd(2n, m, r)), Kp(z, m, ms, D.Fd(3n, m, r))), hk2)
      +e2 = same.fd2(m, ms, r, hs)
      +e3 = same.fd3(m, ms, r, hs)
      or.cong(U32.is_eq(r, c), U32.is_eq(r, c), Bool.or(D.Node(y, ms, D.Fd(2n, ms, r), c), D.Node(z, ms, D.Fd(3n, ms, r), c)), Bool.or(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c)), {==},
        or.cong(D.Node(y, ms, D.Fd(2n, ms, r), c), D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, ms, D.Fd(3n, ms, r), c), D.Node(z, m, D.Fd(3n, m, r), c),
          Equal.trans(Bool, D.Node(y, ms, D.Fd(2n, ms, r), c), D.Node(y, ms, D.Fd(2n, m, r), c), D.Node(y, m, D.Fd(2n, m, r), c), Equal.cong(U32, Bool, ad => D.Node(y, ms, ad, c), D.Fd(2n, ms, r), D.Fd(2n, m, r), e2), node.kp(y, m, ms, D.Fd(2n, m, r), c, CK.Bo.and_l(Kp(y, m, ms, D.Fd(2n, m, r)), Kp(z, m, ms, D.Fd(3n, m, r)), hx))),
          Equal.trans(Bool, D.Node(z, ms, D.Fd(3n, ms, r), c), D.Node(z, ms, D.Fd(3n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c), Equal.cong(U32, Bool, ad => D.Node(z, ms, ad, c), D.Fd(3n, ms, r), D.Fd(3n, m, r), e3), node.kp(z, m, ms, D.Fd(3n, m, r), c, CK.Bo.and_r(Kp(y, m, ms, D.Fd(2n, m, r)), Kp(z, m, ms, D.Fd(3n, m, r)), hx)))))
    case Bk.Term.Prj{+y}:
      +hk2 = hk
      +hs = CK.Bo.and_l(S.Same.at(m, ms, r), Kp(y, m, ms, D.Fd(2n, m, r)), hk2)
      +hx = CK.Bo.and_r(S.Same.at(m, ms, r), Kp(y, m, ms, D.Fd(2n, m, r)), hk2)
      +e2 = same.fd2(m, ms, r, hs)
      or.cong(U32.is_eq(r, c), U32.is_eq(r, c), D.Node(y, ms, D.Fd(2n, ms, r), c), D.Node(y, m, D.Fd(2n, m, r), c), {==},
        Equal.trans(Bool, D.Node(y, ms, D.Fd(2n, ms, r), c), D.Node(y, ms, D.Fd(2n, m, r), c), D.Node(y, m, D.Fd(2n, m, r), c), Equal.cong(U32, Bool, ad => D.Node(y, ms, ad, c), D.Fd(2n, ms, r), D.Fd(2n, m, r), e2), node.kp(y, m, ms, D.Fd(2n, m, r), c, hx)))
    case Bk.Term.Enu{+k}:
      {==}
    case Bk.Term.Lab{+k}:
      {==}
    case Bk.Term.Mat{+k, +y, +z}:
      +hk2 = hk
      +hs = CK.Bo.and_l(S.Same.at(m, ms, r), Bool.and(Kp(y, m, ms, D.Fd(3n, m, r)), Kp(z, m, ms, D.Fd(4n, m, r))), hk2)
      +hx = CK.Bo.and_r(S.Same.at(m, ms, r), Bool.and(Kp(y, m, ms, D.Fd(3n, m, r)), Kp(z, m, ms, D.Fd(4n, m, r))), hk2)
      +e3 = same.fd3(m, ms, r, hs)
      +e4 = same.fd4(m, ms, r, hs)
      or.cong(U32.is_eq(r, c), U32.is_eq(r, c), Bool.or(D.Node(y, ms, D.Fd(3n, ms, r), c), D.Node(z, ms, D.Fd(4n, ms, r), c)), Bool.or(D.Node(y, m, D.Fd(3n, m, r), c), D.Node(z, m, D.Fd(4n, m, r), c)), {==},
        or.cong(D.Node(y, ms, D.Fd(3n, ms, r), c), D.Node(y, m, D.Fd(3n, m, r), c), D.Node(z, ms, D.Fd(4n, ms, r), c), D.Node(z, m, D.Fd(4n, m, r), c),
          Equal.trans(Bool, D.Node(y, ms, D.Fd(3n, ms, r), c), D.Node(y, ms, D.Fd(3n, m, r), c), D.Node(y, m, D.Fd(3n, m, r), c), Equal.cong(U32, Bool, ad => D.Node(y, ms, ad, c), D.Fd(3n, ms, r), D.Fd(3n, m, r), e3), node.kp(y, m, ms, D.Fd(3n, m, r), c, CK.Bo.and_l(Kp(y, m, ms, D.Fd(3n, m, r)), Kp(z, m, ms, D.Fd(4n, m, r)), hx))),
          Equal.trans(Bool, D.Node(z, ms, D.Fd(4n, ms, r), c), D.Node(z, ms, D.Fd(4n, m, r), c), D.Node(z, m, D.Fd(4n, m, r), c), Equal.cong(U32, Bool, ad => D.Node(z, ms, ad, c), D.Fd(4n, ms, r), D.Fd(4n, m, r), e4), node.kp(z, m, ms, D.Fd(4n, m, r), c, CK.Bo.and_r(Kp(y, m, ms, D.Fd(3n, m, r)), Kp(z, m, ms, D.Fd(4n, m, r)), hx)))))
    case Bk.Term.Efq{}:
      {==}
    case Bk.Term.Eql{+y, +z, +w}:
      +hk2 = hk
      +hs = CK.Bo.and_l(S.Same.at(m, ms, r), Bool.and(Kp(y, m, ms, D.Fd(2n, m, r)), Bool.and(Kp(z, m, ms, D.Fd(3n, m, r)), Kp(w, m, ms, D.Fd(4n, m, r)))), hk2)
      +hx = CK.Bo.and_r(S.Same.at(m, ms, r), Bool.and(Kp(y, m, ms, D.Fd(2n, m, r)), Bool.and(Kp(z, m, ms, D.Fd(3n, m, r)), Kp(w, m, ms, D.Fd(4n, m, r)))), hk2)
      +e2 = same.fd2(m, ms, r, hs)
      +e3 = same.fd3(m, ms, r, hs)
      +e4 = same.fd4(m, ms, r, hs)
      or.cong(U32.is_eq(r, c), U32.is_eq(r, c), Bool.or(D.Node(y, ms, D.Fd(2n, ms, r), c), Bool.or(D.Node(z, ms, D.Fd(3n, ms, r), c), D.Node(w, ms, D.Fd(4n, ms, r), c))), Bool.or(D.Node(y, m, D.Fd(2n, m, r), c), Bool.or(D.Node(z, m, D.Fd(3n, m, r), c), D.Node(w, m, D.Fd(4n, m, r), c))), {==},
        or.cong(D.Node(y, ms, D.Fd(2n, ms, r), c), D.Node(y, m, D.Fd(2n, m, r), c), Bool.or(D.Node(z, ms, D.Fd(3n, ms, r), c), D.Node(w, ms, D.Fd(4n, ms, r), c)), Bool.or(D.Node(z, m, D.Fd(3n, m, r), c), D.Node(w, m, D.Fd(4n, m, r), c)),
          Equal.trans(Bool, D.Node(y, ms, D.Fd(2n, ms, r), c), D.Node(y, ms, D.Fd(2n, m, r), c), D.Node(y, m, D.Fd(2n, m, r), c), Equal.cong(U32, Bool, ad => D.Node(y, ms, ad, c), D.Fd(2n, ms, r), D.Fd(2n, m, r), e2), node.kp(y, m, ms, D.Fd(2n, m, r), c, CK.Bo.and_l(Kp(y, m, ms, D.Fd(2n, m, r)), Bool.and(Kp(z, m, ms, D.Fd(3n, m, r)), Kp(w, m, ms, D.Fd(4n, m, r))), hx))),
          or.cong(D.Node(z, ms, D.Fd(3n, ms, r), c), D.Node(z, m, D.Fd(3n, m, r), c), D.Node(w, ms, D.Fd(4n, ms, r), c), D.Node(w, m, D.Fd(4n, m, r), c),
          Equal.trans(Bool, D.Node(z, ms, D.Fd(3n, ms, r), c), D.Node(z, ms, D.Fd(3n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c), Equal.cong(U32, Bool, ad => D.Node(z, ms, ad, c), D.Fd(3n, ms, r), D.Fd(3n, m, r), e3), node.kp(z, m, ms, D.Fd(3n, m, r), c, CK.Bo.and_l(Kp(z, m, ms, D.Fd(3n, m, r)), Kp(w, m, ms, D.Fd(4n, m, r)), CK.Bo.and_r(Kp(y, m, ms, D.Fd(2n, m, r)), Bool.and(Kp(z, m, ms, D.Fd(3n, m, r)), Kp(w, m, ms, D.Fd(4n, m, r))), hx)))),
          Equal.trans(Bool, D.Node(w, ms, D.Fd(4n, ms, r), c), D.Node(w, ms, D.Fd(4n, m, r), c), D.Node(w, m, D.Fd(4n, m, r), c), Equal.cong(U32, Bool, ad => D.Node(w, ms, ad, c), D.Fd(4n, ms, r), D.Fd(4n, m, r), e4), node.kp(w, m, ms, D.Fd(4n, m, r), c, CK.Bo.and_r(Kp(z, m, ms, D.Fd(3n, m, r)), Kp(w, m, ms, D.Fd(4n, m, r)), CK.Bo.and_r(Kp(y, m, ms, D.Fd(2n, m, r)), Bool.and(Kp(z, m, ms, D.Fd(3n, m, r)), Kp(w, m, ms, D.Fd(4n, m, r))), hx)))))))
    case Bk.Term.Rfl{}:
      {==}
    case Bk.Term.Rwt{+y, +z, +w}:
      +hk2 = hk
      +hs = CK.Bo.and_l(S.Same.at(m, ms, r), Bool.and(Kp(y, m, ms, D.Fd(2n, m, r)), Bool.and(Kp(z, m, ms, D.Fd(3n, m, r)), Kp(w, m, ms, D.Fd(4n, m, r)))), hk2)
      +hx = CK.Bo.and_r(S.Same.at(m, ms, r), Bool.and(Kp(y, m, ms, D.Fd(2n, m, r)), Bool.and(Kp(z, m, ms, D.Fd(3n, m, r)), Kp(w, m, ms, D.Fd(4n, m, r)))), hk2)
      +e2 = same.fd2(m, ms, r, hs)
      +e3 = same.fd3(m, ms, r, hs)
      +e4 = same.fd4(m, ms, r, hs)
      or.cong(U32.is_eq(r, c), U32.is_eq(r, c), Bool.or(D.Node(y, ms, D.Fd(2n, ms, r), c), Bool.or(D.Node(z, ms, D.Fd(3n, ms, r), c), D.Node(w, ms, D.Fd(4n, ms, r), c))), Bool.or(D.Node(y, m, D.Fd(2n, m, r), c), Bool.or(D.Node(z, m, D.Fd(3n, m, r), c), D.Node(w, m, D.Fd(4n, m, r), c))), {==},
        or.cong(D.Node(y, ms, D.Fd(2n, ms, r), c), D.Node(y, m, D.Fd(2n, m, r), c), Bool.or(D.Node(z, ms, D.Fd(3n, ms, r), c), D.Node(w, ms, D.Fd(4n, ms, r), c)), Bool.or(D.Node(z, m, D.Fd(3n, m, r), c), D.Node(w, m, D.Fd(4n, m, r), c)),
          Equal.trans(Bool, D.Node(y, ms, D.Fd(2n, ms, r), c), D.Node(y, ms, D.Fd(2n, m, r), c), D.Node(y, m, D.Fd(2n, m, r), c), Equal.cong(U32, Bool, ad => D.Node(y, ms, ad, c), D.Fd(2n, ms, r), D.Fd(2n, m, r), e2), node.kp(y, m, ms, D.Fd(2n, m, r), c, CK.Bo.and_l(Kp(y, m, ms, D.Fd(2n, m, r)), Bool.and(Kp(z, m, ms, D.Fd(3n, m, r)), Kp(w, m, ms, D.Fd(4n, m, r))), hx))),
          or.cong(D.Node(z, ms, D.Fd(3n, ms, r), c), D.Node(z, m, D.Fd(3n, m, r), c), D.Node(w, ms, D.Fd(4n, ms, r), c), D.Node(w, m, D.Fd(4n, m, r), c),
          Equal.trans(Bool, D.Node(z, ms, D.Fd(3n, ms, r), c), D.Node(z, ms, D.Fd(3n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c), Equal.cong(U32, Bool, ad => D.Node(z, ms, ad, c), D.Fd(3n, ms, r), D.Fd(3n, m, r), e3), node.kp(z, m, ms, D.Fd(3n, m, r), c, CK.Bo.and_l(Kp(z, m, ms, D.Fd(3n, m, r)), Kp(w, m, ms, D.Fd(4n, m, r)), CK.Bo.and_r(Kp(y, m, ms, D.Fd(2n, m, r)), Bool.and(Kp(z, m, ms, D.Fd(3n, m, r)), Kp(w, m, ms, D.Fd(4n, m, r))), hx)))),
          Equal.trans(Bool, D.Node(w, ms, D.Fd(4n, ms, r), c), D.Node(w, ms, D.Fd(4n, m, r), c), D.Node(w, m, D.Fd(4n, m, r), c), Equal.cong(U32, Bool, ad => D.Node(w, ms, ad, c), D.Fd(4n, ms, r), D.Fd(4n, m, r), e4), node.kp(w, m, ms, D.Fd(4n, m, r), c, CK.Bo.and_r(Kp(z, m, ms, D.Fd(3n, m, r)), Kp(w, m, ms, D.Fd(4n, m, r)), CK.Bo.and_r(Kp(y, m, ms, D.Fd(2n, m, r)), Bool.and(Kp(z, m, ms, D.Fd(3n, m, r)), Kp(w, m, ms, D.Fd(4n, m, r))), hx)))))))

# Live structures after the copy
# ------------------------------
#
# KF: what Post says that keeps the live terms (Kept, Same, the taken cells
# were garbage or new) and the bounds im < fi <= nx <= nx2. With it, a live
# term stands for itself after the copy (live.kept), and so the owned and
# borrowed roots, the frames and the image stay (HS's parts).

def KF(+m: Cr.Cir.Cells, +ms: Cr.Cir.Cells, +nx: U32, +nx2: U32, +fi: U32, +im: U32, +L: List<&2, D.Rt>, +Y: List<&2, U32>,
  +T: List<&2, U32>, +Pn: List<&2, U32>, +n2: Nat, +Q: List<&2, U32>, +Qn: List<&2, U32>, +rr: U32) -> Data:
  D.P2({S.Kept(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, ms, fi, T, Pn, fi, Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), n2, Q, Qn, Nil{}, [rr]) == True{} : Bool},
  D.P2({S.Same(U32.to_nat(im), m, ms, 1) == True{} : Bool},
  D.P2({S.Incl.go(T, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, L, Y), nx) == True{} : Bool},
  D.P2({U32.is_lt(im, fi) == True{} : Bool}, D.P2({U32.is_le(fi, nx) == True{} : Bool}, {U32.is_le(nx, nx2) == True{} : Bool})))))

def kf.n2(-m: Cr.Cir.Cells, -ms: Cr.Cir.Cells, -nx: U32, -nx2: U32, -fi: U32, -im: U32, -L: List<&2, D.Rt>, -Y: List<&2, U32>,
  -T: List<&2, U32>, -Pn: List<&2, U32>, -n2: Nat, -Q: List<&2, U32>, -Qn: List<&2, U32>, -rr: U32,
  k: KF(m, ms, nx, nx2, fi, im, L, Y, T, Pn, n2, Q, Qn, rr)) -> {U32.is_le(nx, nx2) == True{} : Bool}:
  (_, k1) = k
  (_, k2) = k1
  (_, k3) = k2
  (_, k4) = k3
  (_, a) = k4
  a

def kf.ig(-m: Cr.Cir.Cells, -ms: Cr.Cir.Cells, -nx: U32, -nx2: U32, -fi: U32, -im: U32, -L: List<&2, D.Rt>, -Y: List<&2, U32>,
  -T: List<&2, U32>, -Pn: List<&2, U32>, -n2: Nat, -Q: List<&2, U32>, -Qn: List<&2, U32>, -rr: U32,
  k: KF(m, ms, nx, nx2, fi, im, L, Y, T, Pn, n2, Q, Qn, rr)) -> {S.Incl.go(T, Gb.of(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, L, Y), nx) == True{} : Bool}:
  (_, k1) = k
  (_, k2) = k1
  (a, _) = k2
  a

def kf.kf(-m: Cr.Cir.Cells, -ms: Cr.Cir.Cells, -nx: U32, -nx2: U32, -fi: U32, -im: U32, -L: List<&2, D.Rt>, -Y: List<&2, U32>,
  -T: List<&2, U32>, -Pn: List<&2, U32>, -n2: Nat, -Q: List<&2, U32>, -Qn: List<&2, U32>, -rr: U32,
  k: KF(m, ms, nx, nx2, fi, im, L, Y, T, Pn, n2, Q, Qn, rr)) -> {U32.is_lt(im, fi) == True{} : Bool}:
  (_, k1) = k
  (_, k2) = k1
  (_, k3) = k2
  (a, _) = k3
  a

def kf.fn(-m: Cr.Cir.Cells, -ms: Cr.Cir.Cells, -nx: U32, -nx2: U32, -fi: U32, -im: U32, -L: List<&2, D.Rt>, -Y: List<&2, U32>,
  -T: List<&2, U32>, -Pn: List<&2, U32>, -n2: Nat, -Q: List<&2, U32>, -Qn: List<&2, U32>, -rr: U32,
  k: KF(m, ms, nx, nx2, fi, im, L, Y, T, Pn, n2, Q, Qn, rr)) -> {U32.is_le(fi, nx) == True{} : Bool}:
  (_, k1) = k
  (_, k2) = k1
  (_, k3) = k2
  (_, k4) = k3
  (a, _) = k4
  a

# a live node keeps its fields 0, 2, 3 and 4
def kf.node(+m: Cr.Cir.Cells, +ms: Cr.Cir.Cells, +nx: U32, +nx2: U32, +fi: U32, +im: U32, +L: List<&2, D.Rt>, +Y: List<&2, U32>,
  +T: List<&2, U32>, +Pn: List<&2, U32>, +n2: Nat, +Q: List<&2, U32>, +Qn: List<&2, U32>, +rr: U32,
  k: KF(m, ms, nx, nx2, fi, im, L, Y, T, Pn, n2, Q, Qn, rr), +x: U32, +hx: {Cr.Cir.is_cell(x, im, fi, nx) == True{} : Bool},
  hlv: {Lv0(m, L, x) == True{} : Bool}) -> {S.Same.at(m, ms, x) == True{} : Bool}:
  (hkept, k1) = k
  (hsame, k2) = k1
  (hig, k3) = k2
  (hKF, k4) = k3
  (hfn, _) = k4
  same.node(m, ms, x, im, fi, nx, L, Y, T, Pn, n2, Q, Qn, rr, hx, hlv, hkept, hsame, hig, hKF, hfn)

# the root of a live term is live
def ln.root(t: Bk.Term, +m: Cr.Cir.Cells, +r: U32, +L: List<&2, D.Rt>, h: {Ln(t, m, r, L) == True{} : Bool}) -> {Lv0(m, L, r) == True{} : Bool}:
  match t:
    case Bk.Term.Var{+i}:
      h
    case Bk.Term.Ref{+k}:
      h
    case Bk.Term.Ann{+y, +z}:
      CK.Bo.and_l(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L)), h)
    case Bk.Term.Let{+q, +y, +z}:
      CK.Bo.and_l(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L)), h)
    case Bk.Term.Typ{+y}:
      CK.Bo.and_l(Lv0(m, L, r), Ln(y, m, D.Fd(2n, m, r), L), h)
    case Bk.Term.Min{+y, +z}:
      CK.Bo.and_l(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L)), h)
    case Bk.Term.All{+q, +y, +z}:
      CK.Bo.and_l(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L)), h)
    case Bk.Term.Lam{+q, +y}:
      CK.Bo.and_l(Lv0(m, L, r), Ln(y, m, D.Fd(2n, m, r), L), h)
    case Bk.Term.App{+q, +y, +z}:
      CK.Bo.and_l(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L)), h)
    case Bk.Term.Sig{+q, +y, +z}:
      CK.Bo.and_l(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L)), h)
    case Bk.Term.Tup{+q, +y, +z}:
      CK.Bo.and_l(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(2n, m, r), L), Ln(z, m, D.Fd(3n, m, r), L)), h)
    case Bk.Term.Prj{+y}:
      CK.Bo.and_l(Lv0(m, L, r), Ln(y, m, D.Fd(2n, m, r), L), h)
    case Bk.Term.Enu{+k}:
      h
    case Bk.Term.Lab{+k}:
      h
    case Bk.Term.Mat{+k, +y, +z}:
      CK.Bo.and_l(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(3n, m, r), L), Ln(z, m, D.Fd(4n, m, r), L)), h)
    case Bk.Term.Efq{}:
      h
    case Bk.Term.Eql{+y, +z, +w}:
      CK.Bo.and_l(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(2n, m, r), L), Bool.and(Ln(z, m, D.Fd(3n, m, r), L), Ln(w, m, D.Fd(4n, m, r), L))), h)
    case Bk.Term.Rfl{}:
      h
    case Bk.Term.Rwt{+y, +z, +w}:
      CK.Bo.and_l(Lv0(m, L, r), Bool.and(Ln(y, m, D.Fd(2n, m, r), L), Bool.and(Ln(z, m, D.Fd(3n, m, r), L), Ln(w, m, D.Fd(4n, m, r), L))), h)

# a live term (Ln) stands for itself after the copy
def live.kept(+t: Bk.Term, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +ms: Cr.Cir.Cells,
  +nx: U32, +nx2: U32, +fi: U32, +im: U32, +L: List<&2, D.Rt>, +Y: List<&2, U32>, +T: List<&2, U32>, +Pn: List<&2, U32>, +n2: Nat,
  +Q: List<&2, U32>, +Qn: List<&2, U32>, +rr: U32, +k: KF(m, ms, nx, nx2, fi, im, L, Y, T, Pn, n2, Q, Qn, rr), +r: U32,
  +h: D.IsK(True{}, ds, m, im, fi, nx, ks, img, r, t), hln: {Ln(t, m, r, L) == True{} : Bool}) -> D.IsK(True{}, ds, ms, im, fi, nx2, ks, img, r, t):
  (hkept, k1) = k
  (hsame, k2) = k1
  (hig, k3) = k2
  (hKF, k4) = k3
  (hfn, hn) = k4
  isk.kept(t, True{}, ds, m, ms, im, fi, nx, nx2, ks, img, r, h,
    kp.ln(t, True{}, ds, m, ms, im, fi, nx, ks, img, L, Y, T, Pn, n2, Q, Qn, rr, r, h, hln, hkept, hsame, hig, hKF, hfn), hn)

# and its nodes are the same
def live.nodes(+t: Bk.Term, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +ms: Cr.Cir.Cells,
  +nx: U32, +nx2: U32, +fi: U32, +im: U32, +L: List<&2, D.Rt>, +Y: List<&2, U32>, +T: List<&2, U32>, +Pn: List<&2, U32>, +n2: Nat,
  +Q: List<&2, U32>, +Qn: List<&2, U32>, +rr: U32, +k: KF(m, ms, nx, nx2, fi, im, L, Y, T, Pn, n2, Q, Qn, rr), +r: U32, +c: U32,
  +h: D.IsK(True{}, ds, m, im, fi, nx, ks, img, r, t), hln: {Ln(t, m, r, L) == True{} : Bool}) -> {D.Node(t, ms, r, c) == D.Node(t, m, r, c) : Bool}:
  (hkept, k1) = k
  (hsame, k2) = k1
  (hig, k3) = k2
  (hKF, k4) = k3
  (hfn, hn) = k4
  node.kp(t, m, ms, r, c, kp.ln(t, True{}, ds, m, ms, im, fi, nx, ks, img, L, Y, T, Pn, n2, Q, Qn, rr, r, h, hln, hkept, hsame, hig, hKF, hfn))

# the roots R, each a node of a live term, stand for their terms after the copy
def rts.kept(R: List<&2, D.Rt>, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells,
  +ms: Cr.Cir.Cells, +nx: U32, +nx2: U32, +fi: U32, +im: U32, +os: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +fs: List<&2, D.AF>, +sp: U32,
  +ps: List<&2, U32>, +zs: List<&2, D.Rt>, +g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs), +T: List<&2, U32>, +Pn: List<&2, U32>,
  +n2: Nat, +Qn: List<&2, U32>, +rr: U32,
  +k: KF(m, ms, nx, nx2, fi, im, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs)), T, Pn, n2, ps, Qn, rr),
  hR: D.RtsK(True{}, ds, m, im, fi, nx, ks, img, R), hN: {NdAll(D.Rt.cells(R), Lst(os, D.Tmp.held(xs), fs, m, sp), m) == True{} : Bool}) ->
  D.RtsK(True{}, ds, ms, im, fi, nx2, ks, img, R):
  match R:
    case Nil{}:
      Unit{}
    case Con{D.Rt{+c, +t}, +rest}:
      (+hc, hr) = hR
      +L = Lst(os, D.Tmp.held(xs), fs, m, sp)
      +hn2 = hN
      (live.kept(t, ds, ks, img, m, ms, nx, nx2, fi, im, L, Yc(fs, m, sp, D.Tmp.cells(xs)), T, Pn, n2, ps, Qn, rr, k, c, hc,
         ln.live(t, True{}, ds, m, im, fi, nx, ks, img, ps, gc.tbl(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g), L,
           gc.L(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g), c, hc, CK.Bo.and_l(D.Nodes(L, m, c), NdAll(D.Rt.cells(rest), L, m), hn2))),
       rts.kept(rest, ds, ks, img, m, ms, nx, nx2, fi, im, os, xs, fs, sp, ps, zs, g, T, Pn, n2, Qn, rr, k, hr,
         CK.Bo.and_r(D.Nodes(L, m, c), NdAll(D.Rt.cells(rest), L, m), hn2)))

# a borrowed root (STATIC, or a node of an owned root's term) is live
def ln.held(+t: Bk.Term, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +os: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  +g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs), +c: U32, +hi: D.IsK(True{}, ds, m, im, fi, nx, ks, img, c, t),
  hh: {Bool.or(D.Fl(m, c, 1024), D.Nodes(os, m, c)) == True{} : Bool}) -> {Ln(t, m, c, Lst(os, D.Tmp.held(xs), fs, m, sp)) == True{} : Bool}:
  D.or.cases(D.Fl(m, c, 1024), D.Nodes(os, m, c), {Ln(t, m, c, Lst(os, D.Tmp.held(xs), fs, m, sp)) == True{} : Bool}, hh,
    e => ln.stat(t, True{}, ds, m, im, fi, nx, ks, img, ps, D.Tmp.cells(xs), D.Rt.cells(D.Tmp.held(xs)), gc.tbl(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g),
      Lst(os, D.Tmp.held(xs), fs, m, sp), c, hi, e, gc.clo(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g)),
    e => ln.live(t, True{}, ds, m, im, fi, nx, ks, img, ps, gc.tbl(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g), Lst(os, D.Tmp.held(xs), fs, m, sp),
      gc.L(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g), c, hi, nodes.in.l(os, List.append(&2, D.Rt, D.Tmp.held(xs), D.Fr.rts(fs, m, sp)), m, c, e)))

# the borrowed roots stand for their terms after the copy
def rts.held(R: List<&2, D.Rt>, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells,
  +ms: Cr.Cir.Cells, +nx: U32, +nx2: U32, +fi: U32, +im: U32, +os: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +fs: List<&2, D.AF>, +sp: U32,
  +ps: List<&2, U32>, +zs: List<&2, D.Rt>, +g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs), +T: List<&2, U32>, +Pn: List<&2, U32>,
  +n2: Nat, +Qn: List<&2, U32>, +rr: U32,
  +k: KF(m, ms, nx, nx2, fi, im, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs)), T, Pn, n2, ps, Qn, rr),
  hR: D.RtsK(True{}, ds, m, im, fi, nx, ks, img, R), hH: D.Held(m, os, R)) -> D.RtsK(True{}, ds, ms, im, fi, nx2, ks, img, R):
  match R:
    case Nil{}:
      Unit{}
    case Con{D.Rt{+c, +t}, +rest}:
      (+hc, hr) = hR
      (hh, hhr) = hH
      (live.kept(t, ds, ks, img, m, ms, nx, nx2, fi, im, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs)), T, Pn, n2, ps, Qn, rr, k, c, hc,
         ln.held(t, ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, c, hc, hh)),
       rts.held(rest, ds, ks, img, m, ms, nx, nx2, fi, im, os, xs, fs, sp, ps, zs, g, T, Pn, n2, Qn, rr, k, hr, hhr))

# the nodes of the owned roots' terms are the same after the copy
def nodes.kept(R: List<&2, D.Rt>, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells,
  +ms: Cr.Cir.Cells, +nx: U32, +nx2: U32, +fi: U32, +im: U32, +os: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +fs: List<&2, D.AF>, +sp: U32,
  +ps: List<&2, U32>, +zs: List<&2, D.Rt>, +g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs), +T: List<&2, U32>, +Pn: List<&2, U32>,
  +n2: Nat, +Qn: List<&2, U32>, +rr: U32,
  +k: KF(m, ms, nx, nx2, fi, im, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs)), T, Pn, n2, ps, Qn, rr), +c: U32,
  hR: D.RtsK(True{}, ds, m, im, fi, nx, ks, img, R), hN: {NdAll(D.Rt.cells(R), Lst(os, D.Tmp.held(xs), fs, m, sp), m) == True{} : Bool}) ->
  {D.Nodes(R, ms, c) == D.Nodes(R, m, c) : Bool}:
  match R:
    case Nil{}:
      {==}
    case Con{D.Rt{+r, +t}, +rest}:
      (+hc, hr) = hR
      +L = Lst(os, D.Tmp.held(xs), fs, m, sp)
      +hn2 = hN
      or.cong(D.Node(t, ms, r, c), D.Node(t, m, r, c), D.Nodes(rest, ms, c), D.Nodes(rest, m, c),
        live.nodes(t, ds, ks, img, m, ms, nx, nx2, fi, im, L, Yc(fs, m, sp, D.Tmp.cells(xs)), T, Pn, n2, ps, Qn, rr, k, r, c, hc,
          ln.live(t, True{}, ds, m, im, fi, nx, ks, img, ps, gc.tbl(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g), L,
            gc.L(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g), r, hc, CK.Bo.and_l(D.Nodes(L, m, r), NdAll(D.Rt.cells(rest), L, m), hn2))),
        nodes.kept(rest, ds, ks, img, m, ms, nx, nx2, fi, im, os, xs, fs, sp, ps, zs, g, T, Pn, n2, Qn, rr, k, c, hr,
          CK.Bo.and_r(D.Nodes(L, m, r), NdAll(D.Rt.cells(rest), L, m), hn2)))

# a cell that keeps its field 0 keeps its STATIC flag
def fl.same(+m: Cr.Cir.Cells, +ms: Cr.Cir.Cells, +c: U32, h: {S.Same.at(m, ms, c) == True{} : Bool}) -> {D.Fl(ms, c, 1024) == D.Fl(m, c, 1024) : Bool}:
  Equal.cong(U32, Bool, z => U32.is_ne(U32.and(z, 1024), 0), D.Fd(0n, ms, c), D.Fd(0n, m, c),
    CK.U.eq(S.Fd(0n, ms, c), S.Fd(0n, m, c), CK.Bo.and_l(U32.is_eq(S.Fd(0n, ms, c), S.Fd(0n, m, c)),
      Bool.and(U32.is_eq(S.Fd(2n, ms, c), S.Fd(2n, m, c)), Bool.and(U32.is_eq(S.Fd(3n, ms, c), S.Fd(3n, m, c)), U32.is_eq(S.Fd(4n, ms, c), S.Fd(4n, m, c)))), h)))

# the borrowed roots are held after the copy: STATIC (each keeps its field
# 0), or a node of an owned root's term (each keeps its nodes)
def held.kept(R: List<&2, D.Rt>, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells,
  +ms: Cr.Cir.Cells, +nx: U32, +nx2: U32, +fi: U32, +im: U32, +os: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +fs: List<&2, D.AF>, +sp: U32,
  +ps: List<&2, U32>, +zs: List<&2, D.Rt>, +g: GC(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs), +T: List<&2, U32>, +Pn: List<&2, U32>,
  +n2: Nat, +Qn: List<&2, U32>, +rr: U32, +u: Bk.Term,
  +k: KF(m, ms, nx, nx2, fi, im, Lst(os, D.Tmp.held(xs), fs, m, sp), Yc(fs, m, sp, D.Tmp.cells(xs)), T, Pn, n2, ps, Qn, rr),
  hR: D.RtsK(True{}, ds, m, im, fi, nx, ks, img, R), hH: D.Held(m, os, R)) -> D.Held(ms, Con{D.Rt{rr, u}, os}, R):
  match R:
    case Nil{}:
      Unit{}
    case Con{D.Rt{+c, +t}, +rest}:
      (+hc, hr) = hR
      (+hh, hhr) = hH
      +L = Lst(os, D.Tmp.held(xs), fs, m, sp)
      +hln = ln.held(t, ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, c, hc, hh)
      +hs = kf.node(m, ms, nx, nx2, fi, im, L, Yc(fs, m, sp, D.Tmp.cells(xs)), T, Pn, n2, ps, Qn, rr, k, c,
        isk.cell(t, True{}, ds, m, im, fi, nx, ks, img, c, hc), ln.root(t, m, c, L, hln))
      +en = nodes.kept(os, ds, ks, img, m, ms, nx, nx2, fi, im, os, xs, fs, sp, ps, zs, g, T, Pn, n2, Qn, rr, k, c,
        gc.os(ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g), ndall.os(D.Rt.cells(os), ds, ks, img, m, nx, fi, im, os, xs, fs, sp, ps, zs, g, D.allin.refl(D.Rt.cells(os))))
      (D.or.cases(D.Fl(m, c, 1024), D.Nodes(os, m, c), {Bool.or(D.Fl(ms, c, 1024), D.Nodes(Con{D.Rt{rr, u}, os}, ms, c)) == True{} : Bool}, hh,
         e => CK.Bo.or_il(D.Fl(ms, c, 1024), D.Nodes(Con{D.Rt{rr, u}, os}, ms, c), (%Equal.sym(Bool, D.Fl(ms, c, 1024), D.Fl(m, c, 1024), fl.same(m, ms, c, hs)) : {_ == True{} : Bool}; e)),
         e => CK.Bo.or_ir(D.Fl(ms, c, 1024), D.Nodes(Con{D.Rt{rr, u}, os}, ms, c),
           CK.Bo.or_ir(D.Node(u, ms, rr, c), D.Nodes(os, ms, c), (%Equal.sym(Bool, D.Nodes(os, ms, c), D.Nodes(os, m, c), en) : {_ == True{} : Bool}; e)))),
       held.kept(rest, ds, ks, img, m, ms, nx, nx2, fi, im, os, xs, fs, sp, ps, zs, g, T, Pn, n2, Qn, rr, u, k, hr, hhr))

# After the copy
# --------------
#
# CopyQ's parts from Post's: a live cell was no garbage, so it was not taken
# (Incl.go: the taken cells were garbage or new), so it is neither new
# garbage (Gb) nor pending (AL's Sub); the own cells stay within the budget.

# Nat.max's sides
def le.max.l(+a: Nat, +b: Nat) -> N.Le(a, Nat.max(a, b)):
  match a:
    case 0n:
      N.le_zero(b)
    case 1n+p:
      match b:
        case 0n:
          N.le_refl(1n+p)
        case 1n+q:
          le.max.l(p, q)

def le.max.r(+a: Nat, +b: Nat) -> N.Le(b, Nat.max(a, b)):
  match a:
    case 0n:
      N.le_refl(b)
    case 1n+p:
      match b:
        case 0n:
          N.le_zero(1n+p)
        case 1n+q:
          le.max.r(p, q)

# the own cells after the copy: as many as before (next stayed), or within
# the budget B
def mem.cq(+nx: U32, +nx2: U32, +fi: U32, +B: Nat,
  h: {Bool.or(U32.is_eq(nx2, nx), Nat.is_le(Nat.sub(U32.to_nat(nx2), U32.to_nat(fi)), B)) == True{} : Bool}) ->
  N.Le(Nat.sub(U32.to_nat(nx2), U32.to_nat(fi)), Nat.max(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), B)):
  +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
  +n2 = Nat.sub(U32.to_nat(nx2), U32.to_nat(fi))
  D.or.cases(U32.is_eq(nx2, nx), Nat.is_le(n2, B), N.Le(n2, Nat.max(n, B)), h,
    e => (%Equal.sym(U32, nx2, nx, CK.U.eq(nx2, nx, e)) : N.Le(Nat.sub(U32.to_nat(_), U32.to_nat(fi)), Nat.max(n, B)); le.max.l(n, B)),
    e => N.le_trans(n2, B, Nat.max(n, B), N.toLe(n2, B, e), le.max.r(n, B)))

# a cell out of the garbage P, below N, is not taken
def ig.out(T: List<&2, U32>, +P: List<&2, U32>, +N: U32, +x: U32, h: {S.Incl.go(T, P, N) == True{} : Bool},
  +hp: {S.Has(P, x) == False{} : Bool}, +hx: {U32.is_lt(x, N) == True{} : Bool}) -> {S.Has(T, x) == False{} : Bool}:
  match T:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      +h2 = h
      +A = Bool.or(S.Has(P, y), U32.is_le(N, y))
      +ha = CK.Bo.and_l(A, S.Incl.go(rest, P, N), h2)
      +ey = bool.case(U32.is_eq(y, x), U32.is_eq(y, x), {U32.is_eq(y, x) == False{} : Bool}, {==},
        e => CK.U.lt_ge(x, N, {U32.is_eq(y, x) == False{} : Bool}, hx,
          CK.Bo.or_r(S.Has(P, x), U32.is_le(N, x), (%CK.U.eq(y, x, e) : {Bool.or(S.Has(P, _), U32.is_le(N, _)) == True{} : Bool}; ha), hp)),
        e => e)
      or.ff(U32.is_eq(y, x), S.Has(rest, x), ey, ig.out(rest, P, N, x, CK.Bo.and_r(A, S.Incl.go(rest, P, N), h2), hp, hx))

# a cell neither old garbage nor taken is no new garbage
def gb.out(Pn: List<&2, U32>, +P: List<&2, U32>, +T: List<&2, U32>, +Qn: List<&2, U32>, +ms: Cr.Cir.Cells, +x: U32,
  h: {S.Gb(Pn, P, T, Qn, ms) == True{} : Bool}, +hp: {S.Has(P, x) == False{} : Bool}, +ht: {S.Has(T, x) == False{} : Bool}) ->
  {S.Has(Pn, x) == False{} : Bool}:
  match Pn:
    case Nil{}:
      {==}
    case Con{+c, +rest}:
      +h2 = h
      +A1 = Bool.and(S.Has(P, c), Bool.not(S.Has(T, c)))
      +A2 = Bool.and(S.Has(T, c), Bool.and(U32.is_eq(S.Fd(0n, ms, c), 45), S.Has(Qn, c)))
      +ha = CK.Bo.and_l(Bool.or(A1, A2), S.Gb(rest, P, T, Qn, ms), h2)
      +ec = bool.case(U32.is_eq(c, x), U32.is_eq(c, x), {U32.is_eq(c, x) == False{} : Bool}, {==},
        +e => D.or.cases(A1, A2, {U32.is_eq(c, x) == False{} : Bool}, ha,
          e1 => CK.Bo.tf({U32.is_eq(c, x) == False{} : Bool}, Equal.trans(Bool, False{}, S.Has(P, c), True{},
            Equal.sym(Bool, S.Has(P, c), False{}, (%Equal.sym(U32, c, x, CK.U.eq(c, x, e)) : {S.Has(P, _) == False{} : Bool}; hp)), CK.Bo.and_l(S.Has(P, c), Bool.not(S.Has(T, c)), e1))),
          e1 => CK.Bo.tf({U32.is_eq(c, x) == False{} : Bool}, Equal.trans(Bool, False{}, S.Has(T, c), True{},
            Equal.sym(Bool, S.Has(T, c), False{}, (%Equal.sym(U32, c, x, CK.U.eq(c, x, e)) : {S.Has(T, _) == False{} : Bool}; ht)),
            CK.Bo.and_l(S.Has(T, c), Bool.and(U32.is_eq(S.Fd(0n, ms, c), 45), S.Has(Qn, c)), e1)))),
        e => e)
      or.ff(U32.is_eq(c, x), S.Has(rest, x), ec, gb.out(rest, P, T, Qn, ms, x, CK.Bo.and_r(Bool.or(A1, A2), S.Gb(rest, P, T, Qn, ms), h2), hp, ht))

# a cell out of P is out of the cells Q of P
def sub.out(Q: List<&2, U32>, +P: List<&2, U32>, +x: U32, h: {S.Sub(Q, P) == True{} : Bool}, +hp: {S.Has(P, x) == False{} : Bool}) ->
  {S.Has(Q, x) == False{} : Bool}:
  match Q:
    case Nil{}:
      {==}
    case Con{+q, +rest}:
      +h2 = h
      +hq = CK.Bo.and_l(S.Has(P, q), S.Sub(rest, P), h2)
      +eq = bool.case(U32.is_eq(q, x), U32.is_eq(q, x), {U32.is_eq(q, x) == False{} : Bool}, {==},
        e => CK.Bo.tf({U32.is_eq(q, x) == False{} : Bool}, Equal.trans(Bool, False{}, S.Has(P, q), True{},
          Equal.sym(Bool, S.Has(P, q), False{}, (%Equal.sym(U32, q, x, CK.U.eq(q, x, e)) : {S.Has(P, _) == False{} : Bool}; hp)), hq)),
        e => e)
      or.ff(U32.is_eq(q, x), S.Has(rest, x), eq, sub.out(rest, P, x, CK.Bo.and_r(S.Has(P, q), S.Sub(rest, P), h2), hp))

# The laws
# --------

def K.copy.post(f, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, wt, keep, os, bs, fs, sp, pend, ps, c, t, ce, es, xs, zs, hs, hac, hl, hc, hp, he, hn, env, ho, hv, hk):
  ?TODO

def K.copy.done(ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, wt, os, bs, fs, sp, pend, ps, c, t, ce, es, xs, zs, hs, hac, hl, hc, hp, he, hn, env, ho, hv):
  match wt:
    case True{}:
      copy.ends(True{}, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, os, bs, fs, sp, pend, ps, c, t, ce, es, xs, zs, hs, hac, hl, hc, hp, he, hn, env, ho)
    case False{}:
      copy.ends(False{}, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, os, bs, fs, sp, pend, ps, c, t, ce, es, xs, zs, hs, hac, hl, hc, hp, he, hn, env, ho)
