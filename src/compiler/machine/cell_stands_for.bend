# compiler: the term that Is says a cell stands for, as T.tm.of reads it
# =====================================================================
#
# The bridge from moves.bend's Is (a cell stands for a term, node by
# node) to cell_terms.bend's T.tm.of (the term that a cell's fields give):
#
#   is.tm: when the cell c stands for t, T.tm.of reads t from c with the fuel
#     Term.size(t) (is.tm.at: with any fuel at least that);
#   is.rd: and every cell that T.tm.of reads from c is a cell that the
#     machine may access (Cir.is_cell, from Nd), as Rd says;
#   quan.img: T.tm.quan reads back the quantity that Img.quan writes.

import Base
import ../../book/impl.bend as Bk
import ../../program/impl.bend as Pg
import ../cir/impl.bend as Cr
import ./impl.bend as Mc
import ./cell_terms.bend as T
import ../need_big.bend as N
import ./definitions.bend as PM

# Kit
# ---

# T.tm.quan reads back the quantity that Img.quan writes
def quan.img(q: Bk.Quan) -> {T.tm.quan(Mc.Img.quan(q)) == q : Bk.Quan}:
  match q:
    case Bk.Quan.Q0{}:
      {==}
    case Bk.Quan.Q1{}:
      {==}
    case Bk.Quan.Q2{}:
      {==}

# the quantity of a cell, as T.tm.of reads it, is the one that Qs says
def quan.of(+x: Cr.Cir.Cell, +q: Bk.Quan, h: PM.Qs(x, q)) -> {T.tm.quan(PM.QnW(Cr.Cir.Cell.get(0n, x))) == q : Bk.Quan}:
  %Equal.sym(U32, PM.QnW(Cr.Cir.Cell.get(0n, x)), Mc.Img.quan(q), h) : {T.tm.quan(_) == q : Bk.Quan}
  quan.img(q)

# a term of no fuel is none: the fuel of a term is at least 1
def size.nz(t: Bk.Term, le: N.Le(Pg.Term.size(t), 0n)) -> Empty:
  match t:
    case Bk.Term.Var{_}:
      le
    case Bk.Term.Ref{_}:
      le
    case Bk.Term.Ann{_, _}:
      le
    case Bk.Term.Let{_, _, _}:
      le
    case Bk.Term.Typ{_}:
      le
    case Bk.Term.Min{_, _}:
      le
    case Bk.Term.All{_, _, _}:
      le
    case Bk.Term.Lam{_, _}:
      le
    case Bk.Term.App{_, _, _}:
      le
    case Bk.Term.Sig{_, _, _}:
      le
    case Bk.Term.Tup{_, _, _}:
      le
    case Bk.Term.Prj{_}:
      le
    case Bk.Term.Enu{_}:
      le
    case Bk.Term.Lab{_}:
      le
    case Bk.Term.Mat{_, _, _}:
      le
    case Bk.Term.Efq{}:
      le
    case Bk.Term.Eql{_, _, _}:
      le
    case Bk.Term.Rfl{}:
      le
    case Bk.Term.Rwt{_, _, _}:
      le

# the first part's fuel, and the second's, of a node of two parts
def le.l(+a: Nat, +b: Nat, +g: Nat, le: N.Le(Nat.add(a, b), g)) -> N.Le(a, g):
  N.le_trans(a, Nat.add(a, b), g, N.le_add_r(a, b), le)

def le.r(+a: Nat, +b: Nat, +g: Nat, le: N.Le(Nat.add(a, b), g)) -> N.Le(b, g):
  N.le_trans(b, Nat.add(a, b), g, N.le_add_l(a, b), le)

# the second part's fuel, and the third's, of a node of three parts
def le.m(+a: Nat, +b: Nat, +d: Nat, +g: Nat, le: N.Le(Nat.add(a, Nat.add(b, d)), g)) -> N.Le(b, g):
  le.l(b, d, g, le.r(a, Nat.add(b, d), g, le))

def le.e(+a: Nat, +b: Nat, +d: Nat, +g: Nat, le: N.Le(Nat.add(a, Nat.add(b, d)), g)) -> N.Le(d, g):
  le.r(b, d, g, le.r(a, Nat.add(b, d), g, le))

# what the node of a cell says: it is a cell, of its tag
def nd.cell(-ds: List<&2, Bk.Def>, -im: U32, -fi: U32, -nx: U32, -c: U32, -x: Cr.Cir.Cell, -t: Bk.Term, -tag: U32,
  h: PM.Nd(ds, im, fi, nx, c, x, t, tag)) -> {Cr.Cir.is_cell(c, im, fi, nx) == True{} : Bool}:
  (e, r) = h
  e

def nd.tag(-ds: List<&2, Bk.Def>, -im: U32, -fi: U32, -nx: U32, -c: U32, -x: Cr.Cir.Cell, -t: Bk.Term, -tag: U32,
  h: PM.Nd(ds, im, fi, nx, c, x, t, tag)) -> {PM.TgW(Cr.Cir.Cell.get(0n, x)) == tag : U32}:
  (e0, r0) = h
  (e1, r1) = r0
  (e, r) = r1
  e

def and.i(a: Bool, -b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      hb
    case False{}:
      Empty.absurd({Bool.and(False{}, b) == True{} : Bool}, N.false_ne_true(ha))

# The terms of the parts
# ----------------------

def one.of(-k: Bk.Term -> Bk.Term, -r: Maybe<&2, Bk.Term>, -a: Bk.Term, -t: Bk.Term,
  er: {r == Some{a} : Maybe<&2, Bk.Term>}, ek: {k(a) == t : Bk.Term}) -> {T.tm.one(k, r) == Some{t} : Maybe<&2, Bk.Term>}:
  %Equal.sym(Maybe<&2, Bk.Term>, r, Some{a}, er) : {T.tm.one(k, _) == Some{t} : Maybe<&2, Bk.Term>}
  %ek : {Some{k(a)} == Some{_} : Maybe<&2, Bk.Term>}
  {==}

def two.of(-k: Bk.Term -> Bk.Term -> Bk.Term, -r: Maybe<&2, Bk.Term>, -s: Maybe<&2, Bk.Term>, -a: Bk.Term, -b: Bk.Term, -t: Bk.Term,
  er: {r == Some{a} : Maybe<&2, Bk.Term>}, es: {s == Some{b} : Maybe<&2, Bk.Term>}, ek: {k(a, b) == t : Bk.Term}) ->
  {T.tm.two(k, r, s) == Some{t} : Maybe<&2, Bk.Term>}:
  %Equal.sym(Maybe<&2, Bk.Term>, r, Some{a}, er) : {T.tm.two(k, _, s) == Some{t} : Maybe<&2, Bk.Term>}
  %Equal.sym(Maybe<&2, Bk.Term>, s, Some{b}, es) : {T.tm.two(k, Some{a}, _) == Some{t} : Maybe<&2, Bk.Term>}
  %ek : {Some{k(a, b)} == Some{_} : Maybe<&2, Bk.Term>}
  {==}

def three.of(-k: Bk.Term -> Bk.Term -> Bk.Term -> Bk.Term, -r: Maybe<&2, Bk.Term>, -s: Maybe<&2, Bk.Term>, -u: Maybe<&2, Bk.Term>,
  -a: Bk.Term, -b: Bk.Term, -d: Bk.Term,
  er: {r == Some{a} : Maybe<&2, Bk.Term>}, es: {s == Some{b} : Maybe<&2, Bk.Term>}, eu: {u == Some{d} : Maybe<&2, Bk.Term>}) ->
  {T.tm.three(k, r, s, u) == Some{k(a, b, d)} : Maybe<&2, Bk.Term>}:
  %Equal.sym(Maybe<&2, Bk.Term>, r, Some{a}, er) : {T.tm.three(k, _, s, u) == Some{k(a, b, d)} : Maybe<&2, Bk.Term>}
  %Equal.sym(Maybe<&2, Bk.Term>, s, Some{b}, es) : {T.tm.three(k, Some{a}, _, u) == Some{k(a, b, d)} : Maybe<&2, Bk.Term>}
  %Equal.sym(Maybe<&2, Bk.Term>, u, Some{d}, eu) : {T.tm.three(k, Some{a}, Some{b}, _) == Some{k(a, b, d)} : Maybe<&2, Bk.Term>}
  {==}

def named.of(-n: Maybe<&2, List<&2, Word(8n)>>, -k: List<&2, Word(8n)>, en: {n == Some{k} : Maybe<&2, List<&2, Word(8n)>>}) ->
  {T.tm.named(n, j => Bk.Term.Lab{j}) == Some{Bk.Term.Lab{k}} : Maybe<&2, Bk.Term>}:
  %Equal.sym(Maybe<&2, List<&2, Word(8n)>>, n, Some{k}, en) : {T.tm.named(_, j => Bk.Term.Lab{j}) == Some{Bk.Term.Lab{k}} : Maybe<&2, Bk.Term>}
  {==}

def mat.of(-n: Maybe<&2, List<&2, Word(8n)>>, -r: Maybe<&2, Bk.Term>, -s: Maybe<&2, Bk.Term>, -k: List<&2, Word(8n)>, -a: Bk.Term, -b: Bk.Term,
  en: {n == Some{k} : Maybe<&2, List<&2, Word(8n)>>}, er: {r == Some{a} : Maybe<&2, Bk.Term>}, es: {s == Some{b} : Maybe<&2, Bk.Term>}) ->
  {T.tm.mat(n, r, s) == Some{Bk.Term.Mat{k, a, b}} : Maybe<&2, Bk.Term>}:
  %Equal.sym(Maybe<&2, List<&2, Word(8n)>>, n, Some{k}, en) : {T.tm.mat(_, r, s) == Some{Bk.Term.Mat{k, a, b}} : Maybe<&2, Bk.Term>}
  %Equal.sym(Maybe<&2, Bk.Term>, r, Some{a}, er) : {T.tm.mat(Some{k}, _, s) == Some{Bk.Term.Mat{k, a, b}} : Maybe<&2, Bk.Term>}
  %Equal.sym(Maybe<&2, Bk.Term>, s, Some{b}, es) : {T.tm.mat(Some{k}, Some{a}, _) == Some{Bk.Term.Mat{k, a, b}} : Maybe<&2, Bk.Term>}
  {==}

# T.tm.of one level down, at the cell's tag tg
def of.at(+g: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +tg: U32,
  e: {PM.Tg(m, c) == tg : U32}) ->
  {T.tm.cell(U32.to_nat(tg), T.tm.quan(PM.Qn(m, c)), c, PM.Fd(2n, m, c), ks, img, u => T.tm.of(g, m, ks, img, PM.Fd(2n, m, c)),
    u => T.tm.of(g, m, ks, img, PM.Fd(3n, m, c)), u => T.tm.of(g, m, ks, img, PM.Fd(4n, m, c))) == T.tm.of(1n+g, m, ks, img, c) : Maybe<&2, Bk.Term>}:
  %e : {T.tm.cell(U32.to_nat(_), T.tm.quan(PM.Qn(m, c)), c, PM.Fd(2n, m, c), ks, img, u => T.tm.of(g, m, ks, img, PM.Fd(2n, m, c)),
    u => T.tm.of(g, m, ks, img, PM.Fd(3n, m, c)), u => T.tm.of(g, m, ks, img, PM.Fd(4n, m, c))) == T.tm.of(1n+g, m, ks, img, c) : Maybe<&2, Bk.Term>}
  {==}

# The bridge
# ----------

# the cell c stands for t: T.tm.of reads t from it, with any fuel f that is at
# least t's size
def is.tm.at(+f: Nat, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +c: U32, t: Bk.Term, +le: N.Le(Pg.Term.size(t), f), h: PM.Is(ds, m, im, fi, nx, ks, img, c, t)) ->
  {T.tm.of(f, m, ks, img, c) == Some{t} : Maybe<&2, Bk.Term>}:
  match f:
    case 0n:
      Empty.absurd({T.tm.of(0n, m, ks, img, c) == Some{t} : Maybe<&2, Bk.Term>}, size.nz(t, le))
    case 1n+(+g):
      match t:
        case Bk.Term.Var{+i}:
          (nd, ei) = h
          %of.at(g, m, ks, img, c, 0, nd.tag(ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Var{i}, 0, nd)) : {_ == Some{Bk.Term.Var{i}} : Maybe<&2, Bk.Term>}
          %ei : {Some{Bk.Term.Var{U32.to_nat(PM.Fd(2n, m, c))}} == Some{Bk.Term.Var{_}} : Maybe<&2, Bk.Term>}
          {==}
        case Bk.Term.Ref{+k}:
          (nd, r) = h
          (ei, r2) = r
          %of.at(g, m, ks, img, c, 1, nd.tag(ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Ref{k}, 1, nd)) : {_ == Some{Bk.Term.Ref{k}} : Maybe<&2, Bk.Term>}
          ei
        case Bk.Term.Ann{+y, +z}:
          (nd, r) = h
          (py, pz) = r
          (sy, hy) = py
          (sz, hz) = pz
          %of.at(g, m, ks, img, c, 2, nd.tag(ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Ann{y, z}, 2, nd)) : {_ == Some{Bk.Term.Ann{y, z}} : Maybe<&2, Bk.Term>}
          two.of(a => b => Bk.Term.Ann{a, b}, T.tm.of(g, m, ks, img, PM.Fd(2n, m, c)), T.tm.of(g, m, ks, img, PM.Fd(3n, m, c)), y, z, Bk.Term.Ann{y, z},
            is.tm.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(2n, m, c), y, le.l(Pg.Term.size(y), Pg.Term.size(z), g, le), hy),
            is.tm.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(3n, m, c), z, le.r(Pg.Term.size(y), Pg.Term.size(z), g, le), hz), {==})
        case Bk.Term.Let{+q, +v, +b}:
          (nd, r) = h
          (hq, r2) = r
          (pv, pb) = r2
          (sv, hv) = pv
          (sb, hb) = pb
          %of.at(g, m, ks, img, c, 3, nd.tag(ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Let{q, v, b}, 3, nd)) : {_ == Some{Bk.Term.Let{q, v, b}} : Maybe<&2, Bk.Term>}
          two.of(a => d => Bk.Term.Let{T.tm.quan(PM.Qn(m, c)), a, d}, T.tm.of(g, m, ks, img, PM.Fd(2n, m, c)), T.tm.of(g, m, ks, img, PM.Fd(3n, m, c)), v, b, Bk.Term.Let{q, v, b},
            is.tm.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(2n, m, c), v, le.l(Pg.Term.size(v), Pg.Term.size(b), g, le), hv),
            is.tm.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(3n, m, c), b, le.r(Pg.Term.size(v), Pg.Term.size(b), g, le), hb),
            Equal.cong(Bk.Quan, Bk.Term, p => Bk.Term.Let{p, v, b}, T.tm.quan(PM.Qn(m, c)), q, quan.of(Cr.Cir.Cells.get(m, c), q, hq)))
        case Bk.Term.Typ{+y}:
          (nd, r) = h
          (sy, hy) = r
          %of.at(g, m, ks, img, c, 4, nd.tag(ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Typ{y}, 4, nd)) : {_ == Some{Bk.Term.Typ{y}} : Maybe<&2, Bk.Term>}
          one.of(a => Bk.Term.Typ{a}, T.tm.of(g, m, ks, img, PM.Fd(2n, m, c)), y, Bk.Term.Typ{y},
            is.tm.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(2n, m, c), y, le, hy), {==})
        case Bk.Term.Min{+y, +z}:
          (nd, r) = h
          (py, pz) = r
          (sy, hy) = py
          (sz, hz) = pz
          %of.at(g, m, ks, img, c, 5, nd.tag(ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Min{y, z}, 5, nd)) : {_ == Some{Bk.Term.Min{y, z}} : Maybe<&2, Bk.Term>}
          two.of(a => b => Bk.Term.Min{a, b}, T.tm.of(g, m, ks, img, PM.Fd(2n, m, c)), T.tm.of(g, m, ks, img, PM.Fd(3n, m, c)), y, z, Bk.Term.Min{y, z},
            is.tm.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(2n, m, c), y, le.l(Pg.Term.size(y), Pg.Term.size(z), g, le), hy),
            is.tm.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(3n, m, c), z, le.r(Pg.Term.size(y), Pg.Term.size(z), g, le), hz), {==})
        case Bk.Term.All{+q, +y, +z}:
          (nd, r) = h
          (hq, r2) = r
          (py, pz) = r2
          (sy, hy) = py
          (sz, hz) = pz
          %of.at(g, m, ks, img, c, 6, nd.tag(ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.All{q, y, z}, 6, nd)) : {_ == Some{Bk.Term.All{q, y, z}} : Maybe<&2, Bk.Term>}
          two.of(a => d => Bk.Term.All{T.tm.quan(PM.Qn(m, c)), a, d}, T.tm.of(g, m, ks, img, PM.Fd(2n, m, c)), T.tm.of(g, m, ks, img, PM.Fd(3n, m, c)), y, z, Bk.Term.All{q, y, z},
            is.tm.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(2n, m, c), y, le.l(Pg.Term.size(y), Pg.Term.size(z), g, le), hy),
            is.tm.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(3n, m, c), z, le.r(Pg.Term.size(y), Pg.Term.size(z), g, le), hz),
            Equal.cong(Bk.Quan, Bk.Term, p => Bk.Term.All{p, y, z}, T.tm.quan(PM.Qn(m, c)), q, quan.of(Cr.Cir.Cells.get(m, c), q, hq)))
        case Bk.Term.Lam{+q, +y}:
          (nd, r) = h
          (hq, r2) = r
          (sy, hy) = r2
          %of.at(g, m, ks, img, c, 7, nd.tag(ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Lam{q, y}, 7, nd)) : {_ == Some{Bk.Term.Lam{q, y}} : Maybe<&2, Bk.Term>}
          one.of(a => Bk.Term.Lam{T.tm.quan(PM.Qn(m, c)), a}, T.tm.of(g, m, ks, img, PM.Fd(2n, m, c)), y, Bk.Term.Lam{q, y},
            is.tm.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(2n, m, c), y, le, hy),
            Equal.cong(Bk.Quan, Bk.Term, p => Bk.Term.Lam{p, y}, T.tm.quan(PM.Qn(m, c)), q, quan.of(Cr.Cir.Cells.get(m, c), q, hq)))
        case Bk.Term.App{+q, +y, +z}:
          (nd, r) = h
          (hq, r2) = r
          (py, pz) = r2
          (sy, hy) = py
          (sz, hz) = pz
          %of.at(g, m, ks, img, c, 8, nd.tag(ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.App{q, y, z}, 8, nd)) : {_ == Some{Bk.Term.App{q, y, z}} : Maybe<&2, Bk.Term>}
          two.of(a => d => Bk.Term.App{T.tm.quan(PM.Qn(m, c)), a, d}, T.tm.of(g, m, ks, img, PM.Fd(2n, m, c)), T.tm.of(g, m, ks, img, PM.Fd(3n, m, c)), y, z, Bk.Term.App{q, y, z},
            is.tm.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(2n, m, c), y, le.l(Pg.Term.size(y), Pg.Term.size(z), g, le), hy),
            is.tm.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(3n, m, c), z, le.r(Pg.Term.size(y), Pg.Term.size(z), g, le), hz),
            Equal.cong(Bk.Quan, Bk.Term, p => Bk.Term.App{p, y, z}, T.tm.quan(PM.Qn(m, c)), q, quan.of(Cr.Cir.Cells.get(m, c), q, hq)))
        case Bk.Term.Sig{+q, +y, +z}:
          (nd, r) = h
          (hq, r2) = r
          (py, pz) = r2
          (sy, hy) = py
          (sz, hz) = pz
          %of.at(g, m, ks, img, c, 9, nd.tag(ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Sig{q, y, z}, 9, nd)) : {_ == Some{Bk.Term.Sig{q, y, z}} : Maybe<&2, Bk.Term>}
          two.of(a => d => Bk.Term.Sig{T.tm.quan(PM.Qn(m, c)), a, d}, T.tm.of(g, m, ks, img, PM.Fd(2n, m, c)), T.tm.of(g, m, ks, img, PM.Fd(3n, m, c)), y, z, Bk.Term.Sig{q, y, z},
            is.tm.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(2n, m, c), y, le.l(Pg.Term.size(y), Pg.Term.size(z), g, le), hy),
            is.tm.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(3n, m, c), z, le.r(Pg.Term.size(y), Pg.Term.size(z), g, le), hz),
            Equal.cong(Bk.Quan, Bk.Term, p => Bk.Term.Sig{p, y, z}, T.tm.quan(PM.Qn(m, c)), q, quan.of(Cr.Cir.Cells.get(m, c), q, hq)))
        case Bk.Term.Tup{+q, +y, +z}:
          (nd, r) = h
          (hq, r2) = r
          (py, pz) = r2
          (sy, hy) = py
          (sz, hz) = pz
          %of.at(g, m, ks, img, c, 10, nd.tag(ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Tup{q, y, z}, 10, nd)) : {_ == Some{Bk.Term.Tup{q, y, z}} : Maybe<&2, Bk.Term>}
          two.of(a => d => Bk.Term.Tup{T.tm.quan(PM.Qn(m, c)), a, d}, T.tm.of(g, m, ks, img, PM.Fd(2n, m, c)), T.tm.of(g, m, ks, img, PM.Fd(3n, m, c)), y, z, Bk.Term.Tup{q, y, z},
            is.tm.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(2n, m, c), y, le.l(Pg.Term.size(y), Pg.Term.size(z), g, le), hy),
            is.tm.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(3n, m, c), z, le.r(Pg.Term.size(y), Pg.Term.size(z), g, le), hz),
            Equal.cong(Bk.Quan, Bk.Term, p => Bk.Term.Tup{p, y, z}, T.tm.quan(PM.Qn(m, c)), q, quan.of(Cr.Cir.Cells.get(m, c), q, hq)))
        case Bk.Term.Prj{+y}:
          (nd, r) = h
          (sy, hy) = r
          %of.at(g, m, ks, img, c, 11, nd.tag(ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Prj{y}, 11, nd)) : {_ == Some{Bk.Term.Prj{y}} : Maybe<&2, Bk.Term>}
          one.of(a => Bk.Term.Prj{a}, T.tm.of(g, m, ks, img, PM.Fd(2n, m, c)), y, Bk.Term.Prj{y},
            is.tm.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(2n, m, c), y, le, hy), {==})
        case Bk.Term.Enu{+e}:
          (nd, r) = h
          (ei, r2) = r
          %of.at(g, m, ks, img, c, 12, nd.tag(ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Enu{e}, 12, nd)) : {_ == Some{Bk.Term.Enu{e}} : Maybe<&2, Bk.Term>}
          ei
        case Bk.Term.Lab{+k}:
          (nd, nm) = h
          (en, ej) = nm
          %of.at(g, m, ks, img, c, 13, nd.tag(ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Lab{k}, 13, nd)) : {_ == Some{Bk.Term.Lab{k}} : Maybe<&2, Bk.Term>}
          named.of(T.tm.name(ks, PM.Fd(2n, m, c)), k, en)
        case Bk.Term.Mat{+k, +y, +z}:
          (nd, r) = h
          (nm, r2) = r
          (en, ej) = nm
          (py, pz) = r2
          (sy, hy) = py
          (sz, hz) = pz
          %of.at(g, m, ks, img, c, 14, nd.tag(ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Mat{k, y, z}, 14, nd)) : {_ == Some{Bk.Term.Mat{k, y, z}} : Maybe<&2, Bk.Term>}
          mat.of(T.tm.name(ks, PM.Fd(2n, m, c)), T.tm.of(g, m, ks, img, PM.Fd(3n, m, c)), T.tm.of(g, m, ks, img, PM.Fd(4n, m, c)), k, y, z, en,
            is.tm.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(3n, m, c), y, le.l(Pg.Term.size(y), Pg.Term.size(z), g, le), hy),
            is.tm.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(4n, m, c), z, le.r(Pg.Term.size(y), Pg.Term.size(z), g, le), hz))
        case Bk.Term.Efq{}:
          %of.at(g, m, ks, img, c, 15, nd.tag(ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Efq{}, 15, h)) : {_ == Some{Bk.Term.Efq{}} : Maybe<&2, Bk.Term>}
          {==}
        case Bk.Term.Eql{+y, +z, +w}:
          (nd, r) = h
          (py, r2) = r
          (sy, hy) = py
          (pz, pw) = r2
          (sz, hz) = pz
          (sw, hw) = pw
          %of.at(g, m, ks, img, c, 16, nd.tag(ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Eql{y, z, w}, 16, nd)) : {_ == Some{Bk.Term.Eql{y, z, w}} : Maybe<&2, Bk.Term>}
          three.of(a => b => d => Bk.Term.Eql{a, b, d}, T.tm.of(g, m, ks, img, PM.Fd(2n, m, c)), T.tm.of(g, m, ks, img, PM.Fd(3n, m, c)), T.tm.of(g, m, ks, img, PM.Fd(4n, m, c)), y, z, w,
            is.tm.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(2n, m, c), y, le.l(Pg.Term.size(y), Nat.add(Pg.Term.size(z), Pg.Term.size(w)), g, le), hy),
            is.tm.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(3n, m, c), z, le.m(Pg.Term.size(y), Pg.Term.size(z), Pg.Term.size(w), g, le), hz),
            is.tm.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(4n, m, c), w, le.e(Pg.Term.size(y), Pg.Term.size(z), Pg.Term.size(w), g, le), hw))
        case Bk.Term.Rfl{}:
          %of.at(g, m, ks, img, c, 17, nd.tag(ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Rfl{}, 17, h)) : {_ == Some{Bk.Term.Rfl{}} : Maybe<&2, Bk.Term>}
          {==}
        case Bk.Term.Rwt{+y, +z, +w}:
          (nd, r) = h
          (py, r2) = r
          (sy, hy) = py
          (pz, pw) = r2
          (sz, hz) = pz
          (sw, hw) = pw
          %of.at(g, m, ks, img, c, 18, nd.tag(ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Rwt{y, z, w}, 18, nd)) : {_ == Some{Bk.Term.Rwt{y, z, w}} : Maybe<&2, Bk.Term>}
          three.of(a => b => d => Bk.Term.Rwt{a, b, d}, T.tm.of(g, m, ks, img, PM.Fd(2n, m, c)), T.tm.of(g, m, ks, img, PM.Fd(3n, m, c)), T.tm.of(g, m, ks, img, PM.Fd(4n, m, c)), y, z, w,
            is.tm.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(2n, m, c), y, le.l(Pg.Term.size(y), Nat.add(Pg.Term.size(z), Pg.Term.size(w)), g, le), hy),
            is.tm.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(3n, m, c), z, le.m(Pg.Term.size(y), Pg.Term.size(z), Pg.Term.size(w), g, le), hz),
            is.tm.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(4n, m, c), w, le.e(Pg.Term.size(y), Pg.Term.size(z), Pg.Term.size(w), g, le), hw))

# the cell c stands for t: T.tm.of reads t from it
def is.tm(+ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +c: U32, +t: Bk.Term, h: PM.Is(ds, m, im, fi, nx, ks, img, c, t)) ->
  {T.tm.of(Pg.Term.size(t), m, ks, img, c) == Some{t} : Maybe<&2, Bk.Term>}:
  is.tm.at(Pg.Term.size(t), ds, m, im, fi, nx, ks, img, c, t, N.le_refl(Pg.Term.size(t)), h)

# Cells that T.tm.of reads
# ------------------------

# the parts that T.tm.of reads of a cell of the tag, by what each part says
def Rd.cell(tag: Nat, r2: Bool, r3: Bool, r4: Bool) -> Bool:
  match tag:
    case 0n:
      True{}
    case 1n:
      True{}
    case 2n:
      r2 && r3
    case 3n:
      r2 && r3
    case 4n:
      r2
    case 5n:
      r2 && r3
    case 6n:
      r2 && r3
    case 7n:
      r2
    case 8n:
      r2 && r3
    case 9n:
      r2 && r3
    case 10n:
      r2 && r3
    case 11n:
      r2
    case 12n:
      True{}
    case 13n:
      True{}
    case 14n:
      r3 && r4
    case 15n:
      True{}
    case 16n:
      r2 && (r3 && r4)
    case 17n:
      True{}
    case 18n:
      r2 && (r3 && r4)
    case 19n+k:
      True{}

# every cell that T.tm.of reads from c, with the fuel f, is a cell that the
# machine may access
def Rd(f: Nat, +m: Cr.Cir.Cells, +c: U32, +im: U32, +fi: U32, +nx: U32) -> Bool:
  match f:
    case 0n:
      True{}
    case 1n+(+g):
      Cr.Cir.is_cell(c, im, fi, nx) && Rd.cell(U32.to_nat(PM.Tg(m, c)), Rd(g, m, PM.Fd(2n, m, c), im, fi, nx),
        Rd(g, m, PM.Fd(3n, m, c), im, fi, nx), Rd(g, m, PM.Fd(4n, m, c), im, fi, nx))

# Rd one level down, at a cell of the term t and the tag tg
def rd.at(+g: Nat, -ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +c: U32, +im: U32, +fi: U32, +nx: U32, -t: Bk.Term, +tg: U32,
  +nd: PM.Nd(ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), t, tg),
  hp: {Rd.cell(U32.to_nat(tg), Rd(g, m, PM.Fd(2n, m, c), im, fi, nx), Rd(g, m, PM.Fd(3n, m, c), im, fi, nx), Rd(g, m, PM.Fd(4n, m, c), im, fi, nx)) == True{} : Bool}) ->
  {Rd(1n+g, m, c, im, fi, nx) == True{} : Bool}:
  %Equal.sym(U32, PM.Tg(m, c), tg, nd.tag(ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), t, tg, nd)) : {Bool.and(Cr.Cir.is_cell(c, im, fi, nx), Rd.cell(U32.to_nat(_), Rd(g, m, PM.Fd(2n, m, c), im, fi, nx),
    Rd(g, m, PM.Fd(3n, m, c), im, fi, nx), Rd(g, m, PM.Fd(4n, m, c), im, fi, nx))) == True{} : Bool}
  and.i(Cr.Cir.is_cell(c, im, fi, nx), Rd.cell(U32.to_nat(tg), Rd(g, m, PM.Fd(2n, m, c), im, fi, nx), Rd(g, m, PM.Fd(3n, m, c), im, fi, nx),
    Rd(g, m, PM.Fd(4n, m, c), im, fi, nx)), nd.cell(ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), t, tg, nd), hp)

# the cell c stands for t: every cell that T.tm.of reads from it, with any
# fuel f, is a cell (Nd)
def is.rd.at(+f: Nat, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +c: U32, t: Bk.Term, h: PM.Is(ds, m, im, fi, nx, ks, img, c, t)) ->
  {Rd(f, m, c, im, fi, nx) == True{} : Bool}:
  match f:
    case 0n:
      {==}
    case 1n+(+g):
      match t:
        case Bk.Term.Var{+i}:
          (nd, ei) = h
          rd.at(g, ds, m, c, im, fi, nx, Bk.Term.Var{i}, 0, nd,
            {==})
        case Bk.Term.Ref{+k}:
          (nd, r) = h
          rd.at(g, ds, m, c, im, fi, nx, Bk.Term.Ref{k}, 1, nd,
            {==})
        case Bk.Term.Ann{+y, +z}:
          (nd, r) = h
          (py, pz) = r
          (sy, hy) = py
          (sz, hz) = pz
          rd.at(g, ds, m, c, im, fi, nx, Bk.Term.Ann{y, z}, 2, nd,
            and.i(Rd(g, m, PM.Fd(2n, m, c), im, fi, nx), Rd(g, m, PM.Fd(3n, m, c), im, fi, nx), is.rd.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(2n, m, c), y, hy), is.rd.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(3n, m, c), z, hz)))
        case Bk.Term.Let{+q, +y, +z}:
          (nd, r) = h
          (hq, r2) = r
          (py, pz) = r2
          (sy, hy) = py
          (sz, hz) = pz
          rd.at(g, ds, m, c, im, fi, nx, Bk.Term.Let{q, y, z}, 3, nd,
            and.i(Rd(g, m, PM.Fd(2n, m, c), im, fi, nx), Rd(g, m, PM.Fd(3n, m, c), im, fi, nx), is.rd.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(2n, m, c), y, hy), is.rd.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(3n, m, c), z, hz)))
        case Bk.Term.Typ{+y}:
          (nd, r) = h
          (sy, hy) = r
          rd.at(g, ds, m, c, im, fi, nx, Bk.Term.Typ{y}, 4, nd,
            is.rd.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(2n, m, c), y, hy))
        case Bk.Term.Min{+y, +z}:
          (nd, r) = h
          (py, pz) = r
          (sy, hy) = py
          (sz, hz) = pz
          rd.at(g, ds, m, c, im, fi, nx, Bk.Term.Min{y, z}, 5, nd,
            and.i(Rd(g, m, PM.Fd(2n, m, c), im, fi, nx), Rd(g, m, PM.Fd(3n, m, c), im, fi, nx), is.rd.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(2n, m, c), y, hy), is.rd.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(3n, m, c), z, hz)))
        case Bk.Term.All{+q, +y, +z}:
          (nd, r) = h
          (hq, r2) = r
          (py, pz) = r2
          (sy, hy) = py
          (sz, hz) = pz
          rd.at(g, ds, m, c, im, fi, nx, Bk.Term.All{q, y, z}, 6, nd,
            and.i(Rd(g, m, PM.Fd(2n, m, c), im, fi, nx), Rd(g, m, PM.Fd(3n, m, c), im, fi, nx), is.rd.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(2n, m, c), y, hy), is.rd.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(3n, m, c), z, hz)))
        case Bk.Term.Lam{+q, +y}:
          (nd, r) = h
          (hq, r2) = r
          (sy, hy) = r2
          rd.at(g, ds, m, c, im, fi, nx, Bk.Term.Lam{q, y}, 7, nd,
            is.rd.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(2n, m, c), y, hy))
        case Bk.Term.App{+q, +y, +z}:
          (nd, r) = h
          (hq, r2) = r
          (py, pz) = r2
          (sy, hy) = py
          (sz, hz) = pz
          rd.at(g, ds, m, c, im, fi, nx, Bk.Term.App{q, y, z}, 8, nd,
            and.i(Rd(g, m, PM.Fd(2n, m, c), im, fi, nx), Rd(g, m, PM.Fd(3n, m, c), im, fi, nx), is.rd.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(2n, m, c), y, hy), is.rd.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(3n, m, c), z, hz)))
        case Bk.Term.Sig{+q, +y, +z}:
          (nd, r) = h
          (hq, r2) = r
          (py, pz) = r2
          (sy, hy) = py
          (sz, hz) = pz
          rd.at(g, ds, m, c, im, fi, nx, Bk.Term.Sig{q, y, z}, 9, nd,
            and.i(Rd(g, m, PM.Fd(2n, m, c), im, fi, nx), Rd(g, m, PM.Fd(3n, m, c), im, fi, nx), is.rd.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(2n, m, c), y, hy), is.rd.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(3n, m, c), z, hz)))
        case Bk.Term.Tup{+q, +y, +z}:
          (nd, r) = h
          (hq, r2) = r
          (py, pz) = r2
          (sy, hy) = py
          (sz, hz) = pz
          rd.at(g, ds, m, c, im, fi, nx, Bk.Term.Tup{q, y, z}, 10, nd,
            and.i(Rd(g, m, PM.Fd(2n, m, c), im, fi, nx), Rd(g, m, PM.Fd(3n, m, c), im, fi, nx), is.rd.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(2n, m, c), y, hy), is.rd.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(3n, m, c), z, hz)))
        case Bk.Term.Prj{+y}:
          (nd, r) = h
          (sy, hy) = r
          rd.at(g, ds, m, c, im, fi, nx, Bk.Term.Prj{y}, 11, nd,
            is.rd.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(2n, m, c), y, hy))
        case Bk.Term.Enu{+e}:
          (nd, r) = h
          rd.at(g, ds, m, c, im, fi, nx, Bk.Term.Enu{e}, 12, nd,
            {==})
        case Bk.Term.Lab{+k}:
          (nd, r) = h
          rd.at(g, ds, m, c, im, fi, nx, Bk.Term.Lab{k}, 13, nd,
            {==})
        case Bk.Term.Mat{+k, +y, +z}:
          (nd, r) = h
          (nm, r2) = r
          (py, pz) = r2
          (sy, hy) = py
          (sz, hz) = pz
          rd.at(g, ds, m, c, im, fi, nx, Bk.Term.Mat{k, y, z}, 14, nd,
            and.i(Rd(g, m, PM.Fd(3n, m, c), im, fi, nx), Rd(g, m, PM.Fd(4n, m, c), im, fi, nx), is.rd.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(3n, m, c), y, hy), is.rd.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(4n, m, c), z, hz)))
        case Bk.Term.Efq{}:
          rd.at(g, ds, m, c, im, fi, nx, Bk.Term.Efq{}, 15, h,
            {==})
        case Bk.Term.Eql{+y, +z, +w}:
          (nd, r) = h
          (py, r2) = r
          (sy, hy) = py
          (pz, pw) = r2
          (sz, hz) = pz
          (sw, hw) = pw
          rd.at(g, ds, m, c, im, fi, nx, Bk.Term.Eql{y, z, w}, 16, nd,
            and.i(Rd(g, m, PM.Fd(2n, m, c), im, fi, nx), Bool.and(Rd(g, m, PM.Fd(3n, m, c), im, fi, nx), Rd(g, m, PM.Fd(4n, m, c), im, fi, nx)), is.rd.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(2n, m, c), y, hy), and.i(Rd(g, m, PM.Fd(3n, m, c), im, fi, nx), Rd(g, m, PM.Fd(4n, m, c), im, fi, nx), is.rd.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(3n, m, c), z, hz), is.rd.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(4n, m, c), w, hw))))
        case Bk.Term.Rfl{}:
          rd.at(g, ds, m, c, im, fi, nx, Bk.Term.Rfl{}, 17, h,
            {==})
        case Bk.Term.Rwt{+y, +z, +w}:
          (nd, r) = h
          (py, r2) = r
          (sy, hy) = py
          (pz, pw) = r2
          (sz, hz) = pz
          (sw, hw) = pw
          rd.at(g, ds, m, c, im, fi, nx, Bk.Term.Rwt{y, z, w}, 18, nd,
            and.i(Rd(g, m, PM.Fd(2n, m, c), im, fi, nx), Bool.and(Rd(g, m, PM.Fd(3n, m, c), im, fi, nx), Rd(g, m, PM.Fd(4n, m, c), im, fi, nx)), is.rd.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(2n, m, c), y, hy), and.i(Rd(g, m, PM.Fd(3n, m, c), im, fi, nx), Rd(g, m, PM.Fd(4n, m, c), im, fi, nx), is.rd.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(3n, m, c), z, hz), is.rd.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(4n, m, c), w, hw))))

# the cell c stands for t: every cell that T.tm.of reads from it is a cell
def is.rd(+ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +c: U32, +t: Bk.Term, h: PM.Is(ds, m, im, fi, nx, ks, img, c, t)) ->
  {Rd(Pg.Term.size(t), m, c, im, fi, nx) == True{} : Bool}:
  is.rd.at(Pg.Term.size(t), ds, m, im, fi, nx, ks, img, c, t, h)
