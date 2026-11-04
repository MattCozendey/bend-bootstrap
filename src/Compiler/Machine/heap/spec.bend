# compiler: layer B3, the heap of the machine
# ===========================================
#
# What the cells of a run (Machine/impl.bend) hold, in terms: one view, one
# footprint, one heap invariant. The view V.tm reads a cell as a term at a
# binder depth d, and checks each node as it reads it: a term's tag, no BUILD
# bit, fv as its parts give it, DATA iff Term.is_data, VALUE only on a value,
# the parts of a STATIC cell STATIC and no poison among them, the name of a
# label or a λ-match as the first of its number in the image's names, the
# body of a Ref where the image places it. A poison cell (a Var whose fv is 0)
# reads as Var{d}: the canonical free variable (canon/spec.bend), so that a
# copy may share it at any depth. Its footprint V.cells is the cells that it
# reads; a heap that agrees on their fields 0, 2, 3 and 4 gives the same view
# (view.frame).
#
# The heap invariant H says, of the live cells L, the owned roots rs (a cell,
# its depth, its term), the frames fs (from the register sp) and the chains
# of argument cells chs: the own cells are L and the free list, each once;
# each live term cell counts its pointers exactly (from the live cells' fields
# of the table's mask, and from the roots); each pointer of a live cell goes
# to a live cell or to a STATIC cell of the image; each root, frame and chain
# reads as its terms, at their depths, with no real variable free there; each
# live cell is STATIC or a node of what they hold; the image is intact
# (ImgOK); and the run has no output yet. Ownership is physical: it follows
# the pointers in the cells, never the lists rs, fs or chs.

import Base
import ../../../Shared/shared.bend as Sd
import ../../../Book/impl.bend as Bk
import ../../../Eval/impl.bend as El
import ../../../Program/impl.bend as Pg
import ../../Cir/impl.bend as Cr
import ../impl.bend as Mc
import ../shared.bend as K
import ../logic/spec.bend as Lg
import ../header/spec.bend as Hs
import ../canon/spec.bend as C
import ../am/spec.bend as A

# Types
# -----

# what a run never changes: the book, the image's names and the terms of its
# cells (from cell 1), the image's last cell, the first own cell
type Cx is Data:
  Cx{ds: List<&2, Bk.Def>, ks: List<&2, List<&2, Word(8n)>>, img: List<&2, Bk.Term>, im: U32, fi: U32}

# an owned root: a cell, the depth at which it is read, and its term there
type Rt is Data:
  Rt{c: U32, d: Nat, t: Bk.Term}

# a chain of argument cells (linked by field 1) from the cell c, with their
# arguments
type Ch is Data:
  Ch{c: U32, as: List<&2, A.Ag>}

def Cx.ds(x: Cx) -> List<&2, Bk.Def>:
  match x:
    case Cx{ds, _, _, _, _}:
      ds

def Cx.ks(x: Cx) -> List<&2, List<&2, Word(8n)>>:
  match x:
    case Cx{_, ks, _, _, _}:
      ks

def Cx.img(x: Cx) -> List<&2, Bk.Term>:
  match x:
    case Cx{_, _, img, _, _}:
      img

def Cx.im(x: Cx) -> U32:
  match x:
    case Cx{_, _, _, im, _}:
      im

def Cx.fi(x: Cx) -> U32:
  match x:
    case Cx{_, _, _, _, fi}:
      fi

# Cells
# -----

def Fd(+k: Nat, m: Cr.Cir.Cells, +c: U32) -> U32:
  Cr.Cir.Cell.get(k, Cr.Cir.Cells.get(m, c))

# the parts of field 0, as the machine reads them (M.tag, M.q, M.flag, M.fv)
def Tg(m: Cr.Cir.Cells, +c: U32) -> U32:
  U32.and(Fd(0n, m, c), 63)

def Qn(m: Cr.Cir.Cells, +c: U32) -> U32:
  U32.and(U32.shrn(Fd(0n, m, c), 6n), 3)

def Fl(m: Cr.Cir.Cells, +c: U32, +bit: U32) -> Bool:
  U32.is_ne(U32.and(Fd(0n, m, c), bit), 0)

def Fv(m: Cr.Cir.Cells, +c: U32) -> U32:
  U32.shrn(Fd(0n, m, c), 13n)

# two Bools are equal
def V.beq(a: Bool, b: Bool) -> Bool:
  Bool.not(Bool.xor(a, b))

# c is one of the machine's own cells: from first, before next
def V.own(x: Cx, +st: Cr.Cir.State, +c: U32) -> Bool:
  U32.is_le(Cx.fi(x), c) && U32.is_lt(c, Lg.St.next(st))

# c is one of the image's cells, flagged STATIC
def V.img(x: Cx, +m: Cr.Cir.Cells, +c: U32) -> Bool:
  Bool.not(U32.is_zero(c)) && U32.is_le(c, Cx.im(x)) && Fl(m, c, Mc.F.static())

# the mask of the counted pointers of the cell c: the table's for its tag
# (Tbl.mask), less the fields still to copy while it is BUILD
def V.mask(+m: Cr.Cir.Cells, +c: U32) -> U32:
  Bool.pick(U32, Fl(m, c, Mc.F.build()),
    U32.and(Hs.Tbl.mask(Tg(m, c)), U32.not(U32.shrn(U32.and(Fd(0n, m, c), 57344), 13n))), Hs.Tbl.mask(Tg(m, c)))

def V.opt(+b: U32, v: U32, +rest: List<&2, U32>) -> List<&2, U32>:
  Bool.pick(List<&2, U32>, U32.is_zero(b), rest, Con{v, rest})

# the counted pointers of the cell c, in the order of its fields
def Ptrs(+m: Cr.Cir.Cells, +c: U32) -> List<&2, U32>:
  +mk = V.mask(m, c)
  V.opt(U32.and(mk, 1), Fd(2n, m, c), V.opt(U32.and(mk, 2), Fd(3n, m, c), V.opt(U32.and(mk, 4), Fd(4n, m, c), [])))

# the mask's bit of the field k (2, 3 or 4); 0 for any other field
def V.bit(k: Nat) -> U32:
  match k:
    case 2n:
      1
    case 3n:
      2
    case 4n:
      4
    case _:
      0

# The view
# --------

def V.quan(+q: U32) -> Bk.Quan:
  Bool.pick(Bk.Quan, U32.is_eq(q, 0), Bk.Quan.Q0{}, Bool.pick(Bk.Quan, U32.is_eq(q, 1), Bk.Quan.Q1{}, Bk.Quan.Q2{}))

# the name of the number i, in the image's names ks
def V.name(ks: List<&2, List<&2, Word(8n)>>, +i: U32) -> Maybe<&2, List<&2, Word(8n)>>:
  List.get(&2, List<&2, Word(8n)>, ks, U32.to_nat(i))

# the term at the cell c of the image, whose terms img hold from cell 1
def V.img.at(img: List<&2, Bk.Term>, +c: U32) -> Maybe<&2, Bk.Term>:
  List.get(&2, Bk.Term, img, U32.to_nat(U32.sub(c, 1)))

def V.mk1(k: Bk.Term -> Bk.Term, r: Maybe<&2, Bk.Term>) -> Maybe<&2, Bk.Term>:
  match r:
    case Some{a}:
      Some{k(a)}
    case None{}:
      None{}

def V.mk2(k: Bk.Term -> Bk.Term -> Bk.Term, r: Maybe<&2, Bk.Term>, s: Maybe<&2, Bk.Term>) -> Maybe<&2, Bk.Term>:
  match r s:
    case Some{a} Some{b}:
      Some{k(a, b)}
    case _ _:
      None{}

def V.mk3(k: Bk.Term -> Bk.Term -> Bk.Term -> Bk.Term, r: Maybe<&2, Bk.Term>, s: Maybe<&2, Bk.Term>,
  t: Maybe<&2, Bk.Term>) -> Maybe<&2, Bk.Term>:
  match r s t:
    case Some{a} Some{b} Some{c}:
      Some{k(a, b, c)}
    case _ _ _:
      None{}

def V.lab(n: Maybe<&2, List<&2, Word(8n)>>) -> Maybe<&2, Bk.Term>:
  match n:
    case Some{k}:
      Some{Bk.Term.Lab{k}}
    case None{}:
      None{}

def V.mat(n: Maybe<&2, List<&2, Word(8n)>>, r: Maybe<&2, Bk.Term>, s: Maybe<&2, Bk.Term>) -> Maybe<&2, Bk.Term>:
  match n r s:
    case Some{k} Some{h} Some{m}:
      Some{Bk.Term.Mat{k, h, m}}
    case _ _ _:
      None{}

# a Ref of the image (its term at its cell, when it is one)
def V.ref(inside: Bool, r: Maybe<&2, Bk.Term>) -> Maybe<&2, Bk.Term>:
  match inside r:
    case True{} Some{Bk.Term.Ref{k}}:
      Some{Bk.Term.Ref{k}}
    case _ _:
      None{}

# an Enu of the image (its term at its cell, when it is one)
def V.enu(inside: Bool, r: Maybe<&2, Bk.Term>) -> Maybe<&2, Bk.Term>:
  match inside r:
    case True{} Some{Bk.Term.Enu{ks}}:
      Some{Bk.Term.Enu{ks}}
    case _ _:
      None{}

# the term of the cell c by its tag tag and quantity q, at the depth d; r2,
# r3 and r4 read the parts in fields 2, 3 and 4 at a depth; none for a cell
# that is no term
def V.build(tag: Nat, +x: Cx, +m: Cr.Cir.Cells, +c: U32, +d: Nat, q: Bk.Quan, r2: Nat -> Maybe<&2, Bk.Term>,
  r3: Nat -> Maybe<&2, Bk.Term>, r4: Nat -> Maybe<&2, Bk.Term>) -> Maybe<&2, Bk.Term>:
  match tag:
    case 0n:
      Some{Bk.Term.Var{Bool.pick(Nat, U32.is_zero(Fv(m, c)), d, U32.to_nat(Fd(2n, m, c)))}}
    case 1n:
      V.ref(U32.is_le(c, Cx.im(x)), V.img.at(Cx.img(x), c))
    case 2n:
      V.mk2(a => b => Bk.Term.Ann{a, b}, r2(d), r3(d))
    case 3n:
      V.mk2(a => b => Bk.Term.Let{q, a, b}, r2(d), r3(1n+d))
    case 4n:
      V.mk1(a => Bk.Term.Typ{a}, r2(d))
    case 5n:
      V.mk2(a => b => Bk.Term.Min{a, b}, r2(d), r3(d))
    case 6n:
      V.mk2(a => b => Bk.Term.All{q, a, b}, r2(d), r3(1n+d))
    case 7n:
      V.mk1(a => Bk.Term.Lam{q, a}, r2(1n+d))
    case 8n:
      V.mk2(a => b => Bk.Term.App{q, a, b}, r2(d), r3(d))
    case 9n:
      V.mk2(a => b => Bk.Term.Sig{q, a, b}, r2(d), r3(1n+d))
    case 10n:
      V.mk2(a => b => Bk.Term.Tup{q, a, b}, r2(d), r3(d))
    case 11n:
      V.mk1(a => Bk.Term.Prj{a}, r2(d))
    case 12n:
      V.enu(U32.is_le(c, Cx.im(x)), V.img.at(Cx.img(x), c))
    case 13n:
      V.lab(V.name(Cx.ks(x), Fd(2n, m, c)))
    case 14n:
      V.mat(V.name(Cx.ks(x), Fd(2n, m, c)), r3(d), r4(d))
    case 15n:
      Some{Bk.Term.Efq{}}
    case 16n:
      V.mk3(a => b => t => Bk.Term.Eql{a, b, t}, r2(d), r3(d), r4(d))
    case 17n:
      Some{Bk.Term.Rfl{}}
    case 18n:
      V.mk3(a => b => t => Bk.Term.Rwt{a, b, t}, r2(d), r3(2n+d), r4(d))
    case _:
      None{}

# fv of a Var cell of the index i, as the image counts it
def V.fv.var(+i: U32) -> U32:
  Bool.pick(U32, U32.is_lt(i, 524286), U32.inc(i), 524287)

# a part's contribution to fv: its fv less the binders above it (fv_max stays)
def V.fv.kid(+m: Cr.Cir.Cells, +c: U32, +k: Nat, +bit: U32) -> U32:
  Bool.pick(U32, U32.is_zero(U32.and(Hs.Tbl.mask(Tg(m, c)), bit)), 0,
    Mc.Img.down(Fv(m, Fd(k, m, c)), U32.from_nat(Hs.Tbl.bind(Tg(m, c), k))))

# fv as the parts of the cell c give it (M.finish, Img.go)
def V.fv.kids(+m: Cr.Cir.Cells, +c: U32) -> U32:
  U32.max(V.fv.kid(m, c, 2n, 1), U32.max(V.fv.kid(m, c, 3n, 2), V.fv.kid(m, c, 4n, 4)))

# the fv of the cell c is right: a poison cell has 0, a real Var its index's,
# any other cell its parts'
def V.fv.ok(+m: Cr.Cir.Cells, +c: U32) -> Bool:
  Bool.pick(Bool, U32.is_zero(Tg(m, c)),
    U32.is_zero(Fv(m, c)) || U32.is_eq(Fv(m, c), V.fv.var(Fd(2n, m, c))),
    U32.is_eq(Fv(m, c), V.fv.kids(m, c)))

def V.all.static(cs: List<&2, U32>, +m: Cr.Cir.Cells) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{c, rest}:
      Fl(m, c, Mc.F.static()) && V.all.static(rest, m)

# a STATIC cell has STATIC parts, and is no poison
def V.st.ok(+m: Cr.Cir.Cells, +c: U32) -> Bool:
  Bool.not(Fl(m, c, Mc.F.static())) ||
    (V.all.static(Ptrs(m, c), m) && (Bool.not(U32.is_zero(Tg(m, c))) || Bool.not(U32.is_zero(Fv(m, c)))))

# the quantity bits of a cell of the term t are its quantity's
def V.q.ok(+q: U32, t: Bk.Term) -> Bool:
  match t:
    case Bk.Term.Let{p, _, _}:
      U32.is_eq(q, Mc.Img.quan(p))
    case Bk.Term.All{p, _, _}:
      U32.is_eq(q, Mc.Img.quan(p))
    case Bk.Term.Lam{p, _}:
      U32.is_eq(q, Mc.Img.quan(p))
    case Bk.Term.App{p, _, _}:
      U32.is_eq(q, Mc.Img.quan(p))
    case Bk.Term.Sig{p, _, _}:
      U32.is_eq(q, Mc.Img.quan(p))
    case Bk.Term.Tup{p, _, _}:
      U32.is_eq(q, Mc.Img.quan(p))
    case _:
      True{}

# field 2 of a cell of the term t at the depth d (n): a real Var's index (a
# poison's term is Var{d}); a Ref's body, as the image places it; the number
# of a label's or a λ-match's name, its first in the image's names
def V.leaf.ok(+x: Cx, +z: Bool, +n: U32, +d: Nat, t: Bk.Term) -> Bool:
  match t:
    case Bk.Term.Var{+i}:
      Bool.pick(Bool, z, Nat.is_eq(i, d), Nat.is_eq(i, U32.to_nat(n)))
    case Bk.Term.Ref{k}:
      U32.is_eq(n, Mc.Img.ref(Mc.Img.defs(Cx.ds(x), Mc.I.book()), k))
    case Bk.Term.Lab{k}:
      U32.is_eq(n, Mc.Img.id(Cx.ks(x), k, 0))
    case Bk.Term.Mat{k, _, _}:
      U32.is_eq(n, Mc.Img.id(Cx.ks(x), k, 0))
    case _:
      True{}

# the checks of the cell c as a node of the term t, read at the depth d
def V.chk(+x: Cx, +m: Cr.Cir.Cells, +c: U32, +d: Nat, +t: Bk.Term) -> Bool:
  Bool.not(Fl(m, c, Mc.F.build())) && V.beq(Fl(m, c, Mc.F.data()), El.Term.is_data(t)) &&
    (Bool.not(Fl(m, c, Mc.F.value())) || El.Eval.vals(Cx.ds(x), t, False{})) && V.q.ok(Qn(m, c), t) &&
    V.leaf.ok(x, U32.is_zero(Fv(m, c)), Fd(2n, m, c), d, t) && V.fv.ok(m, c) && V.st.ok(m, c)

def V.keep(zero: Bool, r: Maybe<&2, Bk.Term>, +x: Cx, +m: Cr.Cir.Cells, +c: U32, +d: Nat) -> Maybe<&2, Bk.Term>:
  match zero r:
    case False{} Some{+t}:
      Bool.pick(Maybe<&2, Bk.Term>, V.chk(x, m, c, d, t), Some{t}, None{})
    case _ _:
      None{}

# the term of the cell c at the depth d, read at most g levels deep, checked
# node by node (V.chk); none for the cell 0, for a cell that is no term, or
# when the levels run out first
def V.tm(g: Nat, +x: Cx, +m: Cr.Cir.Cells, +c: U32, +d: Nat) -> Maybe<&2, Bk.Term>:
  match g:
    case 0n:
      None{}
    case 1n++f:
      V.keep(U32.is_zero(c),
        V.build(U32.to_nat(Tg(m, c)), x, m, c, d, V.quan(Qn(m, c)), e => V.tm(f, x, m, Fd(2n, m, c), e),
          e => V.tm(f, x, m, Fd(3n, m, c), e), e => V.tm(f, x, m, Fd(4n, m, c), e)),
        x, m, c, d)

# V.tm with the levels of the state: next is enough, as the cells that a
# read visits form no cycle
def V.at(+x: Cx, +st: Cr.Cir.State, +c: U32, +d: Nat) -> Maybe<&2, Bk.Term>:
  V.tm(U32.to_nat(Lg.St.next(st)), x, Lg.St.cells(st), c, d)

# the read r gives the term t
def V.is(r: Maybe<&2, Bk.Term>, +t: Bk.Term) -> Bool:
  match r:
    case Some{u}:
      C.Term.is_eq(u, t)
    case None{}:
      False{}

def V.app(+b: U32, xs: List<&2, U32>, +rest: List<&2, U32>) -> List<&2, U32>:
  Bool.pick(List<&2, U32>, U32.is_zero(b), rest, List.append(&2, U32, xs, rest))

# the cells that V.tm reads, g levels deep
def V.cells(g: Nat, +m: Cr.Cir.Cells, +c: U32) -> List<&2, U32>:
  match g:
    case 0n:
      []
    case 1n++f:
      +mk = V.mask(m, c)
      Con{c, V.app(U32.and(mk, 1), V.cells(f, m, Fd(2n, m, c)),
        V.app(U32.and(mk, 2), V.cells(f, m, Fd(3n, m, c)), V.app(U32.and(mk, 4), V.cells(f, m, Fd(4n, m, c)), [])))}

# the term of the field k of the term t (as V.tm reads it there)
def V.kid(t: Bk.Term, k: Nat) -> Maybe<&2, Bk.Term>:
  match t k:
    case Bk.Term.Ann{a, _} 2n:
      Some{a}
    case Bk.Term.Ann{_, b} 3n:
      Some{b}
    case Bk.Term.Let{_, a, _} 2n:
      Some{a}
    case Bk.Term.Let{_, _, b} 3n:
      Some{b}
    case Bk.Term.Typ{a} 2n:
      Some{a}
    case Bk.Term.Min{a, _} 2n:
      Some{a}
    case Bk.Term.Min{_, b} 3n:
      Some{b}
    case Bk.Term.All{_, a, _} 2n:
      Some{a}
    case Bk.Term.All{_, _, b} 3n:
      Some{b}
    case Bk.Term.Lam{_, a} 2n:
      Some{a}
    case Bk.Term.App{_, a, _} 2n:
      Some{a}
    case Bk.Term.App{_, _, b} 3n:
      Some{b}
    case Bk.Term.Sig{_, a, _} 2n:
      Some{a}
    case Bk.Term.Sig{_, _, b} 3n:
      Some{b}
    case Bk.Term.Tup{_, a, _} 2n:
      Some{a}
    case Bk.Term.Tup{_, _, b} 3n:
      Some{b}
    case Bk.Term.Prj{a} 2n:
      Some{a}
    case Bk.Term.Mat{_, a, _} 3n:
      Some{a}
    case Bk.Term.Mat{_, _, b} 4n:
      Some{b}
    case Bk.Term.Eql{a, _, _} 2n:
      Some{a}
    case Bk.Term.Eql{_, b, _} 3n:
      Some{b}
    case Bk.Term.Eql{_, _, c} 4n:
      Some{c}
    case Bk.Term.Rwt{a, _, _} 2n:
      Some{a}
    case Bk.Term.Rwt{_, b, _} 3n:
      Some{b}
    case Bk.Term.Rwt{_, _, c} 4n:
      Some{c}
    case _ _:
      None{}

# the tag of the former of t (the cells' tags 0 to 18)
def V.tag(t: Bk.Term) -> U32:
  match t:
    case Bk.Term.Var{_}:
      0
    case Bk.Term.Ref{_}:
      1
    case Bk.Term.Ann{_, _}:
      2
    case Bk.Term.Let{_, _, _}:
      3
    case Bk.Term.Typ{_}:
      4
    case Bk.Term.Min{_, _}:
      5
    case Bk.Term.All{_, _, _}:
      6
    case Bk.Term.Lam{_, _}:
      7
    case Bk.Term.App{_, _, _}:
      8
    case Bk.Term.Sig{_, _, _}:
      9
    case Bk.Term.Tup{_, _, _}:
      10
    case Bk.Term.Prj{_}:
      11
    case Bk.Term.Enu{_}:
      12
    case Bk.Term.Lab{_}:
      13
    case Bk.Term.Mat{_, _, _}:
      14
    case Bk.Term.Efq{}:
      15
    case Bk.Term.Eql{_, _, _}:
      16
    case Bk.Term.Rfl{}:
      17
    case Bk.Term.Rwt{_, _, _}:
      18

# the cells c and the same cell of m2 have the same fields 0, 2, 3 and 4
def V.same(+m: Cr.Cir.Cells, +m2: Cr.Cir.Cells, +c: U32) -> Bool:
  U32.is_eq(Fd(0n, m2, c), Fd(0n, m, c)) && U32.is_eq(Fd(2n, m2, c), Fd(2n, m, c)) &&
    U32.is_eq(Fd(3n, m2, c), Fd(3n, m, c)) && U32.is_eq(Fd(4n, m2, c), Fd(4n, m, c))

# m and m2 agree on the fields 0, 2, 3 and 4 of each cell of cs
def Agree(cs: List<&2, U32>, +m: Cr.Cir.Cells, +m2: Cr.Cir.Cells) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{c, rest}:
      V.same(m, m2, c) && Agree(rest, m, m2)

def V.rc.kid(+b: U32, r: Bool) -> Bool:
  U32.is_zero(b) || r

# the real variables of the read of c, g levels deep, are bound at the depth
# d: each real Var's index is below the binders above it (a poison is bound
# by none, and needs none); a cell of no field is so; none when the levels
# run out. It does not read fv, which saturates at 524287
def V.rc(g: Nat, +m: Cr.Cir.Cells, +c: U32, +d: Nat) -> Bool:
  match g:
    case 0n:
      False{}
    case 1n++f:
      +mk = V.mask(m, c)
      Bool.pick(Bool, U32.is_zero(Tg(m, c)), U32.is_zero(Fv(m, c)) || Nat.is_lt(U32.to_nat(Fd(2n, m, c)), d),
        V.rc.kid(U32.and(mk, 1), V.rc(f, m, Fd(2n, m, c), Nat.add(d, Hs.Tbl.bind(Tg(m, c), 2n)))) &&
          V.rc.kid(U32.and(mk, 2), V.rc(f, m, Fd(3n, m, c), Nat.add(d, Hs.Tbl.bind(Tg(m, c), 3n)))) &&
          V.rc.kid(U32.and(mk, 4), V.rc(f, m, Fd(4n, m, c), Nat.add(d, Hs.Tbl.bind(Tg(m, c), 4n)))))

# The image
# ---------
#
# What the machine reads of the image (Mc.Img.cells) for the whole run: the
# labels of the names 0 to 9 and the constant terms of cells 1 to 15, STATIC;
# the table by tag (cells 272 to 290); each def's body, STATIC, at its place
# (Img.defs), read at the depth 0. Not the cache of the input's bytes (cells
# 16 to 271): only M.input reads it, and changes it.

# c is a cell of the image that a term of it may use: a fixed one (1 to 15)
# or one of the bodies' (from 291)
def ImgOK.in(+x: Cx, +c: U32) -> Bool:
  (U32.is_le(1, c) && U32.is_le(c, 15)) || (U32.is_le(Mc.I.book(), c) && U32.is_le(c, Cx.im(x)))

def ImgOK.within(cs: List<&2, U32>, +x: Cx) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{c, rest}:
      ImgOK.in(x, c) && ImgOK.within(rest, x)

# the cell c is STATIC and reads as t at the depth 0, from the image's own
# cells only
def ImgOK.at(+g: Nat, +x: Cx, +m: Cr.Cir.Cells, +c: U32, +t: Bk.Term) -> Bool:
  Fl(m, c, Mc.F.static()) && V.is(V.tm(g, x, m, c, 0n), t) && ImgOK.within(V.cells(g, m, c), x)

def ImgOK.lab(+g: Nat, +x: Cx, +m: Cr.Cir.Cells, +i: U32, +k: List<&2, Word(8n)>) -> Bool:
  ImgOK.at(g, x, m, Mc.I.lab(i), Bk.Term.Lab{k})

# the cells 1 to 15 (Img.prefix): the labels of the machine's names 0 to 9,
# the constants Nil, True, False and WNil, and the Ref of main
def ImgOK.fixed(+g: Nat, +x: Cx, +m: Cr.Cir.Cells) -> Bool:
  ImgOK.lab(g, x, m, Mc.N.unit(), Pg.Program.name.unit()) && ImgOK.lab(g, x, m, Mc.N.nil(), Pg.Program.name.nil()) &&
    ImgOK.lab(g, x, m, Mc.N.con(), Pg.Program.name.con()) && ImgOK.lab(g, x, m, Mc.N.wnil(), Pg.Program.name.wnil()) &&
    ImgOK.lab(g, x, m, Mc.N.wcon(), Pg.Program.name.wcon()) && ImgOK.lab(g, x, m, Mc.N.true(), Pg.Program.name.true()) &&
    ImgOK.lab(g, x, m, Mc.N.false(), Pg.Program.name.false()) &&
    ImgOK.lab(g, x, m, Mc.N.q0(), El.Quan.name(Bk.Quan.Q0{})) && ImgOK.lab(g, x, m, Mc.N.q1(), El.Quan.name(Bk.Quan.Q1{})) &&
    ImgOK.lab(g, x, m, Mc.N.q2(), El.Quan.name(Bk.Quan.Q2{})) && ImgOK.at(g, x, m, Mc.I.nil(), Pg.Program.bytes([])) &&
    ImgOK.at(g, x, m, Mc.I.true(), Pg.Program.bit(True{})) && ImgOK.at(g, x, m, Mc.I.false(), Pg.Program.bit(False{})) &&
    ImgOK.at(g, x, m, Mc.I.wnil(), Pg.Program.word(0n, WNil{})) &&
    ImgOK.at(g, x, m, Mc.I.ref_main(), Bk.Term.Ref{Pg.Program.name.main()})

# the cells from at hold the fields 2, 3 and 4 of cs (the table)
def ImgOK.table(cs: List<&2, Cr.Cir.Cell>, +m: Cr.Cir.Cells, +at: U32) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{Cr.Cir.Cell{_, _, a, b, c}, rest}:
      U32.is_eq(Fd(2n, m, at), a) && U32.is_eq(Fd(3n, m, at), b) && U32.is_eq(Fd(4n, m, at), c) &&
        ImgOK.table(rest, m, U32.inc(at))

# the body of each def of dl, from the cell at on (Img.defs): a cell of the
# image that reads as it
def ImgOK.bodies(dl: List<&2, Bk.Def>, +g: Nat, +x: Cx, +m: Cr.Cir.Cells, +at: U32) -> Bool:
  match dl:
    case Nil{}:
      True{}
    case Con{Bk.Def{_, _, +v, _}, rest}:
      Bool.not(U32.is_zero(at)) && U32.is_le(at, Cx.im(x)) && ImgOK.at(g, x, m, at, v) &&
        ImgOK.bodies(rest, g, x, m, U32.add(at, Mc.Img.size(v)))

# the image is intact
def ImgOK(+x: Cx, +m: Cr.Cir.Cells) -> Bool:
  U32.is_le(290, Cx.im(x)) && ImgOK.fixed(U32.to_nat(Cx.im(x)), x, m) && ImgOK.table(Mc.Img.table([]), m, Mc.I.table()) &&
    ImgOK.bodies(Cx.ds(x), U32.to_nat(Cx.im(x)), x, m, Mc.I.book())

# The heap invariant
# ------------------

# a pointer may hold c: a live cell, or a STATIC cell of the image
def V.in(+x: Cx, +st: Cr.Cir.State, +L: List<&2, U32>, +c: U32) -> Bool:
  K.Mem(L, c) || V.img(x, Lg.St.cells(st), c)

def V.cons(+c: U32, r: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match r:
    case Some{l}:
      Some{Con{c, l}}
    case None{}:
      None{}

def V.free.step(zero: Bool, free: Bool, +c: U32, r: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match zero free:
    case True{} _:
      Some{[]}
    case False{} True{}:
      V.cons(c, r)
    case False{} False{}:
      None{}

# the free list from the cell c, by field 1 to 0, each cell FREE; none when it
# is longer than n
def Free.list(n: Nat, +m: Cr.Cir.Cells, +c: U32) -> Maybe<&2, List<&2, U32>>:
  match n:
    case 0n:
      Bool.pick(Maybe<&2, List<&2, U32>>, U32.is_zero(c), Some{[]}, None{})
    case 1n+k:
      V.free.step(U32.is_zero(c), U32.is_eq(Tg(m, c), Mc.K.free()), c, Free.list(k, m, Fd(1n, m, c)))

# the free list of the state, from the register free
def V.free(+st: Cr.Cir.State) -> Maybe<&2, List<&2, U32>>:
  Free.list(U32.to_nat(Lg.St.next(st)), Lg.St.cells(st), Lg.St.reg(st, Mc.R.free()))

# no cell is twice in cs
def V.nodup(cs: List<&2, U32>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{+c, +rest}:
      Bool.not(K.Mem(rest, c)) && V.nodup(rest)

def V.all.own(cs: List<&2, U32>, +x: Cx, +st: Cr.Cir.State) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{c, rest}:
      V.own(x, st, c) && V.all.own(rest, x, st)

def Part.of(r: Maybe<&2, List<&2, U32>>, +x: Cx, +st: Cr.Cir.State, +L: List<&2, U32>) -> Bool:
  match r:
    case Some{F}:
      +all = List.append(&2, U32, L, F)
      V.nodup(all) && V.all.own(all, x, st) &&
        Nat.is_eq(List.length(&2, U32, all), Nat.sub(U32.to_nat(Lg.St.next(st)), U32.to_nat(Cx.fi(x))))
    case None{}:
      False{}

# the own cells (from first to next) are the live ones L and the free list's,
# each once
def Part(+x: Cx, +st: Cr.Cir.State, +L: List<&2, U32>) -> Bool:
  Part.of(V.free(st), x, st, L)

def V.no_out(out: List<&2, Word(8n)>) -> Bool:
  match out:
    case Nil{}:
      True{}
    case _:
      False{}

# the run's fixed parts: the image is intact and is the state's; first is past
# it; next is at most 214748364 (the last that Cir.Stmt.alloc gives); the
# registers of Mach.regs(); no output yet
def Fix(+x: Cx, +st: Cr.Cir.State) -> Bool:
  ImgOK(x, Lg.St.cells(st)) && U32.is_eq(Cx.im(x), Lg.St.image(st)) && U32.is_eq(Cx.fi(x), Lg.St.first(st)) &&
    U32.is_lt(Cx.im(x), Cx.fi(x)) && U32.is_le(Cx.fi(x), Lg.St.next(st)) && U32.is_le(Lg.St.next(st), 214748364) &&
    Nat.is_eq(Lg.St.nregs(st), Mc.Mach.regs()) && U32.is_zero(Lg.St.outn(st)) && V.no_out(Lg.St.out(st))

# room to take a cell: Part and Fix (all that M.alloc needs)
def Room(+x: Cx, +st: Cr.Cir.State, +L: List<&2, U32>) -> Bool:
  Part(x, st, L) && Fix(x, st)

# the times that c is in cs
def V.occ(cs: List<&2, U32>, +c: U32) -> Nat:
  match cs:
    case Nil{}:
      0n
    case Con{p, rest}:
      Nat.add(Bool.pick(Nat, U32.is_eq(p, c), 1n, 0n), V.occ(rest, c))

# the pointers to c from the cells of L
def V.refs(L: List<&2, U32>, +m: Cr.Cir.Cells, +c: U32) -> Nat:
  match L:
    case Nil{}:
      0n
    case Con{l, rest}:
      Nat.add(V.occ(Ptrs(m, l), c), V.refs(rest, m, c))

# the roots of the cell c
def Rt.count(rs: List<&2, Rt>, +c: U32) -> Nat:
  match rs:
    case Nil{}:
      0n
    case Con{Rt{r, _, _}, rest}:
      Nat.add(Bool.pick(Nat, U32.is_eq(r, c), 1n, 0n), Rt.count(rest, c))

# the cell c counts its pointers: a term cell, neither STATIC nor BUILD
def V.counted(+m: Cr.Cir.Cells, +c: U32) -> Bool:
  U32.is_lt(Tg(m, c), 19) && Bool.not(Fl(m, c, Mc.F.static())) && Bool.not(Fl(m, c, Mc.F.build()))

def Cnt.go(cs: List<&2, U32>, +m: Cr.Cir.Cells, +L: List<&2, U32>, +rs: List<&2, Rt>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{+c, rest}:
      (Bool.not(V.counted(m, c)) || Nat.is_eq(U32.to_nat(Fd(1n, m, c)), Nat.add(V.refs(L, m, c), Rt.count(rs, c)))) &&
        Cnt.go(rest, m, L, rs)

# each live term cell that is not STATIC and not BUILD counts its pointers
# exactly: from the live cells (Ptrs) and from the owned roots rs
def Cnt(+m: Cr.Cir.Cells, +L: List<&2, U32>, +rs: List<&2, Rt>) -> Bool:
  Cnt.go(L, m, L, rs)

def V.all.in(ps: List<&2, U32>, +x: Cx, +st: Cr.Cir.State, +L: List<&2, U32>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case Con{p, rest}:
      V.in(x, st, L, p) && V.all.in(rest, x, st, L)

def Clo.go(cs: List<&2, U32>, +x: Cx, +st: Cr.Cir.State, +L: List<&2, U32>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{c, rest}:
      V.all.in(Ptrs(Lg.St.cells(st), c), x, st, L) && Clo.go(rest, x, st, L)

# each pointer of a live cell goes to a live cell or a STATIC cell of the
# image
def Clo(+x: Cx, +st: Cr.Cir.State, +L: List<&2, U32>) -> Bool:
  Clo.go(L, x, st, L)

# the cell c reads as t at the depth d, where no real variable of it is free
# (V.rc)
def V.held.at(+x: Cx, +st: Cr.Cir.State, +c: U32, +d: Nat, +t: Bk.Term) -> Bool:
  V.is(V.at(x, st, c, d), t) && V.rc(U32.to_nat(Lg.St.next(st)), Lg.St.cells(st), c, d)

# each root is an own cell or a STATIC one of the image, and reads as its term
# at its depth, with no real variable free there
def Rts(rs: List<&2, Rt>, +x: Cx, +st: Cr.Cir.State) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case Con{Rt{+c, +d, +t}, rest}:
      (V.own(x, st, c) || V.img(x, Lg.St.cells(st), c)) && V.held.at(x, st, c, d, t) && Rts(rest, x, st)

# the depth of a frame's term (field 2): Let's body under its binder, Rwt's
# motive under its two
def V.FK.depth(k: A.FK) -> Nat:
  match k:
    case A.FK.let{}:
      1n
    case A.FK.rwt{}:
      2n
    case _:
      0n

# the second term of a frame (field 3): only Rwt's, its f
def V.frame.b(k: A.FK, +x: Cx, +st: Cr.Cir.State, +c: U32, +b: Bk.Term) -> Bool:
  match k:
    case A.FK.rwt{}:
      V.held.at(x, st, c, 0n, b)
    case _:
      True{}

# the cell c holds the frame fr: its kind's tag, its quantity, its KNOWN, its
# terms
def V.frame(+x: Cx, +st: Cr.Cir.State, +c: U32, fr: A.AF) -> Bool:
  match fr:
    case A.AF{+kind, q, k, a, b}:
      +m = Lg.St.cells(st)
      U32.is_eq(Tg(m, c), A.FK.tag(kind)) && U32.is_eq(Qn(m, c), Mc.Img.quan(q)) && V.beq(Fl(m, c, Mc.F.known()), k) &&
        V.held.at(x, st, Fd(2n, m, c), V.FK.depth(kind), a) && V.frame.b(kind, x, st, Fd(3n, m, c), b)

def Frs.go(fs: List<&2, A.AF>, +x: Cx, +st: Cr.Cir.State, +c: U32) -> Bool:
  match fs:
    case Nil{}:
      U32.is_zero(c)
    case Con{fr, rest}:
      V.own(x, st, c) && V.frame(x, st, c, fr) && Frs.go(rest, x, st, Fd(1n, Lg.St.cells(st), c))

# the frames from the register sp hold fs, the innermost first, and end there
def Frs(fs: List<&2, A.AF>, +x: Cx, +st: Cr.Cir.State) -> Bool:
  Frs.go(fs, x, st, Lg.St.reg(st, Mc.R.sp()))

def Chs.go(as: List<&2, A.Ag>, +x: Cx, +st: Cr.Cir.State, +c: U32) -> Bool:
  match as:
    case Nil{}:
      U32.is_zero(c)
    case Con{A.Ag{q, k, t}, rest}:
      +m = Lg.St.cells(st)
      V.own(x, st, c) && U32.is_eq(Tg(m, c), Mc.K.arg()) && U32.is_eq(Qn(m, c), Mc.Img.quan(q)) &&
        V.beq(Fl(m, c, Mc.F.known()), k) && V.held.at(x, st, Fd(2n, m, c), 0n, t) && Chs.go(rest, x, st, Fd(1n, m, c))

# each chain's cells hold its arguments (a cell of K.arg: their quantity,
# KNOWN, and the term of field 2 at the depth 0), and end there
def Chs(chs: List<&2, Ch>, +x: Cx, +st: Cr.Cir.State) -> Bool:
  match chs:
    case Nil{}:
      True{}
    case Con{Ch{c, as}, rest}:
      Chs.go(as, x, st, c) && Chs(rest, x, st)

def V.cells.ptrs(ps: List<&2, U32>, +st: Cr.Cir.State) -> List<&2, U32>:
  match ps:
    case Nil{}:
      []
    case Con{p, rest}:
      List.append(&2, U32, V.cells(U32.to_nat(Lg.St.next(st)), Lg.St.cells(st), p), V.cells.ptrs(rest, st))

def Rts.cells(rs: List<&2, Rt>, +st: Cr.Cir.State) -> List<&2, U32>:
  match rs:
    case Nil{}:
      []
    case Con{Rt{c, _, _}, rest}:
      List.append(&2, U32, V.cells(U32.to_nat(Lg.St.next(st)), Lg.St.cells(st), c), Rts.cells(rest, st))

def Frs.cells(fs: List<&2, A.AF>, +st: Cr.Cir.State, +c: U32) -> List<&2, U32>:
  match fs:
    case Nil{}:
      []
    case Con{_, rest}:
      Con{c, List.append(&2, U32, V.cells.ptrs(Ptrs(Lg.St.cells(st), c), st), Frs.cells(rest, st, Fd(1n, Lg.St.cells(st), c)))}

def Chs.cells.go(as: List<&2, A.Ag>, +st: Cr.Cir.State, +c: U32) -> List<&2, U32>:
  match as:
    case Nil{}:
      []
    case Con{_, rest}:
      Con{c, List.append(&2, U32, V.cells.ptrs(Ptrs(Lg.St.cells(st), c), st), Chs.cells.go(rest, st, Fd(1n, Lg.St.cells(st), c)))}

def Chs.cells(chs: List<&2, Ch>, +st: Cr.Cir.State) -> List<&2, U32>:
  match chs:
    case Nil{}:
      []
    case Con{Ch{c, as}, rest}:
      List.append(&2, U32, Chs.cells.go(as, st, c), Chs.cells(rest, st))

# the cells that the roots, the frames and the chains hold: their own, and
# their terms' nodes
def V.held(+st: Cr.Cir.State, rs: List<&2, Rt>, fs: List<&2, A.AF>, chs: List<&2, Ch>) -> List<&2, U32>:
  List.append(&2, U32, Rts.cells(rs, st), List.append(&2, U32, Frs.cells(fs, st, Lg.St.reg(st, Mc.R.sp())), Chs.cells(chs, st)))

def Cov.go(cs: List<&2, U32>, +m: Cr.Cir.Cells, +hs: List<&2, U32>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{+c, rest}:
      Bool.not(Fl(m, c, Mc.F.build())) && (Fl(m, c, Mc.F.static()) || K.Mem(hs, c)) && Cov.go(rest, m, hs)

# the live cells flagged STATIC (the input's byte cache)
def V.stat(L: List<&2, U32>, +m: Cr.Cir.Cells) -> Nat:
  match L:
    case Nil{}:
      0n
    case Con{c, rest}:
      Nat.add(Bool.pick(Nat, Fl(m, c, Mc.F.static()), 1n, 0n), V.stat(rest, m))

# no live cell is BUILD, and each is STATIC or held (V.held): no cell that no
# pointer can reach is live; and at most 6144 are STATIC (the input's cache:
# 256 bytes of 24 cells, AGENTS.md 3.9.1.4)
def Cov(+st: Cr.Cir.State, +L: List<&2, U32>, rs: List<&2, Rt>, fs: List<&2, A.AF>, chs: List<&2, Ch>) -> Bool:
  Cov.go(L, Lg.St.cells(st), V.held(st, rs, fs, chs)) && Nat.is_le(V.stat(L, Lg.St.cells(st)), 6144n)

# the heap invariant
def H(+x: Cx, +st: Cr.Cir.State, +L: List<&2, U32>, +rs: List<&2, Rt>, +fs: List<&2, A.AF>, +chs: List<&2, Ch>) -> Bool:
  Room(x, st, L) && Cnt(Lg.St.cells(st), L, rs) && Clo(x, st, L) && Rts(rs, x, st) && Frs(fs, x, st) && Chs(chs, x, st) &&
    Cov(st, L, rs, fs, chs)

def V.live.if(free: Bool, +c: U32, rest: List<&2, U32>) -> List<&2, U32>:
  match free:
    case True{}:
      rest
    case False{}:
      Con{c, rest}

def V.live.go(n: Nat, +c: U32, +F: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      []
    case 1n+k:
      V.live.if(K.Mem(F, c), c, V.live.go(k, U32.inc(c), F))

def V.free.or(r: Maybe<&2, List<&2, U32>>) -> List<&2, U32>:
  match r:
    case Some{F}:
      F
    case None{}:
      []

# the live cells of a state: its own cells that are not on the free list, in
# order
def V.Live(+st: Cr.Cir.State) -> List<&2, U32>:
  V.live.go(Nat.sub(U32.to_nat(Lg.St.next(st)), U32.to_nat(Lg.St.first(st))), Lg.St.first(st), V.free.or(V.free(st)))

# the cell c is live or a STATIC cell of the image, and reads as t at the
# depth d (what a borrowed pointer needs)
def V.Held(+x: Cx, +st: Cr.Cir.State, +L: List<&2, U32>, +c: U32, +d: Nat, +t: Bk.Term) -> Bool:
  V.in(x, st, L, c) && V.is(V.at(x, st, c, d), t)

# Laws
# ----

# LAW: the frame law: a heap that agrees on what the read reads gives the same
# term
law view.frame:
  for +g: Nat
  for +x: Cx
  for +m: Cr.Cir.Cells
  for +m2: Cr.Cir.Cells
  for +c: U32
  for +d: Nat
  for +a: {Agree(V.cells(g, m, c), m, m2) == True{} : Bool}
  {V.tm(g, x, m2, c, d) == V.tm(g, x, m, c, d) : Maybe<&2, Bk.Term>}

# LAW: more levels read the same term
law view.more:
  for +g: Nat
  for +h: Nat
  for +x: Cx
  for +m: Cr.Cir.Cells
  for +c: U32
  for +d: Nat
  for +t: Bk.Term
  for +e: {V.tm(g, x, m, c, d) == Some{t} : Maybe<&2, Bk.Term>}
  {V.tm(Nat.add(g, h), x, m, c, d) == Some{t} : Maybe<&2, Bk.Term>}

# LAW: deeper, a cell whose real variables are bound at d reads as its term
# shifted from d: only its poison moves (a copy's sharing rests on this)
law view.deeper:
  for +g: Nat
  for +x: Cx
  for +m: Cr.Cir.Cells
  for +c: U32
  for +d: Nat
  for +k: Nat
  for +t: Bk.Term
  for +hr: {V.rc(g, m, c, d) == True{} : Bool}
  for +e: {V.tm(g, x, m, c, d) == Some{t} : Maybe<&2, Bk.Term>}
  {V.tm(g, x, m, c, Nat.add(d, k)) == Some{El.Term.shift(t, k, d)} : Maybe<&2, Bk.Term>}

# LAW: a STATIC cell holds no poison: it reads as the same term at any depth
law view.static:
  for +g: Nat
  for +x: Cx
  for +m: Cr.Cir.Cells
  for +c: U32
  for +d: Nat
  for +e: Nat
  for +t: Bk.Term
  for +hs: {Fl(m, c, Mc.F.static()) == True{} : Bool}
  for +r: {V.tm(g, x, m, c, d) == Some{t} : Maybe<&2, Bk.Term>}
  {V.tm(g, x, m, c, e) == Some{t} : Maybe<&2, Bk.Term>}

# LAW: a cell whose real variables are bound at d reads canonical at d (its
# free variables are its poison)
law view.canon:
  for +g: Nat
  for +x: Cx
  for +m: Cr.Cir.Cells
  for +c: U32
  for +d: Nat
  for +t: Bk.Term
  for +hr: {V.rc(g, m, c, d) == True{} : Bool}
  for +e: {V.tm(g, x, m, c, d) == Some{t} : Maybe<&2, Bk.Term>}
  {C.Canon.is_at(t, d) == True{} : Bool}

# LAW: a STATIC cell whose real variables are bound at k reads closed at k (a
# copy's sharing of an image's part rests on this)
law view.closed:
  for +g: Nat
  for +x: Cx
  for +m: Cr.Cir.Cells
  for +c: U32
  for +d: Nat
  for +k: Nat
  for +t: Bk.Term
  for +hs: {Fl(m, c, Mc.F.static()) == True{} : Bool}
  for +hr: {V.rc(g, m, c, k) == True{} : Bool}
  for +e: {V.tm(g, x, m, c, d) == Some{t} : Maybe<&2, Bk.Term>}
  {C.Term.closed(t, k) == True{} : Bool}

# LAW: a read whose fv (not saturated) is at most d has its real variables
# bound at d (the copy's sharing test gives V.rc)
law view.rc_fv:
  for +g: Nat
  for +x: Cx
  for +m: Cr.Cir.Cells
  for +c: U32
  for +d: Nat
  for +e: Nat
  for +t: Bk.Term
  for +hs: {U32.is_lt(Fv(m, c), 524287) == True{} : Bool}
  for +hf: {Nat.is_le(U32.to_nat(Fv(m, c)), d) == True{} : Bool}
  for +r: {V.tm(g, x, m, c, e) == Some{t} : Maybe<&2, Bk.Term>}
  {V.rc(g, m, c, d) == True{} : Bool}

# LAW: V.rc reads what the view reads (its frame law)
law view.rc_frame:
  for +g: Nat
  for +m: Cr.Cir.Cells
  for +m2: Cr.Cir.Cells
  for +c: U32
  for +d: Nat
  for +a: {Agree(V.cells(g, m, c), m, m2) == True{} : Bool}
  {V.rc(g, m2, c, d) == V.rc(g, m, c, d) : Bool}

# LAW: more levels keep V.rc
law view.rc_more:
  for +g: Nat
  for +h: Nat
  for +m: Cr.Cir.Cells
  for +c: U32
  for +d: Nat
  for +r: {V.rc(g, m, c, d) == True{} : Bool}
  {V.rc(Nat.add(g, h), m, c, d) == True{} : Bool}

# LAW: bound at d, bound at any greater depth
law view.rc_up:
  for +g: Nat
  for +m: Cr.Cir.Cells
  for +c: U32
  for +d: Nat
  for +d2: Nat
  for +hd: {Nat.is_le(d, d2) == True{} : Bool}
  for +r: {V.rc(g, m, c, d) == True{} : Bool}
  {V.rc(g, m, c, d2) == True{} : Bool}

# LAW: a read checks each node (V.chk: BUILD, DATA, VALUE, quantity, field 2,
# fv, STATIC)
law view.chk:
  for +g: Nat
  for +x: Cx
  for +m: Cr.Cir.Cells
  for +c: U32
  for +d: Nat
  for +t: Bk.Term
  for +e: {V.tm(g, x, m, c, d) == Some{t} : Maybe<&2, Bk.Term>}
  {V.chk(x, m, c, d, t) == True{} : Bool}

# LAW: a read's tag is its term's former
law view.tag:
  for +g: Nat
  for +x: Cx
  for +m: Cr.Cir.Cells
  for +c: U32
  for +d: Nat
  for +t: Bk.Term
  for +e: {V.tm(g, x, m, c, d) == Some{t} : Maybe<&2, Bk.Term>}
  {Tg(m, c) == V.tag(t) : U32}

# LAW: a read's part in field k (a field of its tag's mask) reads, one level
# less deep and under the binders above it, as its term's part there
law view.kid:
  for +g: Nat
  for +x: Cx
  for +m: Cr.Cir.Cells
  for +c: U32
  for +d: Nat
  for +k: Nat
  for +t: Bk.Term
  for +e: {V.tm(1n+g, x, m, c, d) == Some{t} : Maybe<&2, Bk.Term>}
  for +hk: {U32.is_zero(U32.and(Hs.Tbl.mask(Tg(m, c)), V.bit(k))) == False{} : Bool}
  {V.tm(g, x, m, Fd(k, m, c), Nat.add(d, Hs.Tbl.bind(Tg(m, c), k))) == V.kid(t, k) : Maybe<&2, Bk.Term>}

# LAW: a store to a cell outside cs keeps Agree
law agree.store:
  for +cs: List<&2, U32>
  for +m: Cr.Cir.Cells
  for +o: U32
  for +k: Nat
  for +v: U32
  for +n: {K.Mem(cs, o) == False{} : Bool}
  {Agree(cs, m, Cr.Cir.Cells.set(m, o, Cr.Cir.Cell.set(k, Cr.Cir.Cells.get(m, o), v))) == True{} : Bool}

# LAW: so does a store to field 1 of any cell
law agree.store1:
  for +cs: List<&2, U32>
  for +m: Cr.Cir.Cells
  for +o: U32
  for +v: U32
  {Agree(cs, m, Cr.Cir.Cells.set(m, o, Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, o), v))) == True{} : Bool}

# LAW: and a new cell outside cs
law agree.put:
  for +cs: List<&2, U32>
  for +m: Cr.Cir.Cells
  for +o: U32
  for +v: Cr.Cir.Cell
  for +n: {K.Mem(cs, o) == False{} : Bool}
  {Agree(cs, m, Cr.Cir.Cells.set(m, o, v)) == True{} : Bool}

# LAW: a heap agrees with itself
law agree.refl:
  for +cs: List<&2, U32>
  for +m: Cr.Cir.Cells
  {Agree(cs, m, m) == True{} : Bool}

# LAW: agreement chains
law agree.trans:
  for +cs: List<&2, U32>
  for +m: Cr.Cir.Cells
  for +m2: Cr.Cir.Cells
  for +m3: Cr.Cir.Cells
  for +a: {Agree(cs, m, m2) == True{} : Bool}
  for +b: {Agree(cs, m2, m3) == True{} : Bool}
  {Agree(cs, m, m3) == True{} : Bool}

# LAW: H does not see a register but free and sp
law h.set:
  for +x: Cx
  for +st: Cr.Cir.State
  for +L: List<&2, U32>
  for +rs: List<&2, Rt>
  for +fs: List<&2, A.AF>
  for +chs: List<&2, Ch>
  for +r: Nat
  for +v: U32
  for +h: {H(x, st, L, rs, fs, chs) == True{} : Bool}
  for +hr: {Nat.is_lt(r, Mc.Mach.regs()) && Bool.not(Nat.is_eq(r, Mc.R.free())) && Bool.not(Nat.is_eq(r, Mc.R.sp())) == True{} : Bool}
  {H(x, Lg.St.set(st, r, v), L, rs, fs, chs) == True{} : Bool}

# LAW: the live cells of H are the state's (V.Live), up to their order
law h.live:
  for +x: Cx
  for +st: Cr.Cir.State
  for +L: List<&2, U32>
  for +rs: List<&2, Rt>
  for +fs: List<&2, A.AF>
  for +chs: List<&2, Ch>
  for +h: {H(x, st, L, rs, fs, chs) == True{} : Bool}
  {H(x, st, V.Live(st), rs, fs, chs) == True{} : Bool}

# LAW: H does not see the order of the roots: two neighbours swap, after any
# prefix pre (so any permutation, step by step)
law h.rts_swap:
  for +x: Cx
  for +st: Cr.Cir.State
  for +L: List<&2, U32>
  for +pre: List<&2, Rt>
  for +a: Rt
  for +b: Rt
  for +rs: List<&2, Rt>
  for +fs: List<&2, A.AF>
  for +chs: List<&2, Ch>
  for +h: {H(x, st, L, List.append(&2, Rt, pre, Con{a, Con{b, rs}}), fs, chs) == True{} : Bool}
  {H(x, st, L, List.append(&2, Rt, pre, Con{b, Con{a, rs}}), fs, chs) == True{} : Bool}

# LAW: nor the order of the chains
law h.chs_swap:
  for +x: Cx
  for +st: Cr.Cir.State
  for +L: List<&2, U32>
  for +rs: List<&2, Rt>
  for +fs: List<&2, A.AF>
  for +pre: List<&2, Ch>
  for +a: Ch
  for +b: Ch
  for +chs: List<&2, Ch>
  for +h: {H(x, st, L, rs, fs, List.append(&2, Ch, pre, Con{a, Con{b, chs}})) == True{} : Bool}
  {H(x, st, L, rs, fs, List.append(&2, Ch, pre, Con{b, Con{a, chs}})) == True{} : Bool}

# LAW: a STATIC cell of the image that reads as t at d (bound there) is one
# more root, with no count to change (M.ret.min's focus, a label of the image)
law h.static_root:
  for +x: Cx
  for +st: Cr.Cir.State
  for +L: List<&2, U32>
  for +rs: List<&2, Rt>
  for +fs: List<&2, A.AF>
  for +chs: List<&2, Ch>
  for +c: U32
  for +d: Nat
  for +t: Bk.Term
  for +h: {H(x, st, L, rs, fs, chs) == True{} : Bool}
  for +hc: {V.img(x, Lg.St.cells(st), c) && V.held.at(x, st, c, d, t) == True{} : Bool}
  {H(x, st, L, Con{Rt{c, d, t}, rs}, fs, chs) == True{} : Bool}

# LAW: with at most 64 roots, a live counted cell's count is below 2^31 (its
# pointers from the cells are at most 3 a live cell, and the live cells are
# below 214748364): an inc cannot wrap
law h.count:
  for +x: Cx
  for +st: Cr.Cir.State
  for +L: List<&2, U32>
  for +rs: List<&2, Rt>
  for +fs: List<&2, A.AF>
  for +chs: List<&2, Ch>
  for +c: U32
  for +h: {H(x, st, L, rs, fs, chs) == True{} : Bool}
  for +hb: {Nat.is_le(List.length(&2, Rt, rs), 64n) == True{} : Bool}
  for +hc: {K.Mem(L, c) && V.counted(Lg.St.cells(st), c) == True{} : Bool}
  {U32.is_lt(Fd(1n, Lg.St.cells(st), c), 2147483648) == True{} : Bool}
