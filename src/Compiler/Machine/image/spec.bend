# compiler: layer B3, the image of a book
# =======================================
#
# The start of a run (Cir.result): the state St0 from which the program runs,
# once Cir.result has room for the image's cells and the input (Start says
# what it computed), and the context Cx.of of a book: its names, the terms of
# the image's cells, and the first own cell. The image is intact at the start
# (img.start: ImgOK, heap/spec.bend), and stays so through every store that
# the machine makes (img.frame, img.store, img.put: to its own cells, to the
# input's cache, or to a count). What the machine reads of it: the table by
# tag (img.table) and the body of the def that a Ref names (img.ref).

import Base
import ../../../Shared/shared.bend as Sd
import ../../../Book/impl.bend as Bk
import ../../../Eval/impl.bend as El
import ../../../Program/impl.bend as Pg
import ../../../Wasm/impl.bend as Wa
import ../../Cir/impl.bend as Cr
import ../impl.bend as Mc
import ../header/spec.bend as Hs
import ../heap/spec.bend as Hp

# The context
# -----------

# the nodes of t in pre-order, as Img.go lays out their cells, then acc
def Cx.pre(+t: Bk.Term, acc: List<&2, Bk.Term>) -> List<&2, Bk.Term>:
  match t:
    case Bk.Term.Var{_}:
      Con{t, acc}
    case Bk.Term.Ref{_}:
      Con{t, acc}
    case Bk.Term.Ann{+a, +b}:
      Con{t, Cx.pre(a, Cx.pre(b, acc))}
    case Bk.Term.Let{_, +a, +b}:
      Con{t, Cx.pre(a, Cx.pre(b, acc))}
    case Bk.Term.Typ{+a}:
      Con{t, Cx.pre(a, acc)}
    case Bk.Term.Min{+a, +b}:
      Con{t, Cx.pre(a, Cx.pre(b, acc))}
    case Bk.Term.All{_, +a, +b}:
      Con{t, Cx.pre(a, Cx.pre(b, acc))}
    case Bk.Term.Lam{_, +a}:
      Con{t, Cx.pre(a, acc)}
    case Bk.Term.App{_, +a, +b}:
      Con{t, Cx.pre(a, Cx.pre(b, acc))}
    case Bk.Term.Sig{_, +a, +b}:
      Con{t, Cx.pre(a, Cx.pre(b, acc))}
    case Bk.Term.Tup{_, +a, +b}:
      Con{t, Cx.pre(a, Cx.pre(b, acc))}
    case Bk.Term.Prj{+a}:
      Con{t, Cx.pre(a, acc)}
    case Bk.Term.Enu{_}:
      Con{t, acc}
    case Bk.Term.Lab{_}:
      Con{t, acc}
    case Bk.Term.Mat{_, +a, +b}:
      Con{t, Cx.pre(a, Cx.pre(b, acc))}
    case Bk.Term.Efq{}:
      Con{t, acc}
    case Bk.Term.Eql{+a, +b, +c}:
      Con{t, Cx.pre(a, Cx.pre(b, Cx.pre(c, acc)))}
    case Bk.Term.Rfl{}:
      Con{t, acc}
    case Bk.Term.Rwt{+a, +b, +c}:
      Con{t, Cx.pre(a, Cx.pre(b, Cx.pre(c, acc)))}

def Cx.bodies(ds: List<&2, Bk.Def>) -> List<&2, Bk.Term>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{Bk.Def{_, _, +v, _}, rest}:
      Cx.pre(v, Cx.bodies(rest))

# the terms of the image's cells, from cell 1: the fixed cells (of which only
# the Ref of main, cell 15, is read here: V.tm reads only a Ref or an Enu
# from this list), then the nodes of the bodies, as Img.cells lays them out
def Cx.terms(ds: List<&2, Bk.Def>) -> List<&2, Bk.Term>:
  List.append(&2, Bk.Term, List.replicate(Bk.Term, 14n, Bk.Term.Efq{}),
    Con{Bk.Term.Ref{Pg.Program.name.main()},
      List.append(&2, Bk.Term, List.replicate(Bk.Term, 275n, Bk.Term.Efq{}), Cx.bodies(ds))})

# the context of a run of the book ds: its names (the machine's first, then
# the bodies', as Img.cells numbers them), the terms of the image's k cells,
# and the first own cell
def Cx.of(+ds: List<&2, Bk.Def>, +k: U32, +first: U32) -> Hp.Cx:
  Hp.Cx{ds, Mc.Img.known(Mc.Img.names.defs(ds)), Cx.terms(ds), k, first}

# The start
# ---------

# the bytes of the cells up to fi + n
def Cells.bytes(+fi: U32, n: Nat) -> Nat:
  Nat.mul(20n, Nat.add(U32.to_nat(fi), n))

# the state from which Cir.result runs the program
def St0(+regs: Nat, cells: List<&2, Cr.Cir.Cell>, +first: U32, +k: U32, +p: U32, +lim: U32, i: List<&2, Word(8n)>) ->
  Cr.Cir.State:
  Cr.Cir.State{List.replicate(U32, regs, 0), Cr.Cir.load(cells, 1, Cr.Cir.Cells.none{}), first, first, k, p, lim, i, Nil{}, 0}

def Mb.is(r: Maybe<&2, U32>, +v: U32) -> Bool:
  match r:
    case Some{u}:
      U32.is_eq(u, v)
    case None{}:
      False{}

# what Cir.result computed for the start: the image's k cells, its room for
# them in m pages, the limit lim of the pages, the input's len bytes, the p
# pages after alloc, and the first cell after the input
def Start(cells: List<&2, Cr.Cir.Cell>, +i: List<&2, Word(8n)>, +m: U32, +k: U32, +len: U32, +p: U32, +lim: U32,
  +first: U32) -> Bool:
  U32.is_eq(k, Cr.Wasm.encode.len(Cr.Cir.Cell, cells)) && U32.is_le(Cr.Cir.pages(Cr.Cir.input.at(k)), m) &&
    U32.is_eq(lim, Wa.Wasm.min(m, 65536)) && Mb.is(Wa.Wasm.length32(i), len) &&
    Mb.is(Cr.Cir.alloc.pages(k, len, Cr.Cir.pages(Cr.Cir.input.at(k)), lim), p) &&
    U32.is_eq(first, Cr.Cir.first(k, U32.add(Cr.Cir.input.at(k), len)))

# The image's frame
# -----------------

def ImgOK.agree.go(n: Nat, +c: U32, +m: Cr.Cir.Cells, +m2: Cr.Cir.Cells) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+j:
      Hp.V.same(m, m2, c) && ImgOK.agree.go(j, U32.inc(c), m, m2)

# m and m2 agree on what ImgOK reads: the fields 0, 2, 3 and 4 of the cells 1
# to 15 and 272 to im
def ImgOK.agree(+x: Hp.Cx, +m: Cr.Cir.Cells, +m2: Cr.Cir.Cells) -> Bool:
  ImgOK.agree.go(15n, 1, m, m2) && ImgOK.agree.go(Nat.sub(U32.to_nat(Hp.Cx.im(x)), 271n), Mc.I.table(), m, m2)

# a store to the field k of the cell o is outside what ImgOK reads: a count
# (field 1), a cell past the image, or a cell of the input's cache
def ImgOK.out(+x: Hp.Cx, +o: U32, +k: Nat) -> Bool:
  Nat.is_eq(k, 1n) || U32.is_lt(Hp.Cx.im(x), o) || (U32.is_le(Mc.I.cache(), o) && U32.is_lt(o, Mc.I.table()))

# the table's cell of the tag t holds what Tbl.mask, Tbl.bind and Tbl.former
# give: the mask in field 2, the binders above fields 2, 3 and 4 in field 3
# (2 bits each, field 2's lowest, as M.bump reads them), and in field 4 not 0
# for a former
def ImgOK.tbl(+m: Cr.Cir.Cells, +t: U32) -> Bool:
  +c = U32.add(Mc.I.table(), t)
  U32.is_eq(Hp.Fd(2n, m, c), Hs.Tbl.mask(t)) && Nat.is_eq(U32.to_nat(U32.and(Hp.Fd(3n, m, c), 3)), Hs.Tbl.bind(t, 2n)) &&
    Nat.is_eq(U32.to_nat(U32.and(U32.shrn(Hp.Fd(3n, m, c), 2n), 3)), Hs.Tbl.bind(t, 3n)) &&
    Nat.is_eq(U32.to_nat(U32.and(U32.shrn(Hp.Fd(3n, m, c), 4n), 3)), Hs.Tbl.bind(t, 4n)) &&
    Hp.V.beq(U32.is_ne(Hp.Fd(4n, m, c), 0), Hs.Tbl.former(t))

def ImgOK.ref.of(r: Maybe<Bk.Def>, +x: Hp.Cx, +m: Cr.Cir.Cells, +c: U32) -> Bool:
  match r:
    case Some{Bk.Def{_, _, +v, _}}:
      Hp.V.img(x, m, c) && Hp.V.is(Hp.V.tm(U32.to_nat(Hp.Cx.im(x)), x, m, c, 0n), v)
    case None{}:
      U32.is_zero(c)

# the cell that a Ref of the name k holds (Img.ref): the body of the first def
# of k (El.Book.get), a STATIC cell of the image; 0 when no def has the name
def ImgOK.ref(+x: Hp.Cx, +m: Cr.Cir.Cells, +k: List<&2, Word(8n)>) -> Bool:
  ImgOK.ref.of(El.Book.get(Hp.Cx.ds(x), k), x, m, Mc.Img.ref(Mc.Img.defs(Hp.Cx.ds(x), Mc.I.book()), k))

# Laws
# ----

# LAW: the image at the start of a run of a book that Book.read reads is
# intact
law img.start:
  for +p: List<&2, Word(8n)>
  for +ds: List<&2, Bk.Def>
  for +i: List<&2, Word(8n)>
  for +m: U32
  for +k: U32
  for +len: U32
  for +pg: U32
  for +lim: U32
  for +first: U32
  for +rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>}
  for +small: {Mc.Img.small(p, 0) == True{} : Bool}
  for +s: {Start(Mc.Img.cells(ds), i, m, k, len, pg, lim, first) == True{} : Bool}
  {Hp.ImgOK(Cx.of(ds, k, first), Cr.Cir.load(Mc.Img.cells(ds), 1, Cr.Cir.Cells.none{})) == True{} : Bool}

# LAW: the image stays intact when what it reads agrees
law img.frame:
  for +x: Hp.Cx
  for +m: Cr.Cir.Cells
  for +m2: Cr.Cir.Cells
  for +h: {Hp.ImgOK(x, m) == True{} : Bool}
  for +a: {ImgOK.agree(x, m, m2) == True{} : Bool}
  {Hp.ImgOK(x, m2) == True{} : Bool}

# LAW: a store outside what the image reads keeps the agreement
law img.store:
  for +x: Hp.Cx
  for +m: Cr.Cir.Cells
  for +o: U32
  for +k: Nat
  for +v: U32
  for +n: {ImgOK.out(x, o, k) == True{} : Bool}
  {ImgOK.agree(x, m, Cr.Cir.Cells.set(m, o, Cr.Cir.Cell.set(k, Cr.Cir.Cells.get(m, o), v))) == True{} : Bool}

# LAW: so does a new cell past the image
law img.put:
  for +x: Hp.Cx
  for +m: Cr.Cir.Cells
  for +o: U32
  for +v: Cr.Cir.Cell
  for +n: {U32.is_lt(Hp.Cx.im(x), o) == True{} : Bool}
  {ImgOK.agree(x, m, Cr.Cir.Cells.set(m, o, v)) == True{} : Bool}

# LAW: the image's table gives the table by tag
law img.table:
  for +x: Hp.Cx
  for +m: Cr.Cir.Cells
  for +t: U32
  for +h: {Hp.ImgOK(x, m) == True{} : Bool}
  for +ht: {U32.is_lt(t, 19) == True{} : Bool}
  {ImgOK.tbl(m, t) == True{} : Bool}

# LAW: a Ref's cell holds its def's body
law img.ref:
  for +x: Hp.Cx
  for +m: Cr.Cir.Cells
  for +k: List<&2, Word(8n)>
  for +h: {Hp.ImgOK(x, m) == True{} : Bool}
  {ImgOK.ref(x, m, k) == True{} : Bool}
