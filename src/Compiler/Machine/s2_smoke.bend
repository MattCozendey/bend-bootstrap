# compiler: smoke checks of heap/spec.bend, image/spec.bend and routines/spec.bend (P2, lane S2)
# ===============================================================================================
#
# Test c (bend2 kinds): computed checks, by {==}, that the statements hold on
# small states of real runs: the view V.tm on the start image of a two-def
# book gives the bodies, and ImgOK holds there (img.start, img.ref,
# img.table replace them); and, round by round on whole runs of Mach.code
# from St0, that the machine's state holds the abstract machine's state:
# Inv of AM.move's next state after each Mach.round(), and AM.move's halt at
# the end (round.sim, input.spec and out.spec replace them). It is outside
# main's closure; the redesign's P5 deletes it.

import Base
import ../../Shared/shared.bend as Sd
import ../../Book/impl.bend as Bk
import ../../Eval/impl.bend as El
import ../../Program/impl.bend as Pg
import ../Cir/impl.bend as Cr
import ./impl.bend as Mc
import ./s1stub/logic.bend as Lg
import ./canon/spec.bend as C
import ./am/spec.bend as A
import ./heap/spec.bend as Hp
import ./image/spec.bend as I

def smk2.nm(c: U32) -> List<&2, Word(8n)>:
  [Sd.Byte.from_u32(c)]

def smk2.V(i: Nat) -> Bk.Term:
  Bk.Term.Var{i}

def smk2.def(k: List<&2, Word(8n)>, v: Bk.Term) -> Bk.Def:
  Bk.Def{k, Bk.Term.Efq{}, v, False{}}

# main = λx. f x; f = λy. (y, Lab a)
def smk2.f() -> Bk.Term:
  Bk.Term.Lam{Bk.Quan.Q1{}, Bk.Term.Tup{Bk.Quan.Q1{}, smk2.V(0n), Bk.Term.Lab{smk2.nm(97)}}}

def smk2.main() -> Bk.Term:
  Bk.Term.Lam{Bk.Quan.Q1{}, Bk.Term.App{Bk.Quan.Q1{}, Bk.Term.Ref{smk2.nm(102)}, smk2.V(0n)}}

def smk2.ds() -> List<&2, Bk.Def>:
  [smk2.def(Pg.Program.name.main(), smk2.main()), smk2.def(smk2.nm(102), smk2.f())]

# the start image of a book, and its context (first: the first cell after
# an empty input)
def smk2.k(+ds: List<&2, Bk.Def>) -> U32:
  Cr.Wasm.encode.len(Cr.Cir.Cell, Mc.Img.cells(ds))

def smk2.m(+ds: List<&2, Bk.Def>) -> Cr.Cir.Cells:
  Cr.Cir.load(Mc.Img.cells(ds), 1, Cr.Cir.Cells.none{})

def smk2.first(+ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>) -> U32:
  Cr.Cir.first(smk2.k(ds), U32.add(Cr.Cir.input.at(smk2.k(ds)), Cr.Wasm.encode.len(Word(8n), i)))

def smk2.x(+ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>) -> Hp.Cx:
  I.Cx.of(ds, smk2.k(ds), smk2.first(ds, i))

# The view on the start image
# ---------------------------

def smk2.v.main() -> {Hp.V.tm(400n, smk2.x(smk2.ds(), []), smk2.m(smk2.ds()), Mc.I.book(), 0n) == Some{smk2.main()} : Maybe<&2, Bk.Term>}:
  {==}

def smk2.v.f() -> {Hp.V.tm(400n, smk2.x(smk2.ds(), []), smk2.m(smk2.ds()), U32.add(Mc.I.book(), Mc.Img.size(smk2.main())), 0n) ==
  Some{smk2.f()} : Maybe<&2, Bk.Term>}:
  {==}

# deeper, f's body: the same term (no poison, the variable is bound)
def smk2.v.f.body() -> {Hp.V.tm(400n, smk2.x(smk2.ds(), []), smk2.m(smk2.ds()), U32.add(Mc.I.book(), U32.inc(Mc.Img.size(smk2.main()))), 5n) ==
  Some{Bk.Term.Tup{Bk.Quan.Q1{}, smk2.V(0n), Bk.Term.Lab{smk2.nm(97)}}} : Maybe<&2, Bk.Term>}:
  {==}

def smk2.v.nil() -> {Hp.V.tm(400n, smk2.x(smk2.ds(), []), smk2.m(smk2.ds()), Mc.I.nil(), 0n) == Some{Pg.Program.bytes([])} : Maybe<&2, Bk.Term>}:
  {==}

# a table cell is no term: as a Var cell with fv 0 it would read as poison,
# but no pointer of a live cell may hold it (Clo), and it is not STATIC
def smk2.v.table() -> {Hp.V.tm(400n, smk2.x(smk2.ds(), []), smk2.m(smk2.ds()), Mc.I.table(), 3n) == Some{smk2.V(3n)} : Maybe<&2, Bk.Term>}:
  {==}

def smk2.v.zero() -> {Hp.V.tm(400n, smk2.x(smk2.ds(), []), smk2.m(smk2.ds()), 0, 0n) == None{} : Maybe<&2, Bk.Term>}:
  {==}

def smk2.imgok() -> {Hp.ImgOK(smk2.x(smk2.ds(), []), smk2.m(smk2.ds())) == True{} : Bool}:
  {==}

def smk2.ref.f() -> {I.ImgOK.ref(smk2.x(smk2.ds(), []), smk2.m(smk2.ds()), smk2.nm(102)) == True{} : Bool}:
  {==}

def smk2.ref.none() -> {I.ImgOK.ref(smk2.x(smk2.ds(), []), smk2.m(smk2.ds()), smk2.nm(103)) == True{} : Bool}:
  {==}

def smk2.tbl.let() -> {I.ImgOK.tbl(smk2.m(smk2.ds()), 3) == True{} : Bool}:
  {==}

def smk2.tbl.rwt() -> {I.ImgOK.tbl(smk2.m(smk2.ds()), 18) == True{} : Bool}:
  {==}

def smk2.tbl.lam() -> {I.ImgOK.tbl(smk2.m(smk2.ds()), 7) == True{} : Bool}:
  {==}
