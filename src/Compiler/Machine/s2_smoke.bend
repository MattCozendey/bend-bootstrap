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
import ./logic/spec.bend as Lg
import ./canon/spec.bend as C
import ./am/spec.bend as A
import ./heap/spec.bend as Hp
import ./image/spec.bend as I
import ./routines/spec.bend as R

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

# Whole runs: the machine against the abstract machine
# ----------------------------------------------------

# a run's check: each round's state held the abstract state (Inv), each round
# went as AM.move goes; the rounds done, and the halt (status, bytes in order)
type SR2 is Data:
  SR2{ok: Bool, n: Nat, end: Maybe<&2, A.AO>}

def smk2.vb(+st: Cr.Cir.State) -> Bool:
  Hp.Fl(Lg.St.cells(st), Lg.St.reg(st, Mc.R.focus()), Mc.F.value())

def smk2.halt(+c: U32, +c2: U32, +st2: Cr.Cir.State, +out: List<&2, Word(8n)>, +k: Nat) -> SR2:
  SR2{U32.is_eq(c, c2) && (Bool.not(U32.is_zero(c)) || Sd.Name.is_eq(List.reverse(&2, Word(8n), Lg.St.out(st2)), out)), k,
    Some{A.AO.halt{c, List.reverse(&2, Word(8n), Lg.St.out(st2))}}}

def smk2.step(ok: Bool, o: Cr.Cir.Out, e: A.AO, +k: Nat, rec: Cr.Cir.State -> A.AS -> SR2) -> SR2:
  match ok o e:
    case True{} Cr.Cir.Out.next{st2} A.AO.next{s2}:
      rec(st2, s2)
    case True{} Cr.Cir.Out.halt{c, st2} A.AO.halt{c2, out}:
      smk2.halt(c, c2, st2, out, k)
    case _ _ _:
      SR2{False{}, k, None{}}

# at most n rounds from st, which should hold s
def smk2.round(n: Nat, +x: Hp.Cx, +st: Cr.Cir.State, +s: A.AS, +k: Nat) -> SR2:
  match n:
    case 0n:
      SR2{True{}, k, None{}}
    case 1n+j:
      smk2.step(R.Inv(x, st, s), Cr.Cir.exec(4000n, Mc.Mach.round(), st), A.AM.move(Hp.Cx.ds(x), smk2.vb(st), s), k,
        st2 => s2 => smk2.round(j, x, st2, s2, 1n+k))

def smk2.or(r: Maybe<&2, U32>) -> U32:
  match r:
    case Some{v}:
      v
    case None{}:
      0

# the start of a run of ds on i, with at most 100 pages: Cir.result's values
def smk2.pg(+ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>) -> U32:
  smk2.or(Cr.Cir.alloc.pages(smk2.k(ds), Cr.Wasm.encode.len(Word(8n), i), Cr.Cir.pages(Cr.Cir.input.at(smk2.k(ds))), 100))

def smk2.st0(+ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>) -> Cr.Cir.State:
  I.St0(Mc.Mach.regs(), Mc.Img.cells(ds), smk2.first(ds, i), smk2.k(ds), smk2.pg(ds, i), 100, i)

def smk2.started(o: Cr.Cir.Out, n: Nat, +x: Hp.Cx, +i: List<&2, Word(8n)>) -> SR2:
  match o:
    case Cr.Cir.Out.next{st}:
      smk2.round(n, x, R.Mode0(st), A.AS{False{}, Pg.Program.start(i), []}, 0n)
    case _:
      SR2{False{}, 0n, None{}}

# n rounds of Mach.code on ds and i, after M.input
def smk2.run(n: Nat, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>) -> SR2:
  smk2.started(Cr.Cir.exec(4000n, Mc.M.input(), smk2.st0(ds, i)), n, smk2.x(ds, i), i)

def smk2.start.ok() -> {I.Start(Mc.Img.cells(smk2.ds()), [], 100, smk2.k(smk2.ds()), 0, smk2.pg(smk2.ds(), []), 100,
  smk2.first(smk2.ds(), [])) == True{} : Bool}:
  {==}

# main = λx. x
def smk2.id() -> List<&2, Bk.Def>:
  [smk2.def(Pg.Program.name.main(), Bk.Term.Lam{Bk.Quan.Q1{}, smk2.V(0n)})]

def smk2.run.id0() -> {smk2.run(50n, smk2.id(), []) == SR2{True{}, 6n, Some{A.AO.halt{0, []}}} : SR2}:
  {==}

def smk2.b(n: U32) -> Word(8n):
  Sd.Byte.from_u32(n)

def smk2.lam(f: Bk.Term) -> Bk.Term:
  Bk.Term.Lam{Bk.Quan.Q1{}, f}

def smk2.app(f: Bk.Term, a: Bk.Term) -> Bk.Term:
  Bk.Term.App{Bk.Quan.Q1{}, f, a}

def smk2.mainof(v: Bk.Term) -> List<&2, Bk.Def>:
  [smk2.def(Pg.Program.name.main(), v)]

# the halt of a run that held at every round
def smk2.ok(r: SR2) -> Maybe<&2, A.AO>:
  match r:
    case SR2{True{}, _, e}:
      e
    case SR2{False{}, _, _}:
      None{}

def smk2.h0(bs: List<&2, Word(8n)>) -> Maybe<&2, A.AO>:
  Some{A.AO.halt{0, bs}}

def smk2.h2() -> Maybe<&2, A.AO>:
  Some{A.AO.halt{2, []}}

# a negative control: a state that does not hold the abstract state fails
def smk2.run.neg() -> {smk2.started(Cr.Cir.exec(4000n, Mc.M.input(), smk2.st0(smk2.id(), [])), 5n, smk2.x(smk2.id(), []), [smk2.b(5)]) ==
  SR2{False{}, 0n, None{}} : SR2}:
  {==}

def smk2.run.id1() -> {smk2.ok(smk2.run(400n, smk2.id(), [smk2.b(5)])) == smk2.h0([smk2.b(5)]) : Maybe<&2, A.AO>}:
  {==}

# main = λx. match x { Nil: Nil; Con h t: t }, by λ-matches of pairs and labels
def smk2.tail() -> List<&2, Bk.Def>:
  smk2.mainof(Bk.Term.Prj{Bk.Term.Mat{Pg.Program.name.nil(), smk2.lam(Pg.Program.bytes([])),
    Bk.Term.Mat{Pg.Program.name.con(), Bk.Term.Prj{smk2.lam(Bk.Term.Prj{smk2.lam(smk2.lam(smk2.V(1n)))})}, Bk.Term.Efq{}}}})

def smk2.run.tail0() -> {smk2.ok(smk2.run(400n, smk2.tail(), [])) == smk2.h0([]) : Maybe<&2, A.AO>}:
  {==}

def smk2.run.tail2() -> {smk2.ok(smk2.run(800n, smk2.tail(), [smk2.b(5), smk2.b(7)])) == smk2.h0([smk2.b(7)]) : Maybe<&2, A.AO>}:
  {==}

# main = λx. (λ0 y. x) v7: a walk through a poison argument
def smk2.poison() -> List<&2, Bk.Def>:
  smk2.mainof(smk2.lam(Bk.Term.App{Bk.Quan.Q0{}, Bk.Term.Lam{Bk.Quan.Q0{}, smk2.V(1n)}, smk2.V(7n)}))

def smk2.run.poison() -> {smk2.ok(smk2.run(400n, smk2.poison(), [])) == smk2.h0([]) : Maybe<&2, A.AO>}:
  {==}

# main = λx. v3: stuck on a free variable
def smk2.free() -> List<&2, Bk.Def>:
  smk2.mainof(smk2.lam(smk2.V(3n)))

def smk2.run.free() -> {smk2.ok(smk2.run(400n, smk2.free(), [])) == smk2.h2() : Maybe<&2, A.AO>}:
  {==}

# main = λx. (let1 m = Min Q1 Q2; rwt Rfl (Typ v0): let0 _ = m; x) :: Efq
def smk2.mix() -> List<&2, Bk.Def>:
  smk2.mainof(smk2.lam(Bk.Term.Ann{
    Bk.Term.Let{Bk.Quan.Q1{}, Bk.Term.Min{Bk.Term.Lab{El.Quan.name(Bk.Quan.Q1{})}, Bk.Term.Lab{El.Quan.name(Bk.Quan.Q2{})}},
      Bk.Term.Rwt{Bk.Term.Rfl{}, Bk.Term.Typ{smk2.V(0n)}, Bk.Term.Let{Bk.Quan.Q0{}, smk2.V(0n), smk2.V(2n)}}},
    Bk.Term.Efq{}}))

def smk2.run.mix() -> {smk2.ok(smk2.run(400n, smk2.mix(), [])) == smk2.h0([]) : Maybe<&2, A.AO>}:
  {==}

# main = λx. Min x Q0: no meet
def smk2.nomeet() -> List<&2, Bk.Def>:
  smk2.mainof(smk2.lam(Bk.Term.Min{smk2.V(0n), Bk.Term.Lab{El.Quan.name(Bk.Quan.Q0{})}}))

def smk2.run.nomeet() -> {smk2.ok(smk2.run(400n, smk2.nomeet(), [])) == smk2.h2() : Maybe<&2, A.AO>}:
  {==}

# main = λx. (λf. f x) (λ-match of pairs: λ-match of labels Con: λh. λ-match
# of pairs: λt. λu. t; else λu. λv. Nil): redexes of λ-matches in the term
def smk2.redex() -> List<&2, Bk.Def>:
  smk2.mainof(smk2.lam(smk2.app(smk2.lam(smk2.app(smk2.V(0n), smk2.V(1n))),
    Bk.Term.Prj{Bk.Term.Mat{Pg.Program.name.con(), Bk.Term.Prj{smk2.lam(Bk.Term.Prj{smk2.lam(smk2.lam(smk2.V(1n)))})},
      smk2.lam(smk2.lam(Pg.Program.bytes([])))}})))

def smk2.run.redex2() -> {smk2.ok(smk2.run(800n, smk2.redex(), [smk2.b(5), smk2.b(7)])) == smk2.h0([smk2.b(7)]) : Maybe<&2, A.AO>}:
  {==}

# main = λx. f x; f = λy. (y, Lab a): a call of a def, then no list of bytes
def smk2.run.two() -> {smk2.ok(smk2.run(400n, smk2.ds(), [])) == smk2.h2() : Maybe<&2, A.AO>}:
  {==}
