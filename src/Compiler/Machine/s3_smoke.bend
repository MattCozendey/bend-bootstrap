# compiler: smoke checks of canon/spec.bend and am/spec.bend (P2, lane S3)
# =========================================================================
#
# Test c (bend2 kinds): computed checks, by {==}, that the statements of
# canon.step, canon.subst, canon.lift and am.ok hold on small terms with free
# variables, and that the abstract machine, run move by move with each move
# checked by AO.ok, ends small programs with the result that Eval gives. They
# stand until the laws are proven (canon.step, canon.subst, canon.subst_below,
# canon.lift, am.ok, am.walk_eval replace them); the redesign's P5 deletes this
# file. It is outside main's closure.

import Base
import ../../Shared/shared.bend as Sd
import ../../Book/impl.bend as Bk
import ../../Eval/impl.bend as El
import ../../Program/impl.bend as Pg
import ./canon/spec.bend as C
import ./am/spec.bend as A

# what a run of the abstract machine gives: each move was right; and its
# halt, or none when the fuel ran out
type SR is Data:
  SR{ok: Bool, end: Maybe<&2, A.AO>}

def SR.and(a: Bool, r: SR) -> SR:
  match r:
    case SR{b, e}:
      SR{a && b, e}

def Smk.cont(ok: Bool, o: A.AO, k: A.AS -> SR) -> SR:
  match o:
    case A.AO.next{s2}:
      SR.and(ok, k(s2))
    case A.AO.halt{c, out}:
      SR{ok, Some{A.AO.halt{c, out}}}

# at most n moves from s, each with no VALUE flag, each checked by AO.ok
def Smk.run(n: Nat, +ds: List<&2, Bk.Def>, +s: A.AS) -> SR:
  match n:
    case 0n:
      SR{True{}, None{}}
    case 1n+m:
      Smk.cont(A.AO.ok(ds, s, A.AM.move(ds, False{}, s)), A.AM.move(ds, False{}, s), r => Smk.run(m, ds, r))

# the same, with the VALUE flag on each focus that is a value (the most that
# AS.ok allows)
def Smk.vb(+ds: List<&2, Bk.Def>, +s: A.AS) -> Bool:
  Bool.not(A.AS.ret(s)) && El.Eval.vals(ds, A.AS.focus(s), False{})

def Smk.runv(n: Nat, +ds: List<&2, Bk.Def>, +s: A.AS) -> SR:
  match n:
    case 0n:
      SR{True{}, None{}}
    case 1n+m:
      Smk.cont(A.AO.ok(ds, s, A.AM.move(ds, Smk.vb(ds, s), s)), A.AM.move(ds, Smk.vb(ds, s), s), r => Smk.runv(m, ds, r))

# the start state of a run of main on the input i
def Smk.start(+i: List<&2, Word(8n)>) -> A.AS:
  A.AS{False{}, Pg.Program.start(i), []}

def smk.nm(c: U32) -> List<&2, Word(8n)>:
  [Sd.Byte.from_u32(c)]

def smk.V(i: Nat) -> Bk.Term:
  Bk.Term.Var{i}

def smk.app1(f: Bk.Term, x: Bk.Term) -> Bk.Term:
  Bk.Term.App{Bk.Quan.Q1{}, f, x}

def smk.lam1(f: Bk.Term) -> Bk.Term:
  Bk.Term.Lam{Bk.Quan.Q1{}, f}

def smk.def1(k: List<&2, Word(8n)>, v: Bk.Term) -> Bk.Def:
  Bk.Def{k, Bk.Term.Efq{}, v, False{}}

def smk.lab(k: List<&2, Word(8n)>) -> Bk.Term:
  Bk.Term.Lab{k}

# Canon.term
# ----------

def smk.canon.var() -> {C.Canon.term(smk.V(3n), 0n) == smk.V(0n) : Bk.Term}:
  {==}

def smk.canon.lam() -> {C.Canon.term(smk.lam1(smk.app1(smk.V(0n), smk.V(5n))), 0n) == smk.lam1(smk.app1(smk.V(0n), smk.V(1n))) : Bk.Term}:
  {==}

def smk.canon.rwt() -> {C.Canon.term(Bk.Term.Rwt{smk.V(2n), smk.V(4n), smk.V(1n)}, 1n) == Bk.Term.Rwt{smk.V(1n), smk.V(3n), smk.V(1n)} : Bk.Term}:
  {==}

def smk.canon.is() -> {C.Canon.is(smk.lam1(smk.app1(smk.V(1n), smk.V(0n)))) == True{} : Bool}:
  {==}

def smk.canon.not() -> {C.Canon.is(smk.lam1(smk.app1(smk.V(2n), smk.V(0n)))) == False{} : Bool}:
  {==}

# CStep and canon.step
# --------------------

# (λ0 y. y z) w, both free: the step's canonical form
def smk.t1() -> Bk.Term:
  Bk.Term.App{Bk.Quan.Q0{}, Bk.Term.Lam{Bk.Quan.Q0{}, smk.app1(smk.V(0n), smk.V(1n))}, smk.V(7n)}

def smk.step.t1() -> {C.CStep([], smk.t1()) == Some{smk.app1(smk.V(0n), smk.V(0n))} : Maybe<Bk.Term>}:
  {==}

def smk.canon.step.t1() -> {C.CStep([], C.Canon.term(smk.t1(), 0n)) == C.CStep([], smk.t1()) : Maybe<Bk.Term>}:
  {==}

# a def f = λx. x v3 (open), called on a label: its walk's leaf, with the free
# variable moved down by the local
def smk.ds2() -> List<&2, Bk.Def>:
  [smk.def1(smk.nm(102), smk.lam1(smk.app1(smk.V(0n), smk.V(3n))))]

def smk.t2() -> Bk.Term:
  smk.app1(Bk.Term.Ref{smk.nm(102)}, smk.lab(smk.nm(97)))

def smk.step.t2() -> {El.Eval.step(smk.ds2(), smk.t2()) == Some{smk.app1(smk.lab(smk.nm(97)), smk.V(2n))} : Maybe<Bk.Term>}:
  {==}

def smk.canon.step.t2() -> {C.CStep(smk.ds2(), C.Canon.term(smk.t2(), 0n)) == C.CStep(smk.ds2(), smk.t2()) : Maybe<Bk.Term>}:
  {==}

# a def g = (λy. y) v5: the walk passes a variable with no local (poison)
def smk.ds3() -> List<&2, Bk.Def>:
  [smk.def1(smk.nm(103), smk.app1(smk.lam1(smk.V(0n)), smk.V(5n)))]

def smk.step.t3() -> {El.Eval.step(smk.ds3(), Bk.Term.Ref{smk.nm(103)}) == Some{smk.V(5n)} : Maybe<Bk.Term>}:
  {==}

def smk.cstep.t3() -> {C.CStep(smk.ds3(), Bk.Term.Ref{smk.nm(103)}) == Some{smk.V(0n)} : Maybe<Bk.Term>}:
  {==}

def smk.am.t3() ->
  {A.AM.move(smk.ds3(), False{}, A.AS{False{}, Bk.Term.Ref{smk.nm(103)}, []}) == A.AO.next{A.AS{False{}, smk.V(0n), []}} : A.AO}:
  {==}

def smk.am.t3.ok() -> {A.AO.ok(smk.ds3(), A.AS{False{}, Bk.Term.Ref{smk.nm(103)}, []},
  A.AM.move(smk.ds3(), False{}, A.AS{False{}, Bk.Term.Ref{smk.nm(103)}, []})) == True{} : Bool}:
  {==}

# the poison: no step, no result, a halt with 2
def smk.am.t3.halt() ->
  {A.AM.move(smk.ds3(), False{}, A.AS{False{}, smk.V(0n), []}) == A.AO.halt{2, []} : A.AO}:
  {==}

def smk.am.t3.halt.ok() -> {A.AO.ok(smk.ds3(), A.AS{False{}, smk.V(0n), []}, A.AO.halt{2, []}) == True{} : Bool}:
  {==}

# the canonical step of an open term in frames: (λ0 y. y z) w in Tup □ (Lab a)
def smk.am.t1() -> A.AS:
  A.AS{True{}, Bk.Term.Lam{Bk.Quan.Q0{}, smk.app1(smk.V(0n), smk.V(1n))},
    [A.AF{A.FK.arg{}, Bk.Quan.Q0{}, False{}, smk.V(0n), smk.V(0n)}, A.AF{A.FK.tupb{}, Bk.Quan.Q1{}, False{}, smk.lab(smk.nm(97)), smk.lab(smk.nm(97))}]}

def smk.am.t1.move() -> {A.AM.move([], False{}, smk.am.t1()) ==
  A.AO.next{A.AS{False{}, smk.app1(smk.V(0n), smk.V(0n)), [A.AF{A.FK.tupb{}, Bk.Quan.Q1{}, False{}, smk.lab(smk.nm(97)), smk.lab(smk.nm(97))}]}} : A.AO}:
  {==}

def smk.am.t1.ok() -> {A.AO.ok([], smk.am.t1(), A.AM.move([], False{}, smk.am.t1())) == True{} : Bool}:
  {==}

# canon.subst, canon.subst_below, canon.lift
# ------------------------------------------

def smk.subst() -> {C.Canon.term(El.Term.subst(C.Canon.term(smk.lam1(smk.app1(smk.V(1n), smk.app1(smk.V(2n), smk.V(4n)))), 1n), [smk.V(6n)], 0n), 0n) ==
  C.Canon.term(El.Term.subst(smk.lam1(smk.app1(smk.V(1n), smk.app1(smk.V(2n), smk.V(4n)))), [smk.V(6n)], 0n), 0n) : Bk.Term}:
  {==}

# Q = λ. v0 v1 v2 at the depth 1 (v2 the poison), moved up by 1, then
# substituted at 1 by one term
def smk.subst_below() -> {C.Canon.term(El.Term.subst(El.Term.shift(smk.lam1(smk.app1(smk.V(0n), smk.app1(smk.V(1n), smk.V(2n)))), 1n, 1n), [smk.lab(smk.nm(97))], 1n), 1n) ==
  smk.lam1(smk.app1(smk.V(0n), smk.app1(smk.V(1n), smk.V(2n)))) : Bk.Term}:
  {==}

def smk.lift() -> {C.Canon.term(El.Term.lift([smk.lam1(smk.V(1n)), smk.lab(smk.nm(97))], 2n, 2n), 2n) ==
  El.Term.shift(smk.lam1(smk.V(1n)), 2n, 0n) : Bk.Term}:
  {==}

# am.walk_eval
# ------------

def smk.walk.t3() -> {A.AW.eval(A.AM.walk(smk.ds3(), smk.app1(smk.lam1(smk.V(0n)), smk.V(5n)), [], [])) ==
  C.Canon.walk(El.Eval.walk(smk.app1(smk.lam1(smk.V(0n)), smk.V(5n)), [], [])) : Maybe<Maybe<Bk.Term>>}:
  {==}

# Whole runs
# ----------

# main = λx. x
def smk.id() -> List<&2, Bk.Def>:
  [smk.def1(Pg.Program.name.main(), smk.lam1(smk.V(0n)))]

def smk.run.id0() -> {Smk.run(400n, smk.id(), Smk.start([])) == SR{True{}, Some{A.AO.halt{0, []}}} : SR}:
  {==}

def smk.run.id1() -> {Smk.run(2000n, smk.id(), Smk.start([Sd.Byte.from_u32(5)])) ==
  SR{True{}, Some{A.AO.halt{0, [Sd.Byte.from_u32(5)]}}} : SR}:
  {==}

# main = λx. match x { Nil: Nil; Con h t: t }, as λ-matches of pairs and of
# labels
def smk.tail() -> List<&2, Bk.Def>:
  [smk.def1(Pg.Program.name.main(),
    Bk.Term.Prj{Bk.Term.Mat{Pg.Program.name.nil(), smk.lam1(Pg.Program.bytes([])),
      Bk.Term.Mat{Pg.Program.name.con(), Bk.Term.Prj{smk.lam1(Bk.Term.Prj{smk.lam1(smk.lam1(smk.V(1n)))})}, Bk.Term.Efq{}}}})]

def smk.run.tail0() -> {Smk.run(400n, smk.tail(), Smk.start([])) == SR{True{}, Some{A.AO.halt{0, []}}} : SR}:
  {==}

def smk.run.tail1() -> {Smk.run(4000n, smk.tail(), Smk.start([Sd.Byte.from_u32(5)])) ==
  SR{True{}, Some{A.AO.halt{0, []}}} : SR}:
  {==}

# main = λx. (λ0 y. x) v7: a walk through a poison argument
def smk.poison() -> List<&2, Bk.Def>:
  [smk.def1(Pg.Program.name.main(), smk.lam1(Bk.Term.App{Bk.Quan.Q0{}, Bk.Term.Lam{Bk.Quan.Q0{}, smk.V(1n)}, smk.V(7n)}))]

def smk.run.poison() -> {Smk.run(400n, smk.poison(), Smk.start([])) == SR{True{}, Some{A.AO.halt{0, []}}} : SR}:
  {==}

# main = λx. v3: stuck on a free variable, no result
def smk.free() -> List<&2, Bk.Def>:
  [smk.def1(Pg.Program.name.main(), smk.lam1(smk.V(3n)))]

def smk.run.free() -> {Smk.run(400n, smk.free(), Smk.start([])) == SR{True{}, Some{A.AO.halt{2, []}}} : SR}:
  {==}

# main = λx. (let1 m = Min Q1 Q2; rwt Rfl (Typ v0): let0 _ = m; x) :: Efq
def smk.mix() -> List<&2, Bk.Def>:
  [smk.def1(Pg.Program.name.main(), smk.lam1(Bk.Term.Ann{
    Bk.Term.Let{Bk.Quan.Q1{}, Bk.Term.Min{smk.lab(El.Quan.name(Bk.Quan.Q1{})), smk.lab(El.Quan.name(Bk.Quan.Q2{}))},
      Bk.Term.Rwt{Bk.Term.Rfl{}, Bk.Term.Typ{smk.V(0n)}, Bk.Term.Let{Bk.Quan.Q0{}, smk.V(0n), smk.V(2n)}}},
    Bk.Term.Efq{}}))]

def smk.run.mix() -> {Smk.run(400n, smk.mix(), Smk.start([])) == SR{True{}, Some{A.AO.halt{0, []}}} : SR}:
  {==}

# main = λx. Min x Q0: no meet of a list and a label, a halt with 2
def smk.nomeet() -> List<&2, Bk.Def>:
  [smk.def1(Pg.Program.name.main(), smk.lam1(Bk.Term.Min{smk.V(0n), smk.lab(El.Quan.name(Bk.Quan.Q0{}))}))]

def smk.run.nomeet() -> {Smk.run(400n, smk.nomeet(), Smk.start([])) == SR{True{}, Some{A.AO.halt{2, []}}} : SR}:
  {==}

# main = λx. (λf. f x) (λ-match of pairs: λ-match of labels Con: λh. λ-match
# of pairs: λt. λu. t; else λu. λv. Nil): the redexes of a λ-match of pairs
# and of labels, in the running term
def smk.redex() -> List<&2, Bk.Def>:
  [smk.def1(Pg.Program.name.main(), smk.lam1(smk.app1(smk.lam1(smk.app1(smk.V(0n), smk.V(1n))),
    Bk.Term.Prj{Bk.Term.Mat{Pg.Program.name.con(), Bk.Term.Prj{smk.lam1(Bk.Term.Prj{smk.lam1(smk.lam1(smk.V(1n)))})},
      smk.lam1(smk.lam1(Pg.Program.bytes([])))}})))]

def smk.run.redex0() -> {Smk.run(1000n, smk.redex(), Smk.start([])) == SR{True{}, Some{A.AO.halt{0, []}}} : SR}:
  {==}

def smk.run.redex1() -> {Smk.run(4000n, smk.redex(), Smk.start([Sd.Byte.from_u32(5)])) ==
  SR{True{}, Some{A.AO.halt{0, []}}} : SR}:
  {==}

# The same runs, with the VALUE flag on each value
# -----------------------------------------------

def smk.runv.id1() -> {Smk.runv(2000n, smk.id(), Smk.start([Sd.Byte.from_u32(5)])) ==
  SR{True{}, Some{A.AO.halt{0, [Sd.Byte.from_u32(5)]}}} : SR}:
  {==}

def smk.runv.tail2() -> {Smk.runv(4000n, smk.tail(), Smk.start([Sd.Byte.from_u32(5), Sd.Byte.from_u32(7)])) ==
  SR{True{}, Some{A.AO.halt{0, [Sd.Byte.from_u32(7)]}}} : SR}:
  {==}

def smk.runv.redex2() -> {Smk.runv(4000n, smk.redex(), Smk.start([Sd.Byte.from_u32(5), Sd.Byte.from_u32(7)])) ==
  SR{True{}, Some{A.AO.halt{0, [Sd.Byte.from_u32(7)]}}} : SR}:
  {==}

def smk.runv.mix() -> {Smk.runv(400n, smk.mix(), Smk.start([])) == SR{True{}, Some{A.AO.halt{0, []}}} : SR}:
  {==}

def smk.runv.poison() -> {Smk.runv(400n, smk.poison(), Smk.start([])) == SR{True{}, Some{A.AO.halt{0, []}}} : SR}:
  {==}
