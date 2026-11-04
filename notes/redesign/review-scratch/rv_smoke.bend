# review scratch (s123): whole runs of Mach.code against AM.move on the
# branches that s2_smoke and s3_smoke did not run; at every round: Inv, AS.ok
# (with the focus' VALUE flag) and am.ok's conclusion AO.ok. Lives in
# Compiler/Machine/ of a scratch copy only.

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

type RV is Data:
  RV{ok: Bool, n: Nat, end: Maybe<&2, A.AO>}

def rv.nm(c: U32) -> List<&2, Word(8n)>:
  [Sd.Byte.from_u32(c)]

def rv.V(i: Nat) -> Bk.Term:
  Bk.Term.Var{i}

def rv.def(k: List<&2, Word(8n)>, v: Bk.Term) -> Bk.Def:
  Bk.Def{k, Bk.Term.Efq{}, v, False{}}

def rv.mainof(v: Bk.Term) -> List<&2, Bk.Def>:
  [rv.def(Pg.Program.name.main(), v)]

def rv.lam(f: Bk.Term) -> Bk.Term:
  Bk.Term.Lam{Bk.Quan.Q1{}, f}

def rv.app(f: Bk.Term, a: Bk.Term) -> Bk.Term:
  Bk.Term.App{Bk.Quan.Q1{}, f, a}

def rv.lab(k: List<&2, Word(8n)>) -> Bk.Term:
  Bk.Term.Lab{k}

def rv.b(n: U32) -> Word(8n):
  Sd.Byte.from_u32(n)

def rv.k(+ds: List<&2, Bk.Def>) -> U32:
  Cr.Wasm.encode.len(Cr.Cir.Cell, Mc.Img.cells(ds))

def rv.first(+ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>) -> U32:
  Cr.Cir.first(rv.k(ds), U32.add(Cr.Cir.input.at(rv.k(ds)), Cr.Wasm.encode.len(Word(8n), i)))

def rv.x(+ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>) -> Hp.Cx:
  I.Cx.of(ds, rv.k(ds), rv.first(ds, i))

def rv.vb(+st: Cr.Cir.State) -> Bool:
  Hp.Fl(Lg.St.cells(st), Hp.V.reg(st, Mc.R.focus()), Mc.F.value())

def rv.halt(+c: U32, +c2: U32, +st2: Cr.Cir.State, +out: List<&2, Word(8n)>, +k: Nat) -> RV:
  RV{U32.is_eq(c, c2) && (Bool.not(U32.is_zero(c)) || Sd.Name.is_eq(List.reverse(&2, Word(8n), Lg.St.out(st2)), out)), k,
    Some{A.AO.halt{c, List.reverse(&2, Word(8n), Lg.St.out(st2))}}}

def rv.step(ok: Bool, o: Cr.Cir.Out, e: A.AO, +k: Nat, rec: Cr.Cir.State -> A.AS -> RV) -> RV:
  match ok o e:
    case True{} Cr.Cir.Out.next{st2} A.AO.next{s2}:
      rec(st2, s2)
    case True{} Cr.Cir.Out.halt{c, st2} A.AO.halt{c2, out}:
      rv.halt(c, c2, st2, out, k)
    case _ _ _:
      RV{False{}, k, None{}}

# the checks of a round from st, which should hold s
def rv.chk(+x: Hp.Cx, +st: Cr.Cir.State, +s: A.AS) -> Bool:
  R.Inv(x, st, s) && A.AS.ok(Hp.Cx.ds(x), rv.vb(st), s) && A.AO.ok(Hp.Cx.ds(x), s, A.AM.move(Hp.Cx.ds(x), rv.vb(st), s))

def rv.round(n: Nat, +x: Hp.Cx, +st: Cr.Cir.State, +s: A.AS, +k: Nat) -> RV:
  match n:
    case 0n:
      RV{True{}, k, None{}}
    case 1n+j:
      rv.step(rv.chk(x, st, s), Cr.Cir.exec(4000n, Mc.Mach.round(), st), A.AM.move(Hp.Cx.ds(x), rv.vb(st), s), k,
        st2 => s2 => rv.round(j, x, st2, s2, 1n+k))

def rv.or(r: Maybe<&2, U32>) -> U32:
  match r:
    case Some{v}:
      v
    case None{}:
      0

def rv.pg(+ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>) -> U32:
  rv.or(Cr.Cir.alloc.pages(rv.k(ds), Cr.Wasm.encode.len(Word(8n), i), Cr.Cir.pages(Cr.Cir.input.at(rv.k(ds))), 100))

def rv.st0(+ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>) -> Cr.Cir.State:
  I.St0(Mc.Mach.regs(), Mc.Img.cells(ds), rv.first(ds, i), rv.k(ds), rv.pg(ds, i), 100, i)

def rv.started(o: Cr.Cir.Out, n: Nat, +x: Hp.Cx, +i: List<&2, Word(8n)>) -> RV:
  match o:
    case Cr.Cir.Out.next{st}:
      rv.round(n, x, R.Mode0(st), A.AS{False{}, Pg.Program.start(i), []}, 0n)
    case _:
      RV{False{}, 0n, None{}}

def rv.run(n: Nat, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>) -> RV:
  rv.started(Cr.Cir.exec(4000n, Mc.M.input(), rv.st0(ds, i)), n, rv.x(ds, i), i)

def rv.ok(r: RV) -> Maybe<&2, A.AO>:
  match r:
    case RV{True{}, _, e}:
      e
    case RV{False{}, _, _}:
      None{}

def rv.h0(bs: List<&2, Word(8n)>) -> Maybe<&2, A.AO>:
  Some{A.AO.halt{0, bs}}

def rv.h2() -> Maybe<&2, A.AO>:
  Some{A.AO.halt{2, []}}

# 1. main = λx. Rwt (Lab Q0) Efq x: a Rwt whose proof is a value but not Rfl
def rv.rwt() -> List<&2, Bk.Def>:
  rv.mainof(rv.lam(Bk.Term.Rwt{rv.lab(El.Quan.name(Bk.Quan.Q0{})), Bk.Term.Efq{}, rv.V(0n)}))

def rv.t.rwt() -> {rv.ok(rv.run(400n, rv.rwt(), [])) == rv.h2() : Maybe<&2, A.AO>}:
  {==}

# 2. main = λx. (λy. y) ((λ-match Nil: Efq; else λl. x) Con): a λ-match of
# labels that misses, by a redex, under a frame
def rv.matmiss() -> List<&2, Bk.Def>:
  rv.mainof(rv.lam(rv.app(rv.lam(rv.V(0n)),
    rv.app(Bk.Term.Mat{Pg.Program.name.nil(), Bk.Term.Efq{}, rv.lam(rv.V(1n))}, rv.lab(Pg.Program.name.con())))))

def rv.t.matmiss() -> {rv.ok(rv.run(400n, rv.matmiss(), [rv.b(5)])) == rv.h0([rv.b(5)]) : Maybe<&2, A.AO>}:
  {==}

# 3. main = λx. (λ2 y. y) (λz. z): a Q2 bind of a term that is no Data
def rv.q2bad() -> List<&2, Bk.Def>:
  rv.mainof(rv.lam(Bk.Term.App{Bk.Quan.Q2{}, Bk.Term.Lam{Bk.Quan.Q2{}, rv.V(0n)}, rv.lam(rv.V(0n))}))

def rv.t.q2bad() -> {rv.ok(rv.run(400n, rv.q2bad(), [])) == rv.h2() : Maybe<&2, A.AO>}:
  {==}

# 3b. main = λx. (λ2 y. y) x: a Q2 bind of Data
def rv.q2ok() -> List<&2, Bk.Def>:
  rv.mainof(rv.lam(Bk.Term.App{Bk.Quan.Q2{}, Bk.Term.Lam{Bk.Quan.Q2{}, rv.V(0n)}, rv.V(0n)}))

def rv.t.q2ok() -> {rv.ok(rv.run(400n, rv.q2ok(), [rv.b(5)])) == rv.h0([rv.b(5)]) : Maybe<&2, A.AO>}:
  {==}

# 4. main = λx. (λ-match of pairs: λa. λb. b) Nil-label: Prj on no pair, by a
# redex
def rv.prjbad() -> List<&2, Bk.Def>:
  rv.mainof(rv.lam(rv.app(Bk.Term.Prj{rv.lam(rv.lam(rv.V(0n)))}, rv.lab(Pg.Program.name.nil()))))

def rv.t.prjbad() -> {rv.ok(rv.run(400n, rv.prjbad(), [])) == rv.h2() : Maybe<&2, A.AO>}:
  {==}

# 4b. f = λ-match of pairs: λa. λb. b; main = λx. f Nil-label: Prj on no
# pair, in a walk
def rv.prjwalk() -> List<&2, Bk.Def>:
  [rv.def(Pg.Program.name.main(), rv.lam(rv.app(Bk.Term.Ref{rv.nm(102)}, rv.lab(Pg.Program.name.nil())))),
    rv.def(rv.nm(102), Bk.Term.Prj{rv.lam(rv.lam(rv.V(0n)))})]

def rv.t.prjwalk() -> {rv.ok(rv.run(400n, rv.prjwalk(), [])) == rv.h2() : Maybe<&2, A.AO>}:
  {==}

# 4c. main = λx. (λ-match of pairs: λa. λb. b) at Q0 on x: a dead Prj redex
def rv.prjdead() -> List<&2, Bk.Def>:
  rv.mainof(rv.lam(Bk.Term.App{Bk.Quan.Q0{}, Bk.Term.Prj{rv.lam(rv.lam(rv.V(0n)))}, rv.V(0n)}))

def rv.t.prjdead() -> {rv.ok(rv.run(400n, rv.prjdead(), [rv.b(5)])) == rv.h2() : Maybe<&2, A.AO>}:
  {==}

# 5. main = λx. (λ-match Nil: x; else Efq) at Q0 on Nil-label: a dead Mat
# redex
def rv.matdead() -> List<&2, Bk.Def>:
  rv.mainof(rv.lam(Bk.Term.App{Bk.Quan.Q0{}, Bk.Term.Mat{Pg.Program.name.nil(), rv.V(0n), Bk.Term.Efq{}},
    rv.lab(Pg.Program.name.nil())}))

def rv.t.matdead() -> {rv.ok(rv.run(400n, rv.matdead(), [])) == rv.h2() : Maybe<&2, A.AO>}:
  {==}

# 6. f = λa. λb. b; main = λx. (f x) x via a Tup frame: a partial call
# (waits), a value spine, then the full call
def rv.partial() -> List<&2, Bk.Def>:
  [rv.def(Pg.Program.name.main(), rv.lam(Bk.Term.Tup{Bk.Quan.Q1{}, rv.app(Bk.Term.Ref{rv.nm(102)}, rv.V(0n)),
     rv.app(rv.app(Bk.Term.Ref{rv.nm(102)}, rv.V(0n)), rv.V(0n))})),
    rv.def(rv.nm(102), rv.lam(rv.lam(rv.V(0n))))]

def rv.t.partial() -> {rv.ok(rv.run(800n, rv.partial(), [rv.b(5)])) == rv.h2() : Maybe<&2, A.AO>}:
  {==}

# negative control: the wrong halt must fail
def rv.t.neg() -> {rv.ok(rv.run(400n, rv.rwt(), [])) == rv.h0([]) : Maybe<&2, A.AO>}:
  {==}
