# compiler: smoke checks of moves/spec.bend and memory/spec.bend (P2, lane S4)
# ============================================================================
#
# Test c (bend2 kinds): computed checks, by {==}, that the move and memory
# statements hold on real runs of Mach.code from St0, round by round: each
# state holds its abstract state (Inv) and what am.ok asks of it (AS.ok, with
# the focus' VALUE flag: inv.vb); each round's outcome is what round.sim says
# of AM.move's outcome (Next.is, Halt.is; out of memory only below Budget);
# the move is right (am.ok); a round that goes on keeps next - first within
# Need and makes no STATIC cell (round.mem); a halt 0 fits (code.fits). The
# cases are those that S2's smoke did not run: a Rwt whose proof is no Rfl, a
# Mat miss by a redex inside a frame, a Q2 bind of no Data (a redex, a Let),
# Prj on no pair, and runs at the edge of a one-page memory (M.input's and a
# round's alloc there). The laws round.sim, round.mem, inv.vb, am.ok and
# code.fits replace them; outside main's closure; P5 deletes it.

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
import ./memory/spec.bend as Me
import ./moves/spec.bend as Mv

# a run's check: each round held (full: with Inv), the rounds done, the halt
# (status, bytes in order), or out of memory below the budget
type SR4 is Data:
  SR4{ok: Bool, n: Nat, end: Maybe<&2, A.AO>, oom: Bool}

# a run's result, but its round count
type SR4Out is Data:
  SR4Out{ok: Bool, end: Maybe<&2, A.AO>, oom: Bool}

# what round.sim, round.mem and code.fits say of a round's outcome o from st
# of s, with mv = AM.move's outcome
def smk4.out(+x: Hp.Cx, +st: Cr.Cir.State, +s: A.AS, +mv: A.AO, o: Cr.Cir.Out) -> Bool:
  match o:
    case Cr.Cir.Out.next{+st2}:
      Mv.Next.is(x, mv, st2) && Nat.is_le(Me.Stat(st2), Me.Stat(st)) &&
        Nat.is_le(Me.Mem.cells(st2), Nat.max(Me.Mem.cells(st), Me.Need(Hp.Cx.ds(x), st, s)))
    case Cr.Cir.Out.halt{+c, +st2}:
      Mv.Halt.is(mv, c, st2) && Me.Fits.halt(Cr.Cir.Out.halt{c, st2})
    case Cr.Cir.Out.out_of_memory{}:
      Nat.is_lt(Lg.Lim(st), Me.Budget(x, st, s))
    case _:
      False{}

def smk4.inv(full: Bool, +x: Hp.Cx, +st: Cr.Cir.State, +s: A.AS) -> Bool:
  match full:
    case True{}:
      R.Inv(x, st, s)
    case False{}:
      True{}

# the checks of one round
def smk4.check(+full: Bool, +x: Hp.Cx, +st: Cr.Cir.State, +s: A.AS, o: Cr.Cir.Out) -> Bool:
  +mv = A.AM.move(Hp.Cx.ds(x), Mv.Vb(st), s)
  smk4.inv(full, x, st, s) && A.AS.ok(Hp.Cx.ds(x), Mv.Vb(st), s) && A.AO.ok(Hp.Cx.ds(x), s, mv) && smk4.out(x, st, s, mv, o)

def smk4.step(ok: Bool, o: Cr.Cir.Out, e: A.AO, +k: Nat, rec: Cr.Cir.State -> A.AS -> SR4) -> SR4:
  match ok o e:
    case True{} Cr.Cir.Out.next{st2} A.AO.next{s2}:
      rec(st2, s2)
    case True{} Cr.Cir.Out.halt{c, st2} A.AO.halt{_, _}:
      SR4{True{}, k, Some{A.AO.halt{c, List.reverse(&2, Word(8n), Lg.St.out(st2))}}, False{}}
    case True{} Cr.Cir.Out.out_of_memory{} _:
      SR4{True{}, k, None{}, True{}}
    case _ _ _:
      SR4{False{}, k, None{}, False{}}

# at most n rounds from st, which should hold s
def smk4.round(n: Nat, +full: Bool, +x: Hp.Cx, +st: Cr.Cir.State, +s: A.AS, +k: Nat) -> SR4:
  match n:
    case 0n:
      SR4{True{}, k, None{}, False{}}
    case 1n+j:
      smk4.step(smk4.check(full, x, st, s, Cr.Cir.exec(4000n, Mc.Mach.round(), st)), Cr.Cir.exec(4000n, Mc.Mach.round(), st),
        A.AM.move(Hp.Cx.ds(x), Mv.Vb(st), s), k, st2 => s2 => smk4.round(j, full, x, st2, s2, 1n+k))

def smk4.or(r: Maybe<&2, U32>) -> U32:
  match r:
    case Some{v}:
      v
    case None{}:
      0

def smk4.k(+ds: List<&2, Bk.Def>) -> U32:
  Cr.Wasm.encode.len(Cr.Cir.Cell, Mc.Img.cells(ds))

def smk4.first(+ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>) -> U32:
  Cr.Cir.first(smk4.k(ds), U32.add(Cr.Cir.input.at(smk4.k(ds)), Cr.Wasm.encode.len(Word(8n), i)))

def smk4.x(+ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>) -> Hp.Cx:
  I.Cx.of(ds, smk4.k(ds), smk4.first(ds, i))

# Cir.result's start of ds on i with at most lim pages
def smk4.st0(+ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +lim: U32) -> Cr.Cir.State:
  I.St0(Mc.Mach.regs(), Mc.Img.cells(ds), smk4.first(ds, i), smk4.k(ds),
    smk4.or(Cr.Cir.alloc.pages(smk4.k(ds), Cr.Wasm.encode.len(Word(8n), i), Cr.Cir.pages(Cr.Cir.input.at(smk4.k(ds))), lim)), lim, i)

# after M.input: the rounds; out of memory only below its budget
def smk4.started(o: Cr.Cir.Out, n: Nat, +full: Bool, +x: Hp.Cx, +i: List<&2, Word(8n)>, +st0: Cr.Cir.State) -> SR4:
  match o:
    case Cr.Cir.Out.next{st}:
      smk4.round(n, full, x, R.Mode0(st), A.AS{False{}, Pg.Program.start(i), []}, 0n)
    case Cr.Cir.Out.out_of_memory{}:
      SR4{Nat.is_lt(Lg.Lim(st0), R.Input.budget(Hp.Cx.fi(x), i)), 0n, None{}, True{}}
    case _:
      SR4{False{}, 0n, None{}, False{}}

# n rounds of Mach.code on ds and i with lim pages, after M.input
def smk4.run(n: Nat, +full: Bool, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +lim: U32) -> SR4:
  smk4.started(Cr.Cir.exec(4000n, Mc.M.input(), smk4.st0(ds, i, lim)), n, full, smk4.x(ds, i), i, smk4.st0(ds, i, lim))

def smk4.nm(c: U32) -> List<&2, Word(8n)>:
  [Sd.Byte.from_u32(c)]

def smk4.b(n: U32) -> Word(8n):
  Sd.Byte.from_u32(n)

def smk4.V(i: Nat) -> Bk.Term:
  Bk.Term.Var{i}

def smk4.lam(f: Bk.Term) -> Bk.Term:
  Bk.Term.Lam{Bk.Quan.Q1{}, f}

def smk4.mainof(v: Bk.Term) -> List<&2, Bk.Def>:
  [Bk.Def{Pg.Program.name.main(), Bk.Term.Efq{}, v, False{}}]

def smk4.h0(bs: List<&2, Word(8n)>) -> SR4Out:
  SR4Out{True{}, Some{A.AO.halt{0, bs}}, False{}}

def smk4.h2() -> SR4Out:
  SR4Out{True{}, Some{A.AO.halt{2, []}}, False{}}

def smk4.res(r: SR4) -> SR4Out:
  match r:
    case SR4{ok, _, e, m}:
      SR4Out{ok, e, m}

# The cases
# ---------

# main = λx. rwt (Lab a) P x: the proof is no Rfl, halt 2
def smk4.rwt() -> List<&2, Bk.Def>:
  smk4.mainof(smk4.lam(Bk.Term.Rwt{Bk.Term.Lab{smk4.nm(97)}, Bk.Term.Typ{smk4.V(0n)}, smk4.V(0n)}))

def smk4.run.rwt() -> {smk4.res(smk4.run(200n, True{}, smk4.rwt(), [], 100)) == smk4.h2() : SR4Out}:
  {==}

# main = λx. let1 v = (λ-match of labels a: Nil; else λl. Nil) (Lab b); v: the
# match misses by a redex, in the frame of the Let; halt 0 with no bytes
def smk4.miss() -> List<&2, Bk.Def>:
  smk4.mainof(smk4.lam(Bk.Term.Let{Bk.Quan.Q1{},
    Bk.Term.App{Bk.Quan.Q1{}, Bk.Term.Mat{smk4.nm(97), Pg.Program.bytes([]), smk4.lam(Pg.Program.bytes([]))}, Bk.Term.Lab{smk4.nm(98)}},
    smk4.V(0n)}))

def smk4.run.miss() -> {smk4.res(smk4.run(400n, True{}, smk4.miss(), [], 100)) == smk4.h0([]) : SR4Out}:
  {==}

# main = λx. (λ2 y. y) (λz. z): a Q2 bind of no Data, halt 2
def smk4.q2() -> List<&2, Bk.Def>:
  smk4.mainof(smk4.lam(Bk.Term.App{Bk.Quan.Q2{}, Bk.Term.Lam{Bk.Quan.Q2{}, smk4.V(0n)}, smk4.lam(smk4.V(0n))}))

def smk4.run.q2() -> {smk4.res(smk4.run(200n, True{}, smk4.q2(), [], 100)) == smk4.h2() : SR4Out}:
  {==}

# main = λx. let2 y = λz. z; y: a Let of Q2 of no Data, halt 2
def smk4.q2let() -> List<&2, Bk.Def>:
  smk4.mainof(smk4.lam(Bk.Term.Let{Bk.Quan.Q2{}, smk4.lam(smk4.V(0n)), smk4.V(0n)}))

def smk4.run.q2let() -> {smk4.res(smk4.run(200n, True{}, smk4.q2let(), [], 100)) == smk4.h2() : SR4Out}:
  {==}

# main = λx. (λ-match of pairs λa. λb. a) (Lab c): Prj on no pair, halt 2
def smk4.prj() -> List<&2, Bk.Def>:
  smk4.mainof(smk4.lam(Bk.Term.App{Bk.Quan.Q1{}, Bk.Term.Prj{smk4.lam(smk4.lam(smk4.V(1n)))}, Bk.Term.Lab{smk4.nm(99)}}))

def smk4.run.prj() -> {smk4.res(smk4.run(200n, True{}, smk4.prj(), [], 100)) == smk4.h2() : SR4Out}:
  {==}

# a negative control: a run checked against the wrong book's moves fails
def smk4.run.neg() -> {smk4.res(smk4.started(Cr.Cir.exec(4000n, Mc.M.input(), smk4.st0(smk4.rwt(), [], 100)), 200n, True{},
  smk4.x(smk4.prj(), []), [], smk4.st0(smk4.rwt(), [], 100))) == SR4Out{False{}, None{}, False{}} : SR4Out}:
  {==}

# Runs at the edge of a one-page memory
# -------------------------------------

# T(n): n pairs nested on the variable 0, each with it first
def smk4.T(n: Nat) -> Bk.Term:
  match n:
    case 0n:
      smk4.V(0n)
    case 1n+k:
      Bk.Term.Tup{Bk.Quan.Q1{}, smk4.V(0n), smk4.T(k)}

# main = λx. main (f x); f = λy. T(250): each call copies 250 pairs that
# hold the last ones, so the live cells grow until a one-page memory is full
def smk4.grow() -> List<&2, Bk.Def>:
  [Bk.Def{Pg.Program.name.main(), Bk.Term.Efq{}, smk4.lam(Bk.Term.App{Bk.Quan.Q1{}, Bk.Term.Ref{Pg.Program.name.main()},
     Bk.Term.App{Bk.Quan.Q1{}, Bk.Term.Ref{smk4.nm(102)}, smk4.V(0n)}}), False{}},
   Bk.Def{smk4.nm(102), Bk.Term.Efq{}, smk4.lam(smk4.T(250n)), False{}}]

# every round holds (round.sim's outcome, round.mem, am.ok) up to a round that
# runs out of memory, and only below its Budget
def smk4.run.edge() -> {smk4.res(smk4.run(400n, False{}, smk4.grow(), [], 1)) == SR4Out{True{}, None{}, True{}} : SR4Out}:
  {==}

# Call.frames is M.call's second loop, word for word: M.call with it in its
# place is M.call (by computation)
def smk4.call(partial: Cr.Cir.Stmt, done: Cr.Cir.Stmt) -> Cr.Cir.Stmt:
  Mc.M.do([
    Mc.M.walk(),
    Mc.M.if(Mc.M.eq(Mc.M.g(Mc.R.wres()), Mc.M.c(1)), Mc.M.do([
      Mc.M.set(Mc.R.cenv(), Mc.M.g(Mc.R.wenv())),
      Mc.M.set(Mc.R.clen(), Mc.M.g(Mc.R.wn())),
      Mc.M.copy(Mc.R.n(), Mc.R.wt()),
      Mc.M.set(Mc.R.wh(), Mc.M.c(0)),
      Mc.M.while(Mc.M.ne(Mc.M.g(Mc.R.wargs()), Mc.M.c(0)), Mc.M.do([
        Mc.M.set(Mc.R.wa(), Mc.M.g(Mc.R.wargs())),
        Mc.M.set(Mc.R.wargs(), Mc.M.f(1n, Mc.M.g(Mc.R.wa()))),
        Mc.M.st(1n, Mc.M.g(Mc.R.wa()), Mc.M.g(Mc.R.wh())),
        Mc.M.set(Mc.R.wh(), Mc.M.g(Mc.R.wa()))])),
      Mv.Call.frames(),
      Mc.M.release.all(Mc.R.wenv()),
      done,
      Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())),
      Mc.M.set(Mc.R.mode(), Mc.M.c(0))]),
    Mc.M.if(Mc.M.eq(Mc.M.g(Mc.R.wres()), Mc.M.c(2)), Mc.M.do([
      Mc.M.release.all(Mc.R.wargs()),
      Mc.M.release.all(Mc.R.wenv()),
      partial]),
      Mc.M.halt(2)))])

def smk4.call.eq(+p: Cr.Cir.Stmt, +d: Cr.Cir.Stmt) -> {Mc.M.call(p, d) == smk4.call(p, d) : Cr.Cir.Stmt}:
  {==}
