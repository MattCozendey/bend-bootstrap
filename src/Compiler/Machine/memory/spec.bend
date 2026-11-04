# compiler: layer B8, the memory of a run
# =======================================
#
# What mach.memory (moves.bend) needs to show that a run with the memory F of
# AGENTS.md 3.9.1.4 (Program.need) never runs out of it, and what mach.safe
# needs to show that a halt 0 never traps.
#
# A round of the main loop runs out of memory only below its budget
# (Budget: moves/spec.bend's round.sim): the cells up to first + Need, where
# Need bounds the live cells at every point of the round (the STATIC own
# cells, the cache, which no round makes; three times the larger of the
# term and of its step: the old term, the new one and the spine's argument
# cells; three cells a node of the largest def body, for a walk; 16 for the
# roots and frames of a move); and the output after next, at most the term's
# nodes. A new cell is taken only when the free list is empty, so next - first
# never passes the most cells that were ever live: round.mem says that a round
# keeps next - first within Need and makes no STATIC cell. Over the run, with
# S the largest term of the run (Program.largest) and C <= 6144 the cache's
# cells, each round's Need is at most Peak(C, S) (need.peak), and each
# round's Budget is at most F (budget.need); M.input's budget too
# (input.need), and the start's limit has F bytes (need.lim). The arithmetic
# is that of memory_bound.bend at 4ebef88, with 3 S where it had 2 S (the
# spine's argument cells), which F still covers since |i| <= S / 72.
#
# code.fits: at a halt 0, the output lies in the memory, as the host checks
# (Cir.ended), by facts of Cir alone (cir_fits.bend at 4ebef88).
#
# eval.stops: a value has no step (Eval's fact that the loop and Need use;
# ev.stops of eval_facts.bend at 4ebef88).

import Base
import ../../../Book/impl.bend as Bk
import ../../../Eval/impl.bend as El
import ../../../Program/impl.bend as Pg
import ../../../Wasm/impl.bend as Wa
import ../../Cir/impl.bend as Cr
import ../impl.bend as Mc
import ../logic/spec.bend as Lg
import ../canon/spec.bend as C
import ../am/spec.bend as A
import ../heap/spec.bend as Hp
import ../image/spec.bend as I
import ../routines/spec.bend as R

# Counts
# ------

# the machine's own cells of a state: from first, before next
def Mem.cells(+st: Cr.Cir.State) -> Nat:
  Nat.sub(U32.to_nat(Lg.St.next(st)), U32.to_nat(Lg.St.first(st)))

# how many of the n cells from c are STATIC
def Stat.go(n: Nat, +m: Cr.Cir.Cells, +c: U32) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+k:
      Nat.add(Bool.pick(Nat, Hp.Fl(m, c, Mc.F.static()), 1n, 0n), Stat.go(k, m, U32.inc(c)))

# the STATIC own cells of a state (the input's cache)
def Stat(+st: Cr.Cir.State) -> Nat:
  Stat.go(Mem.cells(st), Lg.St.cells(st), Lg.St.first(st))

# the nodes of the largest def body
def Defs.big(ds: List<&2, Bk.Def>) -> Nat:
  match ds:
    case Nil{}:
      0n
    case Con{Bk.Def{_, _, v, _}, rest}:
      Nat.max(Pg.Term.size(v), Defs.big(rest))

def StepSize.of(r: Maybe<Bk.Term>) -> Nat:
  match r:
    case Some{u}:
      Pg.Term.size(u)
    case None{}:
      0n

# the nodes of the term that t steps to (canonically), 0 when it has none
def StepSize(+ds: List<&2, Bk.Def>, +t: Bk.Term) -> Nat:
  StepSize.of(C.CStep(ds, t))

# the most own cells that are live during a round from the state st of the
# abstract state s
def Need(+ds: List<&2, Bk.Def>, +st: Cr.Cir.State, +s: A.AS) -> Nat:
  +t = A.AS.term(s)
  Nat.add(Stat(st), Nat.add(16n, Nat.add(Nat.mul(3n, Nat.max(Pg.Term.size(t), StepSize(ds, t))), Nat.mul(3n, Defs.big(ds)))))

# the bytes that a round from st of s may need: the cells up to first + Need,
# then the output (at most the term's nodes), which lies after next
def Budget(+x: Hp.Cx, +st: Cr.Cir.State, +s: A.AS) -> Nat:
  +n = Pg.Term.size(A.AS.term(s))
  Nat.max(Nat.add(I.Cells.bytes(Hp.Cx.fi(x), Need(Hp.Cx.ds(x), st, s)), n), Nat.add(Nat.mul(20n, U32.to_nat(Lg.St.next(st))), n))

# the most own cells of a round of a run whose STATIC own cells are at most C
# and whose terms (and their steps) have at most S nodes
def Peak(+ds: List<&2, Bk.Def>, +C: Nat, +S: Nat) -> Nat:
  Nat.add(C, Nat.add(16n, Nat.add(Nat.mul(3n, S), Nat.mul(3n, Defs.big(ds)))))

# Cir.result's checks before the program, past the first: the alloc of the
# input's len bytes gives pages
def Start.pg(r: Maybe<&2, U32>) -> Bool:
  match r:
    case Some{_}:
      True{}
    case None{}:
      False{}

def Start.len(r: Maybe<&2, U32>, +k: U32, +p: U32, +lim: U32) -> Bool:
  match r:
    case Some{+len}:
      Start.pg(Cr.Cir.alloc.pages(k, len, p, lim))
    case None{}:
      False{}

# Cir.result finds room for the image's cells and the input in m pages: it
# runs the program, not out of memory before it
def Start.ok(+cells: List<&2, Cr.Cir.Cell>, +i: List<&2, Word(8n)>, +m: U32) -> Bool:
  +k = Cr.Wasm.encode.len(Cr.Cir.Cell, cells)
  +p = Cr.Cir.pages(Cr.Cir.input.at(k))
  U32.is_le(p, m) && Start.len(Wa.Wasm.length32(i), k, p, Wa.Wasm.min(m, 65536))

# a halt 0 of the outcome o has its output in the memory, as the host checks
def Fits.halt(o: Cr.Cir.Out) -> Bool:
  match o:
    case Cr.Cir.Out.halt{s, Cr.Cir.State{_, _, nx, _, _, pg, _, _, _, on}}:
      Bool.not(U32.is_eq(s, 0)) || Wa.Wasm.fits(pg, Cr.Cir.at(nx), on)
    case _:
      True{}

# Laws
# ----

# LAW: a value has no step
law eval.stops:
  for +ds: List<&2, Bk.Def>
  for +t: Bk.Term
  for +h: {El.Eval.vals(ds, t, False{}) == True{} : Bool}
  {El.Eval.step(ds, t) == None{} : Maybe<Bk.Term>}

# LAW: a round that goes on keeps the own cells within the larger of those
# before it and its Need, and makes no STATIC cell
law round.mem:
  for +x: Hp.Cx
  for +st: Cr.Cir.State
  for +s: A.AS
  for +iv: {R.Inv(x, st, s) == True{} : Bool}
  for +f: Nat
  for +st2: Cr.Cir.State
  for +e: {Cr.Cir.exec(f, Mc.Mach.round(), st) == Cr.Cir.Out.next{st2} : Cr.Cir.Out}
  {Nat.is_le(Stat(st2), Stat(st)) && Nat.is_le(Mem.cells(st2), Nat.max(Mem.cells(st), Need(Hp.Cx.ds(x), st, s))) == True{} : Bool}

# LAW: after M.input, from Cir.result's start, the cache has at most 6144
# cells, and the own cells are at most Peak, for every run of the program on
# the input within n steps
law input.mem:
  for +p: List<&2, Word(8n)>
  for +ds: List<&2, Bk.Def>
  for +i: List<&2, Word(8n)>
  for +m: U32
  for +k: U32
  for +len: U32
  for +pg: U32
  for +lim: U32
  for +first: U32
  for +n: Nat
  for +rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>}
  for +small: {Mc.Img.small(p, 0) == True{} : Bool}
  for +s: {I.Start(Mc.Img.cells(ds), i, m, k, len, pg, lim, first) == True{} : Bool}
  for +f: Nat
  for +st: Cr.Cir.State
  for +e: {Cr.Cir.exec(f, Mc.M.input(), I.St0(Mc.Mach.regs(), Mc.Img.cells(ds), first, k, pg, lim, i)) == Cr.Cir.Out.next{st} :
    Cr.Cir.Out}
  {Nat.is_le(Stat(R.Mode0(st)), 6144n) &&
    Nat.is_le(Mem.cells(R.Mode0(st)), Peak(ds, Stat(R.Mode0(st)), Pg.Program.largest(p, i, n))) == True{} : Bool}

# LAW: the Need of a round of the run within n steps that reaches the bytes
# o (its term is the j-th, j <= n), with at most C STATIC own cells, is at
# most Peak
law need.peak:
  for +p: List<&2, Word(8n)>
  for +ds: List<&2, Bk.Def>
  for +i: List<&2, Word(8n)>
  for +n: Nat
  for +j: Nat
  for +o: List<&2, Word(8n)>
  for +C: Nat
  for +st: Cr.Cir.State
  for +s: A.AS
  for +rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>}
  for +he: {Pg.Program.result(ds, El.Eval.steps(n, ds, Pg.Program.start(i))) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}
  for +hj: {Nat.is_le(j, n) == True{} : Bool}
  for +ht: {C.Tm.is(C.CSteps(j, ds, Some{Pg.Program.start(i)}), A.AS.term(s)) == True{} : Bool}
  for +hst: {Nat.is_le(Stat(st), C) == True{} : Bool}
  {Nat.is_le(Need(ds, st, s), Peak(ds, C, Pg.Program.largest(p, i, n))) == True{} : Bool}

# LAW: the Budget of such a round, from a state that Inv finds (in the
# context of Cir.result's start) with at most Peak own cells and at most
# C <= 6144 STATIC ones, is at most F
law budget.need:
  for +p: List<&2, Word(8n)>
  for +ds: List<&2, Bk.Def>
  for +i: List<&2, Word(8n)>
  for +m: U32
  for +k: U32
  for +len: U32
  for +pg: U32
  for +lim: U32
  for +first: U32
  for +n: Nat
  for +j: Nat
  for +o: List<&2, Word(8n)>
  for +C: Nat
  for +st: Cr.Cir.State
  for +s: A.AS
  for +rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>}
  for +hs: {I.Start(Mc.Img.cells(ds), i, m, k, len, pg, lim, first) == True{} : Bool}
  for +he: {Pg.Program.result(ds, El.Eval.steps(n, ds, Pg.Program.start(i))) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}
  for +hj: {Nat.is_le(j, n) == True{} : Bool}
  for +ht: {C.Tm.is(C.CSteps(j, ds, Some{Pg.Program.start(i)}), A.AS.term(s)) == True{} : Bool}
  for +iv: {R.Inv(I.Cx.of(ds, k, first), st, s) == True{} : Bool}
  for +hC: {Nat.is_le(C, 6144n) == True{} : Bool}
  for +hst: {Nat.is_le(Stat(st), C) == True{} : Bool}
  for +hm: {Nat.is_le(Mem.cells(st), Peak(ds, C, Pg.Program.largest(p, i, n))) == True{} : Bool}
  {Nat.is_le(Budget(I.Cx.of(ds, k, first), st, s), Pg.Program.need(p, i, n)) == True{} : Bool}

# LAW: M.input's budget is at most F
law input.need:
  for +p: List<&2, Word(8n)>
  for +ds: List<&2, Bk.Def>
  for +i: List<&2, Word(8n)>
  for +m: U32
  for +k: U32
  for +len: U32
  for +pg: U32
  for +lim: U32
  for +first: U32
  for +n: Nat
  for +rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>}
  for +hs: {I.Start(Mc.Img.cells(ds), i, m, k, len, pg, lim, first) == True{} : Bool}
  {Nat.is_le(R.Input.budget(first, i), Pg.Program.need(p, i, n)) == True{} : Bool}

# LAW: with the memory F (the law's big), the limit of Cir.result's start has
# F bytes
law need.lim:
  for +p: List<&2, Word(8n)>
  for +ds: List<&2, Bk.Def>
  for +i: List<&2, Word(8n)>
  for +m: U32
  for +k: U32
  for +len: U32
  for +pg: U32
  for +lim: U32
  for +first: U32
  for +n: Nat
  for +hs: {I.Start(Mc.Img.cells(ds), i, m, k, len, pg, lim, first) == True{} : Bool}
  for +big: {Nat.is_le(Pg.Program.need(p, i, n), Pg.Program.memory(m)) == True{} : Bool}
  {Nat.is_le(Pg.Program.need(p, i, n), Lg.Lim(I.St0(Mc.Mach.regs(), Mc.Img.cells(ds), first, k, pg, lim, i))) == True{} : Bool}

# LAW: with the memory F, Cir.result finds room for the image and the input
# (memory_bound.bend's start.need at 4ebef88, and the input's length)
law start.ok:
  for +p: List<&2, Word(8n)>
  for +ds: List<&2, Bk.Def>
  for +i: List<&2, Word(8n)>
  for +m: U32
  for +n: Nat
  for +rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>}
  for +big: {Nat.is_le(Pg.Program.need(p, i, n), Pg.Program.memory(m)) == True{} : Bool}
  {Start.ok(Mc.Img.cells(ds), i, m) == True{} : Bool}

# LAW: a run of Mach.code from Cir.result's start that halts with 0 has its
# output in the memory
law code.fits:
  for +n: Nat
  for +cells: List<&2, Cr.Cir.Cell>
  for +first: U32
  for +k: U32
  for +pg: U32
  for +lim: U32
  for +i: List<&2, Word(8n)>
  {Fits.halt(Cr.Cir.exec(n, Mc.Mach.code(), I.St0(Mc.Mach.regs(), cells, first, k, pg, lim, i))) == True{} : Bool}
