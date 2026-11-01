# compiler/machine: layer B of the proofs of the laws (compiler/proof.bend)
# =========================================================================
#
#   B (machine): from the image of a book, Mach.code never traps, and it
#     gives what Eval gives, or runs out of memory; with the memory of
#     AGENTS.md 3.8.1.4, it gives it.
#
# A lemma whose body is ?TODO is still open: the laws hold once each is
# proven.

import Base
import ../../book/impl.bend as Bk
import ../../eval/impl.bend as El
import ../../wasm/impl.bend as Wa
import ../../program/impl.bend as Pg
import ../cir/impl.bend as Cr
import ./impl.bend as Mc

# B: the machine never makes an access that its module could not make the
# same way
def mach.safe(
  +p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +m: U32, +n: Nat,
  rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  small: {Mc.Img.small(p, 0) == True{} : Bool}
) -> {Cr.Cir.result(n, Mc.Mach.code(), Mc.Mach.regs(), Mc.Img.cells(ds), i, m) != Wa.Wasm.Outcome.trap{} : Wa.Wasm.Outcome}:
  ?TODO

# B: a result of the machine is the list of bytes of a value that Eval reaches
def mach.sound(
  +p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +m: U32, +n: Nat, +o: List<&2, Word(8n)>,
  rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  small: {Mc.Img.small(p, 0) == True{} : Bool},
  e: {Cr.Cir.result(n, Mc.Mach.code(), Mc.Mach.regs(), Mc.Img.cells(ds), i, m) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome}
) -> &k:Nat -> {Pg.Program.result(ds, El.Eval.steps(k, ds, Pg.Program.start(i))) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}:
  ?TODO

# B: when Eval reaches a list of bytes, the machine gives it, or runs out of
# memory
def mach.complete(
  +p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +m: U32, +k: Nat, +o: List<&2, Word(8n)>,
  rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  small: {Mc.Img.small(p, 0) == True{} : Bool},
  e: {Pg.Program.result(ds, El.Eval.steps(k, ds, Pg.Program.start(i))) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}
) -> &n:Nat -> Or({Cr.Cir.result(n, Mc.Mach.code(), Mc.Mach.regs(), Mc.Img.cells(ds), i, m) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome},
  {Cr.Cir.result(n, Mc.Mach.code(), Mc.Mach.regs(), Mc.Img.cells(ds), i, m) == Wa.Wasm.Outcome.out_of_memory{} : Wa.Wasm.Outcome}):
  ?TODO

# B: with the memory of AGENTS.md 3.8.1.4, the machine gives the list of bytes
def mach.memory(
  +p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +m: U32, +k: Nat, +o: List<&2, Word(8n)>,
  rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  small: {Mc.Img.small(p, 0) == True{} : Bool},
  e: {Pg.Program.result(ds, El.Eval.steps(k, ds, Pg.Program.start(i))) == Some{o} : Maybe<&2, List<&2, Word(8n)>>},
  big: {Nat.is_le(Pg.Program.need(p, i, k), Pg.Program.memory(m)) == True{} : Bool}
) -> &n:Nat -> {Cr.Cir.result(n, Mc.Mach.code(), Mc.Mach.regs(), Mc.Img.cells(ds), i, m) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome}:
  ?TODO
