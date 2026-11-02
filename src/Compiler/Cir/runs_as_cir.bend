# Compiler/Cir: layer A of the proofs of the laws (Compiler/proof.bend)
# =====================================================================
#
#   A (translation): the module that Cir.module makes of the machine runs in
#     the Bend version of WASM as Cir.exec says (Cir.result), for any image of
#     fewer than 2^26 cells, when Cir.exec never traps, on an engine that
#     grants each grow within its pages; on any other engine, it gives the
#     same or runs out of memory; and a module whose program halts at once
#     gives no result.
#
# A lemma whose body is ?TODO is still open: the laws hold once each is
# proven.

import Base
import ../../Wasm/impl.bend as Wa
import ./impl.bend as Cr
import ../Machine/impl.bend as Mc
import ../impl.bend as C
import ./halt.bend as PH

# A: a result of the machine's module, on any engine, is one that Cir gives
# with the engine's pages: a grow that the engine refuses makes the module
# run out of memory, so it gives no result
def mach_wasm.sound(
  +f: Nat, +cells: List<&2, Cr.Cir.Cell>, +i: List<&2, Word(8n)>, +m: U32, +gs: List<&2, Bool>, +o: List<&2, Word(8n)>,
  small: {Nat.is_lt(List.length(&2, Cr.Cir.Cell, cells), U32.to_nat(67108864)) == True{} : Bool},
  safe: @n:Nat -> {Cr.Cir.result(n, Mc.Mach.code(), Mc.Mach.regs(), cells, i, m) != Wa.Wasm.Outcome.trap{} : Wa.Wasm.Outcome},
  e: {Wa.Wasm.run(f, C.Compiler.module(cells), i, Wa.Wasm.Engine{m, gs}) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome}
) -> &n:Nat -> {Cr.Cir.result(n, Mc.Mach.code(), Mc.Mach.regs(), cells, i, m) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome}:
  ?TODO

# A: a result that Cir gives is one of the machine's module, or the module
# runs out of memory, on any engine with the same pages
def mach_wasm.result(
  +n: Nat, +cells: List<&2, Cr.Cir.Cell>, +i: List<&2, Word(8n)>, +m: U32, +gs: List<&2, Bool>, +o: List<&2, Word(8n)>,
  small: {Nat.is_lt(List.length(&2, Cr.Cir.Cell, cells), U32.to_nat(67108864)) == True{} : Bool},
  e: {Cr.Cir.result(n, Mc.Mach.code(), Mc.Mach.regs(), cells, i, m) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome}
) -> &f:Nat -> Or({Wa.Wasm.run(f, C.Compiler.module(cells), i, Wa.Wasm.Engine{m, gs}) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome},
  {Wa.Wasm.run(f, C.Compiler.module(cells), i, Wa.Wasm.Engine{m, gs}) == Wa.Wasm.Outcome.out_of_memory{} : Wa.Wasm.Outcome}):
  ?TODO

# A: a result that Cir gives is one of the machine's module, on an engine
# that grants each grow within the pages
def mach_wasm.result.all(
  +n: Nat, +cells: List<&2, Cr.Cir.Cell>, +i: List<&2, Word(8n)>, +m: U32, +o: List<&2, Word(8n)>,
  small: {Nat.is_lt(List.length(&2, Cr.Cir.Cell, cells), U32.to_nat(67108864)) == True{} : Bool},
  e: {Cr.Cir.result(n, Mc.Mach.code(), Mc.Mach.regs(), cells, i, m) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome}
) -> &f:Nat -> {Wa.Wasm.run(f, C.Compiler.module(cells), i, Wa.Wasm.Engine{m, []}) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome}:
  ?TODO

# A: when Cir runs out of memory, so does the machine's module, on any
# engine with the same pages
def mach_wasm.oom(
  +n: Nat, +cells: List<&2, Cr.Cir.Cell>, +i: List<&2, Word(8n)>, +m: U32, +gs: List<&2, Bool>,
  small: {Nat.is_lt(List.length(&2, Cr.Cir.Cell, cells), U32.to_nat(67108864)) == True{} : Bool},
  e: {Cr.Cir.result(n, Mc.Mach.code(), Mc.Mach.regs(), cells, i, m) == Wa.Wasm.Outcome.out_of_memory{} : Wa.Wasm.Outcome}
) -> &f:Nat -> {Wa.Wasm.run(f, C.Compiler.module(cells), i, Wa.Wasm.Engine{m, gs}) == Wa.Wasm.Outcome.out_of_memory{} : Wa.Wasm.Outcome}:
  ?TODO

# A: a module that halts at once with a status other than 0 gives no result,
# on any engine
def halt.no_result(
  +f: Nat, +s: U32, +i: List<&2, Word(8n)>, +eng: Wa.Wasm.Engine, +o: List<&2, Word(8n)>,
  ns: {U32.is_eq(s, 0) == False{} : Bool},
  e: {Wa.Wasm.run(f, C.Compiler.halt(s), i, eng) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome}
) -> Empty:
  PH.halt.no_result.proof(f, s, i, eng, o, ns, e)

# A: a module that halts at once with the status 1 runs out of memory, on
# any engine
def halt.oom(+i: List<&2, Word(8n)>, +eng: Wa.Wasm.Engine) ->
  &f:Nat -> {Wa.Wasm.run(f, C.Compiler.halt(1), i, eng) == Wa.Wasm.Outcome.out_of_memory{} : Wa.Wasm.Outcome}:
  PH.halt.oom.proof(i, eng)
