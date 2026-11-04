# compiler: the laws of AGENTS.md 3.6.1
# =====================================
#
# They hold for every program, not only for the ones that the kernel accepts
# (AGENTS.md 3.6), and all but enough_memory on every engine (Wasm.Engine:
# what an engine decides that the spec leaves open). Wasm.run is the Bend
# version of WASM's meaning (3.9.1.2), Program.gives what a program gives by
# the Bend version of Eval (3.6.3 and 3.3.3), and Program.need the memory F
# that 3.9.1.4 grants it (3.3.10).

import Base
import ../Wasm/impl.bend as Wa
import ../Program/impl.bend as Pg
import ./impl.bend as C

# LAW (AGENTS.md 3.6.1.1), no wrong result: a result that the compiled program
# gives is the one that Eval gives
law no_wrong_result:
  for +f: Nat
  for +p: List<&2, Word(8n)>
  for +i: List<&2, Word(8n)>
  for +eng: Wa.Wasm.Engine
  for +o: List<&2, Word(8n)>
  for e: {Wa.Wasm.run(f, C.Compiler.compile(p), i, eng) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome}
  exs n: Nat
  {Pg.Program.gives(p, i, n) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}

# LAW (AGENTS.md 3.6.1.2), no other failure: when Eval gives a result, the compiled
# program gives it, or runs out of memory, on an engine of m pages, in one
# fuel f for all answers gs to its grows: so on each engine, also one whose
# answers never end (Wasm.Engine)
law no_other_failure:
  for +p: List<&2, Word(8n)>
  for +i: List<&2, Word(8n)>
  for +n: Nat
  for +o: List<&2, Word(8n)>
  for +m: U32
  for e: {Pg.Program.gives(p, i, n) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}
  exs f: Nat
  for +gs: List<&2, Bool>
  {Wa.Wasm.run(f, C.Compiler.compile(p), i, Wa.Wasm.Engine{m, gs}) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome} |
    {Wa.Wasm.run(f, C.Compiler.compile(p), i, Wa.Wasm.Engine{m, gs}) == Wa.Wasm.Outcome.out_of_memory{} : Wa.Wasm.Outcome}

# LAW (AGENTS.md 3.6.1.3), enough memory: with the memory that
# Program.need asks, on an engine that grants each grow within m pages, the
# compiled program gives the result that Eval gives
law enough_memory:
  for +p: List<&2, Word(8n)>
  for +i: List<&2, Word(8n)>
  for +n: Nat
  for +o: List<&2, Word(8n)>
  for +m: U32
  for e: {Pg.Program.gives(p, i, n) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}
  for big: {Nat.is_le(Pg.Program.need(p, i, n), Pg.Program.memory(m)) == True{} : Bool}
  exs f: Nat
  {Wa.Wasm.run(f, C.Compiler.compile(p), i, Wa.Wasm.Engine{m, []}) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome}

# LAW (AGENTS.md 3.6.1.4), in the subset: the compiled program, on every
# input and engine, is never outside the part of WASM that Wasm.run covers
# (3.9.1.2), which is all that its trust covers (3.9.1.3)
law in_subset:
  for +f: Nat
  for +p: List<&2, Word(8n)>
  for +i: List<&2, Word(8n)>
  for +eng: Wa.Wasm.Engine
  {Wa.Wasm.run(f, C.Compiler.compile(p), i, eng) != Wa.Wasm.Outcome.unsupported{} : Wa.Wasm.Outcome}
