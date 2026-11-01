# compiler: the laws of AGENTS.md 3.7.4
# =====================================
#
# They hold for every program, not only for the ones that the kernel accepts
# (AGENTS.md 3.4.1): Wasm.run is the Bend version of WASM's meaning (3.8.1.2),
# Program.gives what a program gives by the Bend version of Eval (3.4.2 and
# 3.4.3), and Program.need the memory F that 3.8.1.4 grants it (3.4.4).

import Base
import ../wasm/impl.bend as Wa
import ../program/impl.bend as Pg
import ./impl.bend as C

# LAW (AGENTS.md 3.4.1), no wrong result: a result that the compiled program
# gives is the one that Eval gives
law no_wrong_result:
  for +f: Nat
  for +p: List<&2, Word(8n)>
  for +i: List<&2, Word(8n)>
  for +m: U32
  for +o: List<&2, Word(8n)>
  for e: {Wa.Wasm.run(f, C.Compiler.compile(p), i, m) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome}
  exs n: Nat
  {Pg.Program.gives(p, i, n) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}

# LAW (AGENTS.md 3.4.1), no other failure: when Eval gives a result, the compiled
# program gives it, or runs out of memory
law no_other_failure:
  for +p: List<&2, Word(8n)>
  for +i: List<&2, Word(8n)>
  for +n: Nat
  for +o: List<&2, Word(8n)>
  for +m: U32
  for e: {Pg.Program.gives(p, i, n) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}
  exs f: Nat
  {Wa.Wasm.run(f, C.Compiler.compile(p), i, m) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome} |
    {Wa.Wasm.run(f, C.Compiler.compile(p), i, m) == Wa.Wasm.Outcome.out_of_memory{} : Wa.Wasm.Outcome}

# LAW (AGENTS.md 3.4.1 and 3.4.4), enough memory: with the memory that
# Program.need asks, the compiled program gives the result that Eval gives
law enough_memory:
  for +p: List<&2, Word(8n)>
  for +i: List<&2, Word(8n)>
  for +n: Nat
  for +o: List<&2, Word(8n)>
  for +m: U32
  for e: {Pg.Program.gives(p, i, n) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}
  for big: {Nat.is_le(Pg.Program.need(p, i, n), Pg.Program.memory(m)) == True{} : Bool}
  exs f: Nat
  {Wa.Wasm.run(f, C.Compiler.compile(p), i, m) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome}
