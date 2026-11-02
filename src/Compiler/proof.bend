# compiler: the proofs of the laws of AGENTS.md 3.6.1
# ====================================================
#
# The laws of spec.bend follow from two layers, each a set of lemmas in its
# own file (A in Cir/runs_as_cir.bend, B in Machine/runs_as_eval.bend):
#
#   A (translation): the module that Cir.module makes of the machine runs in
#     the Bend version of WASM as Cir.exec says (Cir.result), for any image of
#     fewer than 2^26 cells, when Cir.exec never traps, on an engine that
#     grants each grow within its pages and takes the module; on any other
#     engine, it gives the same or runs out of memory; and a module whose
#     program halts at once gives no result.
#   B (machine): from the image of a book, Mach.code never traps, and it
#     gives what Eval gives, or runs out of memory; with the memory of
#     AGENTS.md 3.9.1.4, it gives it.
#
# A lemma whose body is ?TODO is still open: the laws hold once each is
# proven. The proofs of the laws themselves, at the end, are complete.

import Base
import ../Book/impl.bend as Bk
import ../Eval/impl.bend as El
import ../Wasm/impl.bend as Wa
import ../Program/impl.bend as Pg
import ./Cir/impl.bend as Cr
import ./Machine/impl.bend as Mc
import ./impl.bend as C
import ./spec.bend as S
import ./need_big.bend as PN
import ./img_small.bend as PI
import ./Cir/runs_as_cir.bend as A
import ./Machine/runs_as_eval.bend as B

# the image of a book of fewer than 2^26 bytes has fewer than 2^26 cells
def img.small(
  +p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>,
  rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  small: {Mc.Img.small(p, 0) == True{} : Bool}
) -> {Nat.is_lt(List.length(&2, Cr.Cir.Cell, Mc.Img.cells(ds)), U32.to_nat(67108864)) == True{} : Bool}:
  PI.img.small.nat(p, ds, rd, small)

# a book of 2^26 bytes or more needs more memory than a module can have
def need.big(
  +p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +n: Nat, +m: U32,
  rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  small: {Mc.Img.small(p, 0) == False{} : Bool},
  big: {Nat.is_le(Pg.Program.need(p, i, n), Pg.Program.memory(m)) == True{} : Bool}
) -> Empty:
  PN.need.big.proof(p, ds, i, n, m, rd, small, big)

# The laws
# --------
#
# Each law goes by the cases of Compiler.compile: a book of 2^26 bytes or
# more, a book that Book.read cannot read, and a book that it reads.

def gives.read.at(
  +p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +o: List<&2, Word(8n)>, +k: Nat,
  er: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  ek: {Pg.Program.result(ds, El.Eval.steps(k, ds, Pg.Program.start(i))) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}
) -> {Pg.Program.gives(p, i, k) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}:
  %Equal.sym(Maybe<List<&2, Bk.Def>>, Bk.Book.read(p), Some{ds}, er) : {Pg.Program.gives.of(_, i, k) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}
  ek

# what a program gives after k steps, once its book is read
def gives.read(
  +p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +o: List<&2, Word(8n)>,
  er: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  s: &k:Nat -> {Pg.Program.result(ds, El.Eval.steps(k, ds, Pg.Program.start(i))) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}
) -> &k:Nat -> {Pg.Program.gives(p, i, k) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}:
  (+k, ek) = s
  (k, gives.read.at(p, ds, i, o, k, er, ek))

# the compiler's module of a book that it reads, and of fewer than 2^26
# bytes, is the machine's module of its image; machine is any maker of it,
# so that no check computes the machine's module
def compile.machine(machine: List<&2, Cr.Cir.Cell> -> List<&2, Word(8n)>, +ds: List<&2, Bk.Def>) ->
  {C.Compiler.compile.of(machine, True{}, Some{ds}) == machine(Mc.Img.cells(ds)) : List<&2, Word(8n)>}:
  {==}

# no_wrong_result, for a book that Book.read reads: its machine's result is,
# by A, one that Cir gives, and so, by B, one that Eval gives
def nwr.machine(
  +p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +m: U32, +o: List<&2, Word(8n)>,
  +er: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  +es: {Mc.Img.small(p, 0) == True{} : Bool},
  s: &n:Nat -> {Cr.Cir.result(n, Mc.Mach.code(), Mc.Mach.regs(), Mc.Img.cells(ds), i, m) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome}
) -> &k:Nat -> {Pg.Program.gives(p, i, k) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}:
  (+n, en) = s
  gives.read(p, ds, i, o, er, B.mach.sound(p, ds, i, m, n, o, er, es, en))

def nwr.of(+f: Nat, +p: List<&2, Word(8n)>, +i: List<&2, Word(8n)>, +m: U32, +gs: List<&2, Bool>, +L: Nat, +o: List<&2, Word(8n)>, small: Bool,
  r: Maybe<List<&2, Bk.Def>>) ->
  {Mc.Img.small(p, 0) == small : Bool} -> {Bk.Book.read(p) == r : Maybe<List<&2, Bk.Def>>} ->
  {Wa.Wasm.run(f, C.Compiler.compile.of(C.Compiler.module, small, r), i, Wa.Wasm.Engine{m, gs, L}) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome} ->
  &k:Nat -> {Pg.Program.gives(p, i, k) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}:
  match small r:
    case False{} _:
      es => er => e => Empty.absurd(&k:Nat -> {Pg.Program.gives(p, i, k) == Some{o} : Maybe<&2, List<&2, Word(8n)>>},
        A.halt.no_result(f, 1, i, Wa.Wasm.Engine{m, gs, L}, o, {==}, e))
    case True{} None{}:
      es => er => e => Empty.absurd(&k:Nat -> {Pg.Program.gives(p, i, k) == Some{o} : Maybe<&2, List<&2, Word(8n)>>},
        A.halt.no_result(f, 2, i, Wa.Wasm.Engine{m, gs, L}, o, {==}, e))
    case True{} Some{+ds}:
      +es => +er => e => nwr.machine(p, ds, i, m, o, er, es,
        A.mach_wasm.sound(f, Mc.Img.cells(ds), i, m, gs, L, o, img.small(p, ds, er, es), x => B.mach.safe(p, ds, i, m, x, er, es),
          (%compile.machine(C.Compiler.module, ds) : {Wa.Wasm.run(f, _, i, Wa.Wasm.Engine{m, gs, L}) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome}; e)))

# no_wrong_result, by the parts of the engine
def nwr.eng(+f: Nat, +p: List<&2, Word(8n)>, +i: List<&2, Word(8n)>, eng: Wa.Wasm.Engine, +o: List<&2, Word(8n)>) ->
  {Wa.Wasm.run(f, C.Compiler.compile(p), i, eng) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome} -> &k:Nat -> {Pg.Program.gives(p, i, k) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}:
  match eng:
    case Wa.Wasm.Engine{+m, +gs, +L}:
      e => nwr.of(f, p, i, m, gs, L, o, Mc.Img.small(p, 0), Bk.Book.read(p))({==}, {==}, e)

def S.no_wrong_result(f, p, i, eng, o, e):
  nwr.eng(f, p, i, eng, o)(e)

# Some and None differ: a motive that is Empty at None
def maybe.none(x: Maybe<&2, List<&2, Word(8n)>>) -> Type:
  match x:
    case None{}:
      Empty
    case Some{_}:
      Unit

# Eval gives no result from a book that Book.read cannot read
def gives.none(-o: List<&2, Word(8n)>, e: {None{} == Some{o} : Maybe<&2, List<&2, Word(8n)>>}) -> Empty:
  %Equal.sym(Maybe<&2, List<&2, Word(8n)>>, None{}, Some{o}, e) : maybe.none(_)
  Unit{}

# the machine's module of a book that the compiler reads is its module
def run.machine(+f: Nat, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +eng: Wa.Wasm.Engine, +x: Wa.Wasm.Outcome,
  ef: {Wa.Wasm.run(f, C.Compiler.module(Mc.Img.cells(ds)), i, eng) == x : Wa.Wasm.Outcome}) ->
  {Wa.Wasm.run(f, C.Compiler.compile.of(C.Compiler.module, True{}, Some{ds}), i, eng) == x : Wa.Wasm.Outcome}:
  %Equal.sym(List<&2, Word(8n)>, C.Compiler.compile.of(C.Compiler.module, True{}, Some{ds}), C.Compiler.module(Mc.Img.cells(ds)),
    compile.machine(C.Compiler.module, ds)) : {Wa.Wasm.run(f, _, i, eng) == x : Wa.Wasm.Outcome}
  ef

# no_other_failure, for a book that the compiler reads: by B, the machine gives
# the result or runs out of memory, and so, by A, does its module
def nof.result(+ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +eng: Wa.Wasm.Engine, +o: List<&2, Word(8n)>,
  s: &f:Nat -> Or({Wa.Wasm.run(f, C.Compiler.module(Mc.Img.cells(ds)), i, eng) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome},
    {Wa.Wasm.run(f, C.Compiler.module(Mc.Img.cells(ds)), i, eng) == Wa.Wasm.Outcome.out_of_memory{} : Wa.Wasm.Outcome})) ->
  &f:Nat -> Or({Wa.Wasm.run(f, C.Compiler.compile.of(C.Compiler.module, True{}, Some{ds}), i, eng) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome},
    {Wa.Wasm.run(f, C.Compiler.compile.of(C.Compiler.module, True{}, Some{ds}), i, eng) == Wa.Wasm.Outcome.out_of_memory{} : Wa.Wasm.Outcome}):
  (+f, c) = s
  match c:
    case Inl{a}:
      (f, Inl{run.machine(f, ds, i, eng, Wa.Wasm.Outcome.result{o}, a)})
    case Inr{b}:
      (f, Inr{run.machine(f, ds, i, eng, Wa.Wasm.Outcome.out_of_memory{}, b)})

def nof.oom(+ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +eng: Wa.Wasm.Engine, -o: List<&2, Word(8n)>,
  s: &f:Nat -> {Wa.Wasm.run(f, C.Compiler.module(Mc.Img.cells(ds)), i, eng) == Wa.Wasm.Outcome.out_of_memory{} : Wa.Wasm.Outcome}) ->
  &f:Nat -> Or({Wa.Wasm.run(f, C.Compiler.compile.of(C.Compiler.module, True{}, Some{ds}), i, eng) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome},
    {Wa.Wasm.run(f, C.Compiler.compile.of(C.Compiler.module, True{}, Some{ds}), i, eng) == Wa.Wasm.Outcome.out_of_memory{} : Wa.Wasm.Outcome}):
  (+f, ef) = s
  (f, Inr{run.machine(f, ds, i, eng, Wa.Wasm.Outcome.out_of_memory{}, ef)})

def nof.machine(+p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +m: U32, +gs: List<&2, Bool>, +L: Nat, +o: List<&2, Word(8n)>,
  +er: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  +es: {Mc.Img.small(p, 0) == True{} : Bool},
  s: &n:Nat -> Or({Cr.Cir.result(n, Mc.Mach.code(), Mc.Mach.regs(), Mc.Img.cells(ds), i, m) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome},
    {Cr.Cir.result(n, Mc.Mach.code(), Mc.Mach.regs(), Mc.Img.cells(ds), i, m) == Wa.Wasm.Outcome.out_of_memory{} : Wa.Wasm.Outcome})) ->
  &f:Nat -> Or({Wa.Wasm.run(f, C.Compiler.compile.of(C.Compiler.module, True{}, Some{ds}), i, Wa.Wasm.Engine{m, gs, L}) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome},
    {Wa.Wasm.run(f, C.Compiler.compile.of(C.Compiler.module, True{}, Some{ds}), i, Wa.Wasm.Engine{m, gs, L}) == Wa.Wasm.Outcome.out_of_memory{} : Wa.Wasm.Outcome}):
  (+n, c) = s
  match c:
    case Inl{a}:
      nof.result(ds, i, Wa.Wasm.Engine{m, gs, L}, o, A.mach_wasm.result(n, Mc.Img.cells(ds), i, m, gs, L, o, img.small(p, ds, er, es), a))
    case Inr{b}:
      nof.oom(ds, i, Wa.Wasm.Engine{m, gs, L}, o, A.mach_wasm.oom(n, Mc.Img.cells(ds), i, m, gs, L, img.small(p, ds, er, es), b))

# a module that halts with 1 runs out of memory
def nof.halt(+i: List<&2, Word(8n)>, +eng: Wa.Wasm.Engine, -o: List<&2, Word(8n)>,
  s: &f:Nat -> {Wa.Wasm.run(f, C.Compiler.halt(1), i, eng) == Wa.Wasm.Outcome.out_of_memory{} : Wa.Wasm.Outcome}) ->
  &f:Nat -> Or({Wa.Wasm.run(f, C.Compiler.halt(1), i, eng) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome},
    {Wa.Wasm.run(f, C.Compiler.halt(1), i, eng) == Wa.Wasm.Outcome.out_of_memory{} : Wa.Wasm.Outcome}):
  (+f, ef) = s
  (f, Inr{ef})

def nof.of(+p: List<&2, Word(8n)>, +i: List<&2, Word(8n)>, +n: Nat, +o: List<&2, Word(8n)>, +m: U32, +gs: List<&2, Bool>, +L: Nat, small: Bool,
  r: Maybe<List<&2, Bk.Def>>) ->
  {Mc.Img.small(p, 0) == small : Bool} -> {Bk.Book.read(p) == r : Maybe<List<&2, Bk.Def>>} ->
  {Pg.Program.gives.of(r, i, n) == Some{o} : Maybe<&2, List<&2, Word(8n)>>} ->
  &f:Nat -> Or({Wa.Wasm.run(f, C.Compiler.compile.of(C.Compiler.module, small, r), i, Wa.Wasm.Engine{m, gs, L}) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome},
    {Wa.Wasm.run(f, C.Compiler.compile.of(C.Compiler.module, small, r), i, Wa.Wasm.Engine{m, gs, L}) == Wa.Wasm.Outcome.out_of_memory{} : Wa.Wasm.Outcome}):
  match small r:
    case False{} _:
      es => er => e => nof.halt(i, Wa.Wasm.Engine{m, gs, L}, o, A.halt.oom(i, Wa.Wasm.Engine{m, gs, L}))
    case True{} None{}:
      es => er => e => Empty.absurd(
        &f:Nat -> Or({Wa.Wasm.run(f, C.Compiler.halt(2), i, Wa.Wasm.Engine{m, gs, L}) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome},
          {Wa.Wasm.run(f, C.Compiler.halt(2), i, Wa.Wasm.Engine{m, gs, L}) == Wa.Wasm.Outcome.out_of_memory{} : Wa.Wasm.Outcome}),
        gives.none(o, e))
    case True{} Some{+ds}:
      +es => +er => e => nof.machine(p, ds, i, m, gs, L, o, er, es, B.mach.complete(p, ds, i, m, n, o, er, es, e))

# no_other_failure, by the parts of the engine
def nof.eng(+p: List<&2, Word(8n)>, +i: List<&2, Word(8n)>, +n: Nat, +o: List<&2, Word(8n)>, eng: Wa.Wasm.Engine) ->
  {Pg.Program.gives(p, i, n) == Some{o} : Maybe<&2, List<&2, Word(8n)>>} ->
  &f:Nat -> Or({Wa.Wasm.run(f, C.Compiler.compile(p), i, eng) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome},
    {Wa.Wasm.run(f, C.Compiler.compile(p), i, eng) == Wa.Wasm.Outcome.out_of_memory{} : Wa.Wasm.Outcome}):
  match eng:
    case Wa.Wasm.Engine{+m, +gs, +L}:
      e => nof.of(p, i, n, o, m, gs, L, Mc.Img.small(p, 0), Bk.Book.read(p))({==}, {==}, e)

def S.no_other_failure(p, i, n, o, eng, e):
  nof.eng(p, i, n, o, eng)(e)

# enough_memory: a book of 2^26 bytes or more that Book.read reads asks more
# memory than a module can have; for one that the compiler reads, B then A
def em.result(+ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +m: U32, +L: Nat, +o: List<&2, Word(8n)>,
  s: &f:Nat -> {Wa.Wasm.run(f, C.Compiler.module(Mc.Img.cells(ds)), i, Wa.Wasm.Engine{m, [], L}) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome}) ->
  &f:Nat -> {Wa.Wasm.run(f, C.Compiler.compile.of(C.Compiler.module, True{}, Some{ds}), i, Wa.Wasm.Engine{m, [], L}) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome}:
  (+f, ef) = s
  (f, run.machine(f, ds, i, Wa.Wasm.Engine{m, [], L}, Wa.Wasm.Outcome.result{o}, ef))

# the engine takes the machine's module of a book that the compiler reads
def fits.machine(+ds: List<&2, Bk.Def>, +L: Nat,
  h: {Nat.is_le(List.length(&2, Word(8n), C.Compiler.compile.of(C.Compiler.module, True{}, Some{ds})), L) == True{} : Bool}) ->
  {Nat.is_le(List.length(&2, Word(8n), C.Compiler.module(Mc.Img.cells(ds))), L) == True{} : Bool}:
  %compile.machine(C.Compiler.module, ds) : {Nat.is_le(List.length(&2, Word(8n), _), L) == True{} : Bool}
  h

def em.machine(+p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +m: U32, +L: Nat, +o: List<&2, Word(8n)>,
  +er: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  +es: {Mc.Img.small(p, 0) == True{} : Bool},
  fits: {Nat.is_le(List.length(&2, Word(8n), C.Compiler.module(Mc.Img.cells(ds))), L) == True{} : Bool},
  s: &n:Nat -> {Cr.Cir.result(n, Mc.Mach.code(), Mc.Mach.regs(), Mc.Img.cells(ds), i, m) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome}) ->
  &f:Nat -> {Wa.Wasm.run(f, C.Compiler.compile.of(C.Compiler.module, True{}, Some{ds}), i, Wa.Wasm.Engine{m, [], L}) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome}:
  (+n, en) = s
  em.result(ds, i, m, L, o, A.mach_wasm.result.all(n, Mc.Img.cells(ds), i, m, L, o, img.small(p, ds, er, es), fits, en))

def em.of(+p: List<&2, Word(8n)>, +i: List<&2, Word(8n)>, +n: Nat, +o: List<&2, Word(8n)>, +m: U32, +L: Nat, small: Bool,
  r: Maybe<List<&2, Bk.Def>>) ->
  {Mc.Img.small(p, 0) == small : Bool} -> {Bk.Book.read(p) == r : Maybe<List<&2, Bk.Def>>} ->
  {Pg.Program.gives.of(r, i, n) == Some{o} : Maybe<&2, List<&2, Word(8n)>>} ->
  {Nat.is_le(Pg.Program.need(p, i, n), Pg.Program.memory(m)) == True{} : Bool} ->
  {Nat.is_le(List.length(&2, Word(8n), C.Compiler.compile.of(C.Compiler.module, small, r)), L) == True{} : Bool} ->
  &f:Nat -> {Wa.Wasm.run(f, C.Compiler.compile.of(C.Compiler.module, small, r), i, Wa.Wasm.Engine{m, [], L}) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome}:
  match small r:
    case False{} None{}:
      es => er => e => big => fits => Empty.absurd(
        &f:Nat -> {Wa.Wasm.run(f, C.Compiler.halt(1), i, Wa.Wasm.Engine{m, [], L}) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome},
        gives.none(o, e))
    case False{} Some{+ds}:
      es => er => e => big => fits => Empty.absurd(
        &f:Nat -> {Wa.Wasm.run(f, C.Compiler.halt(1), i, Wa.Wasm.Engine{m, [], L}) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome},
        need.big(p, ds, i, n, m, er, es, big))
    case True{} None{}:
      es => er => e => big => fits => Empty.absurd(
        &f:Nat -> {Wa.Wasm.run(f, C.Compiler.halt(2), i, Wa.Wasm.Engine{m, [], L}) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome},
        gives.none(o, e))
    case True{} Some{+ds}:
      +es => +er => e => big => fits => em.machine(p, ds, i, m, L, o, er, es, fits.machine(ds, L, fits),
        B.mach.memory(p, ds, i, m, n, o, er, es, e, big))

def S.enough_memory(p, i, n, o, m, L, e, big, fits):
  em.of(p, i, n, o, m, L, Mc.Img.small(p, 0), Bk.Book.read(p))({==}, {==}, e, big, fits)
