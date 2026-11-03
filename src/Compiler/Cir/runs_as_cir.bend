# Compiler/Cir: layer A of the proofs of the laws (Compiler/proof.bend)
# =====================================================================
#
#   A (translation): the module that Cir.module makes of the machine runs in
#     the Bend version of WASM as Cir.exec says (Cir.result), for any image of
#     fewer than 2^26 cells, when Cir.exec never traps, on an engine that
#     grants each grow within its pages; on any other engine, it gives the
#     same or runs out of memory; and a module whose program halts at once
#     gives no result.

import Base
import ../../Wasm/impl.bend as Wa
import ./impl.bend as Cr
import ../Machine/impl.bend as Mc
import ../impl.bend as C
import ../need_big.bend as N
import ./halt.bend as PH
import ./more_fuel.bend as MF
import ./simulation_numbers.bend as Z
import ./simulation_host.bend as H

# the module that Compiler.module.of makes of prog is Cir.module's, encoded
def module.of(prog: Cr.Cir.Stmt, regs: Nat, cells: List<&2, Cr.Cir.Cell>) ->
  {Cr.Wasm.encode(Cr.Cir.module(prog, regs, cells)) == C.Compiler.module.of(prog, regs, cells) : List<&2, Word(8n)>}:
  {==}

# the machine's module, on an engine with the answers gs, gives Cir's outcome x (a result, out of memory or no
# result) or runs out of memory after a refusal
def mach_wasm.host(+n: Nat, +cells: List<&2, Cr.Cir.Cell>, +i: List<&2, Word(8n)>, +m: U32, +x: Wa.Wasm.Outcome, +gs: List<&2, Bool>,
  small: {Nat.is_lt(List.length(&2, Cr.Cir.Cell, cells), U32.to_nat(67108864)) == True{} : Bool}, hx: H.is.ro(x),
  e: {Cr.Cir.result(n, Mc.Mach.code(), Mc.Mach.regs(), cells, i, m) == x : Wa.Wasm.Outcome}) ->
  &f:Nat -> H.HO(x, gs, Wa.Wasm.run(f, C.Compiler.module.of(Mc.Mach.code(), Mc.Mach.regs(), cells), i, Wa.Wasm.Engine{m, gs})):
  %module.of(Mc.Mach.code(), Mc.Mach.regs(), cells) : &f:Nat -> H.HO(x, gs, Wa.Wasm.run(f, _, i, Wa.Wasm.Engine{m, gs}))
  H.mach.all(n, cells, i, m, x, gs, small, hx, e)

# a host outcome of x, at one fuel, and a result, at another: x is that result
def sound.ho(+x: Wa.Wasm.Outcome, +f: Nat, +w: List<&2, Word(8n)>, +i: List<&2, Word(8n)>, +eng: Wa.Wasm.Engine, +gs: List<&2, Bool>, +o: List<&2, Word(8n)>,
  nx: {MF.done(x) == True{} : Bool},
  q: &f2:Nat -> H.HO(x, gs, Wa.Wasm.run(f2, w, i, eng)),
  e: {Wa.Wasm.run(f, w, i, eng) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome}) -> {x == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome}:
  (+f2, p) = q
  match p:
    case Inl{eq}:
      +r2 = MF.run.more(f, f2, w, i, eng, Wa.Wasm.Outcome.result{o}, {==}, e)
      +cm = Equal.cong(Nat, Wa.Wasm.Outcome, z => Wa.Wasm.run(z, w, i, eng), Nat.add(f2, f), Nat.add(f, f2), Z.add.comm(f2, f))
      Equal.trans(Wa.Wasm.Outcome, x, Wa.Wasm.run(Nat.add(f2, f), w, i, eng), Wa.Wasm.Outcome.result{o},
        Equal.sym(Wa.Wasm.Outcome, Wa.Wasm.run(Nat.add(f2, f), w, i, eng), x, MF.run.more(f2, f, w, i, eng, x, nx, eq)),
        Equal.trans(Wa.Wasm.Outcome, Wa.Wasm.run(Nat.add(f2, f), w, i, eng), Wa.Wasm.run(Nat.add(f, f2), w, i, eng), Wa.Wasm.Outcome.result{o}, cm, r2))
    case Inr{r}:
      (+k, r1) = r
      (hg, eo) = r1
      +r2 = MF.run.more(f, f2, w, i, eng, Wa.Wasm.Outcome.result{o}, {==}, e)
      +cm = Equal.cong(Nat, Wa.Wasm.Outcome, z => Wa.Wasm.run(z, w, i, eng), Nat.add(f2, f), Nat.add(f, f2), Z.add.comm(f2, f))
      Empty.absurd({x == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome},
        H.res.is(Wa.Wasm.Outcome.out_of_memory{}, o,
          Equal.trans(Wa.Wasm.Outcome, Wa.Wasm.Outcome.out_of_memory{}, Wa.Wasm.run(Nat.add(f2, f), w, i, eng), Wa.Wasm.Outcome.result{o},
            Equal.sym(Wa.Wasm.Outcome, Wa.Wasm.run(Nat.add(f2, f), w, i, eng), Wa.Wasm.Outcome.out_of_memory{}, MF.run.more(f2, f, w, i, eng, Wa.Wasm.Outcome.out_of_memory{}, {==}, eo)),
            Equal.trans(Wa.Wasm.Outcome, Wa.Wasm.run(Nat.add(f2, f), w, i, eng), Wa.Wasm.run(Nat.add(f, f2), w, i, eng), Wa.Wasm.Outcome.result{o}, cm, r2))))

# Cir's outcome x, which is a result, out of memory or no result, is the result that the machine's module gives at the
# fuel f (e)
def sound.ro(+x: Wa.Wasm.Outcome, +f: Nat, +cells: List<&2, Cr.Cir.Cell>, +i: List<&2, Word(8n)>, +m: U32, +gs: List<&2, Bool>, +o: List<&2, Word(8n)>,
  small: {Nat.is_lt(List.length(&2, Cr.Cir.Cell, cells), U32.to_nat(67108864)) == True{} : Bool}, hx: H.is.ro(x), nx: {MF.done(x) == True{} : Bool},
  e: {Wa.Wasm.run(f, C.Compiler.module.of(Mc.Mach.code(), Mc.Mach.regs(), cells), i, Wa.Wasm.Engine{m, gs}) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome},
  +ex: {Cr.Cir.result(Nat.add(41n, f), Mc.Mach.code(), Mc.Mach.regs(), cells, i, m) == x : Wa.Wasm.Outcome}) ->
  {Cr.Cir.result(Nat.add(41n, f), Mc.Mach.code(), Mc.Mach.regs(), cells, i, m) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome}:
  Equal.trans(Wa.Wasm.Outcome, Cr.Cir.result(Nat.add(41n, f), Mc.Mach.code(), Mc.Mach.regs(), cells, i, m), x, Wa.Wasm.Outcome.result{o}, ex,
    sound.ho(x, f, C.Compiler.module.of(Mc.Mach.code(), Mc.Mach.regs(), cells), i, Wa.Wasm.Engine{m, gs}, gs, o, nx,
      mach_wasm.host(Nat.add(41n, f), cells, i, m, x, gs, small, hx, ex), e))

# a result at the fuel f is the result at the fuel 41 + f
def sound.more(+f: Nat, +w: List<&2, Word(8n)>, +i: List<&2, Word(8n)>, +eng: Wa.Wasm.Engine, +o: List<&2, Word(8n)>,
  e: {Wa.Wasm.run(f, w, i, eng) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome}) ->
  {Wa.Wasm.run(Nat.add(41n, f), w, i, eng) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome}:
  Equal.trans(Wa.Wasm.Outcome, Wa.Wasm.run(Nat.add(41n, f), w, i, eng), Wa.Wasm.run(Nat.add(f, 41n), w, i, eng), Wa.Wasm.Outcome.result{o},
    Equal.cong(Nat, Wa.Wasm.Outcome, z => Wa.Wasm.run(z, w, i, eng), Nat.add(41n, f), Nat.add(f, 41n), Z.add.comm(41n, f)),
    MF.run.more(f, 41n, w, i, eng, Wa.Wasm.Outcome.result{o}, {==}, e))

# the host's run at the fuel 41 + f is out of fuel, or out of memory (q), so that it is not the result that it gives at
# the fuel f (e)
def sound.nd.of(+f: Nat, +w: List<&2, Word(8n)>, +i: List<&2, Word(8n)>, +eng: Wa.Wasm.Engine, +o: List<&2, Word(8n)>,
  q: Or({Wa.Wasm.run(Nat.add(41n, f), w, i, eng) == Wa.Wasm.Outcome.not_done{} : Wa.Wasm.Outcome},
    {Wa.Wasm.run(Nat.add(41n, f), w, i, eng) == Wa.Wasm.Outcome.out_of_memory{} : Wa.Wasm.Outcome}),
  e: {Wa.Wasm.run(f, w, i, eng) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome}) -> Empty:
  match q:
    case Inl{eq}:
      H.ndo.is(Wa.Wasm.Outcome.result{o}, Equal.trans(Wa.Wasm.Outcome, Wa.Wasm.Outcome.result{o}, Wa.Wasm.run(Nat.add(41n, f), w, i, eng), Wa.Wasm.Outcome.not_done{},
        Equal.sym(Wa.Wasm.Outcome, Wa.Wasm.run(Nat.add(41n, f), w, i, eng), Wa.Wasm.Outcome.result{o}, sound.more(f, w, i, eng, o, e)), eq))
    case Inr{eq}:
      H.res.is(Wa.Wasm.Outcome.out_of_memory{}, o, Equal.trans(Wa.Wasm.Outcome, Wa.Wasm.Outcome.out_of_memory{}, Wa.Wasm.run(Nat.add(41n, f), w, i, eng), Wa.Wasm.Outcome.result{o},
        Equal.sym(Wa.Wasm.Outcome, Wa.Wasm.run(Nat.add(41n, f), w, i, eng), Wa.Wasm.Outcome.out_of_memory{}, eq), sound.more(f, w, i, eng, o, e)))

# Cir's outcome at the fuel 41 + f is not out of fuel: the machine's module, in that fuel, would be out of fuel, or
# out of memory, and it gives a result at the fuel f
def sound.nd(+f: Nat, +cells: List<&2, Cr.Cir.Cell>, +i: List<&2, Word(8n)>, +m: U32, +gs: List<&2, Bool>, +o: List<&2, Word(8n)>,
  small: {Nat.is_lt(List.length(&2, Cr.Cir.Cell, cells), U32.to_nat(67108864)) == True{} : Bool},
  e: {Wa.Wasm.run(f, C.Compiler.module.of(Mc.Mach.code(), Mc.Mach.regs(), cells), i, Wa.Wasm.Engine{m, gs}) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome},
  ex: {Cr.Cir.result(Nat.add(41n, f), Mc.Mach.code(), Mc.Mach.regs(), cells, i, m) == Wa.Wasm.Outcome.not_done{} : Wa.Wasm.Outcome}) -> Empty:
  sound.nd.of(f, C.Compiler.module.of(Mc.Mach.code(), Mc.Mach.regs(), cells), i, Wa.Wasm.Engine{m, gs}, o,
    H.ho.or(Wa.Wasm.Outcome.not_done{}, gs, Wa.Wasm.run(Nat.add(41n, f), C.Compiler.module.of(Mc.Mach.code(), Mc.Mach.regs(), cells), i, Wa.Wasm.Engine{m, gs}),
      (%module.of(Mc.Mach.code(), Mc.Mach.regs(), cells) : H.HO(Wa.Wasm.Outcome.not_done{}, gs, Wa.Wasm.run(Nat.add(41n, f), _, i, Wa.Wasm.Engine{m, gs}));
        H.mach.all.nd(Nat.add(41n, f), Nat.add(41n, f), cells, i, m, gs, small, N.le_add_r(41n, f), N.le_refl(Nat.add(41n, f)), ex))), e)

# Cir's outcome at the fuel 41 + f is a result, out of memory or no result (the machine's module gives it at the fuel
# f), a trap (safe), or out of fuel (sound.nd); it is never unsupported
def sound.of(x: Wa.Wasm.Outcome, +f: Nat, +cells: List<&2, Cr.Cir.Cell>, +i: List<&2, Word(8n)>, +m: U32, +gs: List<&2, Bool>, +o: List<&2, Word(8n)>,
  small: {Nat.is_lt(List.length(&2, Cr.Cir.Cell, cells), U32.to_nat(67108864)) == True{} : Bool},
  safe: @n:Nat -> {Cr.Cir.result(n, Mc.Mach.code(), Mc.Mach.regs(), cells, i, m) != Wa.Wasm.Outcome.trap{} : Wa.Wasm.Outcome},
  e: {Wa.Wasm.run(f, C.Compiler.module.of(Mc.Mach.code(), Mc.Mach.regs(), cells), i, Wa.Wasm.Engine{m, gs}) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome},
  ex: {Cr.Cir.result(Nat.add(41n, f), Mc.Mach.code(), Mc.Mach.regs(), cells, i, m) == x : Wa.Wasm.Outcome}) ->
  {Cr.Cir.result(Nat.add(41n, f), Mc.Mach.code(), Mc.Mach.regs(), cells, i, m) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome}:
  match x:
    case Wa.Wasm.Outcome.result{+o2}:
      sound.ro(Wa.Wasm.Outcome.result{o2}, f, cells, i, m, gs, o, small, Unit{}, {==}, e, ex)
    case Wa.Wasm.Outcome.out_of_memory{}:
      sound.ro(Wa.Wasm.Outcome.out_of_memory{}, f, cells, i, m, gs, o, small, Unit{}, {==}, e, ex)
    case Wa.Wasm.Outcome.no_result{}:
      sound.ro(Wa.Wasm.Outcome.no_result{}, f, cells, i, m, gs, o, small, Unit{}, {==}, e, ex)
    case Wa.Wasm.Outcome.unsupported{}:
      Empty.absurd({Cr.Cir.result(Nat.add(41n, f), Mc.Mach.code(), Mc.Mach.regs(), cells, i, m) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome},
        (%ex : H.is.cir(_); H.result.cir(Nat.add(41n, f), Mc.Mach.code(), Mc.Mach.regs(), cells, i, m)))
    case Wa.Wasm.Outcome.trap{}:
      Empty.absurd({Cr.Cir.result(Nat.add(41n, f), Mc.Mach.code(), Mc.Mach.regs(), cells, i, m) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome},
        safe(Nat.add(41n, f), ex))
    case Wa.Wasm.Outcome.not_done{}:
      Empty.absurd({Cr.Cir.result(Nat.add(41n, f), Mc.Mach.code(), Mc.Mach.regs(), cells, i, m) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome},
        sound.nd(f, cells, i, m, gs, o, small, e, ex))

# A: a result of the machine's module, on any engine, is one that Cir gives
# with the engine's pages: a grow that the engine refuses makes the module
# run out of memory, so it gives no result
def mach_wasm.sound(
  +f: Nat, +cells: List<&2, Cr.Cir.Cell>, +i: List<&2, Word(8n)>, +m: U32, +gs: List<&2, Bool>, +o: List<&2, Word(8n)>,
  small: {Nat.is_lt(List.length(&2, Cr.Cir.Cell, cells), U32.to_nat(67108864)) == True{} : Bool},
  safe: @n:Nat -> {Cr.Cir.result(n, Mc.Mach.code(), Mc.Mach.regs(), cells, i, m) != Wa.Wasm.Outcome.trap{} : Wa.Wasm.Outcome},
  e: {Wa.Wasm.run(f, C.Compiler.module.of(Mc.Mach.code(), Mc.Mach.regs(), cells), i, Wa.Wasm.Engine{m, gs}) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome}
) -> &n:Nat -> {Cr.Cir.result(n, Mc.Mach.code(), Mc.Mach.regs(), cells, i, m) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome}:
  (Nat.add(41n, f), sound.of(Cr.Cir.result(Nat.add(41n, f), Mc.Mach.code(), Mc.Mach.regs(), cells, i, m), f, cells, i, m, gs, o, small, safe, e, {==}))

# the machine's module, on an engine with the answers gs, gives what Cir gives
# or runs out of memory (q): without the refusal's index
def mach_wasm.result.of(+cells: List<&2, Cr.Cir.Cell>, +i: List<&2, Word(8n)>, +m: U32, +gs: List<&2, Bool>, +o: List<&2, Word(8n)>,
  q: &f:Nat -> H.HO(Wa.Wasm.Outcome.result{o}, gs, Wa.Wasm.run(f, C.Compiler.module.of(Mc.Mach.code(), Mc.Mach.regs(), cells), i, Wa.Wasm.Engine{m, gs}))) ->
  &f:Nat -> Or({Wa.Wasm.run(f, C.Compiler.module.of(Mc.Mach.code(), Mc.Mach.regs(), cells), i, Wa.Wasm.Engine{m, gs}) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome},
    {Wa.Wasm.run(f, C.Compiler.module.of(Mc.Mach.code(), Mc.Mach.regs(), cells), i, Wa.Wasm.Engine{m, gs}) == Wa.Wasm.Outcome.out_of_memory{} : Wa.Wasm.Outcome}):
  (+f, p) = q
  (f, H.ho.or(Wa.Wasm.Outcome.result{o}, gs, Wa.Wasm.run(f, C.Compiler.module.of(Mc.Mach.code(), Mc.Mach.regs(), cells), i, Wa.Wasm.Engine{m, gs}), p))

# A: a result that Cir gives is one of the machine's module, or the module
# runs out of memory, on any engine with the same pages
def mach_wasm.result(
  +n: Nat, +cells: List<&2, Cr.Cir.Cell>, +i: List<&2, Word(8n)>, +m: U32, +gs: List<&2, Bool>, +o: List<&2, Word(8n)>,
  small: {Nat.is_lt(List.length(&2, Cr.Cir.Cell, cells), U32.to_nat(67108864)) == True{} : Bool},
  e: {Cr.Cir.result(n, Mc.Mach.code(), Mc.Mach.regs(), cells, i, m) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome}
) -> &f:Nat -> Or({Wa.Wasm.run(f, C.Compiler.module.of(Mc.Mach.code(), Mc.Mach.regs(), cells), i, Wa.Wasm.Engine{m, gs}) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome},
  {Wa.Wasm.run(f, C.Compiler.module.of(Mc.Mach.code(), Mc.Mach.regs(), cells), i, Wa.Wasm.Engine{m, gs}) == Wa.Wasm.Outcome.out_of_memory{} : Wa.Wasm.Outcome}):
  mach_wasm.result.of(cells, i, m, gs, o,
    (%module.of(Mc.Mach.code(), Mc.Mach.regs(), cells) : &f:Nat -> H.HO(Wa.Wasm.Outcome.result{o}, gs, Wa.Wasm.run(f, _, i, Wa.Wasm.Engine{m, gs}));
      H.mach.all(n, cells, i, m, Wa.Wasm.Outcome.result{o}, gs, small, Unit{}, e)))

# the machine's module, on an engine that grants each grow, gives what Cir
# gives (q)
def mach_wasm.result.all.of(+cells: List<&2, Cr.Cir.Cell>, +i: List<&2, Word(8n)>, +m: U32, +o: List<&2, Word(8n)>,
  q: &f:Nat -> H.HO(Wa.Wasm.Outcome.result{o}, [], Wa.Wasm.run(f, C.Compiler.module.of(Mc.Mach.code(), Mc.Mach.regs(), cells), i, Wa.Wasm.Engine{m, []}))) ->
  &f:Nat -> {Wa.Wasm.run(f, C.Compiler.module.of(Mc.Mach.code(), Mc.Mach.regs(), cells), i, Wa.Wasm.Engine{m, []}) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome}:
  (+f, p) = q
  (f, H.ho.empty(Wa.Wasm.Outcome.result{o}, Wa.Wasm.run(f, C.Compiler.module.of(Mc.Mach.code(), Mc.Mach.regs(), cells), i, Wa.Wasm.Engine{m, []}), p))

# A: a result that Cir gives is one of the machine's module, on an engine
# that grants each grow within the pages
def mach_wasm.result.all(
  +n: Nat, +cells: List<&2, Cr.Cir.Cell>, +i: List<&2, Word(8n)>, +m: U32, +o: List<&2, Word(8n)>,
  small: {Nat.is_lt(List.length(&2, Cr.Cir.Cell, cells), U32.to_nat(67108864)) == True{} : Bool},
  e: {Cr.Cir.result(n, Mc.Mach.code(), Mc.Mach.regs(), cells, i, m) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome}
) -> &f:Nat -> {Wa.Wasm.run(f, C.Compiler.module.of(Mc.Mach.code(), Mc.Mach.regs(), cells), i, Wa.Wasm.Engine{m, []}) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome}:
  mach_wasm.result.all.of(cells, i, m, o,
    (%module.of(Mc.Mach.code(), Mc.Mach.regs(), cells) : &f:Nat -> H.HO(Wa.Wasm.Outcome.result{o}, [], Wa.Wasm.run(f, _, i, Wa.Wasm.Engine{m, []}));
      H.mach.all(n, cells, i, m, Wa.Wasm.Outcome.result{o}, [], small, Unit{}, e)))

# the machine's module, on an engine with the answers gs, runs out of memory
# when Cir does (q)
def mach_wasm.oom.of(+cells: List<&2, Cr.Cir.Cell>, +i: List<&2, Word(8n)>, +m: U32, +gs: List<&2, Bool>,
  q: &f:Nat -> H.HO(Wa.Wasm.Outcome.out_of_memory{}, gs, Wa.Wasm.run(f, C.Compiler.module.of(Mc.Mach.code(), Mc.Mach.regs(), cells), i, Wa.Wasm.Engine{m, gs}))) ->
  &f:Nat -> {Wa.Wasm.run(f, C.Compiler.module.of(Mc.Mach.code(), Mc.Mach.regs(), cells), i, Wa.Wasm.Engine{m, gs}) == Wa.Wasm.Outcome.out_of_memory{} : Wa.Wasm.Outcome}:
  (+f, p) = q
  (f, H.ho.oom(gs, Wa.Wasm.run(f, C.Compiler.module.of(Mc.Mach.code(), Mc.Mach.regs(), cells), i, Wa.Wasm.Engine{m, gs}), p))

# A: when Cir runs out of memory, so does the machine's module, on any
# engine with the same pages
def mach_wasm.oom(
  +n: Nat, +cells: List<&2, Cr.Cir.Cell>, +i: List<&2, Word(8n)>, +m: U32, +gs: List<&2, Bool>,
  small: {Nat.is_lt(List.length(&2, Cr.Cir.Cell, cells), U32.to_nat(67108864)) == True{} : Bool},
  e: {Cr.Cir.result(n, Mc.Mach.code(), Mc.Mach.regs(), cells, i, m) == Wa.Wasm.Outcome.out_of_memory{} : Wa.Wasm.Outcome}
) -> &f:Nat -> {Wa.Wasm.run(f, C.Compiler.module.of(Mc.Mach.code(), Mc.Mach.regs(), cells), i, Wa.Wasm.Engine{m, gs}) == Wa.Wasm.Outcome.out_of_memory{} : Wa.Wasm.Outcome}:
  mach_wasm.oom.of(cells, i, m, gs,
    (%module.of(Mc.Mach.code(), Mc.Mach.regs(), cells) : &f:Nat -> H.HO(Wa.Wasm.Outcome.out_of_memory{}, gs, Wa.Wasm.run(f, _, i, Wa.Wasm.Engine{m, gs}));
      H.mach.all(n, cells, i, m, Wa.Wasm.Outcome.out_of_memory{}, gs, small, Unit{}, e)))

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
