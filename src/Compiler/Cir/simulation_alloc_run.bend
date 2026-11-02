# compiler: a run of alloc
# ========================
#
# alloc(n) (Cir.alloc) gives the input's address a = Cir.input.at(k) with
# the memory grown to the pages that Cir.alloc.pages gives, or -1 when that
# gives none (af.call): by the cases of its four tests, the end a + n wraps
# (c1) or is past 2^32 - 16 (c2), the memory holds the pages already (c3),
# or the limit allows them (c4); each path is a fixed run of at most 41
# steps.

import Base
import ../../Wasm/impl.bend as Wa
import ./impl.bend as Cr
import ../need_big.bend as N
import ./halt.bend as PH
import ./module_round_trip.bend as M
import ./simulation_steps.bend as S
import ./simulation_relation.bend as Q
import ./simulation_write_frame.bend as F
import ./simulation_alloc_emit.bend as A

# The frames
# ----------

def af.a(+k: U32) -> U32:
  Cr.Cir.input.at(k)

def af.E(+k: U32, +len: U32) -> U32:
  U32.add(af.a(k), len)

# the pages that the end needs, as alloc computes them
def af.need(+k: U32, +len: U32) -> U32:
  U32.add(U32.shrn(U32.sub(af.E(k, len), 1), 16n), 1)

def af.LB() -> Wa.Wasm.Label:
  Wa.Wasm.Label{None{}, [Cr.Cir.i.get(2)], 0n}

def af.LG(+k: U32) -> Wa.Wasm.Label:
  Wa.Wasm.Label{None{}, [Cr.Cir.i.const(af.a(k)), Cr.Cir.i.set(2)], 0n}

# the inner block: the growth
def af.G(+k: U32) -> List<&2, Wa.Wasm.Instr>:
  [Cr.Cir.i.get(3), Wa.Wasm.Instr.memory_size{}, Cr.Cir.i.op(Wa.Wasm.Op.le_u{}), Wa.Wasm.Instr.br_if{0},
   Cr.Cir.i.get(3), Wa.Wasm.Instr.memory_size{}, Cr.Cir.i.op(Wa.Wasm.Op.sub{}), Wa.Wasm.Instr.memory_grow{},
   Cr.Cir.i.const(4294967295), Cr.Cir.i.op(Wa.Wasm.Op.eq{}), Wa.Wasm.Instr.br_if{1}]

def af.G1() -> List<&2, Wa.Wasm.Instr>:
  [Cr.Cir.i.get(3), Wa.Wasm.Instr.memory_size{}, Cr.Cir.i.op(Wa.Wasm.Op.sub{}), Wa.Wasm.Instr.memory_grow{},
   Cr.Cir.i.const(4294967295), Cr.Cir.i.op(Wa.Wasm.Op.eq{}), Wa.Wasm.Instr.br_if{1}]

# the outer block after its first test, and after its second
def af.B2(+k: U32) -> List<&2, Wa.Wasm.Instr>:
  [Cr.Cir.i.get(1), Cr.Cir.i.const(1), Cr.Cir.i.op(Wa.Wasm.Op.sub{}), Cr.Cir.i.const(16), Cr.Cir.i.op(Wa.Wasm.Op.shr_u{}),
   Cr.Cir.i.const(1), Cr.Cir.i.op(Wa.Wasm.Op.add{}), Cr.Cir.i.set(3),
   Wa.Wasm.Instr.block{af.G(k)},
   Cr.Cir.i.const(af.a(k)), Cr.Cir.i.set(2)]

def af.B1(+k: U32) -> List<&2, Wa.Wasm.Instr>:
  Con{Cr.Cir.i.get(1), Con{Cr.Cir.i.const(4294967280), Con{Cr.Cir.i.op(Wa.Wasm.Op.gt_u{}), Con{Wa.Wasm.Instr.br_if{0}, af.B2(k)}}}}

def af.L1(+k: U32, +len: U32) -> List<&2, U32>:
  [len, af.E(k, len), 4294967295, 0]

def af.L2(+k: U32, +len: U32) -> List<&2, U32>:
  [len, af.E(k, len), 4294967295, af.need(k, len)]

def af.L3(+k: U32, +len: U32) -> List<&2, U32>:
  [len, af.E(k, len), af.a(k), af.need(k, len)]

def af.fr0(+k: U32, +len: U32) -> Wa.Wasm.Frame:
  Wa.Wasm.Frame{M.body(Cr.Cir.alloc(k)), [], 1n, [], [len, 0, 0, 0]}

# The paths
# ---------

def af.s1(+k: U32, +len: U32, +mm: Wa.Wasm.Memory) ->
  {PH.H.steps(10n, Wa.Wasm.Step.next{af.fr0(k, len), mm}) ==
    Q.Cfg(Con{Wa.Wasm.Instr.br_if{0}, af.B1(k)}, [af.LB()], [Bool.to_u32(U32.is_lt(af.E(k, len), af.a(k)))], af.L1(k, len), mm) : Wa.Wasm.Step}:
  {==}

def af.s2(+k: U32, +len: U32, +mm: Wa.Wasm.Memory) ->
  {PH.H.steps(3n, Q.Cfg(af.B1(k), [af.LB()], [], af.L1(k, len), mm)) ==
    Q.Cfg(Con{Wa.Wasm.Instr.br_if{0}, af.B2(k)}, [af.LB()], [Bool.to_u32(U32.is_gt(af.E(k, len), 4294967280))], af.L1(k, len), mm) : Wa.Wasm.Step}:
  {==}

def af.s3(+k: U32, +len: U32, +p: U32, +lim: U32, +B: Wa.Wasm.Bytes) ->
  {PH.H.steps(12n, Q.Cfg(af.B2(k), [af.LB()], [], af.L1(k, len), Wa.Wasm.Memory{p, lim, [], B})) ==
    Q.Cfg(Con{Wa.Wasm.Instr.br_if{0}, af.G1()}, [af.LG(k), af.LB()], [Bool.to_u32(U32.is_le(af.need(k, len), p))], af.L2(k, len),
      Wa.Wasm.Memory{p, lim, [], B}) : Wa.Wasm.Step}:
  {==}

# a test that fails out of the outer block: alloc gives -1
def af.out(+L: List<&2, U32>, +mm: Wa.Wasm.Memory, +rest: List<&2, Wa.Wasm.Instr>, +v: U32, ez: {U32.is_zero(v) == False{} : Bool},
  eL: {List.get(&2, U32, L, 2n) == Some{4294967295} : Maybe<&2, U32>}) ->
  {PH.H.steps(3n, Q.Cfg(Con{Wa.Wasm.Instr.br_if{0}, rest}, [af.LB()], [v], L, mm)) == Wa.Wasm.Step.done{[4294967295], mm} : Wa.Wasm.Step}:
  S.steps.then(1n, 2n, Q.Cfg(Con{Wa.Wasm.Instr.br_if{0}, rest}, [af.LB()], [v], L, mm), Q.Cfg([Cr.Cir.i.get(2)], [], [], L, mm),
    Wa.Wasm.Step.done{[4294967295], mm}, A.br.ok(v, ez, rest, [Cr.Cir.i.get(2)], [], L, mm),
    %eL : {PH.H.steps(2n, Q.Cfg([Cr.Cir.i.get(2)], [], [], L, mm)) == Wa.Wasm.Step.done{[Maybe.default(&2, U32, _, 0)], mm} : Wa.Wasm.Step}
    {==})

def af.p1(+k: U32, +len: U32, +mm: Wa.Wasm.Memory, e1: {U32.is_lt(af.E(k, len), af.a(k)) == True{} : Bool}) ->
  {PH.H.steps(13n, Wa.Wasm.Step.next{af.fr0(k, len), mm}) == Wa.Wasm.Step.done{[4294967295], mm} : Wa.Wasm.Step}:
  S.steps.then(10n, 3n, Wa.Wasm.Step.next{af.fr0(k, len), mm},
    Q.Cfg(Con{Wa.Wasm.Instr.br_if{0}, af.B1(k)}, [af.LB()], [Bool.to_u32(U32.is_lt(af.E(k, len), af.a(k)))], af.L1(k, len), mm),
    Wa.Wasm.Step.done{[4294967295], mm}, af.s1(k, len, mm),
    af.out(af.L1(k, len), mm, af.B1(k), Bool.to_u32(U32.is_lt(af.E(k, len), af.a(k))), A.tz.t(U32.is_lt(af.E(k, len), af.a(k)), e1), {==}))

# the first test passes
def af.q1(+k: U32, +len: U32, +mm: Wa.Wasm.Memory, e1: {U32.is_lt(af.E(k, len), af.a(k)) == False{} : Bool}) ->
  {PH.H.steps(11n, Wa.Wasm.Step.next{af.fr0(k, len), mm}) == Q.Cfg(af.B1(k), [af.LB()], [], af.L1(k, len), mm) : Wa.Wasm.Step}:
  S.steps.then(10n, 1n, Wa.Wasm.Step.next{af.fr0(k, len), mm},
    Q.Cfg(Con{Wa.Wasm.Instr.br_if{0}, af.B1(k)}, [af.LB()], [Bool.to_u32(U32.is_lt(af.E(k, len), af.a(k)))], af.L1(k, len), mm),
    Q.Cfg(af.B1(k), [af.LB()], [], af.L1(k, len), mm), af.s1(k, len, mm),
    A.br.no(Bool.to_u32(U32.is_lt(af.E(k, len), af.a(k))), A.tz.f(U32.is_lt(af.E(k, len), af.a(k)), e1), af.B1(k), [af.LB()], af.L1(k, len), mm))

def af.p2(+k: U32, +len: U32, +mm: Wa.Wasm.Memory, e1: {U32.is_lt(af.E(k, len), af.a(k)) == False{} : Bool},
  e2: {U32.is_gt(af.E(k, len), 4294967280) == True{} : Bool}) ->
  {PH.H.steps(17n, Wa.Wasm.Step.next{af.fr0(k, len), mm}) == Wa.Wasm.Step.done{[4294967295], mm} : Wa.Wasm.Step}:
  +C1 = Q.Cfg(af.B1(k), [af.LB()], [], af.L1(k, len), mm)
  +v = Bool.to_u32(U32.is_gt(af.E(k, len), 4294967280))
  +C2 = Q.Cfg(Con{Wa.Wasm.Instr.br_if{0}, af.B2(k)}, [af.LB()], [v], af.L1(k, len), mm)
  S.steps.then(11n, 6n, Wa.Wasm.Step.next{af.fr0(k, len), mm}, C1, Wa.Wasm.Step.done{[4294967295], mm}, af.q1(k, len, mm, e1),
    S.steps.then(3n, 3n, C1, C2, Wa.Wasm.Step.done{[4294967295], mm}, af.s2(k, len, mm),
      af.out(af.L1(k, len), mm, af.B2(k), v, A.tz.t(U32.is_gt(af.E(k, len), 4294967280), e2), {==})))

# both tests pass: the pages, tested against those of the memory
def af.q2(+k: U32, +len: U32, +p: U32, +lim: U32, +B: Wa.Wasm.Bytes, e1: {U32.is_lt(af.E(k, len), af.a(k)) == False{} : Bool},
  e2: {U32.is_gt(af.E(k, len), 4294967280) == False{} : Bool}) ->
  {PH.H.steps(27n, Wa.Wasm.Step.next{af.fr0(k, len), Wa.Wasm.Memory{p, lim, [], B}}) ==
    Q.Cfg(Con{Wa.Wasm.Instr.br_if{0}, af.G1()}, [af.LG(k), af.LB()], [Bool.to_u32(U32.is_le(af.need(k, len), p))], af.L2(k, len),
      Wa.Wasm.Memory{p, lim, [], B}) : Wa.Wasm.Step}:
  +mm = {Wa.Wasm.Memory{p, lim, [], B} : Wa.Wasm.Memory}
  +C1 = Q.Cfg(af.B1(k), [af.LB()], [], af.L1(k, len), mm)
  +v = Bool.to_u32(U32.is_gt(af.E(k, len), 4294967280))
  +C2 = Q.Cfg(Con{Wa.Wasm.Instr.br_if{0}, af.B2(k)}, [af.LB()], [v], af.L1(k, len), mm)
  +C3 = Q.Cfg(af.B2(k), [af.LB()], [], af.L1(k, len), mm)
  +C4 = Q.Cfg(Con{Wa.Wasm.Instr.br_if{0}, af.G1()}, [af.LG(k), af.LB()], [Bool.to_u32(U32.is_le(af.need(k, len), p))], af.L2(k, len), mm)
  S.steps.then(11n, 16n, Wa.Wasm.Step.next{af.fr0(k, len), mm}, C1, C4, af.q1(k, len, mm, e1),
    S.steps.then(3n, 13n, C1, C2, C4, af.s2(k, len, mm),
      S.steps.then(1n, 12n, C2, C3, C4, A.br.no(v, A.tz.f(U32.is_gt(af.E(k, len), 4294967280), e2), af.B2(k), [af.LB()], af.L1(k, len), mm),
        af.s3(k, len, p, lim, B))))

# the end of the outer block: alloc gives a
def af.fin(+k: U32, +len: U32, +mm: Wa.Wasm.Memory) ->
  {PH.H.steps(5n, Q.Cfg([Cr.Cir.i.const(af.a(k)), Cr.Cir.i.set(2)], [af.LB()], [], af.L2(k, len), mm)) ==
    Wa.Wasm.Step.done{[af.a(k)], mm} : Wa.Wasm.Step}:
  {==}

# the memory holds the pages already
def af.p3(+k: U32, +len: U32, +p: U32, +lim: U32, +B: Wa.Wasm.Bytes, e1: {U32.is_lt(af.E(k, len), af.a(k)) == False{} : Bool},
  e2: {U32.is_gt(af.E(k, len), 4294967280) == False{} : Bool}, e3: {U32.is_le(af.need(k, len), p) == True{} : Bool}) ->
  {PH.H.steps(33n, Wa.Wasm.Step.next{af.fr0(k, len), Wa.Wasm.Memory{p, lim, [], B}}) == Wa.Wasm.Step.done{[af.a(k)], Wa.Wasm.Memory{p, lim, [], B}} : Wa.Wasm.Step}:
  +mm = {Wa.Wasm.Memory{p, lim, [], B} : Wa.Wasm.Memory}
  +v = Bool.to_u32(U32.is_le(af.need(k, len), p))
  +C4 = Q.Cfg(Con{Wa.Wasm.Instr.br_if{0}, af.G1()}, [af.LG(k), af.LB()], [v], af.L2(k, len), mm)
  +C5 = Q.Cfg([Cr.Cir.i.const(af.a(k)), Cr.Cir.i.set(2)], [af.LB()], [], af.L2(k, len), mm)
  S.steps.then(27n, 6n, Wa.Wasm.Step.next{af.fr0(k, len), mm}, C4, Wa.Wasm.Step.done{[af.a(k)], mm}, af.q2(k, len, p, lim, B, e1, e2),
    S.steps.then(1n, 5n, C4, C5, Wa.Wasm.Step.done{[af.a(k)], mm},
      A.br.ok(v, A.tz.t(U32.is_le(af.need(k, len), p), e3), af.G1(), [Cr.Cir.i.const(af.a(k)), Cr.Cir.i.set(2)], [af.LB()], af.L2(k, len), mm),
      af.fin(k, len, mm)))

# the growth, to its memory.grow
def af.s4(+k: U32, +len: U32, +p: U32, +lim: U32, +B: Wa.Wasm.Bytes) ->
  {PH.H.steps(3n, Q.Cfg(af.G1(), [af.LG(k), af.LB()], [], af.L2(k, len), Wa.Wasm.Memory{p, lim, [], B})) ==
    Q.Cfg([Wa.Wasm.Instr.memory_grow{}, Cr.Cir.i.const(4294967295), Cr.Cir.i.op(Wa.Wasm.Op.eq{}), Wa.Wasm.Instr.br_if{1}],
      [af.LG(k), af.LB()], [U32.sub(af.need(k, len), p)], af.L2(k, len), Wa.Wasm.Memory{p, lim, [], B}) : Wa.Wasm.Step}:
  {==}

def af.C4(+k: U32, +len: U32, +p: U32, +lim: U32, +B: Wa.Wasm.Bytes) -> Wa.Wasm.Step:
  Q.Cfg([Cr.Cir.i.const(4294967295), Cr.Cir.i.op(Wa.Wasm.Op.eq{}), Wa.Wasm.Instr.br_if{1}], [af.LG(k), af.LB()], [p], af.L2(k, len),
    Wa.Wasm.Memory{af.need(k, len), lim, [], B})

# memory.grow by need - p, within the limit: need pages
def af.grow(+k: U32, +len: U32, +p: U32, +lim: U32, +B: Wa.Wasm.Bytes, +e4: {U32.is_le(af.need(k, len), lim) == True{} : Bool},
  +hge: {U32.is_ge(af.need(k, len), p) == True{} : Bool}) ->
  {PH.H.steps(1n, Q.Cfg([Wa.Wasm.Instr.memory_grow{}, Cr.Cir.i.const(4294967295), Cr.Cir.i.op(Wa.Wasm.Op.eq{}), Wa.Wasm.Instr.br_if{1}],
      [af.LG(k), af.LB()], [U32.sub(af.need(k, len), p)], af.L2(k, len), Wa.Wasm.Memory{p, lim, [], B})) == af.C4(k, len, p, lim, B) : Wa.Wasm.Step}:
  +nd = af.need(k, len)
  +R = {[Cr.Cir.i.const(4294967295), Cr.Cir.i.op(Wa.Wasm.Op.eq{}), Wa.Wasm.Instr.br_if{1}] : List<&2, Wa.Wasm.Instr>}
  +LS = {[af.LG(k), af.LB()] : List<&2, Wa.Wasm.Label>}
  %Equal.sym(U32, U32.add(p, U32.sub(nd, p)), nd, A.U32.addsub(p, nd)) :
    {Wa.Wasm.step.within(Bool.and(U32.is_ge(_, p), U32.is_le(_, lim)), p, _, lim, [], B, R, LS, 1n, [], af.L2(k, len)) == af.C4(k, len, p, lim, B) : Wa.Wasm.Step}
  %Equal.sym(Bool, U32.is_ge(nd, p), True{}, hge) :
    {Wa.Wasm.step.within(Bool.and(_, U32.is_le(nd, lim)), p, nd, lim, [], B, R, LS, 1n, [], af.L2(k, len)) == af.C4(k, len, p, lim, B) : Wa.Wasm.Step}
  %Equal.sym(Bool, U32.is_le(nd, lim), True{}, e4) :
    {Wa.Wasm.step.within(Bool.and(True{}, _), p, nd, lim, [], B, R, LS, 1n, [], af.L2(k, len)) == af.C4(k, len, p, lim, B) : Wa.Wasm.Step}
  {==}

def af.and.f(b: Bool) -> {Bool.and(b, False{}) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# memory.grow past the limit: -1
def af.nogrow(+k: U32, +len: U32, +p: U32, +lim: U32, +B: Wa.Wasm.Bytes, +e4: {U32.is_le(af.need(k, len), lim) == False{} : Bool}) ->
  {PH.H.steps(1n, Q.Cfg([Wa.Wasm.Instr.memory_grow{}, Cr.Cir.i.const(4294967295), Cr.Cir.i.op(Wa.Wasm.Op.eq{}), Wa.Wasm.Instr.br_if{1}],
      [af.LG(k), af.LB()], [U32.sub(af.need(k, len), p)], af.L2(k, len), Wa.Wasm.Memory{p, lim, [], B})) ==
    Q.Cfg([Cr.Cir.i.const(4294967295), Cr.Cir.i.op(Wa.Wasm.Op.eq{}), Wa.Wasm.Instr.br_if{1}], [af.LG(k), af.LB()], [4294967295], af.L2(k, len),
      Wa.Wasm.Memory{p, lim, [], B}) : Wa.Wasm.Step}:
  +nd = af.need(k, len)
  +R = {[Cr.Cir.i.const(4294967295), Cr.Cir.i.op(Wa.Wasm.Op.eq{}), Wa.Wasm.Instr.br_if{1}] : List<&2, Wa.Wasm.Instr>}
  +LS = {[af.LG(k), af.LB()] : List<&2, Wa.Wasm.Label>}
  +G = Q.Cfg(R, LS, [4294967295], af.L2(k, len), Wa.Wasm.Memory{p, lim, [], B})
  %Equal.sym(U32, U32.add(p, U32.sub(nd, p)), nd, A.U32.addsub(p, nd)) :
    {Wa.Wasm.step.within(Bool.and(U32.is_ge(_, p), U32.is_le(_, lim)), p, _, lim, [], B, R, LS, 1n, [], af.L2(k, len)) == G : Wa.Wasm.Step}
  %Equal.sym(Bool, U32.is_le(nd, lim), False{}, e4) :
    {Wa.Wasm.step.within(Bool.and(U32.is_ge(nd, p), _), p, nd, lim, [], B, R, LS, 1n, [], af.L2(k, len)) == G : Wa.Wasm.Step}
  %Equal.sym(Bool, Bool.and(U32.is_ge(nd, p), False{}), False{}, af.and.f(U32.is_ge(nd, p))) :
    {Wa.Wasm.step.within(_, p, nd, lim, [], B, R, LS, 1n, [], af.L2(k, len)) == G : Wa.Wasm.Step}
  {==}

# after the growth: p is not -1, so on to the end
def af.tail(+k: U32, +len: U32, +p: U32, +lim: U32, +B: Wa.Wasm.Bytes, +hp: {U32.is_eq(p, 4294967295) == False{} : Bool}) ->
  {PH.H.steps(9n, af.C4(k, len, p, lim, B)) == Wa.Wasm.Step.done{[af.a(k)], Wa.Wasm.Memory{af.need(k, len), lim, [], B}} : Wa.Wasm.Step}:
  +M2 = {Wa.Wasm.Memory{af.need(k, len), lim, [], B} : Wa.Wasm.Memory}
  +C5 = Q.Cfg([Wa.Wasm.Instr.br_if{1}], [af.LG(k), af.LB()], [Bool.to_u32(U32.is_eq(p, 4294967295))], af.L2(k, len), M2)
  S.steps.then(2n, 7n, af.C4(k, len, p, lim, B), C5, Wa.Wasm.Step.done{[af.a(k)], M2}, {==},
    %Equal.sym(Bool, U32.is_eq(p, 4294967295), False{}, hp) :
      {PH.H.steps(7n, Q.Cfg([Wa.Wasm.Instr.br_if{1}], [af.LG(k), af.LB()], [Bool.to_u32(_)], af.L2(k, len), M2)) ==
        Wa.Wasm.Step.done{[af.a(k)], M2} : Wa.Wasm.Step}
    {==})

# the memory lacks the pages: the run to memory.grow
def af.q3(+k: U32, +len: U32, +p: U32, +lim: U32, +B: Wa.Wasm.Bytes, e1: {U32.is_lt(af.E(k, len), af.a(k)) == False{} : Bool},
  e2: {U32.is_gt(af.E(k, len), 4294967280) == False{} : Bool}, e3: {U32.is_le(af.need(k, len), p) == False{} : Bool}) ->
  {PH.H.steps(31n, Wa.Wasm.Step.next{af.fr0(k, len), Wa.Wasm.Memory{p, lim, [], B}}) ==
    Q.Cfg([Wa.Wasm.Instr.memory_grow{}, Cr.Cir.i.const(4294967295), Cr.Cir.i.op(Wa.Wasm.Op.eq{}), Wa.Wasm.Instr.br_if{1}],
      [af.LG(k), af.LB()], [U32.sub(af.need(k, len), p)], af.L2(k, len), Wa.Wasm.Memory{p, lim, [], B}) : Wa.Wasm.Step}:
  +mm = {Wa.Wasm.Memory{p, lim, [], B} : Wa.Wasm.Memory}
  +v = Bool.to_u32(U32.is_le(af.need(k, len), p))
  +C4 = Q.Cfg(Con{Wa.Wasm.Instr.br_if{0}, af.G1()}, [af.LG(k), af.LB()], [v], af.L2(k, len), mm)
  +C5 = Q.Cfg(af.G1(), [af.LG(k), af.LB()], [], af.L2(k, len), mm)
  +C6 = Q.Cfg([Wa.Wasm.Instr.memory_grow{}, Cr.Cir.i.const(4294967295), Cr.Cir.i.op(Wa.Wasm.Op.eq{}), Wa.Wasm.Instr.br_if{1}],
      [af.LG(k), af.LB()], [U32.sub(af.need(k, len), p)], af.L2(k, len), mm)
  S.steps.then(27n, 4n, Wa.Wasm.Step.next{af.fr0(k, len), mm}, C4, C6, af.q2(k, len, p, lim, B, e1, e2),
    S.steps.then(1n, 3n, C4, C5, C6, A.br.no(v, A.tz.f(U32.is_le(af.need(k, len), p), e3), af.G1(), [af.LG(k), af.LB()], af.L2(k, len), mm),
      af.s4(k, len, p, lim, B)))

def af.p4(+k: U32, +len: U32, +p: U32, +lim: U32, +B: Wa.Wasm.Bytes, e1: {U32.is_lt(af.E(k, len), af.a(k)) == False{} : Bool},
  e2: {U32.is_gt(af.E(k, len), 4294967280) == False{} : Bool}, +e3: {U32.is_le(af.need(k, len), p) == False{} : Bool},
  +e4: {U32.is_le(af.need(k, len), lim) == True{} : Bool}, +hp: {U32.is_eq(p, 4294967295) == False{} : Bool}) ->
  {PH.H.steps(41n, Wa.Wasm.Step.next{af.fr0(k, len), Wa.Wasm.Memory{p, lim, [], B}}) ==
    Wa.Wasm.Step.done{[af.a(k)], Wa.Wasm.Memory{af.need(k, len), lim, [], B}} : Wa.Wasm.Step}:
  +nd = af.need(k, len)
  +hge = A.ge.of(nd, p, N.weaken(U32.to_nat(p), U32.to_nat(nd), A.nle.u32(nd, p, e3)))
  +C6 = Q.Cfg([Wa.Wasm.Instr.memory_grow{}, Cr.Cir.i.const(4294967295), Cr.Cir.i.op(Wa.Wasm.Op.eq{}), Wa.Wasm.Instr.br_if{1}],
      [af.LG(k), af.LB()], [U32.sub(nd, p)], af.L2(k, len), Wa.Wasm.Memory{p, lim, [], B})
  S.steps.then(31n, 10n, Wa.Wasm.Step.next{af.fr0(k, len), Wa.Wasm.Memory{p, lim, [], B}}, C6,
    Wa.Wasm.Step.done{[af.a(k)], Wa.Wasm.Memory{nd, lim, [], B}}, af.q3(k, len, p, lim, B, e1, e2, e3),
    S.steps.then(1n, 9n, C6, af.C4(k, len, p, lim, B), Wa.Wasm.Step.done{[af.a(k)], Wa.Wasm.Memory{nd, lim, [], B}},
      af.grow(k, len, p, lim, B, e4, hge), af.tail(k, len, p, lim, B, hp)))

def af.p5(+k: U32, +len: U32, +p: U32, +lim: U32, +B: Wa.Wasm.Bytes, e1: {U32.is_lt(af.E(k, len), af.a(k)) == False{} : Bool},
  e2: {U32.is_gt(af.E(k, len), 4294967280) == False{} : Bool}, e3: {U32.is_le(af.need(k, len), p) == False{} : Bool},
  +e4: {U32.is_le(af.need(k, len), lim) == False{} : Bool}) ->
  {PH.H.steps(37n, Wa.Wasm.Step.next{af.fr0(k, len), Wa.Wasm.Memory{p, lim, [], B}}) ==
    Wa.Wasm.Step.done{[4294967295], Wa.Wasm.Memory{p, lim, [], B}} : Wa.Wasm.Step}:
  +mm = {Wa.Wasm.Memory{p, lim, [], B} : Wa.Wasm.Memory}
  +C6 = Q.Cfg([Wa.Wasm.Instr.memory_grow{}, Cr.Cir.i.const(4294967295), Cr.Cir.i.op(Wa.Wasm.Op.eq{}), Wa.Wasm.Instr.br_if{1}],
      [af.LG(k), af.LB()], [U32.sub(af.need(k, len), p)], af.L2(k, len), mm)
  +C7 = Q.Cfg([Cr.Cir.i.const(4294967295), Cr.Cir.i.op(Wa.Wasm.Op.eq{}), Wa.Wasm.Instr.br_if{1}], [af.LG(k), af.LB()], [4294967295], af.L2(k, len), mm)
  S.steps.then(31n, 6n, Wa.Wasm.Step.next{af.fr0(k, len), mm}, C6, Wa.Wasm.Step.done{[4294967295], mm}, af.q3(k, len, p, lim, B, e1, e2, e3),
    S.steps.then(1n, 5n, C6, C7, Wa.Wasm.Step.done{[4294967295], mm}, af.nogrow(k, len, p, lim, B, e4), {==}))

# The cases
# ---------

# what alloc's tests passed, when it gives the pages p2
def AFF(+k: U32, +len: U32, +p2: U32, +lim: U32) -> Data:
  S.P2({U32.is_lt(af.E(k, len), af.a(k)) == False{} : Bool}, S.P2({U32.is_gt(af.E(k, len), 4294967280) == False{} : Bool},
    S.P2({U32.is_le(af.need(k, len), p2) == True{} : Bool}, {U32.is_le(p2, lim) == True{} : Bool})))

def le.self.rel(c: Cmp, +x: Nat, r: N.Rel(c, x, x)) -> {Cmp.is_le(c) == True{} : Bool}:
  match c:
    case LT{}:
      Empty.absurd({True{} == True{} : Bool}, N.not_succ_le(x, r))
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({False{} == True{} : Bool}, N.not_succ_le(x, r))

def le.self(+x: U32) -> {U32.is_le(x, x) == True{} : Bool}:
  le.self.rel(U32.cmp(x, x), U32.to_nat(x), N.U32.rel(x, x))

# the run of alloc's body, by what Cir.alloc.pages gives
def AFS(r: Maybe<&2, U32>, +k: U32, +len: U32, +p: U32, +lim: U32, +B: Wa.Wasm.Bytes) -> Data:
  match r:
    case None{}:
      S.EX(N2 => S.P2({PH.H.steps(N2, Wa.Wasm.Step.next{af.fr0(k, len), Wa.Wasm.Memory{p, lim, [], B}}) ==
        Wa.Wasm.Step.done{[4294967295], Wa.Wasm.Memory{p, lim, [], B}} : Wa.Wasm.Step}, N.Le(N2, 41n)))
    case Some{+p2}:
      S.EX(N2 => S.P2(S.P2({PH.H.steps(N2, Wa.Wasm.Step.next{af.fr0(k, len), Wa.Wasm.Memory{p, lim, [], B}}) ==
        Wa.Wasm.Step.done{[af.a(k)], Wa.Wasm.Memory{p2, lim, [], B}} : Wa.Wasm.Step}, N.Le(N2, 41n)), AFF(k, len, p2, lim)))

def af.k4(b4: Bool, +k: U32, +len: U32, +p: U32, +lim: U32, +B: Wa.Wasm.Bytes, +e1: {U32.is_lt(af.E(k, len), af.a(k)) == False{} : Bool},
  +e2: {U32.is_gt(af.E(k, len), 4294967280) == False{} : Bool}, +e3: {U32.is_le(af.need(k, len), p) == False{} : Bool},
  +e4: {U32.is_le(af.need(k, len), lim) == b4 : Bool}, +hp: {U32.is_eq(p, 4294967295) == False{} : Bool}) ->
  AFS(Cr.Cir.alloc.grow(False{}, b4, p, af.need(k, len)), k, len, p, lim, B):
  match b4:
    case True{}:
      (41n, ((af.p4(k, len, p, lim, B, e1, e2, e3, e4, hp), Unit{}), (e1, (e2, (le.self(af.need(k, len)), e4)))))
    case False{}:
      (37n, (af.p5(k, len, p, lim, B, e1, e2, e3, e4), Unit{}))

def af.k3(b3: Bool, +k: U32, +len: U32, +p: U32, +lim: U32, +B: Wa.Wasm.Bytes, +e1: {U32.is_lt(af.E(k, len), af.a(k)) == False{} : Bool},
  +e2: {U32.is_gt(af.E(k, len), 4294967280) == False{} : Bool}, +e3: {U32.is_le(af.need(k, len), p) == b3 : Bool},
  +hp: {U32.is_eq(p, 4294967295) == False{} : Bool}, +hpl: {U32.is_le(p, lim) == True{} : Bool}) ->
  AFS(Cr.Cir.alloc.grow(b3, U32.is_le(af.need(k, len), lim), p, af.need(k, len)), k, len, p, lim, B):
  match b3:
    case True{}:
      (33n, ((af.p3(k, len, p, lim, B, e1, e2, e3), Unit{}), (e1, (e2, (e3, hpl)))))
    case False{}:
      af.k4(U32.is_le(af.need(k, len), lim), k, len, p, lim, B, e1, e2, e3, {==}, hp)

def af.k2(b2: Bool, +k: U32, +len: U32, +p: U32, +lim: U32, +B: Wa.Wasm.Bytes, +e1: {U32.is_lt(af.E(k, len), af.a(k)) == False{} : Bool},
  +e2: {U32.is_gt(af.E(k, len), 4294967280) == b2 : Bool}, +hp: {U32.is_eq(p, 4294967295) == False{} : Bool},
  +hpl: {U32.is_le(p, lim) == True{} : Bool}) ->
  AFS(Cr.Cir.alloc.end(Bool.or(False{}, b2), af.E(k, len), p, lim), k, len, p, lim, B):
  match b2:
    case True{}:
      (17n, (af.p2(k, len, Wa.Wasm.Memory{p, lim, [], B}, e1, e2), Unit{}))
    case False{}:
      %F.inc.add1(U32.shrn(U32.sub(af.E(k, len), 1), 16n)) :
        AFS(Cr.Cir.alloc.grow(U32.is_le(_, p), U32.is_le(_, lim), p, _), k, len, p, lim, B)
      af.k3(U32.is_le(af.need(k, len), p), k, len, p, lim, B, e1, e2, {==}, hp, hpl)

def af.k1(b1: Bool, +k: U32, +len: U32, +p: U32, +lim: U32, +B: Wa.Wasm.Bytes, +e1: {U32.is_lt(af.E(k, len), af.a(k)) == b1 : Bool},
  +hp: {U32.is_eq(p, 4294967295) == False{} : Bool}, +hpl: {U32.is_le(p, lim) == True{} : Bool}) ->
  AFS(Cr.Cir.alloc.end(Bool.or(b1, U32.is_gt(af.E(k, len), 4294967280)), af.E(k, len), p, lim), k, len, p, lim, B):
  match b1:
    case True{}:
      (13n, (af.p1(k, len, Wa.Wasm.Memory{p, lim, [], B}, e1), Unit{}))
    case False{}:
      af.k2(U32.is_gt(af.E(k, len), 4294967280), k, len, p, lim, B, e1, {==}, hp, hpl)

def af.steps(+k: U32, +len: U32, +p: U32, +lim: U32, +B: Wa.Wasm.Bytes, +hp: {U32.is_eq(p, 4294967295) == False{} : Bool},
  +hpl: {U32.is_le(p, lim) == True{} : Bool}) ->
  AFS(Cr.Cir.alloc.pages(k, len, p, lim), k, len, p, lim, B):
  af.k1(U32.is_lt(af.E(k, len), af.a(k)), k, len, p, lim, B, {==}, hp, hpl)

# The call
# --------

# what the call of alloc gives, by what Cir.alloc.pages gives
def AFC(c: Wa.Wasm.Call, r: Maybe<&2, U32>, +k: U32, +len: U32, +p: U32, +lim: U32, +B: Wa.Wasm.Bytes) -> Data:
  match r:
    case None{}:
      S.EX(j => S.P2({c == Wa.Wasm.Call.done{[4294967295], Wa.Wasm.Memory{p, lim, [], B}, j} : Wa.Wasm.Call}, N.Le(j, 41n)))
    case Some{+p2}:
      S.P2(S.EX(j => S.P2({c == Wa.Wasm.Call.done{[af.a(k)], Wa.Wasm.Memory{p2, lim, [], B}, j} : Wa.Wasm.Call}, N.Le(j, 41n))), AFF(k, len, p2, lim))

def af.bnd(c: Wa.Wasm.Call, -rs: List<&2, U32>, -mm: Wa.Wasm.Memory, +N2: Nat, hN: N.Le(N2, 41n),
  q: S.EX(j => S.P2({c == Wa.Wasm.Call.done{rs, mm, j} : Wa.Wasm.Call}, N.Le(j, N2)))) ->
  S.EX(j => S.P2({c == Wa.Wasm.Call.done{rs, mm, j} : Wa.Wasm.Call}, N.Le(j, 41n))):
  (+j, r1) = q
  (ec, hj) = r1
  (j, (ec, N.le_trans(j, N2, 41n, hj, hN)))

def af.some(+k: U32, +len: U32, +p: U32, +lim: U32, +B: Wa.Wasm.Bytes, +F: Nat, hF: N.Le(41n, F), +p2: U32, +N2: Nat,
  h2: S.P2({PH.H.steps(N2, Wa.Wasm.Step.next{af.fr0(k, len), Wa.Wasm.Memory{p, lim, [], B}}) ==
    Wa.Wasm.Step.done{[af.a(k)], Wa.Wasm.Memory{p2, lim, [], B}} : Wa.Wasm.Step}, N.Le(N2, 41n))) ->
  S.EX(j => S.P2({Wa.Wasm.call(F, Cr.Cir.alloc(k), [len], Wa.Wasm.Memory{p, lim, [], B}) == Wa.Wasm.Call.done{[af.a(k)], Wa.Wasm.Memory{p2, lim, [], B}, j} : Wa.Wasm.Call}, N.Le(j, 41n))):
  (e, +hN) = h2
  af.bnd(Wa.Wasm.call(F, Cr.Cir.alloc(k), [len], Wa.Wasm.Memory{p, lim, [], B}), [af.a(k)], Wa.Wasm.Memory{p2, lim, [], B}, N2, hN,
    S.run.call(N2, F, af.fr0(k, len), Wa.Wasm.Memory{p, lim, [], B}, [af.a(k)], Wa.Wasm.Memory{p2, lim, [], B}, e, N.le_trans(N2, 41n, F, hN, hF)))

def af.call.go(r: Maybe<&2, U32>, +k: U32, +len: U32, +p: U32, +lim: U32, +B: Wa.Wasm.Bytes, +F: Nat, hF: N.Le(41n, F),
  h: AFS(r, k, len, p, lim, B)) -> AFC(Wa.Wasm.call(F, Cr.Cir.alloc(k), [len], Wa.Wasm.Memory{p, lim, [], B}), r, k, len, p, lim, B):
  match r:
    case None{}:
      (+N2, h1) = h
      (e, +hN) = h1
      af.bnd(Wa.Wasm.call(F, Cr.Cir.alloc(k), [len], Wa.Wasm.Memory{p, lim, [], B}), [4294967295], Wa.Wasm.Memory{p, lim, [], B}, N2, hN,
        S.run.call(N2, F, af.fr0(k, len), Wa.Wasm.Memory{p, lim, [], B}, [4294967295], Wa.Wasm.Memory{p, lim, [], B}, e, N.le_trans(N2, 41n, F, hN, hF)))
    case Some{+p2}:
      (+N2, h1) = h
      (h2, ff) = h1
      (af.some(k, len, p, lim, B, F, hF, p2, N2, h2), ff)

# alloc(len), with the fuel F >= 41, in a memory of p pages, p not -1
def af.call(+k: U32, +len: U32, +p: U32, +lim: U32, +B: Wa.Wasm.Bytes, +F: Nat, hF: N.Le(41n, F),
  +hp: {U32.is_eq(p, 4294967295) == False{} : Bool}, +hpl: {U32.is_le(p, lim) == True{} : Bool}) ->
  AFC(Wa.Wasm.call(F, Cr.Cir.alloc(k), [len], Wa.Wasm.Memory{p, lim, [], B}), Cr.Cir.alloc.pages(k, len, p, lim), k, len, p, lim, B):
  af.call.go(Cr.Cir.alloc.pages(k, len, p, lim), k, len, p, lim, B, F, hF, af.steps(k, len, p, lim, B, hp, hpl))
