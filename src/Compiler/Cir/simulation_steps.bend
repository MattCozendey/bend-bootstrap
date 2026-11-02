# compiler: steps of the model's calls
# ====================================
#
# The simulation (simulation_*.bend) runs the model's functions by PH.H.steps(n,
# st), n steps of a running function (halt.bend), and composes runs by
# steps.then: n steps then m steps are n + m steps. A run that ends after n
# steps gives the call's end, with any fuel F >= n (run.call): the results,
# the memory, and some count of steps j <= n.

import Base
import ../../Wasm/impl.bend as Wa
import ../need_big.bend as N
import ./halt.bend as PH

# Kit
# ---

# a pair of two Data types, itself Data
def P2(-A: Data, -B: Data) -> Data:
  Sigma<&2, &2, A, _ => B>

# a Nat with a property, as Data
def EX(-B: Nat -> Data) -> Data:
  Sigma<&2, &2, Nat, j => B(j)>

# a step that is done
def is.done(st: Wa.Wasm.Step) -> Data:
  match st:
    case Wa.Wasm.Step.done{_, _}:
      Unit
    case Wa.Wasm.Step.next{_, _}:
      Empty
    case Wa.Wasm.Step.trap{_}:
      Empty

def done.rs(st: Wa.Wasm.Step) -> List<&2, U32>:
  match st:
    case Wa.Wasm.Step.done{rs, _}:
      rs
    case _:
      []

def done.mem(st: Wa.Wasm.Step) -> Wa.Wasm.Memory:
  match st:
    case Wa.Wasm.Step.done{_, m}:
      m
    case _:
      Wa.Wasm.Memory{0, 0, [], Wa.Wasm.Bytes.zero{}}

# a running frame is not done
def next.not_done(-fr: Wa.Wasm.Frame, -m: Wa.Wasm.Memory, -rs: List<&2, U32>, -m2: Wa.Wasm.Memory,
  e: {Wa.Wasm.Step.next{fr, m} == Wa.Wasm.Step.done{rs, m2} : Wa.Wasm.Step}) -> Empty:
  %Equal.sym(Wa.Wasm.Step, Wa.Wasm.Step.next{fr, m}, Wa.Wasm.Step.done{rs, m2}, e) : is.done(_)
  Unit{}

# a trap is not done
def trap.not_done(-m: Wa.Wasm.Memory, -rs: List<&2, U32>, -m2: Wa.Wasm.Memory,
  e: {Wa.Wasm.Step.trap{m} == Wa.Wasm.Step.done{rs, m2} : Wa.Wasm.Step}) -> Empty:
  %Equal.sym(Wa.Wasm.Step, Wa.Wasm.Step.trap{m}, Wa.Wasm.Step.done{rs, m2}, e) : is.done(_)
  Unit{}

# Steps
# -----

# a function that ended stays ended
def steps.done(n: Nat, -rs: List<&2, U32>, -m: Wa.Wasm.Memory) ->
  {PH.H.steps(n, Wa.Wasm.Step.done{rs, m}) == Wa.Wasm.Step.done{rs, m} : Wa.Wasm.Step}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def steps.trap(n: Nat, -m: Wa.Wasm.Memory) -> {PH.H.steps(n, Wa.Wasm.Step.trap{m}) == Wa.Wasm.Step.trap{m} : Wa.Wasm.Step}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

# a + b steps are a steps, then b steps
def steps.add(a: Nat, +b: Nat, +st: Wa.Wasm.Step) ->
  {PH.H.steps(Nat.add(a, b), st) == PH.H.steps(b, PH.H.steps(a, st)) : Wa.Wasm.Step}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      match st:
        case Wa.Wasm.Step.next{+fr, +m}:
          steps.add(p, b, Wa.Wasm.step(fr, m))
        case Wa.Wasm.Step.done{+rs, +m}:
          Equal.sym(Wa.Wasm.Step, PH.H.steps(b, Wa.Wasm.Step.done{rs, m}), Wa.Wasm.Step.done{rs, m}, steps.done(b, rs, m))
        case Wa.Wasm.Step.trap{+m}:
          Equal.sym(Wa.Wasm.Step, PH.H.steps(b, Wa.Wasm.Step.trap{m}), Wa.Wasm.Step.trap{m}, steps.trap(b, m))

# a steps from st reach st1, and b more reach st2
def steps.then(+a: Nat, +b: Nat, +st: Wa.Wasm.Step, -st1: Wa.Wasm.Step, -st2: Wa.Wasm.Step,
  e1: {PH.H.steps(a, st) == st1 : Wa.Wasm.Step}, e2: {PH.H.steps(b, st1) == st2 : Wa.Wasm.Step}) ->
  {PH.H.steps(Nat.add(a, b), st) == st2 : Wa.Wasm.Step}:
  Equal.trans(Wa.Wasm.Step, PH.H.steps(Nat.add(a, b), st), PH.H.steps(b, PH.H.steps(a, st)), st2, steps.add(a, b, st),
    Equal.trans(Wa.Wasm.Step, PH.H.steps(b, PH.H.steps(a, st)), PH.H.steps(b, st1), st2,
      Equal.cong(Wa.Wasm.Step, Wa.Wasm.Step, x => PH.H.steps(b, x), PH.H.steps(a, st), st1, e1), e2))

# a run that reached a done step stays there
def steps.then_done(+a: Nat, +b: Nat, +st: Wa.Wasm.Step, -rs: List<&2, U32>, -m: Wa.Wasm.Memory,
  e1: {PH.H.steps(a, st) == Wa.Wasm.Step.done{rs, m} : Wa.Wasm.Step}) ->
  {PH.H.steps(Nat.add(a, b), st) == Wa.Wasm.Step.done{rs, m} : Wa.Wasm.Step}:
  steps.then(a, b, st, Wa.Wasm.Step.done{rs, m}, Wa.Wasm.Step.done{rs, m}, e1, steps.done(b, rs, m))

# Calls
# -----

# what the call from st gives with the fuel F, when the run from st ends
# after n steps with the results rs and the memory m2
def GD(F: Nat, st: Wa.Wasm.Step, -rs: List<&2, U32>, -m2: Wa.Wasm.Memory, n: Nat) -> Data:
  match st:
    case Wa.Wasm.Step.next{fr, m}:
      EX(j => P2({Wa.Wasm.call.go(F, fr, m) == Wa.Wasm.Call.done{rs, m2, j} : Wa.Wasm.Call}, N.Le(j, n)))
    case Wa.Wasm.Step.done{rs1, m1}:
      P2({rs1 == rs : List<&2, U32>}, {m1 == m2 : Wa.Wasm.Memory})
    case Wa.Wasm.Step.trap{_}:
      Empty

def gd.stepped(F1: Nat, st: Wa.Wasm.Step, -rs: List<&2, U32>, -m2: Wa.Wasm.Memory, +n: Nat, q: GD(F1, st, rs, m2, n)) ->
  EX(j => P2({Wa.Wasm.call.stepped(st, g => mm => Wa.Wasm.call.go(F1, g, mm)) == Wa.Wasm.Call.done{rs, m2, j} : Wa.Wasm.Call},
    N.Le(j, 1n+n))):
  match st:
    case Wa.Wasm.Step.next{g, mm}:
      (+j, r) = q
      (eq, le) = r
      (1n+j, (Equal.cong(Wa.Wasm.Call, Wa.Wasm.Call, c => Wa.Wasm.call.plus(c), Wa.Wasm.call.go(F1, g, mm),
        Wa.Wasm.Call.done{rs, m2, j}, eq), le))
    case Wa.Wasm.Step.done{rs1, m1}:
      (e1, e2) = q
      +eq = {(%Equal.sym(List<&2, U32>, rs1, rs, e1) : {Wa.Wasm.Call.done{_, m1, 1n} == Wa.Wasm.Call.done{rs, m2, 1n} : Wa.Wasm.Call};
        %Equal.sym(Wa.Wasm.Memory, m1, m2, e2) : {Wa.Wasm.Call.done{rs, _, 1n} == Wa.Wasm.Call.done{rs, m2, 1n} : Wa.Wasm.Call};
        {==}) : {Wa.Wasm.Call.done{rs1, m1, 1n} == Wa.Wasm.Call.done{rs, m2, 1n} : Wa.Wasm.Call}}
      (1n, (eq, N.le_zero(n)))
    case Wa.Wasm.Step.trap{m}:
      Empty.absurd(EX(j => P2({Wa.Wasm.Call.trap{m} == Wa.Wasm.Call.done{rs, m2, j} : Wa.Wasm.Call}, N.Le(j, 1n+n))), q)

def gd.done(-rs1: List<&2, U32>, -m1: Wa.Wasm.Memory, -rs: List<&2, U32>, -m2: Wa.Wasm.Memory,
  +e: {Wa.Wasm.Step.done{rs1, m1} == Wa.Wasm.Step.done{rs, m2} : Wa.Wasm.Step}) ->
  P2({rs1 == rs : List<&2, U32>}, {m1 == m2 : Wa.Wasm.Memory}):
  (Equal.cong(Wa.Wasm.Step, List<&2, U32>, s => done.rs(s), Wa.Wasm.Step.done{rs1, m1}, Wa.Wasm.Step.done{rs, m2}, e),
   Equal.cong(Wa.Wasm.Step, Wa.Wasm.Memory, s => done.mem(s), Wa.Wasm.Step.done{rs1, m1}, Wa.Wasm.Step.done{rs, m2}, e))

# a run that ends after n steps gives its end with any fuel F >= n
def gd.ext(+n: Nat, +st: Wa.Wasm.Step, +F: Nat, -rs: List<&2, U32>, -m2: Wa.Wasm.Memory,
  e: {PH.H.steps(n, st) == Wa.Wasm.Step.done{rs, m2} : Wa.Wasm.Step}, h: N.Le(n, F)) -> GD(F, st, rs, m2, n):
  match n:
    case 0n:
      match st:
        case Wa.Wasm.Step.next{fr, m}:
          Empty.absurd(GD(F, Wa.Wasm.Step.next{fr, m}, rs, m2, 0n), next.not_done(fr, m, rs, m2, e))
        case Wa.Wasm.Step.done{rs1, m1}:
          gd.done(rs1, m1, rs, m2, e)
        case Wa.Wasm.Step.trap{m}:
          Empty.absurd(GD(F, Wa.Wasm.Step.trap{m}, rs, m2, 0n), trap.not_done(m, rs, m2, e))
    case 1n+p:
      match st:
        case Wa.Wasm.Step.next{+fr, +m}:
          match F:
            case 0n:
              Empty.absurd(GD(0n, Wa.Wasm.Step.next{fr, m}, rs, m2, 1n+p), h)
            case 1n+F1:
              gd.stepped(F1, Wa.Wasm.step(fr, m), rs, m2, p, gd.ext(p, Wa.Wasm.step(fr, m), F1, rs, m2, e, h))
        case Wa.Wasm.Step.done{rs1, m1}:
          gd.done(rs1, m1, rs, m2, e)
        case Wa.Wasm.Step.trap{m}:
          Empty.absurd(GD(F, Wa.Wasm.Step.trap{m}, rs, m2, 1n+p), trap.not_done(m, rs, m2, e))

# a call of a running frame that ends after n steps, with any fuel F >= n
def run.call(+n: Nat, +F: Nat, +fr: Wa.Wasm.Frame, +m: Wa.Wasm.Memory, -rs: List<&2, U32>, -m2: Wa.Wasm.Memory,
  e: {PH.H.steps(n, Wa.Wasm.Step.next{fr, m}) == Wa.Wasm.Step.done{rs, m2} : Wa.Wasm.Step}, h: N.Le(n, F)) ->
  EX(j => P2({Wa.Wasm.call.go(F, fr, m) == Wa.Wasm.Call.done{rs, m2, j} : Wa.Wasm.Call}, N.Le(j, n))):
  gd.ext(n, Wa.Wasm.Step.next{fr, m}, F, rs, m2, e, h)
