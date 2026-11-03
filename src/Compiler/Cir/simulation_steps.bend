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

# a choice of two Data types, itself Data
def OR(-A: Data, -B: Data) -> Data:
  Either<&2, &2, A, B>

# the answers left after k grows within the limit
def Drop(+k: Nat, +gs: List<&2, Bool>) -> List<&2, Bool>:
  match k:
    case 0n:
      gs
    case 1n+p:
      Drop(p, List.drop(&2, Bool, gs, 1n))

# no answers are left from no answers
def drop.nil(+k: Nat) -> {Drop(k, []) == [] : List<&2, Bool>}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      drop.nil(p)

# dropping no answers gives the answers back
def drop.zero(+gs: List<&2, Bool>) -> {List.drop(&2, Bool, gs, 0n) == gs : List<&2, Bool>}:
  match gs:
    case Nil{}:
      {==}
    case Con{_, _}:
      {==}

# dropping a + b answers is dropping a, then b
def drop.add(+a: Nat, +gs: List<&2, Bool>, +b: Nat) ->
  {Drop(Nat.add(a, b), gs) == Drop(b, Drop(a, gs)) : List<&2, Bool>}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      drop.add(p, List.drop(&2, Bool, gs, 1n), b)

# answer a + b is answer b after dropping a answers
def get.add(+a: Nat, +gs: List<&2, Bool>, +b: Nat) ->
  {List.get(&2, Bool, gs, Nat.add(a, b)) == List.get(&2, Bool, Drop(a, gs), b) : Maybe<&2, Bool>}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      match gs:
        case Nil{}:
          (%Equal.sym(List<&2, Bool>, Drop(p, []), [], drop.nil(p)) : {List.get(&2, Bool, [], Nat.add(1n+p, b)) == List.get(&2, Bool, _, b) : Maybe<&2, Bool>}; {==})
        case Con{_, r}:
          (%Equal.sym(List<&2, Bool>, List.drop(&2, Bool, r, 0n), r, drop.zero(r)) :
            {List.get(&2, Bool, r, Nat.add(p, b)) == List.get(&2, Bool, Drop(p, _), b) : Maybe<&2, Bool>}; get.add(p, r, b))

def is.someb(x: Maybe<&2, Bool>) -> Data:
  match x:
    case None{}:
      Empty
    case Some{_}:
      Unit

def none.someb(-y: Bool, e: {None{} == Some{y} : Maybe<&2, Bool>}) -> Empty:
  %Equal.sym(Maybe<&2, Bool>, None{}, Some{y}, e) : is.someb(_)
  Unit{}

# a refused grow is a false first answer
def grants.false(+gs: List<&2, Bool>, h: {Wa.Wasm.grants(gs) == False{} : Bool}) ->
  {List.get(&2, Bool, gs, 0n) == Some{False{}} : Maybe<&2, Bool>}:
  match gs:
    case Nil{}:
      Empty.absurd({List.get(&2, Bool, [], 0n) == Some{False{}} : Maybe<&2, Bool>}, N.true_ne_false(h))
    case Con{g, +rest}:
      match g:
        case False{}:
          {==}
        case True{}:
          Empty.absurd({List.get(&2, Bool, Con{True{}, rest}, 0n) == Some{False{}} : Maybe<&2, Bool>}, N.true_ne_false(h))

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
          steps.add(p, b, Wa.Wasm.step(PH.H.TS(), fr, m))
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

# a step that goes on
def is.next(st: Wa.Wasm.Step) -> Data:
  match st:
    case Wa.Wasm.Step.next{_, _}:
      Unit
    case Wa.Wasm.Step.done{_, _}:
      Empty
    case Wa.Wasm.Step.trap{_}:
      Empty

# a run that goes on for N0 steps goes on for M <= N0 steps
def next.mono(+N0: Nat, +M: Nat, +st: Wa.Wasm.Step, h: N.Le(M, N0), p: is.next(PH.H.steps(N0, st))) -> is.next(PH.H.steps(M, st)):
  match N0:
    case 0n:
      match M:
        case 0n:
          p
        case 1n+M1:
          Empty.absurd(is.next(PH.H.steps(1n+M1, st)), h)
    case 1n+N1:
      match M:
        case 0n:
          match st:
            case Wa.Wasm.Step.next{+fr, +m}:
              Unit{}
            case Wa.Wasm.Step.done{+rs, +m}:
              Empty.absurd(is.next(Wa.Wasm.Step.done{rs, m}), p)
            case Wa.Wasm.Step.trap{+m}:
              Empty.absurd(is.next(Wa.Wasm.Step.trap{m}), p)
        case 1n+M1:
          match st:
            case Wa.Wasm.Step.next{+fr, +m}:
              next.mono(N1, M1, Wa.Wasm.step(PH.H.TS(), fr, m), h, p)
            case Wa.Wasm.Step.done{+rs, +m}:
              Empty.absurd(is.next(PH.H.steps(1n+M1, Wa.Wasm.Step.done{rs, m})), p)
            case Wa.Wasm.Step.trap{+m}:
              Empty.absurd(is.next(PH.H.steps(1n+M1, Wa.Wasm.Step.trap{m})), p)

# a steps reach st1, and b more go on: a + b steps go on
def next.then(+a: Nat, +b: Nat, +st: Wa.Wasm.Step, -st1: Wa.Wasm.Step, e: {PH.H.steps(a, st) == st1 : Wa.Wasm.Step},
  p: is.next(PH.H.steps(b, st1))) -> is.next(PH.H.steps(Nat.add(a, b), st)):
  %Equal.sym(Wa.Wasm.Step, PH.H.steps(Nat.add(a, b), st), PH.H.steps(b, PH.H.steps(a, st)), steps.add(a, b, st)) : is.next(_)
  (%Equal.sym(Wa.Wasm.Step, PH.H.steps(a, st), st1, e) : is.next(PH.H.steps(b, _)); p)

# a run that goes on for fui steps after N0 steps goes on for fu <= N0 + fui steps
def next.wrap(+fu: Nat, +fui: Nat, +N0: Nat, +st: Wa.Wasm.Step, -st1: Wa.Wasm.Step, hf: N.Le(fu, Nat.add(N0, fui)),
  e: {PH.H.steps(N0, st) == st1 : Wa.Wasm.Step}, p: is.next(PH.H.steps(fui, st1))) -> is.next(PH.H.steps(fu, st)):
  next.mono(Nat.add(N0, fui), fu, st, hf, next.then(N0, fui, st, st1, e, p))

# a run from the frame fr, whose first two steps reach Yv, goes on for f steps: a run from the frame fb, whose
# first step reaches Yv, goes on for f - 1 steps
def next.skip(+f: Nat, +fr: Wa.Wasm.Frame, +mm: Wa.Wasm.Memory, +fr1: Wa.Wasm.Frame, +m1: Wa.Wasm.Memory, +Yv: Wa.Wasm.Step,
  +fb: Wa.Wasm.Frame, +mb: Wa.Wasm.Memory,
  h1: {Wa.Wasm.step(PH.H.TS(), fr, mm) == Wa.Wasm.Step.next{fr1, m1} : Wa.Wasm.Step},
  h2: {Wa.Wasm.step(PH.H.TS(), fr1, m1) == Yv : Wa.Wasm.Step},
  hb: {Wa.Wasm.step(PH.H.TS(), fb, mb) == Yv : Wa.Wasm.Step},
  p: is.next(PH.H.steps(f, Wa.Wasm.Step.next{fr, mm}))) -> is.next(PH.H.steps(Nat.sub(f, 1n), Wa.Wasm.Step.next{fb, mb})):
  match f:
    case 0n:
      Unit{}
    case 1n+f1:
      match f1:
        case 0n:
          Unit{}
        case 1n+f2:
          (%Equal.sym(Wa.Wasm.Step, Wa.Wasm.step(PH.H.TS(), fb, mb), Yv, hb) : is.next(PH.H.steps(f2, _));
            (%h2 : is.next(PH.H.steps(f2, _)); (%h1 : is.next(PH.H.steps(1n+f2, _)); p)))

# Calls
# -----

# what the call from st gives with the fuel F, when the run from st ends
# after n steps with the results rs and the memory m2
def GD(F: Nat, st: Wa.Wasm.Step, -rs: List<&2, U32>, -m2: Wa.Wasm.Memory, n: Nat) -> Data:
  match st:
    case Wa.Wasm.Step.next{fr, m}:
      EX(j => P2({Wa.Wasm.call.go(F, PH.H.TS(), fr, m) == Wa.Wasm.Call.done{rs, m2, j} : Wa.Wasm.Call}, N.Le(j, n)))
    case Wa.Wasm.Step.done{rs1, m1}:
      P2({rs1 == rs : List<&2, U32>}, {m1 == m2 : Wa.Wasm.Memory})
    case Wa.Wasm.Step.trap{_}:
      Empty

def gd.stepped(F1: Nat, st: Wa.Wasm.Step, -rs: List<&2, U32>, -m2: Wa.Wasm.Memory, +n: Nat, q: GD(F1, st, rs, m2, n)) ->
  EX(j => P2({Wa.Wasm.call.stepped(st, g => mm => Wa.Wasm.call.go(F1, PH.H.TS(), g, mm)) == Wa.Wasm.Call.done{rs, m2, j} : Wa.Wasm.Call},
    N.Le(j, 1n+n))):
  match st:
    case Wa.Wasm.Step.next{g, mm}:
      (+j, r) = q
      (eq, le) = r
      (1n+j, (Equal.cong(Wa.Wasm.Call, Wa.Wasm.Call, c => Wa.Wasm.call.plus(c), Wa.Wasm.call.go(F1, PH.H.TS(), g, mm),
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
              gd.stepped(F1, Wa.Wasm.step(PH.H.TS(), fr, m), rs, m2, p, gd.ext(p, Wa.Wasm.step(PH.H.TS(), fr, m), F1, rs, m2, e, h))
        case Wa.Wasm.Step.done{rs1, m1}:
          gd.done(rs1, m1, rs, m2, e)
        case Wa.Wasm.Step.trap{m}:
          Empty.absurd(GD(F, Wa.Wasm.Step.trap{m}, rs, m2, 1n+p), trap.not_done(m, rs, m2, e))

# a call of a running frame that ends after n steps, with any fuel F >= n
def run.call(+n: Nat, +F: Nat, +fr: Wa.Wasm.Frame, +m: Wa.Wasm.Memory, -rs: List<&2, U32>, -m2: Wa.Wasm.Memory,
  e: {PH.H.steps(n, Wa.Wasm.Step.next{fr, m}) == Wa.Wasm.Step.done{rs, m2} : Wa.Wasm.Step}, h: N.Le(n, F)) ->
  EX(j => P2({Wa.Wasm.call.go(F, PH.H.TS(), fr, m) == Wa.Wasm.Call.done{rs, m2, j} : Wa.Wasm.Call}, N.Le(j, n))):
  gd.ext(n, Wa.Wasm.Step.next{fr, m}, F, rs, m2, e, h)

# the call of a step s that goes on for N0 steps, in a fuel F <= N0, is not done
def call.nd.go(+F: Nat, +N0: Nat, +s: Wa.Wasm.Step, h: N.Le(F, N0), p: is.next(PH.H.steps(N0, s))) ->
  {Wa.Wasm.call.stepped(s, g => m => Wa.Wasm.call.go(F, PH.H.TS(), g, m)) == Wa.Wasm.Call.not_done{} : Wa.Wasm.Call}:
  match F:
    case 0n:
      match s:
        case Wa.Wasm.Step.next{+g, +mm}:
          {==}
        case Wa.Wasm.Step.done{+rs, +mm}:
          Empty.absurd({Wa.Wasm.call.stepped(Wa.Wasm.Step.done{rs, mm}, g => m => Wa.Wasm.call.go(0n, PH.H.TS(), g, m)) == Wa.Wasm.Call.not_done{} : Wa.Wasm.Call},
            (%steps.done(N0, rs, mm) : is.next(_); p))
        case Wa.Wasm.Step.trap{+mm}:
          Empty.absurd({Wa.Wasm.call.stepped(Wa.Wasm.Step.trap{mm}, g => m => Wa.Wasm.call.go(0n, PH.H.TS(), g, m)) == Wa.Wasm.Call.not_done{} : Wa.Wasm.Call},
            (%steps.trap(N0, mm) : is.next(_); p))
    case 1n+F1:
      match N0:
        case 0n:
          Empty.absurd({Wa.Wasm.call.stepped(s, g => m => Wa.Wasm.call.go(1n+F1, PH.H.TS(), g, m)) == Wa.Wasm.Call.not_done{} : Wa.Wasm.Call}, h)
        case 1n+N1:
          match s:
            case Wa.Wasm.Step.next{+g, +mm}:
              Equal.cong(Wa.Wasm.Call, Wa.Wasm.Call, c => Wa.Wasm.call.plus(c), Wa.Wasm.call.go(1n+F1, PH.H.TS(), g, mm), Wa.Wasm.Call.not_done{},
                call.nd.go(F1, N1, Wa.Wasm.step(PH.H.TS(), g, mm), h, p))
            case Wa.Wasm.Step.done{+rs, +mm}:
              Empty.absurd({Wa.Wasm.call.stepped(Wa.Wasm.Step.done{rs, mm}, g => m => Wa.Wasm.call.go(1n+F1, PH.H.TS(), g, m)) == Wa.Wasm.Call.not_done{} : Wa.Wasm.Call}, p)
            case Wa.Wasm.Step.trap{+mm}:
              Empty.absurd({Wa.Wasm.call.stepped(Wa.Wasm.Step.trap{mm}, g => m => Wa.Wasm.call.go(1n+F1, PH.H.TS(), g, m)) == Wa.Wasm.Call.not_done{} : Wa.Wasm.Call}, p)

# a call of a frame that goes on for N0 steps, in a fuel F <= N0, is not done
def call.nd(+F: Nat, +N0: Nat, +fr: Wa.Wasm.Frame, +m: Wa.Wasm.Memory, h: N.Le(F, N0), p: is.next(PH.H.steps(N0, Wa.Wasm.Step.next{fr, m}))) ->
  {Wa.Wasm.call.go(F, PH.H.TS(), fr, m) == Wa.Wasm.Call.not_done{} : Wa.Wasm.Call}:
  match F:
    case 0n:
      {==}
    case 1n+F1:
      match N0:
        case 0n:
          Empty.absurd({Wa.Wasm.call.go(1n+F1, PH.H.TS(), fr, m) == Wa.Wasm.Call.not_done{} : Wa.Wasm.Call}, h)
        case 1n+N1:
          call.nd.go(F1, N1, Wa.Wasm.step(PH.H.TS(), fr, m), h, p)
