# compiler: more fuel keeps an outcome
# ===================================
#
# A run that ends (anything but not_done) with the fuel f ends the same with
# the fuel f + g. A call that ends with some fuel ends the same with more
# fuel, in the same steps, which are at most its fuel; the host gives run the
# steps that alloc left, Nat.sub(f, used), and with f + g it gives
# Nat.sub(f, used) + g, as used <= f.

import Base
import ../../Wasm/impl.bend as Wa
import ../need_big.bend as PN

# the outcome ends: anything but not_done
def done(x: Wa.Wasm.Outcome) -> Bool:
  match x:
    case Wa.Wasm.Outcome.not_done{}:
      False{}
    case _:
      True{}

# Monotony relations: a ends gives b == a
# ---------------------------------------

def CM(a: Wa.Wasm.Call, b: Wa.Wasm.Call) -> Type:
  match a:
    case Wa.Wasm.Call.done{rs, m, n}:
      {Wa.Wasm.Call.done{rs, m, n} == b : Wa.Wasm.Call}
    case Wa.Wasm.Call.trap{m}:
      {Wa.Wasm.Call.trap{m} == b : Wa.Wasm.Call}
    case Wa.Wasm.Call.not_done{}:
      Unit

# a done call took at most k steps
def CB(k: Nat, a: Wa.Wasm.Call) -> Type:
  match a:
    case Wa.Wasm.Call.done{_, _, n}:
      PN.Le(n, k)
    case Wa.Wasm.Call.trap{_}:
      Unit
    case Wa.Wasm.Call.not_done{}:
      Unit

def IM(a: Wa.Wasm.Invoked, b: Wa.Wasm.Invoked) -> Type:
  match a:
    case Wa.Wasm.Invoked.values{vs, i, n}:
      {Wa.Wasm.Invoked.values{vs, i, n} == b : Wa.Wasm.Invoked}
    case Wa.Wasm.Invoked.trap{i}:
      {Wa.Wasm.Invoked.trap{i} == b : Wa.Wasm.Invoked}
    case Wa.Wasm.Invoked.not_done{}:
      Unit
    case Wa.Wasm.Invoked.unsupported{}:
      {Wa.Wasm.Invoked.unsupported{} == b : Wa.Wasm.Invoked}

def IB(k: Nat, a: Wa.Wasm.Invoked) -> Type:
  match a:
    case Wa.Wasm.Invoked.values{_, _, n}:
      PN.Le(n, k)
    case Wa.Wasm.Invoked.trap{_}:
      Unit
    case Wa.Wasm.Invoked.not_done{}:
      Unit
    case Wa.Wasm.Invoked.unsupported{}:
      Unit

def OM(a: Wa.Wasm.Outcome, b: Wa.Wasm.Outcome) -> Type:
  match a:
    case Wa.Wasm.Outcome.result{bs}:
      {Wa.Wasm.Outcome.result{bs} == b : Wa.Wasm.Outcome}
    case Wa.Wasm.Outcome.out_of_memory{}:
      {Wa.Wasm.Outcome.out_of_memory{} == b : Wa.Wasm.Outcome}
    case Wa.Wasm.Outcome.no_result{}:
      {Wa.Wasm.Outcome.no_result{} == b : Wa.Wasm.Outcome}
    case Wa.Wasm.Outcome.unsupported{}:
      {Wa.Wasm.Outcome.unsupported{} == b : Wa.Wasm.Outcome}
    case Wa.Wasm.Outcome.trap{}:
      {Wa.Wasm.Outcome.trap{} == b : Wa.Wasm.Outcome}
    case Wa.Wasm.Outcome.not_done{}:
      Unit

def OM.refl(x: Wa.Wasm.Outcome) -> OM(x, x):
  match x:
    case Wa.Wasm.Outcome.result{bs}:
      {==}
    case Wa.Wasm.Outcome.out_of_memory{}:
      {==}
    case Wa.Wasm.Outcome.no_result{}:
      {==}
    case Wa.Wasm.Outcome.unsupported{}:
      {==}
    case Wa.Wasm.Outcome.trap{}:
      {==}
    case Wa.Wasm.Outcome.not_done{}:
      Unit{}

# Nat
# ---

# (f - u) + g = (f + g) - u, when u <= f
def sub_add(+f: Nat, +u: Nat, h: PN.Le(u, f), +g: Nat) -> {Nat.add(Nat.sub(f, u), g) == Nat.sub(Nat.add(f, g), u) : Nat}:
  match f:
    case 0n:
      match u:
        case 0n:
          match g:
            case 0n:
              {==}
            case 1n+q:
              {==}
        case 1n+v:
          Empty.absurd({Nat.add(Nat.sub(0n, 1n+v), g) == Nat.sub(Nat.add(0n, g), 1n+v) : Nat}, h)
    case 1n+p:
      match u:
        case 0n:
          {==}
        case 1n+v:
          sub_add(p, v, h, g)

# Calls
# -----

def CM.plus(c: Wa.Wasm.Call, -d: Wa.Wasm.Call, h: CM(c, d)) -> CM(Wa.Wasm.call.plus(c), Wa.Wasm.call.plus(d)):
  match c:
    case Wa.Wasm.Call.done{+rs, +m, +n}:
      %h : {Wa.Wasm.Call.done{rs, m, 1n+n} == Wa.Wasm.call.plus(_) : Wa.Wasm.Call}
      {==}
    case Wa.Wasm.Call.trap{+m}:
      %h : {Wa.Wasm.Call.trap{m} == Wa.Wasm.call.plus(_) : Wa.Wasm.Call}
      {==}
    case Wa.Wasm.Call.not_done{}:
      Unit{}

def CB.plus(+k: Nat, c: Wa.Wasm.Call, h: CB(k, c)) -> CB(1n+k, Wa.Wasm.call.plus(c)):
  match c:
    case Wa.Wasm.Call.done{rs, m, n}:
      h
    case Wa.Wasm.Call.trap{m}:
      h
    case Wa.Wasm.Call.not_done{}:
      h

# the steps after st, with the fuel k and k + g
def go.st(+k: Nat, +g: Nat, st: Wa.Wasm.Step) ->
  CM(Wa.Wasm.call.stepped(st, fr => mm => Wa.Wasm.call.go(k, fr, mm)),
     Wa.Wasm.call.stepped(st, fr => mm => Wa.Wasm.call.go(Nat.add(k, g), fr, mm))):
  match k:
    case 0n:
      match st:
        case Wa.Wasm.Step.next{+fr, +m}:
          Unit{}
        case Wa.Wasm.Step.done{+rs, +m}:
          {==}
        case Wa.Wasm.Step.trap{+m}:
          {==}
    case 1n+p:
      match st:
        case Wa.Wasm.Step.next{+fr, +m}:
          CM.plus(Wa.Wasm.call.go(1n+p, fr, m), Wa.Wasm.call.go(Nat.add(1n+p, g), fr, m), go.st(p, g, Wa.Wasm.step(fr, m)))
        case Wa.Wasm.Step.done{+rs, +m}:
          {==}
        case Wa.Wasm.Step.trap{+m}:
          {==}

def go.more(+k: Nat, +g: Nat, +f: Wa.Wasm.Frame, +mem: Wa.Wasm.Memory) ->
  CM(Wa.Wasm.call.go(k, f, mem), Wa.Wasm.call.go(Nat.add(k, g), f, mem)):
  match k:
    case 0n:
      Unit{}
    case 1n+p:
      go.st(p, g, Wa.Wasm.step(f, mem))

def go.st.bound(+k: Nat, st: Wa.Wasm.Step) ->
  CB(1n+k, Wa.Wasm.call.stepped(st, fr => mm => Wa.Wasm.call.go(k, fr, mm))):
  match k:
    case 0n:
      match st:
        case Wa.Wasm.Step.next{+fr, +m}:
          Unit{}
        case Wa.Wasm.Step.done{rs, m}:
          Unit{}
        case Wa.Wasm.Step.trap{m}:
          Unit{}
    case 1n+p:
      match st:
        case Wa.Wasm.Step.next{+fr, +m}:
          CB.plus(1n+p, Wa.Wasm.call.go(1n+p, fr, m), go.st.bound(p, Wa.Wasm.step(fr, m)))
        case Wa.Wasm.Step.done{rs, m}:
          Unit{}
        case Wa.Wasm.Step.trap{m}:
          Unit{}

def go.bound(+k: Nat, +f: Wa.Wasm.Frame, +mem: Wa.Wasm.Memory) -> CB(k, Wa.Wasm.call.go(k, f, mem)):
  match k:
    case 0n:
      Unit{}
    case 1n+p:
      go.st.bound(p, Wa.Wasm.step(f, mem))

def call.more(+k: Nat, +g: Nat, func: Wa.Wasm.Func, +args: List<&2, U32>, +mem: Wa.Wasm.Memory) ->
  CM(Wa.Wasm.call(k, func, args, mem), Wa.Wasm.call(Nat.add(k, g), func, args, mem)):
  match func:
    case Wa.Wasm.Func{a, +q, +n, +body}:
      go.more(k, g, Wa.Wasm.Frame{body, Nil{}, q, Nil{}, List.append(&2, U32, args, List.replicate(U32, n, 0))}, mem)

def call.bound(+k: Nat, func: Wa.Wasm.Func, +args: List<&2, U32>, +mem: Wa.Wasm.Memory) ->
  CB(k, Wa.Wasm.call(k, func, args, mem)):
  match func:
    case Wa.Wasm.Func{a, +q, +n, +body}:
      go.bound(k, Wa.Wasm.Frame{body, Nil{}, q, Nil{}, List.append(&2, U32, args, List.replicate(U32, n, 0))}, mem)

# Invocations
# -----------

def invoked.more(c: Wa.Wasm.Call, -d: Wa.Wasm.Call, h: CM(c, d), +module: Wa.Wasm.Module) ->
  IM(Wa.Wasm.invoked(c, module), Wa.Wasm.invoked(d, module)):
  match c:
    case Wa.Wasm.Call.done{+rs, +m, +n}:
      %h : IM(Wa.Wasm.invoked(Wa.Wasm.Call.done{rs, m, n}, module), Wa.Wasm.invoked(_, module))
      {==}
    case Wa.Wasm.Call.trap{+m}:
      %h : IM(Wa.Wasm.invoked(Wa.Wasm.Call.trap{m}, module), Wa.Wasm.invoked(_, module))
      {==}
    case Wa.Wasm.Call.not_done{}:
      Unit{}

def invoked.bound(-k: Nat, c: Wa.Wasm.Call, h: CB(k, c), -module: Wa.Wasm.Module) ->
  IB(k, Wa.Wasm.invoked(c, module)):
  match c:
    case Wa.Wasm.Call.done{rs, m, n}:
      h
    case Wa.Wasm.Call.trap{m}:
      h
    case Wa.Wasm.Call.not_done{}:
      h

def arity.more(ok: Bool, +fn: Wa.Wasm.Func, +k: Nat, +g: Nat, +args: List<&2, U32>, +mem: Wa.Wasm.Memory, +module: Wa.Wasm.Module) ->
  IM(Wa.Wasm.invoke.arity(ok, fn, k, args, mem, module), Wa.Wasm.invoke.arity(ok, fn, Nat.add(k, g), args, mem, module)):
  match ok:
    case True{}:
      invoked.more(Wa.Wasm.call(k, fn, args, mem), Wa.Wasm.call(Nat.add(k, g), fn, args, mem), call.more(k, g, fn, args, mem), module)
    case False{}:
      {==}

def arity.bound(ok: Bool, +fn: Wa.Wasm.Func, +k: Nat, +args: List<&2, U32>, +mem: Wa.Wasm.Memory, +module: Wa.Wasm.Module) ->
  IB(k, Wa.Wasm.invoke.arity(ok, fn, k, args, mem, module)):
  match ok:
    case True{}:
      invoked.bound(k, Wa.Wasm.call(k, fn, args, mem), call.bound(k, fn, args, mem), module)
    case False{}:
      Unit{}

def found.more(fm: Maybe<&2, Wa.Wasm.Func>, +k: Nat, +g: Nat, +args: List<&2, U32>, +mem: Wa.Wasm.Memory, +module: Wa.Wasm.Module) ->
  IM(Wa.Wasm.invoke.found(fm, k, args, mem, module), Wa.Wasm.invoke.found(fm, Nat.add(k, g), args, mem, module)):
  match fm:
    case None{}:
      {==}
    case Some{fn}:
      match fn:
        case Wa.Wasm.Func{+p, +q, +n, +body}:
          arity.more(Nat.is_eq(p, List.length(&2, U32, args)), Wa.Wasm.Func{p, q, n, body}, k, g, args, mem, module)

def found.bound(fm: Maybe<&2, Wa.Wasm.Func>, +k: Nat, +args: List<&2, U32>, +mem: Wa.Wasm.Memory, +module: Wa.Wasm.Module) ->
  IB(k, Wa.Wasm.invoke.found(fm, k, args, mem, module)):
  match fm:
    case None{}:
      Unit{}
    case Some{fn}:
      match fn:
        case Wa.Wasm.Func{+p, +q, +n, +body}:
          arity.bound(Nat.is_eq(p, List.length(&2, U32, args)), Wa.Wasm.Func{p, q, n, body}, k, args, mem, module)

def invoke.more(+k: Nat, +g: Nat, inst: Wa.Wasm.Instance, +name: List<&2, Word(8n)>, +args: List<&2, U32>) ->
  IM(Wa.Wasm.invoke(k, inst, name, args), Wa.Wasm.invoke(Nat.add(k, g), inst, name, args)):
  match inst:
    case Wa.Wasm.Instance{module, +mem}:
      match module:
        case Wa.Wasm.Module{+fs, +memory, +es, +seg}:
          found.more(Wa.Wasm.export.func(fs, es, name), k, g, args, mem, Wa.Wasm.Module{fs, memory, es, seg})

def invoke.bound(+k: Nat, inst: Wa.Wasm.Instance, +name: List<&2, Word(8n)>, +args: List<&2, U32>) ->
  IB(k, Wa.Wasm.invoke(k, inst, name, args)):
  match inst:
    case Wa.Wasm.Instance{module, +mem}:
      match module:
        case Wa.Wasm.Module{+fs, +memory, +es, +seg}:
          found.bound(Wa.Wasm.export.func(fs, es, name), k, args, mem, Wa.Wasm.Module{fs, memory, es, seg})

# The host
# --------

def ran.more(a: Wa.Wasm.Invoked, -b: Wa.Wasm.Invoked, h: IM(a, b)) -> OM(Wa.Wasm.run.ran(a), Wa.Wasm.run.ran(b)):
  match a:
    case Wa.Wasm.Invoked.values{+vs, +inst, +n}:
      %h : OM(Wa.Wasm.run.ran(Wa.Wasm.Invoked.values{vs, inst, n}), Wa.Wasm.run.ran(_))
      OM.refl(Wa.Wasm.run.ran(Wa.Wasm.Invoked.values{vs, inst, n}))
    case Wa.Wasm.Invoked.trap{+inst}:
      %h : OM(Wa.Wasm.run.ran(Wa.Wasm.Invoked.trap{inst}), Wa.Wasm.run.ran(_))
      {==}
    case Wa.Wasm.Invoked.not_done{}:
      Unit{}
    case Wa.Wasm.Invoked.unsupported{}:
      %h : OM(Wa.Wasm.run.ran(Wa.Wasm.Invoked.unsupported{}), Wa.Wasm.run.ran(_))
      {==}

def written.more(ok: Bool, +f: Nat, +g: Nat, +inst: Wa.Wasm.Instance, +a: U32, +n: U32) ->
  OM(Wa.Wasm.run.written(ok, f, inst, a, n), Wa.Wasm.run.written(ok, Nat.add(f, g), inst, a, n)):
  match ok:
    case True{}:
      ran.more(Wa.Wasm.invoke(f, inst, Wa.Wasm.name.run(), [a, n]), Wa.Wasm.invoke(Nat.add(f, g), inst, Wa.Wasm.name.run(), [a, n]),
        invoke.more(f, g, inst, Wa.Wasm.name.run(), [a, n]))
    case False{}:
      {==}

def input.more(+f: Nat, +g: Nat, inst: Wa.Wasm.Instance, +a: U32, +n: U32, +i: List<&2, Word(8n)>) ->
  OM(Wa.Wasm.run.input(f, inst, a, n, i), Wa.Wasm.run.input(Nat.add(f, g), inst, a, n, i)):
  match inst:
    case Wa.Wasm.Instance{+module, mem}:
      match mem:
        case Wa.Wasm.Memory{+p, +lim, +bytes}:
          written.more(Wa.Wasm.fits(p, a, n), f, g,
            Wa.Wasm.Instance{module, Wa.Wasm.Memory{p, lim, Wa.Wasm.write.bytes(i, a, bytes)}}, a, n)

def alloced.if.more(full: Bool, +f: Nat, +g: Nat, +inst: Wa.Wasm.Instance, +a: U32, +n: U32, +i: List<&2, Word(8n)>) ->
  OM(Wa.Wasm.run.alloced.if(full, f, inst, a, n, i), Wa.Wasm.run.alloced.if(full, Nat.add(f, g), inst, a, n, i)):
  match full:
    case True{}:
      {==}
    case False{}:
      input.more(f, g, inst, a, n, i)

def alloced.more(+f: Nat, +g: Nat, r: Wa.Wasm.Invoked, -s: Wa.Wasm.Invoked, h: IM(r, s), hb: IB(f, r), +k: U32, +i: List<&2, Word(8n)>) ->
  OM(Wa.Wasm.run.alloced(r, f, k, i), Wa.Wasm.run.alloced(s, Nat.add(f, g), k, i)):
  match r:
    case Wa.Wasm.Invoked.values{vs, +inst, +used}:
      match vs:
        case Nil{}:
          %h : OM(Wa.Wasm.run.alloced(Wa.Wasm.Invoked.values{Nil{}, inst, used}, f, k, i), Wa.Wasm.run.alloced(_, Nat.add(f, g), k, i))
          {==}
        case Con{+a, +rest}:
          %h : OM(Wa.Wasm.run.alloced(Wa.Wasm.Invoked.values{Con{a, rest}, inst, used}, f, k, i), Wa.Wasm.run.alloced(_, Nat.add(f, g), k, i))
          %sub_add(f, used, hb, g) : OM(Wa.Wasm.run.alloced.if(U32.is_eq(a, 4294967295), Nat.sub(f, used), inst, a, k, i),
            Wa.Wasm.run.alloced.if(U32.is_eq(a, 4294967295), _, inst, a, k, i))
          alloced.if.more(U32.is_eq(a, 4294967295), Nat.sub(f, used), g, inst, a, k, i)
    case Wa.Wasm.Invoked.trap{+inst}:
      %h : OM(Wa.Wasm.run.alloced(Wa.Wasm.Invoked.trap{inst}, f, k, i), Wa.Wasm.run.alloced(_, Nat.add(f, g), k, i))
      {==}
    case Wa.Wasm.Invoked.not_done{}:
      Unit{}
    case Wa.Wasm.Invoked.unsupported{}:
      %h : OM(Wa.Wasm.run.alloced(Wa.Wasm.Invoked.unsupported{}, f, k, i), Wa.Wasm.run.alloced(_, Nat.add(f, g), k, i))
      {==}

def sized.more(n: Maybe<&2, U32>, +f: Nat, +g: Nat, +inst: Wa.Wasm.Instance, +i: List<&2, Word(8n)>) ->
  OM(Wa.Wasm.run.sized(n, f, inst, i), Wa.Wasm.run.sized(n, Nat.add(f, g), inst, i)):
  match n:
    case None{}:
      {==}
    case Some{+k}:
      alloced.more(f, g, Wa.Wasm.invoke(f, inst, Wa.Wasm.name.alloc(), [k]), Wa.Wasm.invoke(Nat.add(f, g), inst, Wa.Wasm.name.alloc(), [k]),
        invoke.more(f, g, inst, Wa.Wasm.name.alloc(), [k]), invoke.bound(f, inst, Wa.Wasm.name.alloc(), [k]), k, i)

def instance.more(ok: Bool, +f: Nat, +g: Nat, +inst: Wa.Wasm.Instance, +i: List<&2, Word(8n)>) ->
  OM(Wa.Wasm.run.instance(ok, f, inst, i), Wa.Wasm.run.instance(ok, Nat.add(f, g), inst, i)):
  match ok:
    case True{}:
      sized.more(Wa.Wasm.length32(i), f, g, inst, i)
    case False{}:
      {==}

def made.more(+f: Nat, +g: Nat, made: Wa.Wasm.Made, +i: List<&2, Word(8n)>) ->
  OM(Wa.Wasm.run.made(f, made, i), Wa.Wasm.run.made(Nat.add(f, g), made, i)):
  match made:
    case Wa.Wasm.Made.instance{+inst}:
      instance.more(Wa.Wasm.run.is_host(inst), f, g, inst, i)
    case Wa.Wasm.Made.unsupported{}:
      {==}
    case Wa.Wasm.Made.out_of_memory{}:
      {==}
    case Wa.Wasm.Made.trap{}:
      {==}

def run.om(+f: Nat, +g: Nat, +w: List<&2, Word(8n)>, +i: List<&2, Word(8n)>, +m: U32) ->
  OM(Wa.Wasm.run(f, w, i, m), Wa.Wasm.run(Nat.add(f, g), w, i, m)):
  made.more(f, g, Wa.Wasm.instantiate(w, m), i)

# The lemma
# ---------

def OM.rw(-a: Wa.Wasm.Outcome, -x: Wa.Wasm.Outcome, -b: Wa.Wasm.Outcome, e: {a == x : Wa.Wasm.Outcome}, h: OM(a, b)) -> OM(x, b):
  %e : OM(_, b)
  h

def OM.use(x: Wa.Wasm.Outcome, -b: Wa.Wasm.Outcome, nd: {done(x) == True{} : Bool}, h: OM(x, b)) -> {b == x : Wa.Wasm.Outcome}:
  match x:
    case Wa.Wasm.Outcome.result{+bs}:
      Equal.sym(Wa.Wasm.Outcome, Wa.Wasm.Outcome.result{bs}, b, h)
    case Wa.Wasm.Outcome.out_of_memory{}:
      Equal.sym(Wa.Wasm.Outcome, Wa.Wasm.Outcome.out_of_memory{}, b, h)
    case Wa.Wasm.Outcome.no_result{}:
      Equal.sym(Wa.Wasm.Outcome, Wa.Wasm.Outcome.no_result{}, b, h)
    case Wa.Wasm.Outcome.unsupported{}:
      Equal.sym(Wa.Wasm.Outcome, Wa.Wasm.Outcome.unsupported{}, b, h)
    case Wa.Wasm.Outcome.trap{}:
      Equal.sym(Wa.Wasm.Outcome, Wa.Wasm.Outcome.trap{}, b, h)
    case Wa.Wasm.Outcome.not_done{}:
      Empty.absurd({b == Wa.Wasm.Outcome.not_done{} : Wa.Wasm.Outcome}, PN.false_ne_true(nd))

# more fuel never changes an outcome that is not not_done
def run.more(+f: Nat, +g: Nat, +w: List<&2, Word(8n)>, +i: List<&2, Word(8n)>, +m: U32, +x: Wa.Wasm.Outcome,
  nd: {done(x) == True{} : Bool},
  e: {Wa.Wasm.run(f, w, i, m) == x : Wa.Wasm.Outcome}
) -> {Wa.Wasm.run(Nat.add(f, g), w, i, m) == x : Wa.Wasm.Outcome}:
  OM.use(x, Wa.Wasm.run(Nat.add(f, g), w, i, m), nd,
    OM.rw(Wa.Wasm.run(f, w, i, m), x, Wa.Wasm.run(Nat.add(f, g), w, i, m), e, run.om(f, g, w, i, m)))
