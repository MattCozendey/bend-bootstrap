# compiler: layer B1, the proofs of logic/spec.bend
# =================================================
#
# One def per law of logic/spec.bend. A def whose body is ?TODO is still
# open. The route: exec.more by induction on the fuel, then on the statement
# (as definitions.bend's mono at 4ebef88); tot.of_wp and wp.of_tot by
# induction on the statement, with exec.more to join the fuels of a
# sequence's parts; tot.while by induction on the measure; the accessor laws
# by matching the state.

import Base
import ../../../Shared/shared.bend as Sd
import ../shared.bend as K
import ../../../Wasm/impl.bend as Wa
import ../../need_big.bend as N
import ../../Cir/impl.bend as Cr
import ./spec.bend as Lg

# Kit
# ---

# the run ends: anything but out of fuel
def lg.Ends(o: Cr.Cir.Out) -> Data:
  match o:
    case Cr.Cir.Out.next{_}:
      Unit
    case Cr.Cir.Out.halt{_, _}:
      Unit
    case Cr.Cir.Out.out_of_memory{}:
      Unit
    case Cr.Cir.Out.trap{}:
      Unit
    case Cr.Cir.Out.not_done{}:
      Empty

def lg.ends.of(o: Cr.Cir.Out, +d: {Lg.Out.done(o) == True{} : Bool}) -> lg.Ends(o):
  match o:
    case Cr.Cir.Out.next{_}:
      Unit{}
    case Cr.Cir.Out.halt{_, _}:
      Unit{}
    case Cr.Cir.Out.out_of_memory{}:
      Unit{}
    case Cr.Cir.Out.trap{}:
      Unit{}
    case Cr.Cir.Out.not_done{}:
      K.bool.ff(Empty, d)

# a < b <= c gives a < c
def lg.lt_le(a: Nat, +b: Nat, +c: Nat, +h1: {Nat.is_lt(a, b) == True{} : Bool}, +h2: {Nat.is_le(b, c) == True{} : Bool}) ->
  {Nat.is_lt(a, c) == True{} : Bool}:
  match a b c:
    case 0n 0n _:
      K.bool.ff({Nat.is_lt(0n, c) == True{} : Bool}, h1)
    case 1n+p 0n _:
      K.bool.ff({Nat.is_lt(1n+p, c) == True{} : Bool}, h1)
    case 0n 1n+q 0n:
      K.bool.ff({Nat.is_lt(0n, 0n) == True{} : Bool}, h2)
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 1n+q 0n:
      K.bool.ff({Nat.is_lt(1n+p, 0n) == True{} : Bool}, h2)
    case 1n+p 1n+q 1n+r:
      lg.lt_le(p, q, r, h1, h2)

# a weaker post for an outcome
def lg.ok.wk(o: Cr.Cir.Out, +lim: Nat, +b: Nat, +b2: Nat, -Q: Cr.Cir.State -> Type, -Q2: Cr.Cir.State -> Type,
  -H: U32 -> Cr.Cir.State -> Type, -H2: U32 -> Cr.Cir.State -> Type, +hb: {Nat.is_le(b, b2) == True{} : Bool},
  hq: @x: Cr.Cir.State -> Q(x) -> Q2(x), hh: @k: U32 -> @x: Cr.Cir.State -> H(k, x) -> H2(k, x),
  ok: Lg.Ok(o, lim, b, Q, H)) -> Lg.Ok(o, lim, b2, Q2, H2):
  match o:
    case Cr.Cir.Out.next{st}:
      hq(st, ok)
    case Cr.Cir.Out.halt{s, st}:
      hh(s, st, ok)
    case Cr.Cir.Out.out_of_memory{}:
      lg.lt_le(lim, b, b2, ok, hb)
    case Cr.Cir.Out.trap{}:
      ok
    case Cr.Cir.Out.not_done{}:
      ok

# More fuel
# ---------
#
# A run that ends with the fuel f ends the same with any fuel g >= f (mono),
# by induction on f, then on the statement.

def lg.ends.then(o: Cr.Cir.Out, -k: Cr.Cir.State -> Cr.Cir.Out, d: lg.Ends(Cr.Cir.exec.then(o, k))) -> lg.Ends(o):
  match o:
    case Cr.Cir.Out.next{st}:
      Unit{}
    case Cr.Cir.Out.halt{s, st}:
      Unit{}
    case Cr.Cir.Out.out_of_memory{}:
      Unit{}
    case Cr.Cir.Out.trap{}:
      Unit{}
    case Cr.Cir.Out.not_done{}:
      d

# the rest of a seq, after the same outcome o
def lg.mono.then(o: Cr.Cir.Out, -f: Nat, -g: Nat, -b: Cr.Cir.Stmt, d: lg.Ends(Cr.Cir.exec.then(o, t => Cr.Cir.exec(f, b, t))),
  ih: @t: Cr.Cir.State -> lg.Ends(Cr.Cir.exec(f, b, t)) -> {Cr.Cir.exec(f, b, t) == Cr.Cir.exec(g, b, t) : Cr.Cir.Out}) ->
  {Cr.Cir.exec.then(o, t => Cr.Cir.exec(f, b, t)) == Cr.Cir.exec.then(o, t => Cr.Cir.exec(g, b, t)) : Cr.Cir.Out}:
  match o:
    case Cr.Cir.Out.next{st}:
      ih(st, d)
    case Cr.Cir.Out.halt{s, st}:
      {==}
    case Cr.Cir.Out.out_of_memory{}:
      {==}
    case Cr.Cir.Out.trap{}:
      {==}
    case Cr.Cir.Out.not_done{}:
      {==}

# a seq: its first part by ha, then the rest by ih
def lg.mono.seq(+f: Nat, -g: Nat, +a: Cr.Cir.Stmt, -b: Cr.Cir.Stmt, +st: Cr.Cir.State,
  +d: lg.Ends(Cr.Cir.exec.then(Cr.Cir.exec(f, a, st), t => Cr.Cir.exec(f, b, t))),
  ha: lg.Ends(Cr.Cir.exec(f, a, st)) -> {Cr.Cir.exec(f, a, st) == Cr.Cir.exec(g, a, st) : Cr.Cir.Out},
  ih: @t: Cr.Cir.State -> lg.Ends(Cr.Cir.exec(f, b, t)) -> {Cr.Cir.exec(f, b, t) == Cr.Cir.exec(g, b, t) : Cr.Cir.Out}) ->
  {Cr.Cir.exec.then(Cr.Cir.exec(f, a, st), t => Cr.Cir.exec(f, b, t)) ==
    Cr.Cir.exec.then(Cr.Cir.exec(g, a, st), t => Cr.Cir.exec(g, b, t)) : Cr.Cir.Out}:
  +e = ha(lg.ends.then(Cr.Cir.exec(f, a, st), t => Cr.Cir.exec(f, b, t), d))
  %e : {Cr.Cir.exec.then(Cr.Cir.exec(f, a, st), t => Cr.Cir.exec(f, b, t)) ==
    Cr.Cir.exec.then(_, t => Cr.Cir.exec(g, b, t)) : Cr.Cir.Out}
  lg.mono.then(Cr.Cir.exec(f, a, st), f, g, b, d, ih)

def lg.mono.if.of(z: Bool, -f: Nat, -g: Nat, -t: Cr.Cir.Stmt, -e: Cr.Cir.Stmt, -st: Cr.Cir.State,
  d: lg.Ends(Cr.Cir.exec.if.of(z, u => Cr.Cir.exec(f, t, st), u => Cr.Cir.exec(f, e, st))),
  ht: lg.Ends(Cr.Cir.exec(f, t, st)) -> {Cr.Cir.exec(f, t, st) == Cr.Cir.exec(g, t, st) : Cr.Cir.Out},
  he: lg.Ends(Cr.Cir.exec(f, e, st)) -> {Cr.Cir.exec(f, e, st) == Cr.Cir.exec(g, e, st) : Cr.Cir.Out}) ->
  {Cr.Cir.exec.if.of(z, u => Cr.Cir.exec(f, t, st), u => Cr.Cir.exec(f, e, st)) ==
    Cr.Cir.exec.if.of(z, u => Cr.Cir.exec(g, t, st), u => Cr.Cir.exec(g, e, st)) : Cr.Cir.Out}:
  match z:
    case False{}:
      ht(d)
    case True{}:
      he(d)

# an if: the branch that its condition takes
def lg.mono.if(c: Maybe<&2, U32>, -f: Nat, -g: Nat, -t: Cr.Cir.Stmt, -e: Cr.Cir.Stmt, -st: Cr.Cir.State,
  d: lg.Ends(Cr.Cir.exec.if(c, u => Cr.Cir.exec(f, t, st), u => Cr.Cir.exec(f, e, st))),
  ht: lg.Ends(Cr.Cir.exec(f, t, st)) -> {Cr.Cir.exec(f, t, st) == Cr.Cir.exec(g, t, st) : Cr.Cir.Out},
  he: lg.Ends(Cr.Cir.exec(f, e, st)) -> {Cr.Cir.exec(f, e, st) == Cr.Cir.exec(g, e, st) : Cr.Cir.Out}) ->
  {Cr.Cir.exec.if(c, u => Cr.Cir.exec(f, t, st), u => Cr.Cir.exec(f, e, st)) ==
    Cr.Cir.exec.if(c, u => Cr.Cir.exec(g, t, st), u => Cr.Cir.exec(g, e, st)) : Cr.Cir.Out}:
  match c:
    case Some{x}:
      lg.mono.if.of(U32.is_zero(x), f, g, t, e, st, d, ht, he)
    case None{}:
      {==}

def lg.mono.wh.of(z: Bool, -f: Nat, -g: Nat, -c: Cr.Cir.Expr, -body: Cr.Cir.Stmt, -st: Cr.Cir.State,
  d: lg.Ends(Cr.Cir.exec.if.of(z, u => Cr.Cir.exec.then(Cr.Cir.exec(f, body, st), t => Cr.Cir.exec(f, Cr.Cir.Stmt.while{c, body}, t)),
    u => Cr.Cir.Out.next{st})),
  h: lg.Ends(Cr.Cir.exec.then(Cr.Cir.exec(f, body, st), t => Cr.Cir.exec(f, Cr.Cir.Stmt.while{c, body}, t))) ->
    {Cr.Cir.exec.then(Cr.Cir.exec(f, body, st), t => Cr.Cir.exec(f, Cr.Cir.Stmt.while{c, body}, t)) ==
      Cr.Cir.exec.then(Cr.Cir.exec(g, body, st), t => Cr.Cir.exec(g, Cr.Cir.Stmt.while{c, body}, t)) : Cr.Cir.Out}) ->
  {Cr.Cir.exec.if.of(z, u => Cr.Cir.exec.then(Cr.Cir.exec(f, body, st), t => Cr.Cir.exec(f, Cr.Cir.Stmt.while{c, body}, t)),
    u => Cr.Cir.Out.next{st}) ==
   Cr.Cir.exec.if.of(z, u => Cr.Cir.exec.then(Cr.Cir.exec(g, body, st), t => Cr.Cir.exec(g, Cr.Cir.Stmt.while{c, body}, t)),
    u => Cr.Cir.Out.next{st}) : Cr.Cir.Out}:
  match z:
    case False{}:
      h(d)
    case True{}:
      {==}

# a round of a while: its body, then the while again
def lg.mono.wh(v: Maybe<&2, U32>, -f: Nat, -g: Nat, -c: Cr.Cir.Expr, -body: Cr.Cir.Stmt, -st: Cr.Cir.State,
  d: lg.Ends(Cr.Cir.exec.if(v, u => Cr.Cir.exec.then(Cr.Cir.exec(f, body, st), t => Cr.Cir.exec(f, Cr.Cir.Stmt.while{c, body}, t)),
    u => Cr.Cir.Out.next{st})),
  h: lg.Ends(Cr.Cir.exec.then(Cr.Cir.exec(f, body, st), t => Cr.Cir.exec(f, Cr.Cir.Stmt.while{c, body}, t))) ->
    {Cr.Cir.exec.then(Cr.Cir.exec(f, body, st), t => Cr.Cir.exec(f, Cr.Cir.Stmt.while{c, body}, t)) ==
      Cr.Cir.exec.then(Cr.Cir.exec(g, body, st), t => Cr.Cir.exec(g, Cr.Cir.Stmt.while{c, body}, t)) : Cr.Cir.Out}) ->
  {Cr.Cir.exec.if(v, u => Cr.Cir.exec.then(Cr.Cir.exec(f, body, st), t => Cr.Cir.exec(f, Cr.Cir.Stmt.while{c, body}, t)),
    u => Cr.Cir.Out.next{st}) ==
   Cr.Cir.exec.if(v, u => Cr.Cir.exec.then(Cr.Cir.exec(g, body, st), t => Cr.Cir.exec(g, Cr.Cir.Stmt.while{c, body}, t)),
    u => Cr.Cir.Out.next{st}) : Cr.Cir.Out}:
  match v:
    case Some{x}:
      lg.mono.wh.of(U32.is_zero(x), f, g, c, body, st, d, h)
    case None{}:
      {==}

# more fuel keeps a run that ends
def lg.mono(+f: Nat, +g: Nat, +s: Cr.Cir.Stmt, +st: Cr.Cir.State, +le: N.Le(f, g), +d: lg.Ends(Cr.Cir.exec(f, s, st))) ->
  {Cr.Cir.exec(f, s, st) == Cr.Cir.exec(g, s, st) : Cr.Cir.Out}:
  match f g:
    case 0n 0n:
      {==}
    case 0n 1n+h:
      match s:
        case Cr.Cir.Stmt.nop{}:
          {==}
        case Cr.Cir.Stmt.set{r, e}:
          {==}
        case Cr.Cir.Stmt.store{k, c, v}:
          {==}
        case Cr.Cir.Stmt.alloc{r}:
          {==}
        case Cr.Cir.Stmt.emit{v}:
          {==}
        case Cr.Cir.Stmt.seq{+a, +b}:
          lg.mono.seq(0n, 1n+h, a, b, st, d, x => lg.mono(0n, 1n+h, a, st, le, x), t => x => lg.mono(0n, 1n+h, b, t, le, x))
        case Cr.Cir.Stmt.if{c, +t, +e}:
          lg.mono.if(Cr.Cir.eval(c, st), 0n, 1n+h, t, e, st, d, x => lg.mono(0n, 1n+h, t, st, le, x),
            x => lg.mono(0n, 1n+h, e, st, le, x))
        case Cr.Cir.Stmt.while{c, body}:
          Empty.absurd({Cr.Cir.exec(0n, Cr.Cir.Stmt.while{c, body}, st) == Cr.Cir.exec(1n+h, Cr.Cir.Stmt.while{c, body}, st) : Cr.Cir.Out}, d)
        case Cr.Cir.Stmt.halt{x}:
          {==}
    case 1n+p 0n:
      Empty.absurd({Cr.Cir.exec(1n+p, s, st) == Cr.Cir.exec(0n, s, st) : Cr.Cir.Out}, le)
    case 1n+p 1n+h:
      match s:
        case Cr.Cir.Stmt.nop{}:
          {==}
        case Cr.Cir.Stmt.set{r, e}:
          {==}
        case Cr.Cir.Stmt.store{k, c, v}:
          {==}
        case Cr.Cir.Stmt.alloc{r}:
          {==}
        case Cr.Cir.Stmt.emit{v}:
          {==}
        case Cr.Cir.Stmt.seq{+a, +b}:
          lg.mono.seq(1n+p, 1n+h, a, b, st, d, x => lg.mono(1n+p, 1n+h, a, st, le, x), t => x => lg.mono(1n+p, 1n+h, b, t, le, x))
        case Cr.Cir.Stmt.if{c, +t, +e}:
          lg.mono.if(Cr.Cir.eval(c, st), 1n+p, 1n+h, t, e, st, d, x => lg.mono(1n+p, 1n+h, t, st, le, x),
            x => lg.mono(1n+p, 1n+h, e, st, le, x))
        case Cr.Cir.Stmt.while{+c, +body}:
          lg.mono.wh(Cr.Cir.eval(c, st), p, h, c, body, st, d,
            x => lg.mono.seq(p, h, body, Cr.Cir.Stmt.while{c, body}, st, x, y => lg.mono(p, h, body, st, le, y),
              t => y => lg.mono(p, h, Cr.Cir.Stmt.while{c, body}, t, le, y)))
        case Cr.Cir.Stmt.halt{x}:
          {==}

# Terms of states
# ---------------
#
# A state as Lean's State (Interpreter/Machine.lean): a focus, to evaluate or a value,
# and its frames, the innermost first. A frame is a term with a hole, of a
# kind (the machine's K.app_arg to K.min_a), a quantity q, the flag K (k), and

# an if's branch, by z = U32.is_zero of its condition
def lg.if.of(z: Bool, +f: Nat, -y: Cr.Cir.Stmt, -n: Cr.Cir.Stmt, +st: Cr.Cir.State, +b: Nat, -Q: Cr.Cir.State -> Type,
  -H: U32 -> Cr.Cir.State -> Type, ok: Lg.Ok(Cr.Cir.exec(f, Bool.pick(Cr.Cir.Stmt, z, n, y), st), Lg.Lim(st), b, Q, H)) ->
  Lg.Ok(Cr.Cir.exec.if.of(z, u => Cr.Cir.exec(f, y, st), u => Cr.Cir.exec(f, n, st)), Lg.Lim(st), b, Q, H):
  match z:
    case False{}:
      ok
    case True{}:
      ok

# an if whose condition has the value v
def lg.if.ok(+f: Nat, -c: Cr.Cir.Expr, -y: Cr.Cir.Stmt, -n: Cr.Cir.Stmt, +st: Cr.Cir.State, +b: Nat, -Q: Cr.Cir.State -> Type,
  -H: U32 -> Cr.Cir.State -> Type, +v: U32, +e: {Cr.Cir.eval(c, st) == Some{v} : Maybe<&2, U32>},
  ok: Lg.Ok(Cr.Cir.exec(f, Bool.pick(Cr.Cir.Stmt, U32.is_zero(v), n, y), st), Lg.Lim(st), b, Q, H)) ->
  Lg.Ok(Cr.Cir.exec(f, Cr.Cir.Stmt.if{c, y, n}, st), Lg.Lim(st), b, Q, H):
  match f:
    case 0n:
      %Equal.sym(Maybe<&2, U32>, Cr.Cir.eval(c, st), Some{v}, e) :
        Lg.Ok(Cr.Cir.exec.if(_, u => Cr.Cir.exec(0n, y, st), u => Cr.Cir.exec(0n, n, st)), Lg.Lim(st), b, Q, H)
      lg.if.of(U32.is_zero(v), 0n, y, n, st, b, Q, H, ok)
    case 1n+p:
      %Equal.sym(Maybe<&2, U32>, Cr.Cir.eval(c, st), Some{v}, e) :
        Lg.Ok(Cr.Cir.exec.if(_, u => Cr.Cir.exec(1n+p, y, st), u => Cr.Cir.exec(1n+p, n, st)), Lg.Lim(st), b, Q, H)
      lg.if.of(U32.is_zero(v), 1n+p, y, n, st, b, Q, H, ok)

def Lg.exec.more(f, g, s, st, d):
  Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, s, st), Cr.Cir.exec(Nat.add(f, g), s, st),
    lg.mono(f, Nat.add(f, g), s, st, N.le_add_r(f, g), lg.ends.of(Cr.Cir.exec(f, s, st), d)))

def Lg.tot.any(s, st, b, Q, H, t, g):
  ?TODO

def Lg.tot.seq(a, c, st, b, Q, H, t):
  ?TODO

def Lg.tot.if(c, y, n, st, b, Q, H, v, e, t):
  match t:
    case Tuple{+f, ok}:
      (f, lg.if.ok(f, c, y, n, st, b, Q, H, v, e, ok))

def Lg.tot.while(c, body, b, I, Q, H, r, n, st, i):
  ?TODO

def Lg.tot.wk(s, st, b, b2, Q, Q2, H, H2, hb, hq, hh, t):
  match t:
    case Tuple{+f, ok}:
      (f, lg.ok.wk(Cr.Cir.exec(f, s, st), Lg.Lim(st), b, b2, Q, Q2, H, H2, hb, hq, hh, ok))

def Lg.tot.of_wp(s, st, b, K, H, w):
  ?TODO

def Lg.wp.of_tot(s, st, b, K, H, t):
  ?TODO

def Lg.wp.wk(s, st, b, b2, K, K2, H, H2, hb, hk, hh, w):
  ?TODO

def Lg.exec.set(f, r, e, st, v, he, hr):
  match f:
    case 0n:
      match st:
        case Cr.Cir.State{+regs, cells, next, first, image, pages, limit, input, out, outn}:
          %Equal.sym(Maybe<&2, U32>, Cr.Cir.eval(e, Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}), Some{v}, he) :
            {Cr.Cir.exec.set(r, _, Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}) ==
              Cr.Cir.Out.next{Cr.Cir.State{List.set(&2, U32, regs, r, v), cells, next, first, image, pages, limit, input, out, outn}} : Cr.Cir.Out}
          %Equal.sym(Bool, Nat.is_lt(r, List.length(&2, U32, regs)), True{}, hr) :
            {Cr.Cir.exec.set.of(Cr.Cir.regs.set.if(_, regs, r, v), Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}) ==
              Cr.Cir.Out.next{Cr.Cir.State{List.set(&2, U32, regs, r, v), cells, next, first, image, pages, limit, input, out, outn}} : Cr.Cir.Out}
          {==}
    case 1n+p:
      match st:
        case Cr.Cir.State{+regs, cells, next, first, image, pages, limit, input, out, outn}:
          %Equal.sym(Maybe<&2, U32>, Cr.Cir.eval(e, Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}), Some{v}, he) :
            {Cr.Cir.exec.set(r, _, Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}) ==
              Cr.Cir.Out.next{Cr.Cir.State{List.set(&2, U32, regs, r, v), cells, next, first, image, pages, limit, input, out, outn}} : Cr.Cir.Out}
          %Equal.sym(Bool, Nat.is_lt(r, List.length(&2, U32, regs)), True{}, hr) :
            {Cr.Cir.exec.set.of(Cr.Cir.regs.set.if(_, regs, r, v), Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}) ==
              Cr.Cir.Out.next{Cr.Cir.State{List.set(&2, U32, regs, r, v), cells, next, first, image, pages, limit, input, out, outn}} : Cr.Cir.Out}
          {==}

def Lg.exec.store(f, k, c, e, st, i, v, hc, he, hi):
  ?TODO

def Lg.exec.alloc(f, r, st, hr, ho):
  ?TODO

def Lg.wp.set(r, e, st, b, K, H, v, he, hr, q):
  ?TODO

def Lg.wp.store(k, c, e, st, b, K, H, i, v, hc, he, hi, q):
  ?TODO

def Lg.wp.alloc(r, st, b, K, H, hr, ho, hb, q):
  ?TODO

def Lg.wp.emit(e, st, b, K, H, v, he, hb, q):
  ?TODO

def Lg.reg.set(st, r, v, q, hr):
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      K.list.get_set(U32, regs, r, v, q, hr)

def Lg.reg.store(st, k, c, v, q):
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      {==}

def Lg.reg.alloc(st, r, p, q, hr):
  match st:
    case Cr.Cir.State{regs, cells, +next, first, image, pages, limit, input, out, outn}:
      K.list.get_set(U32, regs, r, next, q, hr)

def Lg.reg.emit(st, v, p, q):
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      {==}

def Lg.nregs.set(st, r, v):
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      K.list.length_set(U32, regs, r, v)

def Lg.nregs.store(st, k, c, v):
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      {==}

def Lg.nregs.alloc(st, r, p):
  match st:
    case Cr.Cir.State{regs, cells, +next, first, image, pages, limit, input, out, outn}:
      K.list.length_set(U32, regs, r, next)

def Lg.nregs.emit(st, v, p):
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      {==}

def Lg.cells.set(st, r, v):
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      {==}

def Lg.cells.store(st, k, c, v):
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      {==}

def Lg.cells.alloc(st, r, p):
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      {==}

def Lg.cells.emit(st, v, p):
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      {==}

def Lg.cells.get_set(m, i, x, j):
  ?TODO

def Lg.cell.get_set(k, x, v, j, hk, hj):
  ?TODO

def Lg.next.set(st, r, v):
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      {==}

def Lg.next.store(st, k, c, v):
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      {==}

def Lg.next.alloc(st, r, p):
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      {==}

def Lg.next.emit(st, v, p):
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      {==}

def Lg.outn.set(st, r, v):
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      {==}

def Lg.outn.store(st, k, c, v):
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      {==}

def Lg.outn.alloc(st, r, p):
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      {==}

def Lg.outn.emit(st, v, p):
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      {==}

def Lg.fixed.set(st, r, v):
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      {==}

def Lg.fixed.store(st, k, c, v):
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      {==}

def Lg.fixed.alloc(st, r, p):
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      {==}

def Lg.fixed.emit(st, v, p):
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      {==}

def Lg.lim.set(st, r, v):
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      {==}

def Lg.lim.store(st, k, c, v):
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      {==}

def Lg.lim.alloc(st, r, p):
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      {==}

def Lg.lim.emit(st, v, p):
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      {==}

def Lg.frame.regs(f, s, st, st2, r, e, w):
  ?TODO

def Lg.frame.fixed(f, s, st, st2, e):
  ?TODO

def Lg.tot.frame(s, st, b, Q, H, t):
  ?TODO

def Lg.tot.frame_out(s, st, b, Q, H, ne, t):
  ?TODO

