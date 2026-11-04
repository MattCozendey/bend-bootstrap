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

# b <= b
def lg.le_refl(+b: Nat) -> {Nat.is_le(b, b) == True{} : Bool}:
  match b:
    case 0n:
      {==}
    case 1n+p:
      lg.le_refl(p)

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

# a + b = b + a
def lg.add_comm(+a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, N.add_zero(b))
    case 1n+p:
      %Equal.sym(Nat, Nat.add(p, b), Nat.add(b, p), lg.add_comm(p, b)) : {1n+_ == Nat.add(b, 1n+p) : Nat}
      Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), N.add_succ_r(b, p))

# a good outcome ended (and the outcome back)
def lg.ok.done(o: Cr.Cir.Out, +lim: Nat, +b: Nat, -Q: Cr.Cir.State -> Type, -H: U32 -> Cr.Cir.State -> Type,
  ok: Lg.Ok(o, lim, b, Q, H)) -> {Lg.Out.done(o) == True{} : Bool} & Lg.Ok(o, lim, b, Q, H):
  match o:
    case Cr.Cir.Out.next{_}:
      ({==}, ok)
    case Cr.Cir.Out.halt{_, _}:
      ({==}, ok)
    case Cr.Cir.Out.out_of_memory{}:
      ({==}, ok)
    case Cr.Cir.Out.trap{}:
      match ok:
    case Cr.Cir.Out.not_done{}:
      match ok:

# a sequence's run, at any fuel
def lg.exec.seq(+f: Nat, +a: Cr.Cir.Stmt, +c: Cr.Cir.Stmt, +st: Cr.Cir.State) ->
  {Cr.Cir.exec(f, Cr.Cir.Stmt.seq{a, c}, st) == Cr.Cir.exec.then(Cr.Cir.exec(f, a, st), t => Cr.Cir.exec(f, c, t)) : Cr.Cir.Out}:
  match f:
    case 0n:
      {==}
    case 1n+p:
      {==}

# the limit's bytes, from the fixed parts
def lg.limf(x: Lg.St.Fixed) -> Nat:
  match x:
    case Lg.St.Fixed{limit, _, _, _}:
      N.D(16n, U32.to_nat(Wa.Wasm.min(limit, 65536)))

def lg.lim.fixed(st: Cr.Cir.State) -> {Lg.Lim(st) == lg.limf(Lg.St.fixed(st)) : Nat}:
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      {==}

# two states with the same fixed parts have the same limit
def lg.lim.eq(+x: Cr.Cir.State, +st: Cr.Cir.State, +e: {Lg.St.fixed(x) == Lg.St.fixed(st) : Lg.St.Fixed}) -> {Lg.Lim(x) == Lg.Lim(st) : Nat}:
  Equal.trans(Nat, Lg.Lim(x), lg.limf(Lg.St.fixed(st)), Lg.Lim(st),
    Equal.trans(Nat, Lg.Lim(x), lg.limf(Lg.St.fixed(x)), lg.limf(Lg.St.fixed(st)), lg.lim.fixed(x),
      Equal.cong(Lg.St.Fixed, Nat, y => lg.limf(y), Lg.St.fixed(x), Lg.St.fixed(st), e)),
    Equal.sym(Nat, Lg.Lim(st), lg.limf(Lg.St.fixed(st)), lg.lim.fixed(st)))

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

# Laws
# ----

def Lg.exec.more(f, g, s, st, d):
  Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, s, st), Cr.Cir.exec(Nat.add(f, g), s, st),
    lg.mono(f, Nat.add(f, g), s, st, N.le_add_r(f, g), lg.ends.of(Cr.Cir.exec(f, s, st), d)))

def Lg.reg.set(st, r, v, q, hr):
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      K.list.get_set(U32, regs, r, v, q, hr)

def Lg.reg.some(st, q, hq):
  match st:
    case Cr.Cir.State{+regs, cells, next, first, image, pages, limit, input, out, outn}:
      K.list.get_lt(U32, regs, q, 0, hq)

def Lg.reg.lt(st, q, c, hq):
  match st:
    case Cr.Cir.State{+regs, cells, next, first, image, pages, limit, input, out, outn}:
      K.list.lt_get(U32, regs, q, c, hq)

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

# gen2 --ind: a helper lemma (proven)
def cells.get_set.i12(+x: Cr.Cir.Cell, +g: Cmp, +g1: Cr.Cir.Cell) ->
  {Bool.pick(Cr.Cir.Cell, Cmp.is_eq(g), x, g1) == Bool.pick(Cr.Cir.Cell, Cmp.is_eq(Word.cmp.fin(True{}, True{}, g)), x, g1) : Cr.Cir.Cell}:
  match g:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

# gen2 --ind: a helper lemma (proven)
def cells.get_set.i11(+p: Nat, +iwt: Word(p), +x: Cr.Cir.Cell, +jwt: Word(p), +g: Cr.Cir.Cell, +g1: Cmp, +hg: {g1 == Word.cmp(p, iwt, jwt) : Cmp}) ->
  {g == Bool.pick(Cr.Cir.Cell, Cmp.is_eq(Word.cmp.fin(False{}, True{}, g1)), x, g) : Cr.Cir.Cell}:
  match g1:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

# gen2 --ind: a helper lemma (proven)
def cells.get_set.i10(+x: Cr.Cir.Cell, +g: Cmp, +g1: Cr.Cir.Cell) ->
  {Bool.pick(Cr.Cir.Cell, Cmp.is_eq(g), x, g1) == Bool.pick(Cr.Cir.Cell, Cmp.is_eq(Word.cmp.fin(False{}, False{}, g)), x, g1) : Cr.Cir.Cell}:
  %K.cmp.fin_ff(g) :
    {Bool.pick(Cr.Cir.Cell, _, x, g1) == Bool.pick(Cr.Cir.Cell, Cmp.is_eq(Word.cmp.fin(False{}, False{}, g)), x, g1) : Cr.Cir.Cell}
  {==}

# gen2 --ind: a helper lemma (proven)
def cells.get_set.i5(+p: Nat, +x: Cr.Cir.Cell, +jwt: Word(p), +g: Cmp) ->
  {Bool.pick(Cr.Cir.Cell, Cmp.is_eq(g), x, Cr.Cir.Cells.get.at(p, jwt, Cr.Cir.Cells.none{})) == Bool.pick(Cr.Cir.Cell, Cmp.is_eq(Word.cmp.fin(True{}, True{}, g)), x, Cr.Cir.Cell{0, 0, 0, 0, 0}) : Cr.Cir.Cell}:
  match p:
    case 0n:
      match jwt g:
        case WNil{} LT{}:
          {==}
        case WNil{} EQ{}:
          {==}
        case WNil{} GT{}:
          {==}
    case 1n+p1:
      match jwt g:
        case WCon{False{}, jwtt} LT{}:
          {==}
        case WCon{False{}, jwtt} EQ{}:
          {==}
        case WCon{False{}, jwtt} GT{}:
          {==}
        case WCon{True{}, jwtt} LT{}:
          {==}
        case WCon{True{}, jwtt} EQ{}:
          {==}
        case WCon{True{}, jwtt} GT{}:
          {==}

# gen2 --ind: a helper lemma (proven)
def cells.get_set.i4(+p: Nat, +iwt: Word(p), +x: Cr.Cir.Cell, +jwt: Word(p), +g: Cmp, +hg: {g == Word.cmp(p, iwt, jwt) : Cmp}) ->
  {Cr.Cir.Cells.get.at(p, jwt, Cr.Cir.Cells.none{}) == Bool.pick(Cr.Cir.Cell, Cmp.is_eq(Word.cmp.fin(True{}, False{}, g)), x, Cr.Cir.Cell{0, 0, 0, 0, 0}) : Cr.Cir.Cell}:
  match p:
    case 0n:
      match iwt jwt:
        case WNil{} WNil{}:
          (%Equal.sym(Cmp, g, Word.cmp(0n, WNil{}, WNil{}), hg) : {Cr.Cir.Cell{0, 0, 0, 0, 0} == Bool.pick(Cr.Cir.Cell, Cmp.is_eq(Word.cmp.fin(True{}, False{}, _)), x, Cr.Cir.Cell{0, 0, 0, 0, 0}) : Cr.Cir.Cell}; {==})
    case 1n+p1:
      match iwt jwt:
        case WCon{False{}, iwtt} WCon{False{}, jwtt}:
          (%Equal.sym(Bool, Cmp.is_eq(Word.cmp.fin(True{}, False{}, g)), False{}, K.cmp.fin_tf(g)) : {Cr.Cir.Cell{0, 0, 0, 0, 0} == Bool.pick(Cr.Cir.Cell, _, x, Cr.Cir.Cell{0, 0, 0, 0, 0}) : Cr.Cir.Cell}; {==})
        case WCon{False{}, iwtt} WCon{True{}, jwtt}:
          (%Equal.sym(Bool, Cmp.is_eq(Word.cmp.fin(True{}, False{}, g)), False{}, K.cmp.fin_tf(g)) : {Cr.Cir.Cell{0, 0, 0, 0, 0} == Bool.pick(Cr.Cir.Cell, _, x, Cr.Cir.Cell{0, 0, 0, 0, 0}) : Cr.Cir.Cell}; {==})
        case WCon{True{}, iwtt} WCon{False{}, jwtt}:
          (%Equal.sym(Bool, Cmp.is_eq(Word.cmp.fin(True{}, False{}, g)), False{}, K.cmp.fin_tf(g)) : {Cr.Cir.Cell{0, 0, 0, 0, 0} == Bool.pick(Cr.Cir.Cell, _, x, Cr.Cir.Cell{0, 0, 0, 0, 0}) : Cr.Cir.Cell}; {==})
        case WCon{True{}, iwtt} WCon{True{}, jwtt}:
          (%Equal.sym(Bool, Cmp.is_eq(Word.cmp.fin(True{}, False{}, g)), False{}, K.cmp.fin_tf(g)) : {Cr.Cir.Cell{0, 0, 0, 0, 0} == Bool.pick(Cr.Cir.Cell, _, x, Cr.Cir.Cell{0, 0, 0, 0, 0}) : Cr.Cir.Cell}; {==})

# gen2 --ind: a helper lemma (proven)
def cells.get_set.i3(+p: Nat, +iwt: Word(p), +x: Cr.Cir.Cell, +jwt: Word(p), +g: Cmp, +hg: {g == Word.cmp(p, iwt, jwt) : Cmp}) ->
  {Cr.Cir.Cells.get.at(p, jwt, Cr.Cir.Cells.none{}) == Bool.pick(Cr.Cir.Cell, Cmp.is_eq(Word.cmp.fin(False{}, True{}, g)), x, Cr.Cir.Cell{0, 0, 0, 0, 0}) : Cr.Cir.Cell}:
  match p:
    case 0n:
      match iwt jwt g:
        case WNil{} WNil{} LT{}:
          {==}
        case WNil{} WNil{} EQ{}:
          {==}
        case WNil{} WNil{} GT{}:
          {==}
    case 1n+p1:
      match iwt jwt g:
        case WCon{False{}, iwtt} WCon{False{}, jwtt} LT{}:
          {==}
        case WCon{False{}, iwtt} WCon{False{}, jwtt} EQ{}:
          {==}
        case WCon{False{}, iwtt} WCon{False{}, jwtt} GT{}:
          {==}
        case WCon{False{}, iwtt} WCon{True{}, jwtt} LT{}:
          {==}
        case WCon{False{}, iwtt} WCon{True{}, jwtt} EQ{}:
          {==}
        case WCon{False{}, iwtt} WCon{True{}, jwtt} GT{}:
          {==}
        case WCon{True{}, iwtt} WCon{False{}, jwtt} LT{}:
          {==}
        case WCon{True{}, iwtt} WCon{False{}, jwtt} EQ{}:
          {==}
        case WCon{True{}, iwtt} WCon{False{}, jwtt} GT{}:
          {==}
        case WCon{True{}, iwtt} WCon{True{}, jwtt} LT{}:
          {==}
        case WCon{True{}, iwtt} WCon{True{}, jwtt} EQ{}:
          {==}
        case WCon{True{}, iwtt} WCon{True{}, jwtt} GT{}:
          {==}

# gen2 --ind: a helper lemma (proven)
def cells.get_set.i2(+p: Nat, +x: Cr.Cir.Cell, +jwt: Word(p), +g: Cmp) ->
  {Bool.pick(Cr.Cir.Cell, Cmp.is_eq(g), x, Cr.Cir.Cells.get.at(p, jwt, Cr.Cir.Cells.none{})) == Bool.pick(Cr.Cir.Cell, Cmp.is_eq(Word.cmp.fin(False{}, False{}, g)), x, Cr.Cir.Cell{0, 0, 0, 0, 0}) : Cr.Cir.Cell}:
  match p:
    case 0n:
      match jwt:
        case WNil{}:
          (%K.cmp.fin_ff(g) : {Bool.pick(Cr.Cir.Cell, _, x, Cr.Cir.Cell{0, 0, 0, 0, 0}) == Bool.pick(Cr.Cir.Cell, Cmp.is_eq(Word.cmp.fin(False{}, False{}, g)), x, Cr.Cir.Cell{0, 0, 0, 0, 0}) : Cr.Cir.Cell}; {==})
    case 1n+p1:
      match jwt:
        case WCon{False{}, jwtt}:
          (%K.cmp.fin_ff(g) : {Bool.pick(Cr.Cir.Cell, _, x, Cr.Cir.Cell{0, 0, 0, 0, 0}) == Bool.pick(Cr.Cir.Cell, Cmp.is_eq(Word.cmp.fin(False{}, False{}, g)), x, Cr.Cir.Cell{0, 0, 0, 0, 0}) : Cr.Cir.Cell}; {==})
        case WCon{True{}, jwtt}:
          (%K.cmp.fin_ff(g) : {Bool.pick(Cr.Cir.Cell, _, x, Cr.Cir.Cell{0, 0, 0, 0, 0}) == Bool.pick(Cr.Cir.Cell, Cmp.is_eq(Word.cmp.fin(False{}, False{}, g)), x, Cr.Cir.Cell{0, 0, 0, 0, 0}) : Cr.Cir.Cell}; {==})

# gen2 --ind: a helper lemma (proven)
def cells.get_set.i1(+n: Nat, +m: Cr.Cir.Cells, +iw: Word(n), +x: Cr.Cir.Cell, +jw: Word(n)) ->
  {Cr.Cir.Cells.get.at(n, jw, Cr.Cir.Cells.set.at(n, iw, m, x)) == Bool.pick(Cr.Cir.Cell, Cmp.is_eq(Word.cmp(n, iw, jw)), x, Cr.Cir.Cells.get.at(n, jw, m)) : Cr.Cir.Cell}:
  match n:
    case 0n:
      match m iw jw:
        case Cr.Cir.Cells.none{} WNil{} WNil{}:
          {==}
        case Cr.Cir.Cells.one{m02} WNil{} WNil{}:
          {==}
        case Cr.Cir.Cells.node{m03, m11} WNil{} WNil{}:
          {==}
    case 1n+p:
      match m iw jw:
        case Cr.Cir.Cells.none{} WCon{False{}, iwt} WCon{False{}, jwt}:
          (%Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get.at(p, jwt, Cr.Cir.Cells.set.at(p, iwt, Cr.Cir.Cells.none{}, x)), Bool.pick(Cr.Cir.Cell, Cmp.is_eq(Word.cmp(p, iwt, jwt)), x, Cr.Cir.Cells.get.at(p, jwt, Cr.Cir.Cells.none{})), cells.get_set.i1(p, Cr.Cir.Cells.none{}, iwt, x, jwt)) : {_ == Bool.pick(Cr.Cir.Cell, Cmp.is_eq(Word.cmp.fin(False{}, False{}, Word.cmp(p, iwt, jwt))), x, Cr.Cir.Cell{0, 0, 0, 0, 0}) : Cr.Cir.Cell}; cells.get_set.i2(p, x, jwt, Word.cmp(p, iwt, jwt)))
        case Cr.Cir.Cells.none{} WCon{False{}, iwt} WCon{True{}, jwt}:
          cells.get_set.i3(p, iwt, x, jwt, Word.cmp(p, iwt, jwt), {==})
        case Cr.Cir.Cells.none{} WCon{True{}, iwt} WCon{False{}, jwt}:
          cells.get_set.i4(p, iwt, x, jwt, Word.cmp(p, iwt, jwt), {==})
        case Cr.Cir.Cells.none{} WCon{True{}, iwt} WCon{True{}, jwt}:
          (%Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get.at(p, jwt, Cr.Cir.Cells.set.at(p, iwt, Cr.Cir.Cells.none{}, x)), Bool.pick(Cr.Cir.Cell, Cmp.is_eq(Word.cmp(p, iwt, jwt)), x, Cr.Cir.Cells.get.at(p, jwt, Cr.Cir.Cells.none{})), cells.get_set.i1(p, Cr.Cir.Cells.none{}, iwt, x, jwt)) : {_ == Bool.pick(Cr.Cir.Cell, Cmp.is_eq(Word.cmp.fin(True{}, True{}, Word.cmp(p, iwt, jwt))), x, Cr.Cir.Cell{0, 0, 0, 0, 0}) : Cr.Cir.Cell}; cells.get_set.i5(p, x, jwt, Word.cmp(p, iwt, jwt)))
        case Cr.Cir.Cells.one{m0} WCon{False{}, iwt} WCon{False{}, jwt}:
          (%Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get.at(p, jwt, Cr.Cir.Cells.set.at(p, iwt, Cr.Cir.Cells.none{}, x)), Bool.pick(Cr.Cir.Cell, Cmp.is_eq(Word.cmp(p, iwt, jwt)), x, Cr.Cir.Cells.get.at(p, jwt, Cr.Cir.Cells.none{})), cells.get_set.i1(p, Cr.Cir.Cells.none{}, iwt, x, jwt)) : {_ == Bool.pick(Cr.Cir.Cell, Cmp.is_eq(Word.cmp.fin(False{}, False{}, Word.cmp(p, iwt, jwt))), x, Cr.Cir.Cell{0, 0, 0, 0, 0}) : Cr.Cir.Cell}; cells.get_set.i2(p, x, jwt, Word.cmp(p, iwt, jwt)))
        case Cr.Cir.Cells.one{m0} WCon{False{}, iwt} WCon{True{}, jwt}:
          cells.get_set.i3(p, iwt, x, jwt, Word.cmp(p, iwt, jwt), {==})
        case Cr.Cir.Cells.one{m0} WCon{True{}, iwt} WCon{False{}, jwt}:
          cells.get_set.i4(p, iwt, x, jwt, Word.cmp(p, iwt, jwt), {==})
        case Cr.Cir.Cells.one{m0} WCon{True{}, iwt} WCon{True{}, jwt}:
          (%Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get.at(p, jwt, Cr.Cir.Cells.set.at(p, iwt, Cr.Cir.Cells.none{}, x)), Bool.pick(Cr.Cir.Cell, Cmp.is_eq(Word.cmp(p, iwt, jwt)), x, Cr.Cir.Cells.get.at(p, jwt, Cr.Cir.Cells.none{})), cells.get_set.i1(p, Cr.Cir.Cells.none{}, iwt, x, jwt)) : {_ == Bool.pick(Cr.Cir.Cell, Cmp.is_eq(Word.cmp.fin(True{}, True{}, Word.cmp(p, iwt, jwt))), x, Cr.Cir.Cell{0, 0, 0, 0, 0}) : Cr.Cir.Cell}; cells.get_set.i5(p, x, jwt, Word.cmp(p, iwt, jwt)))
        case Cr.Cir.Cells.node{m01, m1} WCon{False{}, iwt} WCon{False{}, jwt}:
          (%Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get.at(p, jwt, Cr.Cir.Cells.set.at(p, iwt, m01, x)), Bool.pick(Cr.Cir.Cell, Cmp.is_eq(Word.cmp(p, iwt, jwt)), x, Cr.Cir.Cells.get.at(p, jwt, m01)), cells.get_set.i1(p, m01, iwt, x, jwt)) : {_ == Bool.pick(Cr.Cir.Cell, Cmp.is_eq(Word.cmp.fin(False{}, False{}, Word.cmp(p, iwt, jwt))), x, Cr.Cir.Cells.get.at(p, jwt, m01)) : Cr.Cir.Cell}; cells.get_set.i10(x, Word.cmp(p, iwt, jwt), Cr.Cir.Cells.get.at(p, jwt, m01)))
        case Cr.Cir.Cells.node{m01, m1} WCon{False{}, iwt} WCon{True{}, jwt}:
          cells.get_set.i11(p, iwt, x, jwt, Cr.Cir.Cells.get.at(p, jwt, m1), Word.cmp(p, iwt, jwt), {==})
        case Cr.Cir.Cells.node{m01, m1} WCon{True{}, iwt} WCon{False{}, jwt}:
          (%Equal.sym(Bool, Cmp.is_eq(Word.cmp.fin(True{}, False{}, Word.cmp(p, iwt, jwt))), False{}, K.cmp.fin_tf(Word.cmp(p, iwt, jwt))) : {Cr.Cir.Cells.get.at(p, jwt, m01) == Bool.pick(Cr.Cir.Cell, _, x, Cr.Cir.Cells.get.at(p, jwt, m01)) : Cr.Cir.Cell}; {==})
        case Cr.Cir.Cells.node{m01, m1} WCon{True{}, iwt} WCon{True{}, jwt}:
          (%Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get.at(p, jwt, Cr.Cir.Cells.set.at(p, iwt, m1, x)), Bool.pick(Cr.Cir.Cell, Cmp.is_eq(Word.cmp(p, iwt, jwt)), x, Cr.Cir.Cells.get.at(p, jwt, m1)), cells.get_set.i1(p, m1, iwt, x, jwt)) : {_ == Bool.pick(Cr.Cir.Cell, Cmp.is_eq(Word.cmp.fin(True{}, True{}, Word.cmp(p, iwt, jwt))), x, Cr.Cir.Cells.get.at(p, jwt, m1)) : Cr.Cir.Cell}; cells.get_set.i12(x, Word.cmp(p, iwt, jwt), Cr.Cir.Cells.get.at(p, jwt, m1)))

def Lg.cells.get_set(m, i, x, j):
  match i j:
    case U32{iw} U32{jw}:
      cells.get_set.i1(32n, m, iw, x, jw)

def Lg.cell.get_set(k, x, v, j, hk, hj):
  match k x j:
    case 0n Cr.Cir.Cell{x0, x1, x2, x3, x4} 0n:
      {==}
    case 0n Cr.Cir.Cell{x0, x1, x2, x3, x4} 1n:
      {==}
    case 0n Cr.Cir.Cell{x0, x1, x2, x3, x4} 2n:
      {==}
    case 0n Cr.Cir.Cell{x0, x1, x2, x3, x4} 3n:
      {==}
    case 0n Cr.Cir.Cell{x0, x1, x2, x3, x4} 4n:
      {==}
    case 0n Cr.Cir.Cell{x0, x1, x2, x3, x4} 5n+jp:
      {==}
    case 1n Cr.Cir.Cell{x0, x1, x2, x3, x4} 0n:
      {==}
    case 1n Cr.Cir.Cell{x0, x1, x2, x3, x4} 1n:
      {==}
    case 1n Cr.Cir.Cell{x0, x1, x2, x3, x4} 2n:
      {==}
    case 1n Cr.Cir.Cell{x0, x1, x2, x3, x4} 3n:
      {==}
    case 1n Cr.Cir.Cell{x0, x1, x2, x3, x4} 4n:
      {==}
    case 1n Cr.Cir.Cell{x0, x1, x2, x3, x4} 5n+jp:
      {==}
    case 2n Cr.Cir.Cell{x0, x1, x2, x3, x4} 0n:
      {==}
    case 2n Cr.Cir.Cell{x0, x1, x2, x3, x4} 1n:
      {==}
    case 2n Cr.Cir.Cell{x0, x1, x2, x3, x4} 2n:
      {==}
    case 2n Cr.Cir.Cell{x0, x1, x2, x3, x4} 3n:
      {==}
    case 2n Cr.Cir.Cell{x0, x1, x2, x3, x4} 4n:
      {==}
    case 2n Cr.Cir.Cell{x0, x1, x2, x3, x4} 5n+jp:
      {==}
    case 3n Cr.Cir.Cell{x0, x1, x2, x3, x4} 0n:
      {==}
    case 3n Cr.Cir.Cell{x0, x1, x2, x3, x4} 1n:
      {==}
    case 3n Cr.Cir.Cell{x0, x1, x2, x3, x4} 2n:
      {==}
    case 3n Cr.Cir.Cell{x0, x1, x2, x3, x4} 3n:
      {==}
    case 3n Cr.Cir.Cell{x0, x1, x2, x3, x4} 4n:
      {==}
    case 3n Cr.Cir.Cell{x0, x1, x2, x3, x4} 5n+jp:
      {==}
    case 4n Cr.Cir.Cell{x0, x1, x2, x3, x4} 0n:
      {==}
    case 4n Cr.Cir.Cell{x0, x1, x2, x3, x4} 1n:
      {==}
    case 4n Cr.Cir.Cell{x0, x1, x2, x3, x4} 2n:
      {==}
    case 4n Cr.Cir.Cell{x0, x1, x2, x3, x4} 3n:
      {==}
    case 4n Cr.Cir.Cell{x0, x1, x2, x3, x4} 4n:
      {==}
    case 4n Cr.Cir.Cell{x0, x1, x2, x3, x4} 5n+jp:
      K.bool.tf2({Cr.Cir.Cell.get(5n+jp, Cr.Cir.Cell.set(4n, Cr.Cir.Cell{x0, x1, x2, x3, x4}, v)) == Bool.pick(U32, Nat.is_eq(4n, 5n+jp), v, Cr.Cir.Cell.get(5n+jp, Cr.Cir.Cell{x0, x1, x2, x3, x4})) : U32}, Nat.is_le(5n+jp, 4n), hj, {==})
    case 5n+kp Cr.Cir.Cell{x0, x1, x2, x3, x4} 0n:
      {==}
    case 5n+kp Cr.Cir.Cell{x0, x1, x2, x3, x4} 1n:
      {==}
    case 5n+kp Cr.Cir.Cell{x0, x1, x2, x3, x4} 2n:
      {==}
    case 5n+kp Cr.Cir.Cell{x0, x1, x2, x3, x4} 3n:
      {==}
    case 5n+kp Cr.Cir.Cell{x0, x1, x2, x3, x4} 4n:
      K.bool.ff({Cr.Cir.Cell.get(4n, Cr.Cir.Cell.set(5n+kp, Cr.Cir.Cell{x0, x1, x2, x3, x4}, v)) == Bool.pick(U32, Nat.is_eq(5n+kp, 4n), v, Cr.Cir.Cell.get(4n, Cr.Cir.Cell{x0, x1, x2, x3, x4})) : U32}, hk)
    case 5n+kp Cr.Cir.Cell{x0, x1, x2, x3, x4} 5n+jp:
      K.bool.tf2({Cr.Cir.Cell.get(5n+jp, Cr.Cir.Cell.set(5n+kp, Cr.Cir.Cell{x0, x1, x2, x3, x4}, v)) == Bool.pick(U32, Nat.is_eq(5n+kp, 5n+jp), v, Cr.Cir.Cell.get(5n+jp, Cr.Cir.Cell{x0, x1, x2, x3, x4})) : U32}, Nat.is_le(5n+jp, 4n), hj, {==})

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

# gen2 --ind: a helper (a constructor test)
def frame.fixed.is_next_1(z: Cr.Cir.Out) -> Type:
  match z:
    case Cr.Cir.Out.next{f0}:
      Unit
    case _:
      Empty

# gen2 --ind: a helper (an inversion)
def frame.fixed.inv69(+st2: Cr.Cir.State, +Sta0: List<&2, U32>, +Sta1: Cr.Cir.Cells, +Sta2: U32, +Sta3: U32, +Sta4: U32, +Sta6: U32, +Sta7: List<&2, Word(8n)>, +Sta8: List<&2, Word(8n)>, +Sta9: U32, +h2: {Cmp.is_eq(U32.cmp(Sta9, 0)) == True{} : Bool}, +h4: {Cmp.is_lt(U32.cmp(Sta2, 214748364)) == True{} : Bool}, +Som0: U32, +r: Maybe<&2, List<&2, U32>>, +h: {Cr.Cir.exec.set.of(r, Cr.Cir.State{Sta0, Cr.Cir.Cells.set(Sta1, Sta2, Cr.Cir.Cell{0, 0, 0, 0, 0}), U32.inc(Sta2), Sta3, Sta4, Som0, Sta6, Sta7, Sta8, Sta9}) == Cr.Cir.Out.next{st2} : Cr.Cir.Out}, -G: Type, k: @+x_0: List<&2, U32> -> @+h1: {r == Some{x_0} : Maybe<&2, List<&2, U32>>} -> @+h2: {Cr.Cir.exec.set.of(Some{x_0}, Cr.Cir.State{Sta0, Cr.Cir.Cells.set(Sta1, Sta2, Cr.Cir.Cell{0, 0, 0, 0, 0}), U32.inc(Sta2), Sta3, Sta4, Som0, Sta6, Sta7, Sta8, Sta9}) == Cr.Cir.Out.next{st2} : Cr.Cir.Out} -> G) -> G:
  match r:
    case None{}:
      Empty.absurd(G, (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec.set.of(None{}, Cr.Cir.State{Sta0, Cr.Cir.Cells.set(Sta1, Sta2, Cr.Cir.Cell{0, 0, 0, 0, 0}), U32.inc(Sta2), Sta3, Sta4, Som0, Sta6, Sta7, Sta8, Sta9}), Cr.Cir.Out.next{st2}, h) : frame.fixed.is_next_1(_); Unit{}))
    case Some{x_0}:
      k(x_0, {==}, h)

# gen2 --ind: a helper (an inversion)
def frame.fixed.inv61(+st2: Cr.Cir.State, +Som0: U32, +Sta0: List<&2, U32>, +Sta1: Cr.Cir.Cells, +Sta2: U32, +Sta3: U32, +Sta4: U32, +Sta5: U32, +Sta6: U32, +Sta7: List<&2, Word(8n)>, +Sta8: List<&2, Word(8n)>, +Sta9: U32, +h3: {Cr.Cir.exec.emit(Some{Som0}, Cr.Cir.State{Sta0, Sta1, Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9}) == Cr.Cir.Out.next{st2} : Cr.Cir.Out}, +h4: {Bool.and(Cmp.is_lt(U32.cmp(Sta2, 214748365)), Cmp.is_ge(U32.cmp(U32.add(U32.add(U32.shl(U32.shl(U32.shl(U32.shl(Sta2)))), U32.shl(U32.shl(Sta2))), Sta9), Sta9))) == True{} : Bool}, +h5: {Cr.Cir.exec.emit.if(True{}, U32.add(U32.add(U32.shl(U32.shl(U32.shl(U32.shl(Sta2)))), U32.shl(U32.shl(Sta2))), Sta9), Som0, Cr.Cir.State{Sta0, Sta1, Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9}) == Cr.Cir.Out.next{st2} : Cr.Cir.Out}, +r: Maybe<&2, U32>, +h: {Cr.Cir.exec.emit.of(r, Som0, Cr.Cir.State{Sta0, Sta1, Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9}) == Cr.Cir.Out.next{st2} : Cr.Cir.Out}, -G: Type, k: @+x_0: U32 -> @+h1: {r == Some{x_0} : Maybe<&2, U32>} -> @+h2: {Cr.Cir.exec.emit.of(Some{x_0}, Som0, Cr.Cir.State{Sta0, Sta1, Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9}) == Cr.Cir.Out.next{st2} : Cr.Cir.Out} -> G) -> G:
  match r:
    case None{}:
      Empty.absurd(G, (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec.emit.of(None{}, Som0, Cr.Cir.State{Sta0, Sta1, Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9}), Cr.Cir.Out.next{st2}, h) : frame.fixed.is_next_1(_); Unit{}))
    case Some{x_0}:
      k(x_0, {==}, h)

# gen2 --ind: a helper (an inversion)
def frame.fixed.inv59(+s02: Nat, +st2: Cr.Cir.State, +Sta0: List<&2, U32>, +Sta1: Cr.Cir.Cells, +Sta2: U32, +Sta3: U32, +Sta4: U32, +Sta5: U32, +Sta6: U32, +Sta7: List<&2, Word(8n)>, +Sta8: List<&2, Word(8n)>, +Sta9: U32, +h1: {Cr.Cir.exec.alloc(s02, Cr.Cir.State{Sta0, Sta1, Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9}) == Cr.Cir.Out.next{st2} : Cr.Cir.Out}, +h2: {Cmp.is_eq(U32.cmp(Sta9, 0)) == True{} : Bool}, +h3: {Cr.Cir.exec.alloc.if(True{}, s02, Cr.Cir.State{Sta0, Sta1, Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9}) == Cr.Cir.Out.next{st2} : Cr.Cir.Out}, +h4: {Cmp.is_lt(U32.cmp(Sta2, 214748364)) == True{} : Bool}, +h5: {Cr.Cir.exec.bump.if(True{}, s02, Sta2, Sta5, Sta6, Cr.Cir.State{Sta0, Sta1, Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9}) == Cr.Cir.Out.next{st2} : Cr.Cir.Out}, +r: Maybe<&2, U32>, +h: {Cr.Cir.exec.bump.of(s02, Sta2, Cr.Cir.State{Sta0, Sta1, Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9}, r) == Cr.Cir.Out.next{st2} : Cr.Cir.Out}, -G: Type, k: @+x_0: U32 -> @+h1: {r == Some{x_0} : Maybe<&2, U32>} -> @+h2: {Cr.Cir.exec.bump.of(s02, Sta2, Cr.Cir.State{Sta0, Sta1, Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9}, Some{x_0}) == Cr.Cir.Out.next{st2} : Cr.Cir.Out} -> G) -> G:
  match r:
    case None{}:
      Empty.absurd(G, (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec.bump.of(s02, Sta2, Cr.Cir.State{Sta0, Sta1, Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9}, None{}), Cr.Cir.Out.next{st2}, h) : frame.fixed.is_next_1(_); Unit{}))
    case Some{x_0}:
      k(x_0, {==}, h)

# gen2 --ind: a helper (an inversion)
def frame.fixed.inv57(+s01: Nat, +st2: Cr.Cir.State, +Som0: U32, +Som01: U32, +Sta0: List<&2, U32>, +Sta1: Cr.Cir.Cells, +Sta2: U32, +Sta3: U32, +Sta4: U32, +Sta5: U32, +Sta6: U32, +Sta7: List<&2, Word(8n)>, +Sta8: List<&2, Word(8n)>, +Sta9: U32, +h5: {Cr.Cir.exec.store(s01, Some{Som0}, Some{Som01}, Cr.Cir.State{Sta0, Sta1, Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9}) == Cr.Cir.Out.next{st2} : Cr.Cir.Out}, +r: Bool, +h: {Cr.Cir.exec.store.if(r, s01, Som0, Som01, Cr.Cir.State{Sta0, Sta1, Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9}) == Cr.Cir.Out.next{st2} : Cr.Cir.Out}, -G: Type, k: @+h1: {r == True{} : Bool} -> @+h2: {Cr.Cir.exec.store.if(True{}, s01, Som0, Som01, Cr.Cir.State{Sta0, Sta1, Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9}) == Cr.Cir.Out.next{st2} : Cr.Cir.Out} -> G) -> G:
  match r:
    case False{}:
      Empty.absurd(G, (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec.store.if(False{}, s01, Som0, Som01, Cr.Cir.State{Sta0, Sta1, Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9}), Cr.Cir.Out.next{st2}, h) : frame.fixed.is_next_1(_); Unit{}))
    case True{}:
      k({==}, h)

# gen2 --ind: a helper (an inversion)
def frame.fixed.inv55(+fp: Nat, +s06: Cr.Cir.Expr, +s14: Cr.Cir.Stmt, +st2: Cr.Cir.State, +r: Cr.Cir.Out, +h: {Cr.Cir.exec.then(r, t => Cr.Cir.exec(fp, Cr.Cir.Stmt.while{s06, s14}, t)) == Cr.Cir.Out.next{st2} : Cr.Cir.Out}, -G: Type, k: @+x_0: Cr.Cir.State -> @+h1: {r == Cr.Cir.Out.next{x_0} : Cr.Cir.Out} -> @+h2: {Cr.Cir.exec.then(Cr.Cir.Out.next{x_0}, t => Cr.Cir.exec(fp, Cr.Cir.Stmt.while{s06, s14}, t)) == Cr.Cir.Out.next{st2} : Cr.Cir.Out} -> G) -> G:
  match r:
    case Cr.Cir.Out.next{x_0}:
      k(x_0, {==}, h)
    case Cr.Cir.Out.halt{y_0, y_1}:
      Empty.absurd(G, (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec.then(Cr.Cir.Out.halt{y_0, y_1}, t => Cr.Cir.exec(fp, Cr.Cir.Stmt.while{s06, s14}, t)), Cr.Cir.Out.next{st2}, h) : frame.fixed.is_next_1(_); Unit{}))
    case Cr.Cir.Out.out_of_memory{}:
      Empty.absurd(G, (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec.then(Cr.Cir.Out.out_of_memory{}, t => Cr.Cir.exec(fp, Cr.Cir.Stmt.while{s06, s14}, t)), Cr.Cir.Out.next{st2}, h) : frame.fixed.is_next_1(_); Unit{}))
    case Cr.Cir.Out.trap{}:
      Empty.absurd(G, (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec.then(Cr.Cir.Out.trap{}, t => Cr.Cir.exec(fp, Cr.Cir.Stmt.while{s06, s14}, t)), Cr.Cir.Out.next{st2}, h) : frame.fixed.is_next_1(_); Unit{}))
    case Cr.Cir.Out.not_done{}:
      Empty.absurd(G, (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec.then(Cr.Cir.Out.not_done{}, t => Cr.Cir.exec(fp, Cr.Cir.Stmt.while{s06, s14}, t)), Cr.Cir.Out.next{st2}, h) : frame.fixed.is_next_1(_); Unit{}))

# gen2 --ind: a helper (an inversion)
def frame.fixed.inv47(+st2: Cr.Cir.State, +Som0: U32, +Sta0: List<&2, U32>, +Sta1: Cr.Cir.Cells, +Sta2: U32, +Sta3: U32, +Sta4: U32, +Sta5: U32, +Sta6: U32, +Sta7: List<&2, Word(8n)>, +Sta8: List<&2, Word(8n)>, +Sta9: U32, +h3: {Cr.Cir.exec.emit(Some{Som0}, Cr.Cir.State{Sta0, Sta1, Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9}) == Cr.Cir.Out.next{st2} : Cr.Cir.Out}, +r: Bool, +h: {Cr.Cir.exec.emit.if(r, U32.add(U32.add(U32.shl(U32.shl(U32.shl(U32.shl(Sta2)))), U32.shl(U32.shl(Sta2))), Sta9), Som0, Cr.Cir.State{Sta0, Sta1, Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9}) == Cr.Cir.Out.next{st2} : Cr.Cir.Out}, -G: Type, k: @+h1: {r == True{} : Bool} -> @+h2: {Cr.Cir.exec.emit.if(True{}, U32.add(U32.add(U32.shl(U32.shl(U32.shl(U32.shl(Sta2)))), U32.shl(U32.shl(Sta2))), Sta9), Som0, Cr.Cir.State{Sta0, Sta1, Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9}) == Cr.Cir.Out.next{st2} : Cr.Cir.Out} -> G) -> G:
  match r:
    case False{}:
      Empty.absurd(G, (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec.emit.if(False{}, U32.add(U32.add(U32.shl(U32.shl(U32.shl(U32.shl(Sta2)))), U32.shl(U32.shl(Sta2))), Sta9), Som0, Cr.Cir.State{Sta0, Sta1, Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9}), Cr.Cir.Out.next{st2}, h) : frame.fixed.is_next_1(_); Unit{}))
    case True{}:
      k({==}, h)

# gen2 --ind: a helper (an inversion)
def frame.fixed.inv45(+s02: Nat, +st2: Cr.Cir.State, +Sta0: List<&2, U32>, +Sta1: Cr.Cir.Cells, +Sta2: U32, +Sta3: U32, +Sta4: U32, +Sta5: U32, +Sta6: U32, +Sta7: List<&2, Word(8n)>, +Sta8: List<&2, Word(8n)>, +Sta9: U32, +h1: {Cr.Cir.exec.alloc(s02, Cr.Cir.State{Sta0, Sta1, Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9}) == Cr.Cir.Out.next{st2} : Cr.Cir.Out}, +h2: {Cmp.is_eq(U32.cmp(Sta9, 0)) == True{} : Bool}, +h3: {Cr.Cir.exec.alloc.if(True{}, s02, Cr.Cir.State{Sta0, Sta1, Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9}) == Cr.Cir.Out.next{st2} : Cr.Cir.Out}, +r: Bool, +h: {Cr.Cir.exec.bump.if(r, s02, Sta2, Sta5, Sta6, Cr.Cir.State{Sta0, Sta1, Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9}) == Cr.Cir.Out.next{st2} : Cr.Cir.Out}, -G: Type, k: @+h1: {r == True{} : Bool} -> @+h2: {Cr.Cir.exec.bump.if(True{}, s02, Sta2, Sta5, Sta6, Cr.Cir.State{Sta0, Sta1, Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9}) == Cr.Cir.Out.next{st2} : Cr.Cir.Out} -> G) -> G:
  match r:
    case False{}:
      Empty.absurd(G, (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec.bump.if(False{}, s02, Sta2, Sta5, Sta6, Cr.Cir.State{Sta0, Sta1, Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9}), Cr.Cir.Out.next{st2}, h) : frame.fixed.is_next_1(_); Unit{}))
    case True{}:
      k({==}, h)

# gen2 --ind: a helper (an inversion)
def frame.fixed.inv43(+s01: Nat, +st2: Cr.Cir.State, +Som0: U32, +Som01: U32, +r: Cr.Cir.State, +h: {Cr.Cir.exec.store(s01, Some{Som0}, Some{Som01}, r) == Cr.Cir.Out.next{st2} : Cr.Cir.Out}, -G: Type, k: @+x_0: List<&2, U32> -> @+x_1: Cr.Cir.Cells -> @+x_2: U32 -> @+x_3: U32 -> @+x_4: U32 -> @+x_5: U32 -> @+x_6: U32 -> @+x_7: List<&2, Word(8n)> -> @+x_8: List<&2, Word(8n)> -> @+x_9: U32 -> @+h1: {r == Cr.Cir.State{x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9} : Cr.Cir.State} -> @+h2: {Cr.Cir.exec.store(s01, Some{Som0}, Some{Som01}, Cr.Cir.State{x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9}) == Cr.Cir.Out.next{st2} : Cr.Cir.Out} -> G) -> G:
  match r:
    case Cr.Cir.State{x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9}:
      k(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, {==}, h)

# gen2 --ind: a helper (an inversion)
def frame.fixed.inv42(+st2: Cr.Cir.State, +Sta0: List<&2, U32>, +Sta1: Cr.Cir.Cells, +Sta2: U32, +Sta3: U32, +Sta4: U32, +Sta5: U32, +Sta6: U32, +Sta7: List<&2, Word(8n)>, +Sta8: List<&2, Word(8n)>, +Sta9: U32, +r: Maybe<&2, List<&2, U32>>, +h: {Cr.Cir.exec.set.of(r, Cr.Cir.State{Sta0, Sta1, Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9}) == Cr.Cir.Out.next{st2} : Cr.Cir.Out}, -G: Type, k: @+x_0: List<&2, U32> -> @+h1: {r == Some{x_0} : Maybe<&2, List<&2, U32>>} -> @+h2: {Cr.Cir.exec.set.of(Some{x_0}, Cr.Cir.State{Sta0, Sta1, Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9}) == Cr.Cir.Out.next{st2} : Cr.Cir.Out} -> G) -> G:
  match r:
    case None{}:
      Empty.absurd(G, (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec.set.of(None{}, Cr.Cir.State{Sta0, Sta1, Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9}), Cr.Cir.Out.next{st2}, h) : frame.fixed.is_next_1(_); Unit{}))
    case Some{x_0}:
      k(x_0, {==}, h)

# gen2 --ind: a helper (a case split)
def frame.fixed.case3(+fp: Nat, +s06: Cr.Cir.Expr, +s14: Cr.Cir.Stmt, +st: Cr.Cir.State, +st2: Cr.Cir.State, +e: {Cr.Cir.exec(1n+fp, Cr.Cir.Stmt.while{s06, s14}, st) == Cr.Cir.Out.next{st2} : Cr.Cir.Out}, +r: Bool, +h: {Cr.Cir.exec.if.of(r, u => Cr.Cir.exec.then(Cr.Cir.exec(fp, s14, st), t => Cr.Cir.exec(fp, Cr.Cir.Stmt.while{s06, s14}, t)), u => Cr.Cir.Out.next{st}) == Cr.Cir.Out.next{st2} : Cr.Cir.Out}, -G: Type, k0: @+h1: {r == False{} : Bool} -> @+h2: {Cr.Cir.exec.if.of(False{}, u => Cr.Cir.exec.then(Cr.Cir.exec(fp, s14, st), t => Cr.Cir.exec(fp, Cr.Cir.Stmt.while{s06, s14}, t)), u => Cr.Cir.Out.next{st}) == Cr.Cir.Out.next{st2} : Cr.Cir.Out} -> G, k1: @+h1: {r == True{} : Bool} -> @+h2: {Cr.Cir.exec.if.of(True{}, u => Cr.Cir.exec.then(Cr.Cir.exec(fp, s14, st), t => Cr.Cir.exec(fp, Cr.Cir.Stmt.while{s06, s14}, t)), u => Cr.Cir.Out.next{st}) == Cr.Cir.Out.next{st2} : Cr.Cir.Out} -> G) -> G:
  match r:
    case False{}:
      k0({==}, h)
    case True{}:
      k1({==}, h)

# gen2 --ind: a helper (a case split)
def frame.fixed.case2(+fp: Nat, +s13: Cr.Cir.Stmt, +s21: Cr.Cir.Stmt, +st: Cr.Cir.State, +st2: Cr.Cir.State, +r: Bool, +h: {Cr.Cir.exec.if.of(r, u => Cr.Cir.exec(1n+fp, s13, st), u => Cr.Cir.exec(1n+fp, s21, st)) == Cr.Cir.Out.next{st2} : Cr.Cir.Out}, -G: Type, k0: @+h1: {r == False{} : Bool} -> @+h2: {Cr.Cir.exec.if.of(False{}, u => Cr.Cir.exec(1n+fp, s13, st), u => Cr.Cir.exec(1n+fp, s21, st)) == Cr.Cir.Out.next{st2} : Cr.Cir.Out} -> G, k1: @+h1: {r == True{} : Bool} -> @+h2: {Cr.Cir.exec.if.of(True{}, u => Cr.Cir.exec(1n+fp, s13, st), u => Cr.Cir.exec(1n+fp, s21, st)) == Cr.Cir.Out.next{st2} : Cr.Cir.Out} -> G) -> G:
  match r:
    case False{}:
      k0({==}, h)
    case True{}:
      k1({==}, h)

# gen2 --ind: a helper (a case split)
def frame.fixed.case1(+s13: Cr.Cir.Stmt, +s21: Cr.Cir.Stmt, +st: Cr.Cir.State, +st2: Cr.Cir.State, +r: Bool, +h: {Cr.Cir.exec.if.of(r, u => Cr.Cir.exec(0n, s13, st), u => Cr.Cir.exec(0n, s21, st)) == Cr.Cir.Out.next{st2} : Cr.Cir.Out}, -G: Type, k0: @+h1: {r == False{} : Bool} -> @+h2: {Cr.Cir.exec.if.of(False{}, u => Cr.Cir.exec(0n, s13, st), u => Cr.Cir.exec(0n, s21, st)) == Cr.Cir.Out.next{st2} : Cr.Cir.Out} -> G, k1: @+h1: {r == True{} : Bool} -> @+h2: {Cr.Cir.exec.if.of(True{}, u => Cr.Cir.exec(0n, s13, st), u => Cr.Cir.exec(0n, s21, st)) == Cr.Cir.Out.next{st2} : Cr.Cir.Out} -> G) -> G:
  match r:
    case False{}:
      k0({==}, h)
    case True{}:
      k1({==}, h)

# gen2 --ind: a helper (an inversion)
def frame.fixed.inv28(+st2: Cr.Cir.State, +Som0: U32, +r: Cr.Cir.State, +h: {Cr.Cir.exec.emit(Some{Som0}, r) == Cr.Cir.Out.next{st2} : Cr.Cir.Out}, -G: Type, k: @+x_0: List<&2, U32> -> @+x_1: Cr.Cir.Cells -> @+x_2: U32 -> @+x_3: U32 -> @+x_4: U32 -> @+x_5: U32 -> @+x_6: U32 -> @+x_7: List<&2, Word(8n)> -> @+x_8: List<&2, Word(8n)> -> @+x_9: U32 -> @+h1: {r == Cr.Cir.State{x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9} : Cr.Cir.State} -> @+h2: {Cr.Cir.exec.emit(Some{Som0}, Cr.Cir.State{x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9}) == Cr.Cir.Out.next{st2} : Cr.Cir.Out} -> G) -> G:
  match r:
    case Cr.Cir.State{x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9}:
      k(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, {==}, h)

# gen2 --ind: a helper (an inversion)
def frame.fixed.inv27(+s02: Nat, +st2: Cr.Cir.State, +Sta0: List<&2, U32>, +Sta1: Cr.Cir.Cells, +Sta2: U32, +Sta3: U32, +Sta4: U32, +Sta5: U32, +Sta6: U32, +Sta7: List<&2, Word(8n)>, +Sta8: List<&2, Word(8n)>, +Sta9: U32, +h1: {Cr.Cir.exec.alloc(s02, Cr.Cir.State{Sta0, Sta1, Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9}) == Cr.Cir.Out.next{st2} : Cr.Cir.Out}, +r: Bool, +h: {Cr.Cir.exec.alloc.if(r, s02, Cr.Cir.State{Sta0, Sta1, Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9}) == Cr.Cir.Out.next{st2} : Cr.Cir.Out}, -G: Type, k: @+h1: {r == True{} : Bool} -> @+h2: {Cr.Cir.exec.alloc.if(True{}, s02, Cr.Cir.State{Sta0, Sta1, Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9}) == Cr.Cir.Out.next{st2} : Cr.Cir.Out} -> G) -> G:
  match r:
    case False{}:
      Empty.absurd(G, (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec.alloc.if(False{}, s02, Cr.Cir.State{Sta0, Sta1, Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9}), Cr.Cir.Out.next{st2}, h) : frame.fixed.is_next_1(_); Unit{}))
    case True{}:
      k({==}, h)

# gen2 --ind: a helper (an inversion)
def frame.fixed.inv25(+s01: Nat, +st: Cr.Cir.State, +st2: Cr.Cir.State, +Som0: U32, +r: Maybe<&2, U32>, +h: {Cr.Cir.exec.store(s01, Some{Som0}, r, st) == Cr.Cir.Out.next{st2} : Cr.Cir.Out}, -G: Type, k: @+x_0: U32 -> @+h1: {r == Some{x_0} : Maybe<&2, U32>} -> @+h2: {Cr.Cir.exec.store(s01, Some{Som0}, Some{x_0}, st) == Cr.Cir.Out.next{st2} : Cr.Cir.Out} -> G) -> G:
  match r:
    case None{}:
      Empty.absurd(G, (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec.store(s01, Some{Som0}, None{}, st), Cr.Cir.Out.next{st2}, h) : frame.fixed.is_next_1(_); Unit{}))
    case Some{x_0}:
      k(x_0, {==}, h)

# gen2 --ind: a helper (an inversion)
def frame.fixed.inv23(+s0: Nat, +st2: Cr.Cir.State, +Som0: U32, +r: Cr.Cir.State, +h: {Cr.Cir.exec.set(s0, Some{Som0}, r) == Cr.Cir.Out.next{st2} : Cr.Cir.Out}, -G: Type, k: @+x_0: List<&2, U32> -> @+x_1: Cr.Cir.Cells -> @+x_2: U32 -> @+x_3: U32 -> @+x_4: U32 -> @+x_5: U32 -> @+x_6: U32 -> @+x_7: List<&2, Word(8n)> -> @+x_8: List<&2, Word(8n)> -> @+x_9: U32 -> @+h1: {r == Cr.Cir.State{x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9} : Cr.Cir.State} -> @+h2: {Cr.Cir.exec.set(s0, Some{Som0}, Cr.Cir.State{x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9}) == Cr.Cir.Out.next{st2} : Cr.Cir.Out} -> G) -> G:
  match r:
    case Cr.Cir.State{x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9}:
      k(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, {==}, h)

# gen2 --ind: a helper (an inversion)
def frame.fixed.inv22(+fp: Nat, +s06: Cr.Cir.Expr, +s14: Cr.Cir.Stmt, +st: Cr.Cir.State, +st2: Cr.Cir.State, +e: {Cr.Cir.exec(1n+fp, Cr.Cir.Stmt.while{s06, s14}, st) == Cr.Cir.Out.next{st2} : Cr.Cir.Out}, +r: Maybe<&2, U32>, +h: {Cr.Cir.exec.if(r, u => Cr.Cir.exec.then(Cr.Cir.exec(fp, s14, st), t => Cr.Cir.exec(fp, Cr.Cir.Stmt.while{s06, s14}, t)), u => Cr.Cir.Out.next{st}) == Cr.Cir.Out.next{st2} : Cr.Cir.Out}, -G: Type, k: @+x_0: U32 -> @+h1: {r == Some{x_0} : Maybe<&2, U32>} -> @+h2: {Cr.Cir.exec.if(Some{x_0}, u => Cr.Cir.exec.then(Cr.Cir.exec(fp, s14, st), t => Cr.Cir.exec(fp, Cr.Cir.Stmt.while{s06, s14}, t)), u => Cr.Cir.Out.next{st}) == Cr.Cir.Out.next{st2} : Cr.Cir.Out} -> G) -> G:
  match r:
    case None{}:
      Empty.absurd(G, (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec.if(None{}, u => Cr.Cir.exec.then(Cr.Cir.exec(fp, s14, st), t => Cr.Cir.exec(fp, Cr.Cir.Stmt.while{s06, s14}, t)), u => Cr.Cir.Out.next{st}), Cr.Cir.Out.next{st2}, h) : frame.fixed.is_next_1(_); Unit{}))
    case Some{x_0}:
      k(x_0, {==}, h)

# gen2 --ind: a helper (an inversion)
def frame.fixed.inv20(+fp: Nat, +s13: Cr.Cir.Stmt, +s21: Cr.Cir.Stmt, +st: Cr.Cir.State, +st2: Cr.Cir.State, +r: Maybe<&2, U32>, +h: {Cr.Cir.exec.if(r, u => Cr.Cir.exec(1n+fp, s13, st), u => Cr.Cir.exec(1n+fp, s21, st)) == Cr.Cir.Out.next{st2} : Cr.Cir.Out}, -G: Type, k: @+x_0: U32 -> @+h1: {r == Some{x_0} : Maybe<&2, U32>} -> @+h2: {Cr.Cir.exec.if(Some{x_0}, u => Cr.Cir.exec(1n+fp, s13, st), u => Cr.Cir.exec(1n+fp, s21, st)) == Cr.Cir.Out.next{st2} : Cr.Cir.Out} -> G) -> G:
  match r:
    case None{}:
      Empty.absurd(G, (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec.if(None{}, u => Cr.Cir.exec(1n+fp, s13, st), u => Cr.Cir.exec(1n+fp, s21, st)), Cr.Cir.Out.next{st2}, h) : frame.fixed.is_next_1(_); Unit{}))
    case Some{x_0}:
      k(x_0, {==}, h)

# gen2 --ind: a helper (an inversion)
def frame.fixed.inv18(+fp: Nat, +s12: Cr.Cir.Stmt, +st2: Cr.Cir.State, +r: Cr.Cir.Out, +h: {Cr.Cir.exec.then(r, t => Cr.Cir.exec(1n+fp, s12, t)) == Cr.Cir.Out.next{st2} : Cr.Cir.Out}, -G: Type, k: @+x_0: Cr.Cir.State -> @+h1: {r == Cr.Cir.Out.next{x_0} : Cr.Cir.Out} -> @+h2: {Cr.Cir.exec.then(Cr.Cir.Out.next{x_0}, t => Cr.Cir.exec(1n+fp, s12, t)) == Cr.Cir.Out.next{st2} : Cr.Cir.Out} -> G) -> G:
  match r:
    case Cr.Cir.Out.next{x_0}:
      k(x_0, {==}, h)
    case Cr.Cir.Out.halt{y_0, y_1}:
      Empty.absurd(G, (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec.then(Cr.Cir.Out.halt{y_0, y_1}, t => Cr.Cir.exec(1n+fp, s12, t)), Cr.Cir.Out.next{st2}, h) : frame.fixed.is_next_1(_); Unit{}))
    case Cr.Cir.Out.out_of_memory{}:
      Empty.absurd(G, (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec.then(Cr.Cir.Out.out_of_memory{}, t => Cr.Cir.exec(1n+fp, s12, t)), Cr.Cir.Out.next{st2}, h) : frame.fixed.is_next_1(_); Unit{}))
    case Cr.Cir.Out.trap{}:
      Empty.absurd(G, (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec.then(Cr.Cir.Out.trap{}, t => Cr.Cir.exec(1n+fp, s12, t)), Cr.Cir.Out.next{st2}, h) : frame.fixed.is_next_1(_); Unit{}))
    case Cr.Cir.Out.not_done{}:
      Empty.absurd(G, (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec.then(Cr.Cir.Out.not_done{}, t => Cr.Cir.exec(1n+fp, s12, t)), Cr.Cir.Out.next{st2}, h) : frame.fixed.is_next_1(_); Unit{}))

# gen2 --ind: a helper (an inversion)
def frame.fixed.inv10(+s13: Cr.Cir.Stmt, +s21: Cr.Cir.Stmt, +st: Cr.Cir.State, +st2: Cr.Cir.State, +r: Maybe<&2, U32>, +h: {Cr.Cir.exec.if(r, u => Cr.Cir.exec(0n, s13, st), u => Cr.Cir.exec(0n, s21, st)) == Cr.Cir.Out.next{st2} : Cr.Cir.Out}, -G: Type, k: @+x_0: U32 -> @+h1: {r == Some{x_0} : Maybe<&2, U32>} -> @+h2: {Cr.Cir.exec.if(Some{x_0}, u => Cr.Cir.exec(0n, s13, st), u => Cr.Cir.exec(0n, s21, st)) == Cr.Cir.Out.next{st2} : Cr.Cir.Out} -> G) -> G:
  match r:
    case None{}:
      Empty.absurd(G, (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec.if(None{}, u => Cr.Cir.exec(0n, s13, st), u => Cr.Cir.exec(0n, s21, st)), Cr.Cir.Out.next{st2}, h) : frame.fixed.is_next_1(_); Unit{}))
    case Some{x_0}:
      k(x_0, {==}, h)

# gen2 --ind: a helper (an inversion)
def frame.fixed.inv8(+s12: Cr.Cir.Stmt, +st2: Cr.Cir.State, +r: Cr.Cir.Out, +h: {Cr.Cir.exec.then(r, t => Cr.Cir.exec(0n, s12, t)) == Cr.Cir.Out.next{st2} : Cr.Cir.Out}, -G: Type, k: @+x_0: Cr.Cir.State -> @+h1: {r == Cr.Cir.Out.next{x_0} : Cr.Cir.Out} -> @+h2: {Cr.Cir.exec.then(Cr.Cir.Out.next{x_0}, t => Cr.Cir.exec(0n, s12, t)) == Cr.Cir.Out.next{st2} : Cr.Cir.Out} -> G) -> G:
  match r:
    case Cr.Cir.Out.next{x_0}:
      k(x_0, {==}, h)
    case Cr.Cir.Out.halt{y_0, y_1}:
      Empty.absurd(G, (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec.then(Cr.Cir.Out.halt{y_0, y_1}, t => Cr.Cir.exec(0n, s12, t)), Cr.Cir.Out.next{st2}, h) : frame.fixed.is_next_1(_); Unit{}))
    case Cr.Cir.Out.out_of_memory{}:
      Empty.absurd(G, (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec.then(Cr.Cir.Out.out_of_memory{}, t => Cr.Cir.exec(0n, s12, t)), Cr.Cir.Out.next{st2}, h) : frame.fixed.is_next_1(_); Unit{}))
    case Cr.Cir.Out.trap{}:
      Empty.absurd(G, (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec.then(Cr.Cir.Out.trap{}, t => Cr.Cir.exec(0n, s12, t)), Cr.Cir.Out.next{st2}, h) : frame.fixed.is_next_1(_); Unit{}))
    case Cr.Cir.Out.not_done{}:
      Empty.absurd(G, (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec.then(Cr.Cir.Out.not_done{}, t => Cr.Cir.exec(0n, s12, t)), Cr.Cir.Out.next{st2}, h) : frame.fixed.is_next_1(_); Unit{}))

# gen2 --ind: a helper (an inversion)
def frame.fixed.inv7(+st: Cr.Cir.State, +st2: Cr.Cir.State, +r: Maybe<&2, U32>, +h: {Cr.Cir.exec.emit(r, st) == Cr.Cir.Out.next{st2} : Cr.Cir.Out}, -G: Type, k: @+x_0: U32 -> @+h1: {r == Some{x_0} : Maybe<&2, U32>} -> @+h2: {Cr.Cir.exec.emit(Some{x_0}, st) == Cr.Cir.Out.next{st2} : Cr.Cir.Out} -> G) -> G:
  match r:
    case None{}:
      Empty.absurd(G, (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec.emit(None{}, st), Cr.Cir.Out.next{st2}, h) : frame.fixed.is_next_1(_); Unit{}))
    case Some{x_0}:
      k(x_0, {==}, h)

# gen2 --ind: a helper (an inversion)
def frame.fixed.inv5(+s02: Nat, +st2: Cr.Cir.State, +r: Cr.Cir.State, +h: {Cr.Cir.exec.alloc(s02, r) == Cr.Cir.Out.next{st2} : Cr.Cir.Out}, -G: Type, k: @+x_0: List<&2, U32> -> @+x_1: Cr.Cir.Cells -> @+x_2: U32 -> @+x_3: U32 -> @+x_4: U32 -> @+x_5: U32 -> @+x_6: U32 -> @+x_7: List<&2, Word(8n)> -> @+x_8: List<&2, Word(8n)> -> @+x_9: U32 -> @+h1: {r == Cr.Cir.State{x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9} : Cr.Cir.State} -> @+h2: {Cr.Cir.exec.alloc(s02, Cr.Cir.State{x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9}) == Cr.Cir.Out.next{st2} : Cr.Cir.Out} -> G) -> G:
  match r:
    case Cr.Cir.State{x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9}:
      k(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, {==}, h)

# gen2 --ind: a helper (an inversion)
def frame.fixed.inv4(+s01: Nat, +s2: Cr.Cir.Expr, +st: Cr.Cir.State, +st2: Cr.Cir.State, +r: Maybe<&2, U32>, +h: {Cr.Cir.exec.store(s01, r, Cr.Cir.eval(s2, st), st) == Cr.Cir.Out.next{st2} : Cr.Cir.Out}, -G: Type, k: @+x_0: U32 -> @+h1: {r == Some{x_0} : Maybe<&2, U32>} -> @+h2: {Cr.Cir.exec.store(s01, Some{x_0}, Cr.Cir.eval(s2, st), st) == Cr.Cir.Out.next{st2} : Cr.Cir.Out} -> G) -> G:
  match r:
    case None{}:
      Empty.absurd(G, (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec.store(s01, None{}, Cr.Cir.eval(s2, st), st), Cr.Cir.Out.next{st2}, h) : frame.fixed.is_next_1(_); Unit{}))
    case Some{x_0}:
      k(x_0, {==}, h)

# gen2 --ind: a helper (an inversion)
def frame.fixed.inv2(+s0: Nat, +st: Cr.Cir.State, +st2: Cr.Cir.State, +r: Maybe<&2, U32>, +h: {Cr.Cir.exec.set(s0, r, st) == Cr.Cir.Out.next{st2} : Cr.Cir.Out}, -G: Type, k: @+x_0: U32 -> @+h1: {r == Some{x_0} : Maybe<&2, U32>} -> @+h2: {Cr.Cir.exec.set(s0, Some{x_0}, st) == Cr.Cir.Out.next{st2} : Cr.Cir.Out} -> G) -> G:
  match r:
    case None{}:
      Empty.absurd(G, (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec.set(s0, None{}, st), Cr.Cir.Out.next{st2}, h) : frame.fixed.is_next_1(_); Unit{}))
    case Some{x_0}:
      k(x_0, {==}, h)

# gen2 --ind: a helper (a projection)
def frame.fixed.next_0_1(z: Cr.Cir.Out, d: Cr.Cir.State) -> Cr.Cir.State:
  match z:
    case Cr.Cir.Out.next{f0}:
      f0
    case _:
      d

def Lg.frame.fixed(f, s, st, st2, e):
  match f s:
    case 0n Cr.Cir.Stmt.nop{}:
      (%Equal.cong(Cr.Cir.Out, Cr.Cir.State, z => frame.fixed.next_0_1(z, st), Cr.Cir.Out.next{st}, Cr.Cir.Out.next{st2}, e) : {Lg.St.fixed(_) == Lg.St.fixed(st) : Lg.St.Fixed}; {==})
    case 0n Cr.Cir.Stmt.set{s0, s1}:
      frame.fixed.inv2(s0, st, st2, Cr.Cir.eval(s1, st), e, {Lg.St.fixed(st2) == Lg.St.fixed(st) : Lg.St.Fixed}, Som0 => h => h1 => frame.fixed.inv23(s0, st2, Som0, st, h1, {Lg.St.fixed(st2) == Lg.St.fixed(st) : Lg.St.Fixed}, Sta0 => Sta1 => Sta2 => Sta3 => Sta4 => Sta5 => Sta6 => Sta7 => Sta8 => Sta9 => h2 => h3 => frame.fixed.inv42(st2, Sta0, Sta1, Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9, Cr.Cir.regs.set.if(Cmp.is_lt(Nat.cmp(s0, List.length(&2, U32, Sta0))), Sta0, s0, Som0), h3, {Lg.St.fixed(st2) == Lg.St.fixed(st) : Lg.St.Fixed}, Som01 => h4 => h5 => (%Equal.cong(Cr.Cir.Out, Cr.Cir.State, z => frame.fixed.next_0_1(z, Cr.Cir.State{Som01, Sta1, Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9}), Cr.Cir.Out.next{Cr.Cir.State{Som01, Sta1, Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9}}, Cr.Cir.Out.next{st2}, h5) : {Lg.St.fixed(_) == Lg.St.fixed(st) : Lg.St.Fixed}; (%Equal.sym(Cr.Cir.State, st, Cr.Cir.State{Sta0, Sta1, Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9}, h2) : {Lg.St.Fixed{Sta6, Sta7, Sta3, Sta4} == Lg.St.fixed(_) : Lg.St.Fixed}; {==})))))
    case 0n Cr.Cir.Stmt.store{s01, s11, s2}:
      frame.fixed.inv4(s01, s2, st, st2, Cr.Cir.eval(s11, st), e, {Lg.St.fixed(st2) == Lg.St.fixed(st) : Lg.St.Fixed}, Som0 => h => h1 => frame.fixed.inv25(s01, st, st2, Som0, Cr.Cir.eval(s2, st), h1, {Lg.St.fixed(st2) == Lg.St.fixed(st) : Lg.St.Fixed}, Som01 => h2 => h3 => frame.fixed.inv43(s01, st2, Som0, Som01, st, h3, {Lg.St.fixed(st2) == Lg.St.fixed(st) : Lg.St.Fixed}, Sta0 => Sta1 => Sta2 => Sta3 => Sta4 => Sta5 => Sta6 => Sta7 => Sta8 => Sta9 => h4 => h5 => frame.fixed.inv57(s01, st2, Som0, Som01, Sta0, Sta1, Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9, h5, Bool.or(Bool.and(Bool.not(Cmp.is_eq(U32.cmp(Som0, 0))), Cmp.is_le(U32.cmp(Som0, Sta4))), Bool.and(Cmp.is_le(U32.cmp(Sta3, Som0)), Cmp.is_lt(U32.cmp(Som0, Sta2)))), h5, {Lg.St.fixed(st2) == Lg.St.fixed(st) : Lg.St.Fixed}, h6 => h7 => (%Equal.cong(Cr.Cir.Out, Cr.Cir.State, z => frame.fixed.next_0_1(z, Cr.Cir.State{Sta0, Cr.Cir.Cells.set(Sta1, Som0, Cr.Cir.Cell.set(s01, Cr.Cir.Cells.get(Sta1, Som0), Som01)), Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9}), Cr.Cir.Out.next{Cr.Cir.State{Sta0, Cr.Cir.Cells.set(Sta1, Som0, Cr.Cir.Cell.set(s01, Cr.Cir.Cells.get(Sta1, Som0), Som01)), Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9}}, Cr.Cir.Out.next{st2}, h7) : {Lg.St.fixed(_) == Lg.St.fixed(st) : Lg.St.Fixed}; (%Equal.sym(Cr.Cir.State, st, Cr.Cir.State{Sta0, Sta1, Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9}, h4) : {Lg.St.Fixed{Sta6, Sta7, Sta3, Sta4} == Lg.St.fixed(_) : Lg.St.Fixed}; {==}))))))
    case 0n Cr.Cir.Stmt.alloc{s02}:
      frame.fixed.inv5(s02, st2, st, e, {Lg.St.fixed(st2) == Lg.St.fixed(st) : Lg.St.Fixed}, Sta0 => Sta1 => Sta2 => Sta3 => Sta4 => Sta5 => Sta6 => Sta7 => Sta8 => Sta9 => h => h1 => frame.fixed.inv27(s02, st2, Sta0, Sta1, Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9, h1, Cmp.is_eq(U32.cmp(Sta9, 0)), h1, {Lg.St.fixed(st2) == Lg.St.fixed(st) : Lg.St.Fixed}, h2 => h3 => frame.fixed.inv45(s02, st2, Sta0, Sta1, Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9, h1, h2, h3, Cmp.is_lt(U32.cmp(Sta2, 214748364)), h3, {Lg.St.fixed(st2) == Lg.St.fixed(st) : Lg.St.Fixed}, h4 => h5 => frame.fixed.inv59(s02, st2, Sta0, Sta1, Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9, h1, h2, h3, h4, h5, Cr.Cir.room.if(Cmp.is_le(U32.cmp(U32.inc(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.add(U32.add(U32.shl(U32.shl(U32.shl(U32.shl(Sta2)))), U32.shl(U32.shl(Sta2))), 19)))))))))))))))))), Sta5)), Cmp.is_le(U32.cmp(U32.inc(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.add(U32.add(U32.shl(U32.shl(U32.shl(U32.shl(Sta2)))), U32.shl(U32.shl(Sta2))), 19)))))))))))))))))), Sta6)), Sta5, U32.inc(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.add(U32.add(U32.shl(U32.shl(U32.shl(U32.shl(Sta2)))), U32.shl(U32.shl(Sta2))), 19))))))))))))))))))), h5, {Lg.St.fixed(st2) == Lg.St.fixed(st) : Lg.St.Fixed}, Som0 => h6 => h7 => frame.fixed.inv69(st2, Sta0, Sta1, Sta2, Sta3, Sta4, Sta6, Sta7, Sta8, Sta9, h2, h4, Som0, Cr.Cir.regs.set.if(Cmp.is_lt(Nat.cmp(s02, List.length(&2, U32, Sta0))), Sta0, s02, Sta2), h7, {Lg.St.fixed(st2) == Lg.St.fixed(st) : Lg.St.Fixed}, Som01 => h8 => h9 => (%Equal.cong(Cr.Cir.Out, Cr.Cir.State, z => frame.fixed.next_0_1(z, Cr.Cir.State{Som01, Cr.Cir.Cells.set(Sta1, Sta2, Cr.Cir.Cell{0, 0, 0, 0, 0}), U32.inc(Sta2), Sta3, Sta4, Som0, Sta6, Sta7, Sta8, Sta9}), Cr.Cir.Out.next{Cr.Cir.State{Som01, Cr.Cir.Cells.set(Sta1, Sta2, Cr.Cir.Cell{0, 0, 0, 0, 0}), U32.inc(Sta2), Sta3, Sta4, Som0, Sta6, Sta7, Sta8, Sta9}}, Cr.Cir.Out.next{st2}, h9) : {Lg.St.fixed(_) == Lg.St.fixed(st) : Lg.St.Fixed}; (%Equal.sym(Cr.Cir.State, st, Cr.Cir.State{Sta0, Sta1, Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9}, h) : {Lg.St.Fixed{Sta6, Sta7, Sta3, Sta4} == Lg.St.fixed(_) : Lg.St.Fixed}; {==})))))))
    case 0n Cr.Cir.Stmt.emit{s03}:
      frame.fixed.inv7(st, st2, Cr.Cir.eval(s03, st), e, {Lg.St.fixed(st2) == Lg.St.fixed(st) : Lg.St.Fixed}, Som0 => h => h1 => frame.fixed.inv28(st2, Som0, st, h1, {Lg.St.fixed(st2) == Lg.St.fixed(st) : Lg.St.Fixed}, Sta0 => Sta1 => Sta2 => Sta3 => Sta4 => Sta5 => Sta6 => Sta7 => Sta8 => Sta9 => h2 => h3 => frame.fixed.inv47(st2, Som0, Sta0, Sta1, Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9, h3, Bool.and(Cmp.is_lt(U32.cmp(Sta2, 214748365)), Cmp.is_ge(U32.cmp(U32.add(U32.add(U32.shl(U32.shl(U32.shl(U32.shl(Sta2)))), U32.shl(U32.shl(Sta2))), Sta9), Sta9))), h3, {Lg.St.fixed(st2) == Lg.St.fixed(st) : Lg.St.Fixed}, h4 => h5 => frame.fixed.inv61(st2, Som0, Sta0, Sta1, Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9, h3, h4, h5, Cr.Cir.room.if(Cmp.is_le(U32.cmp(U32.inc(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.add(U32.add(U32.shl(U32.shl(U32.shl(U32.shl(Sta2)))), U32.shl(U32.shl(Sta2))), Sta9)))))))))))))))))), Sta5)), Cmp.is_le(U32.cmp(U32.inc(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.add(U32.add(U32.shl(U32.shl(U32.shl(U32.shl(Sta2)))), U32.shl(U32.shl(Sta2))), Sta9)))))))))))))))))), Sta6)), Sta5, U32.inc(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.add(U32.add(U32.shl(U32.shl(U32.shl(U32.shl(Sta2)))), U32.shl(U32.shl(Sta2))), Sta9))))))))))))))))))), h5, {Lg.St.fixed(st2) == Lg.St.fixed(st) : Lg.St.Fixed}, Som01 => h6 => h7 => (%Equal.cong(Cr.Cir.Out, Cr.Cir.State, z => frame.fixed.next_0_1(z, Cr.Cir.State{Sta0, Sta1, Sta2, Sta3, Sta4, Som01, Sta6, Sta7, Sd.Byte.from_u32(Som0) <> Sta8, U32.inc(Sta9)}), Cr.Cir.Out.next{Cr.Cir.State{Sta0, Sta1, Sta2, Sta3, Sta4, Som01, Sta6, Sta7, Sd.Byte.from_u32(Som0) <> Sta8, U32.inc(Sta9)}}, Cr.Cir.Out.next{st2}, h7) : {Lg.St.fixed(_) == Lg.St.fixed(st) : Lg.St.Fixed}; (%Equal.sym(Cr.Cir.State, st, Cr.Cir.State{Sta0, Sta1, Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9}, h2) : {Lg.St.Fixed{Sta6, Sta7, Sta3, Sta4} == Lg.St.fixed(_) : Lg.St.Fixed}; {==}))))))
    case 0n Cr.Cir.Stmt.seq{s04, s12}:
      frame.fixed.inv8(s12, st2, Cr.Cir.exec(0n, s04, st), e, {Lg.St.fixed(st2) == Lg.St.fixed(st) : Lg.St.Fixed}, nex0 => h => h1 => Equal.trans(Lg.St.Fixed, Lg.St.fixed(st2), Lg.St.fixed(nex0), Lg.St.fixed(st), Lg.frame.fixed(0n, s12, nex0, st2, h1), Lg.frame.fixed(0n, s04, st, nex0, h)))
    case 0n Cr.Cir.Stmt.if{s05, s13, s21}:
      frame.fixed.inv10(s13, s21, st, st2, Cr.Cir.eval(s05, st), e, {Lg.St.fixed(st2) == Lg.St.fixed(st) : Lg.St.Fixed}, Som0 => h => h1 => frame.fixed.case1(s13, s21, st, st2, Cmp.is_eq(U32.cmp(Som0, 0)), h1, {Lg.St.fixed(st2) == Lg.St.fixed(st) : Lg.St.Fixed}, h2 => h3 => Lg.frame.fixed(0n, s13, st, st2, h3), h2 => h3 => Lg.frame.fixed(0n, s21, st, st2, h3)))
    case 0n Cr.Cir.Stmt.while{s06, s14}:
      Empty.absurd({Lg.St.fixed(st2) == Lg.St.fixed(st) : Lg.St.Fixed}, (%Equal.sym(Cr.Cir.Out, Cr.Cir.Out.not_done{}, Cr.Cir.Out.next{st2}, e) : lg.Ends(_); Unit{}))
    case 0n Cr.Cir.Stmt.halt{s07}:
      Empty.absurd({Lg.St.fixed(st2) == Lg.St.fixed(st) : Lg.St.Fixed}, (%Equal.sym(Cr.Cir.Out, Cr.Cir.Out.halt{s07, st}, Cr.Cir.Out.next{st2}, e) : frame.fixed.is_next_1(_); Unit{}))
    case 1n+fp Cr.Cir.Stmt.nop{}:
      (%Equal.cong(Cr.Cir.Out, Cr.Cir.State, z => frame.fixed.next_0_1(z, st), Cr.Cir.Out.next{st}, Cr.Cir.Out.next{st2}, e) : {Lg.St.fixed(_) == Lg.St.fixed(st) : Lg.St.Fixed}; {==})
    case 1n+fp Cr.Cir.Stmt.set{s0, s1}:
      frame.fixed.inv2(s0, st, st2, Cr.Cir.eval(s1, st), e, {Lg.St.fixed(st2) == Lg.St.fixed(st) : Lg.St.Fixed}, Som0 => h => h1 => frame.fixed.inv23(s0, st2, Som0, st, h1, {Lg.St.fixed(st2) == Lg.St.fixed(st) : Lg.St.Fixed}, Sta0 => Sta1 => Sta2 => Sta3 => Sta4 => Sta5 => Sta6 => Sta7 => Sta8 => Sta9 => h2 => h3 => frame.fixed.inv42(st2, Sta0, Sta1, Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9, Cr.Cir.regs.set.if(Cmp.is_lt(Nat.cmp(s0, List.length(&2, U32, Sta0))), Sta0, s0, Som0), h3, {Lg.St.fixed(st2) == Lg.St.fixed(st) : Lg.St.Fixed}, Som01 => h4 => h5 => (%Equal.cong(Cr.Cir.Out, Cr.Cir.State, z => frame.fixed.next_0_1(z, Cr.Cir.State{Som01, Sta1, Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9}), Cr.Cir.Out.next{Cr.Cir.State{Som01, Sta1, Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9}}, Cr.Cir.Out.next{st2}, h5) : {Lg.St.fixed(_) == Lg.St.fixed(st) : Lg.St.Fixed}; (%Equal.sym(Cr.Cir.State, st, Cr.Cir.State{Sta0, Sta1, Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9}, h2) : {Lg.St.Fixed{Sta6, Sta7, Sta3, Sta4} == Lg.St.fixed(_) : Lg.St.Fixed}; {==})))))
    case 1n+fp Cr.Cir.Stmt.store{s01, s11, s2}:
      frame.fixed.inv4(s01, s2, st, st2, Cr.Cir.eval(s11, st), e, {Lg.St.fixed(st2) == Lg.St.fixed(st) : Lg.St.Fixed}, Som0 => h => h1 => frame.fixed.inv25(s01, st, st2, Som0, Cr.Cir.eval(s2, st), h1, {Lg.St.fixed(st2) == Lg.St.fixed(st) : Lg.St.Fixed}, Som01 => h2 => h3 => frame.fixed.inv43(s01, st2, Som0, Som01, st, h3, {Lg.St.fixed(st2) == Lg.St.fixed(st) : Lg.St.Fixed}, Sta0 => Sta1 => Sta2 => Sta3 => Sta4 => Sta5 => Sta6 => Sta7 => Sta8 => Sta9 => h4 => h5 => frame.fixed.inv57(s01, st2, Som0, Som01, Sta0, Sta1, Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9, h5, Bool.or(Bool.and(Bool.not(Cmp.is_eq(U32.cmp(Som0, 0))), Cmp.is_le(U32.cmp(Som0, Sta4))), Bool.and(Cmp.is_le(U32.cmp(Sta3, Som0)), Cmp.is_lt(U32.cmp(Som0, Sta2)))), h5, {Lg.St.fixed(st2) == Lg.St.fixed(st) : Lg.St.Fixed}, h6 => h7 => (%Equal.cong(Cr.Cir.Out, Cr.Cir.State, z => frame.fixed.next_0_1(z, Cr.Cir.State{Sta0, Cr.Cir.Cells.set(Sta1, Som0, Cr.Cir.Cell.set(s01, Cr.Cir.Cells.get(Sta1, Som0), Som01)), Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9}), Cr.Cir.Out.next{Cr.Cir.State{Sta0, Cr.Cir.Cells.set(Sta1, Som0, Cr.Cir.Cell.set(s01, Cr.Cir.Cells.get(Sta1, Som0), Som01)), Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9}}, Cr.Cir.Out.next{st2}, h7) : {Lg.St.fixed(_) == Lg.St.fixed(st) : Lg.St.Fixed}; (%Equal.sym(Cr.Cir.State, st, Cr.Cir.State{Sta0, Sta1, Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9}, h4) : {Lg.St.Fixed{Sta6, Sta7, Sta3, Sta4} == Lg.St.fixed(_) : Lg.St.Fixed}; {==}))))))
    case 1n+fp Cr.Cir.Stmt.alloc{s02}:
      frame.fixed.inv5(s02, st2, st, e, {Lg.St.fixed(st2) == Lg.St.fixed(st) : Lg.St.Fixed}, Sta0 => Sta1 => Sta2 => Sta3 => Sta4 => Sta5 => Sta6 => Sta7 => Sta8 => Sta9 => h => h1 => frame.fixed.inv27(s02, st2, Sta0, Sta1, Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9, h1, Cmp.is_eq(U32.cmp(Sta9, 0)), h1, {Lg.St.fixed(st2) == Lg.St.fixed(st) : Lg.St.Fixed}, h2 => h3 => frame.fixed.inv45(s02, st2, Sta0, Sta1, Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9, h1, h2, h3, Cmp.is_lt(U32.cmp(Sta2, 214748364)), h3, {Lg.St.fixed(st2) == Lg.St.fixed(st) : Lg.St.Fixed}, h4 => h5 => frame.fixed.inv59(s02, st2, Sta0, Sta1, Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9, h1, h2, h3, h4, h5, Cr.Cir.room.if(Cmp.is_le(U32.cmp(U32.inc(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.add(U32.add(U32.shl(U32.shl(U32.shl(U32.shl(Sta2)))), U32.shl(U32.shl(Sta2))), 19)))))))))))))))))), Sta5)), Cmp.is_le(U32.cmp(U32.inc(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.add(U32.add(U32.shl(U32.shl(U32.shl(U32.shl(Sta2)))), U32.shl(U32.shl(Sta2))), 19)))))))))))))))))), Sta6)), Sta5, U32.inc(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.add(U32.add(U32.shl(U32.shl(U32.shl(U32.shl(Sta2)))), U32.shl(U32.shl(Sta2))), 19))))))))))))))))))), h5, {Lg.St.fixed(st2) == Lg.St.fixed(st) : Lg.St.Fixed}, Som0 => h6 => h7 => frame.fixed.inv69(st2, Sta0, Sta1, Sta2, Sta3, Sta4, Sta6, Sta7, Sta8, Sta9, h2, h4, Som0, Cr.Cir.regs.set.if(Cmp.is_lt(Nat.cmp(s02, List.length(&2, U32, Sta0))), Sta0, s02, Sta2), h7, {Lg.St.fixed(st2) == Lg.St.fixed(st) : Lg.St.Fixed}, Som01 => h8 => h9 => (%Equal.cong(Cr.Cir.Out, Cr.Cir.State, z => frame.fixed.next_0_1(z, Cr.Cir.State{Som01, Cr.Cir.Cells.set(Sta1, Sta2, Cr.Cir.Cell{0, 0, 0, 0, 0}), U32.inc(Sta2), Sta3, Sta4, Som0, Sta6, Sta7, Sta8, Sta9}), Cr.Cir.Out.next{Cr.Cir.State{Som01, Cr.Cir.Cells.set(Sta1, Sta2, Cr.Cir.Cell{0, 0, 0, 0, 0}), U32.inc(Sta2), Sta3, Sta4, Som0, Sta6, Sta7, Sta8, Sta9}}, Cr.Cir.Out.next{st2}, h9) : {Lg.St.fixed(_) == Lg.St.fixed(st) : Lg.St.Fixed}; (%Equal.sym(Cr.Cir.State, st, Cr.Cir.State{Sta0, Sta1, Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9}, h) : {Lg.St.Fixed{Sta6, Sta7, Sta3, Sta4} == Lg.St.fixed(_) : Lg.St.Fixed}; {==})))))))
    case 1n+fp Cr.Cir.Stmt.emit{s03}:
      frame.fixed.inv7(st, st2, Cr.Cir.eval(s03, st), e, {Lg.St.fixed(st2) == Lg.St.fixed(st) : Lg.St.Fixed}, Som0 => h => h1 => frame.fixed.inv28(st2, Som0, st, h1, {Lg.St.fixed(st2) == Lg.St.fixed(st) : Lg.St.Fixed}, Sta0 => Sta1 => Sta2 => Sta3 => Sta4 => Sta5 => Sta6 => Sta7 => Sta8 => Sta9 => h2 => h3 => frame.fixed.inv47(st2, Som0, Sta0, Sta1, Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9, h3, Bool.and(Cmp.is_lt(U32.cmp(Sta2, 214748365)), Cmp.is_ge(U32.cmp(U32.add(U32.add(U32.shl(U32.shl(U32.shl(U32.shl(Sta2)))), U32.shl(U32.shl(Sta2))), Sta9), Sta9))), h3, {Lg.St.fixed(st2) == Lg.St.fixed(st) : Lg.St.Fixed}, h4 => h5 => frame.fixed.inv61(st2, Som0, Sta0, Sta1, Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9, h3, h4, h5, Cr.Cir.room.if(Cmp.is_le(U32.cmp(U32.inc(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.add(U32.add(U32.shl(U32.shl(U32.shl(U32.shl(Sta2)))), U32.shl(U32.shl(Sta2))), Sta9)))))))))))))))))), Sta5)), Cmp.is_le(U32.cmp(U32.inc(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.add(U32.add(U32.shl(U32.shl(U32.shl(U32.shl(Sta2)))), U32.shl(U32.shl(Sta2))), Sta9)))))))))))))))))), Sta6)), Sta5, U32.inc(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.add(U32.add(U32.shl(U32.shl(U32.shl(U32.shl(Sta2)))), U32.shl(U32.shl(Sta2))), Sta9))))))))))))))))))), h5, {Lg.St.fixed(st2) == Lg.St.fixed(st) : Lg.St.Fixed}, Som01 => h6 => h7 => (%Equal.cong(Cr.Cir.Out, Cr.Cir.State, z => frame.fixed.next_0_1(z, Cr.Cir.State{Sta0, Sta1, Sta2, Sta3, Sta4, Som01, Sta6, Sta7, Sd.Byte.from_u32(Som0) <> Sta8, U32.inc(Sta9)}), Cr.Cir.Out.next{Cr.Cir.State{Sta0, Sta1, Sta2, Sta3, Sta4, Som01, Sta6, Sta7, Sd.Byte.from_u32(Som0) <> Sta8, U32.inc(Sta9)}}, Cr.Cir.Out.next{st2}, h7) : {Lg.St.fixed(_) == Lg.St.fixed(st) : Lg.St.Fixed}; (%Equal.sym(Cr.Cir.State, st, Cr.Cir.State{Sta0, Sta1, Sta2, Sta3, Sta4, Sta5, Sta6, Sta7, Sta8, Sta9}, h2) : {Lg.St.Fixed{Sta6, Sta7, Sta3, Sta4} == Lg.St.fixed(_) : Lg.St.Fixed}; {==}))))))
    case 1n+fp Cr.Cir.Stmt.seq{s04, s12}:
      frame.fixed.inv18(fp, s12, st2, Cr.Cir.exec(1n+fp, s04, st), e, {Lg.St.fixed(st2) == Lg.St.fixed(st) : Lg.St.Fixed}, nex0 => h => h1 => Equal.trans(Lg.St.Fixed, Lg.St.fixed(st2), Lg.St.fixed(nex0), Lg.St.fixed(st), Lg.frame.fixed(1n+fp, s12, nex0, st2, h1), Lg.frame.fixed(1n+fp, s04, st, nex0, h)))
    case 1n+fp Cr.Cir.Stmt.if{s05, s13, s21}:
      frame.fixed.inv20(fp, s13, s21, st, st2, Cr.Cir.eval(s05, st), e, {Lg.St.fixed(st2) == Lg.St.fixed(st) : Lg.St.Fixed}, Som0 => h => h1 => frame.fixed.case2(fp, s13, s21, st, st2, Cmp.is_eq(U32.cmp(Som0, 0)), h1, {Lg.St.fixed(st2) == Lg.St.fixed(st) : Lg.St.Fixed}, h2 => h3 => Lg.frame.fixed(1n+fp, s13, st, st2, h3), h2 => h3 => Lg.frame.fixed(1n+fp, s21, st, st2, h3)))
    case 1n+fp Cr.Cir.Stmt.while{s06, s14}:
      frame.fixed.inv22(fp, s06, s14, st, st2, e, Cr.Cir.eval(s06, st), e, {Lg.St.fixed(st2) == Lg.St.fixed(st) : Lg.St.Fixed}, Som0 => h => h1 => frame.fixed.case3(fp, s06, s14, st, st2, e, Cmp.is_eq(U32.cmp(Som0, 0)), h1, {Lg.St.fixed(st2) == Lg.St.fixed(st) : Lg.St.Fixed}, h2 => h3 => frame.fixed.inv55(fp, s06, s14, st2, Cr.Cir.exec(fp, s14, st), h3, {Lg.St.fixed(st2) == Lg.St.fixed(st) : Lg.St.Fixed}, nex0 => h4 => h5 => Equal.trans(Lg.St.Fixed, Lg.St.fixed(st2), Lg.St.fixed(nex0), Lg.St.fixed(st), Lg.frame.fixed(fp, Cr.Cir.Stmt.while{s06, s14}, nex0, st2, h5), Lg.frame.fixed(fp, s14, st, nex0, h4))), h2 => h3 => (%Equal.cong(Cr.Cir.Out, Cr.Cir.State, z => frame.fixed.next_0_1(z, st), Cr.Cir.Out.next{st}, Cr.Cir.Out.next{st2}, h3) : {Lg.St.fixed(_) == Lg.St.fixed(st) : Lg.St.Fixed}; {==})))
    case 1n+fp Cr.Cir.Stmt.halt{s07}:
      Empty.absurd({Lg.St.fixed(st2) == Lg.St.fixed(st) : Lg.St.Fixed}, (%Equal.sym(Cr.Cir.Out, Cr.Cir.Out.halt{s07, st}, Cr.Cir.Out.next{st2}, e) : frame.fixed.is_next_1(_); Unit{}))

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

def Lg.tot.if(c, y, n, st, b, Q, H, v, e, t):
  match t:
    case Tuple{+f, ok}:
      (f, lg.if.ok(f, c, y, n, st, b, Q, H, v, e, ok))

def Lg.tot.wk(s, st, b, b2, Q, Q2, H, H2, hb, hq, hh, t):
  match t:
    case Tuple{+f, ok}:
      (f, lg.ok.wk(Cr.Cir.exec(f, s, st), Lg.Lim(st), b, b2, Q, Q2, H, H2, hb, hq, hh, ok))

# a sequence whose first part ends at x with the fuel f1, and whose second
# ends from x with the fuel f2, ends so with the fuel f1 + f2
def lg.seq.eq(+f1: Nat, +f2: Nat, +a: Cr.Cir.Stmt, +c: Cr.Cir.Stmt, +st: Cr.Cir.State, +x: Cr.Cir.State,
  +eq: {Cr.Cir.exec(f1, a, st) == Cr.Cir.Out.next{x} : Cr.Cir.Out}, +d2: {Lg.Out.done(Cr.Cir.exec(f2, c, x)) == True{} : Bool}) ->
  {Cr.Cir.exec(Nat.add(f1, f2), Cr.Cir.Stmt.seq{a, c}, st) == Cr.Cir.exec(f2, c, x) : Cr.Cir.Out}:
  +ea = Equal.trans(Cr.Cir.Out, Cr.Cir.exec(Nat.add(f1, f2), a, st), Cr.Cir.exec(f1, a, st), Cr.Cir.Out.next{x},
    Lg.exec.more(f1, f2, a, st, Equal.cong(Cr.Cir.Out, Bool, o => Lg.Out.done(o), Cr.Cir.exec(f1, a, st), Cr.Cir.Out.next{x}, eq)), eq)
  +e2 = Equal.cong(Cr.Cir.Out, Cr.Cir.Out, o => Cr.Cir.exec.then(o, t => Cr.Cir.exec(Nat.add(f1, f2), c, t)),
    Cr.Cir.exec(Nat.add(f1, f2), a, st), Cr.Cir.Out.next{x}, ea)
  +e3 = Equal.trans(Cr.Cir.Out, Cr.Cir.exec(Nat.add(f1, f2), c, x), Cr.Cir.exec(Nat.add(f2, f1), c, x), Cr.Cir.exec(f2, c, x),
    Equal.cong(Nat, Cr.Cir.Out, g => Cr.Cir.exec(g, c, x), Nat.add(f1, f2), Nat.add(f2, f1), lg.add_comm(f1, f2)),
    Lg.exec.more(f2, f1, c, x, d2))
  Equal.trans(Cr.Cir.Out, Cr.Cir.exec(Nat.add(f1, f2), Cr.Cir.Stmt.seq{a, c}, st), Cr.Cir.exec(Nat.add(f1, f2), c, x), Cr.Cir.exec(f2, c, x),
    Equal.trans(Cr.Cir.Out, Cr.Cir.exec(Nat.add(f1, f2), Cr.Cir.Stmt.seq{a, c}, st),
      Cr.Cir.exec.then(Cr.Cir.exec(Nat.add(f1, f2), a, st), t => Cr.Cir.exec(Nat.add(f1, f2), c, t)), Cr.Cir.exec(Nat.add(f1, f2), c, x),
      lg.exec.seq(Nat.add(f1, f2), a, c, st), e2),
    e3)

# a sequence whose first part stops (a halt, out of memory) with the fuel f1
def lg.seq.stop(+f1: Nat, +a: Cr.Cir.Stmt, +c: Cr.Cir.Stmt, +st: Cr.Cir.State, +o: Cr.Cir.Out,
  +eq: {Cr.Cir.exec(f1, a, st) == o : Cr.Cir.Out}) ->
  {Cr.Cir.exec(f1, Cr.Cir.Stmt.seq{a, c}, st) == Cr.Cir.exec.then(o, t => Cr.Cir.exec(f1, c, t)) : Cr.Cir.Out}:
  Equal.trans(Cr.Cir.Out, Cr.Cir.exec(f1, Cr.Cir.Stmt.seq{a, c}, st), Cr.Cir.exec.then(Cr.Cir.exec(f1, a, st), t => Cr.Cir.exec(f1, c, t)),
    Cr.Cir.exec.then(o, t => Cr.Cir.exec(f1, c, t)), lg.exec.seq(f1, a, c, st),
    Equal.cong(Cr.Cir.Out, Cr.Cir.Out, p => Cr.Cir.exec.then(p, t => Cr.Cir.exec(f1, c, t)), Cr.Cir.exec(f1, a, st), o, eq))

def lg.seq.next(+f1: Nat, +f2: Nat, +a: Cr.Cir.Stmt, +c: Cr.Cir.Stmt, +st: Cr.Cir.State, +x: Cr.Cir.State, +b: Nat,
  -Q: Cr.Cir.State -> Type, -H: U32 -> Cr.Cir.State -> Type, +eq: {Cr.Cir.exec(f1, a, st) == Cr.Cir.Out.next{x} : Cr.Cir.Out},
  +d2: {Lg.Out.done(Cr.Cir.exec(f2, c, x)) == True{} : Bool}, ok2: Lg.Ok(Cr.Cir.exec(f2, c, x), Lg.Lim(x), b, Q, H)) ->
  Lg.Ok(Cr.Cir.exec(Nat.add(f1, f2), Cr.Cir.Stmt.seq{a, c}, st), Lg.Lim(st), b, Q, H):
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(Nat.add(f1, f2), Cr.Cir.Stmt.seq{a, c}, st), Cr.Cir.exec(f2, c, x), lg.seq.eq(f1, f2, a, c, st, x, eq, d2)) :
    Lg.Ok(_, Lg.Lim(st), b, Q, H)
  %lg.lim.eq(x, st, Lg.frame.fixed(f1, a, st, x, eq)) : Lg.Ok(Cr.Cir.exec(f2, c, x), _, b, Q, H)
  ok2

def lg.seq.halt(+f1: Nat, +a: Cr.Cir.Stmt, +c: Cr.Cir.Stmt, +st: Cr.Cir.State, +b: Nat, -Q: Cr.Cir.State -> Type,
  -H: U32 -> Cr.Cir.State -> Type, +k: U32, +x: Cr.Cir.State, +eq: {Cr.Cir.exec(f1, a, st) == Cr.Cir.Out.halt{k, x} : Cr.Cir.Out},
  ok: H(k, x)) -> Lg.Ok(Cr.Cir.exec(f1, Cr.Cir.Stmt.seq{a, c}, st), Lg.Lim(st), b, Q, H):
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f1, Cr.Cir.Stmt.seq{a, c}, st), Cr.Cir.exec.then(Cr.Cir.Out.halt{k, x}, t => Cr.Cir.exec(f1, c, t)),
    lg.seq.stop(f1, a, c, st, Cr.Cir.Out.halt{k, x}, eq)) : Lg.Ok(_, Lg.Lim(st), b, Q, H)
  ok

def lg.seq.oom(+f1: Nat, +a: Cr.Cir.Stmt, +c: Cr.Cir.Stmt, +st: Cr.Cir.State, +b: Nat, -Q: Cr.Cir.State -> Type,
  -H: U32 -> Cr.Cir.State -> Type, +eq: {Cr.Cir.exec(f1, a, st) == Cr.Cir.Out.out_of_memory{} : Cr.Cir.Out},
  +ok: {Nat.is_lt(Lg.Lim(st), b) == True{} : Bool}) -> Lg.Ok(Cr.Cir.exec(f1, Cr.Cir.Stmt.seq{a, c}, st), Lg.Lim(st), b, Q, H):
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f1, Cr.Cir.Stmt.seq{a, c}, st), Cr.Cir.exec.then(Cr.Cir.Out.out_of_memory{}, t => Cr.Cir.exec(f1, c, t)),
    lg.seq.stop(f1, a, c, st, Cr.Cir.Out.out_of_memory{}, eq)) : Lg.Ok(_, Lg.Lim(st), b, Q, H)
  ok

# the next case of tot.seq, with the second part's run ended
def lg.seq.pair(+f1: Nat, +f2: Nat, +a: Cr.Cir.Stmt, +c: Cr.Cir.Stmt, +st: Cr.Cir.State, +x: Cr.Cir.State, +b: Nat,
  -Q: Cr.Cir.State -> Type, -H: U32 -> Cr.Cir.State -> Type, +eq: {Cr.Cir.exec(f1, a, st) == Cr.Cir.Out.next{x} : Cr.Cir.Out},
  p: {Lg.Out.done(Cr.Cir.exec(f2, c, x)) == True{} : Bool} & Lg.Ok(Cr.Cir.exec(f2, c, x), Lg.Lim(x), b, Q, H)) ->
  Lg.Tot(Cr.Cir.Stmt.seq{a, c}, st, b, Q, H):
  match p:
    case Tuple{+d2, ok2}:
      (Nat.add(f1, f2), lg.seq.next(f1, f2, a, c, st, x, b, Q, H, eq, d2, ok2))

# tot.seq by the outcome o of the first part with its fuel f1
def lg.seq.go(o: Cr.Cir.Out, +f1: Nat, +a: Cr.Cir.Stmt, +c: Cr.Cir.Stmt, +st: Cr.Cir.State, +b: Nat, -Q: Cr.Cir.State -> Type,
  -H: U32 -> Cr.Cir.State -> Type, +eq: {Cr.Cir.exec(f1, a, st) == o : Cr.Cir.Out},
  ok: Lg.Ok(o, Lg.Lim(st), b, x => Lg.Tot(c, x, b, Q, H), H)) -> Lg.Tot(Cr.Cir.Stmt.seq{a, c}, st, b, Q, H):
  match o:
    case Cr.Cir.Out.next{+x}:
      match ok:
        case Tuple{+f2, ok2}:
          lg.seq.pair(f1, f2, a, c, st, x, b, Q, H, eq, lg.ok.done(Cr.Cir.exec(f2, c, x), Lg.Lim(x), b, Q, H, ok2))
    case Cr.Cir.Out.halt{+k, +x}:
      (f1, lg.seq.halt(f1, a, c, st, b, Q, H, k, x, eq, ok))
    case Cr.Cir.Out.out_of_memory{}:
      (f1, lg.seq.oom(f1, a, c, st, b, Q, H, eq, ok))
    case Cr.Cir.Out.trap{}:
      match ok:
    case Cr.Cir.Out.not_done{}:
      match ok:

def Lg.tot.seq(a, c, st, b, Q, H, t):
  match t:
    case Tuple{+f1, ok1}:
      lg.seq.go(Cr.Cir.exec(f1, a, st), f1, a, c, st, b, Q, H, {==}, ok1)

# a store's run, once its fuel is known: as Cir.exec.store
def lg.store.go(+f: Nat, +k: Nat, +c: Cr.Cir.Expr, +e: Cr.Cir.Expr, +st: Cr.Cir.State, +i: U32, +v: U32,
  +hc: {Cr.Cir.eval(c, st) == Some{i} : Maybe<&2, U32>}, +he: {Cr.Cir.eval(e, st) == Some{v} : Maybe<&2, U32>},
  +hi: {Lg.St.is_cell(st, i) == True{} : Bool}) ->
  {Cr.Cir.exec.store(k, Cr.Cir.eval(c, st), Cr.Cir.eval(e, st), st) == Cr.Cir.Out.next{Lg.St.store(st, k, i, v)} : Cr.Cir.Out}:
  match st:
    case Cr.Cir.State{+regs, +cells, +next, +first, +image, +pages, +limit, +input, +out, +outn}:
      %Equal.sym(Maybe<&2, U32>, Cr.Cir.eval(c, Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}), Some{i}, hc) :
        {Cr.Cir.exec.store(k, _, Cr.Cir.eval(e, Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}), Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}) == Cr.Cir.Out.next{Lg.St.store(Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}, k, i, v)} : Cr.Cir.Out}
      %Equal.sym(Maybe<&2, U32>, Cr.Cir.eval(e, Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}), Some{v}, he) :
        {Cr.Cir.exec.store(k, Some{i}, _, Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}) == Cr.Cir.Out.next{Lg.St.store(Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}, k, i, v)} : Cr.Cir.Out}
      %Equal.sym(Bool, Cr.Cir.is_cell(i, image, first, next), True{}, hi) :
        {Cr.Cir.exec.store.if(_, k, i, v, Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}) == Cr.Cir.Out.next{Lg.St.store(Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}, k, i, v)} : Cr.Cir.Out}
      {==}

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
  match f:
    case 0n:
      lg.store.go(0n, k, c, e, st, i, v, hc, he, hi)
    case 1n+p:
      lg.store.go(1n+p, k, c, e, st, i, v, hc, he, hi)

def Lg.exec.alloc(f, r, st, hr, ho):
  ?TODO

def Lg.wp.set(r, e, st, b, K, H, v, he, hr, q):
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(0n, Cr.Cir.Stmt.set{r, e}, st), Cr.Cir.Out.next{Lg.St.set(st, r, v)}, Lg.exec.set(0n, r, e, st, v, he, hr)) :
    Lg.WP.ok(_, Lg.Lim(st), b, K, H)
  q

def Lg.wp.store(k, c, e, st, b, K, H, i, v, hc, he, hi, q):
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(0n, Cr.Cir.Stmt.store{k, c, e}, st), Cr.Cir.Out.next{Lg.St.store(st, k, i, v)}, Lg.exec.store(0n, k, c, e, st, i, v, hc, he, hi)) :
    Lg.WP.ok(_, Lg.Lim(st), b, K, H)
  q

def Lg.wp.alloc(r, st, b, K, H, hr, ho, hb, q):
  ?TODO

def Lg.wp.emit(e, st, b, K, H, v, he, hb, q):
  ?TODO

def Lg.tot.any(s, st, b, Q, H, t, g):
  ?TODO

def Lg.tot.while(c, body, b, I, Q, H, r, n, st, i):
  ?TODO

# a primitive's WP.ok is its Ok
def lg.wpok(o: Cr.Cir.Out, +lim: Nat, +b: Nat, -K: (U32 -> Cr.Cir.State -> Type) -> Cr.Cir.State -> Type,
  -H: U32 -> Cr.Cir.State -> Type, w: Lg.WP.ok(o, lim, b, K, H)) -> Lg.Ok(o, lim, b, x => K(H, x), H):
  match o:
    case Cr.Cir.Out.next{x}:
      w
    case Cr.Cir.Out.halt{k, x}:
      w
    case Cr.Cir.Out.out_of_memory{}:
      w
    case Cr.Cir.Out.trap{}:
      w
    case Cr.Cir.Out.not_done{}:
      w

# tot.of_wp for an if, by z = U32.is_zero of its condition's value x
def lg.ofwp.pick(z: Bool, +x: U32, +hz: {U32.is_zero(x) == z : Bool}, +c: Cr.Cir.Expr, +t: Cr.Cir.Stmt, +e: Cr.Cir.Stmt,
  +st: Cr.Cir.State, +b: Nat, -K: (U32 -> Cr.Cir.State -> Type) -> Cr.Cir.State -> Type, -H: U32 -> Cr.Cir.State -> Type,
  +ev: {Cr.Cir.eval(c, st) == Some{x} : Maybe<&2, U32>},
  w: Lg.WP.pick(z, k => h => Lg.WP(t, b, q => y => k(q, y), j => y => h(j, y), st),
    k => h => Lg.WP(e, b, q => y => k(q, y), j => y => h(j, y), st), K, H),
  iht: Lg.WP(t, b, q => y => K(q, y), j => y => H(j, y), st) -> Lg.Tot(t, st, b, y => K(H, y), H),
  ihe: Lg.WP(e, b, q => y => K(q, y), j => y => H(j, y), st) -> Lg.Tot(e, st, b, y => K(H, y), H)) ->
  Lg.Tot(Cr.Cir.Stmt.if{c, t, e}, st, b, y => K(H, y), H):
  match z:
    case False{}:
      Lg.tot.if(c, t, e, st, b, y => K(H, y), H, x, ev,
        (%Equal.sym(Bool, U32.is_zero(x), False{}, hz) : Lg.Tot(Bool.pick(Cr.Cir.Stmt, _, e, t), st, b, y => K(H, y), H); iht(w)))
    case True{}:
      Lg.tot.if(c, t, e, st, b, y => K(H, y), H, x, ev,
        (%Equal.sym(Bool, U32.is_zero(x), True{}, hz) : Lg.Tot(Bool.pick(Cr.Cir.Stmt, _, e, t), st, b, y => K(H, y), H); ihe(w)))

# tot.of_wp for an if, by its condition's value v
def lg.ofwp.if(v: Maybe<&2, U32>, +c: Cr.Cir.Expr, +t: Cr.Cir.Stmt, +e: Cr.Cir.Stmt, +st: Cr.Cir.State, +b: Nat,
  -K: (U32 -> Cr.Cir.State -> Type) -> Cr.Cir.State -> Type, -H: U32 -> Cr.Cir.State -> Type,
  +ev: {Cr.Cir.eval(c, st) == v : Maybe<&2, U32>},
  w: Lg.WP.if(v, k => h => Lg.WP(t, b, q => y => k(q, y), j => y => h(j, y), st),
    k => h => Lg.WP(e, b, q => y => k(q, y), j => y => h(j, y), st), K, H),
  iht: Lg.WP(t, b, q => y => K(q, y), j => y => H(j, y), st) -> Lg.Tot(t, st, b, y => K(H, y), H),
  ihe: Lg.WP(e, b, q => y => K(q, y), j => y => H(j, y), st) -> Lg.Tot(e, st, b, y => K(H, y), H)) ->
  Lg.Tot(Cr.Cir.Stmt.if{c, t, e}, st, b, y => K(H, y), H):
  match v:
    case Some{+x}:
      lg.ofwp.pick(U32.is_zero(x), x, {==}, c, t, e, st, b, K, H, ev, w, iht, ihe)
    case None{}:
      match w:

def Lg.tot.of_wp(s, st, b, K, H, w):
  match s:
    case Cr.Cir.Stmt.nop{}:
      (0n, w)
    case Cr.Cir.Stmt.set{r, e}:
      (0n, lg.wpok(Cr.Cir.exec(0n, Cr.Cir.Stmt.set{r, e}, st), Lg.Lim(st), b, K, H, w))
    case Cr.Cir.Stmt.store{k, c, v}:
      (0n, lg.wpok(Cr.Cir.exec(0n, Cr.Cir.Stmt.store{k, c, v}, st), Lg.Lim(st), b, K, H, w))
    case Cr.Cir.Stmt.alloc{r}:
      (0n, lg.wpok(Cr.Cir.exec(0n, Cr.Cir.Stmt.alloc{r}, st), Lg.Lim(st), b, K, H, w))
    case Cr.Cir.Stmt.emit{v}:
      (0n, lg.wpok(Cr.Cir.exec(0n, Cr.Cir.Stmt.emit{v}, st), Lg.Lim(st), b, K, H, w))
    case Cr.Cir.Stmt.seq{+a, +c}:
      Lg.tot.seq(a, c, st, b, y => K(H, y), H,
        Lg.tot.wk(a, st, b, b, x => Lg.WP(c, b, k => y => K(k, y), j => y => H(j, y), x), x => Lg.Tot(c, x, b, y => K(H, y), H),
          j => y => H(j, y), H, lg.le_refl(b),
          x => wx => Lg.tot.of_wp(c, x, b, k => y => K(k, y), j => y => H(j, y), wx), k => x => hx => hx,
          Lg.tot.of_wp(a, st, b, h => x => Lg.WP(c, b, k => y => K(k, y), j => y => h(j, y), x), j => y => H(j, y), w)))
    case Cr.Cir.Stmt.if{+c, +t, +e}:
      lg.ofwp.if(Cr.Cir.eval(c, st), c, t, e, st, b, K, H, {==}, w,
        wt => Lg.tot.of_wp(t, st, b, q => y => K(q, y), j => y => H(j, y), wt),
        we => Lg.tot.of_wp(e, st, b, q => y => K(q, y), j => y => H(j, y), we))
    case Cr.Cir.Stmt.while{c, body}:
      w
    case Cr.Cir.Stmt.halt{k}:
      (0n, w)

# s has no seq, if or while
def lg.is_prim(s: Cr.Cir.Stmt) -> Bool:
  match s:
    case Cr.Cir.Stmt.seq{_, _}:
      False{}
    case Cr.Cir.Stmt.if{_, _, _}:
      False{}
    case Cr.Cir.Stmt.while{_, _}:
      False{}
    case _:
      True{}

# a primitive runs the same with any fuel
def lg.prim.ok(+f: Nat, +s: Cr.Cir.Stmt, +st: Cr.Cir.State, +lim: Nat, +b: Nat, -Q: Cr.Cir.State -> Type,
  -H: U32 -> Cr.Cir.State -> Type, +np: {lg.is_prim(s) == True{} : Bool}, ok: Lg.Ok(Cr.Cir.exec(f, s, st), lim, b, Q, H)) ->
  Lg.Ok(Cr.Cir.exec(0n, s, st), lim, b, Q, H):
  match f:
    case 0n:
      ok
    case 1n+p:
      match s:
        case Cr.Cir.Stmt.nop{}:
          ok
        case Cr.Cir.Stmt.set{r, e}:
          ok
        case Cr.Cir.Stmt.store{k, c, v}:
          ok
        case Cr.Cir.Stmt.alloc{r}:
          ok
        case Cr.Cir.Stmt.emit{v}:
          ok
        case Cr.Cir.Stmt.seq{a, c}:
          K.bool.ff(Lg.Ok(Cr.Cir.exec(0n, Cr.Cir.Stmt.seq{a, c}, st), lim, b, Q, H), np)
        case Cr.Cir.Stmt.if{c, t, e}:
          K.bool.ff(Lg.Ok(Cr.Cir.exec(0n, Cr.Cir.Stmt.if{c, t, e}, st), lim, b, Q, H), np)
        case Cr.Cir.Stmt.while{c, body}:
          K.bool.ff(Lg.Ok(Cr.Cir.exec(0n, Cr.Cir.Stmt.while{c, body}, st), lim, b, Q, H), np)
        case Cr.Cir.Stmt.halt{k}:
          ok

# a primitive's Ok is its WP.ok
def lg.okwp(o: Cr.Cir.Out, +lim: Nat, +b: Nat, -K: (U32 -> Cr.Cir.State -> Type) -> Cr.Cir.State -> Type,
  -H: U32 -> Cr.Cir.State -> Type, w: Lg.Ok(o, lim, b, x => K(H, x), H)) -> Lg.WP.ok(o, lim, b, K, H):
  match o:
    case Cr.Cir.Out.next{x}:
      w
    case Cr.Cir.Out.halt{k, x}:
      w
    case Cr.Cir.Out.out_of_memory{}:
      w
    case Cr.Cir.Out.trap{}:
      w
    case Cr.Cir.Out.not_done{}:
      w

# the WP.ok of a primitive from its Tot
def lg.prim.wp(+s: Cr.Cir.Stmt, +st: Cr.Cir.State, +b: Nat, -K: (U32 -> Cr.Cir.State -> Type) -> Cr.Cir.State -> Type,
  -H: U32 -> Cr.Cir.State -> Type, +np: {lg.is_prim(s) == True{} : Bool}, t: Lg.Tot(s, st, b, x => K(H, x), H)) ->
  Lg.WP.ok(Cr.Cir.exec(0n, s, st), Lg.Lim(st), b, K, H):
  match t:
    case Tuple{+f, ok}:
      lg.okwp(Cr.Cir.exec(0n, s, st), Lg.Lim(st), b, K, H, lg.prim.ok(f, s, st, Lg.Lim(st), b, x => K(H, x), H, np, ok))

# a sequence's first part, by its outcome o with the fuel f
def lg.split.go(o: Cr.Cir.Out, +f: Nat, +a: Cr.Cir.Stmt, +c: Cr.Cir.Stmt, +st: Cr.Cir.State, +b: Nat, -Q: Cr.Cir.State -> Type,
  -H: U32 -> Cr.Cir.State -> Type, +eq: {Cr.Cir.exec(f, a, st) == o : Cr.Cir.Out},
  ok: Lg.Ok(Cr.Cir.exec.then(o, t => Cr.Cir.exec(f, c, t)), Lg.Lim(st), b, Q, H)) ->
  Lg.Ok(o, Lg.Lim(st), b, x => Lg.Tot(c, x, b, Q, H), H):
  match o:
    case Cr.Cir.Out.next{+x}:
      (f, (%Equal.sym(Nat, Lg.Lim(x), Lg.Lim(st), lg.lim.eq(x, st, Lg.frame.fixed(f, a, st, x, eq))) :
        Lg.Ok(Cr.Cir.exec(f, c, x), _, b, Q, H); ok))
    case Cr.Cir.Out.halt{k, x}:
      ok
    case Cr.Cir.Out.out_of_memory{}:
      ok
    case Cr.Cir.Out.trap{}:
      ok
    case Cr.Cir.Out.not_done{}:
      ok

# the Tot of a sequence gives its first part's, to a state from which the
# second runs
def lg.seq.split(+a: Cr.Cir.Stmt, +c: Cr.Cir.Stmt, +st: Cr.Cir.State, +b: Nat, -Q: Cr.Cir.State -> Type,
  -H: U32 -> Cr.Cir.State -> Type, t: Lg.Tot(Cr.Cir.Stmt.seq{a, c}, st, b, Q, H)) ->
  Lg.Tot(a, st, b, x => Lg.Tot(c, x, b, Q, H), H):
  match t:
    case Tuple{+f, ok}:
      (f, lg.split.go(Cr.Cir.exec(f, a, st), f, a, c, st, b, Q, H, {==},
        (%lg.exec.seq(f, a, c, st) : Lg.Ok(_, Lg.Lim(st), b, Q, H); ok)))

# an if's run by z = U32.is_zero of its condition's value: its branch's run
def lg.if.of.back(z: Bool, +f: Nat, -t: Cr.Cir.Stmt, -e: Cr.Cir.Stmt, +st: Cr.Cir.State, +b: Nat, -Q: Cr.Cir.State -> Type,
  -H: U32 -> Cr.Cir.State -> Type, ok: Lg.Ok(Cr.Cir.exec.if.of(z, u => Cr.Cir.exec(f, t, st), u => Cr.Cir.exec(f, e, st)), Lg.Lim(st), b, Q, H)) ->
  Lg.Ok(Cr.Cir.exec(f, Bool.pick(Cr.Cir.Stmt, z, e, t), st), Lg.Lim(st), b, Q, H):
  match z:
    case False{}:
      ok
    case True{}:
      ok

# the run of an if whose condition has the value x is its branch's
def lg.if.back(+f: Nat, -c: Cr.Cir.Expr, -t: Cr.Cir.Stmt, -e: Cr.Cir.Stmt, +st: Cr.Cir.State, +b: Nat, -Q: Cr.Cir.State -> Type,
  -H: U32 -> Cr.Cir.State -> Type, +x: U32, +ev: {Cr.Cir.eval(c, st) == Some{x} : Maybe<&2, U32>},
  ok: Lg.Ok(Cr.Cir.exec(f, Cr.Cir.Stmt.if{c, t, e}, st), Lg.Lim(st), b, Q, H)) ->
  Lg.Ok(Cr.Cir.exec(f, Bool.pick(Cr.Cir.Stmt, U32.is_zero(x), e, t), st), Lg.Lim(st), b, Q, H):
  match f:
    case 0n:
      lg.if.of.back(U32.is_zero(x), 0n, t, e, st, b, Q, H,
        (%ev : Lg.Ok(Cr.Cir.exec.if(_, u => Cr.Cir.exec(0n, t, st), u => Cr.Cir.exec(0n, e, st)), Lg.Lim(st), b, Q, H); ok))
    case 1n+p:
      lg.if.of.back(U32.is_zero(x), 1n+p, t, e, st, b, Q, H,
        (%ev : Lg.Ok(Cr.Cir.exec.if(_, u => Cr.Cir.exec(1n+p, t, st), u => Cr.Cir.exec(1n+p, e, st)), Lg.Lim(st), b, Q, H); ok))

# an if whose condition has no value traps: no Tot holds of it
def lg.if.none(-c: Cr.Cir.Expr, -t: Cr.Cir.Stmt, -e: Cr.Cir.Stmt, +st: Cr.Cir.State, +b: Nat, -Q: Cr.Cir.State -> Type,
  -H: U32 -> Cr.Cir.State -> Type, +ev: {Cr.Cir.eval(c, st) == None{} : Maybe<&2, U32>},
  tt: Lg.Tot(Cr.Cir.Stmt.if{c, t, e}, st, b, Q, H)) -> Empty:
  match tt:
    case Tuple{+f, ok}:
      match f:
        case 0n:
          (%ev : Lg.Ok(Cr.Cir.exec.if(_, u => Cr.Cir.exec(0n, t, st), u => Cr.Cir.exec(0n, e, st)), Lg.Lim(st), b, Q, H); ok)
        case 1n+p:
          (%ev : Lg.Ok(Cr.Cir.exec.if(_, u => Cr.Cir.exec(1n+p, t, st), u => Cr.Cir.exec(1n+p, e, st)), Lg.Lim(st), b, Q, H); ok)

# the Tot of an if whose condition has the value x gives its branch's
def lg.if.split(+c: Cr.Cir.Expr, +t: Cr.Cir.Stmt, +e: Cr.Cir.Stmt, +st: Cr.Cir.State, +b: Nat, -Q: Cr.Cir.State -> Type,
  -H: U32 -> Cr.Cir.State -> Type, +x: U32, +ev: {Cr.Cir.eval(c, st) == Some{x} : Maybe<&2, U32>},
  tt: Lg.Tot(Cr.Cir.Stmt.if{c, t, e}, st, b, Q, H)) -> Lg.Tot(Bool.pick(Cr.Cir.Stmt, U32.is_zero(x), e, t), st, b, Q, H):
  match tt:
    case Tuple{+f, ok}:
      (f, lg.if.back(f, c, t, e, st, b, Q, H, x, ev, ok))

# tot.of_wp's converse for an if, by z = U32.is_zero of its condition's value
def lg.oftot.pick(z: Bool, +x: U32, +hz: {U32.is_zero(x) == z : Bool}, +c: Cr.Cir.Expr, +t: Cr.Cir.Stmt, +e: Cr.Cir.Stmt,
  +st: Cr.Cir.State, +b: Nat, -K: (U32 -> Cr.Cir.State -> Type) -> Cr.Cir.State -> Type, -H: U32 -> Cr.Cir.State -> Type,
  tp: Lg.Tot(Bool.pick(Cr.Cir.Stmt, U32.is_zero(x), e, t), st, b, y => K(H, y), H),
  iht: Lg.Tot(t, st, b, y => K(H, y), H) -> Lg.WP(t, b, q => y => K(q, y), j => y => H(j, y), st),
  ihe: Lg.Tot(e, st, b, y => K(H, y), H) -> Lg.WP(e, b, q => y => K(q, y), j => y => H(j, y), st)) ->
  Lg.WP.pick(z, k => h => Lg.WP(t, b, q => y => k(q, y), j => y => h(j, y), st),
    k => h => Lg.WP(e, b, q => y => k(q, y), j => y => h(j, y), st), K, H):
  match z:
    case False{}:
      iht((%hz : Lg.Tot(Bool.pick(Cr.Cir.Stmt, _, e, t), st, b, y => K(H, y), H); tp))
    case True{}:
      ihe((%hz : Lg.Tot(Bool.pick(Cr.Cir.Stmt, _, e, t), st, b, y => K(H, y), H); tp))

# tot.of_wp's converse for an if, by its condition's value v
def lg.oftot.if(v: Maybe<&2, U32>, +c: Cr.Cir.Expr, +t: Cr.Cir.Stmt, +e: Cr.Cir.Stmt, +st: Cr.Cir.State, +b: Nat,
  -K: (U32 -> Cr.Cir.State -> Type) -> Cr.Cir.State -> Type, -H: U32 -> Cr.Cir.State -> Type,
  +ev: {Cr.Cir.eval(c, st) == v : Maybe<&2, U32>}, tt: Lg.Tot(Cr.Cir.Stmt.if{c, t, e}, st, b, y => K(H, y), H),
  iht: Lg.Tot(t, st, b, y => K(H, y), H) -> Lg.WP(t, b, q => y => K(q, y), j => y => H(j, y), st),
  ihe: Lg.Tot(e, st, b, y => K(H, y), H) -> Lg.WP(e, b, q => y => K(q, y), j => y => H(j, y), st)) ->
  Lg.WP.if(v, k => h => Lg.WP(t, b, q => y => k(q, y), j => y => h(j, y), st),
    k => h => Lg.WP(e, b, q => y => k(q, y), j => y => h(j, y), st), K, H):
  match v:
    case Some{+x}:
      lg.oftot.pick(U32.is_zero(x), x, {==}, c, t, e, st, b, K, H, lg.if.split(c, t, e, st, b, y => K(H, y), H, x, ev, tt), iht, ihe)
    case None{}:
      lg.if.none(c, t, e, st, b, y => K(H, y), H, ev, tt)

def Lg.wp.of_tot(s, st, b, K, H, t):
  match s:
    case Cr.Cir.Stmt.nop{}:
      lg.prim.wp(Cr.Cir.Stmt.nop{}, st, b, K, H, {==}, t)
    case Cr.Cir.Stmt.set{+r, +e}:
      lg.prim.wp(Cr.Cir.Stmt.set{r, e}, st, b, K, H, {==}, t)
    case Cr.Cir.Stmt.store{+k, +c, +v}:
      lg.prim.wp(Cr.Cir.Stmt.store{k, c, v}, st, b, K, H, {==}, t)
    case Cr.Cir.Stmt.alloc{+r}:
      lg.prim.wp(Cr.Cir.Stmt.alloc{r}, st, b, K, H, {==}, t)
    case Cr.Cir.Stmt.emit{+v}:
      lg.prim.wp(Cr.Cir.Stmt.emit{v}, st, b, K, H, {==}, t)
    case Cr.Cir.Stmt.seq{+a, +c}:
      Lg.wp.of_tot(a, st, b, h => x => Lg.WP(c, b, k => y => K(k, y), j => y => h(j, y), x), j => y => H(j, y),
        Lg.tot.wk(a, st, b, b, x => Lg.Tot(c, x, b, y => K(H, y), H), x => Lg.WP(c, b, k => y => K(k, y), j => y => H(j, y), x),
          H, j => y => H(j, y), lg.le_refl(b),
          x => tc => Lg.wp.of_tot(c, x, b, k => y => K(k, y), j => y => H(j, y), tc), k => x => hx => hx,
          lg.seq.split(a, c, st, b, y => K(H, y), H, t)))
    case Cr.Cir.Stmt.if{+c, +t2, +e}:
      lg.oftot.if(Cr.Cir.eval(c, st), c, t2, e, st, b, K, H, {==}, t,
        tt => Lg.wp.of_tot(t2, st, b, q => y => K(q, y), j => y => H(j, y), tt),
        te => Lg.wp.of_tot(e, st, b, q => y => K(q, y), j => y => H(j, y), te))
    case Cr.Cir.Stmt.while{c, body}:
      t
    case Cr.Cir.Stmt.halt{+k}:
      lg.prim.wp(Cr.Cir.Stmt.halt{k}, st, b, K, H, {==}, t)

def Lg.wp.wk(s, st, b, b2, K, K2, H, H2, hb, hk, hh, w):
  Lg.wp.of_tot(s, st, b2, K2, H2, Lg.tot.wk(s, st, b, b2, x => K(H, x), x => K2(H2, x), H, H2, hb, hk, hh, Lg.tot.of_wp(s, st, b, K, H, w)))

def Lg.tot.frame(s, st, b, Q, H, t):
  ?TODO

def Lg.tot.frame_out(s, st, b, Q, H, ne, t):
  ?TODO
