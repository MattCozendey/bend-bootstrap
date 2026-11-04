# compiler: layer B1, the program logic of Cir
# ============================================
#
# One judgment for a run of Cir code: Tot(s, st, b, Q, H) says that some fuel
# runs s from st to a good outcome: next, with a state of which Q holds; a
# halt, of which H holds; out of memory only when the memory limit of st has
# fewer than b bytes; never a trap, never out of fuel. Fuel monotonicity
# (exec.more) gives the form at any fuel (tot.any) that mach.safe and
# mach.sound need.
#
# WP(s, b, K, H, st) is Tot computed by the structure of s: a sequence runs
# its first part to a state from which the rest runs, an if takes the branch
# of its condition's value, a primitive (set, store, alloc, emit, halt) runs
# by Cir.exec at the fuel 0, and a while is Tot itself (the while rule,
# tot.while, opens it). So a goal WP(code, ..) on closed code unfolds by
# evaluation, down to its primitives and its loops; tot.of_wp and wp.of_tot
# go between the two forms, so a routine's Tot law closes the WP of its call.
# K takes the post of a halt as its first argument, so that each path of WP
# uses it once (Bend's variables are affine).
#
# The rewrite kit: exec.* (a primitive's run), reg.*, cells.*, lim.*, next.*
# (an accessor of the state after St.set, St.store, St.alloc), and the frame
# laws (frame.regs, frame.fixed, tot.frame): a run writes only the registers
# of Cir.writes, and keeps the limit, the input, first and the image. A proof
# may also destructure a state (match st) at its start: the accessors and
# updaters then compute, and only List and Cells facts remain.

import Base
import ../../../Shared/shared.bend as Sd
import ../shared.bend as K
import ../../../Wasm/impl.bend as Wa
import ../../need_big.bend as N
import ../../Cir/impl.bend as Cr

# The state
# ---------

# register r of the state st; nothing when there is no register r
def Reg(st: Cr.Cir.State, +r: Nat) -> Maybe<&2, U32>:
  Cr.Cir.eval.get(r, st)

# the value of register r; 0 when there is no register r
def St.reg(st: Cr.Cir.State, +r: Nat) -> U32:
  Maybe.default(&2, U32, Reg(st, r), 0)

def St.regs(st: Cr.Cir.State) -> List<&2, U32>:
  match st:
    case Cr.Cir.State{regs, _, _, _, _, _, _, _, _, _}:
      regs

# the number of registers
def St.nregs(st: Cr.Cir.State) -> Nat:
  List.length(&2, U32, St.regs(st))

def St.cells(st: Cr.Cir.State) -> Cr.Cir.Cells:
  match st:
    case Cr.Cir.State{_, cells, _, _, _, _, _, _, _, _}:
      cells

def St.next(st: Cr.Cir.State) -> U32:
  match st:
    case Cr.Cir.State{_, _, next, _, _, _, _, _, _, _}:
      next

def St.first(st: Cr.Cir.State) -> U32:
  match st:
    case Cr.Cir.State{_, _, _, first, _, _, _, _, _, _}:
      first

def St.image(st: Cr.Cir.State) -> U32:
  match st:
    case Cr.Cir.State{_, _, _, _, image, _, _, _, _, _}:
      image

def St.pages(st: Cr.Cir.State) -> U32:
  match st:
    case Cr.Cir.State{_, _, _, _, _, pages, _, _, _, _}:
      pages

def St.limit(st: Cr.Cir.State) -> U32:
  match st:
    case Cr.Cir.State{_, _, _, _, _, _, limit, _, _, _}:
      limit

def St.input(st: Cr.Cir.State) -> List<&2, Word(8n)>:
  match st:
    case Cr.Cir.State{_, _, _, _, _, _, _, input, _, _}:
      input

def St.out(st: Cr.Cir.State) -> List<&2, Word(8n)>:
  match st:
    case Cr.Cir.State{_, _, _, _, _, _, _, _, out, _}:
      out

def St.outn(st: Cr.Cir.State) -> U32:
  match st:
    case Cr.Cir.State{_, _, _, _, _, _, _, _, _, outn}:
      outn

# field k of the cell c
def St.fd(st: Cr.Cir.State, +k: Nat, +c: U32) -> U32:
  Cr.Cir.Cell.get(k, Cr.Cir.Cells.get(St.cells(st), c))

# the cell c is one that Cir lets the machine read and write
def St.is_cell(+st: Cr.Cir.State, +c: U32) -> Bool:
  Cr.Cir.is_cell(c, St.image(st), St.first(st), St.next(st))

# the memory limit of st, in bytes: 2^16 x its pages, up to 2^16 pages, as
# Program.memory counts them (N.mul_D relates the two); 2^16 is N.D(16, 1),
# so that no check counts to it
def Lim(st: Cr.Cir.State) -> Nat:
  N.D(16n, U32.to_nat(Wa.Wasm.min(St.limit(st), 65536)))

# what a run never changes: the limit, the input, first and the image
type St.Fixed is Data:
  St.Fixed{limit: U32, input: List<&2, Word(8n)>, first: U32, image: U32}

def St.fixed(st: Cr.Cir.State) -> St.Fixed:
  match st:
    case Cr.Cir.State{_, _, _, first, image, _, limit, input, _, _}:
      St.Fixed{limit, input, first, image}

# st with the register r set to v
def St.set(st: Cr.Cir.State, +r: Nat, v: U32) -> Cr.Cir.State:
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      Cr.Cir.State{List.set(&2, U32, regs, r, v), cells, next, first, image, pages, limit, input, out, outn}

# st with the field k of the cell c set to v
def St.store(st: Cr.Cir.State, +k: Nat, +c: U32, v: U32) -> Cr.Cir.State:
  match st:
    case Cr.Cir.State{regs, +cells, next, first, image, pages, limit, input, out, outn}:
      Cr.Cir.State{regs, Cr.Cir.Cells.set(cells, c, Cr.Cir.Cell.set(k, Cr.Cir.Cells.get(cells, c), v)), next, first, image,
        pages, limit, input, out, outn}

# st after a new cell (alloc): the register r holds the cell next, all zeros;
# next moves on; the memory has p pages
def St.alloc(st: Cr.Cir.State, +r: Nat, p: U32) -> Cr.Cir.State:
  match st:
    case Cr.Cir.State{regs, cells, +next, first, image, _, limit, input, out, outn}:
      Cr.Cir.State{List.set(&2, U32, regs, r, next), Cr.Cir.Cells.set(cells, next, Cr.Cir.Cell.zero()), U32.inc(next),
        first, image, p, limit, input, out, outn}

# st after an emit of the low byte of v, the memory then of p pages
def St.emit(st: Cr.Cir.State, v: U32, p: U32) -> Cr.Cir.State:
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, _, limit, input, out, outn}:
      Cr.Cir.State{regs, cells, next, first, image, p, limit, input, Con{Sd.Byte.from_u32(v), out}, U32.inc(outn)}

# The judgment
# ------------

# the run ended: anything but out of fuel
def Out.done(o: Cr.Cir.Out) -> Bool:
  match o:
    case Cr.Cir.Out.not_done{}:
      False{}
    case _:
      True{}

# the outcome o is good: next with Q, a halt with H, out of memory only when
# the limit lim has fewer than b bytes; never a trap, never out of fuel
def Ok(o: Cr.Cir.Out, +lim: Nat, +b: Nat, Q: Cr.Cir.State -> Type, H: U32 -> Cr.Cir.State -> Type) -> Type:
  match o:
    case Cr.Cir.Out.next{st}:
      Q(st)
    case Cr.Cir.Out.halt{s, st}:
      H(s, st)
    case Cr.Cir.Out.out_of_memory{}:
      {Nat.is_lt(lim, b) == True{} : Bool}
    case Cr.Cir.Out.trap{}:
      Empty
    case Cr.Cir.Out.not_done{}:
      Empty

# Tot: with some fuel, s runs from st to a good outcome
def Tot(s: Cr.Cir.Stmt, +st: Cr.Cir.State, +b: Nat, -Q: Cr.Cir.State -> Type, -H: U32 -> Cr.Cir.State -> Type) -> Type:
  &f:Nat -> Ok(Cr.Cir.exec(f, s, st), Lim(st), b, Q, H)

# no halt
def No(s: U32, st: Cr.Cir.State) -> Type:
  Empty

# WP
# --

# the post of a primitive's outcome o: as Ok, with K given the post of a halt
def WP.ok(o: Cr.Cir.Out, +lim: Nat, +b: Nat, K: (U32 -> Cr.Cir.State -> Type) -> Cr.Cir.State -> Type,
  H: U32 -> Cr.Cir.State -> Type) -> Type:
  match o:
    case Cr.Cir.Out.next{st}:
      K(H, st)
    case Cr.Cir.Out.halt{s, st}:
      H(s, st)
    case Cr.Cir.Out.out_of_memory{}:
      {Nat.is_lt(lim, b) == True{} : Bool}
    case Cr.Cir.Out.trap{}:
      Empty
    case Cr.Cir.Out.not_done{}:
      Empty

# the branch of an if, by z = U32.is_zero of its condition: yes when false
def WP.pick(z: Bool,
  yes: ((U32 -> Cr.Cir.State -> Type) -> Cr.Cir.State -> Type) -> (U32 -> Cr.Cir.State -> Type) -> Type,
  no: ((U32 -> Cr.Cir.State -> Type) -> Cr.Cir.State -> Type) -> (U32 -> Cr.Cir.State -> Type) -> Type,
  K: (U32 -> Cr.Cir.State -> Type) -> Cr.Cir.State -> Type, H: U32 -> Cr.Cir.State -> Type) -> Type:
  match z:
    case False{}:
      yes(K, H)
    case True{}:
      no(K, H)

# an if, by the value v of its condition; a trap when it has none
def WP.if(v: Maybe<&2, U32>,
  yes: ((U32 -> Cr.Cir.State -> Type) -> Cr.Cir.State -> Type) -> (U32 -> Cr.Cir.State -> Type) -> Type,
  no: ((U32 -> Cr.Cir.State -> Type) -> Cr.Cir.State -> Type) -> (U32 -> Cr.Cir.State -> Type) -> Type,
  K: (U32 -> Cr.Cir.State -> Type) -> Cr.Cir.State -> Type, H: U32 -> Cr.Cir.State -> Type) -> Type:
  match v:
    case Some{x}:
      WP.pick(U32.is_zero(x), yes, no, K, H)
    case None{}:
      Empty

# the weakest precondition of s from st, within the budget b: K of the state
# after it (given H), or H of a halt; out of memory only below b bytes
def WP(s: Cr.Cir.Stmt, +b: Nat, K: (U32 -> Cr.Cir.State -> Type) -> Cr.Cir.State -> Type,
  H: U32 -> Cr.Cir.State -> Type, +st: Cr.Cir.State) -> Type:
  match s:
    case Cr.Cir.Stmt.nop{}:
      K(H, st)
    case Cr.Cir.Stmt.set{r, e}:
      WP.ok(Cr.Cir.exec(0n, Cr.Cir.Stmt.set{r, e}, st), Lim(st), b, K, H)
    case Cr.Cir.Stmt.store{k, c, v}:
      WP.ok(Cr.Cir.exec(0n, Cr.Cir.Stmt.store{k, c, v}, st), Lim(st), b, K, H)
    case Cr.Cir.Stmt.alloc{r}:
      WP.ok(Cr.Cir.exec(0n, Cr.Cir.Stmt.alloc{r}, st), Lim(st), b, K, H)
    case Cr.Cir.Stmt.emit{v}:
      WP.ok(Cr.Cir.exec(0n, Cr.Cir.Stmt.emit{v}, st), Lim(st), b, K, H)
    case Cr.Cir.Stmt.seq{a, c}:
      WP(a, b, h => t => WP(c, b, k => x => K(k, x), j => y => h(j, y), t), j => y => H(j, y), st)
    case Cr.Cir.Stmt.if{c, t, e}:
      WP.if(Cr.Cir.eval(c, st), k => h => WP(t, b, q => x => k(q, x), j => y => h(j, y), st),
        k => h => WP(e, b, q => x => k(q, x), j => y => h(j, y), st), K, H)
    case Cr.Cir.Stmt.while{c, body}:
      Tot(Cr.Cir.Stmt.while{c, body}, st, b, x => K(H, x), H)
    case Cr.Cir.Stmt.halt{k}:
      H(k, st)

# The while rule
# --------------

# a round of a while from st, with the invariant I at the measure n, by z =
# U32.is_zero of its condition: at 0, Q; else the body runs to I at a smaller
# measure
def Loop.pick(z: Bool, body: Cr.Cir.Stmt, +st: Cr.Cir.State, +b: Nat, +n: Nat, I: Nat -> Cr.Cir.State -> Type,
  Q: Cr.Cir.State -> Type, H: U32 -> Cr.Cir.State -> Type) -> Type:
  match z:
    case True{}:
      Q(st)
    case False{}:
      WP(body, b, h => t => &k:Nat -> {Nat.is_lt(k, n) == True{} : Bool} & I(k, t), j => y => H(j, y), st)

# a round of a while, by the value v of its condition; a trap when it has none
def Loop.of(v: Maybe<&2, U32>, body: Cr.Cir.Stmt, +st: Cr.Cir.State, +b: Nat, +n: Nat, I: Nat -> Cr.Cir.State -> Type,
  Q: Cr.Cir.State -> Type, H: U32 -> Cr.Cir.State -> Type) -> Type:
  match v:
    case Some{x}:
      Loop.pick(U32.is_zero(x), body, st, b, n, I, Q, H)
    case None{}:
      Empty

def Loop(c: Cr.Cir.Expr, body: Cr.Cir.Stmt, +st: Cr.Cir.State, +b: Nat, +n: Nat, I: Nat -> Cr.Cir.State -> Type,
  Q: Cr.Cir.State -> Type, H: U32 -> Cr.Cir.State -> Type) -> Type:
  Loop.of(Cr.Cir.eval(c, st), body, st, b, n, I, Q, H)

# The syntactic frame
# -------------------

# the registers that s may write: the targets of its sets and allocs
def Cir.writes(s: Cr.Cir.Stmt) -> List<&2, Nat>:
  match s:
    case Cr.Cir.Stmt.set{r, _}:
      [r]
    case Cr.Cir.Stmt.alloc{r}:
      [r]
    case Cr.Cir.Stmt.seq{a, c}:
      List.append(&2, Nat, Cir.writes(a), Cir.writes(c))
    case Cr.Cir.Stmt.if{_, t, e}:
      List.append(&2, Nat, Cir.writes(t), Cir.writes(e))
    case Cr.Cir.Stmt.while{_, body}:
      Cir.writes(body)
    case _:
      []

# s has an emit
def Cir.emits(s: Cr.Cir.Stmt) -> Bool:
  match s:
    case Cr.Cir.Stmt.emit{_}:
      True{}
    case Cr.Cir.Stmt.seq{a, c}:
      Cir.emits(a) || Cir.emits(c)
    case Cr.Cir.Stmt.if{_, t, e}:
      Cir.emits(t) || Cir.emits(e)
    case Cr.Cir.Stmt.while{_, body}:
      Cir.emits(body)
    case _:
      False{}

# each register of rs2 from the i-th is the one of rs, but those of ws; as
# many registers
def Regs.kept(rs: List<&2, U32>, +rs2: List<&2, U32>, +ws: List<&2, Nat>, +i: Nat) -> Bool:
  match rs rs2:
    case Nil{} Nil{}:
      True{}
    case Con{x, xr} Con{y, yr}:
      (K.Has(ws, i) || U32.is_eq(x, y)) && Regs.kept(xr, yr, ws, 1n+i)
    case _ _:
      False{}

# st2 keeps the registers of st, but those of ws; next does not go back
def St.kept(+st: Cr.Cir.State, +st2: Cr.Cir.State, +ws: List<&2, Nat>) -> Bool:
  Regs.kept(St.regs(st), St.regs(st2), ws, 0n) && U32.is_le(St.next(st), St.next(st2))

# Laws: the judgment
# ------------------

# LAW: a run that ends with the fuel f ends the same with more fuel
law exec.more:
  for +f: Nat
  for +g: Nat
  for +s: Cr.Cir.Stmt
  for +st: Cr.Cir.State
  for +d: {Out.done(Cr.Cir.exec(f, s, st)) == True{} : Bool}
  {Cr.Cir.exec(Nat.add(f, g), s, st) == Cr.Cir.exec(f, s, st) : Cr.Cir.Out}

# LAW: at any fuel, a Tot run is out of fuel or good (what mach.safe and
# mach.sound use)
law tot.any:
  for +s: Cr.Cir.Stmt
  for +st: Cr.Cir.State
  for +b: Nat
  for -Q: Cr.Cir.State -> Type
  for -H: U32 -> Cr.Cir.State -> Type
  for t: Tot(s, st, b, Q, H)
  for +g: Nat
  Or({Cr.Cir.exec(g, s, st) == Cr.Cir.Out.not_done{} : Cr.Cir.Out}, Ok(Cr.Cir.exec(g, s, st), Lim(st), b, Q, H))

# LAW: a sequence: the first statement runs to a state from which the second
# does
law tot.seq:
  for +a: Cr.Cir.Stmt
  for +c: Cr.Cir.Stmt
  for +st: Cr.Cir.State
  for +b: Nat
  for -Q: Cr.Cir.State -> Type
  for -H: U32 -> Cr.Cir.State -> Type
  for t: Tot(a, st, b, x => Tot(c, x, b, Q, H), H)
  Tot(Cr.Cir.Stmt.seq{a, c}, st, b, Q, H)

# LAW: an if, by the value v of its condition
law tot.if:
  for +c: Cr.Cir.Expr
  for +y: Cr.Cir.Stmt
  for +n: Cr.Cir.Stmt
  for +st: Cr.Cir.State
  for +b: Nat
  for -Q: Cr.Cir.State -> Type
  for -H: U32 -> Cr.Cir.State -> Type
  for +v: U32
  for +e: {Cr.Cir.eval(c, st) == Some{v} : Maybe<&2, U32>}
  for t: Tot(Bool.pick(Cr.Cir.Stmt, U32.is_zero(v), n, y), st, b, Q, H)
  Tot(Cr.Cir.Stmt.if{c, y, n}, st, b, Q, H)

# LAW: the while rule: an invariant I, indexed by a measure that each round
# lowers (Loop: the condition has a value; at 0, Q; else the body's WP to I
# at a smaller measure)
law tot.while:
  for +c: Cr.Cir.Expr
  for +body: Cr.Cir.Stmt
  for +b: Nat
  for -I: Nat -> Cr.Cir.State -> Type
  for -Q: Cr.Cir.State -> Type
  for -H: U32 -> Cr.Cir.State -> Type
  for r: @n: Nat -> @st: Cr.Cir.State -> I(n, st) -> Loop(c, body, st, b, n, I, Q, H)
  for +n: Nat
  for +st: Cr.Cir.State
  for i: I(n, st)
  Tot(Cr.Cir.Stmt.while{c, body}, st, b, Q, H)

# LAW: a weaker conclusion: a larger budget, weaker posts
law tot.wk:
  for +s: Cr.Cir.Stmt
  for +st: Cr.Cir.State
  for +b: Nat
  for +b2: Nat
  for -Q: Cr.Cir.State -> Type
  for -Q2: Cr.Cir.State -> Type
  for -H: U32 -> Cr.Cir.State -> Type
  for -H2: U32 -> Cr.Cir.State -> Type
  for +hb: {Nat.is_le(b, b2) == True{} : Bool}
  for hq: @x: Cr.Cir.State -> Q(x) -> Q2(x)
  for hh: @k: U32 -> @x: Cr.Cir.State -> H(k, x) -> H2(k, x)
  for t: Tot(s, st, b, Q, H)
  Tot(s, st, b2, Q2, H2)

# LAW: WP is sound: it gives Tot
law tot.of_wp:
  for +s: Cr.Cir.Stmt
  for +st: Cr.Cir.State
  for +b: Nat
  for -K: (U32 -> Cr.Cir.State -> Type) -> Cr.Cir.State -> Type
  for -H: U32 -> Cr.Cir.State -> Type
  for w: WP(s, b, K, H, st)
  Tot(s, st, b, x => K(H, x), H)

# LAW: WP is the weakest: Tot gives it (so a routine's Tot law closes the WP
# of its call)
law wp.of_tot:
  for +s: Cr.Cir.Stmt
  for +st: Cr.Cir.State
  for +b: Nat
  for -K: (U32 -> Cr.Cir.State -> Type) -> Cr.Cir.State -> Type
  for -H: U32 -> Cr.Cir.State -> Type
  for t: Tot(s, st, b, x => K(H, x), H)
  WP(s, b, K, H, st)

# LAW: a weaker WP: a larger budget, weaker posts
law wp.wk:
  for +s: Cr.Cir.Stmt
  for +st: Cr.Cir.State
  for +b: Nat
  for +b2: Nat
  for -K: (U32 -> Cr.Cir.State -> Type) -> Cr.Cir.State -> Type
  for -K2: (U32 -> Cr.Cir.State -> Type) -> Cr.Cir.State -> Type
  for -H: U32 -> Cr.Cir.State -> Type
  for -H2: U32 -> Cr.Cir.State -> Type
  for +hb: {Nat.is_le(b, b2) == True{} : Bool}
  for hk: @x: Cr.Cir.State -> K(H, x) -> K2(H2, x)
  for hh: @k: U32 -> @x: Cr.Cir.State -> H(k, x) -> H2(k, x)
  for w: WP(s, b, K, H, st)
  WP(s, b2, K2, H2, st)

# Laws: the primitives
# --------------------
#
# A primitive's step, as WP asks it: wp.set, wp.store, wp.alloc, wp.emit
# (apply rules: the WP of the primitive from the post of its next state);
# exec.set, exec.store, exec.alloc (its run). An alloc and an emit run out of
# memory only below the bytes that they need: 20 (next + 1) for a new cell,
# 20 next + outn + 1 for an output byte.

# LAW: a set, as an equation of the run
law exec.set:
  for +f: Nat
  for +r: Nat
  for +e: Cr.Cir.Expr
  for +st: Cr.Cir.State
  for +v: U32
  for +he: {Cr.Cir.eval(e, st) == Some{v} : Maybe<&2, U32>}
  for +hr: {Nat.is_lt(r, St.nregs(st)) == True{} : Bool}
  {Cr.Cir.exec(f, Cr.Cir.Stmt.set{r, e}, st) == Cr.Cir.Out.next{St.set(st, r, v)} : Cr.Cir.Out}

# LAW: a store to a cell that Cir allows
law exec.store:
  for +f: Nat
  for +k: Nat
  for +c: Cr.Cir.Expr
  for +e: Cr.Cir.Expr
  for +st: Cr.Cir.State
  for +i: U32
  for +v: U32
  for +hc: {Cr.Cir.eval(c, st) == Some{i} : Maybe<&2, U32>}
  for +he: {Cr.Cir.eval(e, st) == Some{v} : Maybe<&2, U32>}
  for +hi: {St.is_cell(st, i) == True{} : Bool}
  {Cr.Cir.exec(f, Cr.Cir.Stmt.store{k, c, e}, st) == Cr.Cir.Out.next{St.store(st, k, i, v)} : Cr.Cir.Out}

# LAW: an alloc with no output yet: a new cell (the memory then of p pages),
# or out of memory below 20 (next + 1) bytes
law exec.alloc:
  for +f: Nat
  for +r: Nat
  for +st: Cr.Cir.State
  for +hr: {Nat.is_lt(r, St.nregs(st)) == True{} : Bool}
  for +ho: {St.outn(st) == 0 : U32}
  Or(&p:U32 -> {Cr.Cir.exec(f, Cr.Cir.Stmt.alloc{r}, st) == Cr.Cir.Out.next{St.alloc(st, r, p)} : Cr.Cir.Out},
    {Cr.Cir.exec(f, Cr.Cir.Stmt.alloc{r}, st) == Cr.Cir.Out.out_of_memory{} : Cr.Cir.Out} &
    {Nat.is_lt(Lim(st), Nat.mul(20n, Nat.add(U32.to_nat(St.next(st)), 1n))) == True{} : Bool})

# LAW: the WP of a set: its post at the state with r set
law wp.set:
  for +r: Nat
  for +e: Cr.Cir.Expr
  for +st: Cr.Cir.State
  for +b: Nat
  for -K: (U32 -> Cr.Cir.State -> Type) -> Cr.Cir.State -> Type
  for -H: U32 -> Cr.Cir.State -> Type
  for +v: U32
  for +he: {Cr.Cir.eval(e, st) == Some{v} : Maybe<&2, U32>}
  for +hr: {Nat.is_lt(r, St.nregs(st)) == True{} : Bool}
  for q: K(H, St.set(st, r, v))
  WP(Cr.Cir.Stmt.set{r, e}, b, K, H, st)

# LAW: the WP of a store: its post at the state with the field set
law wp.store:
  for +k: Nat
  for +c: Cr.Cir.Expr
  for +e: Cr.Cir.Expr
  for +st: Cr.Cir.State
  for +b: Nat
  for -K: (U32 -> Cr.Cir.State -> Type) -> Cr.Cir.State -> Type
  for -H: U32 -> Cr.Cir.State -> Type
  for +i: U32
  for +v: U32
  for +hc: {Cr.Cir.eval(c, st) == Some{i} : Maybe<&2, U32>}
  for +he: {Cr.Cir.eval(e, st) == Some{v} : Maybe<&2, U32>}
  for +hi: {St.is_cell(st, i) == True{} : Bool}
  for q: K(H, St.store(st, k, i, v))
  WP(Cr.Cir.Stmt.store{k, c, e}, b, K, H, st)

# LAW: the WP of an alloc, with no output yet and a budget of 20 (next + 1)
# bytes: its post at the state with the new cell, for the pages p that the
# memory then has
law wp.alloc:
  for +r: Nat
  for +st: Cr.Cir.State
  for +b: Nat
  for -K: (U32 -> Cr.Cir.State -> Type) -> Cr.Cir.State -> Type
  for -H: U32 -> Cr.Cir.State -> Type
  for +hr: {Nat.is_lt(r, St.nregs(st)) == True{} : Bool}
  for +ho: {St.outn(st) == 0 : U32}
  for +hb: {Nat.is_le(Nat.mul(20n, Nat.add(U32.to_nat(St.next(st)), 1n)), b) == True{} : Bool}
  for q: @p: U32 -> K(H, St.alloc(st, r, p))
  WP(Cr.Cir.Stmt.alloc{r}, b, K, H, st)

# LAW: the WP of an emit, with a budget of 20 next + outn + 1 bytes: its post
# at the state with the byte out, for the pages p that the memory then has
law wp.emit:
  for +e: Cr.Cir.Expr
  for +st: Cr.Cir.State
  for +b: Nat
  for -K: (U32 -> Cr.Cir.State -> Type) -> Cr.Cir.State -> Type
  for -H: U32 -> Cr.Cir.State -> Type
  for +v: U32
  for +he: {Cr.Cir.eval(e, st) == Some{v} : Maybe<&2, U32>}
  for +hb: {Nat.is_le(Nat.add(Nat.mul(20n, U32.to_nat(St.next(st))), Nat.add(U32.to_nat(St.outn(st)), 1n)), b) == True{} : Bool}
  for q: @p: U32 -> K(H, St.emit(st, v, p))
  WP(Cr.Cir.Stmt.emit{e}, b, K, H, st)

# Laws: accessors after updaters
# ------------------------------
#
# For a state that a proof does not destructure: Reg, St.nregs, St.cells,
# St.next, St.outn, St.fixed and Lim after St.set, St.store, St.alloc and
# St.emit (named <accessor>.<updater>). St.image, St.first, St.limit and
# St.input are parts of St.fixed.

# LAW: a register after a set
law reg.set:
  for +st: Cr.Cir.State
  for +r: Nat
  for +v: U32
  for +q: Nat
  for +hr: {Nat.is_lt(r, St.nregs(st)) == True{} : Bool}
  {Reg(St.set(st, r, v), q) == Bool.pick(Maybe<&2, U32>, Nat.is_eq(r, q), Some{v}, Reg(st, q)) : Maybe<&2, U32>}

# LAW: a register below the count has a value: St.reg
law reg.some:
  for +st: Cr.Cir.State
  for +q: Nat
  for +hq: {Nat.is_lt(q, St.nregs(st)) == True{} : Bool}
  {Reg(st, q) == Some{St.reg(st, q)} : Maybe<&2, U32>}

# LAW: a register with a value is below the count
law reg.lt:
  for +st: Cr.Cir.State
  for +q: Nat
  for +c: U32
  for +hq: {Reg(st, q) == Some{c} : Maybe<&2, U32>}
  {Nat.is_lt(q, St.nregs(st)) == True{} : Bool}

# LAW: a register after a store, an alloc (its register gets the old next) and
# an emit
law reg.store:
  for +st: Cr.Cir.State
  for +k: Nat
  for +c: U32
  for +v: U32
  for +q: Nat
  {Reg(St.store(st, k, c, v), q) == Reg(st, q) : Maybe<&2, U32>}

law reg.alloc:
  for +st: Cr.Cir.State
  for +r: Nat
  for +p: U32
  for +q: Nat
  for +hr: {Nat.is_lt(r, St.nregs(st)) == True{} : Bool}
  {Reg(St.alloc(st, r, p), q) == Bool.pick(Maybe<&2, U32>, Nat.is_eq(r, q), Some{St.next(st)}, Reg(st, q)) : Maybe<&2, U32>}

law reg.emit:
  for +st: Cr.Cir.State
  for +v: U32
  for +p: U32
  for +q: Nat
  {Reg(St.emit(st, v, p), q) == Reg(st, q) : Maybe<&2, U32>}

# LAW: the number of registers stays
law nregs.set:
  for +st: Cr.Cir.State
  for +r: Nat
  for +v: U32
  {St.nregs(St.set(st, r, v)) == St.nregs(st) : Nat}

law nregs.store:
  for +st: Cr.Cir.State
  for +k: Nat
  for +c: U32
  for +v: U32
  {St.nregs(St.store(st, k, c, v)) == St.nregs(st) : Nat}

law nregs.alloc:
  for +st: Cr.Cir.State
  for +r: Nat
  for +p: U32
  {St.nregs(St.alloc(st, r, p)) == St.nregs(st) : Nat}

law nregs.emit:
  for +st: Cr.Cir.State
  for +v: U32
  for +p: U32
  {St.nregs(St.emit(st, v, p)) == St.nregs(st) : Nat}

# LAW: the cells after a set (the same), a store (the field set), an alloc
# (the cell next, all zeros) and an emit (the same)
law cells.set:
  for +st: Cr.Cir.State
  for +r: Nat
  for +v: U32
  {St.cells(St.set(st, r, v)) == St.cells(st) : Cr.Cir.Cells}

law cells.store:
  for +st: Cr.Cir.State
  for +k: Nat
  for +c: U32
  for +v: U32
  {St.cells(St.store(st, k, c, v)) ==
    Cr.Cir.Cells.set(St.cells(st), c, Cr.Cir.Cell.set(k, Cr.Cir.Cells.get(St.cells(st), c), v)) : Cr.Cir.Cells}

law cells.alloc:
  for +st: Cr.Cir.State
  for +r: Nat
  for +p: U32
  {St.cells(St.alloc(st, r, p)) == Cr.Cir.Cells.set(St.cells(st), St.next(st), Cr.Cir.Cell.zero()) : Cr.Cir.Cells}

law cells.emit:
  for +st: Cr.Cir.State
  for +v: U32
  for +p: U32
  {St.cells(St.emit(st, v, p)) == St.cells(st) : Cr.Cir.Cells}

# LAW: a cell after Cells.set: the new one at its number, else the old
law cells.get_set:
  for +m: Cr.Cir.Cells
  for +i: U32
  for +x: Cr.Cir.Cell
  for +j: U32
  {Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, i, x), j) == Bool.pick(Cr.Cir.Cell, U32.is_eq(i, j), x, Cr.Cir.Cells.get(m, j)) : Cr.Cir.Cell}

# LAW: a field after Cell.set, for fields 0 to 4
law cell.get_set:
  for +k: Nat
  for +x: Cr.Cir.Cell
  for +v: U32
  for +j: Nat
  for +hk: {Nat.is_le(k, 4n) == True{} : Bool}
  for +hj: {Nat.is_le(j, 4n) == True{} : Bool}
  {Cr.Cir.Cell.get(j, Cr.Cir.Cell.set(k, x, v)) == Bool.pick(U32, Nat.is_eq(k, j), v, Cr.Cir.Cell.get(j, x)) : U32}

# LAW: next after a set, a store and an emit (the same), and an alloc (one
# more)
law next.set:
  for +st: Cr.Cir.State
  for +r: Nat
  for +v: U32
  {St.next(St.set(st, r, v)) == St.next(st) : U32}

law next.store:
  for +st: Cr.Cir.State
  for +k: Nat
  for +c: U32
  for +v: U32
  {St.next(St.store(st, k, c, v)) == St.next(st) : U32}

law next.alloc:
  for +st: Cr.Cir.State
  for +r: Nat
  for +p: U32
  {St.next(St.alloc(st, r, p)) == U32.inc(St.next(st)) : U32}

law next.emit:
  for +st: Cr.Cir.State
  for +v: U32
  for +p: U32
  {St.next(St.emit(st, v, p)) == St.next(st) : U32}

# LAW: the output's length after a set, a store, an alloc (the same) and an
# emit (one more)
law outn.set:
  for +st: Cr.Cir.State
  for +r: Nat
  for +v: U32
  {St.outn(St.set(st, r, v)) == St.outn(st) : U32}

law outn.store:
  for +st: Cr.Cir.State
  for +k: Nat
  for +c: U32
  for +v: U32
  {St.outn(St.store(st, k, c, v)) == St.outn(st) : U32}

law outn.alloc:
  for +st: Cr.Cir.State
  for +r: Nat
  for +p: U32
  {St.outn(St.alloc(st, r, p)) == St.outn(st) : U32}

law outn.emit:
  for +st: Cr.Cir.State
  for +v: U32
  for +p: U32
  {St.outn(St.emit(st, v, p)) == U32.inc(St.outn(st)) : U32}

# LAW: the fixed parts after each updater
law fixed.set:
  for +st: Cr.Cir.State
  for +r: Nat
  for +v: U32
  {St.fixed(St.set(st, r, v)) == St.fixed(st) : St.Fixed}

law fixed.store:
  for +st: Cr.Cir.State
  for +k: Nat
  for +c: U32
  for +v: U32
  {St.fixed(St.store(st, k, c, v)) == St.fixed(st) : St.Fixed}

law fixed.alloc:
  for +st: Cr.Cir.State
  for +r: Nat
  for +p: U32
  {St.fixed(St.alloc(st, r, p)) == St.fixed(st) : St.Fixed}

law fixed.emit:
  for +st: Cr.Cir.State
  for +v: U32
  for +p: U32
  {St.fixed(St.emit(st, v, p)) == St.fixed(st) : St.Fixed}

# LAW: the limit's bytes after each updater
law lim.set:
  for +st: Cr.Cir.State
  for +r: Nat
  for +v: U32
  {Lim(St.set(st, r, v)) == Lim(st) : Nat}

law lim.store:
  for +st: Cr.Cir.State
  for +k: Nat
  for +c: U32
  for +v: U32
  {Lim(St.store(st, k, c, v)) == Lim(st) : Nat}

law lim.alloc:
  for +st: Cr.Cir.State
  for +r: Nat
  for +p: U32
  {Lim(St.alloc(st, r, p)) == Lim(st) : Nat}

law lim.emit:
  for +st: Cr.Cir.State
  for +v: U32
  for +p: U32
  {Lim(St.emit(st, v, p)) == Lim(st) : Nat}

# Laws: the frame
# ---------------

# LAW: the register frame: a register that s does not write keeps its value
law frame.regs:
  for +f: Nat
  for +s: Cr.Cir.Stmt
  for +st: Cr.Cir.State
  for +st2: Cr.Cir.State
  for +r: Nat
  for +e: {Cr.Cir.exec(f, s, st) == Cr.Cir.Out.next{st2} : Cr.Cir.Out}
  for +w: {K.Has(Cir.writes(s), r) == False{} : Bool}
  {Reg(st2, r) == Reg(st, r) : Maybe<&2, U32>}

# LAW: a run keeps the limit, the input, first and the image
law frame.fixed:
  for +f: Nat
  for +s: Cr.Cir.Stmt
  for +st: Cr.Cir.State
  for +st2: Cr.Cir.State
  for +e: {Cr.Cir.exec(f, s, st) == Cr.Cir.Out.next{st2} : Cr.Cir.Out}
  {St.fixed(st2) == St.fixed(st) : St.Fixed}

# LAW: the frame of a Tot: its next state also keeps the registers outside
# Cir.writes(s) (and next does not go back), and the fixed parts
law tot.frame:
  for +s: Cr.Cir.Stmt
  for +st: Cr.Cir.State
  for +b: Nat
  for -Q: Cr.Cir.State -> Type
  for -H: U32 -> Cr.Cir.State -> Type
  for t: Tot(s, st, b, Q, H)
  Tot(s, st, b, x => Q(x) & ({St.kept(st, x, Cir.writes(s)) == True{} : Bool} & {St.fixed(x) == St.fixed(st) : St.Fixed}), H)

# LAW: a run with no emit keeps the output
law tot.frame_out:
  for +s: Cr.Cir.Stmt
  for +st: Cr.Cir.State
  for +b: Nat
  for -Q: Cr.Cir.State -> Type
  for -H: U32 -> Cr.Cir.State -> Type
  for +ne: {Cir.emits(s) == False{} : Bool}
  for t: Tot(s, st, b, Q, H)
  Tot(s, st, b, x => Q(x) & ({St.out(x) == St.out(st) : List<&2, Word(8n)>} & {St.outn(x) == St.outn(st) : U32}), H)
