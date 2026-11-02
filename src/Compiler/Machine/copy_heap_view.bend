# compiler: the copy's view of the heap
# =====================================
#
# In the middle of a copy (M.copy.walk), HS does not hold of the cells: a
# new cell on the walk's stack has a term's tag, field 1 is the stack's link,
# not a count, and its fields hold the parts of its source that are still to
# copy, which their counts do not count. The proofs of the copy (this file
# and the rest) keep HS of a view instead: the cells v, which agree with the
# real cells m but at the cells zs of the stacks (Agr), where v holds cells
# that point nowhere and that nothing points to. The machine's statements run
# on m; a statement that never reads nor writes a cell of zs runs the same
# on v, so the shared lemmas (alloc.post) can be used on v.
#
# Here: Agr and Kp (the cells zs stay), their stores, and the simulation of
# M.dec (sim.dec): its run on m and on v ends with the same registers, and
# cells that still agree.

import Base
import ../Cir/impl.bend as Cr
import ./impl.bend as Mc
import ../need_big.bend as N
import ./definitions.bend as PM
import ./statement_runs.bend as X

# Agreement
# ---------

# the cells m and v agree at every cell out of zs
def Agr(+m: Cr.Cir.Cells, +v: Cr.Cir.Cells, +zs: List<&2, U32>) -> Type:
  @q: U32 -> {PM.Mem(zs, q) == False{} : Bool} -> {Cr.Cir.Cells.get(m, q) == Cr.Cir.Cells.get(v, q) : Cr.Cir.Cell}

# the cells m2 keep the cells of zs that m has
def Kp(+m: Cr.Cir.Cells, +m2: Cr.Cir.Cells, +zs: List<&2, U32>) -> Type:
  @q: U32 -> {PM.Mem(zs, q) == True{} : Bool} -> {Cr.Cir.Cells.get(m2, q) == Cr.Cir.Cells.get(m, q) : Cr.Cir.Cell}

def kp.refl(+m: Cr.Cir.Cells, +zs: List<&2, U32>) -> Kp(m, m, zs):
  +q => +h => {==}

def kp.trans(+m: Cr.Cir.Cells, +m2: Cr.Cir.Cells, +m3: Cr.Cir.Cells, +zs: List<&2, U32>, a: Kp(m, m2, zs), b: Kp(m2, m3, zs)) ->
  Kp(m, m3, zs):
  +q => +h => Equal.trans(Cr.Cir.Cell, Cr.Cir.Cells.get(m3, q), Cr.Cir.Cells.get(m2, q), Cr.Cir.Cells.get(m, q), b(q, h), a(q, h))

# a cell of zs is not one out of zs
def mem.ne.b(b: Bool, +zs: List<&2, U32>, +q: U32, +i: U32, eb: {U32.is_eq(q, i) == b : Bool},
  hq: {PM.Mem(zs, q) == True{} : Bool}, hi: {PM.Mem(zs, i) == False{} : Bool}) -> {U32.is_eq(q, i) == False{} : Bool}:
  match b:
    case True{}:
      +e = PM.u32.eq(q, i, eb)
      PM.bool.ft({U32.is_eq(q, i) == False{} : Bool}, Equal.trans(Bool, False{}, PM.Mem(zs, q), True{},
        Equal.sym(Bool, PM.Mem(zs, q), False{}, (%Equal.sym(U32, q, i, e) : {PM.Mem(zs, _) == False{} : Bool}; hi)), hq))
    case False{}:
      eb

def mem.ne(+zs: List<&2, U32>, +q: U32, +i: U32, hq: {PM.Mem(zs, q) == True{} : Bool}, hi: {PM.Mem(zs, i) == False{} : Bool}) ->
  {U32.is_eq(q, i) == False{} : Bool}:
  mem.ne.b(U32.is_eq(q, i), zs, q, i, {==}, hq, hi)

# a set at a cell out of zs keeps the cells of zs
def kp.set(+m: Cr.Cir.Cells, +m2: Cr.Cir.Cells, +zs: List<&2, U32>, +i: U32, +c: Cr.Cir.Cell, k: Kp(m, m2, zs),
  hi: {PM.Mem(zs, i) == False{} : Bool}) -> Kp(m, Cr.Cir.Cells.set(m2, i, c), zs):
  +q => +h => Equal.trans(Cr.Cir.Cell, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m2, i, c), q), Cr.Cir.Cells.get(m2, q), Cr.Cir.Cells.get(m, q),
    PM.cl.go(m2, q, i, c, mem.ne(zs, q, i, h, hi)), k(q, h))

# the same set of both keeps the agreement
def agr.set.b(b: Bool, +m: Cr.Cir.Cells, +v: Cr.Cir.Cells, +zs: List<&2, U32>, +i: U32, +c: Cr.Cir.Cell, +q: U32,
  +eb: {U32.is_eq(q, i) == b : Bool}, a: Agr(m, v, zs), hq: {PM.Mem(zs, q) == False{} : Bool}) ->
  {Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, i, c), q) == Cr.Cir.Cells.get(Cr.Cir.Cells.set(v, i, c), q) : Cr.Cir.Cell}:
  match b:
    case True{}:
      +e = PM.u32.eq(q, i, eb)
      %Equal.sym(U32, q, i, e) : {Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, i, c), _) == Cr.Cir.Cells.get(Cr.Cir.Cells.set(v, i, c), _) : Cr.Cir.Cell}
      Equal.trans(Cr.Cir.Cell, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, i, c), i), c, Cr.Cir.Cells.get(Cr.Cir.Cells.set(v, i, c), i),
        PM.cl.gs(m, i, c), Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(Cr.Cir.Cells.set(v, i, c), i), c, PM.cl.gs(v, i, c)))
    case False{}:
      Equal.trans(Cr.Cir.Cell, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, i, c), q), Cr.Cir.Cells.get(m, q), Cr.Cir.Cells.get(Cr.Cir.Cells.set(v, i, c), q),
        PM.cl.go(m, q, i, c, eb),
        Equal.trans(Cr.Cir.Cell, Cr.Cir.Cells.get(m, q), Cr.Cir.Cells.get(v, q), Cr.Cir.Cells.get(Cr.Cir.Cells.set(v, i, c), q), a(q, hq),
          Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(Cr.Cir.Cells.set(v, i, c), q), Cr.Cir.Cells.get(v, q), PM.cl.go(v, q, i, c, eb))))

def agr.set(+m: Cr.Cir.Cells, +v: Cr.Cir.Cells, +zs: List<&2, U32>, +i: U32, +c: Cr.Cir.Cell, a: Agr(m, v, zs)) ->
  Agr(Cr.Cir.Cells.set(m, i, c), Cr.Cir.Cells.set(v, i, c), zs):
  +q => +hq => agr.set.b(U32.is_eq(q, i), m, v, zs, i, c, q, {==}, a, hq)

# a store of a field of a cell out of zs, in both
def agr.put.b(b: Bool, +m: Cr.Cir.Cells, +v: Cr.Cir.Cells, +zs: List<&2, U32>, +k: Nat, +i: U32, +x: U32, +q: U32,
  +eb: {U32.is_eq(q, i) == b : Bool}, a: Agr(m, v, zs), +hi: {PM.Mem(zs, i) == False{} : Bool},
  +hq: {PM.Mem(zs, q) == False{} : Bool}) ->
  {Cr.Cir.Cells.get(X.X.put(m, k, i, x), q) == Cr.Cir.Cells.get(X.X.put(v, k, i, x), q) : Cr.Cir.Cell}:
  match b:
    case True{}:
      +e = PM.u32.eq(q, i, eb)
      +ci = a(i, hi)
      %Equal.sym(U32, q, i, e) : {Cr.Cir.Cells.get(X.X.put(m, k, i, x), _) == Cr.Cir.Cells.get(X.X.put(v, k, i, x), _) : Cr.Cir.Cell}
      %ci : {Cr.Cir.Cells.get(X.X.put(m, k, i, x), i) == Cr.Cir.Cells.get(Cr.Cir.Cells.set(v, i, Cr.Cir.Cell.set(k, _, x)), i) : Cr.Cir.Cell}
      Equal.trans(Cr.Cir.Cell, Cr.Cir.Cells.get(X.X.put(m, k, i, x), i), Cr.Cir.Cell.set(k, Cr.Cir.Cells.get(m, i), x),
        Cr.Cir.Cells.get(Cr.Cir.Cells.set(v, i, Cr.Cir.Cell.set(k, Cr.Cir.Cells.get(m, i), x)), i),
        PM.cl.gs(m, i, Cr.Cir.Cell.set(k, Cr.Cir.Cells.get(m, i), x)),
        Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(Cr.Cir.Cells.set(v, i, Cr.Cir.Cell.set(k, Cr.Cir.Cells.get(m, i), x)), i),
          Cr.Cir.Cell.set(k, Cr.Cir.Cells.get(m, i), x), PM.cl.gs(v, i, Cr.Cir.Cell.set(k, Cr.Cir.Cells.get(m, i), x))))
    case False{}:
      Equal.trans(Cr.Cir.Cell, Cr.Cir.Cells.get(X.X.put(m, k, i, x), q), Cr.Cir.Cells.get(m, q), Cr.Cir.Cells.get(X.X.put(v, k, i, x), q),
        PM.cl.go(m, q, i, Cr.Cir.Cell.set(k, Cr.Cir.Cells.get(m, i), x), eb),
        Equal.trans(Cr.Cir.Cell, Cr.Cir.Cells.get(m, q), Cr.Cir.Cells.get(v, q), Cr.Cir.Cells.get(X.X.put(v, k, i, x), q), a(q, hq),
          Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(X.X.put(v, k, i, x), q), Cr.Cir.Cells.get(v, q),
            PM.cl.go(v, q, i, Cr.Cir.Cell.set(k, Cr.Cir.Cells.get(v, i), x), eb))))

def agr.put(+m: Cr.Cir.Cells, +v: Cr.Cir.Cells, +zs: List<&2, U32>, +k: Nat, +i: U32, +x: U32, a: Agr(m, v, zs),
  +hi: {PM.Mem(zs, i) == False{} : Bool}) -> Agr(X.X.put(m, k, i, x), X.X.put(v, k, i, x), zs):
  +q => +hq => agr.put.b(U32.is_eq(q, i), m, v, zs, k, i, x, q, {==}, a, hi, hq)

def kp.put(+m: Cr.Cir.Cells, +m2: Cr.Cir.Cells, +zs: List<&2, U32>, +k: Nat, +i: U32, +x: U32, kk: Kp(m, m2, zs),
  hi: {PM.Mem(zs, i) == False{} : Bool}) -> Kp(m, X.X.put(m2, k, i, x), zs):
  kp.set(m, m2, zs, i, Cr.Cir.Cell.set(k, Cr.Cir.Cells.get(m2, i), x), kk, hi)

# Field 1
# -------

# the cells m2 differ from m in field 1 only
def F1(+m: Cr.Cir.Cells, +m2: Cr.Cir.Cells) -> Type:
  @q: U32 -> {Cr.Cir.Cells.get(m2, q) == Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, q), PM.Fd(1n, m2, q)) : Cr.Cir.Cell}

def c1.get(+y: Cr.Cir.Cell, +w: U32) -> {Cr.Cir.Cell.get(1n, Cr.Cir.Cell.set(1n, y, w)) == w : U32}:
  match y:
    case Cr.Cir.Cell{a, b, x2, x3, x4}:
      {==}

def c1.set2(+y: Cr.Cir.Cell, +a: U32, +b: U32) -> {Cr.Cir.Cell.set(1n, Cr.Cir.Cell.set(1n, y, a), b) == Cr.Cir.Cell.set(1n, y, b) : Cr.Cir.Cell}:
  match y:
    case Cr.Cir.Cell{c0, c1, x2, x3, x4}:
      {==}

# a field other than 1 of a cell set in field 1
def c1.other(+k: Nat, +y: Cr.Cir.Cell, +w: U32, hk: {Nat.is_eq(k, 1n) == False{} : Bool}) ->
  {Cr.Cir.Cell.get(k, Cr.Cir.Cell.set(1n, y, w)) == Cr.Cir.Cell.get(k, y) : U32}:
  match k y:
    case 0n Cr.Cir.Cell{c0, c1, x2, x3, x4}:
      {==}
    case 1n Cr.Cir.Cell{c0, c1, x2, x3, x4}:
      X.k.ft({Cr.Cir.Cell.get(1n, Cr.Cir.Cell.set(1n, Cr.Cir.Cell{c0, c1, x2, x3, x4}, w)) == Cr.Cir.Cell.get(1n, Cr.Cir.Cell{c0, c1, x2, x3, x4}) : U32}, hk)
    case 2n Cr.Cir.Cell{c0, c1, x2, x3, x4}:
      {==}
    case 3n Cr.Cir.Cell{c0, c1, x2, x3, x4}:
      {==}
    case 4n+p Cr.Cir.Cell{c0, c1, x2, x3, x4}:
      {==}

def f1.refl(+m: Cr.Cir.Cells) -> F1(m, m):
  +q => PM.set1.id(Cr.Cir.Cells.get(m, q))

def f1.put.b(b: Bool, +m: Cr.Cir.Cells, +i: U32, +x: U32, +q: U32, +eb: {U32.is_eq(q, i) == b : Bool}) ->
  {Cr.Cir.Cells.get(X.X.put(m, 1n, i, x), q) == Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, q), PM.Fd(1n, X.X.put(m, 1n, i, x), q)) : Cr.Cir.Cell}:
  match b:
    case True{}:
      +e = PM.u32.eq(q, i, eb)
      +y = Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, i), x)
      %Equal.sym(U32, q, i, e) : {Cr.Cir.Cells.get(X.X.put(m, 1n, i, x), _) == Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, _), PM.Fd(1n, X.X.put(m, 1n, i, x), _)) : Cr.Cir.Cell}
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(X.X.put(m, 1n, i, x), i), y, PM.cl.gs(m, i, y)) :
        {_ == Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, i), Cr.Cir.Cell.get(1n, _)) : Cr.Cir.Cell}
      %Equal.sym(U32, Cr.Cir.Cell.get(1n, y), x, c1.get(Cr.Cir.Cells.get(m, i), x)) : {y == Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, i), _) : Cr.Cir.Cell}
      {==}
    case False{}:
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(X.X.put(m, 1n, i, x), q), Cr.Cir.Cells.get(m, q),
        PM.cl.go(m, q, i, Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, i), x), eb)) :
        {_ == Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, q), Cr.Cir.Cell.get(1n, _)) : Cr.Cir.Cell}
      PM.set1.id(Cr.Cir.Cells.get(m, q))

def f1.put(+m: Cr.Cir.Cells, +i: U32, +x: U32) -> F1(m, X.X.put(m, 1n, i, x)):
  +q => f1.put.b(U32.is_eq(q, i), m, i, x, q, {==})

def f1.trans(+m: Cr.Cir.Cells, +m2: Cr.Cir.Cells, +m3: Cr.Cir.Cells, a: F1(m, m2), b: F1(m2, m3)) -> F1(m, m3):
  +q =>
    +w2 = PM.Fd(1n, m2, q)
    +w3 = PM.Fd(1n, m3, q)
    Equal.trans(Cr.Cir.Cell, Cr.Cir.Cells.get(m3, q), Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m2, q), w3),
      Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, q), w3), b(q),
      Equal.trans(Cr.Cir.Cell, Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m2, q), w3),
        Cr.Cir.Cell.set(1n, Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, q), w2), w3), Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, q), w3),
        Equal.cong(Cr.Cir.Cell, Cr.Cir.Cell, y => Cr.Cir.Cell.set(1n, y, w3), Cr.Cir.Cells.get(m2, q), Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, q), w2), a(q)),
        c1.set2(Cr.Cir.Cells.get(m, q), w2, w3)))

# Two runs
# --------

# after a run from the registers regs on m and on v: the registers regs2,
# cells m2 and v2 that agree but at zs and keep zs; m2 differs from m in
# field 1 only; 63 registers, of which aq and am stay
def Rel2(+regs: List<&2, U32>, +regs2: List<&2, U32>, +m: Cr.Cir.Cells, +v: Cr.Cir.Cells, +m2: Cr.Cir.Cells, +v2: Cr.Cir.Cells,
  +zs: List<&2, U32>) -> Type:
  Agr(m2, v2, zs) & (Kp(m, m2, zs) & (Kp(v, v2, zs) & (F1(m, m2) & ({List.length(&2, U32, regs2) == 63n : Nat} &
    ({List.get(&2, U32, regs2, 6n) == List.get(&2, U32, regs, 6n) : Maybe<&2, U32>} &
     {List.get(&2, U32, regs2, 7n) == List.get(&2, U32, regs, 7n) : Maybe<&2, U32>})))))

# s runs on m and on v to such states
def Two(+f: Nat, +s: Cr.Cir.Stmt, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +v: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +zs: List<&2, U32>) -> Type:
  Sigma<&1, &1, List<&2, U32>, regs2 => Sigma<&1, &1, Cr.Cir.Cells, m2 => Sigma<&1, &1, Cr.Cir.Cells, v2 =>
    {Cr.Cir.exec(f, s, X.X.st(regs, m, nx, fi, im, pg, lim, inp)) == Cr.Cir.Out.next{X.X.st(regs2, m2, nx, fi, im, pg, lim, inp)} : Cr.Cir.Out} &
    ({Cr.Cir.exec(f, s, X.X.st(regs, v, nx, fi, im, pg, lim, inp)) == Cr.Cir.Out.next{X.X.st(regs2, v2, nx, fi, im, pg, lim, inp)} : Cr.Cir.Out} &
    Rel2(regs, regs2, m, v, m2, v2, zs))>>>

# a run that changes nothing
def two.id(+f: Nat, +s: Cr.Cir.Stmt, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +v: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +zs: List<&2, U32>, a: Agr(m, v, zs), +hl: {List.length(&2, U32, regs) == 63n : Nat},
  em: {Cr.Cir.exec(f, s, X.X.st(regs, m, nx, fi, im, pg, lim, inp)) == Cr.Cir.Out.next{X.X.st(regs, m, nx, fi, im, pg, lim, inp)} : Cr.Cir.Out},
  ev: {Cr.Cir.exec(f, s, X.X.st(regs, v, nx, fi, im, pg, lim, inp)) == Cr.Cir.Out.next{X.X.st(regs, v, nx, fi, im, pg, lim, inp)} : Cr.Cir.Out}) ->
  Two(f, s, regs, m, v, nx, fi, im, pg, lim, inp, zs):
  (regs, (m, (v, (em, (ev, (a, (kp.refl(m, zs), (kp.refl(v, zs), (f1.refl(m), (hl, ({==}, {==})))))))))))

# a set of r keeps the register j
def L.keep(xs: List<&2, U32>, r: Nat, j: Nat, +v: U32, ne: {Nat.is_eq(r, j) == False{} : Bool}) ->
  {List.get(&2, U32, List.set(&2, U32, xs, r, v), j) == List.get(&2, U32, xs, j) : Maybe<&2, U32>}:
  match xs r j:
    case Nil{} _ _:
      {==}
    case Con{x, t} 0n 0n:
      X.k.ft({List.get(&2, U32, List.set(&2, U32, Con{x, t}, 0n, v), 0n) == List.get(&2, U32, Con{x, t}, 0n) : Maybe<&2, U32>}, ne)
    case Con{x, t} 0n 1n+q:
      {==}
    case Con{x, t} 1n+p 0n:
      {==}
    case Con{x, t} 1n+p 1n+q:
      L.keep(t, p, q, v, ne)

# a property of a cell, carried along an equation
def tr.cell(-P: Cr.Cir.Cell -> Type, -y1: Cr.Cir.Cell, -y2: Cr.Cir.Cell, e: {y1 == y2 : Cr.Cir.Cell}, h: P(y1)) -> P(y2):
  %e : P(_)
  h

def tr.u32(-P: U32 -> Type, -a: U32, -b: U32, e: {a == b : U32}, h: P(a)) -> P(b):
  %e : P(_)
  h

# M.dec(dx)
# ---------

def sim.dec.d(b: Bool, +f: Nat, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +v: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +zs: List<&2, U32>, +x: U32, +pend: U32,
  +hl: {List.length(&2, U32, regs) == 63n : Nat}, +h4: {List.get(&2, U32, regs, 4n) == Some{x} : Maybe<&2, U32>},
  +h3: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>}, a: Agr(m, v, zs),
  +hz: {U32.is_eq(x, 0) == False{} : Bool}, +hc: {Cr.Cir.is_cell(x, im, fi, nx) == True{} : Bool},
  +hm: {PM.Mem(zs, x) == False{} : Bool}, +ex: {Cr.Cir.Cells.get(m, x) == Cr.Cir.Cells.get(v, x) : Cr.Cir.Cell},
  +hs: {U32.is_ne(U32.and(Cr.Cir.Cell.get(0n, Cr.Cir.Cells.get(m, x)), 1024), 0) == False{} : Bool},
  +eb: {U32.is_eq(U32.sub(Cr.Cir.Cell.get(1n, Cr.Cir.Cells.get(m, x)), 1), 0) == b : Bool}) ->
  Two(f, Mc.M.dec(Mc.R.dx()), regs, m, v, nx, fi, im, pg, lim, inp, zs):
  match b:
    case False{}:
      +d = U32.sub(Cr.Cir.Cell.get(1n, Cr.Cir.Cells.get(m, x)), 1)
      +hsv = tr.cell(y => {U32.is_ne(U32.and(Cr.Cir.Cell.get(0n, y), 1024), 0) == False{} : Bool}, Cr.Cir.Cells.get(m, x), Cr.Cir.Cells.get(v, x), ex, hs)
      +em = X.dec.eq.n(f, regs, m, nx, fi, im, pg, lim, inp, 4n, x, hl, h4, hz, hc, hs, eb, {==})
      +ev0 = X.dec.eq.n(f, regs, v, nx, fi, im, pg, lim, inp, 4n, x, hl, h4, hz, hc, hsv,
        tr.cell(y => {U32.is_eq(U32.sub(Cr.Cir.Cell.get(1n, y), 1), 0) == False{} : Bool}, Cr.Cir.Cells.get(m, x), Cr.Cir.Cells.get(v, x), ex, eb), {==})
      +ev = tr.cell(y => {Cr.Cir.exec(f, Mc.M.dec(4n), X.X.st(regs, v, nx, fi, im, pg, lim, inp)) ==
          Cr.Cir.Out.next{X.X.st(X.X.set(regs, 5n, U32.sub(Cr.Cir.Cell.get(1n, y), 1)), X.X.put(v, 1n, x, U32.sub(Cr.Cir.Cell.get(1n, y), 1)), nx, fi, im, pg, lim, inp)} : Cr.Cir.Out},
        Cr.Cir.Cells.get(v, x), Cr.Cir.Cells.get(m, x), Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(m, x), Cr.Cir.Cells.get(v, x), ex), ev0)
      (X.X.set(regs, 5n, d), (X.X.put(m, 1n, x, d), (X.X.put(v, 1n, x, d), (em, (ev,
        (agr.put(m, v, zs, 1n, x, d, a, hm), (kp.put(m, m, zs, 1n, x, d, kp.refl(m, zs), hm), (kp.put(v, v, zs, 1n, x, d, kp.refl(v, zs), hm),
        (f1.put(m, x, d), (X.L.len(regs, 5n, d, 63n, hl), (L.keep(regs, 5n, 6n, d, {==}), L.keep(regs, 5n, 7n, d, {==}))))))))))))
    case True{}:
      +d = U32.sub(Cr.Cir.Cell.get(1n, Cr.Cir.Cells.get(m, x)), 1)
      +hsv = tr.cell(y => {U32.is_ne(U32.and(Cr.Cir.Cell.get(0n, y), 1024), 0) == False{} : Bool}, Cr.Cir.Cells.get(m, x), Cr.Cir.Cells.get(v, x), ex, hs)
      +em = X.dec.eq.p(f, regs, m, nx, fi, im, pg, lim, inp, 4n, x, pend, hl, h4, h3, hz, hc, hs, eb, {==})
      +ev0 = X.dec.eq.p(f, regs, v, nx, fi, im, pg, lim, inp, 4n, x, pend, hl, h4, h3, hz, hc, hsv,
        tr.cell(y => {U32.is_eq(U32.sub(Cr.Cir.Cell.get(1n, y), 1), 0) == True{} : Bool}, Cr.Cir.Cells.get(m, x), Cr.Cir.Cells.get(v, x), ex, eb), {==})
      +ev = tr.cell(y => {Cr.Cir.exec(f, Mc.M.dec(4n), X.X.st(regs, v, nx, fi, im, pg, lim, inp)) ==
          Cr.Cir.Out.next{X.X.st(X.X.set(X.X.set(regs, 5n, U32.sub(Cr.Cir.Cell.get(1n, y), 1)), 3n, x),
            X.X.put(X.X.put(v, 1n, x, U32.sub(Cr.Cir.Cell.get(1n, y), 1)), 1n, x, pend), nx, fi, im, pg, lim, inp)} : Cr.Cir.Out},
        Cr.Cir.Cells.get(v, x), Cr.Cir.Cells.get(m, x), Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(m, x), Cr.Cir.Cells.get(v, x), ex), ev0)
      +r1 = X.X.set(regs, 5n, d)
      +m1 = X.X.put(m, 1n, x, d)
      +v1 = X.X.put(v, 1n, x, d)
      k1 = kp.put(m, m, zs, 1n, x, d, kp.refl(m, zs), hm)
      j1 = kp.put(v, v, zs, 1n, x, d, kp.refl(v, zs), hm)
      (X.X.set(r1, 3n, x), (X.X.put(m1, 1n, x, pend), (X.X.put(v1, 1n, x, pend), (em, (ev,
        (agr.put(m1, v1, zs, 1n, x, pend, agr.put(m, v, zs, 1n, x, d, a, hm), hm),
        (kp.trans(m, m, X.X.put(m1, 1n, x, pend), zs, kp.refl(m, zs), kp.put(m, m1, zs, 1n, x, pend, k1, hm)),
        (kp.trans(v, v, X.X.put(v1, 1n, x, pend), zs, kp.refl(v, zs), kp.put(v, v1, zs, 1n, x, pend, j1, hm)),
        (f1.trans(m, m1, X.X.put(m1, 1n, x, pend), f1.put(m, x, d), f1.put(m1, x, pend)),
        (X.L.len(r1, 3n, x, 63n, X.L.len(regs, 5n, d, 63n, hl)),
        (Equal.trans(Maybe<&2, U32>, List.get(&2, U32, X.X.set(r1, 3n, x), 6n), List.get(&2, U32, r1, 6n), List.get(&2, U32, regs, 6n),
           L.keep(r1, 3n, 6n, x, {==}), L.keep(regs, 5n, 6n, d, {==})),
         Equal.trans(Maybe<&2, U32>, List.get(&2, U32, X.X.set(r1, 3n, x), 7n), List.get(&2, U32, r1, 7n), List.get(&2, U32, regs, 7n),
           L.keep(r1, 3n, 7n, x, {==}), L.keep(regs, 5n, 7n, d, {==})))))))))))))

def sim.dec.s(b: Bool, +f: Nat, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +v: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +zs: List<&2, U32>, +x: U32, +pend: U32,
  +hl: {List.length(&2, U32, regs) == 63n : Nat}, +h4: {List.get(&2, U32, regs, 4n) == Some{x} : Maybe<&2, U32>},
  +h3: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>}, a: Agr(m, v, zs),
  +hz: {U32.is_eq(x, 0) == False{} : Bool}, +hc: {Cr.Cir.is_cell(x, im, fi, nx) == True{} : Bool},
  +hm: {PM.Mem(zs, x) == False{} : Bool}, +ex: {Cr.Cir.Cells.get(m, x) == Cr.Cir.Cells.get(v, x) : Cr.Cir.Cell},
  +eb: {U32.is_ne(U32.and(Cr.Cir.Cell.get(0n, Cr.Cir.Cells.get(m, x)), 1024), 0) == b : Bool}) ->
  Two(f, Mc.M.dec(Mc.R.dx()), regs, m, v, nx, fi, im, pg, lim, inp, zs):
  match b:
    case True{}:
      two.id(f, Mc.M.dec(Mc.R.dx()), regs, m, v, nx, fi, im, pg, lim, inp, zs, a, hl,
        X.dec.eq.s(f, regs, m, nx, fi, im, pg, lim, inp, 4n, x, h4, hz, hc, eb),
        X.dec.eq.s(f, regs, v, nx, fi, im, pg, lim, inp, 4n, x, h4, hz, hc,
          tr.cell(y => {U32.is_ne(U32.and(Cr.Cir.Cell.get(0n, y), 1024), 0) == True{} : Bool}, Cr.Cir.Cells.get(m, x), Cr.Cir.Cells.get(v, x), ex, eb)))
    case False{}:
      sim.dec.d(U32.is_eq(U32.sub(Cr.Cir.Cell.get(1n, Cr.Cir.Cells.get(m, x)), 1), 0), f, regs, m, v, nx, fi, im, pg, lim, inp, zs, x, pend,
        hl, h4, h3, a, hz, hc, hm, ex, eb, {==})

# M.dec(dx) of the cell x in dx: 0, or a cell out of zs, the same in both
# (ex: Agr is used once, at the cells that M.dec writes)
def sim.dec.z(b: Bool, +f: Nat, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +v: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +zs: List<&2, U32>, +x: U32, +pend: U32,
  +hl: {List.length(&2, U32, regs) == 63n : Nat}, +h4: {List.get(&2, U32, regs, 4n) == Some{x} : Maybe<&2, U32>},
  +h3: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>}, a: Agr(m, v, zs),
  +hx: {Bool.or(U32.is_eq(x, 0), Bool.and(Bool.not(PM.Mem(zs, x)), Cr.Cir.is_cell(x, im, fi, nx))) == True{} : Bool},
  +ex: {Cr.Cir.Cells.get(m, x) == Cr.Cir.Cells.get(v, x) : Cr.Cir.Cell}, +eb: {U32.is_eq(x, 0) == b : Bool}) ->
  Two(f, Mc.M.dec(Mc.R.dx()), regs, m, v, nx, fi, im, pg, lim, inp, zs):
  match b:
    case True{}:
      +e = PM.u32.eq(x, 0, eb)
      +h40 = tr.u32(y => {List.get(&2, U32, regs, 4n) == Some{y} : Maybe<&2, U32>}, x, 0, e, h4)
      two.id(f, Mc.M.dec(Mc.R.dx()), regs, m, v, nx, fi, im, pg, lim, inp, zs, a, hl,
        X.dec.eq.z(f, regs, m, nx, fi, im, pg, lim, inp, 4n, h40), X.dec.eq.z(f, regs, v, nx, fi, im, pg, lim, inp, 4n, h40))
    case False{}:
      +ok = {Bool.and(Bool.not(PM.Mem(zs, x)), Cr.Cir.is_cell(x, im, fi, nx)) : Bool}
      +hy = {(%eb : {Bool.or(_, ok) == True{} : Bool}; hx) : {ok == True{} : Bool}}
      +hm = PM.not.t(PM.Mem(zs, x), PM.and.l(Bool.not(PM.Mem(zs, x)), Cr.Cir.is_cell(x, im, fi, nx), hy))
      +hc = PM.and.r(Bool.not(PM.Mem(zs, x)), Cr.Cir.is_cell(x, im, fi, nx), hy)
      sim.dec.s(U32.is_ne(U32.and(Cr.Cir.Cell.get(0n, Cr.Cir.Cells.get(m, x)), 1024), 0), f, regs, m, v, nx, fi, im, pg, lim, inp,
        zs, x, pend, hl, h4, h3, a, eb, hc, hm, ex, {==})
