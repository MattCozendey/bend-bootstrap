# compiler: the start of the machine, M.input (layer B)
# =====================================================
#
# M.input, from Cir.result's start state, leaves the focus the cell of
# Program.start(i): In.input.post (any fuel: next with In.Post, out of
# memory only below the budget of first + 1 + 27 |i| cells, or out of fuel)
# and In.input.done (the fuel 10 + |i| ends it), in the shapes of
# input.post and input.done of move_kit.bend, with In.Post in place of InvIn
# and the premise 272 <= first.
#
# Kit: In.Go(f, s, st, k, R, Om), a run of s then k, in CPS, out of memory
# only when Om holds (In.oom: below a budget of cells) (In.sq, In.set,
# In.str, In.mk, In.wh, In.wh.end, In.ifT, In.ifF, In.nop). The facts of a
# state: In.Fa (next is numbered N, F <= N, the image's cells 1 3 5 11 12
# 13 14 15 and the cache's entries stand for their terms, reading only cells
# below 16 or from F before N), In.St (a cell stands for a term), In.Fr (the
# cells that the run keeps). The rounds: In.ir (bits), In.il (8 rounds),
# In.cch (a new cache entry), In.lst (a new list cell), In.or (a byte),
# In.ol (the loop), In.inp (M.input). The start's facts: In.start.
#
# Pitfall: the checker normalizes two types that differ, even by a let or a
# def to unfold; a St or Im at a concrete fuel then explodes (T.tm.of has 3
# branches a level). So the lemmas take the fuels as variables, avoid lets
# of values in types, and spell the same terms in every type.

import Base
import ../../Shared/shared.bend as Sd
import ../../Book/impl.bend as Bk
import ../../Wasm/impl.bend as Wa
import ../../Program/impl.bend as Pg
import ../Cir/impl.bend as Cr
import ./impl.bend as Mc
import ./cell_terms.bend as T
import ../need_big.bend as N
import ../Cir/module_round_trip.bend as PM
import ../Cir/instrs_round_trip.bend as PI
import ../img_small.bend as PG
import ./definitions.bend as D
import ./first_cell_past_table.bend as FC

# Cells
# -----

# a cell set at w is there
def Cl.get_set.at(n: Nat, +w: Word(n), +m: Cr.Cir.Cells, +c: Cr.Cir.Cell) ->
  {Cr.Cir.Cells.get.at(n, w, Cr.Cir.Cells.set.at(n, w, m, c)) == c : Cr.Cir.Cell}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{False{}, +t}:
          match m:
            case Cr.Cir.Cells.node{+lo, +hi}:
              Cl.get_set.at(p, t, lo, c)
            case Cr.Cir.Cells.none{}:
              Cl.get_set.at(p, t, Cr.Cir.Cells.none{}, c)
            case Cr.Cir.Cells.one{+d}:
              Cl.get_set.at(p, t, Cr.Cir.Cells.none{}, c)
        case WCon{True{}, +t}:
          match m:
            case Cr.Cir.Cells.node{+lo, +hi}:
              Cl.get_set.at(p, t, hi, c)
            case Cr.Cir.Cells.none{}:
              Cl.get_set.at(p, t, Cr.Cir.Cells.none{}, c)
            case Cr.Cir.Cells.one{+d}:
              Cl.get_set.at(p, t, Cr.Cir.Cells.none{}, c)

def Cl.get_set(+m: Cr.Cir.Cells, +i: U32, +c: Cr.Cir.Cell) -> {Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, i, c), i) == c : Cr.Cir.Cell}:
  match i:
    case U32{+w}:
      Cl.get_set.at(32n, w, m, c)

# a cell set twice at w holds the second
def Cl.set_set.at(n: Nat, +w: Word(n), +m: Cr.Cir.Cells, +c: Cr.Cir.Cell, +d: Cr.Cir.Cell) ->
  {Cr.Cir.Cells.set.at(n, w, m, d) == Cr.Cir.Cells.set.at(n, w, Cr.Cir.Cells.set.at(n, w, m, c), d) : Cr.Cir.Cells}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{False{}, +t}:
          match m:
            case Cr.Cir.Cells.node{+lo, +hi}:
              %Cl.set_set.at(p, t, lo, c, d) : {Cr.Cir.Cells.node{Cr.Cir.Cells.set.at(p, t, lo, d), hi} == Cr.Cir.Cells.node{_, hi} : Cr.Cir.Cells}
              {==}
            case Cr.Cir.Cells.none{}:
              %Cl.set_set.at(p, t, Cr.Cir.Cells.none{}, c, d) : {Cr.Cir.Cells.node{Cr.Cir.Cells.set.at(p, t, Cr.Cir.Cells.none{}, d), Cr.Cir.Cells.none{}} == Cr.Cir.Cells.node{_, Cr.Cir.Cells.none{}} : Cr.Cir.Cells}
              {==}
            case Cr.Cir.Cells.one{+e}:
              %Cl.set_set.at(p, t, Cr.Cir.Cells.none{}, c, d) : {Cr.Cir.Cells.node{Cr.Cir.Cells.set.at(p, t, Cr.Cir.Cells.none{}, d), Cr.Cir.Cells.none{}} == Cr.Cir.Cells.node{_, Cr.Cir.Cells.none{}} : Cr.Cir.Cells}
              {==}
        case WCon{True{}, +t}:
          match m:
            case Cr.Cir.Cells.node{+lo, +hi}:
              %Cl.set_set.at(p, t, hi, c, d) : {Cr.Cir.Cells.node{lo, Cr.Cir.Cells.set.at(p, t, hi, d)} == Cr.Cir.Cells.node{lo, _} : Cr.Cir.Cells}
              {==}
            case Cr.Cir.Cells.none{}:
              %Cl.set_set.at(p, t, Cr.Cir.Cells.none{}, c, d) : {Cr.Cir.Cells.node{Cr.Cir.Cells.none{}, Cr.Cir.Cells.set.at(p, t, Cr.Cir.Cells.none{}, d)} == Cr.Cir.Cells.node{Cr.Cir.Cells.none{}, _} : Cr.Cir.Cells}
              {==}
            case Cr.Cir.Cells.one{+e}:
              %Cl.set_set.at(p, t, Cr.Cir.Cells.none{}, c, d) : {Cr.Cir.Cells.node{Cr.Cir.Cells.none{}, Cr.Cir.Cells.set.at(p, t, Cr.Cir.Cells.none{}, d)} == Cr.Cir.Cells.node{Cr.Cir.Cells.none{}, _} : Cr.Cir.Cells}
              {==}

def Cl.set_set(+m: Cr.Cir.Cells, +i: U32, +c: Cr.Cir.Cell, +d: Cr.Cir.Cell) ->
  {Cr.Cir.Cells.set(m, i, d) == Cr.Cir.Cells.set(Cr.Cir.Cells.set(m, i, c), i, d) : Cr.Cir.Cells}:
  match i:
    case U32{+w}:
      Cl.set_set.at(32n, w, m, c, d)

# no cell is all zeros
def Cl.get_none(n: Nat, +v: Word(n)) -> {Cr.Cir.Cell.zero() == Cr.Cir.Cells.get.at(n, v, Cr.Cir.Cells.none{}) : Cr.Cir.Cell}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match v:
        case WCon{False{}, +s}:
          {==}
        case WCon{True{}, +s}:
          {==}

# a set at w keeps the cell at another address v
def Cl.get_other.at(n: Nat, +v: Word(n), +w: Word(n), +m: Cr.Cir.Cells, +c: Cr.Cir.Cell, ne: {v == w : Word(n)} -> Empty) ->
  {Cr.Cir.Cells.get.at(n, v, m) == Cr.Cir.Cells.get.at(n, v, Cr.Cir.Cells.set.at(n, w, m, c)) : Cr.Cir.Cell}:
  match n:
    case 0n:
      match v w:
        case WNil{} WNil{}:
          Empty.absurd({Cr.Cir.Cells.get.at(0n, WNil{}, m) == Cr.Cir.Cells.get.at(0n, WNil{}, Cr.Cir.Cells.set.at(0n, WNil{}, m, c)) : Cr.Cir.Cell}, ne({==}))
    case 1n+(+p):
      match v w:
        case WCon{False{}, +s} WCon{False{}, +t}:
          match m:
            case Cr.Cir.Cells.node{+lo, +hi}:
              Cl.get_other.at(p, s, t, lo, c, e => ne(Equal.cong(Word(p), Word(1n+p), x => WCon{False{}, x}, s, t, e)))
            case Cr.Cir.Cells.none{}:
              Equal.trans(Cr.Cir.Cell, Cr.Cir.Cell.zero(), Cr.Cir.Cells.get.at(p, s, Cr.Cir.Cells.none{}), Cr.Cir.Cells.get.at(p, s, Cr.Cir.Cells.set.at(p, t, Cr.Cir.Cells.none{}, c)),
                Cl.get_none(p, s), Cl.get_other.at(p, s, t, Cr.Cir.Cells.none{}, c, e => ne(Equal.cong(Word(p), Word(1n+p), x => WCon{False{}, x}, s, t, e))))
            case Cr.Cir.Cells.one{+d}:
              Equal.trans(Cr.Cir.Cell, Cr.Cir.Cell.zero(), Cr.Cir.Cells.get.at(p, s, Cr.Cir.Cells.none{}), Cr.Cir.Cells.get.at(p, s, Cr.Cir.Cells.set.at(p, t, Cr.Cir.Cells.none{}, c)),
                Cl.get_none(p, s), Cl.get_other.at(p, s, t, Cr.Cir.Cells.none{}, c, e => ne(Equal.cong(Word(p), Word(1n+p), x => WCon{False{}, x}, s, t, e))))
        case WCon{True{}, +s} WCon{True{}, +t}:
          match m:
            case Cr.Cir.Cells.node{+lo, +hi}:
              Cl.get_other.at(p, s, t, hi, c, e => ne(Equal.cong(Word(p), Word(1n+p), x => WCon{True{}, x}, s, t, e)))
            case Cr.Cir.Cells.none{}:
              Equal.trans(Cr.Cir.Cell, Cr.Cir.Cell.zero(), Cr.Cir.Cells.get.at(p, s, Cr.Cir.Cells.none{}), Cr.Cir.Cells.get.at(p, s, Cr.Cir.Cells.set.at(p, t, Cr.Cir.Cells.none{}, c)),
                Cl.get_none(p, s), Cl.get_other.at(p, s, t, Cr.Cir.Cells.none{}, c, e => ne(Equal.cong(Word(p), Word(1n+p), x => WCon{True{}, x}, s, t, e))))
            case Cr.Cir.Cells.one{+d}:
              Equal.trans(Cr.Cir.Cell, Cr.Cir.Cell.zero(), Cr.Cir.Cells.get.at(p, s, Cr.Cir.Cells.none{}), Cr.Cir.Cells.get.at(p, s, Cr.Cir.Cells.set.at(p, t, Cr.Cir.Cells.none{}, c)),
                Cl.get_none(p, s), Cl.get_other.at(p, s, t, Cr.Cir.Cells.none{}, c, e => ne(Equal.cong(Word(p), Word(1n+p), x => WCon{True{}, x}, s, t, e))))
        case WCon{False{}, +s} WCon{True{}, +t}:
          match m:
            case Cr.Cir.Cells.node{+lo, +hi}:
              {==}
            case Cr.Cir.Cells.none{}:
              Cl.get_none(p, s)
            case Cr.Cir.Cells.one{+d}:
              Cl.get_none(p, s)
        case WCon{True{}, +s} WCon{False{}, +t}:
          match m:
            case Cr.Cir.Cells.node{+lo, +hi}:
              {==}
            case Cr.Cir.Cells.none{}:
              Cl.get_none(p, s)
            case Cr.Cir.Cells.one{+d}:
              Cl.get_none(p, s)

def Cl.get_other(+m: Cr.Cir.Cells, +j: U32, +i: U32, +c: Cr.Cir.Cell, ne: {j == i : U32} -> Empty) ->
  {Cr.Cir.Cells.get(m, j) == Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, i, c), j) : Cr.Cir.Cell}:
  match j i:
    case U32{+v} U32{+w}:
      Cl.get_other.at(32n, v, w, m, c, e => ne(Equal.cong(Word(32n), U32, x => U32{x}, v, w, e)))

# Runs
# ----

# a state of the run: the registers, the cells, the next cell and the pages
def In.S(regs: List<&2, U32>, m: Cr.Cir.Cells, next: U32, F: U32, K: U32, pg: U32, L: U32, I: List<&2, Word(8n)>) -> Cr.Cir.State:
  Cr.Cir.State{regs, m, next, F, K, pg, L, I, Nil{}, 0}

# o ends after the statement with a state of which Q holds, or out of memory
# when Om holds (the budget: In.oom)
def In.Ok(o: Cr.Cir.Out, Q: Cr.Cir.State -> Type, Om: Type) -> Type:
  match o:
    case Cr.Cir.Out.next{st}:
      Q(st)
    case Cr.Cir.Out.halt{_, _}:
      Empty
    case Cr.Cir.Out.out_of_memory{}:
      Om
    case Cr.Cir.Out.trap{}:
      Empty
    case Cr.Cir.Out.not_done{}:
      Empty

# st is the state of regs, m and next, with any pages, and X holds
def In.Is(st: Cr.Cir.State, regs: List<&2, U32>, m: Cr.Cir.Cells, next: U32, F: U32, K: U32, L: U32, I: List<&2, Word(8n)>, X: Type) -> Type:
  match st:
    case Cr.Cir.State{rg, ms, nx, fi, im, +pg, li, inp, out, outn}:
      {In.S(regs, m, next, F, K, pg, L, I) == Cr.Cir.State{rg, ms, nx, fi, im, pg, li, inp, out, outn} : Cr.Cir.State} & X

# a statement, then more
def In.then(o: Cr.Cir.Out, -k: Cr.Cir.State -> Cr.Cir.Out, -Q: Cr.Cir.State -> Type, -R: Cr.Cir.State -> Type,
  -Om: Type, h: In.Ok(o, Q, Om), g: @st: Cr.Cir.State -> Q(st) -> In.Ok(k(st), R, Om)) -> In.Ok(Cr.Cir.exec.then(o, k), R, Om):
  match o:
    case Cr.Cir.Out.next{st}:
      g(st, h)
    case Cr.Cir.Out.halt{s, st}:
      match h:
    case Cr.Cir.Out.out_of_memory{}:
      h
    case Cr.Cir.Out.trap{}:
      match h:
    case Cr.Cir.Out.not_done{}:
      match h:

# a state of which Is holds, by its pages
def In.at(st: Cr.Cir.State, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +next: U32, +F: U32, +K: U32, +L: U32, +I: List<&2, Word(8n)>, -X: Type,
  -R: Cr.Cir.State -> Type, -Om: Type, -k: Cr.Cir.State -> Cr.Cir.Out, e: In.Is(st, regs, m, next, F, K, L, I, X),
  g: @pg: U32 -> X -> In.Ok(k(In.S(regs, m, next, F, K, pg, L, I)), R, Om)) -> In.Ok(k(st), R, Om):
  match st:
    case Cr.Cir.State{rg, ms, nx, fi, im, +pg, li, inp, out, outn}:
      (eq, x) = e
      %eq : In.Ok(k(_), R, Om)
      g(pg, x)

# a then b, when a ends in the state of regs, m and next
def In.seq(+f: Nat, a: Cr.Cir.Stmt, +b: Cr.Cir.Stmt, st: Cr.Cir.State, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +next: U32, +F: U32, +K: U32, +L: U32,
  +I: List<&2, Word(8n)>, -X: Type, -R: Cr.Cir.State -> Type,
  -Om: Type, h: In.Ok(Cr.Cir.exec(1n+f, a, st), s => In.Is(s, regs, m, next, F, K, L, I, X), Om),
  g: @pg: U32 -> X -> In.Ok(Cr.Cir.exec(1n+f, b, In.S(regs, m, next, F, K, pg, L, I)), R, Om)) ->
  In.Ok(Cr.Cir.exec(1n+f, Cr.Cir.Stmt.seq{a, b}, st), R, Om):
  In.then(Cr.Cir.exec(1n+f, a, st), t => Cr.Cir.exec(1n+f, b, t), s => In.Is(s, regs, m, next, F, K, L, I, X), R, Om, h,
    s => e => In.at(s, regs, m, next, F, K, L, I, X, R, Om, t => Cr.Cir.exec(1n+f, b, t), e, g))

# The budget
# ----------
#
# An alloc at the cell next fails when next is past 214748364, or when
# Cir.room finds no page for the cell's last byte, 20 next + 19: either way
# the limit has fewer than 20 (next + 1) bytes (In.oomb, In.oomf). So a run
# whose allocs take cells below Bc runs out of memory only when the limit
# has fewer than 20 Bc bytes (In.oom, In.Ok's out-of-memory case).

# out of memory, below the budget of Bc cells
def In.oom(+L: U32, +Bc: Nat) -> Type:
  N.Le(1n+D.Lim.bytes(L), Nat.mul(20n, Bc))

# k (1 + p) = k + k p
def In.mul_succ_r(k: Nat, +p: Nat) -> {Nat.mul(k, 1n+p) == Nat.add(k, Nat.mul(k, p)) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+(+j):
      %Equal.sym(Nat, Nat.mul(j, 1n+p), Nat.add(j, Nat.mul(j, p)), In.mul_succ_r(j, p)) : {Nat.add(1n+p, _) == Nat.add(1n+j, Nat.mul(1n+j, p)) : Nat}
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, Nat.add(j, Nat.mul(j, p))), Nat.add(j, Nat.add(p, Nat.mul(j, p))), N.add_swap(p, j, Nat.mul(j, p)))

# 20 x, as the cells' bytes count it and as hw.t20 does
def In.mul20(x: Nat) -> {Nat.mul(20n, x) == FC.hw.t20(x) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+(+p):
      %Equal.sym(Nat, Nat.mul(20n, 1n+p), Nat.add(20n, Nat.mul(20n, p)), In.mul_succ_r(20n, p)) : {_ == FC.hw.t20(1n+p) : Nat}
      %Equal.sym(Nat, Nat.mul(20n, p), FC.hw.t20(p), In.mul20(p)) : {Nat.add(20n, _) == FC.hw.t20(1n+p) : Nat}
      {==}

# 2^k x grows with x
def In.D_mono(k: Nat, +x: Nat, +y: Nat, h: N.Le(x, y)) -> N.Le(N.D(k, x), N.D(k, y)):
  match k:
    case 0n:
      h
    case 1n+(+q):
      N.double_mono(N.D(q, x), N.D(q, y), In.D_mono(q, x, y, h))

# 2^k (2 x) = 2 (2^k x)
def In.D_double(k: Nat, +x: Nat) -> {N.D(k, Nat.double(x)) == Nat.double(N.D(k, x)) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+(+q):
      Equal.cong(Nat, Nat, z => Nat.double(z), N.D(q, Nat.double(x)), Nat.double(N.D(q, x)), In.D_double(q, x))

# Big numbers meet only in equations, spelled as their types state them:
# bend2 computes a comparison of two types that differ by a def or a beta
# step, and the double of a big literal overflows its stack.

# 2^k x = hw.W(k), for x = 1
def In.W.eq(+k: Nat, -x: Nat, ex: {x == FC.hw.bn(True{}) : Nat}) -> {N.D(k, x) == FC.hw.W(k) : Nat}:
  %Equal.sym(Nat, x, FC.hw.bn(True{}), ex) : {N.D(k, _) == FC.hw.W(k) : Nat}
  {==}

# 2^16 K = 2^32, for K = 2^16
def In.w32.eq(+K: U32, eK: {U32.to_nat(K) == N.D(16n, 1n) : Nat}) -> {N.D(16n, U32.to_nat(K)) == FC.hw.W(32n) : Nat}:
  %Equal.sym(Nat, U32.to_nat(K), N.D(16n, 1n), eK) : {N.D(16n, _) == FC.hw.W(32n) : Nat}
  Equal.trans(Nat, N.D(16n, N.D(16n, 1n)), N.D(32n, 1n), FC.hw.W(32n), N.D_add(16n, 16n, 32n, 1n, {==}), In.W.eq(32n, 1n, {==}))

# the bytes of a limit, unfolded
def In.lim.unf(+L: U32) -> {D.Lim.bytes(L) == N.D(16n, U32.to_nat(Wa.Wasm.min(L, 65536))) : Nat}:
  {==}

# the minimum of L and K is at most K
def In.min.le2(+L: U32, +K: U32) -> N.Le(U32.to_nat(Wa.Wasm.min(L, K)), U32.to_nat(K)):
  N.min.case(U32.is_le(L, K), L, K, {==})

# the bytes of a limit are at most 2^16 65536
def In.lim.le16(+L: U32) -> N.Le(D.Lim.bytes(L), N.D(16n, U32.to_nat(65536))):
  %Equal.sym(Nat, D.Lim.bytes(L), N.D(16n, U32.to_nat(Wa.Wasm.min(L, 65536))), In.lim.unf(L)) : N.Le(_, N.D(16n, U32.to_nat(65536)))
  In.D_mono(16n, U32.to_nat(Wa.Wasm.min(L, 65536)), U32.to_nat(65536), In.min.le2(L, 65536))

# the bytes of a limit are at most 2^32
def In.lim.le(+L: U32) -> N.Le(D.Lim.bytes(L), FC.hw.W(32n)):
  N.le_rw_r(D.Lim.bytes(L), N.D(16n, U32.to_nat(65536)), FC.hw.W(32n), In.w32.eq(65536, N.val_65536()), In.lim.le16(L))

# a <= b gives 1 + a <= 1 + b
def In.le_succ2(-a: Nat, -b: Nat, h: N.Le(a, b)) -> N.Le(1n+a, 1n+b):
  h

# a comparison: below, or not below
def In.lt.le(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), e: {Cmp.is_lt(c) == True{} : Bool}) -> N.Le(1n+x, y):
  match c:
    case LT{}:
      r
    case EQ{}:
      Empty.absurd(N.Le(1n+x, y), N.false_ne_true(e))
    case GT{}:
      Empty.absurd(N.Le(1n+x, y), N.false_ne_true(e))

def In.nlt.le(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), e: {Cmp.is_lt(c) == False{} : Bool}) -> N.Le(y, x):
  match c:
    case LT{}:
      Empty.absurd(N.Le(y, x), N.true_ne_false(e))
    case EQ{}:
      %r : N.Le(_, x)
      N.le_refl(x)
    case GT{}:
      N.weaken(y, x, r)

def In.nle.lt(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), e: {Cmp.is_le(c) == False{} : Bool}) -> N.Le(1n+y, x):
  match c:
    case LT{}:
      Empty.absurd(N.Le(1n+y, x), N.true_ne_false(e))
    case EQ{}:
      Empty.absurd(N.Le(1n+y, x), N.true_ne_false(e))
    case GT{}:
      r

# The literal 214748364
# ---------------------
#
# Copied from Compiler/Cir/simulation_alloc_emit.bend (it imports
# Compiler/Cir/halt.bend, the whole compiler), over a variable x.

def In.q4(j: Nat) -> Nat:
  match j:
    case 0n:
      0n
    case 1n+q:
      4n+In.q4(q)

# n bits of 0x0CCC...C with j nibbles of 12 at the bottom, its lowest bit
# first; the index is n itself, so that the word of 32 bits is a Word(32n)
def In.wb(n: Nat, j: Nat) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n:
      WCon{False{}, WNil{}}
    case 2n:
      WCon{False{}, WCon{False{}, WNil{}}}
    case 3n:
      WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}
    case 4n+p:
      match j:
        case 0n:
          WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, In.wb(p, 0n)}}}}
        case 1n+q:
          WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, In.wb(p, q)}}}}

def In.wb.val(j: Nat, +n: Nat, e: {n == 4n+In.q4(j) : Nat}) -> {Word.to_nat(n, In.wb(n, j)) == FC.hw.pat(j) : Nat}:
  match j:
    case 0n:
      %Equal.sym(Nat, n, 4n, e) : {Word.to_nat(_, In.wb(_, 0n)) == FC.hw.pat(0n) : Nat}
      {==}
    case 1n+(+q):
      %Equal.sym(Nat, n, 4n+In.q4(1n+q), e) : {Word.to_nat(_, In.wb(_, 1n+q)) == FC.hw.pat(1n+q) : Nat}
      %Equal.sym(Nat, Word.to_nat(In.q4(1n+q), In.wb(In.q4(1n+q), q)), FC.hw.pat(q), In.wb.val(q, In.q4(1n+q), {==})) :
        {Nat.double(Nat.double(1n+Nat.double(1n+Nat.double(_)))) == Nat.add(12n, N.D(4n, FC.hw.pat(q))) : Nat}
      {==}

# x = 214748364 = pat(7)
def In.lit.pat(+x: U32, e: {x == 214748364 : U32}) -> {U32.to_nat(x) == FC.hw.pat(7n) : Nat}:
  %Equal.trans(U32, U32{In.wb(32n, 7n)}, 214748364, x, {==}, Equal.sym(U32, x, 214748364, e)) : {U32.to_nat(_) == FC.hw.pat(7n) : Nat}
  Equal.trans(Nat, U32.to_nat(U32{In.wb(32n, 7n)}), Word.to_nat(32n, In.wb(32n, 7n)), FC.hw.pat(7n), N.u32_to_nat(In.wb(32n, 7n)),
    In.wb.val(7n, 32n, {==}))

# A failed alloc
# --------------

# next past P, with 2^4 + 20 P = 2^32: the limit has fewer than 20 (next + 1) bytes
def In.oomb.of(+nx: Nat, +L: U32, +P: Nat, hP: {Nat.add(FC.hw.W(4n), FC.hw.t20(P)) == FC.hw.W(32n) : Nat}, hpn: N.Le(P, nx)) ->
  N.Le(1n+D.Lim.bytes(L), FC.hw.t20(1n+nx)):
  +b = {(%hP : N.Le(1n+_, 20n+FC.hw.t20(P)); N.le_add_l(3n, FC.hw.t20(P))) : N.Le(1n+FC.hw.W(32n), 20n+FC.hw.t20(P))}
  N.le_trans(1n+D.Lim.bytes(L), 1n+FC.hw.W(32n), FC.hw.t20(1n+nx), In.le_succ2(D.Lim.bytes(L), FC.hw.W(32n), In.lim.le(L)),
    N.le_trans(1n+FC.hw.W(32n), 20n+FC.hw.t20(P), FC.hw.t20(1n+nx), b, FC.hw.t20_mono(1n+P, 1n+nx, hpn)))

# next past 214748364
def In.oomb(+next: U32, +L: U32, eb: {U32.is_lt(next, 214748364) == False{} : Bool}) ->
  N.Le(1n+D.Lim.bytes(L), Nat.mul(20n, 1n+U32.to_nat(next))):
  +hpn = N.le_rw_l(U32.to_nat(214748364), FC.hw.pat(7n), U32.to_nat(next), In.lit.pat(214748364, {==}),
    In.nlt.le(U32.cmp(next, 214748364), U32.to_nat(next), U32.to_nat(214748364), N.U32.rel(next, 214748364), eb))
  %Equal.sym(Nat, Nat.mul(20n, 1n+U32.to_nat(next)), FC.hw.t20(1n+U32.to_nat(next)), In.mul20(1n+U32.to_nat(next))) :
    N.Le(1n+D.Lim.bytes(L), _)
  In.oomb.of(U32.to_nat(next), L, FC.hw.pat(7n), FC.hw.hP(7n, 32n, {==}), hpn)

# a Maybe that holds a value
def In.isS(x: Maybe<&2, U32>) -> Type:
  match x:
    case None{}:
      Empty
    case Some{_}:
      Unit

def In.sn(-x: U32, e: {Some{x} == None{} : Maybe<&2, U32>}) -> Empty:
  %e : In.isS(_)
  Unit{}

def In.room.if.none(a: Bool, b: Bool, -p: U32, -nd: U32, e: {Cr.Cir.room.if(a, b, p, nd) == None{} : Maybe<&2, U32>}) -> {b == False{} : Bool}:
  match a b:
    case True{} _:
      Empty.absurd({b == False{} : Bool}, In.sn(p, e))
    case False{} True{}:
      Empty.absurd({True{} == False{} : Bool}, In.sn(nd, e))
    case False{} False{}:
      {==}

# Cir.room finds none only when the limit does not hold need
def In.room.none(+b: U32, +p: U32, +lim: U32, e: {Cr.Cir.room(b, p, lim) == None{} : Maybe<&2, U32>}) ->
  {U32.is_le(U32.inc(U32.shrn(b, 16n)), lim) == False{} : Bool}:
  In.room.if.none(U32.is_le(U32.inc(U32.shrn(b, 16n)), p), U32.is_le(U32.inc(U32.shrn(b, 16n)), lim), p, U32.inc(U32.shrn(b, 16n)), e)

# the bits of w with a 0 on top have its value
def In.pad.val(n: Nat, +w: Word(n)) -> {Word.to_nat(1n+n, Word.shr.pad(n, w)) == Word.to_nat(n, w) : Nat}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+(+p):
      match w:
        case WCon{False{}, +t}:
          Equal.cong(Nat, Nat, z => Nat.double(z), Word.to_nat(1n+p, Word.shr.pad(p, t)), Word.to_nat(p, t), In.pad.val(p, t))
        case WCon{True{}, +t}:
          Equal.cong(Nat, Nat, z => 1n+Nat.double(z), Word.to_nat(1n+p, Word.shr.pad(p, t)), Word.to_nat(p, t), In.pad.val(p, t))

# 2 (x >> 1) <= x
def In.shr.le(x: U32) -> N.Le(Nat.double(U32.to_nat(U32.shr(x))), U32.to_nat(x)):
  match x:
    case U32{w}:
      match w:
        case WCon{False{}, +t}:
          %Equal.sym(Nat, Word.to_nat(32n, Word.shr.pad(31n, t)), Word.to_nat(31n, t), In.pad.val(31n, t)) :
            N.Le(Nat.double(_), Nat.double(Word.to_nat(31n, t)))
          N.le_refl(Nat.double(Word.to_nat(31n, t)))
        case WCon{True{}, +t}:
          %Equal.sym(Nat, Word.to_nat(32n, Word.shr.pad(31n, t)), Word.to_nat(31n, t), In.pad.val(31n, t)) :
            N.Le(Nat.double(_), 1n+Nat.double(Word.to_nat(31n, t)))
          N.le_succ(Nat.double(Word.to_nat(31n, t)), Nat.double(Word.to_nat(31n, t)), N.le_refl(Nat.double(Word.to_nat(31n, t))))

# 2^k (x >> k) <= x
def In.shrn.le(k: Nat, +x: U32) -> N.Le(N.D(k, U32.to_nat(U32.shrn(x, k))), U32.to_nat(x)):
  match k:
    case 0n:
      N.le_refl(U32.to_nat(x))
    case 1n+(+q):
      %In.D_double(q, U32.to_nat(U32.shr(U32.shrn(x, q)))) : N.Le(_, U32.to_nat(x))
      N.le_trans(N.D(q, Nat.double(U32.to_nat(U32.shr(U32.shrn(x, q))))), N.D(q, U32.to_nat(U32.shrn(x, q))), U32.to_nat(x),
        In.D_mono(q, Nat.double(U32.to_nat(U32.shr(U32.shrn(x, q)))), U32.to_nat(U32.shrn(x, q)), In.shr.le(U32.shrn(x, q))),
        In.shrn.le(q, x))

# the minimum of L and k is at most L
def In.min.le(b: Bool, +L: U32, +k: U32, e: {U32.is_le(L, k) == b : Bool}) -> N.Le(U32.to_nat(Wa.Wasm.min.if(b, L, k)), U32.to_nat(L)):
  match b:
    case True{}:
      N.le_refl(U32.to_nat(L))
    case False{}:
      N.weaken(U32.to_nat(k), U32.to_nat(L), In.nle.lt(U32.cmp(L, k), U32.to_nat(L), U32.to_nat(k), N.U32.rel(L, k), e))

# a sum of words is at most the sum of their values
def In.add.le(+a: U32, +b: U32) -> N.Le(U32.to_nat(U32.add(a, b)), Nat.add(U32.to_nat(a), U32.to_nat(b))):
  match a b:
    case U32{+x} U32{+y}:
      +V = Word.to_nat(32n, Word.add(32n, x, y))
      +Dc = N.D(32n, FC.hw.bn(FC.hw.cout(32n, x, y, False{})))
      N.le_rw_r(V, Nat.add(V, Dc), Nat.add(Word.to_nat(32n, x), Word.to_nat(32n, y)), FC.hw.adc(32n, x, y, False{}), N.le_add_r(V, Dc))

# no page for the cell next's last byte: the limit has fewer than 20 (next + 1) bytes
def In.oomf(+next: U32, +pg: U32, +L: U32, hn: {U32.is_lt(next, 214748364) == True{} : Bool},
  e: {Cr.Cir.room(U32.add(Cr.Cir.at(next), 19), pg, L) == None{} : Maybe<&2, U32>}) ->
  N.Le(1n+D.Lim.bytes(L), Nat.mul(20n, 1n+U32.to_nat(next))):
  +b = U32.add(Cr.Cir.at(next), 19)
  +s = U32.shrn(b, 16n)
  +tn = U32.to_nat(next)
  +h1 = In.nle.lt(U32.cmp(U32.inc(s), L), U32.to_nat(U32.inc(s)), U32.to_nat(L), N.U32.rel(U32.inc(s), L), In.room.none(b, pg, L, e))
  +h2 = N.le_trans(1n+U32.to_nat(L), U32.to_nat(U32.inc(s)), 1n+U32.to_nat(s), h1, N.U32.inc_le(s))
  +h3 = N.le_rw_l(N.D(16n, U32.to_nat(Wa.Wasm.min(L, 65536))), D.Lim.bytes(L), N.D(16n, U32.to_nat(L)),
    Equal.sym(Nat, D.Lim.bytes(L), N.D(16n, U32.to_nat(Wa.Wasm.min(L, 65536))), In.lim.unf(L)),
    In.D_mono(16n, U32.to_nat(Wa.Wasm.min(L, 65536)), U32.to_nat(L), In.min.le(U32.is_le(L, 65536), L, 65536, {==})))
  +h4 = N.le_trans(D.Lim.bytes(L), N.D(16n, U32.to_nat(L)), N.D(16n, U32.to_nat(s)), h3, In.D_mono(16n, U32.to_nat(L), U32.to_nat(s), h2))
  +h5 = N.le_trans(D.Lim.bytes(L), N.D(16n, U32.to_nat(s)), U32.to_nat(b), h4, In.shrn.le(16n, b))
  +hx = N.le_rw_r(tn, U32.to_nat(214748364), FC.hw.pat(7n), In.lit.pat(214748364, {==}),
    N.weaken(tn, U32.to_nat(214748364), In.lt.le(U32.cmp(next, 214748364), tn, U32.to_nat(214748364), N.U32.rel(next, 214748364), hn)))
  +ea = FC.hf.at.val(next, FC.hw.pat(7n), FC.hw.hP(7n, 32n, {==}), hx)
  +h6 = N.le_rw_r(U32.to_nat(b), Nat.add(U32.to_nat(Cr.Cir.at(next)), 19n), Nat.add(FC.hw.t20(tn), 19n),
    Equal.cong(Nat, Nat, z => Nat.add(z, 19n), U32.to_nat(Cr.Cir.at(next)), FC.hw.t20(tn), ea), In.add.le(Cr.Cir.at(next), 19))
  +h7 = N.le_rw_r(U32.to_nat(b), Nat.add(FC.hw.t20(tn), 19n), Nat.add(19n, FC.hw.t20(tn)), FC.hf.add.comm(FC.hw.t20(tn), 19n), h6)
  %Equal.sym(Nat, Nat.mul(20n, 1n+tn), FC.hw.t20(1n+tn), In.mul20(1n+tn)) : N.Le(1n+D.Lim.bytes(L), _)
  N.le_trans(D.Lim.bytes(L), U32.to_nat(b), 19n+FC.hw.t20(tn), h5, h7)

# 20 a <= 20 b, for a <= b
def In.mul20.mono(+a: Nat, +b: Nat, h: N.Le(a, b)) -> N.Le(Nat.mul(20n, a), Nat.mul(20n, b)):
  %Equal.sym(Nat, Nat.mul(20n, a), FC.hw.t20(a), In.mul20(a)) : N.Le(_, Nat.mul(20n, b))
  %Equal.sym(Nat, Nat.mul(20n, b), FC.hw.t20(b), In.mul20(b)) : N.Le(FC.hw.t20(a), _)
  FC.hw.t20_mono(a, b, h)

# out of memory below the budget a, so below a larger budget b
def In.oom.up(+L: U32, +a: Nat, +b: Nat, h: N.Le(a, b), z: N.Le(1n+D.Lim.bytes(L), Nat.mul(20n, a))) -> In.oom(L, b):
  N.le_trans(1n+D.Lim.bytes(L), Nat.mul(20n, a), Nat.mul(20n, b), z, In.mul20.mono(a, b, h))

# the cell next, numbered N, is below the budget Bc
def In.hb(+next: U32, +N: Nat, +Bc: Nat, eN: {U32.to_nat(next) == N : Nat}, h: N.Le(1n+N, Bc)) -> N.Le(1n+U32.to_nat(next), Bc):
  N.le_rw_l(1n+N, 1n+U32.to_nat(next), Bc, Equal.cong(Nat, Nat, z => 1n+z, N, U32.to_nat(next), Equal.sym(Nat, U32.to_nat(next), N, eN)), h)

# Allocation
# ----------

# the cell made of zeros
def In.z() -> Cr.Cir.Cell:
  Cr.Cir.Cell{0, 0, 0, 0, 0}

def In.room(rm: Maybe<&2, U32>, +r: Nat, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +next: U32, +F: U32, +K: U32, +pg: U32, +L: U32,
  +I: List<&2, Word(8n)>, rl: {True{} == Nat.is_lt(r, List.length(&2, U32, regs)) : Bool}, -X: Type, x: X, -Om: Type,
  zf: {rm == None{} : Maybe<&2, U32>} -> Om) ->
  In.Ok(Cr.Cir.exec.bump.of(r, next, In.S(regs, m, next, F, K, pg, L, I), rm),
    s => In.Is(s, List.set(&2, U32, regs, r, next), Cr.Cir.Cells.set(m, next, In.z()), U32.inc(next), F, K, L, I, X), Om):
  match rm:
    case None{}:
      zf({==})
    case Some{+p}:
      %rl : In.Ok(Cr.Cir.exec.set.of(Cr.Cir.regs.set.if(_, regs, r, next), Cr.Cir.State{regs, Cr.Cir.Cells.set(m, next, In.z()), U32.inc(next), F, K, p, L, I, [], 0}),
        s => In.Is(s, List.set(&2, U32, regs, r, next), Cr.Cir.Cells.set(m, next, In.z()), U32.inc(next), F, K, L, I, X), Om)
      ({==}, x)

def In.bump(b: Bool, +r: Nat, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +next: U32, +F: U32, +K: U32, +pg: U32, +L: U32,
  +I: List<&2, Word(8n)>, +eb: {U32.is_lt(next, 214748364) == b : Bool}, rl: {True{} == Nat.is_lt(r, List.length(&2, U32, regs)) : Bool},
  +Bc: Nat, +hb: N.Le(1n+U32.to_nat(next), Bc)) ->
  In.Ok(Cr.Cir.exec.bump.if(b, r, next, pg, L, In.S(regs, m, next, F, K, pg, L, I)),
    s => In.Is(s, List.set(&2, U32, regs, r, next), Cr.Cir.Cells.set(m, next, In.z()), U32.inc(next), F, K, L, I,
      {U32.is_lt(next, 214748364) == True{} : Bool}), In.oom(L, Bc)):
  match b:
    case False{}:
      In.oom.up(L, 1n+U32.to_nat(next), Bc, hb, In.oomb(next, L, eb))
    case True{}:
      In.room(Cr.Cir.room(U32.add(Cr.Cir.at(next), 19), pg, L), r, regs, m, next, F, K, pg, L, I, rl, {U32.is_lt(next, 214748364) == True{} : Bool}, eb,
        In.oom(L, Bc), e => In.oom.up(L, 1n+U32.to_nat(next), Bc, hb, In.oomf(next, pg, L, eb, e)))

# the code of a statement if c then t else e, its t
def In.yes(s: Cr.Cir.Stmt) -> Cr.Cir.Stmt:
  match s:
    case Cr.Cir.Stmt.if{_, t, _}:
      t
    case _:
      s

# a new cell, all zeros, when the pend list is empty
def In.alloc(+f: Nat, +r: Nat, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +next: U32, +F: U32, +K: U32, +pg: U32, +L: U32,
  +I: List<&2, Word(8n)>, p0: {Some{0} == List.get(&2, U32, regs, 3n) : Maybe<&2, U32>}, rl: {True{} == Nat.is_lt(r, List.length(&2, U32, regs)) : Bool}, +Bc: Nat, hb: N.Le(1n+U32.to_nat(next), Bc)) ->
  In.Ok(Cr.Cir.exec(1n+f, Mc.M.alloc(r), In.S(regs, m, next, F, K, pg, L, I)),
    s => In.Is(s, List.set(&2, U32, regs, r, next), Cr.Cir.Cells.set(m, next, In.z()), U32.inc(next), F, K, L, I,
      {U32.is_lt(next, 214748364) == True{} : Bool}), In.oom(L, Bc)):
  %p0 : In.Ok(Cr.Cir.exec.if(Cr.Cir.eval.op(Wa.Wasm.Op.ne{}, _, Some{0}), u => Cr.Cir.exec(1n+f, In.yes(Mc.M.alloc(r)), In.S(regs, m, next, F, K, pg, L, I)),
      u => Cr.Cir.exec(1n+f, Cr.Cir.Stmt.alloc{r}, In.S(regs, m, next, F, K, pg, L, I))),
    s => In.Is(s, List.set(&2, U32, regs, r, next), Cr.Cir.Cells.set(m, next, In.z()), U32.inc(next), F, K, L, I,
      {U32.is_lt(next, 214748364) == True{} : Bool}), In.oom(L, Bc))
  In.bump(U32.is_lt(next, 214748364), r, regs, m, next, F, K, pg, L, I, {==}, rl, Bc, hb)

# field k of the cell i, which register r holds, gets the value of v
def In.store(+f: Nat, +k: Nat, +r: Nat, +v: Cr.Cir.Expr, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +i: U32, +c: Cr.Cir.Cell, +x: U32, +nx: U32,
  +F: U32, +K: U32, +pg: U32, +L: U32, +I: List<&2, Word(8n)>,
  er: {Some{i} == List.get(&2, U32, regs, r) : Maybe<&2, U32>},
  ev: {Some{x} == Cr.Cir.eval(v, In.S(regs, Cr.Cir.Cells.set(m, i, c), nx, F, K, pg, L, I)) : Maybe<&2, U32>},
  ec: {True{} == Cr.Cir.is_cell(i, K, F, nx) : Bool}, -X: Type, -Om: Type, xx: X) ->
  In.Ok(Cr.Cir.exec(1n+f, Cr.Cir.Stmt.store{k, Cr.Cir.Expr.get{r}, v}, In.S(regs, Cr.Cir.Cells.set(m, i, c), nx, F, K, pg, L, I)),
    s => In.Is(s, regs, Cr.Cir.Cells.set(m, i, Cr.Cir.Cell.set(k, c, x)), nx, F, K, L, I, X), Om):
  +st = In.S(regs, Cr.Cir.Cells.set(m, i, c), nx, F, K, pg, L, I)
  %er : In.Ok(Cr.Cir.exec.store(k, _, Cr.Cir.eval(v, st), st), s => In.Is(s, regs, Cr.Cir.Cells.set(m, i, Cr.Cir.Cell.set(k, c, x)), nx, F, K, L, I, X), Om)
  %ev : In.Ok(Cr.Cir.exec.store(k, Some{i}, _, st), s => In.Is(s, regs, Cr.Cir.Cells.set(m, i, Cr.Cir.Cell.set(k, c, x)), nx, F, K, L, I, X), Om)
  %ec : In.Ok(Cr.Cir.exec.store.if(_, k, i, x, st), s => In.Is(s, regs, Cr.Cir.Cells.set(m, i, Cr.Cir.Cell.set(k, c, x)), nx, F, K, L, I, X), Om)
  %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, i, c), i), c, Cl.get_set(m, i, c)) :
    {In.S(regs, Cr.Cir.Cells.set(m, i, Cr.Cir.Cell.set(k, c, x)), nx, F, K, pg, L, I) == In.S(regs, Cr.Cir.Cells.set(Cr.Cir.Cells.set(m, i, c), i, Cr.Cir.Cell.set(k, _, x)), nx, F, K, pg, L, I) : Cr.Cir.State} & X
  %Cl.set_set(m, i, c, Cr.Cir.Cell.set(k, c, x)) :
    {In.S(regs, Cr.Cir.Cells.set(m, i, Cr.Cir.Cell.set(k, c, x)), nx, F, K, pg, L, I) == In.S(regs, _, nx, F, K, pg, L, I) : Cr.Cir.State} & X
  ({==}, xx)

# the facts of a run: the alloc's bound
def In.lt(+next: U32) -> Data:
  {U32.is_lt(next, 214748364) == True{} : Bool}

# the stores of M.make, after its alloc
def In.make.stores(+f: Nat, +r: Nat, +h: Cr.Cir.Expr, +a: Cr.Cir.Expr, +b: Cr.Cir.Expr, +c: Cr.Cir.Expr, +rg: List<&2, U32>, +m: Cr.Cir.Cells,
  +next: U32, +n1: U32, +F: U32, +K: U32, +pg1: U32, +L: U32, +I: List<&2, Word(8n)>, +vh: U32, +va: U32, +vb: U32, +vc: U32,
  -Om: Type, +er: {Some{next} == List.get(&2, U32, rg, r) : Maybe<&2, U32>},
  +ok: {True{} == Cr.Cir.is_cell(next, K, F, n1) : Bool}, +lt: In.lt(next),
  eh: @m2: Cr.Cir.Cells -> @pg2: U32 -> {Some{vh} == Cr.Cir.eval(h, In.S(rg, m2, n1, F, K, pg2, L, I)) : Maybe<&2, U32>},
  ea: @m2: Cr.Cir.Cells -> @pg2: U32 -> {Some{va} == Cr.Cir.eval(a, In.S(rg, m2, n1, F, K, pg2, L, I)) : Maybe<&2, U32>},
  eb: @m2: Cr.Cir.Cells -> @pg2: U32 -> {Some{vb} == Cr.Cir.eval(b, In.S(rg, m2, n1, F, K, pg2, L, I)) : Maybe<&2, U32>},
  ef: @m2: Cr.Cir.Cells -> @pg2: U32 -> {Some{vc} == Cr.Cir.eval(c, In.S(rg, m2, n1, F, K, pg2, L, I)) : Maybe<&2, U32>}) ->
  In.Ok(Cr.Cir.exec(1n+f, Mc.M.do([Mc.M.st(0n, Mc.M.g(r), h), Mc.M.st(1n, Mc.M.g(r), Mc.M.c(1)), Mc.M.st(2n, Mc.M.g(r), a), Mc.M.st(3n, Mc.M.g(r), b), Mc.M.st(4n, Mc.M.g(r), c)]),
      In.S(rg, Cr.Cir.Cells.set(m, next, In.z()), n1, F, K, pg1, L, I)),
    s => In.Is(s, rg, Cr.Cir.Cells.set(m, next, Cr.Cir.Cell{vh, 1, va, vb, vc}), n1, F, K, L, I, In.lt(next)), Om):
  In.seq(f, Mc.M.st(0n, Mc.M.g(r), h), Mc.M.do([Mc.M.st(1n, Mc.M.g(r), Mc.M.c(1)), Mc.M.st(2n, Mc.M.g(r), a), Mc.M.st(3n, Mc.M.g(r), b), Mc.M.st(4n, Mc.M.g(r), c)]),
      In.S(rg, Cr.Cir.Cells.set(m, next, In.z()), n1, F, K, pg1, L, I), rg, Cr.Cir.Cells.set(m, next, Cr.Cir.Cell{vh, 0, 0, 0, 0}), n1, F, K, L, I, In.lt(next),
      s => In.Is(s, rg, Cr.Cir.Cells.set(m, next, Cr.Cir.Cell{vh, 1, va, vb, vc}), n1, F, K, L, I, In.lt(next)),
      Om, In.store(f, 0n, r, h, rg, m, next, In.z(), vh, n1, F, K, pg1, L, I, er, eh(Cr.Cir.Cells.set(m, next, In.z()), pg1), ok, In.lt(next), Om, lt),
      +pg2 => +lt => In.seq(f, Mc.M.st(1n, Mc.M.g(r), Mc.M.c(1)), Mc.M.do([Mc.M.st(2n, Mc.M.g(r), a), Mc.M.st(3n, Mc.M.g(r), b), Mc.M.st(4n, Mc.M.g(r), c)]),
      In.S(rg, Cr.Cir.Cells.set(m, next, Cr.Cir.Cell{vh, 0, 0, 0, 0}), n1, F, K, pg2, L, I), rg, Cr.Cir.Cells.set(m, next, Cr.Cir.Cell{vh, 1, 0, 0, 0}), n1, F, K, L, I, In.lt(next),
      s => In.Is(s, rg, Cr.Cir.Cells.set(m, next, Cr.Cir.Cell{vh, 1, va, vb, vc}), n1, F, K, L, I, In.lt(next)),
      Om, In.store(f, 1n, r, Mc.M.c(1), rg, m, next, Cr.Cir.Cell{vh, 0, 0, 0, 0}, 1, n1, F, K, pg2, L, I, er, {==}, ok, In.lt(next), Om, lt),
      +pg3 => +lt => In.seq(f, Mc.M.st(2n, Mc.M.g(r), a), Mc.M.do([Mc.M.st(3n, Mc.M.g(r), b), Mc.M.st(4n, Mc.M.g(r), c)]),
      In.S(rg, Cr.Cir.Cells.set(m, next, Cr.Cir.Cell{vh, 1, 0, 0, 0}), n1, F, K, pg3, L, I), rg, Cr.Cir.Cells.set(m, next, Cr.Cir.Cell{vh, 1, va, 0, 0}), n1, F, K, L, I, In.lt(next),
      s => In.Is(s, rg, Cr.Cir.Cells.set(m, next, Cr.Cir.Cell{vh, 1, va, vb, vc}), n1, F, K, L, I, In.lt(next)),
      Om, In.store(f, 2n, r, a, rg, m, next, Cr.Cir.Cell{vh, 1, 0, 0, 0}, va, n1, F, K, pg3, L, I, er, ea(Cr.Cir.Cells.set(m, next, Cr.Cir.Cell{vh, 1, 0, 0, 0}), pg3), ok, In.lt(next), Om, lt),
      +pg4 => +lt => In.seq(f, Mc.M.st(3n, Mc.M.g(r), b), Mc.M.do([Mc.M.st(4n, Mc.M.g(r), c)]),
      In.S(rg, Cr.Cir.Cells.set(m, next, Cr.Cir.Cell{vh, 1, va, 0, 0}), n1, F, K, pg4, L, I), rg, Cr.Cir.Cells.set(m, next, Cr.Cir.Cell{vh, 1, va, vb, 0}), n1, F, K, L, I, In.lt(next),
      s => In.Is(s, rg, Cr.Cir.Cells.set(m, next, Cr.Cir.Cell{vh, 1, va, vb, vc}), n1, F, K, L, I, In.lt(next)),
      Om, In.store(f, 3n, r, b, rg, m, next, Cr.Cir.Cell{vh, 1, va, 0, 0}, vb, n1, F, K, pg4, L, I, er, eb(Cr.Cir.Cells.set(m, next, Cr.Cir.Cell{vh, 1, va, 0, 0}), pg4), ok, In.lt(next), Om, lt),
      +pg5 => +lt => In.seq(f, Mc.M.st(4n, Mc.M.g(r), c), Mc.M.do([]),
      In.S(rg, Cr.Cir.Cells.set(m, next, Cr.Cir.Cell{vh, 1, va, vb, 0}), n1, F, K, pg5, L, I), rg, Cr.Cir.Cells.set(m, next, Cr.Cir.Cell{vh, 1, va, vb, vc}), n1, F, K, L, I, In.lt(next),
      s => In.Is(s, rg, Cr.Cir.Cells.set(m, next, Cr.Cir.Cell{vh, 1, va, vb, vc}), n1, F, K, L, I, In.lt(next)),
      Om, In.store(f, 4n, r, c, rg, m, next, Cr.Cir.Cell{vh, 1, va, vb, 0}, vc, n1, F, K, pg5, L, I, er, ef(Cr.Cir.Cells.set(m, next, Cr.Cir.Cell{vh, 1, va, vb, 0}), pg5), ok, In.lt(next), Om, lt),
      +pg6 => +lt => ({==}, lt))))))

# M.make: register r gets a new cell, with the header h and the fields a, b, c
def In.make(+f: Nat, +r: Nat, +h: Cr.Cir.Expr, +a: Cr.Cir.Expr, +b: Cr.Cir.Expr, +c: Cr.Cir.Expr, +regs: List<&2, U32>, +m: Cr.Cir.Cells,
  +next: U32, +F: U32, +K: U32, +pg: U32, +L: U32, +I: List<&2, Word(8n)>, +vh: U32, +va: U32, +vb: U32, +vc: U32,
  +Bc: Nat, hb: N.Le(1n+U32.to_nat(next), Bc), p0: {Some{0} == List.get(&2, U32, regs, 3n) : Maybe<&2, U32>}, rl: {True{} == Nat.is_lt(r, List.length(&2, U32, regs)) : Bool},
  +er: {Some{next} == List.get(&2, U32, List.set(&2, U32, regs, r, next), r) : Maybe<&2, U32>},
  ec: In.lt(next) -> {True{} == Cr.Cir.is_cell(next, K, F, U32.inc(next)) : Bool},
  eh: @m2: Cr.Cir.Cells -> @pg2: U32 -> {Some{vh} == Cr.Cir.eval(h, In.S(List.set(&2, U32, regs, r, next), m2, U32.inc(next), F, K, pg2, L, I)) : Maybe<&2, U32>},
  ea: @m2: Cr.Cir.Cells -> @pg2: U32 -> {Some{va} == Cr.Cir.eval(a, In.S(List.set(&2, U32, regs, r, next), m2, U32.inc(next), F, K, pg2, L, I)) : Maybe<&2, U32>},
  eb: @m2: Cr.Cir.Cells -> @pg2: U32 -> {Some{vb} == Cr.Cir.eval(b, In.S(List.set(&2, U32, regs, r, next), m2, U32.inc(next), F, K, pg2, L, I)) : Maybe<&2, U32>},
  ef: @m2: Cr.Cir.Cells -> @pg2: U32 -> {Some{vc} == Cr.Cir.eval(c, In.S(List.set(&2, U32, regs, r, next), m2, U32.inc(next), F, K, pg2, L, I)) : Maybe<&2, U32>}) ->
  In.Ok(Cr.Cir.exec(1n+f, Mc.M.make(r, h, a, b, c), In.S(regs, m, next, F, K, pg, L, I)),
    s => In.Is(s, List.set(&2, U32, regs, r, next), Cr.Cir.Cells.set(m, next, Cr.Cir.Cell{vh, 1, va, vb, vc}), U32.inc(next), F, K, L, I, In.lt(next)), In.oom(L, Bc)):
  +rg = List.set(&2, U32, regs, r, next)
  +n1 = U32.inc(next)
  In.seq(f, Mc.M.alloc(r), Mc.M.do([Mc.M.st(0n, Mc.M.g(r), h), Mc.M.st(1n, Mc.M.g(r), Mc.M.c(1)), Mc.M.st(2n, Mc.M.g(r), a), Mc.M.st(3n, Mc.M.g(r), b), Mc.M.st(4n, Mc.M.g(r), c)]),
    In.S(regs, m, next, F, K, pg, L, I), rg, Cr.Cir.Cells.set(m, next, In.z()), n1, F, K, L, I, In.lt(next),
    s => In.Is(s, rg, Cr.Cir.Cells.set(m, next, Cr.Cir.Cell{vh, 1, va, vb, vc}), n1, F, K, L, I, In.lt(next)),
    In.oom(L, Bc), In.alloc(f, r, regs, m, next, F, K, pg, L, I, p0, rl, Bc, hb),
    ++pg1 => +lt => In.make.stores(f, r, h, a, b, c, rg, m, next, n1, F, K, pg1, L, I, vh, va, vb, vc, In.oom(L, Bc), er, ec(lt), lt, eh, ea, eb, ef))

# Booleans
# --------

def Bo.ft(-G: Type, h: {True{} == False{} : Bool}) -> G:
  Empty.absurd(G, N.true_ne_false(h))

def Bo.and_l(a: Bool, -b: Bool, h: {True{} == Bool.and(a, b) : Bool}) -> {True{} == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Bo.ft({True{} == False{} : Bool}, h)

def Bo.and_r(a: Bool, b: Bool, h: {True{} == Bool.and(a, b) : Bool}) -> {True{} == b : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      Bo.ft({True{} == b : Bool}, h)

def Bo.and_i(-a: Bool, -b: Bool, ha: {True{} == a : Bool}, hb: {True{} == b : Bool}) -> {True{} == Bool.and(a, b) : Bool}:
  %ha : {True{} == Bool.and(_, b) : Bool}
  %hb : {True{} == Bool.and(True{}, _) : Bool}
  {==}

# The cells a term reads
# ----------------------

# the cell j may be read: one of the image's first 16, or one the machine took
# (from F, before N)
def In.rd(+j: U32, +F: U32, +N: Nat) -> Bool:
  Bool.or(Nat.is_lt(U32.to_nat(j), 16n), Bool.and(Nat.is_le(U32.to_nat(F), U32.to_nat(j)), Nat.is_lt(U32.to_nat(j), N)))

# the parts that a cell of the tag tag reads: only Ref, App, Tup and Lab
def In.rds.cell(tag: Nat, r2: Unit -> Bool, r3: Unit -> Bool) -> Bool:
  match tag:
    case 1n:
      True{}
    case 8n:
      Bool.and(r2(Unit{}), r3(Unit{}))
    case 10n:
      Bool.and(r2(Unit{}), r3(Unit{}))
    case 13n:
      True{}
    case _:
      False{}

# T.tm.of(fuel, m, ks, img, c) reads only cells that may be read, of Ref, App,
# Tup and Lab, and ends before its fuel
def In.rds(fuel: Nat, +m: Cr.Cir.Cells, +F: U32, +N: Nat, +c: U32) -> Bool:
  match fuel:
    case 0n:
      False{}
    case 1n+(+f):
      +cell = Cr.Cir.Cells.get(m, c)
      Bool.and(In.rd(c, F, N), In.rds.cell(U32.to_nat(U32.and(Cr.Cir.Cell.get(0n, cell), 63)),
        u => In.rds(f, m, F, N, Cr.Cir.Cell.get(2n, cell)), u => In.rds(f, m, F, N, Cr.Cir.Cell.get(3n, cell))))

# a pair of two Data types, itself Data
def In.P(-A: Data, -B: Data) -> Data:
  Sigma<&2, &2, A, _ => B>

def In.fr.goal(tag: Nat, +q: Bk.Quan, +c: U32, +f2: U32, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  a2: Maybe<&2, Bk.Term>, a3: Maybe<&2, Bk.Term>, a4: Maybe<&2, Bk.Term>, b2: Maybe<&2, Bk.Term>, b3: Maybe<&2, Bk.Term>, b4: Maybe<&2, Bk.Term>,
  s2: Bool, s3: Bool) -> Data:
  In.P({T.tm.cell(tag, q, c, f2, ks, img, u => a2, u => a3, u => a4) == T.tm.cell(tag, q, c, f2, ks, img, u => b2, u => b3, u => b4) : Maybe<&2, Bk.Term>},
    {True{} == In.rds.cell(tag, u => s2, u => s3) : Bool})

# a cell of the tag, whose parts that it reads give the same terms, gives the
# same term
def In.fr.cell(tag: Nat, +q: Bk.Quan, +c: U32, +f2: U32, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +a2: Maybe<&2, Bk.Term>, +a3: Maybe<&2, Bk.Term>, +a4: Maybe<&2, Bk.Term>, +b2: Maybe<&2, Bk.Term>, +b3: Maybe<&2, Bk.Term>, +b4: Maybe<&2, Bk.Term>,
  +r2: Bool, +r3: Bool, +s2: Bool, +s3: Bool, +h: {True{} == In.rds.cell(tag, u => r2, u => r3) : Bool},
  e2: {True{} == r2 : Bool} -> {a2 == b2 : Maybe<&2, Bk.Term>}, k2: {True{} == r2 : Bool} -> {True{} == s2 : Bool},
  e3: {True{} == r3 : Bool} -> {a3 == b3 : Maybe<&2, Bk.Term>}, k3: {True{} == r3 : Bool} -> {True{} == s3 : Bool}) ->
  In.fr.goal(tag, q, c, f2, ks, img, a2, a3, a4, b2, b3, b4, s2, s3):
  match tag:
    case 0n:
      Bo.ft(In.fr.goal(0n, q, c, f2, ks, img, a2, a3, a4, b2, b3, b4, s2, s3), h)
    case 1n:
      ({==}, {==})
    case 2n:
      Bo.ft(In.fr.goal(2n, q, c, f2, ks, img, a2, a3, a4, b2, b3, b4, s2, s3), h)
    case 3n:
      Bo.ft(In.fr.goal(3n, q, c, f2, ks, img, a2, a3, a4, b2, b3, b4, s2, s3), h)
    case 4n:
      Bo.ft(In.fr.goal(4n, q, c, f2, ks, img, a2, a3, a4, b2, b3, b4, s2, s3), h)
    case 5n:
      Bo.ft(In.fr.goal(5n, q, c, f2, ks, img, a2, a3, a4, b2, b3, b4, s2, s3), h)
    case 6n:
      Bo.ft(In.fr.goal(6n, q, c, f2, ks, img, a2, a3, a4, b2, b3, b4, s2, s3), h)
    case 7n:
      Bo.ft(In.fr.goal(7n, q, c, f2, ks, img, a2, a3, a4, b2, b3, b4, s2, s3), h)
    case 8n:
      +ra = Bo.and_l(r2, r3, h)
      +rb = Bo.and_r(r2, r3, h)
      %e2(ra) : In.fr.goal(8n, q, c, f2, ks, img, a2, a3, a4, _, b3, b4, s2, s3)
      %e3(rb) : In.fr.goal(8n, q, c, f2, ks, img, a2, a3, a4, a2, _, b4, s2, s3)
      ({==}, Bo.and_i(s2, s3, k2(ra), k3(rb)))
    case 9n:
      Bo.ft(In.fr.goal(9n, q, c, f2, ks, img, a2, a3, a4, b2, b3, b4, s2, s3), h)
    case 10n:
      +ra = Bo.and_l(r2, r3, h)
      +rb = Bo.and_r(r2, r3, h)
      %e2(ra) : In.fr.goal(10n, q, c, f2, ks, img, a2, a3, a4, _, b3, b4, s2, s3)
      %e3(rb) : In.fr.goal(10n, q, c, f2, ks, img, a2, a3, a4, a2, _, b4, s2, s3)
      ({==}, Bo.and_i(s2, s3, k2(ra), k3(rb)))
    case 11n:
      Bo.ft(In.fr.goal(11n, q, c, f2, ks, img, a2, a3, a4, b2, b3, b4, s2, s3), h)
    case 12n:
      Bo.ft(In.fr.goal(12n, q, c, f2, ks, img, a2, a3, a4, b2, b3, b4, s2, s3), h)
    case 13n:
      ({==}, {==})
    case 14n+p:
      Bo.ft(In.fr.goal(14n+p, q, c, f2, ks, img, a2, a3, a4, b2, b3, b4, s2, s3), h)

def In.p1(-A: Data, -B: Data, p: In.P(A, B)) -> A:
  (a, b) = p
  a

def In.p2(-A: Data, -B: Data, p: In.P(A, B)) -> B:
  (a, b) = p
  b

# fr.cell's claim, with the check of the cell itself in front
def In.fr.fin(tag: Nat, +q: Bk.Quan, +c: U32, +f2: U32, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +a2: Maybe<&2, Bk.Term>, +a3: Maybe<&2, Bk.Term>, +a4: Maybe<&2, Bk.Term>, +b2: Maybe<&2, Bk.Term>, +b3: Maybe<&2, Bk.Term>, +b4: Maybe<&2, Bk.Term>,
  +s2: Bool, +s3: Bool, +rc: Bool, hc: {True{} == rc : Bool}, r: In.fr.goal(tag, q, c, f2, ks, img, a2, a3, a4, b2, b3, b4, s2, s3)) ->
  In.P({T.tm.cell(tag, q, c, f2, ks, img, u => a2, u => a3, u => a4) == T.tm.cell(tag, q, c, f2, ks, img, u => b2, u => b3, u => b4) : Maybe<&2, Bk.Term>},
    {True{} == Bool.and(rc, In.rds.cell(tag, u => s2, u => s3)) : Bool}):
  (e, k) = r
  (e, Bo.and_i(rc, In.rds.cell(tag, u => s2, u => s3), hc, k))

# a cell that may be read is not one that may not
def In.ne(+c: U32, +i: U32, +F: U32, +N: Nat, hc: {True{} == In.rd(c, F, N) : Bool}, hi: {False{} == In.rd(i, F, N) : Bool},
  e: {c == i : U32}) -> Empty:
  N.true_ne_false(Equal.trans(Bool, True{}, In.rd(c, F, N), False{}, hc,
    Equal.trans(Bool, In.rd(c, F, N), In.rd(i, F, N), False{}, Equal.cong(U32, Bool, j => In.rd(j, F, N), c, i, e),
      Equal.sym(Bool, False{}, In.rd(i, F, N), hi))))

# In.fr's claim, once its fuel's first unit is spent, with the cell cl at c in
# the cells ms
def In.fr.after(+p: Nat, +m: Cr.Cir.Cells, +ms: Cr.Cir.Cells, +F: U32, +N: Nat, +c: U32, +cl: Cr.Cir.Cell, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>) -> Data:
  +cm = Cr.Cir.Cells.get(m, c)
  In.P({T.tm.cell(U32.to_nat(U32.and(Cr.Cir.Cell.get(0n, cm), 63)), T.tm.quan(U32.and(U32.shrn(Cr.Cir.Cell.get(0n, cm), 6n), 3)), c,
      Cr.Cir.Cell.get(2n, cm), ks, img, u => T.tm.of(p, m, ks, img, Cr.Cir.Cell.get(2n, cm)), u => T.tm.of(p, m, ks, img, Cr.Cir.Cell.get(3n, cm)),
      u => T.tm.of(p, m, ks, img, Cr.Cir.Cell.get(4n, cm))) ==
    T.tm.cell(U32.to_nat(U32.and(Cr.Cir.Cell.get(0n, cl), 63)), T.tm.quan(U32.and(U32.shrn(Cr.Cir.Cell.get(0n, cl), 6n), 3)), c,
      Cr.Cir.Cell.get(2n, cl), ks, img, u => T.tm.of(p, ms, ks, img, Cr.Cir.Cell.get(2n, cl)), u => T.tm.of(p, ms, ks, img, Cr.Cir.Cell.get(3n, cl)),
      u => T.tm.of(p, ms, ks, img, Cr.Cir.Cell.get(4n, cl))) : Maybe<&2, Bk.Term>},
    {True{} == Bool.and(In.rd(c, F, N), In.rds.cell(U32.to_nat(U32.and(Cr.Cir.Cell.get(0n, cl), 63)),
      u => In.rds(p, ms, F, N, Cr.Cir.Cell.get(2n, cl)), u => In.rds(p, ms, F, N, Cr.Cir.Cell.get(3n, cl)))) : Bool})

def In.fr.res(f: Nat, +m: Cr.Cir.Cells, +F: U32, +N: Nat, +c: U32, +i: U32, +x: Cr.Cir.Cell, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>) -> Data:
  In.P({T.tm.of(f, m, ks, img, c) == T.tm.of(f, Cr.Cir.Cells.set(m, i, x), ks, img, c) : Maybe<&2, Bk.Term>},
    {True{} == In.rds(f, Cr.Cir.Cells.set(m, i, x), F, N, c) : Bool})

# a term that reads only cells that may be read keeps its term, and still
# reads only those, when a cell that may not be read is set
def In.fr(f: Nat, +m: Cr.Cir.Cells, +F: U32, +N: Nat, +c: U32, +i: U32, +x: Cr.Cir.Cell, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +h: {True{} == In.rds(f, m, F, N, c) : Bool}, +hi: {False{} == In.rd(i, F, N) : Bool}) -> In.fr.res(f, m, F, N, c, i, x, ks, img):
  match f:
    case 0n:
      Bo.ft(In.fr.res(0n, m, F, N, c, i, x, ks, img), h)
    case 1n+(+p):
      +ms = Cr.Cir.Cells.set(m, i, x)
      +cl = Cr.Cir.Cells.get(m, c)
      +tag = U32.to_nat(U32.and(Cr.Cir.Cell.get(0n, cl), 63))
      +f2 = Cr.Cir.Cell.get(2n, cl)
      +f3 = Cr.Cir.Cell.get(3n, cl)
      +f4 = Cr.Cir.Cell.get(4n, cl)
      +hc = Bo.and_l(In.rd(c, F, N), In.rds.cell(tag, u => In.rds(p, m, F, N, f2), u => In.rds(p, m, F, N, f3)), h)
      +hr = Bo.and_r(In.rd(c, F, N), In.rds.cell(tag, u => In.rds(p, m, F, N, f2), u => In.rds(p, m, F, N, f3)), h)
      %Cl.get_other(m, c, i, x, e => In.ne(c, i, F, N, hc, hi, e)) : In.fr.after(p, m, ms, F, N, c, _, ks, img)
      +r = In.fr.cell(tag, T.tm.quan(U32.and(U32.shrn(Cr.Cir.Cell.get(0n, cl), 6n), 3)), c, f2, ks, img,
        T.tm.of(p, m, ks, img, f2), T.tm.of(p, m, ks, img, f3), T.tm.of(p, m, ks, img, f4),
        T.tm.of(p, ms, ks, img, f2), T.tm.of(p, ms, ks, img, f3), T.tm.of(p, ms, ks, img, f4),
        In.rds(p, m, F, N, f2), In.rds(p, m, F, N, f3), In.rds(p, ms, F, N, f2), In.rds(p, ms, F, N, f3), hr,
        k => In.p1({T.tm.of(p, m, ks, img, f2) == T.tm.of(p, ms, ks, img, f2) : Maybe<&2, Bk.Term>}, {True{} == In.rds(p, ms, F, N, f2) : Bool},
          In.fr(p, m, F, N, f2, i, x, ks, img, k, hi)),
        k => In.p2({T.tm.of(p, m, ks, img, f2) == T.tm.of(p, ms, ks, img, f2) : Maybe<&2, Bk.Term>}, {True{} == In.rds(p, ms, F, N, f2) : Bool},
          In.fr(p, m, F, N, f2, i, x, ks, img, k, hi)),
        k => In.p1({T.tm.of(p, m, ks, img, f3) == T.tm.of(p, ms, ks, img, f3) : Maybe<&2, Bk.Term>}, {True{} == In.rds(p, ms, F, N, f3) : Bool},
          In.fr(p, m, F, N, f3, i, x, ks, img, k, hi)),
        k => In.p2({T.tm.of(p, m, ks, img, f3) == T.tm.of(p, ms, ks, img, f3) : Maybe<&2, Bk.Term>}, {True{} == In.rds(p, ms, F, N, f3) : Bool},
          In.fr(p, m, F, N, f3, i, x, ks, img, k, hi)))
      In.fr.fin(tag, T.tm.quan(U32.and(U32.shrn(Cr.Cir.Cell.get(0n, cl), 6n), 3)), c, f2, ks, img,
        T.tm.of(p, m, ks, img, f2), T.tm.of(p, m, ks, img, f3), T.tm.of(p, m, ks, img, f4),
        T.tm.of(p, ms, ks, img, f2), T.tm.of(p, ms, ks, img, f3), T.tm.of(p, ms, ks, img, f4),
        In.rds(p, ms, F, N, f2), In.rds(p, ms, F, N, f3), In.rd(c, F, N), hc, r)

# a term that reads only cells that may be read, with fuel to spare
def In.mono(f: Nat, +m: Cr.Cir.Cells, +F: U32, +N: Nat, +c: U32, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +h: {True{} == In.rds(f, m, F, N, c) : Bool}) ->
  In.P({T.tm.of(f, m, ks, img, c) == T.tm.of(1n+f, m, ks, img, c) : Maybe<&2, Bk.Term>}, {True{} == In.rds(1n+f, m, F, N, c) : Bool}):
  match f:
    case 0n:
      Bo.ft(In.P({T.tm.of(0n, m, ks, img, c) == T.tm.of(1n, m, ks, img, c) : Maybe<&2, Bk.Term>}, {True{} == In.rds(1n, m, F, N, c) : Bool}), h)
    case 1n+(+p):
      +cl = Cr.Cir.Cells.get(m, c)
      +tag = U32.to_nat(U32.and(Cr.Cir.Cell.get(0n, cl), 63))
      +f2 = Cr.Cir.Cell.get(2n, cl)
      +f3 = Cr.Cir.Cell.get(3n, cl)
      +f4 = Cr.Cir.Cell.get(4n, cl)
      +hc = Bo.and_l(In.rd(c, F, N), In.rds.cell(tag, u => In.rds(p, m, F, N, f2), u => In.rds(p, m, F, N, f3)), h)
      +hr = Bo.and_r(In.rd(c, F, N), In.rds.cell(tag, u => In.rds(p, m, F, N, f2), u => In.rds(p, m, F, N, f3)), h)
      +r = In.fr.cell(tag, T.tm.quan(U32.and(U32.shrn(Cr.Cir.Cell.get(0n, cl), 6n), 3)), c, f2, ks, img,
        T.tm.of(p, m, ks, img, f2), T.tm.of(p, m, ks, img, f3), T.tm.of(p, m, ks, img, f4),
        T.tm.of(1n+p, m, ks, img, f2), T.tm.of(1n+p, m, ks, img, f3), T.tm.of(1n+p, m, ks, img, f4),
        In.rds(p, m, F, N, f2), In.rds(p, m, F, N, f3), In.rds(1n+p, m, F, N, f2), In.rds(1n+p, m, F, N, f3), hr,
        k => In.p1({T.tm.of(p, m, ks, img, f2) == T.tm.of(1n+p, m, ks, img, f2) : Maybe<&2, Bk.Term>}, {True{} == In.rds(1n+p, m, F, N, f2) : Bool},
          In.mono(p, m, F, N, f2, ks, img, k)),
        k => In.p2({T.tm.of(p, m, ks, img, f2) == T.tm.of(1n+p, m, ks, img, f2) : Maybe<&2, Bk.Term>}, {True{} == In.rds(1n+p, m, F, N, f2) : Bool},
          In.mono(p, m, F, N, f2, ks, img, k)),
        k => In.p1({T.tm.of(p, m, ks, img, f3) == T.tm.of(1n+p, m, ks, img, f3) : Maybe<&2, Bk.Term>}, {True{} == In.rds(1n+p, m, F, N, f3) : Bool},
          In.mono(p, m, F, N, f3, ks, img, k)),
        k => In.p2({T.tm.of(p, m, ks, img, f3) == T.tm.of(1n+p, m, ks, img, f3) : Maybe<&2, Bk.Term>}, {True{} == In.rds(1n+p, m, F, N, f3) : Bool},
          In.mono(p, m, F, N, f3, ks, img, k)))
      In.fr.fin(tag, T.tm.quan(U32.and(U32.shrn(Cr.Cir.Cell.get(0n, cl), 6n), 3)), c, f2, ks, img,
        T.tm.of(p, m, ks, img, f2), T.tm.of(p, m, ks, img, f3), T.tm.of(p, m, ks, img, f4),
        T.tm.of(1n+p, m, ks, img, f2), T.tm.of(1n+p, m, ks, img, f3), T.tm.of(1n+p, m, ks, img, f4),
        In.rds(1n+p, m, F, N, f2), In.rds(1n+p, m, F, N, f3), In.rd(c, F, N), hc, r)

# Nat: a < n gives a < 1 + n
def Na.lt_up(a: Nat, n: Nat, h: {True{} == Nat.is_lt(a, n) : Bool}) -> {True{} == Nat.is_lt(a, 1n+n) : Bool}:
  match a n:
    case 0n _:
      {==}
    case 1n+x 0n:
      Bo.ft({True{} == Nat.is_lt(1n+x, 1n) : Bool}, h)
    case 1n+x 1n+y:
      Na.lt_up(x, y, h)

def Bo.or_mono(a: Bool, -b: Bool, -c: Bool, h: {True{} == Bool.or(a, b) : Bool}, k: {True{} == b : Bool} -> {True{} == c : Bool}) ->
  {True{} == Bool.or(a, c) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      k(h)

def Bo.and_mono(a: Bool, -b: Bool, -c: Bool, h: {True{} == Bool.and(a, b) : Bool}, k: {True{} == b : Bool} -> {True{} == c : Bool}) ->
  {True{} == Bool.and(a, c) : Bool}:
  match a:
    case True{}:
      k(h)
    case False{}:
      h

# a cell that may be read still may, once one more is taken
def In.rd_up(+j: U32, +F: U32, +N: Nat, h: {True{} == In.rd(j, F, N) : Bool}) -> {True{} == In.rd(j, F, 1n+N) : Bool}:
  Bo.or_mono(Nat.is_lt(U32.to_nat(j), 16n), Bool.and(Nat.is_le(U32.to_nat(F), U32.to_nat(j)), Nat.is_lt(U32.to_nat(j), N)),
    Bool.and(Nat.is_le(U32.to_nat(F), U32.to_nat(j)), Nat.is_lt(U32.to_nat(j), 1n+N)), h,
    k => Bo.and_mono(Nat.is_le(U32.to_nat(F), U32.to_nat(j)), Nat.is_lt(U32.to_nat(j), N), Nat.is_lt(U32.to_nat(j), 1n+N), k,
      l => Na.lt_up(U32.to_nat(j), N, l)))

# a term that reads only cells that may be read still does, once one more
# cell is taken
def In.up(f: Nat, +m: Cr.Cir.Cells, +F: U32, +N: Nat, +c: U32, +h: {True{} == In.rds(f, m, F, N, c) : Bool}) ->
  {True{} == In.rds(f, m, F, 1n+N, c) : Bool}:
  match f:
    case 0n:
      h
    case 1n+(+p):
      +cl = Cr.Cir.Cells.get(m, c)
      +tag = U32.to_nat(U32.and(Cr.Cir.Cell.get(0n, cl), 63))
      +f2 = Cr.Cir.Cell.get(2n, cl)
      +f3 = Cr.Cir.Cell.get(3n, cl)
      +hc = Bo.and_l(In.rd(c, F, N), In.rds.cell(tag, u => In.rds(p, m, F, N, f2), u => In.rds(p, m, F, N, f3)), h)
      +hr = Bo.and_r(In.rd(c, F, N), In.rds.cell(tag, u => In.rds(p, m, F, N, f2), u => In.rds(p, m, F, N, f3)), h)
      +r = In.fr.cell(tag, Bk.Quan.Q0{}, c, f2, [], [], None{}, None{}, None{}, None{}, None{}, None{},
        In.rds(p, m, F, N, f2), In.rds(p, m, F, N, f3), In.rds(p, m, F, 1n+N, f2), In.rds(p, m, F, 1n+N, f3), hr,
        k => {==}, k => In.up(p, m, F, N, f2, k), k => {==}, k => In.up(p, m, F, N, f3, k))
      Bo.and_i(In.rd(c, F, 1n+N), In.rds.cell(tag, u => In.rds(p, m, F, 1n+N, f2), u => In.rds(p, m, F, 1n+N, f3)),
        In.rd_up(c, F, N, hc),
        In.p2({T.tm.cell(tag, Bk.Quan.Q0{}, c, f2, [], [], u => None{}, u => None{}, u => None{}) ==
          T.tm.cell(tag, Bk.Quan.Q0{}, c, f2, [], [], u => None{}, u => None{}, u => None{}) : Maybe<&2, Bk.Term>},
          {True{} == In.rds.cell(tag, u => In.rds(p, m, F, 1n+N, f2), u => In.rds(p, m, F, 1n+N, f3)) : Bool}, r))

# The nodes of a term
# --------------------

# every node of t at the cell r, as Node walks them, is a cell that may be
# read, within the fuel f (as In.rds): no set of a cell that may not be read
# changes the nodes (In.nfr)
def In.nrd(f: Nat, t: Bk.Term, +m: Cr.Cir.Cells, +r: U32, +F: U32, +N: Nat) -> Bool:
  match f:
    case 0n:
      False{}
    case 1n+(+p):
      match t:
        case Bk.Term.Var{_}:
          In.rd(r, F, N)
        case Bk.Term.Ref{_}:
          In.rd(r, F, N)
        case Bk.Term.Ann{y, z}:
          Bool.and(In.rd(r, F, N), Bool.and(In.nrd(p, y, m, D.Fd(2n, m, r), F, N), In.nrd(p, z, m, D.Fd(3n, m, r), F, N)))
        case Bk.Term.Let{_, v, g}:
          Bool.and(In.rd(r, F, N), Bool.and(In.nrd(p, v, m, D.Fd(2n, m, r), F, N), In.nrd(p, g, m, D.Fd(3n, m, r), F, N)))
        case Bk.Term.Typ{y}:
          Bool.and(In.rd(r, F, N), In.nrd(p, y, m, D.Fd(2n, m, r), F, N))
        case Bk.Term.Min{a, b}:
          Bool.and(In.rd(r, F, N), Bool.and(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), In.nrd(p, b, m, D.Fd(3n, m, r), F, N)))
        case Bk.Term.All{_, a, b}:
          Bool.and(In.rd(r, F, N), Bool.and(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), In.nrd(p, b, m, D.Fd(3n, m, r), F, N)))
        case Bk.Term.Lam{_, g}:
          Bool.and(In.rd(r, F, N), In.nrd(p, g, m, D.Fd(2n, m, r), F, N))
        case Bk.Term.App{_, g, y}:
          Bool.and(In.rd(r, F, N), Bool.and(In.nrd(p, g, m, D.Fd(2n, m, r), F, N), In.nrd(p, y, m, D.Fd(3n, m, r), F, N)))
        case Bk.Term.Sig{_, a, b}:
          Bool.and(In.rd(r, F, N), Bool.and(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), In.nrd(p, b, m, D.Fd(3n, m, r), F, N)))
        case Bk.Term.Tup{_, a, b}:
          Bool.and(In.rd(r, F, N), Bool.and(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), In.nrd(p, b, m, D.Fd(3n, m, r), F, N)))
        case Bk.Term.Prj{h}:
          Bool.and(In.rd(r, F, N), In.nrd(p, h, m, D.Fd(2n, m, r), F, N))
        case Bk.Term.Enu{_}:
          In.rd(r, F, N)
        case Bk.Term.Lab{_}:
          In.rd(r, F, N)
        case Bk.Term.Mat{_, h, o}:
          Bool.and(In.rd(r, F, N), Bool.and(In.nrd(p, h, m, D.Fd(3n, m, r), F, N), In.nrd(p, o, m, D.Fd(4n, m, r), F, N)))
        case Bk.Term.Efq{}:
          In.rd(r, F, N)
        case Bk.Term.Eql{a, b, y}:
          Bool.and(In.rd(r, F, N), Bool.and(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), Bool.and(In.nrd(p, b, m, D.Fd(3n, m, r), F, N), In.nrd(p, y, m, D.Fd(4n, m, r), F, N))))
        case Bk.Term.Rfl{}:
          In.rd(r, F, N)
        case Bk.Term.Rwt{w, y, g}:
          Bool.and(In.rd(r, F, N), Bool.and(In.nrd(p, w, m, D.Fd(2n, m, r), F, N), Bool.and(In.nrd(p, y, m, D.Fd(3n, m, r), F, N), In.nrd(p, g, m, D.Fd(4n, m, r), F, N))))

# a field of a cell other than i, once i is set
def In.fd.fr(+k: Nat, +m: Cr.Cir.Cells, +r: U32, +i: U32, +x: Cr.Cir.Cell, ne: {r == i : U32} -> Empty) ->
  {D.Fd(k, m, r) == D.Fd(k, Cr.Cir.Cells.set(m, i, x), r) : U32}:
  Equal.cong(Cr.Cir.Cell, U32, y => Cr.Cir.Cell.get(k, y), Cr.Cir.Cells.get(m, r), Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, i, x), r), Cl.get_other(m, r, i, x, ne))

# the nodes of t at r, and Node, are the same once a cell that may not be
# read is set
def In.nfr(f: Nat, t: Bk.Term, +m: Cr.Cir.Cells, +r: U32, +c: U32, +i: U32, +x: Cr.Cir.Cell, +F: U32, +N: Nat,
  +hn: {True{} == In.nrd(f, t, m, r, F, N) : Bool}, +hi: {False{} == In.rd(i, F, N) : Bool}) ->
  In.P({True{} == In.nrd(f, t, Cr.Cir.Cells.set(m, i, x), r, F, N) : Bool}, {D.Node(t, m, r, c) == D.Node(t, Cr.Cir.Cells.set(m, i, x), r, c) : Bool}):
  match f:
    case 0n:
      Bo.ft(In.P({True{} == In.nrd(0n, t, Cr.Cir.Cells.set(m, i, x), r, F, N) : Bool}, {D.Node(t, m, r, c) == D.Node(t, Cr.Cir.Cells.set(m, i, x), r, c) : Bool}), hn)
    case 1n+(+p):
      match t:
        case Bk.Term.Var{_}:
          (hn, {==})
        case Bk.Term.Ref{_}:
          (hn, {==})
        case Bk.Term.Ann{+y, +z}:
          +hr = Bo.and_l(In.rd(r, F, N), Bool.and(In.nrd(p, y, m, D.Fd(2n, m, r), F, N), In.nrd(p, z, m, D.Fd(3n, m, r), F, N)), hn)
          +hp = Bo.and_r(In.rd(r, F, N), Bool.and(In.nrd(p, y, m, D.Fd(2n, m, r), F, N), In.nrd(p, z, m, D.Fd(3n, m, r), F, N)), hn)
          +hy = Bo.and_l(In.nrd(p, y, m, D.Fd(2n, m, r), F, N), In.nrd(p, z, m, D.Fd(3n, m, r), F, N), hp)
          +ry = Bo.and_r(In.nrd(p, y, m, D.Fd(2n, m, r), F, N), In.nrd(p, z, m, D.Fd(3n, m, r), F, N), hp)
          +qy = In.nfr(p, y, m, D.Fd(2n, m, r), c, i, x, F, N, hy, hi)
          +qz = In.nfr(p, z, m, D.Fd(3n, m, r), c, i, x, F, N, ry, hi)
          +ny = In.p1({True{} == In.nrd(p, y, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), F, N) : Bool}, {D.Node(y, m, D.Fd(2n, m, r), c) == D.Node(y, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), c) : Bool}, qy)
          +ey = In.p2({True{} == In.nrd(p, y, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), F, N) : Bool}, {D.Node(y, m, D.Fd(2n, m, r), c) == D.Node(y, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), c) : Bool}, qy)
          +nz = In.p1({True{} == In.nrd(p, z, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), F, N) : Bool}, {D.Node(z, m, D.Fd(3n, m, r), c) == D.Node(z, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), c) : Bool}, qz)
          +ez = In.p2({True{} == In.nrd(p, z, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), F, N) : Bool}, {D.Node(z, m, D.Fd(3n, m, r), c) == D.Node(z, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), c) : Bool}, qz)
          %In.fd.fr(2n, m, r, i, x, e => In.ne(r, i, F, N, hr, hi, e)) : In.P({True{} == Bool.and(In.rd(r, F, N), Bool.and(In.nrd(p, y, Cr.Cir.Cells.set(m, i, x), _, F, N), In.nrd(p, z, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, Cr.Cir.Cells.set(m, i, x), r), F, N))) : Bool}, {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(y, Cr.Cir.Cells.set(m, i, x), _, c), D.Node(z, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, Cr.Cir.Cells.set(m, i, x), r), c))) : Bool})
          %In.fd.fr(3n, m, r, i, x, e => In.ne(r, i, F, N, hr, hi, e)) : In.P({True{} == Bool.and(In.rd(r, F, N), Bool.and(In.nrd(p, y, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), F, N), In.nrd(p, z, Cr.Cir.Cells.set(m, i, x), _, F, N))) : Bool}, {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(y, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), c), D.Node(z, Cr.Cir.Cells.set(m, i, x), _, c))) : Bool})
          (Bo.and_i(In.rd(r, F, N), Bool.and(In.nrd(p, y, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), F, N), In.nrd(p, z, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), F, N)), hr, Bo.and_i(In.nrd(p, y, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), F, N), In.nrd(p, z, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), F, N), ny, nz)), (%ey : {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(_, D.Node(z, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), c))) : Bool}; %ez : {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(y, m, D.Fd(2n, m, r), c), _)) : Bool}; {==}))
        case Bk.Term.Let{_, +v, +g}:
          +hr = Bo.and_l(In.rd(r, F, N), Bool.and(In.nrd(p, v, m, D.Fd(2n, m, r), F, N), In.nrd(p, g, m, D.Fd(3n, m, r), F, N)), hn)
          +hp = Bo.and_r(In.rd(r, F, N), Bool.and(In.nrd(p, v, m, D.Fd(2n, m, r), F, N), In.nrd(p, g, m, D.Fd(3n, m, r), F, N)), hn)
          +hv = Bo.and_l(In.nrd(p, v, m, D.Fd(2n, m, r), F, N), In.nrd(p, g, m, D.Fd(3n, m, r), F, N), hp)
          +rv = Bo.and_r(In.nrd(p, v, m, D.Fd(2n, m, r), F, N), In.nrd(p, g, m, D.Fd(3n, m, r), F, N), hp)
          +qv = In.nfr(p, v, m, D.Fd(2n, m, r), c, i, x, F, N, hv, hi)
          +qg = In.nfr(p, g, m, D.Fd(3n, m, r), c, i, x, F, N, rv, hi)
          +nv = In.p1({True{} == In.nrd(p, v, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), F, N) : Bool}, {D.Node(v, m, D.Fd(2n, m, r), c) == D.Node(v, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), c) : Bool}, qv)
          +ev = In.p2({True{} == In.nrd(p, v, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), F, N) : Bool}, {D.Node(v, m, D.Fd(2n, m, r), c) == D.Node(v, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), c) : Bool}, qv)
          +ng = In.p1({True{} == In.nrd(p, g, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), F, N) : Bool}, {D.Node(g, m, D.Fd(3n, m, r), c) == D.Node(g, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), c) : Bool}, qg)
          +eg = In.p2({True{} == In.nrd(p, g, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), F, N) : Bool}, {D.Node(g, m, D.Fd(3n, m, r), c) == D.Node(g, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), c) : Bool}, qg)
          %In.fd.fr(2n, m, r, i, x, e => In.ne(r, i, F, N, hr, hi, e)) : In.P({True{} == Bool.and(In.rd(r, F, N), Bool.and(In.nrd(p, v, Cr.Cir.Cells.set(m, i, x), _, F, N), In.nrd(p, g, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, Cr.Cir.Cells.set(m, i, x), r), F, N))) : Bool}, {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(v, m, D.Fd(2n, m, r), c), D.Node(g, m, D.Fd(3n, m, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(v, Cr.Cir.Cells.set(m, i, x), _, c), D.Node(g, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, Cr.Cir.Cells.set(m, i, x), r), c))) : Bool})
          %In.fd.fr(3n, m, r, i, x, e => In.ne(r, i, F, N, hr, hi, e)) : In.P({True{} == Bool.and(In.rd(r, F, N), Bool.and(In.nrd(p, v, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), F, N), In.nrd(p, g, Cr.Cir.Cells.set(m, i, x), _, F, N))) : Bool}, {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(v, m, D.Fd(2n, m, r), c), D.Node(g, m, D.Fd(3n, m, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(v, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), c), D.Node(g, Cr.Cir.Cells.set(m, i, x), _, c))) : Bool})
          (Bo.and_i(In.rd(r, F, N), Bool.and(In.nrd(p, v, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), F, N), In.nrd(p, g, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), F, N)), hr, Bo.and_i(In.nrd(p, v, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), F, N), In.nrd(p, g, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), F, N), nv, ng)), (%ev : {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(v, m, D.Fd(2n, m, r), c), D.Node(g, m, D.Fd(3n, m, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(_, D.Node(g, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), c))) : Bool}; %eg : {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(v, m, D.Fd(2n, m, r), c), D.Node(g, m, D.Fd(3n, m, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(v, m, D.Fd(2n, m, r), c), _)) : Bool}; {==}))
        case Bk.Term.Typ{+y}:
          +hr = Bo.and_l(In.rd(r, F, N), In.nrd(p, y, m, D.Fd(2n, m, r), F, N), hn)
          +hp = Bo.and_r(In.rd(r, F, N), In.nrd(p, y, m, D.Fd(2n, m, r), F, N), hn)
          +qy = In.nfr(p, y, m, D.Fd(2n, m, r), c, i, x, F, N, hp, hi)
          +ny = In.p1({True{} == In.nrd(p, y, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), F, N) : Bool}, {D.Node(y, m, D.Fd(2n, m, r), c) == D.Node(y, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), c) : Bool}, qy)
          +ey = In.p2({True{} == In.nrd(p, y, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), F, N) : Bool}, {D.Node(y, m, D.Fd(2n, m, r), c) == D.Node(y, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), c) : Bool}, qy)
          %In.fd.fr(2n, m, r, i, x, e => In.ne(r, i, F, N, hr, hi, e)) : In.P({True{} == Bool.and(In.rd(r, F, N), In.nrd(p, y, Cr.Cir.Cells.set(m, i, x), _, F, N)) : Bool}, {Bool.or(U32.is_eq(r, c), D.Node(y, m, D.Fd(2n, m, r), c)) == Bool.or(U32.is_eq(r, c), D.Node(y, Cr.Cir.Cells.set(m, i, x), _, c)) : Bool})
          (Bo.and_i(In.rd(r, F, N), In.nrd(p, y, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), F, N), hr, ny), (%ey : {Bool.or(U32.is_eq(r, c), D.Node(y, m, D.Fd(2n, m, r), c)) == Bool.or(U32.is_eq(r, c), _) : Bool}; {==}))
        case Bk.Term.Min{+a, +b}:
          +hr = Bo.and_l(In.rd(r, F, N), Bool.and(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), In.nrd(p, b, m, D.Fd(3n, m, r), F, N)), hn)
          +hp = Bo.and_r(In.rd(r, F, N), Bool.and(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), In.nrd(p, b, m, D.Fd(3n, m, r), F, N)), hn)
          +ha = Bo.and_l(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), In.nrd(p, b, m, D.Fd(3n, m, r), F, N), hp)
          +ra = Bo.and_r(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), In.nrd(p, b, m, D.Fd(3n, m, r), F, N), hp)
          +qa = In.nfr(p, a, m, D.Fd(2n, m, r), c, i, x, F, N, ha, hi)
          +qb = In.nfr(p, b, m, D.Fd(3n, m, r), c, i, x, F, N, ra, hi)
          +na = In.p1({True{} == In.nrd(p, a, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), F, N) : Bool}, {D.Node(a, m, D.Fd(2n, m, r), c) == D.Node(a, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), c) : Bool}, qa)
          +ea = In.p2({True{} == In.nrd(p, a, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), F, N) : Bool}, {D.Node(a, m, D.Fd(2n, m, r), c) == D.Node(a, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), c) : Bool}, qa)
          +nb = In.p1({True{} == In.nrd(p, b, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), F, N) : Bool}, {D.Node(b, m, D.Fd(3n, m, r), c) == D.Node(b, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), c) : Bool}, qb)
          +eb = In.p2({True{} == In.nrd(p, b, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), F, N) : Bool}, {D.Node(b, m, D.Fd(3n, m, r), c) == D.Node(b, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), c) : Bool}, qb)
          %In.fd.fr(2n, m, r, i, x, e => In.ne(r, i, F, N, hr, hi, e)) : In.P({True{} == Bool.and(In.rd(r, F, N), Bool.and(In.nrd(p, a, Cr.Cir.Cells.set(m, i, x), _, F, N), In.nrd(p, b, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, Cr.Cir.Cells.set(m, i, x), r), F, N))) : Bool}, {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(a, m, D.Fd(2n, m, r), c), D.Node(b, m, D.Fd(3n, m, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(a, Cr.Cir.Cells.set(m, i, x), _, c), D.Node(b, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, Cr.Cir.Cells.set(m, i, x), r), c))) : Bool})
          %In.fd.fr(3n, m, r, i, x, e => In.ne(r, i, F, N, hr, hi, e)) : In.P({True{} == Bool.and(In.rd(r, F, N), Bool.and(In.nrd(p, a, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), F, N), In.nrd(p, b, Cr.Cir.Cells.set(m, i, x), _, F, N))) : Bool}, {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(a, m, D.Fd(2n, m, r), c), D.Node(b, m, D.Fd(3n, m, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(a, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), c), D.Node(b, Cr.Cir.Cells.set(m, i, x), _, c))) : Bool})
          (Bo.and_i(In.rd(r, F, N), Bool.and(In.nrd(p, a, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), F, N), In.nrd(p, b, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), F, N)), hr, Bo.and_i(In.nrd(p, a, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), F, N), In.nrd(p, b, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), F, N), na, nb)), (%ea : {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(a, m, D.Fd(2n, m, r), c), D.Node(b, m, D.Fd(3n, m, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(_, D.Node(b, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), c))) : Bool}; %eb : {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(a, m, D.Fd(2n, m, r), c), D.Node(b, m, D.Fd(3n, m, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(a, m, D.Fd(2n, m, r), c), _)) : Bool}; {==}))
        case Bk.Term.All{_, +a, +b}:
          +hr = Bo.and_l(In.rd(r, F, N), Bool.and(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), In.nrd(p, b, m, D.Fd(3n, m, r), F, N)), hn)
          +hp = Bo.and_r(In.rd(r, F, N), Bool.and(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), In.nrd(p, b, m, D.Fd(3n, m, r), F, N)), hn)
          +ha = Bo.and_l(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), In.nrd(p, b, m, D.Fd(3n, m, r), F, N), hp)
          +ra = Bo.and_r(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), In.nrd(p, b, m, D.Fd(3n, m, r), F, N), hp)
          +qa = In.nfr(p, a, m, D.Fd(2n, m, r), c, i, x, F, N, ha, hi)
          +qb = In.nfr(p, b, m, D.Fd(3n, m, r), c, i, x, F, N, ra, hi)
          +na = In.p1({True{} == In.nrd(p, a, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), F, N) : Bool}, {D.Node(a, m, D.Fd(2n, m, r), c) == D.Node(a, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), c) : Bool}, qa)
          +ea = In.p2({True{} == In.nrd(p, a, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), F, N) : Bool}, {D.Node(a, m, D.Fd(2n, m, r), c) == D.Node(a, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), c) : Bool}, qa)
          +nb = In.p1({True{} == In.nrd(p, b, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), F, N) : Bool}, {D.Node(b, m, D.Fd(3n, m, r), c) == D.Node(b, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), c) : Bool}, qb)
          +eb = In.p2({True{} == In.nrd(p, b, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), F, N) : Bool}, {D.Node(b, m, D.Fd(3n, m, r), c) == D.Node(b, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), c) : Bool}, qb)
          %In.fd.fr(2n, m, r, i, x, e => In.ne(r, i, F, N, hr, hi, e)) : In.P({True{} == Bool.and(In.rd(r, F, N), Bool.and(In.nrd(p, a, Cr.Cir.Cells.set(m, i, x), _, F, N), In.nrd(p, b, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, Cr.Cir.Cells.set(m, i, x), r), F, N))) : Bool}, {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(a, m, D.Fd(2n, m, r), c), D.Node(b, m, D.Fd(3n, m, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(a, Cr.Cir.Cells.set(m, i, x), _, c), D.Node(b, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, Cr.Cir.Cells.set(m, i, x), r), c))) : Bool})
          %In.fd.fr(3n, m, r, i, x, e => In.ne(r, i, F, N, hr, hi, e)) : In.P({True{} == Bool.and(In.rd(r, F, N), Bool.and(In.nrd(p, a, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), F, N), In.nrd(p, b, Cr.Cir.Cells.set(m, i, x), _, F, N))) : Bool}, {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(a, m, D.Fd(2n, m, r), c), D.Node(b, m, D.Fd(3n, m, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(a, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), c), D.Node(b, Cr.Cir.Cells.set(m, i, x), _, c))) : Bool})
          (Bo.and_i(In.rd(r, F, N), Bool.and(In.nrd(p, a, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), F, N), In.nrd(p, b, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), F, N)), hr, Bo.and_i(In.nrd(p, a, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), F, N), In.nrd(p, b, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), F, N), na, nb)), (%ea : {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(a, m, D.Fd(2n, m, r), c), D.Node(b, m, D.Fd(3n, m, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(_, D.Node(b, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), c))) : Bool}; %eb : {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(a, m, D.Fd(2n, m, r), c), D.Node(b, m, D.Fd(3n, m, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(a, m, D.Fd(2n, m, r), c), _)) : Bool}; {==}))
        case Bk.Term.Lam{_, +g}:
          +hr = Bo.and_l(In.rd(r, F, N), In.nrd(p, g, m, D.Fd(2n, m, r), F, N), hn)
          +hp = Bo.and_r(In.rd(r, F, N), In.nrd(p, g, m, D.Fd(2n, m, r), F, N), hn)
          +qg = In.nfr(p, g, m, D.Fd(2n, m, r), c, i, x, F, N, hp, hi)
          +ng = In.p1({True{} == In.nrd(p, g, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), F, N) : Bool}, {D.Node(g, m, D.Fd(2n, m, r), c) == D.Node(g, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), c) : Bool}, qg)
          +eg = In.p2({True{} == In.nrd(p, g, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), F, N) : Bool}, {D.Node(g, m, D.Fd(2n, m, r), c) == D.Node(g, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), c) : Bool}, qg)
          %In.fd.fr(2n, m, r, i, x, e => In.ne(r, i, F, N, hr, hi, e)) : In.P({True{} == Bool.and(In.rd(r, F, N), In.nrd(p, g, Cr.Cir.Cells.set(m, i, x), _, F, N)) : Bool}, {Bool.or(U32.is_eq(r, c), D.Node(g, m, D.Fd(2n, m, r), c)) == Bool.or(U32.is_eq(r, c), D.Node(g, Cr.Cir.Cells.set(m, i, x), _, c)) : Bool})
          (Bo.and_i(In.rd(r, F, N), In.nrd(p, g, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), F, N), hr, ng), (%eg : {Bool.or(U32.is_eq(r, c), D.Node(g, m, D.Fd(2n, m, r), c)) == Bool.or(U32.is_eq(r, c), _) : Bool}; {==}))
        case Bk.Term.App{_, +g, +y}:
          +hr = Bo.and_l(In.rd(r, F, N), Bool.and(In.nrd(p, g, m, D.Fd(2n, m, r), F, N), In.nrd(p, y, m, D.Fd(3n, m, r), F, N)), hn)
          +hp = Bo.and_r(In.rd(r, F, N), Bool.and(In.nrd(p, g, m, D.Fd(2n, m, r), F, N), In.nrd(p, y, m, D.Fd(3n, m, r), F, N)), hn)
          +hg = Bo.and_l(In.nrd(p, g, m, D.Fd(2n, m, r), F, N), In.nrd(p, y, m, D.Fd(3n, m, r), F, N), hp)
          +rg = Bo.and_r(In.nrd(p, g, m, D.Fd(2n, m, r), F, N), In.nrd(p, y, m, D.Fd(3n, m, r), F, N), hp)
          +qg = In.nfr(p, g, m, D.Fd(2n, m, r), c, i, x, F, N, hg, hi)
          +qy = In.nfr(p, y, m, D.Fd(3n, m, r), c, i, x, F, N, rg, hi)
          +ng = In.p1({True{} == In.nrd(p, g, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), F, N) : Bool}, {D.Node(g, m, D.Fd(2n, m, r), c) == D.Node(g, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), c) : Bool}, qg)
          +eg = In.p2({True{} == In.nrd(p, g, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), F, N) : Bool}, {D.Node(g, m, D.Fd(2n, m, r), c) == D.Node(g, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), c) : Bool}, qg)
          +ny = In.p1({True{} == In.nrd(p, y, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), F, N) : Bool}, {D.Node(y, m, D.Fd(3n, m, r), c) == D.Node(y, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), c) : Bool}, qy)
          +ey = In.p2({True{} == In.nrd(p, y, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), F, N) : Bool}, {D.Node(y, m, D.Fd(3n, m, r), c) == D.Node(y, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), c) : Bool}, qy)
          %In.fd.fr(2n, m, r, i, x, e => In.ne(r, i, F, N, hr, hi, e)) : In.P({True{} == Bool.and(In.rd(r, F, N), Bool.and(In.nrd(p, g, Cr.Cir.Cells.set(m, i, x), _, F, N), In.nrd(p, y, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, Cr.Cir.Cells.set(m, i, x), r), F, N))) : Bool}, {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(g, m, D.Fd(2n, m, r), c), D.Node(y, m, D.Fd(3n, m, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(g, Cr.Cir.Cells.set(m, i, x), _, c), D.Node(y, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, Cr.Cir.Cells.set(m, i, x), r), c))) : Bool})
          %In.fd.fr(3n, m, r, i, x, e => In.ne(r, i, F, N, hr, hi, e)) : In.P({True{} == Bool.and(In.rd(r, F, N), Bool.and(In.nrd(p, g, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), F, N), In.nrd(p, y, Cr.Cir.Cells.set(m, i, x), _, F, N))) : Bool}, {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(g, m, D.Fd(2n, m, r), c), D.Node(y, m, D.Fd(3n, m, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(g, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), c), D.Node(y, Cr.Cir.Cells.set(m, i, x), _, c))) : Bool})
          (Bo.and_i(In.rd(r, F, N), Bool.and(In.nrd(p, g, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), F, N), In.nrd(p, y, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), F, N)), hr, Bo.and_i(In.nrd(p, g, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), F, N), In.nrd(p, y, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), F, N), ng, ny)), (%eg : {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(g, m, D.Fd(2n, m, r), c), D.Node(y, m, D.Fd(3n, m, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(_, D.Node(y, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), c))) : Bool}; %ey : {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(g, m, D.Fd(2n, m, r), c), D.Node(y, m, D.Fd(3n, m, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(g, m, D.Fd(2n, m, r), c), _)) : Bool}; {==}))
        case Bk.Term.Sig{_, +a, +b}:
          +hr = Bo.and_l(In.rd(r, F, N), Bool.and(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), In.nrd(p, b, m, D.Fd(3n, m, r), F, N)), hn)
          +hp = Bo.and_r(In.rd(r, F, N), Bool.and(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), In.nrd(p, b, m, D.Fd(3n, m, r), F, N)), hn)
          +ha = Bo.and_l(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), In.nrd(p, b, m, D.Fd(3n, m, r), F, N), hp)
          +ra = Bo.and_r(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), In.nrd(p, b, m, D.Fd(3n, m, r), F, N), hp)
          +qa = In.nfr(p, a, m, D.Fd(2n, m, r), c, i, x, F, N, ha, hi)
          +qb = In.nfr(p, b, m, D.Fd(3n, m, r), c, i, x, F, N, ra, hi)
          +na = In.p1({True{} == In.nrd(p, a, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), F, N) : Bool}, {D.Node(a, m, D.Fd(2n, m, r), c) == D.Node(a, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), c) : Bool}, qa)
          +ea = In.p2({True{} == In.nrd(p, a, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), F, N) : Bool}, {D.Node(a, m, D.Fd(2n, m, r), c) == D.Node(a, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), c) : Bool}, qa)
          +nb = In.p1({True{} == In.nrd(p, b, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), F, N) : Bool}, {D.Node(b, m, D.Fd(3n, m, r), c) == D.Node(b, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), c) : Bool}, qb)
          +eb = In.p2({True{} == In.nrd(p, b, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), F, N) : Bool}, {D.Node(b, m, D.Fd(3n, m, r), c) == D.Node(b, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), c) : Bool}, qb)
          %In.fd.fr(2n, m, r, i, x, e => In.ne(r, i, F, N, hr, hi, e)) : In.P({True{} == Bool.and(In.rd(r, F, N), Bool.and(In.nrd(p, a, Cr.Cir.Cells.set(m, i, x), _, F, N), In.nrd(p, b, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, Cr.Cir.Cells.set(m, i, x), r), F, N))) : Bool}, {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(a, m, D.Fd(2n, m, r), c), D.Node(b, m, D.Fd(3n, m, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(a, Cr.Cir.Cells.set(m, i, x), _, c), D.Node(b, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, Cr.Cir.Cells.set(m, i, x), r), c))) : Bool})
          %In.fd.fr(3n, m, r, i, x, e => In.ne(r, i, F, N, hr, hi, e)) : In.P({True{} == Bool.and(In.rd(r, F, N), Bool.and(In.nrd(p, a, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), F, N), In.nrd(p, b, Cr.Cir.Cells.set(m, i, x), _, F, N))) : Bool}, {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(a, m, D.Fd(2n, m, r), c), D.Node(b, m, D.Fd(3n, m, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(a, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), c), D.Node(b, Cr.Cir.Cells.set(m, i, x), _, c))) : Bool})
          (Bo.and_i(In.rd(r, F, N), Bool.and(In.nrd(p, a, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), F, N), In.nrd(p, b, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), F, N)), hr, Bo.and_i(In.nrd(p, a, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), F, N), In.nrd(p, b, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), F, N), na, nb)), (%ea : {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(a, m, D.Fd(2n, m, r), c), D.Node(b, m, D.Fd(3n, m, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(_, D.Node(b, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), c))) : Bool}; %eb : {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(a, m, D.Fd(2n, m, r), c), D.Node(b, m, D.Fd(3n, m, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(a, m, D.Fd(2n, m, r), c), _)) : Bool}; {==}))
        case Bk.Term.Tup{_, +a, +b}:
          +hr = Bo.and_l(In.rd(r, F, N), Bool.and(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), In.nrd(p, b, m, D.Fd(3n, m, r), F, N)), hn)
          +hp = Bo.and_r(In.rd(r, F, N), Bool.and(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), In.nrd(p, b, m, D.Fd(3n, m, r), F, N)), hn)
          +ha = Bo.and_l(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), In.nrd(p, b, m, D.Fd(3n, m, r), F, N), hp)
          +ra = Bo.and_r(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), In.nrd(p, b, m, D.Fd(3n, m, r), F, N), hp)
          +qa = In.nfr(p, a, m, D.Fd(2n, m, r), c, i, x, F, N, ha, hi)
          +qb = In.nfr(p, b, m, D.Fd(3n, m, r), c, i, x, F, N, ra, hi)
          +na = In.p1({True{} == In.nrd(p, a, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), F, N) : Bool}, {D.Node(a, m, D.Fd(2n, m, r), c) == D.Node(a, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), c) : Bool}, qa)
          +ea = In.p2({True{} == In.nrd(p, a, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), F, N) : Bool}, {D.Node(a, m, D.Fd(2n, m, r), c) == D.Node(a, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), c) : Bool}, qa)
          +nb = In.p1({True{} == In.nrd(p, b, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), F, N) : Bool}, {D.Node(b, m, D.Fd(3n, m, r), c) == D.Node(b, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), c) : Bool}, qb)
          +eb = In.p2({True{} == In.nrd(p, b, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), F, N) : Bool}, {D.Node(b, m, D.Fd(3n, m, r), c) == D.Node(b, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), c) : Bool}, qb)
          %In.fd.fr(2n, m, r, i, x, e => In.ne(r, i, F, N, hr, hi, e)) : In.P({True{} == Bool.and(In.rd(r, F, N), Bool.and(In.nrd(p, a, Cr.Cir.Cells.set(m, i, x), _, F, N), In.nrd(p, b, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, Cr.Cir.Cells.set(m, i, x), r), F, N))) : Bool}, {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(a, m, D.Fd(2n, m, r), c), D.Node(b, m, D.Fd(3n, m, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(a, Cr.Cir.Cells.set(m, i, x), _, c), D.Node(b, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, Cr.Cir.Cells.set(m, i, x), r), c))) : Bool})
          %In.fd.fr(3n, m, r, i, x, e => In.ne(r, i, F, N, hr, hi, e)) : In.P({True{} == Bool.and(In.rd(r, F, N), Bool.and(In.nrd(p, a, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), F, N), In.nrd(p, b, Cr.Cir.Cells.set(m, i, x), _, F, N))) : Bool}, {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(a, m, D.Fd(2n, m, r), c), D.Node(b, m, D.Fd(3n, m, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(a, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), c), D.Node(b, Cr.Cir.Cells.set(m, i, x), _, c))) : Bool})
          (Bo.and_i(In.rd(r, F, N), Bool.and(In.nrd(p, a, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), F, N), In.nrd(p, b, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), F, N)), hr, Bo.and_i(In.nrd(p, a, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), F, N), In.nrd(p, b, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), F, N), na, nb)), (%ea : {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(a, m, D.Fd(2n, m, r), c), D.Node(b, m, D.Fd(3n, m, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(_, D.Node(b, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), c))) : Bool}; %eb : {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(a, m, D.Fd(2n, m, r), c), D.Node(b, m, D.Fd(3n, m, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(a, m, D.Fd(2n, m, r), c), _)) : Bool}; {==}))
        case Bk.Term.Prj{+h}:
          +hr = Bo.and_l(In.rd(r, F, N), In.nrd(p, h, m, D.Fd(2n, m, r), F, N), hn)
          +hp = Bo.and_r(In.rd(r, F, N), In.nrd(p, h, m, D.Fd(2n, m, r), F, N), hn)
          +qh = In.nfr(p, h, m, D.Fd(2n, m, r), c, i, x, F, N, hp, hi)
          +nh = In.p1({True{} == In.nrd(p, h, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), F, N) : Bool}, {D.Node(h, m, D.Fd(2n, m, r), c) == D.Node(h, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), c) : Bool}, qh)
          +eh = In.p2({True{} == In.nrd(p, h, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), F, N) : Bool}, {D.Node(h, m, D.Fd(2n, m, r), c) == D.Node(h, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), c) : Bool}, qh)
          %In.fd.fr(2n, m, r, i, x, e => In.ne(r, i, F, N, hr, hi, e)) : In.P({True{} == Bool.and(In.rd(r, F, N), In.nrd(p, h, Cr.Cir.Cells.set(m, i, x), _, F, N)) : Bool}, {Bool.or(U32.is_eq(r, c), D.Node(h, m, D.Fd(2n, m, r), c)) == Bool.or(U32.is_eq(r, c), D.Node(h, Cr.Cir.Cells.set(m, i, x), _, c)) : Bool})
          (Bo.and_i(In.rd(r, F, N), In.nrd(p, h, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), F, N), hr, nh), (%eh : {Bool.or(U32.is_eq(r, c), D.Node(h, m, D.Fd(2n, m, r), c)) == Bool.or(U32.is_eq(r, c), _) : Bool}; {==}))
        case Bk.Term.Enu{_}:
          (hn, {==})
        case Bk.Term.Lab{_}:
          (hn, {==})
        case Bk.Term.Mat{_, +h, +o}:
          +hr = Bo.and_l(In.rd(r, F, N), Bool.and(In.nrd(p, h, m, D.Fd(3n, m, r), F, N), In.nrd(p, o, m, D.Fd(4n, m, r), F, N)), hn)
          +hp = Bo.and_r(In.rd(r, F, N), Bool.and(In.nrd(p, h, m, D.Fd(3n, m, r), F, N), In.nrd(p, o, m, D.Fd(4n, m, r), F, N)), hn)
          +hh = Bo.and_l(In.nrd(p, h, m, D.Fd(3n, m, r), F, N), In.nrd(p, o, m, D.Fd(4n, m, r), F, N), hp)
          +rh = Bo.and_r(In.nrd(p, h, m, D.Fd(3n, m, r), F, N), In.nrd(p, o, m, D.Fd(4n, m, r), F, N), hp)
          +qh = In.nfr(p, h, m, D.Fd(3n, m, r), c, i, x, F, N, hh, hi)
          +qo = In.nfr(p, o, m, D.Fd(4n, m, r), c, i, x, F, N, rh, hi)
          +nh = In.p1({True{} == In.nrd(p, h, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), F, N) : Bool}, {D.Node(h, m, D.Fd(3n, m, r), c) == D.Node(h, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), c) : Bool}, qh)
          +eh = In.p2({True{} == In.nrd(p, h, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), F, N) : Bool}, {D.Node(h, m, D.Fd(3n, m, r), c) == D.Node(h, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), c) : Bool}, qh)
          +no = In.p1({True{} == In.nrd(p, o, Cr.Cir.Cells.set(m, i, x), D.Fd(4n, m, r), F, N) : Bool}, {D.Node(o, m, D.Fd(4n, m, r), c) == D.Node(o, Cr.Cir.Cells.set(m, i, x), D.Fd(4n, m, r), c) : Bool}, qo)
          +eo = In.p2({True{} == In.nrd(p, o, Cr.Cir.Cells.set(m, i, x), D.Fd(4n, m, r), F, N) : Bool}, {D.Node(o, m, D.Fd(4n, m, r), c) == D.Node(o, Cr.Cir.Cells.set(m, i, x), D.Fd(4n, m, r), c) : Bool}, qo)
          %In.fd.fr(3n, m, r, i, x, e => In.ne(r, i, F, N, hr, hi, e)) : In.P({True{} == Bool.and(In.rd(r, F, N), Bool.and(In.nrd(p, h, Cr.Cir.Cells.set(m, i, x), _, F, N), In.nrd(p, o, Cr.Cir.Cells.set(m, i, x), D.Fd(4n, Cr.Cir.Cells.set(m, i, x), r), F, N))) : Bool}, {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(h, m, D.Fd(3n, m, r), c), D.Node(o, m, D.Fd(4n, m, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(h, Cr.Cir.Cells.set(m, i, x), _, c), D.Node(o, Cr.Cir.Cells.set(m, i, x), D.Fd(4n, Cr.Cir.Cells.set(m, i, x), r), c))) : Bool})
          %In.fd.fr(4n, m, r, i, x, e => In.ne(r, i, F, N, hr, hi, e)) : In.P({True{} == Bool.and(In.rd(r, F, N), Bool.and(In.nrd(p, h, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), F, N), In.nrd(p, o, Cr.Cir.Cells.set(m, i, x), _, F, N))) : Bool}, {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(h, m, D.Fd(3n, m, r), c), D.Node(o, m, D.Fd(4n, m, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(h, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), c), D.Node(o, Cr.Cir.Cells.set(m, i, x), _, c))) : Bool})
          (Bo.and_i(In.rd(r, F, N), Bool.and(In.nrd(p, h, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), F, N), In.nrd(p, o, Cr.Cir.Cells.set(m, i, x), D.Fd(4n, m, r), F, N)), hr, Bo.and_i(In.nrd(p, h, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), F, N), In.nrd(p, o, Cr.Cir.Cells.set(m, i, x), D.Fd(4n, m, r), F, N), nh, no)), (%eh : {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(h, m, D.Fd(3n, m, r), c), D.Node(o, m, D.Fd(4n, m, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(_, D.Node(o, Cr.Cir.Cells.set(m, i, x), D.Fd(4n, m, r), c))) : Bool}; %eo : {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(h, m, D.Fd(3n, m, r), c), D.Node(o, m, D.Fd(4n, m, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(h, m, D.Fd(3n, m, r), c), _)) : Bool}; {==}))
        case Bk.Term.Efq{}:
          (hn, {==})
        case Bk.Term.Eql{+a, +b, +y}:
          +hr = Bo.and_l(In.rd(r, F, N), Bool.and(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), Bool.and(In.nrd(p, b, m, D.Fd(3n, m, r), F, N), In.nrd(p, y, m, D.Fd(4n, m, r), F, N))), hn)
          +hp = Bo.and_r(In.rd(r, F, N), Bool.and(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), Bool.and(In.nrd(p, b, m, D.Fd(3n, m, r), F, N), In.nrd(p, y, m, D.Fd(4n, m, r), F, N))), hn)
          +ha = Bo.and_l(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), Bool.and(In.nrd(p, b, m, D.Fd(3n, m, r), F, N), In.nrd(p, y, m, D.Fd(4n, m, r), F, N)), hp)
          +ra = Bo.and_r(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), Bool.and(In.nrd(p, b, m, D.Fd(3n, m, r), F, N), In.nrd(p, y, m, D.Fd(4n, m, r), F, N)), hp)
          +hb = Bo.and_l(In.nrd(p, b, m, D.Fd(3n, m, r), F, N), In.nrd(p, y, m, D.Fd(4n, m, r), F, N), ra)
          +rb = Bo.and_r(In.nrd(p, b, m, D.Fd(3n, m, r), F, N), In.nrd(p, y, m, D.Fd(4n, m, r), F, N), ra)
          +qa = In.nfr(p, a, m, D.Fd(2n, m, r), c, i, x, F, N, ha, hi)
          +qb = In.nfr(p, b, m, D.Fd(3n, m, r), c, i, x, F, N, hb, hi)
          +qy = In.nfr(p, y, m, D.Fd(4n, m, r), c, i, x, F, N, rb, hi)
          +na = In.p1({True{} == In.nrd(p, a, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), F, N) : Bool}, {D.Node(a, m, D.Fd(2n, m, r), c) == D.Node(a, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), c) : Bool}, qa)
          +ea = In.p2({True{} == In.nrd(p, a, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), F, N) : Bool}, {D.Node(a, m, D.Fd(2n, m, r), c) == D.Node(a, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), c) : Bool}, qa)
          +nb = In.p1({True{} == In.nrd(p, b, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), F, N) : Bool}, {D.Node(b, m, D.Fd(3n, m, r), c) == D.Node(b, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), c) : Bool}, qb)
          +eb = In.p2({True{} == In.nrd(p, b, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), F, N) : Bool}, {D.Node(b, m, D.Fd(3n, m, r), c) == D.Node(b, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), c) : Bool}, qb)
          +ny = In.p1({True{} == In.nrd(p, y, Cr.Cir.Cells.set(m, i, x), D.Fd(4n, m, r), F, N) : Bool}, {D.Node(y, m, D.Fd(4n, m, r), c) == D.Node(y, Cr.Cir.Cells.set(m, i, x), D.Fd(4n, m, r), c) : Bool}, qy)
          +ey = In.p2({True{} == In.nrd(p, y, Cr.Cir.Cells.set(m, i, x), D.Fd(4n, m, r), F, N) : Bool}, {D.Node(y, m, D.Fd(4n, m, r), c) == D.Node(y, Cr.Cir.Cells.set(m, i, x), D.Fd(4n, m, r), c) : Bool}, qy)
          %In.fd.fr(2n, m, r, i, x, e => In.ne(r, i, F, N, hr, hi, e)) : In.P({True{} == Bool.and(In.rd(r, F, N), Bool.and(In.nrd(p, a, Cr.Cir.Cells.set(m, i, x), _, F, N), Bool.and(In.nrd(p, b, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, Cr.Cir.Cells.set(m, i, x), r), F, N), In.nrd(p, y, Cr.Cir.Cells.set(m, i, x), D.Fd(4n, Cr.Cir.Cells.set(m, i, x), r), F, N)))) : Bool}, {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(a, m, D.Fd(2n, m, r), c), Bool.or(D.Node(b, m, D.Fd(3n, m, r), c), D.Node(y, m, D.Fd(4n, m, r), c)))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(a, Cr.Cir.Cells.set(m, i, x), _, c), Bool.or(D.Node(b, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, Cr.Cir.Cells.set(m, i, x), r), c), D.Node(y, Cr.Cir.Cells.set(m, i, x), D.Fd(4n, Cr.Cir.Cells.set(m, i, x), r), c)))) : Bool})
          %In.fd.fr(3n, m, r, i, x, e => In.ne(r, i, F, N, hr, hi, e)) : In.P({True{} == Bool.and(In.rd(r, F, N), Bool.and(In.nrd(p, a, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), F, N), Bool.and(In.nrd(p, b, Cr.Cir.Cells.set(m, i, x), _, F, N), In.nrd(p, y, Cr.Cir.Cells.set(m, i, x), D.Fd(4n, Cr.Cir.Cells.set(m, i, x), r), F, N)))) : Bool}, {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(a, m, D.Fd(2n, m, r), c), Bool.or(D.Node(b, m, D.Fd(3n, m, r), c), D.Node(y, m, D.Fd(4n, m, r), c)))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(a, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), c), Bool.or(D.Node(b, Cr.Cir.Cells.set(m, i, x), _, c), D.Node(y, Cr.Cir.Cells.set(m, i, x), D.Fd(4n, Cr.Cir.Cells.set(m, i, x), r), c)))) : Bool})
          %In.fd.fr(4n, m, r, i, x, e => In.ne(r, i, F, N, hr, hi, e)) : In.P({True{} == Bool.and(In.rd(r, F, N), Bool.and(In.nrd(p, a, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), F, N), Bool.and(In.nrd(p, b, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), F, N), In.nrd(p, y, Cr.Cir.Cells.set(m, i, x), _, F, N)))) : Bool}, {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(a, m, D.Fd(2n, m, r), c), Bool.or(D.Node(b, m, D.Fd(3n, m, r), c), D.Node(y, m, D.Fd(4n, m, r), c)))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(a, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), c), Bool.or(D.Node(b, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), c), D.Node(y, Cr.Cir.Cells.set(m, i, x), _, c)))) : Bool})
          (Bo.and_i(In.rd(r, F, N), Bool.and(In.nrd(p, a, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), F, N), Bool.and(In.nrd(p, b, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), F, N), In.nrd(p, y, Cr.Cir.Cells.set(m, i, x), D.Fd(4n, m, r), F, N))), hr, Bo.and_i(In.nrd(p, a, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), F, N), Bool.and(In.nrd(p, b, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), F, N), In.nrd(p, y, Cr.Cir.Cells.set(m, i, x), D.Fd(4n, m, r), F, N)), na, Bo.and_i(In.nrd(p, b, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), F, N), In.nrd(p, y, Cr.Cir.Cells.set(m, i, x), D.Fd(4n, m, r), F, N), nb, ny))), (%ea : {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(a, m, D.Fd(2n, m, r), c), Bool.or(D.Node(b, m, D.Fd(3n, m, r), c), D.Node(y, m, D.Fd(4n, m, r), c)))) == Bool.or(U32.is_eq(r, c), Bool.or(_, Bool.or(D.Node(b, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), c), D.Node(y, Cr.Cir.Cells.set(m, i, x), D.Fd(4n, m, r), c)))) : Bool}; %eb : {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(a, m, D.Fd(2n, m, r), c), Bool.or(D.Node(b, m, D.Fd(3n, m, r), c), D.Node(y, m, D.Fd(4n, m, r), c)))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(a, m, D.Fd(2n, m, r), c), Bool.or(_, D.Node(y, Cr.Cir.Cells.set(m, i, x), D.Fd(4n, m, r), c)))) : Bool}; %ey : {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(a, m, D.Fd(2n, m, r), c), Bool.or(D.Node(b, m, D.Fd(3n, m, r), c), D.Node(y, m, D.Fd(4n, m, r), c)))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(a, m, D.Fd(2n, m, r), c), Bool.or(D.Node(b, m, D.Fd(3n, m, r), c), _))) : Bool}; {==}))
        case Bk.Term.Rfl{}:
          (hn, {==})
        case Bk.Term.Rwt{+w, +y, +g}:
          +hr = Bo.and_l(In.rd(r, F, N), Bool.and(In.nrd(p, w, m, D.Fd(2n, m, r), F, N), Bool.and(In.nrd(p, y, m, D.Fd(3n, m, r), F, N), In.nrd(p, g, m, D.Fd(4n, m, r), F, N))), hn)
          +hp = Bo.and_r(In.rd(r, F, N), Bool.and(In.nrd(p, w, m, D.Fd(2n, m, r), F, N), Bool.and(In.nrd(p, y, m, D.Fd(3n, m, r), F, N), In.nrd(p, g, m, D.Fd(4n, m, r), F, N))), hn)
          +hw = Bo.and_l(In.nrd(p, w, m, D.Fd(2n, m, r), F, N), Bool.and(In.nrd(p, y, m, D.Fd(3n, m, r), F, N), In.nrd(p, g, m, D.Fd(4n, m, r), F, N)), hp)
          +rw = Bo.and_r(In.nrd(p, w, m, D.Fd(2n, m, r), F, N), Bool.and(In.nrd(p, y, m, D.Fd(3n, m, r), F, N), In.nrd(p, g, m, D.Fd(4n, m, r), F, N)), hp)
          +hy = Bo.and_l(In.nrd(p, y, m, D.Fd(3n, m, r), F, N), In.nrd(p, g, m, D.Fd(4n, m, r), F, N), rw)
          +ry = Bo.and_r(In.nrd(p, y, m, D.Fd(3n, m, r), F, N), In.nrd(p, g, m, D.Fd(4n, m, r), F, N), rw)
          +qw = In.nfr(p, w, m, D.Fd(2n, m, r), c, i, x, F, N, hw, hi)
          +qy = In.nfr(p, y, m, D.Fd(3n, m, r), c, i, x, F, N, hy, hi)
          +qg = In.nfr(p, g, m, D.Fd(4n, m, r), c, i, x, F, N, ry, hi)
          +nw = In.p1({True{} == In.nrd(p, w, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), F, N) : Bool}, {D.Node(w, m, D.Fd(2n, m, r), c) == D.Node(w, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), c) : Bool}, qw)
          +ew = In.p2({True{} == In.nrd(p, w, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), F, N) : Bool}, {D.Node(w, m, D.Fd(2n, m, r), c) == D.Node(w, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), c) : Bool}, qw)
          +ny = In.p1({True{} == In.nrd(p, y, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), F, N) : Bool}, {D.Node(y, m, D.Fd(3n, m, r), c) == D.Node(y, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), c) : Bool}, qy)
          +ey = In.p2({True{} == In.nrd(p, y, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), F, N) : Bool}, {D.Node(y, m, D.Fd(3n, m, r), c) == D.Node(y, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), c) : Bool}, qy)
          +ng = In.p1({True{} == In.nrd(p, g, Cr.Cir.Cells.set(m, i, x), D.Fd(4n, m, r), F, N) : Bool}, {D.Node(g, m, D.Fd(4n, m, r), c) == D.Node(g, Cr.Cir.Cells.set(m, i, x), D.Fd(4n, m, r), c) : Bool}, qg)
          +eg = In.p2({True{} == In.nrd(p, g, Cr.Cir.Cells.set(m, i, x), D.Fd(4n, m, r), F, N) : Bool}, {D.Node(g, m, D.Fd(4n, m, r), c) == D.Node(g, Cr.Cir.Cells.set(m, i, x), D.Fd(4n, m, r), c) : Bool}, qg)
          %In.fd.fr(2n, m, r, i, x, e => In.ne(r, i, F, N, hr, hi, e)) : In.P({True{} == Bool.and(In.rd(r, F, N), Bool.and(In.nrd(p, w, Cr.Cir.Cells.set(m, i, x), _, F, N), Bool.and(In.nrd(p, y, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, Cr.Cir.Cells.set(m, i, x), r), F, N), In.nrd(p, g, Cr.Cir.Cells.set(m, i, x), D.Fd(4n, Cr.Cir.Cells.set(m, i, x), r), F, N)))) : Bool}, {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(w, m, D.Fd(2n, m, r), c), Bool.or(D.Node(y, m, D.Fd(3n, m, r), c), D.Node(g, m, D.Fd(4n, m, r), c)))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(w, Cr.Cir.Cells.set(m, i, x), _, c), Bool.or(D.Node(y, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, Cr.Cir.Cells.set(m, i, x), r), c), D.Node(g, Cr.Cir.Cells.set(m, i, x), D.Fd(4n, Cr.Cir.Cells.set(m, i, x), r), c)))) : Bool})
          %In.fd.fr(3n, m, r, i, x, e => In.ne(r, i, F, N, hr, hi, e)) : In.P({True{} == Bool.and(In.rd(r, F, N), Bool.and(In.nrd(p, w, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), F, N), Bool.and(In.nrd(p, y, Cr.Cir.Cells.set(m, i, x), _, F, N), In.nrd(p, g, Cr.Cir.Cells.set(m, i, x), D.Fd(4n, Cr.Cir.Cells.set(m, i, x), r), F, N)))) : Bool}, {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(w, m, D.Fd(2n, m, r), c), Bool.or(D.Node(y, m, D.Fd(3n, m, r), c), D.Node(g, m, D.Fd(4n, m, r), c)))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(w, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), c), Bool.or(D.Node(y, Cr.Cir.Cells.set(m, i, x), _, c), D.Node(g, Cr.Cir.Cells.set(m, i, x), D.Fd(4n, Cr.Cir.Cells.set(m, i, x), r), c)))) : Bool})
          %In.fd.fr(4n, m, r, i, x, e => In.ne(r, i, F, N, hr, hi, e)) : In.P({True{} == Bool.and(In.rd(r, F, N), Bool.and(In.nrd(p, w, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), F, N), Bool.and(In.nrd(p, y, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), F, N), In.nrd(p, g, Cr.Cir.Cells.set(m, i, x), _, F, N)))) : Bool}, {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(w, m, D.Fd(2n, m, r), c), Bool.or(D.Node(y, m, D.Fd(3n, m, r), c), D.Node(g, m, D.Fd(4n, m, r), c)))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(w, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), c), Bool.or(D.Node(y, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), c), D.Node(g, Cr.Cir.Cells.set(m, i, x), _, c)))) : Bool})
          (Bo.and_i(In.rd(r, F, N), Bool.and(In.nrd(p, w, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), F, N), Bool.and(In.nrd(p, y, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), F, N), In.nrd(p, g, Cr.Cir.Cells.set(m, i, x), D.Fd(4n, m, r), F, N))), hr, Bo.and_i(In.nrd(p, w, Cr.Cir.Cells.set(m, i, x), D.Fd(2n, m, r), F, N), Bool.and(In.nrd(p, y, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), F, N), In.nrd(p, g, Cr.Cir.Cells.set(m, i, x), D.Fd(4n, m, r), F, N)), nw, Bo.and_i(In.nrd(p, y, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), F, N), In.nrd(p, g, Cr.Cir.Cells.set(m, i, x), D.Fd(4n, m, r), F, N), ny, ng))), (%ew : {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(w, m, D.Fd(2n, m, r), c), Bool.or(D.Node(y, m, D.Fd(3n, m, r), c), D.Node(g, m, D.Fd(4n, m, r), c)))) == Bool.or(U32.is_eq(r, c), Bool.or(_, Bool.or(D.Node(y, Cr.Cir.Cells.set(m, i, x), D.Fd(3n, m, r), c), D.Node(g, Cr.Cir.Cells.set(m, i, x), D.Fd(4n, m, r), c)))) : Bool}; %ey : {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(w, m, D.Fd(2n, m, r), c), Bool.or(D.Node(y, m, D.Fd(3n, m, r), c), D.Node(g, m, D.Fd(4n, m, r), c)))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(w, m, D.Fd(2n, m, r), c), Bool.or(_, D.Node(g, Cr.Cir.Cells.set(m, i, x), D.Fd(4n, m, r), c)))) : Bool}; %eg : {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(w, m, D.Fd(2n, m, r), c), Bool.or(D.Node(y, m, D.Fd(3n, m, r), c), D.Node(g, m, D.Fd(4n, m, r), c)))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(w, m, D.Fd(2n, m, r), c), Bool.or(D.Node(y, m, D.Fd(3n, m, r), c), _))) : Bool}; {==}))

# the nodes of t at r may still be read once one more cell is taken
def In.nup(f: Nat, t: Bk.Term, +m: Cr.Cir.Cells, +r: U32, +F: U32, +N: Nat, +hn: {True{} == In.nrd(f, t, m, r, F, N) : Bool}) ->
  {True{} == In.nrd(f, t, m, r, F, 1n+N) : Bool}:
  match f:
    case 0n:
      hn
    case 1n+(+p):
      match t:
        case Bk.Term.Var{_}:
          In.rd_up(r, F, N, hn)
        case Bk.Term.Ref{_}:
          In.rd_up(r, F, N, hn)
        case Bk.Term.Ann{+y, +z}:
          +hr = Bo.and_l(In.rd(r, F, N), Bool.and(In.nrd(p, y, m, D.Fd(2n, m, r), F, N), In.nrd(p, z, m, D.Fd(3n, m, r), F, N)), hn)
          +hp = Bo.and_r(In.rd(r, F, N), Bool.and(In.nrd(p, y, m, D.Fd(2n, m, r), F, N), In.nrd(p, z, m, D.Fd(3n, m, r), F, N)), hn)
          +hy = Bo.and_l(In.nrd(p, y, m, D.Fd(2n, m, r), F, N), In.nrd(p, z, m, D.Fd(3n, m, r), F, N), hp)
          +ry = Bo.and_r(In.nrd(p, y, m, D.Fd(2n, m, r), F, N), In.nrd(p, z, m, D.Fd(3n, m, r), F, N), hp)
          Bo.and_i(In.rd(r, F, 1n+N), Bool.and(In.nrd(p, y, m, D.Fd(2n, m, r), F, 1n+N), In.nrd(p, z, m, D.Fd(3n, m, r), F, 1n+N)), In.rd_up(r, F, N, hr), Bo.and_i(In.nrd(p, y, m, D.Fd(2n, m, r), F, 1n+N), In.nrd(p, z, m, D.Fd(3n, m, r), F, 1n+N), In.nup(p, y, m, D.Fd(2n, m, r), F, N, hy), In.nup(p, z, m, D.Fd(3n, m, r), F, N, ry)))
        case Bk.Term.Let{_, +v, +g}:
          +hr = Bo.and_l(In.rd(r, F, N), Bool.and(In.nrd(p, v, m, D.Fd(2n, m, r), F, N), In.nrd(p, g, m, D.Fd(3n, m, r), F, N)), hn)
          +hp = Bo.and_r(In.rd(r, F, N), Bool.and(In.nrd(p, v, m, D.Fd(2n, m, r), F, N), In.nrd(p, g, m, D.Fd(3n, m, r), F, N)), hn)
          +hv = Bo.and_l(In.nrd(p, v, m, D.Fd(2n, m, r), F, N), In.nrd(p, g, m, D.Fd(3n, m, r), F, N), hp)
          +rv = Bo.and_r(In.nrd(p, v, m, D.Fd(2n, m, r), F, N), In.nrd(p, g, m, D.Fd(3n, m, r), F, N), hp)
          Bo.and_i(In.rd(r, F, 1n+N), Bool.and(In.nrd(p, v, m, D.Fd(2n, m, r), F, 1n+N), In.nrd(p, g, m, D.Fd(3n, m, r), F, 1n+N)), In.rd_up(r, F, N, hr), Bo.and_i(In.nrd(p, v, m, D.Fd(2n, m, r), F, 1n+N), In.nrd(p, g, m, D.Fd(3n, m, r), F, 1n+N), In.nup(p, v, m, D.Fd(2n, m, r), F, N, hv), In.nup(p, g, m, D.Fd(3n, m, r), F, N, rv)))
        case Bk.Term.Typ{+y}:
          +hr = Bo.and_l(In.rd(r, F, N), In.nrd(p, y, m, D.Fd(2n, m, r), F, N), hn)
          +hp = Bo.and_r(In.rd(r, F, N), In.nrd(p, y, m, D.Fd(2n, m, r), F, N), hn)
          Bo.and_i(In.rd(r, F, 1n+N), In.nrd(p, y, m, D.Fd(2n, m, r), F, 1n+N), In.rd_up(r, F, N, hr), In.nup(p, y, m, D.Fd(2n, m, r), F, N, hp))
        case Bk.Term.Min{+a, +b}:
          +hr = Bo.and_l(In.rd(r, F, N), Bool.and(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), In.nrd(p, b, m, D.Fd(3n, m, r), F, N)), hn)
          +hp = Bo.and_r(In.rd(r, F, N), Bool.and(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), In.nrd(p, b, m, D.Fd(3n, m, r), F, N)), hn)
          +ha = Bo.and_l(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), In.nrd(p, b, m, D.Fd(3n, m, r), F, N), hp)
          +ra = Bo.and_r(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), In.nrd(p, b, m, D.Fd(3n, m, r), F, N), hp)
          Bo.and_i(In.rd(r, F, 1n+N), Bool.and(In.nrd(p, a, m, D.Fd(2n, m, r), F, 1n+N), In.nrd(p, b, m, D.Fd(3n, m, r), F, 1n+N)), In.rd_up(r, F, N, hr), Bo.and_i(In.nrd(p, a, m, D.Fd(2n, m, r), F, 1n+N), In.nrd(p, b, m, D.Fd(3n, m, r), F, 1n+N), In.nup(p, a, m, D.Fd(2n, m, r), F, N, ha), In.nup(p, b, m, D.Fd(3n, m, r), F, N, ra)))
        case Bk.Term.All{_, +a, +b}:
          +hr = Bo.and_l(In.rd(r, F, N), Bool.and(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), In.nrd(p, b, m, D.Fd(3n, m, r), F, N)), hn)
          +hp = Bo.and_r(In.rd(r, F, N), Bool.and(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), In.nrd(p, b, m, D.Fd(3n, m, r), F, N)), hn)
          +ha = Bo.and_l(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), In.nrd(p, b, m, D.Fd(3n, m, r), F, N), hp)
          +ra = Bo.and_r(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), In.nrd(p, b, m, D.Fd(3n, m, r), F, N), hp)
          Bo.and_i(In.rd(r, F, 1n+N), Bool.and(In.nrd(p, a, m, D.Fd(2n, m, r), F, 1n+N), In.nrd(p, b, m, D.Fd(3n, m, r), F, 1n+N)), In.rd_up(r, F, N, hr), Bo.and_i(In.nrd(p, a, m, D.Fd(2n, m, r), F, 1n+N), In.nrd(p, b, m, D.Fd(3n, m, r), F, 1n+N), In.nup(p, a, m, D.Fd(2n, m, r), F, N, ha), In.nup(p, b, m, D.Fd(3n, m, r), F, N, ra)))
        case Bk.Term.Lam{_, +g}:
          +hr = Bo.and_l(In.rd(r, F, N), In.nrd(p, g, m, D.Fd(2n, m, r), F, N), hn)
          +hp = Bo.and_r(In.rd(r, F, N), In.nrd(p, g, m, D.Fd(2n, m, r), F, N), hn)
          Bo.and_i(In.rd(r, F, 1n+N), In.nrd(p, g, m, D.Fd(2n, m, r), F, 1n+N), In.rd_up(r, F, N, hr), In.nup(p, g, m, D.Fd(2n, m, r), F, N, hp))
        case Bk.Term.App{_, +g, +y}:
          +hr = Bo.and_l(In.rd(r, F, N), Bool.and(In.nrd(p, g, m, D.Fd(2n, m, r), F, N), In.nrd(p, y, m, D.Fd(3n, m, r), F, N)), hn)
          +hp = Bo.and_r(In.rd(r, F, N), Bool.and(In.nrd(p, g, m, D.Fd(2n, m, r), F, N), In.nrd(p, y, m, D.Fd(3n, m, r), F, N)), hn)
          +hg = Bo.and_l(In.nrd(p, g, m, D.Fd(2n, m, r), F, N), In.nrd(p, y, m, D.Fd(3n, m, r), F, N), hp)
          +rg = Bo.and_r(In.nrd(p, g, m, D.Fd(2n, m, r), F, N), In.nrd(p, y, m, D.Fd(3n, m, r), F, N), hp)
          Bo.and_i(In.rd(r, F, 1n+N), Bool.and(In.nrd(p, g, m, D.Fd(2n, m, r), F, 1n+N), In.nrd(p, y, m, D.Fd(3n, m, r), F, 1n+N)), In.rd_up(r, F, N, hr), Bo.and_i(In.nrd(p, g, m, D.Fd(2n, m, r), F, 1n+N), In.nrd(p, y, m, D.Fd(3n, m, r), F, 1n+N), In.nup(p, g, m, D.Fd(2n, m, r), F, N, hg), In.nup(p, y, m, D.Fd(3n, m, r), F, N, rg)))
        case Bk.Term.Sig{_, +a, +b}:
          +hr = Bo.and_l(In.rd(r, F, N), Bool.and(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), In.nrd(p, b, m, D.Fd(3n, m, r), F, N)), hn)
          +hp = Bo.and_r(In.rd(r, F, N), Bool.and(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), In.nrd(p, b, m, D.Fd(3n, m, r), F, N)), hn)
          +ha = Bo.and_l(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), In.nrd(p, b, m, D.Fd(3n, m, r), F, N), hp)
          +ra = Bo.and_r(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), In.nrd(p, b, m, D.Fd(3n, m, r), F, N), hp)
          Bo.and_i(In.rd(r, F, 1n+N), Bool.and(In.nrd(p, a, m, D.Fd(2n, m, r), F, 1n+N), In.nrd(p, b, m, D.Fd(3n, m, r), F, 1n+N)), In.rd_up(r, F, N, hr), Bo.and_i(In.nrd(p, a, m, D.Fd(2n, m, r), F, 1n+N), In.nrd(p, b, m, D.Fd(3n, m, r), F, 1n+N), In.nup(p, a, m, D.Fd(2n, m, r), F, N, ha), In.nup(p, b, m, D.Fd(3n, m, r), F, N, ra)))
        case Bk.Term.Tup{_, +a, +b}:
          +hr = Bo.and_l(In.rd(r, F, N), Bool.and(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), In.nrd(p, b, m, D.Fd(3n, m, r), F, N)), hn)
          +hp = Bo.and_r(In.rd(r, F, N), Bool.and(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), In.nrd(p, b, m, D.Fd(3n, m, r), F, N)), hn)
          +ha = Bo.and_l(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), In.nrd(p, b, m, D.Fd(3n, m, r), F, N), hp)
          +ra = Bo.and_r(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), In.nrd(p, b, m, D.Fd(3n, m, r), F, N), hp)
          Bo.and_i(In.rd(r, F, 1n+N), Bool.and(In.nrd(p, a, m, D.Fd(2n, m, r), F, 1n+N), In.nrd(p, b, m, D.Fd(3n, m, r), F, 1n+N)), In.rd_up(r, F, N, hr), Bo.and_i(In.nrd(p, a, m, D.Fd(2n, m, r), F, 1n+N), In.nrd(p, b, m, D.Fd(3n, m, r), F, 1n+N), In.nup(p, a, m, D.Fd(2n, m, r), F, N, ha), In.nup(p, b, m, D.Fd(3n, m, r), F, N, ra)))
        case Bk.Term.Prj{+h}:
          +hr = Bo.and_l(In.rd(r, F, N), In.nrd(p, h, m, D.Fd(2n, m, r), F, N), hn)
          +hp = Bo.and_r(In.rd(r, F, N), In.nrd(p, h, m, D.Fd(2n, m, r), F, N), hn)
          Bo.and_i(In.rd(r, F, 1n+N), In.nrd(p, h, m, D.Fd(2n, m, r), F, 1n+N), In.rd_up(r, F, N, hr), In.nup(p, h, m, D.Fd(2n, m, r), F, N, hp))
        case Bk.Term.Enu{_}:
          In.rd_up(r, F, N, hn)
        case Bk.Term.Lab{_}:
          In.rd_up(r, F, N, hn)
        case Bk.Term.Mat{_, +h, +o}:
          +hr = Bo.and_l(In.rd(r, F, N), Bool.and(In.nrd(p, h, m, D.Fd(3n, m, r), F, N), In.nrd(p, o, m, D.Fd(4n, m, r), F, N)), hn)
          +hp = Bo.and_r(In.rd(r, F, N), Bool.and(In.nrd(p, h, m, D.Fd(3n, m, r), F, N), In.nrd(p, o, m, D.Fd(4n, m, r), F, N)), hn)
          +hh = Bo.and_l(In.nrd(p, h, m, D.Fd(3n, m, r), F, N), In.nrd(p, o, m, D.Fd(4n, m, r), F, N), hp)
          +rh = Bo.and_r(In.nrd(p, h, m, D.Fd(3n, m, r), F, N), In.nrd(p, o, m, D.Fd(4n, m, r), F, N), hp)
          Bo.and_i(In.rd(r, F, 1n+N), Bool.and(In.nrd(p, h, m, D.Fd(3n, m, r), F, 1n+N), In.nrd(p, o, m, D.Fd(4n, m, r), F, 1n+N)), In.rd_up(r, F, N, hr), Bo.and_i(In.nrd(p, h, m, D.Fd(3n, m, r), F, 1n+N), In.nrd(p, o, m, D.Fd(4n, m, r), F, 1n+N), In.nup(p, h, m, D.Fd(3n, m, r), F, N, hh), In.nup(p, o, m, D.Fd(4n, m, r), F, N, rh)))
        case Bk.Term.Efq{}:
          In.rd_up(r, F, N, hn)
        case Bk.Term.Eql{+a, +b, +y}:
          +hr = Bo.and_l(In.rd(r, F, N), Bool.and(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), Bool.and(In.nrd(p, b, m, D.Fd(3n, m, r), F, N), In.nrd(p, y, m, D.Fd(4n, m, r), F, N))), hn)
          +hp = Bo.and_r(In.rd(r, F, N), Bool.and(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), Bool.and(In.nrd(p, b, m, D.Fd(3n, m, r), F, N), In.nrd(p, y, m, D.Fd(4n, m, r), F, N))), hn)
          +ha = Bo.and_l(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), Bool.and(In.nrd(p, b, m, D.Fd(3n, m, r), F, N), In.nrd(p, y, m, D.Fd(4n, m, r), F, N)), hp)
          +ra = Bo.and_r(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), Bool.and(In.nrd(p, b, m, D.Fd(3n, m, r), F, N), In.nrd(p, y, m, D.Fd(4n, m, r), F, N)), hp)
          +hb = Bo.and_l(In.nrd(p, b, m, D.Fd(3n, m, r), F, N), In.nrd(p, y, m, D.Fd(4n, m, r), F, N), ra)
          +rb = Bo.and_r(In.nrd(p, b, m, D.Fd(3n, m, r), F, N), In.nrd(p, y, m, D.Fd(4n, m, r), F, N), ra)
          Bo.and_i(In.rd(r, F, 1n+N), Bool.and(In.nrd(p, a, m, D.Fd(2n, m, r), F, 1n+N), Bool.and(In.nrd(p, b, m, D.Fd(3n, m, r), F, 1n+N), In.nrd(p, y, m, D.Fd(4n, m, r), F, 1n+N))), In.rd_up(r, F, N, hr), Bo.and_i(In.nrd(p, a, m, D.Fd(2n, m, r), F, 1n+N), Bool.and(In.nrd(p, b, m, D.Fd(3n, m, r), F, 1n+N), In.nrd(p, y, m, D.Fd(4n, m, r), F, 1n+N)), In.nup(p, a, m, D.Fd(2n, m, r), F, N, ha), Bo.and_i(In.nrd(p, b, m, D.Fd(3n, m, r), F, 1n+N), In.nrd(p, y, m, D.Fd(4n, m, r), F, 1n+N), In.nup(p, b, m, D.Fd(3n, m, r), F, N, hb), In.nup(p, y, m, D.Fd(4n, m, r), F, N, rb))))
        case Bk.Term.Rfl{}:
          In.rd_up(r, F, N, hn)
        case Bk.Term.Rwt{+w, +y, +g}:
          +hr = Bo.and_l(In.rd(r, F, N), Bool.and(In.nrd(p, w, m, D.Fd(2n, m, r), F, N), Bool.and(In.nrd(p, y, m, D.Fd(3n, m, r), F, N), In.nrd(p, g, m, D.Fd(4n, m, r), F, N))), hn)
          +hp = Bo.and_r(In.rd(r, F, N), Bool.and(In.nrd(p, w, m, D.Fd(2n, m, r), F, N), Bool.and(In.nrd(p, y, m, D.Fd(3n, m, r), F, N), In.nrd(p, g, m, D.Fd(4n, m, r), F, N))), hn)
          +hw = Bo.and_l(In.nrd(p, w, m, D.Fd(2n, m, r), F, N), Bool.and(In.nrd(p, y, m, D.Fd(3n, m, r), F, N), In.nrd(p, g, m, D.Fd(4n, m, r), F, N)), hp)
          +rw = Bo.and_r(In.nrd(p, w, m, D.Fd(2n, m, r), F, N), Bool.and(In.nrd(p, y, m, D.Fd(3n, m, r), F, N), In.nrd(p, g, m, D.Fd(4n, m, r), F, N)), hp)
          +hy = Bo.and_l(In.nrd(p, y, m, D.Fd(3n, m, r), F, N), In.nrd(p, g, m, D.Fd(4n, m, r), F, N), rw)
          +ry = Bo.and_r(In.nrd(p, y, m, D.Fd(3n, m, r), F, N), In.nrd(p, g, m, D.Fd(4n, m, r), F, N), rw)
          Bo.and_i(In.rd(r, F, 1n+N), Bool.and(In.nrd(p, w, m, D.Fd(2n, m, r), F, 1n+N), Bool.and(In.nrd(p, y, m, D.Fd(3n, m, r), F, 1n+N), In.nrd(p, g, m, D.Fd(4n, m, r), F, 1n+N))), In.rd_up(r, F, N, hr), Bo.and_i(In.nrd(p, w, m, D.Fd(2n, m, r), F, 1n+N), Bool.and(In.nrd(p, y, m, D.Fd(3n, m, r), F, 1n+N), In.nrd(p, g, m, D.Fd(4n, m, r), F, 1n+N)), In.nup(p, w, m, D.Fd(2n, m, r), F, N, hw), Bo.and_i(In.nrd(p, y, m, D.Fd(3n, m, r), F, 1n+N), In.nrd(p, g, m, D.Fd(4n, m, r), F, 1n+N), In.nup(p, y, m, D.Fd(3n, m, r), F, N, hy), In.nup(p, g, m, D.Fd(4n, m, r), F, N, ry))))

# and with one more unit of fuel
def In.nmono(f: Nat, t: Bk.Term, +m: Cr.Cir.Cells, +r: U32, +F: U32, +N: Nat, +hn: {True{} == In.nrd(f, t, m, r, F, N) : Bool}) ->
  {True{} == In.nrd(1n+f, t, m, r, F, N) : Bool}:
  match f:
    case 0n:
      Bo.ft({True{} == In.nrd(1n, t, m, r, F, N) : Bool}, hn)
    case 1n+(+p):
      match t:
        case Bk.Term.Var{_}:
          hn
        case Bk.Term.Ref{_}:
          hn
        case Bk.Term.Ann{+y, +z}:
          +hr = Bo.and_l(In.rd(r, F, N), Bool.and(In.nrd(p, y, m, D.Fd(2n, m, r), F, N), In.nrd(p, z, m, D.Fd(3n, m, r), F, N)), hn)
          +hp = Bo.and_r(In.rd(r, F, N), Bool.and(In.nrd(p, y, m, D.Fd(2n, m, r), F, N), In.nrd(p, z, m, D.Fd(3n, m, r), F, N)), hn)
          +hy = Bo.and_l(In.nrd(p, y, m, D.Fd(2n, m, r), F, N), In.nrd(p, z, m, D.Fd(3n, m, r), F, N), hp)
          +ry = Bo.and_r(In.nrd(p, y, m, D.Fd(2n, m, r), F, N), In.nrd(p, z, m, D.Fd(3n, m, r), F, N), hp)
          Bo.and_i(In.rd(r, F, N), Bool.and(In.nrd(1n+p, y, m, D.Fd(2n, m, r), F, N), In.nrd(1n+p, z, m, D.Fd(3n, m, r), F, N)), hr, Bo.and_i(In.nrd(1n+p, y, m, D.Fd(2n, m, r), F, N), In.nrd(1n+p, z, m, D.Fd(3n, m, r), F, N), In.nmono(p, y, m, D.Fd(2n, m, r), F, N, hy), In.nmono(p, z, m, D.Fd(3n, m, r), F, N, ry)))
        case Bk.Term.Let{_, +v, +g}:
          +hr = Bo.and_l(In.rd(r, F, N), Bool.and(In.nrd(p, v, m, D.Fd(2n, m, r), F, N), In.nrd(p, g, m, D.Fd(3n, m, r), F, N)), hn)
          +hp = Bo.and_r(In.rd(r, F, N), Bool.and(In.nrd(p, v, m, D.Fd(2n, m, r), F, N), In.nrd(p, g, m, D.Fd(3n, m, r), F, N)), hn)
          +hv = Bo.and_l(In.nrd(p, v, m, D.Fd(2n, m, r), F, N), In.nrd(p, g, m, D.Fd(3n, m, r), F, N), hp)
          +rv = Bo.and_r(In.nrd(p, v, m, D.Fd(2n, m, r), F, N), In.nrd(p, g, m, D.Fd(3n, m, r), F, N), hp)
          Bo.and_i(In.rd(r, F, N), Bool.and(In.nrd(1n+p, v, m, D.Fd(2n, m, r), F, N), In.nrd(1n+p, g, m, D.Fd(3n, m, r), F, N)), hr, Bo.and_i(In.nrd(1n+p, v, m, D.Fd(2n, m, r), F, N), In.nrd(1n+p, g, m, D.Fd(3n, m, r), F, N), In.nmono(p, v, m, D.Fd(2n, m, r), F, N, hv), In.nmono(p, g, m, D.Fd(3n, m, r), F, N, rv)))
        case Bk.Term.Typ{+y}:
          +hr = Bo.and_l(In.rd(r, F, N), In.nrd(p, y, m, D.Fd(2n, m, r), F, N), hn)
          +hp = Bo.and_r(In.rd(r, F, N), In.nrd(p, y, m, D.Fd(2n, m, r), F, N), hn)
          Bo.and_i(In.rd(r, F, N), In.nrd(1n+p, y, m, D.Fd(2n, m, r), F, N), hr, In.nmono(p, y, m, D.Fd(2n, m, r), F, N, hp))
        case Bk.Term.Min{+a, +b}:
          +hr = Bo.and_l(In.rd(r, F, N), Bool.and(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), In.nrd(p, b, m, D.Fd(3n, m, r), F, N)), hn)
          +hp = Bo.and_r(In.rd(r, F, N), Bool.and(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), In.nrd(p, b, m, D.Fd(3n, m, r), F, N)), hn)
          +ha = Bo.and_l(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), In.nrd(p, b, m, D.Fd(3n, m, r), F, N), hp)
          +ra = Bo.and_r(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), In.nrd(p, b, m, D.Fd(3n, m, r), F, N), hp)
          Bo.and_i(In.rd(r, F, N), Bool.and(In.nrd(1n+p, a, m, D.Fd(2n, m, r), F, N), In.nrd(1n+p, b, m, D.Fd(3n, m, r), F, N)), hr, Bo.and_i(In.nrd(1n+p, a, m, D.Fd(2n, m, r), F, N), In.nrd(1n+p, b, m, D.Fd(3n, m, r), F, N), In.nmono(p, a, m, D.Fd(2n, m, r), F, N, ha), In.nmono(p, b, m, D.Fd(3n, m, r), F, N, ra)))
        case Bk.Term.All{_, +a, +b}:
          +hr = Bo.and_l(In.rd(r, F, N), Bool.and(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), In.nrd(p, b, m, D.Fd(3n, m, r), F, N)), hn)
          +hp = Bo.and_r(In.rd(r, F, N), Bool.and(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), In.nrd(p, b, m, D.Fd(3n, m, r), F, N)), hn)
          +ha = Bo.and_l(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), In.nrd(p, b, m, D.Fd(3n, m, r), F, N), hp)
          +ra = Bo.and_r(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), In.nrd(p, b, m, D.Fd(3n, m, r), F, N), hp)
          Bo.and_i(In.rd(r, F, N), Bool.and(In.nrd(1n+p, a, m, D.Fd(2n, m, r), F, N), In.nrd(1n+p, b, m, D.Fd(3n, m, r), F, N)), hr, Bo.and_i(In.nrd(1n+p, a, m, D.Fd(2n, m, r), F, N), In.nrd(1n+p, b, m, D.Fd(3n, m, r), F, N), In.nmono(p, a, m, D.Fd(2n, m, r), F, N, ha), In.nmono(p, b, m, D.Fd(3n, m, r), F, N, ra)))
        case Bk.Term.Lam{_, +g}:
          +hr = Bo.and_l(In.rd(r, F, N), In.nrd(p, g, m, D.Fd(2n, m, r), F, N), hn)
          +hp = Bo.and_r(In.rd(r, F, N), In.nrd(p, g, m, D.Fd(2n, m, r), F, N), hn)
          Bo.and_i(In.rd(r, F, N), In.nrd(1n+p, g, m, D.Fd(2n, m, r), F, N), hr, In.nmono(p, g, m, D.Fd(2n, m, r), F, N, hp))
        case Bk.Term.App{_, +g, +y}:
          +hr = Bo.and_l(In.rd(r, F, N), Bool.and(In.nrd(p, g, m, D.Fd(2n, m, r), F, N), In.nrd(p, y, m, D.Fd(3n, m, r), F, N)), hn)
          +hp = Bo.and_r(In.rd(r, F, N), Bool.and(In.nrd(p, g, m, D.Fd(2n, m, r), F, N), In.nrd(p, y, m, D.Fd(3n, m, r), F, N)), hn)
          +hg = Bo.and_l(In.nrd(p, g, m, D.Fd(2n, m, r), F, N), In.nrd(p, y, m, D.Fd(3n, m, r), F, N), hp)
          +rg = Bo.and_r(In.nrd(p, g, m, D.Fd(2n, m, r), F, N), In.nrd(p, y, m, D.Fd(3n, m, r), F, N), hp)
          Bo.and_i(In.rd(r, F, N), Bool.and(In.nrd(1n+p, g, m, D.Fd(2n, m, r), F, N), In.nrd(1n+p, y, m, D.Fd(3n, m, r), F, N)), hr, Bo.and_i(In.nrd(1n+p, g, m, D.Fd(2n, m, r), F, N), In.nrd(1n+p, y, m, D.Fd(3n, m, r), F, N), In.nmono(p, g, m, D.Fd(2n, m, r), F, N, hg), In.nmono(p, y, m, D.Fd(3n, m, r), F, N, rg)))
        case Bk.Term.Sig{_, +a, +b}:
          +hr = Bo.and_l(In.rd(r, F, N), Bool.and(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), In.nrd(p, b, m, D.Fd(3n, m, r), F, N)), hn)
          +hp = Bo.and_r(In.rd(r, F, N), Bool.and(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), In.nrd(p, b, m, D.Fd(3n, m, r), F, N)), hn)
          +ha = Bo.and_l(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), In.nrd(p, b, m, D.Fd(3n, m, r), F, N), hp)
          +ra = Bo.and_r(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), In.nrd(p, b, m, D.Fd(3n, m, r), F, N), hp)
          Bo.and_i(In.rd(r, F, N), Bool.and(In.nrd(1n+p, a, m, D.Fd(2n, m, r), F, N), In.nrd(1n+p, b, m, D.Fd(3n, m, r), F, N)), hr, Bo.and_i(In.nrd(1n+p, a, m, D.Fd(2n, m, r), F, N), In.nrd(1n+p, b, m, D.Fd(3n, m, r), F, N), In.nmono(p, a, m, D.Fd(2n, m, r), F, N, ha), In.nmono(p, b, m, D.Fd(3n, m, r), F, N, ra)))
        case Bk.Term.Tup{_, +a, +b}:
          +hr = Bo.and_l(In.rd(r, F, N), Bool.and(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), In.nrd(p, b, m, D.Fd(3n, m, r), F, N)), hn)
          +hp = Bo.and_r(In.rd(r, F, N), Bool.and(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), In.nrd(p, b, m, D.Fd(3n, m, r), F, N)), hn)
          +ha = Bo.and_l(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), In.nrd(p, b, m, D.Fd(3n, m, r), F, N), hp)
          +ra = Bo.and_r(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), In.nrd(p, b, m, D.Fd(3n, m, r), F, N), hp)
          Bo.and_i(In.rd(r, F, N), Bool.and(In.nrd(1n+p, a, m, D.Fd(2n, m, r), F, N), In.nrd(1n+p, b, m, D.Fd(3n, m, r), F, N)), hr, Bo.and_i(In.nrd(1n+p, a, m, D.Fd(2n, m, r), F, N), In.nrd(1n+p, b, m, D.Fd(3n, m, r), F, N), In.nmono(p, a, m, D.Fd(2n, m, r), F, N, ha), In.nmono(p, b, m, D.Fd(3n, m, r), F, N, ra)))
        case Bk.Term.Prj{+h}:
          +hr = Bo.and_l(In.rd(r, F, N), In.nrd(p, h, m, D.Fd(2n, m, r), F, N), hn)
          +hp = Bo.and_r(In.rd(r, F, N), In.nrd(p, h, m, D.Fd(2n, m, r), F, N), hn)
          Bo.and_i(In.rd(r, F, N), In.nrd(1n+p, h, m, D.Fd(2n, m, r), F, N), hr, In.nmono(p, h, m, D.Fd(2n, m, r), F, N, hp))
        case Bk.Term.Enu{_}:
          hn
        case Bk.Term.Lab{_}:
          hn
        case Bk.Term.Mat{_, +h, +o}:
          +hr = Bo.and_l(In.rd(r, F, N), Bool.and(In.nrd(p, h, m, D.Fd(3n, m, r), F, N), In.nrd(p, o, m, D.Fd(4n, m, r), F, N)), hn)
          +hp = Bo.and_r(In.rd(r, F, N), Bool.and(In.nrd(p, h, m, D.Fd(3n, m, r), F, N), In.nrd(p, o, m, D.Fd(4n, m, r), F, N)), hn)
          +hh = Bo.and_l(In.nrd(p, h, m, D.Fd(3n, m, r), F, N), In.nrd(p, o, m, D.Fd(4n, m, r), F, N), hp)
          +rh = Bo.and_r(In.nrd(p, h, m, D.Fd(3n, m, r), F, N), In.nrd(p, o, m, D.Fd(4n, m, r), F, N), hp)
          Bo.and_i(In.rd(r, F, N), Bool.and(In.nrd(1n+p, h, m, D.Fd(3n, m, r), F, N), In.nrd(1n+p, o, m, D.Fd(4n, m, r), F, N)), hr, Bo.and_i(In.nrd(1n+p, h, m, D.Fd(3n, m, r), F, N), In.nrd(1n+p, o, m, D.Fd(4n, m, r), F, N), In.nmono(p, h, m, D.Fd(3n, m, r), F, N, hh), In.nmono(p, o, m, D.Fd(4n, m, r), F, N, rh)))
        case Bk.Term.Efq{}:
          hn
        case Bk.Term.Eql{+a, +b, +y}:
          +hr = Bo.and_l(In.rd(r, F, N), Bool.and(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), Bool.and(In.nrd(p, b, m, D.Fd(3n, m, r), F, N), In.nrd(p, y, m, D.Fd(4n, m, r), F, N))), hn)
          +hp = Bo.and_r(In.rd(r, F, N), Bool.and(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), Bool.and(In.nrd(p, b, m, D.Fd(3n, m, r), F, N), In.nrd(p, y, m, D.Fd(4n, m, r), F, N))), hn)
          +ha = Bo.and_l(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), Bool.and(In.nrd(p, b, m, D.Fd(3n, m, r), F, N), In.nrd(p, y, m, D.Fd(4n, m, r), F, N)), hp)
          +ra = Bo.and_r(In.nrd(p, a, m, D.Fd(2n, m, r), F, N), Bool.and(In.nrd(p, b, m, D.Fd(3n, m, r), F, N), In.nrd(p, y, m, D.Fd(4n, m, r), F, N)), hp)
          +hb = Bo.and_l(In.nrd(p, b, m, D.Fd(3n, m, r), F, N), In.nrd(p, y, m, D.Fd(4n, m, r), F, N), ra)
          +rb = Bo.and_r(In.nrd(p, b, m, D.Fd(3n, m, r), F, N), In.nrd(p, y, m, D.Fd(4n, m, r), F, N), ra)
          Bo.and_i(In.rd(r, F, N), Bool.and(In.nrd(1n+p, a, m, D.Fd(2n, m, r), F, N), Bool.and(In.nrd(1n+p, b, m, D.Fd(3n, m, r), F, N), In.nrd(1n+p, y, m, D.Fd(4n, m, r), F, N))), hr, Bo.and_i(In.nrd(1n+p, a, m, D.Fd(2n, m, r), F, N), Bool.and(In.nrd(1n+p, b, m, D.Fd(3n, m, r), F, N), In.nrd(1n+p, y, m, D.Fd(4n, m, r), F, N)), In.nmono(p, a, m, D.Fd(2n, m, r), F, N, ha), Bo.and_i(In.nrd(1n+p, b, m, D.Fd(3n, m, r), F, N), In.nrd(1n+p, y, m, D.Fd(4n, m, r), F, N), In.nmono(p, b, m, D.Fd(3n, m, r), F, N, hb), In.nmono(p, y, m, D.Fd(4n, m, r), F, N, rb))))
        case Bk.Term.Rfl{}:
          hn
        case Bk.Term.Rwt{+w, +y, +g}:
          +hr = Bo.and_l(In.rd(r, F, N), Bool.and(In.nrd(p, w, m, D.Fd(2n, m, r), F, N), Bool.and(In.nrd(p, y, m, D.Fd(3n, m, r), F, N), In.nrd(p, g, m, D.Fd(4n, m, r), F, N))), hn)
          +hp = Bo.and_r(In.rd(r, F, N), Bool.and(In.nrd(p, w, m, D.Fd(2n, m, r), F, N), Bool.and(In.nrd(p, y, m, D.Fd(3n, m, r), F, N), In.nrd(p, g, m, D.Fd(4n, m, r), F, N))), hn)
          +hw = Bo.and_l(In.nrd(p, w, m, D.Fd(2n, m, r), F, N), Bool.and(In.nrd(p, y, m, D.Fd(3n, m, r), F, N), In.nrd(p, g, m, D.Fd(4n, m, r), F, N)), hp)
          +rw = Bo.and_r(In.nrd(p, w, m, D.Fd(2n, m, r), F, N), Bool.and(In.nrd(p, y, m, D.Fd(3n, m, r), F, N), In.nrd(p, g, m, D.Fd(4n, m, r), F, N)), hp)
          +hy = Bo.and_l(In.nrd(p, y, m, D.Fd(3n, m, r), F, N), In.nrd(p, g, m, D.Fd(4n, m, r), F, N), rw)
          +ry = Bo.and_r(In.nrd(p, y, m, D.Fd(3n, m, r), F, N), In.nrd(p, g, m, D.Fd(4n, m, r), F, N), rw)
          Bo.and_i(In.rd(r, F, N), Bool.and(In.nrd(1n+p, w, m, D.Fd(2n, m, r), F, N), Bool.and(In.nrd(1n+p, y, m, D.Fd(3n, m, r), F, N), In.nrd(1n+p, g, m, D.Fd(4n, m, r), F, N))), hr, Bo.and_i(In.nrd(1n+p, w, m, D.Fd(2n, m, r), F, N), Bool.and(In.nrd(1n+p, y, m, D.Fd(3n, m, r), F, N), In.nrd(1n+p, g, m, D.Fd(4n, m, r), F, N)), In.nmono(p, w, m, D.Fd(2n, m, r), F, N, hw), Bo.and_i(In.nrd(1n+p, y, m, D.Fd(3n, m, r), F, N), In.nrd(1n+p, g, m, D.Fd(4n, m, r), F, N), In.nmono(p, y, m, D.Fd(3n, m, r), F, N, hy), In.nmono(p, g, m, D.Fd(4n, m, r), F, N, ry))))


# Terms of cells
# --------------

# the cell c of the cells m stands for t with the fuel f, reading only cells
# that may be read (F and N bound the machine's own), and so are t's nodes
def In.St(f: Nat, +m: Cr.Cir.Cells, +F: U32, +N: Nat, +c: U32, +t: Bk.Term, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>) -> Data:
  In.P({Some{t} == T.tm.of(f, m, ks, img, c) : Maybe<&2, Bk.Term>},
    In.P({True{} == In.rds(f, m, F, N, c) : Bool}, {True{} == In.nrd(f, t, m, c, F, N) : Bool}))

# the nodes' part of St
def St.nrd(-f: Nat, -m: Cr.Cir.Cells, -F: U32, -N: Nat, -c: U32, -t: Bk.Term, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>,
  s: In.St(f, m, F, N, c, t, ks, img)) -> {True{} == In.nrd(f, t, m, c, F, N) : Bool}:
  (e, rn) = s
  (r, n) = rn
  n

# a cell that may not be read is set
def St.fr(+f: Nat, +m: Cr.Cir.Cells, +F: U32, +N: Nat, +c: U32, +t: Bk.Term, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +i: U32, +x: Cr.Cir.Cell, +hi: {False{} == In.rd(i, F, N) : Bool}, s: In.St(f, m, F, N, c, t, ks, img)) ->
  In.St(f, Cr.Cir.Cells.set(m, i, x), F, N, c, t, ks, img):
  (e, rn) = s
  (r, n) = rn
  +q = In.fr(f, m, F, N, c, i, x, ks, img, r, hi)
  (Equal.trans(Maybe<&2, Bk.Term>, Some{t}, T.tm.of(f, m, ks, img, c), T.tm.of(f, Cr.Cir.Cells.set(m, i, x), ks, img, c), e,
    In.p1({T.tm.of(f, m, ks, img, c) == T.tm.of(f, Cr.Cir.Cells.set(m, i, x), ks, img, c) : Maybe<&2, Bk.Term>},
      {True{} == In.rds(f, Cr.Cir.Cells.set(m, i, x), F, N, c) : Bool}, q)),
   (In.p2({T.tm.of(f, m, ks, img, c) == T.tm.of(f, Cr.Cir.Cells.set(m, i, x), ks, img, c) : Maybe<&2, Bk.Term>},
      {True{} == In.rds(f, Cr.Cir.Cells.set(m, i, x), F, N, c) : Bool}, q),
    In.p1({True{} == In.nrd(f, t, Cr.Cir.Cells.set(m, i, x), c, F, N) : Bool}, {D.Node(t, m, c, c) == D.Node(t, Cr.Cir.Cells.set(m, i, x), c, c) : Bool},
      In.nfr(f, t, m, c, c, i, x, F, N, n, hi))))

# one more cell is taken
def St.up(+f: Nat, +m: Cr.Cir.Cells, +F: U32, +N: Nat, +c: U32, +t: Bk.Term, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  s: In.St(f, m, F, N, c, t, ks, img)) -> In.St(f, m, F, 1n+N, c, t, ks, img):
  (e, rn) = s
  (r, n) = rn
  (e, (In.up(f, m, F, N, c, r), In.nup(f, t, m, c, F, N, n)))

# one more unit of fuel
def St.mono(+f: Nat, +m: Cr.Cir.Cells, +F: U32, +N: Nat, +c: U32, +t: Bk.Term, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  s: In.St(f, m, F, N, c, t, ks, img)) -> In.St(1n+f, m, F, N, c, t, ks, img):
  (e, rn) = s
  (r, n) = rn
  +q = In.mono(f, m, F, N, c, ks, img, r)
  (Equal.trans(Maybe<&2, Bk.Term>, Some{t}, T.tm.of(f, m, ks, img, c), T.tm.of(1n+f, m, ks, img, c), e,
    In.p1({T.tm.of(f, m, ks, img, c) == T.tm.of(1n+f, m, ks, img, c) : Maybe<&2, Bk.Term>},
      {True{} == In.rds(1n+f, m, F, N, c) : Bool}, q)),
   (In.p2({T.tm.of(f, m, ks, img, c) == T.tm.of(1n+f, m, ks, img, c) : Maybe<&2, Bk.Term>},
      {True{} == In.rds(1n+f, m, F, N, c) : Bool}, q), In.nmono(f, t, m, c, F, N, n)))

# more fuel
def St.add(d: Nat, +f: Nat, +m: Cr.Cir.Cells, +F: U32, +N: Nat, +c: U32, +t: Bk.Term, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  s: In.St(f, m, F, N, c, t, ks, img)) -> In.St(Nat.add(d, f), m, F, N, c, t, ks, img):
  match d:
    case 0n:
      s
    case 1n+(+p):
      St.mono(Nat.add(p, f), m, F, N, c, t, ks, img, St.add(p, f, m, F, N, c, t, ks, img, s))

# (g - f) + f = g, when f <= g
def Na.sub_add(g: Nat, f: Nat, h: N.Le(f, g)) -> {g == Nat.add(Nat.sub(g, f), f) : Nat}:
  match g f:
    case 0n 0n:
      {==}
    case 0n 1n+a:
      Empty.absurd({0n == Nat.add(Nat.sub(0n, 1n+a), 1n+a) : Nat}, h)
    case 1n+b 0n:
      Equal.sym(Nat, Nat.add(1n+b, 0n), 1n+b, N.add_zero(1n+b))
    case 1n+(+b) 1n+(+a):
      %Equal.sym(Nat, Nat.add(Nat.sub(b, a), 1n+a), 1n+Nat.add(Nat.sub(b, a), a), N.add_succ_r(Nat.sub(b, a), a)) : {1n+b == _ : Nat}
      Equal.cong(Nat, Nat, x => 1n+x, b, Nat.add(Nat.sub(b, a), a), Na.sub_add(b, a, h))

# any more fuel
def St.to(+f: Nat, +g: Nat, h: N.Le(f, g), +m: Cr.Cir.Cells, +F: U32, +N: Nat, +c: U32, +t: Bk.Term, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, s: In.St(f, m, F, N, c, t, ks, img)) -> In.St(g, m, F, N, c, t, ks, img):
  %Equal.sym(Nat, g, Nat.add(Nat.sub(g, f), f), Na.sub_add(g, f, h)) : In.St(_, m, F, N, c, t, ks, img)
  St.add(Nat.sub(g, f), f, m, F, N, c, t, ks, img, s)

# St's claim with the cell cl at c, once a unit of fuel is spent
def In.St.after(+f: Nat, +ms: Cr.Cir.Cells, +F: U32, +N: Nat, +c: U32, +cl: Cr.Cir.Cell, +t: Bk.Term, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>) -> Data:
  In.P({Some{t} == T.tm.cell(U32.to_nat(U32.and(Cr.Cir.Cell.get(0n, cl), 63)), T.tm.quan(U32.and(U32.shrn(Cr.Cir.Cell.get(0n, cl), 6n), 3)), c,
      Cr.Cir.Cell.get(2n, cl), ks, img, u => T.tm.of(f, ms, ks, img, Cr.Cir.Cell.get(2n, cl)), u => T.tm.of(f, ms, ks, img, Cr.Cir.Cell.get(3n, cl)),
      u => T.tm.of(f, ms, ks, img, Cr.Cir.Cell.get(4n, cl))) : Maybe<&2, Bk.Term>},
    In.P({True{} == Bool.and(In.rd(c, F, N), In.rds.cell(U32.to_nat(U32.and(Cr.Cir.Cell.get(0n, cl), 63)),
      u => In.rds(f, ms, F, N, Cr.Cir.Cell.get(2n, cl)), u => In.rds(f, ms, F, N, Cr.Cir.Cell.get(3n, cl)))) : Bool},
      {True{} == In.nrd(1n+f, t, ms, c, F, N) : Bool}))

# a cell of two parts, at the quantity 1 (Tup, App), with its parts' terms
def In.two.go(+hd: U32, +f: Nat, +m: Cr.Cir.Cells, +F: U32, +N: Nat, +i: U32, +p: U32, +q: U32, +t: Bk.Term, +tp: Bk.Term, +tq: Bk.Term,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  ep: {Some{tp} == T.tm.of(f, Cr.Cir.Cells.set(m, i, Cr.Cir.Cell{hd, 1, p, q, 0}), ks, img, p) : Maybe<&2, Bk.Term>},
  rp: {True{} == In.rds(f, Cr.Cir.Cells.set(m, i, Cr.Cir.Cell{hd, 1, p, q, 0}), F, 1n+N, p) : Bool},
  eq: {Some{tq} == T.tm.of(f, Cr.Cir.Cells.set(m, i, Cr.Cir.Cell{hd, 1, p, q, 0}), ks, img, q) : Maybe<&2, Bk.Term>},
  rq: {True{} == In.rds(f, Cr.Cir.Cells.set(m, i, Cr.Cir.Cell{hd, 1, p, q, 0}), F, 1n+N, q) : Bool},
  hr: {True{} == In.rd(i, F, 1n+N) : Bool},
  et: {Some{t} == T.tm.cell(U32.to_nat(U32.and(hd, 63)), T.tm.quan(U32.and(U32.shrn(hd, 6n), 3)), i, p, ks, img, u => Some{tp}, u => Some{tq},
    u => T.tm.of(f, Cr.Cir.Cells.set(m, i, Cr.Cir.Cell{hd, 1, p, q, 0}), ks, img, 0)) : Maybe<&2, Bk.Term>},
  er: {True{} == In.rds.cell(U32.to_nat(U32.and(hd, 63)), u => True{}, u => True{}) : Bool},
  en: {True{} == In.nrd(1n+f, t, Cr.Cir.Cells.set(m, i, Cr.Cir.Cell{hd, 1, p, q, 0}), i, F, 1n+N) : Bool}) ->
  In.St(1n+f, Cr.Cir.Cells.set(m, i, Cr.Cir.Cell{hd, 1, p, q, 0}), F, 1n+N, i, t, ks, img):
  +ms = Cr.Cir.Cells.set(m, i, Cr.Cir.Cell{hd, 1, p, q, 0})
  %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(ms, i), Cr.Cir.Cell{hd, 1, p, q, 0}, Cl.get_set(m, i, Cr.Cir.Cell{hd, 1, p, q, 0})) :
    In.St.after(f, ms, F, 1n+N, i, _, t, ks, img)
  %ep : In.P({Some{t} == T.tm.cell(U32.to_nat(U32.and(hd, 63)), T.tm.quan(U32.and(U32.shrn(hd, 6n), 3)), i, p, ks, img, u => _, u => T.tm.of(f, ms, ks, img, q), u => T.tm.of(f, ms, ks, img, 0)) : Maybe<&2, Bk.Term>},
      In.P({True{} == Bool.and(In.rd(i, F, 1n+N), In.rds.cell(U32.to_nat(U32.and(hd, 63)), u => In.rds(f, ms, F, 1n+N, p), u => In.rds(f, ms, F, 1n+N, q))) : Bool}, {True{} == In.nrd(1n+f, t, ms, i, F, 1n+N) : Bool}))
  %eq : In.P({Some{t} == T.tm.cell(U32.to_nat(U32.and(hd, 63)), T.tm.quan(U32.and(U32.shrn(hd, 6n), 3)), i, p, ks, img, u => Some{tp}, u => _, u => T.tm.of(f, ms, ks, img, 0)) : Maybe<&2, Bk.Term>},
      In.P({True{} == Bool.and(In.rd(i, F, 1n+N), In.rds.cell(U32.to_nat(U32.and(hd, 63)), u => In.rds(f, ms, F, 1n+N, p), u => In.rds(f, ms, F, 1n+N, q))) : Bool}, {True{} == In.nrd(1n+f, t, ms, i, F, 1n+N) : Bool}))
  %rp : In.P({Some{t} == T.tm.cell(U32.to_nat(U32.and(hd, 63)), T.tm.quan(U32.and(U32.shrn(hd, 6n), 3)), i, p, ks, img, u => Some{tp}, u => Some{tq}, u => T.tm.of(f, ms, ks, img, 0)) : Maybe<&2, Bk.Term>},
      In.P({True{} == Bool.and(In.rd(i, F, 1n+N), In.rds.cell(U32.to_nat(U32.and(hd, 63)), u => _, u => In.rds(f, ms, F, 1n+N, q))) : Bool}, {True{} == In.nrd(1n+f, t, ms, i, F, 1n+N) : Bool}))
  %rq : In.P({Some{t} == T.tm.cell(U32.to_nat(U32.and(hd, 63)), T.tm.quan(U32.and(U32.shrn(hd, 6n), 3)), i, p, ks, img, u => Some{tp}, u => Some{tq}, u => T.tm.of(f, ms, ks, img, 0)) : Maybe<&2, Bk.Term>},
      In.P({True{} == Bool.and(In.rd(i, F, 1n+N), In.rds.cell(U32.to_nat(U32.and(hd, 63)), u => True{}, u => _)) : Bool}, {True{} == In.nrd(1n+f, t, ms, i, F, 1n+N) : Bool}))
  %hr : In.P({Some{t} == T.tm.cell(U32.to_nat(U32.and(hd, 63)), T.tm.quan(U32.and(U32.shrn(hd, 6n), 3)), i, p, ks, img, u => Some{tp}, u => Some{tq}, u => T.tm.of(f, ms, ks, img, 0)) : Maybe<&2, Bk.Term>},
      In.P({True{} == Bool.and(_, In.rds.cell(U32.to_nat(U32.and(hd, 63)), u => True{}, u => True{})) : Bool}, {True{} == In.nrd(1n+f, t, ms, i, F, 1n+N) : Bool}))
  (et, (er, en))

def In.two.of(+hd: U32, +f: Nat, +m: Cr.Cir.Cells, +F: U32, +N: Nat, +i: U32, +p: U32, +q: U32, +t: Bk.Term, +tp: Bk.Term, +tq: Bk.Term,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  sp: In.St(f, Cr.Cir.Cells.set(m, i, Cr.Cir.Cell{hd, 1, p, q, 0}), F, 1n+N, p, tp, ks, img),
  sq: In.St(f, Cr.Cir.Cells.set(m, i, Cr.Cir.Cell{hd, 1, p, q, 0}), F, 1n+N, q, tq, ks, img),
  hr: {True{} == In.rd(i, F, 1n+N) : Bool},
  et: {Some{t} == T.tm.cell(U32.to_nat(U32.and(hd, 63)), T.tm.quan(U32.and(U32.shrn(hd, 6n), 3)), i, p, ks, img, u => Some{tp}, u => Some{tq},
    u => T.tm.of(f, Cr.Cir.Cells.set(m, i, Cr.Cir.Cell{hd, 1, p, q, 0}), ks, img, 0)) : Maybe<&2, Bk.Term>},
  er: {True{} == In.rds.cell(U32.to_nat(U32.and(hd, 63)), u => True{}, u => True{}) : Bool},
  en: {True{} == In.nrd(1n+f, t, Cr.Cir.Cells.set(m, i, Cr.Cir.Cell{hd, 1, p, q, 0}), i, F, 1n+N) : Bool}) ->
  In.St(1n+f, Cr.Cir.Cells.set(m, i, Cr.Cir.Cell{hd, 1, p, q, 0}), F, 1n+N, i, t, ks, img):
  (ep, rnp) = sp
  (rp, np) = rnp
  (eq, rnq) = sq
  (rq, nq) = rnq
  In.two.go(hd, f, m, F, N, i, p, q, t, tp, tq, ks, img, ep, rp, eq, rq, hr, et, er, en)

# a new cell i of two parts p and q (Tup or App at the quantity 1), which
# stand for tp and tq
def In.two(+hd: U32, +f: Nat, +m: Cr.Cir.Cells, +F: U32, +N: Nat, +i: U32, +p: U32, +q: U32, +t: Bk.Term, +tp: Bk.Term, +tq: Bk.Term,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  sp: In.St(f, m, F, N, p, tp, ks, img), sq: In.St(f, m, F, N, q, tq, ks, img),
  +hi: {False{} == In.rd(i, F, N) : Bool}, hr: {True{} == In.rd(i, F, 1n+N) : Bool},
  et: {Some{t} == T.tm.cell(U32.to_nat(U32.and(hd, 63)), T.tm.quan(U32.and(U32.shrn(hd, 6n), 3)), i, p, ks, img, u => Some{tp}, u => Some{tq},
    u => T.tm.of(f, Cr.Cir.Cells.set(m, i, Cr.Cir.Cell{hd, 1, p, q, 0}), ks, img, 0)) : Maybe<&2, Bk.Term>},
  er: {True{} == In.rds.cell(U32.to_nat(U32.and(hd, 63)), u => True{}, u => True{}) : Bool},
  en: {True{} == In.nrd(1n+f, t, Cr.Cir.Cells.set(m, i, Cr.Cir.Cell{hd, 1, p, q, 0}), i, F, 1n+N) : Bool}) ->
  In.St(1n+f, Cr.Cir.Cells.set(m, i, Cr.Cir.Cell{hd, 1, p, q, 0}), F, 1n+N, i, t, ks, img):
  +x = {Cr.Cir.Cell{hd, 1, p, q, 0} : Cr.Cir.Cell}
  +ms = Cr.Cir.Cells.set(m, i, x)
  In.two.of(hd, f, m, F, N, i, p, q, t, tp, tq, ks, img,
    St.up(f, ms, F, N, p, tp, ks, img, St.fr(f, m, F, N, p, tp, ks, img, i, x, hi, sp)),
    St.up(f, ms, F, N, q, tq, ks, img, St.fr(f, m, F, N, q, tq, ks, img, i, x, hi, sq)), hr, et, er, en)

# the nodes of a new cell i of the Tup of the parts p and q
def In.nrd.tup(+f: Nat, +hd: U32, +m: Cr.Cir.Cells, +F: U32, +N: Nat, +i: U32, +p: U32, +q: U32, +q0: Bk.Quan, +tp: Bk.Term, +tq: Bk.Term,
  hr: {True{} == In.rd(i, F, 1n+N) : Bool},
  np: {True{} == In.nrd(f, tp, Cr.Cir.Cells.set(m, i, Cr.Cir.Cell{hd, 1, p, q, 0}), p, F, 1n+N) : Bool},
  nq: {True{} == In.nrd(f, tq, Cr.Cir.Cells.set(m, i, Cr.Cir.Cell{hd, 1, p, q, 0}), q, F, 1n+N) : Bool}) ->
  {True{} == In.nrd(1n+f, Bk.Term.Tup{q0, tp, tq}, Cr.Cir.Cells.set(m, i, Cr.Cir.Cell{hd, 1, p, q, 0}), i, F, 1n+N) : Bool}:
  +ms = Cr.Cir.Cells.set(m, i, Cr.Cir.Cell{hd, 1, p, q, 0})
  %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(ms, i), Cr.Cir.Cell{hd, 1, p, q, 0}, Cl.get_set(m, i, Cr.Cir.Cell{hd, 1, p, q, 0})) :
    {True{} == Bool.and(In.rd(i, F, 1n+N), Bool.and(In.nrd(f, tp, ms, Cr.Cir.Cell.get(2n, _), F, 1n+N), In.nrd(f, tq, ms, Cr.Cir.Cell.get(3n, _), F, 1n+N))) : Bool}
  Bo.and_i(In.rd(i, F, 1n+N), Bool.and(In.nrd(f, tp, ms, p, F, 1n+N), In.nrd(f, tq, ms, q, F, 1n+N)), hr,
    Bo.and_i(In.nrd(f, tp, ms, p, F, 1n+N), In.nrd(f, tq, ms, q, F, 1n+N), np, nq))

# the nodes of a new cell i of the App of the parts p and q
def In.nrd.app(+f: Nat, +hd: U32, +m: Cr.Cir.Cells, +F: U32, +N: Nat, +i: U32, +p: U32, +q: U32, +q0: Bk.Quan, +tp: Bk.Term, +tq: Bk.Term,
  hr: {True{} == In.rd(i, F, 1n+N) : Bool},
  np: {True{} == In.nrd(f, tp, Cr.Cir.Cells.set(m, i, Cr.Cir.Cell{hd, 1, p, q, 0}), p, F, 1n+N) : Bool},
  nq: {True{} == In.nrd(f, tq, Cr.Cir.Cells.set(m, i, Cr.Cir.Cell{hd, 1, p, q, 0}), q, F, 1n+N) : Bool}) ->
  {True{} == In.nrd(1n+f, Bk.Term.App{q0, tp, tq}, Cr.Cir.Cells.set(m, i, Cr.Cir.Cell{hd, 1, p, q, 0}), i, F, 1n+N) : Bool}:
  +ms = Cr.Cir.Cells.set(m, i, Cr.Cir.Cell{hd, 1, p, q, 0})
  %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(ms, i), Cr.Cir.Cell{hd, 1, p, q, 0}, Cl.get_set(m, i, Cr.Cir.Cell{hd, 1, p, q, 0})) :
    {True{} == Bool.and(In.rd(i, F, 1n+N), Bool.and(In.nrd(f, tp, ms, Cr.Cir.Cell.get(2n, _), F, 1n+N), In.nrd(f, tq, ms, Cr.Cir.Cell.get(3n, _), F, 1n+N))) : Bool}
  Bo.and_i(In.rd(i, F, 1n+N), Bool.and(In.nrd(f, tp, ms, p, F, 1n+N), In.nrd(f, tq, ms, q, F, 1n+N)), hr,
    Bo.and_i(In.nrd(f, tp, ms, p, F, 1n+N), In.nrd(f, tq, ms, q, F, 1n+N), np, nq))

# the pairs that the machine makes: STATIC (1866) or not (842)
def In.hd(st: Bool) -> U32:
  match st:
    case True{}:
      1866
    case False{}:
      842

def In.tup(st: Bool, +f: Nat, +m: Cr.Cir.Cells, +F: U32, +N: Nat, +i: U32, +p: U32, +q: U32, +tp: Bk.Term, +tq: Bk.Term,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +sp: In.St(f, m, F, N, p, tp, ks, img), +sq: In.St(f, m, F, N, q, tq, ks, img),
  +hi: {False{} == In.rd(i, F, N) : Bool}, +hr: {True{} == In.rd(i, F, 1n+N) : Bool}) ->
  In.St(1n+f, Cr.Cir.Cells.set(m, i, Cr.Cir.Cell{In.hd(st), 1, p, q, 0}), F, 1n+N, i, Bk.Term.Tup{Bk.Quan.Q1{}, tp, tq}, ks, img):
  match st:
    case True{}:
      +ms = Cr.Cir.Cells.set(m, i, Cr.Cir.Cell{1866, 1, p, q, 0})
      In.two(1866, f, m, F, N, i, p, q, Bk.Term.Tup{Bk.Quan.Q1{}, tp, tq}, tp, tq, ks, img, sp, sq, hi, hr, {==}, {==},
        In.nrd.tup(f, 1866, m, F, N, i, p, q, Bk.Quan.Q1{}, tp, tq, hr,
          St.nrd(f, ms, F, 1n+N, p, tp, ks, img, St.up(f, ms, F, N, p, tp, ks, img, St.fr(f, m, F, N, p, tp, ks, img, i, Cr.Cir.Cell{1866, 1, p, q, 0}, hi, sp))),
          St.nrd(f, ms, F, 1n+N, q, tq, ks, img, St.up(f, ms, F, N, q, tq, ks, img, St.fr(f, m, F, N, q, tq, ks, img, i, Cr.Cir.Cell{1866, 1, p, q, 0}, hi, sq)))))
    case False{}:
      +ms = Cr.Cir.Cells.set(m, i, Cr.Cir.Cell{842, 1, p, q, 0})
      In.two(842, f, m, F, N, i, p, q, Bk.Term.Tup{Bk.Quan.Q1{}, tp, tq}, tp, tq, ks, img, sp, sq, hi, hr, {==}, {==},
        In.nrd.tup(f, 842, m, F, N, i, p, q, Bk.Quan.Q1{}, tp, tq, hr,
          St.nrd(f, ms, F, 1n+N, p, tp, ks, img, St.up(f, ms, F, N, p, tp, ks, img, St.fr(f, m, F, N, p, tp, ks, img, i, Cr.Cir.Cell{842, 1, p, q, 0}, hi, sp))),
          St.nrd(f, ms, F, 1n+N, q, tq, ks, img, St.up(f, ms, F, N, q, tq, ks, img, St.fr(f, m, F, N, q, tq, ks, img, i, Cr.Cir.Cell{842, 1, p, q, 0}, hi, sq)))))

def In.app(+f: Nat, +m: Cr.Cir.Cells, +F: U32, +N: Nat, +i: U32, +p: U32, +q: U32, +tp: Bk.Term, +tq: Bk.Term,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +sp: In.St(f, m, F, N, p, tp, ks, img), +sq: In.St(f, m, F, N, q, tq, ks, img),
  +hi: {False{} == In.rd(i, F, N) : Bool}, +hr: {True{} == In.rd(i, F, 1n+N) : Bool}) ->
  In.St(1n+f, Cr.Cir.Cells.set(m, i, Cr.Cir.Cell{72, 1, p, q, 0}), F, 1n+N, i, Bk.Term.App{Bk.Quan.Q1{}, tp, tq}, ks, img):
  +ms = Cr.Cir.Cells.set(m, i, Cr.Cir.Cell{72, 1, p, q, 0})
  In.two(72, f, m, F, N, i, p, q, Bk.Term.App{Bk.Quan.Q1{}, tp, tq}, tp, tq, ks, img, sp, sq, hi, hr, {==}, {==},
    In.nrd.app(f, 72, m, F, N, i, p, q, Bk.Quan.Q1{}, tp, tq, hr,
      St.nrd(f, ms, F, 1n+N, p, tp, ks, img, St.up(f, ms, F, N, p, tp, ks, img, St.fr(f, m, F, N, p, tp, ks, img, i, Cr.Cir.Cell{72, 1, p, q, 0}, hi, sp))),
      St.nrd(f, ms, F, 1n+N, q, tq, ks, img, St.up(f, ms, F, N, q, tq, ks, img, St.fr(f, m, F, N, q, tq, ks, img, i, Cr.Cir.Cell{72, 1, p, q, 0}, hi, sq)))))

# Numbers
# -------

def Na.le_t(a: Nat, b: Nat, h: N.Le(a, b)) -> {True{} == Nat.is_le(a, b) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+y:
      {==}
    case 1n+x 0n:
      Empty.absurd({True{} == Nat.is_le(1n+x, 0n) : Bool}, h)
    case 1n+x 1n+y:
      Na.le_t(x, y, h)

# b <= a gives a < b false
def Na.lt_f(a: Nat, b: Nat, h: N.Le(b, a)) -> {False{} == Nat.is_lt(a, b) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 1n+x 0n:
      {==}
    case 0n 1n+y:
      Empty.absurd({False{} == Nat.is_lt(0n, 1n+y) : Bool}, h)
    case 1n+x 1n+y:
      Na.lt_f(x, y, h)

# 1 + b <= a gives a <= b false
def Na.le_f(a: Nat, b: Nat, h: N.Le(1n+b, a)) -> {False{} == Nat.is_le(a, b) : Bool}:
  match a b:
    case 0n _:
      Empty.absurd({False{} == Nat.is_le(0n, b) : Bool}, h)
    case 1n+x 0n:
      {==}
    case 1n+x 1n+y:
      Na.le_f(x, y, h)

def Na.lt_succ(a: Nat) -> {True{} == Nat.is_lt(a, 1n+a) : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+x:
      Na.lt_succ(x)

# a comparison LT gives x < y
def Cm.lt(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), e: {Cmp.is_lt(c) == True{} : Bool}) -> N.Le(1n+x, y):
  match c:
    case LT{}:
      r
    case EQ{}:
      Bo.ft(N.Le(1n+x, y), Equal.sym(Bool, False{}, True{}, e))
    case GT{}:
      Bo.ft(N.Le(1n+x, y), Equal.sym(Bool, False{}, True{}, e))

# x <= y makes the comparison at most EQ
def Cm.le(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), h: N.Le(x, y)) -> {True{} == Cmp.is_le(c) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({True{} == False{} : Bool}, N.not_succ_le(y, N.le_trans(1n+y, x, y, r, h)))

# x < y makes the comparison LT
def Cm.lt_t(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), h: N.Le(1n+x, y)) -> {True{} == Cmp.is_lt(c) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({True{} == False{} : Bool}, N.not_succ_le(x, N.le_rw_r(1n+x, y, x, Equal.sym(Nat, x, y, r), h)))
    case GT{}:
      Empty.absurd({True{} == False{} : Bool}, N.not_succ_le(y, N.le_trans(1n+y, x, y, r, N.weaken(x, y, h))))

# x > y makes the comparison not EQ
def Cm.ne(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), h: N.Le(1n+y, x)) -> {False{} == Cmp.is_eq(c) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({False{} == True{} : Bool}, N.not_succ_le(y, N.le_rw_r(1n+y, x, y, r, h)))
    case GT{}:
      {==}

# below M, a U32 has a next one, one more
def U.inc(+a: U32, +M: U32, h: {U32.is_lt(a, M) == True{} : Bool}) -> {U32.to_nat(U32.inc(a)) == 1n+U32.to_nat(a) : Nat}:
  +l = Cm.lt(U32.cmp(a, M), U32.to_nat(a), U32.to_nat(M), N.U32.rel(a, M), h)
  PI.U32.inc_nat(a, Equal.sym(Bool, U32.is_zero(U32.inc(a)), False{}, PM.nz(a, M, l)))

# The machine's own cells
# -----------------------
#
# What the run keeps true of each cell that it took (In.Rok): the cell may be
# read, its count is 1, its parts (fields 2 and 3) are not 0 and may be read,
# and its header is 1866 (a pair whose parts are STATIC: one of the image's
# first 16 cells, or a 1866 cell), 842 or 72 (the focus). A cell, once taken,
# never changes, so these facts hold to the end, where they give the pointers'
# facts (Pts), the closure of the STATIC cells (Clo) and the nodes of the focus.

def Bo.or_r(a: Bool, -b: Bool, h: {True{} == b : Bool}) -> {True{} == Bool.or(a, b) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

# a part p: not 0, and a cell that may be read
def In.pt(+p: U32, +F: U32, +C: Nat) -> Bool:
  Bool.and(Bool.not(U32.is_eq(p, 0)), In.rd(p, F, C))

# a part p of a STATIC pair: one of the image's first 16 cells, or a 1866 cell
def In.ps(+m: Cr.Cir.Cells, +p: U32) -> Bool:
  Bool.or(Nat.is_lt(U32.to_nat(p), 16n), U32.is_eq(D.Fd(0n, m, p), 1866))

# the header h of a cell of the parts p and q
def In.hdr(+m: Cr.Cir.Cells, +h: U32, +p: U32, +q: U32) -> Bool:
  Bool.or(Bool.and(U32.is_eq(h, 1866), Bool.and(In.ps(m, p), In.ps(m, q))), Bool.or(U32.is_eq(h, 842), U32.is_eq(h, 72)))

# the facts of the value x of a cell that the run took: its count, parts and header
def In.okn(+m: Cr.Cir.Cells, +F: U32, +C: Nat, +x: Cr.Cir.Cell) -> Bool:
  Bool.and(U32.is_eq(Cr.Cir.Cell.get(1n, x), 1),
    Bool.and(In.pt(Cr.Cir.Cell.get(2n, x), F, C), Bool.and(In.pt(Cr.Cir.Cell.get(3n, x), F, C),
      In.hdr(m, Cr.Cir.Cell.get(0n, x), Cr.Cir.Cell.get(2n, x), Cr.Cir.Cell.get(3n, x)))))

# the cell o is one that the run took: from F, before the cell numbered C
def In.own(+o: U32, +F: U32, +C: Nat) -> Bool:
  Bool.and(Nat.is_le(U32.to_nat(F), U32.to_nat(o)), Nat.is_lt(U32.to_nat(o), C))

# the cell o, of the value x: one that the run took, and the facts of x
def In.okx(+m: Cr.Cir.Cells, +F: U32, +C: Nat, +o: U32, +x: Cr.Cir.Cell) -> Bool:
  Bool.and(In.own(o, F, C), In.okn(m, F, C, x))

# a cell that the run took may be read
def Own.rd(+o: U32, +F: U32, +C: Nat, h: {True{} == In.own(o, F, C) : Bool}) -> {True{} == In.rd(o, F, C) : Bool}:
  Bo.or_r(Nat.is_lt(U32.to_nat(o), 16n), In.own(o, F, C), h)

# and it still is, once one more cell is taken
def Own.up(+o: U32, +F: U32, +C: Nat, h: {True{} == In.own(o, F, C) : Bool}) -> {True{} == In.own(o, F, 1n+C) : Bool}:
  Bo.and_mono(Nat.is_le(U32.to_nat(F), U32.to_nat(o)), Nat.is_lt(U32.to_nat(o), C), Nat.is_lt(U32.to_nat(o), 1n+C), h,
    l => Na.lt_up(U32.to_nat(o), C, l))

# it is from F on
def Own.ge(+o: U32, +F: U32, +C: Nat, h: {True{} == In.own(o, F, C) : Bool}) -> N.Le(U32.to_nat(F), U32.to_nat(o)):
  N.toLe(U32.to_nat(F), U32.to_nat(o), Equal.sym(Bool, True{}, Nat.is_le(U32.to_nat(F), U32.to_nat(o)),
    Bo.and_l(Nat.is_le(U32.to_nat(F), U32.to_nat(o)), Nat.is_lt(U32.to_nat(o), C), h)))

# the cell next, numbered N, is one that the run took once it is taken
def Own.new(+next: U32, +N: Nat, +F: U32, eN: {U32.to_nat(next) == N : Nat}, hFN: N.Le(U32.to_nat(F), N)) ->
  {True{} == In.own(next, F, 1n+N) : Bool}:
  %Equal.sym(Nat, U32.to_nat(next), N, eN) : {True{} == Bool.and(Nat.is_le(U32.to_nat(F), _), Nat.is_lt(_, 1n+N)) : Bool}
  Bo.and_i(Nat.is_le(U32.to_nat(F), N), Nat.is_lt(N, 1n+N), Na.le_t(U32.to_nat(F), N, hFN), Na.lt_succ(N))

# each of the n cells from o
def In.Rok(n: Nat, +m: Cr.Cir.Cells, +F: U32, +C: Nat, +o: U32) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(In.okx(m, F, C, o, Cr.Cir.Cells.get(m, o)), In.Rok(p, m, F, C, U32.inc(o)))

# the facts of a part p that may be read, once a cell z that may not be read is set
def Ps.fr(+m: Cr.Cir.Cells, +p: U32, +z: U32, +y: Cr.Cir.Cell, +F: U32, +C: Nat, hp: {True{} == In.rd(p, F, C) : Bool},
  hz: {False{} == In.rd(z, F, C) : Bool}) -> {In.ps(m, p) == In.ps(Cr.Cir.Cells.set(m, z, y), p) : Bool}:
  %Cl.get_other(m, p, z, y, e => In.ne(p, z, F, C, hp, hz, e)) :
    {In.ps(m, p) == Bool.or(Nat.is_lt(U32.to_nat(p), 16n), U32.is_eq(Cr.Cir.Cell.get(0n, _), 1866)) : Bool}
  {==}

def Hdr.fr(+m: Cr.Cir.Cells, +h: U32, +p: U32, +q: U32, +z: U32, +y: Cr.Cir.Cell, +F: U32, +C: Nat,
  hp: {True{} == In.rd(p, F, C) : Bool}, hq: {True{} == In.rd(q, F, C) : Bool}, +hz: {False{} == In.rd(z, F, C) : Bool}) ->
  {In.hdr(m, h, p, q) == In.hdr(Cr.Cir.Cells.set(m, z, y), h, p, q) : Bool}:
  %Ps.fr(m, p, z, y, F, C, hp, hz) : {In.hdr(m, h, p, q) ==
    Bool.or(Bool.and(U32.is_eq(h, 1866), Bool.and(_, In.ps(Cr.Cir.Cells.set(m, z, y), q))), Bool.or(U32.is_eq(h, 842), U32.is_eq(h, 72))) : Bool}
  %Ps.fr(m, q, z, y, F, C, hq, hz) : {In.hdr(m, h, p, q) ==
    Bool.or(Bool.and(U32.is_eq(h, 1866), Bool.and(In.ps(m, p), _)), Bool.or(U32.is_eq(h, 842), U32.is_eq(h, 72))) : Bool}
  {==}

# the parts of a value as In.okn has it
def Okn.p(+m: Cr.Cir.Cells, +F: U32, +C: Nat, +x: Cr.Cir.Cell, h: {True{} == In.okn(m, F, C, x) : Bool}) ->
  {True{} == In.pt(Cr.Cir.Cell.get(2n, x), F, C) : Bool}:
  +h1 = Bo.and_r(U32.is_eq(Cr.Cir.Cell.get(1n, x), 1), Bool.and(In.pt(Cr.Cir.Cell.get(2n, x), F, C), Bool.and(In.pt(Cr.Cir.Cell.get(3n, x), F, C),
      In.hdr(m, Cr.Cir.Cell.get(0n, x), Cr.Cir.Cell.get(2n, x), Cr.Cir.Cell.get(3n, x)))), h)
  Bo.and_l(In.pt(Cr.Cir.Cell.get(2n, x), F, C), Bool.and(In.pt(Cr.Cir.Cell.get(3n, x), F, C),
      In.hdr(m, Cr.Cir.Cell.get(0n, x), Cr.Cir.Cell.get(2n, x), Cr.Cir.Cell.get(3n, x))), h1)

def Okn.q(+m: Cr.Cir.Cells, +F: U32, +C: Nat, +x: Cr.Cir.Cell, h: {True{} == In.okn(m, F, C, x) : Bool}) ->
  {True{} == In.pt(Cr.Cir.Cell.get(3n, x), F, C) : Bool}:
  +h1 = Bo.and_r(U32.is_eq(Cr.Cir.Cell.get(1n, x), 1), Bool.and(In.pt(Cr.Cir.Cell.get(2n, x), F, C), Bool.and(In.pt(Cr.Cir.Cell.get(3n, x), F, C),
      In.hdr(m, Cr.Cir.Cell.get(0n, x), Cr.Cir.Cell.get(2n, x), Cr.Cir.Cell.get(3n, x)))), h)
  +h2 = Bo.and_r(In.pt(Cr.Cir.Cell.get(2n, x), F, C), Bool.and(In.pt(Cr.Cir.Cell.get(3n, x), F, C),
      In.hdr(m, Cr.Cir.Cell.get(0n, x), Cr.Cir.Cell.get(2n, x), Cr.Cir.Cell.get(3n, x))), h1)
  Bo.and_l(In.pt(Cr.Cir.Cell.get(3n, x), F, C), In.hdr(m, Cr.Cir.Cell.get(0n, x), Cr.Cir.Cell.get(2n, x), Cr.Cir.Cell.get(3n, x)), h2)

def Pt.rd(+p: U32, +F: U32, +C: Nat, h: {True{} == In.pt(p, F, C) : Bool}) -> {True{} == In.rd(p, F, C) : Bool}:
  Bo.and_r(Bool.not(U32.is_eq(p, 0)), In.rd(p, F, C), h)

# a value as In.okn has it, once a cell z that may not be read is set
def Okn.fr(+m: Cr.Cir.Cells, +F: U32, +C: Nat, +x: Cr.Cir.Cell, +z: U32, +y: Cr.Cir.Cell,
  hz: {False{} == In.rd(z, F, C) : Bool}, +h: {True{} == In.okn(m, F, C, x) : Bool}) ->
  {True{} == In.okn(Cr.Cir.Cells.set(m, z, y), F, C, x) : Bool}:
  %Hdr.fr(m, Cr.Cir.Cell.get(0n, x), Cr.Cir.Cell.get(2n, x), Cr.Cir.Cell.get(3n, x), z, y, F, C,
    Pt.rd(Cr.Cir.Cell.get(2n, x), F, C, Okn.p(m, F, C, x, h)), Pt.rd(Cr.Cir.Cell.get(3n, x), F, C, Okn.q(m, F, C, x, h)), hz) :
    {True{} == Bool.and(U32.is_eq(Cr.Cir.Cell.get(1n, x), 1),
      Bool.and(In.pt(Cr.Cir.Cell.get(2n, x), F, C), Bool.and(In.pt(Cr.Cir.Cell.get(3n, x), F, C), _))) : Bool}
  h

# a part as In.pt has it, once one more cell is taken
def Pt.up(+p: U32, +F: U32, +C: Nat, h: {True{} == In.pt(p, F, C) : Bool}) -> {True{} == In.pt(p, F, 1n+C) : Bool}:
  Bo.and_mono(Bool.not(U32.is_eq(p, 0)), In.rd(p, F, C), In.rd(p, F, 1n+C), h, k => In.rd_up(p, F, C, k))

# a value as In.okn has it, once one more cell is taken
def Okn.up(+m: Cr.Cir.Cells, +F: U32, +C: Nat, +x: Cr.Cir.Cell, +h: {True{} == In.okn(m, F, C, x) : Bool}) ->
  {True{} == In.okn(m, F, 1n+C, x) : Bool}:
  +p = Cr.Cir.Cell.get(2n, x)
  +q = Cr.Cir.Cell.get(3n, x)
  +hd = In.hdr(m, Cr.Cir.Cell.get(0n, x), p, q)
  +h1 = Bo.and_r(U32.is_eq(Cr.Cir.Cell.get(1n, x), 1), Bool.and(In.pt(p, F, C), Bool.and(In.pt(q, F, C), hd)), h)
  +h2 = Bo.and_r(In.pt(p, F, C), Bool.and(In.pt(q, F, C), hd), h1)
  Bo.and_i(U32.is_eq(Cr.Cir.Cell.get(1n, x), 1), Bool.and(In.pt(p, F, 1n+C), Bool.and(In.pt(q, F, 1n+C), hd)),
    Bo.and_l(U32.is_eq(Cr.Cir.Cell.get(1n, x), 1), Bool.and(In.pt(p, F, C), Bool.and(In.pt(q, F, C), hd)), h),
    Bo.and_i(In.pt(p, F, 1n+C), Bool.and(In.pt(q, F, 1n+C), hd),
      Pt.up(p, F, C, Bo.and_l(In.pt(p, F, C), Bool.and(In.pt(q, F, C), hd), h1)),
      Bo.and_i(In.pt(q, F, 1n+C), hd, Pt.up(q, F, C, Bo.and_l(In.pt(q, F, C), hd, h2)), Bo.and_r(In.pt(q, F, C), hd, h2))))

# a cell as In.okx has it, once a cell z that may not be read is set
def Okx.fr(+m: Cr.Cir.Cells, +F: U32, +C: Nat, +o: U32, +x: Cr.Cir.Cell, +z: U32, +y: Cr.Cir.Cell,
  hz: {False{} == In.rd(z, F, C) : Bool}, +h: {True{} == In.okx(m, F, C, o, x) : Bool}) ->
  {True{} == In.okx(Cr.Cir.Cells.set(m, z, y), F, C, o, x) : Bool}:
  Bo.and_i(In.own(o, F, C), In.okn(Cr.Cir.Cells.set(m, z, y), F, C, x), Bo.and_l(In.own(o, F, C), In.okn(m, F, C, x), h),
    Okn.fr(m, F, C, x, z, y, hz, Bo.and_r(In.own(o, F, C), In.okn(m, F, C, x), h)))

# and once one more cell is taken
def Okx.up(+m: Cr.Cir.Cells, +F: U32, +C: Nat, +o: U32, +x: Cr.Cir.Cell, +h: {True{} == In.okx(m, F, C, o, x) : Bool}) ->
  {True{} == In.okx(m, F, 1n+C, o, x) : Bool}:
  Bo.and_i(In.own(o, F, 1n+C), In.okn(m, F, 1n+C, x), Own.up(o, F, C, Bo.and_l(In.own(o, F, C), In.okn(m, F, C, x), h)),
    Okn.up(m, F, C, x, Bo.and_r(In.own(o, F, C), In.okn(m, F, C, x), h)))

# the n cells from o, once a cell z that may not be read is set
def Rok.fr(n: Nat, +m: Cr.Cir.Cells, +F: U32, +C: Nat, +o: U32, +z: U32, +y: Cr.Cir.Cell,
  +hz: {False{} == In.rd(z, F, C) : Bool}, +h: {True{} == In.Rok(n, m, F, C, o) : Bool}) ->
  {True{} == In.Rok(n, Cr.Cir.Cells.set(m, z, y), F, C, o) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      +x = Cr.Cir.Cells.get(m, o)
      +ha = Bo.and_l(In.okx(m, F, C, o, x), In.Rok(p, m, F, C, U32.inc(o)), h)
      +hb = Bo.and_r(In.okx(m, F, C, o, x), In.Rok(p, m, F, C, U32.inc(o)), h)
      +ho = Own.rd(o, F, C, Bo.and_l(In.own(o, F, C), In.okn(m, F, C, x), ha))
      %Cl.get_other(m, o, z, y, e => In.ne(o, z, F, C, ho, hz, e)) :
        {True{} == Bool.and(In.okx(Cr.Cir.Cells.set(m, z, y), F, C, o, _), In.Rok(p, Cr.Cir.Cells.set(m, z, y), F, C, U32.inc(o))) : Bool}
      Bo.and_i(In.okx(Cr.Cir.Cells.set(m, z, y), F, C, o, x), In.Rok(p, Cr.Cir.Cells.set(m, z, y), F, C, U32.inc(o)),
        Okx.fr(m, F, C, o, x, z, y, hz, ha), Rok.fr(p, m, F, C, U32.inc(o), z, y, hz, hb))

# the n cells from o, once one more cell is taken
def Rok.up(n: Nat, +m: Cr.Cir.Cells, +F: U32, +C: Nat, +o: U32, +h: {True{} == In.Rok(n, m, F, C, o) : Bool}) ->
  {True{} == In.Rok(n, m, F, 1n+C, o) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      +x = Cr.Cir.Cells.get(m, o)
      Bo.and_i(In.okx(m, F, 1n+C, o, x), In.Rok(p, m, F, 1n+C, U32.inc(o)),
        Okx.up(m, F, C, o, x, Bo.and_l(In.okx(m, F, C, o, x), In.Rok(p, m, F, C, U32.inc(o)), h)),
        Rok.up(p, m, F, C, U32.inc(o), Bo.and_r(In.okx(m, F, C, o, x), In.Rok(p, m, F, C, U32.inc(o)), h)))

# the cell n after o
def In.incn(n: Nat, +o: U32) -> U32:
  match n:
    case 0n:
      o
    case 1n+p:
      In.incn(p, U32.inc(o))

# one more cell, after the n cells from o
def Rok.snoc(n: Nat, +m: Cr.Cir.Cells, +F: U32, +C: Nat, +o: U32, +h: {True{} == In.Rok(n, m, F, C, o) : Bool},
  hx: {True{} == In.okx(m, F, C, In.incn(n, o), Cr.Cir.Cells.get(m, In.incn(n, o))) : Bool}) ->
  {True{} == In.Rok(1n+n, m, F, C, o) : Bool}:
  match n:
    case 0n:
      Bo.and_i(In.okx(m, F, C, o, Cr.Cir.Cells.get(m, o)), True{}, hx, {==})
    case 1n+(+p):
      +x = Cr.Cir.Cells.get(m, o)
      Bo.and_i(In.okx(m, F, C, o, x), In.Rok(1n+p, m, F, C, U32.inc(o)),
        Bo.and_l(In.okx(m, F, C, o, x), In.Rok(p, m, F, C, U32.inc(o)), h),
        Rok.snoc(p, m, F, C, U32.inc(o), Bo.and_r(In.okx(m, F, C, o, x), In.Rok(p, m, F, C, U32.inc(o)), h), hx))

# (1 + a) - f = 1 + (a - f), for f <= a
def In.sub_succ(+f: Nat, +a: Nat, h: N.Le(f, a)) -> {Nat.sub(1n+a, f) == 1n+Nat.sub(a, f) : Nat}:
  match f a:
    case 0n 0n:
      {==}
    case 0n 1n+b:
      {==}
    case 1n+g 0n:
      Empty.absurd({Nat.sub(1n, 1n+g) == 1n+Nat.sub(0n, 1n+g) : Nat}, h)
    case 1n+g 1n+b:
      In.sub_succ(g, b, h)

def In.sub_self(a: Nat) -> {Nat.sub(a, a) == 0n : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      In.sub_self(p)

# the cell after i, when the cells from i on stay below M
def Ld.einc(+i: U32, +n: Nat, +M: U32, hov: N.Le(Nat.add(U32.to_nat(i), 1n+n), U32.to_nat(M))) -> {U32.to_nat(U32.inc(i)) == 1n+U32.to_nat(i) : Nat}:
  +ti = U32.to_nat(i)
  +h1 = N.le_rw_l(Nat.add(ti, 1n+n), 1n+Nat.add(ti, n), U32.to_nat(M), N.add_succ_r(ti, n), hov)
  +h2 = N.le_trans(1n+ti, 1n+Nat.add(ti, n), U32.to_nat(M), N.le_add_r(ti, n), h1)
  PI.U32.inc_nat(i, Equal.sym(Bool, U32.is_zero(U32.inc(i)), False{}, PM.nz(i, M, h2)))

def Ld.hov(+i: U32, +n: Nat, +M: U32, +hov: N.Le(Nat.add(U32.to_nat(i), 1n+n), U32.to_nat(M))) -> N.Le(Nat.add(U32.to_nat(U32.inc(i)), n), U32.to_nat(M)):
  +ti = U32.to_nat(i)
  %Equal.sym(Nat, U32.to_nat(U32.inc(i)), 1n+ti, Ld.einc(i, n, M, hov)) : N.Le(Nat.add(_, n), U32.to_nat(M))
  N.le_rw_l(Nat.add(ti, 1n+n), 1n+Nat.add(ti, n), U32.to_nat(M), N.add_succ_r(ti, n), hov)

# the cell n after o is numbered o + n, below M
def In.incn.nat(n: Nat, +o: U32, +M: U32, +h: N.Le(Nat.add(U32.to_nat(o), n), U32.to_nat(M))) ->
  {U32.to_nat(In.incn(n, o)) == Nat.add(U32.to_nat(o), n) : Nat}:
  match n:
    case 0n:
      Equal.sym(Nat, Nat.add(U32.to_nat(o), 0n), U32.to_nat(o), N.add_zero(U32.to_nat(o)))
    case 1n+(+p):
      +e1 = Ld.einc(o, p, M, h)
      Equal.trans(Nat, U32.to_nat(In.incn(p, U32.inc(o))), Nat.add(U32.to_nat(U32.inc(o)), p), Nat.add(U32.to_nat(o), 1n+p),
        In.incn.nat(p, U32.inc(o), M, Ld.hov(o, p, M, h)),
        Equal.trans(Nat, Nat.add(U32.to_nat(U32.inc(o)), p), 1n+Nat.add(U32.to_nat(o), p), Nat.add(U32.to_nat(o), 1n+p),
          Equal.cong(Nat, Nat, z => Nat.add(z, p), U32.to_nat(U32.inc(o)), 1n+U32.to_nat(o), e1),
          Equal.sym(Nat, Nat.add(U32.to_nat(o), 1n+p), 1n+Nat.add(U32.to_nat(o), p), N.add_succ_r(U32.to_nat(o), p))))

# the next cell, numbered N, is the cell N - F after F
def In.incn.eq(+next: U32, +N: Nat, +F: U32, eN: {U32.to_nat(next) == N : Nat}, +hFN: N.Le(U32.to_nat(F), N)) ->
  {In.incn(Nat.sub(N, U32.to_nat(F)), F) == next : U32}:
  +ea = D.add.sub(U32.to_nat(F), N, hFN)
  +eb = Equal.trans(Nat, Nat.add(U32.to_nat(F), Nat.sub(N, U32.to_nat(F))), N, U32.to_nat(next), ea, Equal.sym(Nat, U32.to_nat(next), N, eN))
  D.u32.eq(In.incn(Nat.sub(N, U32.to_nat(F)), F), next, D.u.nat.eq(In.incn(Nat.sub(N, U32.to_nat(F)), F), next,
    Equal.trans(Nat, U32.to_nat(In.incn(Nat.sub(N, U32.to_nat(F)), F)), Nat.add(U32.to_nat(F), Nat.sub(N, U32.to_nat(F))), U32.to_nat(next),
      In.incn.nat(Nat.sub(N, U32.to_nat(F)), F, next, N.le_rw_r(Nat.add(U32.to_nat(F), Nat.sub(N, U32.to_nat(F))), U32.to_nat(next), U32.to_nat(next),
        {==}, N.le_rw_l(U32.to_nat(next), Nat.add(U32.to_nat(F), Nat.sub(N, U32.to_nat(F))), U32.to_nat(next),
          Equal.sym(Nat, Nat.add(U32.to_nat(F), Nat.sub(N, U32.to_nat(F))), U32.to_nat(next), eb), N.le_refl(U32.to_nat(next))))),
      eb)))

# Cells of In.St
# ---------------

# A cell that In.St has: it may be read, and it is not 0 (In.rds reads a tag
# of 1, 8, 10 or 13 there, and the field 0 of the cell 0 is 0)
def In.rds0(+p: Nat, +m: Cr.Cir.Cells, +F: U32, +N: Nat, e0: {D.Fd(0n, m, 0) == 0 : U32}, r: {True{} == In.rds(1n+p, m, F, N, 0) : Bool}) ->
  {True{} == False{} : Bool}:
  %e0 : {True{} == Bool.and(In.rd(0, F, N), In.rds.cell(U32.to_nat(U32.and(_, 63)), u => In.rds(p, m, F, N, Cr.Cir.Cell.get(2n, Cr.Cir.Cells.get(m, 0))),
    u => In.rds(p, m, F, N, Cr.Cir.Cell.get(3n, Cr.Cir.Cells.get(m, 0))))) : Bool}
  r

def St.nz.at(f: Nat, +m: Cr.Cir.Cells, +F: U32, +N: Nat, e0: {D.Fd(0n, m, 0) == 0 : U32}, r: {True{} == In.rds(f, m, F, N, 0) : Bool}) ->
  {True{} == False{} : Bool}:
  match f:
    case 0n:
      r
    case 1n+(+p):
      In.rds0(p, m, F, N, e0, r)

def St.nz.of(b: Bool, +f: Nat, +m: Cr.Cir.Cells, +F: U32, +N: Nat, +c: U32, eb: {U32.is_eq(c, 0) == b : Bool}, e0: {D.Fd(0n, m, 0) == 0 : U32},
  r: {True{} == In.rds(f, m, F, N, c) : Bool}) -> {True{} == Bool.not(b) : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Bo.ft({True{} == Bool.not(True{}) : Bool}, St.nz.at(f, m, F, N, e0, (%D.u32.eq(c, 0, eb) : {True{} == In.rds(f, m, F, N, _) : Bool}; r)))

def St.rd.of(f: Nat, +m: Cr.Cir.Cells, +F: U32, +N: Nat, +c: U32, r: {True{} == In.rds(f, m, F, N, c) : Bool}) -> {True{} == In.rd(c, F, N) : Bool}:
  match f:
    case 0n:
      Bo.ft({True{} == In.rd(c, F, N) : Bool}, r)
    case 1n+(+p):
      Bo.and_l(In.rd(c, F, N), In.rds.cell(U32.to_nat(U32.and(Cr.Cir.Cell.get(0n, Cr.Cir.Cells.get(m, c)), 63)),
        u => In.rds(p, m, F, N, Cr.Cir.Cell.get(2n, Cr.Cir.Cells.get(m, c))), u => In.rds(p, m, F, N, Cr.Cir.Cell.get(3n, Cr.Cir.Cells.get(m, c)))), r)

# a cell that In.St has may be read
def St.rd(+f: Nat, +m: Cr.Cir.Cells, +F: U32, +N: Nat, +c: U32, +t: Bk.Term, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  s: In.St(f, m, F, N, c, t, ks, img)) -> {True{} == In.rd(c, F, N) : Bool}:
  (e, rn) = s
  (r, n) = rn
  St.rd.of(f, m, F, N, c, r)

# a cell that In.St has is a part as In.pt says
def St.pt(+f: Nat, +m: Cr.Cir.Cells, +F: U32, +N: Nat, +c: U32, +t: Bk.Term, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  e0: {D.Fd(0n, m, 0) == 0 : U32}, s: In.St(f, m, F, N, c, t, ks, img)) -> {True{} == In.pt(c, F, N) : Bool}:
  (e, rn) = s
  (r, n) = rn
  +rb = r
  Bo.and_i(Bool.not(U32.is_eq(c, 0)), In.rd(c, F, N), St.nz.of(U32.is_eq(c, 0), f, m, F, N, c, {==}, e0, rb), St.rd.of(f, m, F, N, c, rb))

# the facts of a new cell's value: the count 1, the header h, the parts a and b
def In.okn.mk(+m: Cr.Cir.Cells, +F: U32, +N: Nat, +h: U32, +a: U32, +b: U32, ha: {True{} == In.pt(a, F, N) : Bool},
  hb: {True{} == In.pt(b, F, N) : Bool}, hh: {True{} == In.hdr(m, h, a, b) : Bool}) ->
  {True{} == In.okn(m, F, N, Cr.Cir.Cell{h, 1, a, b, 0}) : Bool}:
  Bo.and_i(U32.is_eq(1, 1), Bool.and(In.pt(a, F, N), Bool.and(In.pt(b, F, N), In.hdr(m, h, a, b))), {==},
    Bo.and_i(In.pt(a, F, N), Bool.and(In.pt(b, F, N), In.hdr(m, h, a, b)), ha, Bo.and_i(In.pt(b, F, N), In.hdr(m, h, a, b), hb, hh)))

# a STATIC pair's header, of STATIC parts
def In.hdr.st(+m: Cr.Cir.Cells, +a: U32, +b: U32, pa: {True{} == In.ps(m, a) : Bool}, pb: {True{} == In.ps(m, b) : Bool}) ->
  {True{} == In.hdr(m, 1866, a, b) : Bool}:
  %pa : {True{} == Bool.or(Bool.and(U32.is_eq(1866, 1866), Bool.and(_, In.ps(m, b))), Bool.or(U32.is_eq(1866, 842), U32.is_eq(1866, 72))) : Bool}
  %pb : {True{} == Bool.or(Bool.and(U32.is_eq(1866, 1866), Bool.and(True{}, _)), Bool.or(U32.is_eq(1866, 842), U32.is_eq(1866, 72))) : Bool}
  {==}

# the image's bit cells, True (12) and False (13)
def In.pt.bit(b: Bool, +F: U32, +N: Nat) -> {True{} == In.pt(Bool.pick(U32, b, 12, 13), F, N) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def In.ps.bit(b: Bool, +m: Cr.Cir.Cells) -> {True{} == In.ps(m, Bool.pick(U32, b, 12, 13)) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the new cell next, a STATIC pair, is a STATIC part
def In.ps.mk(+m: Cr.Cir.Cells, +next: U32, +a: U32, +b: U32) ->
  {True{} == In.ps(Cr.Cir.Cells.set(m, next, Cr.Cir.Cell{In.hd(True{}), 1, a, b, 0}), next) : Bool}:
  %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, next, Cr.Cir.Cell{In.hd(True{}), 1, a, b, 0}), next), Cr.Cir.Cell{In.hd(True{}), 1, a, b, 0},
    Cl.get_set(m, next, Cr.Cir.Cell{In.hd(True{}), 1, a, b, 0})) :
    {True{} == Bool.or(Nat.is_lt(U32.to_nat(next), 16n), U32.is_eq(Cr.Cir.Cell.get(0n, _), 1866)) : Bool}
  Bo.or_r(Nat.is_lt(U32.to_nat(next), 16n), U32.is_eq(1866, 1866), {==})

# The cache
# ---------

type In.Or<-A: Data, -B: Data> is Data:
  In.Or.l{a: A}
  In.Or.r{b: B}

# the low 8 bits of x
def In.low8(x: U32) -> Word(8n):
  match x:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, _}}}}}}}}}:
      WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WNil{}}}}}}}}}

# the cache cell of the byte of the bits w
def In.J(+w: Word(8n)) -> U32:
  U32.add(16, Sd.Byte.to_u32(w))

# the cache's entry for the byte of the bits w: none yet, or the cell of its
# word, a STATIC part
def In.En(+fc: Nat, +m: Cr.Cir.Cells, +F: U32, +N: Nat, +w: Word(8n), +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>) -> Data:
  +v = Cr.Cir.Cell.get(2n, Cr.Cir.Cells.get(m, In.J(w)))
  In.Or<{0 == v : U32}, In.P(In.St(fc, m, F, N, v, Pg.Program.word(8n, w), ks, img), {True{} == In.ps(m, v) : Bool})>

# the bit at the head of bs, False after its end
def In.bh(bs: List<&2, Bool>) -> Bool:
  match bs:
    case Nil{}:
      False{}
    case Con{b, _}:
      b

def In.bt(bs: List<&2, Bool>) -> List<&2, Bool>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{_, r}:
      r

# the byte of the bits bs, the highest first
def In.wl(+bs: List<&2, Bool>) -> Word(8n):
  +b1 = In.bt(bs)
  +b2 = In.bt(b1)
  +b3 = In.bt(b2)
  +b4 = In.bt(b3)
  +b5 = In.bt(b4)
  +b6 = In.bt(b5)
  +b7 = In.bt(b6)
  WCon{In.bh(b7), WCon{In.bh(b6), WCon{In.bh(b5), WCon{In.bh(b4), WCon{In.bh(b3), WCon{In.bh(b2), WCon{In.bh(b1), WCon{In.bh(bs), WNil{}}}}}}}}}

# the bits of w, the lowest first, onto bs
def In.push(n: Nat, w: Word(n), bs: List<&2, Bool>) -> List<&2, Bool>:
  match n:
    case 0n:
      bs
    case 1n+(+p):
      match w:
        case WCon{b, t}:
          In.push(p, t, Con{b, bs})

def In.wl_push(w: Word(8n)) -> {w == In.wl(In.push(8n, w, [])) : Word(8n)}:
  match w:
    case WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WNil{}}}}}}}}}:
      {==}

# the entries of the bytes of the bits bs, after n more, for every n more
def In.CI(n: Nat, +bs: List<&2, Bool>, +fc: Nat, +m: Cr.Cir.Cells, +F: U32, +N: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>) -> Data:
  match n:
    case 0n:
      In.En(fc, m, F, N, In.wl(bs), ks, img)
    case 1n+p:
      In.P(In.CI(p, Con{False{}, bs}, fc, m, F, N, ks, img), In.CI(p, Con{True{}, bs}, fc, m, F, N, ks, img))

# the cache cell of a byte lies in 16 to 271, and gives the byte back
def In.Jb(w: Word(8n)) -> In.P(N.Le(16n, U32.to_nat(In.J(w))), In.P(N.Le(1n+U32.to_nat(In.J(w)), 272n),
  {Sd.Byte.to_u32(w) == U32.and(U32.sub(In.J(w), 16), 255) : U32})):
  match w:
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))

# the bits of a byte, back
def In.low8_u8(w: Word(8n)) -> {w == In.low8(Sd.Byte.to_u32(w)) : Word(8n)}:
  match w:
    case WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WNil{}}}}}}}}}:
      {==}

# the cache cells of two bytes are two
def In.J_inj(+w: Word(8n), +v: Word(8n), e: {In.J(w) == In.J(v) : U32}) -> {w == v : Word(8n)}:
  +a = In.p2(N.Le(1n+U32.to_nat(In.J(w)), 272n), {Sd.Byte.to_u32(w) == U32.and(U32.sub(In.J(w), 16), 255) : U32},
    In.p2(N.Le(16n, U32.to_nat(In.J(w))), In.P(N.Le(1n+U32.to_nat(In.J(w)), 272n), {Sd.Byte.to_u32(w) == U32.and(U32.sub(In.J(w), 16), 255) : U32}), In.Jb(w)))
  +b = In.p2(N.Le(1n+U32.to_nat(In.J(v)), 272n), {Sd.Byte.to_u32(v) == U32.and(U32.sub(In.J(v), 16), 255) : U32},
    In.p2(N.Le(16n, U32.to_nat(In.J(v))), In.P(N.Le(1n+U32.to_nat(In.J(v)), 272n), {Sd.Byte.to_u32(v) == U32.and(U32.sub(In.J(v), 16), 255) : U32}), In.Jb(v)))
  +uw = Equal.trans(U32, Sd.Byte.to_u32(w), U32.and(U32.sub(In.J(w), 16), 255), U32.and(U32.sub(In.J(v), 16), 255), a,
    Equal.cong(U32, U32, y => U32.and(U32.sub(y, 16), 255), In.J(w), In.J(v), e))
  +uv = Equal.trans(U32, Sd.Byte.to_u32(w), U32.and(U32.sub(In.J(v), 16), 255), Sd.Byte.to_u32(v), uw, Equal.sym(U32, Sd.Byte.to_u32(v), U32.and(U32.sub(In.J(v), 16), 255), b))
  Equal.trans(Word(8n), w, In.low8(Sd.Byte.to_u32(w)), v, In.low8_u8(w),
    Equal.trans(Word(8n), In.low8(Sd.Byte.to_u32(w)), In.low8(Sd.Byte.to_u32(v)), v, Equal.cong(U32, Word(8n), y => In.low8(y), Sd.Byte.to_u32(w), Sd.Byte.to_u32(v), uv),
      Equal.sym(Word(8n), v, In.low8(Sd.Byte.to_u32(v)), In.low8_u8(v))))

# bits and words, compared
def In.beq(a: Bool, b: Bool) -> Bool:
  match a b:
    case True{} True{}:
      True{}
    case False{} False{}:
      True{}
    case _ _:
      False{}

def In.weq(n: Nat, a: Word(n), b: Word(n)) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      match a b:
        case WCon{x, s} WCon{y, t}:
          Bool.and(In.beq(x, y), In.weq(p, s, t))

def In.weq_t(n: Nat, a: Word(n), b: Word(n), h: {True{} == In.weq(n, a, b) : Bool}) -> {a == b : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+(+p):
      match a b:
        case WCon{True{}, +s} WCon{True{}, +t}:
          Equal.cong(Word(p), Word(1n+p), z => WCon{True{}, z}, s, t, In.weq_t(p, s, t, h))
        case WCon{False{}, +s} WCon{False{}, +t}:
          Equal.cong(Word(p), Word(1n+p), z => WCon{False{}, z}, s, t, In.weq_t(p, s, t, h))
        case WCon{True{}, +s} WCon{False{}, +t}:
          Bo.ft({WCon{True{}, s} == WCon{False{}, t} : Word(1n+p)}, h)
        case WCon{False{}, +s} WCon{True{}, +t}:
          Bo.ft({WCon{False{}, s} == WCon{True{}, t} : Word(1n+p)}, h)

def In.weq_refl(n: Nat, a: Word(n)) -> {True{} == In.weq(n, a, a) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      match a:
        case WCon{True{}, +s}:
          In.weq_refl(p, s)
        case WCon{False{}, +s}:
          In.weq_refl(p, s)

def In.weq_f(+n: Nat, +a: Word(n), +b: Word(n), h: {False{} == In.weq(n, a, b) : Bool}, e: {a == b : Word(n)}) -> Empty:
  +r = Equal.trans(Bool, True{}, In.weq(n, a, a), In.weq(n, a, b), In.weq_refl(n, a), Equal.cong(Word(n), Bool, z => In.weq(n, a, z), a, b, e))
  N.true_ne_false(Equal.trans(Bool, True{}, In.weq(n, a, b), False{}, r, Equal.sym(Bool, False{}, In.weq(n, a, b), h)))

# Cells that may be read
# ----------------------

def In.Jlo(+w: Word(8n)) -> N.Le(16n, U32.to_nat(In.J(w))):
  In.p1(N.Le(16n, U32.to_nat(In.J(w))), In.P(N.Le(1n+U32.to_nat(In.J(w)), 272n), {Sd.Byte.to_u32(w) == U32.and(U32.sub(In.J(w), 16), 255) : U32}), In.Jb(w))

def In.Jhi(+w: Word(8n)) -> N.Le(1n+U32.to_nat(In.J(w)), 272n):
  In.p1(N.Le(1n+U32.to_nat(In.J(w)), 272n), {Sd.Byte.to_u32(w) == U32.and(U32.sub(In.J(w), 16), 255) : U32},
    In.p2(N.Le(16n, U32.to_nat(In.J(w))), In.P(N.Le(1n+U32.to_nat(In.J(w)), 272n), {Sd.Byte.to_u32(w) == U32.and(U32.sub(In.J(w), 16), 255) : U32}), In.Jb(w)))

# a cache cell may not be read
def In.rdJ(+w: Word(8n), +F: U32, +N: Nat, hF: N.Le(272n, U32.to_nat(F))) -> {False{} == In.rd(In.J(w), F, N) : Bool}:
  +tJ = U32.to_nat(In.J(w))
  %Na.lt_f(tJ, 16n, In.Jlo(w)) : {False{} == Bool.or(_, Bool.and(Nat.is_le(U32.to_nat(F), tJ), Nat.is_lt(tJ, N))) : Bool}
  %Na.le_f(U32.to_nat(F), tJ, N.le_trans(1n+tJ, 272n, U32.to_nat(F), In.Jhi(w), hF)) : {False{} == Bool.or(False{}, Bool.and(_, Nat.is_lt(tJ, N))) : Bool}
  {==}

# a cache cell is none of the machine's own
def In.neJ(+w: Word(8n), +i: U32, hi: N.Le(272n, U32.to_nat(i)), e: {In.J(w) == i : U32}) -> Empty:
  +tJ = U32.to_nat(In.J(w))
  N.not_succ_le(tJ, N.le_rw_r(1n+tJ, U32.to_nat(i), tJ, Equal.sym(Nat, tJ, U32.to_nat(i), Equal.cong(U32, Nat, y => U32.to_nat(y), In.J(w), i, e)),
    N.le_trans(1n+tJ, 272n, U32.to_nat(i), In.Jhi(w), hi)))

# the new cell next (numbered N) may not be read yet, but may once taken
def In.rdNew(+i: U32, +F: U32, +N: Nat, eN: {U32.to_nat(i) == N : Nat}, hF: N.Le(16n, U32.to_nat(F)), +hFN: N.Le(U32.to_nat(F), N)) ->
  In.P({False{} == In.rd(i, F, N) : Bool}, {True{} == In.rd(i, F, 1n+N) : Bool}):
  %Equal.sym(Nat, U32.to_nat(i), N, eN) : In.P({False{} == Bool.or(Nat.is_lt(_, 16n), Bool.and(Nat.is_le(U32.to_nat(F), _), Nat.is_lt(_, N))) : Bool},
    {True{} == Bool.or(Nat.is_lt(_, 16n), Bool.and(Nat.is_le(U32.to_nat(F), _), Nat.is_lt(_, 1n+N))) : Bool})
  %Na.lt_f(N, 16n, N.le_trans(16n, U32.to_nat(F), N, hF, hFN)) : In.P({False{} == Bool.or(_, Bool.and(Nat.is_le(U32.to_nat(F), N), Nat.is_lt(N, N))) : Bool},
    {True{} == Bool.or(_, Bool.and(Nat.is_le(U32.to_nat(F), N), Nat.is_lt(N, 1n+N))) : Bool})
  %Na.le_t(U32.to_nat(F), N, hFN) : In.P({False{} == Bool.or(False{}, Bool.and(_, Nat.is_lt(N, N))) : Bool},
    {True{} == Bool.or(False{}, Bool.and(_, Nat.is_lt(N, 1n+N))) : Bool})
  %Na.lt_f(N, N, N.le_refl(N)) : In.P({False{} == Bool.or(False{}, Bool.and(True{}, _)) : Bool},
    {True{} == Bool.or(False{}, Bool.and(True{}, Nat.is_lt(N, 1n+N))) : Bool})
  ({==}, Na.lt_succ(N))

# the cache cell of a byte is one of the image's
def In.cellJ(+w: Word(8n), +K: U32, +F: U32, +nx: U32, hK: N.Le(271n, U32.to_nat(K))) -> {True{} == Cr.Cir.is_cell(In.J(w), K, F, nx) : Bool}:
  +j = In.J(w)
  +tJ = U32.to_nat(j)
  %Cm.ne(U32.cmp(j, 0), tJ, U32.to_nat(0), N.U32.rel(j, 0), N.le_trans(1n, 16n, tJ, Unit{}, In.Jlo(w))) :
    {True{} == Bool.or(Bool.and(Bool.not(_), U32.is_le(j, K)), Bool.and(U32.is_le(F, j), U32.is_lt(j, nx))) : Bool}
  %Cm.le(U32.cmp(j, K), tJ, U32.to_nat(K), N.U32.rel(j, K), N.le_trans(tJ, 271n, U32.to_nat(K), In.Jhi(w), hK)) :
    {True{} == Bool.or(Bool.and(True{}, _), Bool.and(U32.is_le(F, j), U32.is_lt(j, nx))) : Bool}
  {==}

# the new cell next is one the machine took
def In.cellNew(+next: U32, +K: U32, +F: U32, lt: In.lt(next), hFN: N.Le(U32.to_nat(F), U32.to_nat(next))) ->
  {True{} == Cr.Cir.is_cell(next, K, F, U32.inc(next)) : Bool}:
  +tN = U32.to_nat(next)
  Bo.or_r(Bool.and(Bool.not(U32.is_zero(next)), U32.is_le(next, K)), Bool.and(U32.is_le(F, next), U32.is_lt(next, U32.inc(next))),
    Bo.and_i(U32.is_le(F, next), U32.is_lt(next, U32.inc(next)),
      Cm.le(U32.cmp(F, next), U32.to_nat(F), tN, N.U32.rel(F, next), hFN),
      Cm.lt_t(U32.cmp(next, U32.inc(next)), tN, U32.to_nat(U32.inc(next)), N.U32.rel(next, U32.inc(next)),
        N.le_rw_r(1n+tN, 1n+tN, U32.to_nat(U32.inc(next)), Equal.sym(Nat, U32.to_nat(U32.inc(next)), 1n+tN, U.inc(next, 214748364, lt)), N.le_refl(1n+tN)))))

# The cache's entries
# -------------------

def En.fr.go(+fc: Nat, +m: Cr.Cir.Cells, +F: U32, +N: Nat, +v: U32, +t: Bk.Term, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +i: U32, +x: Cr.Cir.Cell,
  +hi: {False{} == In.rd(i, F, N) : Bool}, e: In.Or<{0 == v : U32}, In.P(In.St(fc, m, F, N, v, t, ks, img), {True{} == In.ps(m, v) : Bool})>) ->
  In.Or<{0 == v : U32}, In.P(In.St(fc, Cr.Cir.Cells.set(m, i, x), F, N, v, t, ks, img), {True{} == In.ps(Cr.Cir.Cells.set(m, i, x), v) : Bool})>:
  match e:
    case In.Or.l{z}:
      In.Or.l{z}
    case In.Or.r{p}:
      (s, pv) = p
      +sb = s
      In.Or.r{(St.fr(fc, m, F, N, v, t, ks, img, i, x, hi, sb),
        (%Ps.fr(m, v, i, x, F, N, St.rd(fc, m, F, N, v, t, ks, img, sb), hi) : {True{} == _ : Bool}; pv))}

# a cell the machine takes keeps every entry
def En.fr(+fc: Nat, +m: Cr.Cir.Cells, +F: U32, +N: Nat, +w: Word(8n), +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +i: U32, +x: Cr.Cir.Cell,
  +hi: {False{} == In.rd(i, F, N) : Bool}, hb: N.Le(272n, U32.to_nat(i)), e: In.En(fc, m, F, N, w, ks, img)) ->
  In.En(fc, Cr.Cir.Cells.set(m, i, x), F, N, w, ks, img):
  +ms = Cr.Cir.Cells.set(m, i, x)
  %Cl.get_other(m, In.J(w), i, x, k => In.neJ(w, i, hb, k)) :
    In.Or<{0 == Cr.Cir.Cell.get(2n, _) : U32}, In.P(In.St(fc, ms, F, N, Cr.Cir.Cell.get(2n, _), Pg.Program.word(8n, w), ks, img),
      {True{} == In.ps(ms, Cr.Cir.Cell.get(2n, _)) : Bool})>
  En.fr.go(fc, m, F, N, Cr.Cir.Cell.get(2n, Cr.Cir.Cells.get(m, In.J(w))), Pg.Program.word(8n, w), ks, img, i, x, hi, e)

def En.up(+fc: Nat, +m: Cr.Cir.Cells, +F: U32, +N: Nat, +w: Word(8n), +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, e: In.En(fc, m, F, N, w, ks, img)) ->
  In.En(fc, m, F, 1n+N, w, ks, img):
  match e:
    case In.Or.l{z}:
      In.Or.l{z}
    case In.Or.r{p}:
      (s, pv) = p
      In.Or.r{(St.up(fc, m, F, N, Cr.Cir.Cell.get(2n, Cr.Cir.Cells.get(m, In.J(w))), Pg.Program.word(8n, w), ks, img, s), pv)}

def CI.fr(n: Nat, +bs: List<&2, Bool>, +fc: Nat, +m: Cr.Cir.Cells, +F: U32, +N: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +i: U32,
  +x: Cr.Cir.Cell, +hi: {False{} == In.rd(i, F, N) : Bool}, +hb: N.Le(272n, U32.to_nat(i)), ci: In.CI(n, bs, fc, m, F, N, ks, img)) ->
  In.CI(n, bs, fc, Cr.Cir.Cells.set(m, i, x), F, N, ks, img):
  match n:
    case 0n:
      En.fr(fc, m, F, N, In.wl(bs), ks, img, i, x, hi, hb, ci)
    case 1n+(+p):
      (a, b) = ci
      (CI.fr(p, Con{False{}, bs}, fc, m, F, N, ks, img, i, x, hi, hb, a), CI.fr(p, Con{True{}, bs}, fc, m, F, N, ks, img, i, x, hi, hb, b))

def CI.up(n: Nat, +bs: List<&2, Bool>, +fc: Nat, +m: Cr.Cir.Cells, +F: U32, +N: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  ci: In.CI(n, bs, fc, m, F, N, ks, img)) -> In.CI(n, bs, fc, m, F, 1n+N, ks, img):
  match n:
    case 0n:
      En.up(fc, m, F, N, In.wl(bs), ks, img, ci)
    case 1n+(+p):
      (a, b) = ci
      (CI.up(p, Con{False{}, bs}, fc, m, F, N, ks, img, a), CI.up(p, Con{True{}, bs}, fc, m, F, N, ks, img, b))

def CI.get(n: Nat, +bs: List<&2, Bool>, +fc: Nat, +m: Cr.Cir.Cells, +F: U32, +N: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  w: Word(n), ci: In.CI(n, bs, fc, m, F, N, ks, img)) -> In.En(fc, m, F, N, In.wl(In.push(n, w, bs)), ks, img):
  match n:
    case 0n:
      match w:
        case WNil{}:
          ci
    case 1n+(+p):
      match w:
        case WCon{False{}, t}:
          (a, b) = ci
          CI.get(p, Con{False{}, bs}, fc, m, F, N, ks, img, t, a)
        case WCon{True{}, t}:
          (a, b) = ci
          CI.get(p, Con{True{}, bs}, fc, m, F, N, ks, img, t, b)

# field 2 of a cell, once set
def Cl.f2(c: Cr.Cir.Cell, +v: U32) -> {v == Cr.Cir.Cell.get(2n, Cr.Cir.Cell.set(2n, c, v)) : U32}:
  match c:
    case Cr.Cir.Cell{a, b, x, y, z}:
      {==}

# the store of the cache: the entry of w8 gets the cell v
def En.st.go(b: Bool, +fc: Nat, +m: Cr.Cir.Cells, +F: U32, +N: Nat, +w: Word(8n), +w8: Word(8n), +v: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +hF: N.Le(272n, U32.to_nat(F)), eb: {b == In.weq(8n, w, w8) : Bool},
  sv: In.St(fc, Cr.Cir.Cells.set(m, In.J(w8), Cr.Cir.Cell.set(2n, Cr.Cir.Cells.get(m, In.J(w8)), v)), F, N, v, Pg.Program.word(8n, w8), ks, img),
  pv: {True{} == In.ps(Cr.Cir.Cells.set(m, In.J(w8), Cr.Cir.Cell.set(2n, Cr.Cir.Cells.get(m, In.J(w8)), v)), v) : Bool}, e: In.En(fc, m, F, N, w, ks, img)) ->
  In.En(fc, Cr.Cir.Cells.set(m, In.J(w8), Cr.Cir.Cell.set(2n, Cr.Cir.Cells.get(m, In.J(w8)), v)), F, N, w, ks, img):
  match b:
    case True{}:
      %Equal.sym(Word(8n), w, w8, In.weq_t(8n, w, w8, eb)) : In.En(fc, Cr.Cir.Cells.set(m, In.J(w8), Cr.Cir.Cell.set(2n, Cr.Cir.Cells.get(m, In.J(w8)), v)), F, N, _, ks, img)
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, In.J(w8), Cr.Cir.Cell.set(2n, Cr.Cir.Cells.get(m, In.J(w8)), v)), In.J(w8)), Cr.Cir.Cell.set(2n, Cr.Cir.Cells.get(m, In.J(w8)), v), Cl.get_set(m, In.J(w8), Cr.Cir.Cell.set(2n, Cr.Cir.Cells.get(m, In.J(w8)), v))) :
        In.Or<{0 == Cr.Cir.Cell.get(2n, _) : U32}, In.P(In.St(fc, Cr.Cir.Cells.set(m, In.J(w8), Cr.Cir.Cell.set(2n, Cr.Cir.Cells.get(m, In.J(w8)), v)), F, N, Cr.Cir.Cell.get(2n, _), Pg.Program.word(8n, w8), ks, img),
          {True{} == In.ps(Cr.Cir.Cells.set(m, In.J(w8), Cr.Cir.Cell.set(2n, Cr.Cir.Cells.get(m, In.J(w8)), v)), Cr.Cir.Cell.get(2n, _)) : Bool})>
      %Cl.f2(Cr.Cir.Cells.get(m, In.J(w8)), v) :
        In.Or<{0 == _ : U32}, In.P(In.St(fc, Cr.Cir.Cells.set(m, In.J(w8), Cr.Cir.Cell.set(2n, Cr.Cir.Cells.get(m, In.J(w8)), v)), F, N, _, Pg.Program.word(8n, w8), ks, img),
          {True{} == In.ps(Cr.Cir.Cells.set(m, In.J(w8), Cr.Cir.Cell.set(2n, Cr.Cir.Cells.get(m, In.J(w8)), v)), _) : Bool})>
      In.Or.r{(sv, pv)}
    case False{}:
      %Cl.get_other(m, In.J(w), In.J(w8), Cr.Cir.Cell.set(2n, Cr.Cir.Cells.get(m, In.J(w8)), v), k => In.weq_f(8n, w, w8, eb, In.J_inj(w, w8, k))) :
        In.Or<{0 == Cr.Cir.Cell.get(2n, _) : U32}, In.P(In.St(fc, Cr.Cir.Cells.set(m, In.J(w8), Cr.Cir.Cell.set(2n, Cr.Cir.Cells.get(m, In.J(w8)), v)), F, N, Cr.Cir.Cell.get(2n, _), Pg.Program.word(8n, w), ks, img),
          {True{} == In.ps(Cr.Cir.Cells.set(m, In.J(w8), Cr.Cir.Cell.set(2n, Cr.Cir.Cells.get(m, In.J(w8)), v)), Cr.Cir.Cell.get(2n, _)) : Bool})>
      En.fr.go(fc, m, F, N, Cr.Cir.Cell.get(2n, Cr.Cir.Cells.get(m, In.J(w))), Pg.Program.word(8n, w), ks, img, In.J(w8), Cr.Cir.Cell.set(2n, Cr.Cir.Cells.get(m, In.J(w8)), v),
        In.rdJ(w8, F, N, hF), e)

def CI.st(n: Nat, +bs: List<&2, Bool>, +fc: Nat, +m: Cr.Cir.Cells, +F: U32, +N: Nat, +w8: Word(8n), +v: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +hF: N.Le(272n, U32.to_nat(F)),
  +sv: In.St(fc, Cr.Cir.Cells.set(m, In.J(w8), Cr.Cir.Cell.set(2n, Cr.Cir.Cells.get(m, In.J(w8)), v)), F, N, v, Pg.Program.word(8n, w8), ks, img),
  +pv: {True{} == In.ps(Cr.Cir.Cells.set(m, In.J(w8), Cr.Cir.Cell.set(2n, Cr.Cir.Cells.get(m, In.J(w8)), v)), v) : Bool}, ci: In.CI(n, bs, fc, m, F, N, ks, img)) ->
  In.CI(n, bs, fc, Cr.Cir.Cells.set(m, In.J(w8), Cr.Cir.Cell.set(2n, Cr.Cir.Cells.get(m, In.J(w8)), v)), F, N, ks, img):
  match n:
    case 0n:
      En.st.go(In.weq(8n, In.wl(bs), w8), fc, m, F, N, In.wl(bs), w8, v, ks, img, hF, {==}, sv, pv, ci)
    case 1n+(+p):
      (a, b) = ci
      (CI.st(p, Con{False{}, bs}, fc, m, F, N, w8, v, ks, img, hF, sv, pv, a), CI.st(p, Con{True{}, bs}, fc, m, F, N, w8, v, ks, img, hF, sv, pv, b))

# The image's cells that the machine points to
# ----------------------------------------------

# the labels (), Con, WCon (cells 1, 3, 5), Nil (11), True (12), False (13),
# WNil (14) and the Ref of main (15)
def In.Im(+f0: Nat, +m: Cr.Cir.Cells, +F: U32, +N: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>) -> Data:
  In.P(In.St(f0, m, F, N, 1, Bk.Term.Lab{Pg.Program.name.unit()}, ks, img), In.P(In.St(f0, m, F, N, 3, Bk.Term.Lab{Pg.Program.name.con()}, ks, img), In.P(In.St(f0, m, F, N, 5, Bk.Term.Lab{Pg.Program.name.wcon()}, ks, img), In.P(In.St(f0, m, F, N, 11, Pg.Program.bytes([]), ks, img), In.P(In.St(f0, m, F, N, 12, Pg.Program.bit(True{}), ks, img), In.P(In.St(f0, m, F, N, 13, Pg.Program.bit(False{}), ks, img), In.P(In.St(f0, m, F, N, 14, Pg.Program.word(0n, WNil{}), ks, img), In.St(f0, m, F, N, 15, Bk.Term.Ref{Pg.Program.name.main()}, ks, img))))))))

def Im.fr(+f0: Nat, +m: Cr.Cir.Cells, +F: U32, +N: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +i: U32, +x: Cr.Cir.Cell,
  +hi: {False{} == In.rd(i, F, N) : Bool}, im: In.Im(f0, m, F, N, ks, img)) -> In.Im(f0, Cr.Cir.Cells.set(m, i, x), F, N, ks, img):
  (s0, r0) = im
  (s1, r1) = r0
  (s2, r2) = r1
  (s3, r3) = r2
  (s4, r4) = r3
  (s5, r5) = r4
  (s6, r6) = r5
  (St.fr(f0, m, F, N, 1, Bk.Term.Lab{Pg.Program.name.unit()}, ks, img, i, x, hi, s0), (St.fr(f0, m, F, N, 3, Bk.Term.Lab{Pg.Program.name.con()}, ks, img, i, x, hi, s1), (St.fr(f0, m, F, N, 5, Bk.Term.Lab{Pg.Program.name.wcon()}, ks, img, i, x, hi, s2), (St.fr(f0, m, F, N, 11, Pg.Program.bytes([]), ks, img, i, x, hi, s3), (St.fr(f0, m, F, N, 12, Pg.Program.bit(True{}), ks, img, i, x, hi, s4), (St.fr(f0, m, F, N, 13, Pg.Program.bit(False{}), ks, img, i, x, hi, s5), (St.fr(f0, m, F, N, 14, Pg.Program.word(0n, WNil{}), ks, img, i, x, hi, s6), St.fr(f0, m, F, N, 15, Bk.Term.Ref{Pg.Program.name.main()}, ks, img, i, x, hi, r6))))))))

def Im.up(+f0: Nat, +m: Cr.Cir.Cells, +F: U32, +N: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  im: In.Im(f0, m, F, N, ks, img)) -> In.Im(f0, m, F, 1n+N, ks, img):
  (s0, r0) = im
  (s1, r1) = r0
  (s2, r2) = r1
  (s3, r3) = r2
  (s4, r4) = r3
  (s5, r5) = r4
  (s6, r6) = r5
  (St.up(f0, m, F, N, 1, Bk.Term.Lab{Pg.Program.name.unit()}, ks, img, s0), (St.up(f0, m, F, N, 3, Bk.Term.Lab{Pg.Program.name.con()}, ks, img, s1), (St.up(f0, m, F, N, 5, Bk.Term.Lab{Pg.Program.name.wcon()}, ks, img, s2), (St.up(f0, m, F, N, 11, Pg.Program.bytes([]), ks, img, s3), (St.up(f0, m, F, N, 12, Pg.Program.bit(True{}), ks, img, s4), (St.up(f0, m, F, N, 13, Pg.Program.bit(False{}), ks, img, s5), (St.up(f0, m, F, N, 14, Pg.Program.word(0n, WNil{}), ks, img, s6), St.up(f0, m, F, N, 15, Bk.Term.Ref{Pg.Program.name.main()}, ks, img, r6))))))))

def Im.g1(+f0: Nat, +m: Cr.Cir.Cells, +F: U32, +N: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  im: In.Im(f0, m, F, N, ks, img)) -> In.St(f0, m, F, N, 1, Bk.Term.Lab{Pg.Program.name.unit()}, ks, img):
  (s0, r0) = im
  (s1, r1) = r0
  (s2, r2) = r1
  (s3, r3) = r2
  (s4, r4) = r3
  (s5, r5) = r4
  (s6, r6) = r5
  s0

def Im.g3(+f0: Nat, +m: Cr.Cir.Cells, +F: U32, +N: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  im: In.Im(f0, m, F, N, ks, img)) -> In.St(f0, m, F, N, 3, Bk.Term.Lab{Pg.Program.name.con()}, ks, img):
  (s0, r0) = im
  (s1, r1) = r0
  (s2, r2) = r1
  (s3, r3) = r2
  (s4, r4) = r3
  (s5, r5) = r4
  (s6, r6) = r5
  s1

def Im.g5(+f0: Nat, +m: Cr.Cir.Cells, +F: U32, +N: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  im: In.Im(f0, m, F, N, ks, img)) -> In.St(f0, m, F, N, 5, Bk.Term.Lab{Pg.Program.name.wcon()}, ks, img):
  (s0, r0) = im
  (s1, r1) = r0
  (s2, r2) = r1
  (s3, r3) = r2
  (s4, r4) = r3
  (s5, r5) = r4
  (s6, r6) = r5
  s2

def Im.g11(+f0: Nat, +m: Cr.Cir.Cells, +F: U32, +N: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  im: In.Im(f0, m, F, N, ks, img)) -> In.St(f0, m, F, N, 11, Pg.Program.bytes([]), ks, img):
  (s0, r0) = im
  (s1, r1) = r0
  (s2, r2) = r1
  (s3, r3) = r2
  (s4, r4) = r3
  (s5, r5) = r4
  (s6, r6) = r5
  s3

def Im.g12(+f0: Nat, +m: Cr.Cir.Cells, +F: U32, +N: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  im: In.Im(f0, m, F, N, ks, img)) -> In.St(f0, m, F, N, 12, Pg.Program.bit(True{}), ks, img):
  (s0, r0) = im
  (s1, r1) = r0
  (s2, r2) = r1
  (s3, r3) = r2
  (s4, r4) = r3
  (s5, r5) = r4
  (s6, r6) = r5
  s4

def Im.g13(+f0: Nat, +m: Cr.Cir.Cells, +F: U32, +N: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  im: In.Im(f0, m, F, N, ks, img)) -> In.St(f0, m, F, N, 13, Pg.Program.bit(False{}), ks, img):
  (s0, r0) = im
  (s1, r1) = r0
  (s2, r2) = r1
  (s3, r3) = r2
  (s4, r4) = r3
  (s5, r5) = r4
  (s6, r6) = r5
  s5

def Im.g14(+f0: Nat, +m: Cr.Cir.Cells, +F: U32, +N: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  im: In.Im(f0, m, F, N, ks, img)) -> In.St(f0, m, F, N, 14, Pg.Program.word(0n, WNil{}), ks, img):
  (s0, r0) = im
  (s1, r1) = r0
  (s2, r2) = r1
  (s3, r3) = r2
  (s4, r4) = r3
  (s5, r5) = r4
  (s6, r6) = r5
  s6

def Im.g15(+f0: Nat, +m: Cr.Cir.Cells, +F: U32, +N: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  im: In.Im(f0, m, F, N, ks, img)) -> In.St(f0, m, F, N, 15, Bk.Term.Ref{Pg.Program.name.main()}, ks, img):
  (s0, r0) = im
  (s1, r1) = r0
  (s2, r2) = r1
  (s3, r3) = r2
  (s4, r4) = r3
  (s5, r5) = r4
  (s6, r6) = r5
  r6

# The facts of the run's cells
# ----------------------------

# the cells once the cache's entry of w8 gets v
def In.cs(+m: Cr.Cir.Cells, +w8: Word(8n), +v: U32) -> Cr.Cir.Cells:
  Cr.Cir.Cells.set(m, In.J(w8), Cr.Cir.Cell.set(2n, Cr.Cir.Cells.get(m, In.J(w8)), v))

# F is past the table (291 <= F); the table's masks of App (cell 280) and
# Tup (cell 282) are 3; the field 0 of the cell 0 is 0; and the cells that
# the run took, from F before N, are as In.Rok says
def In.Fb(+m: Cr.Cir.Cells, +N: Nat, +F: U32) -> Data:
  In.P(N.Le(291n, U32.to_nat(F)), In.P({D.Fd(2n, m, 280) == 3 : U32}, In.P({D.Fd(2n, m, 282) == 3 : U32},
    In.P({D.Fd(0n, m, 0) == 0 : U32}, {True{} == In.Rok(Nat.sub(N, U32.to_nat(F)), m, F, N, F) : Bool}))))

# a cell below b is not b
def In.ne.lt(+a: U32, +b: U32, h: N.Le(1n+U32.to_nat(a), U32.to_nat(b)), e: {a == b : U32}) -> Empty:
  N.not_succ_le(U32.to_nat(b), N.le_rw_l(1n+U32.to_nat(a), 1n+U32.to_nat(b), U32.to_nat(b), Equal.cong(U32, Nat, z => 1n+U32.to_nat(z), a, b, e), h))

def In.ne.gt(+a: U32, +b: U32, h: N.Le(1n+U32.to_nat(a), U32.to_nat(b)), e: {b == a : U32}) -> Empty:
  In.ne.lt(a, b, h, Equal.sym(U32, b, a, e))

# a field of the cell j, once another cell i is set
def Fd.fr(+k: Nat, +m: Cr.Cir.Cells, +j: U32, +i: U32, +x: Cr.Cir.Cell, +v: U32, ne: {j == i : U32} -> Empty,
  h: {D.Fd(k, m, j) == v : U32}) -> {D.Fd(k, Cr.Cir.Cells.set(m, i, x), j) == v : U32}:
  %Cl.get_other(m, j, i, x, ne) : {Cr.Cir.Cell.get(k, _) == v : U32}
  h

# the new cell next, numbered N, as In.okx has it once it holds x
def Fb.hx(+m: Cr.Cir.Cells, +next: U32, +N: Nat, +F: U32, +x: Cr.Cir.Cell, +eN: {U32.to_nat(next) == N : Nat},
  +hFN: N.Le(U32.to_nat(F), N), +hi: {False{} == In.rd(next, F, N) : Bool},
  hx: {True{} == In.okn(m, F, N, x) : Bool}) ->
  {True{} == In.okx(Cr.Cir.Cells.set(m, next, x), F, 1n+N, In.incn(Nat.sub(N, U32.to_nat(F)), F),
    Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, next, x), In.incn(Nat.sub(N, U32.to_nat(F)), F))) : Bool}:
  +ms = Cr.Cir.Cells.set(m, next, x)
  %Equal.sym(U32, In.incn(Nat.sub(N, U32.to_nat(F)), F), next, In.incn.eq(next, N, F, eN, hFN)) :
    {True{} == In.okx(ms, F, 1n+N, _, Cr.Cir.Cells.get(ms, _)) : Bool}
  %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(ms, next), x, Cl.get_set(m, next, x)) : {True{} == In.okx(ms, F, 1n+N, next, _) : Bool}
  Bo.and_i(In.own(next, F, 1n+N), In.okn(ms, F, 1n+N, x), Own.new(next, N, F, eN, hFN), Okn.up(ms, F, N, x, Okn.fr(m, F, N, x, next, x, hi, hx)))

# the cells that the run took, once the cell next gets x
def Fb.rok(+m: Cr.Cir.Cells, +next: U32, +N: Nat, +F: U32, +x: Cr.Cir.Cell, +eN: {U32.to_nat(next) == N : Nat},
  +hFN: N.Le(U32.to_nat(F), N), +hi: {False{} == In.rd(next, F, N) : Bool},
  hx: {True{} == In.okn(m, F, N, x) : Bool}, rk: {True{} == In.Rok(Nat.sub(N, U32.to_nat(F)), m, F, N, F) : Bool}) ->
  {True{} == In.Rok(Nat.sub(1n+N, U32.to_nat(F)), Cr.Cir.Cells.set(m, next, x), F, 1n+N, F) : Bool}:
  +ms = Cr.Cir.Cells.set(m, next, x)
  +n = Nat.sub(N, U32.to_nat(F))
  %Equal.sym(Nat, Nat.sub(1n+N, U32.to_nat(F)), 1n+n, In.sub_succ(U32.to_nat(F), N, hFN)) : {True{} == In.Rok(_, ms, F, 1n+N, F) : Bool}
  Rok.snoc(n, ms, F, 1n+N, F, Rok.up(n, ms, F, N, F, Rok.fr(n, m, F, N, F, next, x, hi, rk)), Fb.hx(m, next, N, F, x, eN, hFN, hi, hx))

# the facts, once the cell next (numbered N) gets the value x, as In.okn says
def Fb.step(+m: Cr.Cir.Cells, +next: U32, +N: Nat, +F: U32, +x: Cr.Cir.Cell, +eN: {U32.to_nat(next) == N : Nat},
  +hFN: N.Le(U32.to_nat(F), N), +hi: {False{} == In.rd(next, F, N) : Bool},
  hx: {True{} == In.okn(m, F, N, x) : Bool}, fb: In.Fb(m, N, F)) -> In.Fb(Cr.Cir.Cells.set(m, next, x), 1n+N, F):
  (h291, r1) = fb
  (e280, r2) = r1
  (e282, r3) = r2
  (e0, rk) = r3
  +h291b = h291
  +lF = N.le_rw_r(U32.to_nat(F), N, U32.to_nat(next), Equal.sym(Nat, U32.to_nat(next), N, eN), hFN)
  +hF2 = N.le_trans(291n, U32.to_nat(F), U32.to_nat(next), h291b, lF)
  (h291b,
   (Fd.fr(2n, m, 280, next, x, 3, e => In.ne.lt(280, next, N.le_trans(281n, 291n, U32.to_nat(next), Unit{}, hF2), e), e280),
    (Fd.fr(2n, m, 282, next, x, 3, e => In.ne.lt(282, next, N.le_trans(283n, 291n, U32.to_nat(next), Unit{}, hF2), e), e282),
     (Fd.fr(0n, m, 0, next, x, 0, e => In.ne.lt(0, next, N.le_trans(1n, 291n, U32.to_nat(next), Unit{}, hF2), e), e0),
      Fb.rok(m, next, N, F, x, eN, hFN, hi, hx, rk)))))

# a STATIC part that may be read, once the cache's entry of w8 gets v
def Ps.cs(+m: Cr.Cir.Cells, +p: U32, +w8: Word(8n), +F: U32, +N: Nat, hF: N.Le(272n, U32.to_nat(F)), hp: {True{} == In.rd(p, F, N) : Bool},
  h: {True{} == In.ps(m, p) : Bool}) -> {True{} == In.ps(Cr.Cir.Cells.set(m, In.J(w8), Cr.Cir.Cell.set(2n, Cr.Cir.Cells.get(m, In.J(w8)), p)), p) : Bool}:
  %Ps.fr(m, p, In.J(w8), Cr.Cir.Cell.set(2n, Cr.Cir.Cells.get(m, In.J(w8)), p), F, N, hp, In.rdJ(w8, F, N, hF)) : {True{} == _ : Bool}
  h

# a field of the cell j, once the cache's entry of w8 (another cell) gets v
def Fd.cs(+k: Nat, +m: Cr.Cir.Cells, +j: U32, +w8: Word(8n), +v: U32, +u: U32, ne: {j == In.J(w8) : U32} -> Empty,
  h: {D.Fd(k, m, j) == u : U32}) -> {D.Fd(k, In.cs(m, w8, v), j) == u : U32}:
  Fd.fr(k, m, j, In.J(w8), Cr.Cir.Cell.set(2n, Cr.Cir.Cells.get(m, In.J(w8)), v), u, ne, h)

# the cells that the run took, once the cache's entry of w8 gets v
def Rok.cs(+n: Nat, +m: Cr.Cir.Cells, +F: U32, +N: Nat, +w8: Word(8n), +v: U32, hF: N.Le(272n, U32.to_nat(F)),
  h: {True{} == In.Rok(n, m, F, N, F) : Bool}) -> {True{} == In.Rok(n, In.cs(m, w8, v), F, N, F) : Bool}:
  Rok.fr(n, m, F, N, F, In.J(w8), Cr.Cir.Cell.set(2n, Cr.Cir.Cells.get(m, In.J(w8)), v), In.rdJ(w8, F, N, hF), h)

# the facts, once the cache's entry of w8 gets v
def Fb.cs(+m: Cr.Cir.Cells, +N: Nat, +F: U32, +w8: Word(8n), +v: U32, fb: In.Fb(m, N, F)) -> In.Fb(In.cs(m, w8, v), N, F):
  (h291, r1) = fb
  (e280, r2) = r1
  (e282, r3) = r2
  (e0, rk) = r3
  +h291b = h291
  (h291b,
   (Fd.cs(2n, m, 280, w8, v, 3, e => In.ne.gt(In.J(w8), 280, N.le_trans(1n+U32.to_nat(In.J(w8)), 272n, 280n, In.Jhi(w8), Unit{}), e), e280),
    (Fd.cs(2n, m, 282, w8, v, 3, e => In.ne.gt(In.J(w8), 282, N.le_trans(1n+U32.to_nat(In.J(w8)), 272n, 282n, In.Jhi(w8), Unit{}), e), e282),
     (Fd.cs(0n, m, 0, w8, v, 0, e => In.ne.lt(0, In.J(w8), N.le_trans(1n, 16n, U32.to_nat(In.J(w8)), Unit{}, In.Jlo(w8)), e), e0),
      Rok.cs(Nat.sub(N, U32.to_nat(F)), m, F, N, w8, v, N.le_trans(272n, 291n, U32.to_nat(F), Unit{}, h291b), rk)))))

# Pointers of the run's cells
# ---------------------------
#
# A cell that the run took is a pair (Tup, 1866 or 842) or the focus (App, 72),
# whose mask is 3 (cells 282 and 280): its pointers are its fields 2 and 3. A
# set of a cell z that may not be read, and that is not one of these table
# cells, keeps the pointers of each of them (Pc.fr).

# the header of a value as In.okn has it
def Okn.hdr(+m: Cr.Cir.Cells, +F: U32, +C: Nat, +x: Cr.Cir.Cell, h: {True{} == In.okn(m, F, C, x) : Bool}) ->
  {True{} == In.hdr(m, Cr.Cir.Cell.get(0n, x), Cr.Cir.Cell.get(2n, x), Cr.Cir.Cell.get(3n, x)) : Bool}:
  +h1 = Bo.and_r(U32.is_eq(Cr.Cir.Cell.get(1n, x), 1), Bool.and(In.pt(Cr.Cir.Cell.get(2n, x), F, C), Bool.and(In.pt(Cr.Cir.Cell.get(3n, x), F, C),
      In.hdr(m, Cr.Cir.Cell.get(0n, x), Cr.Cir.Cell.get(2n, x), Cr.Cir.Cell.get(3n, x)))), h)
  +h2 = Bo.and_r(In.pt(Cr.Cir.Cell.get(2n, x), F, C), Bool.and(In.pt(Cr.Cir.Cell.get(3n, x), F, C),
      In.hdr(m, Cr.Cir.Cell.get(0n, x), Cr.Cir.Cell.get(2n, x), Cr.Cir.Cell.get(3n, x))), h1)
  Bo.and_r(In.pt(Cr.Cir.Cell.get(3n, x), F, C), In.hdr(m, Cr.Cir.Cell.get(0n, x), Cr.Cir.Cell.get(2n, x), Cr.Cir.Cell.get(3n, x)), h2)

# a header of the run's cells is 1866, 842 or 72
def Hdr.cases.of(b1: Bool, b2: Bool, b3: Bool, +h: U32, -X: Bool, e1: {U32.is_eq(h, 1866) == b1 : Bool}, e2: {U32.is_eq(h, 842) == b2 : Bool},
  e3: {U32.is_eq(h, 72) == b3 : Bool}, hh: {True{} == Bool.or(Bool.and(b1, X), Bool.or(b2, b3)) : Bool}) ->
  In.Or<{h == 1866 : U32}, In.Or<{h == 842 : U32}, {h == 72 : U32}>>:
  match b1:
    case True{}:
      In.Or.l{D.u32.eq(h, 1866, e1)}
    case False{}:
      match b2:
        case True{}:
          In.Or.r{In.Or.l{D.u32.eq(h, 842, e2)}}
        case False{}:
          match b3:
            case True{}:
              In.Or.r{In.Or.r{D.u32.eq(h, 72, e3)}}
            case False{}:
              Bo.ft(In.Or<{h == 1866 : U32}, In.Or<{h == 842 : U32}, {h == 72 : U32}>>, hh)

def Hdr.cases(+m: Cr.Cir.Cells, +h: U32, +p: U32, +q: U32, hh: {True{} == In.hdr(m, h, p, q) : Bool}) ->
  In.Or<{h == 1866 : U32}, In.Or<{h == 842 : U32}, {h == 72 : U32}>>:
  Hdr.cases.of(U32.is_eq(h, 1866), U32.is_eq(h, 842), U32.is_eq(h, 72), h, Bool.and(In.ps(m, p), In.ps(m, q)), {==}, {==}, {==}, hh)

# two cells that are not one: is_eq says it
def U.nef.of(b: Bool, +x: U32, +y: U32, eb: {U32.is_eq(x, y) == b : Bool}, ne: {x == y : U32} -> Empty) -> {U32.is_eq(x, y) == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({U32.is_eq(x, y) == False{} : Bool}, ne(D.u32.eq(x, y, eb)))
    case False{}:
      eb

def U.nef(+x: U32, +y: U32, ne: {x == y : U32} -> Empty) -> {U32.is_eq(x, y) == False{} : Bool}:
  U.nef.of(U32.is_eq(x, y), x, y, {==}, ne)

# the table's cell of the mask of a cell of the header h is not z, when z is neither 280 nor 282
def Tb.at(+h: U32, +z: U32, n280: {U32.is_eq(280, z) == False{} : Bool}, n282: {U32.is_eq(282, z) == False{} : Bool},
  hc: In.Or<{h == 1866 : U32}, In.Or<{h == 842 : U32}, {h == 72 : U32}>>) ->
  {Bool.or(Bool.not(U32.is_lt(U32.and(h, 63), 19)), Bool.not(U32.is_eq(U32.add(272, U32.and(h, 63)), z))) == True{} : Bool}:
  match hc:
    case In.Or.l{e}:
      %Equal.sym(U32, h, 1866, e) : {Bool.or(Bool.not(U32.is_lt(U32.and(_, 63), 19)), Bool.not(U32.is_eq(U32.add(272, U32.and(_, 63)), z))) == True{} : Bool}
      %Equal.sym(Bool, U32.is_eq(282, z), False{}, n282) : {Bool.or(Bool.not(U32.is_lt(10, 19)), Bool.not(_)) == True{} : Bool}
      {==}
    case In.Or.r{r}:
      match r:
        case In.Or.l{e}:
          %Equal.sym(U32, h, 842, e) : {Bool.or(Bool.not(U32.is_lt(U32.and(_, 63), 19)), Bool.not(U32.is_eq(U32.add(272, U32.and(_, 63)), z))) == True{} : Bool}
          %Equal.sym(Bool, U32.is_eq(282, z), False{}, n282) : {Bool.or(Bool.not(U32.is_lt(10, 19)), Bool.not(_)) == True{} : Bool}
          {==}
        case In.Or.r{e}:
          %Equal.sym(U32, h, 72, e) : {Bool.or(Bool.not(U32.is_lt(U32.and(_, 63), 19)), Bool.not(U32.is_eq(U32.add(272, U32.and(_, 63)), z))) == True{} : Bool}
          %Equal.sym(Bool, U32.is_eq(280, z), False{}, n280) : {Bool.or(Bool.not(U32.is_lt(8, 19)), Bool.not(_)) == True{} : Bool}
          {==}

# a cell that the run took reads its mask at 280 or 282, so not at z
def Own.tblat(+m: Cr.Cir.Cells, +F: U32, +C: Nat, +o: U32, +z: U32, n280: {U32.is_eq(280, z) == False{} : Bool},
  n282: {U32.is_eq(282, z) == False{} : Bool}, h: {True{} == In.okx(m, F, C, o, Cr.Cir.Cells.get(m, o)) : Bool}) ->
  {D.TblAt(m, o, z) == True{} : Bool}:
  Tb.at(D.Fd(0n, m, o), z, n280, n282, Hdr.cases(m, D.Fd(0n, m, o), D.Fd(2n, m, o), D.Fd(3n, m, o),
    Okn.hdr(m, F, C, Cr.Cir.Cells.get(m, o), Bo.and_r(In.own(o, F, C), In.okn(m, F, C, Cr.Cir.Cells.get(m, o)), h))))

# the pointers to c of n + 1 cells: of the n, then of the last
def Pc.snoc(n: Nat, +m: Cr.Cir.Cells, +ps: List<&2, U32>, +o: U32, +c: U32) ->
  {D.Pc(1n+n, m, ps, o, c) == Nat.add(D.Pc(n, m, ps, o, c), D.RcL(D.Fs(m, ps, In.incn(n, o)), c)) : Nat}:
  match n:
    case 0n:
      N.add_zero(D.RcL(D.Fs(m, ps, o), c))
    case 1n+(+p):
      Equal.trans(Nat, Nat.add(D.RcL(D.Fs(m, ps, o), c), D.Pc(1n+p, m, ps, U32.inc(o), c)),
        Nat.add(D.RcL(D.Fs(m, ps, o), c), Nat.add(D.Pc(p, m, ps, U32.inc(o), c), D.RcL(D.Fs(m, ps, In.incn(p, U32.inc(o))), c))),
        Nat.add(Nat.add(D.RcL(D.Fs(m, ps, o), c), D.Pc(p, m, ps, U32.inc(o), c)), D.RcL(D.Fs(m, ps, In.incn(p, U32.inc(o))), c)),
        Equal.cong(Nat, Nat, w => Nat.add(D.RcL(D.Fs(m, ps, o), c), w), D.Pc(1n+p, m, ps, U32.inc(o), c),
          Nat.add(D.Pc(p, m, ps, U32.inc(o), c), D.RcL(D.Fs(m, ps, In.incn(p, U32.inc(o))), c)), Pc.snoc(p, m, ps, U32.inc(o), c)),
        Equal.sym(Nat, Nat.add(Nat.add(D.RcL(D.Fs(m, ps, o), c), D.Pc(p, m, ps, U32.inc(o), c)), D.RcL(D.Fs(m, ps, In.incn(p, U32.inc(o))), c)),
          Nat.add(D.RcL(D.Fs(m, ps, o), c), Nat.add(D.Pc(p, m, ps, U32.inc(o), c), D.RcL(D.Fs(m, ps, In.incn(p, U32.inc(o))), c))),
          N.add_assoc(D.RcL(D.Fs(m, ps, o), c), D.Pc(p, m, ps, U32.inc(o), c), D.RcL(D.Fs(m, ps, In.incn(p, U32.inc(o))), c))))

# the pointers to c of the n cells from o (that the run took), once a cell z
# that may not be read, and that is not one of the table's cells 280 and 282, is set
def Pc.fr(n: Nat, +m: Cr.Cir.Cells, +z: U32, +y: Cr.Cir.Cell, +F: U32, +C: Nat, +o: U32, +c: U32, +hz: {False{} == In.rd(z, F, C) : Bool},
  +n280: {U32.is_eq(280, z) == False{} : Bool}, +n282: {U32.is_eq(282, z) == False{} : Bool}, +h: {True{} == In.Rok(n, m, F, C, o) : Bool}) ->
  {D.Pc(n, Cr.Cir.Cells.set(m, z, y), [], o, c) == D.Pc(n, m, [], o, c) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      +x = Cr.Cir.Cells.get(m, o)
      +ha = Bo.and_l(In.okx(m, F, C, o, x), In.Rok(p, m, F, C, U32.inc(o)), h)
      +hb = Bo.and_r(In.okx(m, F, C, o, x), In.Rok(p, m, F, C, U32.inc(o)), h)
      +ho = Own.rd(o, F, C, Bo.and_l(In.own(o, F, C), In.okn(m, F, C, x), ha))
      +e1 = D.fs.eq(m, z, y, [], o, U.nef(o, z, e => In.ne(o, z, F, C, ho, hz, e)), Own.tblat(m, F, C, o, z, n280, n282, ha))
      %Equal.sym(List<&2, U32>, D.Fs(Cr.Cir.Cells.set(m, z, y), [], o), D.Fs(m, [], o), e1) :
        {Nat.add(D.RcL(_, c), D.Pc(p, Cr.Cir.Cells.set(m, z, y), [], U32.inc(o), c)) == Nat.add(D.RcL(D.Fs(m, [], o), c), D.Pc(p, m, [], U32.inc(o), c)) : Nat}
      %Equal.sym(Nat, D.Pc(p, Cr.Cir.Cells.set(m, z, y), [], U32.inc(o), c), D.Pc(p, m, [], U32.inc(o), c), Pc.fr(p, m, z, y, F, C, U32.inc(o), c, hz, n280, n282, hb)) :
        {Nat.add(D.RcL(D.Fs(m, [], o), c), _) == Nat.add(D.RcL(D.Fs(m, [], o), c), D.Pc(p, m, [], U32.inc(o), c)) : Nat}
      {==}

# The facts of a state
# --------------------

# next is numbered N, from F, and the image's cells and the cache stand for
# their terms
def In.Fa(+m: Cr.Cir.Cells, +next: U32, +N: Nat, +F: U32, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>) -> Data:
  In.P({U32.to_nat(next) == N : Nat}, In.P(N.Le(U32.to_nat(F), N), In.P(In.Im(f0, m, F, N, ks, img), In.P(In.CI(8n, [], fc, m, F, N, ks, img), In.Fb(m, N, F)))))

# the new cell may not be read yet
def Fa.hi(+m: Cr.Cir.Cells, +next: U32, +N: Nat, +F: U32, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  hF: N.Le(272n, U32.to_nat(F)), fa: In.Fa(m, next, N, F, f0, fc, ks, img)) -> {False{} == In.rd(next, F, N) : Bool}:
  (eN, r) = fa
  (hFN, r2) = r
  In.p1({False{} == In.rd(next, F, N) : Bool}, {True{} == In.rd(next, F, 1n+N) : Bool},
    In.rdNew(next, F, N, eN, N.le_trans(16n, 272n, U32.to_nat(F), Unit{}, hF), hFN))

# and may be once taken
def Fa.hr(+m: Cr.Cir.Cells, +next: U32, +N: Nat, +F: U32, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  hF: N.Le(272n, U32.to_nat(F)), fa: In.Fa(m, next, N, F, f0, fc, ks, img)) -> {True{} == In.rd(next, F, 1n+N) : Bool}:
  (eN, r) = fa
  (hFN, r2) = r
  In.p2({False{} == In.rd(next, F, N) : Bool}, {True{} == In.rd(next, F, 1n+N) : Bool},
    In.rdNew(next, F, N, eN, N.le_trans(16n, 272n, U32.to_nat(F), Unit{}, hF), hFN))

def Fa.lF(+m: Cr.Cir.Cells, +next: U32, +N: Nat, +F: U32, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  fa: In.Fa(m, next, N, F, f0, fc, ks, img)) -> N.Le(U32.to_nat(F), U32.to_nat(next)):
  (eN, r) = fa
  (hFN, r2) = r
  N.le_rw_r(U32.to_nat(F), N, U32.to_nat(next), Equal.sym(Nat, U32.to_nat(next), N, eN), hFN)

def Fa.im(+m: Cr.Cir.Cells, +next: U32, +N: Nat, +F: U32, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  fa: In.Fa(m, next, N, F, f0, fc, ks, img)) -> In.Im(f0, m, F, N, ks, img):
  (eN, r) = fa
  (hFN, r2) = r
  (im, r3) = r2
  im

def Fa.ci(+m: Cr.Cir.Cells, +next: U32, +N: Nat, +F: U32, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  fa: In.Fa(m, next, N, F, f0, fc, ks, img)) -> In.CI(8n, [], fc, m, F, N, ks, img):
  (eN, r) = fa
  (hFN, r2) = r
  (im, r3) = r2
  (ci, fb) = r3
  ci

def Fa.fb(+m: Cr.Cir.Cells, +next: U32, +N: Nat, +F: U32, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  fa: In.Fa(m, next, N, F, f0, fc, ks, img)) -> In.Fb(m, N, F):
  (eN, r) = fa
  (hFN, r2) = r
  (im, r3) = r2
  (ci, fb) = r3
  fb

# the field 0 of the cell 0 is 0
def Fa.e0(+m: Cr.Cir.Cells, +next: U32, +N: Nat, +F: U32, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  fa: In.Fa(m, next, N, F, f0, fc, ks, img)) -> {D.Fd(0n, m, 0) == 0 : U32}:
  (eN, r) = fa
  (hFN, r2) = r
  (im, r3) = r2
  (ci, fb) = r3
  (h291, f1) = fb
  (e280, f2) = f1
  (e282, f3) = f2
  (e0, rk) = f3
  e0

def Fa.eN(+m: Cr.Cir.Cells, +next: U32, +N: Nat, +F: U32, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  fa: In.Fa(m, next, N, F, f0, fc, ks, img)) -> {U32.to_nat(next) == N : Nat}:
  (eN, r) = fa
  eN

def Fa.hFN(+m: Cr.Cir.Cells, +next: U32, +N: Nat, +F: U32, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  fa: In.Fa(m, next, N, F, f0, fc, ks, img)) -> N.Le(U32.to_nat(F), N):
  (eN, r) = fa
  (hFN, r2) = r
  hFN

# the facts once the cell next, set to x, is taken
def Fa.step(+m: Cr.Cir.Cells, +next: U32, +N: Nat, +F: U32, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +x: Cr.Cir.Cell, lt: In.lt(next), +hF: N.Le(272n, U32.to_nat(F)), hx: {True{} == In.okn(m, F, N, x) : Bool},
  +fa: In.Fa(m, next, N, F, f0, fc, ks, img)) ->
  In.Fa(Cr.Cir.Cells.set(m, next, x), U32.inc(next), 1n+N, F, f0, fc, ks, img):
  +hi = Fa.hi(m, next, N, F, f0, fc, ks, img, hF, fa)
  +lF = Fa.lF(m, next, N, F, f0, fc, ks, img, fa)
  +eN = Fa.eN(m, next, N, F, f0, fc, ks, img, fa)
  +hFN = Fa.hFN(m, next, N, F, f0, fc, ks, img, fa)
  +im = Fa.im(m, next, N, F, f0, fc, ks, img, fa)
  +ci = Fa.ci(m, next, N, F, f0, fc, ks, img, fa)
  (Equal.trans(Nat, U32.to_nat(U32.inc(next)), 1n+U32.to_nat(next), 1n+N, U.inc(next, 214748364, lt), Equal.cong(Nat, Nat, z => 1n+z, U32.to_nat(next), N, eN)),
   (N.le_succ(U32.to_nat(F), N, hFN),
    (Im.up(f0, Cr.Cir.Cells.set(m, next, x), F, N, ks, img, Im.fr(f0, m, F, N, ks, img, next, x, hi, im)),
     (CI.up(8n, [], fc, Cr.Cir.Cells.set(m, next, x), F, N, ks, img,
       CI.fr(8n, [], fc, m, F, N, ks, img, next, x, hi, N.le_trans(272n, U32.to_nat(F), U32.to_nat(next), hF, lF), ci)),
      Fb.step(m, next, N, F, x, eN, hFN, hi, hx, Fa.fb(m, next, N, F, f0, fc, ks, img, fa))))))

# a term framed over a new cell
def St.step(+f: Nat, +m: Cr.Cir.Cells, +F: U32, +N: Nat, +c: U32, +t: Bk.Term, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +i: U32, +x: Cr.Cir.Cell, +hi: {False{} == In.rd(i, F, N) : Bool}, s: In.St(f, m, F, N, c, t, ks, img)) ->
  In.St(f, Cr.Cir.Cells.set(m, i, x), F, 1n+N, c, t, ks, img):
  St.up(f, Cr.Cir.Cells.set(m, i, x), F, N, c, t, ks, img, St.fr(f, m, F, N, c, t, ks, img, i, x, hi, s))

# the facts once the cache's entry of w8 gets v, which stands for its word
def Fa.cs(+m: Cr.Cir.Cells, +next: U32, +N: Nat, +F: U32, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +w8: Word(8n), +v: U32, +hF: N.Le(272n, U32.to_nat(F)), +sv: In.St(fc, m, F, N, v, Pg.Program.word(8n, w8), ks, img),
  pv: {True{} == In.ps(m, v) : Bool}, +fa: In.Fa(m, next, N, F, f0, fc, ks, img)) -> In.Fa(In.cs(m, w8, v), next, N, F, f0, fc, ks, img):
  +x = Cr.Cir.Cell.set(2n, Cr.Cir.Cells.get(m, In.J(w8)), v)
  +hi = In.rdJ(w8, F, N, hF)
  (Fa.eN(m, next, N, F, f0, fc, ks, img, fa),
   (Fa.hFN(m, next, N, F, f0, fc, ks, img, fa),
    (Im.fr(f0, m, F, N, ks, img, In.J(w8), x, hi, Fa.im(m, next, N, F, f0, fc, ks, img, fa)),
     (CI.st(8n, [], fc, m, F, N, w8, v, ks, img, hF, St.fr(fc, m, F, N, v, Pg.Program.word(8n, w8), ks, img, In.J(w8), x, hi, sv),
       Ps.cs(m, v, w8, F, N, hF, St.rd(fc, m, F, N, v, Pg.Program.word(8n, w8), ks, img, sv), pv), Fa.ci(m, next, N, F, f0, fc, ks, img, fa)),
      Fb.cs(m, N, F, w8, v, Fa.fb(m, next, N, F, f0, fc, ks, img, fa))))))

# The registers
# -------------

# the registers of M.input: focus, ii, ib, il, iu, ij, t1 and t2, the
# others 0
def In.R(+fo: U32, +ii: U32, +ib: U32, +il: U32, +iu: U32, +ij: U32, +t1: U32, +t2: U32) -> List<&2, U32>:
  Con{fo, List.append(&2, U32, List.replicate(U32, 48n, 0), [ii, ib, il, iu, ij, 0, 0, 0, 0, 0, 0, 0, t1, t2])}

def In.R0() -> {List.replicate(U32, Mc.Mach.regs(), 0) == In.R(0, 0, 0, 0, 0, 0, 0, 0) : List<&2, U32>}:
  {==}

# Bits
# ----

def In.b0(y: U32) -> Bool:
  match y:
    case U32{WCon{b, _}}:
      b

def Wd.and_zero(n: Nat, t: Word(n)) -> {Word.zero(n) == Word.and(n, t, Word.zero(n)) : Word(n)}:
  match n:
    case 0n:
      match t:
        case WNil{}:
          {==}
    case 1n+(+p):
      match t:
        case WCon{True{}, +r}:
          Equal.cong(Word(p), Word(1n+p), z => WCon{False{}, z}, Word.zero(p), Word.and(p, r, Word.zero(p)), Wd.and_zero(p, r))
        case WCon{False{}, +r}:
          Equal.cong(Word(p), Word(1n+p), z => WCon{False{}, z}, Word.zero(p), Word.and(p, r, Word.zero(p)), Wd.and_zero(p, r))

# M.pick of the low bit of y: 12 (True) or 13 (False)
def In.pv(y: U32) -> {Bool.pick(U32, In.b0(y), 12, 13) == U32.or(U32.and(12, U32.sub(0, U32.and(y, 1))), U32.and(13, U32.sub(U32.and(y, 1), 1))) : U32}:
  match y:
    case U32{WCon{True{}, +t}}:
      %Wd.and_zero(31n, t) : {12 == U32.or(U32.and(12, U32.sub(0, U32{WCon{True{}, _}})), U32.and(13, U32.sub(U32{WCon{True{}, _}}, 1))) : U32}
      {==}
    case U32{WCon{False{}, +t}}:
      %Wd.and_zero(31n, t) : {13 == U32.or(U32.and(12, U32.sub(0, U32{WCon{False{}, _}})), U32.and(13, U32.sub(U32{WCon{False{}, _}}, 1))) : U32}
      {==}

# the cell of the bit b in the image
def Im.bit(b: Bool, +f0: Nat, +m: Cr.Cir.Cells, +F: U32, +N: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  im: In.Im(f0, m, F, N, ks, img)) -> In.St(f0, m, F, N, Bool.pick(U32, b, 12, 13), Pg.Program.bit(b), ks, img):
  match b:
    case True{}:
      Im.g12(f0, m, F, N, ks, img, im)
    case False{}:
      Im.g13(f0, m, F, N, ks, img, im)

# Loops
# -----

# a round of a while whose condition holds
def In.loop(+f: Nat, +c: Cr.Cir.Expr, +body: Cr.Cir.Stmt, +st: Cr.Cir.State, -Q: Cr.Cir.State -> Type, -R: Cr.Cir.State -> Type,
  -Om: Type, ev: {Some{1} == Cr.Cir.eval(c, st) : Maybe<&2, U32>}, h: In.Ok(Cr.Cir.exec(f, body, st), Q, Om),
  g: @s: Cr.Cir.State -> Q(s) -> In.Ok(Cr.Cir.exec(f, Cr.Cir.Stmt.while{c, body}, s), R, Om)) ->
  In.Ok(Cr.Cir.exec(1n+f, Cr.Cir.Stmt.while{c, body}, st), R, Om):
  %ev : In.Ok(Cr.Cir.exec.if(_, u => Cr.Cir.exec.then(Cr.Cir.exec(f, body, st), t => Cr.Cir.exec(f, Cr.Cir.Stmt.while{c, body}, t)), u => Cr.Cir.Out.next{st}), R, Om)
  In.then(Cr.Cir.exec(f, body, st), t => Cr.Cir.exec(f, Cr.Cir.Stmt.while{c, body}, t), Q, R, Om, h, g)

# the end of a while
def In.loop.end(+f: Nat, +c: Cr.Cir.Expr, +body: Cr.Cir.Stmt, +st: Cr.Cir.State, -R: Cr.Cir.State -> Type,
  -Om: Type, ev: {Some{0} == Cr.Cir.eval(c, st) : Maybe<&2, U32>}, k: R(st)) -> In.Ok(Cr.Cir.exec(1n+f, Cr.Cir.Stmt.while{c, body}, st), R, Om):
  %ev : In.Ok(Cr.Cir.exec.if(_, u => Cr.Cir.exec.then(Cr.Cir.exec(f, body, st), t => Cr.Cir.exec(f, Cr.Cir.Stmt.while{c, body}, t)), u => Cr.Cir.Out.next{st}), R, Om)
  k

# Runs, then more
# ---------------

# s runs from st with the fuel f, then k: the run ends with a state of which
# R holds, or out of memory
def In.Go(f: Nat, s: Cr.Cir.Stmt, st: Cr.Cir.State, k: Cr.Cir.State -> Cr.Cir.Out, R: Cr.Cir.State -> Type, Om: Type) -> Type:
  In.Ok(Cr.Cir.exec.then(Cr.Cir.exec(f, s, st), k), R, Om)

# a run, then k1, then k2, regrouped
def In.assoc(o: Cr.Cir.Out, -k1: Cr.Cir.State -> Cr.Cir.Out, -k2: Cr.Cir.State -> Cr.Cir.Out, -R: Cr.Cir.State -> Type,
  -Om: Type, h: In.Ok(Cr.Cir.exec.then(o, t => Cr.Cir.exec.then(k1(t), k2)), R, Om)) -> In.Ok(Cr.Cir.exec.then(Cr.Cir.exec.then(o, k1), k2), R, Om):
  match o:
    case Cr.Cir.Out.next{st}:
      h
    case Cr.Cir.Out.halt{s, st}:
      h
    case Cr.Cir.Out.out_of_memory{}:
      h
    case Cr.Cir.Out.trap{}:
      h
    case Cr.Cir.Out.not_done{}:
      h

# a then b
def In.sq(+f: Nat, +a: Cr.Cir.Stmt, -b: Cr.Cir.Stmt, +st: Cr.Cir.State, -k: Cr.Cir.State -> Cr.Cir.Out, -R: Cr.Cir.State -> Type,
  -Om: Type, h: In.Go(1n+f, a, st, t => Cr.Cir.exec.then(Cr.Cir.exec(1n+f, b, t), k), R, Om)) -> In.Go(1n+f, Cr.Cir.Stmt.seq{a, b}, st, k, R, Om):
  In.assoc(Cr.Cir.exec(1n+f, a, st), t => Cr.Cir.exec(1n+f, b, t), k, R, Om, h)

# nothing
def In.nop(-f: Nat, -st: Cr.Cir.State, -k: Cr.Cir.State -> Cr.Cir.Out, -R: Cr.Cir.State -> Type, -Om: Type, h: In.Ok(k(st), R, Om)) ->
  In.Go(1n+f, Cr.Cir.Stmt.nop{}, st, k, R, Om):
  h

# register r gets the value v of e
def In.set(+f: Nat, +r: Nat, -e: Cr.Cir.Expr, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +next: U32, +F: U32, +K: U32, +pg: U32, +L: U32,
  +I: List<&2, Word(8n)>, +v: U32, ev: {Some{v} == Cr.Cir.eval(e, In.S(regs, m, next, F, K, pg, L, I)) : Maybe<&2, U32>},
  rl: {True{} == Nat.is_lt(r, List.length(&2, U32, regs)) : Bool}, -k: Cr.Cir.State -> Cr.Cir.Out, -R: Cr.Cir.State -> Type,
  -Om: Type, h: In.Ok(k(In.S(List.set(&2, U32, regs, r, v), m, next, F, K, pg, L, I)), R, Om)) ->
  In.Go(1n+f, Cr.Cir.Stmt.set{r, e}, In.S(regs, m, next, F, K, pg, L, I), k, R, Om):
  +st = In.S(regs, m, next, F, K, pg, L, I)
  %ev : In.Ok(Cr.Cir.exec.then(Cr.Cir.exec.set(r, _, st), k), R, Om)
  %rl : In.Ok(Cr.Cir.exec.then(Cr.Cir.exec.set.of(Cr.Cir.regs.set.if(_, regs, r, v), st), k), R, Om)
  h

# field kf of the cell i, the value of c, gets the value x of v
def In.str(+f: Nat, +kf: Nat, -c: Cr.Cir.Expr, -v: Cr.Cir.Expr, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +next: U32, +F: U32, +K: U32, +pg: U32,
  +L: U32, +I: List<&2, Word(8n)>, +i: U32, +x: U32,
  evc: {Some{i} == Cr.Cir.eval(c, In.S(regs, m, next, F, K, pg, L, I)) : Maybe<&2, U32>},
  evv: {Some{x} == Cr.Cir.eval(v, In.S(regs, m, next, F, K, pg, L, I)) : Maybe<&2, U32>},
  ec: {True{} == Cr.Cir.is_cell(i, K, F, next) : Bool}, -k: Cr.Cir.State -> Cr.Cir.Out, -R: Cr.Cir.State -> Type,
  -Om: Type, h: In.Ok(k(In.S(regs, Cr.Cir.Cells.set(m, i, Cr.Cir.Cell.set(kf, Cr.Cir.Cells.get(m, i), x)), next, F, K, pg, L, I)), R, Om)) ->
  In.Go(1n+f, Cr.Cir.Stmt.store{kf, c, v}, In.S(regs, m, next, F, K, pg, L, I), k, R, Om):
  +st = In.S(regs, m, next, F, K, pg, L, I)
  %evc : In.Ok(Cr.Cir.exec.then(Cr.Cir.exec.store(kf, _, Cr.Cir.eval(v, st), st), k), R, Om)
  %evv : In.Ok(Cr.Cir.exec.then(Cr.Cir.exec.store(kf, Some{i}, _, st), k), R, Om)
  %ec : In.Ok(Cr.Cir.exec.then(Cr.Cir.exec.store.if(_, kf, i, x, st), k), R, Om)
  h

# a round of a while whose condition holds
def In.wh(+f: Nat, +c: Cr.Cir.Expr, +body: Cr.Cir.Stmt, +st: Cr.Cir.State, -k: Cr.Cir.State -> Cr.Cir.Out, -R: Cr.Cir.State -> Type,
  -Om: Type, ev: {Some{1} == Cr.Cir.eval(c, st) : Maybe<&2, U32>},
  h: In.Go(f, body, st, t => Cr.Cir.exec.then(Cr.Cir.exec(f, Cr.Cir.Stmt.while{c, body}, t), k), R, Om)) ->
  In.Go(1n+f, Cr.Cir.Stmt.while{c, body}, st, k, R, Om):
  %ev : In.Ok(Cr.Cir.exec.then(Cr.Cir.exec.if(_, u => Cr.Cir.exec.then(Cr.Cir.exec(f, body, st), t => Cr.Cir.exec(f, Cr.Cir.Stmt.while{c, body}, t)),
    u => Cr.Cir.Out.next{st}), k), R, Om)
  In.assoc(Cr.Cir.exec(f, body, st), t => Cr.Cir.exec(f, Cr.Cir.Stmt.while{c, body}, t), k, R, Om, h)

# the end of a while
def In.wh.end(+f: Nat, +c: Cr.Cir.Expr, +body: Cr.Cir.Stmt, +st: Cr.Cir.State, -k: Cr.Cir.State -> Cr.Cir.Out, -R: Cr.Cir.State -> Type,
  -Om: Type, ev: {Some{0} == Cr.Cir.eval(c, st) : Maybe<&2, U32>}, h: In.Ok(k(st), R, Om)) -> In.Go(1n+f, Cr.Cir.Stmt.while{c, body}, st, k, R, Om):
  %ev : In.Ok(Cr.Cir.exec.then(Cr.Cir.exec.if(_, u => Cr.Cir.exec.then(Cr.Cir.exec(f, body, st), t => Cr.Cir.exec(f, Cr.Cir.Stmt.while{c, body}, t)),
    u => Cr.Cir.Out.next{st}), k), R, Om)
  h

# if c then t else e, when c is not 0
def In.ifT(+f: Nat, +c: Cr.Cir.Expr, -t: Cr.Cir.Stmt, -e: Cr.Cir.Stmt, +st: Cr.Cir.State, +x: U32,
  ev: {Some{x} == Cr.Cir.eval(c, st) : Maybe<&2, U32>}, ez: {False{} == U32.is_zero(x) : Bool},
  -k: Cr.Cir.State -> Cr.Cir.Out, -R: Cr.Cir.State -> Type, -Om: Type, h: In.Go(1n+f, t, st, k, R, Om)) -> In.Go(1n+f, Cr.Cir.Stmt.if{c, t, e}, st, k, R, Om):
  %ev : In.Ok(Cr.Cir.exec.then(Cr.Cir.exec.if(_, u => Cr.Cir.exec(1n+f, t, st), u => Cr.Cir.exec(1n+f, e, st)), k), R, Om)
  %ez : In.Ok(Cr.Cir.exec.then(Cr.Cir.exec.if.of(_, u => Cr.Cir.exec(1n+f, t, st), u => Cr.Cir.exec(1n+f, e, st)), k), R, Om)
  h

# if c then t else e, when c is 0
def In.ifF(+f: Nat, +c: Cr.Cir.Expr, -t: Cr.Cir.Stmt, -e: Cr.Cir.Stmt, +st: Cr.Cir.State, +x: U32,
  ev: {Some{x} == Cr.Cir.eval(c, st) : Maybe<&2, U32>}, ez: {True{} == U32.is_zero(x) : Bool},
  -k: Cr.Cir.State -> Cr.Cir.Out, -R: Cr.Cir.State -> Type, -Om: Type, h: In.Go(1n+f, e, st, k, R, Om)) -> In.Go(1n+f, Cr.Cir.Stmt.if{c, t, e}, st, k, R, Om):
  %ev : In.Ok(Cr.Cir.exec.then(Cr.Cir.exec.if(_, u => Cr.Cir.exec(1n+f, t, st), u => Cr.Cir.exec(1n+f, e, st)), k), R, Om)
  %ez : In.Ok(Cr.Cir.exec.then(Cr.Cir.exec.if.of(_, u => Cr.Cir.exec(1n+f, t, st), u => Cr.Cir.exec(1n+f, e, st)), k), R, Om)
  h

# M.make, then k
def In.mk(+f: Nat, +r: Nat, +h: Cr.Cir.Expr, +a: Cr.Cir.Expr, +b: Cr.Cir.Expr, +c: Cr.Cir.Expr, +regs: List<&2, U32>, +m: Cr.Cir.Cells,
  +next: U32, +F: U32, +K: U32, +pg: U32, +L: U32, +I: List<&2, Word(8n)>, +vh: U32, +va: U32, +vb: U32, +vc: U32,
  +Bc: Nat, hb: N.Le(1n+U32.to_nat(next), Bc), p0: {Some{0} == List.get(&2, U32, regs, 3n) : Maybe<&2, U32>}, rl: {True{} == Nat.is_lt(r, List.length(&2, U32, regs)) : Bool},
  +er: {Some{next} == List.get(&2, U32, List.set(&2, U32, regs, r, next), r) : Maybe<&2, U32>},
  ec: In.lt(next) -> {True{} == Cr.Cir.is_cell(next, K, F, U32.inc(next)) : Bool},
  eh: @m2: Cr.Cir.Cells -> @pg2: U32 -> {Some{vh} == Cr.Cir.eval(h, In.S(List.set(&2, U32, regs, r, next), m2, U32.inc(next), F, K, pg2, L, I)) : Maybe<&2, U32>},
  ea: @m2: Cr.Cir.Cells -> @pg2: U32 -> {Some{va} == Cr.Cir.eval(a, In.S(List.set(&2, U32, regs, r, next), m2, U32.inc(next), F, K, pg2, L, I)) : Maybe<&2, U32>},
  eb: @m2: Cr.Cir.Cells -> @pg2: U32 -> {Some{vb} == Cr.Cir.eval(b, In.S(List.set(&2, U32, regs, r, next), m2, U32.inc(next), F, K, pg2, L, I)) : Maybe<&2, U32>},
  ef: @m2: Cr.Cir.Cells -> @pg2: U32 -> {Some{vc} == Cr.Cir.eval(c, In.S(List.set(&2, U32, regs, r, next), m2, U32.inc(next), F, K, pg2, L, I)) : Maybe<&2, U32>},
  -k: Cr.Cir.State -> Cr.Cir.Out, -R: Cr.Cir.State -> Type,
  g: @pg2: U32 -> In.lt(next) -> In.Ok(k(In.S(List.set(&2, U32, regs, r, next), Cr.Cir.Cells.set(m, next, Cr.Cir.Cell{vh, 1, va, vb, vc}), U32.inc(next), F, K, pg2, L, I)), R, In.oom(L, Bc))) ->
  In.Go(1n+f, Mc.M.make(r, h, a, b, c), In.S(regs, m, next, F, K, pg, L, I), k, R, In.oom(L, Bc)):
  +rg = List.set(&2, U32, regs, r, next)
  +ms = Cr.Cir.Cells.set(m, next, Cr.Cir.Cell{vh, 1, va, vb, vc})
  In.then(Cr.Cir.exec(1n+f, Mc.M.make(r, h, a, b, c), In.S(regs, m, next, F, K, pg, L, I)), k,
    s => In.Is(s, rg, ms, U32.inc(next), F, K, L, I, In.lt(next)), R,
    In.oom(L, Bc), In.make(f, r, h, a, b, c, regs, m, next, F, K, pg, L, I, vh, va, vb, vc, Bc, hb, p0, rl, er, ec, eh, ea, eb, ef),
    s => e => In.at(s, rg, ms, U32.inc(next), F, K, L, I, In.lt(next), R, In.oom(L, Bc), k, e, g))

# The cells that the run keeps
# ----------------------------

# the cell j is one that the run keeps: one of the image's first 16, or one
# from the table on, before F
def In.kp(+j: U32, +F: U32) -> Bool:
  Bool.or(Nat.is_lt(U32.to_nat(j), 16n), Bool.and(Nat.is_le(272n, U32.to_nat(j)), Nat.is_lt(U32.to_nat(j), U32.to_nat(F))))

# m holds the cells of m0 that the run keeps
def In.Fr(m0: Cr.Cir.Cells, m: Cr.Cir.Cells, F: U32) -> Type:
  @j: U32 -> {True{} == In.kp(j, F) : Bool} -> {Cr.Cir.Cells.get(m0, j) == Cr.Cir.Cells.get(m, j) : Cr.Cir.Cell}

def Fr.refl(-m0: Cr.Cir.Cells, -F: U32) -> In.Fr(m0, m0, F):
  j => h => {==}

# a cell from F on is none that the run keeps
def In.kpNew(+i: U32, +F: U32, hF: N.Le(272n, U32.to_nat(F)), +hi: N.Le(U32.to_nat(F), U32.to_nat(i))) -> {False{} == In.kp(i, F) : Bool}:
  +ti = U32.to_nat(i)
  +tF = U32.to_nat(F)
  +h272 = N.le_trans(272n, tF, ti, hF, hi)
  %Na.lt_f(ti, 16n, N.le_trans(16n, 272n, ti, Unit{}, h272)) : {False{} == Bool.or(_, Bool.and(Nat.is_le(272n, ti), Nat.is_lt(ti, tF))) : Bool}
  %Na.le_t(272n, ti, h272) : {False{} == Bool.or(False{}, Bool.and(_, Nat.is_lt(ti, tF))) : Bool}
  %Na.lt_f(ti, tF, hi) : {False{} == Bool.or(False{}, Bool.and(True{}, _)) : Bool}
  {==}

# a cache cell is none that the run keeps
def In.kpJ(+w: Word(8n), +F: U32) -> {False{} == In.kp(In.J(w), F) : Bool}:
  +tJ = U32.to_nat(In.J(w))
  %Na.lt_f(tJ, 16n, In.Jlo(w)) : {False{} == Bool.or(_, Bool.and(Nat.is_le(272n, tJ), Nat.is_lt(tJ, U32.to_nat(F)))) : Bool}
  %Na.le_f(272n, tJ, In.Jhi(w)) : {False{} == Bool.or(False{}, Bool.and(_, Nat.is_lt(tJ, U32.to_nat(F)))) : Bool}
  {==}

def In.kpne(+j: U32, +i: U32, +F: U32, h: {True{} == In.kp(j, F) : Bool}, hi: {False{} == In.kp(i, F) : Bool}, e: {j == i : U32}) -> Empty:
  N.true_ne_false(Equal.trans(Bool, True{}, In.kp(j, F), False{}, h,
    Equal.trans(Bool, In.kp(j, F), In.kp(i, F), False{}, Equal.cong(U32, Bool, z => In.kp(z, F), j, i, e),
      Equal.sym(Bool, False{}, In.kp(i, F), hi))))

# a set of a cell that the run does not keep
def Fr.set(-m0: Cr.Cir.Cells, +m: Cr.Cir.Cells, +F: U32, +i: U32, +x: Cr.Cir.Cell, +hi: {False{} == In.kp(i, F) : Bool},
  fr: In.Fr(m0, m, F)) -> In.Fr(m0, Cr.Cir.Cells.set(m, i, x), F):
  +j => +h => Equal.trans(Cr.Cir.Cell, Cr.Cir.Cells.get(m0, j), Cr.Cir.Cells.get(m, j), Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, i, x), j),
    fr(j, h), Cl.get_other(m, j, i, x, e => In.kpne(j, i, F, h, hi, e)))

# a new cell
def Fr.step(-m0: Cr.Cir.Cells, +m: Cr.Cir.Cells, +F: U32, +i: U32, +x: Cr.Cir.Cell, hF: N.Le(272n, U32.to_nat(F)),
  hi: N.Le(U32.to_nat(F), U32.to_nat(i)), fr: In.Fr(m0, m, F)) -> In.Fr(m0, Cr.Cir.Cells.set(m, i, x), F):
  Fr.set(m0, m, F, i, x, In.kpNew(i, F, hF, hi), fr)

# the cache's entry of w8
def Fr.cs(-m0: Cr.Cir.Cells, +m: Cr.Cir.Cells, +F: U32, +w8: Word(8n), +v: U32, fr: In.Fr(m0, m, F)) -> In.Fr(m0, In.cs(m, w8, v), F):
  Fr.set(m0, m, F, In.J(w8), Cr.Cir.Cell.set(2n, Cr.Cir.Cells.get(m, In.J(w8)), v), In.kpJ(w8, F), fr)

# The code of M.input
# -------------------

def In.c.i1() -> Cr.Cir.Stmt:
  Mc.M.set(Mc.R.ij(), Mc.M.sub(Mc.M.g(Mc.R.ij()), Mc.M.c(1)))

def In.c.i2() -> Cr.Cir.Stmt:
  Mc.M.make(Mc.R.t1(), Mc.M.c(Mc.M.h.static()), Mc.M.g(Mc.R.iu()), Mc.M.c(Mc.I.lab(Mc.N.unit())), Mc.M.c(0))

def In.c.pick() -> Cr.Cir.Expr:
  Mc.M.pick(Mc.M.and(Mc.M.shr(Mc.M.g(Mc.R.ib()), Mc.M.g(Mc.R.ij())), Mc.M.c(1)), Mc.M.c(Mc.I.true()), Mc.M.c(Mc.I.false()))

def In.c.i3() -> Cr.Cir.Stmt:
  Mc.M.make(Mc.R.t2(), Mc.M.c(Mc.M.h.static()), In.c.pick(), Mc.M.g(Mc.R.t1()), Mc.M.c(0))

def In.c.i4() -> Cr.Cir.Stmt:
  Mc.M.make(Mc.R.iu(), Mc.M.c(Mc.M.h.static()), Mc.M.c(Mc.I.lab(Mc.N.wcon())), Mc.M.g(Mc.R.t2()), Mc.M.c(0))

def In.c.inner() -> Cr.Cir.Stmt:
  Mc.M.do([In.c.i1(), In.c.i2(), In.c.i3(), In.c.i4()])

# the bit j of ib
def In.bit(+ib: U32, +j: U32) -> Bool:
  In.b0(U32.shrn(ib, U32.to_nat(U32.and(j, 31))))

# the pick of the bit: 12 or 13
def In.evpick(+fo: U32, +ii: U32, +ib: U32, +il: U32, +iu: U32, +ij: U32, +t1: U32, +t2: U32, +m: Cr.Cir.Cells, +next: U32,
  +F: U32, +K: U32, +pg: U32, +L: U32, +I: List<&2, Word(8n)>) ->
  {Some{Bool.pick(U32, In.bit(ib, ij), 12, 13)} == Cr.Cir.eval(In.c.pick(), In.S(In.R(fo, ii, ib, il, iu, ij, t1, t2), m, next, F, K, pg, L, I)) : Maybe<&2, U32>}:
  +y = U32.shrn(ib, U32.to_nat(U32.and(ij, 31)))
  %Equal.sym(U32, Bool.pick(U32, In.b0(y), 12, 13), U32.or(U32.and(12, U32.sub(0, U32.and(y, 1))), U32.and(13, U32.sub(U32.and(y, 1), 1))), In.pv(y)) :
    {Some{_} == Cr.Cir.eval(In.c.pick(), In.S(In.R(fo, ii, ib, il, iu, ij, t1, t2), m, next, F, K, pg, L, I)) : Maybe<&2, U32>}
  {==}

# The bits' loop
# --------------

# what a round of the bits' loop gives: the word iu2 of 1 + n bits, the bit
# of ib at j in front of t, with the fuel fw and the count N
def In.ir.K(+fo: U32, +ii: U32, +ib: U32, +il: U32, +j: U32, +N: Nat, +F: U32, +K: U32, +L: U32, +I: List<&2, Word(8n)>, +f0: Nat,
  +fc: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, -m0: Cr.Cir.Cells, +fw: Nat, +n: Nat, +t: Word(n), +fl: Nat, +bl: Bk.Term,
  -k: Cr.Cir.State -> Cr.Cir.Out, -R: Cr.Cir.State -> Type, +Bc: Nat) -> Type:
  @iu2: U32 -> @t12: U32 -> @t22: U32 -> @m2: Cr.Cir.Cells -> @nx2: U32 -> @pg2: U32 -> In.Fa(m2, nx2, N, F, f0, fc, ks, img) ->
    In.St(fw, m2, F, N, iu2, Pg.Program.word(1n+n, WCon{In.bit(ib, j), t}), ks, img) -> {True{} == In.ps(m2, iu2) : Bool} -> In.St(fl, m2, F, N, il, bl, ks, img) ->
    In.Fr(m0, m2, F) -> In.Ok(k(In.S(In.R(fo, ii, ib, il, iu2, j, t12, t22), m2, nx2, F, K, pg2, L, I)), R, In.oom(L, Bc))

# the third make of a round: iu gets WCon in front of the cell t2
def In.ir.c(+f: Nat, +fo: U32, +ii: U32, +ib: U32, +il: U32, +iu: U32, +j: U32, +t1: U32, +t2: U32, +m: Cr.Cir.Cells, +next: U32,
  +N: Nat, +F: U32, +K: U32, +pg: U32, +L: U32, +I: List<&2, Word(8n)>, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  -m0: Cr.Cir.Cells, +fw: Nat, +n: Nat, +t: Word(n), +fl: Nat, +bl: Bk.Term,
  +hF: N.Le(272n, U32.to_nat(F)), +hw: N.Le(f0, fw), +fa: In.Fa(m, next, N, F, f0, fc, ks, img),
  +s2: In.St(fw, m, F, N, t2, Bk.Term.Tup{Bk.Quan.Q1{}, Pg.Program.bit(In.bit(ib, j)), Bk.Term.Tup{Bk.Quan.Q1{}, Pg.Program.word(n, t), Bk.Term.Lab{Pg.Program.name.unit()}}}, ks, img),
  +pt2: {True{} == In.ps(m, t2) : Bool}, +sl: In.St(fl, m, F, N, il, bl, ks, img), fr: In.Fr(m0, m, F),
  +Bc: Nat, +hB: N.Le(1n+N, Bc), -k: Cr.Cir.State -> Cr.Cir.Out, -R: Cr.Cir.State -> Type,
  g: In.ir.K(fo, ii, ib, il, j, 1n+N, F, K, L, I, f0, fc, ks, img, m0, 1n+fw, n, t, fl, bl, k, R, Bc)) ->
  In.Go(1n+f, Mc.M.do([In.c.i4()]), In.S(In.R(fo, ii, ib, il, iu, j, t1, t2), m, next, F, K, pg, L, I), k, R, In.oom(L, Bc)):
  In.sq(f, In.c.i4(), Mc.M.do([]), In.S(In.R(fo, ii, ib, il, iu, j, t1, t2), m, next, F, K, pg, L, I), k, R,
   In.oom(L, Bc), In.mk(f, Mc.R.iu(), Mc.M.c(Mc.M.h.static()), Mc.M.c(Mc.I.lab(Mc.N.wcon())), Mc.M.g(Mc.R.t2()), Mc.M.c(0), In.R(fo, ii, ib, il, iu, j, t1, t2), m, next,
    F, K, pg, L, I, In.hd(True{}), 5, t2, 0,
    Bc, In.hb(next, N, Bc, Fa.eN(m, next, N, F, f0, fc, ks, img, fa), hB), {==}, {==}, {==}, lt => In.cellNew(next, K, F, lt, Fa.lF(m, next, N, F, f0, fc, ks, img, fa)),
    m4 => pg4 => {==}, m4 => pg4 => {==}, m4 => pg4 => {==}, m4 => pg4 => {==}, t => Cr.Cir.exec.then(Cr.Cir.exec(1n+f, Mc.M.do([]), t), k), R,
    +pg3 => +lt3 =>
     In.nop(f, In.S(In.R(fo, ii, ib, il, next, j, t1, t2), Cr.Cir.Cells.set(m, next, Cr.Cir.Cell{In.hd(True{}), 1, 5, t2, 0}), U32.inc(next), F, K, pg3, L, I), k, R,
       In.oom(L, Bc), g(next, t1, t2, Cr.Cir.Cells.set(m, next, Cr.Cir.Cell{In.hd(True{}), 1, 5, t2, 0}), U32.inc(next), pg3,
         Fa.step(m, next, N, F, f0, fc, ks, img, Cr.Cir.Cell{In.hd(True{}), 1, 5, t2, 0}, lt3, hF,
           In.okn.mk(m, F, N, In.hd(True{}), 5, t2, {==},
             St.pt(fw, m, F, N, t2, Bk.Term.Tup{Bk.Quan.Q1{}, Pg.Program.bit(In.bit(ib, j)), Bk.Term.Tup{Bk.Quan.Q1{}, Pg.Program.word(n, t), Bk.Term.Lab{Pg.Program.name.unit()}}}, ks, img, Fa.e0(m, next, N, F, f0, fc, ks, img, fa), s2),
             In.hdr.st(m, 5, t2, {==}, pt2)), fa),
         In.tup(True{}, fw, m, F, N, next, 5, t2, Bk.Term.Lab{Pg.Program.name.wcon()},
           Bk.Term.Tup{Bk.Quan.Q1{}, Pg.Program.bit(In.bit(ib, j)), Bk.Term.Tup{Bk.Quan.Q1{}, Pg.Program.word(n, t), Bk.Term.Lab{Pg.Program.name.unit()}}}, ks, img,
           St.to(f0, fw, hw, m, F, N, 5, Bk.Term.Lab{Pg.Program.name.wcon()}, ks, img, Im.g5(f0, m, F, N, ks, img, Fa.im(m, next, N, F, f0, fc, ks, img, fa))),
           s2, Fa.hi(m, next, N, F, f0, fc, ks, img, hF, fa), Fa.hr(m, next, N, F, f0, fc, ks, img, hF, fa)),
         In.ps.mk(m, next, 5, t2),
         St.step(fl, m, F, N, il, bl, ks, img, next, Cr.Cir.Cell{In.hd(True{}), 1, 5, t2, 0}, Fa.hi(m, next, N, F, f0, fc, ks, img, hF, fa), sl),
         Fr.step(m0, m, F, next, Cr.Cir.Cell{In.hd(True{}), 1, 5, t2, 0}, hF, Fa.lF(m, next, N, F, f0, fc, ks, img, fa), fr)))))

# the second make of a round: t2 gets the bit in front of the cell t1
def In.ir.b(+f: Nat, +fo: U32, +ii: U32, +ib: U32, +il: U32, +iu: U32, +j: U32, +t1: U32, +t2: U32, +m: Cr.Cir.Cells, +next: U32,
  +N: Nat, +F: U32, +K: U32, +pg: U32, +L: U32, +I: List<&2, Word(8n)>, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  -m0: Cr.Cir.Cells, +fw: Nat, +n: Nat, +t: Word(n), +fl: Nat, +bl: Bk.Term,
  +hF: N.Le(272n, U32.to_nat(F)), +hw: N.Le(f0, fw), +fa: In.Fa(m, next, N, F, f0, fc, ks, img),
  +s1: In.St(fw, m, F, N, t1, Bk.Term.Tup{Bk.Quan.Q1{}, Pg.Program.word(n, t), Bk.Term.Lab{Pg.Program.name.unit()}}, ks, img),
  +pt1: {True{} == In.ps(m, t1) : Bool}, +sl: In.St(fl, m, F, N, il, bl, ks, img), fr: In.Fr(m0, m, F),
  +Bc: Nat, +hB: N.Le(2n+N, Bc), -k: Cr.Cir.State -> Cr.Cir.Out, -R: Cr.Cir.State -> Type,
  g: In.ir.K(fo, ii, ib, il, j, 1n+(1n+N), F, K, L, I, f0, fc, ks, img, m0, 1n+(1n+fw), n, t, fl, bl, k, R, Bc)) ->
  In.Go(1n+f, Mc.M.do([In.c.i3(), In.c.i4()]), In.S(In.R(fo, ii, ib, il, iu, j, t1, t2), m, next, F, K, pg, L, I), k, R, In.oom(L, Bc)):
  In.sq(f, In.c.i3(), Mc.M.do([In.c.i4()]), In.S(In.R(fo, ii, ib, il, iu, j, t1, t2), m, next, F, K, pg, L, I), k, R,
   In.oom(L, Bc), In.mk(f, Mc.R.t2(), Mc.M.c(Mc.M.h.static()), In.c.pick(), Mc.M.g(Mc.R.t1()), Mc.M.c(0), In.R(fo, ii, ib, il, iu, j, t1, t2), m, next,
    F, K, pg, L, I, In.hd(True{}), Bool.pick(U32, In.bit(ib, j), 12, 13), t1, 0,
    Bc, In.hb(next, N, Bc, Fa.eN(m, next, N, F, f0, fc, ks, img, fa), N.weaken(1n+N, Bc, hB)), {==}, {==}, {==}, lt => In.cellNew(next, K, F, lt, Fa.lF(m, next, N, F, f0, fc, ks, img, fa)),
    m4 => pg4 => {==}, m4 => pg4 => In.evpick(fo, ii, ib, il, iu, j, t1, next, m4, U32.inc(next), F, K, pg4, L, I),
    m4 => pg4 => {==}, m4 => pg4 => {==}, t => Cr.Cir.exec.then(Cr.Cir.exec(1n+f, Mc.M.do([In.c.i4()]), t), k), R,
    +pg3 => +lt3 =>
     In.ir.c(f, fo, ii, ib, il, iu, j, t1, next, Cr.Cir.Cells.set(m, next, Cr.Cir.Cell{In.hd(True{}), 1, Bool.pick(U32, In.bit(ib, j), 12, 13), t1, 0}),
       U32.inc(next), 1n+N, F, K, pg3, L, I, f0, fc, ks, img, m0, 1n+fw, n, t, fl, bl, hF, N.le_succ(f0, fw, hw),
       Fa.step(m, next, N, F, f0, fc, ks, img, Cr.Cir.Cell{In.hd(True{}), 1, Bool.pick(U32, In.bit(ib, j), 12, 13), t1, 0}, lt3, hF,
         In.okn.mk(m, F, N, In.hd(True{}), Bool.pick(U32, In.bit(ib, j), 12, 13), t1, In.pt.bit(In.bit(ib, j), F, N),
           St.pt(fw, m, F, N, t1, Bk.Term.Tup{Bk.Quan.Q1{}, Pg.Program.word(n, t), Bk.Term.Lab{Pg.Program.name.unit()}}, ks, img, Fa.e0(m, next, N, F, f0, fc, ks, img, fa), s1),
           In.hdr.st(m, Bool.pick(U32, In.bit(ib, j), 12, 13), t1, In.ps.bit(In.bit(ib, j), m), pt1)), fa),
       In.tup(True{}, fw, m, F, N, next, Bool.pick(U32, In.bit(ib, j), 12, 13), t1, Pg.Program.bit(In.bit(ib, j)),
         Bk.Term.Tup{Bk.Quan.Q1{}, Pg.Program.word(n, t), Bk.Term.Lab{Pg.Program.name.unit()}}, ks, img,
         St.to(f0, fw, hw, m, F, N, Bool.pick(U32, In.bit(ib, j), 12, 13), Pg.Program.bit(In.bit(ib, j)), ks, img,
           Im.bit(In.bit(ib, j), f0, m, F, N, ks, img, Fa.im(m, next, N, F, f0, fc, ks, img, fa))),
         s1, Fa.hi(m, next, N, F, f0, fc, ks, img, hF, fa), Fa.hr(m, next, N, F, f0, fc, ks, img, hF, fa)),
       In.ps.mk(m, next, Bool.pick(U32, In.bit(ib, j), 12, 13), t1),
       St.step(fl, m, F, N, il, bl, ks, img, next, Cr.Cir.Cell{In.hd(True{}), 1, Bool.pick(U32, In.bit(ib, j), 12, 13), t1, 0},
         Fa.hi(m, next, N, F, f0, fc, ks, img, hF, fa), sl),
       Fr.step(m0, m, F, next, Cr.Cir.Cell{In.hd(True{}), 1, Bool.pick(U32, In.bit(ib, j), 12, 13), t1, 0}, hF, Fa.lF(m, next, N, F, f0, fc, ks, img, fa), fr),
       Bc, hB, k, R, g)))

# a round of the bits' loop: ij goes down by one, and iu gets the bit of ib
# at ij in front
def In.ir(+f: Nat, +fo: U32, +ii: U32, +ib: U32, +il: U32, +iu: U32, +jp: U32, +t1: U32, +t2: U32, +m: Cr.Cir.Cells, +next: U32,
  +N: Nat, +F: U32, +K: U32, +pg: U32, +L: U32, +I: List<&2, Word(8n)>, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  -m0: Cr.Cir.Cells, +fw: Nat, +n: Nat, +t: Word(n), +fl: Nat, +bl: Bk.Term,
  +hF: N.Le(272n, U32.to_nat(F)), +hw: N.Le(f0, fw), +fa: In.Fa(m, next, N, F, f0, fc, ks, img),
  +sw: In.St(fw, m, F, N, iu, Pg.Program.word(n, t), ks, img), +pu: {True{} == In.ps(m, iu) : Bool}, +sl: In.St(fl, m, F, N, il, bl, ks, img), fr: In.Fr(m0, m, F),
  +Bc: Nat, +hB: N.Le(3n+N, Bc), -k: Cr.Cir.State -> Cr.Cir.Out, -R: Cr.Cir.State -> Type,
  g: In.ir.K(fo, ii, ib, il, U32.sub(jp, 1), 3n+N, F, K, L, I, f0, fc, ks, img, m0, 3n+fw, n, t, fl, bl, k, R, Bc)) ->
  In.Go(1n+f, In.c.inner(), In.S(In.R(fo, ii, ib, il, iu, jp, t1, t2), m, next, F, K, pg, L, I), k, R, In.oom(L, Bc)):
  In.sq(f, In.c.i1(), Mc.M.do([In.c.i2(), In.c.i3(), In.c.i4()]), In.S(In.R(fo, ii, ib, il, iu, jp, t1, t2), m, next, F, K, pg, L, I), k, R,
   In.oom(L, Bc), In.set(f, Mc.R.ij(), Mc.M.sub(Mc.M.g(Mc.R.ij()), Mc.M.c(1)), In.R(fo, ii, ib, il, iu, jp, t1, t2), m, next, F, K, pg, L, I, U32.sub(jp, 1), {==}, {==},
    t => Cr.Cir.exec.then(Cr.Cir.exec(1n+f, Mc.M.do([In.c.i2(), In.c.i3(), In.c.i4()]), t), k), R,
    In.oom(L, Bc), In.sq(f, In.c.i2(), Mc.M.do([In.c.i3(), In.c.i4()]), In.S(In.R(fo, ii, ib, il, iu, U32.sub(jp, 1), t1, t2), m, next, F, K, pg, L, I), k, R,
     In.oom(L, Bc), In.mk(f, Mc.R.t1(), Mc.M.c(Mc.M.h.static()), Mc.M.g(Mc.R.iu()), Mc.M.c(Mc.I.lab(Mc.N.unit())), Mc.M.c(0), In.R(fo, ii, ib, il, iu, U32.sub(jp, 1), t1, t2),
      m, next, F, K, pg, L, I, In.hd(True{}), iu, 1, 0,
      Bc, In.hb(next, N, Bc, Fa.eN(m, next, N, F, f0, fc, ks, img, fa), N.weaken(1n+N, Bc, N.weaken(2n+N, Bc, hB))), {==}, {==}, {==}, lt => In.cellNew(next, K, F, lt, Fa.lF(m, next, N, F, f0, fc, ks, img, fa)),
      m4 => pg4 => {==}, m4 => pg4 => {==}, m4 => pg4 => {==}, m4 => pg4 => {==}, t => Cr.Cir.exec.then(Cr.Cir.exec(1n+f, Mc.M.do([In.c.i3(), In.c.i4()]), t), k), R,
      +pg3 => +lt3 =>
       In.ir.b(f, fo, ii, ib, il, iu, U32.sub(jp, 1), next, t2, Cr.Cir.Cells.set(m, next, Cr.Cir.Cell{In.hd(True{}), 1, iu, 1, 0}),
         U32.inc(next), 1n+N, F, K, pg3, L, I, f0, fc, ks, img, m0, 1n+fw, n, t, fl, bl, hF, N.le_succ(f0, fw, hw),
         Fa.step(m, next, N, F, f0, fc, ks, img, Cr.Cir.Cell{In.hd(True{}), 1, iu, 1, 0}, lt3, hF,
           In.okn.mk(m, F, N, In.hd(True{}), iu, 1, St.pt(fw, m, F, N, iu, Pg.Program.word(n, t), ks, img, Fa.e0(m, next, N, F, f0, fc, ks, img, fa), sw), {==},
             In.hdr.st(m, iu, 1, pu, {==})), fa),
         In.tup(True{}, fw, m, F, N, next, iu, 1, Pg.Program.word(n, t), Bk.Term.Lab{Pg.Program.name.unit()}, ks, img, sw,
           St.to(f0, fw, hw, m, F, N, 1, Bk.Term.Lab{Pg.Program.name.unit()}, ks, img, Im.g1(f0, m, F, N, ks, img, Fa.im(m, next, N, F, f0, fc, ks, img, fa))),
           Fa.hi(m, next, N, F, f0, fc, ks, img, hF, fa), Fa.hr(m, next, N, F, f0, fc, ks, img, hF, fa)),
         In.ps.mk(m, next, iu, 1),
         St.step(fl, m, F, N, il, bl, ks, img, next, Cr.Cir.Cell{In.hd(True{}), 1, iu, 1, 0}, Fa.hi(m, next, N, F, f0, fc, ks, img, hF, fa), sl),
         Fr.step(m0, m, F, next, Cr.Cir.Cell{In.hd(True{}), 1, iu, 1, 0}, hF, Fa.lF(m, next, N, F, f0, fc, ks, img, fa), fr),
         Bc, hB, k, R, g)))))

# the bits' loop
def In.c.W() -> Cr.Cir.Stmt:
  Mc.M.while(Mc.M.ne(Mc.M.g(Mc.R.ij()), Mc.M.c(0)), In.c.inner())

# the word of the low byte of ib, the lowest bit first
def In.wd(+ib: U32) -> Word(8n):
  WCon{In.bit(ib, 0), WCon{In.bit(ib, 1), WCon{In.bit(ib, 2), WCon{In.bit(ib, 3), WCon{In.bit(ib, 4), WCon{In.bit(ib, 5), WCon{In.bit(ib, 6),
    WCon{In.bit(ib, 7), WNil{}}}}}}}}}

# the word that the bits' loop builds
def In.wd.eq(+ib: U32) -> {Pg.Program.word(1n+(1n+(1n+(1n+(1n+(1n+(1n+(1n+0n))))))), WCon{In.bit(ib, U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1), 1), 1), 1), 1)), WCon{In.bit(ib, U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1), 1), 1), 1)), WCon{In.bit(ib, U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1), 1), 1)), WCon{In.bit(ib, U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1), 1)), WCon{In.bit(ib, U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1)), WCon{In.bit(ib, U32.sub(U32.sub(U32.sub(8, 1), 1), 1)), WCon{In.bit(ib, U32.sub(U32.sub(8, 1), 1)), WCon{In.bit(ib, U32.sub(8, 1)), WNil{}}}}}}}}}) == Pg.Program.word(8n, In.wd(ib)) : Bk.Term}:
  {==}

# a term, by an equation
def St.cast(-f: Nat, -m: Cr.Cir.Cells, -F: U32, -N: Nat, -c: U32, -t: Bk.Term, -u: Bk.Term, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>,
  e: {t == u : Bk.Term}, s: In.St(f, m, F, N, c, t, ks, img)) -> In.St(f, m, F, N, c, u, ks, img):
  %e : In.St(f, m, F, N, c, _, ks, img)
  s

# the bits' loop: iu gets the word of the low byte of ib, over the image's
# WNil, in 8 rounds of 3 new cells
def In.il(+Z: Nat, +fo: U32, +ii: U32, +ib: U32, +il: U32, +t1: U32, +t2: U32, +m: Cr.Cir.Cells, +next: U32,
  +N: Nat, +F: U32, +K: U32, +pg: U32, +L: U32, +I: List<&2, Word(8n)>, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  -m0: Cr.Cir.Cells, +fl: Nat, +bl: Bk.Term, +hF: N.Le(272n, U32.to_nat(F)), +fa: In.Fa(m, next, N, F, f0, fc, ks, img),
  +sl: In.St(fl, m, F, N, il, bl, ks, img), fr: In.Fr(m0, m, F), +Bc: Nat, +hB: N.Le(24n+N, Bc), -k: Cr.Cir.State -> Cr.Cir.Out, -R: Cr.Cir.State -> Type,
  g: @iu2: U32 -> @ij2: U32 -> @t12: U32 -> @t22: U32 -> @m2: Cr.Cir.Cells -> @nx2: U32 -> @pg2: U32 -> In.Fa(m2, nx2, 24n+N, F, f0, fc, ks, img) ->
    In.St(24n+f0, m2, F, 24n+N, iu2, Pg.Program.word(8n, In.wd(ib)), ks, img) -> {True{} == In.ps(m2, iu2) : Bool} -> In.St(fl, m2, F, 24n+N, il, bl, ks, img) -> In.Fr(m0, m2, F) ->
    In.Ok(k(In.S(In.R(fo, ii, ib, il, iu2, ij2, t12, t22), m2, nx2, F, K, pg2, L, I)), R, In.oom(L, Bc))) ->
  In.Go(9n+Z, In.c.W(), In.S(In.R(fo, ii, ib, il, 14, 8, t1, t2), m, next, F, K, pg, L, I), k, R, In.oom(L, Bc)):
  In.wh(8n+Z, Mc.M.ne(Mc.M.g(Mc.R.ij()), Mc.M.c(0)), In.c.inner(), In.S(In.R(fo, ii, ib, il, 14, 8, t1, t2), m, next, F, K, pg, L, I), k, R, In.oom(L, Bc), {==},
   In.ir(7n+Z, fo, ii, ib, il, 14, 8, t1, t2, m, next, N, F, K, pg, L, I, f0, fc, ks, img, m0, f0, 0n, WNil{}, fl, bl, hF, N.le_refl(f0), fa, Im.g14(f0, m, F, N, ks, img, Fa.im(m, next, N, F, f0, fc, ks, img, fa)), {==}, sl, fr,
    Bc, N.le_trans(3n+N, 24n+N, Bc, N.le_add_l(21n, 3n+N), hB), t => Cr.Cir.exec.then(Cr.Cir.exec(8n+Z, In.c.W(), t), k), R,
    +iu1 => +ta1 => +tb1 => +m1 => +nx1 => +pg1 => +fa1 => +sw1 => +pu1 => +sl1 => fr1 =>
     In.wh(7n+Z, Mc.M.ne(Mc.M.g(Mc.R.ij()), Mc.M.c(0)), In.c.inner(), In.S(In.R(fo, ii, ib, il, iu1, U32.sub(8, 1), ta1, tb1), m1, nx1, F, K, pg1, L, I), k, R, In.oom(L, Bc), {==},
      In.ir(6n+Z, fo, ii, ib, il, iu1, U32.sub(8, 1), ta1, tb1, m1, nx1, 3n+N, F, K, pg1, L, I, f0, fc, ks, img, m0, 3n+f0, 1n+0n, WCon{In.bit(ib, U32.sub(8, 1)), WNil{}}, fl, bl, hF, N.le_add_l(3n, f0), fa1, sw1, pu1, sl1, fr1,
       Bc, N.le_trans(3n+(3n+N), 24n+N, Bc, N.le_add_l(18n, 3n+(3n+N)), hB), t => Cr.Cir.exec.then(Cr.Cir.exec(7n+Z, In.c.W(), t), k), R,
       +iu2 => +ta2 => +tb2 => +m2 => +nx2 => +pg2 => +fa2 => +sw2 => +pu2 => +sl2 => fr2 =>
        In.wh(6n+Z, Mc.M.ne(Mc.M.g(Mc.R.ij()), Mc.M.c(0)), In.c.inner(), In.S(In.R(fo, ii, ib, il, iu2, U32.sub(U32.sub(8, 1), 1), ta2, tb2), m2, nx2, F, K, pg2, L, I), k, R, In.oom(L, Bc), {==},
         In.ir(5n+Z, fo, ii, ib, il, iu2, U32.sub(U32.sub(8, 1), 1), ta2, tb2, m2, nx2, 6n+N, F, K, pg2, L, I, f0, fc, ks, img, m0, 6n+f0, 1n+(1n+0n), WCon{In.bit(ib, U32.sub(U32.sub(8, 1), 1)), WCon{In.bit(ib, U32.sub(8, 1)), WNil{}}}, fl, bl, hF, N.le_add_l(6n, f0), fa2, sw2, pu2, sl2, fr2,
          Bc, N.le_trans(3n+(6n+N), 24n+N, Bc, N.le_add_l(15n, 3n+(6n+N)), hB), t => Cr.Cir.exec.then(Cr.Cir.exec(6n+Z, In.c.W(), t), k), R,
          +iu3 => +ta3 => +tb3 => +m3 => +nx3 => +pg3 => +fa3 => +sw3 => +pu3 => +sl3 => fr3 =>
           In.wh(5n+Z, Mc.M.ne(Mc.M.g(Mc.R.ij()), Mc.M.c(0)), In.c.inner(), In.S(In.R(fo, ii, ib, il, iu3, U32.sub(U32.sub(U32.sub(8, 1), 1), 1), ta3, tb3), m3, nx3, F, K, pg3, L, I), k, R, In.oom(L, Bc), {==},
            In.ir(4n+Z, fo, ii, ib, il, iu3, U32.sub(U32.sub(U32.sub(8, 1), 1), 1), ta3, tb3, m3, nx3, 9n+N, F, K, pg3, L, I, f0, fc, ks, img, m0, 9n+f0, 1n+(1n+(1n+0n)), WCon{In.bit(ib, U32.sub(U32.sub(U32.sub(8, 1), 1), 1)), WCon{In.bit(ib, U32.sub(U32.sub(8, 1), 1)), WCon{In.bit(ib, U32.sub(8, 1)), WNil{}}}}, fl, bl, hF, N.le_add_l(9n, f0), fa3, sw3, pu3, sl3, fr3,
             Bc, N.le_trans(3n+(9n+N), 24n+N, Bc, N.le_add_l(12n, 3n+(9n+N)), hB), t => Cr.Cir.exec.then(Cr.Cir.exec(5n+Z, In.c.W(), t), k), R,
             +iu4 => +ta4 => +tb4 => +m4 => +nx4 => +pg4 => +fa4 => +sw4 => +pu4 => +sl4 => fr4 =>
              In.wh(4n+Z, Mc.M.ne(Mc.M.g(Mc.R.ij()), Mc.M.c(0)), In.c.inner(), In.S(In.R(fo, ii, ib, il, iu4, U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1), ta4, tb4), m4, nx4, F, K, pg4, L, I), k, R, In.oom(L, Bc), {==},
               In.ir(3n+Z, fo, ii, ib, il, iu4, U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1), ta4, tb4, m4, nx4, 12n+N, F, K, pg4, L, I, f0, fc, ks, img, m0, 12n+f0, 1n+(1n+(1n+(1n+0n))), WCon{In.bit(ib, U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1)), WCon{In.bit(ib, U32.sub(U32.sub(U32.sub(8, 1), 1), 1)), WCon{In.bit(ib, U32.sub(U32.sub(8, 1), 1)), WCon{In.bit(ib, U32.sub(8, 1)), WNil{}}}}}, fl, bl, hF, N.le_add_l(12n, f0), fa4, sw4, pu4, sl4, fr4,
                Bc, N.le_trans(3n+(12n+N), 24n+N, Bc, N.le_add_l(9n, 3n+(12n+N)), hB), t => Cr.Cir.exec.then(Cr.Cir.exec(4n+Z, In.c.W(), t), k), R,
                +iu5 => +ta5 => +tb5 => +m5 => +nx5 => +pg5 => +fa5 => +sw5 => +pu5 => +sl5 => fr5 =>
                 In.wh(3n+Z, Mc.M.ne(Mc.M.g(Mc.R.ij()), Mc.M.c(0)), In.c.inner(), In.S(In.R(fo, ii, ib, il, iu5, U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1), 1), ta5, tb5), m5, nx5, F, K, pg5, L, I), k, R, In.oom(L, Bc), {==},
                  In.ir(2n+Z, fo, ii, ib, il, iu5, U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1), 1), ta5, tb5, m5, nx5, 15n+N, F, K, pg5, L, I, f0, fc, ks, img, m0, 15n+f0, 1n+(1n+(1n+(1n+(1n+0n)))), WCon{In.bit(ib, U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1), 1)), WCon{In.bit(ib, U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1)), WCon{In.bit(ib, U32.sub(U32.sub(U32.sub(8, 1), 1), 1)), WCon{In.bit(ib, U32.sub(U32.sub(8, 1), 1)), WCon{In.bit(ib, U32.sub(8, 1)), WNil{}}}}}}, fl, bl, hF, N.le_add_l(15n, f0), fa5, sw5, pu5, sl5, fr5,
                   Bc, N.le_trans(3n+(15n+N), 24n+N, Bc, N.le_add_l(6n, 3n+(15n+N)), hB), t => Cr.Cir.exec.then(Cr.Cir.exec(3n+Z, In.c.W(), t), k), R,
                   +iu6 => +ta6 => +tb6 => +m6 => +nx6 => +pg6 => +fa6 => +sw6 => +pu6 => +sl6 => fr6 =>
                    In.wh(2n+Z, Mc.M.ne(Mc.M.g(Mc.R.ij()), Mc.M.c(0)), In.c.inner(), In.S(In.R(fo, ii, ib, il, iu6, U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1), 1), 1), ta6, tb6), m6, nx6, F, K, pg6, L, I), k, R, In.oom(L, Bc), {==},
                     In.ir(1n+Z, fo, ii, ib, il, iu6, U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1), 1), 1), ta6, tb6, m6, nx6, 18n+N, F, K, pg6, L, I, f0, fc, ks, img, m0, 18n+f0, 1n+(1n+(1n+(1n+(1n+(1n+0n))))), WCon{In.bit(ib, U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1), 1), 1)), WCon{In.bit(ib, U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1), 1)), WCon{In.bit(ib, U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1)), WCon{In.bit(ib, U32.sub(U32.sub(U32.sub(8, 1), 1), 1)), WCon{In.bit(ib, U32.sub(U32.sub(8, 1), 1)), WCon{In.bit(ib, U32.sub(8, 1)), WNil{}}}}}}}, fl, bl, hF, N.le_add_l(18n, f0), fa6, sw6, pu6, sl6, fr6,
                      Bc, N.le_trans(3n+(18n+N), 24n+N, Bc, N.le_add_l(3n, 3n+(18n+N)), hB), t => Cr.Cir.exec.then(Cr.Cir.exec(2n+Z, In.c.W(), t), k), R,
                      +iu7 => +ta7 => +tb7 => +m7 => +nx7 => +pg7 => +fa7 => +sw7 => +pu7 => +sl7 => fr7 =>
                       In.wh(1n+Z, Mc.M.ne(Mc.M.g(Mc.R.ij()), Mc.M.c(0)), In.c.inner(), In.S(In.R(fo, ii, ib, il, iu7, U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1), 1), 1), 1), ta7, tb7), m7, nx7, F, K, pg7, L, I), k, R, In.oom(L, Bc), {==},
                        In.ir(Z, fo, ii, ib, il, iu7, U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1), 1), 1), 1), ta7, tb7, m7, nx7, 21n+N, F, K, pg7, L, I, f0, fc, ks, img, m0, 21n+f0, 1n+(1n+(1n+(1n+(1n+(1n+(1n+0n)))))), WCon{In.bit(ib, U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1), 1), 1), 1)), WCon{In.bit(ib, U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1), 1), 1)), WCon{In.bit(ib, U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1), 1)), WCon{In.bit(ib, U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1)), WCon{In.bit(ib, U32.sub(U32.sub(U32.sub(8, 1), 1), 1)), WCon{In.bit(ib, U32.sub(U32.sub(8, 1), 1)), WCon{In.bit(ib, U32.sub(8, 1)), WNil{}}}}}}}}, fl, bl, hF, N.le_add_l(21n, f0), fa7, sw7, pu7, sl7, fr7,
                         Bc, hB, t => Cr.Cir.exec.then(Cr.Cir.exec(1n+Z, In.c.W(), t), k), R,
                         +iu8 => +ta8 => +tb8 => +m8 => +nx8 => +pg8 => +fa8 => +sw8 => +pu8 => +sl8 => fr8 =>
                          In.wh.end(Z, Mc.M.ne(Mc.M.g(Mc.R.ij()), Mc.M.c(0)), In.c.inner(), In.S(In.R(fo, ii, ib, il, iu8, U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1), 1), 1), 1), 1), ta8, tb8), m8, nx8, F, K, pg8, L, I), k, R, In.oom(L, Bc), {==},
                           g(iu8, U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1), 1), 1), 1), 1), ta8, tb8, m8, nx8, pg8, fa8, St.cast(24n+f0, m8, F, 24n+N, iu8, Pg.Program.word(1n+(1n+(1n+(1n+(1n+(1n+(1n+(1n+0n))))))), WCon{In.bit(ib, U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1), 1), 1), 1), 1)), WCon{In.bit(ib, U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1), 1), 1), 1)), WCon{In.bit(ib, U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1), 1), 1)), WCon{In.bit(ib, U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1), 1)), WCon{In.bit(ib, U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1)), WCon{In.bit(ib, U32.sub(U32.sub(U32.sub(8, 1), 1), 1)), WCon{In.bit(ib, U32.sub(U32.sub(8, 1), 1)), WCon{In.bit(ib, U32.sub(8, 1)), WNil{}}}}}}}}}), Pg.Program.word(8n, In.wd(ib)), ks, img, In.wd.eq(ib), sw8), pu8, sl8, fr8))))))))))))))))))

# The cache's new entry
# ---------------------

def In.c.c1() -> Cr.Cir.Stmt:
  Mc.M.set(Mc.R.iu(), Mc.M.c(Mc.I.wnil()))

def In.c.c2() -> Cr.Cir.Stmt:
  Mc.M.set(Mc.R.ij(), Mc.M.c(8))

def In.c.c3() -> Cr.Cir.Stmt:
  Mc.M.st(2n, Mc.M.add(Mc.M.c(Mc.I.cache()), Mc.M.g(Mc.R.ib())), Mc.M.g(Mc.R.iu()))

def In.c.cache() -> Cr.Cir.Stmt:
  Mc.M.do([In.c.c1(), In.c.c2(), In.c.W(), In.c.c3()])

# the word of a byte, as the bits' loop builds it
def In.wd_u8(w8: Word(8n)) -> {Pg.Program.word(8n, In.wd(Sd.Byte.to_u32(w8))) == Pg.Program.word(8n, w8) : Bk.Term}:
  match w8:
    case WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WNil{}}}}}}}}}:
      {==}

# what the cache's new entry gives: the cell iu2 of the word of the byte w8,
# in 24 new cells
def In.cch.K(+fo: U32, +ii: U32, +w8: Word(8n), +il: U32, +N: Nat, +F: U32, +K: U32, +L: U32, +I: List<&2, Word(8n)>, +f0: Nat, +fc: Nat,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, -m0: Cr.Cir.Cells, +fl: Nat, +bl: Bk.Term, -k: Cr.Cir.State -> Cr.Cir.Out, -R: Cr.Cir.State -> Type, +Bc: Nat) -> Type:
  @iu2: U32 -> @ij2: U32 -> @t12: U32 -> @t22: U32 -> @m2: Cr.Cir.Cells -> @nx2: U32 -> @pg2: U32 -> In.Fa(m2, nx2, N, F, f0, fc, ks, img) ->
    In.St(fc, m2, F, N, iu2, Pg.Program.word(8n, w8), ks, img) -> {True{} == In.ps(m2, iu2) : Bool} -> In.St(fl, m2, F, N, il, bl, ks, img) -> In.Fr(m0, m2, F) ->
    In.Ok(k(In.S(In.R(fo, ii, Sd.Byte.to_u32(w8), il, iu2, ij2, t12, t22), m2, nx2, F, K, pg2, L, I)), R, In.oom(L, Bc))

# the store of the cache's new entry
def In.cch.c(+Z: Nat, +fo: U32, +ii: U32, +w8: Word(8n), +il: U32, +iu: U32, +ij: U32, +t1: U32, +t2: U32, +m: Cr.Cir.Cells,
  +next: U32, +N: Nat, +F: U32, +K: U32, +pg: U32, +L: U32, +I: List<&2, Word(8n)>, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, -m0: Cr.Cir.Cells, +fl: Nat, +bl: Bk.Term, +hF: N.Le(272n, U32.to_nat(F)), +hK: N.Le(271n, U32.to_nat(K)),
  +fa: In.Fa(m, next, N, F, f0, fc, ks, img), +sv: In.St(fc, m, F, N, iu, Pg.Program.word(8n, w8), ks, img), +pv: {True{} == In.ps(m, iu) : Bool},
  +sl: In.St(fl, m, F, N, il, bl, ks, img), fr: In.Fr(m0, m, F), +Bc: Nat, -k: Cr.Cir.State -> Cr.Cir.Out, -R: Cr.Cir.State -> Type,
  g: In.cch.K(fo, ii, w8, il, N, F, K, L, I, f0, fc, ks, img, m0, fl, bl, k, R, Bc)) ->
  In.Go(1n+(8n+Z), Mc.M.do([In.c.c3()]), In.S(In.R(fo, ii, Sd.Byte.to_u32(w8), il, iu, ij, t1, t2), m, next, F, K, pg, L, I), k, R, In.oom(L, Bc)):
  In.sq(8n+Z, In.c.c3(), Mc.M.do([]), In.S(In.R(fo, ii, Sd.Byte.to_u32(w8), il, iu, ij, t1, t2), m, next, F, K, pg, L, I), k, R,
   In.oom(L, Bc), In.str(8n+Z, 2n, Mc.M.add(Mc.M.c(Mc.I.cache()), Mc.M.g(Mc.R.ib())), Mc.M.g(Mc.R.iu()), In.R(fo, ii, Sd.Byte.to_u32(w8), il, iu, ij, t1, t2), m, next,
    F, K, pg, L, I, In.J(w8), iu, {==}, {==}, In.cellJ(w8, K, F, next, hK), t => Cr.Cir.exec.then(Cr.Cir.exec(1n+(8n+Z), Mc.M.do([]), t), k), R,
    In.oom(L, Bc), In.nop(8n+Z, In.S(In.R(fo, ii, Sd.Byte.to_u32(w8), il, iu, ij, t1, t2), In.cs(m, w8, iu), next, F, K, pg, L, I), k, R,
     In.oom(L, Bc), g(iu, ij, t1, t2, In.cs(m, w8, iu), next, pg, Fa.cs(m, next, N, F, f0, fc, ks, img, w8, iu, hF, sv, pv, fa),
       St.fr(fc, m, F, N, iu, Pg.Program.word(8n, w8), ks, img, In.J(w8), Cr.Cir.Cell.set(2n, Cr.Cir.Cells.get(m, In.J(w8)), iu), In.rdJ(w8, F, N, hF), sv),
       Ps.cs(m, iu, w8, F, N, hF, St.rd(fc, m, F, N, iu, Pg.Program.word(8n, w8), ks, img, sv), pv),
       St.fr(fl, m, F, N, il, bl, ks, img, In.J(w8), Cr.Cir.Cell.set(2n, Cr.Cir.Cells.get(m, In.J(w8)), iu), In.rdJ(w8, F, N, hF), sl),
       Fr.cs(m0, m, F, w8, iu, fr)))))

# the cache's new entry: the word of the byte w8, as 8 bits over the image's
# WNil, stored in the cache
def In.cch(+Z: Nat, +fo: U32, +ii: U32, +w8: Word(8n), +il: U32, +iu: U32, +ij: U32, +t1: U32, +t2: U32, +m: Cr.Cir.Cells,
  +next: U32, +N: Nat, +F: U32, +K: U32, +pg: U32, +L: U32, +I: List<&2, Word(8n)>, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, -m0: Cr.Cir.Cells, +fl: Nat, +bl: Bk.Term, +hF: N.Le(272n, U32.to_nat(F)), +hK: N.Le(271n, U32.to_nat(K)),
  hc: N.Le(24n+f0, fc), +fa: In.Fa(m, next, N, F, f0, fc, ks, img),
  +sl: In.St(fl, m, F, N, il, bl, ks, img), fr: In.Fr(m0, m, F), +Bc: Nat, +hB: N.Le(24n+N, Bc), -k: Cr.Cir.State -> Cr.Cir.Out, -R: Cr.Cir.State -> Type,
  g: In.cch.K(fo, ii, w8, il, 24n+N, F, K, L, I, f0, fc, ks, img, m0, fl, bl, k, R, Bc)) ->
  In.Go(9n+Z, In.c.cache(), In.S(In.R(fo, ii, Sd.Byte.to_u32(w8), il, iu, ij, t1, t2), m, next, F, K, pg, L, I), k, R, In.oom(L, Bc)):
  In.sq(8n+Z, In.c.c1(), Mc.M.do([In.c.c2(), In.c.W(), In.c.c3()]), In.S(In.R(fo, ii, Sd.Byte.to_u32(w8), il, iu, ij, t1, t2), m, next, F, K, pg, L, I), k, R,
   In.oom(L, Bc), In.set(8n+Z, Mc.R.iu(), Mc.M.c(Mc.I.wnil()), In.R(fo, ii, Sd.Byte.to_u32(w8), il, iu, ij, t1, t2), m, next, F, K, pg, L, I, 14, {==}, {==},
    t => Cr.Cir.exec.then(Cr.Cir.exec(1n+(8n+Z), Mc.M.do([In.c.c2(), In.c.W(), In.c.c3()]), t), k), R,
    In.oom(L, Bc), In.sq(8n+Z, In.c.c2(), Mc.M.do([In.c.W(), In.c.c3()]), In.S(In.R(fo, ii, Sd.Byte.to_u32(w8), il, 14, ij, t1, t2), m, next, F, K, pg, L, I), k, R,
     In.oom(L, Bc), In.set(8n+Z, Mc.R.ij(), Mc.M.c(8), In.R(fo, ii, Sd.Byte.to_u32(w8), il, 14, ij, t1, t2), m, next, F, K, pg, L, I, 8, {==}, {==},
      t => Cr.Cir.exec.then(Cr.Cir.exec(1n+(8n+Z), Mc.M.do([In.c.W(), In.c.c3()]), t), k), R,
      In.oom(L, Bc), In.sq(8n+Z, In.c.W(), Mc.M.do([In.c.c3()]), In.S(In.R(fo, ii, Sd.Byte.to_u32(w8), il, 14, 8, t1, t2), m, next, F, K, pg, L, I), k, R,
       In.oom(L, Bc), In.il(Z, fo, ii, Sd.Byte.to_u32(w8), il, t1, t2, m, next, N, F, K, pg, L, I, f0, fc, ks, img, m0, fl, bl, hF, fa, sl, fr,
        Bc, hB, t => Cr.Cir.exec.then(Cr.Cir.exec(1n+(8n+Z), Mc.M.do([In.c.c3()]), t), k), R,
        +iu2 => +ij2 => +t12 => +t22 => +m2 => +nx2 => +pg2 => +fa2 => +su2 => +pu2 => +sl2 => fr2 =>
         In.cch.c(Z, fo, ii, w8, il, iu2, ij2, t12, t22, m2, nx2, 24n+N, F, K, pg2, L, I, f0, fc, ks, img, m0, fl, bl, hF, hK, fa2,
          St.to(24n+f0, fc, hc, m2, F, 24n+N, iu2, Pg.Program.word(8n, w8), ks, img,
            St.cast(24n+f0, m2, F, 24n+N, iu2, Pg.Program.word(8n, In.wd(Sd.Byte.to_u32(w8))), Pg.Program.word(8n, w8), ks, img, In.wd_u8(w8), su2)),
          pu2, sl2, fr2, Bc, k, R, g)))))))

# The list's new cell
# -------------------

def In.c.b5() -> Cr.Cir.Stmt:
  Mc.M.make(Mc.R.t1(), Mc.M.c(Mc.M.h.data()), Mc.M.g(Mc.R.il()), Mc.M.c(Mc.I.lab(Mc.N.unit())), Mc.M.c(0))

def In.c.b6() -> Cr.Cir.Stmt:
  Mc.M.make(Mc.R.t2(), Mc.M.c(Mc.M.h.data()), Mc.M.g(Mc.R.iu()), Mc.M.g(Mc.R.t1()), Mc.M.c(0))

def In.c.b7() -> Cr.Cir.Stmt:
  Mc.M.make(Mc.R.il(), Mc.M.c(Mc.M.h.data()), Mc.M.c(Mc.I.lab(Mc.N.con())), Mc.M.g(Mc.R.t2()), Mc.M.c(0))

# Con with the fields cu and bl
def In.con.eq(+cu: Bk.Term, +bl: Bk.Term) ->
  {Bk.Term.Tup{Bk.Quan.Q1{}, Bk.Term.Lab{Pg.Program.name.con()}, Bk.Term.Tup{Bk.Quan.Q1{}, cu, Bk.Term.Tup{Bk.Quan.Q1{}, bl, Bk.Term.Lab{Pg.Program.name.unit()}}}} ==
    Pg.Program.ctor(Pg.Program.name.con(), [cu, bl]) : Bk.Term}:
  {==}

# what the list's new cell gives: the cell il2 of Con with the fields cu and bl
def In.lst.K(+fo: U32, +ii: U32, +ib: U32, +iu: U32, +ij: U32, +N: Nat, +F: U32, +K: U32, +L: U32, +I: List<&2, Word(8n)>, +f0: Nat,
  +fc: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, -m0: Cr.Cir.Cells, +fs: Nat, +cu: Bk.Term, +bl: Bk.Term,
  -k: Cr.Cir.State -> Cr.Cir.Out, -R: Cr.Cir.State -> Type, +Bc: Nat) -> Type:
  @il2: U32 -> @t12: U32 -> @t22: U32 -> @m2: Cr.Cir.Cells -> @nx2: U32 -> @pg2: U32 -> In.Fa(m2, nx2, N, F, f0, fc, ks, img) ->
    In.St(fs, m2, F, N, il2, Pg.Program.ctor(Pg.Program.name.con(), [cu, bl]), ks, img) -> In.Fr(m0, m2, F) ->
    In.Ok(k(In.S(In.R(fo, ii, ib, il2, iu, ij, t12, t22), m2, nx2, F, K, pg2, L, I)), R, In.oom(L, Bc))

# the list's last make: il gets Con in front of the cell t2
def In.lst.c(+f: Nat, +fo: U32, +ii: U32, +ib: U32, +il: U32, +iu: U32, +ij: U32, +t1: U32, +t2: U32, +m: Cr.Cir.Cells, +next: U32,
  +N: Nat, +F: U32, +K: U32, +pg: U32, +L: U32, +I: List<&2, Word(8n)>, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  -m0: Cr.Cir.Cells, +fs: Nat, +cu: Bk.Term, +bl: Bk.Term, +hF: N.Le(272n, U32.to_nat(F)), +hs: N.Le(f0, fs), +fa: In.Fa(m, next, N, F, f0, fc, ks, img),
  +s2: In.St(fs, m, F, N, t2, Bk.Term.Tup{Bk.Quan.Q1{}, cu, Bk.Term.Tup{Bk.Quan.Q1{}, bl, Bk.Term.Lab{Pg.Program.name.unit()}}}, ks, img), fr: In.Fr(m0, m, F),
  +Bc: Nat, +hB: N.Le(1n+N, Bc), -k: Cr.Cir.State -> Cr.Cir.Out, -R: Cr.Cir.State -> Type,
  g: In.lst.K(fo, ii, ib, iu, ij, 1n+N, F, K, L, I, f0, fc, ks, img, m0, 1n+fs, cu, bl, k, R, Bc)) ->
  In.Go(1n+f, Mc.M.do([In.c.b7()]), In.S(In.R(fo, ii, ib, il, iu, ij, t1, t2), m, next, F, K, pg, L, I), k, R, In.oom(L, Bc)):
  In.sq(f, In.c.b7(), Mc.M.do([]), In.S(In.R(fo, ii, ib, il, iu, ij, t1, t2), m, next, F, K, pg, L, I), k, R,
   In.oom(L, Bc), In.mk(f, Mc.R.il(), Mc.M.c(Mc.M.h.data()), Mc.M.c(Mc.I.lab(Mc.N.con())), Mc.M.g(Mc.R.t2()), Mc.M.c(0), In.R(fo, ii, ib, il, iu, ij, t1, t2), m, next,
    F, K, pg, L, I, In.hd(False{}), 3, t2, 0,
    Bc, In.hb(next, N, Bc, Fa.eN(m, next, N, F, f0, fc, ks, img, fa), hB), {==}, {==}, {==}, lt => In.cellNew(next, K, F, lt, Fa.lF(m, next, N, F, f0, fc, ks, img, fa)),
    m4 => pg4 => {==}, m4 => pg4 => {==}, m4 => pg4 => {==}, m4 => pg4 => {==}, t => Cr.Cir.exec.then(Cr.Cir.exec(1n+f, Mc.M.do([]), t), k), R,
    +pg3 => +lt3 =>
     In.nop(f, In.S(In.R(fo, ii, ib, next, iu, ij, t1, t2), Cr.Cir.Cells.set(m, next, Cr.Cir.Cell{In.hd(False{}), 1, 3, t2, 0}), U32.inc(next), F, K, pg3, L, I), k, R,
       In.oom(L, Bc), g(next, t1, t2, Cr.Cir.Cells.set(m, next, Cr.Cir.Cell{In.hd(False{}), 1, 3, t2, 0}), U32.inc(next), pg3,
         Fa.step(m, next, N, F, f0, fc, ks, img, Cr.Cir.Cell{In.hd(False{}), 1, 3, t2, 0}, lt3, hF,
           In.okn.mk(m, F, N, In.hd(False{}), 3, t2, {==},
             St.pt(fs, m, F, N, t2, Bk.Term.Tup{Bk.Quan.Q1{}, cu, Bk.Term.Tup{Bk.Quan.Q1{}, bl, Bk.Term.Lab{Pg.Program.name.unit()}}}, ks, img, Fa.e0(m, next, N, F, f0, fc, ks, img, fa), s2), {==}), fa),
         St.cast(1n+fs, Cr.Cir.Cells.set(m, next, Cr.Cir.Cell{In.hd(False{}), 1, 3, t2, 0}), F, 1n+N, next,
           Bk.Term.Tup{Bk.Quan.Q1{}, Bk.Term.Lab{Pg.Program.name.con()}, Bk.Term.Tup{Bk.Quan.Q1{}, cu, Bk.Term.Tup{Bk.Quan.Q1{}, bl, Bk.Term.Lab{Pg.Program.name.unit()}}}},
           Pg.Program.ctor(Pg.Program.name.con(), [cu, bl]), ks, img, In.con.eq(cu, bl),
           In.tup(False{}, fs, m, F, N, next, 3, t2, Bk.Term.Lab{Pg.Program.name.con()},
             Bk.Term.Tup{Bk.Quan.Q1{}, cu, Bk.Term.Tup{Bk.Quan.Q1{}, bl, Bk.Term.Lab{Pg.Program.name.unit()}}}, ks, img,
             St.to(f0, fs, hs, m, F, N, 3, Bk.Term.Lab{Pg.Program.name.con()}, ks, img, Im.g3(f0, m, F, N, ks, img, Fa.im(m, next, N, F, f0, fc, ks, img, fa))),
             s2, Fa.hi(m, next, N, F, f0, fc, ks, img, hF, fa), Fa.hr(m, next, N, F, f0, fc, ks, img, hF, fa))),
         Fr.step(m0, m, F, next, Cr.Cir.Cell{In.hd(False{}), 1, 3, t2, 0}, hF, Fa.lF(m, next, N, F, f0, fc, ks, img, fa), fr)))))

# the list's second make: t2 gets the cell iu in front of the cell t1
def In.lst.b(+f: Nat, +fo: U32, +ii: U32, +ib: U32, +il: U32, +iu: U32, +ij: U32, +t1: U32, +t2: U32, +m: Cr.Cir.Cells, +next: U32,
  +N: Nat, +F: U32, +K: U32, +pg: U32, +L: U32, +I: List<&2, Word(8n)>, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  -m0: Cr.Cir.Cells, +fs: Nat, +cu: Bk.Term, +bl: Bk.Term, +hF: N.Le(272n, U32.to_nat(F)), +hs: N.Le(f0, fs), hcs: N.Le(fc, fs),
  +fa: In.Fa(m, next, N, F, f0, fc, ks, img), +su: In.St(fc, m, F, N, iu, cu, ks, img),
  +s1: In.St(fs, m, F, N, t1, Bk.Term.Tup{Bk.Quan.Q1{}, bl, Bk.Term.Lab{Pg.Program.name.unit()}}, ks, img), fr: In.Fr(m0, m, F),
  +Bc: Nat, +hB: N.Le(2n+N, Bc), -k: Cr.Cir.State -> Cr.Cir.Out, -R: Cr.Cir.State -> Type,
  g: In.lst.K(fo, ii, ib, iu, ij, 1n+(1n+N), F, K, L, I, f0, fc, ks, img, m0, 1n+(1n+fs), cu, bl, k, R, Bc)) ->
  In.Go(1n+f, Mc.M.do([In.c.b6(), In.c.b7()]), In.S(In.R(fo, ii, ib, il, iu, ij, t1, t2), m, next, F, K, pg, L, I), k, R, In.oom(L, Bc)):
  In.sq(f, In.c.b6(), Mc.M.do([In.c.b7()]), In.S(In.R(fo, ii, ib, il, iu, ij, t1, t2), m, next, F, K, pg, L, I), k, R,
   In.oom(L, Bc), In.mk(f, Mc.R.t2(), Mc.M.c(Mc.M.h.data()), Mc.M.g(Mc.R.iu()), Mc.M.g(Mc.R.t1()), Mc.M.c(0), In.R(fo, ii, ib, il, iu, ij, t1, t2), m, next,
    F, K, pg, L, I, In.hd(False{}), iu, t1, 0,
    Bc, In.hb(next, N, Bc, Fa.eN(m, next, N, F, f0, fc, ks, img, fa), N.weaken(1n+N, Bc, hB)), {==}, {==}, {==}, lt => In.cellNew(next, K, F, lt, Fa.lF(m, next, N, F, f0, fc, ks, img, fa)),
    m4 => pg4 => {==}, m4 => pg4 => {==}, m4 => pg4 => {==}, m4 => pg4 => {==}, t => Cr.Cir.exec.then(Cr.Cir.exec(1n+f, Mc.M.do([In.c.b7()]), t), k), R,
    +pg3 => +lt3 =>
     In.lst.c(f, fo, ii, ib, il, iu, ij, t1, next, Cr.Cir.Cells.set(m, next, Cr.Cir.Cell{In.hd(False{}), 1, iu, t1, 0}), U32.inc(next), 1n+N,
       F, K, pg3, L, I, f0, fc, ks, img, m0, 1n+fs, cu, bl, hF, N.le_succ(f0, fs, hs),
       Fa.step(m, next, N, F, f0, fc, ks, img, Cr.Cir.Cell{In.hd(False{}), 1, iu, t1, 0}, lt3, hF,
         In.okn.mk(m, F, N, In.hd(False{}), iu, t1, St.pt(fc, m, F, N, iu, cu, ks, img, Fa.e0(m, next, N, F, f0, fc, ks, img, fa), su),
           St.pt(fs, m, F, N, t1, Bk.Term.Tup{Bk.Quan.Q1{}, bl, Bk.Term.Lab{Pg.Program.name.unit()}}, ks, img, Fa.e0(m, next, N, F, f0, fc, ks, img, fa), s1), {==}), fa),
       In.tup(False{}, fs, m, F, N, next, iu, t1, cu, Bk.Term.Tup{Bk.Quan.Q1{}, bl, Bk.Term.Lab{Pg.Program.name.unit()}}, ks, img,
         St.to(fc, fs, hcs, m, F, N, iu, cu, ks, img, su), s1, Fa.hi(m, next, N, F, f0, fc, ks, img, hF, fa), Fa.hr(m, next, N, F, f0, fc, ks, img, hF, fa)),
       Fr.step(m0, m, F, next, Cr.Cir.Cell{In.hd(False{}), 1, iu, t1, 0}, hF, Fa.lF(m, next, N, F, f0, fc, ks, img, fa), fr), Bc, hB, k, R, g)))

# the list's new cell: il gets Con of the cells iu and il
def In.lst(+f: Nat, +fo: U32, +ii: U32, +ib: U32, +il: U32, +iu: U32, +ij: U32, +t1: U32, +t2: U32, +m: Cr.Cir.Cells, +next: U32,
  +N: Nat, +F: U32, +K: U32, +pg: U32, +L: U32, +I: List<&2, Word(8n)>, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  -m0: Cr.Cir.Cells, +fl: Nat, +cu: Bk.Term, +bl: Bk.Term, +hF: N.Le(272n, U32.to_nat(F)), +hl: N.Le(f0, fl), hcl: N.Le(fc, 1n+fl),
  +fa: In.Fa(m, next, N, F, f0, fc, ks, img), +su: In.St(fc, m, F, N, iu, cu, ks, img), +pu: {True{} == In.ps(m, iu) : Bool},
  +sl: In.St(fl, m, F, N, il, bl, ks, img), fr: In.Fr(m0, m, F), +Bc: Nat, +hB: N.Le(3n+N, Bc), -k: Cr.Cir.State -> Cr.Cir.Out, -R: Cr.Cir.State -> Type,
  g: In.lst.K(fo, ii, ib, iu, ij, 3n+N, F, K, L, I, f0, fc, ks, img, m0, 3n+fl, cu, bl, k, R, Bc)) ->
  In.Go(1n+f, Mc.M.do([In.c.b5(), In.c.b6(), In.c.b7()]), In.S(In.R(fo, ii, ib, il, iu, ij, t1, t2), m, next, F, K, pg, L, I), k, R, In.oom(L, Bc)):
  In.sq(f, In.c.b5(), Mc.M.do([In.c.b6(), In.c.b7()]), In.S(In.R(fo, ii, ib, il, iu, ij, t1, t2), m, next, F, K, pg, L, I), k, R,
   In.oom(L, Bc), In.mk(f, Mc.R.t1(), Mc.M.c(Mc.M.h.data()), Mc.M.g(Mc.R.il()), Mc.M.c(Mc.I.lab(Mc.N.unit())), Mc.M.c(0), In.R(fo, ii, ib, il, iu, ij, t1, t2), m, next,
    F, K, pg, L, I, In.hd(False{}), il, 1, 0,
    Bc, In.hb(next, N, Bc, Fa.eN(m, next, N, F, f0, fc, ks, img, fa), N.weaken(1n+N, Bc, N.weaken(2n+N, Bc, hB))), {==}, {==}, {==}, lt => In.cellNew(next, K, F, lt, Fa.lF(m, next, N, F, f0, fc, ks, img, fa)),
    m4 => pg4 => {==}, m4 => pg4 => {==}, m4 => pg4 => {==}, m4 => pg4 => {==}, t => Cr.Cir.exec.then(Cr.Cir.exec(1n+f, Mc.M.do([In.c.b6(), In.c.b7()]), t), k), R,
    +pg3 => +lt3 =>
     In.lst.b(f, fo, ii, ib, il, iu, ij, next, t2, Cr.Cir.Cells.set(m, next, Cr.Cir.Cell{In.hd(False{}), 1, il, 1, 0}), U32.inc(next), 1n+N,
       F, K, pg3, L, I, f0, fc, ks, img, m0, 1n+fl, cu, bl, hF, N.le_succ(f0, fl, hl), hcl,
       Fa.step(m, next, N, F, f0, fc, ks, img, Cr.Cir.Cell{In.hd(False{}), 1, il, 1, 0}, lt3, hF,
         In.okn.mk(m, F, N, In.hd(False{}), il, 1, St.pt(fl, m, F, N, il, bl, ks, img, Fa.e0(m, next, N, F, f0, fc, ks, img, fa), sl), {==}, {==}), fa),
       St.step(fc, m, F, N, iu, cu, ks, img, next, Cr.Cir.Cell{In.hd(False{}), 1, il, 1, 0}, Fa.hi(m, next, N, F, f0, fc, ks, img, hF, fa), su),
       In.tup(False{}, fl, m, F, N, next, il, 1, bl, Bk.Term.Lab{Pg.Program.name.unit()}, ks, img, sl,
         St.to(f0, fl, hl, m, F, N, 1, Bk.Term.Lab{Pg.Program.name.unit()}, ks, img, Im.g1(f0, m, F, N, ks, img, Fa.im(m, next, N, F, f0, fc, ks, img, fa))),
         Fa.hi(m, next, N, F, f0, fc, ks, img, hF, fa), Fa.hr(m, next, N, F, f0, fc, ks, img, hF, fa)),
       Fr.step(m0, m, F, next, Cr.Cir.Cell{In.hd(False{}), 1, il, 1, 0}, hF, Fa.lF(m, next, N, F, f0, fc, ks, img, fa), fr), Bc, hB, k, R, g)))

# The input's bytes
# -----------------

# the element p of I, 0 past its end
def In.nth(I: List<&2, Word(8n)>, p: Nat) -> Word(8n):
  Maybe.default(&2, Word(8n), List.get(&2, Word(8n), I, p), Word.zero(8n))

def In.get_at(I: List<&2, Word(8n)>, p: Nat, h: N.Le(1n+p, List.length(&2, Word(8n), I))) -> {Some{In.nth(I, p)} == List.get(&2, Word(8n), I, p) : Maybe<&2, Word(8n)>}:
  match I:
    case Nil{}:
      Empty.absurd({Some{In.nth([], p)} == List.get(&2, Word(8n), [], p) : Maybe<&2, Word(8n)>}, h)
    case Con{x, r}:
      match p:
        case 0n:
          {==}
        case 1n+q:
          In.get_at(r, q, h)

def In.drop0(I: List<&2, Word(8n)>) -> {I == List.drop(&2, Word(8n), I, 0n) : List<&2, Word(8n)>}:
  match I:
    case Nil{}:
      {==}
    case Con{x, r}:
      {==}

# the list from p on: its element p, then the list from 1 + p on
def In.drop_at(I: List<&2, Word(8n)>, p: Nat, h: N.Le(1n+p, List.length(&2, Word(8n), I))) ->
  {Con{In.nth(I, p), List.drop(&2, Word(8n), I, 1n+p)} == List.drop(&2, Word(8n), I, p) : List<&2, Word(8n)>}:
  match I:
    case Nil{}:
      Empty.absurd({Con{In.nth([], p), List.drop(&2, Word(8n), [], 1n+p)} == List.drop(&2, Word(8n), [], p) : List<&2, Word(8n)>}, h)
    case Con{+x, +r}:
      match p:
        case 0n:
          Equal.cong(List<&2, Word(8n)>, List<&2, Word(8n)>, y => Con{x, y}, List.drop(&2, Word(8n), r, 0n), r,
            Equal.sym(List<&2, Word(8n)>, r, List.drop(&2, Word(8n), r, 0n), In.drop0(r)))
        case 1n+q:
          In.drop_at(r, q, h)

def In.drop_len(I: List<&2, Word(8n)>) -> {[] == List.drop(&2, Word(8n), I, List.length(&2, Word(8n), I)) : List<&2, Word(8n)>}:
  match I:
    case Nil{}:
      {==}
    case Con{x, r}:
      In.drop_len(r)

# the input's size
def In.enc_len(I: List<&2, Word(8n)>) -> {U32.from_nat(List.length(&2, Word(8n), I)) == Cr.Wasm.encode.len(Word(8n), I) : U32}:
  match I:
    case Nil{}:
      {==}
    case Con{x, r}:
      Equal.cong(U32, U32, y => U32.inc(y), U32.from_nat(List.length(&2, Word(8n), r)), Cr.Wasm.encode.len(Word(8n), r), In.enc_len(r))

# the bytes from p on: Con of the byte p and the bytes from 1 + p on
def In.bytes.step(+I: List<&2, Word(8n)>, +p: Nat, +x: Word(8n), hd: {Con{x, List.drop(&2, Word(8n), I, 1n+p)} == List.drop(&2, Word(8n), I, p) : List<&2, Word(8n)>}) ->
  {Pg.Program.ctor(Pg.Program.name.con(), [Pg.Program.word(8n, x), Pg.Program.bytes(List.drop(&2, Word(8n), I, 1n+p))]) ==
    Pg.Program.bytes(List.drop(&2, Word(8n), I, p)) : Bk.Term}:
  %hd : {Pg.Program.ctor(Pg.Program.name.con(), [Pg.Program.word(8n, x), Pg.Program.bytes(List.drop(&2, Word(8n), I, 1n+p))]) == Pg.Program.bytes(_) : Bk.Term}
  {==}

# an entry, by an equation of its byte
def En.cast(-fc: Nat, -m: Cr.Cir.Cells, -F: U32, -N: Nat, -w: Word(8n), -v: Word(8n), -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>,
  e: {w == v : Word(8n)}, x: In.En(fc, m, F, N, w, ks, img)) -> In.En(fc, m, F, N, v, ks, img):
  %e : In.En(fc, m, F, N, _, ks, img)
  x

# the cache's entry of w8, when it is not 0, stands for its word
def In.hit(+fc: Nat, +m: Cr.Cir.Cells, +F: U32, +N: Nat, +w8: Word(8n), +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  eb: {U32.is_eq(Cr.Cir.Cell.get(2n, Cr.Cir.Cells.get(m, In.J(w8))), 0) == False{} : Bool}, en: In.En(fc, m, F, N, w8, ks, img)) ->
  In.St(fc, m, F, N, Cr.Cir.Cell.get(2n, Cr.Cir.Cells.get(m, In.J(w8))), Pg.Program.word(8n, w8), ks, img):
  match en:
    case In.Or.l{z}:
      +v = Cr.Cir.Cell.get(2n, Cr.Cir.Cells.get(m, In.J(w8)))
      Empty.absurd(In.St(fc, m, F, N, Cr.Cir.Cell.get(2n, Cr.Cir.Cells.get(m, In.J(w8))), Pg.Program.word(8n, w8), ks, img),
        N.true_ne_false(Equal.trans(Bool, True{}, U32.is_eq(v, 0), False{}, Equal.cong(U32, Bool, y => U32.is_eq(y, 0), 0, v, z), eb)))
    case In.Or.r{p}:
      (s, pv) = p
      s

# and it is a STATIC part
def In.hit.ps(+fc: Nat, +m: Cr.Cir.Cells, +F: U32, +N: Nat, +w8: Word(8n), +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  eb: {U32.is_eq(Cr.Cir.Cell.get(2n, Cr.Cir.Cells.get(m, In.J(w8))), 0) == False{} : Bool}, en: In.En(fc, m, F, N, w8, ks, img)) ->
  {True{} == In.ps(m, Cr.Cir.Cell.get(2n, Cr.Cir.Cells.get(m, In.J(w8)))) : Bool}:
  match en:
    case In.Or.l{z}:
      +v = Cr.Cir.Cell.get(2n, Cr.Cir.Cells.get(m, In.J(w8)))
      Empty.absurd({True{} == In.ps(m, Cr.Cir.Cell.get(2n, Cr.Cir.Cells.get(m, In.J(w8)))) : Bool},
        N.true_ne_false(Equal.trans(Bool, True{}, U32.is_eq(v, 0), False{}, Equal.cong(U32, Bool, y => U32.is_eq(y, 0), 0, v, z), eb)))
    case In.Or.r{p}:
      (s, pv) = p
      pv

# A round of the input's loop
# ---------------------------

def In.c.b1() -> Cr.Cir.Stmt:
  Mc.M.set(Mc.R.ii(), Mc.M.sub(Mc.M.g(Mc.R.ii()), Mc.M.c(1)))

def In.c.b2() -> Cr.Cir.Stmt:
  Mc.M.set(Mc.R.ib(), Cr.Cir.Expr.byte{Mc.M.g(Mc.R.ii())})

def In.c.b3() -> Cr.Cir.Stmt:
  Mc.M.set(Mc.R.iu(), Mc.M.f(2n, Mc.M.add(Mc.M.c(Mc.I.cache()), Mc.M.g(Mc.R.ib()))))

def In.c.b4() -> Cr.Cir.Stmt:
  Mc.M.when(Mc.M.eq(Mc.M.g(Mc.R.iu()), Mc.M.c(0)), In.c.cache())

def In.c.body() -> Cr.Cir.Stmt:
  Mc.M.do([In.c.b1(), In.c.b2(), In.c.b3(), In.c.b4(), In.c.b5(), In.c.b6(), In.c.b7()])

# the byte that the round reads: the input's element p
def In.evb(+I: List<&2, Word(8n)>, +p: Nat, +M: U32, +hpl: N.Le(1n+p, List.length(&2, Word(8n), I)), +hLM: N.Le(List.length(&2, Word(8n), I), U32.to_nat(M)),
  +fo: U32, +ib: U32, +il: U32, +iu: U32, +ij: U32, +t1: U32, +t2: U32, +m: Cr.Cir.Cells, +next: U32, +F: U32, +K: U32, +pg: U32, +L: U32) ->
  {Some{Sd.Byte.to_u32(In.nth(I, p))} == Cr.Cir.eval(Cr.Cir.Expr.byte{Mc.M.g(Mc.R.ii())}, In.S(In.R(fo, U32.from_nat(p), ib, il, iu, ij, t1, t2), m, next, F, K, pg, L, I)) : Maybe<&2, U32>}:
  +x = In.nth(I, p)
  %Equal.sym(Nat, U32.to_nat(U32.from_nat(p)), p, PM.tofrom(p, M, N.le_trans(p, List.length(&2, Word(8n), I), U32.to_nat(M), N.weaken(p, List.length(&2, Word(8n), I), hpl), hLM))) :
    {Some{Sd.Byte.to_u32(x)} == Cr.Cir.eval.byte.of(List.get(&2, Word(8n), I, _)) : Maybe<&2, U32>}
  %In.get_at(I, p, hpl) : {Some{Sd.Byte.to_u32(x)} == Cr.Cir.eval.byte.of(_) : Maybe<&2, U32>}
  {==}

# the cache's entry of the byte
def In.evf(+w8: Word(8n), +fo: U32, +ii: U32, +il: U32, +iu: U32, +ij: U32, +t1: U32, +t2: U32, +m: Cr.Cir.Cells, +next: U32,
  +F: U32, +K: U32, +pg: U32, +L: U32, +I: List<&2, Word(8n)>, hK: N.Le(271n, U32.to_nat(K))) ->
  {Some{Cr.Cir.Cell.get(2n, Cr.Cir.Cells.get(m, In.J(w8)))} ==
    Cr.Cir.eval(Mc.M.f(2n, Mc.M.add(Mc.M.c(Mc.I.cache()), Mc.M.g(Mc.R.ib()))), In.S(In.R(fo, ii, Sd.Byte.to_u32(w8), il, iu, ij, t1, t2), m, next, F, K, pg, L, I)) : Maybe<&2, U32>}:
  %In.cellJ(w8, K, F, next, hK) : {Some{Cr.Cir.Cell.get(2n, Cr.Cir.Cells.get(m, In.J(w8)))} == Cr.Cir.eval.field.if(_, 2n, m, In.J(w8)) : Maybe<&2, U32>}
  {==}

# the test of the cache's entry v
def In.evc(+v: U32, -b: Bool, eb: {U32.is_eq(v, 0) == b : Bool}, +fo: U32, +ii: U32, +ib: U32, +il: U32, +ij: U32, +t1: U32, +t2: U32,
  +m: Cr.Cir.Cells, +next: U32, +F: U32, +K: U32, +pg: U32, +L: U32, +I: List<&2, Word(8n)>) ->
  {Some{Bool.to_u32(b)} == Cr.Cir.eval(Mc.M.eq(Mc.M.g(Mc.R.iu()), Mc.M.c(0)), In.S(In.R(fo, ii, ib, il, v, ij, t1, t2), m, next, F, K, pg, L, I)) : Maybe<&2, U32>}:
  %eb : {Some{Bool.to_u32(_)} == Cr.Cir.eval(Mc.M.eq(Mc.M.g(Mc.R.iu()), Mc.M.c(0)), In.S(In.R(fo, ii, ib, il, v, ij, t1, t2), m, next, F, K, pg, L, I)) : Maybe<&2, U32>}
  {==}

# what a round of the input's loop gives: the cell il2 of the bytes bp, with
# the fuel fs, in at most 27 new cells
def In.or.K(+fo: U32, +p: Nat, +N: Nat, +F: U32, +K: U32, +L: U32, +I: List<&2, Word(8n)>, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, -m0: Cr.Cir.Cells, +fs: Nat, +bp: Bk.Term, -k: Cr.Cir.State -> Cr.Cir.Out, -R: Cr.Cir.State -> Type, +Bc: Nat) -> Type:
  @ib2: U32 -> @il2: U32 -> @iu2: U32 -> @ij2: U32 -> @t12: U32 -> @t22: U32 -> @m2: Cr.Cir.Cells -> @nx2: U32 -> @N2: Nat -> @pg2: U32 ->
    N.Le(N2, 27n+N) -> In.Fa(m2, nx2, N2, F, f0, fc, ks, img) -> In.St(fs, m2, F, N2, il2, bp, ks, img) -> In.Fr(m0, m2, F) ->
    In.Ok(k(In.S(In.R(fo, U32.from_nat(p), ib2, il2, iu2, ij2, t12, t22), m2, nx2, F, K, pg2, L, I)), R, In.oom(L, Bc))

# the round, from the test of the cache's entry on
def In.or.b4(b: Bool, +Z: Nat, +fo: U32, +p: Nat, +w8: Word(8n), +il: U32, +ij: U32, +t1: U32, +t2: U32, +m: Cr.Cir.Cells, +next: U32,
  +N: Nat, +F: U32, +K: U32, +pg: U32, +L: U32, +I: List<&2, Word(8n)>, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  -m0: Cr.Cir.Cells, +fl: Nat, +bl: Bk.Term, +bp: Bk.Term, +hF: N.Le(272n, U32.to_nat(F)), +hK: N.Le(271n, U32.to_nat(K)), +hc: N.Le(24n+f0, fc),
  +hcl: N.Le(fc, fl), +fa: In.Fa(m, next, N, F, f0, fc, ks, img), +sl: In.St(fl, m, F, N, il, bl, ks, img), fr: In.Fr(m0, m, F),
  ebl: {Pg.Program.ctor(Pg.Program.name.con(), [Pg.Program.word(8n, w8), bl]) == bp : Bk.Term},
  +eb: {U32.is_eq(Cr.Cir.Cell.get(2n, Cr.Cir.Cells.get(m, In.J(w8))), 0) == b : Bool}, +Bc: Nat, +hB: N.Le(27n+N, Bc), -k: Cr.Cir.State -> Cr.Cir.Out, -R: Cr.Cir.State -> Type,
  g: In.or.K(fo, p, N, F, K, L, I, f0, fc, ks, img, m0, 3n+fl, bp, k, R, Bc)) ->
  In.Go(1n+(8n+Z), Mc.M.do([In.c.b4(), In.c.b5(), In.c.b6(), In.c.b7()]),
    In.S(In.R(fo, U32.from_nat(p), Sd.Byte.to_u32(w8), il, Cr.Cir.Cell.get(2n, Cr.Cir.Cells.get(m, In.J(w8))), ij, t1, t2), m, next, F, K, pg, L, I), k, R, In.oom(L, Bc)):
  match b:
    case True{}:
      +hl = N.le_trans(f0, fc, fl, N.le_trans(f0, 24n+f0, fc, N.le_add_l(24n, f0), hc), hcl)
      +hcl1 = N.le_succ(fc, fl, hcl)
      In.sq(8n+Z, In.c.b4(), Mc.M.do([In.c.b5(), In.c.b6(), In.c.b7()]),
       In.S(In.R(fo, U32.from_nat(p), Sd.Byte.to_u32(w8), il, Cr.Cir.Cell.get(2n, Cr.Cir.Cells.get(m, In.J(w8))), ij, t1, t2), m, next, F, K, pg, L, I), k, R,
       In.oom(L, Bc), In.ifT(8n+Z, Mc.M.eq(Mc.M.g(Mc.R.iu()), Mc.M.c(0)), In.c.cache(), Cr.Cir.Stmt.nop{},
        In.S(In.R(fo, U32.from_nat(p), Sd.Byte.to_u32(w8), il, Cr.Cir.Cell.get(2n, Cr.Cir.Cells.get(m, In.J(w8))), ij, t1, t2), m, next, F, K, pg, L, I), 1,
        In.evc(Cr.Cir.Cell.get(2n, Cr.Cir.Cells.get(m, In.J(w8))), True{}, eb, fo, U32.from_nat(p), Sd.Byte.to_u32(w8), il, ij, t1, t2, m, next, F, K, pg, L, I), {==},
        t => Cr.Cir.exec.then(Cr.Cir.exec(1n+(8n+Z), Mc.M.do([In.c.b5(), In.c.b6(), In.c.b7()]), t), k), R,
        In.oom(L, Bc), In.cch(Z, fo, U32.from_nat(p), w8, il, Cr.Cir.Cell.get(2n, Cr.Cir.Cells.get(m, In.J(w8))), ij, t1, t2, m, next, N, F, K, pg, L, I, f0, fc, ks, img,
         m0, fl, bl, hF, hK, hc, fa, sl, fr, Bc, N.le_trans(24n+N, 27n+N, Bc, N.le_add_l(3n, 24n+N), hB), t => Cr.Cir.exec.then(Cr.Cir.exec(1n+(8n+Z), Mc.M.do([In.c.b5(), In.c.b6(), In.c.b7()]), t), k), R,
         +iu2 => +ij2 => +t12 => +t22 => +m2 => +nx2 => +pg2 => +fa2 => +su2 => +pu2 => +sl2 => fr2 =>
          In.lst(8n+Z, fo, U32.from_nat(p), Sd.Byte.to_u32(w8), il, iu2, ij2, t12, t22, m2, nx2, 24n+N, F, K, pg2, L, I, f0, fc, ks, img, m0, fl,
           Pg.Program.word(8n, w8), bl, hF, hl, hcl1, fa2, su2, pu2, sl2, fr2, Bc, hB, k, R,
           +il3 => +t13 => +t23 => +m3 => +nx3 => +pg3 => +fa3 => +sl3 => fr3 =>
            g(Sd.Byte.to_u32(w8), il3, iu2, ij2, t13, t23, m3, nx3, 3n+(24n+N), pg3, N.le_refl(27n+N), fa3,
              St.cast(3n+fl, m3, F, 3n+(24n+N), il3, Pg.Program.ctor(Pg.Program.name.con(), [Pg.Program.word(8n, w8), bl]), bp, ks, img, ebl, sl3), fr3)))))
    case False{}:
      +hl = N.le_trans(f0, fc, fl, N.le_trans(f0, 24n+f0, fc, N.le_add_l(24n, f0), hc), hcl)
      +hcl1 = N.le_succ(fc, fl, hcl)
      In.sq(8n+Z, In.c.b4(), Mc.M.do([In.c.b5(), In.c.b6(), In.c.b7()]),
       In.S(In.R(fo, U32.from_nat(p), Sd.Byte.to_u32(w8), il, Cr.Cir.Cell.get(2n, Cr.Cir.Cells.get(m, In.J(w8))), ij, t1, t2), m, next, F, K, pg, L, I), k, R,
       In.oom(L, Bc), In.ifF(8n+Z, Mc.M.eq(Mc.M.g(Mc.R.iu()), Mc.M.c(0)), In.c.cache(), Cr.Cir.Stmt.nop{},
        In.S(In.R(fo, U32.from_nat(p), Sd.Byte.to_u32(w8), il, Cr.Cir.Cell.get(2n, Cr.Cir.Cells.get(m, In.J(w8))), ij, t1, t2), m, next, F, K, pg, L, I), 0,
        In.evc(Cr.Cir.Cell.get(2n, Cr.Cir.Cells.get(m, In.J(w8))), False{}, eb, fo, U32.from_nat(p), Sd.Byte.to_u32(w8), il, ij, t1, t2, m, next, F, K, pg, L, I), {==},
        t => Cr.Cir.exec.then(Cr.Cir.exec(1n+(8n+Z), Mc.M.do([In.c.b5(), In.c.b6(), In.c.b7()]), t), k), R,
        In.oom(L, Bc), In.nop(8n+Z, In.S(In.R(fo, U32.from_nat(p), Sd.Byte.to_u32(w8), il, Cr.Cir.Cell.get(2n, Cr.Cir.Cells.get(m, In.J(w8))), ij, t1, t2), m, next, F, K, pg, L, I),
         t => Cr.Cir.exec.then(Cr.Cir.exec(1n+(8n+Z), Mc.M.do([In.c.b5(), In.c.b6(), In.c.b7()]), t), k), R,
         In.oom(L, Bc), In.lst(8n+Z, fo, U32.from_nat(p), Sd.Byte.to_u32(w8), il, Cr.Cir.Cell.get(2n, Cr.Cir.Cells.get(m, In.J(w8))), ij, t1, t2, m, next, N, F, K, pg, L, I,
          f0, fc, ks, img, m0, fl, Pg.Program.word(8n, w8), bl, hF, hl, hcl1, fa,
          In.hit(fc, m, F, N, w8, ks, img, eb, En.cast(fc, m, F, N, In.wl(In.push(8n, w8, [])), w8, ks, img,
            Equal.sym(Word(8n), w8, In.wl(In.push(8n, w8, [])), In.wl_push(w8)), CI.get(8n, [], fc, m, F, N, ks, img, w8, Fa.ci(m, next, N, F, f0, fc, ks, img, fa)))),
          In.hit.ps(fc, m, F, N, w8, ks, img, eb, En.cast(fc, m, F, N, In.wl(In.push(8n, w8, [])), w8, ks, img,
            Equal.sym(Word(8n), w8, In.wl(In.push(8n, w8, [])), In.wl_push(w8)), CI.get(8n, [], fc, m, F, N, ks, img, w8, Fa.ci(m, next, N, F, f0, fc, ks, img, fa)))),
          sl, fr, Bc, N.le_trans(3n+N, 27n+N, Bc, N.le_add_l(24n, 3n+N), hB), k, R,
          +il3 => +t13 => +t23 => +m3 => +nx3 => +pg3 => +fa3 => +sl3 => fr3 =>
           g(Sd.Byte.to_u32(w8), il3, Cr.Cir.Cell.get(2n, Cr.Cir.Cells.get(m, In.J(w8))), ij, t13, t23, m3, nx3, 3n+N, pg3, N.le_add_l(24n, N), fa3,
             St.cast(3n+fl, m3, F, 3n+N, il3, Pg.Program.ctor(Pg.Program.name.con(), [Pg.Program.word(8n, w8), bl]), bp, ks, img, ebl, sl3), fr3)))))

# a round of the input's loop: ii goes down by one to p, and il gets Con of
# the byte p in front
def In.or(+Z: Nat, +fo: U32, +p: Nat, +ib: U32, +il: U32, +iu: U32, +ij: U32, +t1: U32, +t2: U32, +m: Cr.Cir.Cells, +next: U32,
  +N: Nat, +F: U32, +K: U32, +pg: U32, +L: U32, +I: List<&2, Word(8n)>, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  -m0: Cr.Cir.Cells, +fl: Nat, +M: U32, +hF: N.Le(272n, U32.to_nat(F)), +hK: N.Le(271n, U32.to_nat(K)), +hc: N.Le(24n+f0, fc),
  +hcl: N.Le(fc, fl), +hpl: N.Le(1n+p, List.length(&2, Word(8n), I)), +hLM: N.Le(List.length(&2, Word(8n), I), U32.to_nat(M)),
  +fa: In.Fa(m, next, N, F, f0, fc, ks, img), +sl: In.St(fl, m, F, N, il, Pg.Program.bytes(List.drop(&2, Word(8n), I, 1n+p)), ks, img), fr: In.Fr(m0, m, F),
  +Bc: Nat, +hB: N.Le(27n+N, Bc), -k: Cr.Cir.State -> Cr.Cir.Out, -R: Cr.Cir.State -> Type,
  g: In.or.K(fo, p, N, F, K, L, I, f0, fc, ks, img, m0, 3n+fl, Pg.Program.bytes(List.drop(&2, Word(8n), I, p)), k, R, Bc)) ->
  In.Go(9n+Z, In.c.body(), In.S(In.R(fo, U32.from_nat(1n+p), ib, il, iu, ij, t1, t2), m, next, F, K, pg, L, I), k, R, In.oom(L, Bc)):
  In.sq(8n+Z, In.c.b1(), Mc.M.do([In.c.b2(), In.c.b3(), In.c.b4(), In.c.b5(), In.c.b6(), In.c.b7()]),
   In.S(In.R(fo, U32.from_nat(1n+p), ib, il, iu, ij, t1, t2), m, next, F, K, pg, L, I), k, R,
   In.oom(L, Bc), In.set(8n+Z, Mc.R.ii(), Mc.M.sub(Mc.M.g(Mc.R.ii()), Mc.M.c(1)), In.R(fo, U32.from_nat(1n+p), ib, il, iu, ij, t1, t2), m, next, F, K, pg, L, I,
    U32.from_nat(p), Equal.cong(U32, Maybe<&2, U32>, z => Some{z}, U32.from_nat(p), U32.sub(U32.inc(U32.from_nat(p)), 1), PI.U32.inc_dec(U32.from_nat(p))), {==},
    t => Cr.Cir.exec.then(Cr.Cir.exec(1n+(8n+Z), Mc.M.do([In.c.b2(), In.c.b3(), In.c.b4(), In.c.b5(), In.c.b6(), In.c.b7()]), t), k), R,
    In.oom(L, Bc), In.sq(8n+Z, In.c.b2(), Mc.M.do([In.c.b3(), In.c.b4(), In.c.b5(), In.c.b6(), In.c.b7()]),
     In.S(In.R(fo, U32.from_nat(p), ib, il, iu, ij, t1, t2), m, next, F, K, pg, L, I), k, R,
     In.oom(L, Bc), In.set(8n+Z, Mc.R.ib(), Cr.Cir.Expr.byte{Mc.M.g(Mc.R.ii())}, In.R(fo, U32.from_nat(p), ib, il, iu, ij, t1, t2), m, next, F, K, pg, L, I,
      Sd.Byte.to_u32(In.nth(I, p)), In.evb(I, p, M, hpl, hLM, fo, ib, il, iu, ij, t1, t2, m, next, F, K, pg, L), {==},
      t => Cr.Cir.exec.then(Cr.Cir.exec(1n+(8n+Z), Mc.M.do([In.c.b3(), In.c.b4(), In.c.b5(), In.c.b6(), In.c.b7()]), t), k), R,
      In.oom(L, Bc), In.sq(8n+Z, In.c.b3(), Mc.M.do([In.c.b4(), In.c.b5(), In.c.b6(), In.c.b7()]),
       In.S(In.R(fo, U32.from_nat(p), Sd.Byte.to_u32(In.nth(I, p)), il, iu, ij, t1, t2), m, next, F, K, pg, L, I), k, R,
       In.oom(L, Bc), In.set(8n+Z, Mc.R.iu(), Mc.M.f(2n, Mc.M.add(Mc.M.c(Mc.I.cache()), Mc.M.g(Mc.R.ib()))), In.R(fo, U32.from_nat(p), Sd.Byte.to_u32(In.nth(I, p)), il, iu, ij, t1, t2),
        m, next, F, K, pg, L, I, Cr.Cir.Cell.get(2n, Cr.Cir.Cells.get(m, In.J(In.nth(I, p)))),
        In.evf(In.nth(I, p), fo, U32.from_nat(p), il, iu, ij, t1, t2, m, next, F, K, pg, L, I, hK), {==},
        t => Cr.Cir.exec.then(Cr.Cir.exec(1n+(8n+Z), Mc.M.do([In.c.b4(), In.c.b5(), In.c.b6(), In.c.b7()]), t), k), R,
        In.oom(L, Bc), In.or.b4(U32.is_eq(Cr.Cir.Cell.get(2n, Cr.Cir.Cells.get(m, In.J(In.nth(I, p)))), 0), Z, fo, p, In.nth(I, p), il, ij, t1, t2,
         m, next, N, F, K, pg, L, I, f0, fc, ks, img, m0, fl, Pg.Program.bytes(List.drop(&2, Word(8n), I, 1n+p)), Pg.Program.bytes(List.drop(&2, Word(8n), I, p)),
         hF, hK, hc, hcl, fa, sl, fr, In.bytes.step(I, p, In.nth(I, p), In.drop_at(I, p, hpl)), {==}, Bc, hB, k, R, g)))))))

# The input's loop
# ----------------

def In.c.OW() -> Cr.Cir.Stmt:
  Mc.M.while(Mc.M.ne(Mc.M.g(Mc.R.ii()), Mc.M.c(0)), In.c.body())

# the fuel of the list after k more rounds, from fl
def In.f3(k: Nat, fl: Nat) -> Nat:
  match k:
    case 0n:
      fl
    case 1n+p:
      In.f3(p, 3n+fl)

def In.f3.ge(k: Nat, +fl: Nat) -> N.Le(fl, In.f3(k, fl)):
  match k:
    case 0n:
      N.le_refl(fl)
    case 1n+(+p):
      N.le_trans(fl, 3n+fl, In.f3(p, 3n+fl), N.le_add_l(3n, fl), In.f3.ge(p, 3n+fl))

# the most cells after k more rounds, from N: 27 a round
def In.cap(k: Nat, N: Nat) -> Nat:
  match k:
    case 0n:
      N
    case 1n+p:
      In.cap(p, 27n+N)

def In.cap.mono(k: Nat, +a: Nat, +b: Nat, h: N.Le(a, b)) -> N.Le(In.cap(k, a), In.cap(k, b)):
  match k:
    case 0n:
      h
    case 1n+(+p):
      In.cap.mono(p, 27n+a, 27n+b, h)

def In.cap.ge(k: Nat, +N: Nat) -> N.Le(N, In.cap(k, N)):
  match k:
    case 0n:
      N.le_refl(N)
    case 1n+(+p):
      N.le_trans(N, 27n+N, In.cap(p, 27n+N), N.le_add_l(27n, N), In.cap.ge(p, 27n+N))

# the most cells, 27 a round
def In.cap.eq(k: Nat, +N: Nat) -> {In.cap(k, N) == Nat.add(N, Nat.mul(27n, k)) : Nat}:
  match k:
    case 0n:
      Equal.sym(Nat, Nat.add(N, 0n), N, N.add_zero(N))
    case 1n+(+p):
      %Equal.sym(Nat, Nat.mul(27n, 1n+p), Nat.add(27n, Nat.mul(27n, p)), In.mul_succ_r(27n, p)) : {In.cap(1n+p, N) == Nat.add(N, _) : Nat}
      Equal.trans(Nat, In.cap(p, 27n+N), Nat.add(27n+N, Nat.mul(27n, p)), Nat.add(N, Nat.add(27n, Nat.mul(27n, p))), In.cap.eq(p, 27n+N),
        Equal.sym(Nat, Nat.add(N, Nat.add(27n, Nat.mul(27n, p))), Nat.add(27n, Nat.add(N, Nat.mul(27n, p))), N.add_swap(N, 27n, Nat.mul(27n, p))))

# the test of the input's loop, while ii is 1 + p
def In.evne(+p: Nat, +M: U32, +h: N.Le(1n+p, U32.to_nat(M)), +fo: U32, +ib: U32, +il: U32, +iu: U32, +ij: U32, +t1: U32, +t2: U32,
  +m: Cr.Cir.Cells, +next: U32, +F: U32, +K: U32, +pg: U32, +L: U32, +I: List<&2, Word(8n)>) ->
  {Some{1} == Cr.Cir.eval(Mc.M.ne(Mc.M.g(Mc.R.ii()), Mc.M.c(0)), In.S(In.R(fo, U32.from_nat(1n+p), ib, il, iu, ij, t1, t2), m, next, F, K, pg, L, I)) : Maybe<&2, U32>}:
  +tf = PM.tofrom(p, M, N.weaken(p, U32.to_nat(M), h))
  +h2 = N.le_rw_l(1n+p, 1n+U32.to_nat(U32.from_nat(p)), U32.to_nat(M),
    Equal.cong(Nat, Nat, q => 1n+q, p, U32.to_nat(U32.from_nat(p)), Equal.sym(Nat, U32.to_nat(U32.from_nat(p)), p, tf)), h)
  %Equal.sym(Bool, U32.is_zero(U32.inc(U32.from_nat(p))), False{}, PM.nz(U32.from_nat(p), M, h2)) :
    {Some{1} == Some{Bool.to_u32(Bool.not(_))} : Maybe<&2, U32>}
  {==}

# what the input's loop gives: the cell il2 of the input's bytes
def In.ol.K(+fo: U32, +k: Nat, +N: Nat, +F: U32, +K: U32, +L: U32, +I: List<&2, Word(8n)>, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, -m0: Cr.Cir.Cells, +fs: Nat, -k_: Cr.Cir.State -> Cr.Cir.Out, -R: Cr.Cir.State -> Type, +Bc: Nat) -> Type:
  @ib2: U32 -> @il2: U32 -> @iu2: U32 -> @ij2: U32 -> @t12: U32 -> @t22: U32 -> @m2: Cr.Cir.Cells -> @nx2: U32 -> @N2: Nat -> @pg2: U32 ->
    N.Le(N2, In.cap(k, N)) -> In.Fa(m2, nx2, N2, F, f0, fc, ks, img) -> In.St(fs, m2, F, N2, il2, Pg.Program.bytes(List.drop(&2, Word(8n), I, 0n)), ks, img) ->
    In.Fr(m0, m2, F) -> In.Ok(k_(In.S(In.R(fo, 0, ib2, il2, iu2, ij2, t12, t22), m2, nx2, F, K, pg2, L, I)), R, In.oom(L, Bc))

# the input's loop, with k bytes still to read: il holds the bytes from k on
def In.ol(k: Nat, +d: Nat, +fo: U32, +ib: U32, +il: U32, +iu: U32, +ij: U32, +t1: U32, +t2: U32, +m: Cr.Cir.Cells, +next: U32,
  +N: Nat, +F: U32, +K: U32, +pg: U32, +L: U32, +I: List<&2, Word(8n)>, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  -m0: Cr.Cir.Cells, +fl: Nat, +M: U32, +hF: N.Le(272n, U32.to_nat(F)), +hK: N.Le(271n, U32.to_nat(K)), +hc: N.Le(24n+f0, fc),
  +hcl: N.Le(fc, fl), +hkl: N.Le(k, List.length(&2, Word(8n), I)), +hLM: N.Le(List.length(&2, Word(8n), I), U32.to_nat(M)),
  +fa: In.Fa(m, next, N, F, f0, fc, ks, img), +sl: In.St(fl, m, F, N, il, Pg.Program.bytes(List.drop(&2, Word(8n), I, k)), ks, img), fr: In.Fr(m0, m, F),
  +Bc: Nat, +hB: N.Le(1n+In.cap(k, N), Bc), -k_: Cr.Cir.State -> Cr.Cir.Out, -R: Cr.Cir.State -> Type,
  g: In.ol.K(fo, k, N, F, K, L, I, f0, fc, ks, img, m0, In.f3(k, fl), k_, R, Bc)) ->
  In.Go(10n+Nat.add(k, d), In.c.OW(), In.S(In.R(fo, U32.from_nat(k), ib, il, iu, ij, t1, t2), m, next, F, K, pg, L, I), k_, R, In.oom(L, Bc)):
  match k:
    case 0n:
      In.wh.end(9n+d, Mc.M.ne(Mc.M.g(Mc.R.ii()), Mc.M.c(0)), In.c.body(), In.S(In.R(fo, U32.from_nat(0n), ib, il, iu, ij, t1, t2), m, next, F, K, pg, L, I),
        k_, R, In.oom(L, Bc), {==}, g(ib, il, iu, ij, t1, t2, m, next, N, pg, N.le_refl(N), fa, sl, fr))
    case 1n+(+p):
      In.wh(9n+(1n+Nat.add(p, d)), Mc.M.ne(Mc.M.g(Mc.R.ii()), Mc.M.c(0)), In.c.body(), In.S(In.R(fo, U32.from_nat(1n+p), ib, il, iu, ij, t1, t2), m, next, F, K, pg, L, I),
       k_, R, In.oom(L, Bc), In.evne(p, M, N.le_trans(1n+p, List.length(&2, Word(8n), I), U32.to_nat(M), hkl, hLM), fo, ib, il, iu, ij, t1, t2, m, next, F, K, pg, L, I),
       In.or(1n+Nat.add(p, d), fo, p, ib, il, iu, ij, t1, t2, m, next, N, F, K, pg, L, I, f0, fc, ks, img, m0, fl, M, hF, hK, hc, hcl, hkl, hLM, fa, sl, fr,
        Bc, N.le_trans(27n+N, 1n+In.cap(p, 27n+N), Bc, N.le_succ(27n+N, In.cap(p, 27n+N), In.cap.ge(p, 27n+N)), hB), t => Cr.Cir.exec.then(Cr.Cir.exec(9n+(1n+Nat.add(p, d)), In.c.OW(), t), k_), R,
        +ib2 => +il2 => +iu2 => +ij2 => +t12 => +t22 => +m2 => +nx2 => +N2 => +pg2 => +hN2 => +fa2 => +sl2 => fr2 =>
         In.ol(p, d, fo, ib2, il2, iu2, ij2, t12, t22, m2, nx2, N2, F, K, pg2, L, I, f0, fc, ks, img, m0, 3n+fl, M, hF, hK, hc,
          N.le_succ(fc, 2n+fl, N.le_succ(fc, 1n+fl, N.le_succ(fc, fl, hcl))), N.weaken(p, List.length(&2, Word(8n), I), hkl), hLM, fa2, sl2, fr2, Bc, N.le_trans(1n+In.cap(p, N2), 1n+In.cap(p, 27n+N), Bc, In.cap.mono(p, N2, 27n+N, hN2), hB), k_, R,
          +ib3 => +il3 => +iu3 => +ij3 => +t13 => +t23 => +m3 => +nx3 => +N3 => +pg3 => hN3 => +fa3 => +sl3 => fr3 =>
           g(ib3, il3, iu3, ij3, t13, t23, m3, nx3, N3, pg3,
             N.le_trans(N3, In.cap(p, N2), In.cap(p, 27n+N), hN3, In.cap.mono(p, N2, 27n+N, hN2)), fa3, sl3, fr3))))

# M.input
# -------

# a pair of types, and a value with a property
def In.T(-A: Type, -B: Type) -> Type:
  Sigma<&1, &1, A, _ => B>

def In.EU(-B: U32 -> Type) -> Type:
  Sigma<&2, &1, U32, x => B(x)>

def In.EN(-B: Nat -> Type) -> Type:
  Sigma<&2, &1, Nat, x => B(x)>

def In.EC(-B: Cr.Cir.Cells -> Type) -> Type:
  Sigma<&2, &1, Cr.Cir.Cells, x => B(x)>

# the end of a run, in a state of which R holds
def In.top(o: Cr.Cir.Out, -R: Cr.Cir.State -> Type, -Om: Type, h: In.Ok(Cr.Cir.exec.then(o, t => Cr.Cir.Out.next{t}), R, Om)) -> In.Ok(o, R, Om):
  match o:
    case Cr.Cir.Out.next{st}:
      h
    case Cr.Cir.Out.halt{s, st}:
      h
    case Cr.Cir.Out.out_of_memory{}:
      h
    case Cr.Cir.Out.trap{}:
      h
    case Cr.Cir.Out.not_done{}:
      h

# the term of a state with no frame is its focus's
def In.state(+f: Nat, +fo: U32, +ib: U32, +il: U32, +iu: U32, +ij: U32, +t1: U32, +t2: U32, +m1: Cr.Cir.Cells, +nx1: U32, +F: U32,
  +K: U32, +pg1: U32, +L: U32, +I: List<&2, Word(8n)>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +t: Bk.Term,
  e: {Some{t} == T.tm.of(1n+f, m1, ks, img, fo) : Maybe<&2, Bk.Term>}) ->
  {Some{t} == T.tm.state(1n+f, ks, img, In.S(In.R(fo, 0, ib, il, iu, ij, t1, t2), m1, nx1, F, K, pg1, L, I)) : Maybe<&2, Bk.Term>}:
  %e : {Some{t} == T.tm.bind(_, u => T.tm.plugs(1n+f, m1, ks, img, 0, u)) : Maybe<&2, Bk.Term>}
  {==}

# what M.input leaves, by the values of the registers (focus fo; ii, sp, pend
# and mode 0), its cells m1 and its next cell nx1, numbered N1: the start's
# other parts; the term of the state and of the focus, with the fuel ff,
# reading only the image's first 16 cells and the cells from F before N1;
# the image's cells and the cache still stand for their terms; the cells that
# the run keeps (In.kp) are m0's; and N1 is at most ncap
def In.Fin(+fo: U32, +ib: U32, +il: U32, +iu: U32, +ij: U32, +t1: U32, +t2: U32, +m1: Cr.Cir.Cells, +nx1: U32, +N1: Nat, +pg1: U32,
  -m0: Cr.Cir.Cells, +F: U32, +K: U32, +L: U32, +I: List<&2, Word(8n)>, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +ff: Nat, +ncap: Nat, +st: Cr.Cir.State) -> Type:
  In.T({st == In.S(In.R(fo, 0, ib, il, iu, ij, t1, t2), m1, nx1, F, K, pg1, L, I) : Cr.Cir.State},
   In.T({Some{Pg.Program.start(I)} == T.tm.state(ff, ks, img, st) : Maybe<&2, Bk.Term>},
    In.T(In.St(ff, m1, F, N1, fo, Pg.Program.start(I), ks, img),
     In.T(In.Fa(m1, nx1, N1, F, f0, fc, ks, img),
      In.T(In.Fr(m0, m1, F), N.Le(N1, ncap))))))

def In.Post(-m0: Cr.Cir.Cells, +F: U32, +K: U32, +L: U32, +I: List<&2, Word(8n)>, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +ff: Nat, +ncap: Nat, +st: Cr.Cir.State) -> Type:
  In.EU(+fo => In.EU(+ib => In.EU(+il => In.EU(+iu => In.EU(+ij => In.EU(+t1 => In.EU(+t2 =>
    In.EC(+m1 => In.EU(+nx1 => In.EN(+N1 => In.EU(+pg1 =>
      In.Fin(fo, ib, il, iu, ij, t1, t2, m1, nx1, N1, pg1, m0, F, K, L, I, f0, fc, ks, img, ff, ncap, st))))))))))))

def In.c.s1() -> Cr.Cir.Stmt:
  Mc.M.set(Mc.R.il(), Mc.M.c(Mc.I.nil()))

def In.c.s2() -> Cr.Cir.Stmt:
  Mc.M.set(Mc.R.ii(), Cr.Cir.Expr.size{})

def In.c.s4() -> Cr.Cir.Stmt:
  Mc.M.make(Mc.R.focus(), Mc.M.c(U32.or(Mc.T.app(), 64)), Mc.M.c(Mc.I.ref_main()), Mc.M.g(Mc.R.il()), Mc.M.c(0))

# the focus: main applied to the list
def In.inp.end(+f: Nat, +ib: U32, +il: U32, +iu: U32, +ij: U32, +t1: U32, +t2: U32, +m: Cr.Cir.Cells, +next: U32, +N: Nat,
  +F: U32, +K: U32, +pg: U32, +L: U32, +I: List<&2, Word(8n)>, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  -m0: Cr.Cir.Cells, +fl: Nat, +ncap: Nat, +hF: N.Le(272n, U32.to_nat(F)), +hl: N.Le(f0, fl), +hN: N.Le(N, ncap),
  +fa: In.Fa(m, next, N, F, f0, fc, ks, img), +sl: In.St(fl, m, F, N, il, Pg.Program.bytes(List.drop(&2, Word(8n), I, 0n)), ks, img), fr: In.Fr(m0, m, F)) ->
  In.Go(1n+f, Mc.M.do([In.c.s4()]), In.S(In.R(0, 0, ib, il, iu, ij, t1, t2), m, next, F, K, pg, L, I), t => Cr.Cir.Out.next{t},
    s => In.Post(m0, F, K, L, I, f0, fc, ks, img, 1n+fl, 1n+ncap, s), In.oom(L, 1n+ncap)):
  In.sq(f, In.c.s4(), Mc.M.do([]), In.S(In.R(0, 0, ib, il, iu, ij, t1, t2), m, next, F, K, pg, L, I), t => Cr.Cir.Out.next{t},
   s => In.Post(m0, F, K, L, I, f0, fc, ks, img, 1n+fl, 1n+ncap, s),
   In.oom(L, 1n+ncap), In.mk(f, Mc.R.focus(), Mc.M.c(U32.or(Mc.T.app(), 64)), Mc.M.c(Mc.I.ref_main()), Mc.M.g(Mc.R.il()), Mc.M.c(0), In.R(0, 0, ib, il, iu, ij, t1, t2), m, next,
    F, K, pg, L, I, 72, 15, il, 0,
    1n+ncap, In.hb(next, N, 1n+ncap, Fa.eN(m, next, N, F, f0, fc, ks, img, fa), hN), {==}, {==}, {==}, lt => In.cellNew(next, K, F, lt, Fa.lF(m, next, N, F, f0, fc, ks, img, fa)),
    m4 => pg4 => {==}, m4 => pg4 => {==}, m4 => pg4 => {==}, m4 => pg4 => {==},
    t => Cr.Cir.exec.then(Cr.Cir.exec(1n+f, Mc.M.do([]), t), u => Cr.Cir.Out.next{u}), s => In.Post(m0, F, K, L, I, f0, fc, ks, img, 1n+fl, 1n+ncap, s),
    +pg3 => +lt3 =>
     +sf = St.cast(1n+fl, Cr.Cir.Cells.set(m, next, Cr.Cir.Cell{72, 1, 15, il, 0}), F, 1n+N, next,
       Bk.Term.App{Bk.Quan.Q1{}, Bk.Term.Ref{Pg.Program.name.main()}, Pg.Program.bytes(List.drop(&2, Word(8n), I, 0n))}, Pg.Program.start(I), ks, img,
       Equal.cong(List<&2, Word(8n)>, Bk.Term, y => Bk.Term.App{Bk.Quan.Q1{}, Bk.Term.Ref{Pg.Program.name.main()}, Pg.Program.bytes(y)}, List.drop(&2, Word(8n), I, 0n), I,
         Equal.sym(List<&2, Word(8n)>, I, List.drop(&2, Word(8n), I, 0n), In.drop0(I))),
       In.app(fl, m, F, N, next, 15, il, Bk.Term.Ref{Pg.Program.name.main()}, Pg.Program.bytes(List.drop(&2, Word(8n), I, 0n)), ks, img,
         St.to(f0, fl, hl, m, F, N, 15, Bk.Term.Ref{Pg.Program.name.main()}, ks, img, Im.g15(f0, m, F, N, ks, img, Fa.im(m, next, N, F, f0, fc, ks, img, fa))),
         sl, Fa.hi(m, next, N, F, f0, fc, ks, img, hF, fa), Fa.hr(m, next, N, F, f0, fc, ks, img, hF, fa)))
     In.nop(f, In.S(In.R(next, 0, ib, il, iu, ij, t1, t2), Cr.Cir.Cells.set(m, next, Cr.Cir.Cell{72, 1, 15, il, 0}), U32.inc(next), F, K, pg3, L, I),
      t => Cr.Cir.Out.next{t}, s => In.Post(m0, F, K, L, I, f0, fc, ks, img, 1n+fl, 1n+ncap, s),
      In.oom(L, 1n+ncap), (next, (ib, (il, (iu, (ij, (t1, (t2, (Cr.Cir.Cells.set(m, next, Cr.Cir.Cell{72, 1, 15, il, 0}), (U32.inc(next), (1n+N, (pg3,
        ({==}, (In.state(fl, next, ib, il, iu, ij, t1, t2, Cr.Cir.Cells.set(m, next, Cr.Cir.Cell{72, 1, 15, il, 0}), U32.inc(next), F, K, pg3, L, I,
                 ks, img, Pg.Program.start(I), In.p1({Some{Pg.Program.start(I)} == T.tm.of(1n+fl, Cr.Cir.Cells.set(m, next, Cr.Cir.Cell{72, 1, 15, il, 0}), ks, img, next) : Maybe<&2, Bk.Term>},
                   In.P({True{} == In.rds(1n+fl, Cr.Cir.Cells.set(m, next, Cr.Cir.Cell{72, 1, 15, il, 0}), F, 1n+N, next) : Bool},
                     {True{} == In.nrd(1n+fl, Pg.Program.start(I), Cr.Cir.Cells.set(m, next, Cr.Cir.Cell{72, 1, 15, il, 0}), next, F, 1n+N) : Bool}), sf)),
         (sf, (Fa.step(m, next, N, F, f0, fc, ks, img, Cr.Cir.Cell{72, 1, 15, il, 0}, lt3, hF,
                 In.okn.mk(m, F, N, 72, 15, il, {==}, St.pt(fl, m, F, N, il, Pg.Program.bytes(List.drop(&2, Word(8n), I, 0n)), ks, img, Fa.e0(m, next, N, F, f0, fc, ks, img, fa), sl), {==}), fa),
          (Fr.step(m0, m, F, next, Cr.Cir.Cell{72, 1, 15, il, 0}, hF, Fa.lF(m, next, N, F, f0, fc, ks, img, fa), fr), hN)))))))))))))))))))

# M.input, from a state whose cells m stand for the image's terms and whose
# cache is empty or stands for its bytes' words: the run makes the focus the
# cell of main applied to the list of the input's bytes, or runs out of memory
def In.inp(+d: Nat, +F: U32, +K: U32, +pg: U32, +L: U32, +I: List<&2, Word(8n)>, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +M: U32, +m: Cr.Cir.Cells, +hF: N.Le(272n, U32.to_nat(F)), +hK: N.Le(271n, U32.to_nat(K)), +hc: N.Le(24n+f0, fc),
  +hLM: N.Le(List.length(&2, Word(8n), I), U32.to_nat(M)), +fa: In.Fa(m, F, U32.to_nat(F), F, f0, fc, ks, img)) ->
  In.Ok(Cr.Cir.exec(10n+Nat.add(List.length(&2, Word(8n), I), d), Mc.M.input(), In.S(In.R(0, 0, 0, 0, 0, 0, 0, 0), m, F, F, K, pg, L, I)),
    s => In.Post(m, F, K, L, I, f0, fc, ks, img, 1n+In.f3(List.length(&2, Word(8n), I), fc), 1n+In.cap(List.length(&2, Word(8n), I), U32.to_nat(F)), s), In.oom(L, 1n+In.cap(List.length(&2, Word(8n), I), U32.to_nat(F)))):
  +len = List.length(&2, Word(8n), I)
  +N0 = U32.to_nat(F)
  +hf = N.le_trans(f0, 24n+f0, fc, N.le_add_l(24n, f0), hc)
  In.top(Cr.Cir.exec(10n+Nat.add(List.length(&2, Word(8n), I), d), Mc.M.input(), In.S(In.R(0, 0, 0, 0, 0, 0, 0, 0), m, F, F, K, pg, L, I)),
   s => In.Post(m, F, K, L, I, f0, fc, ks, img, 1n+In.f3(List.length(&2, Word(8n), I), fc), 1n+In.cap(List.length(&2, Word(8n), I), U32.to_nat(F)), s),
   In.oom(L, 1n+In.cap(List.length(&2, Word(8n), I), U32.to_nat(F))), In.sq(9n+Nat.add(List.length(&2, Word(8n), I), d), In.c.s1(), Mc.M.do([In.c.s2(), In.c.OW(), In.c.s4()]), In.S(In.R(0, 0, 0, 0, 0, 0, 0, 0), m, F, F, K, pg, L, I),
    t => Cr.Cir.Out.next{t}, s => In.Post(m, F, K, L, I, f0, fc, ks, img, 1n+In.f3(List.length(&2, Word(8n), I), fc), 1n+In.cap(List.length(&2, Word(8n), I), U32.to_nat(F)), s),
    In.oom(L, 1n+In.cap(List.length(&2, Word(8n), I), U32.to_nat(F))), In.set(9n+Nat.add(List.length(&2, Word(8n), I), d), Mc.R.il(), Mc.M.c(Mc.I.nil()), In.R(0, 0, 0, 0, 0, 0, 0, 0), m, F, F, K, pg, L, I, 11, {==}, {==},
     t => Cr.Cir.exec.then(Cr.Cir.exec(1n+(9n+Nat.add(List.length(&2, Word(8n), I), d)), Mc.M.do([In.c.s2(), In.c.OW(), In.c.s4()]), t), u => Cr.Cir.Out.next{u}),
     s => In.Post(m, F, K, L, I, f0, fc, ks, img, 1n+In.f3(List.length(&2, Word(8n), I), fc), 1n+In.cap(List.length(&2, Word(8n), I), U32.to_nat(F)), s),
     In.oom(L, 1n+In.cap(List.length(&2, Word(8n), I), U32.to_nat(F))), In.sq(9n+Nat.add(List.length(&2, Word(8n), I), d), In.c.s2(), Mc.M.do([In.c.OW(), In.c.s4()]), In.S(In.R(0, 0, 0, 11, 0, 0, 0, 0), m, F, F, K, pg, L, I),
      t => Cr.Cir.Out.next{t}, s => In.Post(m, F, K, L, I, f0, fc, ks, img, 1n+In.f3(List.length(&2, Word(8n), I), fc), 1n+In.cap(List.length(&2, Word(8n), I), U32.to_nat(F)), s),
      In.oom(L, 1n+In.cap(List.length(&2, Word(8n), I), U32.to_nat(F))), In.set(9n+Nat.add(List.length(&2, Word(8n), I), d), Mc.R.ii(), Cr.Cir.Expr.size{}, In.R(0, 0, 0, 11, 0, 0, 0, 0), m, F, F, K, pg, L, I,
       U32.from_nat(List.length(&2, Word(8n), I)),
       Equal.cong(U32, Maybe<&2, U32>, z => Some{z}, U32.from_nat(List.length(&2, Word(8n), I)), Cr.Wasm.encode.len(Word(8n), I), In.enc_len(I)), {==},
       t => Cr.Cir.exec.then(Cr.Cir.exec(1n+(9n+Nat.add(List.length(&2, Word(8n), I), d)), Mc.M.do([In.c.OW(), In.c.s4()]), t), u => Cr.Cir.Out.next{u}),
       s => In.Post(m, F, K, L, I, f0, fc, ks, img, 1n+In.f3(List.length(&2, Word(8n), I), fc), 1n+In.cap(List.length(&2, Word(8n), I), U32.to_nat(F)), s),
       In.oom(L, 1n+In.cap(List.length(&2, Word(8n), I), U32.to_nat(F))), In.sq(9n+Nat.add(List.length(&2, Word(8n), I), d), In.c.OW(), Mc.M.do([In.c.s4()]),
        In.S(In.R(0, U32.from_nat(List.length(&2, Word(8n), I)), 0, 11, 0, 0, 0, 0), m, F, F, K, pg, L, I),
        t => Cr.Cir.Out.next{t}, s => In.Post(m, F, K, L, I, f0, fc, ks, img, 1n+In.f3(List.length(&2, Word(8n), I), fc), 1n+In.cap(List.length(&2, Word(8n), I), U32.to_nat(F)), s),
        In.oom(L, 1n+In.cap(List.length(&2, Word(8n), I), U32.to_nat(F))), In.ol(List.length(&2, Word(8n), I), d, 0, 0, 11, 0, 0, 0, 0, m, F, U32.to_nat(F), F, K, pg, L, I, f0, fc, ks, img, m, fc, M, hF, hK, hc,
         N.le_refl(fc), N.le_refl(List.length(&2, Word(8n), I)), hLM, fa,
         St.cast(fc, m, F, U32.to_nat(F), 11, Pg.Program.bytes([]), Pg.Program.bytes(List.drop(&2, Word(8n), I, List.length(&2, Word(8n), I))), ks, img,
           Equal.cong(List<&2, Word(8n)>, Bk.Term, y => Pg.Program.bytes(y), [], List.drop(&2, Word(8n), I, List.length(&2, Word(8n), I)), In.drop_len(I)),
           St.to(f0, fc, hf, m, F, U32.to_nat(F), 11, Pg.Program.bytes([]), ks, img, Im.g11(f0, m, F, U32.to_nat(F), ks, img, Fa.im(m, F, U32.to_nat(F), F, f0, fc, ks, img, fa)))),
         Fr.refl(m, F),
         1n+In.cap(List.length(&2, Word(8n), I), U32.to_nat(F)), N.le_refl(1n+In.cap(List.length(&2, Word(8n), I), U32.to_nat(F))), t => Cr.Cir.exec.then(Cr.Cir.exec(1n+(9n+Nat.add(List.length(&2, Word(8n), I), d)), Mc.M.do([In.c.s4()]), t), u => Cr.Cir.Out.next{u}),
         s => In.Post(m, F, K, L, I, f0, fc, ks, img, 1n+In.f3(List.length(&2, Word(8n), I), fc), 1n+In.cap(List.length(&2, Word(8n), I), U32.to_nat(F)), s),
         +ib2 => +il2 => +iu2 => +ij2 => +t12 => +t22 => +m2 => +nx2 => +N2 => +pg2 => hN => +fa2 => +sl2 => fr2 =>
          In.inp.end(9n+Nat.add(List.length(&2, Word(8n), I), d), ib2, il2, iu2, ij2, t12, t22, m2, nx2, N2, F, K, pg2, L, I, f0, fc, ks, img, m,
            In.f3(List.length(&2, Word(8n), I), fc), In.cap(List.length(&2, Word(8n), I), U32.to_nat(F)), hF,
            N.le_trans(f0, fc, In.f3(List.length(&2, Word(8n), I), fc), hf, In.f3.ge(List.length(&2, Word(8n), I), fc)), hN, fa2, sl2, fr2))))))))

# Numbers, once more
# ------------------

# 0 is no successor
def Na.dz(n: Nat) -> Type:
  match n:
    case 0n:
      Unit
    case 1n+p:
      Empty

def Na.zs(-x: Nat, e: {0n == 1n+x : Nat}) -> Empty:
  %e : Na.dz(_)
  Unit{}

def Na.pr(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def Na.dbl_inj(a: Nat, b: Nat, e: {Nat.double(a) == Nat.double(b) : Nat}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+y:
      Empty.absurd({0n == 1n+y : Nat}, Na.zs(1n+Nat.double(y), e))
    case 1n+x 0n:
      Empty.absurd({1n+x == 0n : Nat}, Na.zs(1n+Nat.double(x), Equal.sym(Nat, 2n+Nat.double(x), 0n, e)))
    case 1n+(+x) 1n+(+y):
      Equal.cong(Nat, Nat, z => 1n+z, x, y, Na.dbl_inj(x, y, Equal.cong(Nat, Nat, z => Na.pr(Na.pr(z)), 2n+Nat.double(x), 2n+Nat.double(y), e)))

def Na.dbl_odd(a: Nat, b: Nat, e: {Nat.double(a) == 1n+Nat.double(b) : Nat}) -> Empty:
  match a b:
    case 0n _:
      Na.zs(Nat.double(b), e)
    case 1n+x 0n:
      Na.zs(Nat.double(x), Equal.sym(Nat, 1n+Nat.double(x), 0n, Equal.cong(Nat, Nat, z => Na.pr(z), 2n+Nat.double(x), 1n, e)))
    case 1n+(+x) 1n+(+y):
      Na.dbl_odd(x, y, Equal.cong(Nat, Nat, z => Na.pr(Na.pr(z)), 2n+Nat.double(x), 3n+Nat.double(y), e))

# two words of the same number are one
def Wd.inj(n: Nat, a: Word(n), b: Word(n), e: {Word.to_nat(n, a) == Word.to_nat(n, b) : Nat}) -> {a == b : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+(+p):
      match a b:
        case WCon{False{}, +s} WCon{False{}, +t}:
          Equal.cong(Word(p), Word(1n+p), z => WCon{False{}, z}, s, t,
            Wd.inj(p, s, t, Na.dbl_inj(Word.to_nat(p, s), Word.to_nat(p, t), e)))
        case WCon{True{}, +s} WCon{True{}, +t}:
          Equal.cong(Word(p), Word(1n+p), z => WCon{True{}, z}, s, t,
            Wd.inj(p, s, t, Na.dbl_inj(Word.to_nat(p, s), Word.to_nat(p, t),
              Equal.cong(Nat, Nat, z => Na.pr(z), 1n+Nat.double(Word.to_nat(p, s)), 1n+Nat.double(Word.to_nat(p, t)), e))))
        case WCon{False{}, +s} WCon{True{}, +t}:
          Empty.absurd({WCon{False{}, s} == WCon{True{}, t} : Word(1n+p)}, Na.dbl_odd(Word.to_nat(p, s), Word.to_nat(p, t), e))
        case WCon{True{}, +s} WCon{False{}, +t}:
          Empty.absurd({WCon{True{}, s} == WCon{False{}, t} : Word(1n+p)},
            Na.dbl_odd(Word.to_nat(p, t), Word.to_nat(p, s), Equal.sym(Nat, 1n+Nat.double(Word.to_nat(p, s)), Nat.double(Word.to_nat(p, t)), e)))

def U.inj(a: U32, b: U32, e: {U32.to_nat(a) == U32.to_nat(b) : Nat}) -> {a == b : U32}:
  match a b:
    case U32{+x} U32{+y}:
      Equal.cong(Word(32n), U32, z => U32{z}, x, y, Wd.inj(32n, x, y, e))

def Na.le_split.of(+x: Nat, +y: Nat, r: In.Or<{x == y : Nat}, N.Le(1n+x, y)>) -> In.Or<{1n+x == 1n+y : Nat}, N.Le(2n+x, 1n+y)>:
  match r:
    case In.Or.l{e}:
      In.Or.l{Equal.cong(Nat, Nat, z => 1n+z, x, y, e)}
    case In.Or.r{h}:
      In.Or.r{h}

# a <= b: a is b, or below it
def Na.le_split(a: Nat, b: Nat, h: N.Le(a, b)) -> In.Or<{a == b : Nat}, N.Le(1n+a, b)>:
  match a b:
    case 0n 0n:
      In.Or.l{{==}}
    case 0n 1n+y:
      In.Or.r{N.le_zero(y)}
    case 1n+x 0n:
      Empty.absurd(In.Or<{1n+x == 0n : Nat}, N.Le(2n+x, 0n)>, h)
    case 1n+(+x) 1n+(+y):
      Na.le_split.of(x, y, Na.le_split(x, y, h))


# The start's cells
# -----------------

# the image's cells 1 to 15, with main's body at the cell main
def In.p15(+main: U32) -> List<&2, Cr.Cir.Cell>:
  Mc.Img.labels(10n, 0,
    Mc.Img.pair(Mc.I.lab(Mc.N.nil()), Mc.I.lab(Mc.N.unit()), Mc.Img.pair(Mc.I.lab(Mc.N.true()), Mc.I.lab(Mc.N.unit()),
    Mc.Img.pair(Mc.I.lab(Mc.N.false()), Mc.I.lab(Mc.N.unit()), Mc.Img.pair(Mc.I.lab(Mc.N.wnil()), Mc.I.lab(Mc.N.unit()),
    Mc.Img.cell(1025, main, Mc.N.main(), 0, []))))))

# and to 271, the cache's
def In.p271(+main: U32) -> List<&2, Cr.Cir.Cell>:
  List.append(&2, Cr.Cir.Cell, In.p15(main), Mc.Img.blank(256n, []))

def In.m15(+main: U32) -> Cr.Cir.Cells:
  Cr.Cir.load(In.p15(main), 1, Cr.Cir.Cells.none{})

def In.m271(+main: U32) -> Cr.Cir.Cells:
  Cr.Cir.load(In.p271(main), 1, Cr.Cir.Cells.none{})


# the image's cells that the machine points to, with the fuel 80
def Im.m15(+main: U32, +F: U32, +N: Nat, +ds: List<&2, Bk.Def>) -> In.Im(80n, In.m15(main), F, N, T.tm.names(ds), T.tm.img(ds)):
  (({==}, ({==}, {==})), (({==}, ({==}, {==})), (({==}, ({==}, {==})), (({==}, ({==}, {==})), (({==}, ({==}, {==})), (({==}, ({==}, {==})), (({==}, ({==}, {==})), ({==}, ({==}, {==})))))))))

# Loads
# -----

# a load from i on keeps the cells below i
def Ld.keep(cs: List<&2, Cr.Cir.Cell>, +i: U32, +m: Cr.Cir.Cells, +j: U32, +M: U32, hj: N.Le(1n+U32.to_nat(j), U32.to_nat(i)),
  +hov: N.Le(Nat.add(U32.to_nat(i), List.length(&2, Cr.Cir.Cell, cs)), U32.to_nat(M))) ->
  {Cr.Cir.Cells.get(m, j) == Cr.Cir.Cells.get(Cr.Cir.load(cs, i, m), j) : Cr.Cir.Cell}:
  match cs:
    case Nil{}:
      {==}
    case Con{+c, +rest}:
      +tj = U32.to_nat(j)
      +ti = U32.to_nat(i)
      +hj1 = hj
      +hj2 = N.le_rw_r(1n+tj, 1n+ti, U32.to_nat(U32.inc(i)), Equal.sym(Nat, U32.to_nat(U32.inc(i)), 1n+ti, Ld.einc(i, List.length(&2, Cr.Cir.Cell, rest), M, hov)),
        N.le_succ(1n+tj, ti, hj1))
      Equal.trans(Cr.Cir.Cell, Cr.Cir.Cells.get(m, j), Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, i, c), j),
        Cr.Cir.Cells.get(Cr.Cir.load(rest, U32.inc(i), Cr.Cir.Cells.set(m, i, c)), j),
        Cl.get_other(m, j, i, c, e => N.not_succ_le(ti, N.le_rw_l(1n+tj, 1n+ti, ti, Equal.cong(U32, Nat, z => 1n+U32.to_nat(z), j, i, e), hj1))),
        Ld.keep(rest, U32.inc(i), Cr.Cir.Cells.set(m, i, c), j, M, hj2, Ld.hov(i, List.length(&2, Cr.Cir.Cell, rest), M, hov)))

def Ld.blen(q: Nat) -> {List.length(&2, Cr.Cir.Cell, Mc.Img.blank(q, [])) == q : Nat}:
  match q:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, Cr.Cir.Cell, Mc.Img.blank(p, [])), p, Ld.blen(p))

# field 2 of the zero cell set at i, read at j = i
def Ld.z.at(+m: Cr.Cir.Cells, +i: U32, +j: U32, eij: {i == j : U32}) ->
  {0 == Cr.Cir.Cell.get(2n, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, i, Cr.Cir.Cell{0, 0, 0, 0, 0}), j)) : U32}:
  %eij : {0 == Cr.Cir.Cell.get(2n, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, i, Cr.Cir.Cell{0, 0, 0, 0, 0}), _)) : U32}
  %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, i, Cr.Cir.Cell{0, 0, 0, 0, 0}), i), Cr.Cir.Cell{0, 0, 0, 0, 0}, Cl.get_set(m, i, Cr.Cir.Cell{0, 0, 0, 0, 0})) :
    {0 == Cr.Cir.Cell.get(2n, _) : U32}
  {==}

def Ld.zero.go(+q: Nat, +i: U32, +m: Cr.Cir.Cells, +j: U32, +M: U32, r: In.Or<{U32.to_nat(i) == U32.to_nat(j) : Nat}, N.Le(1n+U32.to_nat(i), U32.to_nat(j))>,
  +hov: N.Le(Nat.add(U32.to_nat(i), 1n+q), U32.to_nat(M)),
  ih: N.Le(U32.to_nat(U32.inc(i)), U32.to_nat(j)) -> {0 == Cr.Cir.Cell.get(2n, Cr.Cir.Cells.get(Cr.Cir.load(Mc.Img.blank(q, []), U32.inc(i), Cr.Cir.Cells.set(m, i, Cr.Cir.Cell{0, 0, 0, 0, 0})), j)) : U32}) ->
  {0 == Cr.Cir.Cell.get(2n, Cr.Cir.Cells.get(Cr.Cir.load(Mc.Img.blank(q, []), U32.inc(i), Cr.Cir.Cells.set(m, i, Cr.Cir.Cell{0, 0, 0, 0, 0})), j)) : U32}:
  match r:
    case In.Or.l{+e}:
      +ei = Ld.einc(i, q, M, hov)
      +ms = Cr.Cir.Cells.set(m, i, Cr.Cir.Cell{0, 0, 0, 0, 0})
      +hj = N.le_rw_r(1n+U32.to_nat(j), 1n+U32.to_nat(i), U32.to_nat(U32.inc(i)), Equal.sym(Nat, U32.to_nat(U32.inc(i)), 1n+U32.to_nat(i), ei),
        N.le_rw_l(1n+U32.to_nat(i), 1n+U32.to_nat(j), 1n+U32.to_nat(i), Equal.cong(Nat, Nat, z => 1n+z, U32.to_nat(i), U32.to_nat(j), e), N.le_refl(1n+U32.to_nat(i))))
      +hv = N.le_rw_l(Nat.add(U32.to_nat(U32.inc(i)), q), Nat.add(U32.to_nat(U32.inc(i)), List.length(&2, Cr.Cir.Cell, Mc.Img.blank(q, []))), U32.to_nat(M),
        Equal.cong(Nat, Nat, z => Nat.add(U32.to_nat(U32.inc(i)), z), q, List.length(&2, Cr.Cir.Cell, Mc.Img.blank(q, [])),
          Equal.sym(Nat, List.length(&2, Cr.Cir.Cell, Mc.Img.blank(q, [])), q, Ld.blen(q))), Ld.hov(i, q, M, hov))
      Equal.trans(U32, 0, Cr.Cir.Cell.get(2n, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, i, Cr.Cir.Cell{0, 0, 0, 0, 0}), j)),
        Cr.Cir.Cell.get(2n, Cr.Cir.Cells.get(Cr.Cir.load(Mc.Img.blank(q, []), U32.inc(i), Cr.Cir.Cells.set(m, i, Cr.Cir.Cell{0, 0, 0, 0, 0})), j)),
        Ld.z.at(m, i, j, U.inj(i, j, e)),
        Equal.cong(Cr.Cir.Cell, U32, y => Cr.Cir.Cell.get(2n, y), Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, i, Cr.Cir.Cell{0, 0, 0, 0, 0}), j),
          Cr.Cir.Cells.get(Cr.Cir.load(Mc.Img.blank(q, []), U32.inc(i), Cr.Cir.Cells.set(m, i, Cr.Cir.Cell{0, 0, 0, 0, 0})), j),
          Ld.keep(Mc.Img.blank(q, []), U32.inc(i), Cr.Cir.Cells.set(m, i, Cr.Cir.Cell{0, 0, 0, 0, 0}), j, M, hj, hv)))
    case In.Or.r{h}:
      +ei = Ld.einc(i, q, M, hov)
      ih(N.le_rw_l(1n+U32.to_nat(i), U32.to_nat(U32.inc(i)), U32.to_nat(j), Equal.sym(Nat, U32.to_nat(U32.inc(i)), 1n+U32.to_nat(i), ei), h))

# a load of n zero cells from i: field 2 of each of them is 0
def Ld.zero(n: Nat, +i: U32, +m: Cr.Cir.Cells, +j: U32, +M: U32, +h1: N.Le(U32.to_nat(i), U32.to_nat(j)),
  +h2: N.Le(1n+U32.to_nat(j), Nat.add(U32.to_nat(i), n)), +hov: N.Le(Nat.add(U32.to_nat(i), n), U32.to_nat(M))) ->
  {0 == Cr.Cir.Cell.get(2n, Cr.Cir.Cells.get(Cr.Cir.load(Mc.Img.blank(n, []), i, m), j)) : U32}:
  match n:
    case 0n:
      Empty.absurd({0 == Cr.Cir.Cell.get(2n, Cr.Cir.Cells.get(Cr.Cir.load(Mc.Img.blank(0n, []), i, m), j)) : U32},
        N.not_succ_le(U32.to_nat(j), N.le_trans(1n+U32.to_nat(j), U32.to_nat(i), U32.to_nat(j),
          N.le_rw_r(1n+U32.to_nat(j), Nat.add(U32.to_nat(i), 0n), U32.to_nat(i), N.add_zero(U32.to_nat(i)), h2), h1)))
    case 1n+(+q):
      +ei = Ld.einc(i, q, M, hov)
      Ld.zero.go(q, i, m, j, M, Na.le_split(U32.to_nat(i), U32.to_nat(j), h1), hov,
        h => Ld.zero(q, U32.inc(i), Cr.Cir.Cells.set(m, i, Cr.Cir.Cell{0, 0, 0, 0, 0}), j, M, h,
          N.le_rw_r(1n+U32.to_nat(j), 1n+Nat.add(U32.to_nat(i), q), Nat.add(U32.to_nat(U32.inc(i)), q),
            Equal.cong(Nat, Nat, z => Nat.add(z, q), 1n+U32.to_nat(i), U32.to_nat(U32.inc(i)), Equal.sym(Nat, U32.to_nat(U32.inc(i)), 1n+U32.to_nat(i), ei)),
            N.le_rw_r(1n+U32.to_nat(j), Nat.add(U32.to_nat(i), 1n+q), 1n+Nat.add(U32.to_nat(i), q), N.add_succ_r(U32.to_nat(i), q), h2)),
          Ld.hov(i, q, M, hov)))

# the cells xs then ys, loaded from i
def In.adv(xs: List<&2, Cr.Cir.Cell>, +i: U32) -> U32:
  match xs:
    case Nil{}:
      i
    case Con{_, r}:
      In.adv(r, U32.inc(i))

def Ld.app(xs: List<&2, Cr.Cir.Cell>, +ys: List<&2, Cr.Cir.Cell>, +i: U32, +m: Cr.Cir.Cells) ->
  {Cr.Cir.load(List.append(&2, Cr.Cir.Cell, xs, ys), i, m) == Cr.Cir.load(ys, In.adv(xs, i), Cr.Cir.load(xs, i, m)) : Cr.Cir.Cells}:
  match xs:
    case Nil{}:
      {==}
    case Con{+c, r}:
      Ld.app(r, ys, U32.inc(i), Cr.Cir.Cells.set(m, i, c))

# The start's facts
# -----------------

def Na.and_le_lt(a: Nat, b: Nat) -> {False{} == Bool.and(Nat.is_le(a, b), Nat.is_lt(b, a)) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+y:
      {==}
    case 1n+x 0n:
      {==}
    case 1n+x 1n+y:
      Na.and_le_lt(x, y)

# at the start (N is F), a cell from 16 on may not be read
def In.rd0(+j: U32, +F: U32, h16: N.Le(16n, U32.to_nat(j))) -> {False{} == In.rd(j, F, U32.to_nat(F)) : Bool}:
  +tj = U32.to_nat(j)
  +tF = U32.to_nat(F)
  %Na.lt_f(tj, 16n, h16) : {False{} == Bool.or(_, Bool.and(Nat.is_le(tF, tj), Nat.is_lt(tj, tF))) : Bool}
  Na.and_le_lt(tF, tj)

# a load from 16 on keeps what the image's cells that the machine points to
# stand for
def Im.load(cs: List<&2, Cr.Cir.Cell>, +i: U32, +m: Cr.Cir.Cells, +F: U32, +f0: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +M: U32,
  h16: N.Le(16n, U32.to_nat(i)), +hov: N.Le(Nat.add(U32.to_nat(i), List.length(&2, Cr.Cir.Cell, cs)), U32.to_nat(M)),
  im: In.Im(f0, m, F, U32.to_nat(F), ks, img)) -> In.Im(f0, Cr.Cir.load(cs, i, m), F, U32.to_nat(F), ks, img):
  match cs:
    case Nil{}:
      im
    case Con{+c, +rest}:
      +h16b = h16
      +ei = Ld.einc(i, List.length(&2, Cr.Cir.Cell, rest), M, hov)
      Im.load(rest, U32.inc(i), Cr.Cir.Cells.set(m, i, c), F, f0, ks, img, M,
        N.le_rw_r(16n, 1n+U32.to_nat(i), U32.to_nat(U32.inc(i)), Equal.sym(Nat, U32.to_nat(U32.inc(i)), 1n+U32.to_nat(i), ei), N.le_succ(16n, U32.to_nat(i), h16b)),
        Ld.hov(i, List.length(&2, Cr.Cir.Cell, rest), M, hov),
        Im.fr(f0, m, F, U32.to_nat(F), ks, img, i, c, In.rd0(i, F, h16b), im))

# a load from 272 on keeps the cache's entries
def CI.load(cs: List<&2, Cr.Cir.Cell>, +i: U32, +m: Cr.Cir.Cells, +F: U32, +fc: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +M: U32,
  h272: N.Le(272n, U32.to_nat(i)), +hov: N.Le(Nat.add(U32.to_nat(i), List.length(&2, Cr.Cir.Cell, cs)), U32.to_nat(M)),
  ci: In.CI(8n, [], fc, m, F, U32.to_nat(F), ks, img)) -> In.CI(8n, [], fc, Cr.Cir.load(cs, i, m), F, U32.to_nat(F), ks, img):
  match cs:
    case Nil{}:
      ci
    case Con{+c, +rest}:
      +hb = h272
      +ei = Ld.einc(i, List.length(&2, Cr.Cir.Cell, rest), M, hov)
      CI.load(rest, U32.inc(i), Cr.Cir.Cells.set(m, i, c), F, fc, ks, img, M,
        N.le_rw_r(272n, 1n+U32.to_nat(i), U32.to_nat(U32.inc(i)), Equal.sym(Nat, U32.to_nat(U32.inc(i)), 1n+U32.to_nat(i), ei), N.le_succ(272n, U32.to_nat(i), hb)),
        Ld.hov(i, List.length(&2, Cr.Cir.Cell, rest), M, hov),
        CI.fr(8n, [], fc, m, F, U32.to_nat(F), ks, img, i, c, In.rd0(i, F, N.le_trans(16n, 272n, U32.to_nat(i), Unit{}, hb)), hb, ci))

# the cache of the image is empty
def In.cz(+main: U32, +w: Word(8n)) -> {0 == Cr.Cir.Cell.get(2n, Cr.Cir.Cells.get(In.m271(main), In.J(w))) : U32}:
  %Equal.sym(Cr.Cir.Cells, Cr.Cir.load(In.p271(main), 1, Cr.Cir.Cells.none{}), Cr.Cir.load(Mc.Img.blank(256n, []), In.adv(In.p15(main), 1), In.m15(main)),
    Ld.app(In.p15(main), Mc.Img.blank(256n, []), 1, Cr.Cir.Cells.none{})) :
    {0 == Cr.Cir.Cell.get(2n, Cr.Cir.Cells.get(_, In.J(w))) : U32}
  Ld.zero(256n, In.adv(In.p15(main), 1), In.m15(main), In.J(w), 272, In.Jlo(w), In.Jhi(w), Unit{})

def CI.z(n: Nat, +bs: List<&2, Bool>, +fc: Nat, +main: U32, +F: U32, +N: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>) ->
  In.CI(n, bs, fc, In.m271(main), F, N, ks, img):
  match n:
    case 0n:
      In.Or.l{In.cz(main, In.wl(bs))}
    case 1n+(+p):
      (CI.z(p, Con{False{}, bs}, fc, main, F, N, ks, img), CI.z(p, Con{True{}, bs}, fc, main, F, N, ks, img))

# the image's cells, cut after cell 15 and after cell 271
def In.pre15.eq(+main: U32, +acc: List<&2, Cr.Cir.Cell>) ->
  {Mc.Img.prefix(main, acc) == List.append(&2, Cr.Cir.Cell, In.p15(main), Mc.Img.blank(256n, Mc.Img.table(acc))) : List<&2, Cr.Cir.Cell>}:
  {==}

def In.pre271.eq(+main: U32, +acc: List<&2, Cr.Cir.Cell>) ->
  {Mc.Img.prefix(main, acc) == List.append(&2, Cr.Cir.Cell, In.p271(main), Mc.Img.table(acc)) : List<&2, Cr.Cir.Cell>}:
  {==}

# the main def's body, and the cells of the book's bodies
def In.main(+ds: List<&2, Bk.Def>) -> U32:
  Mc.Img.ref(Mc.Img.defs(ds, Mc.I.book()), Pg.Program.name.main())

def In.bodies(+ds: List<&2, Bk.Def>) -> List<&2, Cr.Cir.Cell>:
  Mc.Img.bodies(ds, Mc.Img.ids(Mc.Img.known(Mc.Img.names.defs(ds)), 0, Mc.Img.Trie.none{}),
    Mc.Img.refs(Mc.Img.defs(ds, Mc.I.book()), Mc.Img.Trie.none{}), Mc.I.book())

def In.cells.eq(+ds: List<&2, Bk.Def>) -> {Mc.Img.cells(ds) == Mc.Img.prefix(In.main(ds), In.bodies(ds)) : List<&2, Cr.Cir.Cell>}:
  {==}

# the start's cells, from cell 16 on and from cell 272 on
def In.e15(+ds: List<&2, Bk.Def>) ->
  {Cr.Cir.load(Mc.Img.blank(256n, Mc.Img.table(In.bodies(ds))), In.adv(In.p15(In.main(ds)), 1), In.m15(In.main(ds))) ==
    Cr.Cir.load(Mc.Img.cells(ds), 1, Cr.Cir.Cells.none{}) : Cr.Cir.Cells}:
  %Equal.sym(List<&2, Cr.Cir.Cell>, Mc.Img.cells(ds), Mc.Img.prefix(In.main(ds), In.bodies(ds)), In.cells.eq(ds)) :
    {Cr.Cir.load(Mc.Img.blank(256n, Mc.Img.table(In.bodies(ds))), In.adv(In.p15(In.main(ds)), 1), In.m15(In.main(ds))) == Cr.Cir.load(_, 1, Cr.Cir.Cells.none{}) : Cr.Cir.Cells}
  %Equal.sym(List<&2, Cr.Cir.Cell>, Mc.Img.prefix(In.main(ds), In.bodies(ds)),
    List.append(&2, Cr.Cir.Cell, In.p15(In.main(ds)), Mc.Img.blank(256n, Mc.Img.table(In.bodies(ds)))), In.pre15.eq(In.main(ds), In.bodies(ds))) :
    {Cr.Cir.load(Mc.Img.blank(256n, Mc.Img.table(In.bodies(ds))), In.adv(In.p15(In.main(ds)), 1), In.m15(In.main(ds))) == Cr.Cir.load(_, 1, Cr.Cir.Cells.none{}) : Cr.Cir.Cells}
  Equal.sym(Cr.Cir.Cells, Cr.Cir.load(List.append(&2, Cr.Cir.Cell, In.p15(In.main(ds)), Mc.Img.blank(256n, Mc.Img.table(In.bodies(ds)))), 1, Cr.Cir.Cells.none{}), Cr.Cir.load(Mc.Img.blank(256n, Mc.Img.table(In.bodies(ds))), In.adv(In.p15(In.main(ds)), 1), In.m15(In.main(ds))),
    Ld.app(In.p15(In.main(ds)), Mc.Img.blank(256n, Mc.Img.table(In.bodies(ds))), 1, Cr.Cir.Cells.none{}))

def In.e271(+ds: List<&2, Bk.Def>) ->
  {Cr.Cir.load(Mc.Img.table(In.bodies(ds)), In.adv(In.p271(In.main(ds)), 1), In.m271(In.main(ds))) ==
    Cr.Cir.load(Mc.Img.cells(ds), 1, Cr.Cir.Cells.none{}) : Cr.Cir.Cells}:
  %Equal.sym(List<&2, Cr.Cir.Cell>, Mc.Img.cells(ds), Mc.Img.prefix(In.main(ds), In.bodies(ds)), In.cells.eq(ds)) :
    {Cr.Cir.load(Mc.Img.table(In.bodies(ds)), In.adv(In.p271(In.main(ds)), 1), In.m271(In.main(ds))) == Cr.Cir.load(_, 1, Cr.Cir.Cells.none{}) : Cr.Cir.Cells}
  %Equal.sym(List<&2, Cr.Cir.Cell>, Mc.Img.prefix(In.main(ds), In.bodies(ds)),
    List.append(&2, Cr.Cir.Cell, In.p271(In.main(ds)), Mc.Img.table(In.bodies(ds))), In.pre271.eq(In.main(ds), In.bodies(ds))) :
    {Cr.Cir.load(Mc.Img.table(In.bodies(ds)), In.adv(In.p271(In.main(ds)), 1), In.m271(In.main(ds))) == Cr.Cir.load(_, 1, Cr.Cir.Cells.none{}) : Cr.Cir.Cells}
  Equal.sym(Cr.Cir.Cells, Cr.Cir.load(List.append(&2, Cr.Cir.Cell, In.p271(In.main(ds)), Mc.Img.table(In.bodies(ds))), 1, Cr.Cir.Cells.none{}), Cr.Cir.load(Mc.Img.table(In.bodies(ds)), In.adv(In.p271(In.main(ds)), 1), In.m271(In.main(ds))),
    Ld.app(In.p271(In.main(ds)), Mc.Img.table(In.bodies(ds)), 1, Cr.Cir.Cells.none{}))


# the facts of other cells, by an equation
def Im.cast(-f0: Nat, -m: Cr.Cir.Cells, -m2: Cr.Cir.Cells, -F: U32, -N: Nat, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>,
  e: {m == m2 : Cr.Cir.Cells}, im: In.Im(f0, m, F, N, ks, img)) -> In.Im(f0, m2, F, N, ks, img):
  %e : In.Im(f0, _, F, N, ks, img)
  im

def CI.cast(-fc: Nat, -m: Cr.Cir.Cells, -m2: Cr.Cir.Cells, -F: U32, -N: Nat, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>,
  e: {m == m2 : Cr.Cir.Cells}, ci: In.CI(8n, [], fc, m, F, N, ks, img)) -> In.CI(8n, [], fc, m2, F, N, ks, img):
  %e : In.CI(8n, [], fc, _, F, N, ks, img)
  ci

# the image's cells that the machine points to stand for their terms at the start
def In.start.im(+ds: List<&2, Bk.Def>, +F: U32, +M: U32, +hsm: N.Le(1n+List.length(&2, Cr.Cir.Cell, Mc.Img.cells(ds)), U32.to_nat(M))) ->
  In.Im(80n, Cr.Cir.load(Mc.Img.cells(ds), 1, Cr.Cir.Cells.none{}), F, U32.to_nat(F), T.tm.names(ds), T.tm.img(ds)):
  Im.cast(80n, Cr.Cir.load(Mc.Img.blank(256n, Mc.Img.table(In.bodies(ds))), In.adv(In.p15(In.main(ds)), 1), In.m15(In.main(ds))),
   Cr.Cir.load(Mc.Img.cells(ds), 1, Cr.Cir.Cells.none{}), F, U32.to_nat(F), T.tm.names(ds), T.tm.img(ds), In.e15(ds),
   Im.load(Mc.Img.blank(256n, Mc.Img.table(In.bodies(ds))), In.adv(In.p15(In.main(ds)), 1), In.m15(In.main(ds)), F, 80n, T.tm.names(ds), T.tm.img(ds), M,
    Unit{}, hsm, Im.m15(In.main(ds), F, U32.to_nat(F), ds)))

# the cache is empty at the start
def In.start.ci(+ds: List<&2, Bk.Def>, +F: U32, +M: U32, +fc: Nat, +hsm: N.Le(1n+List.length(&2, Cr.Cir.Cell, Mc.Img.cells(ds)), U32.to_nat(M))) ->
  In.CI(8n, [], fc, Cr.Cir.load(Mc.Img.cells(ds), 1, Cr.Cir.Cells.none{}), F, U32.to_nat(F), T.tm.names(ds), T.tm.img(ds)):
  CI.cast(fc, Cr.Cir.load(Mc.Img.table(In.bodies(ds)), In.adv(In.p271(In.main(ds)), 1), In.m271(In.main(ds))),
   Cr.Cir.load(Mc.Img.cells(ds), 1, Cr.Cir.Cells.none{}), F, U32.to_nat(F), T.tm.names(ds), T.tm.img(ds), In.e271(ds),
   CI.load(Mc.Img.table(In.bodies(ds)), In.adv(In.p271(In.main(ds)), 1), In.m271(In.main(ds)), F, fc, T.tm.names(ds), T.tm.img(ds), M,
    Unit{}, hsm, CI.z(8n, [], fc, In.main(ds), F, U32.to_nat(F), T.tm.names(ds), T.tm.img(ds))))

# the cell j of the cells cs, all zeros past their end
def In.cnth(cs: List<&2, Cr.Cir.Cell>, j: Nat) -> Cr.Cir.Cell:
  match cs:
    case Nil{}:
      Cr.Cir.Cell.zero()
    case Con{c, r}:
      match j:
        case 0n:
          c
        case 1n+p:
          In.cnth(r, p)

# a load of the cells cs from i: the cell j after i holds the cell j of cs
def Ld.nth(cs: List<&2, Cr.Cir.Cell>, +i: U32, +m: Cr.Cir.Cells, j: Nat, +M: U32, hj: N.Le(1n+j, List.length(&2, Cr.Cir.Cell, cs)),
  +hov: N.Le(Nat.add(U32.to_nat(i), List.length(&2, Cr.Cir.Cell, cs)), U32.to_nat(M))) ->
  {Cr.Cir.Cells.get(Cr.Cir.load(cs, i, m), In.incn(j, i)) == In.cnth(cs, j) : Cr.Cir.Cell}:
  match cs:
    case Nil{}:
      Empty.absurd({Cr.Cir.Cells.get(Cr.Cir.load([], i, m), In.incn(j, i)) == In.cnth([], j) : Cr.Cir.Cell}, hj)
    case Con{+c, +r}:
      match j:
        case 0n:
          +ei = Ld.einc(i, List.length(&2, Cr.Cir.Cell, r), M, hov)
          Equal.trans(Cr.Cir.Cell, Cr.Cir.Cells.get(Cr.Cir.load(r, U32.inc(i), Cr.Cir.Cells.set(m, i, c)), i), Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, i, c), i), c,
            Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, i, c), i), Cr.Cir.Cells.get(Cr.Cir.load(r, U32.inc(i), Cr.Cir.Cells.set(m, i, c)), i),
              Ld.keep(r, U32.inc(i), Cr.Cir.Cells.set(m, i, c), i, M,
                N.le_rw_r(1n+U32.to_nat(i), 1n+U32.to_nat(i), U32.to_nat(U32.inc(i)), Equal.sym(Nat, U32.to_nat(U32.inc(i)), 1n+U32.to_nat(i), ei), N.le_refl(1n+U32.to_nat(i))),
                Ld.hov(i, List.length(&2, Cr.Cir.Cell, r), M, hov))),
            Cl.get_set(m, i, c))
        case 1n+(+p):
          Ld.nth(r, U32.inc(i), Cr.Cir.Cells.set(m, i, c), p, M, hj, Ld.hov(i, List.length(&2, Cr.Cir.Cell, r), M, hov))

# the start's table cell j after 272, with the mask a
def In.start.tbl(+ds: List<&2, Bk.Def>, +M: U32, +hsm: N.Le(1n+List.length(&2, Cr.Cir.Cell, Mc.Img.cells(ds)), U32.to_nat(M)), j: Nat, +a: U32,
  hj: N.Le(1n+j, List.length(&2, Cr.Cir.Cell, Mc.Img.table(In.bodies(ds)))),
  ea: {Cr.Cir.Cell.get(2n, In.cnth(Mc.Img.table(In.bodies(ds)), j)) == a : U32}) ->
  {D.Fd(2n, Cr.Cir.load(Mc.Img.cells(ds), 1, Cr.Cir.Cells.none{}), In.incn(j, In.adv(In.p271(In.main(ds)), 1))) == a : U32}:
  +bs = In.bodies(ds)
  %In.e271(ds) : {Cr.Cir.Cell.get(2n, Cr.Cir.Cells.get(_, In.incn(j, In.adv(In.p271(In.main(ds)), 1)))) == a : U32}
  %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(Cr.Cir.load(Mc.Img.table(bs), In.adv(In.p271(In.main(ds)), 1), In.m271(In.main(ds))), In.incn(j, In.adv(In.p271(In.main(ds)), 1))),
    In.cnth(Mc.Img.table(bs), j), Ld.nth(Mc.Img.table(bs), In.adv(In.p271(In.main(ds)), 1), In.m271(In.main(ds)), j, M, hj, hsm)) :
    {Cr.Cir.Cell.get(2n, _) == a : U32}
  ea

# the field 0 of the start's cell 0 is 0: the image's cells are loaded from 1
def In.start.e0(+ds: List<&2, Bk.Def>, +M: U32, +hsm: N.Le(1n+List.length(&2, Cr.Cir.Cell, Mc.Img.cells(ds)), U32.to_nat(M))) ->
  {D.Fd(0n, Cr.Cir.load(Mc.Img.cells(ds), 1, Cr.Cir.Cells.none{}), 0) == 0 : U32}:
  %Ld.keep(Mc.Img.cells(ds), 1, Cr.Cir.Cells.none{}, 0, M, Unit{}, hsm) : {Cr.Cir.Cell.get(0n, _) == 0 : U32}
  {==}

# the run took no cell yet
def In.start.rok(+m: Cr.Cir.Cells, +F: U32) -> {True{} == In.Rok(Nat.sub(U32.to_nat(F), U32.to_nat(F)), m, F, U32.to_nat(F), F) : Bool}:
  %Equal.sym(Nat, Nat.sub(U32.to_nat(F), U32.to_nat(F)), 0n, In.sub_self(U32.to_nat(F))) : {True{} == In.Rok(_, m, F, U32.to_nat(F), F) : Bool}
  {==}

# the facts of the run's cells at the start
def In.start.fb(+ds: List<&2, Bk.Def>, +F: U32, +M: U32, h291: N.Le(291n, U32.to_nat(F)),
  +hsm: N.Le(1n+List.length(&2, Cr.Cir.Cell, Mc.Img.cells(ds)), U32.to_nat(M))) ->
  In.Fb(Cr.Cir.load(Mc.Img.cells(ds), 1, Cr.Cir.Cells.none{}), U32.to_nat(F), F):
  (h291, (In.start.tbl(ds, M, hsm, 8n, 3, Unit{}, {==}), (In.start.tbl(ds, M, hsm, 10n, 3, Unit{}, {==}),
    (In.start.e0(ds, M, hsm), In.start.rok(Cr.Cir.load(Mc.Img.cells(ds), 1, Cr.Cir.Cells.none{}), F)))))

# the facts of the start state: next and first are F, numbered as F; the
# image's cells that the machine points to stand for their terms with the
# fuel 80; the cache is empty
def In.start(+ds: List<&2, Bk.Def>, +F: U32, +M: U32, +fc: Nat, h291: N.Le(291n, U32.to_nat(F)),
  +hsm: N.Le(1n+List.length(&2, Cr.Cir.Cell, Mc.Img.cells(ds)), U32.to_nat(M))) ->
  In.Fa(Cr.Cir.load(Mc.Img.cells(ds), 1, Cr.Cir.Cells.none{}), F, U32.to_nat(F), F, 80n, fc, T.tm.names(ds), T.tm.img(ds)):
  ({==}, (N.le_refl(U32.to_nat(F)), (In.start.im(ds, F, M, hsm), (In.start.ci(ds, F, M, fc, hsm), In.start.fb(ds, F, M, h291, hsm)))))

# 291 <= first, from what Cir.result computed: the image has 290 cells or more, and first is past it
def In.h291(+p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +m: U32, +k: U32, +len: U32,
  +pg: U32, +lim: U32, +first: U32, +rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>}, +small: {Mc.Img.small(p, 0) == True{} : Bool},
  s: D.Start(Mc.Img.cells(ds), i, m, k, len, pg, lim, first)) -> N.Le(291n, U32.to_nat(first)):
  (ek, r1) = s
  (em, r2) = r1
  (elim, r3) = r2
  (el, r4) = r3
  (ea, ef) = r4
  +ek2 = ek
  N.le_trans(291n, 1n+U32.to_nat(k), U32.to_nat(first), FC.hf.k290(ds, k, ek2, FC.hf.hsm(p, ds, rd, small)),
    FC.hf.kF(p, ds, k, len, first, rd, small, ek2, ef))

# M.input from Cir.result's start
# -------------------------------

# a run of which In.Ok holds, out of memory below the budget Bc, may be what
# PostB asks with the bytes B = 20 Bc
def Ok.post(o: Cr.Cir.Out, -Q: Cr.Cir.State -> Type, -Q2: Cr.Cir.State -> Type, -H: U32 -> Cr.Cir.State -> Type, dn: Bool,
  -L: U32, -Bc: Nat, -B: Nat, eB: {Nat.mul(20n, Bc) == B : Nat}, h: In.Ok(o, Q, In.oom(L, Bc)),
  c: @st: Cr.Cir.State -> Q(st) -> Q2(st)) -> D.PostB(dn, o, Q2, H, B, L):
  match o:
    case Cr.Cir.Out.next{st}:
      c(st, h)
    case Cr.Cir.Out.halt{s, st}:
      Empty.absurd(H(s, st), h)
    case Cr.Cir.Out.out_of_memory{}:
      N.le_rw_r(1n+D.Lim.bytes(L), Nat.mul(20n, Bc), B, eB, h)
    case Cr.Cir.Out.trap{}:
      h
    case Cr.Cir.Out.not_done{}:
      Empty.absurd(D.ND(dn), h)

# and it ends
def Ok.ends(o: Cr.Cir.Out, -Q: Cr.Cir.State -> Type, -Om: Type, h: In.Ok(o, Q, Om)) -> D.Ends(o):
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
      h

# a run with less fuel: the same outcome, or out of fuel
def In.post.of(o: Cr.Cir.Out, -o2: Cr.Cir.Out, -Q: Cr.Cir.State -> Type, -H: U32 -> Cr.Cir.State -> Type, -B: Nat, -L: U32,
  e: D.Ends(o) -> {o == o2 : Cr.Cir.Out}, h: D.PostB(False{}, o2, Q, H, B, L)) -> D.PostB(False{}, o, Q, H, B, L):
  match o:
    case Cr.Cir.Out.next{st}:
      %Equal.sym(Cr.Cir.Out, Cr.Cir.Out.next{st}, o2, e(Unit{})) : D.PostB(False{}, _, Q, H, B, L)
      h
    case Cr.Cir.Out.halt{s, st}:
      %Equal.sym(Cr.Cir.Out, Cr.Cir.Out.halt{s, st}, o2, e(Unit{})) : D.PostB(False{}, _, Q, H, B, L)
      h
    case Cr.Cir.Out.out_of_memory{}:
      %Equal.sym(Cr.Cir.Out, Cr.Cir.Out.out_of_memory{}, o2, e(Unit{})) : D.PostB(False{}, _, Q, H, B, L)
      h
    case Cr.Cir.Out.trap{}:
      %Equal.sym(Cr.Cir.Out, Cr.Cir.Out.trap{}, o2, e(Unit{})) : D.PostB(False{}, _, Q, H, B, L)
      h
    case Cr.Cir.Out.not_done{}:
      Unit{}

# the budget of M.input: 20 (1 + F + 27 n) bytes, as input.post counts them
def In.budget.eq(+n: Nat, +first: U32) ->
  {Nat.mul(20n, 1n+In.cap(n, U32.to_nat(first))) == D.Cells.bytes(first, 1n+Nat.mul(27n, n)) : Nat}:
  Equal.cong(Nat, Nat, z => Nat.mul(20n, z), 1n+In.cap(n, U32.to_nat(first)), Nat.add(U32.to_nat(first), 1n+Nat.mul(27n, n)),
    Equal.trans(Nat, 1n+In.cap(n, U32.to_nat(first)), 1n+Nat.add(U32.to_nat(first), Nat.mul(27n, n)), Nat.add(U32.to_nat(first), 1n+Nat.mul(27n, n)),
      Equal.cong(Nat, Nat, z => 1n+z, In.cap(n, U32.to_nat(first)), Nat.add(U32.to_nat(first), Nat.mul(27n, n)), In.cap.eq(n, U32.to_nat(first))),
      Equal.sym(Nat, Nat.add(U32.to_nat(first), 1n+Nat.mul(27n, n)), 1n+Nat.add(U32.to_nat(first), Nat.mul(27n, n)), N.add_succ_r(U32.to_nat(first), Nat.mul(27n, n)))))

# the image's size, as a U32
def In.enc_lenC(xs: List<&2, Cr.Cir.Cell>) -> {U32.from_nat(List.length(&2, Cr.Cir.Cell, xs)) == Cr.Wasm.encode.len(Cr.Cir.Cell, xs) : U32}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, r}:
      Equal.cong(U32, U32, y => U32.inc(y), U32.from_nat(List.length(&2, Cr.Cir.Cell, r)), Cr.Wasm.encode.len(Cr.Cir.Cell, r), In.enc_lenC(r))

# the image has at least 271 cells
def In.k.ge(+ds: List<&2, Bk.Def>, +k: U32, +M: U32, ek: {k == Cr.Wasm.encode.len(Cr.Cir.Cell, Mc.Img.cells(ds)) : U32},
  +hsm: N.Le(1n+List.length(&2, Cr.Cir.Cell, Mc.Img.cells(ds)), U32.to_nat(M))) -> N.Le(271n, U32.to_nat(k)):
  +n = List.length(&2, Cr.Cir.Cell, Mc.Img.cells(ds))
  %Equal.sym(U32, k, Cr.Wasm.encode.len(Cr.Cir.Cell, Mc.Img.cells(ds)), ek) : N.Le(271n, U32.to_nat(_))
  %In.enc_lenC(Mc.Img.cells(ds)) : N.Le(271n, U32.to_nat(_))
  %Equal.sym(Nat, U32.to_nat(U32.from_nat(n)), n, PM.tofrom(n, M, N.weaken(n, U32.to_nat(M), hsm))) : N.Le(271n, _)
  %Equal.sym(Nat, n, Nat.add(290n, PG.Bl(ds, 0n)), PG.cells_len(ds)) : N.Le(271n, _)
  N.le_trans(271n, 290n, Nat.add(290n, PG.Bl(ds, 0n)), Unit{}, N.le_add_r(290n, PG.Bl(ds, 0n)))

# the image of a book of fewer than 2^26 bytes has fewer than 2^26 cells
def In.hsm(+p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  small: {Mc.Img.small(p, 0) == True{} : Bool}) -> N.Le(1n+List.length(&2, Cr.Cir.Cell, Mc.Img.cells(ds)), U32.to_nat(67108864)):
  PM.lt_le(List.length(&2, Cr.Cir.Cell, Mc.Img.cells(ds)), U32.to_nat(67108864), PG.img.small.nat(p, ds, rd, small))

def In.ek(-cells: List<&2, Cr.Cir.Cell>, -i: List<&2, Word(8n)>, -m: U32, -k: U32, -len: U32, -p: U32, -lim: U32, -first: U32,
  s: D.Start(cells, i, m, k, len, p, lim, first)) -> {k == Cr.Wasm.encode.len(Cr.Cir.Cell, cells) : U32}:
  (ek, r) = s
  ek

# what M.input leaves, from Cir.result's start (In.Post): the image's cells
# with the fuel 80, the cache's entries with the fuel 106. The lemmas below
# spell it out: a type that names In.PostIn instead checks very slowly
def In.PostIn(+ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +first: U32, +k: U32, +lim: U32, +st: Cr.Cir.State) -> Type:
  In.Post(Cr.Cir.load(Mc.Img.cells(ds), 1, Cr.Cir.Cells.none{}), first, k, lim, i, 80n, 104n, T.tm.names(ds), T.tm.img(ds),
    1n+In.f3(List.length(&2, Word(8n), i), 104n), 1n+In.cap(List.length(&2, Word(8n), i), U32.to_nat(first)), st)


# In.inp, from the state St0 of the cells cs
def In.inp0(+d: Nat, +F: U32, +K: U32, +pg: U32, +L: U32, +I: List<&2, Word(8n)>, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +M: U32, +cs: List<&2, Cr.Cir.Cell>, +hF: N.Le(272n, U32.to_nat(F)), +hK: N.Le(271n, U32.to_nat(K)), +hc: N.Le(24n+f0, fc),
  +hLM: N.Le(List.length(&2, Word(8n), I), U32.to_nat(M)), +fa: In.Fa(Cr.Cir.load(cs, 1, Cr.Cir.Cells.none{}), F, U32.to_nat(F), F, f0, fc, ks, img)) ->
  In.Ok(Cr.Cir.exec(10n+Nat.add(List.length(&2, Word(8n), I), d), Mc.M.input(), D.St0(Mc.Mach.regs(), cs, F, K, pg, L, I)),
    s => In.Post(Cr.Cir.load(cs, 1, Cr.Cir.Cells.none{}), F, K, L, I, f0, fc, ks, img, 1n+In.f3(List.length(&2, Word(8n), I), fc),
      1n+In.cap(List.length(&2, Word(8n), I), U32.to_nat(F)), s), In.oom(L, 1n+In.cap(List.length(&2, Word(8n), I), U32.to_nat(F)))):
  In.inp(d, F, K, pg, L, I, f0, fc, ks, img, M, Cr.Cir.load(cs, 1, Cr.Cir.Cells.none{}), hF, hK, hc, hLM, fa)
# M.input from St0, with the fuel 10 + (|i| + d)
def In.input.ok(+d: Nat, +p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +m: U32, +k: U32, +len: U32,
  +pg: U32, +lim: U32, +first: U32, +rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>}, +small: {Mc.Img.small(p, 0) == True{} : Bool},
  +s: D.Start(Mc.Img.cells(ds), i, m, k, len, pg, lim, first), +M2: U32, +hF: N.Le(272n, U32.to_nat(first)),
  +hLM: N.Le(List.length(&2, Word(8n), i), U32.to_nat(M2))) ->
  In.Ok(Cr.Cir.exec(10n+Nat.add(List.length(&2, Word(8n), i), d), Mc.M.input(), D.St0(Mc.Mach.regs(), Mc.Img.cells(ds), first, k, pg, lim, i)),
    s => In.Post(Cr.Cir.load(Mc.Img.cells(ds), 1, Cr.Cir.Cells.none{}), first, k, lim, i, 80n, 104n, T.tm.names(ds), T.tm.img(ds), 1n+In.f3(List.length(&2, Word(8n), i), 104n), 1n+In.cap(List.length(&2, Word(8n), i), U32.to_nat(first)), s), In.oom(lim, 1n+In.cap(List.length(&2, Word(8n), i), U32.to_nat(first)))):
  In.inp0(d, first, k, pg, lim, i, 80n, 104n, T.tm.names(ds), T.tm.img(ds), M2, Mc.Img.cells(ds), hF,
    In.k.ge(ds, k, 67108864, In.ek(Mc.Img.cells(ds), i, m, k, len, pg, lim, first, s), In.hsm(p, ds, rd, small)), Unit{}, hLM,
    In.start(ds, first, 67108864, 104n, In.h291(p, ds, i, m, k, len, pg, lim, first, rd, small, s), In.hsm(p, ds, rd, small)))

# input.post of move_kit.bend, with In.Post (as In.PostIn spells it) in place of InvIn, and the
# premises hF (the first cell is past the cache) and hLM (the input has
# fewer than 2^32 bytes)
def In.input.post.lm(+f: Nat, +p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +m: U32, +k: U32, +len: U32,
  +pg: U32, +lim: U32, +first: U32, +rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>}, +small: {Mc.Img.small(p, 0) == True{} : Bool},
  +s: D.Start(Mc.Img.cells(ds), i, m, k, len, pg, lim, first), +M2: U32, +hF: N.Le(272n, U32.to_nat(first)),
  +hLM: N.Le(List.length(&2, Word(8n), i), U32.to_nat(M2))) ->
  D.PostB(False{}, Cr.Cir.exec(f, Mc.M.input(), D.St0(Mc.Mach.regs(), Mc.Img.cells(ds), first, k, pg, lim, i)), s => In.Post(Cr.Cir.load(Mc.Img.cells(ds), 1, Cr.Cir.Cells.none{}), first, k, lim, i, 80n, 104n, T.tm.names(ds), T.tm.img(ds), 1n+In.f3(List.length(&2, Word(8n), i), 104n), 1n+In.cap(List.length(&2, Word(8n), i), U32.to_nat(first)), s), s2 => st2 => Empty,
    D.Cells.bytes(first, 1n+Nat.mul(27n, List.length(&2, Word(8n), i))), lim):
  In.post.of(Cr.Cir.exec(f, Mc.M.input(), D.St0(Mc.Mach.regs(), Mc.Img.cells(ds), first, k, pg, lim, i)),
    Cr.Cir.exec(10n+Nat.add(List.length(&2, Word(8n), i), f), Mc.M.input(), D.St0(Mc.Mach.regs(), Mc.Img.cells(ds), first, k, pg, lim, i)),
    s => In.Post(Cr.Cir.load(Mc.Img.cells(ds), 1, Cr.Cir.Cells.none{}), first, k, lim, i, 80n, 104n, T.tm.names(ds), T.tm.img(ds), 1n+In.f3(List.length(&2, Word(8n), i), 104n), 1n+In.cap(List.length(&2, Word(8n), i), U32.to_nat(first)), s), s2 => st2 => Empty,
    D.Cells.bytes(first, 1n+Nat.mul(27n, List.length(&2, Word(8n), i))), lim,
    dd => D.mono(f, 10n+Nat.add(List.length(&2, Word(8n), i), f), Mc.M.input(), D.St0(Mc.Mach.regs(), Mc.Img.cells(ds), first, k, pg, lim, i),
      N.le_trans(f, Nat.add(List.length(&2, Word(8n), i), f), 10n+Nat.add(List.length(&2, Word(8n), i), f), N.le_add_l(List.length(&2, Word(8n), i), f),
        N.le_add_l(10n, Nat.add(List.length(&2, Word(8n), i), f))), dd),
    Ok.post(Cr.Cir.exec(10n+Nat.add(List.length(&2, Word(8n), i), f), Mc.M.input(), D.St0(Mc.Mach.regs(), Mc.Img.cells(ds), first, k, pg, lim, i)),
      s => In.Post(Cr.Cir.load(Mc.Img.cells(ds), 1, Cr.Cir.Cells.none{}), first, k, lim, i, 80n, 104n, T.tm.names(ds), T.tm.img(ds), 1n+In.f3(List.length(&2, Word(8n), i), 104n), 1n+In.cap(List.length(&2, Word(8n), i), U32.to_nat(first)), s), s => In.Post(Cr.Cir.load(Mc.Img.cells(ds), 1, Cr.Cir.Cells.none{}), first, k, lim, i, 80n, 104n, T.tm.names(ds), T.tm.img(ds), 1n+In.f3(List.length(&2, Word(8n), i), 104n), 1n+In.cap(List.length(&2, Word(8n), i), U32.to_nat(first)), s), s2 => st2 => Empty, False{},
      lim, 1n+In.cap(List.length(&2, Word(8n), i), U32.to_nat(first)), D.Cells.bytes(first, 1n+Nat.mul(27n, List.length(&2, Word(8n), i))), In.budget.eq(List.length(&2, Word(8n), i), first),
      In.input.ok(f, p, ds, i, m, k, len, pg, lim, first, rd, small, s, M2, hF, hLM), st => q => q))

# input.done of move_kit.bend, with the same premises: the fuel 10 + |i|
# ends the run
def In.input.done.lm(+p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +m: U32, +k: U32, +len: U32,
  +pg: U32, +lim: U32, +first: U32, +rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>}, +small: {Mc.Img.small(p, 0) == True{} : Bool},
  +s: D.Start(Mc.Img.cells(ds), i, m, k, len, pg, lim, first), +M2: U32, +hF: N.Le(272n, U32.to_nat(first)),
  +hLM: N.Le(List.length(&2, Word(8n), i), U32.to_nat(M2))) ->
  D.Ex(Nat, f => D.Ends(Cr.Cir.exec(f, Mc.M.input(), D.St0(Mc.Mach.regs(), Mc.Img.cells(ds), first, k, pg, lim, i)))):
  (10n+Nat.add(List.length(&2, Word(8n), i), 0n),
   Ok.ends(Cr.Cir.exec(10n+Nat.add(List.length(&2, Word(8n), i), 0n), Mc.M.input(), D.St0(Mc.Mach.regs(), Mc.Img.cells(ds), first, k, pg, lim, i)),
     s => In.Post(Cr.Cir.load(Mc.Img.cells(ds), 1, Cr.Cir.Cells.none{}), first, k, lim, i, 80n, 104n, T.tm.names(ds), T.tm.img(ds), 1n+In.f3(List.length(&2, Word(8n), i), 104n), 1n+In.cap(List.length(&2, Word(8n), i), U32.to_nat(first)), s), In.oom(lim, 1n+In.cap(List.length(&2, Word(8n), i), U32.to_nat(first))), In.input.ok(0n, p, ds, i, m, k, len, pg, lim, first, rd, small, s, M2, hF, hLM)))

# The input's length
# ------------------

# the word of n True bits
def In.wones(n: Nat) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      WCon{True{}, In.wones(p)}

def Cf.tf(c: Cmp) -> {False{} == Cmp.is_eq(Word.cmp.fin(True{}, False{}, c)) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def Cf.ft(c: Cmp) -> {False{} == Cmp.is_eq(Word.cmp.fin(False{}, True{}, c)) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def Cf.ff(c: Cmp) -> {Cmp.is_eq(c) == Cmp.is_eq(Word.cmp.fin(False{}, False{}, c)) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def Cf.tt(c: Cmp) -> {Cmp.is_eq(c) == Cmp.is_eq(Word.cmp.fin(True{}, True{}, c)) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

# w + 1 is 0 exactly when w is all ones
def Wd.inc0(n: Nat, w: Word(n)) ->
  {Cmp.is_eq(Word.cmp(n, w, In.wones(n))) == Cmp.is_eq(Word.cmp(n, Word.inc(n, w), Word.zero(n))) : Bool}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+(+p):
      match w:
        case WCon{False{}, +t}:
          Equal.trans(Bool, Cmp.is_eq(Word.cmp.fin(False{}, True{}, Word.cmp(p, t, In.wones(p)))), False{},
            Cmp.is_eq(Word.cmp.fin(True{}, False{}, Word.cmp(p, t, Word.zero(p)))),
            Equal.sym(Bool, False{}, Cmp.is_eq(Word.cmp.fin(False{}, True{}, Word.cmp(p, t, In.wones(p)))), Cf.ft(Word.cmp(p, t, In.wones(p)))),
            Cf.tf(Word.cmp(p, t, Word.zero(p))))
        case WCon{True{}, +t}:
          Equal.trans(Bool, Cmp.is_eq(Word.cmp.fin(True{}, True{}, Word.cmp(p, t, In.wones(p)))), Cmp.is_eq(Word.cmp(p, t, In.wones(p))),
            Cmp.is_eq(Word.cmp.fin(False{}, False{}, Word.cmp(p, Word.inc(p, t), Word.zero(p)))),
            Equal.sym(Bool, Cmp.is_eq(Word.cmp(p, t, In.wones(p))), Cmp.is_eq(Word.cmp.fin(True{}, True{}, Word.cmp(p, t, In.wones(p)))), Cf.tt(Word.cmp(p, t, In.wones(p)))),
            Equal.trans(Bool, Cmp.is_eq(Word.cmp(p, t, In.wones(p))), Cmp.is_eq(Word.cmp(p, Word.inc(p, t), Word.zero(p))),
              Cmp.is_eq(Word.cmp.fin(False{}, False{}, Word.cmp(p, Word.inc(p, t), Word.zero(p)))),
              Wd.inc0(p, t), Cf.ff(Word.cmp(p, Word.inc(p, t), Word.zero(p)))))

def In.inc0(n: U32) -> {U32.is_eq(n, 4294967295) == U32.is_zero(U32.inc(n)) : Bool}:
  match n:
    case U32{w}:
      Wd.inc0(32n, w)

def In.ns(-v: U32, e: {None{} == Some{v} : Maybe<&2, U32>}) -> Empty:
  %Equal.sym(Maybe<&2, U32>, None{}, Some{v}, e) : In.isS(_)
  Unit{}

def L32.if(b: Bool, +n: U32, rest: List<&2, Word(8n)>, +v: U32, eb: {U32.is_eq(n, 4294967295) == b : Bool},
  e: {Wa.Wasm.length32.if(b, u => Wa.Wasm.length32.go(rest, U32.inc(n))) == Some{v} : Maybe<&2, U32>},
  ih: {Wa.Wasm.length32.go(rest, U32.inc(n)) == Some{v} : Maybe<&2, U32>} ->
    N.Le(Nat.add(U32.to_nat(U32.inc(n)), List.length(&2, Word(8n), rest)), U32.to_nat(v))) ->
  N.Le(Nat.add(U32.to_nat(n), 1n+List.length(&2, Word(8n), rest)), U32.to_nat(v)):
  match b:
    case True{}:
      Empty.absurd(N.Le(Nat.add(U32.to_nat(n), 1n+List.length(&2, Word(8n), rest)), U32.to_nat(v)),
        In.ns(v, e))
    case False{}:
      +ei = PI.U32.inc_nat(n, Equal.trans(Bool, False{}, U32.is_eq(n, 4294967295), U32.is_zero(U32.inc(n)),
        Equal.sym(Bool, U32.is_eq(n, 4294967295), False{}, eb), In.inc0(n)))
      %Equal.sym(Nat, Nat.add(U32.to_nat(n), 1n+List.length(&2, Word(8n), rest)), 1n+Nat.add(U32.to_nat(n), List.length(&2, Word(8n), rest)),
        N.add_succ_r(U32.to_nat(n), List.length(&2, Word(8n), rest))) : N.Le(_, U32.to_nat(v))
      %ei : N.Le(Nat.add(_, List.length(&2, Word(8n), rest)), U32.to_nat(v))
      ih(e)

# the input's length fits its U32
def L32.go(xs: List<&2, Word(8n)>, +n: U32, +v: U32, e: {Wa.Wasm.length32.go(xs, n) == Some{v} : Maybe<&2, U32>}) ->
  N.Le(Nat.add(U32.to_nat(n), List.length(&2, Word(8n), xs)), U32.to_nat(v)):
  match xs:
    case Nil{}:
      %Equal.sym(Nat, Nat.add(U32.to_nat(n), 0n), U32.to_nat(n), N.add_zero(U32.to_nat(n))) : N.Le(_, U32.to_nat(v))
      %Equal.cong(Maybe<&2, U32>, U32, y => Maybe.default(&2, U32, y, 0), Some{n}, Some{v}, e) : N.Le(U32.to_nat(n), U32.to_nat(_))
      N.le_refl(U32.to_nat(n))
    case Con{x, +rest}:
      L32.if(U32.is_eq(n, 4294967295), n, rest, v, {==}, e, y => L32.go(rest, U32.inc(n), v, y))

def L32(+i: List<&2, Word(8n)>, +len: U32, e: {Wa.Wasm.length32(i) == Some{len} : Maybe<&2, U32>}) -> N.Le(List.length(&2, Word(8n), i), U32.to_nat(len)):
  N.le_rw_l(Nat.add(U32.to_nat(0), List.length(&2, Word(8n), i)), List.length(&2, Word(8n), i), U32.to_nat(len), N.zero_add(List.length(&2, Word(8n), i)), L32.go(i, 0, len, e))

def In.el(-cells: List<&2, Cr.Cir.Cell>, -i: List<&2, Word(8n)>, -m: U32, -k: U32, -len: U32, -p: U32, -lim: U32, -first: U32,
  s: D.Start(cells, i, m, k, len, p, lim, first)) -> {Wa.Wasm.length32(i) == Some{len} : Maybe<&2, U32>}:
  (ek, r1) = s
  (em, r2) = r1
  (elim, r3) = r2
  (el, r4) = r3
  el

# input.post of move_kit.bend, with In.Post in place of InvIn (as
# In.PostIn spells it), and the premise hF: the first cell is past the cache
def In.input.post(+f: Nat, +p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +m: U32, +k: U32, +len: U32,
  +pg: U32, +lim: U32, +first: U32, +rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>}, +small: {Mc.Img.small(p, 0) == True{} : Bool},
  +s: D.Start(Mc.Img.cells(ds), i, m, k, len, pg, lim, first), +hF: N.Le(272n, U32.to_nat(first))) ->
  D.PostB(False{}, Cr.Cir.exec(f, Mc.M.input(), D.St0(Mc.Mach.regs(), Mc.Img.cells(ds), first, k, pg, lim, i)),
    s => In.Post(Cr.Cir.load(Mc.Img.cells(ds), 1, Cr.Cir.Cells.none{}), first, k, lim, i, 80n, 104n, T.tm.names(ds), T.tm.img(ds), 1n+In.f3(List.length(&2, Word(8n), i), 104n), 1n+In.cap(List.length(&2, Word(8n), i), U32.to_nat(first)), s),
    s2 => st2 => Empty, D.Cells.bytes(first, 1n+Nat.mul(27n, List.length(&2, Word(8n), i))), lim):
  In.input.post.lm(f, p, ds, i, m, k, len, pg, lim, first, rd, small, s, len, hF, L32(i, len, In.el(Mc.Img.cells(ds), i, m, k, len, pg, lim, first, s)))

# input.done of move_kit.bend, with the premise hF: the fuel 10 + |i| ends
# the run
def In.input.done(+p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +m: U32, +k: U32, +len: U32,
  +pg: U32, +lim: U32, +first: U32, +rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>}, +small: {Mc.Img.small(p, 0) == True{} : Bool},
  +s: D.Start(Mc.Img.cells(ds), i, m, k, len, pg, lim, first), +hF: N.Le(272n, U32.to_nat(first))) ->
  D.Ex(Nat, f => D.Ends(Cr.Cir.exec(f, Mc.M.input(), D.St0(Mc.Mach.regs(), Mc.Img.cells(ds), first, k, pg, lim, i)))):
  In.input.done.lm(p, ds, i, m, k, len, pg, lim, first, rd, small, s, len, hF, L32(i, len, In.el(Mc.Img.cells(ds), i, m, k, len, pg, lim, first, s)))
