# compiler: the size of the machine's code
# ========================================
#
# The bytes of the code section of Cir.module(Mach.code(), ...) are fewer
# than 2^32 - 1, the premise of M.round.sized (mach.size), so that the
# machine's module decodes to itself (mach.round): each instruction encodes
# to at most 7 bytes, a block to 3 more than its body, a br_table to 12 more
# than 5 per label (ib.len); the code of each unit of a Cir program (NE, NS:
# about one per node) has at most 512 such bytes (cb.expr, cb.stmt); and
# Mach.code has at most 2^16 units (mach.nodes, by evaluation). The code of
# Mach.code itself is never encoded here.

import Base
import ../../shared/shared.bend as Sd
import ../../wasm/impl.bend as Wa
import ./impl.bend as Cr
import ../machine/impl.bend as Mc
import ../need_big.bend as N
import ./halt.bend as PH
import ./module_round_trip.bend as M
import ./simulation_numbers.bend as Z
import ../img_small.bend as G

# the units of code of an expression and of a statement: about one for each
# node, in the order that the code chains them (see cb.expr and cb.stmt)
def NE(e: Cr.Cir.Expr) -> Nat:
  match e:
    case Cr.Cir.Expr.const{_}:
      1n
    case Cr.Cir.Expr.get{_}:
      1n
    case Cr.Cir.Expr.op{_, a, b}:
      Nat.add(NE(a), Nat.add(NE(b), 1n))
    case Cr.Cir.Expr.eqz{a}:
      Nat.add(NE(a), 1n)
    case Cr.Cir.Expr.field{_, c}:
      Nat.add(NE(c), 1n)
    case Cr.Cir.Expr.byte{i}:
      Nat.add(NE(i), 1n)
    case Cr.Cir.Expr.size{}:
      1n

def NS(s: Cr.Cir.Stmt) -> Nat:
  match s:
    case Cr.Cir.Stmt.nop{}:
      0n
    case Cr.Cir.Stmt.set{_, e}:
      Nat.add(NE(e), 1n)
    case Cr.Cir.Stmt.store{_, c, v}:
      Nat.add(NE(c), Nat.add(1n, Nat.add(NE(v), 1n)))
    case Cr.Cir.Stmt.alloc{_}:
      1n
    case Cr.Cir.Stmt.emit{v}:
      Nat.add(1n, Nat.add(NE(v), 1n))
    case Cr.Cir.Stmt.seq{a, b}:
      Nat.add(NS(a), NS(b))
    case Cr.Cir.Stmt.if{c, t, e}:
      Nat.add(Nat.add(Nat.add(Nat.add(NE(c), Nat.add(1n, NS(t))), 1n), NS(e)), 1n)
    case Cr.Cir.Stmt.while{c, body}:
      Nat.add(Nat.add(Nat.add(NE(c), Nat.add(1n, NS(body))), 1n), 1n)
    case Cr.Cir.Stmt.halt{_}:
      1n

# a bound on the bytes of the instructions xs: 7 for each, 3 more than its
# body for a block or loop, 12 more than 5 per label for a br_table
def ib.tab(ls: List<&2, U32>) -> Nat:
  match ls:
    case Nil{}:
      0n
    case Con{_, r}:
      5n+ib.tab(r)

def ib(xs: List<&2, Wa.Wasm.Instr>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{x, rest}:
      match x:
        case Wa.Wasm.Instr.block{body}:
          3n+Nat.add(ib(body), ib(rest))
        case Wa.Wasm.Instr.loop{body}:
          3n+Nat.add(ib(body), ib(rest))
        case Wa.Wasm.Instr.br_table{ls, _}:
          12n+Nat.add(ib.tab(ls), ib(rest))
        case _:
          7n+ib(rest)

# Bytes of instructions
# ----------------------

def len.u(+v: U32) -> N.Le(List.length(&2, Word(8n), Cr.Wasm.encode.uleb(v)), 5n):
  M.ulen(5n, v)

def len.s(+v: U32) -> N.Le(List.length(&2, Word(8n), Cr.Wasm.encode.sleb(v)), 5n):
  N.toLe(List.length(&2, Word(8n), Cr.Wasm.encode.sleb(v)), 5n, PH.H.len_go(5n, v))

# an opcode, an immediate of at most 6 bytes, then R
def with.len(+op: U32, +imm: List<&2, Word(8n)>, +R: List<&2, Word(8n)>, +X: Nat, h: N.Le(List.length(&2, Word(8n), imm), 6n),
  ih: N.Le(List.length(&2, Word(8n), R), X)) -> N.Le(List.length(&2, Word(8n), Cr.Wasm.encode.with(op, imm, R)), 7n+X):
  N.le_rw_l(Nat.add(List.length(&2, Word(8n), imm), List.length(&2, Word(8n), R)), List.length(&2, Word(8n), List.append(&2, Word(8n), imm, R)), 6n+X,
    Equal.sym(Nat, List.length(&2, Word(8n), List.append(&2, Word(8n), imm, R)), Nat.add(List.length(&2, Word(8n), imm), List.length(&2, Word(8n), R)), M.len.app(Word(8n), imm, R)),
    N.add_mono(List.length(&2, Word(8n), imm), 6n, List.length(&2, Word(8n), R), X, h, ih))

# the labels of a br_table
def labels.len(ls: List<&2, U32>, +acc: List<&2, Word(8n)>, +X: Nat, ih: N.Le(List.length(&2, Word(8n), acc), X)) ->
  N.Le(List.length(&2, Word(8n), Cr.Wasm.encode.labels(ls, acc)), Nat.add(ib.tab(ls), X)):
  match ls:
    case Nil{}:
      ih
    case Con{+l, +r}:
      N.le_rw_l(Nat.add(List.length(&2, Word(8n), Cr.Wasm.encode.uleb(l)), List.length(&2, Word(8n), Cr.Wasm.encode.labels(r, acc))),
        List.length(&2, Word(8n), List.append(&2, Word(8n), Cr.Wasm.encode.uleb(l), Cr.Wasm.encode.labels(r, acc))), 5n+Nat.add(ib.tab(r), X),
        Equal.sym(Nat, List.length(&2, Word(8n), List.append(&2, Word(8n), Cr.Wasm.encode.uleb(l), Cr.Wasm.encode.labels(r, acc))),
          Nat.add(List.length(&2, Word(8n), Cr.Wasm.encode.uleb(l)), List.length(&2, Word(8n), Cr.Wasm.encode.labels(r, acc))), M.len.app(Word(8n), Cr.Wasm.encode.uleb(l), Cr.Wasm.encode.labels(r, acc))),
        N.add_mono(List.length(&2, Word(8n), Cr.Wasm.encode.uleb(l)), 5n, List.length(&2, Word(8n), Cr.Wasm.encode.labels(r, acc)), Nat.add(ib.tab(r), X), len.u(l),
          labels.len(r, acc, X, ih)))

# a + (k + x) = k + (a + x)
def shk(+a: Nat, +k: Nat, +x: Nat) -> {Nat.add(a, Nat.add(k, x)) == Nat.add(k, Nat.add(a, x)) : Nat}:
  PH.H.add_k(a, k, x)

# the bytes of a block of the body b, then R: 3 more than the body's bound
def blk.len(+body: List<&2, Wa.Wasm.Instr>, +R: List<&2, Word(8n)>, +X: Nat, ih: N.Le(List.length(&2, Word(8n), R), X),
  hb: N.Le(List.length(&2, Word(8n), Cr.Wasm.encode.instrs(body, Con{Sd.Byte.from_u32(11), R})), Nat.add(ib(body), 1n+List.length(&2, Word(8n), R)))) ->
  N.Le(2n+List.length(&2, Word(8n), Cr.Wasm.encode.instrs(body, Con{Sd.Byte.from_u32(11), R})), 3n+Nat.add(ib(body), X)):
  N.le_trans(2n+List.length(&2, Word(8n), Cr.Wasm.encode.instrs(body, Con{Sd.Byte.from_u32(11), R})), 2n+Nat.add(ib(body), 1n+List.length(&2, Word(8n), R)),
    3n+Nat.add(ib(body), X), hb,
    N.le_rw_l(3n+Nat.add(ib(body), List.length(&2, Word(8n), R)), 2n+Nat.add(ib(body), 1n+List.length(&2, Word(8n), R)), 3n+Nat.add(ib(body), X),
      Equal.sym(Nat, 2n+Nat.add(ib(body), 1n+List.length(&2, Word(8n), R)), 3n+Nat.add(ib(body), List.length(&2, Word(8n), R)),
        Equal.cong(Nat, Nat, z => 2n+z, Nat.add(ib(body), 1n+List.length(&2, Word(8n), R)), 1n+Nat.add(ib(body), List.length(&2, Word(8n), R)), N.add_succ_r(ib(body), List.length(&2, Word(8n), R)))),
      N.add_mono(ib(body), ib(body), List.length(&2, Word(8n), R), X, N.le_refl(ib(body)), ih)))

# reassociate the bound of a block
def blk.as(+Y: Nat, +a: Nat, +b: Nat, +c: Nat, h: N.Le(Y, 3n+Nat.add(a, Nat.add(b, c)))) -> N.Le(Y, 3n+Nat.add(Nat.add(a, b), c)):
  N.le_rw_r(Y, 3n+Nat.add(a, Nat.add(b, c)), 3n+Nat.add(Nat.add(a, b), c),
    Equal.cong(Nat, Nat, z => 3n+z, Nat.add(a, Nat.add(b, c)), Nat.add(Nat.add(a, b), c), Equal.sym(Nat, Nat.add(Nat.add(a, b), c), Nat.add(a, Nat.add(b, c)), Z.add.assoc(a, b, c))), h)

def tab.as(+Y: Nat, +a: Nat, +b: Nat, +c: Nat, h: N.Le(Y, 12n+Nat.add(a, Nat.add(b, c)))) -> N.Le(Y, 12n+Nat.add(Nat.add(a, b), c)):
  N.le_rw_r(Y, 12n+Nat.add(a, Nat.add(b, c)), 12n+Nat.add(Nat.add(a, b), c),
    Equal.cong(Nat, Nat, z => 12n+z, Nat.add(a, Nat.add(b, c)), Nat.add(Nat.add(a, b), c), Equal.sym(Nat, Nat.add(Nat.add(a, b), c), Nat.add(a, Nat.add(b, c)), Z.add.assoc(a, b, c))), h)

# the bytes of the instructions xs, then acc: at most ib(xs) + |acc|
def ib.len(xs: List<&2, Wa.Wasm.Instr>, +acc: List<&2, Word(8n)>) ->
  N.Le(List.length(&2, Word(8n), Cr.Wasm.encode.instrs(xs, acc)), Nat.add(ib(xs), List.length(&2, Word(8n), acc))):
  match xs:
    case Nil{}:
      N.le_refl(List.length(&2, Word(8n), acc))
    case Con{x, +rest}:
      match x:
        case Wa.Wasm.Instr.const{+n}:
          with.len(65, Cr.Wasm.encode.sleb(n), Cr.Wasm.encode.instrs(rest, acc), Nat.add(ib(rest), List.length(&2, Word(8n), acc)),
            N.le_trans(List.length(&2, Word(8n), Cr.Wasm.encode.sleb(n)), 5n, 6n, len.s(n), Unit{}), ib.len(rest, acc))
        case Wa.Wasm.Instr.local_get{+i}:
          with.len(32, Cr.Wasm.encode.uleb(i), Cr.Wasm.encode.instrs(rest, acc), Nat.add(ib(rest), List.length(&2, Word(8n), acc)),
            N.le_trans(List.length(&2, Word(8n), Cr.Wasm.encode.uleb(i)), 5n, 6n, len.u(i), Unit{}), ib.len(rest, acc))
        case Wa.Wasm.Instr.local_set{+i}:
          with.len(33, Cr.Wasm.encode.uleb(i), Cr.Wasm.encode.instrs(rest, acc), Nat.add(ib(rest), List.length(&2, Word(8n), acc)),
            N.le_trans(List.length(&2, Word(8n), Cr.Wasm.encode.uleb(i)), 5n, 6n, len.u(i), Unit{}), ib.len(rest, acc))
        case Wa.Wasm.Instr.local_tee{+i}:
          with.len(34, Cr.Wasm.encode.uleb(i), Cr.Wasm.encode.instrs(rest, acc), Nat.add(ib(rest), List.length(&2, Word(8n), acc)),
            N.le_trans(List.length(&2, Word(8n), Cr.Wasm.encode.uleb(i)), 5n, 6n, len.u(i), Unit{}), ib.len(rest, acc))
        case Wa.Wasm.Instr.op{o}:
          +X = Nat.add(ib(rest), List.length(&2, Word(8n), acc))
          N.le_trans(1n+List.length(&2, Word(8n), Cr.Wasm.encode.instrs(rest, acc)), 1n+X, 7n+X, ib.len(rest, acc), Z.le.add_r(1n, 7n, X, Unit{}))
        case Wa.Wasm.Instr.eqz{}:
          +X = Nat.add(ib(rest), List.length(&2, Word(8n), acc))
          N.le_trans(1n+List.length(&2, Word(8n), Cr.Wasm.encode.instrs(rest, acc)), 1n+X, 7n+X, ib.len(rest, acc), Z.le.add_r(1n, 7n, X, Unit{}))
        case Wa.Wasm.Instr.load{+o}:
          with.len(40, Con{Sd.Byte.from_u32(2), Cr.Wasm.encode.uleb(o)}, Cr.Wasm.encode.instrs(rest, acc), Nat.add(ib(rest), List.length(&2, Word(8n), acc)), len.u(o), ib.len(rest, acc))
        case Wa.Wasm.Instr.load8_u{+o}:
          with.len(45, Con{Sd.Byte.from_u32(0), Cr.Wasm.encode.uleb(o)}, Cr.Wasm.encode.instrs(rest, acc), Nat.add(ib(rest), List.length(&2, Word(8n), acc)), len.u(o), ib.len(rest, acc))
        case Wa.Wasm.Instr.store{+o}:
          with.len(54, Con{Sd.Byte.from_u32(2), Cr.Wasm.encode.uleb(o)}, Cr.Wasm.encode.instrs(rest, acc), Nat.add(ib(rest), List.length(&2, Word(8n), acc)), len.u(o), ib.len(rest, acc))
        case Wa.Wasm.Instr.store8{+o}:
          with.len(58, Con{Sd.Byte.from_u32(0), Cr.Wasm.encode.uleb(o)}, Cr.Wasm.encode.instrs(rest, acc), Nat.add(ib(rest), List.length(&2, Word(8n), acc)), len.u(o), ib.len(rest, acc))
        case Wa.Wasm.Instr.memory_size{}:
          +X = Nat.add(ib(rest), List.length(&2, Word(8n), acc))
          N.le_trans(2n+List.length(&2, Word(8n), Cr.Wasm.encode.instrs(rest, acc)), 2n+X, 7n+X, ib.len(rest, acc), Z.le.add_r(2n, 7n, X, Unit{}))
        case Wa.Wasm.Instr.memory_grow{}:
          +X = Nat.add(ib(rest), List.length(&2, Word(8n), acc))
          N.le_trans(2n+List.length(&2, Word(8n), Cr.Wasm.encode.instrs(rest, acc)), 2n+X, 7n+X, ib.len(rest, acc), Z.le.add_r(2n, 7n, X, Unit{}))
        case Wa.Wasm.Instr.block{+body}:
          +R = Cr.Wasm.encode.instrs(rest, acc)
          blk.as(2n+List.length(&2, Word(8n), Cr.Wasm.encode.instrs(body, Con{Sd.Byte.from_u32(11), R})), ib(body), ib(rest), List.length(&2, Word(8n), acc),
            blk.len(body, R, Nat.add(ib(rest), List.length(&2, Word(8n), acc)), ib.len(rest, acc), ib.len(body, Con{Sd.Byte.from_u32(11), R})))
        case Wa.Wasm.Instr.loop{+body}:
          +R = Cr.Wasm.encode.instrs(rest, acc)
          blk.as(2n+List.length(&2, Word(8n), Cr.Wasm.encode.instrs(body, Con{Sd.Byte.from_u32(11), R})), ib(body), ib(rest), List.length(&2, Word(8n), acc),
            blk.len(body, R, Nat.add(ib(rest), List.length(&2, Word(8n), acc)), ib.len(rest, acc), ib.len(body, Con{Sd.Byte.from_u32(11), R})))
        case Wa.Wasm.Instr.br{+l}:
          with.len(12, Cr.Wasm.encode.uleb(l), Cr.Wasm.encode.instrs(rest, acc), Nat.add(ib(rest), List.length(&2, Word(8n), acc)),
            N.le_trans(List.length(&2, Word(8n), Cr.Wasm.encode.uleb(l)), 5n, 6n, len.u(l), Unit{}), ib.len(rest, acc))
        case Wa.Wasm.Instr.br_if{+l}:
          with.len(13, Cr.Wasm.encode.uleb(l), Cr.Wasm.encode.instrs(rest, acc), Nat.add(ib(rest), List.length(&2, Word(8n), acc)),
            N.le_trans(List.length(&2, Word(8n), Cr.Wasm.encode.uleb(l)), 5n, 6n, len.u(l), Unit{}), ib.len(rest, acc))
        case Wa.Wasm.Instr.br_table{+ls, +l}:
          +R = Cr.Wasm.encode.instrs(rest, acc)
          +X = Nat.add(ib(rest), List.length(&2, Word(8n), acc))
          +T0 = List.append(&2, Word(8n), Cr.Wasm.encode.uleb(l), R)
          +hT0 = N.le_rw_l(Nat.add(List.length(&2, Word(8n), Cr.Wasm.encode.uleb(l)), List.length(&2, Word(8n), R)), List.length(&2, Word(8n), T0), 5n+X,
            Equal.sym(Nat, List.length(&2, Word(8n), T0), Nat.add(List.length(&2, Word(8n), Cr.Wasm.encode.uleb(l)), List.length(&2, Word(8n), R)), M.len.app(Word(8n), Cr.Wasm.encode.uleb(l), R)),
            N.add_mono(List.length(&2, Word(8n), Cr.Wasm.encode.uleb(l)), 5n, List.length(&2, Word(8n), R), X, len.u(l), ib.len(rest, acc)))
          +hall = with.len(14, Cr.Wasm.encode.uleb(Cr.Wasm.encode.len(U32, ls)), Cr.Wasm.encode.labels(ls, T0), Nat.add(ib.tab(ls), 5n+X),
            N.le_trans(List.length(&2, Word(8n), Cr.Wasm.encode.uleb(Cr.Wasm.encode.len(U32, ls))), 5n, 6n, len.u(Cr.Wasm.encode.len(U32, ls)), Unit{}),
            labels.len(ls, T0, 5n+X, hT0))
          +Y = List.length(&2, Word(8n), Cr.Wasm.encode.with(14, Cr.Wasm.encode.uleb(Cr.Wasm.encode.len(U32, ls)), Cr.Wasm.encode.labels(ls, T0)))
          tab.as(Y, ib.tab(ls), ib(rest), List.length(&2, Word(8n), acc),
            N.le_rw_r(Y, 7n+Nat.add(5n, Nat.add(ib.tab(ls), X)), 12n+Nat.add(ib.tab(ls), X), {==},
              N.le_rw_r(Y, 7n+Nat.add(ib.tab(ls), 5n+X), 7n+Nat.add(5n, Nat.add(ib.tab(ls), X)),
                Equal.cong(Nat, Nat, z => 7n+z, Nat.add(ib.tab(ls), 5n+X), Nat.add(5n, Nat.add(ib.tab(ls), X)), shk(ib.tab(ls), 5n, X)), hall)))

# Bytes of the code of a program
# -------------------------------

# 512 n: the bound on the instruction bytes of n units of code
def L(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      512n+L(p)

def L.add(+a: Nat, +b: Nat) -> {L(Nat.add(a, b)) == Nat.add(L(a), L(b)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 512n+z, L(Nat.add(p, b)), Nat.add(L(p), L(b)), L.add(p, b))

def L.mono(+a: Nat, +b: Nat, h: N.Le(a, b)) -> N.Le(L(a), L(b)):
  match a:
    case 0n:
      N.le_zero(L(b))
    case 1n+p:
      match b:
        case 0n:
          Empty.absurd(N.Le(512n+L(p), 0n), h)
        case 1n+q:
          L.mono(p, q, h)

# 2 × (512 x) = 512 (2 x)
def L.double(+x: Nat) -> {L(Nat.double(x)) == Nat.double(L(x)) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      Equal.trans(Nat, 1024n+L(Nat.double(p)), 1024n+Nat.double(L(p)), Nat.double(512n+L(p)),
        Equal.cong(Nat, Nat, z => 1024n+z, L(Nat.double(p)), Nat.double(L(p)), L.double(p)), {==})

def L.D(+k: Nat, +x: Nat) -> {L(N.D(k, x)) == N.D(k, L(x)) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+q:
      Equal.trans(Nat, L(Nat.double(N.D(q, x))), Nat.double(L(N.D(q, x))), Nat.double(N.D(q, L(x))),
        L.double(N.D(q, x)),
        Equal.cong(Nat, Nat, z => Nat.double(z), L(N.D(q, x)), N.D(q, L(x)), L.D(q, x)))

# the bytes X, then Z: at most the bytes of n units more than Z
def B(X: Nat, n: Nat, Z: Nat) -> Data:
  N.Le(X, Nat.add(L(n), Z))

# Y, at most c more than Z, for c <= 512: one unit
def B.one(+c: Nat, +Y: Nat, +Z: Nat, h: N.Le(Y, Nat.add(c, Z)), hc: N.Le(c, 512n)) -> B(Y, 1n, Z):
  N.le_trans(Y, Nat.add(c, Z), Nat.add(512n, Z), h, Z.le.add_r(c, 512n, Z, hc))

# X before Y, Y before Z
def B.chain(+X: Nat, +Y: Nat, +a: Nat, +b: Nat, +Zv: Nat, h1: B(X, a, Y), h2: B(Y, b, Zv)) -> B(X, Nat.add(a, b), Zv):
  N.le_trans(X, Nat.add(L(a), Y), Nat.add(L(Nat.add(a, b)), Zv), h1,
    N.le_rw_r(Nat.add(L(a), Y), Nat.add(L(a), Nat.add(L(b), Zv)), Nat.add(L(Nat.add(a, b)), Zv),
      Equal.trans(Nat, Nat.add(L(a), Nat.add(L(b), Zv)), Nat.add(Nat.add(L(a), L(b)), Zv), Nat.add(L(Nat.add(a, b)), Zv),
        Equal.sym(Nat, Nat.add(Nat.add(L(a), L(b)), Zv), Nat.add(L(a), Nat.add(L(b), Zv)), Z.add.assoc(L(a), L(b), Zv)),
        Equal.cong(Nat, Nat, z => Nat.add(z, Zv), Nat.add(L(a), L(b)), L(Nat.add(a, b)), Equal.sym(Nat, L(Nat.add(a, b)), Nat.add(L(a), L(b)), L.add(a, b)))),
      N.add_mono(L(a), L(a), Y, Nat.add(L(b), Zv), N.le_refl(L(a)), h2)))

# a block of the body P, then Z: P is at most c, c <= 509, more than a units
def B.blk(+P: Nat, +a: Nat, +Zv: Nat, +c: Nat, h: B(P, a, c), hc: N.Le(c, 509n)) -> B(3n+Nat.add(P, Zv), Nat.add(a, 1n), Zv):
  +La = L(a)
  N.le_trans(3n+Nat.add(P, Zv), 3n+Nat.add(Nat.add(La, c), Zv), Nat.add(L(Nat.add(a, 1n)), Zv),
    Z.le.add_r(P, Nat.add(La, c), Zv, h),
    N.le_rw_l(Nat.add(La, Nat.add(3n+c, Zv)), 3n+Nat.add(Nat.add(La, c), Zv), Nat.add(L(Nat.add(a, 1n)), Zv),
      Equal.trans(Nat, Nat.add(La, Nat.add(3n, Nat.add(c, Zv))), Nat.add(3n, Nat.add(La, Nat.add(c, Zv))), 3n+Nat.add(Nat.add(La, c), Zv),
        shk(La, 3n, Nat.add(c, Zv)),
        Equal.cong(Nat, Nat, z => 3n+z, Nat.add(La, Nat.add(c, Zv)), Nat.add(Nat.add(La, c), Zv),
          Equal.sym(Nat, Nat.add(Nat.add(La, c), Zv), Nat.add(La, Nat.add(c, Zv)), Z.add.assoc(La, c, Zv)))),
      N.le_rw_r(Nat.add(La, Nat.add(3n+c, Zv)), Nat.add(La, Nat.add(512n, Zv)), Nat.add(L(Nat.add(a, 1n)), Zv),
        Equal.trans(Nat, Nat.add(La, Nat.add(512n, Zv)), Nat.add(Nat.add(La, L(1n)), Zv), Nat.add(L(Nat.add(a, 1n)), Zv),
          Equal.sym(Nat, Nat.add(Nat.add(La, L(1n)), Zv), Nat.add(La, Nat.add(L(1n), Zv)), Z.add.assoc(La, L(1n), Zv)),
          Equal.cong(Nat, Nat, z => Nat.add(z, Zv), Nat.add(La, L(1n)), L(Nat.add(a, 1n)), Equal.sym(Nat, L(Nat.add(a, 1n)), Nat.add(La, L(1n)), L.add(a, 1n)))),
        N.add_mono(La, La, Nat.add(3n+c, Zv), Nat.add(512n, Zv), N.le_refl(La), Z.le.add_r(3n+c, 512n, Zv, hc)))))

def B.refl(+Y: Nat) -> B(Y, 0n, Y):
  N.le_refl(Y)

# the code of an expression, then acc
def cb.expr(e: Cr.Cir.Expr, +acc: List<&2, Wa.Wasm.Instr>) -> B(ib(Cr.Cir.code.expr(e, acc)), NE(e), ib(acc)):
  match e:
    case Cr.Cir.Expr.const{+n}:
      B.one(7n, 7n+ib(acc), ib(acc), N.le_refl(7n+ib(acc)), Unit{})
    case Cr.Cir.Expr.get{+r}:
      B.one(7n, 7n+ib(acc), ib(acc), N.le_refl(7n+ib(acc)), Unit{})
    case Cr.Cir.Expr.op{+o, +a, +b}:
      +Ab = Cr.Cir.code.expr(b, Con{Cr.Cir.i.op(o), acc})
      B.chain(ib(Cr.Cir.code.expr(a, Ab)), ib(Ab), NE(a), Nat.add(NE(b), 1n), ib(acc), cb.expr(a, Ab),
        B.chain(ib(Ab), 7n+ib(acc), NE(b), 1n, ib(acc), cb.expr(b, Con{Cr.Cir.i.op(o), acc}),
          B.one(7n, 7n+ib(acc), ib(acc), N.le_refl(7n+ib(acc)), Unit{})))
    case Cr.Cir.Expr.eqz{+a}:
      B.chain(ib(Cr.Cir.code.expr(a, Con{Wa.Wasm.Instr.eqz{}, acc})), 7n+ib(acc), NE(a), 1n, ib(acc), cb.expr(a, Con{Wa.Wasm.Instr.eqz{}, acc}),
        B.one(7n, 7n+ib(acc), ib(acc), N.le_refl(7n+ib(acc)), Unit{}))
    case Cr.Cir.Expr.field{+k, +c}:
      +Ac = Cr.Cir.code.at(Con{Wa.Wasm.Instr.load{U32.shln(U32.from_nat(k), 2n)}, acc})
      B.chain(ib(Cr.Cir.code.expr(c, Ac)), 56n+ib(acc), NE(c), 1n, ib(acc), cb.expr(c, Ac),
        B.one(56n, 56n+ib(acc), ib(acc), N.le_refl(56n+ib(acc)), Unit{}))
    case Cr.Cir.Expr.byte{+i}:
      +Ab = {Con{Cr.Cir.i.get(0), Con{Cr.Cir.i.op(Wa.Wasm.Op.add{}), Con{Wa.Wasm.Instr.load8_u{0}, acc}}} : List<&2, Wa.Wasm.Instr>}
      B.chain(ib(Cr.Cir.code.expr(i, Ab)), 21n+ib(acc), NE(i), 1n, ib(acc), cb.expr(i, Ab),
        B.one(21n, 21n+ib(acc), ib(acc), N.le_refl(21n+ib(acc)), Unit{}))
    case Cr.Cir.Expr.size{}:
      B.one(7n, 7n+ib(acc), ib(acc), N.le_refl(7n+ib(acc)), Unit{})

# the bytes of a halt's result and branch
def cb.res(b: Bool, +q: U32) -> N.Le(ib(List.append(&2, Wa.Wasm.Instr, Cr.Cir.code.result(b), [Wa.Wasm.Instr.br{q}])), 98n):
  match b:
    case True{}:
      Unit{}
    case False{}:
      Unit{}

# the code of a statement at d levels inside run's block, then acc
def cb.stmt(s: Cr.Cir.Stmt, +d: Nat, +acc: List<&2, Wa.Wasm.Instr>) -> B(ib(Cr.Cir.code.stmt(s, d, acc)), NS(s), ib(acc)):
  match s:
    case Cr.Cir.Stmt.nop{}:
      B.refl(ib(acc))
    case Cr.Cir.Stmt.set{+r, +e}:
      +Ae = {Con{Cr.Cir.i.set(Cr.Cir.l.reg(r)), acc} : List<&2, Wa.Wasm.Instr>}
      B.chain(ib(Cr.Cir.code.expr(e, Ae)), 7n+ib(acc), NE(e), 1n, ib(acc), cb.expr(e, Ae),
        B.one(7n, 7n+ib(acc), ib(acc), N.le_refl(7n+ib(acc)), Unit{}))
    case Cr.Cir.Stmt.store{+k, +c, +v}:
      +Av = {Con{Wa.Wasm.Instr.store{U32.shln(U32.from_nat(k), 2n)}, acc} : List<&2, Wa.Wasm.Instr>}
      +Ev = Cr.Cir.code.expr(v, Av)
      +Ac = Cr.Cir.code.at(Ev)
      B.chain(ib(Cr.Cir.code.expr(c, Ac)), ib(Ac), NE(c), Nat.add(1n, Nat.add(NE(v), 1n)), ib(acc), cb.expr(c, Ac),
        B.chain(ib(Ac), ib(Ev), 1n, Nat.add(NE(v), 1n), ib(acc), B.one(49n, ib(Ac), ib(Ev), N.le_refl(49n+ib(Ev)), Unit{}),
          B.chain(ib(Ev), 7n+ib(acc), NE(v), 1n, ib(acc), cb.expr(v, Av),
            B.one(7n, 7n+ib(acc), ib(acc), N.le_refl(7n+ib(acc)), Unit{}))))
    case Cr.Cir.Stmt.alloc{+r}:
      B.one(477n, ib(Cr.Cir.code.alloc(Cr.Cir.l.reg(r), d, acc)), ib(acc), N.le_refl(477n+ib(acc)), Unit{})
    case Cr.Cir.Stmt.emit{+v}:
      +Av = {Con{Wa.Wasm.Instr.store8{0}, Con{Cr.Cir.i.get(Cr.Cir.l.outn()), Con{Cr.Cir.i.const(1), Con{Cr.Cir.i.op(Wa.Wasm.Op.add{}),
        Con{Cr.Cir.i.set(Cr.Cir.l.outn()), acc}}}}} : List<&2, Wa.Wasm.Instr>}
      +Ev = Cr.Cir.code.expr(v, Av)
      B.chain(ib(Cr.Cir.code.emit(v, d, acc)), ib(Ev), 1n, Nat.add(NE(v), 1n), ib(acc),
        B.one(316n, ib(Cr.Cir.code.emit(v, d, acc)), ib(Ev), N.le_refl(316n+ib(Ev)), Unit{}),
        B.chain(ib(Ev), 35n+ib(acc), NE(v), 1n, ib(acc), cb.expr(v, Av),
          B.one(35n, 35n+ib(acc), ib(acc), N.le_refl(35n+ib(acc)), Unit{})))
    case Cr.Cir.Stmt.seq{+a, +b}:
      +Sb = Cr.Cir.code.stmt(b, d, acc)
      B.chain(ib(Cr.Cir.code.stmt(a, d, Sb)), ib(Sb), NS(a), NS(b), ib(acc), cb.stmt(a, d, Sb), cb.stmt(b, d, acc))
    case Cr.Cir.Stmt.if{+c, +t, +e}:
      +St = Cr.Cir.code.stmt(t, 2n+d, [Wa.Wasm.Instr.br{1}])
      +Ae = {Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{0}, St}} : List<&2, Wa.Wasm.Instr>}
      +B1 = Cr.Cir.code.expr(c, Ae)
      +Se = Cr.Cir.code.stmt(e, 1n+d, [])
      +n1 = Nat.add(NE(c), Nat.add(1n, NS(t)))
      +h1 = B.chain(ib(B1), ib(Ae), NE(c), Nat.add(1n, NS(t)), 7n, cb.expr(c, Ae),
        B.chain(ib(Ae), ib(St), 1n, NS(t), 7n, B.one(14n, ib(Ae), ib(St), N.le_refl(14n+ib(St)), Unit{}),
          cb.stmt(t, 2n+d, [Wa.Wasm.Instr.br{1}])))
      +h2 = B.blk(ib(B1), n1, ib(Se), 7n, h1, Unit{})
      +h3 = B.chain(3n+Nat.add(ib(B1), ib(Se)), ib(Se), Nat.add(n1, 1n), NS(e), 0n, h2, cb.stmt(e, 1n+d, []))
      B.blk(3n+Nat.add(ib(B1), ib(Se)), Nat.add(Nat.add(n1, 1n), NS(e)), ib(acc), 0n, h3, Unit{})
    case Cr.Cir.Stmt.while{+c, +body}:
      +Sb = Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])
      +Ae = {Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{1}, Sb}} : List<&2, Wa.Wasm.Instr>}
      +B1 = Cr.Cir.code.expr(c, Ae)
      +n1 = Nat.add(NE(c), Nat.add(1n, NS(body)))
      +h1 = B.chain(ib(B1), ib(Ae), NE(c), Nat.add(1n, NS(body)), 7n, cb.expr(c, Ae),
        B.chain(ib(Ae), ib(Sb), 1n, NS(body), 7n, B.one(14n, ib(Ae), ib(Sb), N.le_refl(14n+ib(Sb)), Unit{}),
          cb.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])))
      +h2 = B.blk(ib(B1), n1, 0n, 7n, h1, Unit{})
      B.blk(3n+Nat.add(ib(B1), 0n), Nat.add(n1, 1n), ib(acc), 0n, h2, Unit{})
    case Cr.Cir.Stmt.halt{+v}:
      +R = ib(List.append(&2, Wa.Wasm.Instr, Cr.Cir.code.result(U32.is_zero(v)), [Wa.Wasm.Instr.br{U32.from_nat(1n+d)}]))
      B.one(115n, 17n+Nat.add(R, ib(acc)), ib(acc), Z.le.add_r(R, 98n, ib(acc), cb.res(U32.is_zero(v), U32.from_nat(1n+d))), Unit{})

def mach.nodes() -> N.Le(NS(Mc.Mach.code()), N.D(16n, 1n)):
  Unit{}

# The code section
# ----------------

# x <= 2^k x
def D.ge(+k: Nat, +x: Nat) -> N.Le(x, N.D(k, x)):
  match k:
    case 0n:
      N.le_refl(x)
    case 1n+q:
      N.le_trans(x, N.D(q, x), Nat.double(N.D(q, x)), D.ge(q, x), PH.H.le_double(N.D(q, x)))

def add.self(+x: Nat) -> {Nat.add(x, x) == Nat.double(x) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      Equal.trans(Nat, 1n+Nat.add(p, 1n+p), 2n+Nat.add(p, p), Nat.double(1n+p),
        Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, 1n+p), 1n+Nat.add(p, p), N.add_succ_r(p, p)),
        Equal.cong(Nat, Nat, z => 2n+z, Nat.add(p, p), Nat.double(p), add.self(p)))

# the locals of a function: at most 7 bytes
def loc.len(+n: Nat) -> N.Le(List.length(&2, Word(8n), Cr.Wasm.encode.locals(n)), 7n):
  match n:
    case 0n:
      Unit{}
    case 1n+q:
      +u = Cr.Wasm.encode.uleb(U32.from_nat(1n+q))
      N.le_rw_l(Nat.add(List.length(&2, Word(8n), u), 1n), List.length(&2, Word(8n), List.append(&2, Word(8n), u, [Sd.Byte.from_u32(127)])), 6n,
        Equal.sym(Nat, List.length(&2, Word(8n), List.append(&2, Word(8n), u, [Sd.Byte.from_u32(127)])), Nat.add(List.length(&2, Word(8n), u), 1n), M.len.app(Word(8n), u, [Sd.Byte.from_u32(127)])),
        N.add_mono(List.length(&2, Word(8n), u), 5n, 1n, 1n, len.u(U32.from_nat(1n+q)), N.le_refl(1n)))

# a function's code: at most 13 bytes more than the bound of its body
def code.len(f: Wa.Wasm.Func) -> N.Le(List.length(&2, Word(8n), Cr.Wasm.encode.code(f)), 12n+Nat.add(ib(M.body(f)), 1n)):
  match f:
    case Wa.Wasm.Func{+a, +b, +n, +body}:
      +lo = Cr.Wasm.encode.locals(n)
      +bs = Cr.Wasm.encode.instrs(body, [Sd.Byte.from_u32(11)])
      +c = List.append(&2, Word(8n), lo, bs)
      +u = Cr.Wasm.encode.uleb(Cr.Wasm.encode.len(Word(8n), c))
      +hc = N.le_rw_l(Nat.add(List.length(&2, Word(8n), lo), List.length(&2, Word(8n), bs)), List.length(&2, Word(8n), c), 7n+Nat.add(ib(body), 1n),
        Equal.sym(Nat, List.length(&2, Word(8n), c), Nat.add(List.length(&2, Word(8n), lo), List.length(&2, Word(8n), bs)), M.len.app(Word(8n), lo, bs)),
        N.add_mono(List.length(&2, Word(8n), lo), 7n, List.length(&2, Word(8n), bs), Nat.add(ib(body), 1n), loc.len(n), ib.len(body, [Sd.Byte.from_u32(11)])))
      N.le_rw_l(Nat.add(List.length(&2, Word(8n), u), List.length(&2, Word(8n), c)), List.length(&2, Word(8n), List.append(&2, Word(8n), u, c)), 12n+Nat.add(ib(body), 1n),
        Equal.sym(Nat, List.length(&2, Word(8n), List.append(&2, Word(8n), u, c)), Nat.add(List.length(&2, Word(8n), u), List.length(&2, Word(8n), c)), M.len.app(Word(8n), u, c)),
        N.add_mono(List.length(&2, Word(8n), u), 5n, List.length(&2, Word(8n), c), 7n+Nat.add(ib(body), 1n), len.u(Cr.Wasm.encode.len(Word(8n), c)), hc))

# the codes of two functions
def codes.len(+f1: Wa.Wasm.Func, +f2: Wa.Wasm.Func) -> N.Le(List.length(&2, Word(8n), Cr.Wasm.encode.codes([f1, f2])),
  Nat.add(12n+Nat.add(ib(M.body(f1)), 1n), Nat.add(12n+Nat.add(ib(M.body(f2)), 1n), 0n))):
  +c1 = Cr.Wasm.encode.code(f1)
  +c2 = Cr.Wasm.encode.code(f2)
  +b1 = {12n+Nat.add(ib(M.body(f1)), 1n) : Nat}
  +b2 = {12n+Nat.add(ib(M.body(f2)), 1n) : Nat}
  +t = List.append(&2, Word(8n), c2, [])
  N.le_rw_l(Nat.add(List.length(&2, Word(8n), c1), List.length(&2, Word(8n), t)), List.length(&2, Word(8n), List.append(&2, Word(8n), c1, t)), Nat.add(b1, Nat.add(b2, 0n)),
    Equal.sym(Nat, List.length(&2, Word(8n), List.append(&2, Word(8n), c1, t)), Nat.add(List.length(&2, Word(8n), c1), List.length(&2, Word(8n), t)), M.len.app(Word(8n), c1, t)),
    N.add_mono(List.length(&2, Word(8n), c1), b1, List.length(&2, Word(8n), t), Nat.add(b2, 0n), code.len(f1),
      N.le_rw_l(Nat.add(List.length(&2, Word(8n), c2), 0n), List.length(&2, Word(8n), t), Nat.add(b2, 0n),
        Equal.sym(Nat, List.length(&2, Word(8n), t), Nat.add(List.length(&2, Word(8n), c2), 0n), M.len.app(Word(8n), c2, [])),
        N.add_mono(List.length(&2, Word(8n), c2), b2, 0n, 0n, code.len(f2), N.le_refl(0n)))))

# the bounds of the bodies of alloc and run add up to 468 more than I
def tot(+I: Nat) -> N.Le(Nat.add(12n+Nat.add(258n, 1n), Nat.add(12n+Nat.add(177n+Nat.add(I, 7n), 1n), 0n)), 468n+I):
  +X = Nat.add(Nat.add(Nat.add(I, 7n), 1n), 0n)
  +e = Equal.trans(Nat, X, Nat.add(Nat.add(I, 7n), 1n), Nat.add(8n, I), N.add_zero(Nat.add(Nat.add(I, 7n), 1n)),
    Equal.trans(Nat, Nat.add(Nat.add(I, 7n), 1n), Nat.add(I, 8n), Nat.add(8n, I), Z.add.assoc(I, 7n, 1n), Z.add.comm(I, 8n)))
  N.le_rw_l(Nat.add(8n, I), X, 8n+I, Equal.sym(Nat, X, Nat.add(8n, I), e), N.le_refl(8n+I))

# 470 + I <= 2^7 X, for I <= X and 470 <= X
def fin.le(+I: Nat, +X: Nat, hI: N.Le(I, X), hc: N.Le(470n, X)) -> N.Le(470n+I, N.D(7n, X)):
  N.le_trans(470n+I, N.D(1n, X), N.D(7n, X),
    N.le_rw_r(Nat.add(470n, I), Nat.add(X, X), N.D(1n, X), add.self(X), N.add_mono(470n, X, I, X, hc, hI)),
    N.le_rw_r(N.D(1n, X), N.D(6n, N.D(1n, X)), N.D(7n, X), N.D_add(6n, 1n, 7n, X, {==}), D.ge(6n, N.D(1n, X))))

# the bytes of the code section of a program of at most 2^16 units, before
# the word M = 2^32 - 1
def prog.size(+prog: Cr.Cir.Stmt, +regs: Nat, +k: U32, +M: U32, vM: {1n+U32.to_nat(M) == N.D(32n, 1n) : Nat},
  hN: N.Le(NS(prog), N.D(16n, 1n))) ->
  N.Le(1n+List.length(&2, Word(8n), Cr.Wasm.encode.codes([Cr.Cir.alloc(k), Cr.Cir.run(prog, regs, k)])), U32.to_nat(M)):
  +I = ib(Cr.Cir.code.stmt(prog, 0n, []))
  +S = List.length(&2, Word(8n), Cr.Wasm.encode.codes([Cr.Cir.alloc(k), Cr.Cir.run(prog, regs, k)]))
  +hS = N.le_trans(S, Nat.add(12n+Nat.add(258n, 1n), Nat.add(12n+Nat.add(177n+Nat.add(I, 7n), 1n), 0n)), 468n+I,
    codes.len(Cr.Cir.alloc(k), Cr.Cir.run(prog, regs, k)), tot(I))
  +X = N.D(25n, 1n)
  +eX = Equal.trans(Nat, N.D(16n, L(1n)), N.D(16n, N.D(9n, 1n)), X,
    Equal.cong(Nat, Nat, z => N.D(16n, z), L(1n), N.D(9n, 1n), {==}), N.D_add(16n, 9n, 25n, 1n, {==}))
  +hL = N.le_rw_r(I, Nat.add(L(NS(prog)), 0n), L(NS(prog)), N.add_zero(L(NS(prog))), cb.stmt(prog, 0n, []))
  +hI = N.le_rw_r(I, N.D(16n, L(1n)), X, eX,
    N.le_rw_r(I, L(N.D(16n, 1n)), N.D(16n, L(1n)), L.D(16n, 1n),
      N.le_trans(I, L(NS(prog)), L(N.D(16n, 1n)), hL, L.mono(NS(prog), N.D(16n, 1n), hN))))
  +hc = N.le_trans(470n, N.D(9n, 1n), X, Unit{},
    N.le_rw_r(N.D(9n, 1n), N.D(16n, N.D(9n, 1n)), X, N.D_add(16n, 9n, 25n, 1n, {==}), D.ge(16n, N.D(9n, 1n))))
  +h32 = N.le_rw_r(470n+I, N.D(7n, X), N.D(32n, 1n), N.D_add(7n, 25n, 32n, 1n, {==}), fin.le(I, X, hI, hc))
  N.le_rw_r(2n+S, N.D(32n, 1n), 1n+U32.to_nat(M), Equal.sym(Nat, 1n+U32.to_nat(M), N.D(32n, 1n), vM),
    N.le_trans(2n+S, 470n+I, N.D(32n, 1n), hS, h32))

# the code section of the machine's module, for any cells
def mach.size(+cells: List<&2, Cr.Cir.Cell>) ->
  N.Le(1n+List.length(&2, Word(8n), Cr.Wasm.encode.codes([Cr.Cir.alloc(Cr.Wasm.encode.len(Cr.Cir.Cell, cells)),
    Cr.Cir.run(Mc.Mach.code(), Mc.Mach.regs(), Cr.Wasm.encode.len(Cr.Cir.Cell, cells))])), U32.to_nat(4294967295)):
  prog.size(Mc.Mach.code(), Mc.Mach.regs(), Cr.Wasm.encode.len(Cr.Cir.Cell, cells), 4294967295, M.val_MAX(), mach.nodes())

# the machine's module decodes to itself, for fewer than 2^26 cells
def mach.round(+cells: List<&2, Cr.Cir.Cell>,
  small: {Nat.is_lt(List.length(&2, Cr.Cir.Cell, cells), U32.to_nat(67108864)) == True{} : Bool}) ->
  {Wa.Wasm.decode.module(Cr.Wasm.encode(Cr.Cir.module(Mc.Mach.code(), Mc.Mach.regs(), cells))) ==
    Some{Cr.Cir.module(Mc.Mach.code(), Mc.Mach.regs(), cells)} : Maybe<&2, Wa.Wasm.Module>}:
  M.round.sized(Mc.Mach.code(), Mc.Mach.regs(), cells, 67108864, 4294967295, 50000, G.val_M2(), M.val_MAX(), {==},
    M.lt_le(List.length(&2, Cr.Cir.Cell, cells), U32.to_nat(67108864), small),
    N.toLe(6n+Mc.Mach.regs(), U32.to_nat(50000), {==}), mach.size(cells))
