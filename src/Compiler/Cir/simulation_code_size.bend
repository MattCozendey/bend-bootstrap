# compiler: the size of the machine's code
# ========================================
#
# The bytes of the code section of Cir.module(Mach.code(), ...) are fewer
# than 2^32 - 1, the premise of M.round.sized (mach.size), so that the
# machine's module decodes to itself (mach.round): each instruction encodes
# to at most 7 bytes, a block to 3 more than its body (M.ib.len); the code of
# each unit of a Cir program (NE, NS: about one per node) has at most 512 such
# bytes (cb.expr, cb.stmt); and
# Mach.code has at most 2^16 units (mach.nodes, by evaluation). The code of
# Mach.code itself is never encoded here.

import Base
import ../../Shared/shared.bend as Sd
import ../../Wasm/impl.bend as Wa
import ./impl.bend as Cr
import ../Machine/impl.bend as Mc
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

# a + (k + x) = k + (a + x)
def shk(+a: Nat, +k: Nat, +x: Nat) -> {Nat.add(a, Nat.add(k, x)) == Nat.add(k, Nat.add(a, x)) : Nat}:
  PH.H.add_k(a, k, x)

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
def cb.expr(e: Cr.Cir.Expr, +acc: List<&2, Wa.Wasm.Instr>) -> B(M.ib(Cr.Cir.code.expr(e, acc)), NE(e), M.ib(acc)):
  match e:
    case Cr.Cir.Expr.const{+n}:
      B.one(7n, 7n+M.ib(acc), M.ib(acc), N.le_refl(7n+M.ib(acc)), Unit{})
    case Cr.Cir.Expr.get{+r}:
      B.one(7n, 7n+M.ib(acc), M.ib(acc), N.le_refl(7n+M.ib(acc)), Unit{})
    case Cr.Cir.Expr.op{+o, +a, +b}:
      +Ab = Cr.Cir.code.expr(b, Con{Cr.Cir.i.op(o), acc})
      B.chain(M.ib(Cr.Cir.code.expr(a, Ab)), M.ib(Ab), NE(a), Nat.add(NE(b), 1n), M.ib(acc), cb.expr(a, Ab),
        B.chain(M.ib(Ab), 7n+M.ib(acc), NE(b), 1n, M.ib(acc), cb.expr(b, Con{Cr.Cir.i.op(o), acc}),
          B.one(7n, 7n+M.ib(acc), M.ib(acc), N.le_refl(7n+M.ib(acc)), Unit{})))
    case Cr.Cir.Expr.eqz{+a}:
      B.chain(M.ib(Cr.Cir.code.expr(a, Con{Wa.Wasm.Instr.eqz{}, acc})), 7n+M.ib(acc), NE(a), 1n, M.ib(acc), cb.expr(a, Con{Wa.Wasm.Instr.eqz{}, acc}),
        B.one(7n, 7n+M.ib(acc), M.ib(acc), N.le_refl(7n+M.ib(acc)), Unit{}))
    case Cr.Cir.Expr.field{+k, +c}:
      +Ac = Cr.Cir.code.at(Con{Wa.Wasm.Instr.load{U32.shln(U32.from_nat(k), 2n)}, acc})
      B.chain(M.ib(Cr.Cir.code.expr(c, Ac)), 56n+M.ib(acc), NE(c), 1n, M.ib(acc), cb.expr(c, Ac),
        B.one(56n, 56n+M.ib(acc), M.ib(acc), N.le_refl(56n+M.ib(acc)), Unit{}))
    case Cr.Cir.Expr.byte{+i}:
      +Ab = {Con{Cr.Cir.i.get(0), Con{Cr.Cir.i.op(Wa.Wasm.Op.add{}), Con{Wa.Wasm.Instr.load8_u{0}, acc}}} : List<&2, Wa.Wasm.Instr>}
      B.chain(M.ib(Cr.Cir.code.expr(i, Ab)), 21n+M.ib(acc), NE(i), 1n, M.ib(acc), cb.expr(i, Ab),
        B.one(21n, 21n+M.ib(acc), M.ib(acc), N.le_refl(21n+M.ib(acc)), Unit{}))
    case Cr.Cir.Expr.size{}:
      B.one(7n, 7n+M.ib(acc), M.ib(acc), N.le_refl(7n+M.ib(acc)), Unit{})

# the bytes of a halt's result and branch
def cb.res(b: Bool, +q: U32) -> N.Le(M.ib(List.append(&2, Wa.Wasm.Instr, Cr.Cir.code.result(b), [Wa.Wasm.Instr.br{q}])), 98n):
  match b:
    case True{}:
      Unit{}
    case False{}:
      Unit{}

# the code of a statement at d levels inside run's block, then acc
def cb.stmt(s: Cr.Cir.Stmt, +d: Nat, +acc: List<&2, Wa.Wasm.Instr>) -> B(M.ib(Cr.Cir.code.stmt(s, d, acc)), NS(s), M.ib(acc)):
  match s:
    case Cr.Cir.Stmt.nop{}:
      B.refl(M.ib(acc))
    case Cr.Cir.Stmt.set{+r, +e}:
      +Ae = {Con{Cr.Cir.i.set(Cr.Cir.l.reg(r)), acc} : List<&2, Wa.Wasm.Instr>}
      B.chain(M.ib(Cr.Cir.code.expr(e, Ae)), 7n+M.ib(acc), NE(e), 1n, M.ib(acc), cb.expr(e, Ae),
        B.one(7n, 7n+M.ib(acc), M.ib(acc), N.le_refl(7n+M.ib(acc)), Unit{}))
    case Cr.Cir.Stmt.store{+k, +c, +v}:
      +Av = {Con{Wa.Wasm.Instr.store{U32.shln(U32.from_nat(k), 2n)}, acc} : List<&2, Wa.Wasm.Instr>}
      +Ev = Cr.Cir.code.expr(v, Av)
      +Ac = Cr.Cir.code.at(Ev)
      B.chain(M.ib(Cr.Cir.code.expr(c, Ac)), M.ib(Ac), NE(c), Nat.add(1n, Nat.add(NE(v), 1n)), M.ib(acc), cb.expr(c, Ac),
        B.chain(M.ib(Ac), M.ib(Ev), 1n, Nat.add(NE(v), 1n), M.ib(acc), B.one(49n, M.ib(Ac), M.ib(Ev), N.le_refl(49n+M.ib(Ev)), Unit{}),
          B.chain(M.ib(Ev), 7n+M.ib(acc), NE(v), 1n, M.ib(acc), cb.expr(v, Av),
            B.one(7n, 7n+M.ib(acc), M.ib(acc), N.le_refl(7n+M.ib(acc)), Unit{}))))
    case Cr.Cir.Stmt.alloc{+r}:
      B.one(477n, M.ib(Cr.Cir.code.alloc(Cr.Cir.l.reg(r), d, acc)), M.ib(acc), N.le_refl(477n+M.ib(acc)), Unit{})
    case Cr.Cir.Stmt.emit{+v}:
      +Av = {Con{Wa.Wasm.Instr.store8{0}, Con{Cr.Cir.i.get(Cr.Cir.l.outn()), Con{Cr.Cir.i.const(1), Con{Cr.Cir.i.op(Wa.Wasm.Op.add{}),
        Con{Cr.Cir.i.set(Cr.Cir.l.outn()), acc}}}}} : List<&2, Wa.Wasm.Instr>}
      +Ev = Cr.Cir.code.expr(v, Av)
      B.chain(M.ib(Cr.Cir.code.emit(v, d, acc)), M.ib(Ev), 1n, Nat.add(NE(v), 1n), M.ib(acc),
        B.one(316n, M.ib(Cr.Cir.code.emit(v, d, acc)), M.ib(Ev), N.le_refl(316n+M.ib(Ev)), Unit{}),
        B.chain(M.ib(Ev), 35n+M.ib(acc), NE(v), 1n, M.ib(acc), cb.expr(v, Av),
          B.one(35n, 35n+M.ib(acc), M.ib(acc), N.le_refl(35n+M.ib(acc)), Unit{})))
    case Cr.Cir.Stmt.seq{+a, +b}:
      +Sb = Cr.Cir.code.stmt(b, d, acc)
      B.chain(M.ib(Cr.Cir.code.stmt(a, d, Sb)), M.ib(Sb), NS(a), NS(b), M.ib(acc), cb.stmt(a, d, Sb), cb.stmt(b, d, acc))
    case Cr.Cir.Stmt.if{+c, +t, +e}:
      +St = Cr.Cir.code.stmt(t, 2n+d, [Wa.Wasm.Instr.br{1}])
      +Ae = {Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{0}, St}} : List<&2, Wa.Wasm.Instr>}
      +B1 = Cr.Cir.code.expr(c, Ae)
      +Se = Cr.Cir.code.stmt(e, 1n+d, [])
      +n1 = Nat.add(NE(c), Nat.add(1n, NS(t)))
      +h1 = B.chain(M.ib(B1), M.ib(Ae), NE(c), Nat.add(1n, NS(t)), 7n, cb.expr(c, Ae),
        B.chain(M.ib(Ae), M.ib(St), 1n, NS(t), 7n, B.one(14n, M.ib(Ae), M.ib(St), N.le_refl(14n+M.ib(St)), Unit{}),
          cb.stmt(t, 2n+d, [Wa.Wasm.Instr.br{1}])))
      +h2 = B.blk(M.ib(B1), n1, M.ib(Se), 7n, h1, Unit{})
      +h3 = B.chain(3n+Nat.add(M.ib(B1), M.ib(Se)), M.ib(Se), Nat.add(n1, 1n), NS(e), 0n, h2, cb.stmt(e, 1n+d, []))
      B.blk(3n+Nat.add(M.ib(B1), M.ib(Se)), Nat.add(Nat.add(n1, 1n), NS(e)), M.ib(acc), 0n, h3, Unit{})
    case Cr.Cir.Stmt.while{+c, +body}:
      +Sb = Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])
      +Ae = {Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{1}, Sb}} : List<&2, Wa.Wasm.Instr>}
      +B1 = Cr.Cir.code.expr(c, Ae)
      +n1 = Nat.add(NE(c), Nat.add(1n, NS(body)))
      +h1 = B.chain(M.ib(B1), M.ib(Ae), NE(c), Nat.add(1n, NS(body)), 7n, cb.expr(c, Ae),
        B.chain(M.ib(Ae), M.ib(Sb), 1n, NS(body), 7n, B.one(14n, M.ib(Ae), M.ib(Sb), N.le_refl(14n+M.ib(Sb)), Unit{}),
          cb.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])))
      +h2 = B.blk(M.ib(B1), n1, 0n, 7n, h1, Unit{})
      B.blk(3n+Nat.add(M.ib(B1), 0n), Nat.add(n1, 1n), M.ib(acc), 0n, h2, Unit{})
    case Cr.Cir.Stmt.halt{+v}:
      +R = M.ib(List.append(&2, Wa.Wasm.Instr, Cr.Cir.code.result(U32.is_zero(v)), [Wa.Wasm.Instr.br{U32.from_nat(1n+d)}]))
      B.one(115n, 17n+Nat.add(R, M.ib(acc)), M.ib(acc), Z.le.add_r(R, 98n, M.ib(acc), cb.res(U32.is_zero(v), U32.from_nat(1n+d))), Unit{})

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
  +I = M.ib(Cr.Cir.code.stmt(prog, 0n, []))
  +S = List.length(&2, Word(8n), Cr.Wasm.encode.codes([Cr.Cir.alloc(k), Cr.Cir.run(prog, regs, k)]))
  +hS = N.le_trans(S, Nat.add(12n+Nat.add(258n, 1n), Nat.add(12n+Nat.add(177n+Nat.add(I, 7n), 1n), 0n)), 468n+I,
    M.codes.len(Cr.Cir.alloc(k), Cr.Cir.run(prog, regs, k)), tot(I))
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
