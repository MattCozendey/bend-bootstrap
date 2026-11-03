# compiler: the host's run of the module
# ======================================
#
# Wasm.run of the module of a Cir program, step by step as the host does it
# (instantiation, alloc, the input's write, run, the status and the output),
# against Cir.result: the module decodes to itself and is valid, so the
# instance has the memory of the minimum with the book's cells (inst);
# alloc gives what Cir.alloc.pages says (af.call); run's start reaches the
# program's block with next = Cir.first (pr.go), where the relation holds
# (IN.inv0); the program's code does what Cir.exec says (T.sim.stmt), and
# run's status gives what Cir.ended says.

import Base
import ../../Wasm/impl.bend as Wa
import ./impl.bend as Cr
import ../Machine/impl.bend as Mc
import ../need_big.bend as N
import ./halt.bend as PH
import ./module_round_trip.bend as M
import ./module_valid.bend as V
import ../img_small.bend as G
import ./simulation_steps.bend as S
import ./simulation_memory_bytes.bend as Y
import ./simulation_numbers.bend as Z
import ./simulation_relation.bend as Q
import ./simulation_write_frame.bend as F
import ./simulation_alloc_emit.bend as A
import ./simulation_first_cell_division.bend as DV
import ./simulation_stmt.bend as T
import ./simulation_alloc_run.bend as AF
import ./simulation_run_start.bend as PR
import ./simulation_start_memory.bend as IN
import ./simulation_code_size.bend as CS

# Numbers
# -------

# 1 + (2^32 - 1) = 2^32
def max.nat(+W: Nat, +hW: {W == PH.H.W(32n) : Nat}) -> {1n+U32.to_nat(4294967295) == W : Nat}:
  Equal.trans(Nat, 1n+U32.to_nat(4294967295), N.D(32n, 1n), W, M.val_MAX(), Z.d32.w(W, hW))

# a < b is false: b <= a
def nlt.rel(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), e: {Cmp.is_lt(c) == False{} : Bool}) -> N.Le(y, x):
  match c:
    case LT{}:
      Empty.absurd(N.Le(y, x), N.true_ne_false(e))
    case EQ{}:
      (%Equal.sym(Nat, x, y, r) : N.Le(y, _); N.le_refl(y))
    case GT{}:
      N.weaken(y, x, r)

def nlt.to(+a: U32, +b: U32, e: {U32.is_lt(a, b) == False{} : Bool}) -> N.Le(U32.to_nat(b), U32.to_nat(a)):
  nlt.rel(U32.cmp(a, b), U32.to_nat(a), U32.to_nat(b), N.U32.rel(a, b), e)

# a > b is false: a <= b
def ngt.rel(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), e: {Cmp.is_gt(c) == False{} : Bool}) -> N.Le(x, y):
  match c:
    case LT{}:
      N.weaken(x, y, r)
    case EQ{}:
      (%r : N.Le(x, _); N.le_refl(x))
    case GT{}:
      Empty.absurd(N.Le(x, y), N.true_ne_false(e))

def ngt.to(+a: U32, +b: U32, e: {U32.is_gt(a, b) == False{} : Bool}) -> N.Le(U32.to_nat(a), U32.to_nat(b)):
  ngt.rel(U32.cmp(a, b), U32.to_nat(a), U32.to_nat(b), N.U32.rel(a, b), e)

# a <= b: a <= b as numbers
def le.to(+a: U32, +b: U32, e: {U32.is_le(a, b) == True{} : Bool}) -> N.Le(U32.to_nat(a), U32.to_nat(b)):
  Z.rel.le(U32.cmp(a, b), U32.to_nat(a), U32.to_nat(b), N.U32.rel(a, b), e)

# a = b is false, a <= b: a < b
def ne.rel(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), e: {Cmp.is_eq(c) == False{} : Bool}, h: N.Le(x, y)) -> N.Le(1n+x, y):
  match c:
    case LT{}:
      r
    case EQ{}:
      Empty.absurd(N.Le(1n+x, y), N.true_ne_false(e))
    case GT{}:
      Empty.absurd(N.Le(1n+x, y), N.not_succ_le(y, N.le_trans(1n+y, x, y, r, h)))

# n + 1, when n is not 2^32 - 1 = T
def inc.go(+n: U32, +T: Nat, +eT: {U32.to_nat(4294967295) == T : Nat}, +W: Nat, +hW: {W == PH.H.W(32n) : Nat},
  +eW: {1n+T == W : Nat}, e: {U32.is_eq(n, 4294967295) == False{} : Bool}) ->
  {U32.to_nat(U32.inc(n)) == 1n+U32.to_nat(n) : Nat}:
  +X = U32.to_nat(n)
  +hn = N.le_rw_r(1n+X, W, 1n+T, Equal.sym(Nat, 1n+T, W, eW), Z.u32.w(n, W, hW))
  r = {(%eT : N.Rel(U32.cmp(n, 4294967295), X, _); N.U32.rel(n, 4294967295)) :
    N.Rel(U32.cmp(n, 4294967295), X, T)}
  +lt = ne.rel(U32.cmp(n, 4294967295), X, T, r, e, hn)
  F.inc.eq(n, X, {==}, W, hW, N.le_rw_r(2n+X, 1n+T, W, eW, lt))

def inc.ne1(+n: U32, +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, e: {U32.is_eq(n, 4294967295) == False{} : Bool}) ->
  {U32.to_nat(U32.inc(n)) == 1n+U32.to_nat(n) : Nat}:
  inc.go(n, U32.to_nat(4294967295), {==}, W, hW, max.nat(W, hW), e)

# a sum that does not wrap is exact
def nw.go(c: Bool, +V: Nat, +A0: Nat, +B0: Nat, +W: Nat, +hW: {W == PH.H.W(32n) : Nat},
  e: {Nat.add(V, N.D(32n, PH.H.bn(c))) == Nat.add(A0, B0) : Nat}, h: N.Le(A0, V), hB: N.Le(1n+B0, W)) -> {V == Nat.add(A0, B0) : Nat}:
  match c:
    case False{}:
      Equal.trans(Nat, V, Nat.add(V, 0n), Nat.add(A0, B0), Equal.sym(Nat, Nat.add(V, 0n), V, N.add_zero(V)),
        (%Equal.sym(Nat, N.D(32n, 0n), 0n, {==}) : {Nat.add(V, _) == Nat.add(A0, B0) : Nat}; e))
    case True{}:
      +e2 = Equal.trans(Nat, Nat.add(V, W), Nat.add(V, N.D(32n, PH.H.bn(True{}))), Nat.add(A0, B0),
        Equal.cong(Nat, Nat, z => Nat.add(V, z), W, N.D(32n, PH.H.bn(True{})), Equal.trans(Nat, W, PH.H.W(32n), N.D(32n, PH.H.bn(True{})), hW, Z.w.d(32n))), e)
      +l1 = N.le_rw_r(Nat.add(A0, W), Nat.add(V, W), Nat.add(A0, B0), e2, N.add_mono(A0, V, W, W, h, N.le_refl(W)))
      +l2 = PH.H.le_sub_add(A0, W, Nat.add(A0, B0), l1)
      +l3 = {(%Equal.trans(Nat, Nat.sub(Nat.add(A0, B0), A0), Nat.sub(Nat.add(B0, A0), A0), B0,
          Equal.cong(Nat, Nat, z => Nat.sub(z, A0), Nat.add(A0, B0), Nat.add(B0, A0), Z.add.comm(A0, B0)), DV.add.sub.r(B0, A0)) : N.Le(W, _); l2) : N.Le(W, B0)}
      Empty.absurd({V == Nat.add(A0, B0) : Nat}, N.not_succ_le(B0, N.le_trans(1n+B0, W, B0, hB, l3)))

def nowrap(+x: U32, +y: U32, +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, e: {U32.is_lt(U32.add(x, y), x) == False{} : Bool}) ->
  {U32.to_nat(U32.add(x, y)) == Nat.add(U32.to_nat(x), U32.to_nat(y)) : Nat}:
  match x y:
    case U32{+xw} U32{+yw}:
      +V = Word.to_nat(32n, Word.add(32n, xw, yw))
      nw.go(PH.H.cout(32n, xw, yw, False{}), V, Word.to_nat(32n, xw), Word.to_nat(32n, yw), W, hW, PH.H.adc(32n, xw, yw, False{}),
        nlt.to(U32{Word.add(32n, xw, yw)}, U32{xw}, e), Z.u32.w(U32{yw}, W, hW))

# The lengths
# -----------

def enc.from(-X: Data, xs: List<&2, X>) -> {Cr.Wasm.encode.len(X, xs) == U32.from_nat(List.length(&2, X, xs)) : U32}:
  match xs:
    case Nil{}:
      {==}
    case Con{_, rest}:
      Equal.cong(U32, U32, z => U32.inc(z), Cr.Wasm.encode.len(X, rest), U32.from_nat(List.length(&2, X, rest)), enc.from(X, rest))

def L32.T(xs: List<&2, Word(8n)>, +n: U32, +v: U32) -> Data:
  S.P2({v == Z.incn(List.length(&2, Word(8n), xs), n) : U32}, {U32.to_nat(v) == Nat.add(List.length(&2, Word(8n), xs), U32.to_nat(n)) : Nat})

def L32.fin(+x: Word(8n), +rest: List<&2, Word(8n)>, +n: U32, +v: U32, +W: Nat, +hW: {W == PH.H.W(32n) : Nat},
  eb: {U32.is_eq(n, 4294967295) == False{} : Bool}, pr: L32.T(rest, U32.inc(n), v)) -> L32.T(Con{x, rest}, n, v):
  (+e1, +e2) = pr
  +q = List.length(&2, Word(8n), rest)
  (e1, Equal.trans(Nat, U32.to_nat(v), Nat.add(q, U32.to_nat(U32.inc(n))), 1n+Nat.add(q, U32.to_nat(n)), e2,
    Equal.trans(Nat, Nat.add(q, U32.to_nat(U32.inc(n))), Nat.add(q, 1n+U32.to_nat(n)), 1n+Nat.add(q, U32.to_nat(n)),
      Equal.cong(Nat, Nat, z => Nat.add(q, z), U32.to_nat(U32.inc(n)), 1n+U32.to_nat(n), inc.ne1(n, W, hW, eb)),
      N.add_succ_r(q, U32.to_nat(n)))))

def L32.if(b: Bool, +x: Word(8n), +n: U32, +rest: List<&2, Word(8n)>, +v: U32, +W: Nat, +hW: {W == PH.H.W(32n) : Nat},
  eb: {U32.is_eq(n, 4294967295) == b : Bool},
  e: {Wa.Wasm.length32.if(b, u => Wa.Wasm.length32.go(rest, U32.inc(n))) == Some{v} : Maybe<&2, U32>},
  ih: {Wa.Wasm.length32.go(rest, U32.inc(n)) == Some{v} : Maybe<&2, U32>} -> L32.T(rest, U32.inc(n), v)) -> L32.T(Con{x, rest}, n, v):
  match b:
    case True{}:
      Empty.absurd(L32.T(Con{x, rest}, n, v), Q.none.some(v, e))
    case False{}:
      L32.fin(x, rest, n, v, W, hW, eb, ih(e))

# the length that length32 counts from n
def L32.go(xs: List<&2, Word(8n)>, +n: U32, +v: U32, +W: Nat, +hW: {W == PH.H.W(32n) : Nat},
  e: {Wa.Wasm.length32.go(xs, n) == Some{v} : Maybe<&2, U32>}) -> L32.T(xs, n, v):
  match xs:
    case Nil{}:
      +ev = Equal.sym(U32, n, v, Q.some.inj(n, v, e))
      (ev, Equal.cong(U32, Nat, z => U32.to_nat(z), v, n, ev))
    case Con{+x, +rest}:
      L32.if(U32.is_eq(n, 4294967295), x, n, rest, v, W, hW, {==}, e, y => L32.go(rest, U32.inc(n), v, W, hW, y))

# The host's run (H1, H2)
# -----------------------
#
# A program prog of regs registers whose code the simulation covers (ok:
# its registers and fields; hR, hd: its locals and labels have numbers),
# on an engine of m pages that grants each grow: when Cir gives a result,
# the host gives it too, with the fuel of alloc (41) and of run. The
# machine's program is one (mach.all).

# Outcomes

# a result
def is.res(x: Wa.Wasm.Outcome) -> Data:
  match x:
    case Wa.Wasm.Outcome.result{_}:
      Unit
    case Wa.Wasm.Outcome.out_of_memory{}:
      Empty
    case Wa.Wasm.Outcome.no_result{}:
      Empty
    case Wa.Wasm.Outcome.unsupported{}:
      Empty
    case Wa.Wasm.Outcome.trap{}:
      Empty
    case Wa.Wasm.Outcome.not_done{}:
      Empty

# an outcome equal to a result is one
def res.is(x: Wa.Wasm.Outcome, -o: List<&2, Word(8n)>, e: {x == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome}) -> is.res(x):
  %Equal.sym(Wa.Wasm.Outcome, x, Wa.Wasm.Outcome.result{o}, e) : is.res(_)
  Unit{}

# Numbers of the host

# (c + N) - j >= N, for j <= c
def sub.ge(c: Nat, +N0: Nat, j: Nat, h: N.Le(j, c)) -> N.Le(N0, Nat.sub(Nat.add(c, N0), j)):
  match c j:
    case _ 0n:
      N.le_rw_r(N0, Nat.add(c, N0), Nat.sub(Nat.add(c, N0), 0n), Equal.sym(Nat, Nat.sub(Nat.add(c, N0), 0n), Nat.add(c, N0), Q.sub0(Nat.add(c, N0))),
        N.le_add_l(c, N0))
    case 0n 1n+q:
      Empty.absurd(N.Le(N0, Nat.sub(Nat.add(0n, N0), 1n+q)), h)
    case 1n+(+d) 1n+(+q):
      sub.ge(d, N0, q, h)

# x <= c, where 2^32 - 1 > c: x is not 2^32 - 1
def ne.max(+x: U32, +c: U32, h: {U32.is_le(x, c) == True{} : Bool}, hc: {U32.is_le(4294967295, c) == False{} : Bool}) ->
  {U32.is_eq(x, 4294967295) == False{} : Bool}:
  Y.U32.ne(x, 4294967295, ex => N.false_ne_true(Equal.trans(Bool, False{}, U32.is_le(4294967295, c), True{},
    Equal.sym(Bool, U32.is_le(4294967295, c), False{}, hc),
    {(%ex : {U32.is_le(_, c) == True{} : Bool}; h) : {U32.is_le(4294967295, c) == True{} : Bool}})))

# E <= 2^32 - 16 = 20P, when E > 2^32 - 16 is false
def e20.of(+E: U32, -P: Nat, hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  c2: {U32.is_gt(E, 4294967280) == False{} : Bool}) -> N.Le(U32.to_nat(E), PH.H.t20(P)):
  +fw = PH.H.fwc(32n, 4n)
  +c2w = Equal.trans(Bool, U32.is_gt(E, U32{fw}), U32.is_gt(E, 4294967280), False{},
    Equal.cong(U32, Bool, z => U32.is_gt(E, z), U32{fw}, 4294967280, Equal.sym(U32, 4294967280, U32{fw}, PH.H.lit_fw())), c2)
  PH.H.cancel(U32.to_nat(E), U32.to_nat(U32{fw}), Word.to_nat(32n, fw), PH.H.W(4n), PH.H.t20(P), PH.H.W(32n), N.u32_to_nat(fw),
    PH.H.fwc_val(32n, 4n, Unit{}), hP, ngt.to(E, U32{fw}, c2w))

# p <= m and p <= 2^16: p is at most the limit, min(m, 2^16)
def le.min.if(c: Bool, +p: U32, +m: U32, h1: {U32.is_le(p, m) == True{} : Bool}, h2: {U32.is_le(p, 65536) == True{} : Bool}) ->
  {U32.is_le(p, Wa.Wasm.min.if(c, m, 65536)) == True{} : Bool}:
  match c:
    case True{}:
      h1
    case False{}:
      h2

def le.min(+p: U32, +m: U32, h1: {U32.is_le(p, m) == True{} : Bool}, h2: {U32.is_le(p, 65536) == True{} : Bool}) ->
  {U32.is_le(p, Wa.Wasm.min(m, 65536)) == True{} : Bool}:
  le.min.if(U32.is_le(m, 65536), p, m, h1, h2)

# the limit, min(m, 2^16), is at most G = 2^16 (kept a variable)
def lim.le.if(c: Bool, +m: U32, +lim: U32, el: {Wa.Wasm.min.if(c, m, 65536) == lim : U32}, +G: Nat, +eG: {U32.to_nat(65536) == G : Nat},
  e: {U32.is_le(m, 65536) == c : Bool}) -> N.Le(U32.to_nat(lim), G):
  match c:
    case True{}:
      %el : N.Le(U32.to_nat(_), G)
      N.le_rw_r(U32.to_nat(m), U32.to_nat(65536), G, eG, Z.le.of(m, 65536, e))
    case False{}:
      # in the syntax of the rewrite, so that no 2^16 is compared with another
      %el : N.Le(U32.to_nat(_), G)
      N.le_rw_r(U32.to_nat(Wa.Wasm.min.if(False{}, m, 65536)), U32.to_nat(65536), G, eG, N.le_refl(U32.to_nat(65536)))

def lim.le(+m: U32, +G: Nat, +eG: {U32.to_nat(65536) == G : Nat}) -> N.Le(U32.to_nat(Wa.Wasm.min(m, 65536)), G):
  lim.le.if(U32.is_le(m, 65536), m, Wa.Wasm.min(m, 65536), {==}, G, eG, {==})

# 2^16 × 2^16 is W = 2^32
def gw(+W: Nat, +hW: {W == PH.H.W(32n) : Nat}) -> {N.D(16n, N.D(16n, 1n)) == W : Nat}:
  Equal.trans(Nat, N.D(16n, N.D(16n, 1n)), N.D(32n, 1n), W, N.D_add(16n, 16n, 32n, 1n, {==}), Z.d32.w(W, hW))

# a memory of at most 2^16 = G pages has at most 2^32 = W bytes
def pb.w(+p: U32, +G: Nat, +W: Nat, +hG: {N.D(16n, G) == W : Nat}, +eG: {U32.to_nat(65536) == G : Nat},
  h: {U32.is_le(p, 65536) == True{} : Bool}) -> N.Le(Q.PB(p), W):
  N.le_rw_r(Q.PB(p), N.D(16n, G), W, hG,
    M.D_mono(16n, U32.to_nat(p), G, N.le_rw_r(U32.to_nat(p), U32.to_nat(65536), G, eG, Z.le.of(p, 65536, h))))

# a <= b gives 1 + a <= 1 + b
def le.ss(+a: Nat, +b: Nat, h: N.Le(a, b)) -> N.Le(1n+a, 1n+b):
  h

# w bytes from x >= 1 fit in the memory of p pages, when they end within it
# (w may be 0)
def fits.go(wn: Nat, +p: U32, +x: U32, +w: U32, +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +ew: {U32.to_nat(w) == wn : Nat},
  +hx: N.Le(1n, U32.to_nat(x)), +h: N.Le(Nat.add(U32.to_nat(x), U32.to_nat(w)), Q.PB(p)), +hb: N.Le(Q.PB(p), W)) ->
  {Wa.Wasm.fits(p, x, w) == True{} : Bool}:
  match wn:
    case 0n:
      +e0 = Equal.trans(U32, w, U32.from_nat(U32.to_nat(w)), 0, Equal.sym(U32, U32.from_nat(U32.to_nat(w)), w, Z.from.to(w)),
        Equal.cong(Nat, U32, z => U32.from_nat(z), U32.to_nat(w), 0n, ew))
      %Equal.sym(U32, w, 0, e0) : {Wa.Wasm.fits(p, x, _) == True{} : Bool}
      F.fits0(p, x, hx, N.le_trans(U32.to_nat(x), Nat.add(U32.to_nat(x), U32.to_nat(w)), Q.PB(p), N.le_add_r(U32.to_nat(x), U32.to_nat(w)), h))
    case 1n+(+q):
      F.fits.ok(p, x, w, W, hW, {(%Equal.sym(Nat, U32.to_nat(w), 1n+q, ew) : N.Le(1n, _); N.le_zero(q)) : N.Le(1n, U32.to_nat(w))}, h, hb)

def fits.gen(+p: U32, +x: U32, +w: U32, +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hx: N.Le(1n, U32.to_nat(x)),
  +h: N.Le(Nat.add(U32.to_nat(x), U32.to_nat(w)), Q.PB(p)), +hb: N.Le(Q.PB(p), W)) -> {Wa.Wasm.fits(p, x, w) == True{} : Bool}:
  fits.go(U32.to_nat(w), p, x, w, W, hW, {==}, hx, h, hb)

# The data segment (H1)

# 20 bytes for each cell
def bytes.len(cs: List<&2, Cr.Cir.Cell>) -> {List.length(&2, Word(8n), Cr.Cir.bytes(cs)) == PH.H.t20(List.length(&2, Cr.Cir.Cell, cs)) : Nat}:
  match cs:
    case Nil{}:
      {==}
    case Con{Cr.Cir.Cell{a, b, c, d, e}, +rest}:
      Equal.cong(Nat, Nat, z => 20n+z, List.length(&2, Word(8n), Cr.Cir.bytes(rest)), PH.H.t20(List.length(&2, Cr.Cir.Cell, rest)), bytes.len(rest))

# 2 + q + n <= W = 1 + T, for T = 2^32 - 1 (kept a variable): n is not T
def ne.top(+n: U32, +q: Nat, +T: Nat, +eT: {U32.to_nat(4294967295) == T : Nat}, +W: Nat, +eW: {1n+T == W : Nat},
  h: N.Le(2n+Nat.add(q, U32.to_nat(n)), W)) -> {U32.is_eq(n, 4294967295) == False{} : Bool}:
  Y.U32.ne(n, 4294967295, en =>
    N.not_succ_le(T, N.le_trans(1n+T, 1n+Nat.add(q, T), T, N.le_add_l(q, T),
      N.le_rw_r(2n+Nat.add(q, T), W, 1n+T, Equal.sym(Nat, 1n+T, W, eW),
        N.le_rw_l(2n+Nat.add(q, U32.to_nat(4294967295)), 2n+Nat.add(q, T), W,
          Equal.cong(Nat, Nat, z => 2n+Nat.add(q, z), U32.to_nat(4294967295), T, eT),
          {(%en : N.Le(2n+Nat.add(q, U32.to_nat(_)), W); h) : N.Le(2n+Nat.add(q, U32.to_nat(4294967295)), W)})))))

# the step of L32.ex: one byte more, counted from n + 1
def L32.cons(+x: Word(8n), +rest: List<&2, Word(8n)>, +n: U32, ne: {U32.is_eq(n, 4294967295) == False{} : Bool},
  ea: {Nat.add(List.length(&2, Word(8n), rest), U32.to_nat(U32.inc(n))) == 1n+Nat.add(List.length(&2, Word(8n), rest), U32.to_nat(n)) : Nat},
  r: Q.EXU(v => S.P2({Wa.Wasm.length32.go(rest, U32.inc(n)) == Some{v} : Maybe<&2, U32>},
    {U32.to_nat(v) == Nat.add(List.length(&2, Word(8n), rest), U32.to_nat(U32.inc(n))) : Nat}))) ->
  Q.EXU(v => S.P2({Wa.Wasm.length32.go(Con{x, rest}, n) == Some{v} : Maybe<&2, U32>},
    {U32.to_nat(v) == Nat.add(List.length(&2, Word(8n), Con{x, rest}), U32.to_nat(n)) : Nat})):
  (+v, r1) = r
  (ev, nv) = r1
  (v, ({(%Equal.sym(Bool, U32.is_eq(n, 4294967295), False{}, ne) :
      {Wa.Wasm.length32.if(_, u => Wa.Wasm.length32.go(rest, U32.inc(n))) == Some{v} : Maybe<&2, U32>}; ev) :
      {Wa.Wasm.length32.go(Con{x, rest}, n) == Some{v} : Maybe<&2, U32>}},
    Equal.trans(Nat, U32.to_nat(v), Nat.add(List.length(&2, Word(8n), rest), U32.to_nat(U32.inc(n))),
      1n+Nat.add(List.length(&2, Word(8n), rest), U32.to_nat(n)), nv, ea)))

# length32 counts the bytes from n, when they end below 2^32 - 1
def L32.ex(xs: List<&2, Word(8n)>, +n: U32, +W: Nat, +hW: {W == PH.H.W(32n) : Nat},
  +h: N.Le(1n+Nat.add(List.length(&2, Word(8n), xs), U32.to_nat(n)), W)) ->
  Q.EXU(v => S.P2({Wa.Wasm.length32.go(xs, n) == Some{v} : Maybe<&2, U32>}, {U32.to_nat(v) == Nat.add(List.length(&2, Word(8n), xs), U32.to_nat(n)) : Nat})):
  match xs:
    case Nil{}:
      (n, ({==}, {==}))
    case Con{+x, +rest}:
      +q = List.length(&2, Word(8n), rest)
      +N0 = U32.to_nat(n)
      +ne = ne.top(n, q, U32.to_nat(4294967295), {==}, W, max.nat(W, hW), h)
      +ei = inc.ne1(n, W, hW, ne)
      +ea = Equal.trans(Nat, Nat.add(q, U32.to_nat(U32.inc(n))), Nat.add(q, 1n+N0), 1n+Nat.add(q, N0),
        Equal.cong(Nat, Nat, z => Nat.add(q, z), U32.to_nat(U32.inc(n)), 1n+N0, ei), N.add_succ_r(q, N0))
      L32.cons(x, rest, n, ne, ea, L32.ex(rest, U32.inc(n), W, hW, N.le_rw_l(2n+Nat.add(q, N0), 1n+Nat.add(q, U32.to_nat(U32.inc(n))), W,
        Equal.cong(Nat, Nat, z => 1n+z, 1n+Nat.add(q, N0), Nat.add(q, U32.to_nat(U32.inc(n))), Equal.sym(Nat, Nat.add(q, U32.to_nat(U32.inc(n))), 1n+Nat.add(q, N0), ea)), h)))

# the cells' bytes, from byte 20, fit in the memory of the module's minimum,
# Cir.pages(a) pages for a = 20 (k + 1), by the length that length32 gives
def seg.go(+cells: List<&2, Cr.Cir.Cell>, +P: Nat, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +G: Nat, +hG: {N.D(16n, G) == W : Nat}, +eG: {U32.to_nat(65536) == G : Nat}, +eA: {U32.to_nat(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))) == PH.H.t20(1n+List.length(&2, Cr.Cir.Cell, cells)) : Nat},
  +eBz: {Nat.add(List.length(&2, Word(8n), Cr.Cir.bytes(cells)), U32.to_nat(0)) == PH.H.t20(List.length(&2, Cr.Cir.Cell, cells)) : Nat},
  r: Q.EXU(v => S.P2({Wa.Wasm.length32.go(Cr.Cir.bytes(cells), 0) == Some{v} : Maybe<&2, U32>},
    {U32.to_nat(v) == Nat.add(List.length(&2, Word(8n), Cr.Cir.bytes(cells)), U32.to_nat(0)) : Nat}))) ->
  {Wa.Wasm.fits.len(Cr.Cir.pages(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), 20, Wa.Wasm.length32(Cr.Cir.bytes(cells))) == True{} : Bool}:
  (+v, l1) = r
  (ev, nv) = l1
  +K = List.length(&2, Cr.Cir.Cell, cells)
  +a = Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))
  +p0 = Cr.Cir.pages(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells)))
  +B = Cr.Cir.bytes(cells)
  +LB = List.length(&2, Word(8n), B)
  # 20 + 20K = a <= 2^16 p0
  +h1a = N.le_rw_r(1n, PH.H.t20(1n+K), U32.to_nat(a), Equal.sym(Nat, U32.to_nat(a), PH.H.t20(1n+K), eA), Unit{})
  +ha = N.le_rw_l(1n+U32.to_nat(U32.sub(a, 1)), U32.to_nat(a), Q.PB(p0), Z.dec.nat(a, h1a),
    A.room.of(U32.sub(a, 1), p0, W, hW, F.w16(P, hP, W, hW), N.le_refl(U32.to_nat(p0))))
  +e20v = Equal.trans(Nat, Nat.add(U32.to_nat(20), U32.to_nat(v)), Nat.add(U32.to_nat(20), PH.H.t20(K)), U32.to_nat(a),
    Equal.cong(Nat, Nat, z => Nat.add(U32.to_nat(20), z), U32.to_nat(v), PH.H.t20(K), Equal.trans(Nat, U32.to_nat(v), Nat.add(LB, U32.to_nat(0)), PH.H.t20(K), nv, eBz)),
    Equal.sym(Nat, U32.to_nat(a), PH.H.t20(1n+K), eA))
  %Equal.sym(Maybe<&2, U32>, Wa.Wasm.length32(B), Some{v}, ev) : {Wa.Wasm.fits.len(p0, 20, _) == True{} : Bool}
  fits.gen(p0, 20, v, W, hW, Unit{}, N.le_rw_l(U32.to_nat(a), Nat.add(U32.to_nat(20), U32.to_nat(v)), Q.PB(p0), Equal.sym(Nat, Nat.add(U32.to_nat(20), U32.to_nat(v)), U32.to_nat(a), e20v), ha),
    pb.w(p0, G, W, hG, eG, V.pages.le(U32.sub(a, 1))))

# the data segment fits (H1)
def seg.fits(+cells: List<&2, Cr.Cir.Cell>, +P: Nat, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +G: Nat, +hG: {N.D(16n, G) == W : Nat}, +eG: {U32.to_nat(65536) == G : Nat}, +hK1: N.Le(1n+List.length(&2, Cr.Cir.Cell, cells), P), +eA: {U32.to_nat(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))) == PH.H.t20(1n+List.length(&2, Cr.Cir.Cell, cells)) : Nat}) ->
  {Wa.Wasm.fits.len(Cr.Cir.pages(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), 20, Wa.Wasm.length32(Cr.Cir.bytes(cells))) == True{} : Bool}:
  +K = List.length(&2, Cr.Cir.Cell, cells)
  +LB = List.length(&2, Word(8n), Cr.Cir.bytes(cells))
  +eBz = Equal.trans(Nat, Nat.add(LB, U32.to_nat(0)), LB, PH.H.t20(K), N.add_zero(LB), bytes.len(cells))
  +hBn = N.le_rw_r(1n+PH.H.t20(K), PH.H.W(32n), W, Equal.sym(Nat, W, PH.H.W(32n), hW), PH.H.t20_bound(32n, K, P, hP, N.weaken(K, P, hK1)))
  seg.go(cells, P, hP, W, hW, G, hG, eG, eA, eBz, L32.ex(Cr.Cir.bytes(cells), 0, W, hW, N.le_rw_l(1n+PH.H.t20(K), 1n+Nat.add(LB, U32.to_nat(0)), W,
    Equal.cong(Nat, Nat, z => 1n+z, PH.H.t20(K), Nat.add(LB, U32.to_nat(0)), Equal.sym(Nat, Nat.add(LB, U32.to_nat(0)), PH.H.t20(K), eBz)), hBn)))

# the module of Cir.module exports what the host uses
def is.host(+prog: Cr.Cir.Stmt, +regs: Nat, +cells: List<&2, Cr.Cir.Cell>, +mem: Wa.Wasm.Memory) ->
  {Wa.Wasm.run.is_host(Wa.Wasm.Instance{Cr.Cir.module(prog, regs, cells), mem}) == True{} : Bool}:
  {==}

# The call of run (H2)

# an outcome that a completed host call can give here
def is.ro(x: Wa.Wasm.Outcome) -> Data:
  match x:
    case Wa.Wasm.Outcome.result{_}:
      Unit
    case Wa.Wasm.Outcome.out_of_memory{}:
      Unit
    case _:
      Empty

# an outcome of the other forms (hy) is not one of these
def ro.bad(+x: Wa.Wasm.Outcome, +y: Wa.Wasm.Outcome, hx: is.ro(x), hy: is.ro(y) -> Empty, e: {y == x : Wa.Wasm.Outcome}) -> Empty:
  hy((%Equal.sym(Wa.Wasm.Outcome, y, x, e) : is.ro(_); hx))

# run's run from its frame fr in the memory mem: N2 steps end with a status
# s0, of a memory that the host reads as x
def RS(+x: Wa.Wasm.Outcome, +fr: Wa.Wasm.Frame, +mem: Wa.Wasm.Memory) -> Data:
  S.EX(N2 => T.EXM(mm => Q.EXU(s0 => S.P2({PH.H.steps(N2, Wa.Wasm.Step.next{fr, mem}) == Wa.Wasm.Step.done{[s0], mm} : Wa.Wasm.Step},
    {Wa.Wasm.run.status(U32.is_eq(s0, 0), U32.is_eq(s0, 1), U32.is_eq(s0, 2), mm) == x : Wa.Wasm.Outcome}))))

# an engine refusal ends run with 1, and k is the answer that refused it
def OMS(+gs: List<&2, Bool>, +fr: Wa.Wasm.Frame, +mem: Wa.Wasm.Memory) -> Data:
  S.EX(N2 => T.EXM(mm => S.EX(k => S.P2({List.get(&2, Bool, gs, k) == Some{False{}} : Maybe<&2, Bool>},
    {PH.H.steps(N2, Wa.Wasm.Step.next{fr, mem}) == Wa.Wasm.Step.done{[1], mm} : Wa.Wasm.Step}))))

# either the host's exact outcome, or out of memory after a refused grow
def RSO(+x: Wa.Wasm.Outcome, +gs: List<&2, Bool>, +fr: Wa.Wasm.Frame, +mem: Wa.Wasm.Memory) -> Data:
  S.OR(RS(x, fr, mem), OMS(gs, fr, mem))

# the host's outcome, with the refusing answer retained
def HO(+x: Wa.Wasm.Outcome, +gs: List<&2, Bool>, +y: Wa.Wasm.Outcome) -> Data:
  S.OR({y == x : Wa.Wasm.Outcome}, S.EX(k => S.P2({List.get(&2, Bool, gs, k) == Some{False{}} : Maybe<&2, Bool>},
    {y == Wa.Wasm.Outcome.out_of_memory{} : Wa.Wasm.Outcome})))

# no answer can refuse a grow
def ho.empty(+x: Wa.Wasm.Outcome, +y: Wa.Wasm.Outcome, q: HO(x, [], y)) -> {y == x : Wa.Wasm.Outcome}:
  match q:
    case Inl{e}:
      e
    case Inr{r}:
      (+k, p) = r
      (hg, eq) = p
      Empty.absurd({y == x : Wa.Wasm.Outcome}, S.none.someb(False{}, hg))

# drop the witness of a refusal
def ho.or(+x: Wa.Wasm.Outcome, +gs: List<&2, Bool>, +y: Wa.Wasm.Outcome, q: HO(x, gs, y)) ->
  Or({y == x : Wa.Wasm.Outcome}, {y == Wa.Wasm.Outcome.out_of_memory{} : Wa.Wasm.Outcome}):
  match q:
    case Inl{e}:
      Inl{e}
    case Inr{r}:
      (+k, p) = r
      (hg, eq) = p
      Inr{eq}

# the host's outcome is out of memory, when Cir's is
def ho.oom(+gs: List<&2, Bool>, +y: Wa.Wasm.Outcome, q: HO(Wa.Wasm.Outcome.out_of_memory{}, gs, y)) ->
  {y == Wa.Wasm.Outcome.out_of_memory{} : Wa.Wasm.Outcome}:
  match q:
    case Inl{e}:
      e
    case Inr{r}:
      (+k, p) = r
      (hg, eq) = p
      eq

# run's run, by how Cir's program ends (oc): a result only at a halt, whose
# status the host reads as Cir.ended says (HaltOK); an engine refusal ends at 1
def rs.out(oc: Cr.Cir.Out, +fu: Nat, +x: Wa.Wasm.Outcome, +X: List<&2, Wa.Wasm.Instr>, +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32,
  +rg: List<&2, U32>, +nx: U32, +on: U32, +pg: U32, +lm: U32, +gs: List<&2, Bool>, +m: Wa.Wasm.Bytes, +P: Nat, +G: Nat,
  +fr: Wa.Wasm.Frame, +mem: Wa.Wasm.Memory, +N1: Nat, +hx: is.ro(x),
  pre: {PH.H.steps(N1, Wa.Wasm.Step.next{fr, mem}) == T.Cf(X, [T.RL()], a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m) : Wa.Wasm.Step},
  sp: T.GPost(oc, fu, X, [T.RL()], [], [T.RL()], a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m, P, G),
  e: {Cr.Cir.ended(oc) == x : Wa.Wasm.Outcome}) -> RSO(x, gs, fr, mem):
  match oc:
    case Cr.Cir.Out.next{_}:
      Empty.absurd(RSO(x, gs, fr, mem), ro.bad(x, Wa.Wasm.Outcome.no_result{}, hx, z => z, e))
    case Cr.Cir.Out.halt{+s0, st2}:
      match st2:
        case Cr.Cir.State{+rg2, +cl2, +nx2, +fi2, +im2, +pg2, +lm2, +inp2, +ou2, +on2}:
          match sp:
            case Inl{q}:
              (+k, r0) = q
              (+N2, p1) = r0
              (+mm, p2) = p1
              (eq, ok) = p2
              Inl{(Nat.add(N1, N2), (mm, (s0, (S.steps.then(N1, N2, Wa.Wasm.Step.next{fr, mem}, T.Cf(X, [T.RL()], a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m),
                Wa.Wasm.Step.done{[s0], mm}, pre, eq),
                Equal.trans(Wa.Wasm.Outcome, Wa.Wasm.run.status(U32.is_eq(s0, 0), U32.is_eq(s0, 1), U32.is_eq(s0, 2), mm),
                  Cr.Cir.ended.halt(U32.is_eq(s0, 0), U32.is_eq(s0, 1), U32.is_eq(s0, 2), Wa.Wasm.fits(pg2, Cr.Cir.at(nx2), on2), ou2), x, ok, e)))))}
            case Inr{q}:
              (+N2, p1) = q
              (+mm, p2) = p1
              (+k, p3) = p2
              (hg, eq) = p3
              Inr{(Nat.add(N1, N2), (mm, (k, (hg, S.steps.then(N1, N2, Wa.Wasm.Step.next{fr, mem},
                T.Cf(X, [T.RL()], a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m), Wa.Wasm.Step.done{[1], mm}, pre, eq)))))}
    case Cr.Cir.Out.out_of_memory{}:
      match sp:
        case Inl{q}:
          (+k, r0) = q
          (+N2, p1) = r0
          (+mm, eq) = p1
          Inl{(Nat.add(N1, N2), (mm, (1, (S.steps.then(N1, N2, Wa.Wasm.Step.next{fr, mem},
            T.Cf(X, [T.RL()], a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m), Wa.Wasm.Step.done{[1], mm}, pre, eq), e))))}
        case Inr{q}:
          (+N2, p1) = q
          (+mm, p2) = p1
          (+k, p3) = p2
          (hg, eq) = p3
          Inr{(Nat.add(N1, N2), (mm, (k, (hg, S.steps.then(N1, N2, Wa.Wasm.Step.next{fr, mem},
            T.Cf(X, [T.RL()], a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m), Wa.Wasm.Step.done{[1], mm}, pre, eq)))))}
    case Cr.Cir.Out.trap{}:
      Empty.absurd(RSO(x, gs, fr, mem), ro.bad(x, Wa.Wasm.Outcome.trap{}, hx, z => z, e))
    case Cr.Cir.Out.not_done{}:
      Empty.absurd(RSO(x, gs, fr, mem), ro.bad(x, Wa.Wasm.Outcome.not_done{}, hx, z => z, e))

# the call of run gives the status s0 and the memory mm (c): the host reads
# what the status gives (ok)
def ran.go(+x: Wa.Wasm.Outcome, +fr: Wa.Wasm.Frame, +mem: Wa.Wasm.Memory, +X: Wa.Wasm.Module, +F: Nat, +N2: Nat, +mm: Wa.Wasm.Memory, +s0: U32,
  ok: {Wa.Wasm.run.status(U32.is_eq(s0, 0), U32.is_eq(s0, 1), U32.is_eq(s0, 2), mm) == x : Wa.Wasm.Outcome},
  c: S.EX(j => S.P2({Wa.Wasm.call.go(F, PH.H.TS(), fr, mem) == Wa.Wasm.Call.done{[s0], mm, j} : Wa.Wasm.Call}, N.Le(j, N2)))) ->
  {Wa.Wasm.run.ran(Wa.Wasm.invoked(Wa.Wasm.call.go(F, PH.H.TS(), fr, mem), X)) == x : Wa.Wasm.Outcome}:
  (+j, r1) = c
  (ec, hj) = r1
  %Equal.sym(Wa.Wasm.Call, Wa.Wasm.call.go(F, PH.H.TS(), fr, mem), Wa.Wasm.Call.done{[s0], mm, j}, ec) :
    {Wa.Wasm.run.ran(Wa.Wasm.invoked(_, X)) == x : Wa.Wasm.Outcome}
  ok

# the call of run, from a run that ends at the status s0 in N2 steps, with
# fuel F >= N2 (S.run.call)
def ran.of(+x: Wa.Wasm.Outcome, +fr: Wa.Wasm.Frame, +mem: Wa.Wasm.Memory, +X: Wa.Wasm.Module, +F: Nat, +N2: Nat, +mm: Wa.Wasm.Memory, +s0: U32,
  eq: {PH.H.steps(N2, Wa.Wasm.Step.next{fr, mem}) == Wa.Wasm.Step.done{[s0], mm} : Wa.Wasm.Step},
  ok: {Wa.Wasm.run.status(U32.is_eq(s0, 0), U32.is_eq(s0, 1), U32.is_eq(s0, 2), mm) == x : Wa.Wasm.Outcome},
  hF: N.Le(N2, F)) -> {Wa.Wasm.run.ran(Wa.Wasm.invoked(Wa.Wasm.call.go(F, PH.H.TS(), fr, mem), X)) == x : Wa.Wasm.Outcome}:
  ran.go(x, fr, mem, X, F, N2, mm, s0, ok, S.run.call(N2, F, fr, mem, [s0], mm, eq, hF))

# run's run of prog from the program's block, which run's start reaches
# (pre): the relation there (IN.inv0), then the program (T.sim.stmt)
def rs.pre(+n: Nat, +prog: Cr.Cir.Stmt, +regs: Nat, +cells: List<&2, Cr.Cir.Cell>, +i: List<&2, Word(8n)>, +len: U32, +p2: U32, +lim: U32,
  +x: Wa.Wasm.Outcome, +gs: List<&2, Bool>, +MX: U32, +MD: U32, +P: Nat, +G: Nat, +W: Nat, +hW: {W == PH.H.W(32n) : Nat},
  +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat}, +hG: {N.D(16n, G) == W : Nat},
  +eK: {U32.to_nat(Cr.Wasm.encode.len(Cr.Cir.Cell, cells)) == List.length(&2, Cr.Cir.Cell, cells) : Nat}, +hK: N.Le(2n+List.length(&2, Cr.Cir.Cell, cells), P), +hX0: N.Le(U32.to_nat(U32.inc(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), P),
  +eLn: {len == Cr.Wasm.encode.len(Word(8n), i) : U32},
  +eE: {U32.to_nat(U32.add(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells)), len)) == Nat.add(U32.to_nat(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), List.length(&2, Word(8n), i)) : Nat},
  +hEP: N.Le(Nat.add(U32.to_nat(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), List.length(&2, Word(8n), i)), PH.H.t20(P)), +hEB: N.Le(Nat.add(U32.to_nat(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), List.length(&2, Word(8n), i)), Q.PB(p2)),
  +hlm: N.Le(U32.to_nat(lim), G), +hpl: N.Le(U32.to_nat(p2), U32.to_nat(lim)),
  +ok: {V.ok.stmt(prog, regs) == True{} : Bool}, +hR: N.Le(8n+regs, U32.to_nat(MX)), +hd: N.Le(T.dep(prog), U32.to_nat(MD)), +hx: is.ro(x),
  e: {Cr.Cir.ended(Cr.Cir.exec(n, prog, Cr.Cir.State{List.replicate(U32, regs, 0), Cr.Cir.load(cells, 1, Cr.Cir.Cells.none{}),
    Cr.Cir.first(Cr.Wasm.encode.len(Cr.Cir.Cell, cells), U32.add(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells)), len)), Cr.Cir.first(Cr.Wasm.encode.len(Cr.Cir.Cell, cells), U32.add(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells)), len)), Cr.Wasm.encode.len(Cr.Cir.Cell, cells), p2, lim, i, Nil{}, 0})) == x : Wa.Wasm.Outcome},
  pre: PR.PRE(prog, regs, Cr.Wasm.encode.len(Cr.Cir.Cell, cells), Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells)), len, Wa.Wasm.Memory{p2, lim, gs, IN.B2(cells, i)}, Cr.Cir.first(Cr.Wasm.encode.len(Cr.Cir.Cell, cells), U32.add(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells)), len)), P)) ->
  RSO(x, gs, PR.pr.fr(prog, regs, Cr.Wasm.encode.len(Cr.Cir.Cell, cells), Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells)), len), Wa.Wasm.Memory{p2, lim, gs, IN.B2(cells, i)}):
  (pre1, pre2) = pre
  (+N1, eq1) = pre1
  (hEF0, hFP) = pre2
  +k = Cr.Wasm.encode.len(Cr.Cir.Cell, cells)
  +a = Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))
  +L = List.length(&2, Word(8n), i)
  +ad = U32.add(a, len)
  +fst = Cr.Cir.first(k, ad)
  +B2 = IN.B2(cells, i)
  +mm = {Wa.Wasm.Memory{p2, lim, gs, B2} : Wa.Wasm.Memory}
  +rg = List.replicate(U32, regs, 0)
  +cl = Cr.Cir.load(cells, 1, Cr.Cir.Cells.none{})
  +hEF = N.le_rw_l(U32.to_nat(ad), Nat.add(U32.to_nat(a), L), PH.H.t20(U32.to_nat(fst)), eE, hEF0)
  +hI = IN.inv0(cells, i, len, p2, lim, fst, P, G, hP, W, hW, eK, hK, eLn, hEP, hEB, hEF, hFP, hlm, hpl)
  +X = Cr.Cir.code.stmt(prog, 0n, [])
  +sp = T.sim.stmt(n, prog, rg, cl, fst, fst, k, p2, lim, i, [], 0, 0n, [], [T.RL()], {==}, regs, MX, hR, MD, P, G, a, len, fst, 0, ad, gs, B2, hI,
    W, hW, hP, hG, ok, hd)
  rs.out(Cr.Cir.exec(n, prog, Q.St(rg, cl, fst, fst, k, p2, lim, i, [], 0)), n, x, X, a, len, fst, 0, ad, rg, fst, 0, p2, lim, gs, B2, P, G,
    PR.pr.fr(prog, regs, k, a, len), mm, N1, hx, eq1, sp, e)

# run's run of prog, from the call's frame, with the input of len bytes at
# a in p2 pages: run's start (PR.pr.go), then the program's block (rs.pre)
def rs.run(+n: Nat, +prog: Cr.Cir.Stmt, +regs: Nat, +cells: List<&2, Cr.Cir.Cell>, +i: List<&2, Word(8n)>, +len: U32, +p2: U32, +lim: U32,
  +x: Wa.Wasm.Outcome, +gs: List<&2, Bool>, +MX: U32, +MD: U32, +P: Nat, +G: Nat, +W: Nat, +hW: {W == PH.H.W(32n) : Nat},
  +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat}, +hG: {N.D(16n, G) == W : Nat},
  +eK: {U32.to_nat(Cr.Wasm.encode.len(Cr.Cir.Cell, cells)) == List.length(&2, Cr.Cir.Cell, cells) : Nat}, +hK: N.Le(2n+List.length(&2, Cr.Cir.Cell, cells), P), +hX0: N.Le(U32.to_nat(U32.inc(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), P),
  +eLn: {len == Cr.Wasm.encode.len(Word(8n), i) : U32},
  +eE: {U32.to_nat(U32.add(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells)), len)) == Nat.add(U32.to_nat(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), List.length(&2, Word(8n), i)) : Nat},
  +hEP: N.Le(Nat.add(U32.to_nat(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), List.length(&2, Word(8n), i)), PH.H.t20(P)), +hEB: N.Le(Nat.add(U32.to_nat(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), List.length(&2, Word(8n), i)), Q.PB(p2)),
  +hlm: N.Le(U32.to_nat(lim), G), +hpl: N.Le(U32.to_nat(p2), U32.to_nat(lim)),
  +ok: {V.ok.stmt(prog, regs) == True{} : Bool}, +hR: N.Le(8n+regs, U32.to_nat(MX)), +hd: N.Le(T.dep(prog), U32.to_nat(MD)), +hx: is.ro(x),
  e: {Cr.Cir.ended(Cr.Cir.exec(n, prog, Cr.Cir.State{List.replicate(U32, regs, 0), Cr.Cir.load(cells, 1, Cr.Cir.Cells.none{}),
    Cr.Cir.first(Cr.Wasm.encode.len(Cr.Cir.Cell, cells), U32.add(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells)), len)), Cr.Cir.first(Cr.Wasm.encode.len(Cr.Cir.Cell, cells), U32.add(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells)), len)), Cr.Wasm.encode.len(Cr.Cir.Cell, cells), p2, lim, i, Nil{}, 0})) == x : Wa.Wasm.Outcome}) ->
  RSO(x, gs, PR.pr.fr(prog, regs, Cr.Wasm.encode.len(Cr.Cir.Cell, cells), Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells)), len), Wa.Wasm.Memory{p2, lim, gs, IN.B2(cells, i)}):
  +k = Cr.Wasm.encode.len(Cr.Cir.Cell, cells)
  +a = Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))
  +L = List.length(&2, Word(8n), i)
  +ad = U32.add(a, len)
  +hE = N.le_rw_l(Nat.add(U32.to_nat(a), L), U32.to_nat(ad), PH.H.t20(P), Equal.sym(Nat, U32.to_nat(ad), Nat.add(U32.to_nat(a), L), eE), hEP)
  rs.pre(n, prog, regs, cells, i, len, p2, lim, x, gs, MX, MD, P, G, W, hW, hP, hG, eK, hK, hX0, eLn, eE, hEP, hEB, hlm, hpl, ok, hR, hd, hx, e,
    PR.pr.go(prog, regs, k, a, len, Wa.Wasm.Memory{p2, lim, gs, IN.B2(cells, i)}, P, hP, W, hW, hX0, hE))


# The host's run (H2)

# the call of alloc gave a (c), and took the answers to g1, in the fuel 41 + N3, of
# which run's run takes N3 (eq3, ok3): the input fits (fin) at a, not -1 (ane)
def host.call(+prog: Cr.Cir.Stmt, +regs: Nat, +cells: List<&2, Cr.Cir.Cell>, +i: List<&2, Word(8n)>, +len: U32, +lim: U32,
  +x: Wa.Wasm.Outcome, +gs: List<&2, Bool>, +g1: List<&2, Bool>, +p2: U32, +N3: Nat, +mm: Wa.Wasm.Memory, +s0: U32,
  eq3: {PH.H.steps(N3, Wa.Wasm.Step.next{PR.pr.fr(prog, regs, Cr.Wasm.encode.len(Cr.Cir.Cell, cells), Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells)), len), Wa.Wasm.Memory{p2, lim, g1, IN.B2(cells, i)}}) ==
    Wa.Wasm.Step.done{[s0], mm} : Wa.Wasm.Step},
  ok3: {Wa.Wasm.run.status(U32.is_eq(s0, 0), U32.is_eq(s0, 1), U32.is_eq(s0, 2), mm) == x : Wa.Wasm.Outcome},
  ane: {U32.is_eq(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells)), 4294967295) == False{} : Bool}, fin: {Wa.Wasm.fits(p2, Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells)), len) == True{} : Bool},
  c: S.EX(j => S.P2({Wa.Wasm.call(Nat.add(41n, N3), PH.H.TS(), 1n, Cr.Cir.alloc(Cr.Wasm.encode.len(Cr.Cir.Cell, cells)), [len], Wa.Wasm.Memory{Cr.Cir.pages(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), lim, gs, IN.B0(cells)}) ==
    Wa.Wasm.Call.done{[AF.af.a(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))], Wa.Wasm.Memory{p2, lim, g1, IN.B0(cells)}, j} : Wa.Wasm.Call}, N.Le(j, 41n)))) ->
  {Wa.Wasm.run.alloced(Wa.Wasm.invoked(Wa.Wasm.call(Nat.add(41n, N3), PH.H.TS(), 1n, Cr.Cir.alloc(Cr.Wasm.encode.len(Cr.Cir.Cell, cells)), [len], Wa.Wasm.Memory{Cr.Cir.pages(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), lim, gs, IN.B0(cells)}),
    Cr.Cir.module(prog, regs, cells)), Nat.add(41n, N3), len, i) == x : Wa.Wasm.Outcome}:
  (+j, c1) = c
  (ec, hj) = c1
  +k = Cr.Wasm.encode.len(Cr.Cir.Cell, cells)
  +a = Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))
  +p0 = Cr.Cir.pages(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells)))
  +B0 = IN.B0(cells)
  +X = Cr.Cir.module(prog, regs, cells)
  +f = Nat.add(41n, N3)
  +F0 = Nat.sub(f, j)
  +ran = ran.of(x, PR.pr.fr(prog, regs, k, a, len), Wa.Wasm.Memory{p2, lim, g1, IN.B2(cells, i)}, X, F0, N3, mm, s0, eq3, ok3, sub.ge(41n, N3, j, hj))
  %Equal.sym(Wa.Wasm.Call, Wa.Wasm.call(f, PH.H.TS(), 1n, Cr.Cir.alloc(k), [len], Wa.Wasm.Memory{p0, lim, gs, B0}),
      Wa.Wasm.Call.done{[AF.af.a(k)], Wa.Wasm.Memory{p2, lim, g1, B0}, j}, ec) :
    {Wa.Wasm.run.alloced(Wa.Wasm.invoked(_, X), f, len, i) == x : Wa.Wasm.Outcome}
  %Equal.sym(Bool, U32.is_eq(a, 4294967295), False{}, ane) :
    {Wa.Wasm.run.alloced.if(_, F0, Wa.Wasm.Instance{X, Wa.Wasm.Memory{p2, lim, g1, B0}}, a, len, i) == x : Wa.Wasm.Outcome}
  %Equal.sym(Bool, Wa.Wasm.fits(p2, a, len), True{}, fin) :
    {Wa.Wasm.run.written(_, F0, Wa.Wasm.Instance{X, Wa.Wasm.Memory{p2, lim, g1, Wa.Wasm.write.bytes(i, a, B0)}}, a, len) == x : Wa.Wasm.Outcome}
  ran

# the call of alloc gave -1 (c): out of memory
def host.neg(+prog: Cr.Cir.Stmt, +regs: Nat, +cells: List<&2, Cr.Cir.Cell>, +i: List<&2, Word(8n)>, +len: U32, +M0: Wa.Wasm.Memory,
  +M1: Wa.Wasm.Memory, +F: Nat,
  c: S.EX(j => S.P2({Wa.Wasm.call(F, PH.H.TS(), 1n, Cr.Cir.alloc(Cr.Wasm.encode.len(Cr.Cir.Cell, cells)), [len], M0) ==
    Wa.Wasm.Call.done{[4294967295], M1, j} : Wa.Wasm.Call}, N.Le(j, 41n)))) ->
  {Wa.Wasm.run.alloced(Wa.Wasm.invoked(Wa.Wasm.call(F, PH.H.TS(), 1n, Cr.Cir.alloc(Cr.Wasm.encode.len(Cr.Cir.Cell, cells)), [len], M0),
    Cr.Cir.module(prog, regs, cells)), F, len, i) == Wa.Wasm.Outcome.out_of_memory{} : Wa.Wasm.Outcome}:
  (+j, c1) = c
  (ec, hj) = c1
  %Equal.sym(Wa.Wasm.Call, Wa.Wasm.call(F, PH.H.TS(), 1n, Cr.Cir.alloc(Cr.Wasm.encode.len(Cr.Cir.Cell, cells)), [len], M0),
      Wa.Wasm.Call.done{[4294967295], M1, j}, ec) :
    {Wa.Wasm.run.alloced(Wa.Wasm.invoked(_, Cr.Cir.module(prog, regs, cells)), F, len, i) == Wa.Wasm.Outcome.out_of_memory{} : Wa.Wasm.Outcome}
  {==}

# alloc gave -1 after an engine's refusal (h): out of memory, with the answer's index
def host.refused(+prog: Cr.Cir.Stmt, +regs: Nat, +cells: List<&2, Cr.Cir.Cell>, +i: List<&2, Word(8n)>, +len: U32, +lim: U32,
  +x: Wa.Wasm.Outcome, +gs: List<&2, Bool>,
  h: AF.AFR(Cr.Wasm.encode.len(Cr.Cir.Cell, cells), len, Cr.Cir.pages(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), lim, gs, IN.B0(cells))) ->
  &f:Nat -> HO(x, gs, Wa.Wasm.run.alloced(Wa.Wasm.invoked(Wa.Wasm.call(f, PH.H.TS(), 1n, Cr.Cir.alloc(Cr.Wasm.encode.len(Cr.Cir.Cell, cells)), [len], Wa.Wasm.Memory{Cr.Cir.pages(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), lim, gs, IN.B0(cells)}),
    Cr.Cir.module(prog, regs, cells)), f, len, i)):
  (+N2, h1) = h
  (+k0, h2) = h1
  (hg, h3) = h2
  (41n, Inr{(k0, (hg, host.neg(prog, regs, cells, i, len, Wa.Wasm.Memory{Cr.Cir.pages(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), lim, gs, IN.B0(cells)},
    Wa.Wasm.Memory{Cr.Cir.pages(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), lim, S.Drop(1n, gs), IN.B0(cells)}, 41n,
    AF.af.done(Cr.Wasm.encode.len(Cr.Cir.Cell, cells), len, Wa.Wasm.Memory{Cr.Cir.pages(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), lim, gs, IN.B0(cells)}, 4294967295,
      Wa.Wasm.Memory{Cr.Cir.pages(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), lim, S.Drop(1n, gs), IN.B0(cells)}, 41n, N.le_refl(41n), N2, h3))))})

# alloc gave -1 with no refusal (h), as Cir does (e): out of memory
def host.none(+prog: Cr.Cir.Stmt, +regs: Nat, +cells: List<&2, Cr.Cir.Cell>, +i: List<&2, Word(8n)>, +len: U32, +lim: U32,
  +x: Wa.Wasm.Outcome, +gs: List<&2, Bool>,
  h: S.EX(N2 => S.P2({PH.H.steps(N2, Wa.Wasm.Step.next{AF.af.fr0(Cr.Wasm.encode.len(Cr.Cir.Cell, cells), len), Wa.Wasm.Memory{Cr.Cir.pages(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), lim, gs, IN.B0(cells)}}) ==
    Wa.Wasm.Step.done{[4294967295], Wa.Wasm.Memory{Cr.Cir.pages(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), lim, gs, IN.B0(cells)}} : Wa.Wasm.Step}, N.Le(N2, 41n))),
  e: {Wa.Wasm.Outcome.out_of_memory{} == x : Wa.Wasm.Outcome}) ->
  &f:Nat -> HO(x, gs, Wa.Wasm.run.alloced(Wa.Wasm.invoked(Wa.Wasm.call(f, PH.H.TS(), 1n, Cr.Cir.alloc(Cr.Wasm.encode.len(Cr.Cir.Cell, cells)), [len], Wa.Wasm.Memory{Cr.Cir.pages(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), lim, gs, IN.B0(cells)}),
    Cr.Cir.module(prog, regs, cells)), f, len, i)):
  (+N2, h1) = h
  (41n, Inl{Equal.trans(Wa.Wasm.Outcome, Wa.Wasm.run.alloced(Wa.Wasm.invoked(Wa.Wasm.call(41n, PH.H.TS(), 1n, Cr.Cir.alloc(Cr.Wasm.encode.len(Cr.Cir.Cell, cells)), [len], Wa.Wasm.Memory{Cr.Cir.pages(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), lim, gs, IN.B0(cells)}),
    Cr.Cir.module(prog, regs, cells)), 41n, len, i), Wa.Wasm.Outcome.out_of_memory{}, x,
    host.neg(prog, regs, cells, i, len, Wa.Wasm.Memory{Cr.Cir.pages(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), lim, gs, IN.B0(cells)},
      Wa.Wasm.Memory{Cr.Cir.pages(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), lim, gs, IN.B0(cells)}, 41n,
      AF.af.done(Cr.Wasm.encode.len(Cr.Cir.Cell, cells), len, Wa.Wasm.Memory{Cr.Cir.pages(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), lim, gs, IN.B0(cells)}, 4294967295,
        Wa.Wasm.Memory{Cr.Cir.pages(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), lim, gs, IN.B0(cells)}, 41n, N.le_refl(41n), N2, h1)), e)})

# alloc's run gave a in N2 <= 41 steps (h2), and took the answers to those after k0; run's run is rr:
# the fuel is 41 + run's steps; a refusal retains its answer's index
def host.ran(+prog: Cr.Cir.Stmt, +regs: Nat, +cells: List<&2, Cr.Cir.Cell>, +i: List<&2, Word(8n)>, +len: U32, +lim: U32,
  +x: Wa.Wasm.Outcome, +gs: List<&2, Bool>, +k0: Nat, +p2: U32, +N2: Nat,
  h2: S.P2({PH.H.steps(N2, Wa.Wasm.Step.next{AF.af.fr0(Cr.Wasm.encode.len(Cr.Cir.Cell, cells), len), Wa.Wasm.Memory{Cr.Cir.pages(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), lim, gs, IN.B0(cells)}}) ==
    Wa.Wasm.Step.done{[AF.af.a(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))], Wa.Wasm.Memory{p2, lim, S.Drop(k0, gs), IN.B0(cells)}} : Wa.Wasm.Step}, N.Le(N2, 41n)),
  ane: {U32.is_eq(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells)), 4294967295) == False{} : Bool}, fin: {Wa.Wasm.fits(p2, Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells)), len) == True{} : Bool},
  rr: RSO(x, S.Drop(k0, gs), PR.pr.fr(prog, regs, Cr.Wasm.encode.len(Cr.Cir.Cell, cells), Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells)), len), Wa.Wasm.Memory{p2, lim, S.Drop(k0, gs), IN.B2(cells, i)})) ->
  &f:Nat -> HO(x, gs, Wa.Wasm.run.alloced(Wa.Wasm.invoked(Wa.Wasm.call(f, PH.H.TS(), 1n, Cr.Cir.alloc(Cr.Wasm.encode.len(Cr.Cir.Cell, cells)), [len], Wa.Wasm.Memory{Cr.Cir.pages(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), lim, gs, IN.B0(cells)}),
    Cr.Cir.module(prog, regs, cells)), f, len, i)):
  match rr:
    case Inl{r}:
      (+N3, r1) = r
      (+mm, r2) = r1
      (+s0, r3) = r2
      (eq3, ok3) = r3
      (Nat.add(41n, N3), Inl{host.call(prog, regs, cells, i, len, lim, x, gs, S.Drop(k0, gs), p2, N3, mm, s0, eq3, ok3, ane, fin,
        AF.af.done(Cr.Wasm.encode.len(Cr.Cir.Cell, cells), len, Wa.Wasm.Memory{Cr.Cir.pages(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), lim, gs, IN.B0(cells)}, AF.af.a(Cr.Wasm.encode.len(Cr.Cir.Cell, cells)),
          Wa.Wasm.Memory{p2, lim, S.Drop(k0, gs), IN.B0(cells)}, Nat.add(41n, N3), N.le_add_r(41n, N3), N2, h2))})
    case Inr{r}:
      (+N3, r1) = r
      (+mm, r2) = r1
      (+k, r3) = r2
      (hg, eq3) = r3
      (Nat.add(41n, N3), Inr{(Nat.add(k0, k), (Equal.trans(Maybe<&2, Bool>, List.get(&2, Bool, gs, Nat.add(k0, k)), List.get(&2, Bool, S.Drop(k0, gs), k), Some{False{}},
        S.get.add(k0, gs, k), hg),
        host.call(prog, regs, cells, i, len, lim, Wa.Wasm.Outcome.out_of_memory{}, gs, S.Drop(k0, gs), p2, N3, mm, 1, eq3, {==}, ane, fin,
          AF.af.done(Cr.Wasm.encode.len(Cr.Cir.Cell, cells), len, Wa.Wasm.Memory{Cr.Cir.pages(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), lim, gs, IN.B0(cells)}, AF.af.a(Cr.Wasm.encode.len(Cr.Cir.Cell, cells)),
            Wa.Wasm.Memory{p2, lim, S.Drop(k0, gs), IN.B0(cells)}, Nat.add(41n, N3), N.le_add_r(41n, N3), N2, h2))))})

# alloc's call, by what Cir.alloc.pages gives (r), exactly or stopped by an engine's refusal (h); then the input's write
# and run's call
def host.alloced(r: Maybe<&2, U32>, +n: Nat, +prog: Cr.Cir.Stmt, +regs: Nat, +cells: List<&2, Cr.Cir.Cell>, +i: List<&2, Word(8n)>,
  +len: U32, +lim: U32, +x: Wa.Wasm.Outcome, +gs: List<&2, Bool>, +MX: U32, +MD: U32, +P: Nat, +G: Nat, +W: Nat, +hW: {W == PH.H.W(32n) : Nat},
  +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat}, +hG: {N.D(16n, G) == W : Nat},
  +eK: {U32.to_nat(Cr.Wasm.encode.len(Cr.Cir.Cell, cells)) == List.length(&2, Cr.Cir.Cell, cells) : Nat}, +hK: N.Le(2n+List.length(&2, Cr.Cir.Cell, cells), P), +hX0: N.Le(U32.to_nat(U32.inc(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), P),
  +eA: {U32.to_nat(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))) == PH.H.t20(1n+List.length(&2, Cr.Cir.Cell, cells)) : Nat},
  +eLn: {len == Cr.Wasm.encode.len(Word(8n), i) : U32}, +eL: {U32.to_nat(len) == List.length(&2, Word(8n), i) : Nat}, +hlm: N.Le(U32.to_nat(lim), G),
  +ok: {V.ok.stmt(prog, regs) == True{} : Bool}, +hR: N.Le(8n+regs, U32.to_nat(MX)), +hd: N.Le(T.dep(prog), U32.to_nat(MD)), +hx: is.ro(x),
  h: AF.AFS(r, Cr.Wasm.encode.len(Cr.Cir.Cell, cells), len, Cr.Cir.pages(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), lim, gs, IN.B0(cells)),
  e: {Cr.Cir.result.alloced(r, n, prog, regs, cells, Cr.Wasm.encode.len(Cr.Cir.Cell, cells), U32.add(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells)), len), lim, i) == x : Wa.Wasm.Outcome}) ->
  &f:Nat -> HO(x, gs, Wa.Wasm.run.alloced(Wa.Wasm.invoked(Wa.Wasm.call(f, PH.H.TS(), 1n, Cr.Cir.alloc(Cr.Wasm.encode.len(Cr.Cir.Cell, cells)), [len], Wa.Wasm.Memory{Cr.Cir.pages(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), lim, gs, IN.B0(cells)}),
    Cr.Cir.module(prog, regs, cells)), f, len, i)):
  match r:
    case None{}:
      match h:
        case Inl{h1}:
          host.none(prog, regs, cells, i, len, lim, x, gs, h1, e)
        case Inr{h1}:
          host.refused(prog, regs, cells, i, len, lim, x, gs, h1)
    case Some{+p2}:
      match h:
        case Inr{h1}:
          host.refused(prog, regs, cells, i, len, lim, x, gs, h1)
        case Inl{h1}:
          (+N2, h2) = h1
          (+k0, h3) = h2
          (h4, ff) = h3
          (e1, f1) = ff
          (+e2, f2) = f1
          (e3, e4) = f2
          +k = Cr.Wasm.encode.len(Cr.Cir.Cell, cells)
          +a = Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))
          +E = U32.add(a, len)
          +K = List.length(&2, Cr.Cir.Cell, cells)
          +L = List.length(&2, Word(8n), i)
          +A = U32.to_nat(a)
          # the input's end, a + len exactly, at most 2^32 - 16
          +eE0 = nowrap(a, len, W, hW, e1)
          +eE = Equal.trans(Nat, U32.to_nat(E), Nat.add(A, U32.to_nat(len)), Nat.add(A, L), eE0, Equal.cong(Nat, Nat, z => Nat.add(A, z), U32.to_nat(len), L, eL))
          +hE = e20.of(E, P, hP, e2)
          +hEP = N.le_rw_l(U32.to_nat(E), Nat.add(A, L), PH.H.t20(P), eE, hE)
          # and within the p2 pages
          +h1A = N.le_rw_r(1n, PH.H.t20(1n+K), A, Equal.sym(Nat, A, PH.H.t20(1n+K), eA), Unit{})
          +h1E = N.le_rw_r(1n, Nat.add(A, U32.to_nat(len)), U32.to_nat(E), Equal.sym(Nat, U32.to_nat(E), Nat.add(A, U32.to_nat(len)), eE0),
            N.le_trans(1n, A, Nat.add(A, U32.to_nat(len)), h1A, N.le_add_r(A, U32.to_nat(len))))
          +hpp = N.le_rw_l(U32.to_nat(AF.af.need(k, len)), U32.to_nat(U32.inc(U32.shrn(U32.sub(E, 1), 16n))), U32.to_nat(p2),
            Equal.cong(U32, Nat, z => U32.to_nat(z), AF.af.need(k, len), U32.inc(U32.shrn(U32.sub(E, 1), 16n)), F.inc.add1(U32.shrn(U32.sub(E, 1), 16n))),
            Z.le.of(AF.af.need(k, len), p2, e3))
          +hEB0 = N.le_rw_l(1n+U32.to_nat(U32.sub(E, 1)), U32.to_nat(E), Q.PB(p2), Z.dec.nat(E, h1E),
            A.room.of(U32.sub(E, 1), p2, W, hW, F.w16(P, hP, W, hW), hpp))
          +hEB = N.le_rw_l(U32.to_nat(E), Nat.add(A, L), Q.PB(p2), eE, hEB0)
          +hpl = Z.le.of(p2, lim, e4)
          # alloc gave a, not -1, and the input fits
          +ane = ne.max(a, 4294967280, Z.le.to(a, 4294967280, N.le_trans(A, U32.to_nat(E), U32.to_nat(4294967280),
            N.le_rw_r(A, Nat.add(A, U32.to_nat(len)), U32.to_nat(E), Equal.sym(Nat, U32.to_nat(E), Nat.add(A, U32.to_nat(len)), eE0), N.le_add_r(A, U32.to_nat(len))),
            ngt.to(E, 4294967280, e2))), {==})
          +fin = fits.gen(p2, a, len, W, hW, h1A, N.le_rw_l(U32.to_nat(E), Nat.add(A, U32.to_nat(len)), Q.PB(p2), eE0, hEB0), A.pb2.le(p2, lim, G, W, hG, hpl, hlm))
          host.ran(prog, regs, cells, i, len, lim, x, gs, k0, p2, N2, h4, ane, fin,
            rs.run(n, prog, regs, cells, i, len, p2, lim, x, S.Drop(k0, gs), MX, MD, P, G, W, hW, hP, hG, eK, hK, hX0, eLn, eE, hEP, hEB, hlm, hpl, ok, hR, hd, hx, e))

# the input of len bytes, as length32 counts them (lt)
def host.len(+n: Nat, +prog: Cr.Cir.Stmt, +regs: Nat, +cells: List<&2, Cr.Cir.Cell>, +i: List<&2, Word(8n)>, +len: U32,
  +lim: U32, +x: Wa.Wasm.Outcome, +gs: List<&2, Bool>, +MX: U32, +MD: U32, +P: Nat, +G: Nat, +W: Nat, +hW: {W == PH.H.W(32n) : Nat},
  +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat}, +hG: {N.D(16n, G) == W : Nat},
  +eK: {U32.to_nat(Cr.Wasm.encode.len(Cr.Cir.Cell, cells)) == List.length(&2, Cr.Cir.Cell, cells) : Nat}, +hK: N.Le(2n+List.length(&2, Cr.Cir.Cell, cells), P), +hX0: N.Le(U32.to_nat(U32.inc(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), P),
  +eA: {U32.to_nat(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))) == PH.H.t20(1n+List.length(&2, Cr.Cir.Cell, cells)) : Nat}, +hlm: N.Le(U32.to_nat(lim), G),
  +ok: {V.ok.stmt(prog, regs) == True{} : Bool}, +hR: N.Le(8n+regs, U32.to_nat(MX)), +hd: N.Le(T.dep(prog), U32.to_nat(MD)), +hx: is.ro(x),
  +hp0: {U32.is_eq(Cr.Cir.pages(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), 4294967295) == False{} : Bool}, +hpl0: {U32.is_le(Cr.Cir.pages(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), lim) == True{} : Bool},
  e: {Cr.Cir.result.alloced(Cr.Cir.alloc.pages(Cr.Wasm.encode.len(Cr.Cir.Cell, cells), len, Cr.Cir.pages(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), lim), n, prog, regs, cells, Cr.Wasm.encode.len(Cr.Cir.Cell, cells), U32.add(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells)), len), lim, i) ==
    x : Wa.Wasm.Outcome},
  lt: L32.T(i, 0, len)) ->
  &f:Nat -> HO(x, gs, Wa.Wasm.run.alloced(Wa.Wasm.invoked(Wa.Wasm.call(f, PH.H.TS(), 1n, Cr.Cir.alloc(Cr.Wasm.encode.len(Cr.Cir.Cell, cells)), [len], Wa.Wasm.Memory{Cr.Cir.pages(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), lim, gs, IN.B0(cells)}),
    Cr.Cir.module(prog, regs, cells)), f, len, i)):
  (el1, el2) = lt
  +L = List.length(&2, Word(8n), i)
  +eL = Equal.trans(Nat, U32.to_nat(len), Nat.add(L, U32.to_nat(0)), L, el2, N.add_zero(L))
  +eLn = Equal.trans(U32, len, Z.incn(L, 0), Cr.Wasm.encode.len(Word(8n), i), el1,
    Equal.trans(U32, Z.incn(L, 0), U32.add(U32.from_nat(L), 0), Cr.Wasm.encode.len(Word(8n), i), Z.incn.add(L, 0),
      Equal.trans(U32, U32.add(U32.from_nat(L), 0), U32.from_nat(L), Cr.Wasm.encode.len(Word(8n), i), Y.U32.add_zero(U32.from_nat(L)),
        Equal.sym(U32, Cr.Wasm.encode.len(Word(8n), i), U32.from_nat(L), enc.from(Word(8n), i)))))
  host.alloced(Cr.Cir.alloc.pages(Cr.Wasm.encode.len(Cr.Cir.Cell, cells), len, Cr.Cir.pages(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), lim), n, prog, regs, cells, i, len, lim, x, gs, MX, MD, P, G, W, hW, hP, hG,
    eK, hK, hX0, eA, eLn, eL, hlm, ok, hR, hd, hx, AF.af.steps(Cr.Wasm.encode.len(Cr.Cir.Cell, cells), len, Cr.Cir.pages(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), lim, gs, IN.B0(cells), hp0, hpl0), e)

# the input's length, by length32 (ln): none is out of memory, for both
def host.sized(ln: Maybe<&2, U32>, +n: Nat, +prog: Cr.Cir.Stmt, +regs: Nat, +cells: List<&2, Cr.Cir.Cell>, +i: List<&2, Word(8n)>,
  +lim: U32, +x: Wa.Wasm.Outcome, +gs: List<&2, Bool>, +MX: U32, +MD: U32, +P: Nat, +G: Nat, +W: Nat, +hW: {W == PH.H.W(32n) : Nat},
  +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat}, +hG: {N.D(16n, G) == W : Nat},
  +eK: {U32.to_nat(Cr.Wasm.encode.len(Cr.Cir.Cell, cells)) == List.length(&2, Cr.Cir.Cell, cells) : Nat}, +hK: N.Le(2n+List.length(&2, Cr.Cir.Cell, cells), P), +hX0: N.Le(U32.to_nat(U32.inc(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), P),
  +eA: {U32.to_nat(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))) == PH.H.t20(1n+List.length(&2, Cr.Cir.Cell, cells)) : Nat}, +hlm: N.Le(U32.to_nat(lim), G),
  +ok: {V.ok.stmt(prog, regs) == True{} : Bool}, +hR: N.Le(8n+regs, U32.to_nat(MX)), +hd: N.Le(T.dep(prog), U32.to_nat(MD)), +hx: is.ro(x),
  +hp0: {U32.is_eq(Cr.Cir.pages(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), 4294967295) == False{} : Bool}, +hpl0: {U32.is_le(Cr.Cir.pages(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), lim) == True{} : Bool},
  eln: {Wa.Wasm.length32(i) == ln : Maybe<&2, U32>},
  e: {Cr.Cir.result.sized(ln, n, prog, regs, cells, Cr.Wasm.encode.len(Cr.Cir.Cell, cells), Cr.Cir.pages(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), lim, i) == x : Wa.Wasm.Outcome}) ->
  &f:Nat -> HO(x, gs, Wa.Wasm.run.sized(ln, f, Wa.Wasm.Instance{Cr.Cir.module(prog, regs, cells), Wa.Wasm.Memory{Cr.Cir.pages(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), lim, gs, IN.B0(cells)}}, i)):
  match ln:
    case None{}:
      (0n, Inl{Equal.trans(Wa.Wasm.Outcome, Wa.Wasm.run.sized(None{}, 0n, Wa.Wasm.Instance{Cr.Cir.module(prog, regs, cells), Wa.Wasm.Memory{Cr.Cir.pages(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), lim, gs, IN.B0(cells)}}, i),
        Wa.Wasm.Outcome.out_of_memory{}, x, {==}, e)})
    case Some{+len}:
      host.len(n, prog, regs, cells, i, len, lim, x, gs, MX, MD, P, G, W, hW, hP, hG, eK, hK, hX0, eA, hlm, ok, hR, hd, hx, hp0, hpl0, e,
        L32.go(i, 0, len, W, hW, eln))

# the instance of the memory of the module's minimum, with the data segment,
# exports what the host uses (H1): the host's run is that of the input (q)
def host.made(+prog: Cr.Cir.Stmt, +regs: Nat, +cells: List<&2, Cr.Cir.Cell>, +i: List<&2, Word(8n)>, +m: U32, +x: Wa.Wasm.Outcome, +gs: List<&2, Bool>,
  +P: Nat, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat}, +W: Nat, +hW: {W == PH.H.W(32n) : Nat},
  +G: Nat, +hG: {N.D(16n, G) == W : Nat}, +eG: {U32.to_nat(65536) == G : Nat},
  +hK1: N.Le(1n+List.length(&2, Cr.Cir.Cell, cells), P), +eA: {U32.to_nat(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))) == PH.H.t20(1n+List.length(&2, Cr.Cir.Cell, cells)) : Nat},
  q: &f:Nat -> HO(x, gs, Wa.Wasm.run.sized(Wa.Wasm.length32(i), f, Wa.Wasm.Instance{Cr.Cir.module(prog, regs, cells),
    Wa.Wasm.Memory{Cr.Cir.pages(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), Wa.Wasm.min(m, 65536), gs, IN.B0(cells)}}, i))) ->
  &f:Nat -> HO(x, gs, Wa.Wasm.run.made(f, Wa.Wasm.instantiate.sized(Wa.Wasm.memory.of.if(True{}, Wa.Wasm.Memory{Cr.Cir.pages(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), Wa.Wasm.min(m, 65536), gs, Wa.Wasm.Bytes.zero{}}),
    Some{Wa.Wasm.Segment{20, Cr.Cir.bytes(cells)}}, Cr.Cir.module(prog, regs, cells)), i)):
  (+f0, pr0) = q
  +p0 = Cr.Cir.pages(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells)))
  +lim = Wa.Wasm.min(m, 65536)
  +B0 = IN.B0(cells)
  +X = Cr.Cir.module(prog, regs, cells)
  (f0, {(
    %Equal.sym(Bool, Wa.Wasm.fits.len(p0, 20, Wa.Wasm.length32(Cr.Cir.bytes(cells))), True{}, seg.fits(cells, P, hP, W, hW, G, hG, eG, hK1, eA)) :
      HO(x, gs, Wa.Wasm.run.made(f0, Wa.Wasm.instantiate.made(Wa.Wasm.memory.init.if(_, p0, lim, gs, Wa.Wasm.write.bytes(Cr.Cir.bytes(cells), 20, Wa.Wasm.Bytes.zero{})),
        X), i))
    %Equal.sym(Bool, Wa.Wasm.run.is_host(Wa.Wasm.Instance{X, Wa.Wasm.Memory{p0, lim, gs, B0}}), True{}, is.host(prog, regs, cells, Wa.Wasm.Memory{p0, lim, gs, B0})) :
      HO(x, gs, Wa.Wasm.run.instance(_, f0, Wa.Wasm.Instance{X, Wa.Wasm.Memory{p0, lim, gs, B0}}, i))
    pr0) : HO(x, gs, Wa.Wasm.run.made(f0, Wa.Wasm.instantiate.sized(Wa.Wasm.memory.of.if(True{}, Wa.Wasm.Memory{p0, lim, gs, Wa.Wasm.Bytes.zero{}}),
      Some{Wa.Wasm.Segment{20, Cr.Cir.bytes(cells)}}, X), i))})

# the memory of the module's minimum, when the engine allows that many pages
# (b); then the data segment and the exports (H1)
def host.mem(b: Bool, +n: Nat, +prog: Cr.Cir.Stmt, +regs: Nat, +cells: List<&2, Cr.Cir.Cell>, +i: List<&2, Word(8n)>, +m: U32,
  +x: Wa.Wasm.Outcome, +gs: List<&2, Bool>, +MX: U32, +MD: U32, +P: Nat, +G: Nat, +W: Nat, +hW: {W == PH.H.W(32n) : Nat},
  +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat}, +hG: {N.D(16n, G) == W : Nat},
  +eK: {U32.to_nat(Cr.Wasm.encode.len(Cr.Cir.Cell, cells)) == List.length(&2, Cr.Cir.Cell, cells) : Nat}, +hK: N.Le(2n+List.length(&2, Cr.Cir.Cell, cells), P), +hK1: N.Le(1n+List.length(&2, Cr.Cir.Cell, cells), P), +hX0: N.Le(U32.to_nat(U32.inc(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), P),
  +eA: {U32.to_nat(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))) == PH.H.t20(1n+List.length(&2, Cr.Cir.Cell, cells)) : Nat}, +eG: {U32.to_nat(65536) == G : Nat}, +hlm: N.Le(U32.to_nat(Wa.Wasm.min(m, 65536)), G),
  +ok: {V.ok.stmt(prog, regs) == True{} : Bool}, +hR: N.Le(8n+regs, U32.to_nat(MX)), +hd: N.Le(T.dep(prog), U32.to_nat(MD)), +hx: is.ro(x),
  eb: {U32.is_le(Cr.Cir.pages(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), m) == b : Bool},
  e: {Cr.Cir.result.memory(b, n, prog, regs, cells, Cr.Wasm.encode.len(Cr.Cir.Cell, cells), Cr.Cir.pages(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), Wa.Wasm.min(m, 65536), i) == x : Wa.Wasm.Outcome}) ->
  &f:Nat -> HO(x, gs, Wa.Wasm.run.made(f, Wa.Wasm.instantiate.sized(Wa.Wasm.memory.of.if(b, Wa.Wasm.Memory{Cr.Cir.pages(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), Wa.Wasm.min(m, 65536), gs, Wa.Wasm.Bytes.zero{}}),
    Some{Wa.Wasm.Segment{20, Cr.Cir.bytes(cells)}}, Cr.Cir.module(prog, regs, cells)), i)):
  match b:
    case False{}:
      (0n, Inl{Equal.trans(Wa.Wasm.Outcome, Wa.Wasm.run.made(0n, Wa.Wasm.instantiate.sized(Wa.Wasm.memory.of.if(False{}, Wa.Wasm.Memory{Cr.Cir.pages(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), Wa.Wasm.min(m, 65536), gs, Wa.Wasm.Bytes.zero{}}),
        Some{Wa.Wasm.Segment{20, Cr.Cir.bytes(cells)}}, Cr.Cir.module(prog, regs, cells)), i), Wa.Wasm.Outcome.out_of_memory{}, x, {==}, e)})
    case True{}:
      +a = Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))
      +p0 = Cr.Cir.pages(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells)))
      +lim = Wa.Wasm.min(m, 65536)
      +hle = V.pages.le(U32.sub(a, 1))
      host.made(prog, regs, cells, i, m, x, gs, P, hP, W, hW, G, hG, eG, hK1, eA,
        host.sized(Wa.Wasm.length32(i), n, prog, regs, cells, i, lim, x, gs, MX, MD, P, G, W, hW, hP, hG, eK, hK, hX0, eA, hlm,
          ok, hR, hd, hx, ne.max(p0, 65536, hle, {==}), le.min(p0, m, eb, hle), {==}, e))

# 1 + K <= M2 < PU = P gives 2 + K <= P; M2 and PU stay variables, so that
# no check compares two closed numbers by counting
def k.lt.p(+K: Nat, +M2: U32, +PU: U32, +P: Nat, h: N.Le(1n+K, U32.to_nat(M2)), hl: {U32.is_lt(M2, PU) == True{} : Bool},
  eP: {U32.to_nat(PU) == P : Nat}) -> N.Le(2n+K, P):
  N.le_trans(2n+K, 1n+U32.to_nat(M2), P, le.ss(1n+K, U32.to_nat(M2), h),
    N.le_rw_r(1n+U32.to_nat(M2), U32.to_nat(PU), P, eP, Z.lt.of(M2, PU, hl)))

# the valid module of prog, instantiated on an engine of m pages with the answers gs to its grows: the host
# gives Cir's outcome x (a result, or out of memory), or runs out of memory after an answer that refuses a grow
def host.all(+n: Nat, +prog: Cr.Cir.Stmt, +regs: Nat, +cells: List<&2, Cr.Cir.Cell>, +i: List<&2, Word(8n)>, +m: U32, +x: Wa.Wasm.Outcome, +gs: List<&2, Bool>,
  +MX: U32, +MD: U32, small: {Nat.is_lt(List.length(&2, Cr.Cir.Cell, cells), U32.to_nat(67108864)) == True{} : Bool},
  +ok: {V.ok.stmt(prog, regs) == True{} : Bool}, +hR: N.Le(8n+regs, U32.to_nat(MX)), +hd: N.Le(T.dep(prog), U32.to_nat(MD)), +hx: is.ro(x),
  e: {Cr.Cir.result(n, prog, regs, cells, i, m) == x : Wa.Wasm.Outcome}) ->
  &f:Nat -> HO(x, gs, Wa.Wasm.run.made(f, Wa.Wasm.instantiate.valid(True{}, Cr.Cir.module(prog, regs, cells), m, gs), i)):
  +W = PH.H.W(32n)
  +P = PH.H.pat(7n)
  +G = N.D(16n, 1n)
  +hW = {{==} : {W == PH.H.W(32n) : Nat}}
  +hP = PH.H.hP()
  +k = Cr.Wasm.encode.len(Cr.Cir.Cell, cells)
  +K = List.length(&2, Cr.Cir.Cell, cells)
  # the book's cells: K < 2^26, so the number k is K, and 2 + K <= P
  +hK0 = M.lt_le(K, U32.to_nat(67108864), small)
  +eK = Equal.trans(Nat, U32.to_nat(k), U32.to_nat(U32.from_nat(K)), K, Equal.cong(U32, Nat, z => U32.to_nat(z), k, U32.from_nat(K), enc.from(Cr.Cir.Cell, cells)),
    M.tofrom(K, 67108864, N.weaken(K, U32.to_nat(67108864), hK0)))
  +hK = k.lt.p(K, 67108864, 214748364, P, hK0, {==}, A.lit.P(P, hP))
  +hK1 = N.le_trans(1n+K, 2n+K, P, N.le_succ(1n+K, 1n+K, N.le_refl(1n+K)), hK)
  # k + 1 = K + 1, and the input's address is a = 20 (K + 1)
  +ek1 = F.inc.eq(k, K, eK, W, hW, N.weaken(2n+K, W, PH.H.small(32n, 1n+K, P, hP, hK)))
  +hX0 = N.le_rw_l(1n+K, U32.to_nat(U32.inc(k)), P, Equal.sym(Nat, U32.to_nat(U32.inc(k)), 1n+K, ek1), hK1)
  +eA = Equal.trans(Nat, U32.to_nat(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), PH.H.t20(U32.to_nat(U32.inc(k))), PH.H.t20(1n+K), F.at.nat(U32.inc(k), P, hP, hX0),
    Equal.cong(Nat, Nat, z => PH.H.t20(z), U32.to_nat(U32.inc(k)), 1n+K, ek1))
  +eG = {N.val_65536() : {U32.to_nat(65536) == G : Nat}}
  host.mem(U32.is_le(Cr.Cir.pages(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), m), n, prog, regs, cells, i, m, x, gs, MX, MD, P, G, W, hW, hP, gw(W, hW), eK, hK, hK1, hX0, eA, eG, lim.le(m, G, eG),
    ok, hR, hd, hx, {==}, e)

# an outcome equal to a host outcome is one, with the same refusal
def ho.rw(+x: Wa.Wasm.Outcome, +gs: List<&2, Bool>, +y: Wa.Wasm.Outcome, +y2: Wa.Wasm.Outcome, e: {y2 == y : Wa.Wasm.Outcome}, q: HO(x, gs, y)) -> HO(x, gs, y2):
  match q:
    case Inl{p}:
      Inl{Equal.trans(Wa.Wasm.Outcome, y2, y, x, e, p)}
    case Inr{r}:
      (+k, r1) = r
      (hg, p) = r1
      Inr{(k, (hg, Equal.trans(Wa.Wasm.Outcome, y2, y, Wa.Wasm.Outcome.out_of_memory{}, e, p)))}

# the bytes of prog's module decode to the module (M.round.sized), which is
# valid (V.valid.module): their run is the instance's (q)
def run.of(+prog: Cr.Cir.Stmt, +regs: Nat, +cells: List<&2, Cr.Cir.Cell>, +i: List<&2, Word(8n)>, +m: U32, +x: Wa.Wasm.Outcome, +gs: List<&2, Bool>,
  small: {Nat.is_lt(List.length(&2, Cr.Cir.Cell, cells), U32.to_nat(67108864)) == True{} : Bool},
  +ok: {V.ok.stmt(prog, regs) == True{} : Bool}, +hr: {Nat.is_le(6n+regs, U32.to_nat(50000)) == True{} : Bool},
  hs: N.Le(1n+List.length(&2, Word(8n), Cr.Wasm.encode.codes([Cr.Cir.alloc(Cr.Wasm.encode.len(Cr.Cir.Cell, cells)),
    Cr.Cir.run(prog, regs, Cr.Wasm.encode.len(Cr.Cir.Cell, cells))])), U32.to_nat(4294967295)),
  q: &f:Nat -> HO(x, gs, Wa.Wasm.run.made(f, Wa.Wasm.instantiate.valid(True{}, Cr.Cir.module(prog, regs, cells), m, gs), i))) ->
  &f:Nat -> HO(x, gs, Wa.Wasm.run(f, Cr.Wasm.encode(Cr.Cir.module(prog, regs, cells)), i, Wa.Wasm.Engine{m, gs})):
  (+f0, pr) = q
  +X = Cr.Cir.module(prog, regs, cells)
  +w = Cr.Wasm.encode(Cr.Cir.module(prog, regs, cells))
  +rd = M.round.sized(prog, regs, cells, 67108864, 4294967295, 50000, G.val_M2(), M.val_MAX(), {==},
    M.lt_le(List.length(&2, Cr.Cir.Cell, cells), U32.to_nat(67108864), small), N.toLe(6n+regs, U32.to_nat(50000), hr), hs)
  +rest = {(
    %Equal.sym(Maybe<&2, Wa.Wasm.Module>, Wa.Wasm.decode.module(w), Some{X}, rd) :
      HO(x, gs, Wa.Wasm.run.made(f0, Wa.Wasm.instantiate.decoded(_, m, gs), i))
    %Equal.sym(Wa.Wasm.Made, Wa.Wasm.instantiate.decoded(Some{X}, m, gs), Wa.Wasm.instantiate.valid(Wa.Wasm.valid.module(X), X, m, gs), PH.H.inst.dec(X, m, gs)) :
      HO(x, gs, Wa.Wasm.run.made(f0, _, i))
    %Equal.sym(Bool, Wa.Wasm.valid.module(X), True{}, V.valid.module(prog, regs, cells, ok, hr)) :
      HO(x, gs, Wa.Wasm.run.made(f0, Wa.Wasm.instantiate.valid(_, X, m, gs), i))
    pr) : HO(x, gs, Wa.Wasm.run.made(f0, Wa.Wasm.instantiate.decoded(Wa.Wasm.decode.module(w), m, gs), i))}
  (f0, ho.rw(x, gs, Wa.Wasm.run.made(f0, Wa.Wasm.instantiate.decoded(Wa.Wasm.decode.module(w), m, gs), i), Wa.Wasm.run(f0, w, i, Wa.Wasm.Engine{m, gs}),
    PH.H.run.eq(f0, w, i, m, gs), rest))

# the run of the bytes of prog's module, on an engine with the answers gs: Cir's outcome x (a result, or out of
# memory), or out of memory after a refusal
def run.all(+n: Nat, +prog: Cr.Cir.Stmt, +regs: Nat, +cells: List<&2, Cr.Cir.Cell>, +i: List<&2, Word(8n)>, +m: U32, +x: Wa.Wasm.Outcome, +gs: List<&2, Bool>,
  +MX: U32, +MD: U32, +small: {Nat.is_lt(List.length(&2, Cr.Cir.Cell, cells), U32.to_nat(67108864)) == True{} : Bool},
  +ok: {V.ok.stmt(prog, regs) == True{} : Bool}, +hR: N.Le(8n+regs, U32.to_nat(MX)), +hd: N.Le(T.dep(prog), U32.to_nat(MD)), +hx: is.ro(x),
  hr: {Nat.is_le(6n+regs, U32.to_nat(50000)) == True{} : Bool},
  hs: N.Le(1n+List.length(&2, Word(8n), Cr.Wasm.encode.codes([Cr.Cir.alloc(Cr.Wasm.encode.len(Cr.Cir.Cell, cells)),
    Cr.Cir.run(prog, regs, Cr.Wasm.encode.len(Cr.Cir.Cell, cells))])), U32.to_nat(4294967295)),
  e: {Cr.Cir.result(n, prog, regs, cells, i, m) == x : Wa.Wasm.Outcome}) ->
  &f:Nat -> HO(x, gs, Wa.Wasm.run(f, Cr.Wasm.encode(Cr.Cir.module(prog, regs, cells)), i, Wa.Wasm.Engine{m, gs})):
  run.of(prog, regs, cells, i, m, x, gs, small, ok, hr, hs, host.all(n, prog, regs, cells, i, m, x, gs, MX, MD, small, ok, hR, hd, hx, e))

# The machine (mach_wasm.result, .oom, .result.all)

# the machine's registers, as locals, have numbers below 50000
def mach.hR() -> N.Le(8n+Mc.Mach.regs(), U32.to_nat(50000)):
  N.toLe(8n+Mc.Mach.regs(), U32.to_nat(50000), {==})

# the labels of the machine's code are fewer than 50000
def mach.hd() -> N.Le(T.dep(Mc.Mach.code()), U32.to_nat(50000)):
  N.toLe(T.dep(Mc.Mach.code()), U32.to_nat(50000), {==})

# the machine's module, run on an engine with the answers gs, gives Cir's outcome x (a result, or out of memory),
# or runs out of memory after a refusal
def mach.all(+n: Nat, +cells: List<&2, Cr.Cir.Cell>, +i: List<&2, Word(8n)>, +m: U32, +x: Wa.Wasm.Outcome, +gs: List<&2, Bool>,
  small: {Nat.is_lt(List.length(&2, Cr.Cir.Cell, cells), U32.to_nat(67108864)) == True{} : Bool}, +hx: is.ro(x),
  e: {Cr.Cir.result(n, Mc.Mach.code(), Mc.Mach.regs(), cells, i, m) == x : Wa.Wasm.Outcome}) ->
  &f:Nat -> HO(x, gs, Wa.Wasm.run(f, Cr.Wasm.encode(Cr.Cir.module(Mc.Mach.code(), Mc.Mach.regs(), cells)), i, Wa.Wasm.Engine{m, gs})):
  run.all(n, Mc.Mach.code(), Mc.Mach.regs(), cells, i, m, x, gs, 50000, 50000, small, V.mach.ok(), mach.hR(), mach.hd(), hx, {==}, CS.mach.size(cells), e)
