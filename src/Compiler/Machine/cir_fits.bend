# compiler: the output fits at halt 0 (layer B)
# =============================================
#
# At halt 0, Cir.ended gives the output only when its outn bytes at byte
# 20 × next fit in the memory's pages, as the host checks (Wasm.fits); else
# a trap. No run of Mach.code ends in that trap, by facts of Cir alone: the
# cells before next and the output after them lie in the memory (Fits) once
# M.input has taken its first new cell (fits.input); every statement keeps
# Fits (fits.exec), as an alloc and an emit grow the pages to hold what they
# add (fits.alloc); and Fits is the host's check (fits.wasm). So a halt of
# Mach.code fits (fits.code).

import Base
import ../../Wasm/impl.bend as Wa
import ../Cir/impl.bend as Cr
import ./impl.bend as Mc
import ../need_big.bend as N
import ../Cir/halt.bend as PH
import ../Cir/simulation_steps.bend as S
import ../Cir/simulation_numbers.bend as Z
import ../Cir/module_valid.bend as V
import ../Cir/module_round_trip.bend as M
import ../Cir/simulation_relation.bend as Q
import ../Cir/simulation_write_frame.bend as F
import ../Cir/simulation_alloc_emit.bend as AE
import ./statement_runs.bend as X

# Statements
# ----------

# the bytes of a memory of p pages that 32-bit addresses reach: 2^16 × p,
# up to 2^16 pages
def Mem.bytes(+p: U32) -> Nat:
  N.D(16n, U32.to_nat(Wa.Wasm.min(p, 65536)))

# the cells before next, 20 bytes each, and the outn bytes of the output
# after them lie in the memory of pg pages
def Fits.of(+nx: U32, +pg: U32, +on: U32) -> Data:
  N.Le(Nat.add(PH.H.t20(U32.to_nat(nx)), U32.to_nat(on)), Mem.bytes(pg))

# the state's cells and output lie in its memory
def Fits(st: Cr.Cir.State) -> Data:
  match st:
    case Cr.Cir.State{_, _, nx, _, _, pg, _, _, _, on}:
      Fits.of(nx, pg, on)

# what an outcome keeps: the state after it, or at its halt, fits; any
# other outcome keeps nothing
def FitsOut(o: Cr.Cir.Out) -> Data:
  match o:
    case Cr.Cir.Out.next{st}:
      Fits(st)
    case Cr.Cir.Out.halt{_, st}:
      Fits(st)
    case _:
      Unit

# no cell to reuse: the pend register holds 0, so that M.alloc takes a new
# cell, by Cir's alloc
def NewCells(st: Cr.Cir.State) -> Data:
  match st:
    case Cr.Cir.State{rg, _, _, _, _, _, _, _, _, _}:
      {List.get(&2, U32, rg, Mc.R.pend()) == Some{0} : Maybe<&2, U32>}

# The memory's bytes
# ------------------
#
# 2^32 is W, 2^16 is G and 214748364 is P, kept as variables beside their
# equations (hW, eG and hG, hP), so that no check counts to them; fits.wasm
# and the room of an alloc or an emit give their values.

# min(p, 65536), by the branch that it takes
def min.eq(+p: U32) -> {Wa.Wasm.min.if(U32.is_le(p, 65536), p, 65536) == Wa.Wasm.min(p, 65536) : U32}:
  {==}

# the branch of min(p, 65536) past 65536
def min.big(+p: U32) -> {65536 == Wa.Wasm.min.if(False{}, p, 65536) : U32}:
  {==}

def min.le(+p: U32, +G: Nat, eG: {U32.to_nat(65536) == G : Nat}) -> N.Le(U32.to_nat(Wa.Wasm.min(p, 65536)), G):
  N.le_rw_r(U32.to_nat(Wa.Wasm.min(p, 65536)), U32.to_nat(65536), G, eG,
    (%min.eq(p) : N.Le(U32.to_nat(_), U32.to_nat(65536)); N.min.case(U32.is_le(p, 65536), p, 65536, {==})))

def min.le_p.if(b: Bool, +p: U32, e: {U32.is_le(p, 65536) == b : Bool}) ->
  N.Le(U32.to_nat(Wa.Wasm.min.if(b, p, 65536)), U32.to_nat(p)):
  match b:
    case True{}:
      N.le_refl(U32.to_nat(p))
    case False{}:
      %min.big(p) : N.Le(U32.to_nat(_), U32.to_nat(p))
      N.weaken(U32.to_nat(65536), U32.to_nat(p), AE.nle.u32(p, 65536, e))

def min.le_p(+p: U32) -> N.Le(U32.to_nat(Wa.Wasm.min(p, 65536)), U32.to_nat(p)):
  %min.eq(p) : N.Le(U32.to_nat(_), U32.to_nat(p))
  min.le_p.if(U32.is_le(p, 65536), p, {==})

def min.ge.if(b: Bool, +p: U32, +x: Nat, +G: Nat, eG: {U32.to_nat(65536) == G : Nat}, h1: N.Le(x, U32.to_nat(p)), h2: N.Le(x, G)) ->
  N.Le(x, U32.to_nat(Wa.Wasm.min.if(b, p, 65536))):
  match b:
    case True{}:
      h1
    case False{}:
      %min.big(p) : N.Le(x, U32.to_nat(_))
      N.le_rw_r(x, G, U32.to_nat(65536), Equal.sym(Nat, U32.to_nat(65536), G, eG), h2)

# x <= p and x <= 65536 give x <= min(p, 65536)
def min.ge(+p: U32, +x: Nat, +G: Nat, eG: {U32.to_nat(65536) == G : Nat}, h1: N.Le(x, U32.to_nat(p)), h2: N.Le(x, G)) ->
  N.Le(x, U32.to_nat(Wa.Wasm.min(p, 65536))):
  %min.eq(p) : N.Le(x, U32.to_nat(_))
  min.ge.if(U32.is_le(p, 65536), p, x, G, eG, h1, h2)

# Mem.bytes, as D spells it
def mem.eq(+p: U32) -> {N.D(16n, U32.to_nat(Wa.Wasm.min(p, 65536))) == Mem.bytes(p) : Nat}:
  {==}

# the memory has at most 2^32 bytes: 2^16 pages of 2^16 bytes
def mem.le(+p: U32, +W: Nat, +G: Nat, eG: {U32.to_nat(65536) == G : Nat}, hG: {N.D(16n, G) == W : Nat}) ->
  N.Le(Mem.bytes(p), W):
  +y = U32.to_nat(Wa.Wasm.min(p, 65536))
  N.le_rw_l(N.D(16n, y), Mem.bytes(p), W, mem.eq(p), N.le_rw_r(N.D(16n, y), N.D(16n, G), W, hG, M.D_mono(16n, y, G, min.le(p, G, eG))))

# a memory of p pages has at most 2^16 bytes a page
def mem.le_p(+p: U32) -> N.Le(Mem.bytes(p), N.D(16n, U32.to_nat(p))):
  +y = U32.to_nat(Wa.Wasm.min(p, 65536))
  N.le_rw_l(N.D(16n, y), Mem.bytes(p), N.D(16n, U32.to_nat(p)), mem.eq(p), M.D_mono(16n, y, U32.to_nat(p), min.le_p(p)))

# pages within min(p, 65536) are within the memory
def mem.ge(+p: U32, +x: Nat, h: N.Le(x, U32.to_nat(Wa.Wasm.min(p, 65536)))) -> N.Le(N.D(16n, x), Mem.bytes(p)):
  +y = U32.to_nat(Wa.Wasm.min(p, 65536))
  N.le_rw_r(N.D(16n, x), N.D(16n, y), Mem.bytes(p), mem.eq(p), M.D_mono(16n, x, y, h))

# 2^n, as H.W and as D
def hw.d(+n: Nat) -> {PH.H.W(n) == N.D(n, PH.H.bn(True{})) : Nat}:
  {==}

# 2^16 pages of 2^16 bytes are 2^32 bytes
def w32() -> {N.D(16n, U32.to_nat(65536)) == PH.H.W(32n) : Nat}:
  %Equal.sym(Nat, U32.to_nat(65536), N.D(16n, 1n), N.val_65536()) : {N.D(16n, _) == PH.H.W(32n) : Nat}
  %Equal.sym(Nat, N.D(16n, N.D(16n, 1n)), N.D(32n, 1n), N.D_add(16n, 16n, 32n, 1n, {==})) : {_ == PH.H.W(32n) : Nat}
  Equal.trans(Nat, N.D(32n, 1n), N.D(32n, PH.H.bn(True{})), PH.H.W(32n), Equal.cong(Nat, Nat, z => N.D(32n, z), 1n, PH.H.bn(True{}), {==}),
    Equal.sym(Nat, PH.H.W(32n), N.D(32n, PH.H.bn(True{})), hw.d(32n)))

# a U32 is below 2^32
def u32.lt(+x: U32, +W: Nat, +hW: {W == PH.H.W(32n) : Nat}) -> N.Le(1n+U32.to_nat(x), W):
  match x:
    case U32{+w}:
      N.le_rw_r(1n+Word.to_nat(32n, w), PH.H.W(32n), W, Equal.sym(Nat, W, PH.H.W(32n), hW), PH.H.bound(32n, w))

# 2 + P <= 2^32
def p.w(+P: Nat, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat}, +W: Nat, +hW: {W == PH.H.W(32n) : Nat}) ->
  N.Le(2n+P, W):
  N.le_rw_r(2n+P, PH.H.W(32n), W, Equal.sym(Nat, W, PH.H.W(32n), hW),
    N.le_rw_r(2n+P, Nat.add(PH.H.W(4n), PH.H.t20(P)), PH.H.W(32n), hP,
      N.le_trans(2n+P, 2n+PH.H.t20(P), Nat.add(PH.H.W(4n), PH.H.t20(P)), PH.H.le_t20(P), N.le_add_l(14n, PH.H.t20(P)))))

# the pages that Cir.room gives, by the branch that it takes, hold its need
def room.need(i: Bool, g: Bool, +p0: U32, +nd: U32, -p: U32, ei: {U32.is_le(nd, p0) == i : Bool},
  e: {Cr.Cir.room.if(i, g, p0, nd) == Some{p} : Maybe<&2, U32>}) -> N.Le(U32.to_nat(nd), U32.to_nat(p)):
  match i g:
    case True{} _:
      %Q.some.inj(p0, p, e) : N.Le(U32.to_nat(nd), U32.to_nat(_))
      Z.le.of(nd, p0, ei)
    case False{} True{}:
      %Q.some.inj(nd, p, e) : N.Le(U32.to_nat(nd), U32.to_nat(_))
      N.le_refl(U32.to_nat(nd))
    case False{} False{}:
      Empty.absurd(N.Le(U32.to_nat(nd), U32.to_nat(p)), Q.none.some(p, e))

# the memory that Cir.room gives for the byte b holds it: 1 + b bytes,
# within the 2^16 pages that 32-bit addresses reach
def room.le(+b: U32, +p0: U32, +lim: U32, +p: U32, e: {Cr.Cir.room(b, p0, lim) == Some{p} : Maybe<&2, U32>},
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +G: Nat, +eG: {U32.to_nat(65536) == G : Nat}, +hG: {N.D(16n, G) == W : Nat},
  +P: Nat, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat}) -> N.Le(1n+U32.to_nat(b), Mem.bytes(p)):
  +B = U32.to_nat(b)
  +sh = U32.shrn(b, 16n)
  +SH = U32.to_nat(sh)
  +nd = U32.inc(sh)
  +hB = u32.lt(b, W, hW)
  +hsh = V.shrn.le(16n, b)
  +en = F.inc.nat(sh, W, hW, AE.s2w(SH, B, W, hsh, hB, F.w16(P, hP, W, hW)))
  +e1 = Equal.sym(Nat, U32.to_nat(nd), 1n+SH, en)
  +h65 = V.dlt(16n, SH, G, N.le_rw_r(1n+N.D(16n, SH), W, N.D(16n, G), Equal.sym(Nat, N.D(16n, G), W, hG),
    N.le_trans(1n+N.D(16n, SH), 1n+B, W, hsh, hB)))
  +hp = room.need(U32.is_le(nd, p0), U32.is_le(nd, lim), p0, nd, p, {==}, e)
  +hm = min.ge(p, U32.to_nat(nd), G, eG, hp, N.le_rw_l(1n+SH, U32.to_nat(nd), G, e1, h65))
  +hup = {(%e1 : N.Le(1n+B, N.D(16n, _)); AE.shrn.up(16n, b)) : N.Le(1n+B, N.D(16n, U32.to_nat(nd)))}
  N.le_trans(1n+B, N.D(16n, U32.to_nat(nd)), Mem.bytes(p), hup, mem.ge(p, U32.to_nat(nd), hm))

# The host's check
# ----------------

# a <= b splits: a < b, or a = b
def le.split.up(+p: Nat, +q: Nat, r: Either<&2, &2, N.Le(1n+p, q), {p == q : Nat}>) ->
  Either<&2, &2, N.Le(2n+p, 1n+q), {1n+p == 1n+q : Nat}>:
  match r:
    case Inl{x}:
      Inl{x}
    case Inr{e}:
      Inr{Equal.cong(Nat, Nat, z => 1n+z, p, q, e)}

def le.split(+a: Nat, +b: Nat, h: N.Le(a, b)) -> Either<&2, &2, N.Le(1n+a, b), {a == b : Nat}>:
  match a b:
    case 0n 0n:
      Inr{{==}}
    case 0n 1n+q:
      Inl{N.le_zero(q)}
    case 1n+p 0n:
      Empty.absurd(Either<&2, &2, N.Le(2n+p, 0n), {1n+p == 0n : Nat}>, h)
    case 1n+p 1n+q:
      le.split.up(p, q, le.split(p, q, h))

def zero.rel(c: Cmp, -x: Nat, r: N.Rel(c, x, U32.to_nat(0)), e: {x == 0n : Nat}) -> {Cmp.is_eq(c) == True{} : Bool}:
  match c:
    case LT{}:
      Empty.absurd({False{} == True{} : Bool}, r)
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({False{} == True{} : Bool}, (%e : N.Le(1n+U32.to_nat(0), _); r))

# a U32 whose number is 0 is 0
def zero.to(+a: U32, e: {U32.to_nat(a) == 0n : Nat}) -> {U32.is_zero(a) == True{} : Bool}:
  zero.rel(U32.cmp(a, 0), U32.to_nat(a), N.U32.rel(a, 0), e)

# the end, below 2^32: the test of its last byte's page
def fits.end.lt(z: Bool, +p: U32, +E: U32, +ez: {U32.is_zero(E) == z : Bool}, h: N.Le(U32.to_nat(E), Mem.bytes(p))) ->
  {Wa.Wasm.fits.end(False{}, p, E) == True{} : Bool}:
  match z:
    case True{}:
      %Equal.sym(Bool, U32.is_zero(E), True{}, ez) : {Bool.or(_, U32.is_lt(U32.shrn(U32.sub(E, 1), 16n), p)) == True{} : Bool}
      {==}
    case False{}:
      +d = U32.sub(E, 1)
      +sh = U32.shrn(d, 16n)
      +h1 = Z.nz.of(E, ez)
      +hd = N.le_rw_l(U32.to_nat(E), 1n+U32.to_nat(d), N.D(16n, U32.to_nat(p)), Equal.sym(Nat, 1n+U32.to_nat(d), U32.to_nat(E), Z.dec.nat(E, h1)),
        N.le_trans(U32.to_nat(E), Mem.bytes(p), N.D(16n, U32.to_nat(p)), h, mem.le_p(p)))
      +c3 = Z.lt.to(sh, p, V.dlt(16n, U32.to_nat(sh), U32.to_nat(p),
        N.le_trans(1n+N.D(16n, U32.to_nat(sh)), 1n+U32.to_nat(d), N.D(16n, U32.to_nat(p)), V.shrn.le(16n, d), hd)))
      %Equal.sym(Bool, U32.is_zero(E), False{}, ez) : {Bool.or(_, U32.is_lt(sh, p)) == True{} : Bool}
      %Equal.sym(Bool, U32.is_lt(sh, p), True{}, c3) : {Bool.or(False{}, _) == True{} : Bool}
      {==}

# len bytes from a that end below 2^32, in the memory: they fit
def wasm.fits.lt(+p: U32, +a: U32, +l: U32, +h: N.Le(Nat.add(U32.to_nat(a), U32.to_nat(l)), Mem.bytes(p)),
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, hS: N.Le(1n+Nat.add(U32.to_nat(a), U32.to_nat(l)), W)) ->
  {Wa.Wasm.fits(p, a, l) == True{} : Bool}:
  +E = U32.add(a, l)
  +S = Nat.add(U32.to_nat(a), U32.to_nat(l))
  +eE = Z.u32.add_ex(a, l, W, hW, hS)
  +c1 = Z.nlt.of(E, a, N.le_rw_r(U32.to_nat(a), S, U32.to_nat(E), Equal.sym(Nat, U32.to_nat(E), S, eE), N.le_add_r(U32.to_nat(a), U32.to_nat(l))))
  %Equal.sym(Bool, U32.is_lt(E, a), False{}, c1) : {Wa.Wasm.fits.end(_, p, E) == True{} : Bool}
  fits.end.lt(U32.is_zero(E), p, E, {==}, N.le_rw_l(S, U32.to_nat(E), Mem.bytes(p), Equal.sym(Nat, U32.to_nat(E), S, eE), h))

# V + W = W gives V = 0
def add.w0(V: Nat, +W: Nat, e: {Nat.add(V, W) == W : Nat}) -> {V == 0n : Nat}:
  match V:
    case 0n:
      {==}
    case 1n+q:
      Empty.absurd({1n+q == 0n : Nat}, N.not_succ_le(W, N.le_rw_r(1n+W, 1n+Nat.add(q, W), W, e, N.le_add_l(q, W))))

# a sum of exactly 2^32, by its carry out: it wraps to 0
def add.top.go(o: Bool, +V: Nat, -X: Nat, +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, e: {Nat.add(V, N.D(32n, PH.H.bn(o))) == X : Nat},
  eS: {X == W : Nat}, hV: N.Le(1n+V, W)) -> {V == 0n : Nat}:
  match o:
    case False{}:
      +eV = Equal.trans(Nat, V, Nat.add(V, N.D(32n, 0n)), W, PH.H.noc.z(32n, V), Equal.trans(Nat, Nat.add(V, N.D(32n, 0n)), X, W, e, eS))
      Empty.absurd({V == 0n : Nat}, N.not_succ_le(V, N.le_rw_r(1n+V, W, V, Equal.sym(Nat, V, W, eV), hV)))
    case True{}:
      add.w0(V, W, Equal.trans(Nat, Nat.add(V, W), X, W,
        Equal.trans(Nat, Nat.add(V, W), Nat.add(V, N.D(32n, PH.H.bn(True{}))), X,
          Equal.cong(Nat, Nat, z => Nat.add(V, z), W, N.D(32n, PH.H.bn(True{})), Equal.trans(Nat, W, PH.H.W(32n), N.D(32n, PH.H.bn(True{})), hW, hw.d(32n))),
          e), eS))

# a + l = 2^32 wraps to 0
def add.top(+a: U32, +l: U32, +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, eS: {Nat.add(U32.to_nat(a), U32.to_nat(l)) == W : Nat}) ->
  {U32.to_nat(U32.add(a, l)) == 0n : Nat}:
  match a l:
    case U32{+aw} U32{+lw}:
      add.top.go(PH.H.cout(32n, aw, lw, False{}), Word.to_nat(32n, Word.add(32n, aw, lw)), Nat.add(Word.to_nat(32n, aw), Word.to_nat(32n, lw)),
        W, hW, PH.H.adc(32n, aw, lw, False{}), eS, u32.lt(U32{Word.add(32n, aw, lw)}, W, hW))

# a + l = 2^32 with l below 2^32: a is not 0
def top.pos(+A: Nat, +L: Nat, +W: Nat, eS: {Nat.add(A, L) == W : Nat}, hL: N.Le(1n+L, W)) -> N.Le(1n, A):
  match A:
    case 0n:
      Empty.absurd(N.Le(1n, 0n), N.not_succ_le(L, N.le_rw_r(1n+L, W, L, Equal.sym(Nat, L, W, eS), hL)))
    case 1n+q:
      N.le_zero(q)

# a memory of 2^32 bytes has 2^16 pages
def full.if(b: Bool, +p: U32, e: {U32.is_le(65536, p) == b : Bool}, +W: Nat, +G: Nat, +eG: {U32.to_nat(65536) == G : Nat},
  +hG: {N.D(16n, G) == W : Nat}, h: N.Le(W, Mem.bytes(p))) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      +PG = U32.to_nat(p)
      +hp = N.le_trans(1n+N.D(16n, PG), N.D(16n, 1n+PG), N.D(16n, G), Z.D.succ(16n, PG),
        M.D_mono(16n, 1n+PG, G, N.le_rw_r(1n+PG, U32.to_nat(65536), G, eG, AE.nle.u32(65536, p, e))))
      +hw = N.le_trans(1n+W, 1n+N.D(16n, PG), N.D(16n, G), N.le_trans(W, Mem.bytes(p), N.D(16n, PG), h, mem.le_p(p)), hp)
      Empty.absurd({False{} == True{} : Bool}, N.not_succ_le(W, N.le_rw_r(1n+W, N.D(16n, G), W, hG, hw)))

# len bytes from a that end at 2^32 exactly, in the memory: they fit, as
# the end wraps to 0 and the memory has 2^16 pages
def wasm.fits.top(+p: U32, +a: U32, +l: U32, +h: N.Le(Nat.add(U32.to_nat(a), U32.to_nat(l)), Mem.bytes(p)),
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +G: Nat, +eG: {U32.to_nat(65536) == G : Nat}, +hG: {N.D(16n, G) == W : Nat},
  +eS: {Nat.add(U32.to_nat(a), U32.to_nat(l)) == W : Nat}) -> {Wa.Wasm.fits(p, a, l) == True{} : Bool}:
  +E = U32.add(a, l)
  +e0 = add.top(a, l, W, hW, eS)
  +ha = top.pos(U32.to_nat(a), U32.to_nat(l), W, eS, u32.lt(l, W, hW))
  +c1 = Z.lt.to(E, a, N.le_rw_l(1n, 1n+U32.to_nat(E), U32.to_nat(a),
    Equal.cong(Nat, Nat, z => 1n+z, 0n, U32.to_nat(E), Equal.sym(Nat, U32.to_nat(E), 0n, e0)), ha))
  %Equal.sym(Bool, U32.is_lt(E, a), True{}, c1) : {Wa.Wasm.fits.end(_, p, E) == True{} : Bool}
  %Equal.sym(Bool, U32.is_zero(E), True{}, zero.to(E, e0)) : {Bool.and(_, U32.is_le(65536, p)) == True{} : Bool}
  full.if(U32.is_le(65536, p), p, {==}, W, G, eG, hG, N.le_rw_l(Nat.add(U32.to_nat(a), U32.to_nat(l)), W, Mem.bytes(p), eS, h))

def wasm.fits.cases(+p: U32, +a: U32, +l: U32, +h: N.Le(Nat.add(U32.to_nat(a), U32.to_nat(l)), Mem.bytes(p)),
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +G: Nat, +eG: {U32.to_nat(65536) == G : Nat}, +hG: {N.D(16n, G) == W : Nat},
  s: Either<&2, &2, N.Le(1n+Nat.add(U32.to_nat(a), U32.to_nat(l)), W), {Nat.add(U32.to_nat(a), U32.to_nat(l)) == W : Nat}>) ->
  {Wa.Wasm.fits(p, a, l) == True{} : Bool}:
  match s:
    case Inl{hS}:
      wasm.fits.lt(p, a, l, h, W, hW, hS)
    case Inr{eS}:
      wasm.fits.top(p, a, l, h, W, hW, G, eG, hG, eS)

# len bytes from a fit in the memory of p pages, as the host checks it,
# when a + len, as an integer, is at most its bytes
def wasm.fits.of(+p: U32, +a: U32, +l: U32, +h: N.Le(Nat.add(U32.to_nat(a), U32.to_nat(l)), Mem.bytes(p)),
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +G: Nat, +eG: {U32.to_nat(65536) == G : Nat}, +hG: {N.D(16n, G) == W : Nat}) ->
  {Wa.Wasm.fits(p, a, l) == True{} : Bool}:
  +S = Nat.add(U32.to_nat(a), U32.to_nat(l))
  wasm.fits.cases(p, a, l, h, W, hW, G, eG, hG, le.split(S, W, N.le_trans(S, Mem.bytes(p), W, h, mem.le(p, W, G, eG, hG))))

# Fits gives next <= P: 20 × next does not wrap
def fits.nx(+nx: U32, +pg: U32, +on: U32, h: Fits.of(nx, pg, on), +W: Nat, +hW: {W == PH.H.W(32n) : Nat},
  +G: Nat, +eG: {U32.to_nat(65536) == G : Nat}, +hG: {N.D(16n, G) == W : Nat},
  +P: Nat, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat}) -> N.Le(U32.to_nat(nx), P):
  +T = PH.H.t20(U32.to_nat(nx))
  +h1 = N.le_trans(T, Mem.bytes(pg), W, N.le_trans(T, Nat.add(T, U32.to_nat(on)), Mem.bytes(pg), N.le_add_r(T, U32.to_nat(on)), h),
    mem.le(pg, W, G, eG, hG))
  +h2 = N.le_rw_r(T, W, Nat.add(PH.H.W(4n), PH.H.t20(P)), Equal.trans(Nat, W, PH.H.W(32n), Nat.add(PH.H.W(4n), PH.H.t20(P)), hW,
    Equal.sym(Nat, Nat.add(PH.H.W(4n), PH.H.t20(P)), PH.H.W(32n), hP)), h1)
  PH.H.t20_lt(U32.to_nat(nx), 1n+P, N.le_trans(1n+T, 1n+Nat.add(PH.H.W(4n), PH.H.t20(P)), PH.H.t20(1n+P), h2, N.le_add_l(3n, PH.H.t20(P))))

# Fits is the host's check of the output at halt 0, as Cir.ended makes it:
# 20 next + outn <= 2^32 needs next <= 214748364, so 20 × next does not wrap
def fits.wasm(+nx: U32, +pg: U32, +on: U32, +h: Fits.of(nx, pg, on)) ->
  {Wa.Wasm.fits(pg, Cr.Cir.at(nx), on) == True{} : Bool}:
  +W = PH.H.W(32n)
  +G = U32.to_nat(65536)
  +P = PH.H.pat(7n)
  +T = PH.H.t20(U32.to_nat(nx))
  +A = U32.to_nat(Cr.Cir.at(nx))
  +ea = F.at.nat(nx, P, PH.H.hP(), fits.nx(nx, pg, on, h, W, {==}, G, {==}, w32(), P, PH.H.hP()))
  wasm.fits.of(pg, Cr.Cir.at(nx), on, N.le_rw_l(Nat.add(T, U32.to_nat(on)), Nat.add(A, U32.to_nat(on)), Mem.bytes(pg),
    Equal.cong(Nat, Nat, z => Nat.add(z, U32.to_nat(on)), T, A, Equal.sym(Nat, A, T, ea)), h), W, {==}, G, {==}, w32())

# The cells and the output after an alloc or an emit
# --------------------------------------------------

# 214748365, one past P
def lit.P1() -> {214748365 == U32.inc(214748364) : U32}:
  {==}

def lit.P1.nat(+P: Nat, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat}, +W: Nat, +hW: {W == PH.H.W(32n) : Nat}) ->
  {U32.to_nat(214748365) == 1n+P : Nat}:
  +eP = AE.lit.P(P, hP)
  +h2 = N.le_rw_l(2n+P, 2n+U32.to_nat(214748364), W,
    Equal.cong(Nat, Nat, z => 2n+z, P, U32.to_nat(214748364), Equal.sym(Nat, U32.to_nat(214748364), P, eP)), p.w(P, hP, W, hW))
  %Equal.sym(U32, 214748365, U32.inc(214748364), lit.P1()) : {U32.to_nat(_) == 1n+P : Nat}
  Equal.trans(Nat, U32.to_nat(U32.inc(214748364)), 1n+U32.to_nat(214748364), 1n+P, F.inc.nat(214748364, W, hW, h2),
    Equal.cong(Nat, Nat, z => 1n+z, U32.to_nat(214748364), P, eP))

# a U32 that is 0 has the number 0
def zero.nat(+a: U32, e: {U32.is_zero(a) == True{} : Bool}) -> {U32.to_nat(a) == 0n : Nat}:
  N.rel_eq(U32.cmp(a, 0), U32.to_nat(a), U32.to_nat(0), N.U32.rel(a, 0), N.toT(U32.is_zero(a), e))

def ge.rel(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), e: {Cmp.is_ge(c) == True{} : Bool}) -> N.Le(y, x):
  match c:
    case LT{}:
      Empty.absurd(N.Le(y, x), N.false_ne_true(e))
    case EQ{}:
      %r : N.Le(_, x)
      N.le_refl(x)
    case GT{}:
      N.weaken(y, x, r)

# a >= b on U32 is b <= a on their numbers
def ge.le(+a: U32, +b: U32, e: {U32.is_ge(a, b) == True{} : Bool}) -> N.Le(U32.to_nat(b), U32.to_nat(a)):
  ge.rel(U32.cmp(a, b), U32.to_nat(a), U32.to_nat(b), N.U32.rel(a, b), e)

# a sum with a carry out is 2^32 more than its word: at least y and below
# 2^32 + y, it carries none
def nowrap.go(c: Bool, +V: Nat, +A0: Nat, +B0: Nat, +W: Nat, +hW: {W == PH.H.W(32n) : Nat},
  e: {Nat.add(V, N.D(32n, PH.H.bn(c))) == Nat.add(A0, B0) : Nat}, h: N.Le(B0, V), hA: N.Le(1n+A0, W)) ->
  {V == Nat.add(A0, B0) : Nat}:
  match c:
    case False{}:
      Equal.trans(Nat, V, Nat.add(V, N.D(32n, 0n)), Nat.add(A0, B0), PH.H.noc.z(32n, V), e)
    case True{}:
      +e2 = Equal.trans(Nat, Nat.add(V, W), Nat.add(V, N.D(32n, PH.H.bn(True{}))), Nat.add(A0, B0),
        Equal.cong(Nat, Nat, z => Nat.add(V, z), W, N.D(32n, PH.H.bn(True{})), Equal.trans(Nat, W, PH.H.W(32n), N.D(32n, PH.H.bn(True{})), hW, hw.d(32n))), e)
      +l1 = N.le_rw_r(Nat.add(B0, W), Nat.add(V, W), Nat.add(A0, B0), e2, N.add_mono(B0, V, W, W, h, N.le_refl(W)))
      +l2 = N.le_rw_r(1n+Nat.add(A0, B0), Nat.add(W, B0), Nat.add(B0, W), Z.add.comm(W, B0), N.add_mono(1n+A0, W, B0, B0, hA, N.le_refl(B0)))
      Empty.absurd({V == Nat.add(A0, B0) : Nat}, N.not_succ_le(Nat.add(A0, B0), N.le_trans(1n+Nat.add(A0, B0), Nat.add(B0, W), Nat.add(A0, B0), l2, l1)))

# x + y whose word is at least y does not wrap: it is exact
def add.nowrap(+x: U32, +y: U32, h: N.Le(U32.to_nat(y), U32.to_nat(U32.add(x, y))), +W: Nat, +hW: {W == PH.H.W(32n) : Nat}) ->
  {U32.to_nat(U32.add(x, y)) == Nat.add(U32.to_nat(x), U32.to_nat(y)) : Nat}:
  match x y:
    case U32{+xw} U32{+yw}:
      nowrap.go(PH.H.cout(32n, xw, yw, False{}), Word.to_nat(32n, Word.add(32n, xw, yw)), Word.to_nat(32n, xw), Word.to_nat(32n, yw),
        W, hW, PH.H.adc(32n, xw, yw, False{}), h, u32.lt(U32{xw}, W, hW))

# an alloc that goes on: its cell next, below P, ends at 20 (next + 1), in
# the pages that Cir.room gave for its last byte; the output is empty
def alloc.room(+nx: U32, +pg: U32, +lm: U32, +on: U32, +p: U32,
  ez: {U32.is_zero(on) == True{} : Bool}, el: {U32.is_lt(nx, 214748364) == True{} : Bool},
  e: {Cr.Cir.room(U32.add(Cr.Cir.at(nx), 19), pg, lm) == Some{p} : Maybe<&2, U32>},
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +G: Nat, +eG: {U32.to_nat(65536) == G : Nat}, +hG: {N.D(16n, G) == W : Nat},
  +P: Nat, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat}) -> Fits.of(U32.inc(nx), p, on):
  +X = U32.to_nat(nx)
  +T = PH.H.t20(X)
  +b = U32.add(Cr.Cir.at(nx), 19)
  +hnx = N.le_rw_r(1n+X, U32.to_nat(214748364), P, AE.lit.P(P, hP), Z.lt.of(nx, 214748364, el))
  +h20 = N.le_rw_l(1n+U32.to_nat(b), 20n+T, Mem.bytes(p),
    Equal.cong(Nat, Nat, z => 1n+z, U32.to_nat(b), 19n+T, AE.room.b(nx, P, hP, W, hW, hnx)), room.le(b, pg, lm, p, e, W, hW, G, eG, hG, P, hP))
  +einc = F.inc.nat(nx, W, hW, N.le_trans(2n+X, 1n+P, W, hnx, N.weaken(1n+P, W, p.w(P, hP, W, hW))))
  +e1 = {(%Equal.sym(Nat, U32.to_nat(U32.inc(nx)), 1n+X, einc) : {Nat.add(PH.H.t20(_), U32.to_nat(on)) == 20n+T : Nat};
      %Equal.sym(Nat, U32.to_nat(on), 0n, zero.nat(on, ez)) : {Nat.add(PH.H.t20(1n+X), _) == 20n+T : Nat};
      N.add_zero(PH.H.t20(1n+X))) : {Nat.add(PH.H.t20(U32.to_nat(U32.inc(nx))), U32.to_nat(on)) == 20n+T : Nat}}
  N.le_rw_l(20n+T, Nat.add(PH.H.t20(U32.to_nat(U32.inc(nx))), U32.to_nat(on)), Mem.bytes(p),
    Equal.sym(Nat, Nat.add(PH.H.t20(U32.to_nat(U32.inc(nx))), U32.to_nat(on)), 20n+T, e1), h20)

# an emit that goes on: its byte, at 20 next + outn, which does not wrap,
# in the pages that Cir.room gave for it
def emit.room(+nx: U32, +on: U32, +pg: U32, +lm: U32, +p: U32,
  +ok: {Bool.and(U32.is_lt(nx, 214748365), U32.is_ge(U32.add(Cr.Cir.at(nx), on), on)) == True{} : Bool},
  e: {Cr.Cir.room(U32.add(Cr.Cir.at(nx), on), pg, lm) == Some{p} : Maybe<&2, U32>},
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +G: Nat, +eG: {U32.to_nat(65536) == G : Nat}, +hG: {N.D(16n, G) == W : Nat},
  +P: Nat, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat}) -> Fits.of(nx, p, U32.inc(on)):
  +X = U32.to_nat(nx)
  +ON = U32.to_nat(on)
  +T = PH.H.t20(X)
  +a = Cr.Cir.at(nx)
  +b = U32.add(a, on)
  +hnx = N.le_rw_r(1n+X, U32.to_nat(214748365), 1n+P, lit.P1.nat(P, hP, W, hW),
    Z.lt.of(nx, 214748365, PH.H.and_l(U32.is_lt(nx, 214748365), U32.is_ge(b, on), ok)))
  +ea = F.at.nat(nx, P, hP, hnx)
  +eb = add.nowrap(a, on, ge.le(b, on, PH.H.and_r(U32.is_lt(nx, 214748365), U32.is_ge(b, on), ok)), W, hW)
  +e3 = Equal.trans(Nat, Nat.add(T, ON), Nat.add(U32.to_nat(a), ON), U32.to_nat(b),
    Equal.cong(Nat, Nat, z => Nat.add(z, ON), T, U32.to_nat(a), Equal.sym(Nat, U32.to_nat(a), T, ea)),
    Equal.sym(Nat, U32.to_nat(b), Nat.add(U32.to_nat(a), ON), eb))
  +e2 = Equal.trans(Nat, Nat.add(T, 1n+ON), 1n+Nat.add(T, ON), 1n+U32.to_nat(b), N.add_succ_r(T, ON),
    Equal.cong(Nat, Nat, z => 1n+z, Nat.add(T, ON), U32.to_nat(b), e3))
  +hs = N.add_mono(T, T, U32.to_nat(U32.inc(on)), 1n+ON, N.le_refl(T), N.U32.inc_le(on))
  N.le_trans(Nat.add(T, U32.to_nat(U32.inc(on))), 1n+U32.to_nat(b), Mem.bytes(p),
    N.le_rw_r(Nat.add(T, U32.to_nat(U32.inc(on))), Nat.add(T, 1n+ON), 1n+U32.to_nat(b), e2, hs),
    room.le(b, pg, lm, p, e, W, hW, G, eG, hG, P, hP))

# The statements
# --------------

def fits.set.of(rs: Maybe<&2, List<&2, U32>>, +st: Cr.Cir.State, h: Fits(st)) -> FitsOut(Cr.Cir.exec.set.of(rs, st)):
  match rs st:
    case Some{x} Cr.Cir.State{rg, cl, nx, fi, im, pg, lm, inp, ou, on}:
      h
    case None{} _:
      Unit{}

# a set keeps next, outn and the pages
def fits.set(r: Nat, v: Maybe<&2, U32>, +st: Cr.Cir.State, h: Fits(st)) -> FitsOut(Cr.Cir.exec.set(r, v, st)):
  match v st:
    case Some{x} Cr.Cir.State{rg, cl, nx, fi, im, pg, lm, inp, ou, on}:
      fits.set.of(Cr.Cir.regs.set(rg, r, x), st, h)
    case None{} _:
      Unit{}

def fits.store.if(ok: Bool, k: Nat, +i: U32, v: U32, +st: Cr.Cir.State, h: Fits(st)) -> FitsOut(Cr.Cir.exec.store.if(ok, k, i, v, st)):
  match ok st:
    case True{} Cr.Cir.State{rg, cl, nx, fi, im, pg, lm, inp, ou, on}:
      h
    case False{} _:
      Unit{}

# a store keeps next, outn and the pages
def fits.store(k: Nat, c: Maybe<&2, U32>, v: Maybe<&2, U32>, +st: Cr.Cir.State, h: Fits(st)) ->
  FitsOut(Cr.Cir.exec.store(k, c, v, st)):
  match c v st:
    case Some{+i} Some{x} Cr.Cir.State{rg, cl, +nx, +fi, +im, pg, lm, inp, ou, on}:
      fits.store.if(Cr.Cir.is_cell(i, im, fi, nx), k, i, x, st, h)
    case Some{i} None{} _:
      Unit{}
    case None{} _ _:
      Unit{}

def fits.bump.of(pm: Maybe<&2, U32>, r: Nat, +rg: List<&2, U32>, +cl: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, Word(8n)>, +ou: List<&2, Word(8n)>, +on: U32, ez: {U32.is_zero(on) == True{} : Bool},
  el: {U32.is_lt(nx, 214748364) == True{} : Bool}, e: {Cr.Cir.room(U32.add(Cr.Cir.at(nx), 19), pg, lm) == pm : Maybe<&2, U32>}) ->
  FitsOut(Cr.Cir.exec.bump.of(r, nx, Cr.Cir.State{rg, cl, nx, fi, im, pg, lm, inp, ou, on}, pm)):
  match pm:
    case Some{+p}:
      fits.set(r, Some{nx}, Cr.Cir.State{rg, Cr.Cir.Cells.set(cl, nx, Cr.Cir.Cell.zero()), U32.inc(nx), fi, im, p, lm, inp, ou, on},
        alloc.room(nx, pg, lm, on, p, ez, el, e, PH.H.W(32n), {==}, U32.to_nat(65536), {==}, w32(), PH.H.pat(7n), PH.H.hP()))
    case None{}:
      Unit{}

def fits.bump.if(c: Bool, r: Nat, +rg: List<&2, U32>, +cl: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, Word(8n)>, +ou: List<&2, Word(8n)>, +on: U32, ez: {U32.is_zero(on) == True{} : Bool},
  el: {U32.is_lt(nx, 214748364) == c : Bool}) ->
  FitsOut(Cr.Cir.exec.bump.if(c, r, nx, pg, lm, Cr.Cir.State{rg, cl, nx, fi, im, pg, lm, inp, ou, on})):
  match c:
    case True{}:
      fits.bump.of(Cr.Cir.room(U32.add(Cr.Cir.at(nx), 19), pg, lm), r, rg, cl, nx, fi, im, pg, lm, inp, ou, on, ez, el, {==})
    case False{}:
      Unit{}

def fits.alloc.if(z: Bool, r: Nat, +rg: List<&2, U32>, +cl: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, Word(8n)>, +ou: List<&2, Word(8n)>, +on: U32, ez: {U32.is_zero(on) == z : Bool}) ->
  FitsOut(Cr.Cir.exec.alloc.if(z, r, Cr.Cir.State{rg, cl, nx, fi, im, pg, lm, inp, ou, on})):
  match z:
    case True{}:
      fits.bump.if(U32.is_lt(nx, 214748364), r, rg, cl, nx, fi, im, pg, lm, inp, ou, on, ez, {==})
    case False{}:
      Unit{}

# an alloc that goes on gives Fits whatever held before: it takes no cell
# once the output began (outn = 0 after it), and the pages that it leaves
# hold its cell, the bytes up to 20 (next + 1)
def fits.alloc(r: Nat, +st: Cr.Cir.State) -> FitsOut(Cr.Cir.exec.alloc(r, st)):
  match st:
    case Cr.Cir.State{rg, cl, nx, fi, im, pg, lm, inp, ou, on}:
      fits.alloc.if(U32.is_zero(on), r, rg, cl, nx, fi, im, pg, lm, inp, ou, on, {==})

def fits.emit.of(pm: Maybe<&2, U32>, x: U32, +rg: List<&2, U32>, +cl: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, Word(8n)>, +ou: List<&2, Word(8n)>, +on: U32,
  ok: {Bool.and(U32.is_lt(nx, 214748365), U32.is_ge(U32.add(Cr.Cir.at(nx), on), on)) == True{} : Bool},
  e: {Cr.Cir.room(U32.add(Cr.Cir.at(nx), on), pg, lm) == pm : Maybe<&2, U32>}) ->
  FitsOut(Cr.Cir.exec.emit.of(pm, x, Cr.Cir.State{rg, cl, nx, fi, im, pg, lm, inp, ou, on})):
  match pm:
    case Some{+p}:
      emit.room(nx, on, pg, lm, p, ok, e, PH.H.W(32n), {==}, U32.to_nat(65536), {==}, w32(), PH.H.pat(7n), PH.H.hP())
    case None{}:
      Unit{}

def fits.emit.if(c: Bool, x: U32, +rg: List<&2, U32>, +cl: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, Word(8n)>, +ou: List<&2, Word(8n)>, +on: U32,
  ok: {Bool.and(U32.is_lt(nx, 214748365), U32.is_ge(U32.add(Cr.Cir.at(nx), on), on)) == c : Bool}) ->
  FitsOut(Cr.Cir.exec.emit.if(c, U32.add(Cr.Cir.at(nx), on), x, Cr.Cir.State{rg, cl, nx, fi, im, pg, lm, inp, ou, on})):
  match c:
    case True{}:
      fits.emit.of(Cr.Cir.room(U32.add(Cr.Cir.at(nx), on), pg, lm), x, rg, cl, nx, fi, im, pg, lm, inp, ou, on, ok, {==})
    case False{}:
      Unit{}

# an emit grows the pages to hold its byte, at 20 next + outn
def fits.emit(v: Maybe<&2, U32>, +st: Cr.Cir.State) -> FitsOut(Cr.Cir.exec.emit(v, st)):
  match v st:
    case Some{x} Cr.Cir.State{rg, cl, nx, fi, im, pg, lm, inp, ou, on}:
      fits.emit.if(Bool.and(U32.is_lt(nx, 214748365), U32.is_ge(U32.add(Cr.Cir.at(nx), on), on)), x, rg, cl, nx, fi, im, pg, lm, inp, ou, on, {==})
    case None{} _:
      Unit{}

# a then the rest: the rest keeps what a's outcome gives
def fits.then(o: Cr.Cir.Out, -k: Cr.Cir.State -> Cr.Cir.Out, ho: FitsOut(o), hk: @t: Cr.Cir.State -> Fits(t) -> FitsOut(k(t))) ->
  FitsOut(Cr.Cir.exec.then(o, k)):
  match o:
    case Cr.Cir.Out.next{st}:
      hk(st, ho)
    case Cr.Cir.Out.halt{s, st}:
      ho
    case Cr.Cir.Out.out_of_memory{}:
      Unit{}
    case Cr.Cir.Out.trap{}:
      Unit{}
    case Cr.Cir.Out.not_done{}:
      Unit{}

def fits.if.of(z: Bool, -yes: Unit -> Cr.Cir.Out, -no: Unit -> Cr.Cir.Out, hy: FitsOut(yes(Unit{})), hn: FitsOut(no(Unit{}))) ->
  FitsOut(Cr.Cir.exec.if.of(z, yes, no)):
  match z:
    case False{}:
      hy
    case True{}:
      hn

# an if: both of its branches keep Fits
def fits.if(c: Maybe<&2, U32>, -yes: Unit -> Cr.Cir.Out, -no: Unit -> Cr.Cir.Out, hy: FitsOut(yes(Unit{})), hn: FitsOut(no(Unit{}))) ->
  FitsOut(Cr.Cir.exec.if(c, yes, no)):
  match c:
    case Some{x}:
      fits.if.of(U32.is_zero(x), yes, no, hy, hn)
    case None{}:
      Unit{}

# every statement keeps Fits, with any fuel: set, store, nop and halt change
# none of next, outn and pages; an alloc gives it (fits.alloc); an emit grows
# the pages to hold its byte, at 20 next + outn
def fits.exec(+f: Nat, s: Cr.Cir.Stmt, +st: Cr.Cir.State, +h: Fits(st)) -> FitsOut(Cr.Cir.exec(f, s, st)):
  match f s:
    case _ Cr.Cir.Stmt.nop{}:
      h
    case _ Cr.Cir.Stmt.set{r, e}:
      fits.set(r, Cr.Cir.eval(e, st), st, h)
    case _ Cr.Cir.Stmt.store{k, c, v}:
      fits.store(k, Cr.Cir.eval(c, st), Cr.Cir.eval(v, st), st, h)
    case _ Cr.Cir.Stmt.alloc{r}:
      fits.alloc(r, st)
    case _ Cr.Cir.Stmt.emit{v}:
      fits.emit(Cr.Cir.eval(v, st), st)
    case _ Cr.Cir.Stmt.seq{+a, +b}:
      fits.then(Cr.Cir.exec(f, a, st), t => Cr.Cir.exec(f, b, t), fits.exec(f, a, st, h), t => ht => fits.exec(f, b, t, ht))
    case _ Cr.Cir.Stmt.if{c, +t, +e}:
      fits.if(Cr.Cir.eval(c, st), u => Cr.Cir.exec(f, t, st), u => Cr.Cir.exec(f, e, st), fits.exec(f, t, st, h), fits.exec(f, e, st, h))
    case 0n Cr.Cir.Stmt.while{_, _}:
      Unit{}
    case 1n+g Cr.Cir.Stmt.while{+c, +body}:
      fits.if(Cr.Cir.eval(c, st),
        u => Cr.Cir.exec.then(Cr.Cir.exec(g, body, st), t => Cr.Cir.exec(g, Cr.Cir.Stmt.while{c, body}, t)),
        u => Cr.Cir.Out.next{st},
        fits.then(Cr.Cir.exec(g, body, st), t => Cr.Cir.exec(g, Cr.Cir.Stmt.while{c, body}, t), fits.exec(g, body, st, h),
          t => ht => fits.exec(g, Cr.Cir.Stmt.while{c, body}, t, ht)),
        h)
    case _ Cr.Cir.Stmt.halt{_}:
      h

# M.input
# -------
#
# M.input runs from a state with no cell to reuse: it sets no pend
# register, so each M.alloc of it finds pend at 0 and takes a new cell, by
# Cir's alloc; and it never halts. Keeps checks this of a statement, and Fit
# says that the state after it fits: when it fit before, or the statement
# surely takes a cell (an alloc) or grows the memory for a byte (an emit).
# keeps.ok proves the check right, for every statement; M.input passes it.

# the test c is 0 when the pend register holds 0: a comparison of pend with
# a constant that gives 0 for it
def Pz.op(o: Wa.Wasm.Op, a: Cr.Cir.Expr, b: Cr.Cir.Expr) -> Bool:
  match a b:
    case Cr.Cir.Expr.get{r} Cr.Cir.Expr.const{n}:
      Bool.and(Nat.is_eq(r, Mc.R.pend()), U32.is_zero(Wa.Wasm.op(o, 0, n)))
    case _ _:
      False{}

def Pz(c: Cr.Cir.Expr) -> Bool:
  match c:
    case Cr.Cir.Expr.op{o, a, b}:
      Pz.op(o, a, b)
    case _:
      False{}

# s keeps the cells new: it sets no pend register, takes no cell into it,
# and never halts; an if whose test is 0 when pend holds 0 runs its else
def Keeps(s: Cr.Cir.Stmt) -> Bool:
  match s:
    case Cr.Cir.Stmt.set{r, _}:
      Bool.not(Nat.is_eq(r, Mc.R.pend()))
    case Cr.Cir.Stmt.alloc{r}:
      Bool.not(Nat.is_eq(r, Mc.R.pend()))
    case Cr.Cir.Stmt.seq{a, b}:
      Bool.and(Keeps(a), Keeps(b))
    case Cr.Cir.Stmt.if{c, t, e}:
      Bool.and(Bool.or(Pz(c), Keeps(t)), Keeps(e))
    case Cr.Cir.Stmt.while{_, body}:
      Keeps(body)
    case Cr.Cir.Stmt.halt{_}:
      False{}
    case _:
      True{}

# the state after s fits: it fit before (m), or s surely takes a cell or
# grows the memory for a byte
def Fit(s: Cr.Cir.Stmt, +m: Bool) -> Bool:
  match s:
    case Cr.Cir.Stmt.alloc{_}:
      True{}
    case Cr.Cir.Stmt.emit{_}:
      True{}
    case Cr.Cir.Stmt.seq{a, b}:
      Fit(b, Fit(a, m))
    case Cr.Cir.Stmt.if{c, t, e}:
      Bool.and(Bool.or(Pz(c), Fit(t, m)), Fit(e, m))
    case _:
      m

# the cells stay new, and the state fits when m
def Kept(m: Bool, +st: Cr.Cir.State) -> Data:
  match m:
    case True{}:
      S.P2(NewCells(st), Fits(st))
    case False{}:
      NewCells(st)

# what an outcome keeps: Kept of the state after it; never a halt
def KeptOut(m: Bool, o: Cr.Cir.Out) -> Data:
  match o:
    case Cr.Cir.Out.next{st}:
      Kept(m, st)
    case Cr.Cir.Out.halt{_, _}:
      Empty
    case _:
      Unit

def kept.new(+m: Bool, -st: Cr.Cir.State, h: Kept(m, st)) -> NewCells(st):
  match m:
    case True{}:
      (a, b) = h
      a
    case False{}:
      h

def kept.and_l(+x: Bool, +y: Bool, -st: Cr.Cir.State, h: Kept(x, st)) -> Kept(Bool.and(x, y), st):
  match x y:
    case True{} True{}:
      h
    case True{} False{}:
      kept.new(True{}, st, h)
    case False{} _:
      h

def kept.and_r(+x: Bool, +y: Bool, -st: Cr.Cir.State, h: Kept(y, st)) -> Kept(Bool.and(x, y), st):
  match x:
    case True{}:
      h
    case False{}:
      kept.new(y, st, h)

def kept.out_l(+x: Bool, +y: Bool, o: Cr.Cir.Out, h: KeptOut(x, o)) -> KeptOut(Bool.and(x, y), o):
  match o:
    case Cr.Cir.Out.next{st}:
      kept.and_l(x, y, st, h)
    case Cr.Cir.Out.halt{s, st}:
      match h:
    case Cr.Cir.Out.out_of_memory{}:
      Unit{}
    case Cr.Cir.Out.trap{}:
      Unit{}
    case Cr.Cir.Out.not_done{}:
      Unit{}

def kept.out_r(+x: Bool, +y: Bool, o: Cr.Cir.Out, h: KeptOut(y, o)) -> KeptOut(Bool.and(x, y), o):
  match o:
    case Cr.Cir.Out.next{st}:
      kept.and_r(x, y, st, h)
    case Cr.Cir.Out.halt{s, st}:
      match h:
    case Cr.Cir.Out.out_of_memory{}:
      Unit{}
    case Cr.Cir.Out.trap{}:
      Unit{}
    case Cr.Cir.Out.not_done{}:
      Unit{}

# an outcome that keeps the cells new and fits keeps both
def kept.both(o: Cr.Cir.Out, hn: KeptOut(False{}, o), hf: FitsOut(o)) -> KeptOut(True{}, o):
  match o:
    case Cr.Cir.Out.next{st}:
      (hn, hf)
    case Cr.Cir.Out.halt{s, st}:
      match hn:
    case Cr.Cir.Out.out_of_memory{}:
      Unit{}
    case Cr.Cir.Out.trap{}:
      Unit{}
    case Cr.Cir.Out.not_done{}:
      Unit{}

# a state whose registers change, but not pend's 0, keeps Kept
def kept.regs(+m: Bool, -rg: List<&2, U32>, +rs: List<&2, U32>, +cl: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32,
  +lm: U32, +inp: List<&2, Word(8n)>, +ou: List<&2, Word(8n)>, +on: U32,
  en: {List.get(&2, U32, rs, Mc.R.pend()) == Some{0} : Maybe<&2, U32>},
  h: Kept(m, Cr.Cir.State{rg, cl, nx, fi, im, pg, lm, inp, ou, on})) -> Kept(m, Cr.Cir.State{rs, cl, nx, fi, im, pg, lm, inp, ou, on}):
  match m:
    case True{}:
      (a, b) = h
      (en, b)
    case False{}:
      en

def kept.set.if(b: Bool, +m: Bool, +r: Nat, +x: U32, +rg: List<&2, U32>, +cl: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32,
  +lm: U32, +inp: List<&2, Word(8n)>, +ou: List<&2, Word(8n)>, +on: U32, hr: {Nat.is_eq(r, Mc.R.pend()) == False{} : Bool},
  +h: Kept(m, Cr.Cir.State{rg, cl, nx, fi, im, pg, lm, inp, ou, on})) ->
  KeptOut(m, Cr.Cir.exec.set.of(Cr.Cir.regs.set.if(b, rg, r, x), Cr.Cir.State{rg, cl, nx, fi, im, pg, lm, inp, ou, on})):
  match b:
    case True{}:
      kept.regs(m, rg, List.set(&2, U32, rg, r, x), cl, nx, fi, im, pg, lm, inp, ou, on,
        X.L.go(rg, r, Mc.R.pend(), x, 0, hr, kept.new(m, Cr.Cir.State{rg, cl, nx, fi, im, pg, lm, inp, ou, on}, h)), h)
    case False{}:
      Unit{}

# a set of a register other than pend keeps the cells new, and Fits
def kept.set(+m: Bool, +r: Nat, v: Maybe<&2, U32>, +st: Cr.Cir.State, hr: {Nat.is_eq(r, Mc.R.pend()) == False{} : Bool},
  +h: Kept(m, st)) -> KeptOut(m, Cr.Cir.exec.set(r, v, st)):
  match v st:
    case Some{x} Cr.Cir.State{rg, cl, nx, fi, im, pg, lm, inp, ou, on}:
      kept.set.if(Nat.is_lt(r, List.length(&2, U32, rg)), m, r, x, rg, cl, nx, fi, im, pg, lm, inp, ou, on, hr, h)
    case None{} _:
      Unit{}

# a state whose cells change keeps Kept
def kept.cells(+m: Bool, +rg: List<&2, U32>, -cl: Cr.Cir.Cells, -c2: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32,
  +lm: U32, +inp: List<&2, Word(8n)>, +ou: List<&2, Word(8n)>, +on: U32,
  h: Kept(m, Cr.Cir.State{rg, cl, nx, fi, im, pg, lm, inp, ou, on})) -> Kept(m, Cr.Cir.State{rg, c2, nx, fi, im, pg, lm, inp, ou, on}):
  match m:
    case True{}:
      (a, b) = h
      (a, b)
    case False{}:
      h

def kept.store.if(ok: Bool, k: Nat, +i: U32, v: U32, +m: Bool, +st: Cr.Cir.State, h: Kept(m, st)) ->
  KeptOut(m, Cr.Cir.exec.store.if(ok, k, i, v, st)):
  match ok st:
    case True{} Cr.Cir.State{rg, cl, nx, fi, im, pg, lm, inp, ou, on}:
      kept.cells(m, rg, cl, Cr.Cir.Cells.set(cl, i, Cr.Cir.Cell.set(k, Cr.Cir.Cells.get(cl, i), v)), nx, fi, im, pg, lm, inp, ou, on, h)
    case False{} _:
      Unit{}

# a store keeps the registers, next, outn and the pages
def kept.store(+m: Bool, k: Nat, c: Maybe<&2, U32>, v: Maybe<&2, U32>, +st: Cr.Cir.State, h: Kept(m, st)) ->
  KeptOut(m, Cr.Cir.exec.store(k, c, v, st)):
  match c v st:
    case Some{+i} Some{x} Cr.Cir.State{rg, cl, +nx, +fi, +im, pg, lm, inp, ou, on}:
      kept.store.if(Cr.Cir.is_cell(i, im, fi, nx), k, i, x, m, st, h)
    case Some{i} None{} _:
      Unit{}
    case None{} _ _:
      Unit{}

def new.bump.of(pm: Maybe<&2, U32>, +r: Nat, +rg: List<&2, U32>, +cl: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, Word(8n)>, +ou: List<&2, Word(8n)>, +on: U32, hr: {Nat.is_eq(r, Mc.R.pend()) == False{} : Bool},
  +h: NewCells(Cr.Cir.State{rg, cl, nx, fi, im, pg, lm, inp, ou, on})) ->
  KeptOut(False{}, Cr.Cir.exec.bump.of(r, nx, Cr.Cir.State{rg, cl, nx, fi, im, pg, lm, inp, ou, on}, pm)):
  match pm:
    case Some{p}:
      kept.set(False{}, r, Some{nx}, Cr.Cir.State{rg, Cr.Cir.Cells.set(cl, nx, Cr.Cir.Cell.zero()), U32.inc(nx), fi, im, p, lm, inp, ou, on}, hr, h)
    case None{}:
      Unit{}

def new.bump.if(c: Bool, +r: Nat, +rg: List<&2, U32>, +cl: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, Word(8n)>, +ou: List<&2, Word(8n)>, +on: U32, hr: {Nat.is_eq(r, Mc.R.pend()) == False{} : Bool},
  +h: NewCells(Cr.Cir.State{rg, cl, nx, fi, im, pg, lm, inp, ou, on})) ->
  KeptOut(False{}, Cr.Cir.exec.bump.if(c, r, nx, pg, lm, Cr.Cir.State{rg, cl, nx, fi, im, pg, lm, inp, ou, on})):
  match c:
    case True{}:
      new.bump.of(Cr.Cir.room(U32.add(Cr.Cir.at(nx), 19), pg, lm), r, rg, cl, nx, fi, im, pg, lm, inp, ou, on, hr, h)
    case False{}:
      Unit{}

def new.alloc.if(z: Bool, +r: Nat, +rg: List<&2, U32>, +cl: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, Word(8n)>, +ou: List<&2, Word(8n)>, +on: U32, hr: {Nat.is_eq(r, Mc.R.pend()) == False{} : Bool},
  +h: NewCells(Cr.Cir.State{rg, cl, nx, fi, im, pg, lm, inp, ou, on})) ->
  KeptOut(False{}, Cr.Cir.exec.alloc.if(z, r, Cr.Cir.State{rg, cl, nx, fi, im, pg, lm, inp, ou, on})):
  match z:
    case True{}:
      new.bump.if(U32.is_lt(nx, 214748364), r, rg, cl, nx, fi, im, pg, lm, inp, ou, on, hr, h)
    case False{}:
      Unit{}

# an alloc into a register other than pend keeps the cells new
def new.alloc(+r: Nat, +st: Cr.Cir.State, hr: {Nat.is_eq(r, Mc.R.pend()) == False{} : Bool}, +h: NewCells(st)) ->
  KeptOut(False{}, Cr.Cir.exec.alloc(r, st)):
  match st:
    case Cr.Cir.State{rg, cl, nx, fi, im, pg, lm, inp, ou, on}:
      new.alloc.if(U32.is_zero(on), r, rg, cl, nx, fi, im, pg, lm, inp, ou, on, hr, h)

def new.emit.of(pm: Maybe<&2, U32>, x: U32, +st: Cr.Cir.State, h: NewCells(st)) -> KeptOut(False{}, Cr.Cir.exec.emit.of(pm, x, st)):
  match pm st:
    case Some{p} Cr.Cir.State{rg, cl, nx, fi, im, pg, lm, inp, ou, on}:
      h
    case None{} _:
      Unit{}

def new.emit.if(ok: Bool, +b: U32, x: U32, +st: Cr.Cir.State, h: NewCells(st)) -> KeptOut(False{}, Cr.Cir.exec.emit.if(ok, b, x, st)):
  match ok st:
    case True{} Cr.Cir.State{rg, cl, nx, fi, im, +pg, lm, inp, ou, on}:
      new.emit.of(Cr.Cir.room(b, pg, lm), x, st, h)
    case False{} _:
      Unit{}

# an emit keeps the registers
def new.emit(v: Maybe<&2, U32>, +st: Cr.Cir.State, h: NewCells(st)) -> KeptOut(False{}, Cr.Cir.exec.emit(v, st)):
  match v st:
    case Some{x} Cr.Cir.State{rg, cl, +nx, fi, im, pg, lm, inp, ou, +on}:
      new.emit.if(Bool.and(U32.is_lt(nx, 214748365), U32.is_ge(U32.add(Cr.Cir.at(nx), on), on)), U32.add(Cr.Cir.at(nx), on), x, st, h)
    case None{} _:
      Unit{}

# an alloc, then the state fits; an emit, the same
def kept.alloc(+m: Bool, +r: Nat, +st: Cr.Cir.State, hr: {Nat.is_eq(r, Mc.R.pend()) == False{} : Bool}, +h: Kept(m, st)) ->
  KeptOut(True{}, Cr.Cir.exec.alloc(r, st)):
  kept.both(Cr.Cir.exec.alloc(r, st), new.alloc(r, st, hr, kept.new(m, st, h)), fits.alloc(r, st))

def kept.emit(+m: Bool, +v: Maybe<&2, U32>, +st: Cr.Cir.State, +h: Kept(m, st)) -> KeptOut(True{}, Cr.Cir.exec.emit(v, st)):
  kept.both(Cr.Cir.exec.emit(v, st), new.emit(v, st, kept.new(m, st, h)), fits.emit(v, st))

# a then the rest: the rest keeps what a's outcome gives
def kept.then(-x: Bool, -y: Bool, o: Cr.Cir.Out, -k: Cr.Cir.State -> Cr.Cir.Out, ho: KeptOut(x, o),
  hk: @t: Cr.Cir.State -> Kept(x, t) -> KeptOut(y, k(t))) -> KeptOut(y, Cr.Cir.exec.then(o, k)):
  match o:
    case Cr.Cir.Out.next{st}:
      hk(st, ho)
    case Cr.Cir.Out.halt{s, st}:
      match ho:
    case Cr.Cir.Out.out_of_memory{}:
      Unit{}
    case Cr.Cir.Out.trap{}:
      Unit{}
    case Cr.Cir.Out.not_done{}:
      Unit{}

def kept.if.of(z: Bool, -x: Bool, -yes: Unit -> Cr.Cir.Out, -no: Unit -> Cr.Cir.Out, hy: KeptOut(x, yes(Unit{})), hn: KeptOut(x, no(Unit{}))) ->
  KeptOut(x, Cr.Cir.exec.if.of(z, yes, no)):
  match z:
    case False{}:
      hy
    case True{}:
      hn

def kept.if(-x: Bool, c: Maybe<&2, U32>, -yes: Unit -> Cr.Cir.Out, -no: Unit -> Cr.Cir.Out, hy: KeptOut(x, yes(Unit{})), hn: KeptOut(x, no(Unit{}))) ->
  KeptOut(x, Cr.Cir.exec.if(c, yes, no)):
  match c:
    case Some{v}:
      kept.if.of(U32.is_zero(v), x, yes, no, hy, hn)
    case None{}:
      Unit{}

# the value of a test, 0
def Zero(v: Maybe<&2, U32>) -> Data:
  match v:
    case Some{x}:
      {U32.is_zero(x) == True{} : Bool}
    case None{}:
      Empty

# an if whose test is 0 runs its else
def kept.if.z(c: Maybe<&2, U32>, -x: Bool, -yes: Unit -> Cr.Cir.Out, -no: Unit -> Cr.Cir.Out, z: Zero(c), hn: KeptOut(x, no(Unit{}))) ->
  KeptOut(x, Cr.Cir.exec.if(c, yes, no)):
  match c:
    case Some{v}:
      %Equal.sym(Bool, U32.is_zero(v), True{}, z) : KeptOut(x, Cr.Cir.exec.if.of(_, yes, no))
      hn
    case None{}:
      match z:

# Nat.is_eq says equal
def nat.eq(a: Nat, b: Nat, e: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({0n == 1n+q : Nat}, N.false_ne_true(e))
    case 1n+p 0n:
      Empty.absurd({1n+p == 0n : Nat}, N.false_ne_true(e))
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, z => 1n+z, p, q, nat.eq(p, q, e))

def pz.of(+o: Wa.Wasm.Op, +r: Nat, +n: U32, +st: Cr.Cir.State, +h: NewCells(st),
  er: {Nat.is_eq(r, Mc.R.pend()) == True{} : Bool}, ez: {U32.is_zero(Wa.Wasm.op(o, 0, n)) == True{} : Bool}) ->
  Zero(Cr.Cir.eval(Cr.Cir.Expr.op{o, Cr.Cir.Expr.get{r}, Cr.Cir.Expr.const{n}}, st)):
  match st:
    case Cr.Cir.State{rg, cl, nx, fi, im, pg, lm, inp, ou, on}:
      %Equal.sym(Nat, r, Mc.R.pend(), nat.eq(r, Mc.R.pend(), er)) : Zero(Cr.Cir.eval.op(o, List.get(&2, U32, rg, _), Some{n}))
      %Equal.sym(Maybe<&2, U32>, List.get(&2, U32, rg, Mc.R.pend()), Some{0}, h) : Zero(Cr.Cir.eval.op(o, _, Some{n}))
      ez

def pz.get(+o: Wa.Wasm.Op, +r: Nat, b: Cr.Cir.Expr, +st: Cr.Cir.State, +h: NewCells(st),
  +e: {Pz.op(o, Cr.Cir.Expr.get{r}, b) == True{} : Bool}) -> Zero(Cr.Cir.eval(Cr.Cir.Expr.op{o, Cr.Cir.Expr.get{r}, b}, st)):
  match b:
    case Cr.Cir.Expr.const{+n}:
      pz.of(o, r, n, st, h, PH.H.and_l(Nat.is_eq(r, Mc.R.pend()), U32.is_zero(Wa.Wasm.op(o, 0, n)), e),
        PH.H.and_r(Nat.is_eq(r, Mc.R.pend()), U32.is_zero(Wa.Wasm.op(o, 0, n)), e))
    case Cr.Cir.Expr.get{x0}:
      Empty.absurd(Zero(Cr.Cir.eval(Cr.Cir.Expr.op{o, Cr.Cir.Expr.get{r}, Cr.Cir.Expr.get{x0}}, st)), N.false_ne_true(e))
    case Cr.Cir.Expr.op{x0, x1, x2}:
      Empty.absurd(Zero(Cr.Cir.eval(Cr.Cir.Expr.op{o, Cr.Cir.Expr.get{r}, Cr.Cir.Expr.op{x0, x1, x2}}, st)), N.false_ne_true(e))
    case Cr.Cir.Expr.eqz{x0}:
      Empty.absurd(Zero(Cr.Cir.eval(Cr.Cir.Expr.op{o, Cr.Cir.Expr.get{r}, Cr.Cir.Expr.eqz{x0}}, st)), N.false_ne_true(e))
    case Cr.Cir.Expr.field{x0, x1}:
      Empty.absurd(Zero(Cr.Cir.eval(Cr.Cir.Expr.op{o, Cr.Cir.Expr.get{r}, Cr.Cir.Expr.field{x0, x1}}, st)), N.false_ne_true(e))
    case Cr.Cir.Expr.byte{x0}:
      Empty.absurd(Zero(Cr.Cir.eval(Cr.Cir.Expr.op{o, Cr.Cir.Expr.get{r}, Cr.Cir.Expr.byte{x0}}, st)), N.false_ne_true(e))
    case Cr.Cir.Expr.size{}:
      Empty.absurd(Zero(Cr.Cir.eval(Cr.Cir.Expr.op{o, Cr.Cir.Expr.get{r}, Cr.Cir.Expr.size{}}, st)), N.false_ne_true(e))

def pz.op(+o: Wa.Wasm.Op, a: Cr.Cir.Expr, +b: Cr.Cir.Expr, +st: Cr.Cir.State, +h: NewCells(st),
  +e: {Pz.op(o, a, b) == True{} : Bool}) -> Zero(Cr.Cir.eval(Cr.Cir.Expr.op{o, a, b}, st)):
  match a:
    case Cr.Cir.Expr.get{+r}:
      pz.get(o, r, b, st, h, e)
    case Cr.Cir.Expr.const{x0}:
      Empty.absurd(Zero(Cr.Cir.eval(Cr.Cir.Expr.op{o, Cr.Cir.Expr.const{x0}, b}, st)), N.false_ne_true(e))
    case Cr.Cir.Expr.op{x0, x1, x2}:
      Empty.absurd(Zero(Cr.Cir.eval(Cr.Cir.Expr.op{o, Cr.Cir.Expr.op{x0, x1, x2}, b}, st)), N.false_ne_true(e))
    case Cr.Cir.Expr.eqz{x0}:
      Empty.absurd(Zero(Cr.Cir.eval(Cr.Cir.Expr.op{o, Cr.Cir.Expr.eqz{x0}, b}, st)), N.false_ne_true(e))
    case Cr.Cir.Expr.field{x0, x1}:
      Empty.absurd(Zero(Cr.Cir.eval(Cr.Cir.Expr.op{o, Cr.Cir.Expr.field{x0, x1}, b}, st)), N.false_ne_true(e))
    case Cr.Cir.Expr.byte{x0}:
      Empty.absurd(Zero(Cr.Cir.eval(Cr.Cir.Expr.op{o, Cr.Cir.Expr.byte{x0}, b}, st)), N.false_ne_true(e))
    case Cr.Cir.Expr.size{}:
      Empty.absurd(Zero(Cr.Cir.eval(Cr.Cir.Expr.op{o, Cr.Cir.Expr.size{}, b}, st)), N.false_ne_true(e))

# a test that Pz accepts is 0 when no cell is to reuse
def pz.zero(c: Cr.Cir.Expr, +st: Cr.Cir.State, +h: NewCells(st), +e: {Pz(c) == True{} : Bool}) -> Zero(Cr.Cir.eval(c, st)):
  match c:
    case Cr.Cir.Expr.op{+o, +a, +b}:
      pz.op(o, a, b, st, h, e)
    case Cr.Cir.Expr.const{x0}:
      Empty.absurd(Zero(Cr.Cir.eval(Cr.Cir.Expr.const{x0}, st)), N.false_ne_true(e))
    case Cr.Cir.Expr.get{x0}:
      Empty.absurd(Zero(Cr.Cir.eval(Cr.Cir.Expr.get{x0}, st)), N.false_ne_true(e))
    case Cr.Cir.Expr.eqz{x0}:
      Empty.absurd(Zero(Cr.Cir.eval(Cr.Cir.Expr.eqz{x0}, st)), N.false_ne_true(e))
    case Cr.Cir.Expr.field{x0, x1}:
      Empty.absurd(Zero(Cr.Cir.eval(Cr.Cir.Expr.field{x0, x1}, st)), N.false_ne_true(e))
    case Cr.Cir.Expr.byte{x0}:
      Empty.absurd(Zero(Cr.Cir.eval(Cr.Cir.Expr.byte{x0}, st)), N.false_ne_true(e))
    case Cr.Cir.Expr.size{}:
      Empty.absurd(Zero(Cr.Cir.eval(Cr.Cir.Expr.size{}, st)), N.false_ne_true(e))

# an if that keeps the cells new: when its test is 0 with no cell to reuse
# (Pz), only its else runs
def keeps.if(z: Bool, +c: Cr.Cir.Expr, +st: Cr.Cir.State, yes: Unit -> Cr.Cir.Out, no: Unit -> Cr.Cir.Out,
  +kt: Bool, +ke: Bool, +tt: Bool, +te: Bool, ez: {Pz(c) == z : Bool}, h: NewCells(st),
  +k: {Bool.and(Bool.or(z, kt), ke) == True{} : Bool},
  iy: {kt == True{} : Bool} -> KeptOut(tt, yes(Unit{})), ino: {ke == True{} : Bool} -> KeptOut(te, no(Unit{}))) ->
  KeptOut(Bool.and(Bool.or(z, tt), te), Cr.Cir.exec.if(Cr.Cir.eval(c, st), yes, no)):
  match z:
    case True{}:
      kept.if.z(Cr.Cir.eval(c, st), te, yes, no, pz.zero(c, st, h, ez), ino(k))
    case False{}:
      kept.if(Bool.and(tt, te), Cr.Cir.eval(c, st), yes, no,
        kept.out_l(tt, te, yes(Unit{}), iy(PH.H.and_l(kt, ke, k))), kept.out_r(tt, te, no(Unit{}), ino(PH.H.and_r(kt, ke, k))))

# from a state that fit, the state after any statement fits
def fit.true(s: Cr.Cir.Stmt) -> {Fit(s, True{}) == True{} : Bool}:
  match s:
    case Cr.Cir.Stmt.seq{+a, +b}:
      %Equal.sym(Bool, Fit(a, True{}), True{}, fit.true(a)) : {Fit(b, _) == True{} : Bool}
      fit.true(b)
    case Cr.Cir.Stmt.if{+c, +t, +e}:
      %Equal.sym(Bool, Fit(t, True{}), True{}, fit.true(t)) : {Bool.and(Bool.or(Pz(c), _), Fit(e, True{})) == True{} : Bool}
      %Equal.sym(Bool, Fit(e, True{}), True{}, fit.true(e)) : {Bool.and(Bool.or(Pz(c), True{}), _) == True{} : Bool}
      %Equal.sym(Bool, Bool.or(Pz(c), True{}), True{}, Z.or.true(Pz(c))) : {Bool.and(_, True{}) == True{} : Bool}
      {==}
    case Cr.Cir.Stmt.nop{}:
      {==}
    case Cr.Cir.Stmt.set{_, _}:
      {==}
    case Cr.Cir.Stmt.store{_, _, _}:
      {==}
    case Cr.Cir.Stmt.alloc{_}:
      {==}
    case Cr.Cir.Stmt.emit{_}:
      {==}
    case Cr.Cir.Stmt.while{_, _}:
      {==}
    case Cr.Cir.Stmt.halt{_}:
      {==}

# the state after a run of s, by Fit, keeps what held before it
def kept.weak(s: Cr.Cir.Stmt, +m: Bool, -st: Cr.Cir.State, h: Kept(Fit(s, m), st)) -> Kept(m, st):
  match m:
    case True{}:
      %fit.true(s) : Kept(_, st)
      h
    case False{}:
      kept.new(Fit(s, False{}), st, h)

# a statement that Keeps accepts keeps the cells new, with any fuel, and
# the state after it fits as Fit says
def keeps.ok(+f: Nat, s: Cr.Cir.Stmt, +st: Cr.Cir.State, +m: Bool, +k: {Keeps(s) == True{} : Bool}, +h: Kept(m, st)) ->
  KeptOut(Fit(s, m), Cr.Cir.exec(f, s, st)):
  match f s:
    case _ Cr.Cir.Stmt.nop{}:
      h
    case _ Cr.Cir.Stmt.set{+r, e}:
      kept.set(m, r, Cr.Cir.eval(e, st), st, Z.not.t(Nat.is_eq(r, Mc.R.pend()), k), h)
    case _ Cr.Cir.Stmt.store{j, c, v}:
      kept.store(m, j, Cr.Cir.eval(c, st), Cr.Cir.eval(v, st), st, h)
    case _ Cr.Cir.Stmt.alloc{+r}:
      kept.alloc(m, r, st, Z.not.t(Nat.is_eq(r, Mc.R.pend()), k), h)
    case _ Cr.Cir.Stmt.emit{v}:
      kept.emit(m, Cr.Cir.eval(v, st), st, h)
    case _ Cr.Cir.Stmt.seq{+a, +b}:
      kept.then(Fit(a, m), Fit(b, Fit(a, m)), Cr.Cir.exec(f, a, st), t => Cr.Cir.exec(f, b, t),
        keeps.ok(f, a, st, m, PH.H.and_l(Keeps(a), Keeps(b), k), h),
        t => ht => keeps.ok(f, b, t, Fit(a, m), PH.H.and_r(Keeps(a), Keeps(b), k), ht))
    case _ Cr.Cir.Stmt.if{+c, +t, +e}:
      keeps.if(Pz(c), c, st, u => Cr.Cir.exec(f, t, st), u => Cr.Cir.exec(f, e, st), Keeps(t), Keeps(e), Fit(t, m), Fit(e, m),
        {==}, kept.new(m, st, h), k, kt => keeps.ok(f, t, st, m, kt, h), ke => keeps.ok(f, e, st, m, ke, h))
    case 0n Cr.Cir.Stmt.while{_, _}:
      Unit{}
    case 1n+g Cr.Cir.Stmt.while{+c, +body}:
      kept.if(m, Cr.Cir.eval(c, st),
        u => Cr.Cir.exec.then(Cr.Cir.exec(g, body, st), t => Cr.Cir.exec(g, Cr.Cir.Stmt.while{c, body}, t)),
        u => Cr.Cir.Out.next{st},
        kept.then(Fit(body, m), m, Cr.Cir.exec(g, body, st), t => Cr.Cir.exec(g, Cr.Cir.Stmt.while{c, body}, t),
          keeps.ok(g, body, st, m, k, h),
          t => ht => keeps.ok(g, Cr.Cir.Stmt.while{c, body}, t, m, k, kept.weak(body, m, t, ht))),
        h)
    case _ Cr.Cir.Stmt.halt{_}:
      N.false_ne_true(k)

# M.input keeps the cells new
def input.keeps() -> {Keeps(Mc.M.input()) == True{} : Bool}:
  {==}

# M.input surely takes a cell
def input.fit() -> {Fit(Mc.M.input(), False{}) == True{} : Bool}:
  {==}

# what an outcome keeps that fits and is no halt
def kept.fits(o: Cr.Cir.Out, h: KeptOut(True{}, o)) -> FitsOut(o):
  match o:
    case Cr.Cir.Out.next{st}:
      (a, b) = h
      b
    case Cr.Cir.Out.halt{s, st}:
      match h:
    case Cr.Cir.Out.out_of_memory{}:
      Unit{}
    case Cr.Cir.Out.trap{}:
      Unit{}
    case Cr.Cir.Out.not_done{}:
      Unit{}

# M.input from a state with no cell to reuse: its allocs take new cells, so
# the state after it fits; M.input never halts
def fits.input(+f: Nat, +st: Cr.Cir.State, h: NewCells(st)) -> FitsOut(Cr.Cir.exec(f, Mc.M.input(), st)):
  kept.fits(Cr.Cir.exec(f, Mc.M.input(), st),
    (%input.fit() : KeptOut(_, Cr.Cir.exec(f, Mc.M.input(), st)); keeps.ok(f, Mc.M.input(), st, False{}, input.keeps(), h)))

# a then b: when a's outcome fits, so does the run of b after it
def fits.seq(+f: Nat, +a: Cr.Cir.Stmt, +b: Cr.Cir.Stmt, +st: Cr.Cir.State, ha: FitsOut(Cr.Cir.exec(f, a, st))) ->
  FitsOut(Cr.Cir.exec(f, Cr.Cir.Stmt.seq{a, b}, st)):
  match f:
    case 0n:
      fits.then(Cr.Cir.exec(0n, a, st), t => Cr.Cir.exec(0n, b, t), ha, t => ht => fits.exec(0n, b, t, ht))
    case 1n+g:
      fits.then(Cr.Cir.exec(1n+g, a, st), t => Cr.Cir.exec(1n+g, b, t), ha, t => ht => fits.exec(1n+g, b, t, ht))

# a run of Mach.code from a state with no cell to reuse: the state after
# it, or at its halt, fits (fits.input, then fits.exec)
def fits.code(+f: Nat, +st: Cr.Cir.State, h: NewCells(st)) -> FitsOut(Cr.Cir.exec(f, Mc.Mach.code(), st)):
  fits.seq(f, Mc.M.input(), X.sel.b(Mc.Mach.code()), st, fits.input(f, st, h))
