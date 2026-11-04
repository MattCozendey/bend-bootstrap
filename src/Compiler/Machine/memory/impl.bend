# compiler: layer B8, the proofs of memory/spec.bend
# =================================================
#
# One def per law of memory/spec.bend. A body that is ?TODO is open. The
# routes: eval.stops ports ev.stops (eval_facts.bend at 4ebef88); need.peak,
# budget.need, input.need and need.lim port memory_bound.bend's arithmetic
# (largest.*, start.size, first.le, k.le, big.le, w.le, room.need,
# memory.le), with 3 S for 2 S and |i| <= S / 72 for |i| <= S; code.fits
# ports cir_fits.bend (Fits is kept by every statement; M.input takes a new
# cell first); round.mem and input.mem step the round and M.input as their
# moves' and routines' proofs do, with the free list's discipline: a new cell
# is taken only when the free list is empty, so next - first is then the
# live cells' number.

import Base
import ../../../Book/impl.bend as Bk
import ../../../Eval/impl.bend as El
import ../../../Program/impl.bend as Pg
import ../../../Wasm/impl.bend as Wa
import ../../Cir/impl.bend as Cr
import ../impl.bend as Mc
import ../../need_big.bend as N
import ../../Cir/simulation_memory_bytes.bend as SB
import ../shared.bend as K
import ../logic/spec.bend as Lg
import ../canon/spec.bend as C
import ../am/spec.bend as A
import ../heap/spec.bend as Hp
import ../image/spec.bend as I
import ../routines/spec.bend as R
import ./spec.bend as Me
import ../logic/impl.bend as LgP
import ../canon/impl.bend as CP
import ../am/impl.bend as AP

# Kit
# ---

# a Bool that is true, from its truth as a type
def me.fromT(b: Bool, t: N.T(b)) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, t)

# The limit's bytes (memory_bound.bend at 4ebef88)
# ------------------------------------------------

def me.D_mono(k: Nat, +a: Nat, +b: Nat, h: N.Le(a, b)) -> N.Le(N.D(k, a), N.D(k, b)):
  match k:
    case 0n:
      h
    case 1n+(+q):
      N.double_mono(N.D(q, a), N.D(q, b), me.D_mono(q, a, b, h))

# the pages of min(m, 65536) are the limit's
def me.lim.y(+m: U32, +lim: U32, elim: {lim == Wa.Wasm.min(m, 65536) : U32}) ->
  N.Le(U32.to_nat(Wa.Wasm.min.if(Cmp.is_le(U32.cmp(m, 65536)), m, 65536)), U32.to_nat(lim)):
  %Equal.sym(U32, lim, Wa.Wasm.min(m, 65536), elim) :
    N.Le(U32.to_nat(Wa.Wasm.min.if(Cmp.is_le(U32.cmp(m, 65536)), m, 65536)), U32.to_nat(_))
  N.le_refl(U32.to_nat(Wa.Wasm.min(m, 65536)))

# so they are at most the pages min(lim, 65536) that Lim counts, by the
# branch of U32.is_le(lim, 65536)
def me.lim.pages(b: Bool, +lim: U32, +y: Nat, hy: N.Le(y, U32.to_nat(65536)), hl: N.Le(y, U32.to_nat(lim))) ->
  N.Le(y, U32.to_nat(Wa.Wasm.min.if(b, lim, 65536))):
  match b:
    case True{}:
      hl
    case False{}:
      %{{==} : {65536 == Wa.Wasm.min.if(False{}, lim, 65536) : U32}} : N.Le(y, U32.to_nat(_))
      hy

# the bytes of m pages are within the limit lim = min(m, 65536)
def me.memory.le(+m: U32, +lim: U32, elim: {lim == Wa.Wasm.min(m, 65536) : U32}) ->
  N.Le(Pg.Program.memory(m), N.D(16n, U32.to_nat(Wa.Wasm.min(lim, 65536)))):
  +L = N.D(16n, U32.to_nat(Wa.Wasm.min(lim, 65536)))
  +y = U32.to_nat(Wa.Wasm.min.if(Cmp.is_le(U32.cmp(m, 65536)), m, 65536))
  +t = U32.to_nat(65536)
  +z = U32.to_nat(Wa.Wasm.min(lim, 65536))
  +hy = N.min.case(Cmp.is_le(U32.cmp(m, 65536)), m, 65536, {==})
  +hz = me.lim.pages(U32.is_le(lim, 65536), lim, y, hy, me.lim.y(m, lim, elim))
  +e2 = Equal.trans(Nat, Nat.mul(t, y), Nat.mul(N.D(16n, 1n), y), N.D(16n, y),
    Equal.cong(Nat, Nat, x => Nat.mul(x, y), t, N.D(16n, 1n), N.val_65536()), N.mul_D(16n, y))
  +h2 = N.le_rw_r(Nat.mul(65536n, y), Nat.mul(t, y), N.D(16n, y), e2, N.mul_mono_l(65536n, t, y, N.le_65536()))
  +h3 = N.le_trans(Nat.mul(65536n, y), N.D(16n, y), L, h2, me.D_mono(16n, y, z, hz))
  N.bridge(m, L, N.le_rw_l(Nat.mul(65536n, y), Nat.add(y, Nat.mul(65535n, y)), L, N.mul_succ(65535n, y), h3))

# the limit of Cir.result's start, from Start
def me.start.lim(+cells: List<&2, Cr.Cir.Cell>, +i: List<&2, Word(8n)>, +m: U32, +k: U32, +len: U32, +pg: U32, +lim: U32,
  +first: U32, +hs: {I.Start(cells, i, m, k, len, pg, lim, first) == True{} : Bool}) -> {lim == Wa.Wasm.min(m, 65536) : U32}:
  +c1 = U32.is_eq(k, Cr.Wasm.encode.len(Cr.Cir.Cell, cells))
  +c2 = U32.is_le(Cr.Cir.pages(Cr.Cir.input.at(k)), m)
  +c3 = U32.is_eq(lim, Wa.Wasm.min(m, 65536))
  +c4 = I.Mb.is(Wa.Wasm.length32(i), len)
  +c6 = U32.is_eq(first, Cr.Cir.first(k, U32.add(Cr.Cir.input.at(k), len)))
  +h5 = K.bool.and_l(Bool.and(Bool.and(Bool.and(Bool.and(c1, c2), c3), c4), I.Mb.is(Cr.Cir.alloc.pages(k, len,
    Cr.Cir.pages(Cr.Cir.input.at(k)), lim), pg)), c6, hs)
  +h4 = K.bool.and_l(Bool.and(Bool.and(Bool.and(c1, c2), c3), c4), I.Mb.is(Cr.Cir.alloc.pages(k, len, Cr.Cir.pages(Cr.Cir.input.at(k)), lim), pg), h5)
  +h3 = K.bool.and_l(Bool.and(Bool.and(c1, c2), c3), c4, h4)
  SB.U32.eq(lim, Wa.Wasm.min(m, 65536), K.bool.and_r(Bool.and(c1, c2), c3, h3))

# Laws
# ----

def Me.eval.stops(ds, t, h):
  ?TODO

def Me.round.mem(x, st, s, iv, f, st2, e):
  ?TODO

def Me.input.mem(p, ds, i, m, k, len, pg, lim, first, n, rd, small, s, f, st, e):
  ?TODO

def Me.need.peak(p, ds, i, n, j, o, C, st, s, rd, he, hj, ht, hst):
  ?TODO

def Me.budget.need(p, ds, i, m, k, len, pg, lim, first, n, j, o, C, st, s, rd, hs, he, hj, ht, iv, hC, hst, hm):
  ?TODO

def Me.input.need(p, ds, i, m, k, len, pg, lim, first, n, rd, hs):
  ?TODO

def Me.need.lim(p, ds, i, m, k, len, pg, lim, first, n, hs, big):
  me.fromT(Nat.is_le(Pg.Program.need(p, i, n), Lg.Lim(I.St0(Mc.Mach.regs(), Mc.Img.cells(ds), first, k, pg, lim, i))),
    N.le_trans(Pg.Program.need(p, i, n), Pg.Program.memory(m), N.D(16n, U32.to_nat(Wa.Wasm.min(lim, 65536))),
      N.toLe(Pg.Program.need(p, i, n), Pg.Program.memory(m), big),
      me.memory.le(m, lim, me.start.lim(Mc.Img.cells(ds), i, m, k, len, pg, lim, first, hs))))

def Me.start.ok(p, ds, i, m, n, rd, big):
  ?TODO

def Me.code.fits(n, cells, first, k, pg, lim, i):
  ?TODO
