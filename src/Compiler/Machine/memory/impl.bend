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
  ?TODO

def Me.code.fits(n, cells, first, k, pg, lim, i):
  ?TODO
