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
import ../../../Program/impl.bend as Pg
import ../../Cir/impl.bend as Cr
import ./spec.bend as Lg

def Lg.exec.more(f, g, s, st, d):
  ?TODO

def Lg.tot.any(s, st, b, Q, H, t, g):
  ?TODO

def Lg.tot.seq(a, c, st, b, Q, H, t):
  ?TODO

def Lg.tot.if(c, y, n, st, b, Q, H, v, e, t):
  ?TODO

def Lg.tot.while(c, body, b, I, Q, H, r, n, st, i):
  ?TODO

def Lg.tot.wk(s, st, b, b2, Q, Q2, H, H2, hb, hq, hh, t):
  ?TODO

def Lg.tot.of_wp(s, st, b, K, H, w):
  ?TODO

def Lg.wp.of_tot(s, st, b, K, H, t):
  ?TODO

def Lg.wp.wk(s, st, b, b2, K, K2, H, H2, hb, hk, hh, w):
  ?TODO

def Lg.exec.set(f, r, e, st, v, he, hr):
  ?TODO

def Lg.exec.store(f, k, c, e, st, i, v, hc, he, hi):
  ?TODO

def Lg.exec.alloc(f, r, st, hr, ho):
  ?TODO

def Lg.wp.set(r, e, st, b, K, H, v, he, hr, q):
  ?TODO

def Lg.wp.store(k, c, e, st, b, K, H, i, v, hc, he, hi, q):
  ?TODO

def Lg.wp.alloc(r, st, b, K, H, hr, ho, hb, q):
  ?TODO

def Lg.wp.emit(e, st, b, K, H, v, he, hb, q):
  ?TODO

def Lg.reg.set(st, r, v, q, hr):
  ?TODO

def Lg.reg.store(st, k, c, v, q):
  ?TODO

def Lg.reg.alloc(st, r, p, q, hr):
  ?TODO

def Lg.reg.emit(st, v, p, q):
  ?TODO

def Lg.nregs.set(st, r, v):
  ?TODO

def Lg.nregs.store(st, k, c, v):
  ?TODO

def Lg.nregs.alloc(st, r, p):
  ?TODO

def Lg.nregs.emit(st, v, p):
  ?TODO

def Lg.cells.set(st, r, v):
  ?TODO

def Lg.cells.store(st, k, c, v):
  ?TODO

def Lg.cells.alloc(st, r, p):
  ?TODO

def Lg.cells.emit(st, v, p):
  ?TODO

def Lg.cells.get_set(m, i, x, j):
  ?TODO

def Lg.cell.get_set(k, x, v, j, hk, hj):
  ?TODO

def Lg.next.set(st, r, v):
  ?TODO

def Lg.next.store(st, k, c, v):
  ?TODO

def Lg.next.alloc(st, r, p):
  ?TODO

def Lg.next.emit(st, v, p):
  ?TODO

def Lg.outn.set(st, r, v):
  ?TODO

def Lg.outn.store(st, k, c, v):
  ?TODO

def Lg.outn.alloc(st, r, p):
  ?TODO

def Lg.outn.emit(st, v, p):
  ?TODO

def Lg.fixed.set(st, r, v):
  ?TODO

def Lg.fixed.store(st, k, c, v):
  ?TODO

def Lg.fixed.alloc(st, r, p):
  ?TODO

def Lg.fixed.emit(st, v, p):
  ?TODO

def Lg.lim.set(st, r, v):
  ?TODO

def Lg.lim.store(st, k, c, v):
  ?TODO

def Lg.lim.alloc(st, r, p):
  ?TODO

def Lg.lim.emit(st, v, p):
  ?TODO

def Lg.frame.regs(f, s, st, st2, r, e, w):
  ?TODO

def Lg.frame.fixed(f, s, st, st2, e):
  ?TODO

def Lg.tot.frame(s, st, b, Q, H, t):
  ?TODO

def Lg.tot.frame_out(s, st, b, Q, H, ne, t):
  ?TODO

