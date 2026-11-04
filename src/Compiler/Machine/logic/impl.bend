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
import ../../../Wasm/impl.bend as Wa
import ../../need_big.bend as N
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
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      K.list.get_set(U32, regs, r, v, q, hr)

def Lg.reg.store(st, k, c, v, q):
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      {==}

def Lg.reg.alloc(st, r, p, q, hr):
  match st:
    case Cr.Cir.State{regs, cells, +next, first, image, pages, limit, input, out, outn}:
      K.list.get_set(U32, regs, r, next, q, hr)

def Lg.reg.emit(st, v, p, q):
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      {==}

def Lg.nregs.set(st, r, v):
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      K.list.length_set(U32, regs, r, v)

def Lg.nregs.store(st, k, c, v):
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      {==}

def Lg.nregs.alloc(st, r, p):
  match st:
    case Cr.Cir.State{regs, cells, +next, first, image, pages, limit, input, out, outn}:
      K.list.length_set(U32, regs, r, next)

def Lg.nregs.emit(st, v, p):
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      {==}

def Lg.cells.set(st, r, v):
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      {==}

def Lg.cells.store(st, k, c, v):
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      {==}

def Lg.cells.alloc(st, r, p):
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      {==}

def Lg.cells.emit(st, v, p):
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      {==}

def Lg.cells.get_set(m, i, x, j):
  ?TODO

def Lg.cell.get_set(k, x, v, j, hk, hj):
  ?TODO

def Lg.next.set(st, r, v):
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      {==}

def Lg.next.store(st, k, c, v):
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      {==}

def Lg.next.alloc(st, r, p):
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      {==}

def Lg.next.emit(st, v, p):
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      {==}

def Lg.outn.set(st, r, v):
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      {==}

def Lg.outn.store(st, k, c, v):
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      {==}

def Lg.outn.alloc(st, r, p):
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      {==}

def Lg.outn.emit(st, v, p):
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      {==}

def Lg.fixed.set(st, r, v):
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      {==}

def Lg.fixed.store(st, k, c, v):
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      {==}

def Lg.fixed.alloc(st, r, p):
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      {==}

def Lg.fixed.emit(st, v, p):
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      {==}

def Lg.lim.set(st, r, v):
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      {==}

def Lg.lim.store(st, k, c, v):
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      {==}

def Lg.lim.alloc(st, r, p):
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      {==}

def Lg.lim.emit(st, v, p):
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      {==}

def Lg.frame.regs(f, s, st, st2, r, e, w):
  ?TODO

def Lg.frame.fixed(f, s, st, st2, e):
  ?TODO

def Lg.tot.frame(s, st, b, Q, H, t):
  ?TODO

def Lg.tot.frame_out(s, st, b, Q, H, ne, t):
  ?TODO

