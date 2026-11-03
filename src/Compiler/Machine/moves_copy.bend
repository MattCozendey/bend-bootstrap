# compiler: layer B, the moves that copy (U12)
# ============================================
#
# mv.ev.unlet, mv.ret.let, mv.ret.app.lam and mv.ret.fun.lam of move_kit.bend: M.data when the
# quantity is 2, M.one, M.copy, then the step.
# Filled by U12; U0 left each as ?TODO.

import Base
import ./move_kit.bend as K

def K.mv.ev.unlet(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, v, b, iv, hv, hq, hfv):
  ?TODO

def K.mv.ret.app.lam(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, r, h, kind, q, k, a, b, iv, hk, hs, hfv):
  ?TODO

def K.mv.ret.fun.lam(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, r, h, focus, q, k, b, iv, hfv):
  ?TODO

def K.mv.ret.let(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, focus, q, k, a, b, iv, hfv):
  ?TODO
