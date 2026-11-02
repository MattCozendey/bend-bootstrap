# compiler: layer B, the moves that push a frame, and the moves to mode 1 (U10)
# =============================================================================
#
# mv.ev.val, mv.ev.former, mv.ev.var (mode 1, or a halt), and mv.ev.app, mv.ev.let, mv.ev.tup,
# mv.ev.tup0, mv.ev.rwt, mv.ev.min (a frame pushed, an admin move) of move_kit.bend.
# Filled by U10; U0 left each as ?TODO.

import Base
import ./move_kit.bend as K

def K.mv.ev.val(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, focus, iv, hv):
  ?TODO

def K.mv.ev.former(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, focus, iv, hf):
  ?TODO

def K.mv.ev.var(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, i, iv, hv):
  ?TODO

def K.mv.ev.let(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, v, b, iv, hv, hq):
  ?TODO

def K.mv.ev.app(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, g, x, iv, hv):
  ?TODO

def K.mv.ev.tup(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, a, b, iv, hv, hq):
  ?TODO

def K.mv.ev.tup0(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, a, b, iv, hv, hq):
  ?TODO

def K.mv.ev.rwt(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, e, p, b, iv, hv):
  ?TODO

def K.mv.ev.min(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, a, b, iv, hv):
  ?TODO
