# compiler: layer B, the heap's operations (U2)
# =============================================
#
# The laws inc.post, dec.post, alloc.post, release.post, is.fresh, node.part,
# store.post, term.post and data.flag of definitions.bend: each statement of
# the heap (M.inc, M.dec, M.alloc, M.release, a store) keeps HSK and the
# accounting AccK, within its budget. Filled by U2; U0 left each as ?TODO.

import Base
import ./definitions.bend as D

def D.inc.post(f, dk, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, r, os, bs, fs, sp, pend, ps, c, u, xs, zs, hs, hac, hn, hc):
  ?TODO

def D.dec.post(f, dk, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, r, os, bs, fs, sp, pend, ps, c, u, xs, zs, hs, hac, hb, hl, hc, hp, h5):
  ?TODO

def D.alloc.post(f, dk, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, r, keep, os, bs, fs, sp, pend, ps, xs, zs, hs, hac, hl, hp, hr, hk):
  ?TODO

def D.release.post(f, dk, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, r, os, bs, fs, sp, pend, ps, z, xs, zs, hs, hac, hz, ht, hf, hm, hfs, hl, hc, hp):
  ?TODO

def D.is.fresh(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps, x, hs):
  ?TODO

def D.node.part(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps, c, y, hs, hn, hy):
  ?TODO

def D.store.post(dk, ds, ks, img, m, nx, fi, im, us, os, bs, fs, sp, pend, ps, z, x, xs, zs, hs, hac, hzx, hb, ho, hm, hzs, hzt, hz0, hzf, ht, hxs, hf):
  ?TODO

def D.term.post(dk, ds, ks, img, m, nx, fi, im, us, os, bs, fs, sp, pend, ps, z, x, t, xs, zs, hs, hac, ho, hm, hzs, hzt, hz0, hzf, hxs, hx1, hf, hi):
  ?TODO

def D.data.flag(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps, c, xs, zs, hs, hac, hd, hco):
  ?TODO
