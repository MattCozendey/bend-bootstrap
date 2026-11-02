# compiler: layer B, M.walk gives Eval.walk (U7)
# ==============================================
#
# walk.post and walk.done of move_kit.bend: M.walk's rounds (λ, λ-match of pairs and labels, App
# of a local, Efq) give Eval.walk; the K.arg chains grow by at most 2 cells a round.
# Filled by U7; U0 left each as ?TODO.

import Base
import ./move_kit.bend as K

def K.walk.post(f, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, keep, os, bs, fs, sp, pend, ps, tc, tt, a, xs, xs0, zs, hs, hac, hst, hl, ht, ha, hp, args, hk):
  ?TODO

def K.walk.done(ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, os, bs, fs, sp, pend, ps, tc, tt, a, xs, hs, hst, hl, ht, ha, hp, args):
  ?TODO
