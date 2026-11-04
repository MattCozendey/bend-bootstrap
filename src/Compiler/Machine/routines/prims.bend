# compiler: layer B4, the proofs of the small routines of routines/spec.bend
# ==========================================================================
#
# One def per law (alloc, make, release, inc, push, pop, swap, one (tot.wp and
# the rewrite kit), and the heap lemmas h.node and h.arg). A body that is
# ?TODO is open.

import Base
import ../../../Shared/shared.bend as Sd
import ../../../Book/impl.bend as Bk
import ../../../Eval/impl.bend as El
import ../../../Program/impl.bend as Pg
import ../../../Wasm/impl.bend as Wa
import ../../Cir/impl.bend as Cr
import ../impl.bend as Mc
import ../shared.bend as K
import ../logic/spec.bend as Lg
import ../canon/spec.bend as C
import ../am/spec.bend as A
import ../heap/spec.bend as Hp
import ../image/spec.bend as I
import ./spec.bend as R
import ../logic/impl.bend as LgP
import ../header/impl.bend as HsP
import ../canon/impl.bend as CP
import ../am/impl.bend as AP
import ../heap/view.bend as HpV
import ../heap/count.bend as HpC
import ../image/impl.bend as IP

def R.alloc.spec(x, st, L, r, hs, hr):
  ?TODO

def R.make.spec(x, st, L, r, h, a, b, c, hv, av, bv, cv, hs, hr, he):
  ?TODO

def R.release.spec(st, r, c, hr, hc):
  ?TODO

def R.inc.spec(x, st, L, rs, fs, chs, r, c, d, t, hs, hr, hn, hb):
  ?TODO

def R.push.spec(x, st, L, rs, fs, chs, fr, h, a, b, ca, cb, hs, he):
  ?TODO

def R.pop.spec(x, st, L, rs, fr, fs, chs, hs):
  ?TODO

def R.swap.spec(x, st, L, rs, fs, chs, fr, fr2, v, h, hs, hh, he):
  ?TODO

def R.one.spec(x, st, L, rs, fs, chs, r, c, t, hs, hr, hw):
  ?TODO

def R.h.node(x, st, L, rs, fs, chs, r, v, ps, t, hs, hr, hn, hc):
  ?TODO

def R.h.arg(x, st, L, rs, fs, chs, r, ag, c, ln, as, hs, hr, hn):
  ?TODO

def R.alloc.reg(st, r, q, hr):
  ?TODO

def R.make.reg(st, r, v, q, hr):
  ?TODO
