# compiler: layer B4, the proofs of dec.spec, release_arg.spec and release_all.spec
# =================================================================================
#
# One def per law (the cascade of M.dec: one tot.while on the list fl (each
# cell on it has count 0, is live, and is no longer held); release.arg and
# release.all from it). A body that is ?TODO is open.

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

def R.dec.spec(x, st, L, rs, fs, chs, r, c, d, t, hs, hr, hw):
  ?TODO

def R.release_arg.spec(x, st, L, rs, fs, chs, a, c, ag, as, hs, hr, hw):
  ?TODO

def R.release_all.spec(x, st, L, rs, fs, chs, l, c, as, hs, hr, hw):
  ?TODO
