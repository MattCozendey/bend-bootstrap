# compiler: layer B4, the proof of copy.spec
# ==========================================
#
# One def per law (M.copy: one tot.while whose invariant is the root's partial
# view (a field still to copy reads as the canonical substitution of its
# source part; share: view.deeper with canon.subst_below, or view.closed with
# canon.subst_closed for a STATIC source; local: canon.lift; past the locals:
# a poison); the measure is the source nodes still to copy). A body that is
# ?TODO is open.

import Base
import ../../../Shared/shared.bend as Sd
import ../../../Book/impl.bend as Bk
import ../../../Eval/impl.bend as El
import ../../../Program/impl.bend as Pg
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

def R.copy.spec(x, st, L, rs, fs, chs, wt, c, t, ce, es, hs, hc, he):
  ?TODO
