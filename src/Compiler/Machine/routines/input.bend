# compiler: layer B4, the proof of input.spec
# ===========================================
#
# One def per law (M.input: its two loops (the bytes from the last, the bits
# of a new byte of the cache); salvage start_input from 4ebef88). A body that
# is ?TODO is open.

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

def R.input.spec(p, ds, i, m, k, len, pg, lim, first, rd, small, s):
  ?TODO
