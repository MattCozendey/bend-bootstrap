# compiler: layer B4, the proof of out.spec
# =========================================
#
# One def per law (M.out: its two loops (the list, the bits of a byte),
# against Program.unbytes). A body that is ?TODO is open.

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

def R.out.spec(x, st, v, iv):
  ?TODO
