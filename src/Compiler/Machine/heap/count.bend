# compiler: layer B3, the proofs of the heap-invariant laws of heap/spec.bend
# ===========================================================================
#
# One def per law (H under a register write (h.set) and its live cells
# (h.live)). A body that is ?TODO is open.

import Base
import ../../../Shared/shared.bend as Sd
import ../../../Book/impl.bend as Bk
import ../../../Eval/impl.bend as El
import ../../../Program/impl.bend as Pg
import ../../Cir/impl.bend as Cr
import ../impl.bend as Mc
import ../shared.bend as K
import ../logic/spec.bend as Lg
import ../header/spec.bend as Hs
import ../canon/spec.bend as C
import ../am/spec.bend as A
import ./spec.bend as Hp
import ../logic/impl.bend as LgP
import ../header/impl.bend as HsP
import ../canon/impl.bend as CP
import ../am/impl.bend as AP
import ./view.bend as HpV

def Hp.h.set(x, st, L, rs, fs, chs, r, v, h, hr):
  ?TODO

def Hp.h.live(x, st, L, rs, fs, chs, h):
  ?TODO

def Hp.h.rts_swap(x, st, L, pre, a, b, rs, fs, chs, h):
  ?TODO

def Hp.h.chs_swap(x, st, L, rs, fs, pre, a, b, chs, h):
  ?TODO

def Hp.h.static_root(x, st, L, rs, fs, chs, c, d, t, h, hc):
  ?TODO

def Hp.h.count(x, st, L, rs, fs, chs, c, h, hb, hc):
  ?TODO
