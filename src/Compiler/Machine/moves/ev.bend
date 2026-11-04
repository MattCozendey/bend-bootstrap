# compiler: layer B7, the proofs of the moves of mode 0 (M.ev) but the call
# =========================================================================
#
# One def per law mv.ev.* of moves/spec.bend but mv.ev.ref (moves/call.bend):
# a run of M.ev from a state that Inv finds, by tot.of_wp and the routine laws
# (inc, dec, push, one, copy, release_arg), the rewrite kit and the heap's
# frame laws. A body that is ?TODO is open.

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
import ../header/spec.bend as Hs
import ../canon/spec.bend as C
import ../am/spec.bend as A
import ../heap/spec.bend as Hp
import ../image/spec.bend as I
import ../routines/spec.bend as R
import ../memory/spec.bend as Me
import ./spec.bend as Mv
import ../logic/impl.bend as LgP
import ../header/impl.bend as HsP
import ../canon/impl.bend as CP
import ../am/impl.bend as AP
import ../heap/view.bend as HpV
import ../heap/count.bend as HpC
import ../image/impl.bend as IP
import ../routines/prims.bend as RP
import ../routines/nth.bend as RN
import ../routines/dec.bend as RD
import ../routines/copy.bend as RC
import ../routines/walk.bend as RW
import ../routines/out.bend as RO
import ../routines/input.bend as RI
import ../memory/impl.bend as MeP

def Mv.mv.ev.val(x, st, t, fs, iv, hv):
  ?TODO

def Mv.mv.ev.var(x, st, i, fs, iv, hv):
  ?TODO

def Mv.mv.ev.app(x, st, q, f, a, fs, iv, hv):
  ?TODO

def Mv.mv.ev.ann(x, st, a, b, fs, iv, hv):
  ?TODO

def Mv.mv.ev.let(x, st, q, v, f, fs, iv, hv, hq):
  ?TODO

def Mv.mv.ev.unlet(x, st, q, v, f, fs, iv, hv, hq):
  ?TODO

def Mv.mv.ev.tup(x, st, q, a, b, fs, iv, hv, hq):
  ?TODO

def Mv.mv.ev.tup0(x, st, q, a, b, fs, iv, hv, hq):
  ?TODO

def Mv.mv.ev.rwt(x, st, e, P, f, fs, iv, hv):
  ?TODO

def Mv.mv.ev.min(x, st, a, b, fs, iv, hv):
  ?TODO
