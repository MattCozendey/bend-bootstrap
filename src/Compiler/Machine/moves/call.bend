# compiler: layer B7, the proofs of the redexes and the calls
# ===========================================================
#
# One def per law of moves/spec.bend for M.redex (λ, Prj, Mat, and a call by
# M.call: the walk, the copy of its leaf, the frames of the arguments left)
# and for M.ev's Ref. M.call has no routine law (its loops move the arguments
# left into frames and release wenv): its run is proven here, once, as a
# helper that the call moves share. A body that is ?TODO is open.

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

def Mv.call.frames(x, st, L, rs, fs, chs, c, ys, hs, hw):
  ?TODO

def Mv.mv.ev.ref(x, st, k, fs, iv, hv):
  ?TODO

def Mv.mv.ret.app.lam(x, st, p, f, kind, q, k, a, b, fs, iv, hk, hs):
  ?TODO

def Mv.mv.ret.app.prj(x, st, h, kind, q, k, a, b, fs, iv, hk, hs):
  ?TODO

def Mv.mv.ret.app.mat(x, st, j, h, m, kind, q, k, a, b, fs, iv, hk, hs):
  ?TODO

def Mv.mv.ret.app.call(x, st, v, kind, q, k, a, b, fs, iv, hk, hs, hc):
  ?TODO

def Mv.mv.ret.fun.lam(x, st, v, q, k, p, f, b, fs, iv):
  ?TODO

def Mv.mv.ret.fun.prj(x, st, v, q, k, h, b, fs, iv):
  ?TODO

def Mv.mv.ret.fun.mat(x, st, v, q, k, j, h, m, b, fs, iv):
  ?TODO

def Mv.mv.ret.fun.call(x, st, v, q, k, g, b, fs, iv, hc):
  ?TODO
