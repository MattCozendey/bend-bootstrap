# compiler: layer B7, the proofs of the moves of mode 1 (M.ret) but the redexes
# =============================================================================
#
# One def per law of moves/spec.bend for M.ret's frames other than App's
# redexes: M.out, the swaps, Let, Tup a □, Rwt and Min a □. A body that is
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

def Mv.mv.out(x, st, v, iv):
  ?TODO

def Mv.mv.ret.swap(x, st, v, kind, q, k, a, b, fs, iv, hk, hs):
  ?TODO

def Mv.mv.ret.let(x, st, v, q, k, f, b, fs, iv):
  ?TODO

def Mv.mv.ret.tupb(x, st, v, q, k, a, b, fs, iv):
  ?TODO

def Mv.mv.ret.tupa(x, st, v, q, k, a, b, fs, iv):
  ?TODO

def Mv.mv.ret.rwt(x, st, v, q, k, P, f, fs, iv):
  ?TODO

def Mv.mv.ret.minb(x, st, v, q, k, a, b, fs, iv):
  ?TODO

def Mv.mv.ret.mina(x, st, v, q, k, a, b, fs, iv):
  ?TODO
