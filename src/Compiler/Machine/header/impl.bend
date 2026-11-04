# compiler: layer B2, the proofs of header/spec.bend
# ==================================================
#
# One def per law of header/spec.bend. A def whose body is ?TODO is still
# open. The route: each mask law by its 32 bits (Word facts by induction on
# the width, then the U32 ones); hd.*_of from the mask laws and Hd.fits.

import Base
import ../shared.bend as K
import ../../Cir/impl.bend as Cr
import ../impl.bend as Mc
import ./spec.bend as Hd

def Hd.hd.tag_of(t, q, fl, fv, h):
  ?TODO

def Hd.hd.q_of(t, q, fl, fv, h):
  ?TODO

def Hd.hd.fv_of(t, q, fl, fv, h):
  ?TODO

def Hd.hd.has_of(t, q, fl, fv, bit, h, hb):
  ?TODO

def Hd.hd.todo_of(t, q, fl, fv, h):
  ?TODO

def Hd.mask.and_or(a, b, m):
  ?TODO

def Hd.mask.and_and(a, b, c):
  ?TODO

def Hd.mask.and_shl(a, n, m):
  ?TODO

def Hd.mask.shr_or(a, b, n):
  ?TODO

def Hd.mask.shr_and(a, m, n):
  ?TODO

def Hd.mask.shr_shl(a, n):
  ?TODO

def Hd.mask.or_zero(a):
  ?TODO

def Hd.mask.zero_or(a):
  ?TODO

def Hd.mask.and_zero(a):
  ?TODO

def Hd.mask.zero_and(a):
  ?TODO

def Hd.mask.and_low(a, k, h):
  ?TODO

def Hd.mask.shr_low(a, k, h):
  ?TODO

def Hd.mask.sub_bit(h, b, e):
  ?TODO

