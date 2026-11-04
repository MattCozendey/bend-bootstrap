# compiler: layer B3, the proofs of the view laws of heap/spec.bend
# =================================================================
#
# One def per law (the view (V.tm), its footprint (V.cells) and agreement
# (Agree)). A body that is ?TODO is open.

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

def Hp.view.frame(g, x, m, m2, c, d, a):
  ?TODO

def Hp.view.more(g, h, x, m, c, d, t, e):
  ?TODO

def Hp.view.deeper(g, x, m, c, d, k, t, hr, e):
  ?TODO

def Hp.view.static(g, x, m, c, d, e, t, hs, r):
  ?TODO

def Hp.view.canon(g, x, m, c, d, t, hr, e):
  ?TODO

def Hp.view.closed(g, x, m, c, d, k, t, hs, hr, e):
  ?TODO

def Hp.view.chk(g, x, m, c, d, t, e):
  ?TODO

def Hp.view.tag(g, x, m, c, d, t, e):
  ?TODO

def Hp.view.kid(g, x, m, c, d, k, t, e, hk):
  ?TODO

def Hp.agree.store(cs, m, o, k, v, n):
  ?TODO

def Hp.agree.store1(cs, m, o, v):
  ?TODO

def Hp.agree.put(cs, m, o, v, n):
  ?TODO

def Hp.agree.refl(cs, m):
  ?TODO

def Hp.agree.trans(cs, m, m2, m3, a, b):
  ?TODO

def Hp.view.rc_fv(g, x, m, c, d, e, t, hs, hf, r):
  ?TODO

def Hp.view.rc_frame(g, m, m2, c, d, a):
  ?TODO

def Hp.view.rc_more(g, h, m, c, d, r):
  ?TODO

def Hp.view.rc_up(g, m, c, d, d2, hd, r):
  ?TODO
