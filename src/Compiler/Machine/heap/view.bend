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

def agree.fin.tt(c: Cmp) -> {Cmp.is_eq(Word.cmp.fin(True{}, True{}, c)) == Cmp.is_eq(c) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def agree.word.cmp.refl(+n: Nat, +w: Word(n)) -> {Cmp.is_eq(Word.cmp(n, w, w)) == True{} : Bool}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{False{}, +t}:
          Equal.trans(Bool, Cmp.is_eq(Word.cmp.fin(False{}, False{}, Word.cmp(p, t, t))),
            Cmp.is_eq(Word.cmp(p, t, t)), True{}, K.cmp.fin_ff(Word.cmp(p, t, t)), agree.word.cmp.refl(p, t))
        case WCon{True{}, +t}:
          Equal.trans(Bool, Cmp.is_eq(Word.cmp.fin(True{}, True{}, Word.cmp(p, t, t))),
            Cmp.is_eq(Word.cmp(p, t, t)), True{}, agree.fin.tt(Word.cmp(p, t, t)), agree.word.cmp.refl(p, t))

def agree.u32.eq.refl(+a: U32) -> {U32.is_eq(a, a) == True{} : Bool}:
  match a:
    case U32{+w}:
      agree.word.cmp.refl(32n, w)

def agree.same.refl(+m: Cr.Cir.Cells, +c: U32) -> {Hp.V.same(m, m, c) == True{} : Bool}:
  +h02 = K.bool.and_i(U32.is_eq(Hp.Fd(0n, m, c), Hp.Fd(0n, m, c)), U32.is_eq(Hp.Fd(2n, m, c), Hp.Fd(2n, m, c)),
    agree.u32.eq.refl(Hp.Fd(0n, m, c)), agree.u32.eq.refl(Hp.Fd(2n, m, c)))
  +h023 = K.bool.and_i(Bool.and(U32.is_eq(Hp.Fd(0n, m, c), Hp.Fd(0n, m, c)), U32.is_eq(Hp.Fd(2n, m, c), Hp.Fd(2n, m, c))),
    U32.is_eq(Hp.Fd(3n, m, c), Hp.Fd(3n, m, c)), h02, agree.u32.eq.refl(Hp.Fd(3n, m, c)))
  +hsame = K.bool.and_i(Bool.and(Bool.and(U32.is_eq(Hp.Fd(0n, m, c), Hp.Fd(0n, m, c)), U32.is_eq(Hp.Fd(2n, m, c), Hp.Fd(2n, m, c))),
    U32.is_eq(Hp.Fd(3n, m, c), Hp.Fd(3n, m, c))), U32.is_eq(Hp.Fd(4n, m, c), Hp.Fd(4n, m, c)), h023,
    agree.u32.eq.refl(Hp.Fd(4n, m, c)))
  hsame

def Hp.agree.refl(cs, m):
  match cs:
    case Nil{}:
      {==}
    case Con{c, rest}:
      K.bool.and_i(Hp.V.same(m, m, c), Hp.Agree(rest, m, m), agree.same.refl(m, c), Hp.agree.refl(rest, m))

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
