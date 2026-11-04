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

def agree.fin.ft(c: Cmp) -> {Cmp.is_eq(Word.cmp.fin(False{}, True{}, c)) == False{} : Bool}:
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

def agree.word.cmp.eq(+n: Nat, +a: Word(n), +b: Word(n), h: {Cmp.is_eq(Word.cmp(n, a, b)) == True{} : Bool}) -> {a == b : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{False{}, +at} WCon{False{}, +bt}:
          +ht = Equal.trans(Bool, Cmp.is_eq(Word.cmp(p, at, bt)), Cmp.is_eq(Word.cmp.fin(False{}, False{}, Word.cmp(p, at, bt))),
            True{}, Equal.sym(Bool, Cmp.is_eq(Word.cmp.fin(False{}, False{}, Word.cmp(p, at, bt))), Cmp.is_eq(Word.cmp(p, at, bt)),
              K.cmp.fin_ff(Word.cmp(p, at, bt))), h)
          Equal.cong(Word(p), Word(1n+p), t => WCon{False{}, t}, at, bt, agree.word.cmp.eq(p, at, bt, ht))
        case WCon{True{}, +at} WCon{True{}, +bt}:
          +ht = Equal.trans(Bool, Cmp.is_eq(Word.cmp(p, at, bt)), Cmp.is_eq(Word.cmp.fin(True{}, True{}, Word.cmp(p, at, bt))),
            True{}, Equal.sym(Bool, Cmp.is_eq(Word.cmp.fin(True{}, True{}, Word.cmp(p, at, bt))), Cmp.is_eq(Word.cmp(p, at, bt)),
              agree.fin.tt(Word.cmp(p, at, bt))), h)
          Equal.cong(Word(p), Word(1n+p), t => WCon{True{}, t}, at, bt, agree.word.cmp.eq(p, at, bt, ht))
        case WCon{False{}, at} WCon{True{}, bt}:
          K.bool.ff({WCon{False{}, at} == WCon{True{}, bt} : Word(1n+p)}, Equal.trans(Bool, False{}, Cmp.is_eq(Word.cmp.fin(False{}, True{}, Word.cmp(p, at, bt))), True{},
            Equal.sym(Bool, Cmp.is_eq(Word.cmp.fin(False{}, True{}, Word.cmp(p, at, bt))), False{}, agree.fin.ft(Word.cmp(p, at, bt))), h))
        case WCon{True{}, at} WCon{False{}, bt}:
          K.bool.ff({WCon{True{}, at} == WCon{False{}, bt} : Word(1n+p)}, Equal.trans(Bool, False{}, Cmp.is_eq(Word.cmp.fin(True{}, False{}, Word.cmp(p, at, bt))), True{},
            Equal.sym(Bool, Cmp.is_eq(Word.cmp.fin(True{}, False{}, Word.cmp(p, at, bt))), False{}, K.cmp.fin_tf(Word.cmp(p, at, bt))), h))

def agree.u32.cmp.eq(+a: U32, +b: U32, h: {U32.is_eq(a, b) == True{} : Bool}) -> {a == b : U32}:
  match a b:
    case U32{+aw} U32{+bw}:
      Equal.cong(Word(32n), U32, w => U32{w}, aw, bw, agree.word.cmp.eq(32n, aw, bw, h))

def agree.mem.head.false(+c: U32, +rest: List<&2, U32>, +o: U32,
  h: {K.Mem(Con{c, rest}, o) == False{} : Bool}) -> {U32.is_eq(c, o) == False{} : Bool}:
  match U32.is_eq(c, o):
    case False{}:
      {==}
    case True{}:
      K.bool.tf({True{} == False{} : Bool}, h)

def agree.mem.tail.false(+c: U32, +rest: List<&2, U32>, +o: U32,
  h: {K.Mem(Con{c, rest}, o) == False{} : Bool}) -> {K.Mem(rest, o) == False{} : Bool}:
  match U32.is_eq(c, o):
    case False{}:
      h
    case True{}:
      K.bool.tf({K.Mem(rest, o) == False{} : Bool}, h)

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

def agree.store1.field(same: Bool, +m: Cr.Cir.Cells, +o: U32, +c: U32, +v: U32, +k: Nat,
  +eq: {U32.is_eq(o, c) == same : Bool}, field: {Cr.Cir.Cell.get(k, Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, o), v)) == Cr.Cir.Cell.get(k, Cr.Cir.Cells.get(m, o)) : U32}) ->
  {U32.is_eq(Hp.Fd(k, Cr.Cir.Cells.set(m, o, Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, o), v)), c), Hp.Fd(k, m, c)) == True{} : Bool}:
  match same:
    case True{}:
      +hidx = agree.u32.cmp.eq(o, c, eq)
      +hread = Equal.trans(Cr.Cir.Cell, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, o, Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, o), v)), c),
        Bool.pick(Cr.Cir.Cell, U32.is_eq(o, c), Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, o), v), Cr.Cir.Cells.get(m, c)),
        Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, o), v), Lg.cells.get_set(m, o, Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, o), v), c),
        Equal.cong(Bool, Cr.Cir.Cell, b => Bool.pick(Cr.Cir.Cell, b, Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, o), v), Cr.Cir.Cells.get(m, c)),
          U32.is_eq(o, c), same, eq))
      +hfield = Equal.cong(Cr.Cir.Cell, U32, cell => Cr.Cir.Cell.get(k, cell),
        Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, o, Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, o), v)), c),
        Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, o), v), hread)
      +hvalue = Equal.trans(U32,
        Hp.Fd(k, Cr.Cir.Cells.set(m, o, Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, o), v)), c),
        Cr.Cir.Cell.get(k, Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, o), v)), Hp.Fd(k, m, c), hfield,
        Equal.trans(U32, Cr.Cir.Cell.get(k, Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, o), v)), Cr.Cir.Cell.get(k, Cr.Cir.Cells.get(m, o)), Hp.Fd(k, m, c),
          field, Equal.cong(U32, U32, z => Cr.Cir.Cell.get(k, Cr.Cir.Cells.get(m, z)), o, c, hidx)))
      Equal.trans(Bool,
        U32.is_eq(Hp.Fd(k, Cr.Cir.Cells.set(m, o, Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, o), v)), c), Hp.Fd(k, m, c)),
        U32.is_eq(Hp.Fd(k, m, c), Hp.Fd(k, m, c)), True{},
        Equal.cong(U32, Bool, z => U32.is_eq(z, Hp.Fd(k, m, c)),
          Hp.Fd(k, Cr.Cir.Cells.set(m, o, Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, o), v)), c), Hp.Fd(k, m, c), hvalue),
        agree.u32.eq.refl(Hp.Fd(k, m, c)))
    case False{}:
      +hread = Equal.trans(Cr.Cir.Cell, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, o, Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, o), v)), c),
        Bool.pick(Cr.Cir.Cell, U32.is_eq(o, c), Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, o), v), Cr.Cir.Cells.get(m, c)),
        Cr.Cir.Cells.get(m, c), Lg.cells.get_set(m, o, Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, o), v), c),
        Equal.cong(Bool, Cr.Cir.Cell, b => Bool.pick(Cr.Cir.Cell, b, Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, o), v), Cr.Cir.Cells.get(m, c)),
          U32.is_eq(o, c), same, eq))
      +hvalue = Equal.cong(Cr.Cir.Cell, U32, cell => Cr.Cir.Cell.get(k, cell),
        Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, o, Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, o), v)), c),
        Cr.Cir.Cells.get(m, c), hread)
      Equal.trans(Bool,
        U32.is_eq(Hp.Fd(k, Cr.Cir.Cells.set(m, o, Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, o), v)), c), Hp.Fd(k, m, c)),
        U32.is_eq(Hp.Fd(k, m, c), Hp.Fd(k, m, c)), True{},
        Equal.cong(U32, Bool, z => U32.is_eq(z, Hp.Fd(k, m, c)),
          Hp.Fd(k, Cr.Cir.Cells.set(m, o, Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, o), v)), c), Hp.Fd(k, m, c), hvalue),
        agree.u32.eq.refl(Hp.Fd(k, m, c)))

def Hp.agree.store1(cs, m, o, v):
  match cs:
    case Nil{}:
      {==}
    case Con{c, rest}:
      +e0 = agree.store1.field(U32.is_eq(o, c), m, o, c, v, 0n, {==}, Lg.cell.get_set(1n, Cr.Cir.Cells.get(m, o), v, 0n, {==}, {==}))
      +e2 = agree.store1.field(U32.is_eq(o, c), m, o, c, v, 2n, {==}, Lg.cell.get_set(1n, Cr.Cir.Cells.get(m, o), v, 2n, {==}, {==}))
      +e3 = agree.store1.field(U32.is_eq(o, c), m, o, c, v, 3n, {==}, Lg.cell.get_set(1n, Cr.Cir.Cells.get(m, o), v, 3n, {==}, {==}))
      +e4 = agree.store1.field(U32.is_eq(o, c), m, o, c, v, 4n, {==}, Lg.cell.get_set(1n, Cr.Cir.Cells.get(m, o), v, 4n, {==}, {==}))
      +h02 = K.bool.and_i(U32.is_eq(Hp.Fd(0n, Cr.Cir.Cells.set(m, o, Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, o), v)), c), Hp.Fd(0n, m, c)),
        U32.is_eq(Hp.Fd(2n, Cr.Cir.Cells.set(m, o, Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, o), v)), c), Hp.Fd(2n, m, c)), e0, e2)
      +h023 = K.bool.and_i(Bool.and(U32.is_eq(Hp.Fd(0n, Cr.Cir.Cells.set(m, o, Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, o), v)), c), Hp.Fd(0n, m, c)),
        U32.is_eq(Hp.Fd(2n, Cr.Cir.Cells.set(m, o, Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, o), v)), c), Hp.Fd(2n, m, c))),
        U32.is_eq(Hp.Fd(3n, Cr.Cir.Cells.set(m, o, Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, o), v)), c), Hp.Fd(3n, m, c)), h02, e3)
      +hsame = K.bool.and_i(Bool.and(Bool.and(U32.is_eq(Hp.Fd(0n, Cr.Cir.Cells.set(m, o, Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, o), v)), c), Hp.Fd(0n, m, c)),
        U32.is_eq(Hp.Fd(2n, Cr.Cir.Cells.set(m, o, Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, o), v)), c), Hp.Fd(2n, m, c))),
        U32.is_eq(Hp.Fd(3n, Cr.Cir.Cells.set(m, o, Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, o), v)), c), Hp.Fd(3n, m, c))),
        U32.is_eq(Hp.Fd(4n, Cr.Cir.Cells.set(m, o, Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, o), v)), c), Hp.Fd(4n, m, c)), h023, e4)
      K.bool.and_i(Hp.V.same(m, Cr.Cir.Cells.set(m, o, Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, o), v)), c), Hp.Agree(rest, m, Cr.Cir.Cells.set(m, o, Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, o), v))),
        hsame, Hp.agree.store1(rest, m, o, v))

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
