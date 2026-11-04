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

# gen2 --ind: a helper lemma (proven)
def mask.and_or.i1(+n: Nat, +aw: Word(n), +bw: Word(n), +mw: Word(n)) ->
  {Word.and(n, Word.or(n, aw, bw), mw) == Word.or(n, Word.and(n, aw, mw), Word.and(n, bw, mw)) : Word(n)}:
  match n:
    case 0n:
      match aw bw mw:
        case WNil{} WNil{} WNil{}:
          {==}
    case 1n+p:
      match aw bw mw:
        case WCon{False{}, awt} WCon{False{}, bwt} WCon{False{}, mwt}:
          (%Equal.sym(Word(p), Word.and(p, Word.or(p, awt, bwt), mwt), Word.or(p, Word.and(p, awt, mwt), Word.and(p, bwt, mwt)), mask.and_or.i1(p, awt, bwt, mwt)) : {WCon{False{}, _} == WCon{False{}, Word.or(p, Word.and(p, awt, mwt), Word.and(p, bwt, mwt))} : Word(1n+p)}; {==})
        case WCon{False{}, awt} WCon{False{}, bwt} WCon{True{}, mwt}:
          (%Equal.sym(Word(p), Word.and(p, Word.or(p, awt, bwt), mwt), Word.or(p, Word.and(p, awt, mwt), Word.and(p, bwt, mwt)), mask.and_or.i1(p, awt, bwt, mwt)) : {WCon{False{}, _} == WCon{False{}, Word.or(p, Word.and(p, awt, mwt), Word.and(p, bwt, mwt))} : Word(1n+p)}; {==})
        case WCon{False{}, awt} WCon{True{}, bwt} WCon{False{}, mwt}:
          (%Equal.sym(Word(p), Word.and(p, Word.or(p, awt, bwt), mwt), Word.or(p, Word.and(p, awt, mwt), Word.and(p, bwt, mwt)), mask.and_or.i1(p, awt, bwt, mwt)) : {WCon{False{}, _} == WCon{False{}, Word.or(p, Word.and(p, awt, mwt), Word.and(p, bwt, mwt))} : Word(1n+p)}; {==})
        case WCon{False{}, awt} WCon{True{}, bwt} WCon{True{}, mwt}:
          (%Equal.sym(Word(p), Word.and(p, Word.or(p, awt, bwt), mwt), Word.or(p, Word.and(p, awt, mwt), Word.and(p, bwt, mwt)), mask.and_or.i1(p, awt, bwt, mwt)) : {WCon{True{}, _} == WCon{True{}, Word.or(p, Word.and(p, awt, mwt), Word.and(p, bwt, mwt))} : Word(1n+p)}; {==})
        case WCon{True{}, awt} WCon{False{}, bwt} WCon{False{}, mwt}:
          (%Equal.sym(Word(p), Word.and(p, Word.or(p, awt, bwt), mwt), Word.or(p, Word.and(p, awt, mwt), Word.and(p, bwt, mwt)), mask.and_or.i1(p, awt, bwt, mwt)) : {WCon{False{}, _} == WCon{False{}, Word.or(p, Word.and(p, awt, mwt), Word.and(p, bwt, mwt))} : Word(1n+p)}; {==})
        case WCon{True{}, awt} WCon{False{}, bwt} WCon{True{}, mwt}:
          (%Equal.sym(Word(p), Word.and(p, Word.or(p, awt, bwt), mwt), Word.or(p, Word.and(p, awt, mwt), Word.and(p, bwt, mwt)), mask.and_or.i1(p, awt, bwt, mwt)) : {WCon{True{}, _} == WCon{True{}, Word.or(p, Word.and(p, awt, mwt), Word.and(p, bwt, mwt))} : Word(1n+p)}; {==})
        case WCon{True{}, awt} WCon{True{}, bwt} WCon{False{}, mwt}:
          (%Equal.sym(Word(p), Word.and(p, Word.or(p, awt, bwt), mwt), Word.or(p, Word.and(p, awt, mwt), Word.and(p, bwt, mwt)), mask.and_or.i1(p, awt, bwt, mwt)) : {WCon{False{}, _} == WCon{False{}, Word.or(p, Word.and(p, awt, mwt), Word.and(p, bwt, mwt))} : Word(1n+p)}; {==})
        case WCon{True{}, awt} WCon{True{}, bwt} WCon{True{}, mwt}:
          (%Equal.sym(Word(p), Word.and(p, Word.or(p, awt, bwt), mwt), Word.or(p, Word.and(p, awt, mwt), Word.and(p, bwt, mwt)), mask.and_or.i1(p, awt, bwt, mwt)) : {WCon{True{}, _} == WCon{True{}, Word.or(p, Word.and(p, awt, mwt), Word.and(p, bwt, mwt))} : Word(1n+p)}; {==})

def Hd.mask.and_or(a, b, m):
  match a b m:
    case U32{aw} U32{bw} U32{mw}:
      Equal.cong(Word(32n), U32, w => U32{w}, Word.and(32n, Word.or(32n, aw, bw), mw), Word.or(32n, Word.and(32n, aw, mw), Word.and(32n, bw, mw)), mask.and_or.i1(32n, aw, bw, mw))

# gen2 --ind: a helper lemma (proven)
def mask.and_and.i1(+n: Nat, +aw: Word(n), +bw: Word(n), +cw: Word(n)) ->
  {Word.and(n, Word.and(n, aw, bw), cw) == Word.and(n, aw, Word.and(n, bw, cw)) : Word(n)}:
  match n:
    case 0n:
      match aw bw cw:
        case WNil{} WNil{} WNil{}:
          {==}
    case 1n+p:
      match aw bw cw:
        case WCon{False{}, awt} WCon{False{}, bwt} WCon{False{}, cwt}:
          (%Equal.sym(Word(p), Word.and(p, Word.and(p, awt, bwt), cwt), Word.and(p, awt, Word.and(p, bwt, cwt)), mask.and_and.i1(p, awt, bwt, cwt)) : {WCon{False{}, _} == WCon{False{}, Word.and(p, awt, Word.and(p, bwt, cwt))} : Word(1n+p)}; {==})
        case WCon{False{}, awt} WCon{False{}, bwt} WCon{True{}, cwt}:
          (%Equal.sym(Word(p), Word.and(p, Word.and(p, awt, bwt), cwt), Word.and(p, awt, Word.and(p, bwt, cwt)), mask.and_and.i1(p, awt, bwt, cwt)) : {WCon{False{}, _} == WCon{False{}, Word.and(p, awt, Word.and(p, bwt, cwt))} : Word(1n+p)}; {==})
        case WCon{False{}, awt} WCon{True{}, bwt} WCon{False{}, cwt}:
          (%Equal.sym(Word(p), Word.and(p, Word.and(p, awt, bwt), cwt), Word.and(p, awt, Word.and(p, bwt, cwt)), mask.and_and.i1(p, awt, bwt, cwt)) : {WCon{False{}, _} == WCon{False{}, Word.and(p, awt, Word.and(p, bwt, cwt))} : Word(1n+p)}; {==})
        case WCon{False{}, awt} WCon{True{}, bwt} WCon{True{}, cwt}:
          (%Equal.sym(Word(p), Word.and(p, Word.and(p, awt, bwt), cwt), Word.and(p, awt, Word.and(p, bwt, cwt)), mask.and_and.i1(p, awt, bwt, cwt)) : {WCon{False{}, _} == WCon{False{}, Word.and(p, awt, Word.and(p, bwt, cwt))} : Word(1n+p)}; {==})
        case WCon{True{}, awt} WCon{False{}, bwt} WCon{False{}, cwt}:
          (%Equal.sym(Word(p), Word.and(p, Word.and(p, awt, bwt), cwt), Word.and(p, awt, Word.and(p, bwt, cwt)), mask.and_and.i1(p, awt, bwt, cwt)) : {WCon{False{}, _} == WCon{False{}, Word.and(p, awt, Word.and(p, bwt, cwt))} : Word(1n+p)}; {==})
        case WCon{True{}, awt} WCon{False{}, bwt} WCon{True{}, cwt}:
          (%Equal.sym(Word(p), Word.and(p, Word.and(p, awt, bwt), cwt), Word.and(p, awt, Word.and(p, bwt, cwt)), mask.and_and.i1(p, awt, bwt, cwt)) : {WCon{False{}, _} == WCon{False{}, Word.and(p, awt, Word.and(p, bwt, cwt))} : Word(1n+p)}; {==})
        case WCon{True{}, awt} WCon{True{}, bwt} WCon{False{}, cwt}:
          (%Equal.sym(Word(p), Word.and(p, Word.and(p, awt, bwt), cwt), Word.and(p, awt, Word.and(p, bwt, cwt)), mask.and_and.i1(p, awt, bwt, cwt)) : {WCon{False{}, _} == WCon{False{}, Word.and(p, awt, Word.and(p, bwt, cwt))} : Word(1n+p)}; {==})
        case WCon{True{}, awt} WCon{True{}, bwt} WCon{True{}, cwt}:
          (%Equal.sym(Word(p), Word.and(p, Word.and(p, awt, bwt), cwt), Word.and(p, awt, Word.and(p, bwt, cwt)), mask.and_and.i1(p, awt, bwt, cwt)) : {WCon{True{}, _} == WCon{True{}, Word.and(p, awt, Word.and(p, bwt, cwt))} : Word(1n+p)}; {==})

def Hd.mask.and_and(a, b, c):
  match a b c:
    case U32{aw} U32{bw} U32{cw}:
      Equal.cong(Word(32n), U32, w => U32{w}, Word.and(32n, Word.and(32n, aw, bw), cw), Word.and(32n, aw, Word.and(32n, bw, cw)), mask.and_and.i1(32n, aw, bw, cw))

def Hd.mask.and_shl(a, n, m):
  ?TODO

# gen2 --ind: a helper lemma (proven)
def mask.shr_or.i4(+p: Nat, +gwt: Word(p), +g1wt: Word(p)) ->
  {Word.shr.pad(p, Word.or(p, gwt, g1wt)) == Word.or(1n+p, Word.shr.pad(p, gwt), Word.shr.pad(p, g1wt)) : Word(1n+p)}:
  match p:
    case 0n:
      {==}
    case 1n+pp:
      match gwt:
        case WCon{head, tail}:
          match g1wt:
            case WCon{head1, tail1}:
              %Equal.sym(Word(1n+pp), Word.shr.pad(pp, Word.or(pp, tail, tail1)), Word.or(1n+pp, Word.shr.pad(pp, tail), Word.shr.pad(pp, tail1)), mask.shr_or.i4(pp, tail, tail1)) :
                {WCon{Bool.or(head, head1), _} == WCon{Bool.or(head, head1), Word.or(1n+pp, Word.shr.pad(pp, tail), Word.shr.pad(pp, tail1))} : Word(2n+pp)}
              {==}

# gen2 --ind: a helper lemma (proven)
def mask.shr_or.i3(+n: Nat, +gw: Word(n), +g1w: Word(n)) ->
  {Word.shr(n, Word.or(n, gw, g1w)) == Word.or(n, Word.shr(n, gw), Word.shr(n, g1w)) : Word(n)}:
  match n:
    case 0n:
      match gw g1w:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match gw g1w:
        case WCon{False{}, gwt} WCon{False{}, g1wt}:
          mask.shr_or.i4(p, gwt, g1wt)
        case WCon{False{}, gwt} WCon{True{}, g1wt}:
          mask.shr_or.i4(p, gwt, g1wt)
        case WCon{True{}, gwt} WCon{False{}, g1wt}:
          mask.shr_or.i4(p, gwt, g1wt)
        case WCon{True{}, gwt} WCon{True{}, g1wt}:
          mask.shr_or.i4(p, gwt, g1wt)

# gen2 --ind: a helper lemma (proven)
def mask.shr_or.i2(+g: U32, +g1: U32) ->
  {U32.shr(U32.or(g, g1)) == U32.or(U32.shr(g), U32.shr(g1)) : U32}:
  match g g1:
    case U32{gw} U32{g1w}:
      Equal.cong(Word(32n), U32, w => U32{w}, Word.shr(32n, Word.or(32n, gw, g1w)), Word.or(32n, Word.shr(32n, gw), Word.shr(32n, g1w)), mask.shr_or.i3(32n, gw, g1w))

def Hd.mask.shr_or(a, b, n):
  match n:
    case 0n:
      {==}
    case 1n+np:
      (%Equal.sym(U32, U32.shrn(U32.or(a, b), np), U32.or(U32.shrn(a, np), U32.shrn(b, np)), Hd.mask.shr_or(a, b, np)) : {U32.shr(_) == U32.or(U32.shr(U32.shrn(a, np)), U32.shr(U32.shrn(b, np))) : U32}; mask.shr_or.i2(U32.shrn(a, np), U32.shrn(b, np)))

# gen2 --ind: a helper lemma (proven)
def mask.shr_and.i4(+p: Nat, +gwt: Word(p), +g1wt: Word(p)) ->
  {Word.shr.pad(p, Word.and(p, gwt, g1wt)) == Word.and(1n+p, Word.shr.pad(p, gwt), Word.shr.pad(p, g1wt)) : Word(1n+p)}:
  match p:
    case 0n:
      {==}
    case 1n+pp:
      match gwt:
        case WCon{head, tail}:
          match g1wt:
            case WCon{head1, tail1}:
              %Equal.sym(Word(1n+pp), Word.shr.pad(pp, Word.and(pp, tail, tail1)), Word.and(1n+pp, Word.shr.pad(pp, tail), Word.shr.pad(pp, tail1)), mask.shr_and.i4(pp, tail, tail1)) :
                {WCon{Bool.and(head, head1), _} == WCon{Bool.and(head, head1), Word.and(1n+pp, Word.shr.pad(pp, tail), Word.shr.pad(pp, tail1))} : Word(2n+pp)}
              {==}

# gen2 --ind: a helper lemma (proven)
def mask.shr_and.i3(+n: Nat, +gw: Word(n), +g1w: Word(n)) ->
  {Word.shr(n, Word.and(n, gw, g1w)) == Word.and(n, Word.shr(n, gw), Word.shr(n, g1w)) : Word(n)}:
  match n:
    case 0n:
      match gw g1w:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match gw g1w:
        case WCon{False{}, gwt} WCon{False{}, g1wt}:
          mask.shr_and.i4(p, gwt, g1wt)
        case WCon{False{}, gwt} WCon{True{}, g1wt}:
          mask.shr_and.i4(p, gwt, g1wt)
        case WCon{True{}, gwt} WCon{False{}, g1wt}:
          mask.shr_and.i4(p, gwt, g1wt)
        case WCon{True{}, gwt} WCon{True{}, g1wt}:
          mask.shr_and.i4(p, gwt, g1wt)

# gen2 --ind: a helper lemma (proven)
def mask.shr_and.i2(+g: U32, +g1: U32) ->
  {U32.shr(U32.and(g, g1)) == U32.and(U32.shr(g), U32.shr(g1)) : U32}:
  match g g1:
    case U32{gw} U32{g1w}:
      Equal.cong(Word(32n), U32, w => U32{w}, Word.shr(32n, Word.and(32n, gw, g1w)), Word.and(32n, Word.shr(32n, gw), Word.shr(32n, g1w)), mask.shr_and.i3(32n, gw, g1w))

def Hd.mask.shr_and(a, m, n):
  match n:
    case 0n:
      {==}
    case 1n+np:
      (%Equal.sym(U32, U32.shrn(U32.and(a, m), np), U32.and(U32.shrn(a, np), U32.shrn(m, np)), Hd.mask.shr_and(a, m, np)) : {U32.shr(_) == U32.and(U32.shr(U32.shrn(a, np)), U32.shr(U32.shrn(m, np))) : U32}; mask.shr_and.i2(U32.shrn(a, np), U32.shrn(m, np)))

def Hd.mask.shr_shl(a, n):
  ?TODO

# gen2 --ind: a helper lemma (proven)
def mask.or_zero.i1(+n: Nat, +aw: Word(n)) ->
  {Word.or(n, aw, Word.zero(n)) == aw : Word(n)}:
  match n:
    case 0n:
      match aw:
        case WNil{}:
          {==}
    case 1n+p:
      match aw:
        case WCon{False{}, awt}:
          (%Equal.sym(Word(p), Word.or(p, awt, Word.zero(p)), awt, mask.or_zero.i1(p, awt)) : {WCon{False{}, _} == WCon{False{}, awt} : Word(1n+p)}; {==})
        case WCon{True{}, awt}:
          (%Equal.sym(Word(p), Word.or(p, awt, Word.zero(p)), awt, mask.or_zero.i1(p, awt)) : {WCon{True{}, _} == WCon{True{}, awt} : Word(1n+p)}; {==})

def Hd.mask.or_zero(a):
  match a:
    case U32{aw}:
      Equal.cong(Word(32n), U32, w => U32{w}, Word.or(32n, aw, Word.zero(32n)), aw, mask.or_zero.i1(32n, aw))

# gen2 --ind: a helper lemma (proven)
def mask.zero_or.i1(+n: Nat, +aw: Word(n)) ->
  {Word.or(n, Word.zero(n), aw) == aw : Word(n)}:
  match n:
    case 0n:
      match aw:
        case WNil{}:
          {==}
    case 1n+p:
      match aw:
        case WCon{False{}, awt}:
          (%Equal.sym(Word(p), Word.or(p, Word.zero(p), awt), awt, mask.zero_or.i1(p, awt)) : {WCon{False{}, _} == WCon{False{}, awt} : Word(1n+p)}; {==})
        case WCon{True{}, awt}:
          (%Equal.sym(Word(p), Word.or(p, Word.zero(p), awt), awt, mask.zero_or.i1(p, awt)) : {WCon{True{}, _} == WCon{True{}, awt} : Word(1n+p)}; {==})

def Hd.mask.zero_or(a):
  match a:
    case U32{aw}:
      Equal.cong(Word(32n), U32, w => U32{w}, Word.or(32n, Word.zero(32n), aw), aw, mask.zero_or.i1(32n, aw))

# gen2 --ind: a helper lemma (proven)
def mask.and_zero.i1(+n: Nat, +aw: Word(n)) ->
  {Word.and(n, aw, Word.zero(n)) == Word.zero(n) : Word(n)}:
  match n:
    case 0n:
      {==}
    case 1n+np:
      match aw:
        case WCon{head, tail}:
          match head:
            case False{}:
              %Equal.sym(Word(np), Word.and(np, tail, Word.zero(np)), Word.zero(np), mask.and_zero.i1(np, tail)) :
                {WCon{False{}, _} == WCon{False{}, Word.zero(np)} : Word(1n+np)}
              {==}
            case True{}:
              %Equal.sym(Word(np), Word.and(np, tail, Word.zero(np)), Word.zero(np), mask.and_zero.i1(np, tail)) :
                {WCon{False{}, _} == WCon{False{}, Word.zero(np)} : Word(1n+np)}
              {==}

def Hd.mask.and_zero(a):
  match a:
    case U32{aw}:
      Equal.cong(Word(32n), U32, w => U32{w}, Word.and(32n, aw, Word.zero(32n)), Word.zero(32n), mask.and_zero.i1(32n, aw))

# gen2 --ind: a helper lemma (proven)
def mask.zero_and.i1(+n: Nat, +aw: Word(n)) ->
  {Word.and(n, Word.zero(n), aw) == Word.zero(n) : Word(n)}:
  match n:
    case 0n:
      {==}
    case 1n+np:
      match aw:
        case WCon{head, tail}:
          %Equal.sym(Word(np), Word.and(np, Word.zero(np), tail), Word.zero(np), mask.zero_and.i1(np, tail)) :
            {WCon{False{}, _} == WCon{False{}, Word.zero(np)} : Word(1n+np)}
          {==}

def Hd.mask.zero_and(a):
  match a:
    case U32{aw}:
      Equal.cong(Word(32n), U32, w => U32{w}, Word.and(32n, Word.zero(32n), aw), Word.zero(32n), mask.zero_and.i1(32n, aw))

def Hd.mask.and_low(a, k, h):
  ?TODO

def Hd.mask.shr_low(a, k, h):
  ?TODO

def Hd.mask.sub_bit(h, b, e):
  ?TODO

