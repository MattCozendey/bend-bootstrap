# compiler: the image's names and their numbers (layer B)
# =======================================================
#
# The image numbers each name of a label or a λ-match once (Img.id, Img.ids)
# and gives each Ref the cell of the body of its name's first def (Img.ref,
# Img.refs). Both go through a trie of the names' bits (Img.trie). This file
# proves what the machine reads back: a word's equality from its bits
# (Word.eq.cmp), a trie's lookup of the names it was built from, and that
# Img.id gives the place of a name's first copy in Img.names.

import Base
import ../../Shared/shared.bend as Sd
import ./definitions.bend as D
import ./impl.bend as Mc
import ../need_big.bend as N

# Words and names
# ---------------
#
# Cmp.is_eq reads equality: Byte.is_eq is Word.cmp's EQ, and Name.is_eq is
# Byte.is_eq on each byte.

# cmp.fin's EQ is the tail's EQ with equal heads
def cmp.fin.eq.cmp(ab: Bool, bb: Bool, t: Cmp, h: {Cmp.is_eq(Word.cmp.fin(ab, bb, t)) == True{} : Bool}) ->
  {t == EQ{} : Cmp}:
  match ab bb:
    case False{} False{}:
      match t:
        case LT{}:
          D.bool.ft({LT{} == EQ{} : Cmp}, h)
        case EQ{}:
          {==}
        case GT{}:
          D.bool.ft({GT{} == EQ{} : Cmp}, h)
    case False{} True{}:
      match t:
        case LT{}:
          D.bool.ft({LT{} == EQ{} : Cmp}, h)
        case EQ{}:
          D.bool.ft({EQ{} == EQ{} : Cmp}, h)
        case GT{}:
          D.bool.ft({GT{} == EQ{} : Cmp}, h)
    case True{} False{}:
      match t:
        case LT{}:
          D.bool.ft({LT{} == EQ{} : Cmp}, h)
        case EQ{}:
          D.bool.ft({EQ{} == EQ{} : Cmp}, h)
        case GT{}:
          D.bool.ft({GT{} == EQ{} : Cmp}, h)
    case True{} True{}:
      match t:
        case LT{}:
          D.bool.ft({LT{} == EQ{} : Cmp}, h)
        case EQ{}:
          {==}
        case GT{}:
          D.bool.ft({GT{} == EQ{} : Cmp}, h)

# cmp.fin's EQ makes the heads equal
def cmp.fin.eq.bool(ab: Bool, bb: Bool, t: Cmp, h: {Cmp.is_eq(Word.cmp.fin(ab, bb, t)) == True{} : Bool}) ->
  {ab == bb : Bool}:
  match ab bb:
    case False{} False{}:
      {==}
    case False{} True{}:
      match t:
        case LT{}:
          D.bool.ft({False{} == True{} : Bool}, h)
        case EQ{}:
          D.bool.ft({False{} == True{} : Bool}, h)
        case GT{}:
          D.bool.ft({False{} == True{} : Bool}, h)
    case True{} False{}:
      match t:
        case LT{}:
          D.bool.ft({True{} == False{} : Bool}, h)
        case EQ{}:
          D.bool.ft({True{} == False{} : Bool}, h)
        case GT{}:
          D.bool.ft({True{} == False{} : Bool}, h)
    case True{} True{}:
      {==}

# is_eq of a comparison that is EQ
def h3.of(c: Cmp, h: {c == EQ{} : Cmp}) -> {Cmp.is_eq(c) == True{} : Bool}:
  %Equal.sym(Cmp, c, EQ{}, h) : {Cmp.is_eq(_) == True{} : Bool}
  {==}

# a word whose bits compare EQ is equal to the other; the + binders: the
# kernel's usage measure lets only a Many binder serve each use
def Word.eq.cmp(n: Nat, +a: Word(n), +b: Word(n), +h: {Cmp.is_eq(Word.cmp(n, a, b)) == True{} : Bool}) ->
  {a == b : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case Succ{+p}:
      match a b:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          +c = Word.cmp(p, at, bt)
          +h1 = cmp.fin.eq.cmp(ab, bb, c, h)
          +h2 = cmp.fin.eq.bool(ab, bb, c, h)
          +e3 = Word.eq.cmp(p, at, bt, h3.of(c, h1))
          %h2 : {WCon{ab, at} == WCon{_, bt} : Word(1n+p)}
          %e3 : {WCon{ab, at} == WCon{ab, _} : Word(1n+p)}
          {==}

# a byte whose comparison says EQ is the same byte
def Byte.eq(x: Word(8n), y: Word(8n), h: {Sd.Byte.is_eq(x, y) == True{} : Bool}) -> {x == y : Word(8n)}:
  Word.eq.cmp(8n, x, y, h)
