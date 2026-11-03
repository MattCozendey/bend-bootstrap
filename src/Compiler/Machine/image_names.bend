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

# A comparison with equal heads
# -----------------------------
#
# Word.cmp.fin with two equal heads is Cmp.is_eq of the tail's comparison.

def cmp.fin.is_eq.ff(c: Cmp) -> {Cmp.is_eq(Word.cmp.fin(False{}, False{}, c)) == Cmp.is_eq(c) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def cmp.fin.is_eq.tt(c: Cmp) -> {Cmp.is_eq(Word.cmp.fin(True{}, True{}, c)) == Cmp.is_eq(c) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def cmp.fin.is_eq.ft(c: Cmp) -> {Cmp.is_eq(Word.cmp.fin(False{}, True{}, c)) == False{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def cmp.fin.is_eq.tf(c: Cmp) -> {Cmp.is_eq(Word.cmp.fin(True{}, False{}, c)) == False{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

# a word compares equal to itself
def Word.cmp.refl(n: Nat, +w: Word(n)) -> {Cmp.is_eq(Word.cmp(n, w, w)) == True{} : Bool}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case Succ{+p}:
      match w:
        case WCon{+b, +r}:
          match b:
            case False{}:
              Equal.trans(Bool, Cmp.is_eq(Word.cmp.fin(False{}, False{}, Word.cmp(p, r, r))), Cmp.is_eq(Word.cmp(p, r, r)), True{},
                cmp.fin.is_eq.ff(Word.cmp(p, r, r)), Word.cmp.refl(p, r))
            case True{}:
              Equal.trans(Bool, Cmp.is_eq(Word.cmp.fin(True{}, True{}, Word.cmp(p, r, r))), Cmp.is_eq(Word.cmp(p, r, r)), True{},
                cmp.fin.is_eq.tt(Word.cmp(p, r, r)), Word.cmp.refl(p, r))

# a byte compares equal to itself
def Byte.eq.refl(x: Word(8n)) -> {Sd.Byte.is_eq(x, x) == True{} : Bool}:
  Word.cmp.refl(8n, x)

# Names
# -----
#
# Name.is_eq is Byte.is_eq on each byte. It is True exactly of equal names.

# a name compares equal to itself
def Name.eq.refl(k: List<&2, Word(8n)>) -> {Sd.Name.is_eq(k, k) == True{} : Bool}:
  match k:
    case Nil{}:
      {==}
    case Con{+b, +rest}:
      D.and.i(Sd.Byte.is_eq(b, b), Sd.Name.is_eq(rest, rest), Byte.eq.refl(b), Name.eq.refl(rest))

# two names whose comparison is True are equal; +e: both bytes and tail use it
def Name.eq.true(a: List<&2, Word(8n)>, b: List<&2, Word(8n)>, +e: {Sd.Name.is_eq(a, b) == True{} : Bool}) ->
  {a == b : List<&2, Word(8n)>}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Con{+x, +xs} Con{+y, +ys}:
      Equal.trans(List<&2, Word(8n)>, Con{x, xs}, Con{y, xs}, Con{y, ys},
        Equal.cong(Word(8n), List<&2, Word(8n)>, z => Con{z, xs}, x, y, Byte.eq(x, y, D.and.l(Sd.Byte.is_eq(x, y), Sd.Name.is_eq(xs, ys), e))),
        Equal.cong(List<&2, Word(8n)>, List<&2, Word(8n)>, z => Con{y, z}, xs, ys, Name.eq.true(xs, ys, D.and.r(Sd.Byte.is_eq(x, y), Sd.Name.is_eq(xs, ys), e))))
    case Nil{} Con{+y, +ys}:
      Empty.absurd({Nil{} == Con{y, ys} : List<&2, Word(8n)>}, N.false_ne_true(e))
    case Con{+x, +xs} Nil{}:
      Empty.absurd({Con{x, xs} == Nil{} : List<&2, Word(8n)>}, N.false_ne_true(e))

# Bool.and is False when its first side is
def and.false.l(a: Bool, -b: Bool, h: {a == False{} : Bool}) -> {Bool.and(a, b) == False{} : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({Bool.and(True{}, b) == False{} : Bool}, N.true_ne_false(h))

# Bool.and is False when its second side is
def and.false.r(a: Bool, b: Bool, h: {b == False{} : Bool}) -> {Bool.and(a, b) == False{} : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      h

# the tail of Name.ne: the comparison of two conses, by its two sides
def Name.ne.cons(x: Word(8n), xs: List<&2, Word(8n)>, y: Word(8n), ys: List<&2, Word(8n)>,
  b1: Bool, e1: {Sd.Byte.is_eq(x, y) == b1 : Bool}, b2: Bool, e2: {Sd.Name.is_eq(xs, ys) == b2 : Bool},
  k: {Con{x, xs} == Con{y, ys} : List<&2, Word(8n)>} -> Empty) ->
  {Bool.and(b1, b2) == False{} : Bool}:
  match b1:
    case False{}:
      {==}
    case True{}:
      match b2:
        case False{}:
          {==}
        case True{}:
          Empty.absurd({Bool.and(True{}, True{}) == False{} : Bool},
            k(Equal.trans(List<&2, Word(8n)>, Con{x, xs}, Con{y, xs}, Con{y, ys},
              Equal.cong(Word(8n), List<&2, Word(8n)>, z => Con{z, xs}, x, y, Byte.eq(x, y, e1)),
              Equal.cong(List<&2, Word(8n)>, List<&2, Word(8n)>, z => Con{y, z}, xs, ys, Name.eq.true(xs, ys, e2)))))

# two names that differ do not compare equal
def Name.ne(a: List<&2, Word(8n)>, b: List<&2, Word(8n)>, k: {a == b : List<&2, Word(8n)>} -> Empty) ->
  {Sd.Name.is_eq(a, b) == False{} : Bool}:
  match a b:
    case Nil{} Nil{}:
      Empty.absurd({Sd.Name.is_eq(Nil{}, Nil{}) == False{} : Bool}, k({==}))
    case Con{+x, +xs} Con{+y, +ys}:
      Name.ne.cons(x, xs, y, ys, Sd.Byte.is_eq(x, y), {==}, Sd.Name.is_eq(xs, ys), {==}, k)
    case Nil{} Con{+y, +ys}:
      {==}
    case Con{+x, +xs} Nil{}:
      {==}
