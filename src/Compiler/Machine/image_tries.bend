# compiler: the image's names, by their bits (layer B)
# ===================================================
#
# Img.trie finds a name in time of its length: a node's value sits where the
# name ends, its two children where the name goes on with a 0 or a 1 bit.
# put writes down the path of a name and set writes the value at its end.
# This file proves the walk: a byte's bits and the path of the name decide
# where a name ends, so put of one name does not move the end of another
# (get.put.other), and find reads back what put wrote (get.put.same). Then
# Img.ids and Img.refs give, for each name, the place of its first copy
# (Img.id) and the body of its first def (Img.ref).

import Base
import ../../Shared/shared.bend as Sd
import ./definitions.bend as D
import ./impl.bend as Mc
import ./image_names.bend as Nm
import ../need_big.bend as N

# Bits and paths
# --------------
#
# A bit picks a child; side writes it. at and with read and write the part
# of a trie under a word's bits.

# the child a bit picks, after side writes it
def bit.side.same(b: Bool, t: Mc.Img.Trie, c: Mc.Img.Trie) ->
  {Mc.Img.trie.bit(b, Mc.Img.trie.side(b, t, c)) == c : Mc.Img.Trie}:
  match b t:
    case False{} Mc.Img.Trie.none{}:
      {==}
    case False{} Mc.Img.Trie.node{v, z, o}:
      {==}
    case True{} Mc.Img.Trie.none{}:
      {==}
    case True{} Mc.Img.Trie.node{v, z, o}:
      {==}

# the other child stays what it was
def bit.side.other(b: Bool, b2: Bool, t: Mc.Img.Trie, c: Mc.Img.Trie, ne: {b == b2 : Bool} -> Empty) ->
  {Mc.Img.trie.bit(b2, Mc.Img.trie.side(b, t, c)) == Mc.Img.trie.bit(b2, t) : Mc.Img.Trie}:
  match b b2:
    case False{} False{}:
      Empty.absurd({Mc.Img.trie.bit(False{}, Mc.Img.trie.side(False{}, t, c)) == Mc.Img.trie.bit(False{}, t) : Mc.Img.Trie}, ne({==}))
    case False{} True{}:
      match t:
        case Mc.Img.Trie.none{}:
          {==}
        case Mc.Img.Trie.node{v, z, o}:
          {==}
    case True{} False{}:
      match t:
        case Mc.Img.Trie.none{}:
          {==}
        case Mc.Img.Trie.node{v, z, o}:
          {==}
    case True{} True{}:
      Empty.absurd({Mc.Img.trie.bit(True{}, Mc.Img.trie.side(True{}, t, c)) == Mc.Img.trie.bit(True{}, t) : Mc.Img.Trie}, ne({==}))

# the root's value is the trie's own
def side.v(b: Bool, t: Mc.Img.Trie, c: Mc.Img.Trie) ->
  {Mc.Img.trie.v(Mc.Img.trie.side(b, t, c)) == Mc.Img.trie.v(t) : Maybe<&2, U32>}:
  match b t:
    case False{} Mc.Img.Trie.none{}:
      {==}
    case False{} Mc.Img.Trie.node{v, z, o}:
      {==}
    case True{} Mc.Img.Trie.none{}:
      {==}
    case True{} Mc.Img.Trie.node{v, z, o}:
      {==}

# a bit of the trie does not change its root's value
def bit.set(b: Bool, t: Mc.Img.Trie, v: U32) ->
  {Mc.Img.trie.bit(b, Mc.Img.trie.set(t, v)) == Mc.Img.trie.bit(b, t) : Mc.Img.Trie}:
  match b t:
    case False{} Mc.Img.Trie.none{}:
      {==}
    case False{} Mc.Img.Trie.node{v0, z, o}:
      {==}
    case True{} Mc.Img.Trie.none{}:
      {==}
    case True{} Mc.Img.Trie.node{v0, z, o}:
      {==}

# a name of one bit or more: with does not change the root's value
def with.v.succ(+n: Nat, +w: Word(1n+n), +t: Mc.Img.Trie, +s: Mc.Img.Trie) ->
  {Mc.Img.trie.v(Mc.Img.trie.with(1n+n, w, t, s)) == Mc.Img.trie.v(t) : Maybe<&2, U32>}:
  match w:
    case WCon{+b, +r}:
      side.v(b, t, Mc.Img.trie.with(n, r, Mc.Img.trie.bit(b, t), s))

# at of with reads s at the name's own bits
def at.with.same(+n: Nat, +w: Word(n), +t: Mc.Img.Trie, +s: Mc.Img.Trie) ->
  {Mc.Img.trie.at(n, w, Mc.Img.trie.with(n, w, t, s)) == s : Mc.Img.Trie}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case Succ{+p}:
      match w:
        case WCon{+b, +r}:
          Equal.trans(Mc.Img.Trie,
            Mc.Img.trie.at(p, r, Mc.Img.trie.bit(b, Mc.Img.trie.side(b, t, Mc.Img.trie.with(p, r, Mc.Img.trie.bit(b, t), s)))),
            Mc.Img.trie.at(p, r, Mc.Img.trie.with(p, r, Mc.Img.trie.bit(b, t), s)), s,
            Equal.cong(Mc.Img.Trie, Mc.Img.Trie, z => Mc.Img.trie.at(p, r, z),
              Mc.Img.trie.bit(b, Mc.Img.trie.side(b, t, Mc.Img.trie.with(p, r, Mc.Img.trie.bit(b, t), s))),
              Mc.Img.trie.with(p, r, Mc.Img.trie.bit(b, t), s), bit.side.same(b, t, Mc.Img.trie.with(p, r, Mc.Img.trie.bit(b, t), s))),
            at.with.same(p, r, Mc.Img.trie.bit(b, t), s))

# at of another name's with reads what at did; the empty and the last byte
# split the recursion, the two heads decide which child stays
def at.with.other(+n: Nat, +w1: Word(n), +w2: Word(n), +t: Mc.Img.Trie, +s: Mc.Img.Trie,
  ne: {w1 == w2 : Word(n)} -> Empty) ->
  {Mc.Img.trie.at(n, w2, Mc.Img.trie.with(n, w1, t, s)) == Mc.Img.trie.at(n, w2, t) : Mc.Img.Trie}:
  match n:
    case 0n:
      match w1 w2:
        case WNil{} WNil{}:
          Empty.absurd({Mc.Img.trie.at(0n, WNil{}, Mc.Img.trie.with(0n, WNil{}, t, s)) == Mc.Img.trie.at(0n, WNil{}, t) : Mc.Img.Trie}, ne({==}))
    case Succ{+p}:
      match w1 w2:
        case WCon{False{}, +r1} WCon{False{}, +r2}:
          Equal.trans(Mc.Img.Trie,
            Mc.Img.trie.at(p, r2, Mc.Img.trie.bit(False{}, Mc.Img.trie.side(False{}, t, Mc.Img.trie.with(p, r1, Mc.Img.trie.bit(False{}, t), s)))),
            Mc.Img.trie.at(p, r2, Mc.Img.trie.with(p, r1, Mc.Img.trie.bit(False{}, t), s)),
            Mc.Img.trie.at(p, r2, Mc.Img.trie.bit(False{}, t)),
            Equal.cong(Mc.Img.Trie, Mc.Img.Trie, z => Mc.Img.trie.at(p, r2, z),
              Mc.Img.trie.bit(False{}, Mc.Img.trie.side(False{}, t, Mc.Img.trie.with(p, r1, Mc.Img.trie.bit(False{}, t), s))),
              Mc.Img.trie.with(p, r1, Mc.Img.trie.bit(False{}, t), s), bit.side.same(False{}, t, Mc.Img.trie.with(p, r1, Mc.Img.trie.bit(False{}, t), s))),
            at.with.other(p, r1, r2, Mc.Img.trie.bit(False{}, t), s,
              e => ne(Equal.cong(Word(p), Word(1n+p), z => WCon{False{}, z}, r1, r2, e))))
        case WCon{False{}, +r1} WCon{True{}, +r2}:
          Equal.cong(Mc.Img.Trie, Mc.Img.Trie, z => Mc.Img.trie.at(p, r2, z),
            Mc.Img.trie.bit(True{}, Mc.Img.trie.side(False{}, t, Mc.Img.trie.with(p, r1, Mc.Img.trie.bit(False{}, t), s))),
            Mc.Img.trie.bit(True{}, t),
            bit.side.other(False{}, True{}, t, Mc.Img.trie.with(p, r1, Mc.Img.trie.bit(False{}, t), s), e => D.bool.ft(Empty, e)))
        case WCon{True{}, +r1} WCon{False{}, +r2}:
          Equal.cong(Mc.Img.Trie, Mc.Img.Trie, z => Mc.Img.trie.at(p, r2, z),
            Mc.Img.trie.bit(False{}, Mc.Img.trie.side(True{}, t, Mc.Img.trie.with(p, r1, Mc.Img.trie.bit(True{}, t), s))),
            Mc.Img.trie.bit(False{}, t),
            bit.side.other(True{}, False{}, t, Mc.Img.trie.with(p, r1, Mc.Img.trie.bit(True{}, t), s), e => N.true_ne_false(e)))
        case WCon{True{}, +r1} WCon{True{}, +r2}:
          Equal.trans(Mc.Img.Trie,
            Mc.Img.trie.at(p, r2, Mc.Img.trie.bit(True{}, Mc.Img.trie.side(True{}, t, Mc.Img.trie.with(p, r1, Mc.Img.trie.bit(True{}, t), s)))),
            Mc.Img.trie.at(p, r2, Mc.Img.trie.with(p, r1, Mc.Img.trie.bit(True{}, t), s)),
            Mc.Img.trie.at(p, r2, Mc.Img.trie.bit(True{}, t)),
            Equal.cong(Mc.Img.Trie, Mc.Img.Trie, z => Mc.Img.trie.at(p, r2, z),
              Mc.Img.trie.bit(True{}, Mc.Img.trie.side(True{}, t, Mc.Img.trie.with(p, r1, Mc.Img.trie.bit(True{}, t), s))),
              Mc.Img.trie.with(p, r1, Mc.Img.trie.bit(True{}, t), s), bit.side.same(True{}, t, Mc.Img.trie.with(p, r1, Mc.Img.trie.bit(True{}, t), s))),
            at.with.other(p, r1, r2, Mc.Img.trie.bit(True{}, t), s,
              e => ne(Equal.cong(Word(p), Word(1n+p), z => WCon{True{}, z}, r1, r2, e))))

# a name of one bit or more: set does not change what at reads
def at.set.succ(+n: Nat, +w: Word(1n+n), +t: Mc.Img.Trie, +v: U32) ->
  {Mc.Img.trie.at(1n+n, w, Mc.Img.trie.set(t, v)) == Mc.Img.trie.at(1n+n, w, t) : Mc.Img.Trie}:
  match w:
    case WCon{+b, +r}:
      Equal.cong(Mc.Img.Trie, Mc.Img.Trie, z => Mc.Img.trie.at(n, r, z),
        Mc.Img.trie.bit(b, Mc.Img.trie.set(t, v)), Mc.Img.trie.bit(b, t), bit.set(b, t, v))

# Reading back what put wrote
# ---------------------------
#
# set writes a value at the end of a name; put writes at the end of a longer
# one and leaves the rest of the trie. These lemmas read it back.

# set writes its value at the root
def set.v(t: Mc.Img.Trie, v: U32) ->
  {Mc.Img.trie.v(Mc.Img.trie.set(t, v)) == Some{v} : Maybe<&2, U32>}:
  match t:
    case Mc.Img.Trie.none{}:
      {==}
    case Mc.Img.Trie.node{v0, z, o}:
      {==}

# put reads back at the name it wrote
def get.put.same(k: List<&2, Word(8n)>, +t: Mc.Img.Trie, +v: U32) ->
  {Mc.Img.trie.get(k, Mc.Img.trie.put(k, t, v)) == Some{v} : Maybe<&2, U32>}:
  match k:
    case Nil{}:
      set.v(t, v)
    case Con{+b, +rest}:
      Equal.trans(Maybe<&2, U32>,
        Mc.Img.trie.get(rest, Mc.Img.trie.at(8n, b, Mc.Img.trie.with(8n, b, t, Mc.Img.trie.put(rest, Mc.Img.trie.at(8n, b, t), v)))),
        Mc.Img.trie.get(rest, Mc.Img.trie.put(rest, Mc.Img.trie.at(8n, b, t), v)),
        Some{v},
        Equal.cong(Mc.Img.Trie, Maybe<&2, U32>, z => Mc.Img.trie.get(rest, z),
          Mc.Img.trie.at(8n, b, Mc.Img.trie.with(8n, b, t, Mc.Img.trie.put(rest, Mc.Img.trie.at(8n, b, t), v))),
          Mc.Img.trie.put(rest, Mc.Img.trie.at(8n, b, t), v),
          at.with.same(8n, b, t, Mc.Img.trie.put(rest, Mc.Img.trie.at(8n, b, t), v))),
        get.put.same(rest, Mc.Img.trie.at(8n, b, t), v))

# a byte equality decides its two sides
def byte.eq.is_true(x: Word(8n), y: Word(8n), e: {x == y : Word(8n)}) ->
  {Sd.Byte.is_eq(x, y) == True{} : Bool}:
  Equal.trans(Bool, Sd.Byte.is_eq(x, y), Sd.Byte.is_eq(y, y), True{},
    Equal.cong(Word(8n), Bool, z => Sd.Byte.is_eq(z, y), x, y, e),
    Nm.Byte.eq.refl(y))

# a byte equality at the root of a put's path: the rest of the trie reads
# through the same bits, so the two branches of the comparison give the same
# answer, and the walk on the rest of the byte never reaches the differing
# bit
def put.at.other(+n: Nat, +b1: Word(n), +b2: Word(n), +r1: List<&2, Word(8n)>, +r2: List<&2, Word(8n)>,
  +t: Mc.Img.Trie, +v: U32, ne: {b1 == b2 : Word(n)} -> Empty) ->
  {Mc.Img.trie.get(r2, Mc.Img.trie.at(n, b2, Mc.Img.trie.with(n, b1, t, Mc.Img.trie.put(r1, Mc.Img.trie.at(n, b1, t), v)))) ==
    Mc.Img.trie.get(r2, Mc.Img.trie.at(n, b2, t)) : Maybe<&2, U32>}:
  match n:
    case 0n:
      match b1 b2:
        case WNil{} WNil{}:
          Empty.absurd({Mc.Img.trie.get(r2, Mc.Img.trie.at(0n, WNil{}, Mc.Img.trie.with(0n, WNil{}, t, Mc.Img.trie.put(r1, Mc.Img.trie.at(0n, WNil{}, t), v)))) ==
            Mc.Img.trie.get(r2, Mc.Img.trie.at(0n, WNil{}, t)) : Maybe<&2, U32>}, ne({==}))
    case Succ{+p}:
      match b1 b2:
        case WCon{False{}, +a1} WCon{False{}, +a2}:
          Equal.trans(Maybe<&2, U32>,
            Mc.Img.trie.get(r2, Mc.Img.trie.at(p, a2, Mc.Img.trie.bit(False{}, Mc.Img.trie.side(False{}, t, Mc.Img.trie.with(p, a1, Mc.Img.trie.bit(False{}, t), Mc.Img.trie.put(r1, Mc.Img.trie.at(p, a1, Mc.Img.trie.bit(False{}, t)), v)))))),
            Mc.Img.trie.get(r2, Mc.Img.trie.at(p, a2, Mc.Img.trie.with(p, a1, Mc.Img.trie.bit(False{}, t), Mc.Img.trie.put(r1, Mc.Img.trie.at(p, a1, Mc.Img.trie.bit(False{}, t)), v)))),
            Mc.Img.trie.get(r2, Mc.Img.trie.at(p, a2, Mc.Img.trie.bit(False{}, t))),
            Equal.cong(Mc.Img.Trie, Maybe<&2, U32>, z => Mc.Img.trie.get(r2, Mc.Img.trie.at(p, a2, z)),
              Mc.Img.trie.bit(False{}, Mc.Img.trie.side(False{}, t, Mc.Img.trie.with(p, a1, Mc.Img.trie.bit(False{}, t), Mc.Img.trie.put(r1, Mc.Img.trie.at(p, a1, Mc.Img.trie.bit(False{}, t)), v)))),
              Mc.Img.trie.with(p, a1, Mc.Img.trie.bit(False{}, t), Mc.Img.trie.put(r1, Mc.Img.trie.at(p, a1, Mc.Img.trie.bit(False{}, t)), v)),
              bit.side.same(False{}, t, Mc.Img.trie.with(p, a1, Mc.Img.trie.bit(False{}, t), Mc.Img.trie.put(r1, Mc.Img.trie.at(p, a1, Mc.Img.trie.bit(False{}, t)), v)))),
            put.at.other(p, a1, a2, r1, r2, Mc.Img.trie.bit(False{}, t), v,
              z => ne(Equal.cong(Word(p), Word(1n+p), q => WCon{False{}, q}, a1, a2, z))))
        case WCon{False{}, +a1} WCon{True{}, +a2}:
          Equal.cong(Mc.Img.Trie, Maybe<&2, U32>, z => Mc.Img.trie.get(r2, Mc.Img.trie.at(p, a2, z)),
            Mc.Img.trie.bit(True{}, Mc.Img.trie.side(False{}, t, Mc.Img.trie.with(p, a1, Mc.Img.trie.bit(False{}, t), Mc.Img.trie.put(r1, Mc.Img.trie.at(p, a1, Mc.Img.trie.bit(False{}, t)), v)))),
            Mc.Img.trie.bit(True{}, t),
            bit.side.other(False{}, True{}, t, Mc.Img.trie.with(p, a1, Mc.Img.trie.bit(False{}, t), Mc.Img.trie.put(r1, Mc.Img.trie.at(p, a1, Mc.Img.trie.bit(False{}, t)), v)), z => D.bool.ft(Empty, z)))
        case WCon{True{}, +a1} WCon{False{}, +a2}:
          Equal.cong(Mc.Img.Trie, Maybe<&2, U32>, z => Mc.Img.trie.get(r2, Mc.Img.trie.at(p, a2, z)),
            Mc.Img.trie.bit(False{}, Mc.Img.trie.side(True{}, t, Mc.Img.trie.with(p, a1, Mc.Img.trie.bit(True{}, t), Mc.Img.trie.put(r1, Mc.Img.trie.at(p, a1, Mc.Img.trie.bit(True{}, t)), v)))),
            Mc.Img.trie.bit(False{}, t),
            bit.side.other(True{}, False{}, t, Mc.Img.trie.with(p, a1, Mc.Img.trie.bit(True{}, t), Mc.Img.trie.put(r1, Mc.Img.trie.at(p, a1, Mc.Img.trie.bit(True{}, t)), v)), z => N.true_ne_false(z)))
        case WCon{True{}, +a1} WCon{True{}, +a2}:
          Equal.trans(Maybe<&2, U32>,
            Mc.Img.trie.get(r2, Mc.Img.trie.at(p, a2, Mc.Img.trie.bit(True{}, Mc.Img.trie.side(True{}, t, Mc.Img.trie.with(p, a1, Mc.Img.trie.bit(True{}, t), Mc.Img.trie.put(r1, Mc.Img.trie.at(p, a1, Mc.Img.trie.bit(True{}, t)), v)))))),
            Mc.Img.trie.get(r2, Mc.Img.trie.at(p, a2, Mc.Img.trie.with(p, a1, Mc.Img.trie.bit(True{}, t), Mc.Img.trie.put(r1, Mc.Img.trie.at(p, a1, Mc.Img.trie.bit(True{}, t)), v)))),
            Mc.Img.trie.get(r2, Mc.Img.trie.at(p, a2, Mc.Img.trie.bit(True{}, t))),
            Equal.cong(Mc.Img.Trie, Maybe<&2, U32>, z => Mc.Img.trie.get(r2, Mc.Img.trie.at(p, a2, z)),
              Mc.Img.trie.bit(True{}, Mc.Img.trie.side(True{}, t, Mc.Img.trie.with(p, a1, Mc.Img.trie.bit(True{}, t), Mc.Img.trie.put(r1, Mc.Img.trie.at(p, a1, Mc.Img.trie.bit(True{}, t)), v)))),
              Mc.Img.trie.with(p, a1, Mc.Img.trie.bit(True{}, t), Mc.Img.trie.put(r1, Mc.Img.trie.at(p, a1, Mc.Img.trie.bit(True{}, t)), v)),
              bit.side.same(True{}, t, Mc.Img.trie.with(p, a1, Mc.Img.trie.bit(True{}, t), Mc.Img.trie.put(r1, Mc.Img.trie.at(p, a1, Mc.Img.trie.bit(True{}, t)), v)))),
            put.at.other(p, a1, a2, r1, r2, Mc.Img.trie.bit(True{}, t), v,
              z => ne(Equal.cong(Word(p), Word(1n+p), q => WCon{True{}, q}, a1, a2, z))))

# the two sides of a byte's comparison, each with what it gives
def byte.eq.split(b1: Word(8n), b2: Word(8n), b: Bool, hb: {Sd.Byte.is_eq(b1, b2) == b : Bool}, -G: Type,
  same: {b1 == b2 : Word(8n)} -> G, diff: ({b1 == b2 : Word(8n)} -> Empty) -> G) -> G:
  match b:
    case True{}:
      same(Nm.Byte.eq(b1, b2, hb))
    case False{}:
      diff(z => N.false_ne_true(Equal.trans(Bool, False{}, Sd.Byte.is_eq(b1, b2), True{},
        Equal.sym(Bool, Sd.Byte.is_eq(b1, b2), False{}, hb), byte.eq.is_true(b1, b2, z))))

# put at one name does not move what another reads
def get.put.other(+k1: List<&2, Word(8n)>, +k2: List<&2, Word(8n)>, +t: Mc.Img.Trie, +v: U32,
  ne: {k1 == k2 : List<&2, Word(8n)>} -> Empty) ->
  {Mc.Img.trie.get(k2, Mc.Img.trie.put(k1, t, v)) == Mc.Img.trie.get(k2, t) : Maybe<&2, U32>}:
  match k1 k2:
    case Nil{} Nil{}:
      Empty.absurd({Mc.Img.trie.get(Nil{}, Mc.Img.trie.put(Nil{}, t, v)) == Mc.Img.trie.get(Nil{}, t) : Maybe<&2, U32>}, ne({==}))
    case Nil{} Con{+b2, +r2}:
      Equal.cong(Mc.Img.Trie, Maybe<&2, U32>, z => Mc.Img.trie.get(r2, z),
        Mc.Img.trie.at(8n, b2, Mc.Img.trie.set(t, v)), Mc.Img.trie.at(8n, b2, t), at.set.succ(7n, b2, t, v))
    case Con{+b1, +r1} Nil{}:
      with.v.succ(7n, b1, t, Mc.Img.trie.put(r1, Mc.Img.trie.at(8n, b1, t), v))
    case Con{+b1, +r1} Con{+b2, +r2}:
      byte.eq.split(b1, b2, Sd.Byte.is_eq(b1, b2), {==},
        {Mc.Img.trie.get(Con{b2, r2}, Mc.Img.trie.put(Con{b1, r1}, t, v)) == Mc.Img.trie.get(Con{b2, r2}, t) : Maybe<&2, U32>},
        +eq =>
          Equal.trans(Maybe<&2, U32>,
            Mc.Img.trie.get(r2, Mc.Img.trie.at(8n, b2, Mc.Img.trie.with(8n, b1, t, Mc.Img.trie.put(r1, Mc.Img.trie.at(8n, b1, t), v)))),
            Mc.Img.trie.get(r2, Mc.Img.trie.at(8n, b1, Mc.Img.trie.with(8n, b1, t, Mc.Img.trie.put(r1, Mc.Img.trie.at(8n, b1, t), v)))),
            Mc.Img.trie.get(r2, Mc.Img.trie.at(8n, b2, t)),
            Equal.cong(Word(8n), Maybe<&2, U32>, z => Mc.Img.trie.get(r2, Mc.Img.trie.at(8n, z, Mc.Img.trie.with(8n, b1, t, Mc.Img.trie.put(r1, Mc.Img.trie.at(8n, b1, t), v)))),
              b2, b1, Equal.sym(Word(8n), b1, b2, eq)),
            Equal.trans(Maybe<&2, U32>,
              Mc.Img.trie.get(r2, Mc.Img.trie.at(8n, b1, Mc.Img.trie.with(8n, b1, t, Mc.Img.trie.put(r1, Mc.Img.trie.at(8n, b1, t), v)))),
              Mc.Img.trie.get(r2, Mc.Img.trie.put(r1, Mc.Img.trie.at(8n, b1, t), v)),
              Mc.Img.trie.get(r2, Mc.Img.trie.at(8n, b2, t)),
              Equal.cong(Mc.Img.Trie, Maybe<&2, U32>, z => Mc.Img.trie.get(r2, z),
                Mc.Img.trie.at(8n, b1, Mc.Img.trie.with(8n, b1, t, Mc.Img.trie.put(r1, Mc.Img.trie.at(8n, b1, t), v))),
                Mc.Img.trie.put(r1, Mc.Img.trie.at(8n, b1, t), v),
                at.with.same(8n, b1, t, Mc.Img.trie.put(r1, Mc.Img.trie.at(8n, b1, t), v))),
              Equal.trans(Maybe<&2, U32>,
                Mc.Img.trie.get(r2, Mc.Img.trie.put(r1, Mc.Img.trie.at(8n, b1, t), v)),
                Mc.Img.trie.get(r2, Mc.Img.trie.at(8n, b1, t)),
                Mc.Img.trie.get(r2, Mc.Img.trie.at(8n, b2, t)),
                get.put.other(r1, r2, Mc.Img.trie.at(8n, b1, t), v,
                  z => ne(Equal.trans(List<&2, Word(8n)>, Con{b1, r1}, Con{b2, r1}, Con{b2, r2},
                    Equal.cong(Word(8n), List<&2, Word(8n)>, q => Con{q, r1}, b1, b2, eq),
                    Equal.cong(List<&2, Word(8n)>, List<&2, Word(8n)>, q => Con{b2, q}, r1, r2, z)))),
                Equal.cong(Word(8n), Maybe<&2, U32>, z => Mc.Img.trie.get(r2, Mc.Img.trie.at(8n, z, t)), b1, b2, eq)))),
        neq => put.at.other(8n, b1, b2, r1, r2, t, v, neq))
