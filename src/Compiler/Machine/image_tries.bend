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

# Reading back
# ------------
#
# A pass over a list of names adds each name to a trie. To say what the trie
# answers at a name, maybe.of reads a Maybe with a default: the value that
# the pass would store, or the value that the trie already had.

# a Maybe as a number: its value, or d
def maybe.of(r: Maybe<&2, U32>, d: U32) -> U32:
  match r:
    case None{}:
      d
    case Some{v}:
      v

def maybe.of.none(d: U32) -> {maybe.of(None{}, d) == d : U32}:
  {==}

def maybe.of.some(v: U32, d: U32) -> {maybe.of(Some{v}, d) == v : U32}:
  {==}

# find.of is maybe.of with 0
def find.of.maybe(r: Maybe<&2, U32>) -> {Mc.Img.trie.find.of(r) == maybe.of(r, 0) : U32}:
  match r:
    case None{}:
      {==}
    case Some{v}:
      {==}

# a Maybe, by its form; each side gets its equality
def maybe.split(r: Maybe<&2, U32>, -G: Type,
  none: {r == None{} : Maybe<&2, U32>} -> G,
  some: @v: U32 -> {r == Some{v} : Maybe<&2, U32>} -> G) -> G:
  match r:
    case None{}:
      none({==})
    case Some{v}:
      some(v, {==})

# a name equal to another compares equal to it
def name.is_eq.true(n: List<&2, Word(8n)>, k: List<&2, Word(8n)>, e: {n == k : List<&2, Word(8n)>}) ->
  {Sd.Name.is_eq(n, k) == True{} : Bool}:
  Equal.trans(Bool, Sd.Name.is_eq(n, k), Sd.Name.is_eq(k, k), True{},
    Equal.cong(List<&2, Word(8n)>, Bool, z => Sd.Name.is_eq(z, k), n, k, e),
    Nm.Name.eq.refl(k))

# a name whose comparison is False differs
def name.ne.of(n: List<&2, Word(8n)>, k: List<&2, Word(8n)>, +hb: {Sd.Name.is_eq(n, k) == False{} : Bool},
  e: {n == k : List<&2, Word(8n)>}) -> Empty:
  N.false_ne_true(Equal.trans(Bool, False{}, Sd.Name.is_eq(n, k), True{},
    Equal.sym(Bool, Sd.Name.is_eq(n, k), False{}, hb), name.is_eq.true(n, k, e)))

# the comparison of two names, by its two sides: each side gets its equality
def name.split(n: List<&2, Word(8n)>, k: List<&2, Word(8n)>, b: Bool, +hb: {Sd.Name.is_eq(n, k) == b : Bool}, -G: Type,
  same: {n == k : List<&2, Word(8n)>} -> {Sd.Name.is_eq(n, k) == True{} : Bool} -> G,
  diff: ({n == k : List<&2, Word(8n)>} -> Empty) -> {Sd.Name.is_eq(n, k) == False{} : Bool} -> G) -> G:
  match b:
    case True{}:
      same(Nm.Name.eq.true(n, k, hb), hb)
    case False{}:
      diff(z => name.ne.of(n, k, hb, z), hb)

# The value that add leaves at a name
# -----------------------------------
#
# add stores the value of a name unless the name has one. These four defs
# say what a read at a name k gives after add at a name n, by the
# comparison of n and k and by what the trie held at n.

def add.read.same.none(n: List<&2, Word(8n)>, +at: U32, +t: Mc.Img.Trie, +k: List<&2, Word(8n)>, +d: U32,
  +eq: {n == k : List<&2, Word(8n)>}, hb: {Sd.Name.is_eq(n, k) == True{} : Bool},
  +hr: {Mc.Img.trie.get(n, t) == None{} : Maybe<&2, U32>}) ->
  {maybe.of(Mc.Img.trie.get(k, Mc.Img.trie.add.if(Mc.Img.trie.get(n, t), t, n, at)), d) ==
   maybe.of(Mc.Img.trie.get(k, t), Mc.Img.ref.if(Sd.Name.is_eq(n, k), at, u => d)) : U32}:
  %Equal.sym(Bool, Sd.Name.is_eq(n, k), True{}, hb) :
    {maybe.of(Mc.Img.trie.get(k, Mc.Img.trie.add.if(Mc.Img.trie.get(n, t), t, n, at)), d) == maybe.of(Mc.Img.trie.get(k, t), Mc.Img.ref.if(_, at, u => d)) : U32}
  %Equal.sym(Maybe<&2, U32>, Mc.Img.trie.get(n, t), None{}, hr) :
    {maybe.of(Mc.Img.trie.get(k, Mc.Img.trie.add.if(_, t, n, at)), d) == maybe.of(Mc.Img.trie.get(k, t), Mc.Img.ref.if(True{}, at, u => d)) : U32}
  %Equal.sym(List<&2, Word(8n)>, n, k, eq) :
    {maybe.of(Mc.Img.trie.get(k, Mc.Img.trie.add.if(None{}, t, _, at)), d) == maybe.of(Mc.Img.trie.get(k, t), Mc.Img.ref.if(True{}, at, u => d)) : U32}
  +h2 = Equal.trans(Maybe<&2, U32>, Mc.Img.trie.get(k, t), Mc.Img.trie.get(n, t), None{},
    Equal.cong(List<&2, Word(8n)>, Maybe<&2, U32>, z => Mc.Img.trie.get(z, t), k, n, Equal.sym(List<&2, Word(8n)>, n, k, eq)),
    hr)
  Equal.trans(U32,
    maybe.of(Mc.Img.trie.get(k, Mc.Img.trie.put(k, t, at)), d),
    at,
    maybe.of(Mc.Img.trie.get(k, t), at),
    Equal.trans(U32,
      maybe.of(Mc.Img.trie.get(k, Mc.Img.trie.put(k, t, at)), d),
      maybe.of(Some{at}, d),
      at,
      Equal.cong(Maybe<&2, U32>, U32, z => maybe.of(z, d), Mc.Img.trie.get(k, Mc.Img.trie.put(k, t, at)), Some{at}, get.put.same(k, t, at)),
      maybe.of.some(at, d)),
    Equal.sym(U32,
      maybe.of(Mc.Img.trie.get(k, t), at),
      at,
      Equal.trans(U32,
        maybe.of(Mc.Img.trie.get(k, t), at),
        maybe.of(None{}, at),
        at,
        Equal.cong(Maybe<&2, U32>, U32, z => maybe.of(z, at), Mc.Img.trie.get(k, t), None{}, h2),
        maybe.of.none(at))))

def add.read.same.some(n: List<&2, Word(8n)>, +at: U32, +t: Mc.Img.Trie, +k: List<&2, Word(8n)>, +d: U32,
  eq: {n == k : List<&2, Word(8n)>}, hb: {Sd.Name.is_eq(n, k) == True{} : Bool}, +v: U32,
  +hs: {Mc.Img.trie.get(n, t) == Some{v} : Maybe<&2, U32>}) ->
  {maybe.of(Mc.Img.trie.get(k, Mc.Img.trie.add.if(Mc.Img.trie.get(n, t), t, n, at)), d) ==
   maybe.of(Mc.Img.trie.get(k, t), Mc.Img.ref.if(Sd.Name.is_eq(n, k), at, u => d)) : U32}:
  %Equal.sym(Bool, Sd.Name.is_eq(n, k), True{}, hb) :
    {maybe.of(Mc.Img.trie.get(k, Mc.Img.trie.add.if(Mc.Img.trie.get(n, t), t, n, at)), d) == maybe.of(Mc.Img.trie.get(k, t), Mc.Img.ref.if(_, at, u => d)) : U32}
  %Equal.sym(Maybe<&2, U32>, Mc.Img.trie.get(n, t), Some{v}, hs) :
    {maybe.of(Mc.Img.trie.get(k, Mc.Img.trie.add.if(_, t, n, at)), d) == maybe.of(Mc.Img.trie.get(k, t), Mc.Img.ref.if(True{}, at, u => d)) : U32}
  +h2 = Equal.trans(Maybe<&2, U32>, Mc.Img.trie.get(k, t), Mc.Img.trie.get(n, t), Some{v},
    Equal.cong(List<&2, Word(8n)>, Maybe<&2, U32>, z => Mc.Img.trie.get(z, t), k, n, Equal.sym(List<&2, Word(8n)>, n, k, eq)),
    hs)
  Equal.trans(U32,
    maybe.of(Mc.Img.trie.get(k, t), d),
    v,
    maybe.of(Mc.Img.trie.get(k, t), at),
    Equal.trans(U32, maybe.of(Mc.Img.trie.get(k, t), d), maybe.of(Some{v}, d), v,
      Equal.cong(Maybe<&2, U32>, U32, z => maybe.of(z, d), Mc.Img.trie.get(k, t), Some{v}, h2),
      maybe.of.some(v, d)),
    Equal.sym(U32, maybe.of(Mc.Img.trie.get(k, t), at), v,
      Equal.trans(U32, maybe.of(Mc.Img.trie.get(k, t), at), maybe.of(Some{v}, at), v,
        Equal.cong(Maybe<&2, U32>, U32, z => maybe.of(z, at), Mc.Img.trie.get(k, t), Some{v}, h2),
        maybe.of.some(v, at))))

def add.read.diff.none(n: List<&2, Word(8n)>, +at: U32, +t: Mc.Img.Trie, +k: List<&2, Word(8n)>, +d: U32,
  ne: {n == k : List<&2, Word(8n)>} -> Empty, hb: {Sd.Name.is_eq(n, k) == False{} : Bool},
  hr: {Mc.Img.trie.get(n, t) == None{} : Maybe<&2, U32>}) ->
  {maybe.of(Mc.Img.trie.get(k, Mc.Img.trie.add.if(Mc.Img.trie.get(n, t), t, n, at)), d) ==
   maybe.of(Mc.Img.trie.get(k, t), Mc.Img.ref.if(Sd.Name.is_eq(n, k), at, u => d)) : U32}:
  %Equal.sym(Bool, Sd.Name.is_eq(n, k), False{}, hb) :
    {maybe.of(Mc.Img.trie.get(k, Mc.Img.trie.add.if(Mc.Img.trie.get(n, t), t, n, at)), d) == maybe.of(Mc.Img.trie.get(k, t), Mc.Img.ref.if(_, at, u => d)) : U32}
  %Equal.sym(Maybe<&2, U32>, Mc.Img.trie.get(n, t), None{}, hr) :
    {maybe.of(Mc.Img.trie.get(k, Mc.Img.trie.add.if(_, t, n, at)), d) == maybe.of(Mc.Img.trie.get(k, t), Mc.Img.ref.if(False{}, at, u => d)) : U32}
  Equal.cong(Maybe<&2, U32>, U32, z => maybe.of(z, d),
    Mc.Img.trie.get(k, Mc.Img.trie.put(n, t, at)), Mc.Img.trie.get(k, t),
    get.put.other(n, k, t, at, ne))

def add.read.diff.some(n: List<&2, Word(8n)>, +at: U32, +t: Mc.Img.Trie, +k: List<&2, Word(8n)>, +d: U32,
  hb: {Sd.Name.is_eq(n, k) == False{} : Bool}, v: U32,
  hs: {Mc.Img.trie.get(n, t) == Some{v} : Maybe<&2, U32>}) ->
  {maybe.of(Mc.Img.trie.get(k, Mc.Img.trie.add.if(Mc.Img.trie.get(n, t), t, n, at)), d) ==
   maybe.of(Mc.Img.trie.get(k, t), Mc.Img.ref.if(Sd.Name.is_eq(n, k), at, u => d)) : U32}:
  %Equal.sym(Bool, Sd.Name.is_eq(n, k), False{}, hb) :
    {maybe.of(Mc.Img.trie.get(k, Mc.Img.trie.add.if(Mc.Img.trie.get(n, t), t, n, at)), d) == maybe.of(Mc.Img.trie.get(k, t), Mc.Img.ref.if(_, at, u => d)) : U32}
  %Equal.sym(Maybe<&2, U32>, Mc.Img.trie.get(n, t), Some{v}, hs) :
    {maybe.of(Mc.Img.trie.get(k, Mc.Img.trie.add.if(_, t, n, at)), d) == maybe.of(Mc.Img.trie.get(k, t), Mc.Img.ref.if(False{}, at, u => d)) : U32}
  {==}

# find of refs gives what Img.ref gives, or the value that the trie held
def refs.find(es: List<&2, Mc.Img.Def>, +t: Mc.Img.Trie, +k: List<&2, Word(8n)>) ->
  {Mc.Img.trie.find(Mc.Img.refs(es, t), k) == maybe.of(Mc.Img.trie.get(k, t), Mc.Img.ref(es, k)) : U32}:
  match es:
    case Nil{}:
      find.of.maybe(Mc.Img.trie.get(k, t))
    case Con{Mc.Img.Def{+n, +at}, +rest}:
      Equal.trans(U32,
        Mc.Img.trie.find(Mc.Img.refs(Con{Mc.Img.Def{n, at}, rest}, t), k),
        maybe.of(Mc.Img.trie.get(k, Mc.Img.trie.add(t, n, at)), Mc.Img.ref(rest, k)),
        maybe.of(Mc.Img.trie.get(k, t), Mc.Img.ref.if(Sd.Name.is_eq(n, k), at, u => Mc.Img.ref(rest, k))),
        refs.find(rest, Mc.Img.trie.add(t, n, at), k),
        name.split(n, k, Sd.Name.is_eq(n, k), {==},
          {maybe.of(Mc.Img.trie.get(k, Mc.Img.trie.add.if(Mc.Img.trie.get(n, t), t, n, at)), Mc.Img.ref(rest, k)) ==
           maybe.of(Mc.Img.trie.get(k, t), Mc.Img.ref.if(Sd.Name.is_eq(n, k), at, u => Mc.Img.ref(rest, k))) : U32},
          +eq => +hb =>
            maybe.split(Mc.Img.trie.get(n, t),
              {maybe.of(Mc.Img.trie.get(k, Mc.Img.trie.add.if(Mc.Img.trie.get(n, t), t, n, at)), Mc.Img.ref(rest, k)) ==
               maybe.of(Mc.Img.trie.get(k, t), Mc.Img.ref.if(Sd.Name.is_eq(n, k), at, u => Mc.Img.ref(rest, k))) : U32},
              hr => add.read.same.none(n, at, t, k, Mc.Img.ref(rest, k), eq, hb, hr),
              v => hs => add.read.same.some(n, at, t, k, Mc.Img.ref(rest, k), eq, hb, v, hs)),
          ne => +hb =>
            maybe.split(Mc.Img.trie.get(n, t),
              {maybe.of(Mc.Img.trie.get(k, Mc.Img.trie.add.if(Mc.Img.trie.get(n, t), t, n, at)), Mc.Img.ref(rest, k)) ==
               maybe.of(Mc.Img.trie.get(k, t), Mc.Img.ref.if(Sd.Name.is_eq(n, k), at, u => Mc.Img.ref(rest, k))) : U32},
              hr => add.read.diff.none(n, at, t, k, Mc.Img.ref(rest, k), ne, hb, hr),
              v => hs => add.read.diff.some(n, at, t, k, Mc.Img.ref(rest, k), hb, v, hs))))

# the part of an empty trie is empty
def at.none(n: Nat, +w: Word(n)) -> {Mc.Img.trie.at(n, w, Mc.Img.Trie.none{}) == Mc.Img.Trie.none{} : Mc.Img.Trie}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{+b, +r}:
          at.none(p, r)

# an empty trie holds no name
def get.none(k: List<&2, Word(8n)>) -> {Mc.Img.trie.get(k, Mc.Img.Trie.none{}) == None{} : Maybe<&2, U32>}:
  match k:
    case Nil{}:
      {==}
    case Con{+b, +rest}:
      Equal.trans(Maybe<&2, U32>,
        Mc.Img.trie.get(rest, Mc.Img.trie.at(8n, b, Mc.Img.Trie.none{})),
        Mc.Img.trie.get(rest, Mc.Img.Trie.none{}),
        None{},
        Equal.cong(Mc.Img.Trie, Maybe<&2, U32>, z => Mc.Img.trie.get(rest, z),
          Mc.Img.trie.at(8n, b, Mc.Img.Trie.none{}), Mc.Img.Trie.none{}, at.none(8n, b)),
        get.none(rest))

# find of refs from an empty trie is Img.ref
def find.refs(+es: List<&2, Mc.Img.Def>, +k: List<&2, Word(8n)>) ->
  {Mc.Img.trie.find(Mc.Img.refs(es, Mc.Img.Trie.none{}), k) == Mc.Img.ref(es, k) : U32}:
  Equal.trans(U32,
    Mc.Img.trie.find(Mc.Img.refs(es, Mc.Img.Trie.none{}), k),
    maybe.of(Mc.Img.trie.get(k, Mc.Img.Trie.none{}), Mc.Img.ref(es, k)),
    Mc.Img.ref(es, k),
    refs.find(es, Mc.Img.Trie.none{}, k),
    Equal.trans(U32,
      maybe.of(Mc.Img.trie.get(k, Mc.Img.Trie.none{}), Mc.Img.ref(es, k)),
      maybe.of(None{}, Mc.Img.ref(es, k)),
      Mc.Img.ref(es, k),
      Equal.cong(Maybe<&2, U32>, U32, z => maybe.of(z, Mc.Img.ref(es, k)),
        Mc.Img.trie.get(k, Mc.Img.Trie.none{}), None{}, get.none(k)),
      maybe.of.none(Mc.Img.ref(es, k))))

# The number of a name in ks
# --------------------------
#
# Img.ids numbers the names of ks in order, each at the place of its first
# copy: num.nat is that place, as a Nat, and first is the name there. They
# agree: the name at the place is the first copy.

# the place of the first copy of k in ks
def num.nat(ks: List<&2, List<&2, Word(8n)>>, +k: List<&2, Word(8n)>) -> Nat:
  match ks:
    case Nil{}:
      0n
    case Con{+n, +rest}:
      Bool.pick(Nat, Sd.Name.is_eq(n, k), 0n, 1n+num.nat(rest, k))

# the first copy of k in ks, if any
def first(ks: List<&2, List<&2, Word(8n)>>, +k: List<&2, Word(8n)>) -> Maybe<&2, List<&2, Word(8n)>>:
  match ks:
    case Nil{}:
      None{}
    case Con{+n, +rest}:
      Bool.pick(Maybe<&2, List<&2, Word(8n)>>, Sd.Name.is_eq(n, k), Some{n}, first(rest, k))

# Bool.pick at a side known True
def pick.true(-A: Type, b: Bool, t: A, f: A, h: {b == True{} : Bool}) -> {Bool.pick(A, b, t, f) == t : A}:
  %Equal.sym(Bool, b, True{}, h) : {Bool.pick(A, _, t, f) == t : A}
  {==}

# Bool.pick at a side known False
def pick.false(-A: Type, b: Bool, t: A, f: A, h: {b == False{} : Bool}) -> {Bool.pick(A, b, t, f) == f : A}:
  %Equal.sym(Bool, b, False{}, h) : {Bool.pick(A, _, t, f) == f : A}
  {==}

# the name at the place of k's first copy is the first copy
def get.num(ks: List<&2, List<&2, Word(8n)>>, +k: List<&2, Word(8n)>) ->
  {List.get(&2, List<&2, Word(8n)>, ks, num.nat(ks, k)) == first(ks, k) : Maybe<&2, List<&2, Word(8n)>>}:
  match ks:
    case Nil{}:
      {==}
    case Con{+n, +rest}:
      name.split(n, k, Sd.Name.is_eq(n, k), {==},
        {List.get(&2, List<&2, Word(8n)>, Con{n, rest}, num.nat(Con{n, rest}, k)) == first(Con{n, rest}, k) : Maybe<&2, List<&2, Word(8n)>>},
        +eq => +hb =>
          +en = pick.true(Nat, Sd.Name.is_eq(n, k), 0n, 1n+num.nat(rest, k), hb)
          +ef = pick.true(Maybe<&2, List<&2, Word(8n)>>, Sd.Name.is_eq(n, k), Some{n}, first(rest, k), hb)
          %Equal.sym(Nat, num.nat(Con{n, rest}, k), 0n, en) : {List.get(&2, List<&2, Word(8n)>, Con{n, rest}, _) == first(Con{n, rest}, k) : Maybe<&2, List<&2, Word(8n)>>}
          %Equal.sym(Maybe<&2, List<&2, Word(8n)>>, first(Con{n, rest}, k), Some{n}, ef) : {List.get(&2, List<&2, Word(8n)>, Con{n, rest}, 0n) == _ : Maybe<&2, List<&2, Word(8n)>>}
          {==},
        ne => +hb =>
          +en = pick.false(Nat, Sd.Name.is_eq(n, k), 0n, 1n+num.nat(rest, k), hb)
          +ef = pick.false(Maybe<&2, List<&2, Word(8n)>>, Sd.Name.is_eq(n, k), Some{n}, first(rest, k), hb)
          %Equal.sym(Nat, num.nat(Con{n, rest}, k), 1n+num.nat(rest, k), en) : {List.get(&2, List<&2, Word(8n)>, Con{n, rest}, _) == first(Con{n, rest}, k) : Maybe<&2, List<&2, Word(8n)>>}
          %Equal.sym(Maybe<&2, List<&2, Word(8n)>>, first(Con{n, rest}, k), first(rest, k), ef) : {List.get(&2, List<&2, Word(8n)>, Con{n, rest}, 1n+num.nat(rest, k)) == _ : Maybe<&2, List<&2, Word(8n)>>}
          Equal.trans(Maybe<&2, List<&2, Word(8n)>>,
            List.get(&2, List<&2, Word(8n)>, Con{n, rest}, 1n+num.nat(rest, k)),
            List.get(&2, List<&2, Word(8n)>, rest, num.nat(rest, k)),
            first(rest, k),
            {==},
            get.num(rest, k)))

# Img.ref.if at a side known
# --------------------------

def ref.if.true(b: Bool, +at: U32, more: Unit -> U32, h: {b == True{} : Bool}) ->
  {Mc.Img.ref.if(b, at, more) == at : U32}:
  %Equal.sym(Bool, b, True{}, h) : {Mc.Img.ref.if(_, at, more) == at : U32}
  {==}

def ref.if.false(b: Bool, +at: U32, more: Unit -> U32, h: {b == False{} : Bool}) ->
  {Mc.Img.ref.if(b, at, more) == more(Unit{}) : U32}:
  %Equal.sym(Bool, b, False{}, h) : {Mc.Img.ref.if(_, at, more) == more(Unit{}) : U32}
  {==}

# a None is no Some
def is.none(m: Maybe<&2, List<&2, Word(8n)>>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{_}:
      Empty

def none.ne.some(-k: List<&2, Word(8n)>, e: {None{} == Some{k} : Maybe<&2, List<&2, Word(8n)>>}) -> Empty:
  %e : is.none(_)
  Unit{}

# Img.ids numbers each name it holds with Img.id's number
# ------------------------------------------------------

# the number that Img.ids writes for k, or 0 when ks has no k
def ids.num(ks: List<&2, List<&2, Word(8n)>>, +k: List<&2, Word(8n)>, +i: U32) -> U32:
  match ks:
    case Nil{}:
      0
    case Con{+n, +rest}:
      Mc.Img.ref.if(Sd.Name.is_eq(n, k), i, u => ids.num(rest, k, U32.inc(i)))

# find of ids: the trie's value for k, or the number that Img.ids writes
def ids.find(ks: List<&2, List<&2, Word(8n)>>, +i: U32, +t: Mc.Img.Trie, +k: List<&2, Word(8n)>) ->
  {Mc.Img.trie.find(Mc.Img.ids(ks, i, t), k) == maybe.of(Mc.Img.trie.get(k, t), ids.num(ks, k, i)) : U32}:
  match ks:
    case Nil{}:
      find.of.maybe(Mc.Img.trie.get(k, t))
    case Con{+n, +rest}:
      Equal.trans(U32,
        Mc.Img.trie.find(Mc.Img.ids(Con{n, rest}, i, t), k),
        maybe.of(Mc.Img.trie.get(k, Mc.Img.trie.add(t, n, i)), ids.num(rest, k, U32.inc(i))),
        maybe.of(Mc.Img.trie.get(k, t), ids.num(Con{n, rest}, k, i)),
        ids.find(rest, U32.inc(i), Mc.Img.trie.add(t, n, i), k),
        name.split(n, k, Sd.Name.is_eq(n, k), {==},
          {maybe.of(Mc.Img.trie.get(k, Mc.Img.trie.add.if(Mc.Img.trie.get(n, t), t, n, i)), ids.num(rest, k, U32.inc(i))) ==
           maybe.of(Mc.Img.trie.get(k, t), Mc.Img.ref.if(Sd.Name.is_eq(n, k), i, u => ids.num(rest, k, U32.inc(i)))) : U32},
          +eq => +hb =>
            maybe.split(Mc.Img.trie.get(n, t),
              {maybe.of(Mc.Img.trie.get(k, Mc.Img.trie.add.if(Mc.Img.trie.get(n, t), t, n, i)), ids.num(rest, k, U32.inc(i))) ==
               maybe.of(Mc.Img.trie.get(k, t), Mc.Img.ref.if(Sd.Name.is_eq(n, k), i, u => ids.num(rest, k, U32.inc(i)))) : U32},
              hr => add.read.same.none(n, i, t, k, ids.num(rest, k, U32.inc(i)), eq, hb, hr),
              v => hs => add.read.same.some(n, i, t, k, ids.num(rest, k, U32.inc(i)), eq, hb, v, hs)),
          ne => +hb =>
            maybe.split(Mc.Img.trie.get(n, t),
              {maybe.of(Mc.Img.trie.get(k, Mc.Img.trie.add.if(Mc.Img.trie.get(n, t), t, n, i)), ids.num(rest, k, U32.inc(i))) ==
               maybe.of(Mc.Img.trie.get(k, t), Mc.Img.ref.if(Sd.Name.is_eq(n, k), i, u => ids.num(rest, k, U32.inc(i)))) : U32},
              hr => add.read.diff.none(n, i, t, k, ids.num(rest, k, U32.inc(i)), ne, hb, hr),
              v => hs => add.read.diff.some(n, i, t, k, ids.num(rest, k, U32.inc(i)), hb, v, hs))))

# find of ids from an empty trie is the number that Img.ids writes
def find.ids(+ks: List<&2, List<&2, Word(8n)>>, +k: List<&2, Word(8n)>) ->
  {Mc.Img.trie.find(Mc.Img.ids(ks, 0, Mc.Img.Trie.none{}), k) == ids.num(ks, k, 0) : U32}:
  Equal.trans(U32,
    Mc.Img.trie.find(Mc.Img.ids(ks, 0, Mc.Img.Trie.none{}), k),
    maybe.of(Mc.Img.trie.get(k, Mc.Img.Trie.none{}), ids.num(ks, k, 0)),
    ids.num(ks, k, 0),
    ids.find(ks, 0, Mc.Img.Trie.none{}, k),
    Equal.trans(U32,
      maybe.of(Mc.Img.trie.get(k, Mc.Img.Trie.none{}), ids.num(ks, k, 0)),
      maybe.of(None{}, ids.num(ks, k, 0)),
      ids.num(ks, k, 0),
      Equal.cong(Maybe<&2, U32>, U32, z => maybe.of(z, ids.num(ks, k, 0)),
        Mc.Img.trie.get(k, Mc.Img.Trie.none{}), None{}, get.none(k)),
      maybe.of.none(ids.num(ks, k, 0))))

# a name that ks holds has Img.id's number
def ids.num.occ(ks: List<&2, List<&2, Word(8n)>>, +k: List<&2, Word(8n)>, +i: U32,
  +h: {first(ks, k) == Some{k} : Maybe<&2, List<&2, Word(8n)>>}) ->
  {ids.num(ks, k, i) == Mc.Img.id(ks, k, i) : U32}:
  match ks:
    case Nil{}:
      Empty.absurd({ids.num(Nil{}, k, i) == Mc.Img.id(Nil{}, k, i) : U32}, none.ne.some(k, h))
    case Con{+n, +rest}:
      name.split(n, k, Sd.Name.is_eq(n, k), {==},
        {ids.num(Con{n, rest}, k, i) == Mc.Img.id(Con{n, rest}, k, i) : U32},
        +eq => +hb =>
          Equal.trans(U32,
            ids.num(Con{n, rest}, k, i),
            i,
            Mc.Img.id(Con{n, rest}, k, i),
            ref.if.true(Sd.Name.is_eq(n, k), i, u => ids.num(rest, k, U32.inc(i)), hb),
            Equal.sym(U32, Mc.Img.id(Con{n, rest}, k, i), i,
              ref.if.true(Sd.Name.is_eq(n, k), i, u => Mc.Img.id(rest, k, U32.inc(i)), hb))),
        ne => +hb =>
          +ef = pick.false(Maybe<&2, List<&2, Word(8n)>>, Sd.Name.is_eq(n, k), Some{n}, first(rest, k), hb)
          +h2 = Equal.trans(Maybe<&2, List<&2, Word(8n)>>, first(rest, k), first(Con{n, rest}, k), Some{k},
            Equal.sym(Maybe<&2, List<&2, Word(8n)>>, first(Con{n, rest}, k), first(rest, k), ef), h)
          Equal.trans(U32,
            ids.num(Con{n, rest}, k, i),
            ids.num(rest, k, U32.inc(i)),
            Mc.Img.id(Con{n, rest}, k, i),
            ref.if.false(Sd.Name.is_eq(n, k), i, u => ids.num(rest, k, U32.inc(i)), hb),
            Equal.trans(U32,
              ids.num(rest, k, U32.inc(i)),
              Mc.Img.id(rest, k, U32.inc(i)),
              Mc.Img.id(Con{n, rest}, k, i),
              ids.num.occ(rest, k, U32.inc(i), h2),
              Equal.sym(U32, Mc.Img.id(Con{n, rest}, k, i), Mc.Img.id(rest, k, U32.inc(i)),
                ref.if.false(Sd.Name.is_eq(n, k), i, u => Mc.Img.id(rest, k, U32.inc(i)), hb)))))

# Img.id's number, at the place of the first copy of k
def id.from(ks: List<&2, List<&2, Word(8n)>>, +k: List<&2, Word(8n)>, +j: Nat) ->
  {Mc.Img.id(ks, k, U32.from_nat(j)) == U32.from_nat(Nat.add(j, num.nat(ks, k))) : U32}:
  match ks:
    case Nil{}:
      Equal.sym(U32, U32.from_nat(Nat.add(j, 0n)), U32.from_nat(j),
        Equal.cong(Nat, U32, z => U32.from_nat(z), Nat.add(j, 0n), j, N.add_zero(j)))
    case Con{+n, +rest}:
      name.split(n, k, Sd.Name.is_eq(n, k), {==},
        {Mc.Img.id(Con{n, rest}, k, U32.from_nat(j)) == U32.from_nat(Nat.add(j, num.nat(Con{n, rest}, k))) : U32},
        +eq => +hb =>
          +en = pick.true(Nat, Sd.Name.is_eq(n, k), 0n, 1n+num.nat(rest, k), hb)
          +e1 = ref.if.true(Sd.Name.is_eq(n, k), U32.from_nat(j), u => Mc.Img.id(rest, k, U32.inc(U32.from_nat(j))), hb)
          %Equal.sym(U32, Mc.Img.ref.if(Sd.Name.is_eq(n, k), U32.from_nat(j), u => Mc.Img.id(rest, k, U32.inc(U32.from_nat(j)))), U32.from_nat(j), e1) : {_ == U32.from_nat(Nat.add(j, num.nat(Con{n, rest}, k))) : U32}
          %Equal.sym(Nat, num.nat(Con{n, rest}, k), 0n, en) : {U32.from_nat(j) == U32.from_nat(Nat.add(j, _)) : U32}
          %Equal.sym(Nat, Nat.add(j, 0n), j, N.add_zero(j)) : {U32.from_nat(j) == U32.from_nat(_) : U32}
          {==},
        ne => +hb =>
          +en = pick.false(Nat, Sd.Name.is_eq(n, k), 0n, 1n+num.nat(rest, k), hb)
          +e1 = ref.if.false(Sd.Name.is_eq(n, k), U32.from_nat(j), u => Mc.Img.id(rest, k, U32.inc(U32.from_nat(j))), hb)
          +ih = id.from(rest, k, 1n+j)
          +es = Equal.cong(Nat, U32, z => U32.from_nat(z),
            Nat.add(1n, Nat.add(j, num.nat(rest, k))), Nat.add(j, Nat.add(1n, num.nat(rest, k))),
            N.add_swap(1n, j, num.nat(rest, k)))
          +ec = Equal.cong(Nat, U32, z => U32.from_nat(Nat.add(j, z)), num.nat(Con{n, rest}, k), 1n+num.nat(rest, k), en)
          Equal.trans(U32,
            Mc.Img.id(Con{n, rest}, k, U32.from_nat(j)),
            Mc.Img.id(rest, k, U32.from_nat(1n+j)),
            U32.from_nat(Nat.add(j, num.nat(Con{n, rest}, k))),
            e1,
            Equal.trans(U32,
              Mc.Img.id(rest, k, U32.from_nat(1n+j)),
              U32.from_nat(Nat.add(1n, Nat.add(j, num.nat(rest, k)))),
              U32.from_nat(Nat.add(j, num.nat(Con{n, rest}, k))),
              ih,
              Equal.trans(U32,
                U32.from_nat(Nat.add(1n, Nat.add(j, num.nat(rest, k)))),
                U32.from_nat(Nat.add(j, Nat.add(1n, num.nat(rest, k)))),
                U32.from_nat(Nat.add(j, num.nat(Con{n, rest}, k))),
                es,
                Equal.sym(U32,
                  U32.from_nat(Nat.add(j, num.nat(Con{n, rest}, k))),
                  U32.from_nat(Nat.add(j, Nat.add(1n, num.nat(rest, k)))),
                  ec)))))

# the number of a name is at most the number of names
def num.nat.le(ks: List<&2, List<&2, Word(8n)>>, +k: List<&2, Word(8n)>) ->
  N.Le(num.nat(ks, k), List.length(&2, List<&2, Word(8n)>, ks)):
  match ks:
    case Nil{}:
      N.le_zero(0n)
    case Con{+n, +rest}:
      name.split(n, k, Sd.Name.is_eq(n, k), {==},
        N.Le(num.nat(Con{n, rest}, k), List.length(&2, List<&2, Word(8n)>, Con{n, rest})),
        +eq => +hb =>
          +en = pick.true(Nat, Sd.Name.is_eq(n, k), 0n, 1n+num.nat(rest, k), hb)
          N.le_rw_l(0n, num.nat(Con{n, rest}, k), List.length(&2, List<&2, Word(8n)>, Con{n, rest}),
            Equal.sym(Nat, num.nat(Con{n, rest}, k), 0n, en),
            N.le_zero(List.length(&2, List<&2, Word(8n)>, Con{n, rest}))),
        ne => +hb =>
          +en = pick.false(Nat, Sd.Name.is_eq(n, k), 0n, 1n+num.nat(rest, k), hb)
          N.le_rw_l(1n+num.nat(rest, k), num.nat(Con{n, rest}, k), List.length(&2, List<&2, Word(8n)>, Con{n, rest}),
            Equal.sym(Nat, num.nat(Con{n, rest}, k), 1n+num.nat(rest, k), en),
            N.add_mono(1n, 1n, num.nat(rest, k), List.length(&2, List<&2, Word(8n)>, rest),
              N.le_refl(1n), num.nat.le(rest, k))))
