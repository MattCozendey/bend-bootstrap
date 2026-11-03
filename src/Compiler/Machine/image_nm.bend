# compiler: the image's name numbers, read back (layer B)
# =======================================================
#
# A cell that stands for a label or a λ-match keeps, in its field 2, the
# number of its name in the image's names ks (Img.id). Nm reads that number
# back: it names the same name (T.tm.name gives Some{k} only at k's copy)
# and it is the number the trie holds (find.ids, ids.num.occ). This file
# joins the two, under a bound on the number of names: the cell's field 2 is
# the number that Img.id gives, and ks at it gives the name back.

import Base
import ../../Shared/shared.bend as Sd
import ./definitions.bend as D
import ./impl.bend as Mc
import ./cell_terms.bend as T
import ./image_tries.bend as TR
import ../need_big.bend as N
import ../Cir/module_round_trip.bend as MO

# a name of ks, read back from the number Img.id gives it: the trie of
# Img.ids holds that number, and ks at it is the name
def nm.find(+ks: List<&2, List<&2, Word(8n)>>, +k: List<&2, Word(8n)>, +M: U32,
  hlen: N.Le(List.length(&2, List<&2, Word(8n)>, ks), U32.to_nat(M)),
  +h: {TR.first(ks, k) == Some{k} : Maybe<&2, List<&2, Word(8n)>>}) ->
  D.P2({T.tm.name(ks, Mc.Img.trie.find(Mc.Img.ids(ks, 0, Mc.Img.Trie.none{}), k)) == Some{k} : Maybe<&2, List<&2, Word(8n)>>},
    {Mc.Img.trie.find(Mc.Img.ids(ks, 0, Mc.Img.Trie.none{}), k) == Mc.Img.id(ks, k, 0) : U32}):
  +ef = TR.find.ids(ks, k)
  +ei = TR.ids.num.occ(ks, k, 0, h)
  +e1 = Equal.cong(U32, Nat, z => U32.to_nat(z),
    Mc.Img.trie.find(Mc.Img.ids(ks, 0, Mc.Img.Trie.none{}), k), TR.ids.num(ks, k, 0), ef)
  +e2 = Equal.cong(U32, Nat, z => U32.to_nat(z), TR.ids.num(ks, k, 0), Mc.Img.id(ks, k, 0), ei)
  +e3 = Equal.cong(U32, Nat, z => U32.to_nat(z), Mc.Img.id(ks, k, 0), U32.from_nat(TR.num.nat(ks, k)),
    TR.id.from(ks, k, 0n))
  +e4 = MO.tofrom(TR.num.nat(ks, k), M,
    N.le_trans(TR.num.nat(ks, k), List.length(&2, List<&2, Word(8n)>, ks), U32.to_nat(M),
      TR.num.nat.le(ks, k), hlen))
  +en = Equal.trans(Nat,
    U32.to_nat(Mc.Img.trie.find(Mc.Img.ids(ks, 0, Mc.Img.Trie.none{}), k)),
    U32.to_nat(Mc.Img.id(ks, k, 0)),
    TR.num.nat(ks, k),
    Equal.trans(Nat,
      U32.to_nat(Mc.Img.trie.find(Mc.Img.ids(ks, 0, Mc.Img.Trie.none{}), k)),
      U32.to_nat(TR.ids.num(ks, k, 0)),
      U32.to_nat(Mc.Img.id(ks, k, 0)),
      e1, e2),
    Equal.trans(Nat, U32.to_nat(Mc.Img.id(ks, k, 0)), U32.to_nat(U32.from_nat(TR.num.nat(ks, k))),
      TR.num.nat(ks, k), e3, e4))
  +eg = Equal.cong(Nat, Maybe<&2, List<&2, Word(8n)>>, z => List.get(&2, List<&2, Word(8n)>, ks, z),
    U32.to_nat(Mc.Img.trie.find(Mc.Img.ids(ks, 0, Mc.Img.Trie.none{}), k)), TR.num.nat(ks, k), en)
  Tuple{Equal.trans(Maybe<&2, List<&2, Word(8n)>>,
      List.get(&2, List<&2, Word(8n)>, ks, U32.to_nat(Mc.Img.trie.find(Mc.Img.ids(ks, 0, Mc.Img.Trie.none{}), k))),
      List.get(&2, List<&2, Word(8n)>, ks, TR.num.nat(ks, k)),
      Some{k},
      eg,
      Equal.trans(Maybe<&2, List<&2, Word(8n)>>,
        List.get(&2, List<&2, Word(8n)>, ks, TR.num.nat(ks, k)), TR.first(ks, k), Some{k}, TR.get.num(ks, k), h)),
    Equal.trans(U32,
      Mc.Img.trie.find(Mc.Img.ids(ks, 0, Mc.Img.Trie.none{}), k),
      TR.ids.num(ks, k, 0),
      Mc.Img.id(ks, k, 0),
      ef, ei)}
