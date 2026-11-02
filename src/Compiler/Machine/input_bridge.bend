# compiler: layer B, the start, as Inv (U8)
# =========================================
#
# input.post and input.done of move_kit.bend: start_input.bend's In.input.post and In.input.done
# (PostB form), then In.PostIn gives InvIn, with Acc (the cache and the start term's nodes).
# Filled by U8; U0 left each as ?TODO.

import Base
import ../../Book/impl.bend as Bk
import ../Cir/impl.bend as Cr
import ./impl.bend as Mc
import ../need_big.bend as N
import ./definitions.bend as D
import ./move_kit.bend as K
import ./start_input.bend as SI
import ./first_cell_past_table.bend as FC

# The start's facts
# -----------------

# the first cell is past the table, from what Cir.result computed
def ib.hF(+p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +m: U32, +k: U32, +len: U32,
  +pg: U32, +lim: U32, +first: U32, +rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  +small: {Mc.Img.small(p, 0) == True{} : Bool}, +s: D.Start(Mc.Img.cells(ds), i, m, k, len, pg, lim, first)) ->
  N.Le(272n, U32.to_nat(first)):
  (ek, r1) = s
  (em, r2) = r1
  (elim, r3) = r2
  (el, r4) = r3
  (ea, ef) = r4
  FC.hf.hF(p, ds, k, len, first, rd, small, ek, ef)

# input.done: the fuel 10 + |i| ends M.input
def ib.done(+p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +m: U32, +k: U32, +len: U32,
  +pg: U32, +lim: U32, +first: U32, +rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  +small: {Mc.Img.small(p, 0) == True{} : Bool}, +s: D.Start(Mc.Img.cells(ds), i, m, k, len, pg, lim, first)) ->
  D.InputDone(p, ds, i, m, k, len, pg, lim, first, rd, small, s):
  SI.In.input.done(p, ds, i, m, k, len, pg, lim, first, rd, small, s, ib.hF(p, ds, i, m, k, len, pg, lim, first, rd, small, s))

def K.input.post(f, p, ds, i, m, k, len, pg, lim, first, rd, small, s):
  ?TODO

def K.input.done(p, ds, i, m, k, len, pg, lim, first, rd, small, s):
  ib.done(p, ds, i, m, k, len, pg, lim, first, rd, small, s)
