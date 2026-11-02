# compiler: layer B, the image at the start (U8)
# ===============================================
#
# At the start of the run (St0, from Cir.result), the cells of the image of
# a book that Book.read reads hold what the moves read of the image, as
# ImgOK (definitions.bend) says: the table by tag from cell 272, whole, as
# Img.table gives it; the body of each def of ds where Img.defs places it,
# from I.book() on, as IsK says (the tag, quantity, VALUE, DATA and STATIC
# flags and fv of each node, the places of the names, the Refs' targets);
# the labels of Q0, Q1 and Q2 at the cells 8, 9 and 10; the image's names,
# the machine's (Img.known) first; and 290 <= k < first.
#
# M.input keeps these cells (start_input.bend's In.Fr), so InvIn has them
# when M.input ends (input_bridge.bend's input.post). Stated by U8; its
# proof may go to a unit of its own.

import Base
import ../../Book/impl.bend as Bk
import ../Cir/impl.bend as Cr
import ./impl.bend as Mc
import ./cell_terms.bend as T
import ./definitions.bend as D

# LAW: the image's cells at the start, as the moves read them (ImgOK), with
# the start's premises of input.post (move_kit.bend)
law img.start:
  for +p: List<&2, Word(8n)>
  for +ds: List<&2, Bk.Def>
  for +i: List<&2, Word(8n)>
  for +m: U32
  for +k: U32
  for +len: U32
  for +pg: U32
  for +lim: U32
  for +first: U32
  for rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>}
  for small: {Mc.Img.small(p, 0) == True{} : Bool}
  for s: D.Start(Mc.Img.cells(ds), i, m, k, len, pg, lim, first)
  D.ImgOK(ds, T.tm.names(ds), T.tm.img(ds), Cr.Cir.load(Mc.Img.cells(ds), 1, Cr.Cir.Cells.none{}), k, first, first)

def img.start(p, ds, i, m, k, len, pg, lim, first, rd, small, s):
  ?TODO
