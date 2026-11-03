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
import ../../Eval/impl.bend as El
import ../Cir/impl.bend as Cr
import ../Cir/simulation_numbers.bend as SN
import ../Cir/leb_round_trip.bend as L
import ../need_big.bend as N
import ./impl.bend as Mc
import ./cell_terms.bend as T
import ./definitions.bend as D
import ./image_layout.bend as IL
import ./image_header_bits.bend as HB
import ./image_flags.bend as IF
import ./image_term_facts.bend as TF
import ./image_occ.bend as OC
import ./image_nm.bend as NM
import ./image_tries.bend as TR
import ./read_var_bound.bend as RV
import ./first_cell_past_table.bend as FC

def label(+ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +j: U32,
  +name: List<&2, Word(8n)>, pl: IL.Pl(im, fi, c),
  cell: {Cr.Cir.Cells.get(m, c) == Cr.Cir.Cell{1549, 0, j, 0, 0} : Cr.Cir.Cell},
  en: {T.tm.name(ks, j) == Some{name} : Maybe<&2, List<&2, Word(8n)>>},
  ei: {j == Mc.Img.id(ks, name, 0) : U32}) -> D.IsK(True{}, ds, m, im, fi, nx, ks, img, c, Bk.Term.Lab{name}):
  %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(m, c), Cr.Cir.Cell{1549, 0, j, 0, 0}, cell) :
    D.IsCK(True{}, ds, m, im, fi, nx, ks, img, c, _, Bk.Term.Lab{name})
  ((IL.pl.cell(im, fi, nx, c, pl), (SN.or.true(D.Own(fi, nx, c)), ({==}, ({==}, ({==}, {==}))))), (en, ei))

def ref.body(+ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +ids: Mc.Img.Trie, +refs: Mc.Img.Trie,
  +at: U32, +tail: List<&2, Bk.Term>, +acc: List<&2, Cr.Cir.Cell>, +k: List<&2, Word(8n)>,
  er: {Mc.Img.trie.find(refs, k) == Mc.Img.ref(Mc.Img.defs(ds, Mc.I.book()), k) : U32},
  h: IL.Lay(Mc.Img.Out.cells(Mc.Img.go(Bk.Term.Ref{k}, ids, refs, U32.inc(at), acc)), T.tm.pre(Bk.Term.Ref{k}, tail), m, img, im, fi, at)) ->
  D.IsK(True{}, ds, m, im, fi, nx, ks, img, at, Bk.Term.Ref{k}):
  (ec, (ei, (pl, _))) = h
  +cell = {Cr.Cir.Cell{Mc.Img.header(Mc.T.ref(), 0, 1024, 0), 0, Mc.Img.trie.find(refs, k), 0, 0} : Cr.Cir.Cell}
  %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(m, at), cell, ec) : D.IsCK(True{}, ds, m, im, fi, nx, ks, img, at, _, Bk.Term.Ref{k})
  ((IL.pl.cell(im, fi, nx, at, pl),
      (SN.or.true(D.Own(fi, nx, at)),
      ({==},
      ({==},
      ({==}, {==}))))),
      (ei, ({==}, er)))

def lab.body(+ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +ids: Mc.Img.Trie, +refs: Mc.Img.Trie,
  +at: U32, +tail: List<&2, Bk.Term>, +acc: List<&2, Cr.Cir.Cell>, +k: List<&2, Word(8n)>,
  en: {T.tm.name(ks, Mc.Img.trie.find(ids, k)) == Some{k} : Maybe<&2, List<&2, Word(8n)>>},
  ei: {Mc.Img.trie.find(ids, k) == Mc.Img.id(ks, k, 0) : U32},
  h: IL.Lay(Mc.Img.Out.cells(Mc.Img.go(Bk.Term.Lab{k}, ids, refs, U32.inc(at), acc)), T.tm.pre(Bk.Term.Lab{k}, tail), m, img, im, fi, at)) ->
  D.IsK(True{}, ds, m, im, fi, nx, ks, img, at, Bk.Term.Lab{k}):
  (ec, (_, (pl, _))) = h
  +cell = {Cr.Cir.Cell{Mc.Img.header(Mc.T.lab(), 0, 1536, 0), 0, Mc.Img.trie.find(ids, k), 0, 0} : Cr.Cir.Cell}
  %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(m, at), cell, ec) : D.IsCK(True{}, ds, m, im, fi, nx, ks, img, at, _, Bk.Term.Lab{k})
  ((IL.pl.cell(im, fi, nx, at, pl),
    (SN.or.true(D.Own(fi, nx, at)),
    ({==},
    ({==},
    ({==}, {==}))))),
    (en, ei))

def efq.body(+ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +ids: Mc.Img.Trie, +refs: Mc.Img.Trie,
  +at: U32, +tail: List<&2, Bk.Term>, +acc: List<&2, Cr.Cir.Cell>,
  h: IL.Lay(Mc.Img.Out.cells(Mc.Img.go(Bk.Term.Efq{}, ids, refs, U32.inc(at), acc)), T.tm.pre(Bk.Term.Efq{}, tail), m, img, im, fi, at)) ->
  D.IsK(True{}, ds, m, im, fi, nx, ks, img, at, Bk.Term.Efq{}):
  (ec, (_, (pl, _))) = h
  +cell = {Cr.Cir.Cell{Mc.Img.header(Mc.T.efq(), 0, 1024, 0), 0, 0, 0, 0} : Cr.Cir.Cell}
  %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(m, at), cell, ec) : D.IsCK(True{}, ds, m, im, fi, nx, ks, img, at, _, Bk.Term.Efq{})
  (IL.pl.cell(im, fi, nx, at, pl),
    (SN.or.true(D.Own(fi, nx, at)),
    ({==},
    ({==},
    ({==}, {==})))))

def rfl.body(+ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +ids: Mc.Img.Trie, +refs: Mc.Img.Trie,
  +at: U32, +tail: List<&2, Bk.Term>, +acc: List<&2, Cr.Cir.Cell>,
  h: IL.Lay(Mc.Img.Out.cells(Mc.Img.go(Bk.Term.Rfl{}, ids, refs, U32.inc(at), acc)), T.tm.pre(Bk.Term.Rfl{}, tail), m, img, im, fi, at)) ->
  D.IsK(True{}, ds, m, im, fi, nx, ks, img, at, Bk.Term.Rfl{}):
  (ec, (_, (pl, _))) = h
  +cell = {Cr.Cir.Cell{Mc.Img.header(Mc.T.rfl(), 0, 1536, 0), 0, 0, 0, 0} : Cr.Cir.Cell}
  %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(m, at), cell, ec) : D.IsCK(True{}, ds, m, im, fi, nx, ks, img, at, _, Bk.Term.Rfl{})
  (IL.pl.cell(im, fi, nx, at, pl),
    (SN.or.true(D.Own(fi, nx, at)),
    ({==},
    ({==},
    ({==}, {==})))))

def enu.body(+ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +ids: Mc.Img.Trie, +refs: Mc.Img.Trie,
  +at: U32, +tail: List<&2, Bk.Term>, +acc: List<&2, Cr.Cir.Cell>, +e: List<&2, List<&2, Word(8n)>>,
  h: IL.Lay(Mc.Img.Out.cells(Mc.Img.go(Bk.Term.Enu{e}, ids, refs, U32.inc(at), acc)), T.tm.pre(Bk.Term.Enu{e}, tail), m, img, im, fi, at)) ->
  D.IsK(True{}, ds, m, im, fi, nx, ks, img, at, Bk.Term.Enu{e}):
  (ec, (ei, (pl, _))) = h
  +cell = {Cr.Cir.Cell{Mc.Img.header(12, 0, 1024, 0), 0, 0, 0, 0} : Cr.Cir.Cell}
  %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(m, at), cell, ec) : D.IsCK(True{}, ds, m, im, fi, nx, ks, img, at, _, Bk.Term.Enu{e})
  ((IL.pl.cell(im, fi, nx, at, pl),
    (SN.or.true(D.Own(fi, nx, at)),
    ({==},
    ({==},
    ({==}, {==}))))),
    (ei, {==}))

def VarHdr(+fv: U32) -> Data:
  D.P2({D.TgW(Mc.Img.header(Mc.T.var(), 0, 1024, fv)) == Mc.T.var() : U32},
  D.P2({D.FlW(Mc.Img.header(Mc.T.var(), 0, 1024, fv), 256) == False{} : Bool},
  D.P2({D.FlW(Mc.Img.header(Mc.T.var(), 0, 1024, fv), 512) == False{} : Bool},
    {D.FlW(Mc.Img.header(Mc.T.var(), 0, 1024, fv), 1024) == True{} : Bool})))

def var.header.of(+fv: U32, hb: HB.Hdr(U32.or(Mc.T.var(), 1024), fv)) -> VarHdr(fv):
  (et, (_, (e256, (e512, (e1024, _))))) = hb
  +lo = U32.or(Mc.T.var(), 1024)
  (Equal.trans(U32, D.TgW(Mc.Img.header(Mc.T.var(), 0, 1024, fv)), U32.and(lo, 63), Mc.T.var(), et, {==}),
  (Equal.trans(Bool, D.FlW(Mc.Img.header(Mc.T.var(), 0, 1024, fv), 256), D.FlW(lo, 256), False{}, e256, {==}),
  (Equal.trans(Bool, D.FlW(Mc.Img.header(Mc.T.var(), 0, 1024, fv), 512), D.FlW(lo, 512), False{}, e512, {==}),
    Equal.trans(Bool, D.FlW(Mc.Img.header(Mc.T.var(), 0, 1024, fv), 1024), D.FlW(U32.or(Mc.T.var(), 1024), 1024), True{}, e1024, {==}))))

def var.header(+fv: U32) -> VarHdr(fv):
  var.header.of(fv, HB.hdr(U32.or(Mc.T.var(), 1024), fv, {==}))

def var.fv(+i: Nat) -> U32:
  Bool.pick(U32, U32.is_lt(U32.from_nat(i), 524286), U32.inc(U32.from_nat(i)), 524287)

def var.body(+ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +ids: Mc.Img.Trie, +refs: Mc.Img.Trie,
  +at: U32, +tail: List<&2, Bk.Term>, +acc: List<&2, Cr.Cir.Cell>, +i: Nat,
  ei: {U32.to_nat(U32.from_nat(i)) == i : Nat},
  vh: VarHdr(var.fv(i)),
  efv: {Bool.or(
    U32.is_eq(D.FvW(Mc.Img.header(Mc.T.var(), 0, 1024, var.fv(i))), 524287),
    Nat.is_lt(i, U32.to_nat(D.FvW(Mc.Img.header(Mc.T.var(), 0, 1024, var.fv(i)))))) == True{} : Bool},
  h: IL.Lay(Mc.Img.Out.cells(Mc.Img.go(Bk.Term.Var{i}, ids, refs, U32.inc(at), acc)), T.tm.pre(Bk.Term.Var{i}, tail), m, img, im, fi, at)) ->
  D.IsK(True{}, ds, m, im, fi, nx, ks, img, at, Bk.Term.Var{i}):
  (et, (e256, (e512, e1024))) = vh
  (ec, (_, (pl, _))) = h
  +u = U32.from_nat(i)
  +cell = {Cr.Cir.Cell{Mc.Img.header(Mc.T.var(), 0, 1024, var.fv(i)), 0, u, 0, 0} : Cr.Cir.Cell}
  %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(m, at), cell, ec) : D.IsCK(True{}, ds, m, im, fi, nx, ks, img, at, _, Bk.Term.Var{i})
  ((IL.pl.cell(im, fi, nx, at, pl),
    (Equal.trans(Bool, Bool.or(D.Own(fi, nx, at), D.FlW(Mc.Img.header(Mc.T.var(), 0, 1024, var.fv(i)), 1024)),
      Bool.or(D.Own(fi, nx, at), True{}), True{},
      Equal.cong(Bool, Bool, b => Bool.or(D.Own(fi, nx, at), b),
        D.FlW(Mc.Img.header(Mc.T.var(), 0, 1024, var.fv(i)), 1024), True{}, e1024), SN.or.true(D.Own(fi, nx, at))),
    (et,
    (Equal.trans(Bool, Bool.or(Bool.not(D.FlW(Mc.Img.header(Mc.T.var(), 0, 1024, var.fv(i)), 256)),
        El.Eval.vals(ds, Bk.Term.Var{i}, False{})),
      Bool.or(Bool.not(False{}), El.Eval.vals(ds, Bk.Term.Var{i}, False{})), True{},
      Equal.cong(Bool, Bool, b => Bool.or(Bool.not(b), El.Eval.vals(ds, Bk.Term.Var{i}, False{})),
        D.FlW(Mc.Img.header(Mc.T.var(), 0, 1024, var.fv(i)), 256), False{}, e256), {==}),
    (Equal.trans(Bool, Bool.or(Bool.not(D.FlW(Mc.Img.header(Mc.T.var(), 0, 1024, var.fv(i)), 512)),
        El.Term.is_data(Bk.Term.Var{i})),
      Bool.or(Bool.not(False{}), El.Term.is_data(Bk.Term.Var{i})), True{},
      Equal.cong(Bool, Bool, b => Bool.or(Bool.not(b), El.Term.is_data(Bk.Term.Var{i})),
        D.FlW(Mc.Img.header(Mc.T.var(), 0, 1024, var.fv(i)), 512), False{}, e512), {==}), efv))))),
    Equal.trans(Nat, U32.to_nat(Cr.Cir.Cell.get(2n, cell)), U32.to_nat(u), i, {==}, ei))

def labels.of(+ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +img: List<&2, Bk.Term>, +im: U32, +fi: U32, +nx: U32,
  r: IL.Lay(IL.Drop(Cr.Cir.Cell, 7n, Mc.Img.cells(ds)), IL.Drop(Bk.Term, 7n, T.tm.img(ds)), m, img, im, fi, IL.Up(7n, 1))) ->
  D.P2(D.IsK(True{}, ds, m, im, fi, nx, T.tm.names(ds), img, 8, Bk.Term.Lab{El.Quan.name(Bk.Quan.Q0{})}),
  D.P2(D.IsK(True{}, ds, m, im, fi, nx, T.tm.names(ds), img, 9, Bk.Term.Lab{El.Quan.name(Bk.Quan.Q1{})}),
    D.IsK(True{}, ds, m, im, fi, nx, T.tm.names(ds), img, 10, Bk.Term.Lab{El.Quan.name(Bk.Quan.Q2{})}))):
  (c8, (_, (p8, (c9, (_, (p9, (c10, (_, (p10, _))))))))) = r
  (label(ds, m, im, fi, nx, T.tm.names(ds), img, 8, 7, El.Quan.name(Bk.Quan.Q0{}), p8, c8, {==}, {==}),
  (label(ds, m, im, fi, nx, T.tm.names(ds), img, 9, 8, El.Quan.name(Bk.Quan.Q1{}), p9, c9, {==}, {==}),
    label(ds, m, im, fi, nx, T.tm.names(ds), img, 10, 9, El.Quan.name(Bk.Quan.Q2{}), p10, c10, {==}, {==})))

def labels(+ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +img: List<&2, Bk.Term>, +im: U32, +fi: U32, +nx: U32,
  h: IL.Lay(Mc.Img.cells(ds), T.tm.img(ds), m, img, im, fi, 1)) ->
  D.P2(D.IsK(True{}, ds, m, im, fi, nx, T.tm.names(ds), img, 8, Bk.Term.Lab{El.Quan.name(Bk.Quan.Q0{})}),
  D.P2(D.IsK(True{}, ds, m, im, fi, nx, T.tm.names(ds), img, 9, Bk.Term.Lab{El.Quan.name(Bk.Quan.Q1{})}),
    D.IsK(True{}, ds, m, im, fi, nx, T.tm.names(ds), img, 10, Bk.Term.Lab{El.Quan.name(Bk.Quan.Q2{})}))):
  labels.of(ds, m, img, im, fi, nx, IL.lay.drop(7n, Mc.Img.cells(ds), T.tm.img(ds), m, img, im, fi, 1, h))

def img.of(+ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +k: U32, +first: U32,
  tbl: D.Tbl(m, k, first, first),
  bodies: D.DefsK(ds, True{}, ds, m, k, first, first, T.tm.names(ds), T.tm.img(ds), Mc.I.book()),
  ls: D.P2(D.IsK(True{}, ds, m, k, first, first, T.tm.names(ds), T.tm.img(ds), 8, Bk.Term.Lab{El.Quan.name(Bk.Quan.Q0{})}),
    D.P2(D.IsK(True{}, ds, m, k, first, first, T.tm.names(ds), T.tm.img(ds), 9, Bk.Term.Lab{El.Quan.name(Bk.Quan.Q1{})}),
      D.IsK(True{}, ds, m, k, first, first, T.tm.names(ds), T.tm.img(ds), 10, Bk.Term.Lab{El.Quan.name(Bk.Quan.Q2{})}))),
  hk: {U32.is_le(290, k) == True{} : Bool}, hf: {U32.is_lt(k, first) == True{} : Bool}) ->
  D.ImgOK(ds, T.tm.names(ds), T.tm.img(ds), m, k, first, first):
  (l0, (l1, l2)) = ls
  (tbl, (bodies, (l0, (l1, (l2, ((Mc.Img.names.defs(ds), {==}), (hk, hf)))))))

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

def img.start.of(+p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +m: U32, +k: U32, +len: U32,
  +pg: U32, +lim: U32, +first: U32, +rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  +small: {Mc.Img.small(p, 0) == True{} : Bool}, s: D.Start(Mc.Img.cells(ds), i, m, k, len, pg, lim, first)) ->
  D.ImgOK(ds, T.tm.names(ds), T.tm.img(ds), Cr.Cir.load(Mc.Img.cells(ds), 1, Cr.Cir.Cells.none{}), k, first, first):
  (+ek, (_, (_, (_, (_, ef))))) = s
  +hsm = FC.hf.hsm(p, ds, rd, small)
  +hf = FC.hf.kF(p, ds, k, len, first, rd, small, ek, ef)
  +mem = Cr.Cir.load(Mc.Img.cells(ds), 1, Cr.Cir.Cells.none{})
  +lay = IL.lay.img(ds, k, first, FC.hf.k.nat(ds, k, ek, hsm), hf)
  img.of(ds, mem, k, first, IL.lay.table(ds, mem, T.tm.img(ds), k, first, first, lay),
    ?TODO, labels(ds, mem, T.tm.img(ds), k, first, first, lay),
    IL.le.to(290, k, FC.hf.k290(ds, k, ek, hsm)), SN.lt.to(k, first, hf))

def img.start(p, ds, i, m, k, len, pg, lim, first, rd, small, s):
  img.start.of(p, ds, i, m, k, len, pg, lim, first, rd, small, s)
