# compiler: where the image's cells and terms lie, at the start (layer B)
# =======================================================================
#
# At the start, Cir.load has put the image's cells (Img.cells) from cell 1
# on, and T.tm.img lists the term of each cell, from cell 1 on, in the same
# order. Lay says both, cell by cell from a cell at: the cell there, its
# term (TmAt), and its place (Pl): one of the image's cells (not 0, at most
# im), none of the machine's own (below fi). load.lay proves Lay for the
# cells that Cir.load puts, in one pass over them; lay.drop moves Lay past
# the first n cells, so that each part of the image (its labels, its table,
# its bodies) gets its own.
#
# The numbers of words are copied from Compiler/Cir/simulation_numbers.bend,
# which imports the whole simulation.

import Base
import ../../Book/impl.bend as Bk
import ../Cir/impl.bend as Cr
import ./impl.bend as Mc
import ./cell_terms.bend as T
import ./definitions.bend as D
import ../need_big.bend as N
import ../Cir/instrs_round_trip.bend as PI

# Numbers of words (copied)
# -------------------------

# a <= b on numbers gives a <= b on U32
def le.rel(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), h: N.Le(x, y)) -> {Cmp.is_le(c) == True{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({False{} == True{} : Bool}, N.not_succ_le(y, N.le_trans(1n+y, x, y, r, h)))

def le.to(+a: U32, +b: U32, h: N.Le(U32.to_nat(a), U32.to_nat(b))) -> {U32.is_le(a, b) == True{} : Bool}:
  le.rel(U32.cmp(a, b), U32.to_nat(a), U32.to_nat(b), N.U32.rel(a, b), h)

# b < a on numbers gives a <= b false
def nle.rel(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), h: N.Le(1n+y, x)) -> {Cmp.is_le(c) == False{} : Bool}:
  match c:
    case LT{}:
      Empty.absurd({True{} == False{} : Bool}, N.not_succ_le(x, N.le_trans(1n+x, y, x, r, N.weaken(y, x, h))))
    case EQ{}:
      Empty.absurd({True{} == False{} : Bool}, N.not_succ_le(y, (%r : N.Le(1n+y, _); h)))
    case GT{}:
      {==}

def nle.to(+a: U32, +b: U32, h: N.Le(1n+U32.to_nat(b), U32.to_nat(a))) -> {U32.is_le(a, b) == False{} : Bool}:
  nle.rel(U32.cmp(a, b), U32.to_nat(a), U32.to_nat(b), N.U32.rel(a, b), h)

# a < b on numbers gives a, b not equal
def ne.rel(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), h: N.Le(1n+x, y)) -> {Cmp.is_eq(c) == False{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({True{} == False{} : Bool}, N.not_succ_le(y, (%r : N.Le(1n+_, y); h)))
    case GT{}:
      {==}

def ne.to(+a: U32, +b: U32, h: N.Le(1n+U32.to_nat(a), U32.to_nat(b))) -> {U32.is_eq(a, b) == False{} : Bool}:
  ne.rel(U32.cmp(a, b), U32.to_nat(a), U32.to_nat(b), N.U32.rel(a, b), h)

# a U32 whose number is at least 1 is not 0
def nz.rel(c: Cmp, +x: Nat, r: N.Rel(c, x, 0n), h: N.Le(1n, x)) -> {Cmp.is_eq(c) == False{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({True{} == False{} : Bool}, (%r : N.Le(1n, _); h))
    case GT{}:
      {==}

def nz.to(+a: U32, h: N.Le(1n, U32.to_nat(a))) -> {U32.is_zero(a) == False{} : Bool}:
  nz.rel(U32.cmp(a, 0), U32.to_nat(a), N.U32.rel(a, 0), h)

# (x - 1) + 1 = x, on words
def W.dec_inc(+n: Nat, +t: Word(n)) -> {Word.inc(n, Word.adc(n, t, Word.zero(n), True{}, False{})) == t : Word(n)}:
  match n:
    case 0n:
      match t:
        case WNil{}:
          {==}
    case 1n+p:
      match t:
        case WCon{False{}, +r}:
          Equal.cong(Word(p), Word(1n+p), z => WCon{False{}, z}, Word.inc(p, Word.adc(p, r, Word.zero(p), True{}, False{})), r, W.dec_inc(p, r))
        case WCon{True{}, +r}:
          Equal.cong(Word(p), Word(1n+p), z => WCon{True{}, z}, Word.adc(p, r, Word.zero(p), True{}, True{}), r, PI.Word.sub0(p, r))

def u32.dec_inc(+x: U32) -> {U32.inc(U32.sub(x, 1)) == x : U32}:
  match x:
    case U32{+w}:
      match w:
        case WCon{False{}, +r}:
          Equal.cong(Word(31n), U32, z => U32{WCon{False{}, z}}, Word.inc(31n, Word.adc(31n, r, Word.zero(31n), True{}, False{})), r, W.dec_inc(31n, r))
        case WCon{True{}, +r}:
          Equal.cong(Word(31n), U32, z => U32{WCon{True{}, z}}, Word.adc(31n, r, Word.zero(31n), True{}, True{}), r, PI.Word.sub0(31n, r))

# x - 1 is one less than x, for x not 0
def dec.nat(+x: U32, h: N.Le(1n, U32.to_nat(x))) -> {1n+U32.to_nat(U32.sub(x, 1)) == U32.to_nat(x) : Nat}:
  +d = U32.sub(x, 1)
  +ez = Equal.trans(Bool, False{}, U32.is_zero(x), U32.is_zero(U32.inc(d)), Equal.sym(Bool, U32.is_zero(x), False{}, nz.to(x, h)),
    Equal.cong(U32, Bool, z => U32.is_zero(z), x, U32.inc(d), Equal.sym(U32, U32.inc(d), x, u32.dec_inc(x))))
  Equal.trans(Nat, 1n+U32.to_nat(d), U32.to_nat(U32.inc(d)), U32.to_nat(x),
    Equal.sym(Nat, U32.to_nat(U32.inc(d)), 1n+U32.to_nat(d), PI.U32.inc_nat(d, ez)),
    Equal.cong(U32, Nat, z => U32.to_nat(z), U32.inc(d), x, u32.dec_inc(x)))

# 1 + a = 1 + b gives a = b
def succ.inj(-a: Nat, -b: Nat, e: {1n+a == 1n+b : Nat}) -> {a == b : Nat}:
  Equal.cong(Nat, Nat, z => D.nat.pred(z), 1n+a, 1n+b, e)

# Lists
# -----

def drop0(xs: List<&2, Bk.Term>) -> {List.drop(&2, Bk.Term, xs, 0n) == xs : List<&2, Bk.Term>}:
  match xs:
    case Nil{}:
      {==}
    case Con{_, _}:
      {==}

# the list past the first 1 + j is the tail of the list past the first j
def drop.tl(xs: List<&2, Bk.Term>, j: Nat) ->
  {List.drop(&2, Bk.Term, xs, 1n+j) == List.tail(&2, Bk.Term, List.drop(&2, Bk.Term, xs, j)) : List<&2, Bk.Term>}:
  match xs j:
    case Nil{} _:
      {==}
    case Con{_, +t} 0n:
      drop0(t)
    case Con{_, +t} 1n+p:
      drop.tl(t, p)

# the j-th of a list is the head of the list past the first j
def get.hd(xs: List<&2, Bk.Term>, j: Nat) ->
  {List.get(&2, Bk.Term, xs, j) == List.head(&2, Bk.Term, List.drop(&2, Bk.Term, xs, j)) : Maybe<&2, Bk.Term>}:
  match xs j:
    case Nil{} _:
      {==}
    case Con{_, _} 0n:
      {==}
    case Con{_, +t} 1n+p:
      get.hd(t, p)

# The layout
# ----------

# the cell at is one of the image's (not 0, at most im) and none of the
# machine's own (below fi)
def Pl(+im: U32, +fi: U32, +at: U32) -> Data:
  D.P2({U32.is_zero(at) == False{} : Bool}, D.P2({U32.is_le(at, im) == True{} : Bool}, {U32.is_le(fi, at) == False{} : Bool}))

# the term of the cell at is the first of ts, when there is one
def TmAt(ts: List<&2, Bk.Term>, +img: List<&2, Bk.Term>, +at: U32) -> Data:
  match ts:
    case Nil{}:
      Unit
    case Con{t, _}:
      {T.tm.image(img, at) == Some{t} : Maybe<&2, Bk.Term>}

# from the cell at on, the cells cs, their terms ts and their places
def Lay(cs: List<&2, Cr.Cir.Cell>, +ts: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +img: List<&2, Bk.Term>, +im: U32, +fi: U32,
  +at: U32) -> Data:
  match cs:
    case Nil{}:
      Unit
    case Con{c, cr}:
      D.P2({Cr.Cir.Cells.get(m, at) == c : Cr.Cir.Cell},
      D.P2(TmAt(ts, img, at),
      D.P2(Pl(im, fi, at), Lay(cr, List.tail(&2, Bk.Term, ts), m, img, im, fi, U32.inc(at)))))

# a place of the image is a cell
def pl.cell(+im: U32, +fi: U32, +nx: U32, +at: U32, h: Pl(im, fi, at)) -> {Cr.Cir.is_cell(at, im, fi, nx) == True{} : Bool}:
  (hz, r) = h
  (hl, _) = r
  %Equal.sym(Bool, U32.is_zero(at), False{}, hz) :
    {Bool.or(Bool.and(Bool.not(_), U32.is_le(at, im)), Bool.and(U32.is_le(fi, at), U32.is_lt(at, nx))) == True{} : Bool}
  %Equal.sym(Bool, U32.is_le(at, im), True{}, hl) :
    {Bool.or(Bool.and(Bool.not(False{}), _), Bool.and(U32.is_le(fi, at), U32.is_lt(at, nx))) == True{} : Bool}
  {==}

# a place of the image is none of the machine's own
def pl.own(+im: U32, +fi: U32, +nx: U32, +at: U32, h: Pl(im, fi, at)) -> {D.Own(fi, nx, at) == False{} : Bool}:
  (_, r) = h
  (_, hf) = r
  %Equal.sym(Bool, U32.is_le(fi, at), False{}, hf) : {Bool.and(_, U32.is_lt(at, nx)) == False{} : Bool}
  {==}

# Loading
# -------

# loading cs from at keeps the cells below at (no wrap: at + |cs| <= top)
def load.frame(cs: List<&2, Cr.Cir.Cell>, +at: U32, +m: Cr.Cir.Cells, +x: U32, +top: U32,
  +hx: N.Le(1n+U32.to_nat(x), U32.to_nat(at)),
  +hb: N.Le(Nat.add(U32.to_nat(at), List.length(&2, Cr.Cir.Cell, cs)), U32.to_nat(top))) ->
  {Cr.Cir.Cells.get(Cr.Cir.load(cs, at, m), x) == Cr.Cir.Cells.get(m, x) : Cr.Cir.Cell}:
  match cs:
    case Nil{}:
      {==}
    case Con{+c, +rest}:
      +a = U32.to_nat(at)
      +l = List.length(&2, Cr.Cir.Cell, rest)
      +ia = U32.to_nat(U32.inc(at))
      +ei = D.u.inc(at, top, N.le_trans(1n+a, Nat.add(a, 1n+l), U32.to_nat(top), N.lt_add(a, l), hb))
      +hx2 = N.le_rw_r(1n+U32.to_nat(x), 1n+a, ia, Equal.sym(Nat, ia, 1n+a, ei), N.le_succ(1n+U32.to_nat(x), a, hx))
      +hb2 = N.le_rw_l(Nat.add(a, 1n+l), Nat.add(ia, l), U32.to_nat(top),
        Equal.trans(Nat, Nat.add(a, 1n+l), 1n+Nat.add(a, l), Nat.add(ia, l), N.add_succ_r(a, l),
          Equal.cong(Nat, Nat, z => Nat.add(z, l), 1n+a, ia, Equal.sym(Nat, ia, 1n+a, ei))), hb)
      Equal.trans(Cr.Cir.Cell, Cr.Cir.Cells.get(Cr.Cir.load(rest, U32.inc(at), Cr.Cir.Cells.set(m, at, c)), x),
        Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, at, c), x), Cr.Cir.Cells.get(m, x),
        load.frame(rest, U32.inc(at), Cr.Cir.Cells.set(m, at, c), x, top, hx2, hb2),
        D.cl.go(m, x, at, c, ne.to(x, at, hx)))

# the term of the cell at, the j-th of img (j = at - 1)
def tm.at(ts: List<&2, Bk.Term>, +img: List<&2, Bk.Term>, +at: U32, +j: Nat,
  hd: {List.drop(&2, Bk.Term, img, j) == ts : List<&2, Bk.Term>},
  +hj: {U32.to_nat(at) == 1n+j : Nat}) -> TmAt(ts, img, at):
  match ts:
    case Nil{}:
      Unit{}
    case Con{+t, +tr}:
      +ej = succ.inj(U32.to_nat(U32.sub(at, 1)), j,
        Equal.trans(Nat, 1n+U32.to_nat(U32.sub(at, 1)), U32.to_nat(at), 1n+j,
          dec.nat(at, (%Equal.sym(Nat, U32.to_nat(at), 1n+j, hj) : N.Le(1n, _); N.le_zero(j))), hj))
      %Equal.sym(Nat, U32.to_nat(U32.sub(at, 1)), j, ej) : {List.get(&2, Bk.Term, img, _) == Some{t} : Maybe<&2, Bk.Term>}
      Equal.trans(Maybe<&2, Bk.Term>, List.get(&2, Bk.Term, img, j), List.head(&2, Bk.Term, List.drop(&2, Bk.Term, img, j)), Some{t},
        get.hd(img, j), Equal.cong(List<&2, Bk.Term>, Maybe<&2, Bk.Term>, z => List.head(&2, Bk.Term, z),
          List.drop(&2, Bk.Term, img, j), Con{t, tr}, hd))

# the cells that Cir.load puts from at, with the terms of img from its j-th
# (j = at - 1): the image's places, below im + 1 <= fi
def load.lay(cs: List<&2, Cr.Cir.Cell>, +ts: List<&2, Bk.Term>, +at: U32, +m: Cr.Cir.Cells, +img: List<&2, Bk.Term>,
  +im: U32, +fi: U32, +j: Nat,
  +hd: {List.drop(&2, Bk.Term, img, j) == ts : List<&2, Bk.Term>},
  +hj: {U32.to_nat(at) == 1n+j : Nat},
  +hb: N.Le(Nat.add(U32.to_nat(at), List.length(&2, Cr.Cir.Cell, cs)), 1n+U32.to_nat(im)),
  +hf: N.Le(1n+U32.to_nat(im), U32.to_nat(fi))) ->
  Lay(cs, ts, Cr.Cir.load(cs, at, m), img, im, fi, at):
  match cs:
    case Nil{}:
      Unit{}
    case Con{+c, +cr}:
      +a = U32.to_nat(at)
      +l = List.length(&2, Cr.Cir.Cell, cr)
      +ia = U32.to_nat(U32.inc(at))
      +mc = Cr.Cir.Cells.set(m, at, c)
      # at + 1 + |cr| <= im + 1
      +hb1 = N.le_rw_l(Nat.add(a, 1n+l), 1n+Nat.add(a, l), 1n+U32.to_nat(im), N.add_succ_r(a, l), hb)
      +hai = N.le_trans(a, Nat.add(a, l), U32.to_nat(im), N.le_add_r(a, l), hb1)
      +haf = N.le_trans(1n+a, 1n+U32.to_nat(im), U32.to_nat(fi), hai, hf)
      +ei = D.u.inc(at, fi, haf)
      +hb2 = N.le_rw_l(1n+Nat.add(a, l), Nat.add(ia, l), 1n+U32.to_nat(im),
        Equal.cong(Nat, Nat, z => Nat.add(z, l), 1n+a, ia, Equal.sym(Nat, ia, 1n+a, ei)), hb1)
      +ec = Equal.trans(Cr.Cir.Cell, Cr.Cir.Cells.get(Cr.Cir.load(cr, U32.inc(at), mc), at), Cr.Cir.Cells.get(mc, at), c,
        load.frame(cr, U32.inc(at), mc, at, fi, (%Equal.sym(Nat, ia, 1n+a, ei) : N.Le(1n+a, _); N.le_refl(1n+a)),
          N.le_trans(Nat.add(ia, l), 1n+U32.to_nat(im), U32.to_nat(fi), hb2, hf)),
        D.cl.gs(m, at, c))
      +pl = {(nz.to(at, (%Equal.sym(Nat, a, 1n+j, hj) : N.Le(1n, _); N.le_zero(j))), (le.to(at, im, hai), nle.to(fi, at, haf))) :
        Pl(im, fi, at)}
      +hd2 = Equal.trans(List<&2, Bk.Term>, List.drop(&2, Bk.Term, img, 1n+j), List.tail(&2, Bk.Term, List.drop(&2, Bk.Term, img, j)),
        List.tail(&2, Bk.Term, ts), drop.tl(img, j),
        Equal.cong(List<&2, Bk.Term>, List<&2, Bk.Term>, z => List.tail(&2, Bk.Term, z), List.drop(&2, Bk.Term, img, j), ts, hd))
      +hj2 = Equal.trans(Nat, ia, 1n+a, 2n+j, ei, Equal.cong(Nat, Nat, z => 1n+z, a, 1n+j, hj))
      (ec, (tm.at(ts, img, at, j, hd, hj), (pl,
        load.lay(cr, List.tail(&2, Bk.Term, ts), U32.inc(at), mc, img, im, fi, 1n+j, hd2, hj2, hb2, hf))))

# Past the first cells
# --------------------

# n cells past at
def Up(n: Nat, +at: U32) -> U32:
  match n:
    case 0n:
      at
    case 1n+p:
      Up(p, U32.inc(at))

# xs past its first n
def Drop(-A: Data, n: Nat, xs: List<&2, A>) -> List<&2, A>:
  match n:
    case 0n:
      xs
    case 1n+p:
      Drop(A, p, List.tail(&2, A, xs))

# the cells past the first, from the next cell
def lay.tl(+cs: List<&2, Cr.Cir.Cell>, +ts: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +img: List<&2, Bk.Term>, +im: U32, +fi: U32,
  +at: U32, h: Lay(cs, ts, m, img, im, fi, at)) ->
  Lay(List.tail(&2, Cr.Cir.Cell, cs), List.tail(&2, Bk.Term, ts), m, img, im, fi, U32.inc(at)):
  match cs:
    case Nil{}:
      Unit{}
    case Con{_, _}:
      (_, r1) = h
      (_, r2) = r1
      (_, r3) = r2
      r3

# the cells past the first n, from n cells past at
def lay.drop(n: Nat, +cs: List<&2, Cr.Cir.Cell>, +ts: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +img: List<&2, Bk.Term>, +im: U32,
  +fi: U32, +at: U32, h: Lay(cs, ts, m, img, im, fi, at)) ->
  Lay(Drop(Cr.Cir.Cell, n, cs), Drop(Bk.Term, n, ts), m, img, im, fi, Up(n, at)):
  match n:
    case 0n:
      h
    case 1n+p:
      lay.drop(p, List.tail(&2, Cr.Cir.Cell, cs), List.tail(&2, Bk.Term, ts), m, img, im, fi, U32.inc(at),
        lay.tl(cs, ts, m, img, im, fi, at, h))

# the cells xs, then ys: each of xs a cell of the image, holding its cell
def lay.tbl(xs: List<&2, Cr.Cir.Cell>, +ys: List<&2, Cr.Cir.Cell>, +ts: List<&2, Bk.Term>, +m: Cr.Cir.Cells,
  +img: List<&2, Bk.Term>, +im: U32, +fi: U32, +nx: U32, +at: U32,
  h: Lay(List.append(&2, Cr.Cir.Cell, xs, ys), ts, m, img, im, fi, at)) -> D.Tbl.go(xs, m, im, fi, nx, at):
  match xs:
    case Nil{}:
      Unit{}
    case Con{+c, +rest}:
      (ec, r1) = h
      (_, r2) = r1
      (pl, r3) = r2
      (pl.cell(im, fi, nx, at, pl), (ec, lay.tbl(rest, ys, List.tail(&2, Bk.Term, ts), m, img, im, fi, nx, U32.inc(at), r3)))

# The image
# ---------

# the image's cells and terms, from cell 1, below first
def lay.img(+ds: List<&2, Bk.Def>, +k: U32, +first: U32,
  +hk: {U32.to_nat(k) == List.length(&2, Cr.Cir.Cell, Mc.Img.cells(ds)) : Nat},
  +hf: N.Le(1n+U32.to_nat(k), U32.to_nat(first))) ->
  Lay(Mc.Img.cells(ds), T.tm.img(ds), Cr.Cir.load(Mc.Img.cells(ds), 1, Cr.Cir.Cells.none{}), T.tm.img(ds), k, first, 1):
  +l = List.length(&2, Cr.Cir.Cell, Mc.Img.cells(ds))
  load.lay(Mc.Img.cells(ds), T.tm.img(ds), 1, Cr.Cir.Cells.none{}, T.tm.img(ds), k, first, 0n, drop0(T.tm.img(ds)), {==},
    N.le_rw_r(Nat.add(U32.to_nat(1), l), 1n+l, 1n+U32.to_nat(k),
      Equal.cong(Nat, Nat, z => 1n+z, l, U32.to_nat(k), Equal.sym(Nat, U32.to_nat(k), l, hk)),
      {N.le_refl(1n+l) : N.Le(Nat.add(U32.to_nat(1), l), 1n+l)}),
    hf)

# the cells of the image past its 290 first: the bodies of the defs
def cells.bodies(+ds: List<&2, Bk.Def>) ->
  {Drop(Cr.Cir.Cell, 290n, Mc.Img.cells(ds)) == Mc.Img.bodies(ds, Mc.Img.ids(Mc.Img.known(Mc.Img.names.defs(ds)), 0, Mc.Img.Trie.none{}),
    Mc.Img.refs(Mc.Img.defs(ds, Mc.I.book()), Mc.Img.Trie.none{}), Mc.I.book()) : List<&2, Cr.Cir.Cell>}:
  {==}

def terms.bodies(+ds: List<&2, Bk.Def>) -> {Drop(Bk.Term, 290n, T.tm.img(ds)) == T.tm.bodies(ds) : List<&2, Bk.Term>}:
  {==}

def up.book() -> {Up(290n, 1) == Mc.I.book() : U32}:
  {==}

# the bodies of the defs, from cell 291 (I.book())
def lay.bodies(+ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +img: List<&2, Bk.Term>, +im: U32, +fi: U32,
  h: Lay(Mc.Img.cells(ds), T.tm.img(ds), m, img, im, fi, 1)) ->
  Lay(Mc.Img.bodies(ds, Mc.Img.ids(Mc.Img.known(Mc.Img.names.defs(ds)), 0, Mc.Img.Trie.none{}),
    Mc.Img.refs(Mc.Img.defs(ds, Mc.I.book()), Mc.Img.Trie.none{}), Mc.I.book()), T.tm.bodies(ds), m, img, im, fi, Mc.I.book()):
  +cs = Drop(Cr.Cir.Cell, 290n, Mc.Img.cells(ds))
  +ts = Drop(Bk.Term, 290n, T.tm.img(ds))
  %cells.bodies(ds) : Lay(_, T.tm.bodies(ds), m, img, im, fi, Mc.I.book())
  %terms.bodies(ds) : Lay(cs, _, m, img, im, fi, Mc.I.book())
  %up.book() : Lay(cs, ts, m, img, im, fi, _)
  lay.drop(290n, Mc.Img.cells(ds), T.tm.img(ds), m, img, im, fi, 1, h)

# the cells of the image past its 271 first: the table, then the bodies
def cells.table(+ds: List<&2, Bk.Def>) ->
  {Drop(Cr.Cir.Cell, 271n, Mc.Img.cells(ds)) == List.append(&2, Cr.Cir.Cell, Mc.Img.table([]), Drop(Cr.Cir.Cell, 290n, Mc.Img.cells(ds))) :
    List<&2, Cr.Cir.Cell>}:
  {==}

def up.table() -> {Up(271n, 1) == 272 : U32}:
  {==}

# the table, whole, from cell 272
def lay.table(+ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +img: List<&2, Bk.Term>, +im: U32, +fi: U32, +nx: U32,
  h: Lay(Mc.Img.cells(ds), T.tm.img(ds), m, img, im, fi, 1)) -> D.Tbl(m, im, fi, nx):
  +ts = Drop(Bk.Term, 271n, T.tm.img(ds))
  +ys = Drop(Cr.Cir.Cell, 290n, Mc.Img.cells(ds))
  +r = lay.drop(271n, Mc.Img.cells(ds), T.tm.img(ds), m, img, im, fi, 1, h)
  +r2 = {(%Equal.sym(List<&2, Cr.Cir.Cell>, Drop(Cr.Cir.Cell, 271n, Mc.Img.cells(ds)), List.append(&2, Cr.Cir.Cell, Mc.Img.table([]), ys),
      cells.table(ds)) : Lay(_, ts, m, img, im, fi, Up(271n, 1)); r) :
    Lay(List.append(&2, Cr.Cir.Cell, Mc.Img.table([]), ys), ts, m, img, im, fi, Up(271n, 1))}
  +r3 = {(%Equal.sym(U32, Up(271n, 1), 272, up.table()) : Lay(List.append(&2, Cr.Cir.Cell, Mc.Img.table([]), ys), ts, m, img, im, fi, _); r2) :
    Lay(List.append(&2, Cr.Cir.Cell, Mc.Img.table([]), ys), ts, m, img, im, fi, 272)}
  lay.tbl(Mc.Img.table([]), ys, ts, m, img, im, fi, nx, 272, r3)
