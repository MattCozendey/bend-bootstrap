# compiler: layer B, the accounting of the machine's own cells (U1)
# =================================================================
#
# What AccK (definitions.bend) gives, and how each heap operation keeps it.
#
#   Many: how many of the n cells from c have a property CP (the properties
#     that Cov asks of a cell: a node of a term, a node of a root's term, one
#     of a list of cells, the cell y, either of two). When the n cells do not
#     wrap (they end at or before a cell e), the nodes of t reach at most |t|
#     of them (node.many), so Cov covers at most the STATIC cells, the roots'
#     nodes and the cells xs (cov.count), and with no pending cell the own
#     cells are at most Acc.need (acc.count).
#   plugs.size: the focus and the frames are the term.
#   cov.perm, cov.perm.x, cov.root, cov.cell: Cov sees its roots and its
#     cells as sets.
#   stat.*: no store makes a STATIC own cell.
#   acc.*: the Acc step of each heap operation (inc, dec at 0, release, a
#     store, the flag DATA, a new cell), for heap_ops.bend (U2).

import Base
import ../../Book/impl.bend as Bk
import ../../Program/impl.bend as Pg
import ../Cir/impl.bend as Cr
import ../need_big.bend as N
import ./definitions.bend as D
import ./statement_runs.bend as X

# Many
# ----

# a property of a cell: a node of the term t at r, a node of a term of the
# roots rs, one of the cells xs, the cell y, either of two, or none
type CP is Data:
  CP.node{t: Bk.Term, m: Cr.Cir.Cells, r: U32}
  CP.nodes{rs: List<&2, D.Rt>, m: Cr.Cir.Cells}
  CP.mem{xs: List<&2, U32>}
  CP.eq{y: U32}
  CP.or{a: CP, b: CP}
  CP.none{}

# p holds of the cell x
def CP.at(p: CP, +x: U32) -> Bool:
  match p:
    case CP.node{t, m, r}:
      D.Node(t, m, r, x)
    case CP.nodes{rs, m}:
      D.Nodes(rs, m, x)
    case CP.mem{xs}:
      D.Mem(xs, x)
    case CP.eq{y}:
      U32.is_eq(y, x)
    case CP.or{a, b}:
      Bool.or(CP.at(a, x), CP.at(b, x))
    case CP.none{}:
      False{}

# how many of the n cells from c p holds of
def Many(n: Nat, +c: U32, +p: CP) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+k:
      Nat.add(D.Nat.of(CP.at(p, c)), Many(k, U32.inc(c), p))

# a node of t at r, one step unfolded: r, or a node of a part, in the fields
# that Node reads
def CP.node.step(t: Bk.Term, +m: Cr.Cir.Cells, +r: U32) -> CP:
  match t:
    case Bk.Term.Var{_}:
      CP.eq{r}
    case Bk.Term.Ref{_}:
      CP.eq{r}
    case Bk.Term.Ann{y, z}:
      CP.or{CP.eq{r}, CP.or{CP.node{y, m, D.Fd(2n, m, r)}, CP.node{z, m, D.Fd(3n, m, r)}}}
    case Bk.Term.Let{_, v, f}:
      CP.or{CP.eq{r}, CP.or{CP.node{v, m, D.Fd(2n, m, r)}, CP.node{f, m, D.Fd(3n, m, r)}}}
    case Bk.Term.Typ{y}:
      CP.or{CP.eq{r}, CP.node{y, m, D.Fd(2n, m, r)}}
    case Bk.Term.Min{a, b}:
      CP.or{CP.eq{r}, CP.or{CP.node{a, m, D.Fd(2n, m, r)}, CP.node{b, m, D.Fd(3n, m, r)}}}
    case Bk.Term.All{_, a, b}:
      CP.or{CP.eq{r}, CP.or{CP.node{a, m, D.Fd(2n, m, r)}, CP.node{b, m, D.Fd(3n, m, r)}}}
    case Bk.Term.Lam{_, f}:
      CP.or{CP.eq{r}, CP.node{f, m, D.Fd(2n, m, r)}}
    case Bk.Term.App{_, f, y}:
      CP.or{CP.eq{r}, CP.or{CP.node{f, m, D.Fd(2n, m, r)}, CP.node{y, m, D.Fd(3n, m, r)}}}
    case Bk.Term.Sig{_, a, b}:
      CP.or{CP.eq{r}, CP.or{CP.node{a, m, D.Fd(2n, m, r)}, CP.node{b, m, D.Fd(3n, m, r)}}}
    case Bk.Term.Tup{_, a, b}:
      CP.or{CP.eq{r}, CP.or{CP.node{a, m, D.Fd(2n, m, r)}, CP.node{b, m, D.Fd(3n, m, r)}}}
    case Bk.Term.Prj{h}:
      CP.or{CP.eq{r}, CP.node{h, m, D.Fd(2n, m, r)}}
    case Bk.Term.Enu{_}:
      CP.eq{r}
    case Bk.Term.Lab{_}:
      CP.eq{r}
    case Bk.Term.Mat{_, h, n}:
      CP.or{CP.eq{r}, CP.or{CP.node{h, m, D.Fd(3n, m, r)}, CP.node{n, m, D.Fd(4n, m, r)}}}
    case Bk.Term.Efq{}:
      CP.eq{r}
    case Bk.Term.Eql{a, b, y}:
      CP.or{CP.eq{r}, CP.or{CP.node{a, m, D.Fd(2n, m, r)}, CP.or{CP.node{b, m, D.Fd(3n, m, r)}, CP.node{y, m, D.Fd(4n, m, r)}}}}
    case Bk.Term.Rfl{}:
      CP.eq{r}
    case Bk.Term.Rwt{e, y, f}:
      CP.or{CP.eq{r}, CP.or{CP.node{e, m, D.Fd(2n, m, r)}, CP.or{CP.node{y, m, D.Fd(3n, m, r)}, CP.node{f, m, D.Fd(4n, m, r)}}}}

# a node of a root's term, one step unfolded: of the first or of the rest
def CP.nodes.step(rs: List<&2, D.Rt>, +m: Cr.Cir.Cells) -> CP:
  match rs:
    case Nil{}:
      CP.none{}
    case Con{D.Rt{r, u}, rest}:
      CP.or{CP.node{u, m, r}, CP.nodes{rest, m}}

# one of the cells, one step unfolded: the first or one of the rest
def CP.mem.step(xs: List<&2, U32>) -> CP:
  match xs:
    case Nil{}:
      CP.none{}
    case Con{y, rest}:
      CP.or{CP.eq{y}, CP.mem{rest}}

# p, one step unfolded
def CP.step(p: CP) -> CP:
  match p:
    case CP.node{t, m, r}:
      CP.node.step(t, m, r)
    case CP.nodes{rs, m}:
      CP.nodes.step(rs, m)
    case CP.mem{xs}:
      CP.mem.step(xs)
    case CP.eq{y}:
      CP.eq{y}
    case CP.or{a, b}:
      CP.or{a, b}
    case CP.none{}:
      CP.none{}

# p and its step hold of the same cells
def cp.step.at(p: CP, +x: U32) -> {CP.at(p, x) == CP.at(CP.step(p), x) : Bool}:
  ?TODO

# so they count the same cells
def many.step(n: Nat, +c: U32, +p: CP) -> {Many(n, c, p) == Many(n, c, CP.step(p)) : Nat}:
  ?TODO

# either of a and b holds of at most the cells that a holds of and those that
# b holds of
def many.or(n: Nat, +c: U32, +a: CP, +b: CP) -> N.Le(Many(n, c, CP.or{a, b}), Nat.add(Many(n, c, a), Many(n, c, b))):
  ?TODO

# the n cells from c, which end at or before the cell e (they do not wrap):
# at most one of them is y
def many.eq(n: Nat, +c: U32, +y: U32, +e: U32, hw: N.Le(Nat.add(U32.to_nat(c), n), U32.to_nat(e))) ->
  N.Le(Many(n, c, CP.eq{y}), 1n):
  ?TODO

# the nodes of t at r are at most |t| of the n cells from c (no wrap)
def node.many(t: Bk.Term, +m: Cr.Cir.Cells, +r: U32, +n: Nat, +c: U32, +e: U32,
  hw: N.Le(Nat.add(U32.to_nat(c), n), U32.to_nat(e))) -> N.Le(Many(n, c, CP.node{t, m, r}), Pg.Term.size(t)):
  ?TODO

# the nodes of the roots' terms are at most their nodes
def nodes.many(rs: List<&2, D.Rt>, +m: Cr.Cir.Cells, +n: Nat, +c: U32, +e: U32,
  hw: N.Le(Nat.add(U32.to_nat(c), n), U32.to_nat(e))) -> N.Le(Many(n, c, CP.nodes{rs, m}), D.Rts.size(rs)):
  ?TODO

# the cells xs are at most |xs| of them
def mem.many(xs: List<&2, U32>, +n: Nat, +c: U32, +e: U32, hw: N.Le(Nat.add(U32.to_nat(c), n), U32.to_nat(e))) ->
  N.Le(Many(n, c, CP.mem{xs}), List.length(&2, U32, xs)):
  ?TODO

# each of the n cells that Cov covers is STATIC, a node of a root's term or
# one of xs
def cov.many(n: Nat, +m: Cr.Cir.Cells, +c: U32, +rs: List<&2, D.Rt>, +xs: List<&2, U32>,
  h: {D.Cov(n, m, c, rs, xs) == True{} : Bool}) ->
  N.Le(n, Nat.add(D.Stat(n, m, c), Nat.add(Many(n, c, CP.nodes{rs, m}), Many(n, c, CP.mem{xs})))):
  ?TODO

# the n cells that Cov covers (no wrap) are at most the STATIC ones, the
# roots' nodes and the cells xs
def cov.count(+n: Nat, +m: Cr.Cir.Cells, +c: U32, +rs: List<&2, D.Rt>, +xs: List<&2, U32>, +e: U32,
  h: {D.Cov(n, m, c, rs, xs) == True{} : Bool}, hw: N.Le(Nat.add(U32.to_nat(c), n), U32.to_nat(e))) ->
  N.Le(n, Nat.add(D.Stat(n, m, c), Nat.add(D.Rts.size(rs), List.length(&2, U32, xs)))):
  ?TODO

# with no pending cell (and so no zombie), the own cells are at most
# Acc.need: the STATIC ones, the roots' and the frames' nodes, the frames and
# the cells xs
def acc.count(+dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +rs: List<&2, D.Rt>, +xs: List<&2, U32>, +sp: U32,
  +fs: List<&2, D.AF>, +zs: List<&2, D.Rt>,
  h: D.AccK(dk, ds, ks, img, m, nx, fi, im, rs, xs, sp, fs, Nil{}, zs)) ->
  N.Le(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), D.Acc.need(m, nx, fi, rs, xs, sp, fs)):
  ?TODO

# The frames and the focus
# ------------------------

# the term of a state has the nodes of its focus, of its frames' terms, and
# one for each frame
def plugs.size(fs: List<&2, D.AF>, +m: Cr.Cir.Cells, +fr: U32, v: Bk.Term) ->
  {Pg.Term.size(D.A.plugs(fs, v)) ==
    Nat.add(Pg.Term.size(v), Nat.add(D.Rts.size(D.Fr.rts(fs, m, fr)), List.length(&2, U32, D.Fr.cells(fs, m, fr)))) : Nat}:
  ?TODO

# Cov's roots and cells are sets
# ------------------------------

# two blocks A and B of the roots, after the roots P, trade places: Cov is
# the same
def cov.perm(n: Nat, +m: Cr.Cir.Cells, +c: U32, +P: List<&2, D.Rt>, +A: List<&2, D.Rt>, +B: List<&2, D.Rt>,
  +C: List<&2, D.Rt>, +xs: List<&2, U32>) ->
  {D.Cov(n, m, c, List.append(&2, D.Rt, P, List.append(&2, D.Rt, A, List.append(&2, D.Rt, B, C))), xs) ==
    D.Cov(n, m, c, List.append(&2, D.Rt, P, List.append(&2, D.Rt, B, List.append(&2, D.Rt, A, C))), xs) : Bool}:
  ?TODO

# two blocks A and B of the cells, after the cells P, trade places: Cov is
# the same
def cov.perm.x(n: Nat, +m: Cr.Cir.Cells, +c: U32, +rs: List<&2, D.Rt>, +P: List<&2, U32>, +A: List<&2, U32>,
  +B: List<&2, U32>, +C: List<&2, U32>) ->
  {D.Cov(n, m, c, rs, List.append(&2, U32, P, List.append(&2, U32, A, List.append(&2, U32, B, C)))) ==
    D.Cov(n, m, c, rs, List.append(&2, U32, P, List.append(&2, U32, B, List.append(&2, U32, A, C)))) : Bool}:
  ?TODO

# one more root keeps Cov
def cov.root(n: Nat, +m: Cr.Cir.Cells, +c: U32, +r: D.Rt, +rs: List<&2, D.Rt>, +xs: List<&2, U32>,
  h: {D.Cov(n, m, c, rs, xs) == True{} : Bool}) -> {D.Cov(n, m, c, Con{r, rs}, xs) == True{} : Bool}:
  ?TODO

# one more cell keeps Cov
def cov.cell(n: Nat, +m: Cr.Cir.Cells, +c: U32, +x: U32, +rs: List<&2, D.Rt>, +xs: List<&2, U32>,
  h: {D.Cov(n, m, c, rs, xs) == True{} : Bool}) -> {D.Cov(n, m, c, rs, Con{x, xs}) == True{} : Bool}:
  ?TODO

# No store makes a STATIC own cell
# --------------------------------

# a store of a cell that is not STATIC: no more STATIC cells
def stat.set(n: Nat, +m: Cr.Cir.Cells, +c: U32, +z: U32, +x: Cr.Cir.Cell,
  hx: {D.FlW(Cr.Cir.Cell.get(0n, x), 1024) == False{} : Bool}) ->
  N.Le(D.Stat(n, Cr.Cir.Cells.set(m, z, x), c), D.Stat(n, m, c)):
  ?TODO

# stores to field 1: the same STATIC cells
def stat.put1(n: Nat, +ws: List<&2, D.W1>, +m: Cr.Cir.Cells, +c: U32) ->
  {D.Stat(n, D.Put1(ws, m), c) == D.Stat(n, m, c) : Nat}:
  ?TODO

# the flag DATA of the cell z: the same STATIC cells
def stat.flag(n: Nat, +m: Cr.Cir.Cells, +c: U32, +z: U32) ->
  {D.Stat(n, Cr.Cir.Cells.set(m, z, Cr.Cir.Cell.set(0n, Cr.Cir.Cells.get(m, z), U32.or(D.Fd(0n, m, z), 512))), c) ==
    D.Stat(n, m, c) : Nat}:
  ?TODO

# a new cell, all zeros, at next nx (from fi on, below the cell e): one more
# own cell, not STATIC
def stat.fresh(+m: Cr.Cir.Cells, +nx: U32, +fi: U32, +e: U32, hfn: {U32.is_le(fi, nx) == True{} : Bool},
  hl: {U32.is_lt(nx, e) == True{} : Bool}) ->
  {D.Stat(Nat.sub(U32.to_nat(U32.inc(nx)), U32.to_nat(fi)), Cr.Cir.Cells.set(m, nx, Cr.Cir.Cell.zero()), fi) ==
    D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi) : Nat}:
  ?TODO

# The Acc step of each heap operation (for heap_ops.bend)
# -------------------------------------------------------
#
# Each takes the operation's HSK and AccK, as its law does, and gives AccK
# after it. Where the operation stores to field 1 or sets the flag DATA, it
# takes the zombies' terms after it (RtsK of zs), which the same frame
# lemmas as HSK's give.

# a new root keeps Acc (M.inc of a STATIC cell changes no cell)
def acc.root(+dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +r: D.Rt, +rs: List<&2, D.Rt>, +xs: List<&2, U32>, +sp: U32,
  +fs: List<&2, D.AF>, +ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  h: D.AccK(dk, ds, ks, img, m, nx, fi, im, rs, xs, sp, fs, ps, zs)) ->
  D.AccK(dk, ds, ks, img, m, nx, fi, im, Con{r, rs}, xs, sp, fs, ps, zs):
  ?TODO

# M.inc of the held term cell c of u (a tag below 19, so no frame): c is a
# root, and its count (field 1) gets v
def acc.inc(+dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>,
  +sp: U32, +pend: U32, +ps: List<&2, U32>, +c: U32, +u: Bk.Term, +v: U32, +xs: List<&2, U32>, +zs: List<&2, D.Rt>,
  hs: D.HSK(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps),
  hac: D.AccK(dk, ds, ks, img, m, nx, fi, im, os, xs, sp, fs, ps, zs),
  ht: {U32.is_lt(D.Tg(m, c), 19) == True{} : Bool},
  hz: D.RtsK(dk, ds, X.X.put(m, 1n, c, v), im, fi, nx, ks, img, zs)) ->
  D.AccK(dk, ds, ks, img, X.X.put(m, 1n, c, v), nx, fi, im, Con{D.Rt{c, u}, os}, xs, sp, fs, ps, zs):
  ?TODO

# M.dec of the root c of u, a term cell, to the count 0: field 1 gets d, then
# pend; c goes to the pend list, and its root to the zombies
def acc.dec.pend(+dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>,
  +sp: U32, +pend: U32, +ps: List<&2, U32>, +c: U32, +u: Bk.Term, +d: U32, +xs: List<&2, U32>, +zs: List<&2, D.Rt>,
  hs: D.HSK(dk, ds, ks, img, m, nx, fi, im, Con{D.Rt{c, u}, os}, bs, fs, sp, pend, ps),
  hac: D.AccK(dk, ds, ks, img, m, nx, fi, im, Con{D.Rt{c, u}, os}, xs, sp, fs, ps, zs),
  ht: {U32.is_lt(D.Tg(m, c), 19) == True{} : Bool},
  hz: D.RtsK(dk, ds, X.X.put(X.X.put(m, 1n, c, d), 1n, c, pend), im, fi, nx, ks, img, Con{D.Rt{c, u}, zs})) ->
  D.AccK(dk, ds, ks, img, X.X.put(X.X.put(m, 1n, c, d), 1n, c, pend), nx, fi, im, os, xs, sp, fs, Con{c, ps}, Con{D.Rt{c, u}, zs}):
  ?TODO

# M.release of z, of the machine's own kinds (tag 32 or more), out of the pend
# list and holding no pointer (so no frame): z leaves the temporaries for the
# pend list, and its field 1 gets pend
def acc.release(+dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>,
  +sp: U32, +pend: U32, +ps: List<&2, U32>, +z: U32, +xs: List<&2, U32>, +zs: List<&2, D.Rt>,
  hs: D.HSK(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps),
  hac: D.AccK(dk, ds, ks, img, m, nx, fi, im, os, Con{z, xs}, sp, fs, ps, zs),
  ht: {U32.is_lt(D.Tg(m, z), 32) == False{} : Bool},
  hm: {D.Mem(ps, z) == False{} : Bool},
  hfs: {D.Fs(m, ps, z) == Nil{} : List<&2, U32>},
  hz: D.RtsK(dk, ds, X.X.put(m, 1n, z, pend), im, fi, nx, ks, img, zs)) ->
  D.AccK(dk, ds, ks, img, X.X.put(m, 1n, z, pend), nx, fi, im, os, xs, sp, fs, Con{z, ps}, zs):
  ?TODO

# a store at the temporary z, which nothing points to, is not STATIC, is out
# of the pend list and holds no pointer (so no frame): Acc's covers stay
def acc.store(+dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>,
  +sp: U32, +pend: U32, +ps: List<&2, U32>, +z: U32, +x: Cr.Cir.Cell, +xs: List<&2, U32>, +zs: List<&2, D.Rt>,
  hs: D.HSK(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps),
  hac: D.AccK(dk, ds, ks, img, m, nx, fi, im, os, xs, sp, fs, ps, zs),
  hzx: {D.Mem(xs, z) == True{} : Bool},
  hm: {D.Mem(ps, z) == False{} : Bool},
  hzs: {D.Fl(m, z, 1024) == False{} : Bool},
  hz0: {D.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, D.Rt.cells(os), z) == 0n : Nat},
  hzf: {D.Fs(m, ps, z) == Nil{} : List<&2, U32>}) ->
  D.AccK(dk, ds, ks, img, Cr.Cir.Cells.set(m, z, x), nx, fi, im, os, xs, sp, fs, ps, zs):
  ?TODO

# the flag DATA of the cell c: the tag, the flag STATIC and fields 1 to 4 stay
def acc.flag(+dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +rs: List<&2, D.Rt>, +xs: List<&2, U32>, +sp: U32,
  +fs: List<&2, D.AF>, +ps: List<&2, U32>, +zs: List<&2, D.Rt>, +c: U32,
  hac: D.AccK(dk, ds, ks, img, m, nx, fi, im, rs, xs, sp, fs, ps, zs),
  hz: D.RtsK(dk, ds, Cr.Cir.Cells.set(m, c, Cr.Cir.Cell.set(0n, Cr.Cir.Cells.get(m, c), U32.or(D.Fd(0n, m, c), 512))), im, fi, nx,
    ks, img, zs)) ->
  D.AccK(dk, ds, ks, img, Cr.Cir.Cells.set(m, c, Cr.Cir.Cell.set(0n, Cr.Cir.Cells.get(m, c), U32.or(D.Fd(0n, m, c), 512))), nx, fi,
    im, rs, xs, sp, fs, ps, zs):
  ?TODO

# a new cell, all zeros, at next nx (the pend list is empty; nx is below the
# cell e): it is a temporary, and next grows
def acc.fresh(+dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>,
  +sp: U32, +pend: U32, +xs: List<&2, U32>, +zs: List<&2, D.Rt>, +e: U32,
  hs: D.HSK(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, Nil{}),
  hac: D.AccK(dk, ds, ks, img, m, nx, fi, im, os, xs, sp, fs, Nil{}, zs),
  hfn: {U32.is_le(fi, nx) == True{} : Bool},
  hl: {U32.is_lt(nx, e) == True{} : Bool}) ->
  D.AccK(dk, ds, ks, img, Cr.Cir.Cells.set(m, nx, Cr.Cir.Cell.zero()), U32.inc(nx), fi, im, os, Con{nx, xs}, sp, fs, Nil{}, Nil{}):
  ?TODO

# Waiting for the AccK fix (B-design part 3; U2's F2): M.dec when the count
# stays above 0 (acc.dec.keep), and M.alloc from the pend list (cov.reuse,
# acc.reuse). Their statements follow the fixed AccK.
