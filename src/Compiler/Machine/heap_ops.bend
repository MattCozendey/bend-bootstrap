# compiler: layer B, the heap's operations (U2)
# =============================================
#
# The laws inc.post, dec.post, alloc.post, release.post, is.fresh, node.part,
# store.post and data.flag of definitions.bend: each statement of the heap
# (M.inc, M.dec, M.alloc, M.release, a store) keeps HSK and the accounting
# AccK, within its budget. Filled by U2; U0 left each as ?TODO.

import Base
import ../../Book/impl.bend as Bk
import ../../Eval/impl.bend as El
import ../Cir/impl.bend as Cr
import ./impl.bend as Mc
import ./definitions.bend as D

# Parts of nodes
# --------------
#
# A part (Fs) of a node c of a term is a node of that term: c is a term
# cell, whose pointers are its parts by its tag's mask (Tbl), and those are
# the fields that Node follows.

# r is a node of every term at r
def node.self(t: Bk.Term, +m: Cr.Cir.Cells, +r: U32, +c: U32, e: {U32.is_eq(r, c) == True{} : Bool}) ->
  {D.Node(t, m, r, c) == True{} : Bool}:
  match t:
    case Bk.Term.Var{_}:
      e
    case Bk.Term.Ref{_}:
      e
    case Bk.Term.Ann{y, z}:
      D.or.l(U32.is_eq(r, c), Bool.or(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c)), e)
    case Bk.Term.Let{_, v, f}:
      D.or.l(U32.is_eq(r, c), Bool.or(D.Node(v, m, D.Fd(2n, m, r), c), D.Node(f, m, D.Fd(3n, m, r), c)), e)
    case Bk.Term.Typ{y}:
      D.or.l(U32.is_eq(r, c), D.Node(y, m, D.Fd(2n, m, r), c), e)
    case Bk.Term.Min{a, b}:
      D.or.l(U32.is_eq(r, c), Bool.or(D.Node(a, m, D.Fd(2n, m, r), c), D.Node(b, m, D.Fd(3n, m, r), c)), e)
    case Bk.Term.All{_, a, b}:
      D.or.l(U32.is_eq(r, c), Bool.or(D.Node(a, m, D.Fd(2n, m, r), c), D.Node(b, m, D.Fd(3n, m, r), c)), e)
    case Bk.Term.Lam{_, f}:
      D.or.l(U32.is_eq(r, c), D.Node(f, m, D.Fd(2n, m, r), c), e)
    case Bk.Term.App{_, f, y}:
      D.or.l(U32.is_eq(r, c), Bool.or(D.Node(f, m, D.Fd(2n, m, r), c), D.Node(y, m, D.Fd(3n, m, r), c)), e)
    case Bk.Term.Sig{_, a, b}:
      D.or.l(U32.is_eq(r, c), Bool.or(D.Node(a, m, D.Fd(2n, m, r), c), D.Node(b, m, D.Fd(3n, m, r), c)), e)
    case Bk.Term.Tup{_, a, b}:
      D.or.l(U32.is_eq(r, c), Bool.or(D.Node(a, m, D.Fd(2n, m, r), c), D.Node(b, m, D.Fd(3n, m, r), c)), e)
    case Bk.Term.Prj{h}:
      D.or.l(U32.is_eq(r, c), D.Node(h, m, D.Fd(2n, m, r), c), e)
    case Bk.Term.Enu{_}:
      e
    case Bk.Term.Lab{_}:
      e
    case Bk.Term.Mat{_, h, n}:
      D.or.l(U32.is_eq(r, c), Bool.or(D.Node(h, m, D.Fd(3n, m, r), c), D.Node(n, m, D.Fd(4n, m, r), c)), e)
    case Bk.Term.Efq{}:
      e
    case Bk.Term.Eql{a, b, y}:
      D.or.l(U32.is_eq(r, c), Bool.or(D.Node(a, m, D.Fd(2n, m, r), c), Bool.or(D.Node(b, m, D.Fd(3n, m, r), c), D.Node(y, m, D.Fd(4n, m, r), c))), e)
    case Bk.Term.Rfl{}:
      e
    case Bk.Term.Rwt{e2, y, f}:
      D.or.l(U32.is_eq(r, c), Bool.or(D.Node(e2, m, D.Fd(2n, m, r), c), Bool.or(D.Node(y, m, D.Fd(3n, m, r), c), D.Node(f, m, D.Fd(4n, m, r), c))), e)

# the pointers of the cell c, a node of the term t at r when c is r, are the
# fields of t's mask
def np.fs(+t: Bk.Term, +dk: Bool, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ps: List<&2, U32>, +tbl: D.Tbl(m, im, fi, nx), +r: U32, +c: U32, +y: U32,
  nd: D.NdK(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), t, D.A.tag(t)), hlt: {U32.is_lt(D.A.tag(t), 19) == True{} : Bool},
  e: {U32.is_eq(r, c) == True{} : Bool}, hy: {D.Mem(D.Fs(m, ps, c), y) == True{} : Bool}) ->
  {D.Mem(D.Fs.term(D.Mask(t), D.Fd(2n, m, r), D.Fd(3n, m, r), D.Fd(4n, m, r)), y) == True{} : Bool}:
  +et = D.nd.tgk(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), t, D.A.tag(t), nd)
  %D.fs.term(m, ps, r, D.A.tag(t), D.Mask(t), et, hlt, D.tbl.mask(m, im, fi, nx, t, tbl)) : {D.Mem(_, y) == True{} : Bool}
  %Equal.sym(U32, r, c, D.u32.eq(r, c, e)) : {D.Mem(D.Fs(m, ps, _), y) == True{} : Bool}
  hy

# a term of one part, in the field x of r
def np.one(+a: Bk.Term, +m: Cr.Cir.Cells, +r: U32, +x: U32, +c: U32, +y: U32,
  hn: {Bool.or(U32.is_eq(r, c), D.Node(a, m, x, c)) == True{} : Bool},
  hm: {U32.is_eq(r, c) == True{} : Bool} -> {Bool.or(U32.is_eq(x, y), False{}) == True{} : Bool},
  ia: {D.Node(a, m, x, c) == True{} : Bool} -> {D.Node(a, m, x, y) == True{} : Bool}) ->
  {Bool.or(U32.is_eq(r, y), D.Node(a, m, x, y)) == True{} : Bool}:
  D.or.cases(U32.is_eq(r, c), D.Node(a, m, x, c), {Bool.or(U32.is_eq(r, y), D.Node(a, m, x, y)) == True{} : Bool}, hn,
    e => D.or.r(U32.is_eq(r, y), D.Node(a, m, x, y),
      D.or.cases(U32.is_eq(x, y), False{}, {D.Node(a, m, x, y) == True{} : Bool}, hm(e),
        ex => node.self(a, m, x, y, ex), ef => D.bool.ft({D.Node(a, m, x, y) == True{} : Bool}, ef))),
    e => D.or.r(U32.is_eq(r, y), D.Node(a, m, x, y), ia(e)))

# a term of two parts, in the fields x and z of r
def np.two(+a: Bk.Term, +b: Bk.Term, +m: Cr.Cir.Cells, +r: U32, +x: U32, +z: U32, +c: U32, +y: U32,
  hn: {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(a, m, x, c), D.Node(b, m, z, c))) == True{} : Bool},
  hm: {U32.is_eq(r, c) == True{} : Bool} -> {Bool.or(U32.is_eq(x, y), Bool.or(U32.is_eq(z, y), False{})) == True{} : Bool},
  ia: {D.Node(a, m, x, c) == True{} : Bool} -> {D.Node(a, m, x, y) == True{} : Bool},
  ib: {D.Node(b, m, z, c) == True{} : Bool} -> {D.Node(b, m, z, y) == True{} : Bool}) ->
  {Bool.or(U32.is_eq(r, y), Bool.or(D.Node(a, m, x, y), D.Node(b, m, z, y))) == True{} : Bool}:
  -G = {Bool.or(U32.is_eq(r, y), Bool.or(D.Node(a, m, x, y), D.Node(b, m, z, y))) == True{} : Bool}
  -R = Bool.or(D.Node(a, m, x, y), D.Node(b, m, z, y))
  D.or.cases(U32.is_eq(r, c), Bool.or(D.Node(a, m, x, c), D.Node(b, m, z, c)), G, hn,
    e => D.or.r(U32.is_eq(r, y), R,
      D.or.cases(U32.is_eq(x, y), Bool.or(U32.is_eq(z, y), False{}), {R == True{} : Bool}, hm(e),
        ex => D.or.l(D.Node(a, m, x, y), D.Node(b, m, z, y), node.self(a, m, x, y, ex)),
        ez => D.or.cases(U32.is_eq(z, y), False{}, {R == True{} : Bool}, ez,
          ez2 => D.or.r(D.Node(a, m, x, y), D.Node(b, m, z, y), node.self(b, m, z, y, ez2)),
          ef => D.bool.ft({R == True{} : Bool}, ef)))),
    e => D.or.r(U32.is_eq(r, y), R,
      D.or.cases(D.Node(a, m, x, c), D.Node(b, m, z, c), {R == True{} : Bool}, e,
        ea => D.or.l(D.Node(a, m, x, y), D.Node(b, m, z, y), ia(ea)),
        eb => D.or.r(D.Node(a, m, x, y), D.Node(b, m, z, y), ib(eb)))))

# a term of three parts, in the fields x, z and w of r
def np.three(+a: Bk.Term, +b: Bk.Term, +d: Bk.Term, +m: Cr.Cir.Cells, +r: U32, +x: U32, +z: U32, +w: U32, +c: U32, +y: U32,
  hn: {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(a, m, x, c), Bool.or(D.Node(b, m, z, c), D.Node(d, m, w, c)))) == True{} : Bool},
  hm: {U32.is_eq(r, c) == True{} : Bool} -> {Bool.or(U32.is_eq(x, y), Bool.or(U32.is_eq(z, y), Bool.or(U32.is_eq(w, y), False{}))) == True{} : Bool},
  ia: {D.Node(a, m, x, c) == True{} : Bool} -> {D.Node(a, m, x, y) == True{} : Bool},
  ib: {D.Node(b, m, z, c) == True{} : Bool} -> {D.Node(b, m, z, y) == True{} : Bool},
  id: {D.Node(d, m, w, c) == True{} : Bool} -> {D.Node(d, m, w, y) == True{} : Bool}) ->
  {Bool.or(U32.is_eq(r, y), Bool.or(D.Node(a, m, x, y), Bool.or(D.Node(b, m, z, y), D.Node(d, m, w, y)))) == True{} : Bool}:
  -G = {Bool.or(U32.is_eq(r, y), Bool.or(D.Node(a, m, x, y), Bool.or(D.Node(b, m, z, y), D.Node(d, m, w, y)))) == True{} : Bool}
  -R = Bool.or(D.Node(a, m, x, y), Bool.or(D.Node(b, m, z, y), D.Node(d, m, w, y)))
  -R2 = Bool.or(D.Node(b, m, z, y), D.Node(d, m, w, y))
  D.or.cases(U32.is_eq(r, c), Bool.or(D.Node(a, m, x, c), Bool.or(D.Node(b, m, z, c), D.Node(d, m, w, c))), G, hn,
    e => D.or.r(U32.is_eq(r, y), R,
      D.or.cases(U32.is_eq(x, y), Bool.or(U32.is_eq(z, y), Bool.or(U32.is_eq(w, y), False{})), {R == True{} : Bool}, hm(e),
        ex => D.or.l(D.Node(a, m, x, y), R2, node.self(a, m, x, y, ex)),
        ez => D.or.r(D.Node(a, m, x, y), R2,
          D.or.cases(U32.is_eq(z, y), Bool.or(U32.is_eq(w, y), False{}), {R2 == True{} : Bool}, ez,
            ez2 => D.or.l(D.Node(b, m, z, y), D.Node(d, m, w, y), node.self(b, m, z, y, ez2)),
            ew => D.or.cases(U32.is_eq(w, y), False{}, {R2 == True{} : Bool}, ew,
              ew2 => D.or.r(D.Node(b, m, z, y), D.Node(d, m, w, y), node.self(d, m, w, y, ew2)),
              ef => D.bool.ft({R2 == True{} : Bool}, ef)))))),
    e => D.or.r(U32.is_eq(r, y), R,
      D.or.cases(D.Node(a, m, x, c), Bool.or(D.Node(b, m, z, c), D.Node(d, m, w, c)), {R == True{} : Bool}, e,
        ea => D.or.l(D.Node(a, m, x, y), R2, ia(ea)),
        e2 => D.or.r(D.Node(a, m, x, y), R2,
          D.or.cases(D.Node(b, m, z, c), D.Node(d, m, w, c), {R2 == True{} : Bool}, e2,
            eb => D.or.l(D.Node(b, m, z, y), D.Node(d, m, w, y), ib(eb)),
            ed => D.or.r(D.Node(b, m, z, y), D.Node(d, m, w, y), id(ed)))))))

# a part y of a node c of the term t at r is a node of t at r
def np.term(t: Bk.Term, +dk: Bool, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +tbl: D.Tbl(m, im, fi, nx), +r: U32, +c: U32, +y: U32,
  h: D.IsK(dk, ds, m, im, fi, nx, ks, img, r, t), hn: {D.Node(t, m, r, c) == True{} : Bool},
  +hy: {D.Mem(D.Fs(m, ps, c), y) == True{} : Bool}) -> {D.Node(t, m, r, y) == True{} : Bool}:
  match t:
    case Bk.Term.Var{+i}:
      match h:
        case Tuple{+nd, _}:
          D.bool.ft({D.Node(Bk.Term.Var{i}, m, r, y) == True{} : Bool}, np.fs(Bk.Term.Var{i}, dk, ds, m, im, fi, nx, ps, tbl, r, c, y, nd, {==}, hn, hy))
    case Bk.Term.Ref{+k}:
      match h:
        case Tuple{+nd, _}:
          D.bool.ft({D.Node(Bk.Term.Ref{k}, m, r, y) == True{} : Bool}, np.fs(Bk.Term.Ref{k}, dk, ds, m, im, fi, nx, ps, tbl, r, c, y, nd, {==}, hn, hy))
    case Bk.Term.Ann{+a, +b}:
      match h:
        case Tuple{+nd, Tuple{Tuple{_, h2}, Tuple{_, h3}}}:
          np.two(a, b, m, r, D.Fd(2n, m, r), D.Fd(3n, m, r), c, y, hn,
            e => np.fs(Bk.Term.Ann{a, b}, dk, ds, m, im, fi, nx, ps, tbl, r, c, y, nd, {==}, e, hy),
            e => np.term(a, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(2n, m, r), c, y, h2, e, hy),
            e => np.term(b, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(3n, m, r), c, y, h3, e, hy))
    case Bk.Term.Let{+q, +a, +b}:
      match h:
        case Tuple{+nd, Tuple{_, Tuple{Tuple{_, h2}, Tuple{_, h3}}}}:
          np.two(a, b, m, r, D.Fd(2n, m, r), D.Fd(3n, m, r), c, y, hn,
            e => np.fs(Bk.Term.Let{q, a, b}, dk, ds, m, im, fi, nx, ps, tbl, r, c, y, nd, {==}, e, hy),
            e => np.term(a, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(2n, m, r), c, y, h2, e, hy),
            e => np.term(b, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(3n, m, r), c, y, h3, e, hy))
    case Bk.Term.Typ{+a}:
      match h:
        case Tuple{+nd, Tuple{_, h2}}:
          np.one(a, m, r, D.Fd(2n, m, r), c, y, hn,
            e => np.fs(Bk.Term.Typ{a}, dk, ds, m, im, fi, nx, ps, tbl, r, c, y, nd, {==}, e, hy),
            e => np.term(a, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(2n, m, r), c, y, h2, e, hy))
    case Bk.Term.Min{+a, +b}:
      match h:
        case Tuple{+nd, Tuple{Tuple{_, h2}, Tuple{_, h3}}}:
          np.two(a, b, m, r, D.Fd(2n, m, r), D.Fd(3n, m, r), c, y, hn,
            e => np.fs(Bk.Term.Min{a, b}, dk, ds, m, im, fi, nx, ps, tbl, r, c, y, nd, {==}, e, hy),
            e => np.term(a, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(2n, m, r), c, y, h2, e, hy),
            e => np.term(b, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(3n, m, r), c, y, h3, e, hy))
    case Bk.Term.All{+q, +a, +b}:
      match h:
        case Tuple{+nd, Tuple{_, Tuple{Tuple{_, h2}, Tuple{_, h3}}}}:
          np.two(a, b, m, r, D.Fd(2n, m, r), D.Fd(3n, m, r), c, y, hn,
            e => np.fs(Bk.Term.All{q, a, b}, dk, ds, m, im, fi, nx, ps, tbl, r, c, y, nd, {==}, e, hy),
            e => np.term(a, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(2n, m, r), c, y, h2, e, hy),
            e => np.term(b, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(3n, m, r), c, y, h3, e, hy))
    case Bk.Term.Lam{+q, +a}:
      match h:
        case Tuple{+nd, Tuple{_, Tuple{_, h2}}}:
          np.one(a, m, r, D.Fd(2n, m, r), c, y, hn,
            e => np.fs(Bk.Term.Lam{q, a}, dk, ds, m, im, fi, nx, ps, tbl, r, c, y, nd, {==}, e, hy),
            e => np.term(a, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(2n, m, r), c, y, h2, e, hy))
    case Bk.Term.App{+q, +a, +b}:
      match h:
        case Tuple{+nd, Tuple{_, Tuple{Tuple{_, h2}, Tuple{_, h3}}}}:
          np.two(a, b, m, r, D.Fd(2n, m, r), D.Fd(3n, m, r), c, y, hn,
            e => np.fs(Bk.Term.App{q, a, b}, dk, ds, m, im, fi, nx, ps, tbl, r, c, y, nd, {==}, e, hy),
            e => np.term(a, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(2n, m, r), c, y, h2, e, hy),
            e => np.term(b, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(3n, m, r), c, y, h3, e, hy))
    case Bk.Term.Sig{+q, +a, +b}:
      match h:
        case Tuple{+nd, Tuple{_, Tuple{Tuple{_, h2}, Tuple{_, h3}}}}:
          np.two(a, b, m, r, D.Fd(2n, m, r), D.Fd(3n, m, r), c, y, hn,
            e => np.fs(Bk.Term.Sig{q, a, b}, dk, ds, m, im, fi, nx, ps, tbl, r, c, y, nd, {==}, e, hy),
            e => np.term(a, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(2n, m, r), c, y, h2, e, hy),
            e => np.term(b, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(3n, m, r), c, y, h3, e, hy))
    case Bk.Term.Tup{+q, +a, +b}:
      match h:
        case Tuple{+nd, Tuple{_, Tuple{Tuple{_, h2}, Tuple{_, h3}}}}:
          np.two(a, b, m, r, D.Fd(2n, m, r), D.Fd(3n, m, r), c, y, hn,
            e => np.fs(Bk.Term.Tup{q, a, b}, dk, ds, m, im, fi, nx, ps, tbl, r, c, y, nd, {==}, e, hy),
            e => np.term(a, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(2n, m, r), c, y, h2, e, hy),
            e => np.term(b, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(3n, m, r), c, y, h3, e, hy))
    case Bk.Term.Prj{+a}:
      match h:
        case Tuple{+nd, Tuple{_, h2}}:
          np.one(a, m, r, D.Fd(2n, m, r), c, y, hn,
            e => np.fs(Bk.Term.Prj{a}, dk, ds, m, im, fi, nx, ps, tbl, r, c, y, nd, {==}, e, hy),
            e => np.term(a, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(2n, m, r), c, y, h2, e, hy))
    case Bk.Term.Enu{+k}:
      match h:
        case Tuple{+nd, _}:
          D.bool.ft({D.Node(Bk.Term.Enu{k}, m, r, y) == True{} : Bool}, np.fs(Bk.Term.Enu{k}, dk, ds, m, im, fi, nx, ps, tbl, r, c, y, nd, {==}, hn, hy))
    case Bk.Term.Lab{+k}:
      match h:
        case Tuple{+nd, _}:
          D.bool.ft({D.Node(Bk.Term.Lab{k}, m, r, y) == True{} : Bool}, np.fs(Bk.Term.Lab{k}, dk, ds, m, im, fi, nx, ps, tbl, r, c, y, nd, {==}, hn, hy))
    case Bk.Term.Mat{+k, +a, +b}:
      match h:
        case Tuple{+nd, Tuple{_, Tuple{Tuple{_, h3}, Tuple{_, h4}}}}:
          np.two(a, b, m, r, D.Fd(3n, m, r), D.Fd(4n, m, r), c, y, hn,
            e => np.fs(Bk.Term.Mat{k, a, b}, dk, ds, m, im, fi, nx, ps, tbl, r, c, y, nd, {==}, e, hy),
            e => np.term(a, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(3n, m, r), c, y, h3, e, hy),
            e => np.term(b, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(4n, m, r), c, y, h4, e, hy))
    case Bk.Term.Efq{}:
      D.bool.ft({D.Node(Bk.Term.Efq{}, m, r, y) == True{} : Bool}, np.fs(Bk.Term.Efq{}, dk, ds, m, im, fi, nx, ps, tbl, r, c, y, h, {==}, hn, hy))
    case Bk.Term.Eql{+a, +b, +d}:
      match h:
        case Tuple{+nd, Tuple{Tuple{_, h2}, Tuple{Tuple{_, h3}, Tuple{_, h4}}}}:
          np.three(a, b, d, m, r, D.Fd(2n, m, r), D.Fd(3n, m, r), D.Fd(4n, m, r), c, y, hn,
            e => np.fs(Bk.Term.Eql{a, b, d}, dk, ds, m, im, fi, nx, ps, tbl, r, c, y, nd, {==}, e, hy),
            e => np.term(a, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(2n, m, r), c, y, h2, e, hy),
            e => np.term(b, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(3n, m, r), c, y, h3, e, hy),
            e => np.term(d, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(4n, m, r), c, y, h4, e, hy))
    case Bk.Term.Rfl{}:
      D.bool.ft({D.Node(Bk.Term.Rfl{}, m, r, y) == True{} : Bool}, np.fs(Bk.Term.Rfl{}, dk, ds, m, im, fi, nx, ps, tbl, r, c, y, h, {==}, hn, hy))
    case Bk.Term.Rwt{+a, +b, +d}:
      match h:
        case Tuple{+nd, Tuple{Tuple{_, h2}, Tuple{Tuple{_, h3}, Tuple{_, h4}}}}:
          np.three(a, b, d, m, r, D.Fd(2n, m, r), D.Fd(3n, m, r), D.Fd(4n, m, r), c, y, hn,
            e => np.fs(Bk.Term.Rwt{a, b, d}, dk, ds, m, im, fi, nx, ps, tbl, r, c, y, nd, {==}, e, hy),
            e => np.term(a, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(2n, m, r), c, y, h2, e, hy),
            e => np.term(b, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(3n, m, r), c, y, h3, e, hy),
            e => np.term(d, dk, ds, m, im, fi, nx, ks, img, ps, tbl, D.Fd(4n, m, r), c, y, h4, e, hy))

# a part of a node of a term of rs is a node of a term of rs
def np.nodes(rs: List<&2, D.Rt>, +dk: Bool, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +tbl: D.Tbl(m, im, fi, nx), +c: U32, +y: U32,
  ho: D.RtsK(dk, ds, m, im, fi, nx, ks, img, rs), hn: {D.Nodes(rs, m, c) == True{} : Bool},
  +hy: {D.Mem(D.Fs(m, ps, c), y) == True{} : Bool}) -> {D.Nodes(rs, m, y) == True{} : Bool}:
  match rs:
    case Nil{}:
      D.bool.ft({D.Nodes(Nil{}, m, y) == True{} : Bool}, hn)
    case Con{D.Rt{+r, +u}, +rest}:
      match ho:
        case Tuple{hu, hr}:
          D.or.cases(D.Node(u, m, r, c), D.Nodes(rest, m, c), {Bool.or(D.Node(u, m, r, y), D.Nodes(rest, m, y)) == True{} : Bool}, hn,
            e => D.or.l(D.Node(u, m, r, y), D.Nodes(rest, m, y), np.term(u, dk, ds, m, im, fi, nx, ks, img, ps, tbl, r, c, y, hu, e, hy)),
            e => D.or.r(D.Node(u, m, r, y), D.Nodes(rest, m, y), np.nodes(rest, dk, ds, m, im, fi, nx, ks, img, ps, tbl, c, y, hr, e, hy)))

# Stores to field 1
# -----------------
#
# M.inc, M.dec, M.release and the parts' decrements of M.alloc store to
# field 1 only (Put1). Every part of HSK but the counts and the links of the
# pend list and of the frames reads fields 0, 2, 3 and 4 only, so it holds
# after them (D.put1.at: each cell is the old one with another field 1).

# a part y of c, after stores to field 1: its old value with another field 1
def pt.p1(+dk: Bool, +t: Bk.Term, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +ws: List<&2, D.W1>, +c: U32, +y: U32,
  sp: D.Sp(fi, nx, c, Cr.Cir.Cells.get(m, y)),
  ih: D.IsCK(dk, ds, D.Put1(ws, m), im, fi, nx, ks, img, y, Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, y), D.Fd(1n, D.Put1(ws, m), y)), t)) ->
  D.P2(D.Sp(fi, nx, c, Cr.Cir.Cells.get(D.Put1(ws, m), y)), D.IsCK(dk, ds, D.Put1(ws, m), im, fi, nx, ks, img, y, Cr.Cir.Cells.get(D.Put1(ws, m), y), t)):
  +M2 = D.Put1(ws, m)
  +Y = Cr.Cir.Cells.get(m, y)
  +W = D.Fd(1n, M2, y)
  %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, y), Cr.Cir.Cell.set(1n, Y, W), D.put1.at(ws, m, y)) :
    D.P2(D.Sp(fi, nx, c, _), D.IsCK(dk, ds, M2, im, fi, nx, ks, img, y, _, t))
  (D.sp.at0(fi, nx, c, Cr.Cir.Cell.set(1n, Y, W), Y, D.cg0(Y, W), sp), ih)

# a cell after stores to field 1 stands for the same term: IsCK reads
# fields 0, 2, 3 and 4 only
def isck.p1(+dk: Bool, t: Bk.Term, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +ws: List<&2, D.W1>, +c: U32, x: Cr.Cir.Cell, +w: U32,
  h: D.IsCK(dk, ds, m, im, fi, nx, ks, img, c, x, t)) ->
  D.IsCK(dk, ds, D.Put1(ws, m), im, fi, nx, ks, img, c, Cr.Cir.Cell.set(1n, x, w), t):
  match t:
    case Bk.Term.Var{+i}:
      match x:
        case Cr.Cir.Cell{+a, b, +x2, +x3, +x4}:
          h
    case Bk.Term.Ref{+k}:
      match x:
        case Cr.Cir.Cell{+a, b, +x2, +x3, +x4}:
          h
    case Bk.Term.Ann{+t1, +t2}:
      match x:
        case Cr.Cir.Cell{+a, b, +x2, +x3, +x4}:
          match h:
            case Tuple{nd, Tuple{Tuple{sp2, h2}, Tuple{sp3, h3}}}:
              (nd, (pt.p1(dk, t1, ds, m, im, fi, nx, ks, img, ws, c, x2, sp2, isck.p1(dk, t1, ds, m, im, fi, nx, ks, img, ws, x2, Cr.Cir.Cells.get(m, x2), D.Fd(1n, D.Put1(ws, m), x2), h2)), pt.p1(dk, t2, ds, m, im, fi, nx, ks, img, ws, c, x3, sp3, isck.p1(dk, t2, ds, m, im, fi, nx, ks, img, ws, x3, Cr.Cir.Cells.get(m, x3), D.Fd(1n, D.Put1(ws, m), x3), h3))))
    case Bk.Term.Let{+q, +t1, +t2}:
      match x:
        case Cr.Cir.Cell{+a, b, +x2, +x3, +x4}:
          match h:
            case Tuple{nd, Tuple{hq, Tuple{Tuple{sp2, h2}, Tuple{sp3, h3}}}}:
              (nd, (hq, (pt.p1(dk, t1, ds, m, im, fi, nx, ks, img, ws, c, x2, sp2, isck.p1(dk, t1, ds, m, im, fi, nx, ks, img, ws, x2, Cr.Cir.Cells.get(m, x2), D.Fd(1n, D.Put1(ws, m), x2), h2)), pt.p1(dk, t2, ds, m, im, fi, nx, ks, img, ws, c, x3, sp3, isck.p1(dk, t2, ds, m, im, fi, nx, ks, img, ws, x3, Cr.Cir.Cells.get(m, x3), D.Fd(1n, D.Put1(ws, m), x3), h3)))))
    case Bk.Term.Typ{+t1}:
      match x:
        case Cr.Cir.Cell{+a, b, +x2, +x3, +x4}:
          match h:
            case Tuple{nd, Tuple{sp2, h2}}:
              (nd, pt.p1(dk, t1, ds, m, im, fi, nx, ks, img, ws, c, x2, sp2, isck.p1(dk, t1, ds, m, im, fi, nx, ks, img, ws, x2, Cr.Cir.Cells.get(m, x2), D.Fd(1n, D.Put1(ws, m), x2), h2)))
    case Bk.Term.Min{+t1, +t2}:
      match x:
        case Cr.Cir.Cell{+a, b, +x2, +x3, +x4}:
          match h:
            case Tuple{nd, Tuple{Tuple{sp2, h2}, Tuple{sp3, h3}}}:
              (nd, (pt.p1(dk, t1, ds, m, im, fi, nx, ks, img, ws, c, x2, sp2, isck.p1(dk, t1, ds, m, im, fi, nx, ks, img, ws, x2, Cr.Cir.Cells.get(m, x2), D.Fd(1n, D.Put1(ws, m), x2), h2)), pt.p1(dk, t2, ds, m, im, fi, nx, ks, img, ws, c, x3, sp3, isck.p1(dk, t2, ds, m, im, fi, nx, ks, img, ws, x3, Cr.Cir.Cells.get(m, x3), D.Fd(1n, D.Put1(ws, m), x3), h3))))
    case Bk.Term.All{+q, +t1, +t2}:
      match x:
        case Cr.Cir.Cell{+a, b, +x2, +x3, +x4}:
          match h:
            case Tuple{nd, Tuple{hq, Tuple{Tuple{sp2, h2}, Tuple{sp3, h3}}}}:
              (nd, (hq, (pt.p1(dk, t1, ds, m, im, fi, nx, ks, img, ws, c, x2, sp2, isck.p1(dk, t1, ds, m, im, fi, nx, ks, img, ws, x2, Cr.Cir.Cells.get(m, x2), D.Fd(1n, D.Put1(ws, m), x2), h2)), pt.p1(dk, t2, ds, m, im, fi, nx, ks, img, ws, c, x3, sp3, isck.p1(dk, t2, ds, m, im, fi, nx, ks, img, ws, x3, Cr.Cir.Cells.get(m, x3), D.Fd(1n, D.Put1(ws, m), x3), h3)))))
    case Bk.Term.Lam{+q, +t1}:
      match x:
        case Cr.Cir.Cell{+a, b, +x2, +x3, +x4}:
          match h:
            case Tuple{nd, Tuple{hq, Tuple{sp2, h2}}}:
              (nd, (hq, pt.p1(dk, t1, ds, m, im, fi, nx, ks, img, ws, c, x2, sp2, isck.p1(dk, t1, ds, m, im, fi, nx, ks, img, ws, x2, Cr.Cir.Cells.get(m, x2), D.Fd(1n, D.Put1(ws, m), x2), h2))))
    case Bk.Term.App{+q, +t1, +t2}:
      match x:
        case Cr.Cir.Cell{+a, b, +x2, +x3, +x4}:
          match h:
            case Tuple{nd, Tuple{hq, Tuple{Tuple{sp2, h2}, Tuple{sp3, h3}}}}:
              (nd, (hq, (pt.p1(dk, t1, ds, m, im, fi, nx, ks, img, ws, c, x2, sp2, isck.p1(dk, t1, ds, m, im, fi, nx, ks, img, ws, x2, Cr.Cir.Cells.get(m, x2), D.Fd(1n, D.Put1(ws, m), x2), h2)), pt.p1(dk, t2, ds, m, im, fi, nx, ks, img, ws, c, x3, sp3, isck.p1(dk, t2, ds, m, im, fi, nx, ks, img, ws, x3, Cr.Cir.Cells.get(m, x3), D.Fd(1n, D.Put1(ws, m), x3), h3)))))
    case Bk.Term.Sig{+q, +t1, +t2}:
      match x:
        case Cr.Cir.Cell{+a, b, +x2, +x3, +x4}:
          match h:
            case Tuple{nd, Tuple{hq, Tuple{Tuple{sp2, h2}, Tuple{sp3, h3}}}}:
              (nd, (hq, (pt.p1(dk, t1, ds, m, im, fi, nx, ks, img, ws, c, x2, sp2, isck.p1(dk, t1, ds, m, im, fi, nx, ks, img, ws, x2, Cr.Cir.Cells.get(m, x2), D.Fd(1n, D.Put1(ws, m), x2), h2)), pt.p1(dk, t2, ds, m, im, fi, nx, ks, img, ws, c, x3, sp3, isck.p1(dk, t2, ds, m, im, fi, nx, ks, img, ws, x3, Cr.Cir.Cells.get(m, x3), D.Fd(1n, D.Put1(ws, m), x3), h3)))))
    case Bk.Term.Tup{+q, +t1, +t2}:
      match x:
        case Cr.Cir.Cell{+a, b, +x2, +x3, +x4}:
          match h:
            case Tuple{nd, Tuple{hq, Tuple{Tuple{sp2, h2}, Tuple{sp3, h3}}}}:
              (nd, (hq, (pt.p1(dk, t1, ds, m, im, fi, nx, ks, img, ws, c, x2, sp2, isck.p1(dk, t1, ds, m, im, fi, nx, ks, img, ws, x2, Cr.Cir.Cells.get(m, x2), D.Fd(1n, D.Put1(ws, m), x2), h2)), pt.p1(dk, t2, ds, m, im, fi, nx, ks, img, ws, c, x3, sp3, isck.p1(dk, t2, ds, m, im, fi, nx, ks, img, ws, x3, Cr.Cir.Cells.get(m, x3), D.Fd(1n, D.Put1(ws, m), x3), h3)))))
    case Bk.Term.Prj{+t1}:
      match x:
        case Cr.Cir.Cell{+a, b, +x2, +x3, +x4}:
          match h:
            case Tuple{nd, Tuple{sp2, h2}}:
              (nd, pt.p1(dk, t1, ds, m, im, fi, nx, ks, img, ws, c, x2, sp2, isck.p1(dk, t1, ds, m, im, fi, nx, ks, img, ws, x2, Cr.Cir.Cells.get(m, x2), D.Fd(1n, D.Put1(ws, m), x2), h2)))
    case Bk.Term.Enu{+k}:
      match x:
        case Cr.Cir.Cell{+a, b, +x2, +x3, +x4}:
          h
    case Bk.Term.Lab{+k}:
      match x:
        case Cr.Cir.Cell{+a, b, +x2, +x3, +x4}:
          h
    case Bk.Term.Mat{+k, +t1, +t2}:
      match x:
        case Cr.Cir.Cell{+a, b, +x2, +x3, +x4}:
          match h:
            case Tuple{nd, Tuple{hn, Tuple{Tuple{sp3, h3}, Tuple{sp4, h4}}}}:
              (nd, (hn, (pt.p1(dk, t1, ds, m, im, fi, nx, ks, img, ws, c, x3, sp3, isck.p1(dk, t1, ds, m, im, fi, nx, ks, img, ws, x3, Cr.Cir.Cells.get(m, x3), D.Fd(1n, D.Put1(ws, m), x3), h3)), pt.p1(dk, t2, ds, m, im, fi, nx, ks, img, ws, c, x4, sp4, isck.p1(dk, t2, ds, m, im, fi, nx, ks, img, ws, x4, Cr.Cir.Cells.get(m, x4), D.Fd(1n, D.Put1(ws, m), x4), h4)))))
    case Bk.Term.Efq{}:
      match x:
        case Cr.Cir.Cell{+a, b, +x2, +x3, +x4}:
          h
    case Bk.Term.Eql{+t1, +t2, +t3}:
      match x:
        case Cr.Cir.Cell{+a, b, +x2, +x3, +x4}:
          match h:
            case Tuple{nd, Tuple{Tuple{sp2, h2}, Tuple{Tuple{sp3, h3}, Tuple{sp4, h4}}}}:
              (nd, (pt.p1(dk, t1, ds, m, im, fi, nx, ks, img, ws, c, x2, sp2, isck.p1(dk, t1, ds, m, im, fi, nx, ks, img, ws, x2, Cr.Cir.Cells.get(m, x2), D.Fd(1n, D.Put1(ws, m), x2), h2)), (pt.p1(dk, t2, ds, m, im, fi, nx, ks, img, ws, c, x3, sp3, isck.p1(dk, t2, ds, m, im, fi, nx, ks, img, ws, x3, Cr.Cir.Cells.get(m, x3), D.Fd(1n, D.Put1(ws, m), x3), h3)), pt.p1(dk, t3, ds, m, im, fi, nx, ks, img, ws, c, x4, sp4, isck.p1(dk, t3, ds, m, im, fi, nx, ks, img, ws, x4, Cr.Cir.Cells.get(m, x4), D.Fd(1n, D.Put1(ws, m), x4), h4)))))
    case Bk.Term.Rfl{}:
      match x:
        case Cr.Cir.Cell{+a, b, +x2, +x3, +x4}:
          h
    case Bk.Term.Rwt{+t1, +t2, +t3}:
      match x:
        case Cr.Cir.Cell{+a, b, +x2, +x3, +x4}:
          match h:
            case Tuple{nd, Tuple{Tuple{sp2, h2}, Tuple{Tuple{sp3, h3}, Tuple{sp4, h4}}}}:
              (nd, (pt.p1(dk, t1, ds, m, im, fi, nx, ks, img, ws, c, x2, sp2, isck.p1(dk, t1, ds, m, im, fi, nx, ks, img, ws, x2, Cr.Cir.Cells.get(m, x2), D.Fd(1n, D.Put1(ws, m), x2), h2)), (pt.p1(dk, t2, ds, m, im, fi, nx, ks, img, ws, c, x3, sp3, isck.p1(dk, t2, ds, m, im, fi, nx, ks, img, ws, x3, Cr.Cir.Cells.get(m, x3), D.Fd(1n, D.Put1(ws, m), x3), h3)), pt.p1(dk, t3, ds, m, im, fi, nx, ks, img, ws, c, x4, sp4, isck.p1(dk, t3, ds, m, im, fi, nx, ks, img, ws, x4, Cr.Cir.Cells.get(m, x4), D.Fd(1n, D.Put1(ws, m), x4), h4)))))


# a cell stands for its term after stores to field 1
def isk.p1(+dk: Bool, +t: Bk.Term, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +ws: List<&2, D.W1>, +c: U32,
  h: D.IsK(dk, ds, m, im, fi, nx, ks, img, c, t)) -> D.IsK(dk, ds, D.Put1(ws, m), im, fi, nx, ks, img, c, t):
  +M2 = D.Put1(ws, m)
  %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, c), Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, c), D.Fd(1n, M2, c)), D.put1.at(ws, m, c)) :
    D.IsCK(dk, ds, M2, im, fi, nx, ks, img, c, _, t)
  isck.p1(dk, t, ds, m, im, fi, nx, ks, img, ws, c, Cr.Cir.Cells.get(m, c), D.Fd(1n, M2, c), h)

def rtsk.p1(+dk: Bool, rs: List<&2, D.Rt>, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +ws: List<&2, D.W1>,
  h: D.RtsK(dk, ds, m, im, fi, nx, ks, img, rs)) -> D.RtsK(dk, ds, D.Put1(ws, m), im, fi, nx, ks, img, rs):
  match rs:
    case Nil{}:
      Unit{}
    case Con{D.Rt{+c, +u}, +rest}:
      match h:
        case Tuple{hu, hr}:
          (isk.p1(dk, u, ds, m, im, fi, nx, ks, img, ws, c, hu), rtsk.p1(dk, rest, ds, m, im, fi, nx, ks, img, ws, hr))

# stores to field 1 keep the nodes of a term: Node reads fields 2 to 4 only
def node.p1(t: Bk.Term, +ws: List<&2, D.W1>, +m: Cr.Cir.Cells, +r: U32, +c: U32) ->
  {D.Node(t, D.Put1(ws, m), r, c) == D.Node(t, m, r, c) : Bool}:
  match t:
    case Bk.Term.Var{+i}:
      {==}
    case Bk.Term.Ref{+k}:
      {==}
    case Bk.Term.Ann{+t1, +t2}:
      +M2 = D.Put1(ws, m)
      %Equal.sym(U32, D.Fd(2n, M2, r), D.Fd(2n, m, r), D.put1.f2(ws, m, r)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, M2, _, c), D.Node(t2, M2, D.Fd(3n, M2, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c))) : Bool}
      %Equal.sym(U32, D.Fd(3n, M2, r), D.Fd(3n, m, r), D.put1.f3(ws, m, r)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, M2, D.Fd(2n, m, r), c), D.Node(t2, M2, _, c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c))) : Bool}
      %Equal.sym(Bool, D.Node(t1, M2, D.Fd(2n, m, r), c), D.Node(t1, m, D.Fd(2n, m, r), c), node.p1(t1, ws, m, D.Fd(2n, m, r), c)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(_, D.Node(t2, M2, D.Fd(3n, m, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c))) : Bool}
      %Equal.sym(Bool, D.Node(t2, M2, D.Fd(3n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c), node.p1(t2, ws, m, D.Fd(3n, m, r), c)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), _)) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c))) : Bool}
      {==}
    case Bk.Term.Let{+q, +t1, +t2}:
      +M2 = D.Put1(ws, m)
      %Equal.sym(U32, D.Fd(2n, M2, r), D.Fd(2n, m, r), D.put1.f2(ws, m, r)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, M2, _, c), D.Node(t2, M2, D.Fd(3n, M2, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c))) : Bool}
      %Equal.sym(U32, D.Fd(3n, M2, r), D.Fd(3n, m, r), D.put1.f3(ws, m, r)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, M2, D.Fd(2n, m, r), c), D.Node(t2, M2, _, c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c))) : Bool}
      %Equal.sym(Bool, D.Node(t1, M2, D.Fd(2n, m, r), c), D.Node(t1, m, D.Fd(2n, m, r), c), node.p1(t1, ws, m, D.Fd(2n, m, r), c)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(_, D.Node(t2, M2, D.Fd(3n, m, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c))) : Bool}
      %Equal.sym(Bool, D.Node(t2, M2, D.Fd(3n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c), node.p1(t2, ws, m, D.Fd(3n, m, r), c)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), _)) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c))) : Bool}
      {==}
    case Bk.Term.Typ{+t1}:
      +M2 = D.Put1(ws, m)
      %Equal.sym(U32, D.Fd(2n, M2, r), D.Fd(2n, m, r), D.put1.f2(ws, m, r)) :
        {Bool.or(U32.is_eq(r, c), D.Node(t1, M2, _, c)) == Bool.or(U32.is_eq(r, c), D.Node(t1, m, D.Fd(2n, m, r), c)) : Bool}
      %Equal.sym(Bool, D.Node(t1, M2, D.Fd(2n, m, r), c), D.Node(t1, m, D.Fd(2n, m, r), c), node.p1(t1, ws, m, D.Fd(2n, m, r), c)) :
        {Bool.or(U32.is_eq(r, c), _) == Bool.or(U32.is_eq(r, c), D.Node(t1, m, D.Fd(2n, m, r), c)) : Bool}
      {==}
    case Bk.Term.Min{+t1, +t2}:
      +M2 = D.Put1(ws, m)
      %Equal.sym(U32, D.Fd(2n, M2, r), D.Fd(2n, m, r), D.put1.f2(ws, m, r)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, M2, _, c), D.Node(t2, M2, D.Fd(3n, M2, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c))) : Bool}
      %Equal.sym(U32, D.Fd(3n, M2, r), D.Fd(3n, m, r), D.put1.f3(ws, m, r)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, M2, D.Fd(2n, m, r), c), D.Node(t2, M2, _, c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c))) : Bool}
      %Equal.sym(Bool, D.Node(t1, M2, D.Fd(2n, m, r), c), D.Node(t1, m, D.Fd(2n, m, r), c), node.p1(t1, ws, m, D.Fd(2n, m, r), c)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(_, D.Node(t2, M2, D.Fd(3n, m, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c))) : Bool}
      %Equal.sym(Bool, D.Node(t2, M2, D.Fd(3n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c), node.p1(t2, ws, m, D.Fd(3n, m, r), c)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), _)) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c))) : Bool}
      {==}
    case Bk.Term.All{+q, +t1, +t2}:
      +M2 = D.Put1(ws, m)
      %Equal.sym(U32, D.Fd(2n, M2, r), D.Fd(2n, m, r), D.put1.f2(ws, m, r)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, M2, _, c), D.Node(t2, M2, D.Fd(3n, M2, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c))) : Bool}
      %Equal.sym(U32, D.Fd(3n, M2, r), D.Fd(3n, m, r), D.put1.f3(ws, m, r)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, M2, D.Fd(2n, m, r), c), D.Node(t2, M2, _, c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c))) : Bool}
      %Equal.sym(Bool, D.Node(t1, M2, D.Fd(2n, m, r), c), D.Node(t1, m, D.Fd(2n, m, r), c), node.p1(t1, ws, m, D.Fd(2n, m, r), c)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(_, D.Node(t2, M2, D.Fd(3n, m, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c))) : Bool}
      %Equal.sym(Bool, D.Node(t2, M2, D.Fd(3n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c), node.p1(t2, ws, m, D.Fd(3n, m, r), c)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), _)) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c))) : Bool}
      {==}
    case Bk.Term.Lam{+q, +t1}:
      +M2 = D.Put1(ws, m)
      %Equal.sym(U32, D.Fd(2n, M2, r), D.Fd(2n, m, r), D.put1.f2(ws, m, r)) :
        {Bool.or(U32.is_eq(r, c), D.Node(t1, M2, _, c)) == Bool.or(U32.is_eq(r, c), D.Node(t1, m, D.Fd(2n, m, r), c)) : Bool}
      %Equal.sym(Bool, D.Node(t1, M2, D.Fd(2n, m, r), c), D.Node(t1, m, D.Fd(2n, m, r), c), node.p1(t1, ws, m, D.Fd(2n, m, r), c)) :
        {Bool.or(U32.is_eq(r, c), _) == Bool.or(U32.is_eq(r, c), D.Node(t1, m, D.Fd(2n, m, r), c)) : Bool}
      {==}
    case Bk.Term.App{+q, +t1, +t2}:
      +M2 = D.Put1(ws, m)
      %Equal.sym(U32, D.Fd(2n, M2, r), D.Fd(2n, m, r), D.put1.f2(ws, m, r)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, M2, _, c), D.Node(t2, M2, D.Fd(3n, M2, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c))) : Bool}
      %Equal.sym(U32, D.Fd(3n, M2, r), D.Fd(3n, m, r), D.put1.f3(ws, m, r)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, M2, D.Fd(2n, m, r), c), D.Node(t2, M2, _, c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c))) : Bool}
      %Equal.sym(Bool, D.Node(t1, M2, D.Fd(2n, m, r), c), D.Node(t1, m, D.Fd(2n, m, r), c), node.p1(t1, ws, m, D.Fd(2n, m, r), c)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(_, D.Node(t2, M2, D.Fd(3n, m, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c))) : Bool}
      %Equal.sym(Bool, D.Node(t2, M2, D.Fd(3n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c), node.p1(t2, ws, m, D.Fd(3n, m, r), c)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), _)) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c))) : Bool}
      {==}
    case Bk.Term.Sig{+q, +t1, +t2}:
      +M2 = D.Put1(ws, m)
      %Equal.sym(U32, D.Fd(2n, M2, r), D.Fd(2n, m, r), D.put1.f2(ws, m, r)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, M2, _, c), D.Node(t2, M2, D.Fd(3n, M2, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c))) : Bool}
      %Equal.sym(U32, D.Fd(3n, M2, r), D.Fd(3n, m, r), D.put1.f3(ws, m, r)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, M2, D.Fd(2n, m, r), c), D.Node(t2, M2, _, c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c))) : Bool}
      %Equal.sym(Bool, D.Node(t1, M2, D.Fd(2n, m, r), c), D.Node(t1, m, D.Fd(2n, m, r), c), node.p1(t1, ws, m, D.Fd(2n, m, r), c)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(_, D.Node(t2, M2, D.Fd(3n, m, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c))) : Bool}
      %Equal.sym(Bool, D.Node(t2, M2, D.Fd(3n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c), node.p1(t2, ws, m, D.Fd(3n, m, r), c)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), _)) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c))) : Bool}
      {==}
    case Bk.Term.Tup{+q, +t1, +t2}:
      +M2 = D.Put1(ws, m)
      %Equal.sym(U32, D.Fd(2n, M2, r), D.Fd(2n, m, r), D.put1.f2(ws, m, r)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, M2, _, c), D.Node(t2, M2, D.Fd(3n, M2, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c))) : Bool}
      %Equal.sym(U32, D.Fd(3n, M2, r), D.Fd(3n, m, r), D.put1.f3(ws, m, r)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, M2, D.Fd(2n, m, r), c), D.Node(t2, M2, _, c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c))) : Bool}
      %Equal.sym(Bool, D.Node(t1, M2, D.Fd(2n, m, r), c), D.Node(t1, m, D.Fd(2n, m, r), c), node.p1(t1, ws, m, D.Fd(2n, m, r), c)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(_, D.Node(t2, M2, D.Fd(3n, m, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c))) : Bool}
      %Equal.sym(Bool, D.Node(t2, M2, D.Fd(3n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c), node.p1(t2, ws, m, D.Fd(3n, m, r), c)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), _)) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c))) : Bool}
      {==}
    case Bk.Term.Prj{+t1}:
      +M2 = D.Put1(ws, m)
      %Equal.sym(U32, D.Fd(2n, M2, r), D.Fd(2n, m, r), D.put1.f2(ws, m, r)) :
        {Bool.or(U32.is_eq(r, c), D.Node(t1, M2, _, c)) == Bool.or(U32.is_eq(r, c), D.Node(t1, m, D.Fd(2n, m, r), c)) : Bool}
      %Equal.sym(Bool, D.Node(t1, M2, D.Fd(2n, m, r), c), D.Node(t1, m, D.Fd(2n, m, r), c), node.p1(t1, ws, m, D.Fd(2n, m, r), c)) :
        {Bool.or(U32.is_eq(r, c), _) == Bool.or(U32.is_eq(r, c), D.Node(t1, m, D.Fd(2n, m, r), c)) : Bool}
      {==}
    case Bk.Term.Enu{+k}:
      {==}
    case Bk.Term.Lab{+k}:
      {==}
    case Bk.Term.Mat{+k, +t1, +t2}:
      +M2 = D.Put1(ws, m)
      %Equal.sym(U32, D.Fd(3n, M2, r), D.Fd(3n, m, r), D.put1.f3(ws, m, r)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, M2, _, c), D.Node(t2, M2, D.Fd(4n, M2, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(3n, m, r), c), D.Node(t2, m, D.Fd(4n, m, r), c))) : Bool}
      %Equal.sym(U32, D.Fd(4n, M2, r), D.Fd(4n, m, r), D.put1.f4(ws, m, r)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, M2, D.Fd(3n, m, r), c), D.Node(t2, M2, _, c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(3n, m, r), c), D.Node(t2, m, D.Fd(4n, m, r), c))) : Bool}
      %Equal.sym(Bool, D.Node(t1, M2, D.Fd(3n, m, r), c), D.Node(t1, m, D.Fd(3n, m, r), c), node.p1(t1, ws, m, D.Fd(3n, m, r), c)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(_, D.Node(t2, M2, D.Fd(4n, m, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(3n, m, r), c), D.Node(t2, m, D.Fd(4n, m, r), c))) : Bool}
      %Equal.sym(Bool, D.Node(t2, M2, D.Fd(4n, m, r), c), D.Node(t2, m, D.Fd(4n, m, r), c), node.p1(t2, ws, m, D.Fd(4n, m, r), c)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(3n, m, r), c), _)) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(3n, m, r), c), D.Node(t2, m, D.Fd(4n, m, r), c))) : Bool}
      {==}
    case Bk.Term.Efq{}:
      {==}
    case Bk.Term.Eql{+t1, +t2, +t3}:
      +M2 = D.Put1(ws, m)
      %Equal.sym(U32, D.Fd(2n, M2, r), D.Fd(2n, m, r), D.put1.f2(ws, m, r)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, M2, _, c), Bool.or(D.Node(t2, M2, D.Fd(3n, M2, r), c), D.Node(t3, M2, D.Fd(4n, M2, r), c)))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), Bool.or(D.Node(t2, m, D.Fd(3n, m, r), c), D.Node(t3, m, D.Fd(4n, m, r), c)))) : Bool}
      %Equal.sym(U32, D.Fd(3n, M2, r), D.Fd(3n, m, r), D.put1.f3(ws, m, r)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, M2, D.Fd(2n, m, r), c), Bool.or(D.Node(t2, M2, _, c), D.Node(t3, M2, D.Fd(4n, M2, r), c)))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), Bool.or(D.Node(t2, m, D.Fd(3n, m, r), c), D.Node(t3, m, D.Fd(4n, m, r), c)))) : Bool}
      %Equal.sym(U32, D.Fd(4n, M2, r), D.Fd(4n, m, r), D.put1.f4(ws, m, r)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, M2, D.Fd(2n, m, r), c), Bool.or(D.Node(t2, M2, D.Fd(3n, m, r), c), D.Node(t3, M2, _, c)))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), Bool.or(D.Node(t2, m, D.Fd(3n, m, r), c), D.Node(t3, m, D.Fd(4n, m, r), c)))) : Bool}
      %Equal.sym(Bool, D.Node(t1, M2, D.Fd(2n, m, r), c), D.Node(t1, m, D.Fd(2n, m, r), c), node.p1(t1, ws, m, D.Fd(2n, m, r), c)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(_, Bool.or(D.Node(t2, M2, D.Fd(3n, m, r), c), D.Node(t3, M2, D.Fd(4n, m, r), c)))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), Bool.or(D.Node(t2, m, D.Fd(3n, m, r), c), D.Node(t3, m, D.Fd(4n, m, r), c)))) : Bool}
      %Equal.sym(Bool, D.Node(t2, M2, D.Fd(3n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c), node.p1(t2, ws, m, D.Fd(3n, m, r), c)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), Bool.or(_, D.Node(t3, M2, D.Fd(4n, m, r), c)))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), Bool.or(D.Node(t2, m, D.Fd(3n, m, r), c), D.Node(t3, m, D.Fd(4n, m, r), c)))) : Bool}
      %Equal.sym(Bool, D.Node(t3, M2, D.Fd(4n, m, r), c), D.Node(t3, m, D.Fd(4n, m, r), c), node.p1(t3, ws, m, D.Fd(4n, m, r), c)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), Bool.or(D.Node(t2, m, D.Fd(3n, m, r), c), _))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), Bool.or(D.Node(t2, m, D.Fd(3n, m, r), c), D.Node(t3, m, D.Fd(4n, m, r), c)))) : Bool}
      {==}
    case Bk.Term.Rfl{}:
      {==}
    case Bk.Term.Rwt{+t1, +t2, +t3}:
      +M2 = D.Put1(ws, m)
      %Equal.sym(U32, D.Fd(2n, M2, r), D.Fd(2n, m, r), D.put1.f2(ws, m, r)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, M2, _, c), Bool.or(D.Node(t2, M2, D.Fd(3n, M2, r), c), D.Node(t3, M2, D.Fd(4n, M2, r), c)))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), Bool.or(D.Node(t2, m, D.Fd(3n, m, r), c), D.Node(t3, m, D.Fd(4n, m, r), c)))) : Bool}
      %Equal.sym(U32, D.Fd(3n, M2, r), D.Fd(3n, m, r), D.put1.f3(ws, m, r)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, M2, D.Fd(2n, m, r), c), Bool.or(D.Node(t2, M2, _, c), D.Node(t3, M2, D.Fd(4n, M2, r), c)))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), Bool.or(D.Node(t2, m, D.Fd(3n, m, r), c), D.Node(t3, m, D.Fd(4n, m, r), c)))) : Bool}
      %Equal.sym(U32, D.Fd(4n, M2, r), D.Fd(4n, m, r), D.put1.f4(ws, m, r)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, M2, D.Fd(2n, m, r), c), Bool.or(D.Node(t2, M2, D.Fd(3n, m, r), c), D.Node(t3, M2, _, c)))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), Bool.or(D.Node(t2, m, D.Fd(3n, m, r), c), D.Node(t3, m, D.Fd(4n, m, r), c)))) : Bool}
      %Equal.sym(Bool, D.Node(t1, M2, D.Fd(2n, m, r), c), D.Node(t1, m, D.Fd(2n, m, r), c), node.p1(t1, ws, m, D.Fd(2n, m, r), c)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(_, Bool.or(D.Node(t2, M2, D.Fd(3n, m, r), c), D.Node(t3, M2, D.Fd(4n, m, r), c)))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), Bool.or(D.Node(t2, m, D.Fd(3n, m, r), c), D.Node(t3, m, D.Fd(4n, m, r), c)))) : Bool}
      %Equal.sym(Bool, D.Node(t2, M2, D.Fd(3n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c), node.p1(t2, ws, m, D.Fd(3n, m, r), c)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), Bool.or(_, D.Node(t3, M2, D.Fd(4n, m, r), c)))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), Bool.or(D.Node(t2, m, D.Fd(3n, m, r), c), D.Node(t3, m, D.Fd(4n, m, r), c)))) : Bool}
      %Equal.sym(Bool, D.Node(t3, M2, D.Fd(4n, m, r), c), D.Node(t3, m, D.Fd(4n, m, r), c), node.p1(t3, ws, m, D.Fd(4n, m, r), c)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), Bool.or(D.Node(t2, m, D.Fd(3n, m, r), c), _))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), Bool.or(D.Node(t2, m, D.Fd(3n, m, r), c), D.Node(t3, m, D.Fd(4n, m, r), c)))) : Bool}
      {==}


def nodes.p1(rs: List<&2, D.Rt>, +ws: List<&2, D.W1>, +m: Cr.Cir.Cells, +c: U32) ->
  {D.Nodes(rs, D.Put1(ws, m), c) == D.Nodes(rs, m, c) : Bool}:
  match rs:
    case Nil{}:
      {==}
    case Con{D.Rt{+r, +u}, +rest}:
      +M2 = D.Put1(ws, m)
      %Equal.sym(Bool, D.Node(u, M2, r, c), D.Node(u, m, r, c), node.p1(u, ws, m, r, c)) :
        {Bool.or(_, D.Nodes(rest, M2, c)) == Bool.or(D.Node(u, m, r, c), D.Nodes(rest, m, c)) : Bool}
      %Equal.sym(Bool, D.Nodes(rest, M2, c), D.Nodes(rest, m, c), nodes.p1(rest, ws, m, c)) :
        {Bool.or(D.Node(u, m, r, c), _) == Bool.or(D.Node(u, m, r, c), D.Nodes(rest, m, c)) : Bool}
      {==}

def held.p1(bs: List<&2, D.Rt>, +os: List<&2, D.Rt>, +ws: List<&2, D.W1>, +m: Cr.Cir.Cells, h: D.Held(m, os, bs)) ->
  D.Held(D.Put1(ws, m), os, bs):
  match bs:
    case Nil{}:
      Unit{}
    case Con{D.Rt{+c, _}, +rest}:
      match h:
        case Tuple{hc, hr}:
          +M2 = D.Put1(ws, m)
          ((%Equal.sym(U32, D.Fd(0n, M2, c), D.Fd(0n, m, c), D.put1.f0(ws, m, c)) :
              {Bool.or(U32.is_ne(U32.and(_, 1024), 0), D.Nodes(os, M2, c)) == True{} : Bool};
            (%Equal.sym(Bool, D.Nodes(os, M2, c), D.Nodes(os, m, c), nodes.p1(os, ws, m, c)) :
                {Bool.or(D.Fl(m, c, 1024), _) == True{} : Bool};
              hc)),
            held.p1(rest, os, ws, m, hr))

# a or b gives a or (x or b)
def or.mid(a: Bool, x: Bool, -b: Bool, h: {Bool.or(a, b) == True{} : Bool}) -> {Bool.or(a, Bool.or(x, b)) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      D.or.r(x, b, h)

# one more root keeps Held
def held.cons(bs: List<&2, D.Rt>, +os: List<&2, D.Rt>, +r: U32, +u: Bk.Term, +m: Cr.Cir.Cells, h: D.Held(m, os, bs)) ->
  D.Held(m, Con{D.Rt{r, u}, os}, bs):
  match bs:
    case Nil{}:
      Unit{}
    case Con{D.Rt{+c, _}, +rest}:
      match h:
        case Tuple{hc, hr}:
          (or.mid(D.Fl(m, c, 1024), D.Node(u, m, r, c), D.Nodes(os, m, c), hc), held.cons(rest, os, r, u, m, hr))

# no cell of ws has a frame's tag (32 to 40)
def W1.nf(ws: List<&2, D.W1>, +m: Cr.Cir.Cells) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case Con{D.W1{+q, _}, rest}:
      Bool.and(Bool.not(Bool.and(U32.is_le(32, D.Tg(m, q)), U32.is_le(D.Tg(m, q), 40))), W1.nf(rest, m))

# a cell q that is no frame's is not the frame fr
def ne.frame(b: Bool, +m: Cr.Cir.Cells, +q: U32, +fr: U32, +kind: D.FK, eb: {U32.is_eq(q, fr) == b : Bool},
  etg: {D.Tg(m, fr) == D.FK.tag(kind) : U32},
  hq: {Bool.not(Bool.and(U32.is_le(32, D.Tg(m, q)), U32.is_le(D.Tg(m, q), 40))) == True{} : Bool}) ->
  {U32.is_eq(q, fr) == False{} : Bool}:
  match b:
    case False{}:
      eb
    case True{}:
      D.bool.ft({U32.is_eq(q, fr) == False{} : Bool},
        (%D.fk.le(kind) : {Bool.not(Bool.and(True{}, _)) == True{} : Bool};
          (%D.fk.ge(kind) : {Bool.not(Bool.and(_, U32.is_le(D.FK.tag(kind), 40))) == True{} : Bool};
            (%etg : {Bool.not(Bool.and(U32.is_le(32, _), U32.is_le(_, 40))) == True{} : Bool};
              (%D.u32.eq(q, fr, eb) : {Bool.not(Bool.and(U32.is_le(32, D.Tg(m, _)), U32.is_le(D.Tg(m, _), 40))) == True{} : Bool};
                hq)))))

# a frame is no cell of ws
def nf.out(ws: List<&2, D.W1>, +m: Cr.Cir.Cells, +fr: U32, +kind: D.FK, +etg: {D.Tg(m, fr) == D.FK.tag(kind) : U32},
  hw: {W1.nf(ws, m) == True{} : Bool}) -> {D.Mem(D.W1.cells(ws), fr) == False{} : Bool}:
  match ws:
    case Nil{}:
      {==}
    case Con{D.W1{+q, _}, +rest}:
      +hw2 = hw
      +nfq = Bool.not(Bool.and(U32.is_le(32, D.Tg(m, q)), U32.is_le(D.Tg(m, q), 40)))
      +ne = ne.frame(U32.is_eq(q, fr), m, q, fr, kind, {==}, etg, D.and.l(nfq, W1.nf(rest, m), hw2))
      %Equal.sym(Bool, U32.is_eq(q, fr), False{}, ne) : {Bool.or(_, D.Mem(D.W1.cells(rest), fr)) == False{} : Bool}
      nf.out(rest, m, fr, kind, etg, D.and.r(nfq, W1.nf(rest, m), hw2))

# a frame's part b, after stores to field 1
def frsb.p1(+dk: Bool, kind: D.FK, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +ws: List<&2, D.W1>, +c: U32, +b: Bk.Term,
  h: D.Frs.bK(dk, ds, m, im, fi, nx, ks, img, c, kind, b)) -> D.Frs.bK(dk, ds, D.Put1(ws, m), im, fi, nx, ks, img, c, kind, b):
  match kind:
    case D.FK.rwt{}:
      isk.p1(dk, b, ds, m, im, fi, nx, ks, img, ws, c, h)
    case D.FK.arg{}:
      Unit{}
    case D.FK.val{}:
      Unit{}
    case D.FK.fun{}:
      Unit{}
    case D.FK.let{}:
      Unit{}
    case D.FK.tupb{}:
      Unit{}
    case D.FK.tupa{}:
      Unit{}
    case D.FK.minb{}:
      Unit{}
    case D.FK.mina{}:
      Unit{}

# stores to field 1 of cells that are no frames keep the frames
def frsk.p1(+dk: Bool, fs: List<&2, D.AF>, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +ws: List<&2, D.W1>, +fr: U32,
  +hw: {W1.nf(ws, m) == True{} : Bool},
  h: D.FrsK(dk, ds, m, im, fi, nx, ks, img, ps, fr, fs)) -> D.FrsK(dk, ds, D.Put1(ws, m), im, fi, nx, ks, img, ps, fr, fs):
  match fs:
    case Nil{}:
      h
    case Con{D.AF{+kind, +q, +k, +a, +b}, +rest}:
      match h:
        case Tuple{e0, Tuple{ev, Tuple{eo, Tuple{es, Tuple{em, Tuple{+etg, Tuple{eq, Tuple{ek, Tuple{ia, Tuple{ib, ir}}}}}}}}}}:
          +M2 = D.Put1(ws, m)
          D.frs.uck(dk, ds, M2, im, fi, nx, ks, img, ps, fr, Con{D.AF{kind, q, k, a, b}, rest},
            D.frsc.atk(dk, ds, M2, im, fi, nx, ks, img, ps, fr, Cr.Cir.Cells.get(M2, fr), Cr.Cir.Cells.get(m, fr), Con{D.AF{kind, q, k, a, b}, rest},
              D.put1.out(ws, m, fr, nf.out(ws, m, fr, kind, etg, hw)),
              (e0, (ev, (eo, (es, (em, (etg, (eq, (ek,
                (isk.p1(dk, a, ds, m, im, fi, nx, ks, img, ws, D.Fd(2n, m, fr), ia),
                (frsb.p1(dk, kind, ds, m, im, fi, nx, ks, img, ws, D.Fd(3n, m, fr), b, ib),
                  frsk.p1(dk, rest, ds, m, im, fi, nx, ks, img, ps, ws, D.Fd(1n, m, fr), hw, ir)))))))))))))

# the table, after stores to field 1
def tbl.p1(rs: List<&2, D.Row>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ws: List<&2, D.W1>, +at: U32,
  h: D.Tbl.go(rs, m, im, fi, nx, at)) -> D.Tbl.go(rs, D.Put1(ws, m), im, fi, nx, at):
  match rs:
    case Nil{}:
      Unit{}
    case Con{D.Row{+a, +b, +c}, +rest}:
      match h:
        case Tuple{ec, Tuple{e2, Tuple{e3, Tuple{e4, r4}}}}:
          +M2 = D.Put1(ws, m)
          (ec, (Equal.trans(U32, D.Fd(2n, M2, at), D.Fd(2n, m, at), a, D.put1.f2(ws, m, at), e2),
            (Equal.trans(U32, D.Fd(3n, M2, at), D.Fd(3n, m, at), b, D.put1.f3(ws, m, at), e3),
            (Equal.trans(U32, D.Fd(4n, M2, at), D.Fd(4n, m, at), c, D.put1.f4(ws, m, at), e4),
              tbl.p1(rest, m, im, fi, nx, ws, U32.inc(at), r4)))))

# the defs' bodies, after stores to field 1
def defs.p1(dl: List<&2, Bk.Def>, +dk: Bool, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +ws: List<&2, D.W1>, +at: U32,
  h: D.DefsK(dl, dk, ds, m, im, fi, nx, ks, img, at)) -> D.DefsK(dl, dk, ds, D.Put1(ws, m), im, fi, nx, ks, img, at):
  match dl:
    case Nil{}:
      Unit{}
    case Con{Bk.Def{_, _, +v, _}, +rest}:
      match h:
        case Tuple{e0, Tuple{ele, Tuple{hv, r3}}}:
          (e0, (ele, (isk.p1(dk, v, ds, m, im, fi, nx, ks, img, ws, at, hv),
            defs.p1(rest, dk, ds, m, im, fi, nx, ks, img, ws, U32.add(at, Mc.Img.size(v)), r3))))

# the image, after stores to field 1
def imgokk.p1(+dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells,
  +im: U32, +fi: U32, +nx: U32, +ws: List<&2, D.W1>,
  h: D.ImgOKK(dk, ds, ks, img, m, im, fi, nx)) -> D.ImgOKK(dk, ds, ks, img, D.Put1(ws, m), im, fi, nx):
  match h:
    case Tuple{tb, Tuple{hd, Tuple{h8, Tuple{h9, Tuple{h10, rest}}}}}:
      (tbl.p1(D.Tbl.rows(), m, im, fi, nx, ws, 272, tb),
        (defs.p1(ds, dk, ds, m, im, fi, nx, ks, img, ws, Mc.I.book(), hd),
        (isk.p1(dk, Bk.Term.Lab{El.Quan.name(Bk.Quan.Q0{})}, ds, m, im, fi, nx, ks, img, ws, 8, h8),
        (isk.p1(dk, Bk.Term.Lab{El.Quan.name(Bk.Quan.Q1{})}, ds, m, im, fi, nx, ks, img, ws, 9, h9),
        (isk.p1(dk, Bk.Term.Lab{El.Quan.name(Bk.Quan.Q2{})}, ds, m, im, fi, nx, ks, img, ws, 10, h10), rest)))))

# no cell of qs is one of ys
def Out(qs: List<&2, U32>, +ys: List<&2, U32>) -> Bool:
  match qs:
    case Nil{}:
      True{}
    case Con{+x, rest}:
      Bool.and(Bool.not(D.Mem(ys, x)), Out(rest, ys))

# the pend list's links, after stores to field 1 of other cells
def chain.p1(qs: List<&2, U32>, +ws: List<&2, D.W1>, +m: Cr.Cir.Cells, +p: U32, hq: {Out(qs, D.W1.cells(ws)) == True{} : Bool},
  h: D.Chain(qs, m, p)) -> D.Chain(qs, D.Put1(ws, m), p):
  match qs:
    case Nil{}:
      h
    case Con{+y, +rest}:
      match h:
        case Tuple{e1, Tuple{e2, r2}}:
          +M2 = D.Put1(ws, m)
          +hq2 = hq
          +nm = Bool.not(D.Mem(D.W1.cells(ws), y))
          (e1, (e2, (%Equal.sym(U32, D.Fd(1n, M2, y), D.Fd(1n, m, y),
              Equal.cong(Cr.Cir.Cell, U32, w => Cr.Cir.Cell.get(1n, w), Cr.Cir.Cells.get(M2, y), Cr.Cir.Cells.get(m, y),
                D.put1.out(ws, m, y, D.not.t(D.Mem(D.W1.cells(ws), y), D.and.l(nm, Out(rest, D.W1.cells(ws)), hq2))))) :
              D.Chain(rest, M2, _);
            chain.p1(rest, ws, m, D.Fd(1n, m, y), D.and.r(nm, Out(rest, D.W1.cells(ws)), hq2), r2))))

# The laws
# --------

def D.inc.post(f, dk, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, r, os, bs, fs, sp, pend, ps, c, u, xs, zs, hs, hac, hn, hc):
  ?TODO

def D.dec.post(f, dk, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, r, os, bs, fs, sp, pend, ps, c, u, xs, zs, hs, hac, hb, hl, hc, hp, h5):
  ?TODO

def D.alloc.post(f, dk, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, r, keep, os, bs, fs, sp, pend, ps, xs, zs, hs, hac, hl, hp, hr, hk):
  ?TODO

def D.release.post(f, dk, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, r, os, bs, fs, sp, pend, ps, z, xs, zs, hs, hac, hz, ht, hf, hm, hfs, hl, hc, hp):
  ?TODO

def D.is.fresh(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps, x, hs):
  ?TODO

def D.node.part(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps, c, y, hs, hn, hy):
  match hs:
    case Tuple{hos, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{+tbl, _}}}}}}:
      np.nodes(os, dk, ds, m, im, fi, nx, ks, img, ps, tbl, c, y, hos, hn, hy)

def D.store.post(dk, ds, ks, img, m, nx, fi, im, us, os, bs, fs, sp, pend, ps, z, x, xs, zs, hs, hac, hzx, hb, ho, hm, hzs, hzt, hz0, hzf, ht, hf):
  ?TODO

def D.data.flag(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps, c, xs, zs, hs, hac, hd):
  ?TODO
