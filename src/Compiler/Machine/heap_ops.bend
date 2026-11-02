# compiler: layer B, the heap's operations (U2)
# =============================================
#
# The laws inc.post, dec.post, alloc.post, release.post, is.fresh, node.part,
# store.post and data.flag of definitions.bend: each statement of the heap
# (M.inc, M.dec, M.alloc, M.release, a store) keeps HSK and the accounting
# AccK, within its budget. Filled by U2; U0 left each as ?TODO.

import Base
import ../../Book/impl.bend as Bk
import ../Cir/impl.bend as Cr
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
