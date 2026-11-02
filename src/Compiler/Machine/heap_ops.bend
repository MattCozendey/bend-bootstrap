# compiler: layer B, the heap's operations (U2)
# =============================================
#
# The laws inc.post, dec.post, alloc.post, release.post, is.fresh, node.part,
# store.post, term.post and data.flag of definitions.bend: each statement of
# the heap (M.inc, M.dec, M.alloc, M.release, a store) keeps HSK and the
# accounting AccK, within its budget. Filled by U2; U0 left each as ?TODO.

import Base
import ../../Book/impl.bend as Bk
import ../../Eval/impl.bend as El
import ../Cir/impl.bend as Cr
import ./impl.bend as Mc
import ../need_big.bend as N
import ./definitions.bend as D
import ./statement_runs.bend as X
import ./accounting.bend as AC

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

# each cell of ws is past b
def W1.gt(ws: List<&2, D.W1>, +b: U32) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case Con{D.W1{+q, _}, rest}:
      Bool.and(U32.is_lt(b, q), W1.gt(rest, b))

# a cell at most b is no cell of ws
def gt.out(ws: List<&2, D.W1>, +b: U32, +at: U32, hw: {W1.gt(ws, b) == True{} : Bool}, +hat: {U32.is_le(at, b) == True{} : Bool}) ->
  {D.Mem(D.W1.cells(ws), at) == False{} : Bool}:
  match ws:
    case Nil{}:
      {==}
    case Con{D.W1{+q, _}, +rest}:
      +hw2 = hw
      +ne = D.ne.sym(at, q, D.lit.ne(U32.is_eq(at, q), at, q, b, {==}, hat, D.u.lt(b, q, D.and.l(U32.is_lt(b, q), W1.gt(rest, b), hw2))))
      %Equal.sym(Bool, U32.is_eq(q, at), False{}, ne) : {Bool.or(_, D.Mem(D.W1.cells(rest), at)) == False{} : Bool}
      gt.out(rest, b, at, D.and.r(U32.is_lt(b, q), W1.gt(rest, b), hw2), hat)

# the table, after stores to field 1 of cells past it
def tbl.p1(cs: List<&2, Cr.Cir.Cell>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ws: List<&2, D.W1>, +at: U32,
  +hw: {W1.gt(ws, 290) == True{} : Bool}, hb: {D.TblB(cs, at) == True{} : Bool},
  h: D.Tbl.go(cs, m, im, fi, nx, at)) -> D.Tbl.go(cs, D.Put1(ws, m), im, fi, nx, at):
  match cs:
    case Nil{}:
      Unit{}
    case Con{+c, +rest}:
      match h:
        case Tuple{ec, Tuple{e, r2}}:
          +hb2 = hb
          +hat = D.and.l(U32.is_le(at, 290), D.TblB(rest, U32.inc(at)), hb2)
          (ec, (Equal.trans(Cr.Cir.Cell, Cr.Cir.Cells.get(D.Put1(ws, m), at), Cr.Cir.Cells.get(m, at), c,
              D.put1.out(ws, m, at, gt.out(ws, 290, at, hw, hat)), e),
            tbl.p1(rest, m, im, fi, nx, ws, U32.inc(at), hw, D.and.r(U32.is_le(at, 290), D.TblB(rest, U32.inc(at)), hb2), r2)))

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

# the image, after stores to field 1 of cells past the table
def imgokk.p1(+dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells,
  +im: U32, +fi: U32, +nx: U32, +ws: List<&2, D.W1>, hw: {W1.gt(ws, 290) == True{} : Bool},
  h: D.ImgOKK(dk, ds, ks, img, m, im, fi, nx)) -> D.ImgOKK(dk, ds, ks, img, D.Put1(ws, m), im, fi, nx):
  match h:
    case Tuple{tb, Tuple{hd, Tuple{h8, Tuple{h9, Tuple{h10, rest}}}}}:
      (tbl.p1(Mc.Img.table([]), m, im, fi, nx, ws, 272, hw, {==}, tb),
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

# Numbers
# -------
#
# A count never wraps: it is at most 3 × the machine's cells + 64 roots
# (D.ptr.bound), and next is at most 214748364 (Heap's Room), below 2^28;
# so a count + 2 is at most 2^32 (cnt.fits), and M.inc's + 1 adds 1.

# w + 0 with no carry is w; with a carry, w + 1
def adc.z(n: Nat, +w: Word(n)) -> {Word.adc(n, w, Word.zero(n), False{}, False{}) == w : Word(n)}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+(+p):
      match w:
        case WCon{False{}, +t}:
          Equal.cong(Word(p), Word(1n+p), z => WCon{False{}, z}, Word.adc(p, t, Word.zero(p), False{}, False{}), t, adc.z(p, t))
        case WCon{True{}, +t}:
          Equal.cong(Word(p), Word(1n+p), z => WCon{True{}, z}, Word.adc(p, t, Word.zero(p), False{}, False{}), t, adc.z(p, t))

def adc.c(n: Nat, +w: Word(n)) -> {Word.adc(n, w, Word.zero(n), False{}, True{}) == Word.inc(n, w) : Word(n)}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+(+p):
      match w:
        case WCon{False{}, +t}:
          Equal.cong(Word(p), Word(1n+p), z => WCon{True{}, z}, Word.adc(p, t, Word.zero(p), False{}, False{}), t, adc.z(p, t))
        case WCon{True{}, +t}:
          Equal.cong(Word(p), Word(1n+p), z => WCon{False{}, z}, Word.adc(p, t, Word.zero(p), False{}, True{}), Word.inc(p, t), adc.c(p, t))

# x + 1 is U32.inc(x)
def add1.inc(+x: U32) -> {U32.add(x, 1) == U32.inc(x) : U32}:
  match x:
    case U32{+w}:
      match w:
        case WCon{False{}, +t}:
          Equal.cong(Word(31n), U32, z => U32{WCon{True{}, z}}, Word.adc(31n, t, Word.zero(31n), False{}, False{}), t, adc.z(31n, t))
        case WCon{True{}, +t}:
          Equal.cong(Word(31n), U32, z => U32{WCon{False{}, z}}, Word.adc(31n, t, Word.zero(31n), False{}, True{}), Word.inc(31n, t), adc.c(31n, t))

# 1 + 2a <= 2b gives 1 + a <= b
def dle.odd(a: Nat, b: Nat, h: N.Le(1n+Nat.double(a), Nat.double(b))) -> N.Le(1n+a, b):
  match a:
    case 0n:
      match b:
        case 0n:
          Empty.absurd(N.Le(1n, 0n), h)
        case 1n+(+q):
          N.le_zero(q)
    case 1n+(+p):
      match b:
        case 0n:
          Empty.absurd(N.Le(2n+p, 0n), h)
        case 1n+(+q):
          dle.odd(p, q, h)

# the increment of an n-bit word below 2^n - 1 adds 1
def inc.fits(n: Nat, w: Word(n), h: N.Le(2n+Word.to_nat(n, w), N.D(n, 1n))) ->
  {Word.to_nat(n, Word.inc(n, w)) == 1n+Word.to_nat(n, w) : Nat}:
  match n:
    case 0n:
      Empty.absurd({Word.to_nat(0n, Word.inc(0n, w)) == 1n+Word.to_nat(0n, w) : Nat}, h)
    case 1n+(+p):
      match w:
        case WCon{False{}, +t}:
          {==}
        case WCon{True{}, +t}:
          +x = Word.to_nat(p, t)
          %Equal.sym(Nat, Word.to_nat(p, Word.inc(p, t)), 1n+x, inc.fits(p, t, dle.odd(1n+x, N.D(p, 1n), h))) :
            {Nat.double(_) == 2n+Nat.double(x) : Nat}
          {==}

# a <= 2a
def le.dbl(a: Nat) -> N.Le(a, Nat.double(a)):
  match a:
    case 0n:
      Unit{}
    case 1n+(+p):
      N.le_succ(p, Nat.double(p), le.dbl(p))

# x <= 2^k x
def le.dk(k: Nat, +x: Nat) -> N.Le(x, N.D(k, x)):
  match k:
    case 0n:
      N.le_refl(x)
    case 1n+(+q):
      N.le_trans(x, N.D(q, x), Nat.double(N.D(q, x)), le.dk(q, x), le.dbl(N.D(q, x)))

# a + b = b + a
def add.comm(a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, N.add_zero(b))
    case 1n+(+p):
      Equal.trans(Nat, 1n+Nat.add(p, b), 1n+Nat.add(b, p), Nat.add(b, 1n+p),
        Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, b), Nat.add(b, p), add.comm(p, b)),
        Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), N.add_succ_r(b, p)))

# a - f <= a
def sub.le(a: Nat, f: Nat) -> N.Le(Nat.sub(a, f), a):
  match a:
    case 0n:
      Unit{}
    case 1n+(+p):
      match f:
        case 0n:
          N.le_refl(1n+p)
        case 1n+(+q):
          N.le_succ(Nat.sub(p, q), p, sub.le(p, q))

# 2 + 3N + L <= 4X, for N < X, L <= 64 and 66 <= X
def cnt.room(+n: Nat, +l: Nat, +x: Nat, hn: N.Le(1n+n, x), hl: N.Le(l, 64n), hx: N.Le(66n, x)) ->
  N.Le(2n+Nat.add(Nat.mul(3n, n), l), Nat.mul(N.D(2n, 1n), x)):
  +s = Nat.mul(3n, n)
  +e66 = Equal.trans(Nat, Nat.add(s, 66n), 1n+Nat.add(s, 65n), 2n+Nat.add(s, 64n), N.add_succ_r(s, 65n),
    Equal.cong(Nat, Nat, z => 1n+z, Nat.add(s, 65n), 1n+Nat.add(s, 64n), N.add_succ_r(s, 64n)))
  +h1 = N.add_mono(s, s, l, 64n, N.le_refl(s), hl)
  +h2 = N.le_rw_r(2n+Nat.add(s, 64n), 2n+Nat.add(s, 64n), Nat.add(66n, s),
    Equal.trans(Nat, 2n+Nat.add(s, 64n), Nat.add(s, 66n), Nat.add(66n, s), Equal.sym(Nat, Nat.add(s, 66n), 2n+Nat.add(s, 64n), e66), add.comm(s, 66n)),
    N.le_refl(2n+Nat.add(s, 64n)))
  +h3 = N.add_mono(66n, x, s, Nat.mul(3n, x), hx, N.mul_mono_r(3n, n, x, N.weaken(n, x, hn)))
  N.le_trans(2n+Nat.add(s, l), 2n+Nat.add(s, 64n), Nat.mul(N.D(2n, 1n), x), h1,
    N.le_trans(2n+Nat.add(s, 64n), Nat.add(66n, s), Nat.mul(N.D(2n, 1n), x), h2, h3))

# 66 <= 2^k × 128
def le66.d(+k: Nat) -> N.Le(66n, N.D(k, N.D(7n, 1n))):
  N.le_trans(66n, N.D(7n, 1n), N.D(k, N.D(7n, 1n)), Unit{}, le.dk(k, N.D(7n, 1n)))

# 4x <= 16x
def le.d4(+x: Nat) -> N.Le(Nat.mul(N.D(2n, 1n), x), N.D(4n, x)):
  N.le_rw_l(N.D(2n, x), Nat.mul(N.D(2n, 1n), x), N.D(4n, x), Equal.sym(Nat, Nat.mul(N.D(2n, 1n), x), N.D(2n, x), N.mul_D(2n, x)),
    N.le_rw_r(N.D(2n, x), N.D(2n, N.D(2n, x)), N.D(4n, x), N.D_add(2n, 2n, 4n, x, {==}), le.dk(2n, N.D(2n, x))))

# 1 + a <= c, from a <= b < c
def lt.trans.le(+a: Nat, +b: Nat, +c: Nat, h1: N.Le(a, b), h2: N.Le(1n+b, c)) -> N.Le(1n+a, c):
  N.le_trans(1n+a, 1n+b, c, h1, h2)

# next, at most 214748364, is below 2^28
def nx.d28(+nx: U32, hr: {U32.is_le(nx, 214748364) == True{} : Bool}) -> N.Le(1n+U32.to_nat(nx), N.D(28n, 1n)):
  +b28 = {U32{N.bit(32n, 28n)} : U32}
  N.le_rw_r(1n+U32.to_nat(nx), U32.to_nat(b28), N.D(28n, 1n),
    Equal.trans(Nat, U32.to_nat(b28), Word.to_nat(32n, N.bit(32n, 28n)), N.D(28n, 1n), N.u32_to_nat(N.bit(32n, 28n)), N.bit_val(32n, 28n, Unit{})),
    lt.trans.le(U32.to_nat(nx), U32.to_nat(214748364), U32.to_nat(b28), D.u.le(nx, 214748364, hr), D.u.lt(214748364, b28, {==})))

# a U32 below 2^32 - 1 gains 1 with no wrap
def u32.inc.fits(v: U32, h: N.Le(2n+U32.to_nat(v), N.D(32n, 1n))) -> {U32.to_nat(U32.inc(v)) == 1n+U32.to_nat(v) : Nat}:
  match v:
    case U32{+w}:
      inc.fits(32n, w, (%N.u32_to_nat(w) : N.Le(2n+_, N.D(32n, 1n)); h))

# a count of at most 3 (nx - fi) + L, L <= 64, with nx below x = 2^k × 128 and
# 16x = 2^32, gains 1 with no wrap (every power of two is a variable here,
# so that no tool computes one)
def cnt.fits.g(+v: U32, +nx: U32, +fi: U32, +l: Nat, +x: Nat, +k: Nat,
  hv: N.Le(U32.to_nat(v), Nat.add(Nat.mul(3n, Nat.sub(U32.to_nat(nx), U32.to_nat(fi))), l)), hl: N.Le(l, 64n),
  hnx: N.Le(1n+U32.to_nat(nx), x), ex: {N.D(k, N.D(7n, 1n)) == x : Nat}, e32: {N.D(4n, x) == N.D(32n, 1n) : Nat}) ->
  {U32.to_nat(U32.add(v, 1)) == 1n+U32.to_nat(v) : Nat}:
  +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
  +hn = N.le_trans(1n+n, 1n+U32.to_nat(nx), x, sub.le(U32.to_nat(nx), U32.to_nat(fi)), hnx)
  +hx = N.le_rw_r(66n, N.D(k, N.D(7n, 1n)), x, ex, le66.d(k))
  +h4 = N.le_rw_r(2n+U32.to_nat(v), N.D(4n, x), N.D(32n, 1n), e32,
    N.le_trans(2n+U32.to_nat(v), 2n+Nat.add(Nat.mul(3n, n), l), N.D(4n, x), hv,
      N.le_trans(2n+Nat.add(Nat.mul(3n, n), l), Nat.mul(N.D(2n, 1n), x), N.D(4n, x), cnt.room(n, l, x, hn, hl, hx), le.d4(x))))
  %Equal.sym(U32, U32.add(v, 1), U32.inc(v), add1.inc(v)) : {U32.to_nat(_) == 1n+U32.to_nat(v) : Nat}
  u32.inc.fits(v, h4)

# a count of at most 3 (nx - fi) + L, L <= 64, gains 1 with no wrap
def cnt.fits(+v: U32, +nx: U32, +fi: U32, +l: Nat, hv: N.Le(U32.to_nat(v), Nat.add(Nat.mul(3n, Nat.sub(U32.to_nat(nx), U32.to_nat(fi))), l)),
  hl: N.Le(l, 64n), hr: {U32.is_le(nx, 214748364) == True{} : Bool}) -> {U32.to_nat(U32.add(v, 1)) == 1n+U32.to_nat(v) : Nat}:
  cnt.fits.g(v, nx, fi, l, N.D(28n, 1n), 21n, hv, hl, nx.d28(nx, hr), N.D_add(21n, 7n, 28n, 1n, {==}), N.D_add(4n, 28n, 32n, 1n, {==}))

# a term's tag is below 19
def atag.lt(t: Bk.Term) -> {U32.is_lt(D.A.tag(t), 19) == True{} : Bool}:
  match t:
    case Bk.Term.Var{_}:
      {==}
    case Bk.Term.Ref{_}:
      {==}
    case Bk.Term.Ann{_, _}:
      {==}
    case Bk.Term.Let{_, _, _}:
      {==}
    case Bk.Term.Typ{_}:
      {==}
    case Bk.Term.Min{_, _}:
      {==}
    case Bk.Term.All{_, _, _}:
      {==}
    case Bk.Term.Lam{_, _}:
      {==}
    case Bk.Term.App{_, _, _}:
      {==}
    case Bk.Term.Sig{_, _, _}:
      {==}
    case Bk.Term.Tup{_, _, _}:
      {==}
    case Bk.Term.Prj{_}:
      {==}
    case Bk.Term.Enu{_}:
      {==}
    case Bk.Term.Lab{_}:
      {==}
    case Bk.Term.Mat{_, _, _}:
      {==}
    case Bk.Term.Efq{}:
      {==}
    case Bk.Term.Eql{_, _, _}:
      {==}
    case Bk.Term.Rfl{}:
      {==}
    case Bk.Term.Rwt{_, _, _}:
      {==}

# a term's tag is no frame's
def atag.nf(t: Bk.Term) -> {Bool.and(Bool.not(Bool.and(U32.is_le(32, D.A.tag(t)), U32.is_le(D.A.tag(t), 40))), True{}) == True{} : Bool}:
  match t:
    case Bk.Term.Var{_}:
      {==}
    case Bk.Term.Ref{_}:
      {==}
    case Bk.Term.Ann{_, _}:
      {==}
    case Bk.Term.Let{_, _, _}:
      {==}
    case Bk.Term.Typ{_}:
      {==}
    case Bk.Term.Min{_, _}:
      {==}
    case Bk.Term.All{_, _, _}:
      {==}
    case Bk.Term.Lam{_, _}:
      {==}
    case Bk.Term.App{_, _, _}:
      {==}
    case Bk.Term.Sig{_, _, _}:
      {==}
    case Bk.Term.Tup{_, _, _}:
      {==}
    case Bk.Term.Prj{_}:
      {==}
    case Bk.Term.Enu{_}:
      {==}
    case Bk.Term.Lab{_}:
      {==}
    case Bk.Term.Mat{_, _, _}:
      {==}
    case Bk.Term.Efq{}:
      {==}
    case Bk.Term.Eql{_, _, _}:
      {==}
    case Bk.Term.Rfl{}:
      {==}
    case Bk.Term.Rwt{_, _, _}:
      {==}

# what the cell of a term says of itself, for either dk
def isk.nd(+dk: Bool, t: Bk.Term, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, h: D.IsK(dk, ds, m, im, fi, nx, ks, img, c, t)) ->
  D.NdK(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), t, D.A.tag(t)):
  match t:
    case Bk.Term.Var{+i}:
      match h:
        case Tuple{nd, _}:
          nd
    case Bk.Term.Ref{+k}:
      match h:
        case Tuple{nd, _}:
          nd
    case Bk.Term.Ann{+t1, +t2}:
      match h:
        case Tuple{nd, _}:
          nd
    case Bk.Term.Let{+q, +t1, +t2}:
      match h:
        case Tuple{nd, _}:
          nd
    case Bk.Term.Typ{+t1}:
      match h:
        case Tuple{nd, _}:
          nd
    case Bk.Term.Min{+t1, +t2}:
      match h:
        case Tuple{nd, _}:
          nd
    case Bk.Term.All{+q, +t1, +t2}:
      match h:
        case Tuple{nd, _}:
          nd
    case Bk.Term.Lam{+q, +t1}:
      match h:
        case Tuple{nd, _}:
          nd
    case Bk.Term.App{+q, +t1, +t2}:
      match h:
        case Tuple{nd, _}:
          nd
    case Bk.Term.Sig{+q, +t1, +t2}:
      match h:
        case Tuple{nd, _}:
          nd
    case Bk.Term.Tup{+q, +t1, +t2}:
      match h:
        case Tuple{nd, _}:
          nd
    case Bk.Term.Prj{+t1}:
      match h:
        case Tuple{nd, _}:
          nd
    case Bk.Term.Enu{+k}:
      match h:
        case Tuple{nd, _}:
          nd
    case Bk.Term.Lab{+k}:
      match h:
        case Tuple{nd, _}:
          nd
    case Bk.Term.Mat{+k, +t1, +t2}:
      match h:
        case Tuple{nd, _}:
          nd
    case Bk.Term.Efq{}:
      h
    case Bk.Term.Eql{+t1, +t2, +t3}:
      match h:
        case Tuple{nd, _}:
          nd
    case Bk.Term.Rfl{}:
      h
    case Bk.Term.Rwt{+t1, +t2, +t3}:
      match h:
        case Tuple{nd, _}:
          nd

# What a cell says of itself
# ---------------------------

def ndk.cell(-dk: Bool, -ds: List<&2, Bk.Def>, -im: U32, -fi: U32, -nx: U32, -c: U32, -x: Cr.Cir.Cell, -t: Bk.Term, -tag: U32,
  h: D.NdK(dk, ds, im, fi, nx, c, x, t, tag)) -> {Cr.Cir.is_cell(c, im, fi, nx) == True{} : Bool}:
  (e, _) = h
  e

def ndk.own(-dk: Bool, -ds: List<&2, Bk.Def>, -im: U32, -fi: U32, -nx: U32, -c: U32, -x: Cr.Cir.Cell, -t: Bk.Term, -tag: U32,
  h: D.NdK(dk, ds, im, fi, nx, c, x, t, tag)) -> {Bool.or(D.Own(fi, nx, c), D.FlW(Cr.Cir.Cell.get(0n, x), 1024)) == True{} : Bool}:
  (_, r) = h
  (e, _) = r
  e

# the image is below the machine's cells
def img.lt(-dk: Bool, -ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -m: Cr.Cir.Cells,
  -im: U32, -fi: U32, -nx: U32, h: D.ImgOKK(dk, ds, ks, img, m, im, fi, nx)) -> {U32.is_lt(im, fi) == True{} : Bool}:
  (_, r1) = h
  (_, r2) = r1
  (_, r3) = r2
  (_, r4) = r3
  (_, r5) = r4
  (_, r6) = r5
  (_, e) = r6
  e

# next is at most 214748364 (Room)
def heap.room(-m: Cr.Cir.Cells, -nx: U32, -fi: U32, -im: U32, -rs: List<&2, U32>, -pend: U32, -ps: List<&2, U32>,
  h: D.Heap(m, nx, fi, im, rs, pend, ps)) -> {U32.is_le(nx, 214748364) == True{} : Bool}:
  (_, r1) = h
  (_, r2) = r1
  (_, r3) = r2
  (_, r4) = r3
  (e, _) = r4
  e

def nz.of(b: Bool, +c: U32, +im: U32, +fi: U32, eb: {U32.is_eq(c, 0) == b : Bool}, hle: {U32.is_le(fi, c) == True{} : Bool},
  him: {U32.is_lt(im, fi) == True{} : Bool}) -> {U32.is_eq(c, 0) == False{} : Bool}:
  match b:
    case False{}:
      eb
    case True{}:
      Empty.absurd({U32.is_eq(c, 0) == False{} : Bool},
        N.le_trans(1n+U32.to_nat(im), U32.to_nat(fi), U32.to_nat(0), D.u.lt(im, fi, him),
          D.u.le(fi, 0, (%D.u32.eq(c, 0, eb) : {U32.is_le(fi, _) == True{} : Bool}; hle))))

# a cell is not 0
def cell.nz(+c: U32, +im: U32, +fi: U32, +nx: U32, hc: {Cr.Cir.is_cell(c, im, fi, nx) == True{} : Bool},
  +him: {U32.is_lt(im, fi) == True{} : Bool}) -> {U32.is_eq(c, 0) == False{} : Bool}:
  D.or.cases(Bool.and(Bool.not(U32.is_zero(c)), U32.is_le(c, im)), Bool.and(U32.is_le(fi, c), U32.is_lt(c, nx)),
    {U32.is_eq(c, 0) == False{} : Bool}, hc,
    e => D.not.t(U32.is_zero(c), D.and.l(Bool.not(U32.is_zero(c)), U32.is_le(c, im), e)),
    e => nz.of(U32.is_eq(c, 0), c, im, fi, {==}, D.and.l(U32.is_le(fi, c), U32.is_lt(c, nx), e), him))

# a or False
def or.false(a: Bool, -b: Bool, h: {Bool.or(a, b) == True{} : Bool}, hb: {b == False{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      D.bool.ft({False{} == True{} : Bool}, (%hb : {_ == True{} : Bool}; h))

# Counts
# ------

def nat.eq.refl(n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      nat.eq.refl(p)

def nat.eq.of(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      D.bool.ft({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      D.bool.ft({1n+p == 0n : Nat}, h)
    case 1n+(+p) 1n+(+q):
      Equal.cong(Nat, Nat, z => 1n+z, p, q, nat.eq.of(p, q, h))

# the length of a list of roots' cells
def len.cells(rs: List<&2, D.Rt>) -> {List.length(&2, U32, D.Rt.cells(rs)) == List.length(&2, D.Rt, rs) : Nat}:
  match rs:
    case Nil{}:
      {==}
    case Con{D.Rt{_, _}, +rest}:
      Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, U32, D.Rt.cells(rest)), List.length(&2, D.Rt, rest), len.cells(rest))

# the count condition at a cell p of the n cells from o
def cnt.get.b(b: Bool, +k: Nat, +m: Cr.Cir.Cells, +o: U32, +p: U32, +N: Nat, +fi: U32, +ps: List<&2, U32>, +rs: List<&2, U32>,
  eb: {U32.is_eq(o, p) == b : Bool},
  h1: N.Le(U32.to_nat(o), U32.to_nat(p)), h2: N.Le(1n+U32.to_nat(p), Nat.add(U32.to_nat(o), 1n+k)),
  hc: {D.Cnt(1n+k, m, o, N, fi, ps, rs) == True{} : Bool},
  ih: N.Le(U32.to_nat(U32.inc(o)), U32.to_nat(p)) -> N.Le(1n+U32.to_nat(p), Nat.add(U32.to_nat(U32.inc(o)), k)) ->
    {D.Cnt(k, m, U32.inc(o), N, fi, ps, rs) == True{} : Bool} ->
    {D.CntC(Cr.Cir.Cells.get(m, p), D.Ptr(N, m, fi, ps, rs, p), ps, p) == True{} : Bool}) ->
  {D.CntC(Cr.Cir.Cells.get(m, p), D.Ptr(N, m, fi, ps, rs, p), ps, p) == True{} : Bool}:
  match b:
    case True{}:
      %D.u32.eq(o, p, eb) : {D.CntC(Cr.Cir.Cells.get(m, _), D.Ptr(N, m, fi, ps, rs, _), ps, _) == True{} : Bool}
      D.and.l(D.CntC(Cr.Cir.Cells.get(m, o), D.Ptr(N, m, fi, ps, rs, o), ps, o), D.Cnt(k, m, U32.inc(o), N, fi, ps, rs), hc)
    case False{}:
      +lt = D.lt.ne(U32.cmp(o, p), U32.to_nat(o), U32.to_nat(p), N.U32.rel(o, p), eb, h1)
      +ei = D.u.inc(o, p, lt)
      +h1b = N.le_rw_l(1n+U32.to_nat(o), U32.to_nat(U32.inc(o)), U32.to_nat(p), Equal.sym(Nat, U32.to_nat(U32.inc(o)), 1n+U32.to_nat(o), ei), lt)
      +h2b = N.le_rw_r(1n+U32.to_nat(p), Nat.add(U32.to_nat(o), 1n+k), Nat.add(U32.to_nat(U32.inc(o)), k),
        Equal.trans(Nat, Nat.add(U32.to_nat(o), 1n+k), 1n+Nat.add(U32.to_nat(o), k), Nat.add(U32.to_nat(U32.inc(o)), k),
          N.add_succ_r(U32.to_nat(o), k),
          Equal.sym(Nat, Nat.add(U32.to_nat(U32.inc(o)), k), 1n+Nat.add(U32.to_nat(o), k),
            Equal.cong(Nat, Nat, x => Nat.add(x, k), U32.to_nat(U32.inc(o)), 1n+U32.to_nat(o), ei))), h2)
      ih(h1b, h2b, D.and.r(D.CntC(Cr.Cir.Cells.get(m, o), D.Ptr(N, m, fi, ps, rs, o), ps, o), D.Cnt(k, m, U32.inc(o), N, fi, ps, rs), hc))

def cnt.get(n: Nat, +m: Cr.Cir.Cells, +o: U32, +p: U32, +N: Nat, +fi: U32, +ps: List<&2, U32>, +rs: List<&2, U32>,
  h1: N.Le(U32.to_nat(o), U32.to_nat(p)), h2: N.Le(1n+U32.to_nat(p), Nat.add(U32.to_nat(o), n)),
  hc: {D.Cnt(n, m, o, N, fi, ps, rs) == True{} : Bool}) ->
  {D.CntC(Cr.Cir.Cells.get(m, p), D.Ptr(N, m, fi, ps, rs, p), ps, p) == True{} : Bool}:
  match n:
    case 0n:
      Empty.absurd({D.CntC(Cr.Cir.Cells.get(m, p), D.Ptr(N, m, fi, ps, rs, p), ps, p) == True{} : Bool},
        N.not_succ_le(U32.to_nat(p), N.le_trans(1n+U32.to_nat(p), U32.to_nat(o), U32.to_nat(p),
          N.le_rw_r(1n+U32.to_nat(p), Nat.add(U32.to_nat(o), 0n), U32.to_nat(o), N.add_zero(U32.to_nat(o)), h2), h1)))
    case 1n+(+k):
      cnt.get.b(U32.is_eq(o, p), k, m, o, p, N, fi, ps, rs, {==}, h1, h2, hc, x => y => z => cnt.get(k, m, U32.inc(o), p, N, fi, ps, rs, x, y, z))

# a term cell, not STATIC, out of the pend list, counts its pointers
def cntc.val(+m: Cr.Cir.Cells, +c: U32, +P: Nat, +ps: List<&2, U32>, h: {D.CntC(Cr.Cir.Cells.get(m, c), P, ps, c) == True{} : Bool},
  ht: {U32.is_lt(D.Tg(m, c), 19) == True{} : Bool}, hs: {D.Fl(m, c, 1024) == False{} : Bool}, hm: {D.Mem(ps, c) == False{} : Bool}) ->
  {U32.to_nat(D.Fd(1n, m, c)) == P : Nat}:
  nat.eq.of(U32.to_nat(D.Fd(1n, m, c)), P,
    (%hm : {Bool.or(Bool.not(True{}), Bool.or(False{}, Bool.or(_, Nat.is_eq(U32.to_nat(D.Fd(1n, m, c)), P)))) == True{} : Bool};
      (%hs : {Bool.or(Bool.not(True{}), Bool.or(_, Bool.or(D.Mem(ps, c), Nat.is_eq(U32.to_nat(D.Fd(1n, m, c)), P)))) == True{} : Bool};
        (%ht : {Bool.or(Bool.not(_), Bool.or(D.Fl(m, c, 1024), Bool.or(D.Mem(ps, c), Nat.is_eq(U32.to_nat(D.Fd(1n, m, c)), P)))) == True{} : Bool};
          h))))

# a cell that has a pointer is no cell of the pend list
def notin.ps(b: Bool, +ps: List<&2, U32>, +m: Cr.Cir.Cells, +fi: U32, +nx: U32, +rs: List<&2, U32>, +c: U32, eb: {D.Mem(ps, c) == b : Bool},
  hpk: D.PendOK(ps, ps, m, fi, nx, rs), hlt: {Nat.is_lt(0n, D.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, rs, c)) == True{} : Bool}) ->
  {D.Mem(ps, c) == False{} : Bool}:
  match b:
    case False{}:
      eb
    case True{}:
      +pm = D.pendok.mem(ps, ps, m, fi, nx, rs, c, hpk, eb)
      D.bool.ft({D.Mem(ps, c) == False{} : Bool},
        (%D.Ex.snd({D.Fl(m, c, 1024) == False{} : Bool}, _ => {D.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, rs, c) == 0n : Nat}, pm) :
          {Nat.is_lt(0n, _) == True{} : Bool}; hlt))

# a cell c that is STATIC or has a pointer is no cell of the pend list
def ne.hd(b: Bool, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +ps: List<&2, U32>, +rs: List<&2, U32>, +c: U32, +p: U32,
  eb: {U32.is_eq(c, p) == b : Bool}, hcd: {D.Hd(m, nx, fi, ps, rs, c) == True{} : Bool},
  hps: {D.Fl(m, p, 1024) == False{} : Bool}, hp0: {D.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, rs, p) == 0n : Nat}) ->
  {U32.is_eq(c, p) == False{} : Bool}:
  match b:
    case False{}:
      eb
    case True{}:
      D.bool.ft({U32.is_eq(c, p) == False{} : Bool},
        (%hp0 : {Bool.or(False{}, Nat.is_lt(0n, _)) == True{} : Bool};
          (%hps : {Bool.or(_, Nat.is_lt(0n, D.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, rs, p))) == True{} : Bool};
            (%D.u32.eq(c, p, eb) : {D.Hd(m, nx, fi, ps, rs, _) == True{} : Bool}; hcd))))

# one more root, at a cell that is STATIC or has a pointer: the pend list's
# cells still have none
def pendok.root(qs: List<&2, U32>, +ps: List<&2, U32>, +m: Cr.Cir.Cells, +fi: U32, +nx: U32, +rs: List<&2, U32>, +c: U32,
  +hcd: {D.Hd(m, nx, fi, ps, rs, c) == True{} : Bool}, h: D.PendOK(qs, ps, m, fi, nx, rs)) -> D.PendOK(qs, ps, m, fi, nx, Con{c, rs}):
  match qs:
    case Nil{}:
      Unit{}
    case Con{+p, +rest}:
      match h:
        case Tuple{ho, Tuple{+hs, Tuple{htg, Tuple{+hp0, hr}}}}:
          +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
          +ne = ne.hd(U32.is_eq(c, p), m, nx, fi, ps, rs, c, p, {==}, hcd, hs, hp0)
          (ho, (hs, (htg, ((%Equal.sym(Bool, U32.is_eq(c, p), False{}, ne) :
              {Nat.add(D.Pc(n, m, ps, fi, p), Nat.add(D.Nat.of(_), D.RcL(rs, p))) == 0n : Nat}; hp0),
            pendok.root(rest, ps, m, fi, nx, rs, c, hcd, hr)))))

# one more root at a STATIC cell keeps the counts
def cntc.root.s(b: Bool, +m: Cr.Cir.Cells, +c: U32, +q: U32, +N: Nat, +fi: U32, +ps: List<&2, U32>, +rs: List<&2, U32>,
  eb: {U32.is_eq(c, q) == b : Bool}, hst: {D.Fl(m, c, 1024) == True{} : Bool},
  h: {D.CntC(Cr.Cir.Cells.get(m, q), D.Ptr(N, m, fi, ps, rs, q), ps, q) == True{} : Bool}) ->
  {D.CntC(Cr.Cir.Cells.get(m, q), D.Ptr(N, m, fi, ps, Con{c, rs}, q), ps, q) == True{} : Bool}:
  match b:
    case False{}:
      %Equal.sym(Bool, U32.is_eq(c, q), False{}, eb) :
        {D.CntC(Cr.Cir.Cells.get(m, q), Nat.add(D.Pc(N, m, ps, fi, q), Nat.add(D.Nat.of(_), D.RcL(rs, q))), ps, q) == True{} : Bool}
      h
    case True{}:
      %D.u32.eq(c, q, eb) : {D.CntC(Cr.Cir.Cells.get(m, _), D.Ptr(N, m, fi, ps, Con{c, rs}, _), ps, _) == True{} : Bool}
      D.or.r(Bool.not(U32.is_lt(D.Tg(m, c), 19)), Bool.or(D.Fl(m, c, 1024), Bool.or(D.Mem(ps, c), Nat.is_eq(U32.to_nat(D.Fd(1n, m, c)), D.Ptr(N, m, fi, ps, Con{c, rs}, c)))),
        D.or.l(D.Fl(m, c, 1024), Bool.or(D.Mem(ps, c), Nat.is_eq(U32.to_nat(D.Fd(1n, m, c)), D.Ptr(N, m, fi, ps, Con{c, rs}, c))), hst))

def cnt.root.s(k: Nat, +m: Cr.Cir.Cells, +c: U32, +o: U32, +N: Nat, +fi: U32, +ps: List<&2, U32>, +rs: List<&2, U32>,
  +hst: {D.Fl(m, c, 1024) == True{} : Bool}, h: {D.Cnt(k, m, o, N, fi, ps, rs) == True{} : Bool}) ->
  {D.Cnt(k, m, o, N, fi, ps, Con{c, rs}) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+(+j):
      +h2 = h
      D.and.i(D.CntC(Cr.Cir.Cells.get(m, o), D.Ptr(N, m, fi, ps, Con{c, rs}, o), ps, o), D.Cnt(j, m, U32.inc(o), N, fi, ps, Con{c, rs}),
        cntc.root.s(U32.is_eq(c, o), m, c, o, N, fi, ps, rs, {==}, hst,
          D.and.l(D.CntC(Cr.Cir.Cells.get(m, o), D.Ptr(N, m, fi, ps, rs, o), ps, o), D.Cnt(j, m, U32.inc(o), N, fi, ps, rs), h2)),
        cnt.root.s(j, m, c, U32.inc(o), N, fi, ps, rs, hst,
          D.and.r(D.CntC(Cr.Cir.Cells.get(m, o), D.Ptr(N, m, fi, ps, rs, o), ps, o), D.Cnt(j, m, U32.inc(o), N, fi, ps, rs), h2)))

# M.inc's count at a cell q: c gains a pointer (a root) and its count v;
# every other cell keeps both
def cntc.inc.b(b: Bool, +m: Cr.Cir.Cells, +c: U32, +v: U32, +q: U32, +N: Nat, +fi: U32, +ps: List<&2, U32>, +rs: List<&2, U32>,
  eb: {U32.is_eq(q, c) == b : Bool}, ev: {U32.to_nat(v) == 1n+D.Ptr(N, m, fi, ps, rs, c) : Nat},
  h: {D.CntC(Cr.Cir.Cells.get(m, q), D.Ptr(N, m, fi, ps, rs, q), ps, q) == True{} : Bool}) ->
  {D.CntC(Cr.Cir.Cells.get(D.Put1([D.W1{c, v}], m), q), D.Ptr(N, m, fi, ps, Con{c, rs}, q), ps, q) == True{} : Bool}:
  match b:
    case False{}:
      +ne = D.ne.sym(q, c, eb)
      +M2 = D.Put1([D.W1{c, v}], m)
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, q), Cr.Cir.Cells.get(m, q),
          D.put1.out([D.W1{c, v}], m, q, (%Equal.sym(Bool, U32.is_eq(c, q), False{}, ne) : {Bool.or(_, False{}) == False{} : Bool}; {==}))) :
        {D.CntC(_, D.Ptr(N, m, fi, ps, Con{c, rs}, q), ps, q) == True{} : Bool}
      %Equal.sym(Bool, U32.is_eq(c, q), False{}, ne) :
        {D.CntC(Cr.Cir.Cells.get(m, q), Nat.add(D.Pc(N, m, ps, fi, q), Nat.add(D.Nat.of(_), D.RcL(rs, q))), ps, q) == True{} : Bool}
      h
    case True{}:
      +M2 = D.Put1([D.W1{c, v}], m)
      +Y = Cr.Cir.Cells.get(m, c)
      +P = D.Ptr(N, m, fi, ps, Con{c, rs}, c)
      %Equal.sym(U32, q, c, D.u32.eq(q, c, eb)) : {D.CntC(Cr.Cir.Cells.get(M2, _), D.Ptr(N, m, fi, ps, Con{c, rs}, _), ps, _) == True{} : Bool}
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, c), Cr.Cir.Cell.set(1n, Y, v), D.cl.gs(m, c, Cr.Cir.Cell.set(1n, Y, v))) :
        {D.CntC(_, P, ps, c) == True{} : Bool}
      D.or.r(Bool.not(U32.is_lt(D.TgW(Cr.Cir.Cell.get(0n, Cr.Cir.Cell.set(1n, Y, v))), 19)),
        Bool.or(D.FlW(Cr.Cir.Cell.get(0n, Cr.Cir.Cell.set(1n, Y, v)), 1024), Bool.or(D.Mem(ps, c), Nat.is_eq(U32.to_nat(Cr.Cir.Cell.get(1n, Cr.Cir.Cell.set(1n, Y, v))), P))),
        D.or.r(D.FlW(Cr.Cir.Cell.get(0n, Cr.Cir.Cell.set(1n, Y, v)), 1024), Bool.or(D.Mem(ps, c), Nat.is_eq(U32.to_nat(Cr.Cir.Cell.get(1n, Cr.Cir.Cell.set(1n, Y, v))), P)),
          D.or.r(D.Mem(ps, c), Nat.is_eq(U32.to_nat(Cr.Cir.Cell.get(1n, Cr.Cir.Cell.set(1n, Y, v))), P),
            (%Equal.sym(U32, Cr.Cir.Cell.get(1n, Cr.Cir.Cell.set(1n, Y, v)), v, D.cg1(Y, v)) : {Nat.is_eq(U32.to_nat(_), P) == True{} : Bool};
              (%Equal.sym(Bool, U32.is_eq(c, c), True{}, D.u32.refl(c)) :
                  {Nat.is_eq(U32.to_nat(v), Nat.add(D.Pc(N, m, ps, fi, c), Nat.add(D.Nat.of(_), D.RcL(rs, c)))) == True{} : Bool};
                (%Equal.sym(Nat, Nat.add(D.Pc(N, m, ps, fi, c), 1n+D.RcL(rs, c)), 1n+Nat.add(D.Pc(N, m, ps, fi, c), D.RcL(rs, c)),
                    N.add_succ_r(D.Pc(N, m, ps, fi, c), D.RcL(rs, c))) : {Nat.is_eq(U32.to_nat(v), _) == True{} : Bool};
                  (%ev : {Nat.is_eq(U32.to_nat(v), _) == True{} : Bool}; nat.eq.refl(U32.to_nat(v)))))))))

def cntc.inc(b: Bool, +m: Cr.Cir.Cells, +c: U32, +v: U32, +q: U32, +N: Nat, +fi: U32, +ps: List<&2, U32>, +rs: List<&2, U32>,
  eb: {U32.is_eq(q, c) == b : Bool}, ev: {U32.to_nat(v) == 1n+D.Ptr(N, m, fi, ps, rs, c) : Nat},
  h: {D.CntC(Cr.Cir.Cells.get(m, q), D.Ptr(N, m, fi, ps, rs, q), ps, q) == True{} : Bool}) ->
  {D.CntC(Cr.Cir.Cells.get(D.Put1([D.W1{c, v}], m), q), D.Ptr(N, D.Put1([D.W1{c, v}], m), fi, ps, Con{c, rs}, q), ps, q) == True{} : Bool}:
  +ws = {[D.W1{c, v}] : List<&2, D.W1>}
  %Equal.sym(Nat, D.Ptr(N, D.Put1(ws, m), fi, ps, Con{c, rs}, q), D.Ptr(N, m, fi, ps, Con{c, rs}, q), D.ptr.put1(N, ws, m, fi, ps, Con{c, rs}, q)) :
    {D.CntC(Cr.Cir.Cells.get(D.Put1(ws, m), q), _, ps, q) == True{} : Bool}
  cntc.inc.b(b, m, c, v, q, N, fi, ps, rs, eb, ev, h)

def cnt.inc(k: Nat, +m: Cr.Cir.Cells, +c: U32, +v: U32, +o: U32, +N: Nat, +fi: U32, +ps: List<&2, U32>, +rs: List<&2, U32>,
  +ev: {U32.to_nat(v) == 1n+D.Ptr(N, m, fi, ps, rs, c) : Nat}, h: {D.Cnt(k, m, o, N, fi, ps, rs) == True{} : Bool}) ->
  {D.Cnt(k, D.Put1([D.W1{c, v}], m), o, N, fi, ps, Con{c, rs}) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+(+j):
      +M2 = D.Put1([D.W1{c, v}], m)
      +h2 = h
      D.and.i(D.CntC(Cr.Cir.Cells.get(M2, o), D.Ptr(N, M2, fi, ps, Con{c, rs}, o), ps, o), D.Cnt(j, M2, U32.inc(o), N, fi, ps, Con{c, rs}),
        cntc.inc(U32.is_eq(o, c), m, c, v, o, N, fi, ps, rs, {==}, ev,
          D.and.l(D.CntC(Cr.Cir.Cells.get(m, o), D.Ptr(N, m, fi, ps, rs, o), ps, o), D.Cnt(j, m, U32.inc(o), N, fi, ps, rs), h2)),
        cnt.inc(j, m, c, v, U32.inc(o), N, fi, ps, rs, ev,
          D.and.r(D.CntC(Cr.Cir.Cells.get(m, o), D.Ptr(N, m, fi, ps, rs, o), ps, o), D.Cnt(j, m, U32.inc(o), N, fi, ps, rs), h2)))

# no cell of the pend list is c
def out.one(qs: List<&2, U32>, +c: U32, h: {D.Mem(qs, c) == False{} : Bool}) -> {Out(qs, [c]) == True{} : Bool}:
  match qs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      +h2 = h
      +ne = D.ne.sym(x, c, D.or.f.l(U32.is_eq(x, c), D.Mem(rest, c), h2))
      %Equal.sym(Bool, U32.is_eq(c, x), False{}, ne) : {Bool.and(Bool.not(Bool.or(_, False{})), Out(rest, [c])) == True{} : Bool}
      out.one(rest, c, D.or.f.r(U32.is_eq(x, c), D.Mem(rest, c), h2))

# a term cell is no frame
def w1.nf.one(+m: Cr.Cir.Cells, +c: U32, +v: U32, +u: Bk.Term, et: {D.Tg(m, c) == D.A.tag(u) : U32}) -> {W1.nf([D.W1{c, v}], m) == True{} : Bool}:
  %Equal.sym(U32, D.Tg(m, c), D.A.tag(u), et) : {Bool.and(Bool.not(Bool.and(U32.is_le(32, _), U32.is_le(_, 40))), True{}) == True{} : Bool}
  atag.nf(u)

# M.inc
# -----

# the counts of a heap
def heap.cnt(-m: Cr.Cir.Cells, -nx: U32, -fi: U32, -im: U32, -rs: List<&2, U32>, -pend: U32, -ps: List<&2, U32>,
  h: D.Heap(m, nx, fi, im, rs, pend, ps)) ->
  {D.Cnt(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), fi, ps, rs) == True{} : Bool}:
  (_, r1) = h
  (_, r2) = r1
  (e, _) = r2
  e

# a or b, a false: b
def or.false.l(a: Bool, -b: Bool, h: {Bool.or(a, b) == True{} : Bool}, ha: {a == False{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      D.bool.ft({b == True{} : Bool}, Equal.sym(Bool, True{}, False{}, ha))
    case False{}:
      h

def lt.of.rel(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), h: N.Le(1n+x, y)) -> {Cmp.is_lt(c) == True{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({Cmp.is_lt(EQ{}) == True{} : Bool}, N.not_succ_le(y, (%r : N.Le(1n+_, y); h)))
    case GT{}:
      Empty.absurd({Cmp.is_lt(GT{}) == True{} : Bool}, N.not_succ_le(y, N.le_trans(1n+y, x, y, r, N.weaken(x, y, h))))

# a < b, from their numbers
def u.lt.of(+a: U32, +b: U32, h: N.Le(1n+U32.to_nat(a), U32.to_nat(b))) -> {U32.is_lt(a, b) == True{} : Bool}:
  lt.of.rel(U32.cmp(a, b), U32.to_nat(a), U32.to_nat(b), N.U32.rel(a, b), h)

# one store, at one of the machine's own cells: past the table
def gt.one(+dk: Bool, -ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -m: Cr.Cir.Cells,
  +im: U32, +fi: U32, +nx: U32, +c: U32, +v: U32, io: D.ImgOKK(dk, ds, ks, img, m, im, fi, nx), own: {D.Own(fi, nx, c) == True{} : Bool}) ->
  {W1.gt([D.W1{c, v}], 290) == True{} : Bool}:
  %Equal.sym(Bool, U32.is_lt(290, c), True{}, u.lt.of(290, c, D.img.hz(dk, ds, ks, img, m, im, fi, nx, c, io, own))) :
    {Bool.and(_, True{}) == True{} : Bool}
  {==}

# HSK after M.inc of a held cell c that is not STATIC: its count gets v, one
# more than its pointers, and it is an owned root too
def inc.hs.n(+dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32,
  +ps: List<&2, U32>, +c: U32, +u: Bk.Term, +v: U32,
  hos: D.RtsK(dk, ds, m, im, fi, nx, ks, img, os), +hbs: D.RtsK(dk, ds, m, im, fi, nx, ks, img, Con{D.Rt{c, u}, bs}),
  hheld: D.Held(m, os, Con{D.Rt{c, u}, bs}), hfrs: D.FrsK(dk, ds, m, im, fi, nx, ks, img, ps, sp, fs),
  hheap: D.Heap(m, nx, fi, im, D.Rt.cells(os), pend, ps), himg: D.ImgOKK(dk, ds, ks, img, m, im, fi, nx),
  +hcd: {D.Hd(m, nx, fi, ps, D.Rt.cells(os), c) == True{} : Bool}, +hpn: {D.Mem(ps, c) == False{} : Bool},
  +et: {D.Tg(m, c) == D.A.tag(u) : U32}, +hgt: {W1.gt([D.W1{c, v}], 290) == True{} : Bool},
  +ev: {U32.to_nat(v) == 1n+D.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, D.Rt.cells(os), c) : Nat}) ->
  D.HSK(dk, ds, ks, img, D.Put1([D.W1{c, v}], m), nx, fi, im, Con{D.Rt{c, u}, os}, Con{D.Rt{c, u}, bs}, fs, sp, pend, ps):
  match hbs:
    case Tuple{+hu, _}:
      match hheld:
        case Tuple{_, hheld2}:
          match hheap:
            case Tuple{hch, Tuple{hpk, Tuple{hcnt, Tuple{hpts, hr}}}}:
              +ws = {[D.W1{c, v}] : List<&2, D.W1>}
              +M2 = D.Put1(ws, m)
              +rs = D.Rt.cells(os)
              +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
              ((isk.p1(dk, u, ds, m, im, fi, nx, ks, img, ws, c, hu), rtsk.p1(dk, os, ds, m, im, fi, nx, ks, img, ws, hos)),
                (rtsk.p1(dk, Con{D.Rt{c, u}, bs}, ds, m, im, fi, nx, ks, img, ws, hbs),
                ((D.or.r(D.Fl(M2, c, 1024), D.Nodes(Con{D.Rt{c, u}, os}, M2, c),
                    D.or.l(D.Node(u, M2, c, c), D.Nodes(os, M2, c), node.self(u, M2, c, c, D.u32.refl(c)))),
                  held.p1(bs, Con{D.Rt{c, u}, os}, ws, m, held.cons(bs, os, c, u, m, hheld2))),
                (frsk.p1(dk, fs, ds, m, im, fi, nx, ks, img, ps, ws, sp, w1.nf.one(m, c, v, u, et), hfrs),
                ((chain.p1(ps, ws, m, pend, out.one(ps, c, hpn), hch),
                  (D.pendok.put1(ps, ps, ws, m, fi, nx, Con{c, rs}, pendok.root(ps, ps, m, fi, nx, rs, c, hcd, hpk)),
                  (cnt.inc(n, m, c, v, fi, n, fi, ps, rs, ev, hcnt),
                  ((%Equal.sym(Bool, D.Pts(n, M2, ps, fi, im, fi, nx), D.Pts(n, m, ps, fi, im, fi, nx), D.pts.put1(n, ws, m, ps, fi, im, fi, nx)) :
                      {_ == True{} : Bool}; hpts),
                    hr)))),
                  imgokk.p1(dk, ds, ks, img, m, im, fi, nx, ws, hgt, himg))))))

# HSK after M.inc of a held STATIC cell c: no cell changes, and c is an
# owned root too
def inc.hs.s(+dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32,
  +ps: List<&2, U32>, +c: U32, +u: Bk.Term,
  hos: D.RtsK(dk, ds, m, im, fi, nx, ks, img, os), +hbs: D.RtsK(dk, ds, m, im, fi, nx, ks, img, Con{D.Rt{c, u}, bs}),
  hheld: D.Held(m, os, Con{D.Rt{c, u}, bs}), hfrs: D.FrsK(dk, ds, m, im, fi, nx, ks, img, ps, sp, fs),
  hheap: D.Heap(m, nx, fi, im, D.Rt.cells(os), pend, ps), himg: D.ImgOKK(dk, ds, ks, img, m, im, fi, nx),
  +hcd: {D.Hd(m, nx, fi, ps, D.Rt.cells(os), c) == True{} : Bool}, +hst: {D.Fl(m, c, 1024) == True{} : Bool}) ->
  D.HSK(dk, ds, ks, img, m, nx, fi, im, Con{D.Rt{c, u}, os}, Con{D.Rt{c, u}, bs}, fs, sp, pend, ps):
  match hbs:
    case Tuple{+hu, _}:
      match hheld:
        case Tuple{_, hheld2}:
          match hheap:
            case Tuple{hch, Tuple{hpk, Tuple{hcnt, hrest}}}:
              +rs = D.Rt.cells(os)
              +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
              ((hu, hos), (hbs, ((D.or.l(D.Fl(m, c, 1024), D.Nodes(Con{D.Rt{c, u}, os}, m, c), hst), held.cons(bs, os, c, u, m, hheld2)),
                (hfrs, ((hch, (pendok.root(ps, ps, m, fi, nx, rs, c, hcd, hpk), (cnt.root.s(n, m, c, fi, n, fi, ps, rs, hst, hcnt), hrest))),
                  himg)))))

# stores to field 1 of one cell
def put1.one(+m: Cr.Cir.Cells, +c: U32, +v: U32) -> {D.Put1([D.W1{c, v}], m) == X.X.put(m, 1n, c, v) : Cr.Cir.Cells}:
  {==}

# M.inc, by the flag STATIC of c
def inc.go(b: Bool, +f: Nat, +dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +r: Nat,
  +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>, +c: U32, +u: Bk.Term,
  +xs: List<&2, D.TmpE>, +zs: List<&2, D.Rt>, +eb: {D.Fl(m, c, 1024) == b : Bool},
  +hos: D.RtsK(dk, ds, m, im, fi, nx, ks, img, os), +hbs: D.RtsK(dk, ds, m, im, fi, nx, ks, img, Con{D.Rt{c, u}, bs}),
  +hheld: D.Held(m, os, Con{D.Rt{c, u}, bs}), +hfrs: D.FrsK(dk, ds, m, im, fi, nx, ks, img, ps, sp, fs),
  +hheap: D.Heap(m, nx, fi, im, D.Rt.cells(os), pend, ps), +himg: D.ImgOKK(dk, ds, ks, img, m, im, fi, nx),
  hac: D.AccK(dk, ds, ks, img, m, nx, fi, im, os, xs, sp, fs, ps, zs),
  hn: N.Le(List.length(&2, D.Rt, os), 64n),
  +hc: {List.get(&2, U32, regs, r) == Some{c} : Maybe<&2, U32>}) ->
  D.PostB(False{}, Cr.Cir.exec(f, Mc.M.inc(r), Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0}),
    st2 => D.Ex(Cr.Cir.Cells, m2 => D.P2({st2 == Cr.Cir.State{regs, m2, nx, fi, im, pg, lim, inp, Nil{}, 0} : Cr.Cir.State},
      D.P2(D.HSK(dk, ds, ks, img, m2, nx, fi, im, Con{D.Rt{c, u}, os}, Con{D.Rt{c, u}, bs}, fs, sp, pend, ps),
        D.AccK(dk, ds, ks, img, m2, nx, fi, im, Con{D.Rt{c, u}, os}, xs, sp, fs, ps, zs)))),
    s => st2 => Empty, 0n, lim):
  match b:
    case True{}:
      +hs = {(hos, (hbs, (hheld, (hfrs, (hheap, himg))))) : D.HSK(dk, ds, ks, img, m, nx, fi, im, os, Con{D.Rt{c, u}, bs}, fs, sp, pend, ps)}
      +hu = D.Ex.fst(D.IsK(dk, ds, m, im, fi, nx, ks, img, c, u), _ => D.RtsK(dk, ds, m, im, fi, nx, ks, img, bs), hbs)
      +nd = isk.nd(dk, u, ds, m, im, fi, nx, ks, img, c, hu)
      +hcell = ndk.cell(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), u, D.A.tag(u), nd)
      +hz = cell.nz(c, im, fi, nx, hcell, img.lt(dk, ds, ks, img, m, im, fi, nx, himg))
      +hcd = D.held.ptr(dk, ds, ks, img, m, nx, fi, im, os, Con{D.Rt{c, u}, bs}, fs, sp, pend, ps, c, hs,
        D.Ex.fst({Bool.or(D.Fl(m, c, 1024), D.Nodes(os, m, c)) == True{} : Bool}, _ => D.Held(m, os, bs), hheld))
      %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, Mc.M.inc(r), Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0}),
          Cr.Cir.Out.next{X.X.st(regs, m, nx, fi, im, pg, lim, inp)}, X.inc.eq.s(f, regs, m, nx, fi, im, pg, lim, inp, r, c, hc, hz, hcell, eb)) :
        D.PostB(False{}, _,
          st2 => D.Ex(Cr.Cir.Cells, m2 => D.P2({st2 == Cr.Cir.State{regs, m2, nx, fi, im, pg, lim, inp, Nil{}, 0} : Cr.Cir.State},
            D.P2(D.HSK(dk, ds, ks, img, m2, nx, fi, im, Con{D.Rt{c, u}, os}, Con{D.Rt{c, u}, bs}, fs, sp, pend, ps),
              D.AccK(dk, ds, ks, img, m2, nx, fi, im, Con{D.Rt{c, u}, os}, xs, sp, fs, ps, zs)))),
          s => st2 => Empty, 0n, lim)
      (m, ({==}, (inc.hs.s(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps, c, u, hos, hbs, hheld, hfrs, hheap, himg, hcd, eb),
        AC.acc.root(dk, ds, ks, img, m, nx, fi, im, D.Rt{c, u}, os, xs, sp, fs, ps, zs, hac))))
    case False{}:
      +hs = {(hos, (hbs, (hheld, (hfrs, (hheap, himg))))) : D.HSK(dk, ds, ks, img, m, nx, fi, im, os, Con{D.Rt{c, u}, bs}, fs, sp, pend, ps)}
      +hu = D.Ex.fst(D.IsK(dk, ds, m, im, fi, nx, ks, img, c, u), _ => D.RtsK(dk, ds, m, im, fi, nx, ks, img, bs), hbs)
      +nd = isk.nd(dk, u, ds, m, im, fi, nx, ks, img, c, hu)
      +hcell = ndk.cell(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), u, D.A.tag(u), nd)
      +hz = cell.nz(c, im, fi, nx, hcell, img.lt(dk, ds, ks, img, m, im, fi, nx, himg))
      +hcd = D.held.ptr(dk, ds, ks, img, m, nx, fi, im, os, Con{D.Rt{c, u}, bs}, fs, sp, pend, ps, c, hs,
        D.Ex.fst({Bool.or(D.Fl(m, c, 1024), D.Nodes(os, m, c)) == True{} : Bool}, _ => D.Held(m, os, bs), hheld))
      +et = {D.nd.tgk(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), u, D.A.tag(u), nd) : {D.Tg(m, c) == D.A.tag(u) : U32}}
      +ht = {(%Equal.sym(U32, D.Tg(m, c), D.A.tag(u), et) : {U32.is_lt(_, 19) == True{} : Bool}; atag.lt(u)) : {U32.is_lt(D.Tg(m, c), 19) == True{} : Bool}}
      +own = or.false(D.Own(fi, nx, c), D.FlW(Cr.Cir.Cell.get(0n, Cr.Cir.Cells.get(m, c)), 1024),
        ndk.own(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), u, D.A.tag(u), nd), eb)
      +rs = D.Rt.cells(os)
      +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
      +hpk = D.heap.pend(m, nx, fi, im, rs, pend, ps, hheap)
      +hlt = or.false.l(D.Fl(m, c, 1024), Nat.is_lt(0n, D.Ptr(n, m, fi, ps, rs, c)), hcd, eb)
      +hpn = notin.ps(D.Mem(ps, c), ps, m, fi, nx, rs, c, {==}, hpk, hlt)
      +h1 = D.u.le(fi, c, D.and.l(U32.is_le(fi, c), U32.is_lt(c, nx), own))
      +hl1 = D.u.lt(c, nx, D.and.r(U32.is_le(fi, c), U32.is_lt(c, nx), own))
      +es = D.add.sub(U32.to_nat(fi), U32.to_nat(nx), N.le_trans(U32.to_nat(fi), U32.to_nat(c), U32.to_nat(nx), h1, N.weaken(U32.to_nat(c), U32.to_nat(nx), hl1)))
      +h2 = N.le_rw_r(1n+U32.to_nat(c), U32.to_nat(nx), Nat.add(U32.to_nat(fi), n), Equal.sym(Nat, Nat.add(U32.to_nat(fi), n), U32.to_nat(nx), es), hl1)
      +hcc = cnt.get(n, m, fi, c, n, fi, ps, rs, h1, h2, heap.cnt(m, nx, fi, im, rs, pend, ps, hheap))
      +hfv = cntc.val(m, c, D.Ptr(n, m, fi, ps, rs, c), ps, hcc, ht, eb, hpn)
      +f1 = D.Fd(1n, m, c)
      +v = U32.add(f1, 1)
      +hb3 = N.le_rw_l(D.Ptr(n, m, fi, ps, rs, c), U32.to_nat(f1), Nat.add(Nat.mul(3n, n), List.length(&2, U32, rs)),
        Equal.sym(Nat, U32.to_nat(f1), D.Ptr(n, m, fi, ps, rs, c), hfv), D.ptr.bound(n, m, fi, ps, rs, c))
      +hl64 = N.le_rw_l(List.length(&2, D.Rt, os), List.length(&2, U32, rs), 64n,
        Equal.sym(Nat, List.length(&2, U32, rs), List.length(&2, D.Rt, os), len.cells(os)), hn)
      +ev0 = cnt.fits(f1, nx, fi, List.length(&2, U32, rs), hb3, hl64, heap.room(m, nx, fi, im, rs, pend, ps, hheap))
      +ev = Equal.trans(Nat, U32.to_nat(v), 1n+U32.to_nat(f1), 1n+D.Ptr(n, m, fi, ps, rs, c), ev0,
        Equal.cong(Nat, Nat, w => 1n+w, U32.to_nat(f1), D.Ptr(n, m, fi, ps, rs, c), hfv))
      +hsk = inc.hs.n(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps, c, u, v, hos, hbs, hheld, hfrs, hheap, himg, hcd, hpn, et,
        gt.one(dk, ds, ks, img, m, im, fi, nx, c, v, himg, own), ev)
      %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, Mc.M.inc(r), Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0}),
          Cr.Cir.Out.next{X.X.st(regs, X.X.put(m, 1n, c, U32.add(Cr.Cir.Cell.get(1n, Cr.Cir.Cells.get(m, c)), 1)), nx, fi, im, pg, lim, inp)},
          X.inc.eq.n(f, regs, m, nx, fi, im, pg, lim, inp, r, c, hc, hz, hcell, eb)) :
        D.PostB(False{}, _,
          st2 => D.Ex(Cr.Cir.Cells, m2 => D.P2({st2 == Cr.Cir.State{regs, m2, nx, fi, im, pg, lim, inp, Nil{}, 0} : Cr.Cir.State},
            D.P2(D.HSK(dk, ds, ks, img, m2, nx, fi, im, Con{D.Rt{c, u}, os}, Con{D.Rt{c, u}, bs}, fs, sp, pend, ps),
              D.AccK(dk, ds, ks, img, m2, nx, fi, im, Con{D.Rt{c, u}, os}, xs, sp, fs, ps, zs)))),
          s => st2 => Empty, 0n, lim)
      (X.X.put(m, 1n, c, v), ({==},
        ((%put1.one(m, c, v) : D.HSK(dk, ds, ks, img, _, nx, fi, im, Con{D.Rt{c, u}, os}, Con{D.Rt{c, u}, bs}, fs, sp, pend, ps); hsk),
          AC.acc.inc(dk, ds, ks, img, m, nx, fi, im, os, Con{D.Rt{c, u}, bs}, fs, sp, pend, ps, c, u, v, xs, zs, hs, hac, ht))))

# M.inc: the parts of HSK, and the flag STATIC of c
def inc.top(+f: Nat, +dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +r: Nat,
  +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>, +c: U32, +u: Bk.Term,
  +xs: List<&2, D.TmpE>, +zs: List<&2, D.Rt>,
  hs: D.HSK(dk, ds, ks, img, m, nx, fi, im, os, Con{D.Rt{c, u}, bs}, fs, sp, pend, ps),
  hac: D.AccK(dk, ds, ks, img, m, nx, fi, im, os, xs, sp, fs, ps, zs),
  hn: N.Le(List.length(&2, D.Rt, os), 64n),
  hc: {List.get(&2, U32, regs, r) == Some{c} : Maybe<&2, U32>}) ->
  D.PostB(False{}, Cr.Cir.exec(f, Mc.M.inc(r), Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0}),
    st2 => D.Ex(Cr.Cir.Cells, m2 => D.P2({st2 == Cr.Cir.State{regs, m2, nx, fi, im, pg, lim, inp, Nil{}, 0} : Cr.Cir.State},
      D.P2(D.HSK(dk, ds, ks, img, m2, nx, fi, im, Con{D.Rt{c, u}, os}, Con{D.Rt{c, u}, bs}, fs, sp, pend, ps),
        D.AccK(dk, ds, ks, img, m2, nx, fi, im, Con{D.Rt{c, u}, os}, xs, sp, fs, ps, zs)))),
    s => st2 => Empty, 0n, lim):
  match hs:
    case Tuple{hos, Tuple{hbs, Tuple{hheld, Tuple{hfrs, Tuple{hheap, himg}}}}}:
      inc.go(D.Fl(m, c, 1024), f, dk, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, r, os, bs, fs, sp, pend, ps, c, u, xs, zs, {==},
        hos, hbs, hheld, hfrs, hheap, himg, hac, hn, hc)

# The laws
# --------

def D.inc.post(f, dk, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, r, os, bs, fs, sp, pend, ps, c, u, xs, zs, hs, hac, hn, hc):
  inc.top(f, dk, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, r, os, bs, fs, sp, pend, ps, c, u, xs, zs, hs, hac, hn, hc)

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

def D.term.post(dk, ds, ks, img, m, nx, fi, im, us, os, bs, fs, sp, pend, ps, z, x, t, xs, zs, hs, hac, ho, hm, hzs, hzt, hz0, hzf, hnt, hnh, hxs, hx1, hf, hi):
  ?TODO

def D.data.flag(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps, c, xs, zs, hs, hac, hd, hco):
  ?TODO
