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
      D.P2({D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m2, fi) == D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi) : Nat},
      D.P2(D.HSK(dk, ds, ks, img, m2, nx, fi, im, Con{D.Rt{c, u}, os}, Con{D.Rt{c, u}, bs}, fs, sp, pend, ps),
        D.AccK(dk, ds, ks, img, m2, nx, fi, im, Con{D.Rt{c, u}, os}, xs, sp, fs, ps, zs))))),
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
            D.P2({D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m2, fi) == D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi) : Nat},
            D.P2(D.HSK(dk, ds, ks, img, m2, nx, fi, im, Con{D.Rt{c, u}, os}, Con{D.Rt{c, u}, bs}, fs, sp, pend, ps),
              D.AccK(dk, ds, ks, img, m2, nx, fi, im, Con{D.Rt{c, u}, os}, xs, sp, fs, ps, zs))))),
          s => st2 => Empty, 0n, lim)
      (m, ({==}, ({==}, (inc.hs.s(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps, c, u, hos, hbs, hheld, hfrs, hheap, himg, hcd, eb),
        AC.acc.root(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps, c, u, xs, zs, hs, hac)))))
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
            D.P2({D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m2, fi) == D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi) : Nat},
            D.P2(D.HSK(dk, ds, ks, img, m2, nx, fi, im, Con{D.Rt{c, u}, os}, Con{D.Rt{c, u}, bs}, fs, sp, pend, ps),
              D.AccK(dk, ds, ks, img, m2, nx, fi, im, Con{D.Rt{c, u}, os}, xs, sp, fs, ps, zs))))),
          s => st2 => Empty, 0n, lim)
      (X.X.put(m, 1n, c, v), ({==}, (AC.stat.put1(n, [D.W1{c, v}], m, fi),
        ((%put1.one(m, c, v) : D.HSK(dk, ds, ks, img, _, nx, fi, im, Con{D.Rt{c, u}, os}, Con{D.Rt{c, u}, bs}, fs, sp, pend, ps); hsk),
          AC.acc.inc(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps, c, u, v, xs, zs, hs, hac, ht)))))

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
      D.P2({D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m2, fi) == D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi) : Nat},
      D.P2(D.HSK(dk, ds, ks, img, m2, nx, fi, im, Con{D.Rt{c, u}, os}, Con{D.Rt{c, u}, bs}, fs, sp, pend, ps),
        D.AccK(dk, ds, ks, img, m2, nx, fi, im, Con{D.Rt{c, u}, os}, xs, sp, fs, ps, zs))))),
    s => st2 => Empty, 0n, lim):
  match hs:
    case Tuple{hos, Tuple{hbs, Tuple{hheld, Tuple{hfrs, Tuple{hheap, himg}}}}}:
      inc.go(D.Fl(m, c, 1024), f, dk, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, r, os, bs, fs, sp, pend, ps, c, u, xs, zs, {==},
        hos, hbs, hheld, hfrs, hheap, himg, hac, hn, hc)

# The pend list
# -------------
#
# A cell z that joins the pend list holds the same pointers there (hfz: a
# term cell's parts, or none): so every cell keeps its pointers (Fs), and
# the counts of pointers (Pc, Ptr), the pointers' targets (Pts), the pend
# list's cells and the counts (Cnt) stay.

# the pointers of the cell o, by the three conditions of Fs: a term cell's
# parts, a frame's, an OWNED argument's
def FsT(a: Bool, x: Bool, y: Bool, +m: Cr.Cir.Cells, +o: U32) -> List<&2, U32>:
  +tg = D.TgW(D.Fd(0n, m, o))
  Bool.pick(List<&2, U32>, a, D.Fs.term(D.Fd(2n, m, U32.add(272, tg)), D.Fd(2n, m, o), D.Fd(3n, m, o), D.Fd(4n, m, o)),
    Bool.pick(List<&2, U32>, x, Con{D.Fd(2n, m, o), D.Fs.opt(U32.is_eq(tg, 38), D.Fd(3n, m, o), Nil{})},
      Bool.pick(List<&2, U32>, y, [D.Fd(2n, m, o)], Nil{})))

# no pointer, when no condition holds
def fst.nil(a: Bool, F: Bool, G: Bool, +m: Cr.Cir.Cells, +o: U32, ea: {a == False{} : Bool}) ->
  {FsT(a, Bool.and(F, False{}), Bool.and(G, False{}), m, o) == Nil{} : List<&2, U32>}:
  match a:
    case True{}:
      Empty.absurd({FsT(True{}, Bool.and(F, False{}), Bool.and(G, False{}), m, o) == Nil{} : List<&2, U32>}, N.true_ne_false(ea))
    case False{}:
      match F:
        case True{}:
          match G:
            case True{}:
              {==}
            case False{}:
              {==}
        case False{}:
          match G:
            case True{}:
              {==}
            case False{}:
              {==}

# the list is empty
def Lnil(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{_, _}:
      False{}

# a frame's condition gives a pointer
def fst.nn(a: Bool, x: Bool, +y: Bool, +m: Cr.Cir.Cells, +o: U32, ea: {a == False{} : Bool}, ex: {x == True{} : Bool},
  e: {FsT(a, x, y, m, o) == Nil{} : List<&2, U32>}) -> Empty:
  match a:
    case True{}:
      N.true_ne_false(ea)
    case False{}:
      match x:
        case True{}:
          N.false_ne_true(Equal.cong(List<&2, U32>, Bool, l => Lnil(l), FsT(False{}, True{}, y, m, o), Nil{}, e))
        case False{}:
          N.false_ne_true(ex)

# a cell of no term (a tag of 19 or more) in the pend list holds no pointer
def fs.pz(+m: Cr.Cir.Cells, +ps: List<&2, U32>, +z: U32, ht: {U32.is_lt(D.Tg(m, z), 19) == False{} : Bool}) ->
  {D.Fs(m, Con{z, ps}, z) == Nil{} : List<&2, U32>}:
  +tg = D.TgW(D.Fd(0n, m, z))
  +F = Bool.and(U32.is_le(32, tg), U32.is_le(tg, 40))
  +G = Bool.and(U32.is_eq(tg, 41), D.FlW(D.Fd(0n, m, z), 4096))
  %Equal.sym(Bool, U32.is_eq(z, z), True{}, D.u32.refl(z)) :
    {FsT(U32.is_lt(tg, 19), Bool.and(F, Bool.not(Bool.or(_, D.Mem(ps, z)))), Bool.and(G, Bool.not(Bool.or(_, D.Mem(ps, z)))), m, z) == Nil{} : List<&2, U32>}
  fst.nil(U32.is_lt(tg, 19), F, G, m, z, ht)

# a cell of no term, out of the pend list, that holds no pointer has no
# frame's tag (a frame holds one)
def nf.z.b(b: Bool, +m: Cr.Cir.Cells, +ps: List<&2, U32>, +z: U32,
  eb: {Bool.and(U32.is_le(32, D.Tg(m, z)), U32.is_le(D.Tg(m, z), 40)) == b : Bool},
  ht: {U32.is_lt(D.Tg(m, z), 19) == False{} : Bool}, hm: {D.Mem(ps, z) == False{} : Bool},
  hfs: {D.Fs(m, ps, z) == Nil{} : List<&2, U32>}) ->
  {Bool.not(Bool.and(U32.is_le(32, D.Tg(m, z)), U32.is_le(D.Tg(m, z), 40))) == True{} : Bool}:
  match b:
    case False{}:
      %Equal.sym(Bool, Bool.and(U32.is_le(32, D.Tg(m, z)), U32.is_le(D.Tg(m, z), 40)), False{}, eb) : {Bool.not(_) == True{} : Bool}
      {==}
    case True{}:
      +tg = D.TgW(D.Fd(0n, m, z))
      +F = Bool.and(U32.is_le(32, tg), U32.is_le(tg, 40))
      +G = Bool.and(U32.is_eq(tg, 41), D.FlW(D.Fd(0n, m, z), 4096))
      +hx = D.and.i(F, Bool.not(D.Mem(ps, z)), eb, (%Equal.sym(Bool, D.Mem(ps, z), False{}, hm) : {Bool.not(_) == True{} : Bool}; {==}))
      Empty.absurd({Bool.not(F) == True{} : Bool},
        fst.nn(U32.is_lt(tg, 19), Bool.and(F, Bool.not(D.Mem(ps, z))), Bool.and(G, Bool.not(D.Mem(ps, z))), m, z, ht, hx, hfs))

def nf.z(+m: Cr.Cir.Cells, +ps: List<&2, U32>, +z: U32, ht: {U32.is_lt(D.Tg(m, z), 19) == False{} : Bool},
  hm: {D.Mem(ps, z) == False{} : Bool}, hfs: {D.Fs(m, ps, z) == Nil{} : List<&2, U32>}) ->
  {Bool.not(Bool.and(U32.is_le(32, D.Tg(m, z)), U32.is_le(D.Tg(m, z), 40))) == True{} : Bool}:
  nf.z.b(Bool.and(U32.is_le(32, D.Tg(m, z)), U32.is_le(D.Tg(m, z), 40)), m, ps, z, {==}, ht, hm, hfs)

# with z in the pend list, holding the same pointers there, every cell keeps
# its pointers
def fs.pcons.b(b: Bool, +m: Cr.Cir.Cells, +ps: List<&2, U32>, +z: U32, +o: U32, eb: {U32.is_eq(z, o) == b : Bool},
  hfz: {D.Fs(m, Con{z, ps}, z) == D.Fs(m, ps, z) : List<&2, U32>}) -> {D.Fs(m, Con{z, ps}, o) == D.Fs(m, ps, o) : List<&2, U32>}:
  match b:
    case True{}:
      %D.u32.eq(z, o, eb) : {D.Fs(m, Con{z, ps}, _) == D.Fs(m, ps, _) : List<&2, U32>}
      hfz
    case False{}:
      +tg = D.TgW(D.Fd(0n, m, o))
      +F = Bool.and(U32.is_le(32, tg), U32.is_le(tg, 40))
      +G = Bool.and(U32.is_eq(tg, 41), D.FlW(D.Fd(0n, m, o), 4096))
      %Equal.sym(Bool, U32.is_eq(z, o), False{}, eb) :
        {FsT(U32.is_lt(tg, 19), Bool.and(F, Bool.not(Bool.or(_, D.Mem(ps, o)))), Bool.and(G, Bool.not(Bool.or(_, D.Mem(ps, o)))), m, o) ==
          D.Fs(m, ps, o) : List<&2, U32>}
      {==}

def fs.pcons(+m: Cr.Cir.Cells, +ps: List<&2, U32>, +z: U32, +o: U32, hfz: {D.Fs(m, Con{z, ps}, z) == D.Fs(m, ps, z) : List<&2, U32>}) ->
  {D.Fs(m, Con{z, ps}, o) == D.Fs(m, ps, o) : List<&2, U32>}:
  fs.pcons.b(U32.is_eq(z, o), m, ps, z, o, {==}, hfz)

def pc.pcons(n: Nat, +m: Cr.Cir.Cells, +ps: List<&2, U32>, +z: U32, +o: U32, +c: U32,
  +hfz: {D.Fs(m, Con{z, ps}, z) == D.Fs(m, ps, z) : List<&2, U32>}) -> {D.Pc(n, m, Con{z, ps}, o, c) == D.Pc(n, m, ps, o, c) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+(+k):
      %Equal.sym(List<&2, U32>, D.Fs(m, Con{z, ps}, o), D.Fs(m, ps, o), fs.pcons(m, ps, z, o, hfz)) :
        {Nat.add(D.RcL(_, c), D.Pc(k, m, Con{z, ps}, U32.inc(o), c)) == D.Pc(1n+k, m, ps, o, c) : Nat}
      %Equal.sym(Nat, D.Pc(k, m, Con{z, ps}, U32.inc(o), c), D.Pc(k, m, ps, U32.inc(o), c), pc.pcons(k, m, ps, z, U32.inc(o), c, hfz)) :
        {Nat.add(D.RcL(D.Fs(m, ps, o), c), _) == D.Pc(1n+k, m, ps, o, c) : Nat}
      {==}

def ptr.pcons(+n: Nat, +m: Cr.Cir.Cells, +fi: U32, +ps: List<&2, U32>, +rs: List<&2, U32>, +z: U32, +c: U32,
  hfz: {D.Fs(m, Con{z, ps}, z) == D.Fs(m, ps, z) : List<&2, U32>}) ->
  {D.Ptr(n, m, fi, Con{z, ps}, rs, c) == D.Ptr(n, m, fi, ps, rs, c) : Nat}:
  Equal.cong(Nat, Nat, w => Nat.add(w, D.RcL(rs, c)), D.Pc(n, m, Con{z, ps}, fi, c), D.Pc(n, m, ps, fi, c), pc.pcons(n, m, ps, z, fi, c, hfz))

def pts.pcons(n: Nat, +m: Cr.Cir.Cells, +ps: List<&2, U32>, +z: U32, +o: U32, +im: U32, +fi: U32, +nx: U32,
  +hfz: {D.Fs(m, Con{z, ps}, z) == D.Fs(m, ps, z) : List<&2, U32>}) ->
  {D.Pts(n, m, Con{z, ps}, o, im, fi, nx) == D.Pts(n, m, ps, o, im, fi, nx) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+(+k):
      %Equal.sym(List<&2, U32>, D.Fs(m, Con{z, ps}, o), D.Fs(m, ps, o), fs.pcons(m, ps, z, o, hfz)) :
        {Bool.and(D.Lt.all(_, m, im, fi, nx), D.Pts(k, m, Con{z, ps}, U32.inc(o), im, fi, nx)) == D.Pts(1n+k, m, ps, o, im, fi, nx) : Bool}
      %Equal.sym(Bool, D.Pts(k, m, Con{z, ps}, U32.inc(o), im, fi, nx), D.Pts(k, m, ps, U32.inc(o), im, fi, nx),
          pts.pcons(k, m, ps, z, U32.inc(o), im, fi, nx, hfz)) :
        {Bool.and(D.Lt.all(D.Fs(m, ps, o), m, im, fi, nx), _) == D.Pts(1n+k, m, ps, o, im, fi, nx) : Bool}
      {==}

def pendok.pcons(qs: List<&2, U32>, +ps: List<&2, U32>, +m: Cr.Cir.Cells, +fi: U32, +nx: U32, +rs: List<&2, U32>, +z: U32,
  +hfz: {D.Fs(m, Con{z, ps}, z) == D.Fs(m, ps, z) : List<&2, U32>}, h: D.PendOK(qs, ps, m, fi, nx, rs)) ->
  D.PendOK(qs, Con{z, ps}, m, fi, nx, rs):
  match qs:
    case Nil{}:
      Unit{}
    case Con{+p, +rest}:
      (ho, r1) = h
      (hs, r2) = r1
      (htg, r3) = r2
      (hp0, r4) = r3
      +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
      (ho, (hs, (htg, ((%Equal.sym(Nat, D.Ptr(n, m, fi, Con{z, ps}, rs, p), D.Ptr(n, m, fi, ps, rs, p), ptr.pcons(n, m, fi, ps, rs, z, p, hfz)) :
          {_ == 0n : Nat}; hp0),
        pendok.pcons(rest, ps, m, fi, nx, rs, z, hfz, r4)))))

# a or (b or (x or c)) gives a or (b or ((e or x) or c))
def or.wk(a: Bool, b: Bool, e: Bool, -x: Bool, -c: Bool, h: {Bool.or(a, Bool.or(b, Bool.or(x, c))) == True{} : Bool}) ->
  {Bool.or(a, Bool.or(b, Bool.or(Bool.or(e, x), c))) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      match b:
        case True{}:
          {==}
        case False{}:
          match e:
            case True{}:
              {==}
            case False{}:
              h

def cntc.pcons(+m: Cr.Cir.Cells, +q: U32, +N: Nat, +fi: U32, +ps: List<&2, U32>, +rs: List<&2, U32>, +z: U32,
  hfz: {D.Fs(m, Con{z, ps}, z) == D.Fs(m, ps, z) : List<&2, U32>},
  h: {D.CntC(Cr.Cir.Cells.get(m, q), D.Ptr(N, m, fi, ps, rs, q), ps, q) == True{} : Bool}) ->
  {D.CntC(Cr.Cir.Cells.get(m, q), D.Ptr(N, m, fi, Con{z, ps}, rs, q), Con{z, ps}, q) == True{} : Bool}:
  %Equal.sym(Nat, D.Ptr(N, m, fi, Con{z, ps}, rs, q), D.Ptr(N, m, fi, ps, rs, q), ptr.pcons(N, m, fi, ps, rs, z, q, hfz)) :
    {D.CntC(Cr.Cir.Cells.get(m, q), _, Con{z, ps}, q) == True{} : Bool}
  or.wk(Bool.not(U32.is_lt(D.Tg(m, q), 19)), D.Fl(m, q, 1024), U32.is_eq(z, q), D.Mem(ps, q),
    Nat.is_eq(U32.to_nat(D.Fd(1n, m, q)), D.Ptr(N, m, fi, ps, rs, q)), h)

def cnt.pcons(k: Nat, +m: Cr.Cir.Cells, +o: U32, +N: Nat, +fi: U32, +ps: List<&2, U32>, +rs: List<&2, U32>, +z: U32,
  +hfz: {D.Fs(m, Con{z, ps}, z) == D.Fs(m, ps, z) : List<&2, U32>}, h: {D.Cnt(k, m, o, N, fi, ps, rs) == True{} : Bool}) ->
  {D.Cnt(k, m, o, N, fi, Con{z, ps}, rs) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+(+j):
      +h2 = h
      D.and.i(D.CntC(Cr.Cir.Cells.get(m, o), D.Ptr(N, m, fi, Con{z, ps}, rs, o), Con{z, ps}, o), D.Cnt(j, m, U32.inc(o), N, fi, Con{z, ps}, rs),
        cntc.pcons(m, o, N, fi, ps, rs, z, hfz,
          D.and.l(D.CntC(Cr.Cir.Cells.get(m, o), D.Ptr(N, m, fi, ps, rs, o), ps, o), D.Cnt(j, m, U32.inc(o), N, fi, ps, rs), h2)),
        cnt.pcons(j, m, U32.inc(o), N, fi, ps, rs, z, hfz,
          D.and.r(D.CntC(Cr.Cir.Cells.get(m, o), D.Ptr(N, m, fi, ps, rs, o), ps, o), D.Cnt(j, m, U32.inc(o), N, fi, ps, rs), h2)))

# with z, of no frame's tag, in the pend list, the frames stay
def frsk.pcons(+dk: Bool, fs: List<&2, D.AF>, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +z: U32, +fr: U32,
  +hq: {Bool.not(Bool.and(U32.is_le(32, D.Tg(m, z)), U32.is_le(D.Tg(m, z), 40))) == True{} : Bool},
  h: D.FrsK(dk, ds, m, im, fi, nx, ks, img, ps, fr, fs)) -> D.FrsK(dk, ds, m, im, fi, nx, ks, img, Con{z, ps}, fr, fs):
  match fs:
    case Nil{}:
      h
    case Con{D.AF{+kind, +q, +k, +a, +b}, +rest}:
      match h:
        case Tuple{e0, Tuple{ev, Tuple{eo, Tuple{es, Tuple{em, Tuple{+etg, Tuple{eq, Tuple{ek, Tuple{ia, Tuple{ib, ir}}}}}}}}}}:
          +ne = ne.frame(U32.is_eq(z, fr), m, z, fr, kind, {==}, etg, hq)
          (e0, (ev, (eo, (es, ((%Equal.sym(Bool, U32.is_eq(z, fr), False{}, ne) : {Bool.or(_, D.Mem(ps, fr)) == False{} : Bool}; em),
            (etg, (eq, (ek, (ia, (ib, frsk.pcons(dk, rest, ds, m, im, fi, nx, ks, img, ps, z, D.Fd(1n, m, fr), hq, ir)))))))))))

# No pointer to a cell of no term
# ------------------------------
#
# A pointer goes to a term cell (Pts, LtC), and an owned root is a term's
# cell: so a cell of a tag of 19 or more has no pointer.

# a <= b, from their numbers
def le.of.rel(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), h: N.Le(x, y)) -> {Cmp.is_le(c) == True{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({Cmp.is_le(GT{}) == True{} : Bool}, N.not_succ_le(y, N.le_trans(1n+y, x, y, r, h)))

def u.le.of(+a: U32, +b: U32, h: N.Le(U32.to_nat(a), U32.to_nat(b))) -> {U32.is_le(a, b) == True{} : Bool}:
  le.of.rel(U32.cmp(a, b), U32.to_nat(a), U32.to_nat(b), N.U32.rel(a, b), h)

# not a < b: b <= a, in numbers
def ge.rel(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), h: {Cmp.is_lt(c) == False{} : Bool}) -> N.Le(y, x):
  match c:
    case LT{}:
      Empty.absurd(N.Le(y, x), N.true_ne_false(h))
    case EQ{}:
      %r : N.Le(_, x)
      N.le_refl(x)
    case GT{}:
      N.weaken(y, x, r)

def u.ge(+a: U32, +b: U32, h: {U32.is_lt(a, b) == False{} : Bool}) -> N.Le(U32.to_nat(b), U32.to_nat(a)):
  ge.rel(U32.cmp(a, b), U32.to_nat(a), U32.to_nat(b), N.U32.rel(a, b), h)

# a tag of 32 or more is not below 19
def lt19.of(b: Bool, +tg: U32, eb: {U32.is_lt(tg, 19) == b : Bool}, h: {U32.is_lt(tg, 32) == False{} : Bool}) ->
  {U32.is_lt(tg, 19) == False{} : Bool}:
  match b:
    case False{}:
      eb
    case True{}:
      Empty.absurd({U32.is_lt(tg, 19) == False{} : Bool},
        N.le_trans(U32.to_nat(32), U32.to_nat(tg), U32.to_nat(19), u.ge(tg, 32, h), N.weaken(U32.to_nat(tg), U32.to_nat(19), D.u.lt(tg, 19, eb))))

# a term cell c is not z, a cell of no term
def ne.t19(b: Bool, +m: Cr.Cir.Cells, +c: U32, +z: U32, eb: {U32.is_eq(c, z) == b : Bool},
  ht: {U32.is_lt(D.Tg(m, z), 19) == False{} : Bool}, hc: {U32.is_lt(D.Tg(m, c), 19) == True{} : Bool}) ->
  {U32.is_eq(c, z) == False{} : Bool}:
  match b:
    case False{}:
      eb
    case True{}:
      Empty.absurd({U32.is_eq(c, z) == False{} : Bool},
        N.false_ne_true((%ht : {_ == True{} : Bool}; (%D.u32.eq(c, z, eb) : {U32.is_lt(D.Tg(m, _), 19) == True{} : Bool}; hc))))

# no pointer of xs, each to a term cell, is z
def rcl.lt(xs: List<&2, U32>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +z: U32,
  +ht: {U32.is_lt(D.Tg(m, z), 19) == False{} : Bool}, h: {D.Lt.all(xs, m, im, fi, nx) == True{} : Bool}) ->
  {D.RcL(xs, z) == 0n : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      +h2 = h
      +ly = D.and.l(D.LtC(y, Cr.Cir.Cells.get(m, y), im, fi, nx), D.Lt.all(rest, m, im, fi, nx), h2)
      +ty = D.and.r(U32.is_lt(y, nx), U32.is_lt(D.Tg(m, y), 19),
        D.and.l(Bool.and(U32.is_lt(y, nx), U32.is_lt(D.Tg(m, y), 19)),
          Bool.and(Cr.Cir.is_cell(y, im, fi, nx), Bool.or(D.Own(fi, nx, y), D.Fl(m, y, 1024))), ly))
      +ne = ne.t19(U32.is_eq(y, z), m, y, z, {==}, ht, ty)
      %Equal.sym(Bool, U32.is_eq(y, z), False{}, ne) : {Nat.add(D.Nat.of(_), D.RcL(rest, z)) == 0n : Nat}
      rcl.lt(rest, m, im, fi, nx, z, ht, D.and.r(D.LtC(y, Cr.Cir.Cells.get(m, y), im, fi, nx), D.Lt.all(rest, m, im, fi, nx), h2))

# no cell points to z
def pc.none(n: Nat, +m: Cr.Cir.Cells, +ps: List<&2, U32>, +o: U32, +z: U32, +im: U32, +fi: U32, +nx: U32,
  +ht: {U32.is_lt(D.Tg(m, z), 19) == False{} : Bool}, h: {D.Pts(n, m, ps, o, im, fi, nx) == True{} : Bool}) ->
  {D.Pc(n, m, ps, o, z) == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+(+k):
      +h2 = h
      %Equal.sym(Nat, D.RcL(D.Fs(m, ps, o), z), 0n, rcl.lt(D.Fs(m, ps, o), m, im, fi, nx, z, ht,
          D.and.l(D.Lt.all(D.Fs(m, ps, o), m, im, fi, nx), D.Pts(k, m, ps, U32.inc(o), im, fi, nx), h2))) :
        {Nat.add(_, D.Pc(k, m, ps, U32.inc(o), z)) == 0n : Nat}
      pc.none(k, m, ps, U32.inc(o), z, im, fi, nx, ht, D.and.r(D.Lt.all(D.Fs(m, ps, o), m, im, fi, nx), D.Pts(k, m, ps, U32.inc(o), im, fi, nx), h2))

# no owned root is z
def rcl.roots(+dk: Bool, os: List<&2, D.Rt>, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +z: U32, +ht: {U32.is_lt(D.Tg(m, z), 19) == False{} : Bool},
  h: D.RtsK(dk, ds, m, im, fi, nx, ks, img, os)) -> {D.RcL(D.Rt.cells(os), z) == 0n : Nat}:
  match os:
    case Nil{}:
      {==}
    case Con{D.Rt{+c, +u}, +rest}:
      match h:
        case Tuple{hu, hr}:
          +nd = isk.nd(dk, u, ds, m, im, fi, nx, ks, img, c, hu)
          +et = {D.nd.tgk(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), u, D.A.tag(u), nd) : {D.Tg(m, c) == D.A.tag(u) : U32}}
          +hc19 = {(%Equal.sym(U32, D.Tg(m, c), D.A.tag(u), et) : {U32.is_lt(_, 19) == True{} : Bool}; atag.lt(u)) :
            {U32.is_lt(D.Tg(m, c), 19) == True{} : Bool}}
          +ne = ne.t19(U32.is_eq(c, z), m, c, z, {==}, ht, hc19)
          %Equal.sym(Bool, U32.is_eq(c, z), False{}, ne) : {Nat.add(D.Nat.of(_), D.RcL(D.Rt.cells(rest), z)) == 0n : Nat}
          rcl.roots(dk, rest, ds, m, im, fi, nx, ks, img, z, ht, hr)

# M.release
# ---------
#
# M.release(r) of a cell z of the machine's own kinds (tag 32 and up), out of
# the pend list, holding no pointer: field 1 of z gets the old pend, and pend
# gets z. Nothing points to z, z holds no pointer in the pend list either and
# is no frame, so HSK holds with z first in the pend list.

# one of the machine's own cells is a cell
def own.cell(+c: U32, +im: U32, +fi: U32, +nx: U32, h: {D.Own(fi, nx, c) == True{} : Bool}) ->
  {Cr.Cir.is_cell(c, im, fi, nx) == True{} : Bool}:
  D.or.r(Bool.and(Bool.not(U32.is_zero(c)), U32.is_le(c, im)), D.Own(fi, nx, c), h)

# the run of M.release(r): field 1 of z gets pend, and pend gets z
def rel.eq(+f: Nat, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32,
  +inp: List<&2, Word(8n)>, +r: Nat, +z: U32, +pend: U32, +hl: {List.length(&2, U32, regs) == 63n : Nat},
  +hc: {List.get(&2, U32, regs, r) == Some{z} : Maybe<&2, U32>}, +hp: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>},
  +hcell: {Cr.Cir.is_cell(z, im, fi, nx) == True{} : Bool}) ->
  {Cr.Cir.exec(f, Mc.M.release(r), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) ==
    Cr.Cir.Out.next{X.X.st(X.X.set(regs, 3n, z), X.X.put(m, 1n, z, pend), nx, fi, im, pg, lim, inp)} : Cr.Cir.Out}:
  +s0 = X.X.st(regs, m, nx, fi, im, pg, lim, inp)
  +m1 = X.X.put(m, 1n, z, pend)
  +s1 = X.X.st(regs, m1, nx, fi, im, pg, lim, inp)
  +s2 = X.X.st(X.X.set(regs, 3n, z), m1, nx, fi, im, pg, lim, inp)
  +rl = Mc.M.release(r)
  +rhs = {Cr.Cir.Out.next{s2} : Cr.Cir.Out}
  %X.rw.seq(f, X.sel.a(rl), X.sel.b(rl), s0, s1, X.run.store(f, 1n, Mc.M.g(r), Mc.M.g(3n), s0, z, pend, hc, hp, hcell)) :
    {_ == rhs : Cr.Cir.Out}
  %X.rw.seq(f, X.sel.a(X.sel.b(rl)), X.sel.b(X.sel.b(rl)), s1, s2, X.run.set(f, 3n, Mc.M.g(r), s1, z, hc, hl, {==})) :
    {_ == rhs : Cr.Cir.Out}
  X.run.nop(f, s2)

# HSK after M.release of z: z heads the pend list, linked to the old pend
def rel.hs(+dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32,
  +ps: List<&2, U32>, +z: U32, hs: D.HSK(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps),
  +hz: {D.Own(fi, nx, z) == True{} : Bool}, +ht: {U32.is_lt(D.Tg(m, z), 32) == False{} : Bool},
  +hf: {D.Fl(m, z, 1024) == False{} : Bool}, +hm: {D.Mem(ps, z) == False{} : Bool},
  +hfs: {D.Fs(m, ps, z) == Nil{} : List<&2, U32>}) ->
  D.HSK(dk, ds, ks, img, D.Put1([D.W1{z, pend}], m), nx, fi, im, os, bs, fs, sp, z, Con{z, ps}):
  match hs:
    case Tuple{hos0, Tuple{hbs, Tuple{hheld, Tuple{hfrs, Tuple{hheap, himg0}}}}}:
      match hheap:
        case Tuple{hch, Tuple{hpk, Tuple{hcnt, Tuple{hpts0, hr}}}}:
          +hos = {hos0 : D.RtsK(dk, ds, m, im, fi, nx, ks, img, os)}
          +himg = {himg0 : D.ImgOKK(dk, ds, ks, img, m, im, fi, nx)}
          +hpts = {hpts0 : {D.Pts(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, ps, fi, im, fi, nx) == True{} : Bool}}
          +ws = {[D.W1{z, pend}] : List<&2, D.W1>}
          +M2 = D.Put1(ws, m)
          +rs = D.Rt.cells(os)
          +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
          +Y = Cr.Cir.Cells.get(m, z)
          +x = Cr.Cir.Cell.set(1n, Y, pend)
          +ht19 = lt19.of(U32.is_lt(D.Tg(m, z), 19), D.Tg(m, z), {==}, ht)
          +hpz = fs.pz(m, ps, z, ht19)
          +hfz = Equal.trans(List<&2, U32>, D.Fs(m, Con{z, ps}, z), Nil{}, D.Fs(m, ps, z), hpz, Equal.sym(List<&2, U32>, D.Fs(m, ps, z), Nil{}, hfs))
          +hnf = nf.z(m, ps, z, ht19, hm, hfs)
          +e0 = D.put1.f0(ws, m, z)
          +hz0 = cell.nz(z, im, fi, nx, own.cell(z, im, fi, nx, hz), img.lt(dk, ds, ks, img, m, im, fi, nx, himg))
          +e1 = Equal.trans(U32, D.Fd(1n, M2, z), Cr.Cir.Cell.get(1n, x), pend,
            Equal.cong(Cr.Cir.Cell, U32, w => Cr.Cir.Cell.get(1n, w), Cr.Cir.Cells.get(M2, z), x, D.cl.gs(m, z, x)), D.cg1(Y, pend))
          +hp0 = {(%Equal.sym(Nat, D.Pc(n, m, ps, fi, z), 0n, pc.none(n, m, ps, fi, z, im, fi, nx, ht19, hpts)) :
              {Nat.add(_, D.RcL(rs, z)) == 0n : Nat};
            rcl.roots(dk, os, ds, m, im, fi, nx, ks, img, z, ht19, hos)) : {D.Ptr(n, m, fi, ps, rs, z) == 0n : Nat}}
          +hpz0 = Equal.trans(Nat, D.Ptr(n, M2, fi, Con{z, ps}, rs, z), D.Ptr(n, m, fi, Con{z, ps}, rs, z), 0n,
            D.ptr.put1(n, ws, m, fi, Con{z, ps}, rs, z),
            Equal.trans(Nat, D.Ptr(n, m, fi, Con{z, ps}, rs, z), D.Ptr(n, m, fi, ps, rs, z), 0n, ptr.pcons(n, m, fi, ps, rs, z, z, hfz), hp0))
          +hxt = {(%Equal.sym(U32, Cr.Cir.Cell.get(0n, x), Cr.Cir.Cell.get(0n, Y), D.cg0(Y, pend)) : {U32.is_lt(D.TgW(_), 19) == False{} : Bool}; ht19) :
            {U32.is_lt(D.TgW(Cr.Cir.Cell.get(0n, x)), 19) == False{} : Bool}}
          +hf1 = Equal.trans(List<&2, U32>, D.Fs(M2, Con{z, ps}, z), D.Fs(m, Con{z, ps}, z), Nil{}, D.fs.put1(ws, m, Con{z, ps}, z), hpz)
          +htN = D.TblR.of(n, m, fi, z, D.img.hz(dk, ds, ks, img, m, im, fi, nx, z, himg, hz))
          +hcnt2 = D.Cnt.fz(n, m, z, x, fi, n, fi, Con{z, ps}, rs, hpz, hf1, htN, hxt, cnt.pcons(n, m, fi, n, fi, ps, rs, z, hfz, hcnt))
          +hpts2 = {(%Equal.sym(Bool, D.Pts(n, M2, Con{z, ps}, fi, im, fi, nx), D.Pts(n, m, Con{z, ps}, fi, im, fi, nx),
                D.pts.put1(n, ws, m, Con{z, ps}, fi, im, fi, nx)) : {_ == True{} : Bool};
              (%Equal.sym(Bool, D.Pts(n, m, Con{z, ps}, fi, im, fi, nx), D.Pts(n, m, ps, fi, im, fi, nx), pts.pcons(n, m, ps, z, fi, im, fi, nx, hfz)) :
                  {_ == True{} : Bool};
                hpts)) : {D.Pts(n, M2, Con{z, ps}, fi, im, fi, nx) == True{} : Bool}}
          +hpk2 = {(hz, ((%Equal.sym(U32, D.Fd(0n, M2, z), D.Fd(0n, m, z), e0) : {U32.is_ne(U32.and(_, 1024), 0) == False{} : Bool}; hf),
              ((%Equal.sym(U32, D.Fd(0n, M2, z), D.Fd(0n, m, z), e0) :
                  {Bool.or(U32.is_lt(U32.and(_, 63), 19), U32.is_le(32, U32.and(_, 63))) == True{} : Bool};
                D.or.r(U32.is_lt(D.Tg(m, z), 19), U32.is_le(32, D.Tg(m, z)), u.le.of(32, D.Tg(m, z), u.ge(D.Tg(m, z), 32, ht)))),
              (hpz0, D.pendok.put1(ps, Con{z, ps}, ws, m, fi, nx, rs, pendok.pcons(ps, ps, m, fi, nx, rs, z, hfz, hpk)))))) :
            D.PendOK(Con{z, ps}, Con{z, ps}, M2, fi, nx, rs)}
          +hch2 = {({==}, (hz0, (%Equal.sym(U32, D.Fd(1n, M2, z), pend, e1) : D.Chain(ps, M2, _);
              chain.p1(ps, ws, m, pend, out.one(ps, z, hm), hch)))) : D.Chain(Con{z, ps}, M2, z)}
          (rtsk.p1(dk, os, ds, m, im, fi, nx, ks, img, ws, hos),
            (rtsk.p1(dk, bs, ds, m, im, fi, nx, ks, img, ws, hbs),
            (held.p1(bs, os, ws, m, hheld),
            (frsk.p1(dk, fs, ds, m, im, fi, nx, ks, img, Con{z, ps}, ws, sp,
                D.and.i(Bool.not(Bool.and(U32.is_le(32, D.Tg(m, z)), U32.is_le(D.Tg(m, z), 40))), True{}, hnf, {==}),
                frsk.pcons(dk, fs, ds, m, im, fi, nx, ks, img, ps, z, sp, hnf, hfrs)),
            ((hch2, (hpk2, (hcnt2, (hpts2, hr)))),
              imgokk.p1(dk, ds, ks, img, m, im, fi, nx, ws, gt.one(dk, ds, ks, img, m, im, fi, nx, z, pend, himg, hz), himg))))))

# M.release: the run, the STATIC cells (field 1 only), HSK and AccK
def rel.go(+f: Nat, +dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +r: Nat,
  +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>, +z: U32,
  +xs: List<&2, D.TmpE>, +zs: List<&2, D.Rt>,
  hs: D.HSK(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps),
  hac: D.AccK(dk, ds, ks, img, m, nx, fi, im, os, Con{D.TmpE{z, Nil{}}, xs}, sp, fs, ps, zs),
  +hz: {D.Own(fi, nx, z) == True{} : Bool}, +ht: {U32.is_lt(D.Tg(m, z), 32) == False{} : Bool},
  +hf: {D.Fl(m, z, 1024) == False{} : Bool}, +hm: {D.Mem(ps, z) == False{} : Bool},
  +hfs: {D.Fs(m, ps, z) == Nil{} : List<&2, U32>}, +hl: {List.length(&2, U32, regs) == 63n : Nat},
  +hc: {List.get(&2, U32, regs, r) == Some{z} : Maybe<&2, U32>}, +hp: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>}) ->
  D.PostB(False{}, Cr.Cir.exec(f, Mc.M.release(r), Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0}),
    st2 => D.Ex(Cr.Cir.Cells, m2 => D.P2({st2 == Cr.Cir.State{List.set(&2, U32, regs, 3n, z), m2, nx, fi, im, pg, lim, inp, Nil{}, 0} : Cr.Cir.State},
      D.P2({D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m2, fi) == D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi) : Nat},
      D.P2(D.HSK(dk, ds, ks, img, m2, nx, fi, im, os, bs, fs, sp, z, Con{z, ps}),
        D.AccK(dk, ds, ks, img, m2, nx, fi, im, os, xs, sp, fs, Con{z, ps}, zs))))),
    s => st2 => Empty, 0n, lim):
  +h2 = hs
  +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, Mc.M.release(r), Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0}),
      Cr.Cir.Out.next{X.X.st(X.X.set(regs, 3n, z), X.X.put(m, 1n, z, pend), nx, fi, im, pg, lim, inp)},
      rel.eq(f, regs, m, nx, fi, im, pg, lim, inp, r, z, pend, hl, hc, hp, own.cell(z, im, fi, nx, hz))) :
    D.PostB(False{}, _,
      st2 => D.Ex(Cr.Cir.Cells, m2 => D.P2({st2 == Cr.Cir.State{List.set(&2, U32, regs, 3n, z), m2, nx, fi, im, pg, lim, inp, Nil{}, 0} : Cr.Cir.State},
        D.P2({D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m2, fi) == D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi) : Nat},
        D.P2(D.HSK(dk, ds, ks, img, m2, nx, fi, im, os, bs, fs, sp, z, Con{z, ps}),
          D.AccK(dk, ds, ks, img, m2, nx, fi, im, os, xs, sp, fs, Con{z, ps}, zs))))),
      s => st2 => Empty, 0n, lim)
  (X.X.put(m, 1n, z, pend), ({==}, (AC.stat.put1(n, [D.W1{z, pend}], m, fi),
    ((%put1.one(m, z, pend) : D.HSK(dk, ds, ks, img, _, nx, fi, im, os, bs, fs, sp, z, Con{z, ps});
        rel.hs(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps, z, h2, hz, ht, hf, hm, hfs)),
      AC.acc.release(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps, z, xs, zs, h2, hac, ht, hm, hfs)))))

# M.dec
# -----
#
# M.dec of an owned root c: a STATIC c changes no cell and leaves the
# roots; else its count, one more than its pointers without that root,
# drops by one, and at 0 c heads the pend list (a term cell there holds the
# same parts). Every other cell keeps its count.

# the number before n
def pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

# 1 + a = 1 + b gives a = b
def succ.inj(-a: Nat, -b: Nat, e: {1n+a == 1n+b : Nat}) -> {a == b : Nat}:
  Equal.cong(Nat, Nat, z => pred(z), 1n+a, 1n+b, e)

# 1 <= 2 x gives 1 <= x
def le1.dbl(x: Nat, h: N.Le(1n, Nat.double(x))) -> N.Le(1n, x):
  match x:
    case 0n:
      Empty.absurd(N.Le(1n, 0n), h)
    case 1n+k:
      N.le_zero(k)

# adding all ones and a carry leaves a word as it was
def w.s1(+n: Nat, +t: Word(n)) -> {Word.adc(n, t, Word.zero(n), True{}, True{}) == t : Word(n)}:
  match n:
    case 0n:
      match t:
        case WNil{}:
          {==}
    case 1n+p:
      match t:
        case WCon{False{}, +r}:
          Equal.cong(Word(p), Word(1n+p), z => WCon{False{}, z}, Word.adc(p, r, Word.zero(p), True{}, True{}), r, w.s1(p, r))
        case WCon{True{}, +r}:
          Equal.cong(Word(p), Word(1n+p), z => WCon{True{}, z}, Word.adc(p, r, Word.zero(p), True{}, True{}), r, w.s1(p, r))

# adding all ones (t - 1) gives one less than t, for t not 0
def w.dec(+n: Nat, +t: Word(n), h: N.Le(1n, Word.to_nat(n, t))) ->
  {1n+Word.to_nat(n, Word.adc(n, t, Word.zero(n), True{}, False{})) == Word.to_nat(n, t) : Nat}:
  match n:
    case 0n:
      match t:
        case WNil{}:
          Empty.absurd({1n+Word.to_nat(0n, Word.adc(0n, WNil{}, Word.zero(0n), True{}, False{})) == Word.to_nat(0n, WNil{}) : Nat}, h)
    case 1n+p:
      match t:
        case WCon{False{}, +r}:
          Equal.cong(Nat, Nat, z => Nat.double(z), 1n+Word.to_nat(p, Word.adc(p, r, Word.zero(p), True{}, False{})), Word.to_nat(p, r),
            w.dec(p, r, le1.dbl(Word.to_nat(p, r), h)))
        case WCon{True{}, +r}:
          Equal.cong(Word(p), Nat, z => 1n+Nat.double(Word.to_nat(p, z)), Word.adc(p, r, Word.zero(p), True{}, True{}), r, w.s1(p, r))

# x - 1 is one less than x, for x not 0
def u32.dec(+x: U32, h: N.Le(1n, U32.to_nat(x))) -> {1n+U32.to_nat(U32.sub(x, 1)) == U32.to_nat(x) : Nat}:
  match x:
    case U32{+w}:
      match w:
        case WCon{False{}, +r}:
          Equal.cong(Nat, Nat, z => Nat.double(z), 1n+Word.to_nat(31n, Word.adc(31n, r, Word.zero(31n), True{}, False{})), Word.to_nat(31n, r),
            w.dec(31n, r, le1.dbl(Word.to_nat(31n, r), h)))
        case WCon{True{}, +r}:
          Equal.cong(Word(31n), Nat, z => 1n+Nat.double(Word.to_nat(31n, z)), Word.adc(31n, r, Word.zero(31n), True{}, True{}), r, w.s1(31n, r))

# a number that a comparison finds not equal to 0 is above 0
def pos.rel(c: Cmp, +x: Nat, r: N.Rel(c, x, 0n), h: {Cmp.is_eq(c) == False{} : Bool}) -> {Nat.is_lt(0n, x) == True{} : Bool}:
  match c:
    case LT{}:
      Empty.absurd({Nat.is_lt(0n, x) == True{} : Bool}, r)
    case EQ{}:
      Empty.absurd({Nat.is_lt(0n, x) == True{} : Bool}, N.true_ne_false(h))
    case GT{}:
      match x:
        case 0n:
          Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, r)
        case 1n+k:
          {==}

# a U32 that is not 0 has a number above 0
def u32.pos(+x: U32, h: {U32.is_eq(x, 0) == False{} : Bool}) -> {Nat.is_lt(0n, U32.to_nat(x)) == True{} : Bool}:
  pos.rel(U32.cmp(x, 0), U32.to_nat(x), N.U32.rel(x, 0), h)

# the pointers to a root: one more than without it
def ptr.root(+n: Nat, +m: Cr.Cir.Cells, +fi: U32, +ps: List<&2, U32>, +rs: List<&2, U32>, +c: U32) ->
  {D.Ptr(n, m, fi, ps, Con{c, rs}, c) == 1n+D.Ptr(n, m, fi, ps, rs, c) : Nat}:
  %Equal.sym(Bool, U32.is_eq(c, c), True{}, D.u32.refl(c)) :
    {Nat.add(D.Pc(n, m, ps, fi, c), Nat.add(D.Nat.of(_), D.RcL(rs, c))) == 1n+D.Ptr(n, m, fi, ps, rs, c) : Nat}
  N.add_succ_r(D.Pc(n, m, ps, fi, c), D.RcL(rs, c))

# a + (x + b) = 0 gives a + b = 0
def add.z3(a: Nat, x: Nat, -b: Nat, h: {Nat.add(a, Nat.add(x, b)) == 0n : Nat}) -> {Nat.add(a, b) == 0n : Nat}:
  match a:
    case 0n:
      match x:
        case 0n:
          h
        case 1n+k:
          D.bool.ft({b == 0n : Nat}, Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), 1n+Nat.add(k, b), 0n, h))
    case 1n+k:
      D.bool.ft({1n+Nat.add(k, b) == 0n : Nat}, Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), 1n+Nat.add(k, Nat.add(x, b)), 0n, h))

# one root less: the pend list's cells still have no pointer
def pendok.drop(qs: List<&2, U32>, +ps: List<&2, U32>, +m: Cr.Cir.Cells, +fi: U32, +nx: U32, +rs: List<&2, U32>, +c: U32,
  h: D.PendOK(qs, ps, m, fi, nx, Con{c, rs})) -> D.PendOK(qs, ps, m, fi, nx, rs):
  match qs:
    case Nil{}:
      Unit{}
    case Con{+p, +rest}:
      match h:
        case Tuple{ho, Tuple{+hs, Tuple{htg, Tuple{+hp0, hr}}}}:
          +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
          (ho, (hs, (htg, (add.z3(D.Pc(n, m, ps, fi, p), D.Nat.of(U32.is_eq(c, p)), D.RcL(rs, p), hp0),
            pendok.drop(rest, ps, m, fi, nx, rs, c, hr)))))

# one root less, at a STATIC cell, keeps the counts
def cntc.drop.s(b: Bool, +m: Cr.Cir.Cells, +c: U32, +q: U32, +N: Nat, +fi: U32, +ps: List<&2, U32>, +rs: List<&2, U32>,
  eb: {U32.is_eq(c, q) == b : Bool}, hst: {D.Fl(m, c, 1024) == True{} : Bool},
  h: {D.CntC(Cr.Cir.Cells.get(m, q), D.Ptr(N, m, fi, ps, Con{c, rs}, q), ps, q) == True{} : Bool}) ->
  {D.CntC(Cr.Cir.Cells.get(m, q), D.Ptr(N, m, fi, ps, rs, q), ps, q) == True{} : Bool}:
  match b:
    case False{}:
      %eb : {D.CntC(Cr.Cir.Cells.get(m, q), Nat.add(D.Pc(N, m, ps, fi, q), Nat.add(D.Nat.of(_), D.RcL(rs, q))), ps, q) == True{} : Bool}
      h
    case True{}:
      %D.u32.eq(c, q, eb) : {D.CntC(Cr.Cir.Cells.get(m, _), D.Ptr(N, m, fi, ps, rs, _), ps, _) == True{} : Bool}
      D.or.r(Bool.not(U32.is_lt(D.Tg(m, c), 19)), Bool.or(D.Fl(m, c, 1024), Bool.or(D.Mem(ps, c), Nat.is_eq(U32.to_nat(D.Fd(1n, m, c)), D.Ptr(N, m, fi, ps, rs, c)))),
        D.or.l(D.Fl(m, c, 1024), Bool.or(D.Mem(ps, c), Nat.is_eq(U32.to_nat(D.Fd(1n, m, c)), D.Ptr(N, m, fi, ps, rs, c))), hst))

def cnt.drop.s(k: Nat, +m: Cr.Cir.Cells, +c: U32, +o: U32, +N: Nat, +fi: U32, +ps: List<&2, U32>, +rs: List<&2, U32>,
  +hst: {D.Fl(m, c, 1024) == True{} : Bool}, h: {D.Cnt(k, m, o, N, fi, ps, Con{c, rs}) == True{} : Bool}) ->
  {D.Cnt(k, m, o, N, fi, ps, rs) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+(+j):
      +h2 = h
      D.and.i(D.CntC(Cr.Cir.Cells.get(m, o), D.Ptr(N, m, fi, ps, rs, o), ps, o), D.Cnt(j, m, U32.inc(o), N, fi, ps, rs),
        cntc.drop.s(U32.is_eq(c, o), m, c, o, N, fi, ps, rs, {==}, hst,
          D.and.l(D.CntC(Cr.Cir.Cells.get(m, o), D.Ptr(N, m, fi, ps, Con{c, rs}, o), ps, o), D.Cnt(j, m, U32.inc(o), N, fi, ps, Con{c, rs}), h2)),
        cnt.drop.s(j, m, c, U32.inc(o), N, fi, ps, rs, hst,
          D.and.r(D.CntC(Cr.Cir.Cells.get(m, o), D.Ptr(N, m, fi, ps, Con{c, rs}, o), ps, o), D.Cnt(j, m, U32.inc(o), N, fi, ps, Con{c, rs}), h2)))

# M.dec's count at a cell q: c loses a pointer (a root) and its count gets
# v; every other cell keeps both
def cntc.dec.b(b: Bool, +m: Cr.Cir.Cells, +c: U32, +v: U32, +q: U32, +N: Nat, +fi: U32, +ps: List<&2, U32>, +rs: List<&2, U32>,
  eb: {U32.is_eq(q, c) == b : Bool}, ev: {U32.to_nat(v) == D.Ptr(N, m, fi, ps, rs, c) : Nat},
  h: {D.CntC(Cr.Cir.Cells.get(m, q), D.Ptr(N, m, fi, ps, Con{c, rs}, q), ps, q) == True{} : Bool}) ->
  {D.CntC(Cr.Cir.Cells.get(D.Put1([D.W1{c, v}], m), q), D.Ptr(N, m, fi, ps, rs, q), ps, q) == True{} : Bool}:
  match b:
    case False{}:
      +ne = D.ne.sym(q, c, eb)
      +M2 = D.Put1([D.W1{c, v}], m)
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, q), Cr.Cir.Cells.get(m, q),
          D.put1.out([D.W1{c, v}], m, q, (%Equal.sym(Bool, U32.is_eq(c, q), False{}, ne) : {Bool.or(_, False{}) == False{} : Bool}; {==}))) :
        {D.CntC(_, D.Ptr(N, m, fi, ps, rs, q), ps, q) == True{} : Bool}
      %ne : {D.CntC(Cr.Cir.Cells.get(m, q), Nat.add(D.Pc(N, m, ps, fi, q), Nat.add(D.Nat.of(_), D.RcL(rs, q))), ps, q) == True{} : Bool}
      h
    case True{}:
      +M2 = D.Put1([D.W1{c, v}], m)
      +Y = Cr.Cir.Cells.get(m, c)
      +P = D.Ptr(N, m, fi, ps, rs, c)
      %Equal.sym(U32, q, c, D.u32.eq(q, c, eb)) : {D.CntC(Cr.Cir.Cells.get(M2, _), D.Ptr(N, m, fi, ps, rs, _), ps, _) == True{} : Bool}
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, c), Cr.Cir.Cell.set(1n, Y, v), D.cl.gs(m, c, Cr.Cir.Cell.set(1n, Y, v))) :
        {D.CntC(_, P, ps, c) == True{} : Bool}
      D.or.r(Bool.not(U32.is_lt(D.TgW(Cr.Cir.Cell.get(0n, Cr.Cir.Cell.set(1n, Y, v))), 19)),
        Bool.or(D.FlW(Cr.Cir.Cell.get(0n, Cr.Cir.Cell.set(1n, Y, v)), 1024), Bool.or(D.Mem(ps, c), Nat.is_eq(U32.to_nat(Cr.Cir.Cell.get(1n, Cr.Cir.Cell.set(1n, Y, v))), P))),
        D.or.r(D.FlW(Cr.Cir.Cell.get(0n, Cr.Cir.Cell.set(1n, Y, v)), 1024), Bool.or(D.Mem(ps, c), Nat.is_eq(U32.to_nat(Cr.Cir.Cell.get(1n, Cr.Cir.Cell.set(1n, Y, v))), P)),
          D.or.r(D.Mem(ps, c), Nat.is_eq(U32.to_nat(Cr.Cir.Cell.get(1n, Cr.Cir.Cell.set(1n, Y, v))), P),
            (%Equal.sym(U32, Cr.Cir.Cell.get(1n, Cr.Cir.Cell.set(1n, Y, v)), v, D.cg1(Y, v)) : {Nat.is_eq(U32.to_nat(_), P) == True{} : Bool};
              (%ev : {Nat.is_eq(U32.to_nat(v), _) == True{} : Bool}; nat.eq.refl(U32.to_nat(v)))))))

def cntc.dec(b: Bool, +m: Cr.Cir.Cells, +c: U32, +v: U32, +q: U32, +N: Nat, +fi: U32, +ps: List<&2, U32>, +rs: List<&2, U32>,
  eb: {U32.is_eq(q, c) == b : Bool}, ev: {U32.to_nat(v) == D.Ptr(N, m, fi, ps, rs, c) : Nat},
  h: {D.CntC(Cr.Cir.Cells.get(m, q), D.Ptr(N, m, fi, ps, Con{c, rs}, q), ps, q) == True{} : Bool}) ->
  {D.CntC(Cr.Cir.Cells.get(D.Put1([D.W1{c, v}], m), q), D.Ptr(N, D.Put1([D.W1{c, v}], m), fi, ps, rs, q), ps, q) == True{} : Bool}:
  +ws = {[D.W1{c, v}] : List<&2, D.W1>}
  %Equal.sym(Nat, D.Ptr(N, D.Put1(ws, m), fi, ps, rs, q), D.Ptr(N, m, fi, ps, rs, q), D.ptr.put1(N, ws, m, fi, ps, rs, q)) :
    {D.CntC(Cr.Cir.Cells.get(D.Put1(ws, m), q), _, ps, q) == True{} : Bool}
  cntc.dec.b(b, m, c, v, q, N, fi, ps, rs, eb, ev, h)

def cnt.dec(k: Nat, +m: Cr.Cir.Cells, +c: U32, +v: U32, +o: U32, +N: Nat, +fi: U32, +ps: List<&2, U32>, +rs: List<&2, U32>,
  +ev: {U32.to_nat(v) == D.Ptr(N, m, fi, ps, rs, c) : Nat}, h: {D.Cnt(k, m, o, N, fi, ps, Con{c, rs}) == True{} : Bool}) ->
  {D.Cnt(k, D.Put1([D.W1{c, v}], m), o, N, fi, ps, rs) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+(+j):
      +M2 = D.Put1([D.W1{c, v}], m)
      +h2 = h
      D.and.i(D.CntC(Cr.Cir.Cells.get(M2, o), D.Ptr(N, M2, fi, ps, rs, o), ps, o), D.Cnt(j, M2, U32.inc(o), N, fi, ps, rs),
        cntc.dec(U32.is_eq(o, c), m, c, v, o, N, fi, ps, rs, {==}, ev,
          D.and.l(D.CntC(Cr.Cir.Cells.get(m, o), D.Ptr(N, m, fi, ps, Con{c, rs}, o), ps, o), D.Cnt(j, m, U32.inc(o), N, fi, ps, Con{c, rs}), h2)),
        cnt.dec(j, m, c, v, U32.inc(o), N, fi, ps, rs, ev,
          D.and.r(D.CntC(Cr.Cir.Cells.get(m, o), D.Ptr(N, m, fi, ps, Con{c, rs}, o), ps, o), D.Cnt(j, m, U32.inc(o), N, fi, ps, Con{c, rs}), h2)))

# a cell of the pend list meets its count's condition
def cntc.mem(+y: Cr.Cir.Cell, -P: Nat, +ps: List<&2, U32>, +o: U32, h: {D.Mem(ps, o) == True{} : Bool}) ->
  {D.CntC(y, P, ps, o) == True{} : Bool}:
  D.or.r(Bool.not(U32.is_lt(D.TgW(Cr.Cir.Cell.get(0n, y)), 19)),
    Bool.or(D.FlW(Cr.Cir.Cell.get(0n, y), 1024), Bool.or(D.Mem(ps, o), Nat.is_eq(U32.to_nat(Cr.Cir.Cell.get(1n, y)), P))),
    D.or.r(D.FlW(Cr.Cir.Cell.get(0n, y), 1024), Bool.or(D.Mem(ps, o), Nat.is_eq(U32.to_nat(Cr.Cir.Cell.get(1n, y)), P)),
      D.or.l(D.Mem(ps, o), Nat.is_eq(U32.to_nat(Cr.Cir.Cell.get(1n, y)), P), h)))

# c heads Con{c, ps}
def mem.hd(+c: U32, -ps: List<&2, U32>) -> {D.Mem(Con{c, ps}, c) == True{} : Bool}:
  %Equal.sym(Bool, U32.is_eq(c, c), True{}, D.u32.refl(c)) : {Bool.or(_, D.Mem(ps, c)) == True{} : Bool}
  {==}

# a term cell's pointers do not depend on the pend list
def fs.term.ps(+m: Cr.Cir.Cells, +ps: List<&2, U32>, +qs: List<&2, U32>, +o: U32, ht: {U32.is_lt(D.Tg(m, o), 19) == True{} : Bool}) ->
  {D.Fs(m, qs, o) == D.Fs(m, ps, o) : List<&2, U32>}:
  +tg = D.TgW(D.Fd(0n, m, o))
  +F = Bool.and(U32.is_le(32, tg), U32.is_le(tg, 40))
  +G = Bool.and(U32.is_eq(tg, 41), D.FlW(D.Fd(0n, m, o), 4096))
  %Equal.sym(Bool, U32.is_lt(tg, 19), True{}, ht) :
    {FsT(_, Bool.and(F, Bool.not(D.Mem(qs, o))), Bool.and(G, Bool.not(D.Mem(qs, o))), m, o) ==
      FsT(_, Bool.and(F, Bool.not(D.Mem(ps, o))), Bool.and(G, Bool.not(D.Mem(ps, o))), m, o) : List<&2, U32>}
  {==}

# M.dec's count at a cell q, when c (a term cell) goes to the pend list with
# its root dropped: a pending cell counts none; every other cell keeps its
# count (field 1 of c gets v1, then v2)
def cntc.pend.b(b: Bool, +m: Cr.Cir.Cells, +c: U32, +v1: U32, +v2: U32, +q: U32, +N: Nat, +fi: U32, +ps: List<&2, U32>,
  +rs: List<&2, U32>, +eb: {U32.is_eq(c, q) == b : Bool},
  hfz: {D.Fs(m, Con{c, ps}, c) == D.Fs(m, ps, c) : List<&2, U32>},
  h: {D.CntC(Cr.Cir.Cells.get(m, q), D.Ptr(N, m, fi, ps, Con{c, rs}, q), ps, q) == True{} : Bool}) ->
  {D.CntC(Cr.Cir.Cells.get(D.Put1([D.W1{c, v2}, D.W1{c, v1}], m), q), D.Ptr(N, D.Put1([D.W1{c, v2}, D.W1{c, v1}], m), fi, Con{c, ps}, rs, q),
    Con{c, ps}, q) == True{} : Bool}:
  match b:
    case True{}:
      +M2 = D.Put1([D.W1{c, v2}, D.W1{c, v1}], m)
      %D.u32.eq(c, q, eb) : {D.CntC(Cr.Cir.Cells.get(M2, _), D.Ptr(N, M2, fi, Con{c, ps}, rs, _), Con{c, ps}, _) == True{} : Bool}
      cntc.mem(Cr.Cir.Cells.get(M2, c), D.Ptr(N, M2, fi, Con{c, ps}, rs, c), Con{c, ps}, c, mem.hd(c, ps))
    case False{}:
      +ws = {[D.W1{c, v2}, D.W1{c, v1}] : List<&2, D.W1>}
      +M2 = D.Put1(ws, m)
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, q), Cr.Cir.Cells.get(m, q),
          D.put1.out(ws, m, q, (%Equal.sym(Bool, U32.is_eq(c, q), False{}, eb) : {Bool.or(_, Bool.or(_, False{})) == False{} : Bool}; {==}))) :
        {D.CntC(_, D.Ptr(N, M2, fi, Con{c, ps}, rs, q), Con{c, ps}, q) == True{} : Bool}
      %Equal.sym(Nat, D.Ptr(N, M2, fi, Con{c, ps}, rs, q), D.Ptr(N, m, fi, Con{c, ps}, rs, q), D.ptr.put1(N, ws, m, fi, Con{c, ps}, rs, q)) :
        {D.CntC(Cr.Cir.Cells.get(m, q), _, Con{c, ps}, q) == True{} : Bool}
      cntc.pcons(m, q, N, fi, ps, rs, c, hfz,
        (%eb : {D.CntC(Cr.Cir.Cells.get(m, q), Nat.add(D.Pc(N, m, ps, fi, q), Nat.add(D.Nat.of(_), D.RcL(rs, q))), ps, q) == True{} : Bool}; h))

def cnt.pend(k: Nat, +m: Cr.Cir.Cells, +c: U32, +v1: U32, +v2: U32, +o: U32, +N: Nat, +fi: U32, +ps: List<&2, U32>, +rs: List<&2, U32>,
  +hfz: {D.Fs(m, Con{c, ps}, c) == D.Fs(m, ps, c) : List<&2, U32>}, h: {D.Cnt(k, m, o, N, fi, ps, Con{c, rs}) == True{} : Bool}) ->
  {D.Cnt(k, D.Put1([D.W1{c, v2}, D.W1{c, v1}], m), o, N, fi, Con{c, ps}, rs) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+(+j):
      +M2 = D.Put1([D.W1{c, v2}, D.W1{c, v1}], m)
      +h2 = h
      D.and.i(D.CntC(Cr.Cir.Cells.get(M2, o), D.Ptr(N, M2, fi, Con{c, ps}, rs, o), Con{c, ps}, o), D.Cnt(j, M2, U32.inc(o), N, fi, Con{c, ps}, rs),
        cntc.pend.b(U32.is_eq(c, o), m, c, v1, v2, o, N, fi, ps, rs, {==}, hfz,
          D.and.l(D.CntC(Cr.Cir.Cells.get(m, o), D.Ptr(N, m, fi, ps, Con{c, rs}, o), ps, o), D.Cnt(j, m, U32.inc(o), N, fi, ps, Con{c, rs}), h2)),
        cnt.pend(j, m, c, v1, v2, U32.inc(o), N, fi, ps, rs, hfz,
          D.and.r(D.CntC(Cr.Cir.Cells.get(m, o), D.Ptr(N, m, fi, ps, Con{c, rs}, o), ps, o), D.Cnt(j, m, U32.inc(o), N, fi, ps, Con{c, rs}), h2)))

# a register below the list's length holds a value
def get.some(xs: List<&2, U32>, r: Nat, h: {Nat.is_lt(r, List.length(&2, U32, xs)) == True{} : Bool}) ->
  {List.get(&2, U32, xs, r) == Some{Maybe.default(&2, U32, List.get(&2, U32, xs, r), 0)} : Maybe<&2, U32>}:
  match xs r:
    case Nil{} 0n:
      D.bool.ft({None{} == Some{0} : Maybe<&2, U32>}, h)
    case Nil{} 1n+p:
      D.bool.ft({None{} == Some{0} : Maybe<&2, U32>}, h)
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+p:
      get.some(t, p, h)

# setting a register to the value that it holds keeps the list
def set.same(xs: List<&2, U32>, r: Nat, +v: U32, h: {List.get(&2, U32, xs, r) == Some{v} : Maybe<&2, U32>}) ->
  {List.set(&2, U32, xs, r, v) == xs : List<&2, U32>}:
  match xs r:
    case Nil{} _:
      {==}
    case Con{x, t} 0n:
      Equal.cong(U32, List<&2, U32>, z => Con{z, t}, v, x,
        Equal.cong(Maybe<&2, U32>, U32, w => Maybe.default(&2, U32, w, 0), Some{v}, Some{x}, Equal.sym(Maybe<&2, U32>, Some{x}, Some{v}, h)))
    case Con{x, t} 1n+p:
      Equal.cong(List<&2, U32>, List<&2, U32>, z => Con{x, z}, List.set(&2, U32, t, p, v), t, set.same(t, p, v, h))

# no cell of the pend list is c (two stores at c)
def out.two(qs: List<&2, U32>, +c: U32, h: {D.Mem(qs, c) == False{} : Bool}) -> {Out(qs, [c, c]) == True{} : Bool}:
  match qs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      +h2 = h
      +ne = D.ne.sym(x, c, D.or.f.l(U32.is_eq(x, c), D.Mem(rest, c), h2))
      %Equal.sym(Bool, U32.is_eq(c, x), False{}, ne) :
        {Bool.and(Bool.not(Bool.or(_, Bool.or(_, False{}))), Out(rest, [c, c])) == True{} : Bool}
      out.two(rest, c, D.or.f.r(U32.is_eq(x, c), D.Mem(rest, c), h2))

# two stores at one of the machine's own cells: past the table
def gt.two(+dk: Bool, -ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -m: Cr.Cir.Cells,
  +im: U32, +fi: U32, +nx: U32, +c: U32, +v1: U32, +v2: U32, io: D.ImgOKK(dk, ds, ks, img, m, im, fi, nx), own: {D.Own(fi, nx, c) == True{} : Bool}) ->
  {W1.gt([D.W1{c, v2}, D.W1{c, v1}], 290) == True{} : Bool}:
  %Equal.sym(Bool, U32.is_lt(290, c), True{}, u.lt.of(290, c, D.img.hz(dk, ds, ks, img, m, im, fi, nx, c, io, own))) :
    {Bool.and(_, Bool.and(_, True{})) == True{} : Bool}
  {==}

# a term cell is no frame (two stores at it)
def w1.nf.two(+m: Cr.Cir.Cells, +c: U32, +v1: U32, +v2: U32, +u: Bk.Term, et: {D.Tg(m, c) == D.A.tag(u) : U32}) ->
  {W1.nf([D.W1{c, v2}, D.W1{c, v1}], m) == True{} : Bool}:
  +X = Bool.not(Bool.and(U32.is_le(32, D.A.tag(u)), U32.is_le(D.A.tag(u), 40)))
  %Equal.sym(U32, D.Tg(m, c), D.A.tag(u), et) :
    {Bool.and(Bool.not(Bool.and(U32.is_le(32, _), U32.is_le(_, 40))), Bool.and(Bool.not(Bool.and(U32.is_le(32, _), U32.is_le(_, 40))), True{})) ==
      True{} : Bool}
  D.and.i(X, Bool.and(X, True{}), D.and.l(X, True{}, atag.nf(u)), atag.nf(u))

# two stores to field 1 of c, the second last
def put1.two(+m: Cr.Cir.Cells, +c: U32, +v1: U32, +v2: U32) ->
  {D.Put1([D.W1{c, v2}, D.W1{c, v1}], m) == X.X.put(X.X.put(m, 1n, c, v1), 1n, c, v2) : Cr.Cir.Cells}:
  {==}

# HSK after M.dec of a STATIC root c: no cell changes, and c is no root
def dec.hs.s(+dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32,
  +ps: List<&2, U32>, +c: U32, +u: Bk.Term,
  hs: D.HSK(dk, ds, ks, img, m, nx, fi, im, Con{D.Rt{c, u}, os}, bs, fs, sp, pend, ps), hb: D.Held(m, os, bs),
  +hst: {D.Fl(m, c, 1024) == True{} : Bool}) ->
  D.HSK(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps):
  match hs:
    case Tuple{hos, Tuple{hbs, Tuple{_, Tuple{hfrs, Tuple{hheap, himg}}}}}:
      match hheap:
        case Tuple{hch, Tuple{hpk, Tuple{hcnt, hrest}}}:
          +hos2 = D.Ex.snd(D.IsK(dk, ds, m, im, fi, nx, ks, img, c, u), _ => D.RtsK(dk, ds, m, im, fi, nx, ks, img, os), hos)
          +rs = D.Rt.cells(os)
          +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
          (hos2, (hbs, (hb, (hfrs, ((hch, (pendok.drop(ps, ps, m, fi, nx, rs, c, hpk), (cnt.drop.s(n, m, c, fi, n, fi, ps, rs, hst, hcnt), hrest))),
            himg)))))

# HSK after M.dec of a root c that keeps a pointer: its count gets v, its
# pointers without the root, and c is no root
def dec.hs.n(+dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32,
  +ps: List<&2, U32>, +c: U32, +u: Bk.Term, +v: U32,
  hs: D.HSK(dk, ds, ks, img, m, nx, fi, im, Con{D.Rt{c, u}, os}, bs, fs, sp, pend, ps), hb: D.Held(m, os, bs),
  +hpn: {D.Mem(ps, c) == False{} : Bool}, +et: {D.Tg(m, c) == D.A.tag(u) : U32}, +hgt: {W1.gt([D.W1{c, v}], 290) == True{} : Bool},
  +ev: {U32.to_nat(v) == D.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, D.Rt.cells(os), c) : Nat}) ->
  D.HSK(dk, ds, ks, img, D.Put1([D.W1{c, v}], m), nx, fi, im, os, bs, fs, sp, pend, ps):
  match hs:
    case Tuple{hos, Tuple{hbs, Tuple{_, Tuple{hfrs, Tuple{hheap, himg}}}}}:
      match hheap:
        case Tuple{hch, Tuple{hpk, Tuple{hcnt, Tuple{hpts, hr}}}}:
          +hos2 = D.Ex.snd(D.IsK(dk, ds, m, im, fi, nx, ks, img, c, u), _ => D.RtsK(dk, ds, m, im, fi, nx, ks, img, os), hos)
          +ws = {[D.W1{c, v}] : List<&2, D.W1>}
          +M2 = D.Put1(ws, m)
          +rs = D.Rt.cells(os)
          +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
          (rtsk.p1(dk, os, ds, m, im, fi, nx, ks, img, ws, hos2),
            (rtsk.p1(dk, bs, ds, m, im, fi, nx, ks, img, ws, hbs),
            (held.p1(bs, os, ws, m, hb),
            (frsk.p1(dk, fs, ds, m, im, fi, nx, ks, img, ps, ws, sp, w1.nf.one(m, c, v, u, et), hfrs),
            ((chain.p1(ps, ws, m, pend, out.one(ps, c, hpn), hch),
              (D.pendok.put1(ps, ps, ws, m, fi, nx, rs, pendok.drop(ps, ps, m, fi, nx, rs, c, hpk)),
              (cnt.dec(n, m, c, v, fi, n, fi, ps, rs, ev, hcnt),
              ((%Equal.sym(Bool, D.Pts(n, M2, ps, fi, im, fi, nx), D.Pts(n, m, ps, fi, im, fi, nx), D.pts.put1(n, ws, m, ps, fi, im, fi, nx)) :
                  {_ == True{} : Bool}; hpts),
                hr)))),
              imgokk.p1(dk, ds, ks, img, m, im, fi, nx, ws, hgt, himg))))))

# HSK after M.dec of a root c to the count 0: c heads the pend list (its
# field 1 gets d, then the old pend), and c is no root
def dec.hs.p(+dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32,
  +ps: List<&2, U32>, +c: U32, +u: Bk.Term, +d: U32,
  hs: D.HSK(dk, ds, ks, img, m, nx, fi, im, Con{D.Rt{c, u}, os}, bs, fs, sp, pend, ps), hb: D.Held(m, os, bs),
  +hz: {D.Own(fi, nx, c) == True{} : Bool}, +hz0: {U32.is_eq(c, 0) == False{} : Bool}, +hf: {D.Fl(m, c, 1024) == False{} : Bool},
  +hpn: {D.Mem(ps, c) == False{} : Bool}, +et: {D.Tg(m, c) == D.A.tag(u) : U32}, +ht: {U32.is_lt(D.Tg(m, c), 19) == True{} : Bool},
  +e0: {D.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, D.Rt.cells(os), c) == 0n : Nat}) ->
  D.HSK(dk, ds, ks, img, D.Put1([D.W1{c, pend}, D.W1{c, d}], m), nx, fi, im, os, bs, fs, sp, c, Con{c, ps}):
  match hs:
    case Tuple{hos, Tuple{hbs, Tuple{_, Tuple{hfrs, Tuple{hheap, himg0}}}}}:
      match hheap:
        case Tuple{hch, Tuple{hpk, Tuple{hcnt, Tuple{hpts0, hr}}}}:
          +hos2 = D.Ex.snd(D.IsK(dk, ds, m, im, fi, nx, ks, img, c, u), _ => D.RtsK(dk, ds, m, im, fi, nx, ks, img, os), hos)
          +himg = {himg0 : D.ImgOKK(dk, ds, ks, img, m, im, fi, nx)}
          +hpts = {hpts0 : {D.Pts(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, ps, fi, im, fi, nx) == True{} : Bool}}
          +ws = {[D.W1{c, pend}, D.W1{c, d}] : List<&2, D.W1>}
          +M1 = D.Put1([D.W1{c, d}], m)
          +M2 = D.Put1(ws, m)
          +rs = D.Rt.cells(os)
          +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
          +hfz = fs.term.ps(m, ps, Con{c, ps}, c, ht)
          +hnf = {(%Equal.sym(U32, D.Tg(m, c), D.A.tag(u), et) : {Bool.not(Bool.and(U32.is_le(32, _), U32.is_le(_, 40))) == True{} : Bool};
              D.and.l(Bool.not(Bool.and(U32.is_le(32, D.A.tag(u)), U32.is_le(D.A.tag(u), 40))), True{}, atag.nf(u))) :
            {Bool.not(Bool.and(U32.is_le(32, D.Tg(m, c)), U32.is_le(D.Tg(m, c), 40))) == True{} : Bool}}
          +Y = Cr.Cir.Cells.get(M1, c)
          +x = Cr.Cir.Cell.set(1n, Y, pend)
          +e1 = Equal.trans(U32, D.Fd(1n, M2, c), Cr.Cir.Cell.get(1n, x), pend,
            Equal.cong(Cr.Cir.Cell, U32, w => Cr.Cir.Cell.get(1n, w), Cr.Cir.Cells.get(M2, c), x, D.cl.gs(M1, c, x)), D.cg1(Y, pend))
          +e0f = D.put1.f0(ws, m, c)
          +hp0 = Equal.trans(Nat, D.Ptr(n, M2, fi, Con{c, ps}, rs, c), D.Ptr(n, m, fi, Con{c, ps}, rs, c), 0n,
            D.ptr.put1(n, ws, m, fi, Con{c, ps}, rs, c),
            Equal.trans(Nat, D.Ptr(n, m, fi, Con{c, ps}, rs, c), D.Ptr(n, m, fi, ps, rs, c), 0n, ptr.pcons(n, m, fi, ps, rs, c, c, hfz), e0))
          +hpts2 = {(%Equal.sym(Bool, D.Pts(n, M2, Con{c, ps}, fi, im, fi, nx), D.Pts(n, m, Con{c, ps}, fi, im, fi, nx),
                D.pts.put1(n, ws, m, Con{c, ps}, fi, im, fi, nx)) : {_ == True{} : Bool};
              (%Equal.sym(Bool, D.Pts(n, m, Con{c, ps}, fi, im, fi, nx), D.Pts(n, m, ps, fi, im, fi, nx), pts.pcons(n, m, ps, c, fi, im, fi, nx, hfz)) :
                  {_ == True{} : Bool};
                hpts)) : {D.Pts(n, M2, Con{c, ps}, fi, im, fi, nx) == True{} : Bool}}
          +hpk2 = {(hz, ((%Equal.sym(U32, D.Fd(0n, M2, c), D.Fd(0n, m, c), e0f) : {U32.is_ne(U32.and(_, 1024), 0) == False{} : Bool}; hf),
              ((%Equal.sym(U32, D.Fd(0n, M2, c), D.Fd(0n, m, c), e0f) :
                  {Bool.or(U32.is_lt(U32.and(_, 63), 19), U32.is_le(32, U32.and(_, 63))) == True{} : Bool};
                D.or.l(U32.is_lt(D.Tg(m, c), 19), U32.is_le(32, D.Tg(m, c)), ht)),
              (hp0, D.pendok.put1(ps, Con{c, ps}, ws, m, fi, nx, rs,
                pendok.pcons(ps, ps, m, fi, nx, rs, c, hfz, pendok.drop(ps, ps, m, fi, nx, rs, c, hpk))))))) :
            D.PendOK(Con{c, ps}, Con{c, ps}, M2, fi, nx, rs)}
          +hch2 = {({==}, (hz0, (%Equal.sym(U32, D.Fd(1n, M2, c), pend, e1) : D.Chain(ps, M2, _);
              chain.p1(ps, ws, m, pend, out.two(ps, c, hpn), hch)))) : D.Chain(Con{c, ps}, M2, c)}
          (rtsk.p1(dk, os, ds, m, im, fi, nx, ks, img, ws, hos2),
            (rtsk.p1(dk, bs, ds, m, im, fi, nx, ks, img, ws, hbs),
            (held.p1(bs, os, ws, m, hb),
            (frsk.p1(dk, fs, ds, m, im, fi, nx, ks, img, Con{c, ps}, ws, sp, w1.nf.two(m, c, d, pend, u, et),
                frsk.pcons(dk, fs, ds, m, im, fi, nx, ks, img, ps, c, sp, hnf, hfrs)),
            ((hch2, (hpk2, (cnt.pend(n, m, c, d, pend, fi, n, fi, ps, rs, hfz, hcnt), (hpts2, hr)))),
              imgokk.p1(dk, ds, ks, img, m, im, fi, nx, ws, gt.two(dk, ds, ks, img, m, im, fi, nx, c, d, pend, himg, hz), himg))))))

# M.dec of a root c that is no STATIC cell, by its count less one (d): c
# keeps a pointer, or it heads the pend list
def dec.cnt(b: Bool, +f: Nat, +dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +r: Nat,
  +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>, +c: U32, +u: Bk.Term,
  +xs: List<&2, D.TmpE>, +zs: List<&2, D.Rt>,
  +eb: {U32.is_eq(U32.sub(D.Fd(1n, m, c), 1), 0) == b : Bool},
  +hs: D.HSK(dk, ds, ks, img, m, nx, fi, im, Con{D.Rt{c, u}, os}, bs, fs, sp, pend, ps),
  hac: D.AccK(dk, ds, ks, img, m, nx, fi, im, Con{D.Rt{c, u}, os}, xs, sp, fs, ps, zs),
  hb: D.Held(m, os, bs),
  +hl: {List.length(&2, U32, regs) == 63n : Nat}, +hc: {List.get(&2, U32, regs, r) == Some{c} : Maybe<&2, U32>},
  +hp: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>}, +h5: {Nat.is_eq(5n, r) == False{} : Bool},
  +hz: {U32.is_eq(c, 0) == False{} : Bool}, +hcell: {Cr.Cir.is_cell(c, im, fi, nx) == True{} : Bool},
  +hf: {D.Fl(m, c, 1024) == False{} : Bool}, +own: {D.Own(fi, nx, c) == True{} : Bool},
  +hpn: {D.Mem(ps, c) == False{} : Bool}, +et: {D.Tg(m, c) == D.A.tag(u) : U32}, +ht: {U32.is_lt(D.Tg(m, c), 19) == True{} : Bool},
  +himg: D.ImgOKK(dk, ds, ks, img, m, im, fi, nx),
  +ed: {U32.to_nat(U32.sub(D.Fd(1n, m, c), 1)) == D.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, D.Rt.cells(os), c) : Nat}) ->
  D.PostB(False{}, Cr.Cir.exec(f, Mc.M.dec(r), Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0}),
    st2 => D.Ex(Cr.Cir.Cells, m2 => D.Ex(U32, d => D.Ex(U32, pend2 => D.Ex(List<&2, U32>, ps2 =>
      D.P2({st2 == Cr.Cir.State{List.set(&2, U32, List.set(&2, U32, regs, 5n, d), 3n, pend2), m2, nx, fi, im, pg, lim, inp, Nil{}, 0} : Cr.Cir.State},
      D.P2({D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m2, fi) == D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi) : Nat},
      D.P2(D.HSK(dk, ds, ks, img, m2, nx, fi, im, os, bs, fs, sp, pend2, ps2),
        D.Ex(List<&2, D.Rt>, zs2 => D.AccK(dk, ds, ks, img, m2, nx, fi, im, os, xs, sp, fs, ps2, zs2))))))))),
    s => st2 => Empty, 0n, lim):
  match b:
    case False{}:
      +d = U32.sub(D.Fd(1n, m, c), 1)
      +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
      +rs = D.Rt.cells(os)
      +hlt = {(%ed : {Nat.is_lt(0n, _) == True{} : Bool}; u32.pos(d, eb)) :
        {Nat.is_lt(0n, D.Ptr(n, m, fi, ps, rs, c)) == True{} : Bool}}
      +hd = D.or.r(D.Fl(m, c, 1024), Nat.is_lt(0n, D.Ptr(n, m, fi, ps, rs, c)), hlt)
      +hsk = dec.hs.n(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps, c, u, d, hs, hb, hpn, et,
        gt.one(dk, ds, ks, img, m, im, fi, nx, c, d, himg, own), ed)
      %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, Mc.M.dec(r), Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0}),
          Cr.Cir.Out.next{X.X.st(X.X.set(regs, 5n, d), X.X.put(m, 1n, c, d), nx, fi, im, pg, lim, inp)},
          X.dec.eq.n(f, regs, m, nx, fi, im, pg, lim, inp, r, c, hl, hc, hz, hcell, hf, eb, h5)) :
        D.PostB(False{}, _,
          st2 => D.Ex(Cr.Cir.Cells, m2 => D.Ex(U32, d => D.Ex(U32, pend2 => D.Ex(List<&2, U32>, ps2 =>
            D.P2({st2 == Cr.Cir.State{List.set(&2, U32, List.set(&2, U32, regs, 5n, d), 3n, pend2), m2, nx, fi, im, pg, lim, inp, Nil{}, 0} : Cr.Cir.State},
            D.P2({D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m2, fi) == D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi) : Nat},
            D.P2(D.HSK(dk, ds, ks, img, m2, nx, fi, im, os, bs, fs, sp, pend2, ps2),
              D.Ex(List<&2, D.Rt>, zs2 => D.AccK(dk, ds, ks, img, m2, nx, fi, im, os, xs, sp, fs, ps2, zs2))))))))),
          s => st2 => Empty, 0n, lim)
      (X.X.put(m, 1n, c, d), (d, (pend, (ps,
        ((%Equal.sym(List<&2, U32>, List.set(&2, U32, List.set(&2, U32, regs, 5n, d), 3n, pend), List.set(&2, U32, regs, 5n, d),
              set.same(List.set(&2, U32, regs, 5n, d), 3n, pend, X.L.go(regs, 5n, 3n, d, pend, {==}, hp))) :
            {Cr.Cir.State{List.set(&2, U32, regs, 5n, d), X.X.put(m, 1n, c, d), nx, fi, im, pg, lim, inp, Nil{}, 0} ==
              Cr.Cir.State{_, X.X.put(m, 1n, c, d), nx, fi, im, pg, lim, inp, Nil{}, 0} : Cr.Cir.State};
          {==}),
        (AC.stat.put1(n, [D.W1{c, d}], m, fi),
        ((%put1.one(m, c, d) : D.HSK(dk, ds, ks, img, _, nx, fi, im, os, bs, fs, sp, pend, ps); hsk),
          (zs, AC.acc.dec.keep(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps, c, u, d, xs, zs, hs, hac, ht, hd)))))))))
    case True{}:
      +d = U32.sub(D.Fd(1n, m, c), 1)
      +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
      +rs = D.Rt.cells(os)
      +e0 = Equal.trans(Nat, D.Ptr(n, m, fi, ps, rs, c), U32.to_nat(d), 0n, Equal.sym(Nat, U32.to_nat(d), D.Ptr(n, m, fi, ps, rs, c), ed),
        Equal.cong(U32, Nat, w => U32.to_nat(w), d, 0, D.u32.eq(d, 0, eb)))
      +hsk = dec.hs.p(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps, c, u, d, hs, hb, own, hz, hf, hpn, et, ht, e0)
      %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, Mc.M.dec(r), Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0}),
          Cr.Cir.Out.next{X.X.st(X.X.set(X.X.set(regs, 5n, d), 3n, c), X.X.put(X.X.put(m, 1n, c, d), 1n, c, pend), nx, fi, im, pg, lim, inp)},
          X.dec.eq.p(f, regs, m, nx, fi, im, pg, lim, inp, r, c, pend, hl, hc, hp, hz, hcell, hf, eb, h5)) :
        D.PostB(False{}, _,
          st2 => D.Ex(Cr.Cir.Cells, m2 => D.Ex(U32, d => D.Ex(U32, pend2 => D.Ex(List<&2, U32>, ps2 =>
            D.P2({st2 == Cr.Cir.State{List.set(&2, U32, List.set(&2, U32, regs, 5n, d), 3n, pend2), m2, nx, fi, im, pg, lim, inp, Nil{}, 0} : Cr.Cir.State},
            D.P2({D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m2, fi) == D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi) : Nat},
            D.P2(D.HSK(dk, ds, ks, img, m2, nx, fi, im, os, bs, fs, sp, pend2, ps2),
              D.Ex(List<&2, D.Rt>, zs2 => D.AccK(dk, ds, ks, img, m2, nx, fi, im, os, xs, sp, fs, ps2, zs2))))))))),
          s => st2 => Empty, 0n, lim)
      (X.X.put(X.X.put(m, 1n, c, d), 1n, c, pend), (d, (c, (Con{c, ps}, ({==},
        ((%put1.two(m, c, d, pend) : {D.Stat(n, _, fi) == D.Stat(n, m, fi) : Nat}; AC.stat.put1(n, [D.W1{c, pend}, D.W1{c, d}], m, fi)),
        ((%put1.two(m, c, d, pend) : D.HSK(dk, ds, ks, img, _, nx, fi, im, os, bs, fs, sp, c, Con{c, ps}); hsk),
          (Con{D.Rt{c, u}, zs}, AC.acc.dec.pend(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps, c, u, d, xs, zs, hs, hac, ht)))))))))

# M.dec of the owned root c of u, by the flag STATIC of c
def dec.go(b: Bool, +f: Nat, +dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +r: Nat,
  +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>, +c: U32, +u: Bk.Term,
  +xs: List<&2, D.TmpE>, +zs: List<&2, D.Rt>,
  +eb: {D.Fl(m, c, 1024) == b : Bool},
  +hos: D.RtsK(dk, ds, m, im, fi, nx, ks, img, Con{D.Rt{c, u}, os}), +hbs: D.RtsK(dk, ds, m, im, fi, nx, ks, img, bs),
  +hheld: D.Held(m, Con{D.Rt{c, u}, os}, bs), +hfrs: D.FrsK(dk, ds, m, im, fi, nx, ks, img, ps, sp, fs),
  +hheap: D.Heap(m, nx, fi, im, Con{c, D.Rt.cells(os)}, pend, ps), +himg: D.ImgOKK(dk, ds, ks, img, m, im, fi, nx),
  hac: D.AccK(dk, ds, ks, img, m, nx, fi, im, Con{D.Rt{c, u}, os}, xs, sp, fs, ps, zs),
  hb: D.Held(m, os, bs),
  +hl: {List.length(&2, U32, regs) == 63n : Nat}, +hc: {List.get(&2, U32, regs, r) == Some{c} : Maybe<&2, U32>},
  +hp: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>}, +h5: {Nat.is_eq(5n, r) == False{} : Bool}) ->
  D.PostB(False{}, Cr.Cir.exec(f, Mc.M.dec(r), Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0}),
    st2 => D.Ex(Cr.Cir.Cells, m2 => D.Ex(U32, d => D.Ex(U32, pend2 => D.Ex(List<&2, U32>, ps2 =>
      D.P2({st2 == Cr.Cir.State{List.set(&2, U32, List.set(&2, U32, regs, 5n, d), 3n, pend2), m2, nx, fi, im, pg, lim, inp, Nil{}, 0} : Cr.Cir.State},
      D.P2({D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m2, fi) == D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi) : Nat},
      D.P2(D.HSK(dk, ds, ks, img, m2, nx, fi, im, os, bs, fs, sp, pend2, ps2),
        D.Ex(List<&2, D.Rt>, zs2 => D.AccK(dk, ds, ks, img, m2, nx, fi, im, os, xs, sp, fs, ps2, zs2))))))))),
    s => st2 => Empty, 0n, lim):
  match b:
    case True{}:
      +hs = {(hos, (hbs, (hheld, (hfrs, (hheap, himg))))) : D.HSK(dk, ds, ks, img, m, nx, fi, im, Con{D.Rt{c, u}, os}, bs, fs, sp, pend, ps)}
      +hu = D.Ex.fst(D.IsK(dk, ds, m, im, fi, nx, ks, img, c, u), _ => D.RtsK(dk, ds, m, im, fi, nx, ks, img, os), hos)
      +nd = isk.nd(dk, u, ds, m, im, fi, nx, ks, img, c, hu)
      +hcell = ndk.cell(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), u, D.A.tag(u), nd)
      +hz = cell.nz(c, im, fi, nx, hcell, img.lt(dk, ds, ks, img, m, im, fi, nx, himg))
      +rs = D.Rt.cells(os)
      +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
      +hsk = dec.hs.s(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps, c, u, hs, hb, eb)
      +hd = D.or.l(D.Fl(m, c, 1024), Nat.is_lt(0n, D.Ptr(n, m, fi, ps, rs, c)), eb)
      +d5 = Maybe.default(&2, U32, List.get(&2, U32, regs, 5n), 0)
      +g5 = get.some(regs, 5n, X.L.lt(regs, 5n, hl, {==}))
      %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, Mc.M.dec(r), Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0}),
          Cr.Cir.Out.next{X.X.st(regs, m, nx, fi, im, pg, lim, inp)}, X.dec.eq.s(f, regs, m, nx, fi, im, pg, lim, inp, r, c, hc, hz, hcell, eb)) :
        D.PostB(False{}, _,
          st2 => D.Ex(Cr.Cir.Cells, m2 => D.Ex(U32, d => D.Ex(U32, pend2 => D.Ex(List<&2, U32>, ps2 =>
            D.P2({st2 == Cr.Cir.State{List.set(&2, U32, List.set(&2, U32, regs, 5n, d), 3n, pend2), m2, nx, fi, im, pg, lim, inp, Nil{}, 0} : Cr.Cir.State},
            D.P2({D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m2, fi) == D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi) : Nat},
            D.P2(D.HSK(dk, ds, ks, img, m2, nx, fi, im, os, bs, fs, sp, pend2, ps2),
              D.Ex(List<&2, D.Rt>, zs2 => D.AccK(dk, ds, ks, img, m2, nx, fi, im, os, xs, sp, fs, ps2, zs2))))))))),
          s => st2 => Empty, 0n, lim)
      (m, (d5, (pend, (ps,
        ((%Equal.sym(List<&2, U32>, List.set(&2, U32, regs, 5n, d5), regs, set.same(regs, 5n, d5, g5)) :
            {Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0} ==
              Cr.Cir.State{List.set(&2, U32, _, 3n, pend), m, nx, fi, im, pg, lim, inp, Nil{}, 0} : Cr.Cir.State};
          (%Equal.sym(List<&2, U32>, List.set(&2, U32, regs, 3n, pend), regs, set.same(regs, 3n, pend, hp)) :
              {Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0} == Cr.Cir.State{_, m, nx, fi, im, pg, lim, inp, Nil{}, 0} : Cr.Cir.State};
            {==})),
        ({==}, (hsk, (zs, AC.acc.drop(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps, c, u, xs, zs, hs, hac, hd)))))))))
    case False{}:
      +hs = {(hos, (hbs, (hheld, (hfrs, (hheap, himg))))) : D.HSK(dk, ds, ks, img, m, nx, fi, im, Con{D.Rt{c, u}, os}, bs, fs, sp, pend, ps)}
      +hu = D.Ex.fst(D.IsK(dk, ds, m, im, fi, nx, ks, img, c, u), _ => D.RtsK(dk, ds, m, im, fi, nx, ks, img, os), hos)
      +nd = isk.nd(dk, u, ds, m, im, fi, nx, ks, img, c, hu)
      +hcell = ndk.cell(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), u, D.A.tag(u), nd)
      +hz = cell.nz(c, im, fi, nx, hcell, img.lt(dk, ds, ks, img, m, im, fi, nx, himg))
      +rs = D.Rt.cells(os)
      +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
      +et = {D.nd.tgk(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), u, D.A.tag(u), nd) : {D.Tg(m, c) == D.A.tag(u) : U32}}
      +ht = {(%Equal.sym(U32, D.Tg(m, c), D.A.tag(u), et) : {U32.is_lt(_, 19) == True{} : Bool}; atag.lt(u)) : {U32.is_lt(D.Tg(m, c), 19) == True{} : Bool}}
      +own = or.false(D.Own(fi, nx, c), D.FlW(Cr.Cir.Cell.get(0n, Cr.Cir.Cells.get(m, c)), 1024),
        ndk.own(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), u, D.A.tag(u), nd), eb)
      +hpk = D.heap.pend(m, nx, fi, im, Con{c, rs}, pend, ps, hheap)
      +er = ptr.root(n, m, fi, ps, rs, c)
      +hlt0 = {(%Equal.sym(Nat, D.Ptr(n, m, fi, ps, Con{c, rs}, c), 1n+D.Ptr(n, m, fi, ps, rs, c), er) : {Nat.is_lt(0n, _) == True{} : Bool}; {==}) :
        {Nat.is_lt(0n, D.Ptr(n, m, fi, ps, Con{c, rs}, c)) == True{} : Bool}}
      +hpn = notin.ps(D.Mem(ps, c), ps, m, fi, nx, Con{c, rs}, c, {==}, hpk, hlt0)
      +h1 = D.u.le(fi, c, D.and.l(U32.is_le(fi, c), U32.is_lt(c, nx), own))
      +hl1 = D.u.lt(c, nx, D.and.r(U32.is_le(fi, c), U32.is_lt(c, nx), own))
      +es = D.add.sub(U32.to_nat(fi), U32.to_nat(nx), N.le_trans(U32.to_nat(fi), U32.to_nat(c), U32.to_nat(nx), h1, N.weaken(U32.to_nat(c), U32.to_nat(nx), hl1)))
      +h2 = N.le_rw_r(1n+U32.to_nat(c), U32.to_nat(nx), Nat.add(U32.to_nat(fi), n), Equal.sym(Nat, Nat.add(U32.to_nat(fi), n), U32.to_nat(nx), es), hl1)
      +hcc = cnt.get(n, m, fi, c, n, fi, ps, Con{c, rs}, h1, h2, heap.cnt(m, nx, fi, im, Con{c, rs}, pend, ps, hheap))
      +hfv = cntc.val(m, c, D.Ptr(n, m, fi, ps, Con{c, rs}, c), ps, hcc, ht, eb, hpn)
      +f1 = D.Fd(1n, m, c)
      +ef1 = Equal.trans(Nat, U32.to_nat(f1), D.Ptr(n, m, fi, ps, Con{c, rs}, c), 1n+D.Ptr(n, m, fi, ps, rs, c), hfv, er)
      +hge = {(%Equal.sym(Nat, U32.to_nat(f1), 1n+D.Ptr(n, m, fi, ps, rs, c), ef1) : N.Le(1n, _); N.le_zero(D.Ptr(n, m, fi, ps, rs, c))) :
        N.Le(1n, U32.to_nat(f1))}
      +ed = succ.inj(U32.to_nat(U32.sub(f1, 1)), D.Ptr(n, m, fi, ps, rs, c),
        Equal.trans(Nat, 1n+U32.to_nat(U32.sub(f1, 1)), U32.to_nat(f1), 1n+D.Ptr(n, m, fi, ps, rs, c), u32.dec(f1, hge), ef1))
      dec.cnt(U32.is_eq(U32.sub(f1, 1), 0), f, dk, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, r, os, bs, fs, sp, pend, ps, c, u, xs, zs, {==}, hs, hac, hb, hl, hc, hp, h5,
        hz, hcell, eb, own, hpn, et, ht, himg, ed)

# M.dec: the parts of HSK, and the flag STATIC of c
def dec.top(+f: Nat, +dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +r: Nat,
  +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>, +c: U32, +u: Bk.Term,
  +xs: List<&2, D.TmpE>, +zs: List<&2, D.Rt>,
  hs: D.HSK(dk, ds, ks, img, m, nx, fi, im, Con{D.Rt{c, u}, os}, bs, fs, sp, pend, ps),
  hac: D.AccK(dk, ds, ks, img, m, nx, fi, im, Con{D.Rt{c, u}, os}, xs, sp, fs, ps, zs),
  hb: D.Held(m, os, bs),
  +hl: {List.length(&2, U32, regs) == 63n : Nat}, +hc: {List.get(&2, U32, regs, r) == Some{c} : Maybe<&2, U32>},
  +hp: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>}, +h5: {Nat.is_eq(5n, r) == False{} : Bool}) ->
  D.PostB(False{}, Cr.Cir.exec(f, Mc.M.dec(r), Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0}),
    st2 => D.Ex(Cr.Cir.Cells, m2 => D.Ex(U32, d => D.Ex(U32, pend2 => D.Ex(List<&2, U32>, ps2 =>
      D.P2({st2 == Cr.Cir.State{List.set(&2, U32, List.set(&2, U32, regs, 5n, d), 3n, pend2), m2, nx, fi, im, pg, lim, inp, Nil{}, 0} : Cr.Cir.State},
      D.P2({D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m2, fi) == D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi) : Nat},
      D.P2(D.HSK(dk, ds, ks, img, m2, nx, fi, im, os, bs, fs, sp, pend2, ps2),
        D.Ex(List<&2, D.Rt>, zs2 => D.AccK(dk, ds, ks, img, m2, nx, fi, im, os, xs, sp, fs, ps2, zs2))))))))),
    s => st2 => Empty, 0n, lim):
  match hs:
    case Tuple{hos, Tuple{hbs, Tuple{hheld, Tuple{hfrs, Tuple{hheap, himg}}}}}:
      dec.go(D.Fl(m, c, 1024), f, dk, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, r, os, bs, fs, sp, pend, ps, c, u, xs, zs, {==},
        hos, hbs, hheld, hfrs, hheap, himg, hac, hb, hl, hc, hp, h5)

# A store at next
# ----------------
#
# The cell nx is no cell of a term or a frame yet (each is below nx: fi <= nx,
# and the image's cells are below fi), and next, at most 214748364, gains 1
# with no wrap: a store at nx keeps every term and frame that HS holds.

# next, at most 214748364, gains 1 with no wrap
def nx.inc(+nx: U32, hr: {U32.is_le(nx, 214748364) == True{} : Bool}) -> {U32.to_nat(U32.inc(nx)) == 1n+U32.to_nat(nx) : Nat}:
  +b28 = {U32{N.bit(32n, 28n)} : U32}
  D.u.inc(nx, b28, lt.trans.le(U32.to_nat(nx), U32.to_nat(214748364), U32.to_nat(b28), D.u.le(nx, 214748364, hr), D.u.lt(214748364, b28, {==})))

# fi <= nx (Heap)
def heap.fn(-m: Cr.Cir.Cells, -nx: U32, -fi: U32, -im: U32, -rs: List<&2, U32>, -pend: U32, -ps: List<&2, U32>,
  h: D.Heap(m, nx, fi, im, rs, pend, ps)) -> {U32.is_le(fi, nx) == True{} : Bool}:
  (_, r1) = h
  (_, r2) = r1
  (_, r3) = r2
  (_, r4) = r3
  (_, e) = r4
  e

# a < b: a is not b
def lt.ne.b(e: Bool, +a: U32, +b: U32, ee: {U32.is_eq(a, b) == e : Bool}, h: {U32.is_lt(a, b) == True{} : Bool}) ->
  {U32.is_eq(a, b) == False{} : Bool}:
  match e:
    case False{}:
      ee
    case True{}:
      Empty.absurd({U32.is_eq(a, b) == False{} : Bool},
        N.not_succ_le(U32.to_nat(b), (%D.u32.eq(a, b, ee) : N.Le(1n+U32.to_nat(_), U32.to_nat(b)); D.u.lt(a, b, h))))

def lt.ne.u(+a: U32, +b: U32, h: {U32.is_lt(a, b) == True{} : Bool}) -> {U32.is_eq(a, b) == False{} : Bool}:
  lt.ne.b(U32.is_eq(a, b), a, b, {==}, h)

# a cell is below next (the image's are below fi, and fi <= nx)
def cell.lt(+c: U32, +im: U32, +fi: U32, +nx: U32, hc: {Cr.Cir.is_cell(c, im, fi, nx) == True{} : Bool},
  +him: {U32.is_lt(im, fi) == True{} : Bool}, +hfn: {U32.is_le(fi, nx) == True{} : Bool}) -> {U32.is_lt(c, nx) == True{} : Bool}:
  D.or.cases(Bool.and(Bool.not(U32.is_zero(c)), U32.is_le(c, im)), D.Own(fi, nx, c), {U32.is_lt(c, nx) == True{} : Bool}, hc,
    e => u.lt.of(c, nx, lt.trans.le(U32.to_nat(c), U32.to_nat(im), U32.to_nat(nx),
      D.u.le(c, im, D.and.r(Bool.not(U32.is_zero(c)), U32.is_le(c, im), e)),
      N.le_trans(1n+U32.to_nat(im), U32.to_nat(fi), U32.to_nat(nx), D.u.lt(im, fi, him), D.u.le(fi, nx, hfn)))),
    e => D.and.r(U32.is_le(fi, c), U32.is_lt(c, nx), e))

# c < nx gives c < nx + 1
def lt.fr(+c: U32, +nx: U32, +hnx: {U32.to_nat(U32.inc(nx)) == 1n+U32.to_nat(nx) : Nat}, h: {U32.is_lt(c, nx) == True{} : Bool}) ->
  {U32.is_lt(c, U32.inc(nx)) == True{} : Bool}:
  u.lt.of(c, U32.inc(nx), N.le_rw_r(1n+U32.to_nat(c), 1n+U32.to_nat(nx), U32.to_nat(U32.inc(nx)),
    Equal.sym(Nat, U32.to_nat(U32.inc(nx)), 1n+U32.to_nat(nx), hnx), N.le_succ(1n+U32.to_nat(c), U32.to_nat(nx), D.u.lt(c, nx, h))))

# an own cell stays one when next gains 1
def own.fr(+fi: U32, +nx: U32, +c: U32, +hnx: {U32.to_nat(U32.inc(nx)) == 1n+U32.to_nat(nx) : Nat}, h: {D.Own(fi, nx, c) == True{} : Bool}) ->
  {D.Own(fi, U32.inc(nx), c) == True{} : Bool}:
  +h2 = h
  D.and.i(U32.is_le(fi, c), U32.is_lt(c, U32.inc(nx)), D.and.l(U32.is_le(fi, c), U32.is_lt(c, nx), h2),
    lt.fr(c, nx, hnx, D.and.r(U32.is_le(fi, c), U32.is_lt(c, nx), h2)))

# own or b, when next gains 1
def or.fr(+fi: U32, +nx: U32, +c: U32, +b: Bool, +hnx: {U32.to_nat(U32.inc(nx)) == 1n+U32.to_nat(nx) : Nat},
  h: {Bool.or(D.Own(fi, nx, c), b) == True{} : Bool}) -> {Bool.or(D.Own(fi, U32.inc(nx), c), b) == True{} : Bool}:
  D.or.cases(D.Own(fi, nx, c), b, {Bool.or(D.Own(fi, U32.inc(nx), c), b) == True{} : Bool}, h,
    e => D.or.l(D.Own(fi, U32.inc(nx), c), b, own.fr(fi, nx, c, hnx, e)),
    e => D.or.r(D.Own(fi, U32.inc(nx), c), b, e))

# a cell stays a cell when next gains 1
def cell.fr(+c: U32, +im: U32, +fi: U32, +nx: U32, +hnx: {U32.to_nat(U32.inc(nx)) == 1n+U32.to_nat(nx) : Nat},
  h: {Cr.Cir.is_cell(c, im, fi, nx) == True{} : Bool}) -> {Cr.Cir.is_cell(c, im, fi, U32.inc(nx)) == True{} : Bool}:
  D.or.cases(Bool.and(Bool.not(U32.is_zero(c)), U32.is_le(c, im)), D.Own(fi, nx, c), {Cr.Cir.is_cell(c, im, fi, U32.inc(nx)) == True{} : Bool}, h,
    e => D.or.l(Bool.and(Bool.not(U32.is_zero(c)), U32.is_le(c, im)), D.Own(fi, U32.inc(nx), c), e),
    e => D.or.r(Bool.and(Bool.not(U32.is_zero(c)), U32.is_le(c, im)), D.Own(fi, U32.inc(nx), c), own.fr(fi, nx, c, hnx, e)))

# a node's facts when next gains 1
def ndk.fr(-dk: Bool, -ds: List<&2, Bk.Def>, +im: U32, +fi: U32, +nx: U32, +c: U32, +x: Cr.Cir.Cell, -t: Bk.Term, -tag: U32,
  +hnx: {U32.to_nat(U32.inc(nx)) == 1n+U32.to_nat(nx) : Nat}, h: D.NdK(dk, ds, im, fi, nx, c, x, t, tag)) ->
  D.NdK(dk, ds, im, fi, U32.inc(nx), c, x, t, tag):
  (e0, r0) = h
  (e1, r1) = r0
  (cell.fr(c, im, fi, nx, hnx, e0), (or.fr(fi, nx, c, D.FlW(Cr.Cir.Cell.get(0n, x), 1024), hnx, e1), r1))

# a part's Sp when next gains 1
def sp.fr(+fi: U32, +nx: U32, +c: U32, +y: Cr.Cir.Cell, +hnx: {U32.to_nat(U32.inc(nx)) == 1n+U32.to_nat(nx) : Nat}, h: D.Sp(fi, nx, c, y)) ->
  D.Sp(fi, U32.inc(nx), c, y):
  or.fr(fi, nx, c, D.FlW(Cr.Cir.Cell.get(0n, y), 1024), hnx, h)

# a node is not nx
def ndk.ne(-dk: Bool, -ds: List<&2, Bk.Def>, +im: U32, +fi: U32, +nx: U32, +c: U32, -x: Cr.Cir.Cell, -t: Bk.Term, -tag: U32,
  +him: {U32.is_lt(im, fi) == True{} : Bool}, +hfn: {U32.is_le(fi, nx) == True{} : Bool},
  h: D.NdK(dk, ds, im, fi, nx, c, x, t, tag)) -> {U32.is_eq(c, nx) == False{} : Bool}:
  lt.ne.u(c, nx, cell.lt(c, im, fi, nx, ndk.cell(dk, ds, im, fi, nx, c, x, t, tag, h), him, hfn))

# a part y of c, after the store at nx: its old value (y is not nx)
def pt.fr(+dk: Bool, +t: Bk.Term, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +X: Cr.Cir.Cell, +c: U32, +y: U32,
  +hnx: {U32.to_nat(U32.inc(nx)) == 1n+U32.to_nat(nx) : Nat},
  sp: D.Sp(fi, nx, c, Cr.Cir.Cells.get(m, y)),
  r: D.P2(D.IsCK(dk, ds, Cr.Cir.Cells.set(m, nx, X), im, fi, U32.inc(nx), ks, img, y, Cr.Cir.Cells.get(m, y), t), {U32.is_eq(y, nx) == False{} : Bool})) ->
  D.P2(D.Sp(fi, U32.inc(nx), c, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, nx, X), y)),
    D.IsCK(dk, ds, Cr.Cir.Cells.set(m, nx, X), im, fi, U32.inc(nx), ks, img, y, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, nx, X), y), t)):
  (ih, hne) = r
  +M2 = Cr.Cir.Cells.set(m, nx, X)
  %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, y), Cr.Cir.Cells.get(m, y), D.cl.go(m, y, nx, X, hne)) :
    D.P2(D.Sp(fi, U32.inc(nx), c, _), D.IsCK(dk, ds, M2, im, fi, U32.inc(nx), ks, img, y, _, t))
  (sp.fr(fi, nx, c, Cr.Cir.Cells.get(m, y), hnx, sp), ih)

# a cell of value x stands for its term after the store at nx, next one more;
# and it is not nx
def isck.fr(+dk: Bool, t: Bk.Term, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +X: Cr.Cir.Cell, +c: U32, x: Cr.Cir.Cell,
  +hnx: {U32.to_nat(U32.inc(nx)) == 1n+U32.to_nat(nx) : Nat}, +him: {U32.is_lt(im, fi) == True{} : Bool},
  +hfn: {U32.is_le(fi, nx) == True{} : Bool},
  +h: D.IsCK(dk, ds, m, im, fi, nx, ks, img, c, x, t)) ->
  D.P2(D.IsCK(dk, ds, Cr.Cir.Cells.set(m, nx, X), im, fi, U32.inc(nx), ks, img, c, x, t), {U32.is_eq(c, nx) == False{} : Bool}):
  match t:
    case Bk.Term.Var{+i}:
      match x:
        case Cr.Cir.Cell{+a, +b, +x2, +x3, +x4}:
          match h:
            case Tuple{+nd, hr}:
              ((ndk.fr(dk, ds, im, fi, nx, c, Cr.Cir.Cell{a, b, x2, x3, x4}, Bk.Term.Var{i}, 0, hnx, nd), hr), ndk.ne(dk, ds, im, fi, nx, c, Cr.Cir.Cell{a, b, x2, x3, x4}, Bk.Term.Var{i}, 0, him, hfn, nd))
    case Bk.Term.Ref{+k}:
      match x:
        case Cr.Cir.Cell{+a, +b, +x2, +x3, +x4}:
          match h:
            case Tuple{+nd, hr}:
              ((ndk.fr(dk, ds, im, fi, nx, c, Cr.Cir.Cell{a, b, x2, x3, x4}, Bk.Term.Ref{k}, 1, hnx, nd), hr), ndk.ne(dk, ds, im, fi, nx, c, Cr.Cir.Cell{a, b, x2, x3, x4}, Bk.Term.Ref{k}, 1, him, hfn, nd))
    case Bk.Term.Ann{+t1, +t2}:
      match x:
        case Cr.Cir.Cell{+a, +b, +x2, +x3, +x4}:
          match h:
            case Tuple{+nd, Tuple{Tuple{sp2, h2}, Tuple{sp3, h3}}}:
              ((ndk.fr(dk, ds, im, fi, nx, c, Cr.Cir.Cell{a, b, x2, x3, x4}, Bk.Term.Ann{t1, t2}, 2, hnx, nd), (pt.fr(dk, t1, ds, m, im, fi, nx, ks, img, X, c, x2, hnx, sp2, isck.fr(dk, t1, ds, m, im, fi, nx, ks, img, X, x2, Cr.Cir.Cells.get(m, x2), hnx, him, hfn, h2)), pt.fr(dk, t2, ds, m, im, fi, nx, ks, img, X, c, x3, hnx, sp3, isck.fr(dk, t2, ds, m, im, fi, nx, ks, img, X, x3, Cr.Cir.Cells.get(m, x3), hnx, him, hfn, h3)))), ndk.ne(dk, ds, im, fi, nx, c, Cr.Cir.Cell{a, b, x2, x3, x4}, Bk.Term.Ann{t1, t2}, 2, him, hfn, nd))
    case Bk.Term.Let{+q, +t1, +t2}:
      match x:
        case Cr.Cir.Cell{+a, +b, +x2, +x3, +x4}:
          match h:
            case Tuple{+nd, Tuple{hq, Tuple{Tuple{sp2, h2}, Tuple{sp3, h3}}}}:
              ((ndk.fr(dk, ds, im, fi, nx, c, Cr.Cir.Cell{a, b, x2, x3, x4}, Bk.Term.Let{q, t1, t2}, 3, hnx, nd), (hq, (pt.fr(dk, t1, ds, m, im, fi, nx, ks, img, X, c, x2, hnx, sp2, isck.fr(dk, t1, ds, m, im, fi, nx, ks, img, X, x2, Cr.Cir.Cells.get(m, x2), hnx, him, hfn, h2)), pt.fr(dk, t2, ds, m, im, fi, nx, ks, img, X, c, x3, hnx, sp3, isck.fr(dk, t2, ds, m, im, fi, nx, ks, img, X, x3, Cr.Cir.Cells.get(m, x3), hnx, him, hfn, h3))))), ndk.ne(dk, ds, im, fi, nx, c, Cr.Cir.Cell{a, b, x2, x3, x4}, Bk.Term.Let{q, t1, t2}, 3, him, hfn, nd))
    case Bk.Term.Typ{+t1}:
      match x:
        case Cr.Cir.Cell{+a, +b, +x2, +x3, +x4}:
          match h:
            case Tuple{+nd, Tuple{sp2, h2}}:
              ((ndk.fr(dk, ds, im, fi, nx, c, Cr.Cir.Cell{a, b, x2, x3, x4}, Bk.Term.Typ{t1}, 4, hnx, nd), pt.fr(dk, t1, ds, m, im, fi, nx, ks, img, X, c, x2, hnx, sp2, isck.fr(dk, t1, ds, m, im, fi, nx, ks, img, X, x2, Cr.Cir.Cells.get(m, x2), hnx, him, hfn, h2))), ndk.ne(dk, ds, im, fi, nx, c, Cr.Cir.Cell{a, b, x2, x3, x4}, Bk.Term.Typ{t1}, 4, him, hfn, nd))
    case Bk.Term.Min{+t1, +t2}:
      match x:
        case Cr.Cir.Cell{+a, +b, +x2, +x3, +x4}:
          match h:
            case Tuple{+nd, Tuple{Tuple{sp2, h2}, Tuple{sp3, h3}}}:
              ((ndk.fr(dk, ds, im, fi, nx, c, Cr.Cir.Cell{a, b, x2, x3, x4}, Bk.Term.Min{t1, t2}, 5, hnx, nd), (pt.fr(dk, t1, ds, m, im, fi, nx, ks, img, X, c, x2, hnx, sp2, isck.fr(dk, t1, ds, m, im, fi, nx, ks, img, X, x2, Cr.Cir.Cells.get(m, x2), hnx, him, hfn, h2)), pt.fr(dk, t2, ds, m, im, fi, nx, ks, img, X, c, x3, hnx, sp3, isck.fr(dk, t2, ds, m, im, fi, nx, ks, img, X, x3, Cr.Cir.Cells.get(m, x3), hnx, him, hfn, h3)))), ndk.ne(dk, ds, im, fi, nx, c, Cr.Cir.Cell{a, b, x2, x3, x4}, Bk.Term.Min{t1, t2}, 5, him, hfn, nd))
    case Bk.Term.All{+q, +t1, +t2}:
      match x:
        case Cr.Cir.Cell{+a, +b, +x2, +x3, +x4}:
          match h:
            case Tuple{+nd, Tuple{hq, Tuple{Tuple{sp2, h2}, Tuple{sp3, h3}}}}:
              ((ndk.fr(dk, ds, im, fi, nx, c, Cr.Cir.Cell{a, b, x2, x3, x4}, Bk.Term.All{q, t1, t2}, 6, hnx, nd), (hq, (pt.fr(dk, t1, ds, m, im, fi, nx, ks, img, X, c, x2, hnx, sp2, isck.fr(dk, t1, ds, m, im, fi, nx, ks, img, X, x2, Cr.Cir.Cells.get(m, x2), hnx, him, hfn, h2)), pt.fr(dk, t2, ds, m, im, fi, nx, ks, img, X, c, x3, hnx, sp3, isck.fr(dk, t2, ds, m, im, fi, nx, ks, img, X, x3, Cr.Cir.Cells.get(m, x3), hnx, him, hfn, h3))))), ndk.ne(dk, ds, im, fi, nx, c, Cr.Cir.Cell{a, b, x2, x3, x4}, Bk.Term.All{q, t1, t2}, 6, him, hfn, nd))
    case Bk.Term.Lam{+q, +t1}:
      match x:
        case Cr.Cir.Cell{+a, +b, +x2, +x3, +x4}:
          match h:
            case Tuple{+nd, Tuple{hq, Tuple{sp2, h2}}}:
              ((ndk.fr(dk, ds, im, fi, nx, c, Cr.Cir.Cell{a, b, x2, x3, x4}, Bk.Term.Lam{q, t1}, 7, hnx, nd), (hq, pt.fr(dk, t1, ds, m, im, fi, nx, ks, img, X, c, x2, hnx, sp2, isck.fr(dk, t1, ds, m, im, fi, nx, ks, img, X, x2, Cr.Cir.Cells.get(m, x2), hnx, him, hfn, h2)))), ndk.ne(dk, ds, im, fi, nx, c, Cr.Cir.Cell{a, b, x2, x3, x4}, Bk.Term.Lam{q, t1}, 7, him, hfn, nd))
    case Bk.Term.App{+q, +t1, +t2}:
      match x:
        case Cr.Cir.Cell{+a, +b, +x2, +x3, +x4}:
          match h:
            case Tuple{+nd, Tuple{hq, Tuple{Tuple{sp2, h2}, Tuple{sp3, h3}}}}:
              ((ndk.fr(dk, ds, im, fi, nx, c, Cr.Cir.Cell{a, b, x2, x3, x4}, Bk.Term.App{q, t1, t2}, 8, hnx, nd), (hq, (pt.fr(dk, t1, ds, m, im, fi, nx, ks, img, X, c, x2, hnx, sp2, isck.fr(dk, t1, ds, m, im, fi, nx, ks, img, X, x2, Cr.Cir.Cells.get(m, x2), hnx, him, hfn, h2)), pt.fr(dk, t2, ds, m, im, fi, nx, ks, img, X, c, x3, hnx, sp3, isck.fr(dk, t2, ds, m, im, fi, nx, ks, img, X, x3, Cr.Cir.Cells.get(m, x3), hnx, him, hfn, h3))))), ndk.ne(dk, ds, im, fi, nx, c, Cr.Cir.Cell{a, b, x2, x3, x4}, Bk.Term.App{q, t1, t2}, 8, him, hfn, nd))
    case Bk.Term.Sig{+q, +t1, +t2}:
      match x:
        case Cr.Cir.Cell{+a, +b, +x2, +x3, +x4}:
          match h:
            case Tuple{+nd, Tuple{hq, Tuple{Tuple{sp2, h2}, Tuple{sp3, h3}}}}:
              ((ndk.fr(dk, ds, im, fi, nx, c, Cr.Cir.Cell{a, b, x2, x3, x4}, Bk.Term.Sig{q, t1, t2}, 9, hnx, nd), (hq, (pt.fr(dk, t1, ds, m, im, fi, nx, ks, img, X, c, x2, hnx, sp2, isck.fr(dk, t1, ds, m, im, fi, nx, ks, img, X, x2, Cr.Cir.Cells.get(m, x2), hnx, him, hfn, h2)), pt.fr(dk, t2, ds, m, im, fi, nx, ks, img, X, c, x3, hnx, sp3, isck.fr(dk, t2, ds, m, im, fi, nx, ks, img, X, x3, Cr.Cir.Cells.get(m, x3), hnx, him, hfn, h3))))), ndk.ne(dk, ds, im, fi, nx, c, Cr.Cir.Cell{a, b, x2, x3, x4}, Bk.Term.Sig{q, t1, t2}, 9, him, hfn, nd))
    case Bk.Term.Tup{+q, +t1, +t2}:
      match x:
        case Cr.Cir.Cell{+a, +b, +x2, +x3, +x4}:
          match h:
            case Tuple{+nd, Tuple{hq, Tuple{Tuple{sp2, h2}, Tuple{sp3, h3}}}}:
              ((ndk.fr(dk, ds, im, fi, nx, c, Cr.Cir.Cell{a, b, x2, x3, x4}, Bk.Term.Tup{q, t1, t2}, 10, hnx, nd), (hq, (pt.fr(dk, t1, ds, m, im, fi, nx, ks, img, X, c, x2, hnx, sp2, isck.fr(dk, t1, ds, m, im, fi, nx, ks, img, X, x2, Cr.Cir.Cells.get(m, x2), hnx, him, hfn, h2)), pt.fr(dk, t2, ds, m, im, fi, nx, ks, img, X, c, x3, hnx, sp3, isck.fr(dk, t2, ds, m, im, fi, nx, ks, img, X, x3, Cr.Cir.Cells.get(m, x3), hnx, him, hfn, h3))))), ndk.ne(dk, ds, im, fi, nx, c, Cr.Cir.Cell{a, b, x2, x3, x4}, Bk.Term.Tup{q, t1, t2}, 10, him, hfn, nd))
    case Bk.Term.Prj{+t1}:
      match x:
        case Cr.Cir.Cell{+a, +b, +x2, +x3, +x4}:
          match h:
            case Tuple{+nd, Tuple{sp2, h2}}:
              ((ndk.fr(dk, ds, im, fi, nx, c, Cr.Cir.Cell{a, b, x2, x3, x4}, Bk.Term.Prj{t1}, 11, hnx, nd), pt.fr(dk, t1, ds, m, im, fi, nx, ks, img, X, c, x2, hnx, sp2, isck.fr(dk, t1, ds, m, im, fi, nx, ks, img, X, x2, Cr.Cir.Cells.get(m, x2), hnx, him, hfn, h2))), ndk.ne(dk, ds, im, fi, nx, c, Cr.Cir.Cell{a, b, x2, x3, x4}, Bk.Term.Prj{t1}, 11, him, hfn, nd))
    case Bk.Term.Enu{+k}:
      match x:
        case Cr.Cir.Cell{+a, +b, +x2, +x3, +x4}:
          match h:
            case Tuple{+nd, hr}:
              ((ndk.fr(dk, ds, im, fi, nx, c, Cr.Cir.Cell{a, b, x2, x3, x4}, Bk.Term.Enu{k}, 12, hnx, nd), hr), ndk.ne(dk, ds, im, fi, nx, c, Cr.Cir.Cell{a, b, x2, x3, x4}, Bk.Term.Enu{k}, 12, him, hfn, nd))
    case Bk.Term.Lab{+k}:
      match x:
        case Cr.Cir.Cell{+a, +b, +x2, +x3, +x4}:
          match h:
            case Tuple{+nd, hr}:
              ((ndk.fr(dk, ds, im, fi, nx, c, Cr.Cir.Cell{a, b, x2, x3, x4}, Bk.Term.Lab{k}, 13, hnx, nd), hr), ndk.ne(dk, ds, im, fi, nx, c, Cr.Cir.Cell{a, b, x2, x3, x4}, Bk.Term.Lab{k}, 13, him, hfn, nd))
    case Bk.Term.Mat{+k, +t1, +t2}:
      match x:
        case Cr.Cir.Cell{+a, +b, +x2, +x3, +x4}:
          match h:
            case Tuple{+nd, Tuple{hn, Tuple{Tuple{sp3, h3}, Tuple{sp4, h4}}}}:
              ((ndk.fr(dk, ds, im, fi, nx, c, Cr.Cir.Cell{a, b, x2, x3, x4}, Bk.Term.Mat{k, t1, t2}, 14, hnx, nd), (hn, (pt.fr(dk, t1, ds, m, im, fi, nx, ks, img, X, c, x3, hnx, sp3, isck.fr(dk, t1, ds, m, im, fi, nx, ks, img, X, x3, Cr.Cir.Cells.get(m, x3), hnx, him, hfn, h3)), pt.fr(dk, t2, ds, m, im, fi, nx, ks, img, X, c, x4, hnx, sp4, isck.fr(dk, t2, ds, m, im, fi, nx, ks, img, X, x4, Cr.Cir.Cells.get(m, x4), hnx, him, hfn, h4))))), ndk.ne(dk, ds, im, fi, nx, c, Cr.Cir.Cell{a, b, x2, x3, x4}, Bk.Term.Mat{k, t1, t2}, 14, him, hfn, nd))
    case Bk.Term.Efq{}:
      match x:
        case Cr.Cir.Cell{+a, +b, +x2, +x3, +x4}:
          (ndk.fr(dk, ds, im, fi, nx, c, Cr.Cir.Cell{a, b, x2, x3, x4}, Bk.Term.Efq{}, 15, hnx, h), ndk.ne(dk, ds, im, fi, nx, c, Cr.Cir.Cell{a, b, x2, x3, x4}, Bk.Term.Efq{}, 15, him, hfn, h))
    case Bk.Term.Eql{+t1, +t2, +t3}:
      match x:
        case Cr.Cir.Cell{+a, +b, +x2, +x3, +x4}:
          match h:
            case Tuple{+nd, Tuple{Tuple{sp2, h2}, Tuple{Tuple{sp3, h3}, Tuple{sp4, h4}}}}:
              ((ndk.fr(dk, ds, im, fi, nx, c, Cr.Cir.Cell{a, b, x2, x3, x4}, Bk.Term.Eql{t1, t2, t3}, 16, hnx, nd), (pt.fr(dk, t1, ds, m, im, fi, nx, ks, img, X, c, x2, hnx, sp2, isck.fr(dk, t1, ds, m, im, fi, nx, ks, img, X, x2, Cr.Cir.Cells.get(m, x2), hnx, him, hfn, h2)), (pt.fr(dk, t2, ds, m, im, fi, nx, ks, img, X, c, x3, hnx, sp3, isck.fr(dk, t2, ds, m, im, fi, nx, ks, img, X, x3, Cr.Cir.Cells.get(m, x3), hnx, him, hfn, h3)), pt.fr(dk, t3, ds, m, im, fi, nx, ks, img, X, c, x4, hnx, sp4, isck.fr(dk, t3, ds, m, im, fi, nx, ks, img, X, x4, Cr.Cir.Cells.get(m, x4), hnx, him, hfn, h4))))), ndk.ne(dk, ds, im, fi, nx, c, Cr.Cir.Cell{a, b, x2, x3, x4}, Bk.Term.Eql{t1, t2, t3}, 16, him, hfn, nd))
    case Bk.Term.Rfl{}:
      match x:
        case Cr.Cir.Cell{+a, +b, +x2, +x3, +x4}:
          (ndk.fr(dk, ds, im, fi, nx, c, Cr.Cir.Cell{a, b, x2, x3, x4}, Bk.Term.Rfl{}, 17, hnx, h), ndk.ne(dk, ds, im, fi, nx, c, Cr.Cir.Cell{a, b, x2, x3, x4}, Bk.Term.Rfl{}, 17, him, hfn, h))
    case Bk.Term.Rwt{+t1, +t2, +t3}:
      match x:
        case Cr.Cir.Cell{+a, +b, +x2, +x3, +x4}:
          match h:
            case Tuple{+nd, Tuple{Tuple{sp2, h2}, Tuple{Tuple{sp3, h3}, Tuple{sp4, h4}}}}:
              ((ndk.fr(dk, ds, im, fi, nx, c, Cr.Cir.Cell{a, b, x2, x3, x4}, Bk.Term.Rwt{t1, t2, t3}, 18, hnx, nd), (pt.fr(dk, t1, ds, m, im, fi, nx, ks, img, X, c, x2, hnx, sp2, isck.fr(dk, t1, ds, m, im, fi, nx, ks, img, X, x2, Cr.Cir.Cells.get(m, x2), hnx, him, hfn, h2)), (pt.fr(dk, t2, ds, m, im, fi, nx, ks, img, X, c, x3, hnx, sp3, isck.fr(dk, t2, ds, m, im, fi, nx, ks, img, X, x3, Cr.Cir.Cells.get(m, x3), hnx, him, hfn, h3)), pt.fr(dk, t3, ds, m, im, fi, nx, ks, img, X, c, x4, hnx, sp4, isck.fr(dk, t3, ds, m, im, fi, nx, ks, img, X, x4, Cr.Cir.Cells.get(m, x4), hnx, him, hfn, h4))))), ndk.ne(dk, ds, im, fi, nx, c, Cr.Cir.Cell{a, b, x2, x3, x4}, Bk.Term.Rwt{t1, t2, t3}, 18, him, hfn, nd))

# a cell stands for its term after the store at nx, next one more (from
# isck.fr: it is not nx, so it keeps its value)
def isk.fr.at(+dk: Bool, +t: Bk.Term, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +X: Cr.Cir.Cell, +c: U32,
  r: D.P2(D.IsCK(dk, ds, Cr.Cir.Cells.set(m, nx, X), im, fi, U32.inc(nx), ks, img, c, Cr.Cir.Cells.get(m, c), t), {U32.is_eq(c, nx) == False{} : Bool})) ->
  D.IsK(dk, ds, Cr.Cir.Cells.set(m, nx, X), im, fi, U32.inc(nx), ks, img, c, t):
  (ih, hne) = r
  +M2 = Cr.Cir.Cells.set(m, nx, X)
  %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, c), Cr.Cir.Cells.get(m, c), D.cl.go(m, c, nx, X, hne)) :
    D.IsCK(dk, ds, M2, im, fi, U32.inc(nx), ks, img, c, _, t)
  ih

def isk.fr(+dk: Bool, +t: Bk.Term, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +X: Cr.Cir.Cell, +c: U32,
  +hnx: {U32.to_nat(U32.inc(nx)) == 1n+U32.to_nat(nx) : Nat}, +him: {U32.is_lt(im, fi) == True{} : Bool},
  +hfn: {U32.is_le(fi, nx) == True{} : Bool},
  h: D.IsK(dk, ds, m, im, fi, nx, ks, img, c, t)) -> D.IsK(dk, ds, Cr.Cir.Cells.set(m, nx, X), im, fi, U32.inc(nx), ks, img, c, t):
  isk.fr.at(dk, t, ds, m, im, fi, nx, ks, img, X, c, isck.fr(dk, t, ds, m, im, fi, nx, ks, img, X, c, Cr.Cir.Cells.get(m, c), hnx, him, hfn, h))

def rtsk.fr(+dk: Bool, rs: List<&2, D.Rt>, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +X: Cr.Cir.Cell,
  +hnx: {U32.to_nat(U32.inc(nx)) == 1n+U32.to_nat(nx) : Nat}, +him: {U32.is_lt(im, fi) == True{} : Bool},
  +hfn: {U32.is_le(fi, nx) == True{} : Bool},
  h: D.RtsK(dk, ds, m, im, fi, nx, ks, img, rs)) -> D.RtsK(dk, ds, Cr.Cir.Cells.set(m, nx, X), im, fi, U32.inc(nx), ks, img, rs):
  match rs:
    case Nil{}:
      Unit{}
    case Con{D.Rt{+c, +u}, +rest}:
      match h:
        case Tuple{hu, hr}:
          (isk.fr(dk, u, ds, m, im, fi, nx, ks, img, X, c, hnx, him, hfn, hu), rtsk.fr(dk, rest, ds, m, im, fi, nx, ks, img, X, hnx, him, hfn, hr))

# a frame's part b after the store at nx
def frsb.fr(+dk: Bool, kind: D.FK, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +X: Cr.Cir.Cell, +c: U32, +b: Bk.Term,
  +hnx: {U32.to_nat(U32.inc(nx)) == 1n+U32.to_nat(nx) : Nat}, +him: {U32.is_lt(im, fi) == True{} : Bool},
  +hfn: {U32.is_le(fi, nx) == True{} : Bool},
  h: D.Frs.bK(dk, ds, m, im, fi, nx, ks, img, c, kind, b)) ->
  D.Frs.bK(dk, ds, Cr.Cir.Cells.set(m, nx, X), im, fi, U32.inc(nx), ks, img, c, kind, b):
  match kind:
    case D.FK.rwt{}:
      isk.fr(dk, b, ds, m, im, fi, nx, ks, img, X, c, hnx, him, hfn, h)
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

# the frames after the store at nx: no frame is nx
def frsk.fr(+dk: Bool, fs: List<&2, D.AF>, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +X: Cr.Cir.Cell, +fr: U32,
  +hnx: {U32.to_nat(U32.inc(nx)) == 1n+U32.to_nat(nx) : Nat}, +him: {U32.is_lt(im, fi) == True{} : Bool},
  +hfn: {U32.is_le(fi, nx) == True{} : Bool},
  h: D.FrsK(dk, ds, m, im, fi, nx, ks, img, ps, fr, fs)) -> D.FrsK(dk, ds, Cr.Cir.Cells.set(m, nx, X), im, fi, U32.inc(nx), ks, img, ps, fr, fs):
  match fs:
    case Nil{}:
      h
    case Con{D.AF{+kind, +q, +k, +a, +b}, +rest}:
      match h:
        case Tuple{e0, Tuple{+ev, Tuple{eo, Tuple{es, Tuple{em, Tuple{etg, Tuple{eq, Tuple{ek, Tuple{ia, Tuple{ib, ir}}}}}}}}}}:
          +M2 = Cr.Cir.Cells.set(m, nx, X)
          +N2 = U32.inc(nx)
          D.frs.uck(dk, ds, M2, im, fi, N2, ks, img, ps, fr, Con{D.AF{kind, q, k, a, b}, rest},
            D.frsc.atk(dk, ds, M2, im, fi, N2, ks, img, ps, fr, Cr.Cir.Cells.get(M2, fr), Cr.Cir.Cells.get(m, fr), Con{D.AF{kind, q, k, a, b}, rest},
              D.cl.go(m, fr, nx, X, lt.ne.u(fr, nx, cell.lt(fr, im, fi, nx, ev, him, hfn))),
              (e0, (cell.fr(fr, im, fi, nx, hnx, ev), (own.fr(fi, nx, fr, hnx, eo), (es, (em, (etg, (eq, (ek,
                (isk.fr(dk, a, ds, m, im, fi, nx, ks, img, X, D.Fd(2n, m, fr), hnx, him, hfn, ia),
                (frsb.fr(dk, kind, ds, m, im, fi, nx, ks, img, X, D.Fd(3n, m, fr), b, hnx, him, hfn, ib),
                  frsk.fr(dk, rest, ds, m, im, fi, nx, ks, img, ps, X, D.Fd(1n, m, fr), hnx, him, hfn, ir)))))))))))))

# a store at next keeps the terms and frames that HS holds
def fresh.top(+dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32,
  +ps: List<&2, U32>, +x: Cr.Cir.Cell,
  hs: D.HSK(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps)) ->
  D.P2(D.RtsK(dk, ds, Cr.Cir.Cells.set(m, nx, x), im, fi, U32.inc(nx), ks, img, os),
    D.P2(D.RtsK(dk, ds, Cr.Cir.Cells.set(m, nx, x), im, fi, U32.inc(nx), ks, img, bs),
      D.FrsK(dk, ds, Cr.Cir.Cells.set(m, nx, x), im, fi, U32.inc(nx), ks, img, ps, sp, fs))):
  match hs:
    case Tuple{hos, Tuple{hbs, Tuple{_, Tuple{hfrs, Tuple{+hheap, himg}}}}}:
      +rs = D.Rt.cells(os)
      +hnx = nx.inc(nx, heap.room(m, nx, fi, im, rs, pend, ps, hheap))
      +him = img.lt(dk, ds, ks, img, m, im, fi, nx, himg)
      +hfn = heap.fn(m, nx, fi, im, rs, pend, ps, hheap)
      (rtsk.fr(dk, os, ds, m, im, fi, nx, ks, img, x, hnx, him, hfn, hos),
        (rtsk.fr(dk, bs, ds, m, im, fi, nx, ks, img, x, hnx, him, hfn, hbs),
          frsk.fr(dk, fs, ds, m, im, fi, nx, ks, img, ps, x, sp, hnx, him, hfn, hfrs)))

# A store of a cell that holds the owned roots us
# -----------------------------------------------
#
# A store at z (own, nothing points to it, it holds no pointer) of a cell x
# whose pointers are the roots us: the cells' pointers to each cell c gain
# z's (pc.mv: z is one of the cells from fi, once), which us lose as roots,
# so every count stays (ptr.st); x is no term cell; z points to term cells
# below next (the roots of us stand for their terms); z is no frame.

# (a + b) + c = (c + b) + a
def add.swap3(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(Nat.add(c, b), a) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(a, b), c), Nat.add(c, Nat.add(a, b)), Nat.add(Nat.add(c, b), a),
    add.comm(Nat.add(a, b), c),
    Equal.trans(Nat, Nat.add(c, Nat.add(a, b)), Nat.add(c, Nat.add(b, a)), Nat.add(Nat.add(c, b), a),
      Equal.cong(Nat, Nat, y => Nat.add(c, y), Nat.add(a, b), Nat.add(b, a), add.comm(a, b)),
      Equal.sym(Nat, Nat.add(Nat.add(c, b), a), Nat.add(c, Nat.add(b, a)), N.add_assoc(c, b, a))))

# o, past z, is not z
def ne.gt.b(b: Bool, +o: U32, +z: U32, eb: {U32.is_eq(o, z) == b : Bool}, h: N.Le(1n+U32.to_nat(z), U32.to_nat(o))) ->
  {U32.is_eq(o, z) == False{} : Bool}:
  match b:
    case False{}:
      eb
    case True{}:
      +e = D.u32.eq(o, z, eb)
      Empty.absurd({U32.is_eq(o, z) == False{} : Bool},
        N.not_succ_le(U32.to_nat(z), (%e : N.Le(1n+U32.to_nat(z), U32.to_nat(_)); h)))

def ne.gt(+o: U32, +z: U32, h: N.Le(1n+U32.to_nat(z), U32.to_nat(o))) -> {U32.is_eq(o, z) == False{} : Bool}:
  ne.gt.b(U32.is_eq(o, z), o, z, {==}, h)

# a store to z keeps the pointers of the k cells from o, all past z and below nx
def pc.out(k: Nat, +m: Cr.Cir.Cells, +z: U32, +x: Cr.Cir.Cell, +ps: List<&2, U32>, +o: U32, +c: U32, +nx: U32,
  hz: N.Le(1n+U32.to_nat(z), U32.to_nat(o)), hb: N.Le(Nat.add(U32.to_nat(o), k), U32.to_nat(nx)),
  ht: {D.TblR(k, m, o, z) == True{} : Bool}) ->
  {D.Pc(k, Cr.Cir.Cells.set(m, z, x), ps, o, c) == D.Pc(k, m, ps, o, c) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+(+j):
      +M2 = Cr.Cir.Cells.set(m, z, x)
      +ht2 = ht
      +hz2 = hz
      +hb2 = hb
      +lt1 = N.le_trans(1n+U32.to_nat(o), Nat.add(U32.to_nat(o), 1n+j), U32.to_nat(nx), N.lt_add(U32.to_nat(o), j), hb2)
      +ei = D.u.inc(o, nx, lt1)
      +hzi = N.le_rw_r(1n+U32.to_nat(z), 1n+U32.to_nat(o), U32.to_nat(U32.inc(o)),
        Equal.sym(Nat, U32.to_nat(U32.inc(o)), 1n+U32.to_nat(o), ei), N.le_succ(1n+U32.to_nat(z), U32.to_nat(o), hz2))
      +hbi = N.le_rw_l(Nat.add(U32.to_nat(o), 1n+j), Nat.add(U32.to_nat(U32.inc(o)), j), U32.to_nat(nx),
        Equal.trans(Nat, Nat.add(U32.to_nat(o), 1n+j), 1n+Nat.add(U32.to_nat(o), j), Nat.add(U32.to_nat(U32.inc(o)), j),
          N.add_succ_r(U32.to_nat(o), j),
          Equal.sym(Nat, Nat.add(U32.to_nat(U32.inc(o)), j), 1n+Nat.add(U32.to_nat(o), j),
            Equal.cong(Nat, Nat, y => Nat.add(y, j), U32.to_nat(U32.inc(o)), 1n+U32.to_nat(o), ei))), hb2)
      +e1 = D.fs.eq(m, z, x, ps, o, ne.gt(o, z, hz2), D.and.l(D.TblAt(m, o, z), D.TblR(j, m, U32.inc(o), z), ht2))
      +e2 = pc.out(j, m, z, x, ps, U32.inc(o), c, nx, hzi, hbi, D.and.r(D.TblAt(m, o, z), D.TblR(j, m, U32.inc(o), z), ht2))
      %Equal.sym(List<&2, U32>, D.Fs(M2, ps, o), D.Fs(m, ps, o), e1) :
        {Nat.add(D.RcL(_, c), D.Pc(j, M2, ps, U32.inc(o), c)) == Nat.add(D.RcL(D.Fs(m, ps, o), c), D.Pc(j, m, ps, U32.inc(o), c)) : Nat}
      %Equal.sym(Nat, D.Pc(j, M2, ps, U32.inc(o), c), D.Pc(j, m, ps, U32.inc(o), c), e2) :
        {Nat.add(D.RcL(D.Fs(m, ps, o), c), _) == Nat.add(D.RcL(D.Fs(m, ps, o), c), D.Pc(j, m, ps, U32.inc(o), c)) : Nat}
      {==}

# the step of pc.mv: o is z, or z is past o
def pc.mv.b(bb: Bool, +j: Nat, +m: Cr.Cir.Cells, +z: U32, +x: Cr.Cir.Cell, +ps: List<&2, U32>, +o: U32, +c: U32, +nx: U32,
  +eb: {U32.is_eq(o, z) == bb : Bool}, +h1: N.Le(U32.to_nat(o), U32.to_nat(z)),
  +h2: N.Le(1n+U32.to_nat(z), Nat.add(U32.to_nat(o), 1n+j)), +hb: N.Le(Nat.add(U32.to_nat(o), 1n+j), U32.to_nat(nx)),
  +ht: {D.TblR(1n+j, m, o, z) == True{} : Bool},
  ih: N.Le(U32.to_nat(U32.inc(o)), U32.to_nat(z)) -> N.Le(1n+U32.to_nat(z), Nat.add(U32.to_nat(U32.inc(o)), j)) ->
    N.Le(Nat.add(U32.to_nat(U32.inc(o)), j), U32.to_nat(nx)) -> {D.TblR(j, m, U32.inc(o), z) == True{} : Bool} ->
    {Nat.add(D.Pc(j, Cr.Cir.Cells.set(m, z, x), ps, U32.inc(o), c), D.RcL(D.Fs(m, ps, z), c)) ==
      Nat.add(D.Pc(j, m, ps, U32.inc(o), c), D.RcL(D.Fs(Cr.Cir.Cells.set(m, z, x), ps, z), c)) : Nat}) ->
  {Nat.add(D.Pc(1n+j, Cr.Cir.Cells.set(m, z, x), ps, o, c), D.RcL(D.Fs(m, ps, z), c)) ==
    Nat.add(D.Pc(1n+j, m, ps, o, c), D.RcL(D.Fs(Cr.Cir.Cells.set(m, z, x), ps, z), c)) : Nat}:
  match bb:
    case True{}:
      +M2 = Cr.Cir.Cells.set(m, z, x)
      +R0 = D.RcL(D.Fs(m, ps, z), c)
      +R1 = D.RcL(D.Fs(M2, ps, z), c)
      +eadd = Equal.trans(Nat, Nat.add(U32.to_nat(o), 1n+j), 1n+Nat.add(U32.to_nat(o), j), Nat.add(1n+U32.to_nat(o), j),
        N.add_succ_r(U32.to_nat(o), j), {==})
      +eo = D.u32.eq(o, z, eb)
      +lt1 = N.le_trans(1n+U32.to_nat(o), Nat.add(U32.to_nat(o), 1n+j), U32.to_nat(nx), N.lt_add(U32.to_nat(o), j), hb)
      +ei = D.u.inc(o, nx, lt1)
      +hzo = {(%eo : N.Le(1n+U32.to_nat(_), U32.to_nat(U32.inc(o)));
        N.le_rw_r(1n+U32.to_nat(o), 1n+U32.to_nat(o), U32.to_nat(U32.inc(o)), Equal.sym(Nat, U32.to_nat(U32.inc(o)), 1n+U32.to_nat(o), ei),
          N.le_refl(1n+U32.to_nat(o)))) : N.Le(1n+U32.to_nat(z), U32.to_nat(U32.inc(o)))}
      +hbi = N.le_rw_l(Nat.add(U32.to_nat(o), 1n+j), Nat.add(U32.to_nat(U32.inc(o)), j), U32.to_nat(nx),
        Equal.trans(Nat, Nat.add(U32.to_nat(o), 1n+j), Nat.add(1n+U32.to_nat(o), j), Nat.add(U32.to_nat(U32.inc(o)), j), eadd,
          Equal.sym(Nat, Nat.add(U32.to_nat(U32.inc(o)), j), Nat.add(1n+U32.to_nat(o), j),
            Equal.cong(Nat, Nat, y => Nat.add(y, j), U32.to_nat(U32.inc(o)), 1n+U32.to_nat(o), ei))), hb)
      +e2 = pc.out(j, m, z, x, ps, U32.inc(o), c, nx, hzo, hbi, D.and.r(D.TblAt(m, o, z), D.TblR(j, m, U32.inc(o), z), ht))
      %Equal.sym(U32, o, z, eo) :
        {Nat.add(Nat.add(D.RcL(D.Fs(M2, ps, _), c), D.Pc(j, M2, ps, U32.inc(o), c)), R0) ==
          Nat.add(Nat.add(D.RcL(D.Fs(m, ps, _), c), D.Pc(j, m, ps, U32.inc(o), c)), R1) : Nat}
      %Equal.sym(Nat, D.Pc(j, M2, ps, U32.inc(o), c), D.Pc(j, m, ps, U32.inc(o), c), e2) :
        {Nat.add(Nat.add(R1, _), R0) == Nat.add(Nat.add(R0, D.Pc(j, m, ps, U32.inc(o), c)), R1) : Nat}
      add.swap3(R1, D.Pc(j, m, ps, U32.inc(o), c), R0)
    case False{}:
      +M2 = Cr.Cir.Cells.set(m, z, x)
      +R0 = D.RcL(D.Fs(m, ps, z), c)
      +R1 = D.RcL(D.Fs(M2, ps, z), c)
      +eadd = Equal.trans(Nat, Nat.add(U32.to_nat(o), 1n+j), 1n+Nat.add(U32.to_nat(o), j), Nat.add(1n+U32.to_nat(o), j),
        N.add_succ_r(U32.to_nat(o), j), {==})
      +lt = D.lt.ne(U32.cmp(o, z), U32.to_nat(o), U32.to_nat(z), N.U32.rel(o, z), eb, h1)
      +ei = D.u.inc(o, z, lt)
      +ej = Equal.trans(Nat, Nat.add(U32.to_nat(o), 1n+j), Nat.add(1n+U32.to_nat(o), j), Nat.add(U32.to_nat(U32.inc(o)), j), eadd,
        Equal.sym(Nat, Nat.add(U32.to_nat(U32.inc(o)), j), Nat.add(1n+U32.to_nat(o), j),
          Equal.cong(Nat, Nat, y => Nat.add(y, j), U32.to_nat(U32.inc(o)), 1n+U32.to_nat(o), ei)))
      +h1b = N.le_rw_l(1n+U32.to_nat(o), U32.to_nat(U32.inc(o)), U32.to_nat(z), Equal.sym(Nat, U32.to_nat(U32.inc(o)), 1n+U32.to_nat(o), ei), lt)
      +h2b = N.le_rw_r(1n+U32.to_nat(z), Nat.add(U32.to_nat(o), 1n+j), Nat.add(U32.to_nat(U32.inc(o)), j), ej, h2)
      +hbb = N.le_rw_l(Nat.add(U32.to_nat(o), 1n+j), Nat.add(U32.to_nat(U32.inc(o)), j), U32.to_nat(nx), ej, hb)
      +e1 = D.fs.eq(m, z, x, ps, o, eb, D.and.l(D.TblAt(m, o, z), D.TblR(j, m, U32.inc(o), z), ht))
      +e2 = ih(h1b, h2b, hbb, D.and.r(D.TblAt(m, o, z), D.TblR(j, m, U32.inc(o), z), ht))
      +A = D.RcL(D.Fs(m, ps, o), c)
      +P1 = D.Pc(j, M2, ps, U32.inc(o), c)
      +P0 = D.Pc(j, m, ps, U32.inc(o), c)
      %Equal.sym(List<&2, U32>, D.Fs(M2, ps, o), D.Fs(m, ps, o), e1) :
        {Nat.add(Nat.add(D.RcL(_, c), P1), R0) == Nat.add(Nat.add(A, P0), R1) : Nat}
      Equal.trans(Nat, Nat.add(Nat.add(A, P1), R0), Nat.add(A, Nat.add(P1, R0)), Nat.add(Nat.add(A, P0), R1),
        N.add_assoc(A, P1, R0),
        Equal.trans(Nat, Nat.add(A, Nat.add(P1, R0)), Nat.add(A, Nat.add(P0, R1)), Nat.add(Nat.add(A, P0), R1),
          Equal.cong(Nat, Nat, y => Nat.add(A, y), Nat.add(P1, R0), Nat.add(P0, R1), e2),
          Equal.sym(Nat, Nat.add(Nat.add(A, P0), R1), Nat.add(A, Nat.add(P0, R1)), N.add_assoc(A, P0, R1))))

# a store to z, one of the k cells from o (below nx), trades z's pointers in Pc
def pc.mv(k: Nat, +m: Cr.Cir.Cells, +z: U32, +x: Cr.Cir.Cell, +ps: List<&2, U32>, +o: U32, +c: U32, +nx: U32,
  h1: N.Le(U32.to_nat(o), U32.to_nat(z)), h2: N.Le(1n+U32.to_nat(z), Nat.add(U32.to_nat(o), k)),
  hb: N.Le(Nat.add(U32.to_nat(o), k), U32.to_nat(nx)), ht: {D.TblR(k, m, o, z) == True{} : Bool}) ->
  {Nat.add(D.Pc(k, Cr.Cir.Cells.set(m, z, x), ps, o, c), D.RcL(D.Fs(m, ps, z), c)) ==
    Nat.add(D.Pc(k, m, ps, o, c), D.RcL(D.Fs(Cr.Cir.Cells.set(m, z, x), ps, z), c)) : Nat}:
  match k:
    case 0n:
      Empty.absurd({Nat.add(0n, D.RcL(D.Fs(m, ps, z), c)) == Nat.add(0n, D.RcL(D.Fs(Cr.Cir.Cells.set(m, z, x), ps, z), c)) : Nat},
        N.not_succ_le(U32.to_nat(z), N.le_trans(1n+U32.to_nat(z), U32.to_nat(o), U32.to_nat(z),
          N.le_rw_r(1n+U32.to_nat(z), Nat.add(U32.to_nat(o), 0n), U32.to_nat(o), N.add_zero(U32.to_nat(o)), h2), h1)))
    case 1n+(+j):
      pc.mv.b(U32.is_eq(o, z), j, m, z, x, ps, o, c, nx, {==}, h1, h2, hb, ht,
        a => b => d => e => pc.mv(j, m, z, x, ps, U32.inc(o), c, nx, a, b, d, e))

# the cells of xs ++ ys that are c: those of xs and of ys
def rcl.app(xs: List<&2, U32>, +ys: List<&2, U32>, +c: U32) ->
  {D.RcL(List.append(&2, U32, xs, ys), c) == Nat.add(D.RcL(xs, c), D.RcL(ys, c)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+r, +rest}:
      +A = D.Nat.of(U32.is_eq(r, c))
      Equal.trans(Nat, Nat.add(A, D.RcL(List.append(&2, U32, rest, ys), c)), Nat.add(A, Nat.add(D.RcL(rest, c), D.RcL(ys, c))),
        Nat.add(Nat.add(A, D.RcL(rest, c)), D.RcL(ys, c)),
        Equal.cong(Nat, Nat, w => Nat.add(A, w), D.RcL(List.append(&2, U32, rest, ys), c), Nat.add(D.RcL(rest, c), D.RcL(ys, c)), rcl.app(rest, ys, c)),
        Equal.sym(Nat, Nat.add(Nat.add(A, D.RcL(rest, c)), D.RcL(ys, c)), Nat.add(A, Nat.add(D.RcL(rest, c), D.RcL(ys, c))),
          N.add_assoc(A, D.RcL(rest, c), D.RcL(ys, c))))

# the cells of the roots us ++ os: those of us, then of os
def cells.app(us: List<&2, D.Rt>, +os: List<&2, D.Rt>) ->
  {D.Rt.cells(List.append(&2, D.Rt, us, os)) == List.append(&2, U32, D.Rt.cells(us), D.Rt.cells(os)) : List<&2, U32>}:
  match us:
    case Nil{}:
      {==}
    case Con{D.Rt{+c, +u}, +rest}:
      Equal.cong(List<&2, U32>, List<&2, U32>, w => Con{c, w}, D.Rt.cells(List.append(&2, D.Rt, rest, os)),
        List.append(&2, U32, D.Rt.cells(rest), D.Rt.cells(os)), cells.app(rest, os))

def rcl.us(+us: List<&2, D.Rt>, +os: List<&2, D.Rt>, +c: U32) ->
  {D.RcL(D.Rt.cells(List.append(&2, D.Rt, us, os)), c) == Nat.add(D.RcL(D.Rt.cells(us), c), D.RcL(D.Rt.cells(os), c)) : Nat}:
  %Equal.sym(List<&2, U32>, D.Rt.cells(List.append(&2, D.Rt, us, os)), List.append(&2, U32, D.Rt.cells(us), D.Rt.cells(os)), cells.app(us, os)) :
    {D.RcL(_, c) == Nat.add(D.RcL(D.Rt.cells(us), c), D.RcL(D.Rt.cells(os), c)) : Nat}
  rcl.app(D.Rt.cells(us), D.Rt.cells(os), c)

# the counts after the store at z: z's pointers, the roots us, leave the roots
def ptr.st(+m: Cr.Cir.Cells, +nx: U32, +fi: U32, +ps: List<&2, U32>, +z: U32, +x: Cr.Cir.Cell, +us: List<&2, D.Rt>,
  +os: List<&2, D.Rt>, +c: U32,
  hf0: {D.Fs(m, ps, z) == Nil{} : List<&2, U32>}, hf1: {D.Fs(Cr.Cir.Cells.set(m, z, x), ps, z) == D.Rt.cells(us) : List<&2, U32>},
  hzo: {D.Own(fi, nx, z) == True{} : Bool}, ht: {D.TblR(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, z) == True{} : Bool}) ->
  {D.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), Cr.Cir.Cells.set(m, z, x), fi, ps, D.Rt.cells(os), c) ==
    D.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, D.Rt.cells(List.append(&2, D.Rt, us, os)), c) : Nat}:
  +o2 = hzo
  +M2 = Cr.Cir.Cells.set(m, z, x)
  +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
  +h1 = D.u.le(fi, z, D.and.l(U32.is_le(fi, z), U32.is_lt(z, nx), o2))
  +hl = D.u.lt(z, nx, D.and.r(U32.is_le(fi, z), U32.is_lt(z, nx), o2))
  +es = D.add.sub(U32.to_nat(fi), U32.to_nat(nx), N.le_trans(U32.to_nat(fi), U32.to_nat(z), U32.to_nat(nx), h1, N.weaken(U32.to_nat(z), U32.to_nat(nx), hl)))
  +es2 = Equal.sym(Nat, Nat.add(U32.to_nat(fi), n), U32.to_nat(nx), es)
  +h2 = N.le_rw_r(1n+U32.to_nat(z), U32.to_nat(nx), Nat.add(U32.to_nat(fi), n), es2, hl)
  +hb = N.le_rw_l(U32.to_nat(nx), Nat.add(U32.to_nat(fi), n), U32.to_nat(nx), es2, N.le_refl(U32.to_nat(nx)))
  +P1 = D.Pc(n, M2, ps, fi, c)
  +P0 = D.Pc(n, m, ps, fi, c)
  +U = D.RcL(D.Rt.cells(us), c)
  +O = D.RcL(D.Rt.cells(os), c)
  +E1 = {(%hf0 : {Nat.add(P1, D.RcL(_, c)) == Nat.add(P0, U) : Nat};
      (%hf1 : {Nat.add(P1, D.RcL(D.Fs(m, ps, z), c)) == Nat.add(P0, D.RcL(_, c)) : Nat}; pc.mv(n, m, z, x, ps, fi, c, nx, h1, h2, hb, ht))) :
    {Nat.add(P1, 0n) == Nat.add(P0, U) : Nat}}
  +E2 = Equal.trans(Nat, P1, Nat.add(P1, 0n), Nat.add(P0, U), Equal.sym(Nat, Nat.add(P1, 0n), P1, N.add_zero(P1)), E1)
  %Equal.sym(Nat, D.RcL(D.Rt.cells(List.append(&2, D.Rt, us, os)), c), Nat.add(U, O), rcl.us(us, os, c)) :
    {Nat.add(P1, O) == Nat.add(P0, _) : Nat}
  Equal.trans(Nat, Nat.add(P1, O), Nat.add(Nat.add(P0, U), O), Nat.add(P0, Nat.add(U, O)),
    Equal.cong(Nat, Nat, w => Nat.add(w, O), P1, Nat.add(P0, U), E2), N.add_assoc(P0, U, O))

# a tag of 32 or more is no term's
def lt19.ge.b(b: Bool, +t: U32, eb: {U32.is_lt(t, 19) == b : Bool}, h: {U32.is_le(32, t) == True{} : Bool}) ->
  {U32.is_lt(t, 19) == False{} : Bool}:
  match b:
    case False{}:
      eb
    case True{}:
      Empty.absurd({U32.is_lt(t, 19) == False{} : Bool},
        N.le_trans(33n, 1n+U32.to_nat(t), 19n, D.u.le(32, t, h), D.u.lt(t, 19, eb)))

def lt19.ge(+t: U32, h: {U32.is_le(32, t) == True{} : Bool}) -> {U32.is_lt(t, 19) == False{} : Bool}:
  lt19.ge.b(U32.is_lt(t, 19), t, {==}, h)

# a tag below 32, or 41 or more, is no frame's tag
def nf.tag.b(a: Bool, b: Bool, +t: U32, ea: {U32.is_le(32, t) == a : Bool}, eb: {U32.is_le(t, 40) == b : Bool},
  h: {Bool.or(U32.is_lt(t, 32), U32.is_le(41, t)) == True{} : Bool}) -> {Bool.not(Bool.and(a, b)) == True{} : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      match b:
        case False{}:
          {==}
        case True{}:
          +l32 = D.u.le(32, t, ea)
          +l40 = D.u.le(t, 40, eb)
          D.or.cases(U32.is_lt(t, 32), U32.is_le(41, t), {Bool.not(Bool.and(True{}, True{})) == True{} : Bool}, h,
            e => Empty.absurd({Bool.not(Bool.and(True{}, True{})) == True{} : Bool},
              N.not_succ_le(U32.to_nat(t), N.le_trans(1n+U32.to_nat(t), 32n, U32.to_nat(t), D.u.lt(t, 32, e), l32))),
            e => Empty.absurd({Bool.not(Bool.and(True{}, True{})) == True{} : Bool}, N.le_trans(41n, U32.to_nat(t), 40n, D.u.le(41, t, e), l40)))

def nf.tag(+t: U32, h: {Bool.or(U32.is_lt(t, 32), U32.is_le(41, t)) == True{} : Bool}) ->
  {Bool.not(Bool.and(U32.is_le(32, t), U32.is_le(t, 40))) == True{} : Bool}:
  nf.tag.b(U32.is_le(32, t), U32.is_le(t, 40), t, {==}, {==}, h)

# the count condition at o after the store at z (x is no term cell), with
# the roots rs1 before and rs2 after
def cntc.st.b(b: Bool, +m: Cr.Cir.Cells, +z: U32, +x: Cr.Cir.Cell, +o: U32, +n: Nat, +fi: U32, +ps: List<&2, U32>,
  +rs1: List<&2, U32>, +rs2: List<&2, U32>, eb: {U32.is_eq(o, z) == b : Bool},
  hxt: {U32.is_lt(D.TgW(Cr.Cir.Cell.get(0n, x)), 19) == False{} : Bool},
  hP: {D.Ptr(n, Cr.Cir.Cells.set(m, z, x), fi, ps, rs2, o) == D.Ptr(n, m, fi, ps, rs1, o) : Nat},
  h: {D.CntC(Cr.Cir.Cells.get(m, o), D.Ptr(n, m, fi, ps, rs1, o), ps, o) == True{} : Bool}) ->
  {D.CntC(Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, x), o), D.Ptr(n, Cr.Cir.Cells.set(m, z, x), fi, ps, rs2, o), ps, o) == True{} : Bool}:
  match b:
    case True{}:
      +M2 = Cr.Cir.Cells.set(m, z, x)
      %Equal.sym(U32, o, z, D.u32.eq(o, z, eb)) : {D.CntC(Cr.Cir.Cells.get(M2, _), D.Ptr(n, M2, fi, ps, rs2, _), ps, _) == True{} : Bool}
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, z), x, D.cl.gs(m, z, x)) : {D.CntC(_, D.Ptr(n, M2, fi, ps, rs2, z), ps, z) == True{} : Bool}
      D.or.l(Bool.not(U32.is_lt(D.TgW(Cr.Cir.Cell.get(0n, x)), 19)), Bool.or(D.FlW(Cr.Cir.Cell.get(0n, x), 1024), Bool.or(D.Mem(ps, z),
        Nat.is_eq(U32.to_nat(Cr.Cir.Cell.get(1n, x)), D.Ptr(n, M2, fi, ps, rs2, z)))),
        (%Equal.sym(Bool, U32.is_lt(D.TgW(Cr.Cir.Cell.get(0n, x)), 19), False{}, hxt) : {Bool.not(_) == True{} : Bool}; {==}))
    case False{}:
      +M2 = Cr.Cir.Cells.set(m, z, x)
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, o), Cr.Cir.Cells.get(m, o), D.cl.go(m, o, z, x, eb)) :
        {D.CntC(_, D.Ptr(n, M2, fi, ps, rs2, o), ps, o) == True{} : Bool}
      %Equal.sym(Nat, D.Ptr(n, M2, fi, ps, rs2, o), D.Ptr(n, m, fi, ps, rs1, o), hP) : {D.CntC(Cr.Cir.Cells.get(m, o), _, ps, o) == True{} : Bool}
      h

def cnt.st(k: Nat, +m: Cr.Cir.Cells, +z: U32, +x: Cr.Cir.Cell, +o: U32, +nx: U32, +fi: U32, +ps: List<&2, U32>,
  +us: List<&2, D.Rt>, +os: List<&2, D.Rt>,
  +hf0: {D.Fs(m, ps, z) == Nil{} : List<&2, U32>}, +hf1: {D.Fs(Cr.Cir.Cells.set(m, z, x), ps, z) == D.Rt.cells(us) : List<&2, U32>},
  +hzo: {D.Own(fi, nx, z) == True{} : Bool}, +htN: {D.TblR(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, z) == True{} : Bool},
  +hxt: {U32.is_lt(D.TgW(Cr.Cir.Cell.get(0n, x)), 19) == False{} : Bool},
  h: {D.Cnt(k, m, o, Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), fi, ps, D.Rt.cells(List.append(&2, D.Rt, us, os))) == True{} : Bool}) ->
  {D.Cnt(k, Cr.Cir.Cells.set(m, z, x), o, Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), fi, ps, D.Rt.cells(os)) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+(+j):
      +M2 = Cr.Cir.Cells.set(m, z, x)
      +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
      +R1 = D.Rt.cells(List.append(&2, D.Rt, us, os))
      +R2 = D.Rt.cells(os)
      +h2 = h
      D.and.i(D.CntC(Cr.Cir.Cells.get(M2, o), D.Ptr(n, M2, fi, ps, R2, o), ps, o), D.Cnt(j, M2, U32.inc(o), n, fi, ps, R2),
        cntc.st.b(U32.is_eq(o, z), m, z, x, o, n, fi, ps, R1, R2, {==}, hxt, ptr.st(m, nx, fi, ps, z, x, us, os, o, hf0, hf1, hzo, htN),
          D.and.l(D.CntC(Cr.Cir.Cells.get(m, o), D.Ptr(n, m, fi, ps, R1, o), ps, o), D.Cnt(j, m, U32.inc(o), n, fi, ps, R1), h2)),
        cnt.st(j, m, z, x, U32.inc(o), nx, fi, ps, us, os, hf0, hf1, hzo, htN, hxt,
          D.and.r(D.CntC(Cr.Cir.Cells.get(m, o), D.Ptr(n, m, fi, ps, R1, o), ps, o), D.Cnt(j, m, U32.inc(o), n, fi, ps, R1), h2)))

# the pend list's cells, none of them z, after the store at z
def pendok.st(qs: List<&2, U32>, +ps: List<&2, U32>, +m: Cr.Cir.Cells, +z: U32, +x: Cr.Cir.Cell, +nx: U32, +fi: U32,
  +us: List<&2, D.Rt>, +os: List<&2, D.Rt>,
  +hf0: {D.Fs(m, ps, z) == Nil{} : List<&2, U32>}, +hf1: {D.Fs(Cr.Cir.Cells.set(m, z, x), ps, z) == D.Rt.cells(us) : List<&2, U32>},
  +hzo: {D.Own(fi, nx, z) == True{} : Bool}, +htN: {D.TblR(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, z) == True{} : Bool},
  hq: {D.Mem(qs, z) == False{} : Bool}, h: D.PendOK(qs, ps, m, fi, nx, D.Rt.cells(List.append(&2, D.Rt, us, os)))) ->
  D.PendOK(qs, ps, Cr.Cir.Cells.set(m, z, x), fi, nx, D.Rt.cells(os)):
  match qs:
    case Nil{}:
      Unit{}
    case Con{+p, +rest}:
      (ho, r1) = h
      (hs, r2) = r1
      (htg, r3) = r2
      (hp0, r4) = r3
      +M2 = Cr.Cir.Cells.set(m, z, x)
      +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
      +hq2 = hq
      +ne = D.or.f.l(U32.is_eq(p, z), D.Mem(rest, z), hq2)
      +ec = D.cl.go(m, p, z, x, ne)
      (ho, ((%Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, p), Cr.Cir.Cells.get(m, p), ec) :
          {U32.is_ne(U32.and(Cr.Cir.Cell.get(0n, _), 1024), 0) == False{} : Bool}; hs),
        ((%Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, p), Cr.Cir.Cells.get(m, p), ec) :
          {Bool.or(U32.is_lt(U32.and(Cr.Cir.Cell.get(0n, _), 63), 19), U32.is_le(32, U32.and(Cr.Cir.Cell.get(0n, _), 63))) == True{} : Bool}; htg),
        ((%Equal.sym(Nat, D.Ptr(n, M2, fi, ps, D.Rt.cells(os), p), D.Ptr(n, m, fi, ps, D.Rt.cells(List.append(&2, D.Rt, us, os)), p),
            ptr.st(m, nx, fi, ps, z, x, us, os, p, hf0, hf1, hzo, htN)) : {_ == 0n : Nat}; hp0),
          pendok.st(rest, ps, m, z, x, nx, fi, us, os, hf0, hf1, hzo, htN, D.or.f.r(U32.is_eq(p, z), D.Mem(rest, z), hq2), r4)))))

# the roots of terms, none of them z, point to term cells below next
def lt.roots(+dk: Bool, us: List<&2, D.Rt>, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +z: U32, +x: Cr.Cir.Cell,
  +him: {U32.is_lt(im, fi) == True{} : Bool}, +hfn: {U32.is_le(fi, nx) == True{} : Bool},
  hr: {D.RcL(D.Rt.cells(us), z) == 0n : Nat}, h: D.RtsK(dk, ds, m, im, fi, nx, ks, img, us)) ->
  {D.Lt.all(D.Rt.cells(us), Cr.Cir.Cells.set(m, z, x), im, fi, nx) == True{} : Bool}:
  match us:
    case Nil{}:
      {==}
    case Con{D.Rt{+c, +u}, +rest}:
      match h:
        case Tuple{+hu, hrest}:
          +hr2 = hr
          +M2 = Cr.Cir.Cells.set(m, z, x)
          +Y = Cr.Cir.Cells.get(m, c)
          +f0 = Cr.Cir.Cell.get(0n, Y)
          +ne = D.of.z(U32.is_eq(c, z), D.RcL(D.Rt.cells(rest), z), hr2)
          +nd = isk.nd(dk, u, ds, m, im, fi, nx, ks, img, c, hu)
          +hcell = ndk.cell(dk, ds, im, fi, nx, c, Y, u, D.A.tag(u), nd)
          +et = {D.nd.tgk(dk, ds, im, fi, nx, c, Y, u, D.A.tag(u), nd) : {D.TgW(f0) == D.A.tag(u) : U32}}
          +htg = {(%Equal.sym(U32, D.TgW(f0), D.A.tag(u), et) : {U32.is_lt(_, 19) == True{} : Bool}; atag.lt(u)) : {U32.is_lt(D.TgW(f0), 19) == True{} : Bool}}
          %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, c), Y, D.cl.go(m, c, z, x, ne)) :
            {Bool.and(D.LtC(c, _, im, fi, nx), D.Lt.all(D.Rt.cells(rest), M2, im, fi, nx)) == True{} : Bool}
          D.and.i(D.LtC(c, Y, im, fi, nx), D.Lt.all(D.Rt.cells(rest), M2, im, fi, nx),
            D.and.i(Bool.and(U32.is_lt(c, nx), U32.is_lt(D.TgW(f0), 19)), Bool.and(Cr.Cir.is_cell(c, im, fi, nx), Bool.or(D.Own(fi, nx, c), D.FlW(f0, 1024))),
              D.and.i(U32.is_lt(c, nx), U32.is_lt(D.TgW(f0), 19), cell.lt(c, im, fi, nx, hcell, him, hfn), htg),
              D.and.i(Cr.Cir.is_cell(c, im, fi, nx), Bool.or(D.Own(fi, nx, c), D.FlW(f0, 1024)), hcell, ndk.own(dk, ds, im, fi, nx, c, Y, u, D.A.tag(u), nd))),
            lt.roots(dk, rest, ds, m, im, fi, nx, ks, img, z, x, him, hfn, D.add0.r(D.Nat.of(U32.is_eq(c, z)), D.RcL(D.Rt.cells(rest), z), hr2), hrest))

# the pointers of the cell o after the store at z: z's are given (hz)
def pts.at.st(b: Bool, +m: Cr.Cir.Cells, +z: U32, +x: Cr.Cir.Cell, +ps: List<&2, U32>, +o: U32, +im: U32, +fi: U32, +nx: U32,
  eb: {U32.is_eq(o, z) == b : Bool},
  hz: {D.Lt.all(D.Fs(Cr.Cir.Cells.set(m, z, x), ps, z), Cr.Cir.Cells.set(m, z, x), im, fi, nx) == True{} : Bool},
  ht: {D.TblAt(m, o, z) == True{} : Bool}, hr: {D.RcL(D.Fs(m, ps, o), z) == 0n : Nat}, h: {D.Lt.all(D.Fs(m, ps, o), m, im, fi, nx) == True{} : Bool}) ->
  {D.Lt.all(D.Fs(Cr.Cir.Cells.set(m, z, x), ps, o), Cr.Cir.Cells.set(m, z, x), im, fi, nx) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(U32, o, z, D.u32.eq(o, z, eb)) : {D.Lt.all(D.Fs(Cr.Cir.Cells.set(m, z, x), ps, _), Cr.Cir.Cells.set(m, z, x), im, fi, nx) == True{} : Bool}
      hz
    case False{}:
      %Equal.sym(List<&2, U32>, D.Fs(Cr.Cir.Cells.set(m, z, x), ps, o), D.Fs(m, ps, o), D.fs.eq(m, z, x, ps, o, eb, ht)) :
        {D.Lt.all(_, Cr.Cir.Cells.set(m, z, x), im, fi, nx) == True{} : Bool}
      D.lt.fz(D.Fs(m, ps, o), m, z, x, im, fi, nx, hr, h)

def pts.st(k: Nat, +m: Cr.Cir.Cells, +z: U32, +x: Cr.Cir.Cell, +ps: List<&2, U32>, +o: U32, +im: U32, +fi: U32, +nx: U32,
  +hz: {D.Lt.all(D.Fs(Cr.Cir.Cells.set(m, z, x), ps, z), Cr.Cir.Cells.set(m, z, x), im, fi, nx) == True{} : Bool},
  hzp: {D.Pc(k, m, ps, o, z) == 0n : Nat}, ht: {D.TblR(k, m, o, z) == True{} : Bool}, h: {D.Pts(k, m, ps, o, im, fi, nx) == True{} : Bool}) ->
  {D.Pts(k, Cr.Cir.Cells.set(m, z, x), ps, o, im, fi, nx) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+(+j):
      +M2 = Cr.Cir.Cells.set(m, z, x)
      +hz2 = hzp
      +ht2 = ht
      +h2 = h
      D.and.i(D.Lt.all(D.Fs(M2, ps, o), M2, im, fi, nx), D.Pts(j, M2, ps, U32.inc(o), im, fi, nx),
        pts.at.st(U32.is_eq(o, z), m, z, x, ps, o, im, fi, nx, {==}, hz, D.and.l(D.TblAt(m, o, z), D.TblR(j, m, U32.inc(o), z), ht2),
          D.add0.l(D.RcL(D.Fs(m, ps, o), z), D.Pc(j, m, ps, U32.inc(o), z), hz2),
          D.and.l(D.Lt.all(D.Fs(m, ps, o), m, im, fi, nx), D.Pts(j, m, ps, U32.inc(o), im, fi, nx), h2)),
        pts.st(j, m, z, x, ps, U32.inc(o), im, fi, nx, hz, D.add0.r(D.RcL(D.Fs(m, ps, o), z), D.Pc(j, m, ps, U32.inc(o), z), hz2),
          D.and.r(D.TblAt(m, o, z), D.TblR(j, m, U32.inc(o), z), ht2), D.and.r(D.Lt.all(D.Fs(m, ps, o), m, im, fi, nx), D.Pts(j, m, ps, U32.inc(o), im, fi, nx), h2)))

# a store to z, a cell of no frame's tag with no pointer, keeps the frames
def frsk.st(+dk: Bool, fs: List<&2, D.AF>, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +rs: List<&2, U32>, +z: U32, +x: Cr.Cir.Cell, +fr: U32,
  +tbl: D.Tbl(m, im, fi, nx), +hz0: {D.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, rs, z) == 0n : Nat},
  +hzs: {D.Fl(m, z, 1024) == False{} : Bool},
  +hq: {Bool.not(Bool.and(U32.is_le(32, D.Tg(m, z)), U32.is_le(D.Tg(m, z), 40))) == True{} : Bool},
  h: D.FrsK(dk, ds, m, im, fi, nx, ks, img, ps, fr, fs)) -> D.FrsK(dk, ds, Cr.Cir.Cells.set(m, z, x), im, fi, nx, ks, img, ps, fr, fs):
  match fs:
    case Nil{}:
      h
    case Con{D.AF{+kind, +q, +k, +a, +b}, +rest}:
      match h:
        case Tuple{e0, Tuple{ev, Tuple{+eo, Tuple{es, Tuple{+em, Tuple{+etg, Tuple{eq, Tuple{ek, Tuple{ia, Tuple{ib, ir}}}}}}}}}}:
          +M2 = Cr.Cir.Cells.set(m, z, x)
          +ne = D.ne.sym(z, fr, ne.frame(U32.is_eq(z, fr), m, z, fr, kind, {==}, etg, hq))
          D.frs.uck(dk, ds, M2, im, fi, nx, ks, img, ps, fr, Con{D.AF{kind, q, k, a, b}, rest},
            D.frsc.atk(dk, ds, M2, im, fi, nx, ks, img, ps, fr, Cr.Cir.Cells.get(M2, fr), Cr.Cir.Cells.get(m, fr), Con{D.AF{kind, q, k, a, b}, rest},
              D.cl.go(m, fr, z, x, ne),
              (e0, (ev, (eo, (es, (em, (etg, (eq, (ek,
                (D.is.fz(dk, a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, D.Fd(2n, m, fr), tbl, hz0, hzs,
                  D.fr.ne(m, nx, fi, ps, rs, fr, D.Fd(2n, m, fr), z, D.FK.tag(kind), etg, D.fk.lt(kind), D.fk.ge(kind), D.fk.le(kind), em, eo,
                    D.mem.hd(D.Fd(2n, m, fr), D.Fs.opt(U32.is_eq(D.FK.tag(kind), 38), D.Fd(3n, m, fr), Nil{})), hz0), ia),
                (D.Frs.b.fz(dk, kind, ds, m, im, fi, nx, ks, img, ps, rs, z, x, fr, b, tbl, hz0, hzs, etg, em, eo, ib),
                  frsk.st(dk, rest, ds, m, im, fi, nx, ks, img, ps, rs, z, x, D.Fd(1n, m, fr), tbl, hz0, hzs, hq, ir)))))))))))))

# the terms of us ++ os: those of us
def rtsk.app.l(+dk: Bool, us: List<&2, D.Rt>, +os: List<&2, D.Rt>, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, h: D.RtsK(dk, ds, m, im, fi, nx, ks, img, List.append(&2, D.Rt, us, os))) ->
  D.RtsK(dk, ds, m, im, fi, nx, ks, img, us):
  match us:
    case Nil{}:
      Unit{}
    case Con{D.Rt{+c, +u}, +rest}:
      match h:
        case Tuple{hu, hr}:
          (hu, rtsk.app.l(dk, rest, os, ds, m, im, fi, nx, ks, img, hr))

# and those of os
def rtsk.app.r(+dk: Bool, us: List<&2, D.Rt>, +os: List<&2, D.Rt>, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, h: D.RtsK(dk, ds, m, im, fi, nx, ks, img, List.append(&2, D.Rt, us, os))) ->
  D.RtsK(dk, ds, m, im, fi, nx, ks, img, os):
  match us:
    case Nil{}:
      h
    case Con{D.Rt{+c, +u}, +rest}:
      match h:
        case Tuple{_, hr}:
          rtsk.app.r(dk, rest, os, ds, m, im, fi, nx, ks, img, hr)

# HSK after the store at z of x, whose pointers are the roots us: us leave
# the roots, and z holds them
def st.go(+dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +us: List<&2, D.Rt>, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32,
  +pend: U32, +ps: List<&2, U32>, +z: U32, +x: Cr.Cir.Cell,
  +hos: D.RtsK(dk, ds, m, im, fi, nx, ks, img, List.append(&2, D.Rt, us, os)), +hbs: D.RtsK(dk, ds, m, im, fi, nx, ks, img, bs),
  +hfrs: D.FrsK(dk, ds, m, im, fi, nx, ks, img, ps, sp, fs),
  +hheap: D.Heap(m, nx, fi, im, D.Rt.cells(List.append(&2, D.Rt, us, os)), pend, ps), +himg: D.ImgOKK(dk, ds, ks, img, m, im, fi, nx),
  +hfn: {U32.is_le(fi, nx) == True{} : Bool}, +hb: D.Held(m, os, bs),
  +ho: {D.Own(fi, nx, z) == True{} : Bool}, +hm: {D.Mem(ps, z) == False{} : Bool}, +hzs: {D.Fl(m, z, 1024) == False{} : Bool},
  +hq: {Bool.not(Bool.and(U32.is_le(32, D.Tg(m, z)), U32.is_le(D.Tg(m, z), 40))) == True{} : Bool},
  +hz0: {D.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, D.Rt.cells(List.append(&2, D.Rt, us, os)), z) == 0n : Nat},
  +hzf: {D.Fs(m, ps, z) == Nil{} : List<&2, U32>}, +hxt: {U32.is_lt(D.TgW(Cr.Cir.Cell.get(0n, x)), 19) == False{} : Bool},
  +hf: {D.Fs(Cr.Cir.Cells.set(m, z, x), ps, z) == D.Rt.cells(us) : List<&2, U32>}) ->
  D.HSK(dk, ds, ks, img, Cr.Cir.Cells.set(m, z, x), nx, fi, im, os, bs, fs, sp, pend, ps):
  match hheap:
    case Tuple{hch, Tuple{hpk, Tuple{hcnt, Tuple{hpts, hr}}}}:
      +M2 = Cr.Cir.Cells.set(m, z, x)
      +rs = D.Rt.cells(List.append(&2, D.Rt, us, os))
      +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
      +tbl = D.img.tbl(dk, ds, ks, img, m, im, fi, nx, himg)
      +htN = D.TblR.of(n, m, fi, z, D.img.hz(dk, ds, ks, img, m, im, fi, nx, z, himg, ho))
      +him = img.lt(dk, ds, ks, img, m, im, fi, nx, himg)
      +hpz = D.add0.l(D.Pc(n, m, ps, fi, z), D.RcL(rs, z), hz0)
      +hrz = D.add0.r(D.Pc(n, m, ps, fi, z), D.RcL(rs, z), hz0)
      +hrz2 = {(%rcl.us(us, os, z) : {_ == 0n : Nat}; hrz) : {Nat.add(D.RcL(D.Rt.cells(us), z), D.RcL(D.Rt.cells(os), z)) == 0n : Nat}}
      +hru = D.add0.l(D.RcL(D.Rt.cells(us), z), D.RcL(D.Rt.cells(os), z), hrz2)
      +hro = D.add0.r(D.RcL(D.Rt.cells(us), z), D.RcL(D.Rt.cells(os), z), hrz2)
      +hno = D.neall.rcl(D.Rt.cells(os), z, hro)
      +hos2 = rtsk.app.r(dk, us, os, ds, m, im, fi, nx, ks, img, hos)
      +hus = rtsk.app.l(dk, us, os, ds, m, im, fi, nx, ks, img, hos)
      +hnb = D.neall.held(dk, bs, os, ds, m, im, fi, nx, ks, img, ps, rs, z, tbl, hz0, hzs, hno, hos2, hb)
      +hzl = {(%Equal.sym(List<&2, U32>, D.Fs(M2, ps, z), D.Rt.cells(us), hf) : {D.Lt.all(_, M2, im, fi, nx) == True{} : Bool};
          lt.roots(dk, us, ds, m, im, fi, nx, ks, img, z, x, him, hfn, hru, hus)) :
        {D.Lt.all(D.Fs(M2, ps, z), M2, im, fi, nx) == True{} : Bool}}
      (D.Rts.fz(dk, os, ds, m, im, fi, nx, ks, img, ps, rs, z, x, tbl, hz0, hzs, hno, hos2),
        (D.Rts.fz(dk, bs, ds, m, im, fi, nx, ks, img, ps, rs, z, x, tbl, hz0, hzs, hnb, hbs),
        (D.Held.fz(dk, bs, os, ds, m, im, fi, nx, ks, img, ps, rs, z, x, tbl, hz0, hzs, hno, hos2, hnb, hb),
        (frsk.st(dk, fs, ds, m, im, fi, nx, ks, img, ps, rs, z, x, sp, tbl, hz0, hzs, hq, hfrs),
        ((D.Chain.fz(ps, m, z, x, pend, hm, hch),
          (pendok.st(ps, ps, m, z, x, nx, fi, us, os, hzf, hf, ho, htN, hm, hpk),
          (cnt.st(n, m, z, x, fi, nx, fi, ps, us, os, hzf, hf, ho, htN, hxt, hcnt),
          (pts.st(n, m, z, x, ps, fi, im, fi, nx, hzl, hpz, htN, hpts), hr)))),
          D.ImgOK.fz(dk, ds, ks, img, m, im, fi, nx, ps, rs, z, x, hz0, hzs, ho, himg))))))

def st.hs(+dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +us: List<&2, D.Rt>, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32,
  +pend: U32, +ps: List<&2, U32>, +z: U32, +x: Cr.Cir.Cell,
  hs: D.HSK(dk, ds, ks, img, m, nx, fi, im, List.append(&2, D.Rt, us, os), bs, fs, sp, pend, ps), +hb: D.Held(m, os, bs),
  +ho: {D.Own(fi, nx, z) == True{} : Bool}, +hm: {D.Mem(ps, z) == False{} : Bool}, +hzs: {D.Fl(m, z, 1024) == False{} : Bool},
  +hq: {Bool.not(Bool.and(U32.is_le(32, D.Tg(m, z)), U32.is_le(D.Tg(m, z), 40))) == True{} : Bool},
  +hz0: {D.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, D.Rt.cells(List.append(&2, D.Rt, us, os)), z) == 0n : Nat},
  +hzf: {D.Fs(m, ps, z) == Nil{} : List<&2, U32>}, +hxt: {U32.is_lt(D.TgW(Cr.Cir.Cell.get(0n, x)), 19) == False{} : Bool},
  +hf: {D.Fs(Cr.Cir.Cells.set(m, z, x), ps, z) == D.Rt.cells(us) : List<&2, U32>}) ->
  D.HSK(dk, ds, ks, img, Cr.Cir.Cells.set(m, z, x), nx, fi, im, os, bs, fs, sp, pend, ps):
  match hs:
    case Tuple{hos, Tuple{hbs, Tuple{_, Tuple{hfrs, Tuple{+hheap, himg}}}}}:
      st.go(dk, ds, ks, img, m, nx, fi, im, us, os, bs, fs, sp, pend, ps, z, x, hos, hbs, hfrs, hheap, himg,
        heap.fn(m, nx, fi, im, D.Rt.cells(List.append(&2, D.Rt, us, os)), pend, ps, hheap), hb, ho, hm, hzs, hq, hz0, hzf, hxt, hf)

# store.post: HSK, and U1's Acc step of the store (the roots us become z's
# terms)
def st.top(+dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +us: List<&2, D.Rt>, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32,
  +pend: U32, +ps: List<&2, U32>, +z: U32, +x: Cr.Cir.Cell, +xs: List<&2, D.TmpE>, +zs: List<&2, D.Rt>,
  +hs: D.HSK(dk, ds, ks, img, m, nx, fi, im, List.append(&2, D.Rt, us, os), bs, fs, sp, pend, ps),
  hac: D.AccK(dk, ds, ks, img, m, nx, fi, im, List.append(&2, D.Rt, us, os), xs, sp, fs, ps, zs),
  hzx: {D.Tmp.head(xs) == Some{z} : Maybe<&2, U32>}, +hb: D.Held(m, os, bs),
  +ho: {D.Own(fi, nx, z) == True{} : Bool}, +hm: {D.Mem(ps, z) == False{} : Bool}, +hzs: {D.Fl(m, z, 1024) == False{} : Bool},
  +hzt: {Bool.or(U32.is_lt(D.Tg(m, z), 32), U32.is_le(41, D.Tg(m, z))) == True{} : Bool},
  +hz0: {D.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, D.Rt.cells(List.append(&2, D.Rt, us, os)), z) == 0n : Nat},
  +hzf: {D.Fs(m, ps, z) == Nil{} : List<&2, U32>}, +ht: {U32.is_le(32, D.TgW(Cr.Cir.Cell.get(0n, x))) == True{} : Bool},
  +hxs: {D.FlW(Cr.Cir.Cell.get(0n, x), 1024) == False{} : Bool},
  +hf: {D.Fs(Cr.Cir.Cells.set(m, z, x), ps, z) == D.Rt.cells(us) : List<&2, U32>}) ->
  D.P2(D.HSK(dk, ds, ks, img, Cr.Cir.Cells.set(m, z, x), nx, fi, im, os, bs, fs, sp, pend, ps),
    D.AccK(dk, ds, ks, img, Cr.Cir.Cells.set(m, z, x), nx, fi, im, os, D.Tmp.hold(us, xs), sp, fs, ps, zs)):
  (st.hs(dk, ds, ks, img, m, nx, fi, im, us, os, bs, fs, sp, pend, ps, z, x, hs, hb, ho, hm, hzs, nf.tag(D.Tg(m, z), hzt), hz0, hzf,
      lt19.ge(D.TgW(Cr.Cir.Cell.get(0n, x)), ht), hf),
    AC.acc.store(dk, ds, ks, img, m, nx, fi, im, us, os, bs, fs, sp, pend, ps, z, x, xs, zs, hs, hac, hzx, hm, hzs, hz0, hzf, hxs, hf))

# A store of a term cell that holds the owned roots us
# ----------------------------------------------------
#
# As store.post, but x is a term cell of count 1 that stands for t: z is a
# new owned root of t, its one pointer, and us leave the roots.

# one more root, at a cell out of the pend list: the pend list's cells still
# have no pointer
def pendok.addroot(qs: List<&2, U32>, +ps: List<&2, U32>, +m: Cr.Cir.Cells, +fi: U32, +nx: U32, +rs: List<&2, U32>, +z: U32,
  hq: {D.Mem(qs, z) == False{} : Bool}, h: D.PendOK(qs, ps, m, fi, nx, rs)) -> D.PendOK(qs, ps, m, fi, nx, Con{z, rs}):
  match qs:
    case Nil{}:
      Unit{}
    case Con{+p, +rest}:
      match h:
        case Tuple{ho, Tuple{+hs, Tuple{htg, Tuple{+hp0, hr}}}}:
          +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
          +hq2 = hq
          +ne = D.ne.sym(p, z, D.or.f.l(U32.is_eq(p, z), D.Mem(rest, z), hq2))
          (ho, (hs, (htg, ((%Equal.sym(Bool, U32.is_eq(z, p), False{}, ne) :
              {Nat.add(D.Pc(n, m, ps, fi, p), Nat.add(D.Nat.of(_), D.RcL(rs, p))) == 0n : Nat}; hp0),
            pendok.addroot(rest, ps, m, fi, nx, rs, z, D.or.f.r(U32.is_eq(p, z), D.Mem(rest, z), hq2), hr)))))

# the count condition at o after the store at z of the term cell x of count
# 1, now a root (R2 the roots but z after, R1 before)
def cntc.tm.b(b: Bool, +m: Cr.Cir.Cells, +z: U32, +x: Cr.Cir.Cell, +o: U32, +n: Nat, +fi: U32, +ps: List<&2, U32>,
  +R1: List<&2, U32>, +R2: List<&2, U32>, +eb: {U32.is_eq(o, z) == b : Bool},
  hx1: {Cr.Cir.Cell.get(1n, x) == 1 : U32}, hp1: {D.Ptr(n, Cr.Cir.Cells.set(m, z, x), fi, ps, Con{z, R2}, z) == 1n : Nat},
  hP: {D.Ptr(n, Cr.Cir.Cells.set(m, z, x), fi, ps, R2, o) == D.Ptr(n, m, fi, ps, R1, o) : Nat},
  h: {D.CntC(Cr.Cir.Cells.get(m, o), D.Ptr(n, m, fi, ps, R1, o), ps, o) == True{} : Bool}) ->
  {D.CntC(Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, x), o), D.Ptr(n, Cr.Cir.Cells.set(m, z, x), fi, ps, Con{z, R2}, o), ps, o) == True{} : Bool}:
  match b:
    case True{}:
      +M2 = Cr.Cir.Cells.set(m, z, x)
      +P = D.Ptr(n, M2, fi, ps, Con{z, R2}, z)
      +f0 = Cr.Cir.Cell.get(0n, x)
      %Equal.sym(U32, o, z, D.u32.eq(o, z, eb)) : {D.CntC(Cr.Cir.Cells.get(M2, _), D.Ptr(n, M2, fi, ps, Con{z, R2}, _), ps, _) == True{} : Bool}
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, z), x, D.cl.gs(m, z, x)) : {D.CntC(_, P, ps, z) == True{} : Bool}
      D.or.r(Bool.not(U32.is_lt(D.TgW(f0), 19)), Bool.or(D.FlW(f0, 1024), Bool.or(D.Mem(ps, z), Nat.is_eq(U32.to_nat(Cr.Cir.Cell.get(1n, x)), P))),
        D.or.r(D.FlW(f0, 1024), Bool.or(D.Mem(ps, z), Nat.is_eq(U32.to_nat(Cr.Cir.Cell.get(1n, x)), P)),
          D.or.r(D.Mem(ps, z), Nat.is_eq(U32.to_nat(Cr.Cir.Cell.get(1n, x)), P),
            (%Equal.sym(U32, Cr.Cir.Cell.get(1n, x), 1, hx1) : {Nat.is_eq(U32.to_nat(_), P) == True{} : Bool};
              (%Equal.sym(Nat, P, 1n, hp1) : {Nat.is_eq(U32.to_nat(1), _) == True{} : Bool}; {==})))))
    case False{}:
      +M2 = Cr.Cir.Cells.set(m, z, x)
      +ne = D.ne.sym(o, z, eb)
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, o), Cr.Cir.Cells.get(m, o), D.cl.go(m, o, z, x, eb)) :
        {D.CntC(_, D.Ptr(n, M2, fi, ps, Con{z, R2}, o), ps, o) == True{} : Bool}
      %Equal.sym(Nat, D.Ptr(n, M2, fi, ps, Con{z, R2}, o), D.Ptr(n, m, fi, ps, R1, o),
          {(%Equal.sym(Bool, U32.is_eq(z, o), False{}, ne) :
              {Nat.add(D.Pc(n, M2, ps, fi, o), Nat.add(D.Nat.of(_), D.RcL(R2, o))) == D.Ptr(n, m, fi, ps, R1, o) : Nat}; hP) :
            {D.Ptr(n, M2, fi, ps, Con{z, R2}, o) == D.Ptr(n, m, fi, ps, R1, o) : Nat}}) :
        {D.CntC(Cr.Cir.Cells.get(m, o), _, ps, o) == True{} : Bool}
      h

def cnt.tm(k: Nat, +m: Cr.Cir.Cells, +z: U32, +x: Cr.Cir.Cell, +o: U32, +nx: U32, +fi: U32, +ps: List<&2, U32>,
  +us: List<&2, D.Rt>, +os: List<&2, D.Rt>,
  +hf0: {D.Fs(m, ps, z) == Nil{} : List<&2, U32>}, +hf1: {D.Fs(Cr.Cir.Cells.set(m, z, x), ps, z) == D.Rt.cells(us) : List<&2, U32>},
  +hzo: {D.Own(fi, nx, z) == True{} : Bool}, +htN: {D.TblR(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, z) == True{} : Bool},
  +hx1: {Cr.Cir.Cell.get(1n, x) == 1 : U32},
  +hp1: {D.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), Cr.Cir.Cells.set(m, z, x), fi, ps, Con{z, D.Rt.cells(os)}, z) == 1n : Nat},
  h: {D.Cnt(k, m, o, Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), fi, ps, D.Rt.cells(List.append(&2, D.Rt, us, os))) == True{} : Bool}) ->
  {D.Cnt(k, Cr.Cir.Cells.set(m, z, x), o, Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), fi, ps, Con{z, D.Rt.cells(os)}) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+(+j):
      +M2 = Cr.Cir.Cells.set(m, z, x)
      +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
      +R1 = D.Rt.cells(List.append(&2, D.Rt, us, os))
      +R2 = D.Rt.cells(os)
      +h2 = h
      D.and.i(D.CntC(Cr.Cir.Cells.get(M2, o), D.Ptr(n, M2, fi, ps, Con{z, R2}, o), ps, o), D.Cnt(j, M2, U32.inc(o), n, fi, ps, Con{z, R2}),
        cntc.tm.b(U32.is_eq(o, z), m, z, x, o, n, fi, ps, R1, R2, {==}, hx1, hp1, ptr.st(m, nx, fi, ps, z, x, us, os, o, hf0, hf1, hzo, htN),
          D.and.l(D.CntC(Cr.Cir.Cells.get(m, o), D.Ptr(n, m, fi, ps, R1, o), ps, o), D.Cnt(j, m, U32.inc(o), n, fi, ps, R1), h2)),
        cnt.tm(j, m, z, x, U32.inc(o), nx, fi, ps, us, os, hf0, hf1, hzo, htN, hx1, hp1,
          D.and.r(D.CntC(Cr.Cir.Cells.get(m, o), D.Ptr(n, m, fi, ps, R1, o), ps, o), D.Cnt(j, m, U32.inc(o), n, fi, ps, R1), h2)))

# HSK after the store at z of the term cell x of t, whose pointers are the
# roots us: z is a new owned root of t, and us leave the roots
def tm.go(+dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +us: List<&2, D.Rt>, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32,
  +pend: U32, +ps: List<&2, U32>, +z: U32, +x: Cr.Cir.Cell, +t: Bk.Term,
  +hos: D.RtsK(dk, ds, m, im, fi, nx, ks, img, List.append(&2, D.Rt, us, os)), +hbs: D.RtsK(dk, ds, m, im, fi, nx, ks, img, bs),
  +hfrs: D.FrsK(dk, ds, m, im, fi, nx, ks, img, ps, sp, fs),
  +hheap: D.Heap(m, nx, fi, im, D.Rt.cells(List.append(&2, D.Rt, us, os)), pend, ps), +himg: D.ImgOKK(dk, ds, ks, img, m, im, fi, nx),
  +hfn: {U32.is_le(fi, nx) == True{} : Bool}, +hb: D.Held(m, os, bs),
  +ho: {D.Own(fi, nx, z) == True{} : Bool}, +hm: {D.Mem(ps, z) == False{} : Bool}, +hzs: {D.Fl(m, z, 1024) == False{} : Bool},
  +hq: {Bool.not(Bool.and(U32.is_le(32, D.Tg(m, z)), U32.is_le(D.Tg(m, z), 40))) == True{} : Bool},
  +hz0: {D.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, D.Rt.cells(List.append(&2, D.Rt, us, os)), z) == 0n : Nat},
  +hzf: {D.Fs(m, ps, z) == Nil{} : List<&2, U32>}, +hx1: {Cr.Cir.Cell.get(1n, x) == 1 : U32},
  +hf: {D.Fs(Cr.Cir.Cells.set(m, z, x), ps, z) == D.Rt.cells(us) : List<&2, U32>},
  +hi: D.IsK(dk, ds, Cr.Cir.Cells.set(m, z, x), im, fi, nx, ks, img, z, t)) ->
  D.HSK(dk, ds, ks, img, Cr.Cir.Cells.set(m, z, x), nx, fi, im, Con{D.Rt{z, t}, os}, bs, fs, sp, pend, ps):
  match hheap:
    case Tuple{hch, Tuple{hpk, Tuple{hcnt, Tuple{hpts, hr}}}}:
      +M2 = Cr.Cir.Cells.set(m, z, x)
      +rs = D.Rt.cells(List.append(&2, D.Rt, us, os))
      +R2 = D.Rt.cells(os)
      +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
      +tbl = D.img.tbl(dk, ds, ks, img, m, im, fi, nx, himg)
      +htN = D.TblR.of(n, m, fi, z, D.img.hz(dk, ds, ks, img, m, im, fi, nx, z, himg, ho))
      +him = img.lt(dk, ds, ks, img, m, im, fi, nx, himg)
      +hpz = D.add0.l(D.Pc(n, m, ps, fi, z), D.RcL(rs, z), hz0)
      +hrz = D.add0.r(D.Pc(n, m, ps, fi, z), D.RcL(rs, z), hz0)
      +hrz2 = {(%rcl.us(us, os, z) : {_ == 0n : Nat}; hrz) : {Nat.add(D.RcL(D.Rt.cells(us), z), D.RcL(R2, z)) == 0n : Nat}}
      +hru = D.add0.l(D.RcL(D.Rt.cells(us), z), D.RcL(R2, z), hrz2)
      +hro = D.add0.r(D.RcL(D.Rt.cells(us), z), D.RcL(R2, z), hrz2)
      +hno = D.neall.rcl(R2, z, hro)
      +hos2 = rtsk.app.r(dk, us, os, ds, m, im, fi, nx, ks, img, hos)
      +hus = rtsk.app.l(dk, us, os, ds, m, im, fi, nx, ks, img, hos)
      +hnb = D.neall.held(dk, bs, os, ds, m, im, fi, nx, ks, img, ps, rs, z, tbl, hz0, hzs, hno, hos2, hb)
      +hzl = {(%Equal.sym(List<&2, U32>, D.Fs(M2, ps, z), D.Rt.cells(us), hf) : {D.Lt.all(_, M2, im, fi, nx) == True{} : Bool};
          lt.roots(dk, us, ds, m, im, fi, nx, ks, img, z, x, him, hfn, hru, hus)) :
        {D.Lt.all(D.Fs(M2, ps, z), M2, im, fi, nx) == True{} : Bool}}
      +hp1 = Equal.trans(Nat, D.Ptr(n, M2, fi, ps, Con{z, R2}, z), 1n+D.Ptr(n, M2, fi, ps, R2, z), 1n, ptr.root(n, M2, fi, ps, R2, z),
        Equal.cong(Nat, Nat, w => 1n+w, D.Ptr(n, M2, fi, ps, R2, z), 0n,
          Equal.trans(Nat, D.Ptr(n, M2, fi, ps, R2, z), D.Ptr(n, m, fi, ps, rs, z), 0n, ptr.st(m, nx, fi, ps, z, x, us, os, z, hzf, hf, ho, htN), hz0)))
      ((hi, D.Rts.fz(dk, os, ds, m, im, fi, nx, ks, img, ps, rs, z, x, tbl, hz0, hzs, hno, hos2)),
        (D.Rts.fz(dk, bs, ds, m, im, fi, nx, ks, img, ps, rs, z, x, tbl, hz0, hzs, hnb, hbs),
        (held.cons(bs, os, z, t, M2, D.Held.fz(dk, bs, os, ds, m, im, fi, nx, ks, img, ps, rs, z, x, tbl, hz0, hzs, hno, hos2, hnb, hb)),
        (frsk.st(dk, fs, ds, m, im, fi, nx, ks, img, ps, rs, z, x, sp, tbl, hz0, hzs, hq, hfrs),
        ((D.Chain.fz(ps, m, z, x, pend, hm, hch),
          (pendok.addroot(ps, ps, M2, fi, nx, R2, z, hm, pendok.st(ps, ps, m, z, x, nx, fi, us, os, hzf, hf, ho, htN, hm, hpk)),
          (cnt.tm(n, m, z, x, fi, nx, fi, ps, us, os, hzf, hf, ho, htN, hx1, hp1, hcnt),
          (pts.st(n, m, z, x, ps, fi, im, fi, nx, hzl, hpz, htN, hpts), hr)))),
          D.ImgOK.fz(dk, ds, ks, img, m, im, fi, nx, ps, rs, z, x, hz0, hzs, ho, himg))))))

def tm.hs(+dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +us: List<&2, D.Rt>, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32,
  +pend: U32, +ps: List<&2, U32>, +z: U32, +x: Cr.Cir.Cell, +t: Bk.Term,
  hs: D.HSK(dk, ds, ks, img, m, nx, fi, im, List.append(&2, D.Rt, us, os), bs, fs, sp, pend, ps), +hb: D.Held(m, os, bs),
  +ho: {D.Own(fi, nx, z) == True{} : Bool}, +hm: {D.Mem(ps, z) == False{} : Bool}, +hzs: {D.Fl(m, z, 1024) == False{} : Bool},
  +hzt: {Bool.or(U32.is_lt(D.Tg(m, z), 32), U32.is_le(41, D.Tg(m, z))) == True{} : Bool},
  +hz0: {D.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, D.Rt.cells(List.append(&2, D.Rt, us, os)), z) == 0n : Nat},
  +hzf: {D.Fs(m, ps, z) == Nil{} : List<&2, U32>}, +hx1: {Cr.Cir.Cell.get(1n, x) == 1 : U32},
  +hf: {D.Fs(Cr.Cir.Cells.set(m, z, x), ps, z) == D.Rt.cells(us) : List<&2, U32>},
  +hi: D.IsK(dk, ds, Cr.Cir.Cells.set(m, z, x), im, fi, nx, ks, img, z, t)) ->
  D.HSK(dk, ds, ks, img, Cr.Cir.Cells.set(m, z, x), nx, fi, im, Con{D.Rt{z, t}, os}, bs, fs, sp, pend, ps):
  match hs:
    case Tuple{hos, Tuple{hbs, Tuple{_, Tuple{hfrs, Tuple{+hheap, himg}}}}}:
      tm.go(dk, ds, ks, img, m, nx, fi, im, us, os, bs, fs, sp, pend, ps, z, x, t, hos, hbs, hfrs, hheap, himg,
        heap.fn(m, nx, fi, im, D.Rt.cells(List.append(&2, D.Rt, us, os)), pend, ps, hheap), hb, ho, hm, hzs, nf.tag(D.Tg(m, z), hzt), hz0, hzf,
        hx1, hf, hi)

# The flag DATA
# -------------
#
# DATA (512) is outside the tag (bits 0-5), the quantity (6-7), VALUE (256),
# STATIC (1024), K (2048), OWNED (4096) and the bound of free variables
# (bits 13 on): setting it at the cell cf (AC.Flag) keeps every cell's facts
# but DATA's, which data.flag's hd gives for the terms at cf. Every cell
# keeps its value but field 0 at cf.

# a shifted pad keeps an or
def pad.or(p: Nat, a: Word(p), b: Word(p)) ->
  {Word.or(1n+p, Word.shr.pad(p, a), Word.shr.pad(p, b)) == Word.shr.pad(p, Word.or(p, a, b)) : Word(1n+p)}:
  match p:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+(+q):
      match a b:
        case WCon{+a1, +at} WCon{+b1, +bt}:
          %pad.or(q, at, bt) : {WCon{Bool.or(a1, b1), Word.or(1n+q, Word.shr.pad(q, at), Word.shr.pad(q, bt))} == WCon{Bool.or(a1, b1), _} : Word(2n+q)}
          {==}

# a shift keeps an or
def shr.or(n: Nat, x: Word(n), y: Word(n)) -> {Word.or(n, Word.shr(n, x), Word.shr(n, y)) == Word.shr(n, Word.or(n, x, y)) : Word(n)}:
  match n:
    case 0n:
      match x y:
        case WNil{} WNil{}:
          {==}
    case 1n+(+p):
      match x y:
        case WCon{a, +xt} WCon{b, +yt}:
          pad.or(p, xt, yt)

def u.shr.or(a: U32, b: U32) -> {U32.or(U32.shr(a), U32.shr(b)) == U32.shr(U32.or(a, b)) : U32}:
  match a b:
    case U32{+x} U32{+y}:
      %shr.or(32n, x, y) : {U32{Word.or(32n, Word.shr(32n, x), Word.shr(32n, y))} == U32{_} : U32}
      {==}

def u.shrn.or(+a: U32, +b: U32, n: Nat) -> {U32.or(U32.shrn(a, n), U32.shrn(b, n)) == U32.shrn(U32.or(a, b), n) : U32}:
  match n:
    case 0n:
      {==}
    case 1n+(+k):
      %u.shrn.or(a, b, k) : {U32.or(U32.shr(U32.shrn(a, k)), U32.shr(U32.shrn(b, k))) == U32.shr(_) : U32}
      u.shr.or(U32.shrn(a, k), U32.shrn(b, k))

# w | 0 is w
def w.or.z(+n: Nat, +w: Word(n)) -> {Word.or(n, w, Word.zero(n)) == w : Word(n)}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{False{}, +t}:
          Equal.cong(Word(p), Word(1n+p), z => WCon{False{}, z}, Word.or(p, t, Word.zero(p)), t, w.or.z(p, t))
        case WCon{True{}, +t}:
          Equal.cong(Word(p), Word(1n+p), z => WCon{True{}, z}, Word.or(p, t, Word.zero(p)), t, w.or.z(p, t))

def u32.or.z(+x: U32) -> {U32.or(x, U32{Word.zero(32n)}) == x : U32}:
  match x:
    case U32{+w}:
      Equal.cong(Word(32n), U32, z => U32{z}, Word.or(32n, w, Word.zero(32n)), w, w.or.z(32n, w))

# 512 >> 13 is 0, 512 >> 6 is 8, 8 & 3 is 0, 512 & 256 is 0, 512 & 2048 is 0
def dat.s13() -> {U32{Word.zero(32n)} == U32.shrn(512, 13n) : U32}:
  {==}

def dat.s6() -> {U32.shrn(512, 6n) == 8 : U32}:
  {==}

def dat.q() -> {U32.and(8, 3) == 0 : U32}:
  {==}

def dat.v() -> {U32.and(512, 256) == 0 : U32}:
  {==}

def dat.k() -> {U32.and(512, 2048) == 0 : U32}:
  {==}

# the bound of free variables, past DATA
def fv.dat(+f0: U32) -> {D.FvW(U32.or(f0, 512)) == D.FvW(f0) : U32}:
  +s = U32.shrn(f0, 13n)
  Equal.trans(U32, U32.shrn(U32.or(f0, 512), 13n), U32.or(s, U32.shrn(512, 13n)), s,
    Equal.sym(U32, U32.or(s, U32.shrn(512, 13n)), U32.shrn(U32.or(f0, 512), 13n), u.shrn.or(f0, 512, 13n)),
    (%dat.s13() : {U32.or(s, _) == s : U32}; u32.or.z(s)))

# the quantity, past DATA
def qn.dat(+f0: U32) -> {D.QnW(U32.or(f0, 512)) == D.QnW(f0) : U32}:
  +s = U32.shrn(f0, 6n)
  Equal.trans(U32, U32.and(U32.shrn(U32.or(f0, 512), 6n), 3), U32.and(U32.or(s, 8), 3), U32.and(s, 3),
    Equal.cong(U32, U32, w => U32.and(w, 3), U32.shrn(U32.or(f0, 512), 6n), U32.or(s, 8),
      Equal.trans(U32, U32.shrn(U32.or(f0, 512), 6n), U32.or(s, U32.shrn(512, 6n)), U32.or(s, 8),
        Equal.sym(U32, U32.or(s, U32.shrn(512, 6n)), U32.shrn(U32.or(f0, 512), 6n), u.shrn.or(f0, 512, 6n)),
        Equal.cong(U32, U32, w => U32.or(s, w), U32.shrn(512, 6n), 8, dat.s6()))),
    AC.u32.and.or(s, 8, 3, dat.q()))

# field 0 at cf after the flag, and at another cell
def fd0.cf(+m: Cr.Cir.Cells, +cf: U32) -> {D.Fd(0n, AC.Flag(m, cf), cf) == U32.or(D.Fd(0n, m, cf), 512) : U32}:
  +X = Cr.Cir.Cell.set(0n, Cr.Cir.Cells.get(m, cf), U32.or(D.Fd(0n, m, cf), 512))
  Equal.trans(U32, D.Fd(0n, AC.Flag(m, cf), cf), Cr.Cir.Cell.get(0n, X), U32.or(D.Fd(0n, m, cf), 512),
    Equal.cong(Cr.Cir.Cell, U32, y => Cr.Cir.Cell.get(0n, y), Cr.Cir.Cells.get(AC.Flag(m, cf), cf), X, D.cl.gs(m, cf, X)),
    AC.s0g0(Cr.Cir.Cells.get(m, cf), U32.or(D.Fd(0n, m, cf), 512)))

def fd0.ne(+m: Cr.Cir.Cells, +cf: U32, +o: U32, eb: {U32.is_eq(o, cf) == False{} : Bool}) ->
  {D.Fd(0n, AC.Flag(m, cf), o) == D.Fd(0n, m, o) : U32}:
  Equal.cong(Cr.Cir.Cell, U32, y => Cr.Cir.Cell.get(0n, y), Cr.Cir.Cells.get(AC.Flag(m, cf), o), Cr.Cir.Cells.get(m, o),
    D.cl.go(m, o, cf, Cr.Cir.Cell.set(0n, Cr.Cir.Cells.get(m, cf), U32.or(D.Fd(0n, m, cf), 512)), eb))

# the quantity and the bound of free variables of every cell stay
def qn.flag.b(b: Bool, +m: Cr.Cir.Cells, +cf: U32, +o: U32, eb: {U32.is_eq(o, cf) == b : Bool}) ->
  {D.QnW(D.Fd(0n, AC.Flag(m, cf), o)) == D.QnW(D.Fd(0n, m, o)) : U32}:
  match b:
    case True{}:
      %Equal.sym(U32, o, cf, D.u32.eq(o, cf, eb)) : {D.QnW(D.Fd(0n, AC.Flag(m, cf), _)) == D.QnW(D.Fd(0n, m, _)) : U32}
      %Equal.sym(U32, D.Fd(0n, AC.Flag(m, cf), cf), U32.or(D.Fd(0n, m, cf), 512), fd0.cf(m, cf)) : {D.QnW(_) == D.QnW(D.Fd(0n, m, cf)) : U32}
      qn.dat(D.Fd(0n, m, cf))
    case False{}:
      Equal.cong(U32, U32, w => D.QnW(w), D.Fd(0n, AC.Flag(m, cf), o), D.Fd(0n, m, o), fd0.ne(m, cf, o, eb))

def qn.flag(+m: Cr.Cir.Cells, +cf: U32, +o: U32) -> {D.QnW(D.Fd(0n, AC.Flag(m, cf), o)) == D.QnW(D.Fd(0n, m, o)) : U32}:
  qn.flag.b(U32.is_eq(o, cf), m, cf, o, {==})

def fv.flag.b(b: Bool, +m: Cr.Cir.Cells, +cf: U32, +o: U32, eb: {U32.is_eq(o, cf) == b : Bool}) ->
  {D.FvW(D.Fd(0n, AC.Flag(m, cf), o)) == D.FvW(D.Fd(0n, m, o)) : U32}:
  match b:
    case True{}:
      %Equal.sym(U32, o, cf, D.u32.eq(o, cf, eb)) : {D.FvW(D.Fd(0n, AC.Flag(m, cf), _)) == D.FvW(D.Fd(0n, m, _)) : U32}
      %Equal.sym(U32, D.Fd(0n, AC.Flag(m, cf), cf), U32.or(D.Fd(0n, m, cf), 512), fd0.cf(m, cf)) : {D.FvW(_) == D.FvW(D.Fd(0n, m, cf)) : U32}
      fv.dat(D.Fd(0n, m, cf))
    case False{}:
      Equal.cong(U32, U32, w => D.FvW(w), D.Fd(0n, AC.Flag(m, cf), o), D.Fd(0n, m, o), fd0.ne(m, cf, o, eb))

def fv.flag(+m: Cr.Cir.Cells, +cf: U32, +o: U32) -> {D.FvW(D.Fd(0n, AC.Flag(m, cf), o)) == D.FvW(D.Fd(0n, m, o)) : U32}:
  fv.flag.b(U32.is_eq(o, cf), m, cf, o, {==})

# a cell after the flag: its old fields, field 0 the new one
def cell.eta0(+y: Cr.Cir.Cell, +w: U32) ->
  {Cr.Cir.Cell.set(0n, y, w) == Cr.Cir.Cell{w, Cr.Cir.Cell.get(1n, y), Cr.Cir.Cell.get(2n, y), Cr.Cir.Cell.get(3n, y), Cr.Cir.Cell.get(4n, y)} : Cr.Cir.Cell}:
  match y:
    case Cr.Cir.Cell{a, b, c2, c3, c4}:
      {==}

def set0.id(+y: Cr.Cir.Cell) -> {y == Cr.Cir.Cell.set(0n, y, Cr.Cir.Cell.get(0n, y)) : Cr.Cir.Cell}:
  match y:
    case Cr.Cir.Cell{a, b, c2, c3, c4}:
      {==}

def fl.at.b(b: Bool, +m: Cr.Cir.Cells, +cf: U32, +o: U32, +eb: {U32.is_eq(o, cf) == b : Bool}) ->
  {Cr.Cir.Cells.get(AC.Flag(m, cf), o) == Cr.Cir.Cell.set(0n, Cr.Cir.Cells.get(m, o), D.Fd(0n, AC.Flag(m, cf), o)) : Cr.Cir.Cell}:
  match b:
    case True{}:
      +X = Cr.Cir.Cell.set(0n, Cr.Cir.Cells.get(m, cf), U32.or(D.Fd(0n, m, cf), 512))
      %Equal.sym(U32, o, cf, D.u32.eq(o, cf, eb)) :
        {Cr.Cir.Cells.get(AC.Flag(m, cf), _) == Cr.Cir.Cell.set(0n, Cr.Cir.Cells.get(m, _), D.Fd(0n, AC.Flag(m, cf), _)) : Cr.Cir.Cell}
      %Equal.sym(U32, D.Fd(0n, AC.Flag(m, cf), cf), U32.or(D.Fd(0n, m, cf), 512), fd0.cf(m, cf)) :
        {Cr.Cir.Cells.get(AC.Flag(m, cf), cf) == Cr.Cir.Cell.set(0n, Cr.Cir.Cells.get(m, cf), _) : Cr.Cir.Cell}
      D.cl.gs(m, cf, X)
    case False{}:
      +Y = Cr.Cir.Cells.get(m, o)
      %Equal.sym(U32, D.Fd(0n, AC.Flag(m, cf), o), D.Fd(0n, m, o), fd0.ne(m, cf, o, eb)) :
        {Cr.Cir.Cells.get(AC.Flag(m, cf), o) == Cr.Cir.Cell.set(0n, Y, _) : Cr.Cir.Cell}
      Equal.trans(Cr.Cir.Cell, Cr.Cir.Cells.get(AC.Flag(m, cf), o), Y, Cr.Cir.Cell.set(0n, Y, Cr.Cir.Cell.get(0n, Y)),
        D.cl.go(m, o, cf, Cr.Cir.Cell.set(0n, Cr.Cir.Cells.get(m, cf), U32.or(D.Fd(0n, m, cf), 512)), eb), set0.id(Y))

# the cell o after the flag, as a cell of its fields
def flag.cell(+m: Cr.Cir.Cells, +cf: U32, +o: U32) ->
  {Cr.Cir.Cells.get(AC.Flag(m, cf), o) ==
    Cr.Cir.Cell{D.Fd(0n, AC.Flag(m, cf), o), D.Fd(1n, m, o), D.Fd(2n, m, o), D.Fd(3n, m, o), D.Fd(4n, m, o)} : Cr.Cir.Cell}:
  Equal.trans(Cr.Cir.Cell, Cr.Cir.Cells.get(AC.Flag(m, cf), o), Cr.Cir.Cell.set(0n, Cr.Cir.Cells.get(m, o), D.Fd(0n, AC.Flag(m, cf), o)),
    Cr.Cir.Cell{D.Fd(0n, AC.Flag(m, cf), o), D.Fd(1n, m, o), D.Fd(2n, m, o), D.Fd(3n, m, o), D.Fd(4n, m, o)},
    fl.at.b(U32.is_eq(o, cf), m, cf, o, {==}), cell.eta0(Cr.Cir.Cells.get(m, o), D.Fd(0n, AC.Flag(m, cf), o)))

# DATA set in field 0, when (for dk) the term is Data
def dat.or(dk: Bool, +f: U32, -t: Bk.Term, h: D.DataK(dk, 512, t)) -> D.DataK(dk, U32.or(f, 512), t):
  match dk:
    case True{}:
      D.or.r(Bool.not(D.FlW(U32.or(f, 512), 512)), El.Term.is_data(t), h)
    case False{}:
      Unit{}

# DATA's meaning at a node, of the term t
def ndk.data(-dk: Bool, -ds: List<&2, Bk.Def>, -im: U32, -fi: U32, -nx: U32, -c: U32, -x: Cr.Cir.Cell, -t: Bk.Term, -tag: U32,
  h: D.NdK(dk, ds, im, fi, nx, c, x, t, tag)) -> D.DataK(dk, Cr.Cir.Cell.get(0n, x), t):
  (_, r0) = h
  (_, r1) = r0
  (_, r2) = r1
  (_, r3) = r2
  (e4, _) = r3
  e4

# DATA's meaning after the flag at the cell c of t: by hd at cf, as before
# elsewhere. hd is used once: after it, a cell stands for one term (U1's
# isk.uniq) gives DATA's meaning of every other term at cf from that one
def root.dat(b: Bool, +dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells,
  +im: U32, +fi: U32, +nx: U32, +cf: U32, +c: U32, +t: Bk.Term, +eb: {U32.is_eq(c, cf) == b : Bool},
  +h: D.IsK(dk, ds, m, im, fi, nx, ks, img, c, t), hd: @t2: Bk.Term -> D.IsK(dk, ds, m, im, fi, nx, ks, img, cf, t2) -> D.DataK(dk, 512, t2), -R: Type,
  ck: (@t2: Bk.Term -> D.IsK(dk, ds, m, im, fi, nx, ks, img, cf, t2) -> D.DataK(dk, 512, t2)) -> D.DataK(dk, D.Fd(0n, AC.Flag(m, cf), c), t) -> R) -> R:
  match b:
    case True{}:
      +e = D.u32.eq(c, cf, eb)
      +hs = {(%e : D.IsK(dk, ds, m, im, fi, nx, ks, img, _, t); h) : D.IsK(dk, ds, m, im, fi, nx, ks, img, cf, t)}
      +dat = hd(t, hs)
      ck(t2 => h2 => (%AC.isk.uniq(dk, ds, m, im, fi, nx, ks, img, cf, t, t2, hs, h2) : D.DataK(dk, 512, _); dat),
        (%Equal.sym(U32, c, cf, e) : D.DataK(dk, D.Fd(0n, AC.Flag(m, cf), _), t);
          (%Equal.sym(U32, D.Fd(0n, AC.Flag(m, cf), cf), U32.or(D.Fd(0n, m, cf), 512), fd0.cf(m, cf)) : D.DataK(dk, _, t);
            dat.or(dk, D.Fd(0n, m, cf), t, dat))))
    case False{}:
      ck(hd, (%Equal.sym(U32, D.Fd(0n, AC.Flag(m, cf), c), D.Fd(0n, m, c), fd0.ne(m, cf, c, eb)) : D.DataK(dk, _, t);
        ndk.data(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), t, D.A.tag(t), isk.nd(dk, t, ds, m, im, fi, nx, ks, img, c, h))))

# a node's facts after the flag, its field 0 now that of the flag (DATA's
# meaning given)
def ndk.flag(-dk: Bool, -ds: List<&2, Bk.Def>, +im: U32, +fi: U32, +nx: U32, +m: Cr.Cir.Cells, +cf: U32, +c: U32, -t: Bk.Term, -tag: U32,
  hdat: D.DataK(dk, D.Fd(0n, AC.Flag(m, cf), c), t), h: D.NdK(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), t, tag)) ->
  D.NdK(dk, ds, im, fi, nx, c, Cr.Cir.Cell{D.Fd(0n, AC.Flag(m, cf), c), D.Fd(1n, m, c), D.Fd(2n, m, c), D.Fd(3n, m, c), D.Fd(4n, m, c)}, t, tag):
  (e0, r0) = h
  (e1, r1) = r0
  (e2, r2) = r1
  (e3, r3) = r2
  (_, e5) = r3
  +W = D.Fd(0n, AC.Flag(m, cf), c)
  +f0 = D.Fd(0n, m, c)
  (e0, ((%Equal.sym(Bool, D.Fl(AC.Flag(m, cf), c, 1024), D.Fl(m, c, 1024), AC.fl.flag(m, cf, c, 1024, AC.and.dat.st())) :
      {Bool.or(D.Own(fi, nx, c), _) == True{} : Bool}; e1),
    (Equal.trans(U32, D.TgW(W), D.TgW(f0), tag, AC.tg.flag(m, cf, c), e2),
    ((%Equal.sym(Bool, D.Fl(AC.Flag(m, cf), c, 256), D.Fl(m, c, 256), AC.fl.flag(m, cf, c, 256, dat.v())) :
        {Bool.or(Bool.not(_), El.Eval.vals(ds, t, False{})) == True{} : Bool}; e3),
    (hdat, (%Equal.sym(U32, D.FvW(W), D.FvW(f0), fv.flag(m, cf, c)) :
        {Bool.or(U32.is_eq(_, 524287), D.Term.below(t, U32.to_nat(_))) == True{} : Bool}; e5))))))

# a part's Sp after the flag: STATIC stays
def sp.flag(+fi: U32, +nx: U32, +c: U32, +m: Cr.Cir.Cells, +cf: U32, +y: U32, h: D.Sp(fi, nx, c, Cr.Cir.Cells.get(m, y))) ->
  D.Sp(fi, nx, c, Cr.Cir.Cells.get(AC.Flag(m, cf), y)):
  %Equal.sym(Bool, D.Fl(AC.Flag(m, cf), y, 1024), D.Fl(m, y, 1024), AC.fl.flag(m, cf, y, 1024, AC.and.dat.st())) :
    {Bool.or(D.Own(fi, nx, c), _) == True{} : Bool}
  h

# a cell stands for its term after the flag (hd is threaded: k gets what
# is left of it)
def isk.dat(+dk: Bool, t: Bk.Term, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +cf: U32, +c: U32, +h: D.IsK(dk, ds, m, im, fi, nx, ks, img, c, t),
  hd: @t2: Bk.Term -> D.IsK(dk, ds, m, im, fi, nx, ks, img, cf, t2) -> D.DataK(dk, 512, t2), -R: Type, ck: (@t2: Bk.Term -> D.IsK(dk, ds, m, im, fi, nx, ks, img, cf, t2) -> D.DataK(dk, 512, t2)) -> D.IsK(dk, ds, AC.Flag(m, cf), im, fi, nx, ks, img, c, t) -> R) -> R:
  match t:
    case Bk.Term.Var{+i}:
      (+nd, hi) = h
      root.dat(U32.is_eq(c, cf), dk, ds, ks, img, m, im, fi, nx, cf, c, Bk.Term.Var{i}, {==}, h, hd, R, hd0 => dat =>
        ck(hd0, D.isc.atk(dk, ds, AC.Flag(m, cf), im, fi, nx, ks, img, c, Cr.Cir.Cells.get(AC.Flag(m, cf), c), Cr.Cir.Cell{D.Fd(0n, AC.Flag(m, cf), c), D.Fd(1n, m, c), D.Fd(2n, m, c), D.Fd(3n, m, c), D.Fd(4n, m, c)}, Bk.Term.Var{i}, flag.cell(m, cf, c), (ndk.flag(dk, ds, im, fi, nx, m, cf, c, Bk.Term.Var{i}, 0, dat, nd), hi))))
    case Bk.Term.Ref{+k}:
      (+nd, r) = h
      (hm, r2) = r
      (hfv, hrf) = r2
      root.dat(U32.is_eq(c, cf), dk, ds, ks, img, m, im, fi, nx, cf, c, Bk.Term.Ref{k}, {==}, h, hd, R, hd0 => dat =>
        ck(hd0, D.isc.atk(dk, ds, AC.Flag(m, cf), im, fi, nx, ks, img, c, Cr.Cir.Cells.get(AC.Flag(m, cf), c), Cr.Cir.Cell{D.Fd(0n, AC.Flag(m, cf), c), D.Fd(1n, m, c), D.Fd(2n, m, c), D.Fd(3n, m, c), D.Fd(4n, m, c)}, Bk.Term.Ref{k}, flag.cell(m, cf, c), (ndk.flag(dk, ds, im, fi, nx, m, cf, c, Bk.Term.Ref{k}, 1, dat, nd), (hm, (Equal.trans(U32, D.FvW(D.Fd(0n, AC.Flag(m, cf), c)), D.FvW(D.Fd(0n, m, c)), 0, fv.flag(m, cf, c), hfv), hrf))))))
    case Bk.Term.Ann{+t1, +t2}:
      (+nd, r0) = h
      (p2, r1) = r0
      (sp2, h2) = p2
      (sp3, h3) = r1
      root.dat(U32.is_eq(c, cf), dk, ds, ks, img, m, im, fi, nx, cf, c, Bk.Term.Ann{t1, t2}, {==}, h, hd, R, hd0 => dat =>
        isk.dat(dk, t1, ds, m, im, fi, nx, ks, img, cf, D.Fd(2n, m, c), h2, hd0, R, hd2 => q2 =>
          isk.dat(dk, t2, ds, m, im, fi, nx, ks, img, cf, D.Fd(3n, m, c), h3, hd2, R, hd3 => q3 =>
            ck(hd3, D.isc.atk(dk, ds, AC.Flag(m, cf), im, fi, nx, ks, img, c, Cr.Cir.Cells.get(AC.Flag(m, cf), c), Cr.Cir.Cell{D.Fd(0n, AC.Flag(m, cf), c), D.Fd(1n, m, c), D.Fd(2n, m, c), D.Fd(3n, m, c), D.Fd(4n, m, c)}, Bk.Term.Ann{t1, t2}, flag.cell(m, cf, c), (ndk.flag(dk, ds, im, fi, nx, m, cf, c, Bk.Term.Ann{t1, t2}, 2, dat, nd), ((sp.flag(fi, nx, c, m, cf, D.Fd(2n, m, c), sp2), q2), (sp.flag(fi, nx, c, m, cf, D.Fd(3n, m, c), sp3), q3))))))))
    case Bk.Term.Let{+q, +t1, +t2}:
      (+nd, r0) = h
      (hq, r1) = r0
      (p2, r2) = r1
      (sp2, h2) = p2
      (sp3, h3) = r2
      root.dat(U32.is_eq(c, cf), dk, ds, ks, img, m, im, fi, nx, cf, c, Bk.Term.Let{q, t1, t2}, {==}, h, hd, R, hd0 => dat =>
        isk.dat(dk, t1, ds, m, im, fi, nx, ks, img, cf, D.Fd(2n, m, c), h2, hd0, R, hd2 => q2 =>
          isk.dat(dk, t2, ds, m, im, fi, nx, ks, img, cf, D.Fd(3n, m, c), h3, hd2, R, hd3 => q3 =>
            ck(hd3, D.isc.atk(dk, ds, AC.Flag(m, cf), im, fi, nx, ks, img, c, Cr.Cir.Cells.get(AC.Flag(m, cf), c), Cr.Cir.Cell{D.Fd(0n, AC.Flag(m, cf), c), D.Fd(1n, m, c), D.Fd(2n, m, c), D.Fd(3n, m, c), D.Fd(4n, m, c)}, Bk.Term.Let{q, t1, t2}, flag.cell(m, cf, c), (ndk.flag(dk, ds, im, fi, nx, m, cf, c, Bk.Term.Let{q, t1, t2}, 3, dat, nd), (Equal.trans(U32, D.QnW(D.Fd(0n, AC.Flag(m, cf), c)), D.QnW(D.Fd(0n, m, c)), Mc.Img.quan(q), qn.flag(m, cf, c), hq), ((sp.flag(fi, nx, c, m, cf, D.Fd(2n, m, c), sp2), q2), (sp.flag(fi, nx, c, m, cf, D.Fd(3n, m, c), sp3), q3)))))))))
    case Bk.Term.Typ{+t1}:
      (+nd, r0) = h
      (sp2, h2) = r0
      root.dat(U32.is_eq(c, cf), dk, ds, ks, img, m, im, fi, nx, cf, c, Bk.Term.Typ{t1}, {==}, h, hd, R, hd0 => dat =>
        isk.dat(dk, t1, ds, m, im, fi, nx, ks, img, cf, D.Fd(2n, m, c), h2, hd0, R, hd2 => q2 =>
          ck(hd2, D.isc.atk(dk, ds, AC.Flag(m, cf), im, fi, nx, ks, img, c, Cr.Cir.Cells.get(AC.Flag(m, cf), c), Cr.Cir.Cell{D.Fd(0n, AC.Flag(m, cf), c), D.Fd(1n, m, c), D.Fd(2n, m, c), D.Fd(3n, m, c), D.Fd(4n, m, c)}, Bk.Term.Typ{t1}, flag.cell(m, cf, c), (ndk.flag(dk, ds, im, fi, nx, m, cf, c, Bk.Term.Typ{t1}, 4, dat, nd), (sp.flag(fi, nx, c, m, cf, D.Fd(2n, m, c), sp2), q2))))))
    case Bk.Term.Min{+t1, +t2}:
      (+nd, r0) = h
      (p2, r1) = r0
      (sp2, h2) = p2
      (sp3, h3) = r1
      root.dat(U32.is_eq(c, cf), dk, ds, ks, img, m, im, fi, nx, cf, c, Bk.Term.Min{t1, t2}, {==}, h, hd, R, hd0 => dat =>
        isk.dat(dk, t1, ds, m, im, fi, nx, ks, img, cf, D.Fd(2n, m, c), h2, hd0, R, hd2 => q2 =>
          isk.dat(dk, t2, ds, m, im, fi, nx, ks, img, cf, D.Fd(3n, m, c), h3, hd2, R, hd3 => q3 =>
            ck(hd3, D.isc.atk(dk, ds, AC.Flag(m, cf), im, fi, nx, ks, img, c, Cr.Cir.Cells.get(AC.Flag(m, cf), c), Cr.Cir.Cell{D.Fd(0n, AC.Flag(m, cf), c), D.Fd(1n, m, c), D.Fd(2n, m, c), D.Fd(3n, m, c), D.Fd(4n, m, c)}, Bk.Term.Min{t1, t2}, flag.cell(m, cf, c), (ndk.flag(dk, ds, im, fi, nx, m, cf, c, Bk.Term.Min{t1, t2}, 5, dat, nd), ((sp.flag(fi, nx, c, m, cf, D.Fd(2n, m, c), sp2), q2), (sp.flag(fi, nx, c, m, cf, D.Fd(3n, m, c), sp3), q3))))))))
    case Bk.Term.All{+q, +t1, +t2}:
      (+nd, r0) = h
      (hq, r1) = r0
      (p2, r2) = r1
      (sp2, h2) = p2
      (sp3, h3) = r2
      root.dat(U32.is_eq(c, cf), dk, ds, ks, img, m, im, fi, nx, cf, c, Bk.Term.All{q, t1, t2}, {==}, h, hd, R, hd0 => dat =>
        isk.dat(dk, t1, ds, m, im, fi, nx, ks, img, cf, D.Fd(2n, m, c), h2, hd0, R, hd2 => q2 =>
          isk.dat(dk, t2, ds, m, im, fi, nx, ks, img, cf, D.Fd(3n, m, c), h3, hd2, R, hd3 => q3 =>
            ck(hd3, D.isc.atk(dk, ds, AC.Flag(m, cf), im, fi, nx, ks, img, c, Cr.Cir.Cells.get(AC.Flag(m, cf), c), Cr.Cir.Cell{D.Fd(0n, AC.Flag(m, cf), c), D.Fd(1n, m, c), D.Fd(2n, m, c), D.Fd(3n, m, c), D.Fd(4n, m, c)}, Bk.Term.All{q, t1, t2}, flag.cell(m, cf, c), (ndk.flag(dk, ds, im, fi, nx, m, cf, c, Bk.Term.All{q, t1, t2}, 6, dat, nd), (Equal.trans(U32, D.QnW(D.Fd(0n, AC.Flag(m, cf), c)), D.QnW(D.Fd(0n, m, c)), Mc.Img.quan(q), qn.flag(m, cf, c), hq), ((sp.flag(fi, nx, c, m, cf, D.Fd(2n, m, c), sp2), q2), (sp.flag(fi, nx, c, m, cf, D.Fd(3n, m, c), sp3), q3)))))))))
    case Bk.Term.Lam{+q, +t1}:
      (+nd, r0) = h
      (hq, r1) = r0
      (sp2, h2) = r1
      root.dat(U32.is_eq(c, cf), dk, ds, ks, img, m, im, fi, nx, cf, c, Bk.Term.Lam{q, t1}, {==}, h, hd, R, hd0 => dat =>
        isk.dat(dk, t1, ds, m, im, fi, nx, ks, img, cf, D.Fd(2n, m, c), h2, hd0, R, hd2 => q2 =>
          ck(hd2, D.isc.atk(dk, ds, AC.Flag(m, cf), im, fi, nx, ks, img, c, Cr.Cir.Cells.get(AC.Flag(m, cf), c), Cr.Cir.Cell{D.Fd(0n, AC.Flag(m, cf), c), D.Fd(1n, m, c), D.Fd(2n, m, c), D.Fd(3n, m, c), D.Fd(4n, m, c)}, Bk.Term.Lam{q, t1}, flag.cell(m, cf, c), (ndk.flag(dk, ds, im, fi, nx, m, cf, c, Bk.Term.Lam{q, t1}, 7, dat, nd), (Equal.trans(U32, D.QnW(D.Fd(0n, AC.Flag(m, cf), c)), D.QnW(D.Fd(0n, m, c)), Mc.Img.quan(q), qn.flag(m, cf, c), hq), (sp.flag(fi, nx, c, m, cf, D.Fd(2n, m, c), sp2), q2)))))))
    case Bk.Term.App{+q, +t1, +t2}:
      (+nd, r0) = h
      (hq, r1) = r0
      (p2, r2) = r1
      (sp2, h2) = p2
      (sp3, h3) = r2
      root.dat(U32.is_eq(c, cf), dk, ds, ks, img, m, im, fi, nx, cf, c, Bk.Term.App{q, t1, t2}, {==}, h, hd, R, hd0 => dat =>
        isk.dat(dk, t1, ds, m, im, fi, nx, ks, img, cf, D.Fd(2n, m, c), h2, hd0, R, hd2 => q2 =>
          isk.dat(dk, t2, ds, m, im, fi, nx, ks, img, cf, D.Fd(3n, m, c), h3, hd2, R, hd3 => q3 =>
            ck(hd3, D.isc.atk(dk, ds, AC.Flag(m, cf), im, fi, nx, ks, img, c, Cr.Cir.Cells.get(AC.Flag(m, cf), c), Cr.Cir.Cell{D.Fd(0n, AC.Flag(m, cf), c), D.Fd(1n, m, c), D.Fd(2n, m, c), D.Fd(3n, m, c), D.Fd(4n, m, c)}, Bk.Term.App{q, t1, t2}, flag.cell(m, cf, c), (ndk.flag(dk, ds, im, fi, nx, m, cf, c, Bk.Term.App{q, t1, t2}, 8, dat, nd), (Equal.trans(U32, D.QnW(D.Fd(0n, AC.Flag(m, cf), c)), D.QnW(D.Fd(0n, m, c)), Mc.Img.quan(q), qn.flag(m, cf, c), hq), ((sp.flag(fi, nx, c, m, cf, D.Fd(2n, m, c), sp2), q2), (sp.flag(fi, nx, c, m, cf, D.Fd(3n, m, c), sp3), q3)))))))))
    case Bk.Term.Sig{+q, +t1, +t2}:
      (+nd, r0) = h
      (hq, r1) = r0
      (p2, r2) = r1
      (sp2, h2) = p2
      (sp3, h3) = r2
      root.dat(U32.is_eq(c, cf), dk, ds, ks, img, m, im, fi, nx, cf, c, Bk.Term.Sig{q, t1, t2}, {==}, h, hd, R, hd0 => dat =>
        isk.dat(dk, t1, ds, m, im, fi, nx, ks, img, cf, D.Fd(2n, m, c), h2, hd0, R, hd2 => q2 =>
          isk.dat(dk, t2, ds, m, im, fi, nx, ks, img, cf, D.Fd(3n, m, c), h3, hd2, R, hd3 => q3 =>
            ck(hd3, D.isc.atk(dk, ds, AC.Flag(m, cf), im, fi, nx, ks, img, c, Cr.Cir.Cells.get(AC.Flag(m, cf), c), Cr.Cir.Cell{D.Fd(0n, AC.Flag(m, cf), c), D.Fd(1n, m, c), D.Fd(2n, m, c), D.Fd(3n, m, c), D.Fd(4n, m, c)}, Bk.Term.Sig{q, t1, t2}, flag.cell(m, cf, c), (ndk.flag(dk, ds, im, fi, nx, m, cf, c, Bk.Term.Sig{q, t1, t2}, 9, dat, nd), (Equal.trans(U32, D.QnW(D.Fd(0n, AC.Flag(m, cf), c)), D.QnW(D.Fd(0n, m, c)), Mc.Img.quan(q), qn.flag(m, cf, c), hq), ((sp.flag(fi, nx, c, m, cf, D.Fd(2n, m, c), sp2), q2), (sp.flag(fi, nx, c, m, cf, D.Fd(3n, m, c), sp3), q3)))))))))
    case Bk.Term.Tup{+q, +t1, +t2}:
      (+nd, r0) = h
      (hq, r1) = r0
      (p2, r2) = r1
      (sp2, h2) = p2
      (sp3, h3) = r2
      root.dat(U32.is_eq(c, cf), dk, ds, ks, img, m, im, fi, nx, cf, c, Bk.Term.Tup{q, t1, t2}, {==}, h, hd, R, hd0 => dat =>
        isk.dat(dk, t1, ds, m, im, fi, nx, ks, img, cf, D.Fd(2n, m, c), h2, hd0, R, hd2 => q2 =>
          isk.dat(dk, t2, ds, m, im, fi, nx, ks, img, cf, D.Fd(3n, m, c), h3, hd2, R, hd3 => q3 =>
            ck(hd3, D.isc.atk(dk, ds, AC.Flag(m, cf), im, fi, nx, ks, img, c, Cr.Cir.Cells.get(AC.Flag(m, cf), c), Cr.Cir.Cell{D.Fd(0n, AC.Flag(m, cf), c), D.Fd(1n, m, c), D.Fd(2n, m, c), D.Fd(3n, m, c), D.Fd(4n, m, c)}, Bk.Term.Tup{q, t1, t2}, flag.cell(m, cf, c), (ndk.flag(dk, ds, im, fi, nx, m, cf, c, Bk.Term.Tup{q, t1, t2}, 10, dat, nd), (Equal.trans(U32, D.QnW(D.Fd(0n, AC.Flag(m, cf), c)), D.QnW(D.Fd(0n, m, c)), Mc.Img.quan(q), qn.flag(m, cf, c), hq), ((sp.flag(fi, nx, c, m, cf, D.Fd(2n, m, c), sp2), q2), (sp.flag(fi, nx, c, m, cf, D.Fd(3n, m, c), sp3), q3)))))))))
    case Bk.Term.Prj{+t1}:
      (+nd, r0) = h
      (sp2, h2) = r0
      root.dat(U32.is_eq(c, cf), dk, ds, ks, img, m, im, fi, nx, cf, c, Bk.Term.Prj{t1}, {==}, h, hd, R, hd0 => dat =>
        isk.dat(dk, t1, ds, m, im, fi, nx, ks, img, cf, D.Fd(2n, m, c), h2, hd0, R, hd2 => q2 =>
          ck(hd2, D.isc.atk(dk, ds, AC.Flag(m, cf), im, fi, nx, ks, img, c, Cr.Cir.Cells.get(AC.Flag(m, cf), c), Cr.Cir.Cell{D.Fd(0n, AC.Flag(m, cf), c), D.Fd(1n, m, c), D.Fd(2n, m, c), D.Fd(3n, m, c), D.Fd(4n, m, c)}, Bk.Term.Prj{t1}, flag.cell(m, cf, c), (ndk.flag(dk, ds, im, fi, nx, m, cf, c, Bk.Term.Prj{t1}, 11, dat, nd), (sp.flag(fi, nx, c, m, cf, D.Fd(2n, m, c), sp2), q2))))))
    case Bk.Term.Enu{+k}:
      (+nd, r) = h
      (hm, hfv) = r
      root.dat(U32.is_eq(c, cf), dk, ds, ks, img, m, im, fi, nx, cf, c, Bk.Term.Enu{k}, {==}, h, hd, R, hd0 => dat =>
        ck(hd0, D.isc.atk(dk, ds, AC.Flag(m, cf), im, fi, nx, ks, img, c, Cr.Cir.Cells.get(AC.Flag(m, cf), c), Cr.Cir.Cell{D.Fd(0n, AC.Flag(m, cf), c), D.Fd(1n, m, c), D.Fd(2n, m, c), D.Fd(3n, m, c), D.Fd(4n, m, c)}, Bk.Term.Enu{k}, flag.cell(m, cf, c), (ndk.flag(dk, ds, im, fi, nx, m, cf, c, Bk.Term.Enu{k}, 12, dat, nd), (hm, Equal.trans(U32, D.FvW(D.Fd(0n, AC.Flag(m, cf), c)), D.FvW(D.Fd(0n, m, c)), 0, fv.flag(m, cf, c), hfv))))))
    case Bk.Term.Lab{+k}:
      (+nd, hn) = h
      root.dat(U32.is_eq(c, cf), dk, ds, ks, img, m, im, fi, nx, cf, c, Bk.Term.Lab{k}, {==}, h, hd, R, hd0 => dat =>
        ck(hd0, D.isc.atk(dk, ds, AC.Flag(m, cf), im, fi, nx, ks, img, c, Cr.Cir.Cells.get(AC.Flag(m, cf), c), Cr.Cir.Cell{D.Fd(0n, AC.Flag(m, cf), c), D.Fd(1n, m, c), D.Fd(2n, m, c), D.Fd(3n, m, c), D.Fd(4n, m, c)}, Bk.Term.Lab{k}, flag.cell(m, cf, c), (ndk.flag(dk, ds, im, fi, nx, m, cf, c, Bk.Term.Lab{k}, 13, dat, nd), hn))))
    case Bk.Term.Mat{+k, +t1, +t2}:
      (+nd, r0) = h
      (hn, r1) = r0
      (p3, r2) = r1
      (sp3, h3) = p3
      (sp4, h4) = r2
      root.dat(U32.is_eq(c, cf), dk, ds, ks, img, m, im, fi, nx, cf, c, Bk.Term.Mat{k, t1, t2}, {==}, h, hd, R, hd0 => dat =>
        isk.dat(dk, t1, ds, m, im, fi, nx, ks, img, cf, D.Fd(3n, m, c), h3, hd0, R, hd3 => q3 =>
          isk.dat(dk, t2, ds, m, im, fi, nx, ks, img, cf, D.Fd(4n, m, c), h4, hd3, R, hd4 => q4 =>
            ck(hd4, D.isc.atk(dk, ds, AC.Flag(m, cf), im, fi, nx, ks, img, c, Cr.Cir.Cells.get(AC.Flag(m, cf), c), Cr.Cir.Cell{D.Fd(0n, AC.Flag(m, cf), c), D.Fd(1n, m, c), D.Fd(2n, m, c), D.Fd(3n, m, c), D.Fd(4n, m, c)}, Bk.Term.Mat{k, t1, t2}, flag.cell(m, cf, c), (ndk.flag(dk, ds, im, fi, nx, m, cf, c, Bk.Term.Mat{k, t1, t2}, 14, dat, nd), (hn, ((sp.flag(fi, nx, c, m, cf, D.Fd(3n, m, c), sp3), q3), (sp.flag(fi, nx, c, m, cf, D.Fd(4n, m, c), sp4), q4)))))))))
    case Bk.Term.Efq{}:
      root.dat(U32.is_eq(c, cf), dk, ds, ks, img, m, im, fi, nx, cf, c, Bk.Term.Efq{}, {==}, h, hd, R, hd0 => dat =>
        ck(hd0, D.isc.atk(dk, ds, AC.Flag(m, cf), im, fi, nx, ks, img, c, Cr.Cir.Cells.get(AC.Flag(m, cf), c), Cr.Cir.Cell{D.Fd(0n, AC.Flag(m, cf), c), D.Fd(1n, m, c), D.Fd(2n, m, c), D.Fd(3n, m, c), D.Fd(4n, m, c)}, Bk.Term.Efq{}, flag.cell(m, cf, c), ndk.flag(dk, ds, im, fi, nx, m, cf, c, Bk.Term.Efq{}, 15, dat, h))))
    case Bk.Term.Eql{+t1, +t2, +t3}:
      (+nd, r0) = h
      (p2, r1) = r0
      (sp2, h2) = p2
      (p3, r2) = r1
      (sp3, h3) = p3
      (sp4, h4) = r2
      root.dat(U32.is_eq(c, cf), dk, ds, ks, img, m, im, fi, nx, cf, c, Bk.Term.Eql{t1, t2, t3}, {==}, h, hd, R, hd0 => dat =>
        isk.dat(dk, t1, ds, m, im, fi, nx, ks, img, cf, D.Fd(2n, m, c), h2, hd0, R, hd2 => q2 =>
          isk.dat(dk, t2, ds, m, im, fi, nx, ks, img, cf, D.Fd(3n, m, c), h3, hd2, R, hd3 => q3 =>
            isk.dat(dk, t3, ds, m, im, fi, nx, ks, img, cf, D.Fd(4n, m, c), h4, hd3, R, hd4 => q4 =>
              ck(hd4, D.isc.atk(dk, ds, AC.Flag(m, cf), im, fi, nx, ks, img, c, Cr.Cir.Cells.get(AC.Flag(m, cf), c), Cr.Cir.Cell{D.Fd(0n, AC.Flag(m, cf), c), D.Fd(1n, m, c), D.Fd(2n, m, c), D.Fd(3n, m, c), D.Fd(4n, m, c)}, Bk.Term.Eql{t1, t2, t3}, flag.cell(m, cf, c), (ndk.flag(dk, ds, im, fi, nx, m, cf, c, Bk.Term.Eql{t1, t2, t3}, 16, dat, nd), ((sp.flag(fi, nx, c, m, cf, D.Fd(2n, m, c), sp2), q2), ((sp.flag(fi, nx, c, m, cf, D.Fd(3n, m, c), sp3), q3), (sp.flag(fi, nx, c, m, cf, D.Fd(4n, m, c), sp4), q4))))))))))
    case Bk.Term.Rfl{}:
      root.dat(U32.is_eq(c, cf), dk, ds, ks, img, m, im, fi, nx, cf, c, Bk.Term.Rfl{}, {==}, h, hd, R, hd0 => dat =>
        ck(hd0, D.isc.atk(dk, ds, AC.Flag(m, cf), im, fi, nx, ks, img, c, Cr.Cir.Cells.get(AC.Flag(m, cf), c), Cr.Cir.Cell{D.Fd(0n, AC.Flag(m, cf), c), D.Fd(1n, m, c), D.Fd(2n, m, c), D.Fd(3n, m, c), D.Fd(4n, m, c)}, Bk.Term.Rfl{}, flag.cell(m, cf, c), ndk.flag(dk, ds, im, fi, nx, m, cf, c, Bk.Term.Rfl{}, 17, dat, h))))
    case Bk.Term.Rwt{+t1, +t2, +t3}:
      (+nd, r0) = h
      (p2, r1) = r0
      (sp2, h2) = p2
      (p3, r2) = r1
      (sp3, h3) = p3
      (sp4, h4) = r2
      root.dat(U32.is_eq(c, cf), dk, ds, ks, img, m, im, fi, nx, cf, c, Bk.Term.Rwt{t1, t2, t3}, {==}, h, hd, R, hd0 => dat =>
        isk.dat(dk, t1, ds, m, im, fi, nx, ks, img, cf, D.Fd(2n, m, c), h2, hd0, R, hd2 => q2 =>
          isk.dat(dk, t2, ds, m, im, fi, nx, ks, img, cf, D.Fd(3n, m, c), h3, hd2, R, hd3 => q3 =>
            isk.dat(dk, t3, ds, m, im, fi, nx, ks, img, cf, D.Fd(4n, m, c), h4, hd3, R, hd4 => q4 =>
              ck(hd4, D.isc.atk(dk, ds, AC.Flag(m, cf), im, fi, nx, ks, img, c, Cr.Cir.Cells.get(AC.Flag(m, cf), c), Cr.Cir.Cell{D.Fd(0n, AC.Flag(m, cf), c), D.Fd(1n, m, c), D.Fd(2n, m, c), D.Fd(3n, m, c), D.Fd(4n, m, c)}, Bk.Term.Rwt{t1, t2, t3}, flag.cell(m, cf, c), (ndk.flag(dk, ds, im, fi, nx, m, cf, c, Bk.Term.Rwt{t1, t2, t3}, 18, dat, nd), ((sp.flag(fi, nx, c, m, cf, D.Fd(2n, m, c), sp2), q2), ((sp.flag(fi, nx, c, m, cf, D.Fd(3n, m, c), sp3), q3), (sp.flag(fi, nx, c, m, cf, D.Fd(4n, m, c), sp4), q4))))))))))

def rtsk.dat(+dk: Bool, rs: List<&2, D.Rt>, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +cf: U32, h: D.RtsK(dk, ds, m, im, fi, nx, ks, img, rs),
  hd: @t2: Bk.Term -> D.IsK(dk, ds, m, im, fi, nx, ks, img, cf, t2) -> D.DataK(dk, 512, t2), -R: Type, ck: (@t2: Bk.Term -> D.IsK(dk, ds, m, im, fi, nx, ks, img, cf, t2) -> D.DataK(dk, 512, t2)) -> D.RtsK(dk, ds, AC.Flag(m, cf), im, fi, nx, ks, img, rs) -> R) -> R:
  match rs:
    case Nil{}:
      ck(hd, Unit{})
    case Con{D.Rt{+c, +u}, +rest}:
      match h:
        case Tuple{+hu, hr}:
          isk.dat(dk, u, ds, m, im, fi, nx, ks, img, cf, c, hu, hd, R, hd1 => q1 =>
            rtsk.dat(dk, rest, ds, m, im, fi, nx, ks, img, cf, hr, hd1, R, hd2 => q2 => ck(hd2, (q1, q2))))


# a frame's part b after the flag
def frsb.dat(+dk: Bool, kind: D.FK, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +cf: U32, +c: U32, +b: Bk.Term,
  +h: D.Frs.bK(dk, ds, m, im, fi, nx, ks, img, c, kind, b), hd: @t2: Bk.Term -> D.IsK(dk, ds, m, im, fi, nx, ks, img, cf, t2) -> D.DataK(dk, 512, t2), -R: Type,
  ck: (@t2: Bk.Term -> D.IsK(dk, ds, m, im, fi, nx, ks, img, cf, t2) -> D.DataK(dk, 512, t2)) -> D.Frs.bK(dk, ds, AC.Flag(m, cf), im, fi, nx, ks, img, c, kind, b) -> R) -> R:
  match kind:
    case D.FK.rwt{}:
      isk.dat(dk, b, ds, m, im, fi, nx, ks, img, cf, c, h, hd, R, ck)
    case D.FK.arg{}:
      ck(hd, Unit{})
    case D.FK.val{}:
      ck(hd, Unit{})
    case D.FK.fun{}:
      ck(hd, Unit{})
    case D.FK.let{}:
      ck(hd, Unit{})
    case D.FK.tupb{}:
      ck(hd, Unit{})
    case D.FK.tupa{}:
      ck(hd, Unit{})
    case D.FK.minb{}:
      ck(hd, Unit{})
    case D.FK.mina{}:
      ck(hd, Unit{})

# the frames after the flag: tag, STATIC, K, the quantity and the links stay
def frsk.dat(+dk: Bool, fs: List<&2, D.AF>, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +cf: U32, +fr: U32,
  h: D.FrsK(dk, ds, m, im, fi, nx, ks, img, ps, fr, fs), hd: @t2: Bk.Term -> D.IsK(dk, ds, m, im, fi, nx, ks, img, cf, t2) -> D.DataK(dk, 512, t2), -R: Type,
  ck: (@t2: Bk.Term -> D.IsK(dk, ds, m, im, fi, nx, ks, img, cf, t2) -> D.DataK(dk, 512, t2)) -> D.FrsK(dk, ds, AC.Flag(m, cf), im, fi, nx, ks, img, ps, fr, fs) -> R) -> R:
  match fs:
    case Nil{}:
      ck(hd, h)
    case Con{D.AF{+kind, +q, +k, +a, +b}, +rest}:
      match h:
        case Tuple{e0, Tuple{ev, Tuple{eo, Tuple{es, Tuple{em, Tuple{etg, Tuple{eq, Tuple{ek, Tuple{+ia, Tuple{+ib, ir}}}}}}}}}}:
          +M2 = AC.Flag(m, cf)
          isk.dat(dk, a, ds, m, im, fi, nx, ks, img, cf, D.Fd(2n, m, fr), ia, hd, R, hd1 => qa =>
            frsb.dat(dk, kind, ds, m, im, fi, nx, ks, img, cf, D.Fd(3n, m, fr), b, ib, hd1, R, hd2 => qb =>
              frsk.dat(dk, rest, ds, m, im, fi, nx, ks, img, ps, cf, D.Fd(1n, m, fr), ir, hd2, R, hd3 => qr =>
                ck(hd3, (e0, (ev, (eo, (Equal.trans(Bool, D.Fl(M2, fr, 1024), D.Fl(m, fr, 1024), False{}, AC.fl.flag(m, cf, fr, 1024, AC.and.dat.st()), es),
                  (em, (Equal.trans(U32, D.Tg(M2, fr), D.Tg(m, fr), D.FK.tag(kind), AC.tg.flag(m, cf, fr), etg),
                  (Equal.trans(U32, D.QnW(D.Fd(0n, M2, fr)), D.QnW(D.Fd(0n, m, fr)), Mc.Img.quan(q), qn.flag(m, cf, fr), eq),
                  (Equal.trans(Bool, D.Fl(M2, fr, 2048), D.Fl(m, fr, 2048), k, AC.fl.flag(m, cf, fr, 2048, dat.k()), ek),
                  ((%Equal.sym(U32, D.Fd(2n, M2, fr), D.Fd(2n, m, fr), AC.fd.flag2(m, cf, fr)) : D.IsK(dk, ds, M2, im, fi, nx, ks, img, _, a); qa),
                  ((%Equal.sym(U32, D.Fd(3n, M2, fr), D.Fd(3n, m, fr), AC.fd.flag3(m, cf, fr)) : D.Frs.bK(dk, ds, M2, im, fi, nx, ks, img, _, kind, b); qb),
                    (%Equal.sym(U32, D.Fd(1n, M2, fr), D.Fd(1n, m, fr), AC.fd.flag1(m, cf, fr)) : D.FrsK(dk, ds, M2, im, fi, nx, ks, img, ps, _, rest); qr)))))))))))))))

# the defs' bodies after the flag
def defs.dat(dl: List<&2, Bk.Def>, +dk: Bool, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +cf: U32, +at: U32,
  h: D.DefsK(dl, dk, ds, m, im, fi, nx, ks, img, at), hd: @t2: Bk.Term -> D.IsK(dk, ds, m, im, fi, nx, ks, img, cf, t2) -> D.DataK(dk, 512, t2), -R: Type,
  ck: (@t2: Bk.Term -> D.IsK(dk, ds, m, im, fi, nx, ks, img, cf, t2) -> D.DataK(dk, 512, t2)) -> D.DefsK(dl, dk, ds, AC.Flag(m, cf), im, fi, nx, ks, img, at) -> R) -> R:
  match dl:
    case Nil{}:
      ck(hd, Unit{})
    case Con{Bk.Def{_, _, +v, _}, +rest}:
      (e0, r1) = h
      (ele, r2) = r1
      (+hv, r3) = r2
      isk.dat(dk, v, ds, m, im, fi, nx, ks, img, cf, at, hv, hd, R, hd1 => qv =>
        defs.dat(rest, dk, ds, m, im, fi, nx, ks, img, cf, U32.add(at, Mc.Img.size(v)), r3, hd1, R, hd2 => qr =>
          ck(hd2, (e0, (ele, (qv, qr))))))

# no cell of cs is STATIC
def TblS(cs: List<&2, Cr.Cir.Cell>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{c, rest}:
      Bool.and(Bool.not(D.FlW(Cr.Cir.Cell.get(0n, c), 1024)), TblS(rest))

def tbl.st() -> {TblS(Mc.Img.table([])) == True{} : Bool}:
  {==}

# a table cell, which is no STATIC cell, is not the STATIC cell cf
def st.ne.b(b: Bool, +m: Cr.Cir.Cells, +at: U32, +cf: U32, +c: Cr.Cir.Cell, eb: {U32.is_eq(at, cf) == b : Bool},
  hc: {Cr.Cir.Cells.get(m, at) == c : Cr.Cir.Cell}, hs: {Bool.not(D.FlW(Cr.Cir.Cell.get(0n, c), 1024)) == True{} : Bool},
  hcf: {D.Fl(m, cf, 1024) == True{} : Bool}) -> {U32.is_eq(at, cf) == False{} : Bool}:
  match b:
    case False{}:
      eb
    case True{}:
      +e = D.u32.eq(at, cf, eb)
      +h1 = {(%Equal.sym(U32, at, cf, e) : {D.Fl(m, _, 1024) == True{} : Bool}; hcf) : {D.Fl(m, at, 1024) == True{} : Bool}}
      +h2 = {(%hc : {D.FlW(Cr.Cir.Cell.get(0n, _), 1024) == True{} : Bool}; h1) : {D.FlW(Cr.Cir.Cell.get(0n, c), 1024) == True{} : Bool}}
      D.bool.ft({U32.is_eq(at, cf) == False{} : Bool}, Equal.trans(Bool, False{}, D.FlW(Cr.Cir.Cell.get(0n, c), 1024), True{},
        Equal.sym(Bool, D.FlW(Cr.Cir.Cell.get(0n, c), 1024), False{}, D.not.t(D.FlW(Cr.Cir.Cell.get(0n, c), 1024), hs)), h2))

# a table cell is not cf: cf is the machine's own (past the table) or STATIC
def tbl.ne(+m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +cf: U32, +at: U32, +c: Cr.Cir.Cell,
  +hco: {Bool.or(D.Own(fi, nx, cf), D.Fl(m, cf, 1024)) == True{} : Bool}, +e290: {U32.is_le(290, im) == True{} : Bool},
  +eim: {U32.is_lt(im, fi) == True{} : Bool}, +hb: {U32.is_le(at, 290) == True{} : Bool}, +hc: {Cr.Cir.Cells.get(m, at) == c : Cr.Cir.Cell},
  +hs: {Bool.not(D.FlW(Cr.Cir.Cell.get(0n, c), 1024)) == True{} : Bool}) -> {U32.is_eq(at, cf) == False{} : Bool}:
  D.or.cases(D.Own(fi, nx, cf), D.Fl(m, cf, 1024), {U32.is_eq(at, cf) == False{} : Bool}, hco,
    e => D.lit.ne(U32.is_eq(at, cf), at, cf, 290, {==}, hb,
      N.le_trans(1n+U32.to_nat(290), 1n+U32.to_nat(im), U32.to_nat(cf), D.u.le(290, im, e290),
        N.le_trans(1n+U32.to_nat(im), U32.to_nat(fi), U32.to_nat(cf), D.u.lt(im, fi, eim), D.u.le(fi, cf, D.and.l(U32.is_le(fi, cf), U32.is_lt(cf, nx), e))))),
    e => st.ne.b(U32.is_eq(at, cf), m, at, cf, c, {==}, hc, hs, e))

# the table after the flag
def tbl.dat(cs: List<&2, Cr.Cir.Cell>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +cf: U32, +at: U32,
  +hco: {Bool.or(D.Own(fi, nx, cf), D.Fl(m, cf, 1024)) == True{} : Bool}, +e290: {U32.is_le(290, im) == True{} : Bool},
  +eim: {U32.is_lt(im, fi) == True{} : Bool}, hb: {D.TblB(cs, at) == True{} : Bool}, hs: {TblS(cs) == True{} : Bool},
  h: D.Tbl.go(cs, m, im, fi, nx, at)) -> D.Tbl.go(cs, AC.Flag(m, cf), im, fi, nx, at):
  match cs:
    case Nil{}:
      Unit{}
    case Con{+c, +rest}:
      (ec, r1) = h
      (+e, r2) = r1
      +hb2 = hb
      +hs2 = hs
      +ne = tbl.ne(m, im, fi, nx, cf, at, c, hco, e290, eim, D.and.l(U32.is_le(at, 290), D.TblB(rest, U32.inc(at)), hb2), e,
        D.and.l(Bool.not(D.FlW(Cr.Cir.Cell.get(0n, c), 1024)), TblS(rest), hs2))
      (ec, (Equal.trans(Cr.Cir.Cell, Cr.Cir.Cells.get(AC.Flag(m, cf), at), Cr.Cir.Cells.get(m, at), c,
          D.cl.go(m, at, cf, Cr.Cir.Cell.set(0n, Cr.Cir.Cells.get(m, cf), U32.or(D.Fd(0n, m, cf), 512)), ne), e),
        tbl.dat(rest, m, im, fi, nx, cf, U32.inc(at), hco, e290, eim, D.and.r(U32.is_le(at, 290), D.TblB(rest, U32.inc(at)), hb2),
          D.and.r(Bool.not(D.FlW(Cr.Cir.Cell.get(0n, c), 1024)), TblS(rest), hs2), r2)))

# the image after the flag
def img.dat(+dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells,
  +im: U32, +fi: U32, +nx: U32, +cf: U32, +hco: {Bool.or(D.Own(fi, nx, cf), D.Fl(m, cf, 1024)) == True{} : Bool},
  h: D.ImgOKK(dk, ds, ks, img, m, im, fi, nx), hd: @t2: Bk.Term -> D.IsK(dk, ds, m, im, fi, nx, ks, img, cf, t2) -> D.DataK(dk, 512, t2), -R: Type,
  ck: (@t2: Bk.Term -> D.IsK(dk, ds, m, im, fi, nx, ks, img, cf, t2) -> D.DataK(dk, 512, t2)) -> D.ImgOKK(dk, ds, ks, img, AC.Flag(m, cf), im, fi, nx) -> R) -> R:
  (tbl, r1) = h
  (hdf, r2) = r1
  (+h8, r3) = r2
  (+h9, r4) = r3
  (+h10, r5) = r4
  (hks, r6) = r5
  (e290a, eima) = r6
  +e290 = {e290a : {U32.is_le(290, im) == True{} : Bool}}
  +eim = {eima : {U32.is_lt(im, fi) == True{} : Bool}}
  defs.dat(ds, dk, ds, m, im, fi, nx, ks, img, cf, Mc.I.book(), hdf, hd, R, hd1 => qd =>
    isk.dat(dk, Bk.Term.Lab{El.Quan.name(Bk.Quan.Q0{})}, ds, m, im, fi, nx, ks, img, cf, 8, h8, hd1, R, hd2 => q8 =>
      isk.dat(dk, Bk.Term.Lab{El.Quan.name(Bk.Quan.Q1{})}, ds, m, im, fi, nx, ks, img, cf, 9, h9, hd2, R, hd3 => q9 =>
        isk.dat(dk, Bk.Term.Lab{El.Quan.name(Bk.Quan.Q2{})}, ds, m, im, fi, nx, ks, img, cf, 10, h10, hd3, R, hd4 => q10 =>
          ck(hd4, (tbl.dat(Mc.Img.table([]), m, im, fi, nx, cf, 272, hco, e290, eim, {==}, tbl.st(), tbl),
            (qd, (q8, (q9, (q10, (hks, (e290, eim))))))))))))

# the borrowed terms after the flag
def held.dat(bs: List<&2, D.Rt>, +os: List<&2, D.Rt>, +m: Cr.Cir.Cells, +cf: U32, h: D.Held(m, os, bs)) -> D.Held(AC.Flag(m, cf), os, bs):
  match bs:
    case Nil{}:
      Unit{}
    case Con{D.Rt{+c, _}, +rest}:
      match h:
        case Tuple{hh, hr}:
          ((%Equal.sym(Bool, D.Fl(AC.Flag(m, cf), c, 1024), D.Fl(m, c, 1024), AC.fl.flag(m, cf, c, 1024, AC.and.dat.st())) :
              {Bool.or(_, D.Nodes(os, AC.Flag(m, cf), c)) == True{} : Bool};
            (%Equal.sym(Bool, D.Nodes(os, AC.Flag(m, cf), c), D.Nodes(os, m, c), AC.nodes.flag(os, m, cf, c)) : {Bool.or(D.Fl(m, c, 1024), _) == True{} : Bool}; hh)),
            held.dat(rest, os, m, cf, hr))

# the pend list's links after the flag
def chain.dat(qs: List<&2, U32>, +m: Cr.Cir.Cells, +cf: U32, +p: U32, h: D.Chain(qs, m, p)) -> D.Chain(qs, AC.Flag(m, cf), p):
  match qs:
    case Nil{}:
      h
    case Con{+x, +rest}:
      match h:
        case Tuple{e1, Tuple{e2, r2}}:
          (e1, (e2, (%Equal.sym(U32, D.Fd(1n, AC.Flag(m, cf), x), D.Fd(1n, m, x), AC.fd.flag1(m, cf, x)) : D.Chain(rest, AC.Flag(m, cf), _);
            chain.dat(rest, m, cf, D.Fd(1n, m, x), r2))))

# the pointers after the flag
def pc.flag(n: Nat, +m: Cr.Cir.Cells, +cf: U32, +ps: List<&2, U32>, +o: U32, +c: U32) -> {D.Pc(n, AC.Flag(m, cf), ps, o, c) == D.Pc(n, m, ps, o, c) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+(+k):
      %Equal.sym(List<&2, U32>, D.Fs(AC.Flag(m, cf), ps, o), D.Fs(m, ps, o), AC.fs.flag(m, cf, ps, o)) :
        {Nat.add(D.RcL(_, c), D.Pc(k, AC.Flag(m, cf), ps, U32.inc(o), c)) == Nat.add(D.RcL(D.Fs(m, ps, o), c), D.Pc(k, m, ps, U32.inc(o), c)) : Nat}
      %Equal.sym(Nat, D.Pc(k, AC.Flag(m, cf), ps, U32.inc(o), c), D.Pc(k, m, ps, U32.inc(o), c), pc.flag(k, m, cf, ps, U32.inc(o), c)) :
        {Nat.add(D.RcL(D.Fs(m, ps, o), c), _) == Nat.add(D.RcL(D.Fs(m, ps, o), c), D.Pc(k, m, ps, U32.inc(o), c)) : Nat}
      {==}

def ptr.flag(+n: Nat, +m: Cr.Cir.Cells, +cf: U32, +fi: U32, +ps: List<&2, U32>, +rs: List<&2, U32>, +c: U32) ->
  {D.Ptr(n, AC.Flag(m, cf), fi, ps, rs, c) == D.Ptr(n, m, fi, ps, rs, c) : Nat}:
  Equal.cong(Nat, Nat, w => Nat.add(w, D.RcL(rs, c)), D.Pc(n, AC.Flag(m, cf), ps, fi, c), D.Pc(n, m, ps, fi, c), pc.flag(n, m, cf, ps, fi, c))

def pendok.dat(qs: List<&2, U32>, +ps: List<&2, U32>, +m: Cr.Cir.Cells, +cf: U32, +fi: U32, +nx: U32, +rs: List<&2, U32>,
  h: D.PendOK(qs, ps, m, fi, nx, rs)) -> D.PendOK(qs, ps, AC.Flag(m, cf), fi, nx, rs):
  match qs:
    case Nil{}:
      Unit{}
    case Con{+p, +rest}:
      (ho, r1) = h
      (hs, r2) = r1
      (htg, r3) = r2
      (hp0, r4) = r3
      +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
      (ho, (Equal.trans(Bool, D.Fl(AC.Flag(m, cf), p, 1024), D.Fl(m, p, 1024), False{}, AC.fl.flag(m, cf, p, 1024, AC.and.dat.st()), hs),
        ((%Equal.sym(U32, D.Tg(AC.Flag(m, cf), p), D.Tg(m, p), AC.tg.flag(m, cf, p)) : {Bool.or(U32.is_lt(_, 19), U32.is_le(32, _)) == True{} : Bool}; htg),
        (Equal.trans(Nat, D.Ptr(n, AC.Flag(m, cf), fi, ps, rs, p), D.Ptr(n, m, fi, ps, rs, p), 0n, ptr.flag(n, m, cf, fi, ps, rs, p), hp0),
          pendok.dat(rest, ps, m, cf, fi, nx, rs, r4)))))

# the count condition at o after the flag (with its pointers P)
def cntc.dat(+m: Cr.Cir.Cells, +cf: U32, +ps: List<&2, U32>, +o: U32, +P: Nat,
  h: {D.CntC(Cr.Cir.Cells.get(m, o), P, ps, o) == True{} : Bool}) -> {D.CntC(Cr.Cir.Cells.get(AC.Flag(m, cf), o), P, ps, o) == True{} : Bool}:
  %Equal.sym(U32, D.Tg(AC.Flag(m, cf), o), D.Tg(m, o), AC.tg.flag(m, cf, o)) :
    {Bool.or(Bool.not(U32.is_lt(_, 19)), Bool.or(D.Fl(AC.Flag(m, cf), o, 1024), Bool.or(D.Mem(ps, o), Nat.is_eq(U32.to_nat(D.Fd(1n, AC.Flag(m, cf), o)), P)))) == True{} : Bool}
  %Equal.sym(Bool, D.Fl(AC.Flag(m, cf), o, 1024), D.Fl(m, o, 1024), AC.fl.flag(m, cf, o, 1024, AC.and.dat.st())) :
    {Bool.or(Bool.not(U32.is_lt(D.Tg(m, o), 19)), Bool.or(_, Bool.or(D.Mem(ps, o), Nat.is_eq(U32.to_nat(D.Fd(1n, AC.Flag(m, cf), o)), P)))) == True{} : Bool}
  %Equal.sym(U32, D.Fd(1n, AC.Flag(m, cf), o), D.Fd(1n, m, o), AC.fd.flag1(m, cf, o)) :
    {Bool.or(Bool.not(U32.is_lt(D.Tg(m, o), 19)), Bool.or(D.Fl(m, o, 1024), Bool.or(D.Mem(ps, o), Nat.is_eq(U32.to_nat(_), P)))) == True{} : Bool}
  h

def cnt.dat(k: Nat, +m: Cr.Cir.Cells, +cf: U32, +o: U32, +N: Nat, +fi: U32, +ps: List<&2, U32>, +rs: List<&2, U32>,
  h: {D.Cnt(k, m, o, N, fi, ps, rs) == True{} : Bool}) -> {D.Cnt(k, AC.Flag(m, cf), o, N, fi, ps, rs) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+(+j):
      +h2 = h
      D.and.i(D.CntC(Cr.Cir.Cells.get(AC.Flag(m, cf), o), D.Ptr(N, AC.Flag(m, cf), fi, ps, rs, o), ps, o), D.Cnt(j, AC.Flag(m, cf), U32.inc(o), N, fi, ps, rs),
        (%Equal.sym(Nat, D.Ptr(N, AC.Flag(m, cf), fi, ps, rs, o), D.Ptr(N, m, fi, ps, rs, o), ptr.flag(N, m, cf, fi, ps, rs, o)) :
            {D.CntC(Cr.Cir.Cells.get(AC.Flag(m, cf), o), _, ps, o) == True{} : Bool};
          cntc.dat(m, cf, ps, o, D.Ptr(N, m, fi, ps, rs, o),
            D.and.l(D.CntC(Cr.Cir.Cells.get(m, o), D.Ptr(N, m, fi, ps, rs, o), ps, o), D.Cnt(j, m, U32.inc(o), N, fi, ps, rs), h2))),
        cnt.dat(j, m, cf, U32.inc(o), N, fi, ps, rs,
          D.and.r(D.CntC(Cr.Cir.Cells.get(m, o), D.Ptr(N, m, fi, ps, rs, o), ps, o), D.Cnt(j, m, U32.inc(o), N, fi, ps, rs), h2)))

# the pointers' targets after the flag: their tags and STATIC stay
def lt.all.dat(xs: List<&2, U32>, +m: Cr.Cir.Cells, +cf: U32, +im: U32, +fi: U32, +nx: U32,
  h: {D.Lt.all(xs, m, im, fi, nx) == True{} : Bool}) -> {D.Lt.all(xs, AC.Flag(m, cf), im, fi, nx) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      +h2 = h
      D.and.i(D.LtC(y, Cr.Cir.Cells.get(AC.Flag(m, cf), y), im, fi, nx), D.Lt.all(rest, AC.Flag(m, cf), im, fi, nx),
        (%Equal.sym(U32, D.Tg(AC.Flag(m, cf), y), D.Tg(m, y), AC.tg.flag(m, cf, y)) :
            {Bool.and(Bool.and(U32.is_lt(y, nx), U32.is_lt(_, 19)), Bool.and(Cr.Cir.is_cell(y, im, fi, nx), Bool.or(D.Own(fi, nx, y), D.Fl(AC.Flag(m, cf), y, 1024)))) == True{} : Bool};
          (%Equal.sym(Bool, D.Fl(AC.Flag(m, cf), y, 1024), D.Fl(m, y, 1024), AC.fl.flag(m, cf, y, 1024, AC.and.dat.st())) :
              {Bool.and(Bool.and(U32.is_lt(y, nx), U32.is_lt(D.Tg(m, y), 19)), Bool.and(Cr.Cir.is_cell(y, im, fi, nx), Bool.or(D.Own(fi, nx, y), _))) == True{} : Bool};
            D.and.l(D.LtC(y, Cr.Cir.Cells.get(m, y), im, fi, nx), D.Lt.all(rest, m, im, fi, nx), h2))),
        lt.all.dat(rest, m, cf, im, fi, nx, D.and.r(D.LtC(y, Cr.Cir.Cells.get(m, y), im, fi, nx), D.Lt.all(rest, m, im, fi, nx), h2)))

def pts.dat(n: Nat, +m: Cr.Cir.Cells, +cf: U32, +ps: List<&2, U32>, +o: U32, +im: U32, +fi: U32, +nx: U32,
  h: {D.Pts(n, m, ps, o, im, fi, nx) == True{} : Bool}) -> {D.Pts(n, AC.Flag(m, cf), ps, o, im, fi, nx) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+(+k):
      +h2 = h
      D.and.i(D.Lt.all(D.Fs(AC.Flag(m, cf), ps, o), AC.Flag(m, cf), im, fi, nx), D.Pts(k, AC.Flag(m, cf), ps, U32.inc(o), im, fi, nx),
        (%Equal.sym(List<&2, U32>, D.Fs(AC.Flag(m, cf), ps, o), D.Fs(m, ps, o), AC.fs.flag(m, cf, ps, o)) : {D.Lt.all(_, AC.Flag(m, cf), im, fi, nx) == True{} : Bool};
          lt.all.dat(D.Fs(m, ps, o), m, cf, im, fi, nx, D.and.l(D.Lt.all(D.Fs(m, ps, o), m, im, fi, nx), D.Pts(k, m, ps, U32.inc(o), im, fi, nx), h2))),
        pts.dat(k, m, cf, ps, U32.inc(o), im, fi, nx, D.and.r(D.Lt.all(D.Fs(m, ps, o), m, im, fi, nx), D.Pts(k, m, ps, U32.inc(o), im, fi, nx), h2)))

# the heap after the flag
def heap.dat(+m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +rs: List<&2, U32>, +pend: U32, +ps: List<&2, U32>, +cf: U32,
  h: D.Heap(m, nx, fi, im, rs, pend, ps)) -> D.Heap(AC.Flag(m, cf), nx, fi, im, rs, pend, ps):
  match h:
    case Tuple{hch, Tuple{hpk, Tuple{hcnt, Tuple{hpts, hr}}}}:
      +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
      (chain.dat(ps, m, cf, pend, hch), (pendok.dat(ps, ps, m, cf, fi, nx, rs, hpk),
        (cnt.dat(n, m, cf, fi, n, fi, ps, rs, hcnt), (pts.dat(n, m, cf, ps, fi, im, fi, nx, hpts), hr))))

# the flag as the law writes it
def flag.eq(+m: Cr.Cir.Cells, +c: U32) ->
  {AC.Flag(m, c) == Cr.Cir.Cells.set(m, c, Cr.Cir.Cell.set(0n, Cr.Cir.Cells.get(m, c), U32.or(D.Fd(0n, m, c), 512))) : Cr.Cir.Cells}:
  {==}

# what data.flag says
def DfR(+dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32,
  +ps: List<&2, U32>, +c: U32, +xs: List<&2, D.TmpE>, +zs: List<&2, D.Rt>) -> Data:
  D.P2(D.HSK(dk, ds, ks, img, Cr.Cir.Cells.set(m, c, Cr.Cir.Cell.set(0n, Cr.Cir.Cells.get(m, c), U32.or(D.Fd(0n, m, c), 512))), nx, fi, im,
    os, bs, fs, sp, pend, ps),
    D.AccK(dk, ds, ks, img, Cr.Cir.Cells.set(m, c, Cr.Cir.Cell.set(0n, Cr.Cir.Cells.get(m, c), U32.or(D.Fd(0n, m, c), 512))), nx, fi, im,
      os, xs, sp, fs, ps, zs))

# data.flag: every term, frame, the heap and the image after the flag, hd
# threaded through them; Acc by U1's acc.flag
def df.top(+dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32,
  +ps: List<&2, U32>, +c: U32, +xs: List<&2, D.TmpE>, +zs: List<&2, D.Rt>,
  hs: D.HSK(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps), +hac: D.AccK(dk, ds, ks, img, m, nx, fi, im, os, xs, sp, fs, ps, zs),
  hd: @t2: Bk.Term -> D.IsK(dk, ds, m, im, fi, nx, ks, img, c, t2) -> D.DataK(dk, 512, t2),
  +hco: {Bool.or(D.Own(fi, nx, c), D.Fl(m, c, 1024)) == True{} : Bool}) ->
  DfR(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps, c, xs, zs):
  match hs:
    case Tuple{hos, Tuple{hbs, Tuple{hh, Tuple{hfrs, Tuple{hheap, himg}}}}}:
      (+hz0, r1) = hac
      (+hh0, _) = r1
      rtsk.dat(dk, os, ds, m, im, fi, nx, ks, img, c, hos, hd, DfR(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps, c, xs, zs), hd1 => qos =>
        rtsk.dat(dk, bs, ds, m, im, fi, nx, ks, img, c, hbs, hd1, DfR(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps, c, xs, zs), hd2 => qbs =>
          frsk.dat(dk, fs, ds, m, im, fi, nx, ks, img, ps, c, sp, hfrs, hd2, DfR(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps, c, xs, zs), hd3 => qfs =>
            img.dat(dk, ds, ks, img, m, im, fi, nx, c, hco, himg, hd3, DfR(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps, c, xs, zs), hd4 => qim =>
              rtsk.dat(dk, zs, ds, m, im, fi, nx, ks, img, c, hz0, hd4, DfR(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps, c, xs, zs), hd5 => qzs =>
                rtsk.dat(dk, D.Tmp.held(xs), ds, m, im, fi, nx, ks, img, c, hh0, hd5, DfR(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps, c, xs, zs), hd6 => qhl =>
                  ((%flag.eq(m, c) : D.HSK(dk, ds, ks, img, _, nx, fi, im, os, bs, fs, sp, pend, ps);
                      (qos, (qbs, (held.dat(bs, os, m, c, hh), (qfs, (heap.dat(m, nx, fi, im, D.Rt.cells(os), pend, ps, c, hheap), qim)))))),
                    AC.acc.flag(dk, ds, ks, img, m, nx, fi, im, os, xs, sp, fs, ps, zs, c, hac,
                      (%flag.eq(m, c) : D.RtsK(dk, ds, _, im, fi, nx, ks, img, zs); qzs),
                      (%flag.eq(m, c) : D.RtsK(dk, ds, _, im, fi, nx, ks, img, D.Tmp.held(xs)); qhl)))))))))


# A new cell at next
# ------------------
#
# M.alloc with an empty pend list takes the new cell nx (Cir's alloc), all
# zeros, at next nx + 1: the n cells from fi, then nx. The new cell is a term
# cell (tag 0) with no pointer and count 0, and nothing points to it.

# the pointers of the n cells from c and of the new cell z after them, which holds none
def pc.fresh(n: Nat, +m: Cr.Cir.Cells, +c: U32, +z: U32, +x: Cr.Cir.Cell, +ps: List<&2, U32>, +y: U32,
  hz: {Nat.add(U32.to_nat(c), n) == U32.to_nat(z) : Nat}, +hf1: {D.Fs(Cr.Cir.Cells.set(m, z, x), ps, z) == Nil{} : List<&2, U32>},
  ht: {D.TblR(n, m, c, z) == True{} : Bool}) ->
  {D.Pc(1n+n, Cr.Cir.Cells.set(m, z, x), ps, c, y) == D.Pc(n, m, ps, c, y) : Nat}:
  match n:
    case 0n:
      +M2 = Cr.Cir.Cells.set(m, z, x)
      %Equal.sym(U32, c, z, AC.at.end(c, z, hz)) : {Nat.add(D.RcL(D.Fs(M2, ps, _), y), 0n) == 0n : Nat}
      %Equal.sym(List<&2, U32>, D.Fs(M2, ps, z), Nil{}, hf1) : {Nat.add(D.RcL(_, y), 0n) == 0n : Nat}
      {==}
    case 1n+(+k):
      +M2 = Cr.Cir.Cells.set(m, z, x)
      +hz2 = hz
      +ht2 = ht
      +ne = AC.ne.lt(c, z, AC.at.lt(c, k, z, hz2))
      +e1 = D.fs.eq(m, z, x, ps, c, ne, D.and.l(D.TblAt(m, c, z), D.TblR(k, m, U32.inc(c), z), ht2))
      +e2 = pc.fresh(k, m, U32.inc(c), z, x, ps, y, AC.at.next(c, k, z, hz2), hf1, D.and.r(D.TblAt(m, c, z), D.TblR(k, m, U32.inc(c), z), ht2))
      %Equal.sym(List<&2, U32>, D.Fs(M2, ps, c), D.Fs(m, ps, c), e1) :
        {Nat.add(D.RcL(_, y), D.Pc(1n+k, M2, ps, U32.inc(c), y)) == Nat.add(D.RcL(D.Fs(m, ps, c), y), D.Pc(k, m, ps, U32.inc(c), y)) : Nat}
      %Equal.sym(Nat, D.Pc(1n+k, M2, ps, U32.inc(c), y), D.Pc(k, m, ps, U32.inc(c), y), e2) :
        {Nat.add(D.RcL(D.Fs(m, ps, c), y), _) == Nat.add(D.RcL(D.Fs(m, ps, c), y), D.Pc(k, m, ps, U32.inc(c), y)) : Nat}
      {==}

def ptr.fresh(+n: Nat, +m: Cr.Cir.Cells, +fi: U32, +z: U32, +x: Cr.Cir.Cell, +ps: List<&2, U32>, +rs: List<&2, U32>, +y: U32,
  hz: {Nat.add(U32.to_nat(fi), n) == U32.to_nat(z) : Nat}, hf1: {D.Fs(Cr.Cir.Cells.set(m, z, x), ps, z) == Nil{} : List<&2, U32>},
  ht: {D.TblR(n, m, fi, z) == True{} : Bool}) ->
  {D.Ptr(1n+n, Cr.Cir.Cells.set(m, z, x), fi, ps, rs, y) == D.Ptr(n, m, fi, ps, rs, y) : Nat}:
  Equal.cong(Nat, Nat, w => Nat.add(w, D.RcL(rs, y)), D.Pc(1n+n, Cr.Cir.Cells.set(m, z, x), ps, fi, y), D.Pc(n, m, ps, fi, y),
    pc.fresh(n, m, fi, z, x, ps, y, hz, hf1, ht))

# the count conditions of the n cells from c, and of the new cell z after them
def cnt.fresh(k: Nat, +m: Cr.Cir.Cells, +c: U32, +z: U32, +x: Cr.Cir.Cell, +N: Nat, +fi: U32, +ps: List<&2, U32>, +rs: List<&2, U32>,
  +hz: {Nat.add(U32.to_nat(c), k) == U32.to_nat(z) : Nat}, +hzN: {Nat.add(U32.to_nat(fi), N) == U32.to_nat(z) : Nat},
  +hf1: {D.Fs(Cr.Cir.Cells.set(m, z, x), ps, z) == Nil{} : List<&2, U32>}, +htN: {D.TblR(N, m, fi, z) == True{} : Bool},
  +hxc: {D.CntC(x, D.Ptr(1n+N, Cr.Cir.Cells.set(m, z, x), fi, ps, rs, z), ps, z) == True{} : Bool},
  h: {D.Cnt(k, m, c, N, fi, ps, rs) == True{} : Bool}) -> {D.Cnt(1n+k, Cr.Cir.Cells.set(m, z, x), c, 1n+N, fi, ps, rs) == True{} : Bool}:
  match k:
    case 0n:
      +M2 = Cr.Cir.Cells.set(m, z, x)
      %Equal.sym(U32, c, z, AC.at.end(c, z, hz)) : {D.Cnt(1n, M2, _, 1n+N, fi, ps, rs) == True{} : Bool}
      D.and.i(D.CntC(Cr.Cir.Cells.get(M2, z), D.Ptr(1n+N, M2, fi, ps, rs, z), ps, z), True{},
        (%Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, z), x, D.cl.gs(m, z, x)) : {D.CntC(_, D.Ptr(1n+N, M2, fi, ps, rs, z), ps, z) == True{} : Bool}; hxc),
        {==})
    case 1n+(+j):
      +M2 = Cr.Cir.Cells.set(m, z, x)
      +hz2 = hz
      +h2 = h
      +ne = AC.ne.lt(c, z, AC.at.lt(c, j, z, hz2))
      D.and.i(D.CntC(Cr.Cir.Cells.get(M2, c), D.Ptr(1n+N, M2, fi, ps, rs, c), ps, c), D.Cnt(1n+j, M2, U32.inc(c), 1n+N, fi, ps, rs),
        (%Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, c), Cr.Cir.Cells.get(m, c), D.cl.go(m, c, z, x, ne)) :
            {D.CntC(_, D.Ptr(1n+N, M2, fi, ps, rs, c), ps, c) == True{} : Bool};
          (%Equal.sym(Nat, D.Ptr(1n+N, M2, fi, ps, rs, c), D.Ptr(N, m, fi, ps, rs, c), ptr.fresh(N, m, fi, z, x, ps, rs, c, hzN, hf1, htN)) :
              {D.CntC(Cr.Cir.Cells.get(m, c), _, ps, c) == True{} : Bool};
            D.and.l(D.CntC(Cr.Cir.Cells.get(m, c), D.Ptr(N, m, fi, ps, rs, c), ps, c), D.Cnt(j, m, U32.inc(c), N, fi, ps, rs), h2))),
        cnt.fresh(j, m, U32.inc(c), z, x, N, fi, ps, rs, AC.at.next(c, j, z, hz2), hzN, hf1, htN, hxc,
          D.and.r(D.CntC(Cr.Cir.Cells.get(m, c), D.Ptr(N, m, fi, ps, rs, c), ps, c), D.Cnt(j, m, U32.inc(c), N, fi, ps, rs), h2)))

# pointers below nx, after the store at nx and with next nx + 1
def lt.all.fresh(xs: List<&2, U32>, +m: Cr.Cir.Cells, +x: Cr.Cir.Cell, +im: U32, +fi: U32, +nx: U32,
  +hnx: {U32.to_nat(U32.inc(nx)) == 1n+U32.to_nat(nx) : Nat},
  h: {D.Lt.all(xs, m, im, fi, nx) == True{} : Bool}) -> {D.Lt.all(xs, Cr.Cir.Cells.set(m, nx, x), im, fi, U32.inc(nx)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      +M2 = Cr.Cir.Cells.set(m, nx, x)
      +h2 = h
      +Y = Cr.Cir.Cells.get(m, y)
      +f0 = Cr.Cir.Cell.get(0n, Y)
      +lc = D.and.l(D.LtC(y, Y, im, fi, nx), D.Lt.all(rest, m, im, fi, nx), h2)
      +la = D.and.l(Bool.and(U32.is_lt(y, nx), U32.is_lt(D.TgW(f0), 19)), Bool.and(Cr.Cir.is_cell(y, im, fi, nx), Bool.or(D.Own(fi, nx, y), D.FlW(f0, 1024))), lc)
      +lb = D.and.r(Bool.and(U32.is_lt(y, nx), U32.is_lt(D.TgW(f0), 19)), Bool.and(Cr.Cir.is_cell(y, im, fi, nx), Bool.or(D.Own(fi, nx, y), D.FlW(f0, 1024))), lc)
      +hy = D.and.l(U32.is_lt(y, nx), U32.is_lt(D.TgW(f0), 19), la)
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, y), Y, D.cl.go(m, y, nx, x, lt.ne.u(y, nx, hy))) :
        {Bool.and(D.LtC(y, _, im, fi, U32.inc(nx)), D.Lt.all(rest, M2, im, fi, U32.inc(nx))) == True{} : Bool}
      D.and.i(D.LtC(y, Y, im, fi, U32.inc(nx)), D.Lt.all(rest, M2, im, fi, U32.inc(nx)),
        D.and.i(Bool.and(U32.is_lt(y, U32.inc(nx)), U32.is_lt(D.TgW(f0), 19)), Bool.and(Cr.Cir.is_cell(y, im, fi, U32.inc(nx)), Bool.or(D.Own(fi, U32.inc(nx), y), D.FlW(f0, 1024))),
          D.and.i(U32.is_lt(y, U32.inc(nx)), U32.is_lt(D.TgW(f0), 19), lt.fr(y, nx, hnx, hy), D.and.r(U32.is_lt(y, nx), U32.is_lt(D.TgW(f0), 19), la)),
          D.and.i(Cr.Cir.is_cell(y, im, fi, U32.inc(nx)), Bool.or(D.Own(fi, U32.inc(nx), y), D.FlW(f0, 1024)),
            cell.fr(y, im, fi, nx, hnx, D.and.l(Cr.Cir.is_cell(y, im, fi, nx), Bool.or(D.Own(fi, nx, y), D.FlW(f0, 1024)), lb)),
            or.fr(fi, nx, y, D.FlW(f0, 1024), hnx, D.and.r(Cr.Cir.is_cell(y, im, fi, nx), Bool.or(D.Own(fi, nx, y), D.FlW(f0, 1024)), lb)))),
        lt.all.fresh(rest, m, x, im, fi, nx, hnx, D.and.r(D.LtC(y, Y, im, fi, nx), D.Lt.all(rest, m, im, fi, nx), h2)))

# the pointers' targets of the n cells from c, and of the new cell z (none)
def pts.fresh(k: Nat, +m: Cr.Cir.Cells, +c: U32, +z: U32, +x: Cr.Cir.Cell, +ps: List<&2, U32>, +im: U32, +fi: U32,
  +hnx: {U32.to_nat(U32.inc(z)) == 1n+U32.to_nat(z) : Nat}, +hz: {Nat.add(U32.to_nat(c), k) == U32.to_nat(z) : Nat},
  +hf1: {D.Fs(Cr.Cir.Cells.set(m, z, x), ps, z) == Nil{} : List<&2, U32>}, ht: {D.TblR(k, m, c, z) == True{} : Bool},
  h: {D.Pts(k, m, ps, c, im, fi, z) == True{} : Bool}) -> {D.Pts(1n+k, Cr.Cir.Cells.set(m, z, x), ps, c, im, fi, U32.inc(z)) == True{} : Bool}:
  match k:
    case 0n:
      +M2 = Cr.Cir.Cells.set(m, z, x)
      %Equal.sym(U32, c, z, AC.at.end(c, z, hz)) : {D.Pts(1n, M2, ps, _, im, fi, U32.inc(z)) == True{} : Bool}
      %Equal.sym(List<&2, U32>, D.Fs(M2, ps, z), Nil{}, hf1) : {Bool.and(D.Lt.all(_, M2, im, fi, U32.inc(z)), True{}) == True{} : Bool}
      {==}
    case 1n+(+j):
      +M2 = Cr.Cir.Cells.set(m, z, x)
      +hz2 = hz
      +ht2 = ht
      +h2 = h
      +ne = AC.ne.lt(c, z, AC.at.lt(c, j, z, hz2))
      D.and.i(D.Lt.all(D.Fs(M2, ps, c), M2, im, fi, U32.inc(z)), D.Pts(1n+j, M2, ps, U32.inc(c), im, fi, U32.inc(z)),
        (%Equal.sym(List<&2, U32>, D.Fs(M2, ps, c), D.Fs(m, ps, c), D.fs.eq(m, z, x, ps, c, ne, D.and.l(D.TblAt(m, c, z), D.TblR(j, m, U32.inc(c), z), ht2))) :
            {D.Lt.all(_, M2, im, fi, U32.inc(z)) == True{} : Bool};
          lt.all.fresh(D.Fs(m, ps, c), m, x, im, fi, z, hnx, D.and.l(D.Lt.all(D.Fs(m, ps, c), m, im, fi, z), D.Pts(j, m, ps, U32.inc(c), im, fi, z), h2))),
        pts.fresh(j, m, U32.inc(c), z, x, ps, im, fi, hnx, AC.at.next(c, j, z, hz2), hf1, D.and.r(D.TblAt(m, c, z), D.TblR(j, m, U32.inc(c), z), ht2),
          D.and.r(D.Lt.all(D.Fs(m, ps, c), m, im, fi, z), D.Pts(j, m, ps, U32.inc(c), im, fi, z), h2)))

# no pointer of a list of pointers below nx is nx
def rcl.lt.z(L: List<&2, U32>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, h: {D.Lt.all(L, m, im, fi, nx) == True{} : Bool}) ->
  {D.RcL(L, nx) == 0n : Nat}:
  match L:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      +h2 = h
      +Y = Cr.Cir.Cells.get(m, y)
      +f0 = Cr.Cir.Cell.get(0n, Y)
      +lc = D.and.l(D.LtC(y, Y, im, fi, nx), D.Lt.all(rest, m, im, fi, nx), h2)
      +hy = D.and.l(U32.is_lt(y, nx), U32.is_lt(D.TgW(f0), 19),
        D.and.l(Bool.and(U32.is_lt(y, nx), U32.is_lt(D.TgW(f0), 19)), Bool.and(Cr.Cir.is_cell(y, im, fi, nx), Bool.or(D.Own(fi, nx, y), D.FlW(f0, 1024))), lc))
      %Equal.sym(Bool, U32.is_eq(y, nx), False{}, lt.ne.u(y, nx, hy)) : {Nat.add(D.Nat.of(_), D.RcL(rest, nx)) == 0n : Nat}
      rcl.lt.z(rest, m, im, fi, nx, D.and.r(D.LtC(y, Y, im, fi, nx), D.Lt.all(rest, m, im, fi, nx), h2))

# no cell points to nx
def pc.pts.z(n: Nat, +m: Cr.Cir.Cells, +ps: List<&2, U32>, +o: U32, +im: U32, +fi: U32, +nx: U32,
  h: {D.Pts(n, m, ps, o, im, fi, nx) == True{} : Bool}) -> {D.Pc(n, m, ps, o, nx) == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+(+k):
      +h2 = h
      %Equal.sym(Nat, D.RcL(D.Fs(m, ps, o), nx), 0n,
          rcl.lt.z(D.Fs(m, ps, o), m, im, fi, nx, D.and.l(D.Lt.all(D.Fs(m, ps, o), m, im, fi, nx), D.Pts(k, m, ps, U32.inc(o), im, fi, nx), h2))) :
        {Nat.add(_, D.Pc(k, m, ps, U32.inc(o), nx)) == 0n : Nat}
      pc.pts.z(k, m, ps, U32.inc(o), im, fi, nx, D.and.r(D.Lt.all(D.Fs(m, ps, o), m, im, fi, nx), D.Pts(k, m, ps, U32.inc(o), im, fi, nx), h2))

# a cell that stands for a term is not nx
def isck.ne.k(+dk: Bool, +t: Bk.Term, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +y: U32,
  +him: {U32.is_lt(im, fi) == True{} : Bool}, +hfn: {U32.is_le(fi, nx) == True{} : Bool},
  h: D.IsK(dk, ds, m, im, fi, nx, ks, img, y, t)) -> {U32.is_eq(y, nx) == False{} : Bool}:
  ndk.ne(dk, ds, im, fi, nx, y, Cr.Cir.Cells.get(m, y), t, D.A.tag(t), him, hfn, isk.nd(dk, t, ds, m, im, fi, nx, ks, img, y, h))

# no root is nx: each is a cell below it
def rcl.roots.z(+dk: Bool, os: List<&2, D.Rt>, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +him: {U32.is_lt(im, fi) == True{} : Bool}, +hfn: {U32.is_le(fi, nx) == True{} : Bool},
  h: D.RtsK(dk, ds, m, im, fi, nx, ks, img, os)) -> {D.RcL(D.Rt.cells(os), nx) == 0n : Nat}:
  match os:
    case Nil{}:
      {==}
    case Con{D.Rt{+c, +u}, +rest}:
      match h:
        case Tuple{hu, hr}:
          %Equal.sym(Bool, U32.is_eq(c, nx), False{}, isck.ne.k(dk, u, ds, m, im, fi, nx, ks, img, c, him, hfn, hu)) :
            {Nat.add(D.Nat.of(_), D.RcL(D.Rt.cells(rest), nx)) == 0n : Nat}
          rcl.roots.z(dk, rest, ds, m, im, fi, nx, ks, img, him, hfn, hr)

# the nodes of a term (its cells, all below nx) after the store at nx
def node.fresh(+dk: Bool, t: Bk.Term, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +x: Cr.Cir.Cell, +r: U32, +c: U32,
  +him: {U32.is_lt(im, fi) == True{} : Bool}, +hfn: {U32.is_le(fi, nx) == True{} : Bool},
  +h: D.IsK(dk, ds, m, im, fi, nx, ks, img, r, t)) ->
  {D.Node(t, Cr.Cir.Cells.set(m, nx, x), r, c) == D.Node(t, m, r, c) : Bool}:
  match t:
    case Bk.Term.Var{+i}:
      {==}
    case Bk.Term.Ref{+k}:
      {==}
    case Bk.Term.Ann{+t1, +t2}:
      (+nd, r0) = h
      (p2, r1) = r0
      (sp2, h2) = p2
      (sp3, h3) = r1
      +M2 = Cr.Cir.Cells.set(m, nx, x)
      +ec = D.cl.go(m, r, nx, x, lt.ne.u(r, nx, cell.lt(r, im, fi, nx, ndk.cell(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Ann{t1, t2}, 2, nd), him, hfn)))
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, r), Cr.Cir.Cells.get(m, r), ec) :
        {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, M2, Cr.Cir.Cell.get(2n, _), c), D.Node(t2, M2, Cr.Cir.Cell.get(3n, _), c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c))) : Bool}
      %Equal.sym(Bool, D.Node(t1, M2, D.Fd(2n, m, r), c), D.Node(t1, m, D.Fd(2n, m, r), c),
          node.fresh(dk, t1, ds, m, im, fi, nx, ks, img, x, D.Fd(2n, m, r), c, him, hfn, h2)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(_, D.Node(t2, M2, D.Fd(3n, m, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c))) : Bool}
      %Equal.sym(Bool, D.Node(t2, M2, D.Fd(3n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c),
          node.fresh(dk, t2, ds, m, im, fi, nx, ks, img, x, D.Fd(3n, m, r), c, him, hfn, h3)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), _)) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c))) : Bool}
      {==}
    case Bk.Term.Let{+q, +t1, +t2}:
      (+nd, r0) = h
      (hq, r1) = r0
      (p2, r2) = r1
      (sp2, h2) = p2
      (sp3, h3) = r2
      +M2 = Cr.Cir.Cells.set(m, nx, x)
      +ec = D.cl.go(m, r, nx, x, lt.ne.u(r, nx, cell.lt(r, im, fi, nx, ndk.cell(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Let{q, t1, t2}, 3, nd), him, hfn)))
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, r), Cr.Cir.Cells.get(m, r), ec) :
        {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, M2, Cr.Cir.Cell.get(2n, _), c), D.Node(t2, M2, Cr.Cir.Cell.get(3n, _), c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c))) : Bool}
      %Equal.sym(Bool, D.Node(t1, M2, D.Fd(2n, m, r), c), D.Node(t1, m, D.Fd(2n, m, r), c),
          node.fresh(dk, t1, ds, m, im, fi, nx, ks, img, x, D.Fd(2n, m, r), c, him, hfn, h2)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(_, D.Node(t2, M2, D.Fd(3n, m, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c))) : Bool}
      %Equal.sym(Bool, D.Node(t2, M2, D.Fd(3n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c),
          node.fresh(dk, t2, ds, m, im, fi, nx, ks, img, x, D.Fd(3n, m, r), c, him, hfn, h3)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), _)) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c))) : Bool}
      {==}
    case Bk.Term.Typ{+t1}:
      (+nd, r0) = h
      (sp2, h2) = r0
      +M2 = Cr.Cir.Cells.set(m, nx, x)
      +ec = D.cl.go(m, r, nx, x, lt.ne.u(r, nx, cell.lt(r, im, fi, nx, ndk.cell(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Typ{t1}, 4, nd), him, hfn)))
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, r), Cr.Cir.Cells.get(m, r), ec) :
        {Bool.or(U32.is_eq(r, c), D.Node(t1, M2, Cr.Cir.Cell.get(2n, _), c)) == Bool.or(U32.is_eq(r, c), D.Node(t1, m, D.Fd(2n, m, r), c)) : Bool}
      %Equal.sym(Bool, D.Node(t1, M2, D.Fd(2n, m, r), c), D.Node(t1, m, D.Fd(2n, m, r), c),
          node.fresh(dk, t1, ds, m, im, fi, nx, ks, img, x, D.Fd(2n, m, r), c, him, hfn, h2)) :
        {Bool.or(U32.is_eq(r, c), _) == Bool.or(U32.is_eq(r, c), D.Node(t1, m, D.Fd(2n, m, r), c)) : Bool}
      {==}
    case Bk.Term.Min{+t1, +t2}:
      (+nd, r0) = h
      (p2, r1) = r0
      (sp2, h2) = p2
      (sp3, h3) = r1
      +M2 = Cr.Cir.Cells.set(m, nx, x)
      +ec = D.cl.go(m, r, nx, x, lt.ne.u(r, nx, cell.lt(r, im, fi, nx, ndk.cell(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Min{t1, t2}, 5, nd), him, hfn)))
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, r), Cr.Cir.Cells.get(m, r), ec) :
        {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, M2, Cr.Cir.Cell.get(2n, _), c), D.Node(t2, M2, Cr.Cir.Cell.get(3n, _), c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c))) : Bool}
      %Equal.sym(Bool, D.Node(t1, M2, D.Fd(2n, m, r), c), D.Node(t1, m, D.Fd(2n, m, r), c),
          node.fresh(dk, t1, ds, m, im, fi, nx, ks, img, x, D.Fd(2n, m, r), c, him, hfn, h2)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(_, D.Node(t2, M2, D.Fd(3n, m, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c))) : Bool}
      %Equal.sym(Bool, D.Node(t2, M2, D.Fd(3n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c),
          node.fresh(dk, t2, ds, m, im, fi, nx, ks, img, x, D.Fd(3n, m, r), c, him, hfn, h3)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), _)) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c))) : Bool}
      {==}
    case Bk.Term.All{+q, +t1, +t2}:
      (+nd, r0) = h
      (hq, r1) = r0
      (p2, r2) = r1
      (sp2, h2) = p2
      (sp3, h3) = r2
      +M2 = Cr.Cir.Cells.set(m, nx, x)
      +ec = D.cl.go(m, r, nx, x, lt.ne.u(r, nx, cell.lt(r, im, fi, nx, ndk.cell(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.All{q, t1, t2}, 6, nd), him, hfn)))
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, r), Cr.Cir.Cells.get(m, r), ec) :
        {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, M2, Cr.Cir.Cell.get(2n, _), c), D.Node(t2, M2, Cr.Cir.Cell.get(3n, _), c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c))) : Bool}
      %Equal.sym(Bool, D.Node(t1, M2, D.Fd(2n, m, r), c), D.Node(t1, m, D.Fd(2n, m, r), c),
          node.fresh(dk, t1, ds, m, im, fi, nx, ks, img, x, D.Fd(2n, m, r), c, him, hfn, h2)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(_, D.Node(t2, M2, D.Fd(3n, m, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c))) : Bool}
      %Equal.sym(Bool, D.Node(t2, M2, D.Fd(3n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c),
          node.fresh(dk, t2, ds, m, im, fi, nx, ks, img, x, D.Fd(3n, m, r), c, him, hfn, h3)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), _)) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c))) : Bool}
      {==}
    case Bk.Term.Lam{+q, +t1}:
      (+nd, r0) = h
      (hq, r1) = r0
      (sp2, h2) = r1
      +M2 = Cr.Cir.Cells.set(m, nx, x)
      +ec = D.cl.go(m, r, nx, x, lt.ne.u(r, nx, cell.lt(r, im, fi, nx, ndk.cell(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Lam{q, t1}, 7, nd), him, hfn)))
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, r), Cr.Cir.Cells.get(m, r), ec) :
        {Bool.or(U32.is_eq(r, c), D.Node(t1, M2, Cr.Cir.Cell.get(2n, _), c)) == Bool.or(U32.is_eq(r, c), D.Node(t1, m, D.Fd(2n, m, r), c)) : Bool}
      %Equal.sym(Bool, D.Node(t1, M2, D.Fd(2n, m, r), c), D.Node(t1, m, D.Fd(2n, m, r), c),
          node.fresh(dk, t1, ds, m, im, fi, nx, ks, img, x, D.Fd(2n, m, r), c, him, hfn, h2)) :
        {Bool.or(U32.is_eq(r, c), _) == Bool.or(U32.is_eq(r, c), D.Node(t1, m, D.Fd(2n, m, r), c)) : Bool}
      {==}
    case Bk.Term.App{+q, +t1, +t2}:
      (+nd, r0) = h
      (hq, r1) = r0
      (p2, r2) = r1
      (sp2, h2) = p2
      (sp3, h3) = r2
      +M2 = Cr.Cir.Cells.set(m, nx, x)
      +ec = D.cl.go(m, r, nx, x, lt.ne.u(r, nx, cell.lt(r, im, fi, nx, ndk.cell(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.App{q, t1, t2}, 8, nd), him, hfn)))
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, r), Cr.Cir.Cells.get(m, r), ec) :
        {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, M2, Cr.Cir.Cell.get(2n, _), c), D.Node(t2, M2, Cr.Cir.Cell.get(3n, _), c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c))) : Bool}
      %Equal.sym(Bool, D.Node(t1, M2, D.Fd(2n, m, r), c), D.Node(t1, m, D.Fd(2n, m, r), c),
          node.fresh(dk, t1, ds, m, im, fi, nx, ks, img, x, D.Fd(2n, m, r), c, him, hfn, h2)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(_, D.Node(t2, M2, D.Fd(3n, m, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c))) : Bool}
      %Equal.sym(Bool, D.Node(t2, M2, D.Fd(3n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c),
          node.fresh(dk, t2, ds, m, im, fi, nx, ks, img, x, D.Fd(3n, m, r), c, him, hfn, h3)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), _)) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c))) : Bool}
      {==}
    case Bk.Term.Sig{+q, +t1, +t2}:
      (+nd, r0) = h
      (hq, r1) = r0
      (p2, r2) = r1
      (sp2, h2) = p2
      (sp3, h3) = r2
      +M2 = Cr.Cir.Cells.set(m, nx, x)
      +ec = D.cl.go(m, r, nx, x, lt.ne.u(r, nx, cell.lt(r, im, fi, nx, ndk.cell(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Sig{q, t1, t2}, 9, nd), him, hfn)))
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, r), Cr.Cir.Cells.get(m, r), ec) :
        {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, M2, Cr.Cir.Cell.get(2n, _), c), D.Node(t2, M2, Cr.Cir.Cell.get(3n, _), c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c))) : Bool}
      %Equal.sym(Bool, D.Node(t1, M2, D.Fd(2n, m, r), c), D.Node(t1, m, D.Fd(2n, m, r), c),
          node.fresh(dk, t1, ds, m, im, fi, nx, ks, img, x, D.Fd(2n, m, r), c, him, hfn, h2)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(_, D.Node(t2, M2, D.Fd(3n, m, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c))) : Bool}
      %Equal.sym(Bool, D.Node(t2, M2, D.Fd(3n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c),
          node.fresh(dk, t2, ds, m, im, fi, nx, ks, img, x, D.Fd(3n, m, r), c, him, hfn, h3)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), _)) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c))) : Bool}
      {==}
    case Bk.Term.Tup{+q, +t1, +t2}:
      (+nd, r0) = h
      (hq, r1) = r0
      (p2, r2) = r1
      (sp2, h2) = p2
      (sp3, h3) = r2
      +M2 = Cr.Cir.Cells.set(m, nx, x)
      +ec = D.cl.go(m, r, nx, x, lt.ne.u(r, nx, cell.lt(r, im, fi, nx, ndk.cell(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Tup{q, t1, t2}, 10, nd), him, hfn)))
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, r), Cr.Cir.Cells.get(m, r), ec) :
        {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, M2, Cr.Cir.Cell.get(2n, _), c), D.Node(t2, M2, Cr.Cir.Cell.get(3n, _), c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c))) : Bool}
      %Equal.sym(Bool, D.Node(t1, M2, D.Fd(2n, m, r), c), D.Node(t1, m, D.Fd(2n, m, r), c),
          node.fresh(dk, t1, ds, m, im, fi, nx, ks, img, x, D.Fd(2n, m, r), c, him, hfn, h2)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(_, D.Node(t2, M2, D.Fd(3n, m, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c))) : Bool}
      %Equal.sym(Bool, D.Node(t2, M2, D.Fd(3n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c),
          node.fresh(dk, t2, ds, m, im, fi, nx, ks, img, x, D.Fd(3n, m, r), c, him, hfn, h3)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), _)) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c))) : Bool}
      {==}
    case Bk.Term.Prj{+t1}:
      (+nd, r0) = h
      (sp2, h2) = r0
      +M2 = Cr.Cir.Cells.set(m, nx, x)
      +ec = D.cl.go(m, r, nx, x, lt.ne.u(r, nx, cell.lt(r, im, fi, nx, ndk.cell(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Prj{t1}, 11, nd), him, hfn)))
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, r), Cr.Cir.Cells.get(m, r), ec) :
        {Bool.or(U32.is_eq(r, c), D.Node(t1, M2, Cr.Cir.Cell.get(2n, _), c)) == Bool.or(U32.is_eq(r, c), D.Node(t1, m, D.Fd(2n, m, r), c)) : Bool}
      %Equal.sym(Bool, D.Node(t1, M2, D.Fd(2n, m, r), c), D.Node(t1, m, D.Fd(2n, m, r), c),
          node.fresh(dk, t1, ds, m, im, fi, nx, ks, img, x, D.Fd(2n, m, r), c, him, hfn, h2)) :
        {Bool.or(U32.is_eq(r, c), _) == Bool.or(U32.is_eq(r, c), D.Node(t1, m, D.Fd(2n, m, r), c)) : Bool}
      {==}
    case Bk.Term.Enu{+k}:
      {==}
    case Bk.Term.Lab{+k}:
      {==}
    case Bk.Term.Mat{+k, +t1, +t2}:
      (+nd, r0) = h
      (hn, r1) = r0
      (p3, r2) = r1
      (sp3, h3) = p3
      (sp4, h4) = r2
      +M2 = Cr.Cir.Cells.set(m, nx, x)
      +ec = D.cl.go(m, r, nx, x, lt.ne.u(r, nx, cell.lt(r, im, fi, nx, ndk.cell(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Mat{k, t1, t2}, 14, nd), him, hfn)))
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, r), Cr.Cir.Cells.get(m, r), ec) :
        {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, M2, Cr.Cir.Cell.get(3n, _), c), D.Node(t2, M2, Cr.Cir.Cell.get(4n, _), c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(3n, m, r), c), D.Node(t2, m, D.Fd(4n, m, r), c))) : Bool}
      %Equal.sym(Bool, D.Node(t1, M2, D.Fd(3n, m, r), c), D.Node(t1, m, D.Fd(3n, m, r), c),
          node.fresh(dk, t1, ds, m, im, fi, nx, ks, img, x, D.Fd(3n, m, r), c, him, hfn, h3)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(_, D.Node(t2, M2, D.Fd(4n, m, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(3n, m, r), c), D.Node(t2, m, D.Fd(4n, m, r), c))) : Bool}
      %Equal.sym(Bool, D.Node(t2, M2, D.Fd(4n, m, r), c), D.Node(t2, m, D.Fd(4n, m, r), c),
          node.fresh(dk, t2, ds, m, im, fi, nx, ks, img, x, D.Fd(4n, m, r), c, him, hfn, h4)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(3n, m, r), c), _)) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(3n, m, r), c), D.Node(t2, m, D.Fd(4n, m, r), c))) : Bool}
      {==}
    case Bk.Term.Efq{}:
      {==}
    case Bk.Term.Eql{+t1, +t2, +t3}:
      (+nd, r0) = h
      (p2, r1) = r0
      (sp2, h2) = p2
      (p3, r2) = r1
      (sp3, h3) = p3
      (sp4, h4) = r2
      +M2 = Cr.Cir.Cells.set(m, nx, x)
      +ec = D.cl.go(m, r, nx, x, lt.ne.u(r, nx, cell.lt(r, im, fi, nx, ndk.cell(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Eql{t1, t2, t3}, 16, nd), him, hfn)))
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, r), Cr.Cir.Cells.get(m, r), ec) :
        {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, M2, Cr.Cir.Cell.get(2n, _), c), Bool.or(D.Node(t2, M2, Cr.Cir.Cell.get(3n, _), c), D.Node(t3, M2, Cr.Cir.Cell.get(4n, _), c)))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), Bool.or(D.Node(t2, m, D.Fd(3n, m, r), c), D.Node(t3, m, D.Fd(4n, m, r), c)))) : Bool}
      %Equal.sym(Bool, D.Node(t1, M2, D.Fd(2n, m, r), c), D.Node(t1, m, D.Fd(2n, m, r), c),
          node.fresh(dk, t1, ds, m, im, fi, nx, ks, img, x, D.Fd(2n, m, r), c, him, hfn, h2)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(_, Bool.or(D.Node(t2, M2, D.Fd(3n, m, r), c), D.Node(t3, M2, D.Fd(4n, m, r), c)))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), Bool.or(D.Node(t2, m, D.Fd(3n, m, r), c), D.Node(t3, m, D.Fd(4n, m, r), c)))) : Bool}
      %Equal.sym(Bool, D.Node(t2, M2, D.Fd(3n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c),
          node.fresh(dk, t2, ds, m, im, fi, nx, ks, img, x, D.Fd(3n, m, r), c, him, hfn, h3)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), Bool.or(_, D.Node(t3, M2, D.Fd(4n, m, r), c)))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), Bool.or(D.Node(t2, m, D.Fd(3n, m, r), c), D.Node(t3, m, D.Fd(4n, m, r), c)))) : Bool}
      %Equal.sym(Bool, D.Node(t3, M2, D.Fd(4n, m, r), c), D.Node(t3, m, D.Fd(4n, m, r), c),
          node.fresh(dk, t3, ds, m, im, fi, nx, ks, img, x, D.Fd(4n, m, r), c, him, hfn, h4)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), Bool.or(D.Node(t2, m, D.Fd(3n, m, r), c), _))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), Bool.or(D.Node(t2, m, D.Fd(3n, m, r), c), D.Node(t3, m, D.Fd(4n, m, r), c)))) : Bool}
      {==}
    case Bk.Term.Rfl{}:
      {==}
    case Bk.Term.Rwt{+t1, +t2, +t3}:
      (+nd, r0) = h
      (p2, r1) = r0
      (sp2, h2) = p2
      (p3, r2) = r1
      (sp3, h3) = p3
      (sp4, h4) = r2
      +M2 = Cr.Cir.Cells.set(m, nx, x)
      +ec = D.cl.go(m, r, nx, x, lt.ne.u(r, nx, cell.lt(r, im, fi, nx, ndk.cell(dk, ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Rwt{t1, t2, t3}, 18, nd), him, hfn)))
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, r), Cr.Cir.Cells.get(m, r), ec) :
        {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, M2, Cr.Cir.Cell.get(2n, _), c), Bool.or(D.Node(t2, M2, Cr.Cir.Cell.get(3n, _), c), D.Node(t3, M2, Cr.Cir.Cell.get(4n, _), c)))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), Bool.or(D.Node(t2, m, D.Fd(3n, m, r), c), D.Node(t3, m, D.Fd(4n, m, r), c)))) : Bool}
      %Equal.sym(Bool, D.Node(t1, M2, D.Fd(2n, m, r), c), D.Node(t1, m, D.Fd(2n, m, r), c),
          node.fresh(dk, t1, ds, m, im, fi, nx, ks, img, x, D.Fd(2n, m, r), c, him, hfn, h2)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(_, Bool.or(D.Node(t2, M2, D.Fd(3n, m, r), c), D.Node(t3, M2, D.Fd(4n, m, r), c)))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), Bool.or(D.Node(t2, m, D.Fd(3n, m, r), c), D.Node(t3, m, D.Fd(4n, m, r), c)))) : Bool}
      %Equal.sym(Bool, D.Node(t2, M2, D.Fd(3n, m, r), c), D.Node(t2, m, D.Fd(3n, m, r), c),
          node.fresh(dk, t2, ds, m, im, fi, nx, ks, img, x, D.Fd(3n, m, r), c, him, hfn, h3)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), Bool.or(_, D.Node(t3, M2, D.Fd(4n, m, r), c)))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), Bool.or(D.Node(t2, m, D.Fd(3n, m, r), c), D.Node(t3, m, D.Fd(4n, m, r), c)))) : Bool}
      %Equal.sym(Bool, D.Node(t3, M2, D.Fd(4n, m, r), c), D.Node(t3, m, D.Fd(4n, m, r), c),
          node.fresh(dk, t3, ds, m, im, fi, nx, ks, img, x, D.Fd(4n, m, r), c, him, hfn, h4)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), Bool.or(D.Node(t2, m, D.Fd(3n, m, r), c), _))) == Bool.or(U32.is_eq(r, c), Bool.or(D.Node(t1, m, D.Fd(2n, m, r), c), Bool.or(D.Node(t2, m, D.Fd(3n, m, r), c), D.Node(t3, m, D.Fd(4n, m, r), c)))) : Bool}
      {==}

# the nodes of the owned terms after the store at nx
def nodes.fresh(+dk: Bool, os: List<&2, D.Rt>, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +x: Cr.Cir.Cell, +c: U32,
  +him: {U32.is_lt(im, fi) == True{} : Bool}, +hfn: {U32.is_le(fi, nx) == True{} : Bool},
  h: D.RtsK(dk, ds, m, im, fi, nx, ks, img, os)) -> {D.Nodes(os, Cr.Cir.Cells.set(m, nx, x), c) == D.Nodes(os, m, c) : Bool}:
  match os:
    case Nil{}:
      {==}
    case Con{D.Rt{+r, +u}, +rest}:
      match h:
        case Tuple{+hu, hr}:
          +M2 = Cr.Cir.Cells.set(m, nx, x)
          %Equal.sym(Bool, D.Node(u, M2, r, c), D.Node(u, m, r, c), node.fresh(dk, u, ds, m, im, fi, nx, ks, img, x, r, c, him, hfn, hu)) :
            {Bool.or(_, D.Nodes(rest, M2, c)) == Bool.or(D.Node(u, m, r, c), D.Nodes(rest, m, c)) : Bool}
          %Equal.sym(Bool, D.Nodes(rest, M2, c), D.Nodes(rest, m, c), nodes.fresh(dk, rest, ds, m, im, fi, nx, ks, img, x, c, him, hfn, hr)) :
            {Bool.or(D.Node(u, m, r, c), _) == Bool.or(D.Node(u, m, r, c), D.Nodes(rest, m, c)) : Bool}
          {==}

# the borrowed terms after the store at nx (each borrowed cell is below nx)
def held.fresh(+dk: Bool, bs: List<&2, D.Rt>, +os: List<&2, D.Rt>, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +x: Cr.Cir.Cell,
  +him: {U32.is_lt(im, fi) == True{} : Bool}, +hfn: {U32.is_le(fi, nx) == True{} : Bool},
  +hos: D.RtsK(dk, ds, m, im, fi, nx, ks, img, os), hbs: D.RtsK(dk, ds, m, im, fi, nx, ks, img, bs), h: D.Held(m, os, bs)) ->
  D.Held(Cr.Cir.Cells.set(m, nx, x), os, bs):
  match bs:
    case Nil{}:
      Unit{}
    case Con{D.Rt{+c, +u}, +rest}:
      match hbs:
        case Tuple{+hu, hbr}:
          match h:
            case Tuple{hh, hr}:
              +M2 = Cr.Cir.Cells.set(m, nx, x)
              +ne = isck.ne.k(dk, u, ds, m, im, fi, nx, ks, img, c, him, hfn, hu)
              ((%Equal.sym(Bool, D.Fl(M2, c, 1024), D.Fl(m, c, 1024),
                    Equal.cong(Cr.Cir.Cell, Bool, y => U32.is_ne(U32.and(Cr.Cir.Cell.get(0n, y), 1024), 0), Cr.Cir.Cells.get(M2, c), Cr.Cir.Cells.get(m, c),
                      D.cl.go(m, c, nx, x, ne))) :
                  {Bool.or(_, D.Nodes(os, M2, c)) == True{} : Bool};
                (%Equal.sym(Bool, D.Nodes(os, M2, c), D.Nodes(os, m, c), nodes.fresh(dk, os, ds, m, im, fi, nx, ks, img, x, c, him, hfn, hos)) :
                    {Bool.or(D.Fl(m, c, 1024), _) == True{} : Bool}; hh)),
                held.fresh(dk, rest, os, ds, m, im, fi, nx, ks, img, x, him, hfn, hos, hbr, hr))

# the table after the store at nx (its cells are at most 290, below nx)
def tbl.fresh(cs: List<&2, Cr.Cir.Cell>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +x: Cr.Cir.Cell, +at: U32,
  +hnx: {U32.to_nat(U32.inc(nx)) == 1n+U32.to_nat(nx) : Nat}, +hz: N.Le(1n+U32.to_nat(290), U32.to_nat(nx)),
  hb: {D.TblB(cs, at) == True{} : Bool}, h: D.Tbl.go(cs, m, im, fi, nx, at)) -> D.Tbl.go(cs, Cr.Cir.Cells.set(m, nx, x), im, fi, U32.inc(nx), at):
  match cs:
    case Nil{}:
      Unit{}
    case Con{+c, +rest}:
      (ec, r1) = h
      (e, r2) = r1
      +hb2 = hb
      +ne = D.lit.ne(U32.is_eq(at, nx), at, nx, 290, {==}, D.and.l(U32.is_le(at, 290), D.TblB(rest, U32.inc(at)), hb2), hz)
      (cell.fr(at, im, fi, nx, hnx, ec), (Equal.trans(Cr.Cir.Cell, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, nx, x), at), Cr.Cir.Cells.get(m, at), c,
          D.cl.go(m, at, nx, x, ne), e),
        tbl.fresh(rest, m, im, fi, nx, x, U32.inc(at), hnx, hz, D.and.r(U32.is_le(at, 290), D.TblB(rest, U32.inc(at)), hb2), r2)))

# the defs' bodies after the store at nx
def defs.fresh(dl: List<&2, Bk.Def>, +dk: Bool, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +x: Cr.Cir.Cell, +at: U32,
  +hnx: {U32.to_nat(U32.inc(nx)) == 1n+U32.to_nat(nx) : Nat}, +him: {U32.is_lt(im, fi) == True{} : Bool}, +hfn: {U32.is_le(fi, nx) == True{} : Bool},
  h: D.DefsK(dl, dk, ds, m, im, fi, nx, ks, img, at)) -> D.DefsK(dl, dk, ds, Cr.Cir.Cells.set(m, nx, x), im, fi, U32.inc(nx), ks, img, at):
  match dl:
    case Nil{}:
      Unit{}
    case Con{Bk.Def{_, _, +v, _}, +rest}:
      (e0, r1) = h
      (ele, r2) = r1
      (hv, r3) = r2
      (e0, (ele, (isk.fr(dk, v, ds, m, im, fi, nx, ks, img, x, at, hnx, him, hfn, hv),
        defs.fresh(rest, dk, ds, m, im, fi, nx, ks, img, x, U32.add(at, Mc.Img.size(v)), hnx, him, hfn, r3))))

# the image after the store at nx, with next nx + 1
def imgok.fresh(+dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells,
  +im: U32, +fi: U32, +nx: U32, +x: Cr.Cir.Cell, +hnx: {U32.to_nat(U32.inc(nx)) == 1n+U32.to_nat(nx) : Nat},
  +hfn: {U32.is_le(fi, nx) == True{} : Bool},
  h: D.ImgOKK(dk, ds, ks, img, m, im, fi, nx)) -> D.ImgOKK(dk, ds, ks, img, Cr.Cir.Cells.set(m, nx, x), im, fi, U32.inc(nx)):
  (tbl, r1) = h
  (hd, r2) = r1
  (h8, r3) = r2
  (h9, r4) = r3
  (h10, r5) = r4
  (hks, r6) = r5
  (e290a, eima) = r6
  +e290 = {e290a : {U32.is_le(290, im) == True{} : Bool}}
  +eim = {eima : {U32.is_lt(im, fi) == True{} : Bool}}
  +hz = N.le_trans(1n+U32.to_nat(290), 1n+U32.to_nat(im), U32.to_nat(nx), D.u.le(290, im, e290),
    N.le_trans(1n+U32.to_nat(im), U32.to_nat(fi), U32.to_nat(nx), D.u.lt(im, fi, eim), D.u.le(fi, nx, hfn)))
  (tbl.fresh(Mc.Img.table([]), m, im, fi, nx, x, 272, hnx, hz, {==}, tbl),
    (defs.fresh(ds, dk, ds, m, im, fi, nx, ks, img, x, Mc.I.book(), hnx, eim, hfn, hd),
    (isk.fr(dk, Bk.Term.Lab{El.Quan.name(Bk.Quan.Q0{})}, ds, m, im, fi, nx, ks, img, x, 8, hnx, eim, hfn, h8),
    (isk.fr(dk, Bk.Term.Lab{El.Quan.name(Bk.Quan.Q1{})}, ds, m, im, fi, nx, ks, img, x, 9, hnx, eim, hfn, h9),
    (isk.fr(dk, Bk.Term.Lab{El.Quan.name(Bk.Quan.Q2{})}, ds, m, im, fi, nx, ks, img, x, 10, hnx, eim, hfn, h10),
    (hks, (e290, eim)))))))

# 290 <= im (the image)
def img.ge(-dk: Bool, -ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -m: Cr.Cir.Cells,
  -im: U32, -fi: U32, -nx: U32, h: D.ImgOKK(dk, ds, ks, img, m, im, fi, nx)) -> {U32.is_le(290, im) == True{} : Bool}:
  (_, r1) = h
  (_, r2) = r1
  (_, r3) = r2
  (_, r4) = r3
  (_, r5) = r4
  (_, r6) = r5
  (e, _) = r6
  e

# a cell all zeros is a Var: no pointer (the table's mask for Var is 0)
def fs.zero(+m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ps: List<&2, U32>, tbl: D.Tbl(m, im, fi, nx),
  hz: N.Le(1n+U32.to_nat(290), U32.to_nat(nx))) -> {D.Fs(Cr.Cir.Cells.set(m, nx, Cr.Cir.Cell.zero()), ps, nx) == Nil{} : List<&2, U32>}:
  +M2 = Cr.Cir.Cells.set(m, nx, Cr.Cir.Cell.zero())
  +e272 = Equal.trans(U32, D.Fd(2n, M2, 272), D.Fd(2n, m, 272), 0,
    Equal.cong(Cr.Cir.Cell, U32, y => Cr.Cir.Cell.get(2n, y), Cr.Cir.Cells.get(M2, 272), Cr.Cir.Cells.get(m, 272),
      D.cl.go(m, 272, nx, Cr.Cir.Cell.zero(), D.lit.ne(U32.is_eq(272, nx), 272, nx, 290, {==}, {==}, hz))),
    D.tbl.mask(m, im, fi, nx, Bk.Term.Var{0n}, tbl))
  %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, nx), Cr.Cir.Cell.zero(), D.cl.gs(m, nx, Cr.Cir.Cell.zero())) :
    {D.FsK(U32.is_lt(D.TgW(Cr.Cir.Cell.get(0n, _)), 19), D.Fd(2n, M2, U32.add(272, D.TgW(Cr.Cir.Cell.get(0n, _)))), _, ps, nx) == Nil{} : List<&2, U32>}
  %Equal.sym(U32, D.Fd(2n, M2, 272), 0, e272) : {D.Fs.term(_, 0, 0, 0) == Nil{} : List<&2, U32>}
  {==}

# HSK after M.alloc's new cell nx (the pend list empty): next is nx + 1
def hs.fresh.go(+dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32,
  +hos: D.RtsK(dk, ds, m, im, fi, nx, ks, img, os), +hbs: D.RtsK(dk, ds, m, im, fi, nx, ks, img, bs), +hheld: D.Held(m, os, bs),
  +hfrs: D.FrsK(dk, ds, m, im, fi, nx, ks, img, Nil{}, sp, fs), +hheap: D.Heap(m, nx, fi, im, D.Rt.cells(os), pend, Nil{}),
  +himg: D.ImgOKK(dk, ds, ks, img, m, im, fi, nx), +hlt: {U32.is_lt(nx, 214748364) == True{} : Bool}) ->
  D.HSK(dk, ds, ks, img, Cr.Cir.Cells.set(m, nx, Cr.Cir.Cell.zero()), U32.inc(nx), fi, im, os, bs, fs, sp, pend, Nil{}):
  (hch, r1) = hheap
  (_, r2) = r1
  (hcnt, r3) = r2
  (hpts, _) = r3
  +X = Cr.Cir.Cell.zero()
  +M2 = Cr.Cir.Cells.set(m, nx, X)
  +rs = D.Rt.cells(os)
  +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
  +hfn = heap.fn(m, nx, fi, im, rs, pend, Nil{}, hheap)
  +him = img.lt(dk, ds, ks, img, m, im, fi, nx, himg)
  +tbl = D.img.tbl(dk, ds, ks, img, m, im, fi, nx, himg)
  +hnx = D.u.inc(nx, 214748364, D.u.lt(nx, 214748364, hlt))
  +le = D.u.le(fi, nx, hfn)
  +es = D.add.sub(U32.to_nat(fi), U32.to_nat(nx), le)
  +en = Equal.trans(Nat, Nat.sub(U32.to_nat(U32.inc(nx)), U32.to_nat(fi)), Nat.sub(1n+U32.to_nat(nx), U32.to_nat(fi)), 1n+n,
    Equal.cong(Nat, Nat, w => Nat.sub(w, U32.to_nat(fi)), U32.to_nat(U32.inc(nx)), 1n+U32.to_nat(nx), hnx),
    AC.sub.succ(U32.to_nat(nx), U32.to_nat(fi), le))
  +hz290 = N.le_trans(1n+U32.to_nat(290), 1n+U32.to_nat(im), U32.to_nat(nx), D.u.le(290, im, img.ge(dk, ds, ks, img, m, im, fi, nx, himg)),
    N.le_trans(1n+U32.to_nat(im), U32.to_nat(fi), U32.to_nat(nx), D.u.lt(im, fi, him), le))
  +htN = D.TblR.of(n, m, fi, nx, hz290)
  +hf1 = fs.zero(m, im, fi, nx, Nil{}, tbl, hz290)
  +hp0 = Equal.trans(Nat, D.Ptr(1n+n, M2, fi, Nil{}, rs, nx), D.Ptr(n, m, fi, Nil{}, rs, nx), 0n,
    ptr.fresh(n, m, fi, nx, X, Nil{}, rs, nx, es, hf1, htN),
    Equal.trans(Nat, Nat.add(D.Pc(n, m, Nil{}, fi, nx), D.RcL(rs, nx)), Nat.add(0n, D.RcL(rs, nx)), 0n,
      Equal.cong(Nat, Nat, w => Nat.add(w, D.RcL(rs, nx)), D.Pc(n, m, Nil{}, fi, nx), 0n, pc.pts.z(n, m, Nil{}, fi, im, fi, nx, hpts)),
      rcl.roots.z(dk, os, ds, m, im, fi, nx, ks, img, him, hfn, hos)))
  +hxc = {(%Equal.sym(Nat, D.Ptr(1n+n, M2, fi, Nil{}, rs, nx), 0n, hp0) : {D.CntC(X, _, Nil{}, nx) == True{} : Bool}; {==}) :
    {D.CntC(X, D.Ptr(1n+n, M2, fi, Nil{}, rs, nx), Nil{}, nx) == True{} : Bool}}
  (rtsk.fr(dk, os, ds, m, im, fi, nx, ks, img, X, hnx, him, hfn, hos),
    (rtsk.fr(dk, bs, ds, m, im, fi, nx, ks, img, X, hnx, him, hfn, hbs),
    (held.fresh(dk, bs, os, ds, m, im, fi, nx, ks, img, X, him, hfn, hos, hbs, hheld),
    (frsk.fr(dk, fs, ds, m, im, fi, nx, ks, img, Nil{}, X, sp, hnx, him, hfn, hfrs),
    ((hch, (Unit{},
      ((%Equal.sym(Nat, Nat.sub(U32.to_nat(U32.inc(nx)), U32.to_nat(fi)), 1n+n, en) : {D.Cnt(_, M2, fi, _, fi, Nil{}, rs) == True{} : Bool};
          cnt.fresh(n, m, fi, nx, X, n, fi, Nil{}, rs, es, es, hf1, htN, hxc, hcnt)),
      ((%Equal.sym(Nat, Nat.sub(U32.to_nat(U32.inc(nx)), U32.to_nat(fi)), 1n+n, en) : {D.Pts(_, M2, Nil{}, fi, im, fi, U32.inc(nx)) == True{} : Bool};
          pts.fresh(n, m, fi, nx, X, Nil{}, im, fi, hnx, es, hf1, htN, hpts)),
      (u.le.of(U32.inc(nx), 214748364, N.le_rw_l(1n+U32.to_nat(nx), U32.to_nat(U32.inc(nx)), U32.to_nat(214748364),
          Equal.sym(Nat, U32.to_nat(U32.inc(nx)), 1n+U32.to_nat(nx), hnx), D.u.lt(nx, 214748364, hlt))),
        u.le.of(fi, U32.inc(nx), N.le_rw_r(U32.to_nat(fi), 1n+U32.to_nat(nx), U32.to_nat(U32.inc(nx)),
          Equal.sym(Nat, U32.to_nat(U32.inc(nx)), 1n+U32.to_nat(nx), hnx), N.le_succ(U32.to_nat(fi), U32.to_nat(nx), le)))))))),
      imgok.fresh(dk, ds, ks, img, m, im, fi, nx, X, hnx, hfn, himg))))))

def hs.fresh(+dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32,
  hs: D.HSK(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, Nil{}), +hlt: {U32.is_lt(nx, 214748364) == True{} : Bool}) ->
  D.HSK(dk, ds, ks, img, Cr.Cir.Cells.set(m, nx, Cr.Cir.Cell.zero()), U32.inc(nx), fi, im, os, bs, fs, sp, pend, Nil{}):
  match hs:
    case Tuple{+hos, Tuple{+hbs, Tuple{+hheld, Tuple{+hfrs, Tuple{+hheap, himg}}}}}:
      hs.fresh.go(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, hos, hbs, hheld, hfrs, hheap, himg, hlt)

# The laws
# --------

def D.inc.post(f, dk, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, r, os, bs, fs, sp, pend, ps, c, u, xs, zs, hs, hac, hn, hc):
  inc.top(f, dk, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, r, os, bs, fs, sp, pend, ps, c, u, xs, zs, hs, hac, hn, hc)

def D.dec.post(f, dk, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, r, os, bs, fs, sp, pend, ps, c, u, xs, zs, hs, hac, hb, hl, hc, hp, h5):
  dec.top(f, dk, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, r, os, bs, fs, sp, pend, ps, c, u, xs, zs, hs, hac, hb, hl, hc, hp, h5)

def D.alloc.post(f, dk, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, r, keep, os, bs, fs, sp, pend, ps, xs, zs, hs, hac, hl, hp, hr, hk):
  ?TODO

def D.release.post(f, dk, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, r, os, bs, fs, sp, pend, ps, z, xs, zs, hs, hac, hz, ht, hf, hm, hfs, hl, hc, hp):
  rel.go(f, dk, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, r, os, bs, fs, sp, pend, ps, z, xs, zs, hs, hac, hz, ht, hf, hm, hfs, hl, hc, hp)

def D.is.fresh(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps, x, hs):
  fresh.top(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps, x, hs)

def D.node.part(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps, c, y, hs, hn, hy):
  match hs:
    case Tuple{hos, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{+tbl, _}}}}}}:
      np.nodes(os, dk, ds, m, im, fi, nx, ks, img, ps, tbl, c, y, hos, hn, hy)

def D.store.post(dk, ds, ks, img, m, nx, fi, im, us, os, bs, fs, sp, pend, ps, z, x, xs, zs, hs, hac, hzx, hb, ho, hm, hzs, hzt, hz0, hzf, ht, hxs, hf):
  st.top(dk, ds, ks, img, m, nx, fi, im, us, os, bs, fs, sp, pend, ps, z, x, xs, zs, hs, hac, hzx, hb, ho, hm, hzs, hzt, hz0, hzf, ht, hxs, hf)

def D.term.post(dk, ds, ks, img, m, nx, fi, im, us, os, bs, fs, sp, pend, ps, z, x, t, xs, zs, hs, hac, ho, hm, hzs, hzt, hz0, hzf, hxs, hx1, hf, hi):
  ?TODO

def D.data.flag(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps, c, xs, zs, hs, hac, hd, hco):
  df.top(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps, c, xs, zs, hs, hac, hd, hco)
