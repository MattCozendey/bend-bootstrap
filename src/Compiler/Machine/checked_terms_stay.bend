# compiler: checked terms stay
# ============================
#
# A checked term (D.Tm) reads only cells that may be read, by its tag's
# parts; it stays when the run writes a cell that it may not read, when it
# writes only a count (field 1), with more fuel, and when more cells may be
# read. Each proof goes by the fuel, and at a cell by Cg: T.tm.cell gives the
# same term from parts that give at least what they gave.

import Base
import ../../Book/impl.bend as Bk
import ../Cir/impl.bend as Cr
import ./cell_terms.bend as T
import ../need_big.bend as N
import ./copy_substitution.bend as D
import ./copy_kit.bend as K

# Parts
# -----

# a part that gave a gives a again
def Pt(p: Unit -> Maybe<&2, Bk.Term>, q: Unit -> Maybe<&2, Bk.Term>) -> Type:
  @a: Bk.Term -> {p(Unit{}) == Some{a} : Maybe<&2, Bk.Term>} -> {q(Unit{}) == Some{a} : Maybe<&2, Bk.Term>}

def Mb.some(-A: Data, -a: A, -b: A, e: {Some{a} == Some{b} : Maybe<&2, A>}) -> {a == b : A}:
  Equal.cong(Maybe<&2, A>, A, x => Maybe.default(&2, A, x, a), Some{a}, Some{b}, e)

def Mb.ns(-A: Data, -b: A, -G: Type, e: {None{} == Some{b} : Maybe<&2, A>}) -> G:
  Empty.absurd(G, N.true_ne_false(Equal.cong(Maybe<&2, A>, Bool, x => Maybe.is_none(&2, A, x), None{}, Some{b}, e)))

def Cg.one(-k: Bk.Term -> Bk.Term, r: Maybe<&2, Bk.Term>, s: Maybe<&2, Bk.Term>, -t: Bk.Term,
  h: {T.tm.one(k, r) == Some{t} : Maybe<&2, Bk.Term>}, g: @a: Bk.Term -> {r == Some{a} : Maybe<&2, Bk.Term>} -> {s == Some{a} : Maybe<&2, Bk.Term>}) ->
  {T.tm.one(k, s) == Some{t} : Maybe<&2, Bk.Term>}:
  match r:
    case None{}:
      Mb.ns(Bk.Term, t, {T.tm.one(k, s) == Some{t} : Maybe<&2, Bk.Term>}, h)
    case Some{+a}:
      %Equal.sym(Maybe<&2, Bk.Term>, s, Some{a}, g(a, {==})) : {T.tm.one(k, _) == Some{t} : Maybe<&2, Bk.Term>}
      h

def Cg.two.s(-k: Bk.Term -> Bk.Term -> Bk.Term, +a: Bk.Term, r2: Maybe<&2, Bk.Term>, s1: Maybe<&2, Bk.Term>, s2: Maybe<&2, Bk.Term>, -t: Bk.Term,
  e1: {s1 == Some{a} : Maybe<&2, Bk.Term>}, h: {T.tm.two(k, Some{a}, r2) == Some{t} : Maybe<&2, Bk.Term>},
  g2: @b: Bk.Term -> {r2 == Some{b} : Maybe<&2, Bk.Term>} -> {s2 == Some{b} : Maybe<&2, Bk.Term>}) ->
  {T.tm.two(k, s1, s2) == Some{t} : Maybe<&2, Bk.Term>}:
  match r2:
    case None{}:
      Mb.ns(Bk.Term, t, {T.tm.two(k, s1, s2) == Some{t} : Maybe<&2, Bk.Term>}, h)
    case Some{+b}:
      %Equal.sym(Maybe<&2, Bk.Term>, s1, Some{a}, e1) : {T.tm.two(k, _, s2) == Some{t} : Maybe<&2, Bk.Term>}
      %Equal.sym(Maybe<&2, Bk.Term>, s2, Some{b}, g2(b, {==})) : {T.tm.two(k, Some{a}, _) == Some{t} : Maybe<&2, Bk.Term>}
      h

def Cg.two(-k: Bk.Term -> Bk.Term -> Bk.Term, r1: Maybe<&2, Bk.Term>, r2: Maybe<&2, Bk.Term>, s1: Maybe<&2, Bk.Term>, s2: Maybe<&2, Bk.Term>,
  -t: Bk.Term, h: {T.tm.two(k, r1, r2) == Some{t} : Maybe<&2, Bk.Term>},
  g1: @a: Bk.Term -> {r1 == Some{a} : Maybe<&2, Bk.Term>} -> {s1 == Some{a} : Maybe<&2, Bk.Term>},
  g2: @b: Bk.Term -> {r2 == Some{b} : Maybe<&2, Bk.Term>} -> {s2 == Some{b} : Maybe<&2, Bk.Term>}) ->
  {T.tm.two(k, s1, s2) == Some{t} : Maybe<&2, Bk.Term>}:
  match r1:
    case None{}:
      Mb.ns(Bk.Term, t, {T.tm.two(k, s1, s2) == Some{t} : Maybe<&2, Bk.Term>}, h)
    case Some{+a}:
      Cg.two.s(k, a, r2, s1, s2, t, g1(a, {==}), h, g2)

def Cg.three.t(-k: Bk.Term -> Bk.Term -> Bk.Term -> Bk.Term, +a: Bk.Term, +b: Bk.Term, r3: Maybe<&2, Bk.Term>, s1: Maybe<&2, Bk.Term>,
  s2: Maybe<&2, Bk.Term>, s3: Maybe<&2, Bk.Term>, -t: Bk.Term, e1: {s1 == Some{a} : Maybe<&2, Bk.Term>}, e2: {s2 == Some{b} : Maybe<&2, Bk.Term>},
  h: {T.tm.three(k, Some{a}, Some{b}, r3) == Some{t} : Maybe<&2, Bk.Term>},
  g3: @c: Bk.Term -> {r3 == Some{c} : Maybe<&2, Bk.Term>} -> {s3 == Some{c} : Maybe<&2, Bk.Term>}) ->
  {T.tm.three(k, s1, s2, s3) == Some{t} : Maybe<&2, Bk.Term>}:
  match r3:
    case None{}:
      Mb.ns(Bk.Term, t, {T.tm.three(k, s1, s2, s3) == Some{t} : Maybe<&2, Bk.Term>}, h)
    case Some{+c}:
      %Equal.sym(Maybe<&2, Bk.Term>, s1, Some{a}, e1) : {T.tm.three(k, _, s2, s3) == Some{t} : Maybe<&2, Bk.Term>}
      %Equal.sym(Maybe<&2, Bk.Term>, s2, Some{b}, e2) : {T.tm.three(k, Some{a}, _, s3) == Some{t} : Maybe<&2, Bk.Term>}
      %Equal.sym(Maybe<&2, Bk.Term>, s3, Some{c}, g3(c, {==})) : {T.tm.three(k, Some{a}, Some{b}, _) == Some{t} : Maybe<&2, Bk.Term>}
      h

def Cg.three.s(-k: Bk.Term -> Bk.Term -> Bk.Term -> Bk.Term, +a: Bk.Term, r2: Maybe<&2, Bk.Term>, r3: Maybe<&2, Bk.Term>, s1: Maybe<&2, Bk.Term>,
  s2: Maybe<&2, Bk.Term>, s3: Maybe<&2, Bk.Term>, -t: Bk.Term, e1: {s1 == Some{a} : Maybe<&2, Bk.Term>},
  h: {T.tm.three(k, Some{a}, r2, r3) == Some{t} : Maybe<&2, Bk.Term>},
  g2: @b: Bk.Term -> {r2 == Some{b} : Maybe<&2, Bk.Term>} -> {s2 == Some{b} : Maybe<&2, Bk.Term>},
  g3: @c: Bk.Term -> {r3 == Some{c} : Maybe<&2, Bk.Term>} -> {s3 == Some{c} : Maybe<&2, Bk.Term>}) ->
  {T.tm.three(k, s1, s2, s3) == Some{t} : Maybe<&2, Bk.Term>}:
  match r2:
    case None{}:
      Mb.ns(Bk.Term, t, {T.tm.three(k, s1, s2, s3) == Some{t} : Maybe<&2, Bk.Term>}, h)
    case Some{+b}:
      Cg.three.t(k, a, b, r3, s1, s2, s3, t, e1, g2(b, {==}), h, g3)

def Cg.three(-k: Bk.Term -> Bk.Term -> Bk.Term -> Bk.Term, r1: Maybe<&2, Bk.Term>, r2: Maybe<&2, Bk.Term>, r3: Maybe<&2, Bk.Term>,
  s1: Maybe<&2, Bk.Term>, s2: Maybe<&2, Bk.Term>, s3: Maybe<&2, Bk.Term>, -t: Bk.Term,
  h: {T.tm.three(k, r1, r2, r3) == Some{t} : Maybe<&2, Bk.Term>},
  g1: @a: Bk.Term -> {r1 == Some{a} : Maybe<&2, Bk.Term>} -> {s1 == Some{a} : Maybe<&2, Bk.Term>},
  g2: @b: Bk.Term -> {r2 == Some{b} : Maybe<&2, Bk.Term>} -> {s2 == Some{b} : Maybe<&2, Bk.Term>},
  g3: @c: Bk.Term -> {r3 == Some{c} : Maybe<&2, Bk.Term>} -> {s3 == Some{c} : Maybe<&2, Bk.Term>}) ->
  {T.tm.three(k, s1, s2, s3) == Some{t} : Maybe<&2, Bk.Term>}:
  match r1:
    case None{}:
      Mb.ns(Bk.Term, t, {T.tm.three(k, s1, s2, s3) == Some{t} : Maybe<&2, Bk.Term>}, h)
    case Some{+a}:
      Cg.three.s(k, a, r2, r3, s1, s2, s3, t, g1(a, {==}), h, g2, g3)

def Cg.mat.t(+kk: List<&2, Word(8n)>, +a: Bk.Term, r2: Maybe<&2, Bk.Term>, s1: Maybe<&2, Bk.Term>, s2: Maybe<&2, Bk.Term>, -t: Bk.Term,
  e1: {s1 == Some{a} : Maybe<&2, Bk.Term>}, h: {T.tm.mat(Some{kk}, Some{a}, r2) == Some{t} : Maybe<&2, Bk.Term>},
  g2: @b: Bk.Term -> {r2 == Some{b} : Maybe<&2, Bk.Term>} -> {s2 == Some{b} : Maybe<&2, Bk.Term>}) ->
  {T.tm.mat(Some{kk}, s1, s2) == Some{t} : Maybe<&2, Bk.Term>}:
  match r2:
    case None{}:
      Mb.ns(Bk.Term, t, {T.tm.mat(Some{kk}, s1, s2) == Some{t} : Maybe<&2, Bk.Term>}, h)
    case Some{+b}:
      %Equal.sym(Maybe<&2, Bk.Term>, s1, Some{a}, e1) : {T.tm.mat(Some{kk}, _, s2) == Some{t} : Maybe<&2, Bk.Term>}
      %Equal.sym(Maybe<&2, Bk.Term>, s2, Some{b}, g2(b, {==})) : {T.tm.mat(Some{kk}, Some{a}, _) == Some{t} : Maybe<&2, Bk.Term>}
      h

def Cg.mat.s(+kk: List<&2, Word(8n)>, r1: Maybe<&2, Bk.Term>, r2: Maybe<&2, Bk.Term>, s1: Maybe<&2, Bk.Term>, s2: Maybe<&2, Bk.Term>, -t: Bk.Term,
  h: {T.tm.mat(Some{kk}, r1, r2) == Some{t} : Maybe<&2, Bk.Term>},
  g1: @a: Bk.Term -> {r1 == Some{a} : Maybe<&2, Bk.Term>} -> {s1 == Some{a} : Maybe<&2, Bk.Term>},
  g2: @b: Bk.Term -> {r2 == Some{b} : Maybe<&2, Bk.Term>} -> {s2 == Some{b} : Maybe<&2, Bk.Term>}) ->
  {T.tm.mat(Some{kk}, s1, s2) == Some{t} : Maybe<&2, Bk.Term>}:
  match r1:
    case None{}:
      Mb.ns(Bk.Term, t, {T.tm.mat(Some{kk}, s1, s2) == Some{t} : Maybe<&2, Bk.Term>}, h)
    case Some{+a}:
      Cg.mat.t(kk, a, r2, s1, s2, t, g1(a, {==}), h, g2)

def Cg.mat(n: Maybe<&2, List<&2, Word(8n)>>, r1: Maybe<&2, Bk.Term>, r2: Maybe<&2, Bk.Term>, s1: Maybe<&2, Bk.Term>, s2: Maybe<&2, Bk.Term>, -t: Bk.Term,
  h: {T.tm.mat(n, r1, r2) == Some{t} : Maybe<&2, Bk.Term>},
  g1: @a: Bk.Term -> {r1 == Some{a} : Maybe<&2, Bk.Term>} -> {s1 == Some{a} : Maybe<&2, Bk.Term>},
  g2: @b: Bk.Term -> {r2 == Some{b} : Maybe<&2, Bk.Term>} -> {s2 == Some{b} : Maybe<&2, Bk.Term>}) ->
  {T.tm.mat(n, s1, s2) == Some{t} : Maybe<&2, Bk.Term>}:
  match n:
    case None{}:
      Mb.ns(Bk.Term, t, {T.tm.mat(None{}, s1, s2) == Some{t} : Maybe<&2, Bk.Term>}, h)
    case Some{+kk}:
      Cg.mat.s(kk, r1, r2, s1, s2, t, h, g1, g2)

# T.tm.cell gives the same term t from parts that give at least what they gave
def Cg(tag: Nat, +q: Bk.Quan, +c: U32, +f2: U32, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  p2: Unit -> Maybe<&2, Bk.Term>, p3: Unit -> Maybe<&2, Bk.Term>, p4: Unit -> Maybe<&2, Bk.Term>,
  q2: Unit -> Maybe<&2, Bk.Term>, q3: Unit -> Maybe<&2, Bk.Term>, q4: Unit -> Maybe<&2, Bk.Term>, -t: Bk.Term,
  h: {T.tm.cell(tag, q, c, f2, ks, img, p2, p3, p4) == Some{t} : Maybe<&2, Bk.Term>},
  g2: Pt(p2, q2), g3: Pt(p3, q3), g4: Pt(p4, q4)) ->
  {T.tm.cell(tag, q, c, f2, ks, img, q2, q3, q4) == Some{t} : Maybe<&2, Bk.Term>}:
  match tag:
    case 0n:
      h
    case 1n:
      h
    case 2n:
      Cg.two(a => b => Bk.Term.Ann{a, b}, p2(Unit{}), p3(Unit{}), q2(Unit{}), q3(Unit{}), t, h, g2, g3)
    case 3n:
      Cg.two(a => b => Bk.Term.Let{q, a, b}, p2(Unit{}), p3(Unit{}), q2(Unit{}), q3(Unit{}), t, h, g2, g3)
    case 4n:
      Cg.one(a => Bk.Term.Typ{a}, p2(Unit{}), q2(Unit{}), t, h, g2)
    case 5n:
      Cg.two(a => b => Bk.Term.Min{a, b}, p2(Unit{}), p3(Unit{}), q2(Unit{}), q3(Unit{}), t, h, g2, g3)
    case 6n:
      Cg.two(a => b => Bk.Term.All{q, a, b}, p2(Unit{}), p3(Unit{}), q2(Unit{}), q3(Unit{}), t, h, g2, g3)
    case 7n:
      Cg.one(a => Bk.Term.Lam{q, a}, p2(Unit{}), q2(Unit{}), t, h, g2)
    case 8n:
      Cg.two(a => b => Bk.Term.App{q, a, b}, p2(Unit{}), p3(Unit{}), q2(Unit{}), q3(Unit{}), t, h, g2, g3)
    case 9n:
      Cg.two(a => b => Bk.Term.Sig{q, a, b}, p2(Unit{}), p3(Unit{}), q2(Unit{}), q3(Unit{}), t, h, g2, g3)
    case 10n:
      Cg.two(a => b => Bk.Term.Tup{q, a, b}, p2(Unit{}), p3(Unit{}), q2(Unit{}), q3(Unit{}), t, h, g2, g3)
    case 11n:
      Cg.one(a => Bk.Term.Prj{a}, p2(Unit{}), q2(Unit{}), t, h, g2)
    case 12n:
      h
    case 13n:
      h
    case 14n:
      Cg.mat(T.tm.name(ks, f2), p3(Unit{}), p4(Unit{}), q3(Unit{}), q4(Unit{}), t, h, g3, g4)
    case 15n:
      h
    case 16n:
      Cg.three(a => b => y => Bk.Term.Eql{a, b, y}, p2(Unit{}), p3(Unit{}), p4(Unit{}), q2(Unit{}), q3(Unit{}), q4(Unit{}), t, h, g2, g3, g4)
    case 17n:
      h
    case 18n:
      Cg.three(a => b => y => Bk.Term.Rwt{a, b, y}, p2(Unit{}), p3(Unit{}), p4(Unit{}), q2(Unit{}), q3(Unit{}), q4(Unit{}), t, h, g2, g3, g4)
    case 19n+r:
      h

# Checked terms
# -------------

# Tm.chk gives t from a part that gives at least what it gave
def Tm.chk.cg(+tag: Nat, +fvf: U32, r: Maybe<&2, Bk.Term>, s: Maybe<&2, Bk.Term>, -t: Bk.Term,
  h: {D.Tm.chk(tag, fvf, r) == Some{t} : Maybe<&2, Bk.Term>},
  g: @a: Bk.Term -> {r == Some{a} : Maybe<&2, Bk.Term>} -> {s == Some{a} : Maybe<&2, Bk.Term>}) ->
  {D.Tm.chk(tag, fvf, s) == Some{t} : Maybe<&2, Bk.Term>}:
  match r:
    case None{}:
      Mb.ns(Bk.Term, t, {D.Tm.chk(tag, fvf, s) == Some{t} : Maybe<&2, Bk.Term>}, h)
    case Some{+a}:
      %Equal.sym(Maybe<&2, Bk.Term>, s, Some{a}, g(a, {==})) : {D.Tm.chk(tag, fvf, _) == Some{t} : Maybe<&2, Bk.Term>}
      h

# the checked term of the cell c, whose content is cell, with the fuel 1 + f,
# when ok says that c may be read
def Tm.at.b(ok: Bool, +f: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +K: U32, +F: U32,
  +X: List<&2, U32>, +N: U32, +c: U32, +cell: Cr.Cir.Cell) -> Maybe<&2, Bk.Term>:
  +f0 = Cr.Cir.Cell.get(0n, cell)
  +tag = U32.to_nat(U32.and(f0, 63))
  D.Tm.if(ok, u => D.Tm.chk(tag, U32.shrn(f0, 13n),
    T.tm.cell(tag, T.tm.quan(U32.and(U32.shrn(f0, 6n), 3)), c, Cr.Cir.Cell.get(2n, cell), ks, img,
      u => D.Tm(f, m, ks, img, K, F, X, N, Cr.Cir.Cell.get(2n, cell)),
      u => D.Tm(f, m, ks, img, K, F, X, N, Cr.Cir.Cell.get(3n, cell)),
      u => D.Tm(f, m, ks, img, K, F, X, N, Cr.Cir.Cell.get(4n, cell)))))

def Tm.at(+f: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +K: U32, +F: U32,
  +X: List<&2, U32>, +N: U32, +c: U32, +cell: Cr.Cir.Cell) -> Maybe<&2, Bk.Term>:
  Tm.at.b(D.Al(K, F, X, N, c), f, m, ks, img, K, F, X, N, c, cell)

def Tm.at.eq(+f: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +K: U32, +F: U32,
  +X: List<&2, U32>, +N: U32, +c: U32) ->
  {D.Tm(1n+f, m, ks, img, K, F, X, N, c) == Tm.at(f, m, ks, img, K, F, X, N, c, Cr.Cir.Cells.get(m, c)) : Maybe<&2, Bk.Term>}:
  {==}

# a cell that a checked term reads may be read
def Tm.al.if(b: Bool, +f: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +K: U32, +F: U32,
  +X: List<&2, U32>, +N: U32, +c: U32, +cell: Cr.Cir.Cell, -t: Bk.Term, eb: {b == D.Al(K, F, X, N, c) : Bool},
  h: {Tm.at.b(b, f, m, ks, img, K, F, X, N, c, cell) == Some{t} : Maybe<&2, Bk.Term>}) -> {D.Al(K, F, X, N, c) == True{} : Bool}:
  match b:
    case True{}:
      Equal.sym(Bool, True{}, D.Al(K, F, X, N, c), eb)
    case False{}:
      Mb.ns(Bk.Term, t, {D.Al(K, F, X, N, c) == True{} : Bool}, h)

# a cell that may be read is not one that may not
def Al.ne.if(b: Bool, +K: U32, +F: U32, +X: List<&2, U32>, +N: U32, +c: U32, +i: U32, eb: {b == U32.is_eq(c, i) : Bool},
  ha: {D.Al(K, F, X, N, c) == True{} : Bool}, hi: {False{} == D.Al(K, F, X, N, i) : Bool}) -> {U32.is_eq(c, i) == False{} : Bool}:
  match b:
    case True{}:
      +e = K.U.eq(c, i, Equal.sym(Bool, True{}, U32.is_eq(c, i), eb))
      K.Bo.ft({U32.is_eq(c, i) == False{} : Bool}, Equal.trans(Bool, True{}, D.Al(K, F, X, N, c), False{},
        Equal.sym(Bool, D.Al(K, F, X, N, c), True{}, ha),
        Equal.trans(Bool, D.Al(K, F, X, N, c), D.Al(K, F, X, N, i), False{}, Equal.cong(U32, Bool, y => D.Al(K, F, X, N, y), c, i, e),
          Equal.sym(Bool, False{}, D.Al(K, F, X, N, i), hi))))
    case False{}:
      Equal.sym(Bool, False{}, U32.is_eq(c, i), eb)

# the round at a readable cell, from parts that give at least what they gave
def Tm.at.cg(b: Bool, +f: Nat, +f2: Nat, +m: Cr.Cir.Cells, +m2: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +K: U32, +F: U32, +X: List<&2, U32>, +N: U32, +X2: List<&2, U32>, +N2: U32, +b2: Bool, +c: U32, +cell: Cr.Cir.Cell, -t: Bk.Term,
  eb: {b == b2 : Bool},
  h: {Tm.at.b(b, f, m, ks, img, K, F, X, N, c, cell) == Some{t} : Maybe<&2, Bk.Term>},
  g2: Pt(u => D.Tm(f, m, ks, img, K, F, X, N, Cr.Cir.Cell.get(2n, cell)), u => D.Tm(f2, m2, ks, img, K, F, X2, N2, Cr.Cir.Cell.get(2n, cell))),
  g3: Pt(u => D.Tm(f, m, ks, img, K, F, X, N, Cr.Cir.Cell.get(3n, cell)), u => D.Tm(f2, m2, ks, img, K, F, X2, N2, Cr.Cir.Cell.get(3n, cell))),
  g4: Pt(u => D.Tm(f, m, ks, img, K, F, X, N, Cr.Cir.Cell.get(4n, cell)), u => D.Tm(f2, m2, ks, img, K, F, X2, N2, Cr.Cir.Cell.get(4n, cell)))) ->
  {Tm.at.b(b2, f2, m2, ks, img, K, F, X2, N2, c, cell) == Some{t} : Maybe<&2, Bk.Term>}:
  match b:
    case False{}:
      Mb.ns(Bk.Term, t, {Tm.at.b(b2, f2, m2, ks, img, K, F, X2, N2, c, cell) == Some{t} : Maybe<&2, Bk.Term>}, h)
    case True{}:
      %eb : {Tm.at.b(_, f2, m2, ks, img, K, F, X2, N2, c, cell) == Some{t} : Maybe<&2, Bk.Term>}
      +f0 = Cr.Cir.Cell.get(0n, cell)
      +tag = U32.to_nat(U32.and(f0, 63))
      +q = T.tm.quan(U32.and(U32.shrn(f0, 6n), 3))
      Tm.chk.cg(tag, U32.shrn(f0, 13n),
        T.tm.cell(tag, q, c, Cr.Cir.Cell.get(2n, cell), ks, img,
          u => D.Tm(f, m, ks, img, K, F, X, N, Cr.Cir.Cell.get(2n, cell)), u => D.Tm(f, m, ks, img, K, F, X, N, Cr.Cir.Cell.get(3n, cell)),
          u => D.Tm(f, m, ks, img, K, F, X, N, Cr.Cir.Cell.get(4n, cell))),
        T.tm.cell(tag, q, c, Cr.Cir.Cell.get(2n, cell), ks, img,
          u => D.Tm(f2, m2, ks, img, K, F, X2, N2, Cr.Cir.Cell.get(2n, cell)), u => D.Tm(f2, m2, ks, img, K, F, X2, N2, Cr.Cir.Cell.get(3n, cell)),
          u => D.Tm(f2, m2, ks, img, K, F, X2, N2, Cr.Cir.Cell.get(4n, cell))),
        t, h,
        a => ha => Cg(tag, q, c, Cr.Cir.Cell.get(2n, cell), ks, img,
          u => D.Tm(f, m, ks, img, K, F, X, N, Cr.Cir.Cell.get(2n, cell)), u => D.Tm(f, m, ks, img, K, F, X, N, Cr.Cir.Cell.get(3n, cell)),
          u => D.Tm(f, m, ks, img, K, F, X, N, Cr.Cir.Cell.get(4n, cell)),
          u => D.Tm(f2, m2, ks, img, K, F, X2, N2, Cr.Cir.Cell.get(2n, cell)), u => D.Tm(f2, m2, ks, img, K, F, X2, N2, Cr.Cir.Cell.get(3n, cell)),
          u => D.Tm(f2, m2, ks, img, K, F, X2, N2, Cr.Cir.Cell.get(4n, cell)), a, ha, g2, g3, g4))

# writing a cell i that may not be read keeps a checked term
def Tm.wx(f: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +K: U32, +F: U32,
  +X: List<&2, U32>, +N: U32, +c: U32, +i: U32, +x: Cr.Cir.Cell, -t: Bk.Term, +hi: {False{} == D.Al(K, F, X, N, i) : Bool},
  +h: {D.Tm(f, m, ks, img, K, F, X, N, c) == Some{t} : Maybe<&2, Bk.Term>}) ->
  {D.Tm(f, Cr.Cir.Cells.set(m, i, x), ks, img, K, F, X, N, c) == Some{t} : Maybe<&2, Bk.Term>}:
  match f:
    case 0n:
      Mb.ns(Bk.Term, t, {D.Tm(0n, Cr.Cir.Cells.set(m, i, x), ks, img, K, F, X, N, c) == Some{t} : Maybe<&2, Bk.Term>}, h)
    case 1n+(+p):
      +m2 = Cr.Cir.Cells.set(m, i, x)
      +cell = Cr.Cir.Cells.get(m, c)
      +ha = Tm.al.if(D.Al(K, F, X, N, c), p, m, ks, img, K, F, X, N, c, cell, t, {==}, h)
      +ne = Al.ne.if(U32.is_eq(c, i), K, F, X, N, c, i, {==}, ha, hi)
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(m2, c), cell, K.Cl.get_ne(m, c, i, x, ne)) :
        {Tm.at(p, m2, ks, img, K, F, X, N, c, _) == Some{t} : Maybe<&2, Bk.Term>}
      Tm.at.cg(D.Al(K, F, X, N, c), p, p, m, m2, ks, img, K, F, X, N, X, N, D.Al(K, F, X, N, c), c, cell, t, {==}, h,
        a => ha2 => Tm.wx(p, m, ks, img, K, F, X, N, Cr.Cir.Cell.get(2n, cell), i, x, a, hi, ha2),
        a => ha3 => Tm.wx(p, m, ks, img, K, F, X, N, Cr.Cir.Cell.get(3n, cell), i, x, a, hi, ha3),
        a => ha4 => Tm.wx(p, m, ks, img, K, F, X, N, Cr.Cir.Cell.get(4n, cell), i, x, a, hi, ha4))

# a count's write leaves the cell's term the same
def Tm.at.s1(+f: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +K: U32, +F: U32,
  +X: List<&2, U32>, +N: U32, +c: U32, cl: Cr.Cir.Cell, +v: U32) ->
  {Tm.at(f, m, ks, img, K, F, X, N, c, cl) == Tm.at(f, m, ks, img, K, F, X, N, c, Cr.Cir.Cell.set(1n, cl, v)) : Maybe<&2, Bk.Term>}:
  match cl:
    case Cr.Cir.Cell{+a, +b, +x, +y, +z}:
      {==}

# the cell c after a write of the count of i: c's cell, or i's with another count
def Tm.w1.cell(b: Bool, +f: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +K: U32, +F: U32,
  +X: List<&2, U32>, +N: U32, +c: U32, +i: U32, +v: U32, eb: {b == U32.is_eq(c, i) : Bool}) ->
  {Tm.at(f, Cr.Cir.Cells.set(m, i, Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, i), v)), ks, img, K, F, X, N, c, Cr.Cir.Cells.get(m, c)) ==
    Tm.at(f, Cr.Cir.Cells.set(m, i, Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, i), v)), ks, img, K, F, X, N, c,
      Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, i, Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, i), v)), c)) : Maybe<&2, Bk.Term>}:
  match b:
    case True{}:
      +m2 = Cr.Cir.Cells.set(m, i, Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, i), v))
      +e = K.U.eq(c, i, Equal.sym(Bool, True{}, U32.is_eq(c, i), eb))
      %Equal.sym(U32, c, i, e) : {Tm.at(f, m2, ks, img, K, F, X, N, c, Cr.Cir.Cells.get(m, _)) == Tm.at(f, m2, ks, img, K, F, X, N, c, Cr.Cir.Cells.get(m2, _)) : Maybe<&2, Bk.Term>}
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(m2, i), Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, i), v), K.Cl.get_set(m, i, Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, i), v))) :
        {Tm.at(f, m2, ks, img, K, F, X, N, c, Cr.Cir.Cells.get(m, i)) == Tm.at(f, m2, ks, img, K, F, X, N, c, _) : Maybe<&2, Bk.Term>}
      Tm.at.s1(f, m2, ks, img, K, F, X, N, c, Cr.Cir.Cells.get(m, i), v)
    case False{}:
      +m2 = Cr.Cir.Cells.set(m, i, Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, i), v))
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(m2, c), Cr.Cir.Cells.get(m, c), K.Cl.get_ne(m, c, i, Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, i), v), Equal.sym(Bool, False{}, U32.is_eq(c, i), eb))) :
        {Tm.at(f, m2, ks, img, K, F, X, N, c, Cr.Cir.Cells.get(m, c)) == Tm.at(f, m2, ks, img, K, F, X, N, c, _) : Maybe<&2, Bk.Term>}
      {==}

# writing the count of any cell i keeps a checked term: no term reads it
def Tm.w1(f: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +K: U32, +F: U32,
  +X: List<&2, U32>, +N: U32, +c: U32, +i: U32, +v: U32, -t: Bk.Term,
  +h: {D.Tm(f, m, ks, img, K, F, X, N, c) == Some{t} : Maybe<&2, Bk.Term>}) ->
  {D.Tm(f, Cr.Cir.Cells.set(m, i, Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, i), v)), ks, img, K, F, X, N, c) == Some{t} : Maybe<&2, Bk.Term>}:
  match f:
    case 0n:
      Mb.ns(Bk.Term, t, {D.Tm(0n, Cr.Cir.Cells.set(m, i, Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, i), v)), ks, img, K, F, X, N, c) == Some{t} : Maybe<&2, Bk.Term>}, h)
    case 1n+(+p):
      +m2 = Cr.Cir.Cells.set(m, i, Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, i), v))
      +cell = Cr.Cir.Cells.get(m, c)
      %Tm.w1.cell(U32.is_eq(c, i), p, m, ks, img, K, F, X, N, c, i, v, {==}) :
        {_ == Some{t} : Maybe<&2, Bk.Term>}
      Tm.at.cg(D.Al(K, F, X, N, c), p, p, m, m2, ks, img, K, F, X, N, X, N, D.Al(K, F, X, N, c), c, cell, t, {==}, h,
        a => ha2 => Tm.w1(p, m, ks, img, K, F, X, N, Cr.Cir.Cell.get(2n, cell), i, v, a, ha2),
        a => ha3 => Tm.w1(p, m, ks, img, K, F, X, N, Cr.Cir.Cell.get(3n, cell), i, v, a, ha3),
        a => ha4 => Tm.w1(p, m, ks, img, K, F, X, N, Cr.Cir.Cell.get(4n, cell), i, v, a, ha4))

# more fuel keeps a checked term
def Tm.lift(f: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +K: U32, +F: U32,
  +X: List<&2, U32>, +N: U32, +c: U32, -t: Bk.Term, +h: {D.Tm(f, m, ks, img, K, F, X, N, c) == Some{t} : Maybe<&2, Bk.Term>}) ->
  {D.Tm(1n+f, m, ks, img, K, F, X, N, c) == Some{t} : Maybe<&2, Bk.Term>}:
  match f:
    case 0n:
      Mb.ns(Bk.Term, t, {D.Tm(1n, m, ks, img, K, F, X, N, c) == Some{t} : Maybe<&2, Bk.Term>}, h)
    case 1n+(+p):
      +cell = Cr.Cir.Cells.get(m, c)
      Tm.at.cg(D.Al(K, F, X, N, c), p, 1n+p, m, m, ks, img, K, F, X, N, X, N, D.Al(K, F, X, N, c), c, cell, t, {==}, h,
        a => ha2 => Tm.lift(p, m, ks, img, K, F, X, N, Cr.Cir.Cell.get(2n, cell), a, ha2),
        a => ha3 => Tm.lift(p, m, ks, img, K, F, X, N, Cr.Cir.Cell.get(3n, cell), a, ha3),
        a => ha4 => Tm.lift(p, m, ks, img, K, F, X, N, Cr.Cir.Cell.get(4n, cell), a, ha4))

def Tm.chk.inv.ok(b: Bool, +a: Bk.Term, -t: Bk.Term, h: {D.Tm.ok(b, a) == Some{t} : Maybe<&2, Bk.Term>}) -> {Some{a} == Some{t} : Maybe<&2, Bk.Term>}:
  match b:
    case True{}:
      h
    case False{}:
      Mb.ns(Bk.Term, t, {Some{a} == Some{t} : Maybe<&2, Bk.Term>}, h)

# Tm.chk keeps only the terms that its part gives
def Tm.chk.inv(+tag: Nat, +fvf: U32, r: Maybe<&2, Bk.Term>, -t: Bk.Term, h: {D.Tm.chk(tag, fvf, r) == Some{t} : Maybe<&2, Bk.Term>}) ->
  {r == Some{t} : Maybe<&2, Bk.Term>}:
  match r:
    case None{}:
      Mb.ns(Bk.Term, t, {None{} == Some{t} : Maybe<&2, Bk.Term>}, h)
    case Some{+a}:
      Tm.chk.inv.ok(D.FvOK(tag, fvf, a), a, t, h)

# the cell's term by T.tm.of, at a cell that Tm reads, from parts that give what Tm gave
def Tm.of.at(b: Bool, +f: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +K: U32, +F: U32,
  +X: List<&2, U32>, +N: U32, +c: U32, +cell: Cr.Cir.Cell, -t: Bk.Term,
  h: {Tm.at.b(b, f, m, ks, img, K, F, X, N, c, cell) == Some{t} : Maybe<&2, Bk.Term>},
  g2: Pt(u => D.Tm(f, m, ks, img, K, F, X, N, Cr.Cir.Cell.get(2n, cell)), u => T.tm.of(f, m, ks, img, Cr.Cir.Cell.get(2n, cell))),
  g3: Pt(u => D.Tm(f, m, ks, img, K, F, X, N, Cr.Cir.Cell.get(3n, cell)), u => T.tm.of(f, m, ks, img, Cr.Cir.Cell.get(3n, cell))),
  g4: Pt(u => D.Tm(f, m, ks, img, K, F, X, N, Cr.Cir.Cell.get(4n, cell)), u => T.tm.of(f, m, ks, img, Cr.Cir.Cell.get(4n, cell)))) ->
  {T.tm.cell(U32.to_nat(U32.and(Cr.Cir.Cell.get(0n, cell), 63)), T.tm.quan(U32.and(U32.shrn(Cr.Cir.Cell.get(0n, cell), 6n), 3)), c,
    Cr.Cir.Cell.get(2n, cell), ks, img, u => T.tm.of(f, m, ks, img, Cr.Cir.Cell.get(2n, cell)), u => T.tm.of(f, m, ks, img, Cr.Cir.Cell.get(3n, cell)),
    u => T.tm.of(f, m, ks, img, Cr.Cir.Cell.get(4n, cell))) == Some{t} : Maybe<&2, Bk.Term>}:
  match b:
    case False{}:
      +f0 = Cr.Cir.Cell.get(0n, cell)
      +tag = U32.to_nat(U32.and(f0, 63))
      +q = T.tm.quan(U32.and(U32.shrn(f0, 6n), 3))
      Mb.ns(Bk.Term, t, {T.tm.cell(tag, q, c, Cr.Cir.Cell.get(2n, cell), ks, img, u => T.tm.of(f, m, ks, img, Cr.Cir.Cell.get(2n, cell)),
        u => T.tm.of(f, m, ks, img, Cr.Cir.Cell.get(3n, cell)), u => T.tm.of(f, m, ks, img, Cr.Cir.Cell.get(4n, cell))) == Some{t} : Maybe<&2, Bk.Term>}, h)
    case True{}:
      +f0 = Cr.Cir.Cell.get(0n, cell)
      +tag = U32.to_nat(U32.and(f0, 63))
      +q = T.tm.quan(U32.and(U32.shrn(f0, 6n), 3))
      Cg(tag, q, c, Cr.Cir.Cell.get(2n, cell), ks, img,
        u => D.Tm(f, m, ks, img, K, F, X, N, Cr.Cir.Cell.get(2n, cell)), u => D.Tm(f, m, ks, img, K, F, X, N, Cr.Cir.Cell.get(3n, cell)),
        u => D.Tm(f, m, ks, img, K, F, X, N, Cr.Cir.Cell.get(4n, cell)),
        u => T.tm.of(f, m, ks, img, Cr.Cir.Cell.get(2n, cell)), u => T.tm.of(f, m, ks, img, Cr.Cir.Cell.get(3n, cell)),
        u => T.tm.of(f, m, ks, img, Cr.Cir.Cell.get(4n, cell)), t,
        Tm.chk.inv(tag, U32.shrn(f0, 13n), T.tm.cell(tag, q, c, Cr.Cir.Cell.get(2n, cell), ks, img,
          u => D.Tm(f, m, ks, img, K, F, X, N, Cr.Cir.Cell.get(2n, cell)), u => D.Tm(f, m, ks, img, K, F, X, N, Cr.Cir.Cell.get(3n, cell)),
          u => D.Tm(f, m, ks, img, K, F, X, N, Cr.Cir.Cell.get(4n, cell))), t, h), g2, g3, g4)

# a checked term is the cell's term by T.tm.of (cell_terms.bend)
def Tm.of(f: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +K: U32, +F: U32,
  +X: List<&2, U32>, +N: U32, +c: U32, -t: Bk.Term, +h: {D.Tm(f, m, ks, img, K, F, X, N, c) == Some{t} : Maybe<&2, Bk.Term>}) ->
  {T.tm.of(f, m, ks, img, c) == Some{t} : Maybe<&2, Bk.Term>}:
  match f:
    case 0n:
      Mb.ns(Bk.Term, t, {T.tm.of(0n, m, ks, img, c) == Some{t} : Maybe<&2, Bk.Term>}, h)
    case 1n+(+p):
      +cell = Cr.Cir.Cells.get(m, c)
      Tm.of.at(D.Al(K, F, X, N, c), p, m, ks, img, K, F, X, N, c, cell, t, h,
        a => ha2 => Tm.of(p, m, ks, img, K, F, X, N, Cr.Cir.Cell.get(2n, cell), a, ha2),
        a => ha3 => Tm.of(p, m, ks, img, K, F, X, N, Cr.Cir.Cell.get(3n, cell), a, ha3),
        a => ha4 => Tm.of(p, m, ks, img, K, F, X, N, Cr.Cir.Cell.get(4n, cell), a, ha4))

# More cells that may be read
# ---------------------------

def Has.incl.if(b: Bool, +z: U32, rest: List<&2, U32>, +X: List<&2, U32>, +N: U32, +y: U32, +eb: {b == U32.is_eq(z, y) : Bool},
  +hz: {Bool.or(D.Has(X, z), U32.is_le(N, z)) == True{} : Bool},
  hr: {D.Has(rest, y) == True{} : Bool} -> {Bool.or(D.Has(X, y), U32.is_le(N, y)) == True{} : Bool},
  +hy: {Bool.or(b, D.Has(rest, y)) == True{} : Bool}) -> {Bool.or(D.Has(X, y), U32.is_le(N, y)) == True{} : Bool}:
  match b:
    case True{}:
      +e = K.U.eq(z, y, Equal.sym(Bool, True{}, U32.is_eq(z, y), eb))
      %e : {Bool.or(D.Has(X, _), U32.is_le(N, _)) == True{} : Bool}
      hz
    case False{}:
      hr(hy)

# a cell of X2 is one of X or from N on
def Has.incl(X2: List<&2, U32>, +X: List<&2, U32>, +N: U32, +y: U32, +hi: {D.Incl.go(X2, X, N) == True{} : Bool},
  +hy: {D.Has(X2, y) == True{} : Bool}) -> {Bool.or(D.Has(X, y), U32.is_le(N, y)) == True{} : Bool}:
  match X2:
    case Nil{}:
      K.Bo.tf({Bool.or(D.Has(X, y), U32.is_le(N, y)) == True{} : Bool}, hy)
    case Con{+z, +rest}:
      Has.incl.if(U32.is_eq(z, y), z, rest, X, N, y, {==},
        K.Bo.and_l(Bool.or(D.Has(X, z), U32.is_le(N, z)), D.Incl.go(rest, X, N), hi),
        k => Has.incl(rest, X, N, y, K.Bo.and_r(Bool.or(D.Has(X, z), U32.is_le(N, z)), D.Incl.go(rest, X, N), hi), k), hy)

def Al.incl.cell(b: Bool, +K: U32, +F: U32, +N: U32, +N2: U32, +x: U32, +eb: {b == Bool.and(Bool.not(U32.is_zero(x)), U32.is_le(x, K)) : Bool},
  +ic: {Bool.or(b, Bool.and(U32.is_le(F, x), U32.is_lt(x, N))) == True{} : Bool}, +hn: {U32.is_le(N, N2) == True{} : Bool}) ->
  {Cr.Cir.is_cell(x, K, F, N2) == True{} : Bool}:
  match b:
    case True{}:
      %eb : {Bool.or(_, Bool.and(U32.is_le(F, x), U32.is_lt(x, N2))) == True{} : Bool}
      {==}
    case False{}:
      %eb : {Bool.or(_, Bool.and(U32.is_le(F, x), U32.is_lt(x, N2))) == True{} : Bool}
      K.Bo.and_i(U32.is_le(F, x), U32.is_lt(x, N2), K.Bo.and_l(U32.is_le(F, x), U32.is_lt(x, N), ic),
        K.U.lt_le(x, N, N2, K.Bo.and_r(U32.is_le(F, x), U32.is_lt(x, N), ic), hn))

def Al.incl.has.c(c: Bool, +K: U32, +F: U32, +N: U32, +x: U32, +ec: {c == Bool.and(Bool.not(U32.is_zero(x)), U32.is_le(x, K)) : Bool},
  +ic: {Bool.or(c, Bool.and(U32.is_le(F, x), U32.is_lt(x, N))) == True{} : Bool}, +hkn: {U32.is_lt(K, N) == True{} : Bool},
  +le: {U32.is_le(N, x) == True{} : Bool}) -> {True{} == False{} : Bool}:
  match c:
    case True{}:
      +xk = K.Bo.and_r(Bool.not(U32.is_zero(x)), U32.is_le(x, K), Equal.sym(Bool, True{}, Bool.and(Bool.not(U32.is_zero(x)), U32.is_le(x, K)), ec))
      K.U.lt_ge(x, N, {True{} == False{} : Bool}, K.U.le_lt(x, K, N, xk, hkn), le)
    case False{}:
      K.U.lt_ge(x, N, {True{} == False{} : Bool}, K.Bo.and_r(U32.is_le(F, x), U32.is_lt(x, N), ic), le)

def Al.incl.has(b: Bool, c: Bool, +K: U32, +F: U32, +N: U32, +x: U32, +ec: {c == Bool.and(Bool.not(U32.is_zero(x)), U32.is_le(x, K)) : Bool},
  +ic: {Bool.or(c, Bool.and(U32.is_le(F, x), U32.is_lt(x, N))) == True{} : Bool}, +hkn: {U32.is_lt(K, N) == True{} : Bool},
  hnx: {b == True{} : Bool} -> {U32.is_le(N, x) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Al.incl.has.c(c, K, F, N, x, ec, ic, hkn, hnx({==}))

# a cell that may be read still may once more cells may be read
def Al.incl(+K: U32, +F: U32, +X: List<&2, U32>, +N: U32, +X2: List<&2, U32>, +N2: U32, +x: U32,
  +hin: {D.Incl(X, N, X2, N2) == True{} : Bool}, +hkn: {U32.is_lt(K, N) == True{} : Bool},
  +ha: {D.Al(K, F, X, N, x) == True{} : Bool}) -> {D.Al(K, F, X2, N2, x) == True{} : Bool}:
  +ic = K.Bo.and_l(Cr.Cir.is_cell(x, K, F, N), Bool.and(Bool.not(D.Has(X, x)), Bool.not(D.Tbc(x))), ha)
  +rest = K.Bo.and_r(Cr.Cir.is_cell(x, K, F, N), Bool.and(Bool.not(D.Has(X, x)), Bool.not(D.Tbc(x))), ha)
  +nh = K.Bo.not_t(D.Has(X, x), K.Bo.and_l(Bool.not(D.Has(X, x)), Bool.not(D.Tbc(x)), rest))
  +nt = K.Bo.and_r(Bool.not(D.Has(X, x)), Bool.not(D.Tbc(x)), rest)
  +hn = K.Bo.and_l(U32.is_le(N, N2), D.Incl.go(X2, X, N), hin)
  +hg = K.Bo.and_r(U32.is_le(N, N2), D.Incl.go(X2, X, N), hin)
  +b1 = Bool.and(Bool.not(U32.is_zero(x)), U32.is_le(x, K))
  +ic2 = Al.incl.cell(b1, K, F, N, N2, x, {==}, ic, hn)
  +nh2 = Al.incl.has(D.Has(X2, x), b1, K, F, N, x, {==}, ic, hkn,
    k => K.Bo.or_r(D.Has(X, x), U32.is_le(N, x), Has.incl(X2, X, N, x, hg, k), nh))
  K.Bo.and_i(Cr.Cir.is_cell(x, K, F, N2), Bool.and(Bool.not(D.Has(X2, x)), Bool.not(D.Tbc(x))), ic2,
    K.Bo.and_i(Bool.not(D.Has(X2, x)), Bool.not(D.Tbc(x)), K.Bo.not_i(D.Has(X2, x), nh2), nt))

# more cells that may be read keep a checked term
def Tm.mono(f: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +K: U32, +F: U32,
  +X: List<&2, U32>, +N: U32, +X2: List<&2, U32>, +N2: U32, +c: U32, -t: Bk.Term,
  +hin: {D.Incl(X, N, X2, N2) == True{} : Bool}, +hkn: {U32.is_lt(K, N) == True{} : Bool},
  +h: {D.Tm(f, m, ks, img, K, F, X, N, c) == Some{t} : Maybe<&2, Bk.Term>}) ->
  {D.Tm(f, m, ks, img, K, F, X2, N2, c) == Some{t} : Maybe<&2, Bk.Term>}:
  match f:
    case 0n:
      Mb.ns(Bk.Term, t, {D.Tm(0n, m, ks, img, K, F, X2, N2, c) == Some{t} : Maybe<&2, Bk.Term>}, h)
    case 1n+(+p):
      +cell = Cr.Cir.Cells.get(m, c)
      +ha = Tm.al.if(D.Al(K, F, X, N, c), p, m, ks, img, K, F, X, N, c, cell, t, {==}, h)
      +ha2 = Al.incl(K, F, X, N, X2, N2, c, hin, hkn, ha)
      Tm.at.cg(D.Al(K, F, X, N, c), p, p, m, m, ks, img, K, F, X, N, X2, N2, D.Al(K, F, X2, N2, c), c, cell, t,
        Equal.trans(Bool, D.Al(K, F, X, N, c), True{}, D.Al(K, F, X2, N2, c), ha, Equal.sym(Bool, D.Al(K, F, X2, N2, c), True{}, ha2)), h,
        a => k2 => Tm.mono(p, m, ks, img, K, F, X, N, X2, N2, Cr.Cir.Cell.get(2n, cell), a, hin, hkn, k2),
        a => k3 => Tm.mono(p, m, ks, img, K, F, X, N, X2, N2, Cr.Cir.Cell.get(3n, cell), a, hin, hkn, k3),
        a => k4 => Tm.mono(p, m, ks, img, K, F, X, N, X2, N2, Cr.Cir.Cell.get(4n, cell), a, hin, hkn, k4))

# Stores away from a term's nodes
# -------------------------------

def Or.cong2(-a1: Bool, -a2: Bool, -b1: Bool, -b2: Bool, e1: {a1 == a2 : Bool}, e2: {b1 == b2 : Bool}) ->
  {Bool.or(a1, b1) == Bool.or(a2, b2) : Bool}:
  %e1 : {Bool.or(a1, b1) == Bool.or(_, b2) : Bool}
  %e2 : {Bool.or(a1, b1) == Bool.or(a1, _) : Bool}
  {==}

# one part's node equality, before and after its root's field is read
def node.child(t: Bk.Term, +m: Cr.Cir.Cells, +z: U32, +xc: Cr.Cir.Cell, +r: U32, +x: U32, +k: Nat,
  ne: {U32.is_eq(r, z) == False{} : Bool},
  ih: {D.Node(t, Cr.Cir.Cells.set(m, z, xc), D.Fd(k, m, r), x) == D.Node(t, m, D.Fd(k, m, r), x) : Bool}) ->
  {D.Node(t, Cr.Cir.Cells.set(m, z, xc), D.Fd(k, Cr.Cir.Cells.set(m, z, xc), r), x) == D.Node(t, m, D.Fd(k, m, r), x) : Bool}:
  +M2 = Cr.Cir.Cells.set(m, z, xc)
  Equal.trans(Bool, D.Node(t, M2, D.Fd(k, M2, r), x), D.Node(t, M2, D.Fd(k, m, r), x), D.Node(t, m, D.Fd(k, m, r), x),
    Equal.cong(U32, Bool, w => D.Node(t, M2, w, x), D.Fd(k, M2, r), D.Fd(k, m, r),
      Equal.cong(Cr.Cir.Cell, U32, w => Cr.Cir.Cell.get(k, w), Cr.Cir.Cells.get(M2, r), Cr.Cir.Cells.get(m, r), K.Cl.get_ne(m, r, z, xc, ne))),
    ih)

# a store at a cell z that is no node of t at r keeps the nodes of t
def node.set(t: Bk.Term, +m: Cr.Cir.Cells, +z: U32, +xc: Cr.Cir.Cell, +r: U32, +x: U32, hn: {D.Node(t, m, r, z) == False{} : Bool}) ->
  {D.Node(t, Cr.Cir.Cells.set(m, z, xc), r, x) == D.Node(t, m, r, x) : Bool}:
  match t:
    case Bk.Term.Var{+i}:
      {==}
    case Bk.Term.Ref{+k}:
      {==}
    case Bk.Term.Ann{+y, +y2}:
      +M2 = Cr.Cir.Cells.set(m, z, xc)
      +hn2 = hn
      +ner = K.or.fl(U32.is_eq(r, z), Bool.or(D.Node(y, m, D.Fd(2n, m, r), z), D.Node(y2, m, D.Fd(3n, m, r), z)), hn2)
      +nrest = K.or.fr(U32.is_eq(r, z), Bool.or(D.Node(y, m, D.Fd(2n, m, r), z), D.Node(y2, m, D.Fd(3n, m, r), z)), hn2)
      +hp0 = K.or.fl(D.Node(y, m, D.Fd(2n, m, r), z), D.Node(y2, m, D.Fd(3n, m, r), z), nrest)
      +hq0 = K.or.fr(D.Node(y, m, D.Fd(2n, m, r), z), D.Node(y2, m, D.Fd(3n, m, r), z), nrest)
      Equal.cong(Bool, Bool, w => Bool.or(U32.is_eq(r, x), w), Bool.or(D.Node(y, M2, D.Fd(2n, M2, r), x), D.Node(y2, M2, D.Fd(3n, M2, r), x)), Bool.or(D.Node(y, m, D.Fd(2n, m, r), x), D.Node(y2, m, D.Fd(3n, m, r), x)),
        Or.cong2(D.Node(y, M2, D.Fd(2n, M2, r), x), D.Node(y, m, D.Fd(2n, m, r), x), D.Node(y2, M2, D.Fd(3n, M2, r), x), D.Node(y2, m, D.Fd(3n, m, r), x),
          node.child(y, m, z, xc, r, x, 2n, ner, node.set(y, m, z, xc, D.Fd(2n, m, r), x, hp0)),
          node.child(y2, m, z, xc, r, x, 3n, ner, node.set(y2, m, z, xc, D.Fd(3n, m, r), x, hq0))))
    case Bk.Term.Let{+q, +v, +f}:
      +M2 = Cr.Cir.Cells.set(m, z, xc)
      +hn2 = hn
      +ner = K.or.fl(U32.is_eq(r, z), Bool.or(D.Node(v, m, D.Fd(2n, m, r), z), D.Node(f, m, D.Fd(3n, m, r), z)), hn2)
      +nrest = K.or.fr(U32.is_eq(r, z), Bool.or(D.Node(v, m, D.Fd(2n, m, r), z), D.Node(f, m, D.Fd(3n, m, r), z)), hn2)
      +hp0 = K.or.fl(D.Node(v, m, D.Fd(2n, m, r), z), D.Node(f, m, D.Fd(3n, m, r), z), nrest)
      +hq0 = K.or.fr(D.Node(v, m, D.Fd(2n, m, r), z), D.Node(f, m, D.Fd(3n, m, r), z), nrest)
      Equal.cong(Bool, Bool, w => Bool.or(U32.is_eq(r, x), w), Bool.or(D.Node(v, M2, D.Fd(2n, M2, r), x), D.Node(f, M2, D.Fd(3n, M2, r), x)), Bool.or(D.Node(v, m, D.Fd(2n, m, r), x), D.Node(f, m, D.Fd(3n, m, r), x)),
        Or.cong2(D.Node(v, M2, D.Fd(2n, M2, r), x), D.Node(v, m, D.Fd(2n, m, r), x), D.Node(f, M2, D.Fd(3n, M2, r), x), D.Node(f, m, D.Fd(3n, m, r), x),
          node.child(v, m, z, xc, r, x, 2n, ner, node.set(v, m, z, xc, D.Fd(2n, m, r), x, hp0)),
          node.child(f, m, z, xc, r, x, 3n, ner, node.set(f, m, z, xc, D.Fd(3n, m, r), x, hq0))))
    case Bk.Term.Typ{+y}:
      +M2 = Cr.Cir.Cells.set(m, z, xc)
      +hn2 = hn
      +ner = K.or.fl(U32.is_eq(r, z), D.Node(y, m, D.Fd(2n, m, r), z), hn2)
      +nrest = K.or.fr(U32.is_eq(r, z), D.Node(y, m, D.Fd(2n, m, r), z), hn2)
      Equal.cong(Bool, Bool, w => Bool.or(U32.is_eq(r, x), w), D.Node(y, M2, D.Fd(2n, M2, r), x), D.Node(y, m, D.Fd(2n, m, r), x),
        node.child(y, m, z, xc, r, x, 2n, ner, node.set(y, m, z, xc, D.Fd(2n, m, r), x, nrest)))
    case Bk.Term.Min{+a, +b}:
      +M2 = Cr.Cir.Cells.set(m, z, xc)
      +hn2 = hn
      +ner = K.or.fl(U32.is_eq(r, z), Bool.or(D.Node(a, m, D.Fd(2n, m, r), z), D.Node(b, m, D.Fd(3n, m, r), z)), hn2)
      +nrest = K.or.fr(U32.is_eq(r, z), Bool.or(D.Node(a, m, D.Fd(2n, m, r), z), D.Node(b, m, D.Fd(3n, m, r), z)), hn2)
      +hp0 = K.or.fl(D.Node(a, m, D.Fd(2n, m, r), z), D.Node(b, m, D.Fd(3n, m, r), z), nrest)
      +hq0 = K.or.fr(D.Node(a, m, D.Fd(2n, m, r), z), D.Node(b, m, D.Fd(3n, m, r), z), nrest)
      Equal.cong(Bool, Bool, w => Bool.or(U32.is_eq(r, x), w), Bool.or(D.Node(a, M2, D.Fd(2n, M2, r), x), D.Node(b, M2, D.Fd(3n, M2, r), x)), Bool.or(D.Node(a, m, D.Fd(2n, m, r), x), D.Node(b, m, D.Fd(3n, m, r), x)),
        Or.cong2(D.Node(a, M2, D.Fd(2n, M2, r), x), D.Node(a, m, D.Fd(2n, m, r), x), D.Node(b, M2, D.Fd(3n, M2, r), x), D.Node(b, m, D.Fd(3n, m, r), x),
          node.child(a, m, z, xc, r, x, 2n, ner, node.set(a, m, z, xc, D.Fd(2n, m, r), x, hp0)),
          node.child(b, m, z, xc, r, x, 3n, ner, node.set(b, m, z, xc, D.Fd(3n, m, r), x, hq0))))
    case Bk.Term.All{+q, +a, +b}:
      +M2 = Cr.Cir.Cells.set(m, z, xc)
      +hn2 = hn
      +ner = K.or.fl(U32.is_eq(r, z), Bool.or(D.Node(a, m, D.Fd(2n, m, r), z), D.Node(b, m, D.Fd(3n, m, r), z)), hn2)
      +nrest = K.or.fr(U32.is_eq(r, z), Bool.or(D.Node(a, m, D.Fd(2n, m, r), z), D.Node(b, m, D.Fd(3n, m, r), z)), hn2)
      +hp0 = K.or.fl(D.Node(a, m, D.Fd(2n, m, r), z), D.Node(b, m, D.Fd(3n, m, r), z), nrest)
      +hq0 = K.or.fr(D.Node(a, m, D.Fd(2n, m, r), z), D.Node(b, m, D.Fd(3n, m, r), z), nrest)
      Equal.cong(Bool, Bool, w => Bool.or(U32.is_eq(r, x), w), Bool.or(D.Node(a, M2, D.Fd(2n, M2, r), x), D.Node(b, M2, D.Fd(3n, M2, r), x)), Bool.or(D.Node(a, m, D.Fd(2n, m, r), x), D.Node(b, m, D.Fd(3n, m, r), x)),
        Or.cong2(D.Node(a, M2, D.Fd(2n, M2, r), x), D.Node(a, m, D.Fd(2n, m, r), x), D.Node(b, M2, D.Fd(3n, M2, r), x), D.Node(b, m, D.Fd(3n, m, r), x),
          node.child(a, m, z, xc, r, x, 2n, ner, node.set(a, m, z, xc, D.Fd(2n, m, r), x, hp0)),
          node.child(b, m, z, xc, r, x, 3n, ner, node.set(b, m, z, xc, D.Fd(3n, m, r), x, hq0))))
    case Bk.Term.Lam{+q, +f}:
      +M2 = Cr.Cir.Cells.set(m, z, xc)
      +hn2 = hn
      +ner = K.or.fl(U32.is_eq(r, z), D.Node(f, m, D.Fd(2n, m, r), z), hn2)
      +nrest = K.or.fr(U32.is_eq(r, z), D.Node(f, m, D.Fd(2n, m, r), z), hn2)
      Equal.cong(Bool, Bool, w => Bool.or(U32.is_eq(r, x), w), D.Node(f, M2, D.Fd(2n, M2, r), x), D.Node(f, m, D.Fd(2n, m, r), x),
        node.child(f, m, z, xc, r, x, 2n, ner, node.set(f, m, z, xc, D.Fd(2n, m, r), x, nrest)))
    case Bk.Term.App{+q, +f, +y}:
      +M2 = Cr.Cir.Cells.set(m, z, xc)
      +hn2 = hn
      +ner = K.or.fl(U32.is_eq(r, z), Bool.or(D.Node(f, m, D.Fd(2n, m, r), z), D.Node(y, m, D.Fd(3n, m, r), z)), hn2)
      +nrest = K.or.fr(U32.is_eq(r, z), Bool.or(D.Node(f, m, D.Fd(2n, m, r), z), D.Node(y, m, D.Fd(3n, m, r), z)), hn2)
      +hp0 = K.or.fl(D.Node(f, m, D.Fd(2n, m, r), z), D.Node(y, m, D.Fd(3n, m, r), z), nrest)
      +hq0 = K.or.fr(D.Node(f, m, D.Fd(2n, m, r), z), D.Node(y, m, D.Fd(3n, m, r), z), nrest)
      Equal.cong(Bool, Bool, w => Bool.or(U32.is_eq(r, x), w), Bool.or(D.Node(f, M2, D.Fd(2n, M2, r), x), D.Node(y, M2, D.Fd(3n, M2, r), x)), Bool.or(D.Node(f, m, D.Fd(2n, m, r), x), D.Node(y, m, D.Fd(3n, m, r), x)),
        Or.cong2(D.Node(f, M2, D.Fd(2n, M2, r), x), D.Node(f, m, D.Fd(2n, m, r), x), D.Node(y, M2, D.Fd(3n, M2, r), x), D.Node(y, m, D.Fd(3n, m, r), x),
          node.child(f, m, z, xc, r, x, 2n, ner, node.set(f, m, z, xc, D.Fd(2n, m, r), x, hp0)),
          node.child(y, m, z, xc, r, x, 3n, ner, node.set(y, m, z, xc, D.Fd(3n, m, r), x, hq0))))
    case Bk.Term.Sig{+q, +a, +b}:
      +M2 = Cr.Cir.Cells.set(m, z, xc)
      +hn2 = hn
      +ner = K.or.fl(U32.is_eq(r, z), Bool.or(D.Node(a, m, D.Fd(2n, m, r), z), D.Node(b, m, D.Fd(3n, m, r), z)), hn2)
      +nrest = K.or.fr(U32.is_eq(r, z), Bool.or(D.Node(a, m, D.Fd(2n, m, r), z), D.Node(b, m, D.Fd(3n, m, r), z)), hn2)
      +hp0 = K.or.fl(D.Node(a, m, D.Fd(2n, m, r), z), D.Node(b, m, D.Fd(3n, m, r), z), nrest)
      +hq0 = K.or.fr(D.Node(a, m, D.Fd(2n, m, r), z), D.Node(b, m, D.Fd(3n, m, r), z), nrest)
      Equal.cong(Bool, Bool, w => Bool.or(U32.is_eq(r, x), w), Bool.or(D.Node(a, M2, D.Fd(2n, M2, r), x), D.Node(b, M2, D.Fd(3n, M2, r), x)), Bool.or(D.Node(a, m, D.Fd(2n, m, r), x), D.Node(b, m, D.Fd(3n, m, r), x)),
        Or.cong2(D.Node(a, M2, D.Fd(2n, M2, r), x), D.Node(a, m, D.Fd(2n, m, r), x), D.Node(b, M2, D.Fd(3n, M2, r), x), D.Node(b, m, D.Fd(3n, m, r), x),
          node.child(a, m, z, xc, r, x, 2n, ner, node.set(a, m, z, xc, D.Fd(2n, m, r), x, hp0)),
          node.child(b, m, z, xc, r, x, 3n, ner, node.set(b, m, z, xc, D.Fd(3n, m, r), x, hq0))))
    case Bk.Term.Tup{+q, +a, +b}:
      +M2 = Cr.Cir.Cells.set(m, z, xc)
      +hn2 = hn
      +ner = K.or.fl(U32.is_eq(r, z), Bool.or(D.Node(a, m, D.Fd(2n, m, r), z), D.Node(b, m, D.Fd(3n, m, r), z)), hn2)
      +nrest = K.or.fr(U32.is_eq(r, z), Bool.or(D.Node(a, m, D.Fd(2n, m, r), z), D.Node(b, m, D.Fd(3n, m, r), z)), hn2)
      +hp0 = K.or.fl(D.Node(a, m, D.Fd(2n, m, r), z), D.Node(b, m, D.Fd(3n, m, r), z), nrest)
      +hq0 = K.or.fr(D.Node(a, m, D.Fd(2n, m, r), z), D.Node(b, m, D.Fd(3n, m, r), z), nrest)
      Equal.cong(Bool, Bool, w => Bool.or(U32.is_eq(r, x), w), Bool.or(D.Node(a, M2, D.Fd(2n, M2, r), x), D.Node(b, M2, D.Fd(3n, M2, r), x)), Bool.or(D.Node(a, m, D.Fd(2n, m, r), x), D.Node(b, m, D.Fd(3n, m, r), x)),
        Or.cong2(D.Node(a, M2, D.Fd(2n, M2, r), x), D.Node(a, m, D.Fd(2n, m, r), x), D.Node(b, M2, D.Fd(3n, M2, r), x), D.Node(b, m, D.Fd(3n, m, r), x),
          node.child(a, m, z, xc, r, x, 2n, ner, node.set(a, m, z, xc, D.Fd(2n, m, r), x, hp0)),
          node.child(b, m, z, xc, r, x, 3n, ner, node.set(b, m, z, xc, D.Fd(3n, m, r), x, hq0))))
    case Bk.Term.Prj{+h}:
      +M2 = Cr.Cir.Cells.set(m, z, xc)
      +hn2 = hn
      +ner = K.or.fl(U32.is_eq(r, z), D.Node(h, m, D.Fd(2n, m, r), z), hn2)
      +nrest = K.or.fr(U32.is_eq(r, z), D.Node(h, m, D.Fd(2n, m, r), z), hn2)
      Equal.cong(Bool, Bool, w => Bool.or(U32.is_eq(r, x), w), D.Node(h, M2, D.Fd(2n, M2, r), x), D.Node(h, m, D.Fd(2n, m, r), x),
        node.child(h, m, z, xc, r, x, 2n, ner, node.set(h, m, z, xc, D.Fd(2n, m, r), x, nrest)))
    case Bk.Term.Enu{+e}:
      {==}
    case Bk.Term.Lab{+k}:
      {==}
    case Bk.Term.Mat{+k, +h, +o}:
      +M2 = Cr.Cir.Cells.set(m, z, xc)
      +hn2 = hn
      +ner = K.or.fl(U32.is_eq(r, z), Bool.or(D.Node(h, m, D.Fd(3n, m, r), z), D.Node(o, m, D.Fd(4n, m, r), z)), hn2)
      +nrest = K.or.fr(U32.is_eq(r, z), Bool.or(D.Node(h, m, D.Fd(3n, m, r), z), D.Node(o, m, D.Fd(4n, m, r), z)), hn2)
      +hp0 = K.or.fl(D.Node(h, m, D.Fd(3n, m, r), z), D.Node(o, m, D.Fd(4n, m, r), z), nrest)
      +hq0 = K.or.fr(D.Node(h, m, D.Fd(3n, m, r), z), D.Node(o, m, D.Fd(4n, m, r), z), nrest)
      Equal.cong(Bool, Bool, w => Bool.or(U32.is_eq(r, x), w), Bool.or(D.Node(h, M2, D.Fd(3n, M2, r), x), D.Node(o, M2, D.Fd(4n, M2, r), x)), Bool.or(D.Node(h, m, D.Fd(3n, m, r), x), D.Node(o, m, D.Fd(4n, m, r), x)),
        Or.cong2(D.Node(h, M2, D.Fd(3n, M2, r), x), D.Node(h, m, D.Fd(3n, m, r), x), D.Node(o, M2, D.Fd(4n, M2, r), x), D.Node(o, m, D.Fd(4n, m, r), x),
          node.child(h, m, z, xc, r, x, 3n, ner, node.set(h, m, z, xc, D.Fd(3n, m, r), x, hp0)),
          node.child(o, m, z, xc, r, x, 4n, ner, node.set(o, m, z, xc, D.Fd(4n, m, r), x, hq0))))
    case Bk.Term.Efq{}:
      {==}
    case Bk.Term.Eql{+a, +b, +y}:
      +M2 = Cr.Cir.Cells.set(m, z, xc)
      +hn2 = hn
      +ner = K.or.fl(U32.is_eq(r, z), Bool.or(D.Node(a, m, D.Fd(2n, m, r), z), Bool.or(D.Node(b, m, D.Fd(3n, m, r), z), D.Node(y, m, D.Fd(4n, m, r), z))), hn2)
      +nrest = K.or.fr(U32.is_eq(r, z), Bool.or(D.Node(a, m, D.Fd(2n, m, r), z), Bool.or(D.Node(b, m, D.Fd(3n, m, r), z), D.Node(y, m, D.Fd(4n, m, r), z))), hn2)
      +hp0 = K.or.fl(D.Node(a, m, D.Fd(2n, m, r), z), Bool.or(D.Node(b, m, D.Fd(3n, m, r), z), D.Node(y, m, D.Fd(4n, m, r), z)), nrest)
      +hq0 = K.or.fr(D.Node(a, m, D.Fd(2n, m, r), z), Bool.or(D.Node(b, m, D.Fd(3n, m, r), z), D.Node(y, m, D.Fd(4n, m, r), z)), nrest)
      +hp1 = K.or.fl(D.Node(b, m, D.Fd(3n, m, r), z), D.Node(y, m, D.Fd(4n, m, r), z), hq0)
      +hq1 = K.or.fr(D.Node(b, m, D.Fd(3n, m, r), z), D.Node(y, m, D.Fd(4n, m, r), z), hq0)
      Equal.cong(Bool, Bool, w => Bool.or(U32.is_eq(r, x), w), Bool.or(D.Node(a, M2, D.Fd(2n, M2, r), x), Bool.or(D.Node(b, M2, D.Fd(3n, M2, r), x), D.Node(y, M2, D.Fd(4n, M2, r), x))), Bool.or(D.Node(a, m, D.Fd(2n, m, r), x), Bool.or(D.Node(b, m, D.Fd(3n, m, r), x), D.Node(y, m, D.Fd(4n, m, r), x))),
        Or.cong2(D.Node(a, M2, D.Fd(2n, M2, r), x), D.Node(a, m, D.Fd(2n, m, r), x), Bool.or(D.Node(b, M2, D.Fd(3n, M2, r), x), D.Node(y, M2, D.Fd(4n, M2, r), x)), Bool.or(D.Node(b, m, D.Fd(3n, m, r), x), D.Node(y, m, D.Fd(4n, m, r), x)),
          node.child(a, m, z, xc, r, x, 2n, ner, node.set(a, m, z, xc, D.Fd(2n, m, r), x, hp0)),
          Or.cong2(D.Node(b, M2, D.Fd(3n, M2, r), x), D.Node(b, m, D.Fd(3n, m, r), x), D.Node(y, M2, D.Fd(4n, M2, r), x), D.Node(y, m, D.Fd(4n, m, r), x),
            node.child(b, m, z, xc, r, x, 3n, ner, node.set(b, m, z, xc, D.Fd(3n, m, r), x, hp1)),
            node.child(y, m, z, xc, r, x, 4n, ner, node.set(y, m, z, xc, D.Fd(4n, m, r), x, hq1)))))
    case Bk.Term.Rfl{}:
      {==}
    case Bk.Term.Rwt{+e, +p, +f}:
      +M2 = Cr.Cir.Cells.set(m, z, xc)
      +hn2 = hn
      +ner = K.or.fl(U32.is_eq(r, z), Bool.or(D.Node(e, m, D.Fd(2n, m, r), z), Bool.or(D.Node(p, m, D.Fd(3n, m, r), z), D.Node(f, m, D.Fd(4n, m, r), z))), hn2)
      +nrest = K.or.fr(U32.is_eq(r, z), Bool.or(D.Node(e, m, D.Fd(2n, m, r), z), Bool.or(D.Node(p, m, D.Fd(3n, m, r), z), D.Node(f, m, D.Fd(4n, m, r), z))), hn2)
      +hp0 = K.or.fl(D.Node(e, m, D.Fd(2n, m, r), z), Bool.or(D.Node(p, m, D.Fd(3n, m, r), z), D.Node(f, m, D.Fd(4n, m, r), z)), nrest)
      +hq0 = K.or.fr(D.Node(e, m, D.Fd(2n, m, r), z), Bool.or(D.Node(p, m, D.Fd(3n, m, r), z), D.Node(f, m, D.Fd(4n, m, r), z)), nrest)
      +hp1 = K.or.fl(D.Node(p, m, D.Fd(3n, m, r), z), D.Node(f, m, D.Fd(4n, m, r), z), hq0)
      +hq1 = K.or.fr(D.Node(p, m, D.Fd(3n, m, r), z), D.Node(f, m, D.Fd(4n, m, r), z), hq0)
      Equal.cong(Bool, Bool, w => Bool.or(U32.is_eq(r, x), w), Bool.or(D.Node(e, M2, D.Fd(2n, M2, r), x), Bool.or(D.Node(p, M2, D.Fd(3n, M2, r), x), D.Node(f, M2, D.Fd(4n, M2, r), x))), Bool.or(D.Node(e, m, D.Fd(2n, m, r), x), Bool.or(D.Node(p, m, D.Fd(3n, m, r), x), D.Node(f, m, D.Fd(4n, m, r), x))),
        Or.cong2(D.Node(e, M2, D.Fd(2n, M2, r), x), D.Node(e, m, D.Fd(2n, m, r), x), Bool.or(D.Node(p, M2, D.Fd(3n, M2, r), x), D.Node(f, M2, D.Fd(4n, M2, r), x)), Bool.or(D.Node(p, m, D.Fd(3n, m, r), x), D.Node(f, m, D.Fd(4n, m, r), x)),
          node.child(e, m, z, xc, r, x, 2n, ner, node.set(e, m, z, xc, D.Fd(2n, m, r), x, hp0)),
          Or.cong2(D.Node(p, M2, D.Fd(3n, M2, r), x), D.Node(p, m, D.Fd(3n, m, r), x), D.Node(f, M2, D.Fd(4n, M2, r), x), D.Node(f, m, D.Fd(4n, m, r), x),
            node.child(p, m, z, xc, r, x, 3n, ner, node.set(p, m, z, xc, D.Fd(3n, m, r), x, hp1)),
            node.child(f, m, z, xc, r, x, 4n, ner, node.set(f, m, z, xc, D.Fd(4n, m, r), x, hq1)))))

# a store at a cell that is no node of any root keeps their nodes
def nodes.set(rs: List<&2, D.Rt>, +m: Cr.Cir.Cells, +z: U32, +xc: Cr.Cir.Cell, +x: U32, hn: {D.Nodes(rs, m, z) == False{} : Bool}) ->
  {D.Nodes(rs, Cr.Cir.Cells.set(m, z, xc), x) == D.Nodes(rs, m, x) : Bool}:
  match rs:
    case Nil{}:
      {==}
    case Con{D.Rt{_, +r, +u}, +rest}:
      +hn2 = hn
      Or.cong2(D.Node(u, Cr.Cir.Cells.set(m, z, xc), r, x), D.Node(u, m, r, x), D.Nodes(rest, Cr.Cir.Cells.set(m, z, xc), x), D.Nodes(rest, m, x),
        node.set(u, m, z, xc, r, x, K.or.fl(D.Node(u, m, r, z), D.Nodes(rest, m, z), hn2)),
        nodes.set(rest, m, z, xc, x, K.or.fr(D.Node(u, m, r, z), D.Nodes(rest, m, z), hn2)))

# the field of a root that is not the stored cell
def made.fd(+k: Nat, +ms: Cr.Cir.Cells, +r: U32, +z: U32, +xc: Cr.Cir.Cell, ne: {U32.is_eq(r, z) == False{} : Bool}) ->
  {D.Fd(k, Cr.Cir.Cells.set(ms, z, xc), r) == D.Fd(k, ms, r) : U32}:
  Equal.cong(Cr.Cir.Cell, U32, w => Cr.Cir.Cell.get(k, w), Cr.Cir.Cells.get(Cr.Cir.Cells.set(ms, z, xc), r), Cr.Cir.Cells.get(ms, r),
    K.Cl.get_ne(ms, r, z, xc, ne))

# a new copy's accounting reads only its own cell
def made.new(+ms: Cr.Cir.Cells, +T: List<&2, U32>, +r: U32, +tg: U32, +z: U32, +xc: Cr.Cir.Cell,
  +ne: {U32.is_eq(r, z) == False{} : Bool}, h: {D.New(ms, T, r, tg) == True{} : Bool}) ->
  {D.New(Cr.Cir.Cells.set(ms, z, xc), T, r, tg) == True{} : Bool}:
  +M2 = Cr.Cir.Cells.set(ms, z, xc)
  +e0 = made.fd(0n, ms, r, z, xc, ne)
  +e1 = made.fd(1n, ms, r, z, xc, ne)
  %Equal.sym(U32, D.Fd(0n, M2, r), D.Fd(0n, ms, r), e0) :
    {Bool.and(D.Has(T, r), Bool.and(U32.is_eq(D.Fd(1n, M2, r), 1), Bool.and(U32.is_zero(U32.and(_, 7936)),
      U32.is_eq(U32.and(_, 63), tg)))) == True{} : Bool}
  %Equal.sym(U32, D.Fd(1n, M2, r), D.Fd(1n, ms, r), e1) :
    {Bool.and(D.Has(T, r), Bool.and(U32.is_eq(_, 1), Bool.and(U32.is_zero(U32.and(D.Fd(0n, ms, r), 7936)),
      U32.is_eq(U32.and(D.Fd(0n, ms, r), 63), tg)))) == True{} : Bool}
  h

# a copied cell's comparison reads only its own cell in the new memory
def made.cpy(+ms: Cr.Cir.Cells, +m0: Cr.Cir.Cells, +S: List<&2, D.Rt>, +r: U32, +s: U32, +z: U32, +xc: Cr.Cir.Cell,
  +ne: {U32.is_eq(r, z) == False{} : Bool}, h: {D.Cpy(ms, m0, S, r, s) == True{} : Bool}) ->
  {D.Cpy(Cr.Cir.Cells.set(ms, z, xc), m0, S, r, s) == True{} : Bool}:
  +M2 = Cr.Cir.Cells.set(ms, z, xc)
  +e0 = made.fd(0n, ms, r, z, xc, ne)
  +e2 = made.fd(2n, ms, r, z, xc, ne)
  %Equal.sym(U32, D.Fd(0n, M2, r), D.Fd(0n, ms, r), e0) :
    {Bool.and(D.Nodes(S, m0, s), Bool.and(U32.is_eq(U32.and(_, 255), U32.and(D.Fd(0n, m0, s), 255)),
      Bool.or(Bool.not(Bool.or(U32.is_eq(U32.and(_, 63), 13), U32.is_eq(U32.and(_, 63), 14))),
        U32.is_eq(D.Fd(2n, M2, r), D.Fd(2n, m0, s))))) == True{} : Bool}
  %Equal.sym(U32, D.Fd(2n, M2, r), D.Fd(2n, ms, r), e2) :
    {Bool.and(D.Nodes(S, m0, s), Bool.and(U32.is_eq(U32.and(D.Fd(0n, ms, r), 255), U32.and(D.Fd(0n, m0, s), 255)),
      Bool.or(Bool.not(Bool.or(U32.is_eq(U32.and(D.Fd(0n, ms, r), 63), 13), U32.is_eq(U32.and(D.Fd(0n, ms, r), 63), 14))),
        U32.is_eq(_, D.Fd(2n, m0, s))))) == True{} : Bool}
  h

# both parts of a new node stay
def made.nw(+ms: Cr.Cir.Cells, +m0: Cr.Cir.Cells, +S: List<&2, D.Rt>, +T: List<&2, U32>, +cs: List<&2, D.Pr>,
  +r: U32, +tg: U32, +z: U32, +xc: Cr.Cir.Cell, +ne: {U32.is_eq(r, z) == False{} : Bool},
  h: {D.Nw(ms, m0, S, T, cs, r, tg) == True{} : Bool}) -> {D.Nw(Cr.Cir.Cells.set(ms, z, xc), m0, S, T, cs, r, tg) == True{} : Bool}:
  +M2 = Cr.Cir.Cells.set(ms, z, xc)
  +h2 = h
  K.Bo.and_i(D.New(M2, T, r, tg), D.Cpy(M2, m0, S, r, D.Pr.of(cs, r)),
    made.new(ms, T, r, tg, z, xc, ne, K.Bo.and_l(D.New(ms, T, r, tg), D.Cpy(ms, m0, S, r, D.Pr.of(cs, r)), h2)),
    made.cpy(ms, m0, S, r, D.Pr.of(cs, r), z, xc, ne, K.Bo.and_r(D.New(ms, T, r, tg), D.Cpy(ms, m0, S, r, D.Pr.of(cs, r)), h2)))

# keep the old-node alternative, or transport the new-node alternative
def made.or(s: Bool, -a: Bool, -b: Bool, h: {Bool.or(s, a) == True{} : Bool}, k: {a == True{} : Bool} -> {b == True{} : Bool}) ->
  {Bool.or(s, b) == True{} : Bool}:
  match s:
    case True{}:
      {==}
    case False{}:
      k(h)

# transport a new node and everything below it, leaving the old-node alternative unchanged
def made.cell(s: Bool, +n: Bool, +a: Bool, +n2: Bool, +a2: Bool, h: {Bool.or(s, Bool.and(n, a)) == True{} : Bool},
  kn: {n == True{} : Bool} -> {n2 == True{} : Bool}, ka: {a == True{} : Bool} -> {a2 == True{} : Bool}) ->
  {Bool.or(s, Bool.and(n2, a2)) == True{} : Bool}:
  made.or(s, Bool.and(n, a), Bool.and(n2, a2), h, q =>
    +q2 = q
    K.Bo.and_i(n2, a2, kn(K.Bo.and_l(n, a, q2)), ka(K.Bo.and_r(n, a, q2))))
