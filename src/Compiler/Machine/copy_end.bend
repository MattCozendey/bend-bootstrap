# compiler: the end of a copy's walk
# ==================================
#
# M.copy.end (copy_walk.bend's end.run) gives the result's register the
# root's field 2, makes the root a K.root (45: no term, no pointer) and puts
# it at the head of the pend list. Once the frames are gone, the walk's
# invariant then gives Post's facts: the root joins the garbage and the pend
# list, the result's register holds the pointer that the root held, and each
# other cell keeps what it holds. The two stores are one store at the root z
# (end.one), Cr.Cir.Cells.set(m, z, xc), and each lemma below carries one
# fact across it.

import Base
import ../../Book/impl.bend as Bk
import ../../Program/impl.bend as Pg
import ../Cir/impl.bend as Cr
import ./impl.bend as Mc
import ./cell_terms.bend as T
import ../need_big.bend as N
import ./copy_substitution.bend as D
import ./copy_kit.bend as K
import ./copy_walk.bend as W
import ./checked_terms_stay.bend as C
import ./statement_runs.bend as Sr

# The store at the root
# ---------------------

# the cells after M.copy.end: the root is a K.root linked to the old pend
def EndM(+m: Cr.Cir.Cells, +root: U32, +pv: U32) -> Cr.Cir.Cells:
  Sr.X.put(Sr.X.put(m, 0n, root, Mc.K.root()), 1n, root, pv)

# the root's cell after M.copy.end
def Ec(+m: Cr.Cir.Cells, +root: U32, +pv: U32) -> Cr.Cir.Cell:
  Cr.Cir.Cell.set(1n, Cr.Cir.Cell.set(0n, Cr.Cir.Cells.get(m, root), 45), pv)

# a second set of the same cell replaces the first
def Cl.set_set.at(n: Nat, +w: Word(n), +m: Cr.Cir.Cells, +a: Cr.Cir.Cell, +b: Cr.Cir.Cell) ->
  {Cr.Cir.Cells.set.at(n, w, Cr.Cir.Cells.set.at(n, w, m, a), b) == Cr.Cir.Cells.set.at(n, w, m, b) : Cr.Cir.Cells}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{False{}, +t}:
          match m:
            case Cr.Cir.Cells.node{+lo, +hi}:
              Equal.cong(Cr.Cir.Cells, Cr.Cir.Cells, x => Cr.Cir.Cells.node{x, hi}, Cr.Cir.Cells.set.at(p, t, Cr.Cir.Cells.set.at(p, t, lo, a), b),
                Cr.Cir.Cells.set.at(p, t, lo, b), Cl.set_set.at(p, t, lo, a, b))
            case Cr.Cir.Cells.none{}:
              Equal.cong(Cr.Cir.Cells, Cr.Cir.Cells, x => Cr.Cir.Cells.node{x, Cr.Cir.Cells.none{}},
                Cr.Cir.Cells.set.at(p, t, Cr.Cir.Cells.set.at(p, t, Cr.Cir.Cells.none{}, a), b), Cr.Cir.Cells.set.at(p, t, Cr.Cir.Cells.none{}, b),
                Cl.set_set.at(p, t, Cr.Cir.Cells.none{}, a, b))
            case Cr.Cir.Cells.one{+d}:
              Equal.cong(Cr.Cir.Cells, Cr.Cir.Cells, x => Cr.Cir.Cells.node{x, Cr.Cir.Cells.none{}},
                Cr.Cir.Cells.set.at(p, t, Cr.Cir.Cells.set.at(p, t, Cr.Cir.Cells.none{}, a), b), Cr.Cir.Cells.set.at(p, t, Cr.Cir.Cells.none{}, b),
                Cl.set_set.at(p, t, Cr.Cir.Cells.none{}, a, b))
        case WCon{True{}, +t}:
          match m:
            case Cr.Cir.Cells.node{+lo, +hi}:
              Equal.cong(Cr.Cir.Cells, Cr.Cir.Cells, x => Cr.Cir.Cells.node{lo, x}, Cr.Cir.Cells.set.at(p, t, Cr.Cir.Cells.set.at(p, t, hi, a), b),
                Cr.Cir.Cells.set.at(p, t, hi, b), Cl.set_set.at(p, t, hi, a, b))
            case Cr.Cir.Cells.none{}:
              Equal.cong(Cr.Cir.Cells, Cr.Cir.Cells, x => Cr.Cir.Cells.node{Cr.Cir.Cells.none{}, x},
                Cr.Cir.Cells.set.at(p, t, Cr.Cir.Cells.set.at(p, t, Cr.Cir.Cells.none{}, a), b), Cr.Cir.Cells.set.at(p, t, Cr.Cir.Cells.none{}, b),
                Cl.set_set.at(p, t, Cr.Cir.Cells.none{}, a, b))
            case Cr.Cir.Cells.one{+d}:
              Equal.cong(Cr.Cir.Cells, Cr.Cir.Cells, x => Cr.Cir.Cells.node{Cr.Cir.Cells.none{}, x},
                Cr.Cir.Cells.set.at(p, t, Cr.Cir.Cells.set.at(p, t, Cr.Cir.Cells.none{}, a), b), Cr.Cir.Cells.set.at(p, t, Cr.Cir.Cells.none{}, b),
                Cl.set_set.at(p, t, Cr.Cir.Cells.none{}, a, b))

def Cl.set_set(+m: Cr.Cir.Cells, +i: U32, +a: Cr.Cir.Cell, +b: Cr.Cir.Cell) ->
  {Cr.Cir.Cells.set(Cr.Cir.Cells.set(m, i, a), i, b) == Cr.Cir.Cells.set(m, i, b) : Cr.Cir.Cells}:
  match i:
    case U32{+w}:
      Cl.set_set.at(32n, w, m, a, b)

# M.copy.end's two stores at the root are one
def end.one(+m: Cr.Cir.Cells, +root: U32, +pv: U32) -> {EndM(m, root, pv) == Cr.Cir.Cells.set(m, root, Ec(m, root, pv)) : Cr.Cir.Cells}:
  +c1 = Cr.Cir.Cell.set(0n, Cr.Cir.Cells.get(m, root), 45)
  +m1 = Cr.Cir.Cells.set(m, root, c1)
  %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(m1, root), c1, K.Cl.get_set(m, root, c1)) :
    {Cr.Cir.Cells.set(m1, root, Cr.Cir.Cell.set(1n, _, pv)) == Cr.Cir.Cells.set(m, root, Ec(m, root, pv)) : Cr.Cir.Cells}
  Cl.set_set(m, root, c1, Cr.Cir.Cell.set(1n, c1, pv))

def end.c0(c: Cr.Cir.Cell, +pv: U32) -> {Cr.Cir.Cell.get(0n, Cr.Cir.Cell.set(1n, Cr.Cir.Cell.set(0n, c, 45), pv)) == 45 : U32}:
  match c:
    case Cr.Cir.Cell{a0, a1, a2, a3, a4}:
      {==}

def end.c1(c: Cr.Cir.Cell, +pv: U32) -> {Cr.Cir.Cell.get(1n, Cr.Cir.Cell.set(1n, Cr.Cir.Cell.set(0n, c, 45), pv)) == pv : U32}:
  match c:
    case Cr.Cir.Cell{a0, a1, a2, a3, a4}:
      {==}

# the root is past the table
def end.hz(+K: U32, +F: U32, +root: U32, +hk: {U32.is_le(290, K) == True{} : Bool},
  +hkf: {U32.is_lt(K, F) == True{} : Bool}, +hfr: {U32.is_le(F, root) == True{} : Bool}) -> N.Le(291n, U32.to_nat(root)):
  N.le_trans(291n, 1n+U32.to_nat(K), U32.to_nat(root), K.U.le(290, K, hk),
    N.le_trans(1n+U32.to_nat(K), U32.to_nat(F), U32.to_nat(root), K.U.lt(K, F, hkf), K.U.le(F, root, hfr)))

# field k of z after the store is xc's
def fd.z(+k: Nat, +m: Cr.Cir.Cells, +z: U32, +xc: Cr.Cir.Cell) -> {D.Fd(k, Cr.Cir.Cells.set(m, z, xc), z) == Cr.Cir.Cell.get(k, xc) : U32}:
  Equal.cong(Cr.Cir.Cell, U32, w => Cr.Cir.Cell.get(k, w), Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, xc), z), xc, K.Cl.get_set(m, z, xc))

def f0.z(+m: Cr.Cir.Cells, +z: U32, +xc: Cr.Cir.Cell, +h0: {Cr.Cir.Cell.get(0n, xc) == 45 : U32}) ->
  {D.Fd(0n, Cr.Cir.Cells.set(m, z, xc), z) == 45 : U32}:
  Equal.trans(U32, D.Fd(0n, Cr.Cir.Cells.set(m, z, xc), z), Cr.Cir.Cell.get(0n, xc), 45, fd.z(0n, m, z, xc), h0)

# The pointers across the store
# -----------------------------

# a cell other than z is in Con{z, Q} when it is in Q
def has.cons.ne(+z: U32, +Q: List<&2, U32>, +o: U32, ne: {U32.is_eq(z, o) == False{} : Bool}) ->
  {D.Has(Con{z, Q}, o) == D.Has(Q, o) : Bool}:
  %Equal.sym(Bool, U32.is_eq(z, o), False{}, ne) : {Bool.or(_, D.Has(Q, o)) == D.Has(Q, o) : Bool}
  {==}

# z is in Con{z, Q}
def has.cons.eq(+z: U32, +Q: List<&2, U32>) -> {D.Has(Con{z, Q}, z) == True{} : Bool}:
  %Equal.sym(Bool, U32.is_eq(z, z), True{}, K.U.eq_refl(z)) : {Bool.or(_, D.Has(Q, z)) == True{} : Bool}
  {==}

# the root holds no pointer once it is a K.root
def ps.z0(+m: Cr.Cir.Cells, +z: U32, +xc: Cr.Cir.Cell, +Q: List<&2, U32>, +h0: {Cr.Cir.Cell.get(0n, xc) == 45 : U32}) ->
  {D.Ps(Cr.Cir.Cells.set(m, z, xc), Q, z) == Nil{} : List<&2, U32>}:
  +ms = Cr.Cir.Cells.set(m, z, xc)
  %Equal.sym(U32, D.Fd(0n, ms, z), 45, f0.z(m, z, xc, h0)) :
    {Bool.pick(List<&2, U32>, U32.is_lt(U32.and(_, 63), 19),
      D.Ps.term(D.Fd(2n, ms, U32.add(272, U32.and(_, 63))), D.Fd(2n, ms, z), D.Fd(3n, ms, z), D.Fd(4n, ms, z)),
      Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_le(32, U32.and(_, 63)), U32.is_le(U32.and(_, 63), 40)), Bool.not(D.Has(Q, z))),
        Con{D.Fd(2n, ms, z), D.Ps.opt(U32.is_eq(U32.and(_, 63), 38), D.Fd(3n, ms, z), Nil{})},
        Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_eq(U32.and(_, 63), 41), U32.is_ne(U32.and(_, 4096), 0)), Bool.not(D.Has(Q, z))),
          [D.Fd(2n, ms, z)], Nil{}))) == Nil{} : List<&2, U32>}
  {==}

# another cell keeps its pointers, with z at the head of the pend list
def ps.zo(+m: Cr.Cir.Cells, +z: U32, +xc: Cr.Cir.Cell, +Q: List<&2, U32>, +o: U32, +ne: {U32.is_eq(o, z) == False{} : Bool},
  +hz: N.Le(291n, U32.to_nat(z))) -> {D.Ps(Cr.Cir.Cells.set(m, z, xc), Con{z, Q}, o) == D.Ps(m, Q, o) : List<&2, U32>}:
  +ms = Cr.Cir.Cells.set(m, z, xc)
  Equal.trans(List<&2, U32>, D.Ps(ms, Con{z, Q}, o), D.Ps(ms, Q, o), D.Ps(m, Q, o),
    W.ps.hq(ms, Con{z, Q}, Q, o, has.cons.ne(z, Q, o, K.U.ne.sym(o, z, ne))), K.ps.set(m, z, xc, Q, o, ne, hz))

# the cell at 272 + 11 holds the mask of a Prj's parts
def tb.i11() -> {U32.add(272, 11) == U32.inc(U32.inc(U32.inc(U32.inc(U32.inc(U32.inc(U32.inc(U32.inc(U32.inc(U32.inc(U32.inc(272))))))))))) : U32}:
  {==}

# a Prj's mask, by the table: its one part, in field 2
def tb.prj(+m: Cr.Cir.Cells, t: D.Tb(m)) -> {D.Fd(2n, m, U32.add(272, 11)) == 1 : U32}:
  (_, t1) = t
  (_, t2) = t1
  (_, t3) = t2
  (_, t4) = t3
  (_, t5) = t4
  (_, t6) = t5
  (_, t7) = t6
  (_, t8) = t7
  (_, t9) = t8
  (_, t10) = t9
  (_, t11) = t10
  (e11, _) = t11
  %tb.i11() : {Cr.Cir.Cell.get(2n, Cr.Cir.Cells.get(m, _)) == 1 : U32}
  %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(m, U32.inc(U32.inc(U32.inc(U32.inc(U32.inc(U32.inc(U32.inc(U32.inc(U32.inc(U32.inc(U32.inc(272)))))))))))),
    Cr.Cir.Cell{0, 0, 1, 0, 1}, e11) : {Cr.Cir.Cell.get(2n, _) == 1 : U32}
  {==}

# a Prj's pointers: its part in field 2
def ps.prj(+m: Cr.Cir.Cells, +Q: List<&2, U32>, +z: U32, +ht: {U32.and(D.Fd(0n, m, z), 63) == 11 : U32}, +tb: D.Tb(m)) ->
  {D.Ps(m, Q, z) == [D.Fd(2n, m, z)] : List<&2, U32>}:
  %Equal.sym(U32, U32.and(D.Fd(0n, m, z), 63), 11, ht) :
    {Bool.pick(List<&2, U32>, U32.is_lt(_, 19),
      D.Ps.term(D.Fd(2n, m, U32.add(272, _)), D.Fd(2n, m, z), D.Fd(3n, m, z), D.Fd(4n, m, z)),
      Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_le(32, _), U32.is_le(_, 40)), Bool.not(D.Has(Q, z))),
        Con{D.Fd(2n, m, z), D.Ps.opt(U32.is_eq(_, 38), D.Fd(3n, m, z), Nil{})},
        Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_eq(_, 41), U32.is_ne(U32.and(D.Fd(0n, m, z), 4096), 0)), Bool.not(D.Has(Q, z))),
          [D.Fd(2n, m, z)], Nil{}))) == [D.Fd(2n, m, z)] : List<&2, U32>}
  %Equal.sym(U32, D.Fd(2n, m, U32.add(272, 11)), 1, tb.prj(m, tb)) :
    {D.Ps.term(_, D.Fd(2n, m, z), D.Fd(3n, m, z), D.Fd(4n, m, z)) == [D.Fd(2n, m, z)] : List<&2, U32>}
  {==}

# the pointers to c of the n cells from o, z not among them, with z at the
# head of the pend list
def pc.zn(n: Nat, +m: Cr.Cir.Cells, +z: U32, +xc: Cr.Cir.Cell, +Q: List<&2, U32>, +o: U32, +c: U32,
  +hz: N.Le(291n, U32.to_nat(z)), hn: {K.Ne(n, o, z) == True{} : Bool}) ->
  {D.Pc(n, Cr.Cir.Cells.set(m, z, xc), Con{z, Q}, o, c) == D.Pc(n, m, Q, o, c) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      +ms = Cr.Cir.Cells.set(m, z, xc)
      +hn2 = hn
      +ne = K.Bo.not_t(U32.is_eq(o, z), K.Bo.and_l(Bool.not(U32.is_eq(o, z)), K.Ne(p, U32.inc(o), z), hn2))
      %Equal.sym(List<&2, U32>, D.Ps(ms, Con{z, Q}, o), D.Ps(m, Q, o), ps.zo(m, z, xc, Q, o, ne, hz)) :
        {Nat.add(D.Occ(_, c), D.Pc(p, ms, Con{z, Q}, U32.inc(o), c)) == Nat.add(D.Occ(D.Ps(m, Q, o), c), D.Pc(p, m, Q, U32.inc(o), c)) : Nat}
      %Equal.sym(Nat, D.Pc(p, ms, Con{z, Q}, U32.inc(o), c), D.Pc(p, m, Q, U32.inc(o), c),
        pc.zn(p, m, z, xc, Q, U32.inc(o), c, hz, K.Bo.and_r(Bool.not(U32.is_eq(o, z)), K.Ne(p, U32.inc(o), z), hn2))) :
        {Nat.add(D.Occ(D.Ps(m, Q, o), c), _) == Nat.add(D.Occ(D.Ps(m, Q, o), c), D.Pc(p, m, Q, U32.inc(o), c)) : Nat}
      {==}

def pc.z.b(e: Bool, +p: Nat, +m: Cr.Cir.Cells, +z: U32, +xc: Cr.Cir.Cell, +Q: List<&2, U32>, +o: U32, +c: U32,
  +hz: N.Le(291n, U32.to_nat(z)), +h0: {Cr.Cir.Cell.get(0n, xc) == 45 : U32}, +eo: {U32.is_eq(o, z) == e : Bool},
  h: {Bool.pick(Bool, e, K.Ne(p, U32.inc(o), z), W.Once(p, U32.inc(o), z)) == True{} : Bool},
  k: {W.Once(p, U32.inc(o), z) == True{} : Bool} ->
    {Nat.add(D.Pc(p, Cr.Cir.Cells.set(m, z, xc), Con{z, Q}, U32.inc(o), c), D.Occ(D.Ps(m, Q, z), c)) == D.Pc(p, m, Q, U32.inc(o), c) : Nat}) ->
  {Nat.add(Nat.add(D.Occ(D.Ps(Cr.Cir.Cells.set(m, z, xc), Con{z, Q}, o), c), D.Pc(p, Cr.Cir.Cells.set(m, z, xc), Con{z, Q}, U32.inc(o), c)),
    D.Occ(D.Ps(m, Q, z), c)) == Nat.add(D.Occ(D.Ps(m, Q, o), c), D.Pc(p, m, Q, U32.inc(o), c)) : Nat}:
  match e:
    case True{}:
      +ms = Cr.Cir.Cells.set(m, z, xc)
      +eq = Equal.sym(U32, o, z, K.U.eq(o, z, eo))
      +X = D.Pc(p, ms, Con{z, Q}, U32.inc(o), c)
      +Y = D.Pc(p, m, Q, U32.inc(o), c)
      +V = D.Occ(D.Ps(m, Q, z), c)
      +e0 = {(%eq : {D.Ps(ms, Con{z, Q}, _) == Nil{} : List<&2, U32>}; ps.z0(m, z, xc, Con{z, Q}, h0)) : {D.Ps(ms, Con{z, Q}, o) == Nil{} : List<&2, U32>}}
      +e1 = {(%eq : {D.Occ(D.Ps(m, Q, _), c) == V : Nat}; {==}) : {D.Occ(D.Ps(m, Q, o), c) == V : Nat}}
      %Equal.sym(List<&2, U32>, D.Ps(ms, Con{z, Q}, o), Nil{}, e0) : {Nat.add(Nat.add(D.Occ(_, c), X), V) == Nat.add(D.Occ(D.Ps(m, Q, o), c), Y) : Nat}
      %Equal.sym(Nat, D.Occ(D.Ps(m, Q, o), c), V, e1) : {Nat.add(X, V) == Nat.add(_, Y) : Nat}
      %Equal.sym(Nat, X, Y, pc.zn(p, m, z, xc, Q, U32.inc(o), c, hz, h)) : {Nat.add(_, V) == Nat.add(V, Y) : Nat}
      W.Na.comm(Y, V)
    case False{}:
      +ms = Cr.Cir.Cells.set(m, z, xc)
      +X = D.Pc(p, ms, Con{z, Q}, U32.inc(o), c)
      +Y = D.Pc(p, m, Q, U32.inc(o), c)
      +V = D.Occ(D.Ps(m, Q, z), c)
      +A = D.Occ(D.Ps(m, Q, o), c)
      %Equal.sym(List<&2, U32>, D.Ps(ms, Con{z, Q}, o), D.Ps(m, Q, o), ps.zo(m, z, xc, Q, o, eo, hz)) :
        {Nat.add(Nat.add(D.Occ(_, c), X), V) == Nat.add(A, Y) : Nat}
      Equal.trans(Nat, Nat.add(Nat.add(A, X), V), Nat.add(A, Nat.add(X, V)), Nat.add(A, Y), N.add_assoc(A, X, V),
        Equal.cong(Nat, Nat, w => Nat.add(A, w), Nat.add(X, V), Y, k(h)))

# the pointers to c of the n cells from o, z once among them: z's pointers go
def pc.z(n: Nat, +m: Cr.Cir.Cells, +z: U32, +xc: Cr.Cir.Cell, +Q: List<&2, U32>, +o: U32, +c: U32,
  +hz: N.Le(291n, U32.to_nat(z)), +h0: {Cr.Cir.Cell.get(0n, xc) == 45 : U32}, h: {W.Once(n, o, z) == True{} : Bool}) ->
  {Nat.add(D.Pc(n, Cr.Cir.Cells.set(m, z, xc), Con{z, Q}, o, c), D.Occ(D.Ps(m, Q, z), c)) == D.Pc(n, m, Q, o, c) : Nat}:
  match n:
    case 0n:
      K.Bo.tf({Nat.add(0n, D.Occ(D.Ps(m, Q, z), c)) == 0n : Nat}, h)
    case 1n+(+p):
      pc.z.b(U32.is_eq(o, z), p, m, z, xc, Q, o, c, hz, h0, {==}, h, h2 => pc.z(p, m, z, xc, Q, U32.inc(o), c, hz, h0, h2))

# Lists
# -----

# z is in xs ++ Con{z, ys}
def has.mid(xs: List<&2, U32>, +z: U32, +ys: List<&2, U32>) -> {D.Has(List.append(&2, U32, xs, Con{z, ys}), z) == True{} : Bool}:
  match xs:
    case Nil{}:
      has.cons.eq(z, ys)
    case Con{+y, +rest}:
      K.Bo.or_ir(U32.is_eq(y, z), D.Has(List.append(&2, U32, rest, Con{z, ys}), z), has.mid(rest, z, ys))

# xs is within xs ++ ys
def sub.l(xs: List<&2, U32>, +ys: List<&2, U32>) -> {D.Sub(xs, List.append(&2, U32, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      K.Bo.and_i(D.Has(Con{x, List.append(&2, U32, rest, ys)}, x), D.Sub(rest, Con{x, List.append(&2, U32, rest, ys)}),
        K.Bo.or_il(U32.is_eq(x, x), D.Has(List.append(&2, U32, rest, ys), x), K.U.eq_refl(x)),
        W.sub.cons(rest, x, List.append(&2, U32, rest, ys), sub.l(rest, ys)))

# ys is within xs ++ Con{z, ys}
def sub.r(xs: List<&2, U32>, +z: U32, +ys: List<&2, U32>) -> {D.Sub(ys, List.append(&2, U32, xs, Con{z, ys})) == True{} : Bool}:
  match xs:
    case Nil{}:
      W.sub.cons(ys, z, ys, W.sub.refl(ys))
    case Con{+x, +rest}:
      W.sub.cons(ys, x, List.append(&2, U32, rest, Con{z, ys}), sub.r(rest, z, ys))

# a cell of A ++ B is one of A ++ Con{z, B}
def has.ins(A: List<&2, U32>, +z: U32, +B: List<&2, U32>, +x: U32, h: {D.Has(List.append(&2, U32, A, B), x) == True{} : Bool}) ->
  {D.Has(List.append(&2, U32, A, Con{z, B}), x) == True{} : Bool}:
  match A:
    case Nil{}:
      K.Bo.or_ir(U32.is_eq(z, x), D.Has(B, x), h)
    case Con{+a, +rest}:
      W.or.mono_r(U32.is_eq(a, x), D.Has(List.append(&2, U32, rest, B), x), D.Has(List.append(&2, U32, rest, Con{z, B}), x), h,
        k => has.ins(rest, z, B, x, k))

# the cells of xs within A ++ B are within A ++ Con{z, B}
def sub.ins(xs: List<&2, U32>, +A: List<&2, U32>, +z: U32, +B: List<&2, U32>, h: {D.Sub(xs, List.append(&2, U32, A, B)) == True{} : Bool}) ->
  {D.Sub(xs, List.append(&2, U32, A, Con{z, B})) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      +h2 = h
      K.Bo.and_i(D.Has(List.append(&2, U32, A, Con{z, B}), x), D.Sub(rest, List.append(&2, U32, A, Con{z, B})),
        has.ins(A, z, B, x, K.Bo.and_l(D.Has(List.append(&2, U32, A, B), x), D.Sub(rest, List.append(&2, U32, A, B)), h2)),
        sub.ins(rest, A, z, B, K.Bo.and_r(D.Has(List.append(&2, U32, A, B), x), D.Sub(rest, List.append(&2, U32, A, B)), h2)))

# each cell of ys, within X, is one of X or from N on
def incl.sub(ys: List<&2, U32>, +X: List<&2, U32>, +N: U32, h: {D.Sub(ys, X) == True{} : Bool}) -> {D.Incl.go(ys, X, N) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      +h2 = h
      K.Bo.and_i(Bool.or(D.Has(X, y), U32.is_le(N, y)), D.Incl.go(rest, X, N),
        K.Bo.or_il(D.Has(X, y), U32.is_le(N, y), K.Bo.and_l(D.Has(X, y), D.Sub(rest, X), h2)),
        incl.sub(rest, X, N, K.Bo.and_r(D.Has(X, y), D.Sub(rest, X), h2)))

# each garbage cell, old (Gw), is one of P0 or from N on
def incl.gw(P: List<&2, U32>, +P0: List<&2, U32>, +T: List<&2, U32>, +N: U32, h: {W.Gw(P, P0, T) == True{} : Bool}) ->
  {D.Incl.go(P, P0, N) == True{} : Bool}:
  match P:
    case Nil{}:
      {==}
    case Con{+c, +rest}:
      +h2 = h
      +hc = K.Bo.and_l(Bool.and(D.Has(P0, c), Bool.not(D.Has(T, c))), W.Gw(rest, P0, T), h2)
      K.Bo.and_i(Bool.or(D.Has(P0, c), U32.is_le(N, c)), D.Incl.go(rest, P0, N),
        K.Bo.or_il(D.Has(P0, c), U32.is_le(N, c), K.Bo.and_l(D.Has(P0, c), Bool.not(D.Has(T, c)), hc)),
        incl.gw(rest, P0, T, N, K.Bo.and_r(Bool.and(D.Has(P0, c), Bool.not(D.Has(T, c))), W.Gw(rest, P0, T), h2)))

# Nodes and the root
# ------------------

# a cell that is no node of a term is not its root
def node.root(t: Bk.Term, +m: Cr.Cir.Cells, +r: U32, +c: U32, h: {D.Node(t, m, r, c) == False{} : Bool}) ->
  {U32.is_eq(r, c) == False{} : Bool}:
  match t:
    case Bk.Term.Var{_}:
      h
    case Bk.Term.Ref{_}:
      h
    case Bk.Term.Ann{+y, +w}:
      K.or.fl(U32.is_eq(r, c), Bool.or(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(w, m, D.Fd(3n, m, r), c)), h)
    case Bk.Term.Let{_, +y, +w}:
      K.or.fl(U32.is_eq(r, c), Bool.or(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(w, m, D.Fd(3n, m, r), c)), h)
    case Bk.Term.Typ{+y}:
      K.or.fl(U32.is_eq(r, c), D.Node(y, m, D.Fd(2n, m, r), c), h)
    case Bk.Term.Min{+y, +w}:
      K.or.fl(U32.is_eq(r, c), Bool.or(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(w, m, D.Fd(3n, m, r), c)), h)
    case Bk.Term.All{_, +y, +w}:
      K.or.fl(U32.is_eq(r, c), Bool.or(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(w, m, D.Fd(3n, m, r), c)), h)
    case Bk.Term.Lam{_, +y}:
      K.or.fl(U32.is_eq(r, c), D.Node(y, m, D.Fd(2n, m, r), c), h)
    case Bk.Term.App{_, +y, +w}:
      K.or.fl(U32.is_eq(r, c), Bool.or(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(w, m, D.Fd(3n, m, r), c)), h)
    case Bk.Term.Sig{_, +y, +w}:
      K.or.fl(U32.is_eq(r, c), Bool.or(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(w, m, D.Fd(3n, m, r), c)), h)
    case Bk.Term.Tup{_, +y, +w}:
      K.or.fl(U32.is_eq(r, c), Bool.or(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(w, m, D.Fd(3n, m, r), c)), h)
    case Bk.Term.Prj{+y}:
      K.or.fl(U32.is_eq(r, c), D.Node(y, m, D.Fd(2n, m, r), c), h)
    case Bk.Term.Enu{_}:
      h
    case Bk.Term.Lab{_}:
      h
    case Bk.Term.Mat{_, +y, +w}:
      K.or.fl(U32.is_eq(r, c), Bool.or(D.Node(y, m, D.Fd(3n, m, r), c), D.Node(w, m, D.Fd(4n, m, r), c)), h)
    case Bk.Term.Efq{}:
      h
    case Bk.Term.Eql{+y, +w, +v}:
      K.or.fl(U32.is_eq(r, c), Bool.or(D.Node(y, m, D.Fd(2n, m, r), c), Bool.or(D.Node(w, m, D.Fd(3n, m, r), c), D.Node(v, m, D.Fd(4n, m, r), c))), h)
    case Bk.Term.Rfl{}:
      h
    case Bk.Term.Rwt{+y, +w, +v}:
      K.or.fl(U32.is_eq(r, c), Bool.or(D.Node(y, m, D.Fd(2n, m, r), c), Bool.or(D.Node(w, m, D.Fd(3n, m, r), c), D.Node(v, m, D.Fd(4n, m, r), c))), h)

def nxat.has.b(e: Bool, +c: U32, +rest: List<&2, U32>, +u: Bk.Term, +m: Cr.Cir.Cells, +r: U32, +z: U32, ec: {U32.is_eq(c, z) == e : Bool},
  hz: {Bool.or(e, D.Has(rest, z)) == True{} : Bool}, hc: {D.Node(u, m, r, c) == False{} : Bool},
  k: {D.Has(rest, z) == True{} : Bool} -> {D.Node(u, m, r, z) == False{} : Bool}) -> {D.Node(u, m, r, z) == False{} : Bool}:
  match e:
    case True{}:
      (%K.U.eq(c, z, ec) : {D.Node(u, m, r, _) == False{} : Bool}; hc)
    case False{}:
      k(hz)

# a cell of xs is no node of a root that has none in xs
def nxat.has(xs: List<&2, U32>, +u: Bk.Term, +m: Cr.Cir.Cells, +r: U32, +z: U32, hz: {D.Has(xs, z) == True{} : Bool},
  h: {W.Nx.at(xs, u, m, r) == True{} : Bool}) -> {D.Node(u, m, r, z) == False{} : Bool}:
  match xs:
    case Nil{}:
      K.Bo.tf({D.Node(u, m, r, z) == False{} : Bool}, hz)
    case Con{+c, +rest}:
      +h2 = h
      +hc = K.Bo.not_t(D.Node(u, m, r, c), K.Bo.and_l(Bool.not(D.Node(u, m, r, c)), W.Nx.at(rest, u, m, r), h2))
      +hr = K.Bo.and_r(Bool.not(D.Node(u, m, r, c)), W.Nx.at(rest, u, m, r), h2)
      nxat.has.b(U32.is_eq(c, z), c, rest, u, m, r, z, {==}, hz, hc, k => nxat.has(rest, u, m, r, z, k, hr))

# a cell of xs is no node of roots that have none in xs
def nx.has(rs: List<&2, D.Rt>, +m: Cr.Cir.Cells, +xs: List<&2, U32>, +z: U32, +hz: {D.Has(xs, z) == True{} : Bool},
  h: {W.Nx(rs, m, xs) == True{} : Bool}) -> {D.Nodes(rs, m, z) == False{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case Con{D.Rt{_, +r, +u}, +rest}:
      +h2 = h
      %Equal.sym(Bool, D.Node(u, m, r, z), False{}, nxat.has(xs, u, m, r, z, hz, K.Bo.and_l(W.Nx.at(xs, u, m, r), W.Nx(rest, m, xs), h2))) :
        {Bool.or(_, D.Nodes(rest, m, z)) == False{} : Bool}
      nx.has(rest, m, xs, z, hz, K.Bo.and_r(W.Nx.at(xs, u, m, r), W.Nx(rest, m, xs), h2))

# a root that has no node in xs is not in xs
def nxat.out(xs: List<&2, U32>, +u: Bk.Term, +m: Cr.Cir.Cells, +r: U32, h: {W.Nx.at(xs, u, m, r) == True{} : Bool}) ->
  {D.Has(xs, r) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+c, +rest}:
      +h2 = h
      +hc = K.Bo.not_t(D.Node(u, m, r, c), K.Bo.and_l(Bool.not(D.Node(u, m, r, c)), W.Nx.at(rest, u, m, r), h2))
      %Equal.sym(Bool, U32.is_eq(c, r), False{}, K.U.ne.sym(r, c, node.root(u, m, r, c, hc))) : {Bool.or(_, D.Has(rest, r)) == False{} : Bool}
      nxat.out(rest, u, m, r, K.Bo.and_r(Bool.not(D.Node(u, m, r, c)), W.Nx.at(rest, u, m, r), h2))


# What the result is made of
# --------------------------

# a node of one part, in the field ka of r, stays made when the part does
def made.una(+ms: Cr.Cir.Cells, +m0: Cr.Cir.Cells, +S: List<&2, D.Rt>, +T: List<&2, U32>, +cs: List<&2, D.Pr>, +r: U32,
  +z: U32, +xc: Cr.Cir.Cell, +ka: Nat, +y: Bk.Term,
  hn: {Bool.or(U32.is_eq(r, z), D.Node(y, ms, D.Fd(ka, ms, r), z)) == False{} : Bool},
  h: {Bool.or(D.Nodes(S, m0, r), Bool.and(D.Nw(ms, m0, S, T, cs, r), D.Made(y, ms, m0, D.Fd(ka, ms, r), S, T, cs))) == True{} : Bool},
  fy: @a: U32 -> {D.Node(y, ms, a, z) == False{} : Bool} -> {D.Made(y, ms, m0, a, S, T, cs) == True{} : Bool} ->
    {D.Made(y, Cr.Cir.Cells.set(ms, z, xc), m0, a, S, T, cs) == True{} : Bool}) ->
  {Bool.or(D.Nodes(S, m0, r), Bool.and(D.Nw(Cr.Cir.Cells.set(ms, z, xc), m0, S, T, cs, r), D.Made(y, Cr.Cir.Cells.set(ms, z, xc), m0, D.Fd(ka, Cr.Cir.Cells.set(ms, z, xc), r), S, T, cs))) == True{} : Bool}:
  +M2 = Cr.Cir.Cells.set(ms, z, xc)
  +hn2 = hn
  +ne = K.or.fl(U32.is_eq(r, z), D.Node(y, ms, D.Fd(ka, ms, r), z), hn2)
  +nr = K.or.fr(U32.is_eq(r, z), D.Node(y, ms, D.Fd(ka, ms, r), z), hn2)
  %Equal.sym(U32, D.Fd(ka, M2, r), D.Fd(ka, ms, r), C.made.fd(ka, ms, r, z, xc, ne)) :
    {Bool.or(D.Nodes(S, m0, r), Bool.and(D.Nw(M2, m0, S, T, cs, r), D.Made(y, M2, m0, _, S, T, cs))) == True{} : Bool}
  C.made.cell(D.Nodes(S, m0, r), D.Nw(ms, m0, S, T, cs, r), D.Made(y, ms, m0, D.Fd(ka, ms, r), S, T, cs),
    D.Nw(M2, m0, S, T, cs, r), D.Made(y, M2, m0, D.Fd(ka, ms, r), S, T, cs), h,
    q => C.made.nw(ms, m0, S, T, cs, r, z, xc, ne, q),
    q =>
      +q2 = q
      fy(D.Fd(ka, ms, r), nr, q2))

# a node of two parts, in the fields ka and kb of r, stays made when each part does
def made.bin(+ms: Cr.Cir.Cells, +m0: Cr.Cir.Cells, +S: List<&2, D.Rt>, +T: List<&2, U32>, +cs: List<&2, D.Pr>, +r: U32,
  +z: U32, +xc: Cr.Cir.Cell, +ka: Nat, +kb: Nat, +y: Bk.Term, +w: Bk.Term,
  hn: {Bool.or(U32.is_eq(r, z), Bool.or(D.Node(y, ms, D.Fd(ka, ms, r), z), D.Node(w, ms, D.Fd(kb, ms, r), z))) == False{} : Bool},
  h: {Bool.or(D.Nodes(S, m0, r), Bool.and(D.Nw(ms, m0, S, T, cs, r), Bool.and(D.Made(y, ms, m0, D.Fd(ka, ms, r), S, T, cs), D.Made(w, ms, m0, D.Fd(kb, ms, r), S, T, cs)))) == True{} : Bool},
  fy: @a: U32 -> {D.Node(y, ms, a, z) == False{} : Bool} -> {D.Made(y, ms, m0, a, S, T, cs) == True{} : Bool} ->
    {D.Made(y, Cr.Cir.Cells.set(ms, z, xc), m0, a, S, T, cs) == True{} : Bool},
  fw: @a: U32 -> {D.Node(w, ms, a, z) == False{} : Bool} -> {D.Made(w, ms, m0, a, S, T, cs) == True{} : Bool} ->
    {D.Made(w, Cr.Cir.Cells.set(ms, z, xc), m0, a, S, T, cs) == True{} : Bool}) ->
  {Bool.or(D.Nodes(S, m0, r), Bool.and(D.Nw(Cr.Cir.Cells.set(ms, z, xc), m0, S, T, cs, r), Bool.and(D.Made(y, Cr.Cir.Cells.set(ms, z, xc), m0, D.Fd(ka, Cr.Cir.Cells.set(ms, z, xc), r), S, T, cs), D.Made(w, Cr.Cir.Cells.set(ms, z, xc), m0, D.Fd(kb, Cr.Cir.Cells.set(ms, z, xc), r), S, T, cs)))) == True{} : Bool}:
  +M2 = Cr.Cir.Cells.set(ms, z, xc)
  +hn2 = hn
  +ne = K.or.fl(U32.is_eq(r, z), Bool.or(D.Node(y, ms, D.Fd(ka, ms, r), z), D.Node(w, ms, D.Fd(kb, ms, r), z)), hn2)
  +nr = K.or.fr(U32.is_eq(r, z), Bool.or(D.Node(y, ms, D.Fd(ka, ms, r), z), D.Node(w, ms, D.Fd(kb, ms, r), z)), hn2)
  %Equal.sym(U32, D.Fd(ka, M2, r), D.Fd(ka, ms, r), C.made.fd(ka, ms, r, z, xc, ne)) :
    {Bool.or(D.Nodes(S, m0, r), Bool.and(D.Nw(M2, m0, S, T, cs, r), Bool.and(D.Made(y, M2, m0, _, S, T, cs), D.Made(w, M2, m0, D.Fd(kb, M2, r), S, T, cs)))) == True{} : Bool}
  %Equal.sym(U32, D.Fd(kb, M2, r), D.Fd(kb, ms, r), C.made.fd(kb, ms, r, z, xc, ne)) :
    {Bool.or(D.Nodes(S, m0, r), Bool.and(D.Nw(M2, m0, S, T, cs, r), Bool.and(D.Made(y, M2, m0, D.Fd(ka, ms, r), S, T, cs), D.Made(w, M2, m0, _, S, T, cs)))) == True{} : Bool}
  C.made.cell(D.Nodes(S, m0, r), D.Nw(ms, m0, S, T, cs, r), Bool.and(D.Made(y, ms, m0, D.Fd(ka, ms, r), S, T, cs), D.Made(w, ms, m0, D.Fd(kb, ms, r), S, T, cs)),
    D.Nw(M2, m0, S, T, cs, r), Bool.and(D.Made(y, M2, m0, D.Fd(ka, ms, r), S, T, cs), D.Made(w, M2, m0, D.Fd(kb, ms, r), S, T, cs)), h,
    q => C.made.nw(ms, m0, S, T, cs, r, z, xc, ne, q),
    q =>
      +q2 = q
      K.Bo.and_i(D.Made(y, M2, m0, D.Fd(ka, ms, r), S, T, cs), D.Made(w, M2, m0, D.Fd(kb, ms, r), S, T, cs),
        fy(D.Fd(ka, ms, r), K.or.fl(D.Node(y, ms, D.Fd(ka, ms, r), z), D.Node(w, ms, D.Fd(kb, ms, r), z), nr), K.Bo.and_l(D.Made(y, ms, m0, D.Fd(ka, ms, r), S, T, cs), D.Made(w, ms, m0, D.Fd(kb, ms, r), S, T, cs), q2)),
        fw(D.Fd(kb, ms, r), K.or.fr(D.Node(y, ms, D.Fd(ka, ms, r), z), D.Node(w, ms, D.Fd(kb, ms, r), z), nr), K.Bo.and_r(D.Made(y, ms, m0, D.Fd(ka, ms, r), S, T, cs), D.Made(w, ms, m0, D.Fd(kb, ms, r), S, T, cs), q2))))

# a node of three parts, in the fields ka to kc of r, stays made when each part does
def made.ter(+ms: Cr.Cir.Cells, +m0: Cr.Cir.Cells, +S: List<&2, D.Rt>, +T: List<&2, U32>, +cs: List<&2, D.Pr>, +r: U32,
  +z: U32, +xc: Cr.Cir.Cell, +ka: Nat, +kb: Nat, +kc: Nat, +y: Bk.Term, +w: Bk.Term, +v: Bk.Term,
  hn: {Bool.or(U32.is_eq(r, z), Bool.or(D.Node(y, ms, D.Fd(ka, ms, r), z), Bool.or(D.Node(w, ms, D.Fd(kb, ms, r), z), D.Node(v, ms, D.Fd(kc, ms, r), z)))) == False{} : Bool},
  h: {Bool.or(D.Nodes(S, m0, r), Bool.and(D.Nw(ms, m0, S, T, cs, r), Bool.and(D.Made(y, ms, m0, D.Fd(ka, ms, r), S, T, cs), Bool.and(D.Made(w, ms, m0, D.Fd(kb, ms, r), S, T, cs), D.Made(v, ms, m0, D.Fd(kc, ms, r), S, T, cs))))) == True{} : Bool},
  fy: @a: U32 -> {D.Node(y, ms, a, z) == False{} : Bool} -> {D.Made(y, ms, m0, a, S, T, cs) == True{} : Bool} ->
    {D.Made(y, Cr.Cir.Cells.set(ms, z, xc), m0, a, S, T, cs) == True{} : Bool},
  fw: @a: U32 -> {D.Node(w, ms, a, z) == False{} : Bool} -> {D.Made(w, ms, m0, a, S, T, cs) == True{} : Bool} ->
    {D.Made(w, Cr.Cir.Cells.set(ms, z, xc), m0, a, S, T, cs) == True{} : Bool},
  fv: @a: U32 -> {D.Node(v, ms, a, z) == False{} : Bool} -> {D.Made(v, ms, m0, a, S, T, cs) == True{} : Bool} ->
    {D.Made(v, Cr.Cir.Cells.set(ms, z, xc), m0, a, S, T, cs) == True{} : Bool}) ->
  {Bool.or(D.Nodes(S, m0, r), Bool.and(D.Nw(Cr.Cir.Cells.set(ms, z, xc), m0, S, T, cs, r), Bool.and(D.Made(y, Cr.Cir.Cells.set(ms, z, xc), m0, D.Fd(ka, Cr.Cir.Cells.set(ms, z, xc), r), S, T, cs), Bool.and(D.Made(w, Cr.Cir.Cells.set(ms, z, xc), m0, D.Fd(kb, Cr.Cir.Cells.set(ms, z, xc), r), S, T, cs), D.Made(v, Cr.Cir.Cells.set(ms, z, xc), m0, D.Fd(kc, Cr.Cir.Cells.set(ms, z, xc), r), S, T, cs))))) == True{} : Bool}:
  +M2 = Cr.Cir.Cells.set(ms, z, xc)
  +hn2 = hn
  +ne = K.or.fl(U32.is_eq(r, z), Bool.or(D.Node(y, ms, D.Fd(ka, ms, r), z), Bool.or(D.Node(w, ms, D.Fd(kb, ms, r), z), D.Node(v, ms, D.Fd(kc, ms, r), z))), hn2)
  +nr = K.or.fr(U32.is_eq(r, z), Bool.or(D.Node(y, ms, D.Fd(ka, ms, r), z), Bool.or(D.Node(w, ms, D.Fd(kb, ms, r), z), D.Node(v, ms, D.Fd(kc, ms, r), z))), hn2)
  %Equal.sym(U32, D.Fd(ka, M2, r), D.Fd(ka, ms, r), C.made.fd(ka, ms, r, z, xc, ne)) :
    {Bool.or(D.Nodes(S, m0, r), Bool.and(D.Nw(M2, m0, S, T, cs, r), Bool.and(D.Made(y, M2, m0, _, S, T, cs), Bool.and(D.Made(w, M2, m0, D.Fd(kb, M2, r), S, T, cs), D.Made(v, M2, m0, D.Fd(kc, M2, r), S, T, cs))))) == True{} : Bool}
  %Equal.sym(U32, D.Fd(kb, M2, r), D.Fd(kb, ms, r), C.made.fd(kb, ms, r, z, xc, ne)) :
    {Bool.or(D.Nodes(S, m0, r), Bool.and(D.Nw(M2, m0, S, T, cs, r), Bool.and(D.Made(y, M2, m0, D.Fd(ka, ms, r), S, T, cs), Bool.and(D.Made(w, M2, m0, _, S, T, cs), D.Made(v, M2, m0, D.Fd(kc, M2, r), S, T, cs))))) == True{} : Bool}
  %Equal.sym(U32, D.Fd(kc, M2, r), D.Fd(kc, ms, r), C.made.fd(kc, ms, r, z, xc, ne)) :
    {Bool.or(D.Nodes(S, m0, r), Bool.and(D.Nw(M2, m0, S, T, cs, r), Bool.and(D.Made(y, M2, m0, D.Fd(ka, ms, r), S, T, cs), Bool.and(D.Made(w, M2, m0, D.Fd(kb, ms, r), S, T, cs), D.Made(v, M2, m0, _, S, T, cs))))) == True{} : Bool}
  C.made.cell(D.Nodes(S, m0, r), D.Nw(ms, m0, S, T, cs, r), Bool.and(D.Made(y, ms, m0, D.Fd(ka, ms, r), S, T, cs), Bool.and(D.Made(w, ms, m0, D.Fd(kb, ms, r), S, T, cs), D.Made(v, ms, m0, D.Fd(kc, ms, r), S, T, cs))),
    D.Nw(M2, m0, S, T, cs, r), Bool.and(D.Made(y, M2, m0, D.Fd(ka, ms, r), S, T, cs), Bool.and(D.Made(w, M2, m0, D.Fd(kb, ms, r), S, T, cs), D.Made(v, M2, m0, D.Fd(kc, ms, r), S, T, cs))), h,
    q => C.made.nw(ms, m0, S, T, cs, r, z, xc, ne, q),
    q =>
      +q2 = q
      K.Bo.and_i(D.Made(y, M2, m0, D.Fd(ka, ms, r), S, T, cs), Bool.and(D.Made(w, M2, m0, D.Fd(kb, ms, r), S, T, cs), D.Made(v, M2, m0, D.Fd(kc, ms, r), S, T, cs)),
        fy(D.Fd(ka, ms, r), K.or.fl(D.Node(y, ms, D.Fd(ka, ms, r), z), Bool.or(D.Node(w, ms, D.Fd(kb, ms, r), z), D.Node(v, ms, D.Fd(kc, ms, r), z)), nr), K.Bo.and_l(D.Made(y, ms, m0, D.Fd(ka, ms, r), S, T, cs), Bool.and(D.Made(w, ms, m0, D.Fd(kb, ms, r), S, T, cs), D.Made(v, ms, m0, D.Fd(kc, ms, r), S, T, cs)), q2)),
        K.Bo.and_i(D.Made(w, M2, m0, D.Fd(kb, ms, r), S, T, cs), D.Made(v, M2, m0, D.Fd(kc, ms, r), S, T, cs),
          fw(D.Fd(kb, ms, r), K.or.fl(D.Node(w, ms, D.Fd(kb, ms, r), z), D.Node(v, ms, D.Fd(kc, ms, r), z), K.or.fr(D.Node(y, ms, D.Fd(ka, ms, r), z), Bool.or(D.Node(w, ms, D.Fd(kb, ms, r), z), D.Node(v, ms, D.Fd(kc, ms, r), z)), nr)), K.Bo.and_l(D.Made(w, ms, m0, D.Fd(kb, ms, r), S, T, cs), D.Made(v, ms, m0, D.Fd(kc, ms, r), S, T, cs), K.Bo.and_r(D.Made(y, ms, m0, D.Fd(ka, ms, r), S, T, cs), Bool.and(D.Made(w, ms, m0, D.Fd(kb, ms, r), S, T, cs), D.Made(v, ms, m0, D.Fd(kc, ms, r), S, T, cs)), q2))),
          fv(D.Fd(kc, ms, r), K.or.fr(D.Node(w, ms, D.Fd(kb, ms, r), z), D.Node(v, ms, D.Fd(kc, ms, r), z), K.or.fr(D.Node(y, ms, D.Fd(ka, ms, r), z), Bool.or(D.Node(w, ms, D.Fd(kb, ms, r), z), D.Node(v, ms, D.Fd(kc, ms, r), z)), nr)), K.Bo.and_r(D.Made(w, ms, m0, D.Fd(kb, ms, r), S, T, cs), D.Made(v, ms, m0, D.Fd(kc, ms, r), S, T, cs), K.Bo.and_r(D.Made(y, ms, m0, D.Fd(ka, ms, r), S, T, cs), Bool.and(D.Made(w, ms, m0, D.Fd(kb, ms, r), S, T, cs), D.Made(v, ms, m0, D.Fd(kc, ms, r), S, T, cs)), q2))))))

# a store at a cell z that is no node of the result u at r keeps what u is made of
def made.set(u: Bk.Term, +ms: Cr.Cir.Cells, +m0: Cr.Cir.Cells, +r: U32, +S: List<&2, D.Rt>, +T: List<&2, U32>,
  +cs: List<&2, D.Pr>, +z: U32, +xc: Cr.Cir.Cell, hn: {D.Node(u, ms, r, z) == False{} : Bool},
  h: {D.Made(u, ms, m0, r, S, T, cs) == True{} : Bool}) -> {D.Made(u, Cr.Cir.Cells.set(ms, z, xc), m0, r, S, T, cs) == True{} : Bool}:
  match u:
    case Bk.Term.Var{_}:
      C.made.or(D.Nodes(S, m0, r), D.New(ms, T, r), D.New(Cr.Cir.Cells.set(ms, z, xc), T, r), h, q => C.made.new(ms, T, r, z, xc, hn, q))
    case Bk.Term.Ref{_}:
      h
    case Bk.Term.Ann{+y, +w}:
      made.bin(ms, m0, S, T, cs, r, z, xc, 2n, 3n, y, w, hn, h, a => na => q => made.set(y, ms, m0, a, S, T, cs, z, xc, na, q),
        a => na => q => made.set(w, ms, m0, a, S, T, cs, z, xc, na, q))
    case Bk.Term.Let{_, +y, +w}:
      made.bin(ms, m0, S, T, cs, r, z, xc, 2n, 3n, y, w, hn, h, a => na => q => made.set(y, ms, m0, a, S, T, cs, z, xc, na, q),
        a => na => q => made.set(w, ms, m0, a, S, T, cs, z, xc, na, q))
    case Bk.Term.Typ{+y}:
      made.una(ms, m0, S, T, cs, r, z, xc, 2n, y, hn, h, a => na => q => made.set(y, ms, m0, a, S, T, cs, z, xc, na, q))
    case Bk.Term.Min{+y, +w}:
      made.bin(ms, m0, S, T, cs, r, z, xc, 2n, 3n, y, w, hn, h, a => na => q => made.set(y, ms, m0, a, S, T, cs, z, xc, na, q),
        a => na => q => made.set(w, ms, m0, a, S, T, cs, z, xc, na, q))
    case Bk.Term.All{_, +y, +w}:
      made.bin(ms, m0, S, T, cs, r, z, xc, 2n, 3n, y, w, hn, h, a => na => q => made.set(y, ms, m0, a, S, T, cs, z, xc, na, q),
        a => na => q => made.set(w, ms, m0, a, S, T, cs, z, xc, na, q))
    case Bk.Term.Lam{_, +y}:
      made.una(ms, m0, S, T, cs, r, z, xc, 2n, y, hn, h, a => na => q => made.set(y, ms, m0, a, S, T, cs, z, xc, na, q))
    case Bk.Term.App{_, +y, +w}:
      made.bin(ms, m0, S, T, cs, r, z, xc, 2n, 3n, y, w, hn, h, a => na => q => made.set(y, ms, m0, a, S, T, cs, z, xc, na, q),
        a => na => q => made.set(w, ms, m0, a, S, T, cs, z, xc, na, q))
    case Bk.Term.Sig{_, +y, +w}:
      made.bin(ms, m0, S, T, cs, r, z, xc, 2n, 3n, y, w, hn, h, a => na => q => made.set(y, ms, m0, a, S, T, cs, z, xc, na, q),
        a => na => q => made.set(w, ms, m0, a, S, T, cs, z, xc, na, q))
    case Bk.Term.Tup{_, +y, +w}:
      made.bin(ms, m0, S, T, cs, r, z, xc, 2n, 3n, y, w, hn, h, a => na => q => made.set(y, ms, m0, a, S, T, cs, z, xc, na, q),
        a => na => q => made.set(w, ms, m0, a, S, T, cs, z, xc, na, q))
    case Bk.Term.Prj{+y}:
      made.una(ms, m0, S, T, cs, r, z, xc, 2n, y, hn, h, a => na => q => made.set(y, ms, m0, a, S, T, cs, z, xc, na, q))
    case Bk.Term.Enu{_}:
      h
    case Bk.Term.Lab{_}:
      C.made.or(D.Nodes(S, m0, r), D.Nw(ms, m0, S, T, cs, r), D.Nw(Cr.Cir.Cells.set(ms, z, xc), m0, S, T, cs, r), h,
        q => C.made.nw(ms, m0, S, T, cs, r, z, xc, hn, q))
    case Bk.Term.Mat{_, +y, +w}:
      made.bin(ms, m0, S, T, cs, r, z, xc, 3n, 4n, y, w, hn, h, a => na => q => made.set(y, ms, m0, a, S, T, cs, z, xc, na, q),
        a => na => q => made.set(w, ms, m0, a, S, T, cs, z, xc, na, q))
    case Bk.Term.Efq{}:
      C.made.or(D.Nodes(S, m0, r), D.Nw(ms, m0, S, T, cs, r), D.Nw(Cr.Cir.Cells.set(ms, z, xc), m0, S, T, cs, r), h,
        q => C.made.nw(ms, m0, S, T, cs, r, z, xc, hn, q))
    case Bk.Term.Eql{+y, +w, +v}:
      made.ter(ms, m0, S, T, cs, r, z, xc, 2n, 3n, 4n, y, w, v, hn, h, a => na => q => made.set(y, ms, m0, a, S, T, cs, z, xc, na, q),
        a => na => q => made.set(w, ms, m0, a, S, T, cs, z, xc, na, q), a => na => q => made.set(v, ms, m0, a, S, T, cs, z, xc, na, q))
    case Bk.Term.Rfl{}:
      C.made.or(D.Nodes(S, m0, r), D.Nw(ms, m0, S, T, cs, r), D.Nw(Cr.Cir.Cells.set(ms, z, xc), m0, S, T, cs, r), h,
        q => C.made.nw(ms, m0, S, T, cs, r, z, xc, hn, q))
    case Bk.Term.Rwt{+y, +w, +v}:
      made.ter(ms, m0, S, T, cs, r, z, xc, 2n, 3n, 4n, y, w, v, hn, h, a => na => q => made.set(y, ms, m0, a, S, T, cs, z, xc, na, q),
        a => na => q => made.set(w, ms, m0, a, S, T, cs, z, xc, na, q), a => na => q => made.set(v, ms, m0, a, S, T, cs, z, xc, na, q))
