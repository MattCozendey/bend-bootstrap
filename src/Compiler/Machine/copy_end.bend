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
  +tg: U32, +z: U32, +xc: Cr.Cir.Cell, +ka: Nat, +y: Bk.Term,
  hn: {Bool.or(U32.is_eq(r, z), D.Node(y, ms, D.Fd(ka, ms, r), z)) == False{} : Bool},
  h: {Bool.or(D.Nodes(S, m0, r), Bool.and(D.Nw(ms, m0, S, T, cs, r, tg), D.Made(y, ms, m0, D.Fd(ka, ms, r), S, T, cs))) == True{} : Bool},
  fy: @a: U32 -> {D.Node(y, ms, a, z) == False{} : Bool} -> {D.Made(y, ms, m0, a, S, T, cs) == True{} : Bool} ->
    {D.Made(y, Cr.Cir.Cells.set(ms, z, xc), m0, a, S, T, cs) == True{} : Bool}) ->
  {Bool.or(D.Nodes(S, m0, r), Bool.and(D.Nw(Cr.Cir.Cells.set(ms, z, xc), m0, S, T, cs, r, tg), D.Made(y, Cr.Cir.Cells.set(ms, z, xc), m0, D.Fd(ka, Cr.Cir.Cells.set(ms, z, xc), r), S, T, cs))) == True{} : Bool}:
  +M2 = Cr.Cir.Cells.set(ms, z, xc)
  +hn2 = hn
  +ne = K.or.fl(U32.is_eq(r, z), D.Node(y, ms, D.Fd(ka, ms, r), z), hn2)
  +nr = K.or.fr(U32.is_eq(r, z), D.Node(y, ms, D.Fd(ka, ms, r), z), hn2)
  %Equal.sym(U32, D.Fd(ka, M2, r), D.Fd(ka, ms, r), C.made.fd(ka, ms, r, z, xc, ne)) :
    {Bool.or(D.Nodes(S, m0, r), Bool.and(D.Nw(M2, m0, S, T, cs, r, tg), D.Made(y, M2, m0, _, S, T, cs))) == True{} : Bool}
  C.made.cell(D.Nodes(S, m0, r), D.Nw(ms, m0, S, T, cs, r, tg), D.Made(y, ms, m0, D.Fd(ka, ms, r), S, T, cs),
    D.Nw(M2, m0, S, T, cs, r, tg), D.Made(y, M2, m0, D.Fd(ka, ms, r), S, T, cs), h,
    q => C.made.nw(ms, m0, S, T, cs, r, tg, z, xc, ne, q),
    q =>
      +q2 = q
      fy(D.Fd(ka, ms, r), nr, q2))

# a node of two parts, in the fields ka and kb of r, stays made when each part does
def made.bin(+ms: Cr.Cir.Cells, +m0: Cr.Cir.Cells, +S: List<&2, D.Rt>, +T: List<&2, U32>, +cs: List<&2, D.Pr>, +r: U32,
  +tg: U32, +z: U32, +xc: Cr.Cir.Cell, +ka: Nat, +kb: Nat, +y: Bk.Term, +w: Bk.Term,
  hn: {Bool.or(U32.is_eq(r, z), Bool.or(D.Node(y, ms, D.Fd(ka, ms, r), z), D.Node(w, ms, D.Fd(kb, ms, r), z))) == False{} : Bool},
  h: {Bool.or(D.Nodes(S, m0, r), Bool.and(D.Nw(ms, m0, S, T, cs, r, tg), Bool.and(D.Made(y, ms, m0, D.Fd(ka, ms, r), S, T, cs), D.Made(w, ms, m0, D.Fd(kb, ms, r), S, T, cs)))) == True{} : Bool},
  fy: @a: U32 -> {D.Node(y, ms, a, z) == False{} : Bool} -> {D.Made(y, ms, m0, a, S, T, cs) == True{} : Bool} ->
    {D.Made(y, Cr.Cir.Cells.set(ms, z, xc), m0, a, S, T, cs) == True{} : Bool},
  fw: @a: U32 -> {D.Node(w, ms, a, z) == False{} : Bool} -> {D.Made(w, ms, m0, a, S, T, cs) == True{} : Bool} ->
    {D.Made(w, Cr.Cir.Cells.set(ms, z, xc), m0, a, S, T, cs) == True{} : Bool}) ->
  {Bool.or(D.Nodes(S, m0, r), Bool.and(D.Nw(Cr.Cir.Cells.set(ms, z, xc), m0, S, T, cs, r, tg), Bool.and(D.Made(y, Cr.Cir.Cells.set(ms, z, xc), m0, D.Fd(ka, Cr.Cir.Cells.set(ms, z, xc), r), S, T, cs), D.Made(w, Cr.Cir.Cells.set(ms, z, xc), m0, D.Fd(kb, Cr.Cir.Cells.set(ms, z, xc), r), S, T, cs)))) == True{} : Bool}:
  +M2 = Cr.Cir.Cells.set(ms, z, xc)
  +hn2 = hn
  +ne = K.or.fl(U32.is_eq(r, z), Bool.or(D.Node(y, ms, D.Fd(ka, ms, r), z), D.Node(w, ms, D.Fd(kb, ms, r), z)), hn2)
  +nr = K.or.fr(U32.is_eq(r, z), Bool.or(D.Node(y, ms, D.Fd(ka, ms, r), z), D.Node(w, ms, D.Fd(kb, ms, r), z)), hn2)
  %Equal.sym(U32, D.Fd(ka, M2, r), D.Fd(ka, ms, r), C.made.fd(ka, ms, r, z, xc, ne)) :
    {Bool.or(D.Nodes(S, m0, r), Bool.and(D.Nw(M2, m0, S, T, cs, r, tg), Bool.and(D.Made(y, M2, m0, _, S, T, cs), D.Made(w, M2, m0, D.Fd(kb, M2, r), S, T, cs)))) == True{} : Bool}
  %Equal.sym(U32, D.Fd(kb, M2, r), D.Fd(kb, ms, r), C.made.fd(kb, ms, r, z, xc, ne)) :
    {Bool.or(D.Nodes(S, m0, r), Bool.and(D.Nw(M2, m0, S, T, cs, r, tg), Bool.and(D.Made(y, M2, m0, D.Fd(ka, ms, r), S, T, cs), D.Made(w, M2, m0, _, S, T, cs)))) == True{} : Bool}
  C.made.cell(D.Nodes(S, m0, r), D.Nw(ms, m0, S, T, cs, r, tg), Bool.and(D.Made(y, ms, m0, D.Fd(ka, ms, r), S, T, cs), D.Made(w, ms, m0, D.Fd(kb, ms, r), S, T, cs)),
    D.Nw(M2, m0, S, T, cs, r, tg), Bool.and(D.Made(y, M2, m0, D.Fd(ka, ms, r), S, T, cs), D.Made(w, M2, m0, D.Fd(kb, ms, r), S, T, cs)), h,
    q => C.made.nw(ms, m0, S, T, cs, r, tg, z, xc, ne, q),
    q =>
      +q2 = q
      K.Bo.and_i(D.Made(y, M2, m0, D.Fd(ka, ms, r), S, T, cs), D.Made(w, M2, m0, D.Fd(kb, ms, r), S, T, cs),
        fy(D.Fd(ka, ms, r), K.or.fl(D.Node(y, ms, D.Fd(ka, ms, r), z), D.Node(w, ms, D.Fd(kb, ms, r), z), nr), K.Bo.and_l(D.Made(y, ms, m0, D.Fd(ka, ms, r), S, T, cs), D.Made(w, ms, m0, D.Fd(kb, ms, r), S, T, cs), q2)),
        fw(D.Fd(kb, ms, r), K.or.fr(D.Node(y, ms, D.Fd(ka, ms, r), z), D.Node(w, ms, D.Fd(kb, ms, r), z), nr), K.Bo.and_r(D.Made(y, ms, m0, D.Fd(ka, ms, r), S, T, cs), D.Made(w, ms, m0, D.Fd(kb, ms, r), S, T, cs), q2))))

# a node of three parts, in the fields ka to kc of r, stays made when each part does
def made.ter(+ms: Cr.Cir.Cells, +m0: Cr.Cir.Cells, +S: List<&2, D.Rt>, +T: List<&2, U32>, +cs: List<&2, D.Pr>, +r: U32,
  +tg: U32, +z: U32, +xc: Cr.Cir.Cell, +ka: Nat, +kb: Nat, +kc: Nat, +y: Bk.Term, +w: Bk.Term, +v: Bk.Term,
  hn: {Bool.or(U32.is_eq(r, z), Bool.or(D.Node(y, ms, D.Fd(ka, ms, r), z), Bool.or(D.Node(w, ms, D.Fd(kb, ms, r), z), D.Node(v, ms, D.Fd(kc, ms, r), z)))) == False{} : Bool},
  h: {Bool.or(D.Nodes(S, m0, r), Bool.and(D.Nw(ms, m0, S, T, cs, r, tg), Bool.and(D.Made(y, ms, m0, D.Fd(ka, ms, r), S, T, cs), Bool.and(D.Made(w, ms, m0, D.Fd(kb, ms, r), S, T, cs), D.Made(v, ms, m0, D.Fd(kc, ms, r), S, T, cs))))) == True{} : Bool},
  fy: @a: U32 -> {D.Node(y, ms, a, z) == False{} : Bool} -> {D.Made(y, ms, m0, a, S, T, cs) == True{} : Bool} ->
    {D.Made(y, Cr.Cir.Cells.set(ms, z, xc), m0, a, S, T, cs) == True{} : Bool},
  fw: @a: U32 -> {D.Node(w, ms, a, z) == False{} : Bool} -> {D.Made(w, ms, m0, a, S, T, cs) == True{} : Bool} ->
    {D.Made(w, Cr.Cir.Cells.set(ms, z, xc), m0, a, S, T, cs) == True{} : Bool},
  fv: @a: U32 -> {D.Node(v, ms, a, z) == False{} : Bool} -> {D.Made(v, ms, m0, a, S, T, cs) == True{} : Bool} ->
    {D.Made(v, Cr.Cir.Cells.set(ms, z, xc), m0, a, S, T, cs) == True{} : Bool}) ->
  {Bool.or(D.Nodes(S, m0, r), Bool.and(D.Nw(Cr.Cir.Cells.set(ms, z, xc), m0, S, T, cs, r, tg), Bool.and(D.Made(y, Cr.Cir.Cells.set(ms, z, xc), m0, D.Fd(ka, Cr.Cir.Cells.set(ms, z, xc), r), S, T, cs), Bool.and(D.Made(w, Cr.Cir.Cells.set(ms, z, xc), m0, D.Fd(kb, Cr.Cir.Cells.set(ms, z, xc), r), S, T, cs), D.Made(v, Cr.Cir.Cells.set(ms, z, xc), m0, D.Fd(kc, Cr.Cir.Cells.set(ms, z, xc), r), S, T, cs))))) == True{} : Bool}:
  +M2 = Cr.Cir.Cells.set(ms, z, xc)
  +hn2 = hn
  +ne = K.or.fl(U32.is_eq(r, z), Bool.or(D.Node(y, ms, D.Fd(ka, ms, r), z), Bool.or(D.Node(w, ms, D.Fd(kb, ms, r), z), D.Node(v, ms, D.Fd(kc, ms, r), z))), hn2)
  +nr = K.or.fr(U32.is_eq(r, z), Bool.or(D.Node(y, ms, D.Fd(ka, ms, r), z), Bool.or(D.Node(w, ms, D.Fd(kb, ms, r), z), D.Node(v, ms, D.Fd(kc, ms, r), z))), hn2)
  %Equal.sym(U32, D.Fd(ka, M2, r), D.Fd(ka, ms, r), C.made.fd(ka, ms, r, z, xc, ne)) :
    {Bool.or(D.Nodes(S, m0, r), Bool.and(D.Nw(M2, m0, S, T, cs, r, tg), Bool.and(D.Made(y, M2, m0, _, S, T, cs), Bool.and(D.Made(w, M2, m0, D.Fd(kb, M2, r), S, T, cs), D.Made(v, M2, m0, D.Fd(kc, M2, r), S, T, cs))))) == True{} : Bool}
  %Equal.sym(U32, D.Fd(kb, M2, r), D.Fd(kb, ms, r), C.made.fd(kb, ms, r, z, xc, ne)) :
    {Bool.or(D.Nodes(S, m0, r), Bool.and(D.Nw(M2, m0, S, T, cs, r, tg), Bool.and(D.Made(y, M2, m0, D.Fd(ka, ms, r), S, T, cs), Bool.and(D.Made(w, M2, m0, _, S, T, cs), D.Made(v, M2, m0, D.Fd(kc, M2, r), S, T, cs))))) == True{} : Bool}
  %Equal.sym(U32, D.Fd(kc, M2, r), D.Fd(kc, ms, r), C.made.fd(kc, ms, r, z, xc, ne)) :
    {Bool.or(D.Nodes(S, m0, r), Bool.and(D.Nw(M2, m0, S, T, cs, r, tg), Bool.and(D.Made(y, M2, m0, D.Fd(ka, ms, r), S, T, cs), Bool.and(D.Made(w, M2, m0, D.Fd(kb, ms, r), S, T, cs), D.Made(v, M2, m0, _, S, T, cs))))) == True{} : Bool}
  C.made.cell(D.Nodes(S, m0, r), D.Nw(ms, m0, S, T, cs, r, tg), Bool.and(D.Made(y, ms, m0, D.Fd(ka, ms, r), S, T, cs), Bool.and(D.Made(w, ms, m0, D.Fd(kb, ms, r), S, T, cs), D.Made(v, ms, m0, D.Fd(kc, ms, r), S, T, cs))),
    D.Nw(M2, m0, S, T, cs, r, tg), Bool.and(D.Made(y, M2, m0, D.Fd(ka, ms, r), S, T, cs), Bool.and(D.Made(w, M2, m0, D.Fd(kb, ms, r), S, T, cs), D.Made(v, M2, m0, D.Fd(kc, ms, r), S, T, cs))), h,
    q => C.made.nw(ms, m0, S, T, cs, r, tg, z, xc, ne, q),
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
      C.made.or(D.Nodes(S, m0, r), D.New(ms, T, r, 0), D.New(Cr.Cir.Cells.set(ms, z, xc), T, r, 0), h, q => C.made.new(ms, T, r, 0, z, xc, hn, q))
    case Bk.Term.Ref{_}:
      h
    case Bk.Term.Ann{+y, +w}:
      made.bin(ms, m0, S, T, cs, r, 2, z, xc, 2n, 3n, y, w, hn, h, a => na => q => made.set(y, ms, m0, a, S, T, cs, z, xc, na, q),
        a => na => q => made.set(w, ms, m0, a, S, T, cs, z, xc, na, q))
    case Bk.Term.Let{_, +y, +w}:
      made.bin(ms, m0, S, T, cs, r, 3, z, xc, 2n, 3n, y, w, hn, h, a => na => q => made.set(y, ms, m0, a, S, T, cs, z, xc, na, q),
        a => na => q => made.set(w, ms, m0, a, S, T, cs, z, xc, na, q))
    case Bk.Term.Typ{+y}:
      made.una(ms, m0, S, T, cs, r, 4, z, xc, 2n, y, hn, h, a => na => q => made.set(y, ms, m0, a, S, T, cs, z, xc, na, q))
    case Bk.Term.Min{+y, +w}:
      made.bin(ms, m0, S, T, cs, r, 5, z, xc, 2n, 3n, y, w, hn, h, a => na => q => made.set(y, ms, m0, a, S, T, cs, z, xc, na, q),
        a => na => q => made.set(w, ms, m0, a, S, T, cs, z, xc, na, q))
    case Bk.Term.All{_, +y, +w}:
      made.bin(ms, m0, S, T, cs, r, 6, z, xc, 2n, 3n, y, w, hn, h, a => na => q => made.set(y, ms, m0, a, S, T, cs, z, xc, na, q),
        a => na => q => made.set(w, ms, m0, a, S, T, cs, z, xc, na, q))
    case Bk.Term.Lam{_, +y}:
      made.una(ms, m0, S, T, cs, r, 7, z, xc, 2n, y, hn, h, a => na => q => made.set(y, ms, m0, a, S, T, cs, z, xc, na, q))
    case Bk.Term.App{_, +y, +w}:
      made.bin(ms, m0, S, T, cs, r, 8, z, xc, 2n, 3n, y, w, hn, h, a => na => q => made.set(y, ms, m0, a, S, T, cs, z, xc, na, q),
        a => na => q => made.set(w, ms, m0, a, S, T, cs, z, xc, na, q))
    case Bk.Term.Sig{_, +y, +w}:
      made.bin(ms, m0, S, T, cs, r, 9, z, xc, 2n, 3n, y, w, hn, h, a => na => q => made.set(y, ms, m0, a, S, T, cs, z, xc, na, q),
        a => na => q => made.set(w, ms, m0, a, S, T, cs, z, xc, na, q))
    case Bk.Term.Tup{_, +y, +w}:
      made.bin(ms, m0, S, T, cs, r, 10, z, xc, 2n, 3n, y, w, hn, h, a => na => q => made.set(y, ms, m0, a, S, T, cs, z, xc, na, q),
        a => na => q => made.set(w, ms, m0, a, S, T, cs, z, xc, na, q))
    case Bk.Term.Prj{+y}:
      made.una(ms, m0, S, T, cs, r, 11, z, xc, 2n, y, hn, h, a => na => q => made.set(y, ms, m0, a, S, T, cs, z, xc, na, q))
    case Bk.Term.Enu{_}:
      h
    case Bk.Term.Lab{_}:
      C.made.or(D.Nodes(S, m0, r), D.Nw(ms, m0, S, T, cs, r, 13), D.Nw(Cr.Cir.Cells.set(ms, z, xc), m0, S, T, cs, r, 13), h,
        q => C.made.nw(ms, m0, S, T, cs, r, 13, z, xc, hn, q))
    case Bk.Term.Mat{_, +y, +w}:
      made.bin(ms, m0, S, T, cs, r, 14, z, xc, 3n, 4n, y, w, hn, h, a => na => q => made.set(y, ms, m0, a, S, T, cs, z, xc, na, q),
        a => na => q => made.set(w, ms, m0, a, S, T, cs, z, xc, na, q))
    case Bk.Term.Efq{}:
      C.made.or(D.Nodes(S, m0, r), D.Nw(ms, m0, S, T, cs, r, 15), D.Nw(Cr.Cir.Cells.set(ms, z, xc), m0, S, T, cs, r, 15), h,
        q => C.made.nw(ms, m0, S, T, cs, r, 15, z, xc, hn, q))
    case Bk.Term.Eql{+y, +w, +v}:
      made.ter(ms, m0, S, T, cs, r, 16, z, xc, 2n, 3n, 4n, y, w, v, hn, h, a => na => q => made.set(y, ms, m0, a, S, T, cs, z, xc, na, q),
        a => na => q => made.set(w, ms, m0, a, S, T, cs, z, xc, na, q), a => na => q => made.set(v, ms, m0, a, S, T, cs, z, xc, na, q))
    case Bk.Term.Rfl{}:
      C.made.or(D.Nodes(S, m0, r), D.Nw(ms, m0, S, T, cs, r, 17), D.Nw(Cr.Cir.Cells.set(ms, z, xc), m0, S, T, cs, r, 17), h,
        q => C.made.nw(ms, m0, S, T, cs, r, 17, z, xc, hn, q))
    case Bk.Term.Rwt{+y, +w, +v}:
      made.ter(ms, m0, S, T, cs, r, 18, z, xc, 2n, 3n, 4n, y, w, v, hn, h, a => na => q => made.set(y, ms, m0, a, S, T, cs, z, xc, na, q),
        a => na => q => made.set(w, ms, m0, a, S, T, cs, z, xc, na, q), a => na => q => made.set(v, ms, m0, a, S, T, cs, z, xc, na, q))

# One cell across the store
# -------------------------

# a cell other than z keeps its STATIC flag
def stc.ne(+m: Cr.Cir.Cells, +z: U32, +xc: Cr.Cir.Cell, +c: U32, ne: {U32.is_eq(c, z) == False{} : Bool}) ->
  {D.Stc(Cr.Cir.Cells.set(m, z, xc), c) == D.Stc(m, c) : Bool}:
  Equal.cong(U32, Bool, w => U32.is_ne(U32.and(w, 1024), 0), D.Fd(0n, Cr.Cir.Cells.set(m, z, xc), c), D.Fd(0n, m, c),
    C.made.fd(0n, m, c, z, xc, ne))

# a cell other than z keeps its fields 0 and 2 to 4
def same.at.ne(+m0: Cr.Cir.Cells, +m: Cr.Cir.Cells, +z: U32, +xc: Cr.Cir.Cell, +c: U32, ne: {U32.is_eq(c, z) == False{} : Bool}) ->
  {D.Same.at(m0, Cr.Cir.Cells.set(m, z, xc), c) == D.Same.at(m0, m, c) : Bool}:
  %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, xc), c), Cr.Cir.Cells.get(m, c), K.Cl.get_ne(m, c, z, xc, ne)) :
    {Bool.and(U32.is_eq(Cr.Cir.Cell.get(0n, _), D.Fd(0n, m0, c)), Bool.and(U32.is_eq(Cr.Cir.Cell.get(2n, _), D.Fd(2n, m0, c)),
      Bool.and(U32.is_eq(Cr.Cir.Cell.get(3n, _), D.Fd(3n, m0, c)), U32.is_eq(Cr.Cir.Cell.get(4n, _), D.Fd(4n, m0, c))))) == D.Same.at(m0, m, c) : Bool}
  {==}

# z, once in T, is not another cell c out of T
def has.ne.b(e: Bool, +T: List<&2, U32>, +z: U32, +c: U32, ez: {U32.is_eq(z, c) == e : Bool}, hz: {D.Has(T, z) == True{} : Bool},
  hc: {D.Has(T, c) == False{} : Bool}) -> {e == False{} : Bool}:
  match e:
    case True{}:
      Equal.trans(Bool, True{}, D.Has(T, c), False{},
        Equal.sym(Bool, D.Has(T, c), True{}, (%K.U.eq(z, c, ez) : {D.Has(T, _) == True{} : Bool}; hz)), hc)
    case False{}:
      {==}

def has.ne(+T: List<&2, U32>, +z: U32, +c: U32, hz: {D.Has(T, z) == True{} : Bool}, hc: {D.Has(T, c) == False{} : Bool}) ->
  {U32.is_eq(z, c) == False{} : Bool}:
  has.ne.b(U32.is_eq(z, c), T, z, c, {==}, hz, hc)

# the n cells from c, none of them z, keep their fields 0 and 2 to 4
def same.ne(n: Nat, +m0: Cr.Cir.Cells, +m: Cr.Cir.Cells, +z: U32, +xc: Cr.Cir.Cell, +c: U32, hn: {K.Ne(n, c, z) == True{} : Bool},
  h: {D.Same(n, m0, m, c) == True{} : Bool}) -> {D.Same(n, m0, Cr.Cir.Cells.set(m, z, xc), c) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      +ms = Cr.Cir.Cells.set(m, z, xc)
      +hn2 = hn
      +h2 = h
      +ne = K.Bo.not_t(U32.is_eq(c, z), K.Bo.and_l(Bool.not(U32.is_eq(c, z)), K.Ne(p, U32.inc(c), z), hn2))
      %Equal.sym(Bool, D.Same.at(m0, ms, c), D.Same.at(m0, m, c), same.at.ne(m0, m, z, xc, c, ne)) :
        {Bool.and(_, D.Same(p, m0, ms, U32.inc(c))) == True{} : Bool}
      K.Bo.and_i(D.Same.at(m0, m, c), D.Same(p, m0, ms, U32.inc(c)), K.Bo.and_l(D.Same.at(m0, m, c), D.Same(p, m0, m, U32.inc(c)), h2),
        same.ne(p, m0, m, z, xc, U32.inc(c), K.Bo.and_r(Bool.not(U32.is_eq(c, z)), K.Ne(p, U32.inc(c), z), hn2),
          K.Bo.and_r(D.Same.at(m0, m, c), D.Same(p, m0, m, U32.inc(c)), h2)))

# The roots and the kept cells
# ----------------------------

# a store at z, which the run may not read, keeps the roots' checked terms
def rts.wx(rs: List<&2, D.Rt>, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +K: U32, +F: U32,
  +X: List<&2, U32>, +N: U32, +z: U32, +xc: Cr.Cir.Cell, +hi: {False{} == D.Al(K, F, X, N, z) : Bool},
  h: D.Rts(m, ks, img, K, F, X, N, rs)) -> D.Rts(Cr.Cir.Cells.set(m, z, xc), ks, img, K, F, X, N, rs):
  match rs:
    case Nil{}:
      h
    case Con{D.Rt{+f, +c, +t}, +rest}:
      (ht, hr) = h
      (C.Tm.wx(f, m, ks, img, K, F, X, N, c, z, xc, t, hi, ht), rts.wx(rest, m, ks, img, K, F, X, N, z, xc, hi, hr))

# z, which may not be read and is none of E, is no kept cell
def kc.ok.z(+K: U32, +F: U32, +X: List<&2, U32>, +N: U32, +E: List<&2, U32>, +z: U32, +cl: Cr.Cir.Cell,
  hal: {D.Al(K, F, X, N, z) == False{} : Bool}, he: {D.Has(E, z) == False{} : Bool}) -> {D.Kc.ok(K, F, X, N, E, z, cl) == False{} : Bool}:
  +tg = U32.to_nat(U32.and(Cr.Cir.Cell.get(0n, cl), 63))
  %Equal.sym(Bool, D.Al(K, F, X, N, z), False{}, hal) :
    {Bool.or(Bool.and(_, Nat.is_le(19n, tg)), Bool.and(D.Has(E, z), Bool.and(Bool.and(U32.is_le(F, z), U32.is_lt(z, N)), Nat.is_le(19n, tg)))) == False{} : Bool}
  %Equal.sym(Bool, D.Has(E, z), False{}, he) :
    {Bool.or(Bool.and(False{}, Nat.is_le(19n, tg)), Bool.and(_, Bool.and(Bool.and(U32.is_le(F, z), U32.is_lt(z, N)), Nat.is_le(19n, tg)))) == False{} : Bool}
  {==}

def kc.ne.b(e: Bool, +K: U32, +F: U32, +X: List<&2, U32>, +N: U32, +E: List<&2, U32>, +x: U32, +z: U32, +cl: Cr.Cir.Cell,
  ex: {U32.is_eq(x, z) == e : Bool}, hal: {D.Al(K, F, X, N, z) == False{} : Bool}, he: {D.Has(E, z) == False{} : Bool},
  hok: {D.Kc.ok(K, F, X, N, E, x, cl) == True{} : Bool}) -> {e == False{} : Bool}:
  match e:
    case True{}:
      Equal.trans(Bool, True{}, D.Kc.ok(K, F, X, N, E, z, cl), False{},
        Equal.sym(Bool, D.Kc.ok(K, F, X, N, E, z, cl), True{}, (%K.U.eq(x, z, ex) : {D.Kc.ok(K, F, X, N, E, _, cl) == True{} : Bool}; hok)),
        kc.ok.z(K, F, X, N, E, z, cl, hal, he))
    case False{}:
      {==}

# a store at z, which is no kept cell, keeps the kept cells
def kcs.wx(kc: List<&2, D.Kc>, +m: Cr.Cir.Cells, +K: U32, +F: U32, +X: List<&2, U32>, +N: U32, +E: List<&2, U32>, +z: U32,
  +xc: Cr.Cir.Cell, +hal: {D.Al(K, F, X, N, z) == False{} : Bool}, +he: {D.Has(E, z) == False{} : Bool},
  h: D.Kcs(m, K, F, X, N, E, kc)) -> D.Kcs(Cr.Cir.Cells.set(m, z, xc), K, F, X, N, E, kc):
  match kc:
    case Nil{}:
      h
    case Con{D.Kc{+x, +cl}, +rest}:
      (hg, h2) = h
      (hok, hr) = h2
      +hok2 = hok
      (Equal.trans(Cr.Cir.Cell, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, xc), x), Cr.Cir.Cells.get(m, x), cl,
         K.Cl.get_ne(m, x, z, xc, kc.ne.b(U32.is_eq(x, z), K, F, X, N, E, x, z, cl, {==}, hal, he, hok2)), hg),
       (hok2, kcs.wx(rest, m, K, F, X, N, E, z, xc, hal, he, hr)))

# The cover
# ---------

def cv.at.b(e: Bool, +m: Cr.Cir.Cells, +c: U32, +P: List<&2, U32>, +z: U32, +xc: Cr.Cir.Cell, +g: Nat, +r: U32, +u: Bk.Term,
  +RH: List<&2, D.Rt>, +xs: List<&2, U32>, ec: {U32.is_eq(z, c) == e : Bool}, +hn: {D.Nodes(Con{D.Rt{g, r, u}, RH}, m, z) == False{} : Bool},
  h: {Bool.or(D.Stc(m, c), Bool.or(D.Has(P, c), Bool.or(D.Nodes(Con{D.Rt{0n, r, u}, RH}, m, c), Bool.or(e, D.Has(xs, c))))) == True{} : Bool}) ->
  {Bool.or(D.Stc(Cr.Cir.Cells.set(m, z, xc), c), Bool.or(Bool.or(e, D.Has(P, c)), Bool.or(D.Nodes(Con{D.Rt{g, r, u}, RH}, Cr.Cir.Cells.set(m, z, xc), c),
    D.Has(xs, c)))) == True{} : Bool}:
  match e:
    case True{}:
      +ms = Cr.Cir.Cells.set(m, z, xc)
      K.Bo.or_ir(D.Stc(ms, c), Bool.or(Bool.or(True{}, D.Has(P, c)), Bool.or(D.Nodes(Con{D.Rt{g, r, u}, RH}, ms, c), D.Has(xs, c))), {==})
    case False{}:
      +ms = Cr.Cir.Cells.set(m, z, xc)
      +rg = {Con{D.Rt{g, r, u}, RH} : List<&2, D.Rt>}
      %Equal.sym(Bool, D.Stc(ms, c), D.Stc(m, c), stc.ne(m, z, xc, c, K.U.ne.sym(z, c, ec))) :
        {Bool.or(_, Bool.or(D.Has(P, c), Bool.or(D.Nodes(rg, ms, c), D.Has(xs, c)))) == True{} : Bool}
      %Equal.sym(Bool, D.Nodes(rg, ms, c), D.Nodes(rg, m, c), C.nodes.set(rg, m, z, xc, c, hn)) :
        {Bool.or(D.Stc(m, c), Bool.or(D.Has(P, c), Bool.or(_, D.Has(xs, c)))) == True{} : Bool}
      h

# the cover after the store at the root z: z leaves the walk's cells for the
# garbage, and the result's root, now with its fuel g, keeps its nodes
def cv.end(n: Nat, +m: Cr.Cir.Cells, +c: U32, +P: List<&2, U32>, +z: U32, +xc: Cr.Cir.Cell, +g: Nat, +r: U32, +u: Bk.Term,
  +RH: List<&2, D.Rt>, +xs: List<&2, U32>, +hn: {D.Nodes(Con{D.Rt{g, r, u}, RH}, m, z) == False{} : Bool},
  h: {D.Cv(n, m, c, P, Con{D.Rt{0n, r, u}, RH}, Con{z, xs}) == True{} : Bool}) ->
  {D.Cv(n, Cr.Cir.Cells.set(m, z, xc), c, Con{z, P}, Con{D.Rt{g, r, u}, RH}, xs) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      +ms = Cr.Cir.Cells.set(m, z, xc)
      +r0 = {Con{D.Rt{0n, r, u}, RH} : List<&2, D.Rt>}
      +rg = {Con{D.Rt{g, r, u}, RH} : List<&2, D.Rt>}
      +h2 = h
      +A0 = Bool.or(D.Stc(m, c), Bool.or(D.Has(P, c), Bool.or(D.Nodes(r0, m, c), D.Has(Con{z, xs}, c))))
      K.Bo.and_i(Bool.or(D.Stc(ms, c), Bool.or(D.Has(Con{z, P}, c), Bool.or(D.Nodes(rg, ms, c), D.Has(xs, c)))),
        D.Cv(p, ms, U32.inc(c), Con{z, P}, rg, xs),
        cv.at.b(U32.is_eq(z, c), m, c, P, z, xc, g, r, u, RH, xs, {==}, hn, K.Bo.and_l(A0, D.Cv(p, m, U32.inc(c), P, r0, Con{z, xs}), h2)),
        cv.end(p, m, U32.inc(c), P, z, xc, g, r, u, RH, xs, hn, K.Bo.and_r(A0, D.Cv(p, m, U32.inc(c), P, r0, Con{z, xs}), h2)))

# The closure
# -----------

# cells ys none of which is z keep their STATIC flags
def all.static.ne(ys: List<&2, U32>, +m: Cr.Cir.Cells, +z: U32, +xc: Cr.Cir.Cell, h: {D.Occ(ys, z) == 0n : Nat}) ->
  {D.All.static(ys, Cr.Cir.Cells.set(m, z, xc)) == D.All.static(ys, m) : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      +ms = Cr.Cir.Cells.set(m, z, xc)
      +h2 = h
      %Equal.sym(Bool, D.Stc(ms, y), D.Stc(m, y), stc.ne(m, z, xc, y, W.nof.z(U32.is_eq(y, z), W.Na.add0l(D.Nat.of(U32.is_eq(y, z)), D.Occ(rest, z), h2)))) :
        {Bool.and(_, D.All.static(rest, ms)) == Bool.and(D.Stc(m, y), D.All.static(rest, m)) : Bool}
      %Equal.sym(Bool, D.All.static(rest, ms), D.All.static(rest, m),
        all.static.ne(rest, m, z, xc, K.Na.add0r(D.Nat.of(U32.is_eq(y, z)), D.Occ(rest, z), h2))) :
        {Bool.and(D.Stc(m, y), _) == Bool.and(D.Stc(m, y), D.All.static(rest, m)) : Bool}
      {==}

def all.held.ne(ys: List<&2, U32>, +m: Cr.Cir.Cells, +z: U32, +xc: Cr.Cir.Cell, +cs: List<&2, U32>, +hc: List<&2, U32>,
  h: {D.Occ(ys, z) == 0n : Nat}) -> {D.All.held(ys, Cr.Cir.Cells.set(m, z, xc), cs, hc) == D.All.held(ys, m, cs, hc) : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      +ms = Cr.Cir.Cells.set(m, z, xc)
      +h2 = h
      %Equal.sym(Bool, D.Stc(ms, y), D.Stc(m, y), stc.ne(m, z, xc, y, W.nof.z(U32.is_eq(y, z), W.Na.add0l(D.Nat.of(U32.is_eq(y, z)), D.Occ(rest, z), h2)))) :
        {Bool.and(Bool.or(_, Bool.or(D.Has(cs, y), D.Has(hc, y))), D.All.held(rest, ms, cs, hc)) ==
          Bool.and(Bool.or(D.Stc(m, y), Bool.or(D.Has(cs, y), D.Has(hc, y))), D.All.held(rest, m, cs, hc)) : Bool}
      %Equal.sym(Bool, D.All.held(rest, ms, cs, hc), D.All.held(rest, m, cs, hc),
        all.held.ne(rest, m, z, xc, cs, hc, K.Na.add0r(D.Nat.of(U32.is_eq(y, z)), D.Occ(rest, z), h2))) :
        {Bool.and(Bool.or(D.Stc(m, y), Bool.or(D.Has(cs, y), D.Has(hc, y))), _) ==
          Bool.and(Bool.or(D.Stc(m, y), Bool.or(D.Has(cs, y), D.Has(hc, y))), D.All.held(rest, m, cs, hc)) : Bool}
      {==}

# a cell other than z, none of whose pointers is z, keeps its closure
def clo.at.ne(+m: Cr.Cir.Cells, +z: U32, +xc: Cr.Cir.Cell, +c: U32, +Q: List<&2, U32>, +cs: List<&2, U32>, +hc: List<&2, U32>,
  +ne: {U32.is_eq(c, z) == False{} : Bool}, +ho: {D.Occ(D.Ps(m, Q, c), z) == 0n : Nat}, +hz: N.Le(291n, U32.to_nat(z))) ->
  {D.Clo.at(Cr.Cir.Cells.set(m, z, xc), c, Con{z, Q}, cs, hc) == D.Clo.at(m, c, Q, cs, hc) : Bool}:
  +ms = Cr.Cir.Cells.set(m, z, xc)
  +ps = D.Ps(m, Q, c)
  %Equal.sym(List<&2, U32>, D.Ps(ms, Con{z, Q}, c), ps, ps.zo(m, z, xc, Q, c, ne, hz)) :
    {Bool.and(Bool.or(Bool.not(D.Stc(ms, c)), D.All.static(_, ms)), Bool.or(Bool.not(D.Has(cs, c)), D.All.held(_, ms, cs, hc))) ==
      D.Clo.at(m, c, Q, cs, hc) : Bool}
  %Equal.sym(Bool, D.Stc(ms, c), D.Stc(m, c), stc.ne(m, z, xc, c, ne)) :
    {Bool.and(Bool.or(Bool.not(_), D.All.static(ps, ms)), Bool.or(Bool.not(D.Has(cs, c)), D.All.held(ps, ms, cs, hc))) ==
      D.Clo.at(m, c, Q, cs, hc) : Bool}
  %Equal.sym(Bool, D.All.static(ps, ms), D.All.static(ps, m), all.static.ne(ps, m, z, xc, ho)) :
    {Bool.and(Bool.or(Bool.not(D.Stc(m, c)), _), Bool.or(Bool.not(D.Has(cs, c)), D.All.held(ps, ms, cs, hc))) ==
      D.Clo.at(m, c, Q, cs, hc) : Bool}
  %Equal.sym(Bool, D.All.held(ps, ms, cs, hc), D.All.held(ps, m, cs, hc), all.held.ne(ps, m, z, xc, cs, hc, ho)) :
    {Bool.and(Bool.or(Bool.not(D.Stc(m, c)), D.All.static(ps, m)), Bool.or(Bool.not(D.Has(cs, c)), _)) ==
      D.Clo.at(m, c, Q, cs, hc) : Bool}
  {==}

# the released root holds no pointer, so its closure holds
def clo.at.z(+m: Cr.Cir.Cells, +z: U32, +xc: Cr.Cir.Cell, +Q: List<&2, U32>, +cs: List<&2, U32>, +hc: List<&2, U32>,
  +h0: {Cr.Cir.Cell.get(0n, xc) == 45 : U32}) -> {D.Clo.at(Cr.Cir.Cells.set(m, z, xc), z, Con{z, Q}, cs, hc) == True{} : Bool}:
  +ms = Cr.Cir.Cells.set(m, z, xc)
  %Equal.sym(List<&2, U32>, D.Ps(ms, Con{z, Q}, z), Nil{}, ps.z0(m, z, xc, Con{z, Q}, h0)) :
    {Bool.and(Bool.or(Bool.not(D.Stc(ms, z)), D.All.static(_, ms)), Bool.or(Bool.not(D.Has(cs, z)), D.All.held(_, ms, cs, hc))) == True{} : Bool}
  K.Bo.and_i(Bool.or(Bool.not(D.Stc(ms, z)), D.All.static(Nil{}, ms)), Bool.or(Bool.not(D.Has(cs, z)), D.All.held(Nil{}, ms, cs, hc)),
    K.Bo.or_ir(Bool.not(D.Stc(ms, z)), D.All.static(Nil{}, ms), {==}), K.Bo.or_ir(Bool.not(D.Has(cs, z)), D.All.held(Nil{}, ms, cs, hc), {==}))

def clo.at.b(e: Bool, +m: Cr.Cir.Cells, +c: U32, +Q: List<&2, U32>, +z: U32, +xc: Cr.Cir.Cell, +cs: List<&2, U32>, +hc: List<&2, U32>,
  +E: List<&2, U32>, ec: {U32.is_eq(z, c) == e : Bool}, +hz: N.Le(291n, U32.to_nat(z)), +h0: {Cr.Cir.Cell.get(0n, xc) == 45 : U32},
  +ho: {D.Occ(D.Ps(m, Q, c), z) == 0n : Nat}, h: {Bool.or(Bool.or(e, D.Has(E, c)), D.Clo.at(m, c, Q, cs, hc)) == True{} : Bool}) ->
  {Bool.or(D.Has(E, c), D.Clo.at(Cr.Cir.Cells.set(m, z, xc), c, Con{z, Q}, cs, hc)) == True{} : Bool}:
  match e:
    case True{}:
      K.Bo.or_ir(D.Has(E, c), D.Clo.at(Cr.Cir.Cells.set(m, z, xc), c, Con{z, Q}, cs, hc),
        (%K.U.eq(z, c, ec) : {D.Clo.at(Cr.Cir.Cells.set(m, z, xc), _, Con{z, Q}, cs, hc) == True{} : Bool}; clo.at.z(m, z, xc, Q, cs, hc, h0)))
    case False{}:
      %Equal.sym(Bool, D.Clo.at(Cr.Cir.Cells.set(m, z, xc), c, Con{z, Q}, cs, hc), D.Clo.at(m, c, Q, cs, hc),
        clo.at.ne(m, z, xc, c, Q, cs, hc, K.U.ne.sym(z, c, ec), ho, hz)) : {Bool.or(D.Has(E, c), _) == True{} : Bool}
      h

# the closure after the store at the root z: z leaves the cells E' that it
# need not hold for, and holds no pointer; no other cell points to z
def clo.end(n: Nat, +m: Cr.Cir.Cells, +c: U32, +Q: List<&2, U32>, +z: U32, +xc: Cr.Cir.Cell, +cs: List<&2, U32>, +hc: List<&2, U32>,
  +E: List<&2, U32>, +hz: N.Le(291n, U32.to_nat(z)), +h0: {Cr.Cir.Cell.get(0n, xc) == 45 : U32}, hp: {D.Pc(n, m, Q, c, z) == 0n : Nat},
  h: {D.Clo(n, m, c, Q, cs, hc, Con{z, E}) == True{} : Bool}) -> {D.Clo(n, Cr.Cir.Cells.set(m, z, xc), c, Con{z, Q}, cs, hc, E) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      +ms = Cr.Cir.Cells.set(m, z, xc)
      +hp2 = hp
      +h2 = h
      +A0 = Bool.or(D.Has(Con{z, E}, c), D.Clo.at(m, c, Q, cs, hc))
      K.Bo.and_i(Bool.or(D.Has(E, c), D.Clo.at(ms, c, Con{z, Q}, cs, hc)), D.Clo(p, ms, U32.inc(c), Con{z, Q}, cs, hc, E),
        clo.at.b(U32.is_eq(z, c), m, c, Q, z, xc, cs, hc, E, {==}, hz, h0, W.Na.add0l(D.Occ(D.Ps(m, Q, c), z), D.Pc(p, m, Q, U32.inc(c), z), hp2),
          K.Bo.and_l(A0, D.Clo(p, m, U32.inc(c), Q, cs, hc, Con{z, E}), h2)),
        clo.end(p, m, U32.inc(c), Q, z, xc, cs, hc, E, hz, h0, K.Na.add0r(D.Occ(D.Ps(m, Q, c), z), D.Pc(p, m, Q, U32.inc(c), z), hp2),
          K.Bo.and_r(A0, D.Clo(p, m, U32.inc(c), Q, cs, hc, Con{z, E}), h2)))

# The counts
# ----------

# the own cells' pointers to c after the store, and the result's register:
# those before, as the root's one pointer (to r) moves to the register
def cnt.end0(+b: Nat, +m: Cr.Cir.Cells, +z: U32, +xc: Cr.Cir.Cell, +Q: List<&2, U32>, +F: U32, +c: U32, +r: U32,
  +hz: N.Le(291n, U32.to_nat(z)), +h0: {Cr.Cir.Cell.get(0n, xc) == 45 : U32}, +honce: {W.Once(b, F, z) == True{} : Bool},
  +hps: {D.Ps(m, Q, z) == [r] : List<&2, U32>}) ->
  {Nat.add(D.Pc(b, Cr.Cir.Cells.set(m, z, xc), Con{z, Q}, F, c), D.Occ([r], c)) == D.Pc(b, m, Q, F, c) : Nat}:
  (%hps : {Nat.add(D.Pc(b, Cr.Cir.Cells.set(m, z, xc), Con{z, Q}, F, c), D.Occ(_, c)) == D.Pc(b, m, Q, F, c) : Nat};
    pc.z(b, m, z, xc, Q, F, c, hz, h0, honce))

def cnt.end(+b: Nat, +m: Cr.Cir.Cells, +z: U32, +xc: Cr.Cir.Cell, +Q: List<&2, U32>, +F: U32, +c: U32, +r: U32,
  +hz: N.Le(291n, U32.to_nat(z)), +h0: {Cr.Cir.Cell.get(0n, xc) == 45 : U32}, +honce: {W.Once(b, F, z) == True{} : Bool},
  +hps: {D.Ps(m, Q, z) == [r] : List<&2, U32>}) ->
  {Nat.add(D.Pc(b, Cr.Cir.Cells.set(m, z, xc), Con{z, Q}, F, c), D.Occ([r], c)) == Nat.add(D.Pc(b, m, Q, F, c), D.Occ(Nil{}, c)) : Nat}:
  Equal.trans(Nat, Nat.add(D.Pc(b, Cr.Cir.Cells.set(m, z, xc), Con{z, Q}, F, c), D.Occ([r], c)), D.Pc(b, m, Q, F, c),
    Nat.add(D.Pc(b, m, Q, F, c), D.Occ(Nil{}, c)), cnt.end0(b, m, z, xc, Q, F, c, r, hz, h0, honce, hps),
    Equal.sym(Nat, Nat.add(D.Pc(b, m, Q, F, c), 0n), D.Pc(b, m, Q, F, c), N.add_zero(D.Pc(b, m, Q, F, c))))

# What stays
# ----------

def kept.at.f(+m0: Cr.Cir.Cells, +m: Cr.Cir.Cells, +c: U32, +P: List<&2, U32>, +F: U32, +a: Nat, +b: Nat, +Q0: List<&2, U32>,
  +Q: List<&2, U32>, +z: U32, +xc: Cr.Cir.Cell, +r: U32, +ne: {U32.is_eq(z, c) == False{} : Bool},
  +ecnt: {Nat.add(D.Pc(b, Cr.Cir.Cells.set(m, z, xc), Con{z, Q}, F, c), D.Occ([r], c)) == Nat.add(D.Pc(b, m, Q, F, c), D.Occ(Nil{}, c)) : Nat},
  h: {Bool.and(D.Same.at(m0, m, c), Bool.or(Bool.or(U32.is_le(19, U32.and(D.Fd(0n, m0, c), 63)), Bool.or(D.Stc(m0, c), D.Has(P, c))),
    Nat.is_eq(Nat.add(U32.to_nat(D.Fd(1n, m, c)), Nat.add(D.Pc(a, m0, Q0, F, c), D.Occ(Nil{}, c))),
      Nat.add(U32.to_nat(D.Fd(1n, m0, c)), Nat.add(D.Pc(b, m, Q, F, c), D.Occ(Nil{}, c)))))) == True{} : Bool}) ->
  {Bool.and(D.Same.at(m0, Cr.Cir.Cells.set(m, z, xc), c), Bool.or(Bool.or(U32.is_le(19, U32.and(D.Fd(0n, m0, c), 63)),
    Bool.or(D.Stc(m0, c), D.Has(Con{z, P}, c))),
    Nat.is_eq(Nat.add(U32.to_nat(D.Fd(1n, Cr.Cir.Cells.set(m, z, xc), c)), Nat.add(D.Pc(a, m0, Q0, F, c), D.Occ(Nil{}, c))),
      Nat.add(U32.to_nat(D.Fd(1n, m0, c)), Nat.add(D.Pc(b, Cr.Cir.Cells.set(m, z, xc), Con{z, Q}, F, c), D.Occ([r], c)))))) == True{} : Bool}:
  +ms = Cr.Cir.Cells.set(m, z, xc)
  +nc = K.U.ne.sym(z, c, ne)
  +T19 = U32.is_le(19, U32.and(D.Fd(0n, m0, c), 63))
  +L0 = Nat.add(D.Pc(a, m0, Q0, F, c), D.Occ(Nil{}, c))
  %Equal.sym(Bool, D.Same.at(m0, ms, c), D.Same.at(m0, m, c), same.at.ne(m0, m, z, xc, c, nc)) :
    {Bool.and(_, Bool.or(Bool.or(T19, Bool.or(D.Stc(m0, c), Bool.or(U32.is_eq(z, c), D.Has(P, c)))),
      Nat.is_eq(Nat.add(U32.to_nat(D.Fd(1n, ms, c)), L0), Nat.add(U32.to_nat(D.Fd(1n, m0, c)), Nat.add(D.Pc(b, ms, Con{z, Q}, F, c), D.Occ([r], c)))))) == True{} : Bool}
  %Equal.sym(Bool, U32.is_eq(z, c), False{}, ne) :
    {Bool.and(D.Same.at(m0, m, c), Bool.or(Bool.or(T19, Bool.or(D.Stc(m0, c), Bool.or(_, D.Has(P, c)))),
      Nat.is_eq(Nat.add(U32.to_nat(D.Fd(1n, ms, c)), L0), Nat.add(U32.to_nat(D.Fd(1n, m0, c)), Nat.add(D.Pc(b, ms, Con{z, Q}, F, c), D.Occ([r], c)))))) == True{} : Bool}
  %Equal.sym(U32, D.Fd(1n, ms, c), D.Fd(1n, m, c), C.made.fd(1n, m, c, z, xc, nc)) :
    {Bool.and(D.Same.at(m0, m, c), Bool.or(Bool.or(T19, Bool.or(D.Stc(m0, c), D.Has(P, c))),
      Nat.is_eq(Nat.add(U32.to_nat(_), L0), Nat.add(U32.to_nat(D.Fd(1n, m0, c)), Nat.add(D.Pc(b, ms, Con{z, Q}, F, c), D.Occ([r], c)))))) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(D.Pc(b, ms, Con{z, Q}, F, c), D.Occ([r], c)), Nat.add(D.Pc(b, m, Q, F, c), D.Occ(Nil{}, c)), ecnt) :
    {Bool.and(D.Same.at(m0, m, c), Bool.or(Bool.or(T19, Bool.or(D.Stc(m0, c), D.Has(P, c))),
      Nat.is_eq(Nat.add(U32.to_nat(D.Fd(1n, m, c)), L0), Nat.add(U32.to_nat(D.Fd(1n, m0, c)), _)))) == True{} : Bool}
  h

def kept.at.b(t: Bool, +m0: Cr.Cir.Cells, +m: Cr.Cir.Cells, +c: U32, +T: List<&2, U32>, +P: List<&2, U32>, +F: U32, +a: Nat, +b: Nat,
  +Q0: List<&2, U32>, +Q: List<&2, U32>, +z: U32, +xc: Cr.Cir.Cell, +r: U32, et: {D.Has(T, c) == t : Bool},
  +hTz: {D.Has(T, z) == True{} : Bool},
  +ecnt: {Nat.add(D.Pc(b, Cr.Cir.Cells.set(m, z, xc), Con{z, Q}, F, c), D.Occ([r], c)) == Nat.add(D.Pc(b, m, Q, F, c), D.Occ(Nil{}, c)) : Nat},
  h: {Bool.or(t, Bool.and(D.Same.at(m0, m, c), Bool.or(Bool.or(U32.is_le(19, U32.and(D.Fd(0n, m0, c), 63)), Bool.or(D.Stc(m0, c), D.Has(P, c))),
    Nat.is_eq(Nat.add(U32.to_nat(D.Fd(1n, m, c)), Nat.add(D.Pc(a, m0, Q0, F, c), D.Occ(Nil{}, c))),
      Nat.add(U32.to_nat(D.Fd(1n, m0, c)), Nat.add(D.Pc(b, m, Q, F, c), D.Occ(Nil{}, c))))))) == True{} : Bool}) ->
  {Bool.or(t, Bool.and(D.Same.at(m0, Cr.Cir.Cells.set(m, z, xc), c), Bool.or(Bool.or(U32.is_le(19, U32.and(D.Fd(0n, m0, c), 63)),
    Bool.or(D.Stc(m0, c), D.Has(Con{z, P}, c))),
    Nat.is_eq(Nat.add(U32.to_nat(D.Fd(1n, Cr.Cir.Cells.set(m, z, xc), c)), Nat.add(D.Pc(a, m0, Q0, F, c), D.Occ(Nil{}, c))),
      Nat.add(U32.to_nat(D.Fd(1n, m0, c)), Nat.add(D.Pc(b, Cr.Cir.Cells.set(m, z, xc), Con{z, Q}, F, c), D.Occ([r], c))))))) == True{} : Bool}:
  match t:
    case True{}:
      {==}
    case False{}:
      kept.at.f(m0, m, c, P, F, a, b, Q0, Q, z, xc, r, has.ne(T, z, c, hTz, et), ecnt, h)

# what stays after the store at the root z: z is taken, it joins the
# garbage and the pend list, and its one pointer (to r) goes to the result's
# register
def kept.end(k: Nat, +m0: Cr.Cir.Cells, +m: Cr.Cir.Cells, +c: U32, +T: List<&2, U32>, +P: List<&2, U32>, +F: U32, +a: Nat, +b: Nat,
  +Q0: List<&2, U32>, +Q: List<&2, U32>, +z: U32, +xc: Cr.Cir.Cell, +r: U32, +hTz: {D.Has(T, z) == True{} : Bool},
  +hz: N.Le(291n, U32.to_nat(z)), +h0: {Cr.Cir.Cell.get(0n, xc) == 45 : U32}, +honce: {W.Once(b, F, z) == True{} : Bool},
  +hps: {D.Ps(m, Q, z) == [r] : List<&2, U32>}, h: {D.Kept(k, m0, m, c, T, P, F, a, b, Q0, Q, Nil{}, Nil{}) == True{} : Bool}) ->
  {D.Kept(k, m0, Cr.Cir.Cells.set(m, z, xc), c, T, Con{z, P}, F, a, b, Q0, Con{z, Q}, Nil{}, [r]) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+(+p):
      +ms = Cr.Cir.Cells.set(m, z, xc)
      +h2 = h
      +A0 = Bool.or(D.Has(T, c), Bool.and(D.Same.at(m0, m, c), Bool.or(Bool.or(U32.is_le(19, U32.and(D.Fd(0n, m0, c), 63)),
        Bool.or(D.Stc(m0, c), D.Has(P, c))), Nat.is_eq(Nat.add(U32.to_nat(D.Fd(1n, m, c)), Nat.add(D.Pc(a, m0, Q0, F, c), D.Occ(Nil{}, c))),
          Nat.add(U32.to_nat(D.Fd(1n, m0, c)), Nat.add(D.Pc(b, m, Q, F, c), D.Occ(Nil{}, c)))))))
      +A1 = Bool.or(D.Has(T, c), Bool.and(D.Same.at(m0, ms, c), Bool.or(Bool.or(U32.is_le(19, U32.and(D.Fd(0n, m0, c), 63)),
        Bool.or(D.Stc(m0, c), D.Has(Con{z, P}, c))), Nat.is_eq(Nat.add(U32.to_nat(D.Fd(1n, ms, c)), Nat.add(D.Pc(a, m0, Q0, F, c), D.Occ(Nil{}, c))),
          Nat.add(U32.to_nat(D.Fd(1n, m0, c)), Nat.add(D.Pc(b, ms, Con{z, Q}, F, c), D.Occ([r], c)))))))
      K.Bo.and_i(A1, D.Kept(p, m0, ms, U32.inc(c), T, Con{z, P}, F, a, b, Q0, Con{z, Q}, Nil{}, [r]),
        kept.at.b(D.Has(T, c), m0, m, c, T, P, F, a, b, Q0, Q, z, xc, r, {==}, hTz, cnt.end(b, m, z, xc, Q, F, c, r, hz, h0, honce, hps),
          K.Bo.and_l(A0, D.Kept(p, m0, m, U32.inc(c), T, P, F, a, b, Q0, Q, Nil{}, Nil{}), h2)),
        kept.end(p, m0, m, U32.inc(c), T, P, F, a, b, Q0, Q, z, xc, r, hTz, hz, h0, honce, hps,
          K.Bo.and_r(A0, D.Kept(p, m0, m, U32.inc(c), T, P, F, a, b, Q0, Q, Nil{}, Nil{}), h2)))

# The taken cells
# ---------------

def tc.at.b(e: Bool, +m: Cr.Cir.Cells, +c: U32, +P: List<&2, U32>, +Q: List<&2, U32>, +n: Nat, +F: U32, +z: U32, +xc: Cr.Cir.Cell,
  +r: U32, ec: {U32.is_eq(z, c) == e : Bool},
  +ecnt: {Nat.add(D.Pc(n, Cr.Cir.Cells.set(m, z, xc), Con{z, Q}, F, c), D.Occ([r], c)) == D.Pc(n, m, Q, F, c) : Nat},
  h: {Bool.or(D.Has(P, c), Bool.or(Bool.or(e, D.Has(Nil{}, c)), Nat.is_eq(U32.to_nat(D.Fd(1n, m, c)), D.Pc(n, m, Q, F, c)))) == True{} : Bool}) ->
  {Bool.or(Bool.or(e, D.Has(P, c)), Nat.is_eq(U32.to_nat(D.Fd(1n, Cr.Cir.Cells.set(m, z, xc), c)),
    Nat.add(D.Pc(n, Cr.Cir.Cells.set(m, z, xc), Con{z, Q}, F, c), D.Occ([r], c)))) == True{} : Bool}:
  match e:
    case True{}:
      {==}
    case False{}:
      +ms = Cr.Cir.Cells.set(m, z, xc)
      %Equal.sym(U32, D.Fd(1n, ms, c), D.Fd(1n, m, c), C.made.fd(1n, m, c, z, xc, K.U.ne.sym(z, c, ec))) :
        {Bool.or(Bool.or(False{}, D.Has(P, c)), Nat.is_eq(U32.to_nat(_), Nat.add(D.Pc(n, ms, Con{z, Q}, F, c), D.Occ([r], c)))) == True{} : Bool}
      %Equal.sym(Nat, Nat.add(D.Pc(n, ms, Con{z, Q}, F, c), D.Occ([r], c)), D.Pc(n, m, Q, F, c), ecnt) :
        {Bool.or(Bool.or(False{}, D.Has(P, c)), Nat.is_eq(U32.to_nat(D.Fd(1n, m, c)), _)) == True{} : Bool}
      h

# the taken cells count their pointers after the store at the root z, which
# joins the garbage
def tc.end(T: List<&2, U32>, +m: Cr.Cir.Cells, +P: List<&2, U32>, +Q: List<&2, U32>, +n: Nat, +F: U32, +z: U32, +xc: Cr.Cir.Cell,
  +r: U32, +hz: N.Le(291n, U32.to_nat(z)), +h0: {Cr.Cir.Cell.get(0n, xc) == 45 : U32}, +honce: {W.Once(n, F, z) == True{} : Bool},
  +hps: {D.Ps(m, Q, z) == [r] : List<&2, U32>}, h: {W.TcW(T, m, P, Q, Con{z, Nil{}}, n, F) == True{} : Bool}) ->
  {D.Tc(T, Cr.Cir.Cells.set(m, z, xc), Con{z, P}, Con{z, Q}, n, F, r) == True{} : Bool}:
  match T:
    case Nil{}:
      {==}
    case Con{+c, +rest}:
      +ms = Cr.Cir.Cells.set(m, z, xc)
      +h2 = h
      +A0 = Bool.or(D.Has(P, c), Bool.or(D.Has(Con{z, Nil{}}, c), Nat.is_eq(U32.to_nat(D.Fd(1n, m, c)), D.Pc(n, m, Q, F, c))))
      K.Bo.and_i(Bool.or(D.Has(Con{z, P}, c), Nat.is_eq(U32.to_nat(D.Fd(1n, ms, c)), Nat.add(D.Pc(n, ms, Con{z, Q}, F, c), D.Occ([r], c)))),
        D.Tc(rest, ms, Con{z, P}, Con{z, Q}, n, F, r),
        tc.at.b(U32.is_eq(z, c), m, c, P, Q, n, F, z, xc, r, {==}, cnt.end0(n, m, z, xc, Q, F, c, r, hz, h0, honce, hps),
          K.Bo.and_l(A0, W.TcW(rest, m, P, Q, Con{z, Nil{}}, n, F), h2)),
        tc.end(rest, m, P, Q, n, F, z, xc, r, hz, h0, honce, hps, K.Bo.and_r(A0, W.TcW(rest, m, P, Q, Con{z, Nil{}}, n, F), h2)))

def tk.at.b(e: Bool, +m: Cr.Cir.Cells, +c: U32, +P: List<&2, U32>, +z: U32, +xc: Cr.Cir.Cell, +r: U32, +u: Bk.Term,
  ec: {U32.is_eq(z, c) == e : Bool}, +hn: {D.Node(u, m, r, z) == False{} : Bool}, +h0: {Cr.Cir.Cell.get(0n, xc) == 45 : U32},
  h: {Bool.or(Bool.or(D.Node(u, m, r, c), D.Nodes(Nil{}, m, c)), Bool.or(e, D.Has(Nil{}, c))) == True{} : Bool}) ->
  {Bool.or(D.Node(u, Cr.Cir.Cells.set(m, z, xc), r, c), Bool.and(U32.is_eq(D.Fd(0n, Cr.Cir.Cells.set(m, z, xc), c), 45),
    Bool.or(e, D.Has(P, c)))) == True{} : Bool}:
  match e:
    case True{}:
      +ms = Cr.Cir.Cells.set(m, z, xc)
      K.Bo.or_ir(D.Node(u, ms, r, c), Bool.and(U32.is_eq(D.Fd(0n, ms, c), 45), Bool.or(True{}, D.Has(P, c))),
        (%K.U.eq(z, c, ec) : {Bool.and(U32.is_eq(D.Fd(0n, ms, _), 45), Bool.or(True{}, D.Has(P, c))) == True{} : Bool};
          (%Equal.sym(U32, D.Fd(0n, ms, z), 45, f0.z(m, z, xc, h0)) : {Bool.and(U32.is_eq(_, 45), Bool.or(True{}, D.Has(P, c))) == True{} : Bool}; {==})))
    case False{}:
      +ms = Cr.Cir.Cells.set(m, z, xc)
      %Equal.sym(Bool, D.Node(u, ms, r, c), D.Node(u, m, r, c), C.node.set(u, m, z, xc, r, c, hn)) :
        {Bool.or(_, Bool.and(U32.is_eq(D.Fd(0n, ms, c), 45), Bool.or(False{}, D.Has(P, c)))) == True{} : Bool}
      K.Bo.or_il(D.Node(u, m, r, c), Bool.and(U32.is_eq(D.Fd(0n, ms, c), 45), Bool.or(False{}, D.Has(P, c))),
        K.Bo.or_l(D.Node(u, m, r, c), D.Nodes(Nil{}, m, c),
          K.Bo.or_l(Bool.or(D.Node(u, m, r, c), D.Nodes(Nil{}, m, c)), Bool.or(False{}, D.Has(Nil{}, c)), h, {==}), {==}))

# each taken cell is a node of the result or the released root
def tk.end(T: List<&2, U32>, +m: Cr.Cir.Cells, +P: List<&2, U32>, +z: U32, +xc: Cr.Cir.Cell, +r: U32, +u: Bk.Term,
  +hn: {D.Node(u, m, r, z) == False{} : Bool}, +h0: {Cr.Cir.Cell.get(0n, xc) == 45 : U32},
  h: {W.TkW(T, m, Con{D.Rt{0n, r, u}, Nil{}}, Con{z, Nil{}}) == True{} : Bool}) ->
  {D.Tk(T, Cr.Cir.Cells.set(m, z, xc), u, r, Con{z, P}) == True{} : Bool}:
  match T:
    case Nil{}:
      {==}
    case Con{+c, +rest}:
      +ms = Cr.Cir.Cells.set(m, z, xc)
      +h2 = h
      +A0 = Bool.or(D.Nodes(Con{D.Rt{0n, r, u}, Nil{}}, m, c), D.Has(Con{z, Nil{}}, c))
      K.Bo.and_i(Bool.or(D.Node(u, ms, r, c), Bool.and(U32.is_eq(D.Fd(0n, ms, c), 45), D.Has(Con{z, P}, c))), D.Tk(rest, ms, u, r, Con{z, P}),
        tk.at.b(U32.is_eq(z, c), m, c, P, z, xc, r, u, {==}, hn, h0, K.Bo.and_l(A0, W.TkW(rest, m, Con{D.Rt{0n, r, u}, Nil{}}, Con{z, Nil{}}), h2)),
        tk.end(rest, m, P, z, xc, r, u, hn, h0, K.Bo.and_r(A0, W.TkW(rest, m, Con{D.Rt{0n, r, u}, Nil{}}, Con{z, Nil{}}), h2)))

# the old garbage, not taken, stays garbage
def gb.gw(P: List<&2, U32>, +P0: List<&2, U32>, +T: List<&2, U32>, +Qn: List<&2, U32>, +ms: Cr.Cir.Cells,
  h: {W.Gw(P, P0, T) == True{} : Bool}) -> {D.Gb(P, P0, T, Qn, ms) == True{} : Bool}:
  match P:
    case Nil{}:
      {==}
    case Con{+c, +rest}:
      +h2 = h
      +G = Bool.and(D.Has(P0, c), Bool.not(D.Has(T, c)))
      K.Bo.and_i(Bool.or(G, Bool.and(D.Has(T, c), Bool.and(U32.is_eq(D.Fd(0n, ms, c), 45), D.Has(Qn, c)))), D.Gb(rest, P0, T, Qn, ms),
        K.Bo.or_il(G, Bool.and(D.Has(T, c), Bool.and(U32.is_eq(D.Fd(0n, ms, c), 45), D.Has(Qn, c))), K.Bo.and_l(G, W.Gw(rest, P0, T), h2)),
        gb.gw(rest, P0, T, Qn, ms, K.Bo.and_r(G, W.Gw(rest, P0, T), h2)))

def nf.at.b(e: Bool, +m: Cr.Cir.Cells, +c: U32, +z: U32, +xc: Cr.Cir.Cell, ec: {U32.is_eq(z, c) == e : Bool},
  +h0: {Cr.Cir.Cell.get(0n, xc) == 45 : U32}, h: {Bool.or(Bool.or(e, D.Has(Nil{}, c)), U32.is_zero(U32.and(D.Fd(0n, m, c), 7936))) == True{} : Bool}) ->
  {U32.is_zero(U32.and(D.Fd(0n, Cr.Cir.Cells.set(m, z, xc), c), 7936)) == True{} : Bool}:
  match e:
    case True{}:
      +ms = Cr.Cir.Cells.set(m, z, xc)
      (%K.U.eq(z, c, ec) : {U32.is_zero(U32.and(D.Fd(0n, ms, _), 7936)) == True{} : Bool};
        (%Equal.sym(U32, D.Fd(0n, ms, z), 45, f0.z(m, z, xc, h0)) : {U32.is_zero(U32.and(_, 7936)) == True{} : Bool}; {==}))
    case False{}:
      %Equal.sym(U32, D.Fd(0n, Cr.Cir.Cells.set(m, z, xc), c), D.Fd(0n, m, c), C.made.fd(0n, m, c, z, xc, K.U.ne.sym(z, c, ec))) :
        {U32.is_zero(U32.and(_, 7936)) == True{} : Bool}
      h

# the taken cells hold no flag: the released root's header is K.root
def nf.end(T: List<&2, U32>, +m: Cr.Cir.Cells, +z: U32, +xc: Cr.Cir.Cell, +h0: {Cr.Cir.Cell.get(0n, xc) == 45 : U32},
  h: {W.NfX(T, m, Con{z, Nil{}}) == True{} : Bool}) -> {D.Nf(T, Cr.Cir.Cells.set(m, z, xc)) == True{} : Bool}:
  match T:
    case Nil{}:
      {==}
    case Con{+c, +rest}:
      +h2 = h
      +A0 = Bool.or(D.Has(Con{z, Nil{}}, c), U32.is_zero(U32.and(D.Fd(0n, m, c), 7936)))
      K.Bo.and_i(U32.is_zero(U32.and(D.Fd(0n, Cr.Cir.Cells.set(m, z, xc), c), 7936)), D.Nf(rest, Cr.Cir.Cells.set(m, z, xc)),
        nf.at.b(U32.is_eq(z, c), m, c, z, xc, {==}, h0, K.Bo.and_l(A0, W.NfX(rest, m, Con{z, Nil{}}), h2)),
        nf.end(rest, m, z, xc, h0, K.Bo.and_r(A0, W.NfX(rest, m, Con{z, Nil{}}), h2)))

# The allocation's invariant
# --------------------------

# a store at z, no cell of os, keeps their pointers Pp (their tags are the
# garbage's, so their masks stay)
def pp.ne(os: List<&2, U32>, +m: Cr.Cir.Cells, +P: List<&2, U32>, +Q: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32,
  +N: U32, +z: U32, +xc: Cr.Cir.Cell, +c: U32, h: {D.AL.cells(os, m, P, Q, zs, K, F, N) == True{} : Bool},
  hn: {D.Has(os, z) == False{} : Bool}, +hz: N.Le(291n, U32.to_nat(z))) -> {D.Pp(os, Cr.Cir.Cells.set(m, z, xc), c) == D.Pp(os, m, c) : Nat}:
  match os:
    case Nil{}:
      {==}
    case Con{+o, +rest}:
      +M2 = Cr.Cir.Cells.set(m, z, xc)
      +h2 = h
      +hn2 = hn
      +hd = K.al.hd(o, rest, m, P, Q, zs, K, F, N, h2)
      %Equal.sym(Nat, D.Ow(M2, o, c), D.Ow(m, o, c),
        K.ow.set(m, z, xc, o, c, D.Has(Q, o), K.or.fl(U32.is_eq(o, z), D.Has(rest, z), hn2), K.al.hd.tg(m, Q, o, F, N, hd), hz)) :
        {Nat.add(_, D.Pp(rest, M2, c)) == Nat.add(D.Ow(m, o, c), D.Pp(rest, m, c)) : Nat}
      %Equal.sym(Nat, D.Pp(rest, M2, c), D.Pp(rest, m, c), pp.ne(rest, m, P, Q, zs, K, F, N, z, xc, c, K.al.rest(o, rest, m, P, Q, zs, K, F, N, h2),
        K.or.fr(U32.is_eq(o, z), D.Has(rest, z), hn2), hz)) :
        {Nat.add(D.Ow(m, o, c), _) == Nat.add(D.Ow(m, o, c), D.Pp(rest, m, c)) : Nat}
      {==}

# the released root's mask is 0: its reuse drops nothing
def am.z0(+m: Cr.Cir.Cells, +z: U32, +xc: Cr.Cir.Cell, +h0: {Cr.Cir.Cell.get(0n, xc) == 45 : U32}) ->
  {D.Am(Cr.Cir.Cells.set(m, z, xc), z) == 0 : U32}:
  +ms = Cr.Cir.Cells.set(m, z, xc)
  %Equal.sym(U32, D.Fd(0n, ms, z), 45, f0.z(m, z, xc, h0)) :
    {Bool.pick(U32, U32.is_lt(U32.and(_, 63), 32), D.Fd(2n, ms, U32.add(272, U32.and(_, 63))), 0) == 0 : U32}
  {==}

# the released root points to nothing
def ow.z0(+m: Cr.Cir.Cells, +z: U32, +xc: Cr.Cir.Cell, +c: U32, +h0: {Cr.Cir.Cell.get(0n, xc) == 45 : U32}) ->
  {D.Ow(Cr.Cir.Cells.set(m, z, xc), z, c) == 0n : Nat}:
  +ms = Cr.Cir.Cells.set(m, z, xc)
  %Equal.sym(U32, D.Am(ms, z), 0, am.z0(m, z, xc, h0)) :
    {Nat.add(D.Nat.of(Bool.and(U32.is_ne(U32.and(_, 1), 0), U32.is_eq(D.Fd(2n, ms, z), c))),
      Nat.add(D.Nat.of(Bool.and(U32.is_ne(U32.and(_, 2), 0), U32.is_eq(D.Fd(3n, ms, z), c))),
        D.Nat.of(Bool.and(U32.is_ne(U32.and(_, 4), 0), U32.is_eq(D.Fd(4n, ms, z), c))))) == 0n : Nat}
  {==}

# the garbage with the released root at its head points to c as before
def pp.zp(+m: Cr.Cir.Cells, +P: List<&2, U32>, +Q: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +N: U32, +z: U32,
  +xc: Cr.Cir.Cell, +c: U32, +hcs: {D.AL.cells(P, m, P, Q, zs, K, F, N) == True{} : Bool}, +hPz: {D.Has(P, z) == False{} : Bool},
  +hz: N.Le(291n, U32.to_nat(z)), +h0: {Cr.Cir.Cell.get(0n, xc) == 45 : U32}) ->
  {D.Pp(Con{z, P}, Cr.Cir.Cells.set(m, z, xc), c) == D.Pp(P, m, c) : Nat}:
  +ms = Cr.Cir.Cells.set(m, z, xc)
  %Equal.sym(Nat, D.Ow(ms, z, c), 0n, ow.z0(m, z, xc, c, h0)) : {Nat.add(_, D.Pp(P, ms, c)) == D.Pp(P, m, c) : Nat}
  pp.ne(P, m, P, Q, zs, K, F, N, z, xc, c, hcs, hPz, hz)

# a part p, not z, of a garbage cell across the store at z
def part.end.z(+m: Cr.Cir.Cells, +P: List<&2, U32>, +Q: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +N: U32, +z: U32,
  +xc: Cr.Cir.Cell, +p: U32, +Zv: Nat, +ne: {U32.is_eq(p, z) == False{} : Bool}, +hcs: {D.AL.cells(P, m, P, Q, zs, K, F, N) == True{} : Bool},
  +hPz: {D.Has(P, z) == False{} : Bool}, +hz: N.Le(291n, U32.to_nat(z)), +h0: {Cr.Cir.Cell.get(0n, xc) == 45 : U32},
  h1: {Bool.or(U32.is_zero(p), Bool.and(Cr.Cir.is_cell(p, K, F, N), Bool.or(D.Stc(m, p), Bool.or(Bool.and(D.Has(P, p), Nat.is_lt(D.Zz(zs, p), Zv)),
    Nat.is_lt(D.Pp(P, m, p), U32.to_nat(D.Fd(1n, m, p))))))) == True{} : Bool}) ->
  {Bool.or(U32.is_zero(p), Bool.and(Cr.Cir.is_cell(p, K, F, N), Bool.or(D.Stc(Cr.Cir.Cells.set(m, z, xc), p),
    Bool.or(Bool.and(D.Has(Con{z, P}, p), Nat.is_lt(D.Zz(zs, p), Zv)),
      Nat.is_lt(D.Pp(Con{z, P}, Cr.Cir.Cells.set(m, z, xc), p), U32.to_nat(D.Fd(1n, Cr.Cir.Cells.set(m, z, xc), p))))))) == True{} : Bool}:
  +ms = Cr.Cir.Cells.set(m, z, xc)
  +IC = Cr.Cir.is_cell(p, K, F, N)
  +ZL = Nat.is_lt(D.Zz(zs, p), Zv)
  %Equal.sym(Bool, D.Stc(ms, p), D.Stc(m, p), stc.ne(m, z, xc, p, ne)) :
    {Bool.or(U32.is_zero(p), Bool.and(IC, Bool.or(_, Bool.or(Bool.and(D.Has(Con{z, P}, p), ZL),
      Nat.is_lt(D.Pp(Con{z, P}, ms, p), U32.to_nat(D.Fd(1n, ms, p))))))) == True{} : Bool}
  %Equal.sym(Bool, D.Has(Con{z, P}, p), D.Has(P, p), has.cons.ne(z, P, p, K.U.ne.sym(p, z, ne))) :
    {Bool.or(U32.is_zero(p), Bool.and(IC, Bool.or(D.Stc(m, p), Bool.or(Bool.and(_, ZL),
      Nat.is_lt(D.Pp(Con{z, P}, ms, p), U32.to_nat(D.Fd(1n, ms, p))))))) == True{} : Bool}
  %Equal.sym(Nat, D.Pp(Con{z, P}, ms, p), D.Pp(P, m, p), pp.zp(m, P, Q, zs, K, F, N, z, xc, p, hcs, hPz, hz, h0)) :
    {Bool.or(U32.is_zero(p), Bool.and(IC, Bool.or(D.Stc(m, p), Bool.or(Bool.and(D.Has(P, p), ZL),
      Nat.is_lt(_, U32.to_nat(D.Fd(1n, ms, p))))))) == True{} : Bool}
  %Equal.sym(U32, D.Fd(1n, ms, p), D.Fd(1n, m, p), C.made.fd(1n, m, p, z, xc, ne)) :
    {Bool.or(U32.is_zero(p), Bool.and(IC, Bool.or(D.Stc(m, p), Bool.or(Bool.and(D.Has(P, p), ZL),
      Nat.is_lt(D.Pp(P, m, p), U32.to_nat(_)))))) == True{} : Bool}
  h1

# a part of a garbage cell across the store at z: none, or not z
def part.end.s(s: Bool, +m: Cr.Cir.Cells, +P: List<&2, U32>, +Q: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +N: U32,
  +z: U32, +xc: Cr.Cir.Cell, +am: U32, +bit: U32, +p: U32, +Zv: Nat, +es: {U32.is_zero(U32.and(am, bit)) == s : Bool},
  +hcs: {D.AL.cells(P, m, P, Q, zs, K, F, N) == True{} : Bool}, +hPz: {D.Has(P, z) == False{} : Bool}, +hz: N.Le(291n, U32.to_nat(z)),
  +h0: {Cr.Cir.Cell.get(0n, xc) == 45 : U32}, h: {D.AL.part(m, P, zs, Zv, am, bit, p, K, F, N) == True{} : Bool},
  +hpz: {Bool.and(U32.is_ne(U32.and(am, bit), 0), U32.is_eq(p, z)) == False{} : Bool}) ->
  {D.AL.part(Cr.Cir.Cells.set(m, z, xc), Con{z, P}, zs, Zv, am, bit, p, K, F, N) == True{} : Bool}:
  match s:
    case True{}:
      +ms = Cr.Cir.Cells.set(m, z, xc)
      +R1N = Bool.or(U32.is_zero(p), Bool.and(Cr.Cir.is_cell(p, K, F, N), Bool.or(D.Stc(ms, p), Bool.or(Bool.and(D.Has(Con{z, P}, p),
        Nat.is_lt(D.Zz(zs, p), Zv)), Nat.is_lt(D.Pp(Con{z, P}, ms, p), U32.to_nat(D.Fd(1n, ms, p)))))))
      K.Bo.or_il(U32.is_zero(U32.and(am, bit)), R1N, es)
    case False{}:
      +ms = Cr.Cir.Cells.set(m, z, xc)
      +R1N = Bool.or(U32.is_zero(p), Bool.and(Cr.Cir.is_cell(p, K, F, N), Bool.or(D.Stc(ms, p), Bool.or(Bool.and(D.Has(Con{z, P}, p),
        Nat.is_lt(D.Zz(zs, p), Zv)), Nat.is_lt(D.Pp(Con{z, P}, ms, p), U32.to_nat(D.Fd(1n, ms, p)))))))
      +R1O = Bool.or(U32.is_zero(p), Bool.and(Cr.Cir.is_cell(p, K, F, N), Bool.or(D.Stc(m, p), Bool.or(Bool.and(D.Has(P, p),
        Nat.is_lt(D.Zz(zs, p), Zv)), Nat.is_lt(D.Pp(P, m, p), U32.to_nat(D.Fd(1n, m, p)))))))
      +ne = {(%es : {Bool.and(Bool.not(_), U32.is_eq(p, z)) == False{} : Bool}; hpz) : {U32.is_eq(p, z) == False{} : Bool}}
      K.Bo.or_ir(U32.is_zero(U32.and(am, bit)), R1N,
        part.end.z(m, P, Q, zs, K, F, N, z, xc, p, Zv, ne, hcs, hPz, hz, h0, K.Bo.or_r(U32.is_zero(U32.and(am, bit)), R1O, h, es)))

# a garbage cell's own facts across the store at z, which it is not
def hd.end(+m: Cr.Cir.Cells, +z: U32, +xc: Cr.Cir.Cell, +Q: List<&2, U32>, +o: U32, +F: U32, +N: U32,
  +ne: {U32.is_eq(o, z) == False{} : Bool}, h: {K.AL.hd(m, Q, o, F, N) == True{} : Bool}) ->
  {K.AL.hd(Cr.Cir.Cells.set(m, z, xc), Con{z, Q}, o, F, N) == True{} : Bool}:
  +ms = Cr.Cir.Cells.set(m, z, xc)
  %Equal.sym(U32, D.Fd(0n, ms, o), D.Fd(0n, m, o), C.made.fd(0n, m, o, z, xc, ne)) :
    {Bool.and(Bool.and(Bool.and(U32.is_le(F, o), U32.is_lt(o, N)), Bool.not(U32.is_ne(U32.and(_, 1024), 0))),
      Bool.or(U32.is_le(U32.and(_, 63), 18), Bool.and(U32.is_le(32, U32.and(_, 63)), D.Has(Con{z, Q}, o)))) == True{} : Bool}
  %Equal.sym(Bool, D.Has(Con{z, Q}, o), D.Has(Q, o), has.cons.ne(z, Q, o, K.U.ne.sym(o, z, ne))) :
    {Bool.and(Bool.and(Bool.and(U32.is_le(F, o), U32.is_lt(o, N)), Bool.not(U32.is_ne(U32.and(D.Fd(0n, m, o), 1024), 0))),
      Bool.or(U32.is_le(U32.and(D.Fd(0n, m, o), 63), 18), Bool.and(U32.is_le(32, U32.and(D.Fd(0n, m, o), 63)), _))) == True{} : Bool}
  h

# a garbage cell's parts across the store at z, which none of them is
def pt.end(+m: Cr.Cir.Cells, +P: List<&2, U32>, +Q: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +N: U32, +z: U32,
  +xc: Cr.Cir.Cell, +o: U32, +ne: {U32.is_eq(o, z) == False{} : Bool}, +hd: {K.AL.hd(m, Q, o, F, N) == True{} : Bool},
  how: {D.Ow(m, o, z) == 0n : Nat}, +hcs: {D.AL.cells(P, m, P, Q, zs, K, F, N) == True{} : Bool}, +hPz: {D.Has(P, z) == False{} : Bool},
  +hz: N.Le(291n, U32.to_nat(z)), +h0: {Cr.Cir.Cell.get(0n, xc) == 45 : U32}, h: {K.AL.pt(m, P, zs, o, K, F, N) == True{} : Bool}) ->
  {K.AL.pt(Cr.Cir.Cells.set(m, z, xc), Con{z, P}, zs, o, K, F, N) == True{} : Bool}:
  +ms = Cr.Cir.Cells.set(m, z, xc)
  +am = D.Am(m, o)
  +Zv = D.Zz(zs, o)
  +Pn = {Con{z, P} : List<&2, U32>}
  %Equal.sym(U32, D.Am(ms, o), am, K.am.set(m, z, xc, o, D.Has(Q, o), ne, K.al.hd.tg(m, Q, o, F, N, hd), hz)) :
    {Bool.and(D.AL.part(ms, Pn, zs, Zv, _, 1, D.Fd(2n, ms, o), K, F, N),
      Bool.and(D.AL.part(ms, Pn, zs, Zv, _, 2, D.Fd(3n, ms, o), K, F, N), D.AL.part(ms, Pn, zs, Zv, _, 4, D.Fd(4n, ms, o), K, F, N))) == True{} : Bool}
  %Equal.sym(U32, D.Fd(2n, ms, o), D.Fd(2n, m, o), C.made.fd(2n, m, o, z, xc, ne)) :
    {Bool.and(D.AL.part(ms, Pn, zs, Zv, am, 1, _, K, F, N),
      Bool.and(D.AL.part(ms, Pn, zs, Zv, am, 2, D.Fd(3n, ms, o), K, F, N), D.AL.part(ms, Pn, zs, Zv, am, 4, D.Fd(4n, ms, o), K, F, N))) == True{} : Bool}
  %Equal.sym(U32, D.Fd(3n, ms, o), D.Fd(3n, m, o), C.made.fd(3n, m, o, z, xc, ne)) :
    {Bool.and(D.AL.part(ms, Pn, zs, Zv, am, 1, D.Fd(2n, m, o), K, F, N),
      Bool.and(D.AL.part(ms, Pn, zs, Zv, am, 2, _, K, F, N), D.AL.part(ms, Pn, zs, Zv, am, 4, D.Fd(4n, ms, o), K, F, N))) == True{} : Bool}
  %Equal.sym(U32, D.Fd(4n, ms, o), D.Fd(4n, m, o), C.made.fd(4n, m, o, z, xc, ne)) :
    {Bool.and(D.AL.part(ms, Pn, zs, Zv, am, 1, D.Fd(2n, m, o), K, F, N),
      Bool.and(D.AL.part(ms, Pn, zs, Zv, am, 2, D.Fd(3n, m, o), K, F, N), D.AL.part(ms, Pn, zs, Zv, am, 4, _, K, F, N))) == True{} : Bool}
  +h2 = h
  +how2 = how
  +B1 = Bool.and(U32.is_ne(U32.and(am, 1), 0), U32.is_eq(D.Fd(2n, m, o), z))
  +B2 = Bool.and(U32.is_ne(U32.and(am, 2), 0), U32.is_eq(D.Fd(3n, m, o), z))
  +B3 = Bool.and(U32.is_ne(U32.and(am, 4), 0), U32.is_eq(D.Fd(4n, m, o), z))
  +r23 = K.Na.add0r(D.Nat.of(B1), Nat.add(D.Nat.of(B2), D.Nat.of(B3)), how2)
  +P1O = D.AL.part(m, P, zs, Zv, am, 1, D.Fd(2n, m, o), K, F, N)
  +P2O = D.AL.part(m, P, zs, Zv, am, 2, D.Fd(3n, m, o), K, F, N)
  +P3O = D.AL.part(m, P, zs, Zv, am, 4, D.Fd(4n, m, o), K, F, N)
  +P2N = D.AL.part(ms, Pn, zs, Zv, am, 2, D.Fd(3n, m, o), K, F, N)
  +P3N = D.AL.part(ms, Pn, zs, Zv, am, 4, D.Fd(4n, m, o), K, F, N)
  +h23 = K.Bo.and_r(P1O, Bool.and(P2O, P3O), h2)
  K.Bo.and_i(D.AL.part(ms, Pn, zs, Zv, am, 1, D.Fd(2n, m, o), K, F, N), Bool.and(P2N, P3N),
    part.end.s(U32.is_zero(U32.and(am, 1)), m, P, Q, zs, K, F, N, z, xc, am, 1, D.Fd(2n, m, o), Zv, {==}, hcs, hPz, hz, h0,
      K.Bo.and_l(P1O, Bool.and(P2O, P3O), h2), W.nof.z(B1, W.Na.add0l(D.Nat.of(B1), Nat.add(D.Nat.of(B2), D.Nat.of(B3)), how2))),
    K.Bo.and_i(P2N, P3N,
      part.end.s(U32.is_zero(U32.and(am, 2)), m, P, Q, zs, K, F, N, z, xc, am, 2, D.Fd(3n, m, o), Zv, {==}, hcs, hPz, hz, h0,
        K.Bo.and_l(P2O, P3O, h23), W.nof.z(B2, W.Na.add0l(D.Nat.of(B2), D.Nat.of(B3), r23))),
      part.end.s(U32.is_zero(U32.and(am, 4)), m, P, Q, zs, K, F, N, z, xc, am, 4, D.Fd(4n, m, o), Zv, {==}, hcs, hPz, hz, h0,
        K.Bo.and_r(P2O, P3O, h23), W.nof.z(B3, K.Na.add0r(D.Nat.of(B2), D.Nat.of(B3), r23)))))

# a garbage cell's counts across the store at z: it is not z, nor the
# result r that z pointed to
def ct.end(+m: Cr.Cir.Cells, +P: List<&2, U32>, +Q: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +N: U32, +z: U32,
  +xc: Cr.Cir.Cell, +o: U32, +r: U32, +ne: {U32.is_eq(o, z) == False{} : Bool}, +hro: {U32.is_eq(r, o) == False{} : Bool},
  +hcs: {D.AL.cells(P, m, P, Q, zs, K, F, N) == True{} : Bool}, +hPz: {D.Has(P, z) == False{} : Bool}, +hz: N.Le(291n, U32.to_nat(z)),
  +h0: {Cr.Cir.Cell.get(0n, xc) == 45 : U32}, +honce: {W.Once(Nat.sub(U32.to_nat(N), U32.to_nat(F)), F, z) == True{} : Bool},
  +hps: {D.Ps(m, Q, z) == [r] : List<&2, U32>}, h: {K.AL.ct(m, P, Q, o, F, N) == True{} : Bool}) ->
  {K.AL.ct(Cr.Cir.Cells.set(m, z, xc), Con{z, P}, Con{z, Q}, o, F, N) == True{} : Bool}:
  +ms = Cr.Cir.Cells.set(m, z, xc)
  +n = Nat.sub(U32.to_nat(N), U32.to_nat(F))
  +pp = D.Pp(P, m, o)
  +p2 = D.Pp(Con{z, P}, ms, o)
  +e1 = {(%hro : {Nat.add(D.Pc(n, ms, Con{z, Q}, F, o), Nat.add(D.Nat.of(_), D.Occ(Nil{}, o))) == D.Pc(n, m, Q, F, o) : Nat};
      cnt.end0(n, m, z, xc, Q, F, o, r, hz, h0, honce, hps)) : {Nat.add(D.Pc(n, ms, Con{z, Q}, F, o), 0n) == D.Pc(n, m, Q, F, o) : Nat}}
  +epc = Equal.trans(Nat, D.Pc(n, ms, Con{z, Q}, F, o), Nat.add(D.Pc(n, ms, Con{z, Q}, F, o), 0n), D.Pc(n, m, Q, F, o),
    Equal.sym(Nat, Nat.add(D.Pc(n, ms, Con{z, Q}, F, o), 0n), D.Pc(n, ms, Con{z, Q}, F, o), N.add_zero(D.Pc(n, ms, Con{z, Q}, F, o))), e1)
  %Equal.sym(Nat, D.Pc(n, ms, Con{z, Q}, F, o), D.Pc(n, m, Q, F, o), epc) :
    {Bool.and(Nat.is_eq(_, p2), Bool.pick(Bool, D.Has(Con{z, Q}, o), Nat.is_eq(p2, 0n),
      Bool.and(Nat.is_eq(p2, U32.to_nat(D.Fd(1n, ms, o))), Nat.is_lt(0n, p2)))) == True{} : Bool}
  %Equal.sym(Nat, p2, pp, pp.zp(m, P, Q, zs, K, F, N, z, xc, o, hcs, hPz, hz, h0)) :
    {Bool.and(Nat.is_eq(D.Pc(n, m, Q, F, o), _), Bool.pick(Bool, D.Has(Con{z, Q}, o), Nat.is_eq(_, 0n),
      Bool.and(Nat.is_eq(_, U32.to_nat(D.Fd(1n, ms, o))), Nat.is_lt(0n, _)))) == True{} : Bool}
  %Equal.sym(Bool, D.Has(Con{z, Q}, o), D.Has(Q, o), has.cons.ne(z, Q, o, K.U.ne.sym(o, z, ne))) :
    {Bool.and(Nat.is_eq(D.Pc(n, m, Q, F, o), pp), Bool.pick(Bool, _, Nat.is_eq(pp, 0n),
      Bool.and(Nat.is_eq(pp, U32.to_nat(D.Fd(1n, ms, o))), Nat.is_lt(0n, pp)))) == True{} : Bool}
  %Equal.sym(U32, D.Fd(1n, ms, o), D.Fd(1n, m, o), C.made.fd(1n, m, o, z, xc, ne)) :
    {Bool.and(Nat.is_eq(D.Pc(n, m, Q, F, o), pp), Bool.pick(Bool, D.Has(Q, o), Nat.is_eq(pp, 0n),
      Bool.and(Nat.is_eq(pp, U32.to_nat(_)), Nat.is_lt(0n, pp)))) == True{} : Bool}
  h

# the garbage cells os of P across the store at the root z, which none of
# them is nor points to, and none of them is r
def al.cells.end(os: List<&2, U32>, +m: Cr.Cir.Cells, +P: List<&2, U32>, +Q: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32,
  +N: U32, +z: U32, +xc: Cr.Cir.Cell, +r: U32, +hcs: {D.AL.cells(P, m, P, Q, zs, K, F, N) == True{} : Bool},
  +hPz: {D.Has(P, z) == False{} : Bool}, +hz: N.Le(291n, U32.to_nat(z)), +h0: {Cr.Cir.Cell.get(0n, xc) == 45 : U32},
  +honce: {W.Once(Nat.sub(U32.to_nat(N), U32.to_nat(F)), F, z) == True{} : Bool}, +hps: {D.Ps(m, Q, z) == [r] : List<&2, U32>},
  hos: {D.Has(os, z) == False{} : Bool}, hro: {D.Has(os, r) == False{} : Bool}, hpp: {D.Pp(os, m, z) == 0n : Nat},
  h: {D.AL.cells(os, m, P, Q, zs, K, F, N) == True{} : Bool}) ->
  {D.AL.cells(os, Cr.Cir.Cells.set(m, z, xc), Con{z, P}, Con{z, Q}, zs, K, F, N) == True{} : Bool}:
  match os:
    case Nil{}:
      {==}
    case Con{+o, +rest}:
      +ms = Cr.Cir.Cells.set(m, z, xc)
      +h2 = h
      +hos2 = hos
      +hro2 = hro
      +hpp2 = hpp
      +ne = K.or.fl(U32.is_eq(o, z), D.Has(rest, z), hos2)
      +nr = K.U.ne.sym(o, r, K.or.fl(U32.is_eq(o, r), D.Has(rest, r), hro2))
      +hd = K.al.hd(o, rest, m, P, Q, zs, K, F, N, h2)
      K.al.cons(o, rest, ms, Con{z, P}, Con{z, Q}, zs, K, F, N,
        hd.end(m, z, xc, Q, o, F, N, ne, hd),
        pt.end(m, P, Q, zs, K, F, N, z, xc, o, ne, hd, W.Na.add0l(D.Ow(m, o, z), D.Pp(rest, m, z), hpp2), hcs, hPz, hz, h0,
          K.al.pt(o, rest, m, P, Q, zs, K, F, N, h2)),
        ct.end(m, P, Q, zs, K, F, N, z, xc, o, r, ne, nr, hcs, hPz, hz, h0, honce, hps, K.al.ct(o, rest, m, P, Q, zs, K, F, N, h2)),
        al.cells.end(rest, m, P, Q, zs, K, F, N, z, xc, r, hcs, hPz, hz, h0, honce, hps, K.or.fr(U32.is_eq(o, z), D.Has(rest, z), hos2),
          K.or.fr(U32.is_eq(o, r), D.Has(rest, r), hro2), K.Na.add0r(D.Ow(m, o, z), D.Pp(rest, m, z), hpp2),
          K.al.rest(o, rest, m, P, Q, zs, K, F, N, h2)))

# the released root's own facts: an own cell, not STATIC, of the machine's
# kind, pending
def hd.z(+m: Cr.Cir.Cells, +z: U32, +xc: Cr.Cir.Cell, +Q: List<&2, U32>, +F: U32, +N: U32, +hfz: {U32.is_le(F, z) == True{} : Bool},
  +hzn: {U32.is_lt(z, N) == True{} : Bool}, +h0: {Cr.Cir.Cell.get(0n, xc) == 45 : U32}) ->
  {K.AL.hd(Cr.Cir.Cells.set(m, z, xc), Con{z, Q}, z, F, N) == True{} : Bool}:
  +ms = Cr.Cir.Cells.set(m, z, xc)
  %Equal.sym(U32, D.Fd(0n, ms, z), 45, f0.z(m, z, xc, h0)) :
    {Bool.and(Bool.and(Bool.and(U32.is_le(F, z), U32.is_lt(z, N)), Bool.not(U32.is_ne(U32.and(_, 1024), 0))),
      Bool.or(U32.is_le(U32.and(_, 63), 18), Bool.and(U32.is_le(32, U32.and(_, 63)), D.Has(Con{z, Q}, z)))) == True{} : Bool}
  K.Bo.and_i(Bool.and(Bool.and(U32.is_le(F, z), U32.is_lt(z, N)), Bool.not(U32.is_ne(U32.and(45, 1024), 0))),
    Bool.or(U32.is_le(U32.and(45, 63), 18), Bool.and(U32.is_le(32, U32.and(45, 63)), D.Has(Con{z, Q}, z))),
    K.Bo.and_i(Bool.and(U32.is_le(F, z), U32.is_lt(z, N)), Bool.not(U32.is_ne(U32.and(45, 1024), 0)),
      K.Bo.and_i(U32.is_le(F, z), U32.is_lt(z, N), hfz, hzn), {==}),
    has.cons.eq(z, Q))

# the released root has no part
def pt.z(+m: Cr.Cir.Cells, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +z: U32, +xc: Cr.Cir.Cell, +K: U32, +F: U32, +N: U32,
  +h0: {Cr.Cir.Cell.get(0n, xc) == 45 : U32}) -> {K.AL.pt(Cr.Cir.Cells.set(m, z, xc), Con{z, P}, zs, z, K, F, N) == True{} : Bool}:
  +ms = Cr.Cir.Cells.set(m, z, xc)
  +Zv = D.Zz(zs, z)
  +Pn = {Con{z, P} : List<&2, U32>}
  %Equal.sym(U32, D.Am(ms, z), 0, am.z0(m, z, xc, h0)) :
    {Bool.and(D.AL.part(ms, Pn, zs, Zv, _, 1, D.Fd(2n, ms, z), K, F, N),
      Bool.and(D.AL.part(ms, Pn, zs, Zv, _, 2, D.Fd(3n, ms, z), K, F, N), D.AL.part(ms, Pn, zs, Zv, _, 4, D.Fd(4n, ms, z), K, F, N))) == True{} : Bool}
  {==}

# nothing points to the released root, pending
def ct.z(+m: Cr.Cir.Cells, +P: List<&2, U32>, +Q: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +N: U32, +z: U32,
  +xc: Cr.Cir.Cell, +r: U32, +hcs: {D.AL.cells(P, m, P, Q, zs, K, F, N) == True{} : Bool}, +hPz: {D.Has(P, z) == False{} : Bool},
  +hz: N.Le(291n, U32.to_nat(z)), +h0: {Cr.Cir.Cell.get(0n, xc) == 45 : U32},
  +honce: {W.Once(Nat.sub(U32.to_nat(N), U32.to_nat(F)), F, z) == True{} : Bool}, +hps: {D.Ps(m, Q, z) == [r] : List<&2, U32>},
  +hpz: {D.Pp(P, m, z) == 0n : Nat}, +hpc: {D.Pc(Nat.sub(U32.to_nat(N), U32.to_nat(F)), m, Q, F, z) == 0n : Nat}) ->
  {K.AL.ct(Cr.Cir.Cells.set(m, z, xc), Con{z, P}, Con{z, Q}, z, F, N) == True{} : Bool}:
  +ms = Cr.Cir.Cells.set(m, z, xc)
  +n = Nat.sub(U32.to_nat(N), U32.to_nat(F))
  +p2 = D.Pp(Con{z, P}, ms, z)
  +e0 = Equal.trans(Nat, Nat.add(D.Pc(n, ms, Con{z, Q}, F, z), D.Occ([r], z)), D.Pc(n, m, Q, F, z), 0n,
    cnt.end0(n, m, z, xc, Q, F, z, r, hz, h0, honce, hps), hpc)
  +epc = W.Na.add0l(D.Pc(n, ms, Con{z, Q}, F, z), D.Occ([r], z), e0)
  +epp = Equal.trans(Nat, p2, D.Pp(P, m, z), 0n, pp.zp(m, P, Q, zs, K, F, N, z, xc, z, hcs, hPz, hz, h0), hpz)
  %Equal.sym(Nat, D.Pc(n, ms, Con{z, Q}, F, z), 0n, epc) :
    {Bool.and(Nat.is_eq(_, p2), Bool.pick(Bool, D.Has(Con{z, Q}, z), Nat.is_eq(p2, 0n),
      Bool.and(Nat.is_eq(p2, U32.to_nat(D.Fd(1n, ms, z))), Nat.is_lt(0n, p2)))) == True{} : Bool}
  %Equal.sym(Nat, p2, 0n, epp) :
    {Bool.and(Nat.is_eq(0n, _), Bool.pick(Bool, D.Has(Con{z, Q}, z), Nat.is_eq(_, 0n),
      Bool.and(Nat.is_eq(_, U32.to_nat(D.Fd(1n, ms, z))), Nat.is_lt(0n, _)))) == True{} : Bool}
  %Equal.sym(Bool, D.Has(Con{z, Q}, z), True{}, has.cons.eq(z, Q)) :
    {Bool.and(Nat.is_eq(0n, 0n), Bool.pick(Bool, _, Nat.is_eq(0n, 0n),
      Bool.and(Nat.is_eq(0n, U32.to_nat(D.Fd(1n, ms, z))), Nat.is_lt(0n, 0n)))) == True{} : Bool}
  {==}

# pointers ys, none of them z, stay below N and 0 or term cells
def all.lt.ne(ys: List<&2, U32>, +m: Cr.Cir.Cells, +N: U32, +z: U32, +xc: Cr.Cir.Cell, ho: {D.Occ(ys, z) == 0n : Nat},
  h: {D.All.lt(ys, m, N) == True{} : Bool}) -> {D.All.lt(ys, Cr.Cir.Cells.set(m, z, xc), N) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      +ms = Cr.Cir.Cells.set(m, z, xc)
      +ho2 = ho
      +h2 = h
      +ne = W.nof.z(U32.is_eq(y, z), W.Na.add0l(D.Nat.of(U32.is_eq(y, z)), D.Occ(rest, z), ho2))
      +A0 = Bool.and(U32.is_lt(y, N), Bool.or(U32.is_zero(y), U32.is_le(U32.and(D.Fd(0n, m, y), 63), 18)))
      %Equal.sym(U32, D.Fd(0n, ms, y), D.Fd(0n, m, y), C.made.fd(0n, m, y, z, xc, ne)) :
        {Bool.and(Bool.and(U32.is_lt(y, N), Bool.or(U32.is_zero(y), U32.is_le(U32.and(_, 63), 18))), D.All.lt(rest, ms, N)) == True{} : Bool}
      K.Bo.and_i(A0, D.All.lt(rest, ms, N), K.Bo.and_l(A0, D.All.lt(rest, m, N), h2),
        all.lt.ne(rest, m, N, z, xc, K.Na.add0r(D.Nat.of(U32.is_eq(y, z)), D.Occ(rest, z), ho2), K.Bo.and_r(A0, D.All.lt(rest, m, N), h2)))

def lt.at.b(e: Bool, +m: Cr.Cir.Cells, +Q: List<&2, U32>, +o: U32, +N: U32, +z: U32, +xc: Cr.Cir.Cell, eo: {U32.is_eq(o, z) == e : Bool},
  +hz: N.Le(291n, U32.to_nat(z)), +h0: {Cr.Cir.Cell.get(0n, xc) == 45 : U32}, +ho: {D.Occ(D.Ps(m, Q, o), z) == 0n : Nat},
  h: {D.All.lt(D.Ps(m, Q, o), m, N) == True{} : Bool}) -> {D.All.lt(D.Ps(Cr.Cir.Cells.set(m, z, xc), Con{z, Q}, o), Cr.Cir.Cells.set(m, z, xc), N) == True{} : Bool}:
  match e:
    case True{}:
      +ms = Cr.Cir.Cells.set(m, z, xc)
      (%Equal.sym(U32, o, z, K.U.eq(o, z, eo)) : {D.All.lt(D.Ps(ms, Con{z, Q}, _), ms, N) == True{} : Bool};
        (%Equal.sym(List<&2, U32>, D.Ps(ms, Con{z, Q}, z), Nil{}, ps.z0(m, z, xc, Con{z, Q}, h0)) : {D.All.lt(_, ms, N) == True{} : Bool}; {==}))
    case False{}:
      +ms = Cr.Cir.Cells.set(m, z, xc)
      %Equal.sym(List<&2, U32>, D.Ps(ms, Con{z, Q}, o), D.Ps(m, Q, o), ps.zo(m, z, xc, Q, o, eo, hz)) : {D.All.lt(_, ms, N) == True{} : Bool}
      all.lt.ne(D.Ps(m, Q, o), m, N, z, xc, ho, h)

# the own cells' pointers stay below N and 0 or term cells: none is z, and z
# holds none
def lt.end(k: Nat, +m: Cr.Cir.Cells, +Q: List<&2, U32>, +o: U32, +N: U32, +z: U32, +xc: Cr.Cir.Cell, +hz: N.Le(291n, U32.to_nat(z)),
  +h0: {Cr.Cir.Cell.get(0n, xc) == 45 : U32}, hp: {D.Pc(k, m, Q, o, z) == 0n : Nat}, h: {D.Lt(k, m, Q, o, N) == True{} : Bool}) ->
  {D.Lt(k, Cr.Cir.Cells.set(m, z, xc), Con{z, Q}, o, N) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+(+p):
      +ms = Cr.Cir.Cells.set(m, z, xc)
      +hp2 = hp
      +h2 = h
      K.Bo.and_i(D.All.lt(D.Ps(ms, Con{z, Q}, o), ms, N), D.Lt(p, ms, Con{z, Q}, U32.inc(o), N),
        lt.at.b(U32.is_eq(o, z), m, Q, o, N, z, xc, {==}, hz, h0, W.Na.add0l(D.Occ(D.Ps(m, Q, o), z), D.Pc(p, m, Q, U32.inc(o), z), hp2),
          K.Bo.and_l(D.All.lt(D.Ps(m, Q, o), m, N), D.Lt(p, m, Q, U32.inc(o), N), h2)),
        lt.end(p, m, Q, U32.inc(o), N, z, xc, hz, h0, K.Na.add0r(D.Occ(D.Ps(m, Q, o), z), D.Pc(p, m, Q, U32.inc(o), z), hp2),
          K.Bo.and_r(D.All.lt(D.Ps(m, Q, o), m, N), D.Lt(p, m, Q, U32.inc(o), N), h2)))

# the pend list from the released root z: z, linked to the old pend list
def chain.z(+m: Cr.Cir.Cells, +Q: List<&2, U32>, +z: U32, +xc: Cr.Cir.Cell, +pend: U32, +K: U32, +F: U32,
  +hkf: {U32.is_lt(K, F) == True{} : Bool}, +hfz: {U32.is_le(F, z) == True{} : Bool}, +h1: {Cr.Cir.Cell.get(1n, xc) == pend : U32},
  hch: {D.Chain(Q, m, pend) == True{} : Bool}, hQz: {D.Has(Q, z) == False{} : Bool}) ->
  {D.Chain(Con{z, Q}, Cr.Cir.Cells.set(m, z, xc), z) == True{} : Bool}:
  +ms = Cr.Cir.Cells.set(m, z, xc)
  %Equal.sym(U32, D.Fd(1n, ms, z), pend, Equal.trans(U32, D.Fd(1n, ms, z), Cr.Cir.Cell.get(1n, xc), pend, fd.z(1n, m, z, xc), h1)) :
    {Bool.and(U32.is_eq(z, z), Bool.and(Bool.not(U32.is_zero(z)), D.Chain(Q, ms, _))) == True{} : Bool}
  K.Bo.and_i(U32.is_eq(z, z), Bool.and(Bool.not(U32.is_zero(z)), D.Chain(Q, ms, pend)), K.U.eq_refl(z),
    K.Bo.and_i(Bool.not(U32.is_zero(z)), D.Chain(Q, ms, pend), K.Bo.not_i(U32.is_zero(z), K.U.nz(z, K, F, hkf, hfz)),
      K.chain.set(Q, m, z, xc, pend, hch, hQz)))

# the allocation's invariant after the store at the root z: z, a K.root that
# points to nothing and that nothing points to, heads the pend list and
# joins the garbage
def al.end(+m: Cr.Cir.Cells, +pend: U32, +P: List<&2, U32>, +Q: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +N: U32,
  +z: U32, +xc: Cr.Cir.Cell, +r: U32, +hkf: {U32.is_lt(K, F) == True{} : Bool}, +hfz: {U32.is_le(F, z) == True{} : Bool},
  +hzn: {U32.is_lt(z, N) == True{} : Bool}, +hz: N.Le(291n, U32.to_nat(z)), +h0: {Cr.Cir.Cell.get(0n, xc) == 45 : U32},
  +h1: {Cr.Cir.Cell.get(1n, xc) == pend : U32}, +honce: {W.Once(Nat.sub(U32.to_nat(N), U32.to_nat(F)), F, z) == True{} : Bool},
  +hps: {D.Ps(m, Q, z) == [r] : List<&2, U32>}, +hpz: {D.Pp(P, m, z) == 0n : Nat},
  +hpc: {D.Pc(Nat.sub(U32.to_nat(N), U32.to_nat(F)), m, Q, F, z) == 0n : Nat}, +hPz: {D.Has(P, z) == False{} : Bool},
  +hPr: {D.Has(P, r) == False{} : Bool}, h: {D.AL(m, pend, P, Q, zs, K, F, N) == True{} : Bool}) ->
  {D.AL(Cr.Cir.Cells.set(m, z, xc), z, Con{z, P}, Con{z, Q}, zs, K, F, N) == True{} : Bool}:
  +ms = Cr.Cir.Cells.set(m, z, xc)
  +n = Nat.sub(U32.to_nat(N), U32.to_nat(F))
  +Pn = {Con{z, P} : List<&2, U32>}
  +Qn = {Con{z, Q} : List<&2, U32>}
  +h2 = h
  +C1 = D.AL.cells(P, m, P, Q, zs, K, F, N)
  +L1 = D.Lt(n, m, Q, F, N)
  +S1 = Bool.and(D.Sub(Q, P), D.Nodup(P))
  +H1 = Bool.and(D.Chain(Q, m, pend), D.Nodup(Q))
  +hH = K.Bo.and_l(H1, Bool.and(S1, Bool.and(C1, L1)), h2)
  +hR = K.Bo.and_r(H1, Bool.and(S1, Bool.and(C1, L1)), h2)
  +hS = K.Bo.and_l(S1, Bool.and(C1, L1), hR)
  +hCL = K.Bo.and_r(S1, Bool.and(C1, L1), hR)
  +hcs = K.Bo.and_l(C1, L1, hCL)
  +hsub = K.Bo.and_l(D.Sub(Q, P), D.Nodup(P), hS)
  +hQz = K.sub.nhas(Q, P, z, hsub, hPz)
  +C2 = D.AL.cells(Pn, ms, Pn, Qn, zs, K, F, N)
  +L2 = D.Lt(n, ms, Qn, F, N)
  K.Bo.and_i(Bool.and(D.Chain(Qn, ms, z), D.Nodup(Qn)), Bool.and(Bool.and(D.Sub(Qn, Pn), D.Nodup(Pn)), Bool.and(C2, L2)),
    K.Bo.and_i(D.Chain(Qn, ms, z), D.Nodup(Qn),
      chain.z(m, Q, z, xc, pend, K, F, hkf, hfz, h1, K.Bo.and_l(D.Chain(Q, m, pend), D.Nodup(Q), hH), hQz),
      K.Bo.and_i(Bool.not(D.Has(Q, z)), D.Nodup(Q), K.Bo.not_i(D.Has(Q, z), hQz), K.Bo.and_r(D.Chain(Q, m, pend), D.Nodup(Q), hH))),
    K.Bo.and_i(Bool.and(D.Sub(Qn, Pn), D.Nodup(Pn)), Bool.and(C2, L2),
      K.Bo.and_i(D.Sub(Qn, Pn), D.Nodup(Pn),
        K.Bo.and_i(D.Has(Pn, z), D.Sub(Q, Pn), has.cons.eq(z, P), W.sub.cons(Q, z, P, hsub)),
        K.Bo.and_i(Bool.not(D.Has(P, z)), D.Nodup(P), K.Bo.not_i(D.Has(P, z), hPz), K.Bo.and_r(D.Sub(Q, P), D.Nodup(P), hS))),
      K.Bo.and_i(C2, L2,
        K.al.cons(z, P, ms, Pn, Qn, zs, K, F, N, hd.z(m, z, xc, Q, F, N, hfz, hzn, h0), pt.z(m, P, zs, z, xc, K, F, N, h0),
          ct.z(m, P, Q, zs, K, F, N, z, xc, r, hcs, hPz, hz, h0, honce, hps, hpz, hpc),
          al.cells.end(P, m, P, Q, zs, K, F, N, z, xc, r, hcs, hPz, hz, h0, honce, hps, hPz, hPr, hpz, hcs)),
        lt.end(n, m, Q, F, N, z, xc, hz, h0, hpc, K.Bo.and_r(C1, L1, hCL)))))

# The release
# -----------

# an own cell (from F on, past the image K) is below next
def cell.own.of(b: Bool, +x: U32, +K: U32, +F: U32, +N: U32, eb: {Bool.and(Bool.not(U32.is_zero(x)), U32.is_le(x, K)) == b : Bool},
  +hkx: {U32.is_lt(K, x) == True{} : Bool}, h: {Bool.or(b, Bool.and(U32.is_le(F, x), U32.is_lt(x, N))) == True{} : Bool}) ->
  {U32.is_lt(x, N) == True{} : Bool}:
  match b:
    case True{}:
      K.U.lt_ge(K, x, {U32.is_lt(x, N) == True{} : Bool}, hkx, K.Bo.and_r(Bool.not(U32.is_zero(x)), U32.is_le(x, K), eb))
    case False{}:
      K.Bo.and_r(U32.is_le(F, x), U32.is_lt(x, N), h)

def cell.own(+x: U32, +K: U32, +F: U32, +N: U32, +hkf: {U32.is_lt(K, F) == True{} : Bool}, +hfx: {U32.is_le(F, x) == True{} : Bool},
  h: {Cr.Cir.is_cell(x, K, F, N) == True{} : Bool}) -> {U32.is_lt(x, N) == True{} : Bool}:
  cell.own.of(Bool.and(Bool.not(U32.is_zero(x)), U32.is_le(x, K)), x, K, F, N, {==}, K.U.lt_le(K, F, x, hkf, hfx), h)

# a cell past the image K and at or past next N is none
def cell.past.b(a: Bool, c: Bool, +z: U32, +K: U32, +F: U32, +N: U32, ea: {U32.is_le(z, K) == a : Bool}, ec: {U32.is_lt(z, N) == c : Bool},
  +hkz: {U32.is_lt(K, z) == True{} : Bool}, +hnz: {U32.is_le(N, z) == True{} : Bool}) ->
  {Bool.or(Bool.and(Bool.not(U32.is_zero(z)), a), Bool.and(U32.is_le(F, z), c)) == False{} : Bool}:
  match a c:
    case True{} _:
      K.U.lt_ge(K, z, {Bool.or(Bool.and(Bool.not(U32.is_zero(z)), True{}), Bool.and(U32.is_le(F, z), c)) == False{} : Bool}, hkz, ea)
    case False{} True{}:
      K.U.lt_ge(z, N, {Bool.or(Bool.and(Bool.not(U32.is_zero(z)), False{}), Bool.and(U32.is_le(F, z), True{})) == False{} : Bool}, ec, hnz)
    case False{} False{}:
      %Equal.sym(Bool, Bool.and(Bool.not(U32.is_zero(z)), False{}), False{}, W.and.f(Bool.not(U32.is_zero(z)))) :
        {Bool.or(_, Bool.and(U32.is_le(F, z), False{})) == False{} : Bool}
      W.and.f(U32.is_le(F, z))

def cell.past(+z: U32, +K: U32, +F: U32, +N: U32, +hkz: {U32.is_lt(K, z) == True{} : Bool}, +hnz: {U32.is_le(N, z) == True{} : Bool}) ->
  {Cr.Cir.is_cell(z, K, F, N) == False{} : Bool}:
  cell.past.b(U32.is_le(z, K), U32.is_lt(z, N), z, K, F, N, {==}, {==}, hkz, hnz)

# a cell of X may not be read
def al.has(+K: U32, +F: U32, +X: List<&2, U32>, +N: U32, +z: U32, hx: {D.Has(X, z) == True{} : Bool}) -> {D.Al(K, F, X, N, z) == False{} : Bool}:
  %Equal.sym(Bool, D.Has(X, z), True{}, hx) : {Bool.and(Cr.Cir.is_cell(z, K, F, N), Bool.and(Bool.not(_), Bool.not(D.Tbc(z)))) == False{} : Bool}
  W.and.f(Cr.Cir.is_cell(z, K, F, N))

def al.out.b(b: Bool, +K: U32, +F: U32, +X0: List<&2, U32>, +E: List<&2, U32>, +N: U32, +z: U32, eb: {D.Has(X0, z) == b : Bool},
  +hkz: {U32.is_lt(K, z) == True{} : Bool}, h: {Bool.or(b, U32.is_le(N, z)) == True{} : Bool}) ->
  {D.Al(K, F, List.append(&2, U32, X0, E), N, z) == False{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, D.Has(List.append(&2, U32, X0, E), z), Bool.or(D.Has(X0, z), D.Has(E, z)), K.has.app(X0, E, z)) :
        {Bool.and(Cr.Cir.is_cell(z, K, F, N), Bool.and(Bool.not(_), Bool.not(D.Tbc(z)))) == False{} : Bool}
      %Equal.sym(Bool, D.Has(X0, z), True{}, eb) :
        {Bool.and(Cr.Cir.is_cell(z, K, F, N), Bool.and(Bool.not(Bool.or(_, D.Has(E, z))), Bool.not(D.Tbc(z)))) == False{} : Bool}
      W.and.f(Cr.Cir.is_cell(z, K, F, N))
    case False{}:
      %Equal.sym(Bool, Cr.Cir.is_cell(z, K, F, N), False{}, cell.past(z, K, F, N, hkz, h)) :
        {Bool.and(_, Bool.and(Bool.not(D.Has(List.append(&2, U32, X0, E), z)), Bool.not(D.Tbc(z)))) == False{} : Bool}
      {==}

# a cell that was garbage at the start (in X0) or not yet a cell (at or past
# N) may not be read with the start's X0 ++ E and N
def al.out(+K: U32, +F: U32, +X0: List<&2, U32>, +E: List<&2, U32>, +N: U32, +z: U32, +hkz: {U32.is_lt(K, z) == True{} : Bool},
  h: {Bool.or(D.Has(X0, z), U32.is_le(N, z)) == True{} : Bool}) -> {D.Al(K, F, List.append(&2, U32, X0, E), N, z) == False{} : Bool}:
  al.out.b(D.Has(X0, z), K, F, X0, E, N, z, {==}, hkz, h)

# the fuel of the result's checked term, when hx
def end.g(hx: Bool, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +K: U32, +F: U32, +P: List<&2, U32>,
  +E: List<&2, U32>, +nx: U32, +root: U32, +u: Bk.Term,
  h: D.Hx(hx, D.Ex(Nat, g => {D.Tm(g, m, ks, img, K, F, List.append(&2, U32, P, Con{root, E}), nx, D.Fd(2n, m, root)) == Some{u} : Maybe<&2, Bk.Term>}))) -> Nat:
  match hx:
    case True{}:
      (g0, _) = h
      g0
    case False{}:
      0n

# the result's checked term after the release: the root, which the term
# never reads, joins the garbage
def end.tm(hx: Bool, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +K: U32, +F: U32, +P: List<&2, U32>,
  +E: List<&2, U32>, +nx: U32, +root: U32, +xc: Cr.Cir.Cell, +u: Bk.Term, +hkn: {U32.is_lt(K, nx) == True{} : Bool},
  h: D.Hx(hx, D.Ex(Nat, g => {D.Tm(g, m, ks, img, K, F, List.append(&2, U32, P, Con{root, E}), nx, D.Fd(2n, m, root)) == Some{u} : Maybe<&2, Bk.Term>}))) ->
  D.Hx(hx, {D.Tm(end.g(hx, m, ks, img, K, F, P, E, nx, root, u, h), Cr.Cir.Cells.set(m, root, xc), ks, img, K, F,
    List.append(&2, U32, Con{root, P}, E), nx, D.Fd(2n, m, root)) == Some{u} : Maybe<&2, Bk.Term>}):
  match hx:
    case True{}:
      (g0, htm) = h
      +g = g0
      +ms = Cr.Cir.Cells.set(m, root, xc)
      +X = {List.append(&2, U32, P, Con{root, E}) : List<&2, U32>}
      +hin = K.Bo.and_i(U32.is_le(nx, nx), D.Incl.go(Con{root, List.append(&2, U32, P, E)}, X, nx), K.U.le_t(nx, nx, N.le_refl(U32.to_nat(nx))),
        K.Bo.and_i(Bool.or(D.Has(X, root), U32.is_le(nx, root)), D.Incl.go(List.append(&2, U32, P, E), X, nx),
          K.Bo.or_il(D.Has(X, root), U32.is_le(nx, root), has.mid(P, root, E)),
          incl.sub(List.append(&2, U32, P, E), X, nx, K.sub.app(P, E, X, sub.l(P, Con{root, E}), sub.r(P, root, E)))))
      +hi = Equal.sym(Bool, D.Al(K, F, X, nx, root), False{}, al.has(K, F, X, nx, root, has.mid(P, root, E)))
      C.Tm.mono(g, ms, ks, img, K, F, X, nx, List.append(&2, U32, Con{root, P}, E), nx, D.Fd(2n, m, root), u, hin, hkn,
        C.Tm.wx(g, m, ks, img, K, F, X, nx, D.Fd(2n, m, root), root, xc, u, hi, htm))
    case False{}:
      Unit{}

# M.copy.end, at the walk's end (no frames): register rr gets the copy from
# the root (register rt), whose release gives Post's facts; ups are the
# registers' writes, rg the registers before, and hbc says that Bc is the
# own cells' budget of the walk's accounting
def end.post(+f: Nat, +hx: Bool, +mo: D.Mo, +t: Bk.Term, +regs: List<&2, U32>, +scr: List<&2, Nat>, +rr: Nat, +rt: Nat,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +K: U32, +F: U32, +pg: U32, +L: U32, +I: List<&2, Word(8n)>,
  +m0: Cr.Cir.Cells, +P0: List<&2, U32>, +Q0: List<&2, U32>, +E: List<&2, U32>, +N0: U32, +Bc: Nat, +rs: List<&2, D.Rt>,
  +ts: List<&2, D.Tmp>, +kc: List<&2, D.Kc>, +S: List<&2, D.Rt>, +B0: Nat, +e: Nat, +zs: List<&2, D.Zs>, +cs: List<&2, D.Pr>,
  +x: U32, -Bu: Nat, +rg: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +P: List<&2, U32>, +Q: List<&2, U32>, +pend: U32, +root: U32,
  +T: List<&2, U32>, +ups: List<&2, D.Up>,
  +hl: {List.length(&2, U32, rg) == 63n : Nat}, +hr: {Nat.is_lt(rr, 63n) == True{} : Bool},
  +hrt: {List.get(&2, U32, rg, rt) == Some{root} : Maybe<&2, U32>},
  +hrt1: {List.get(&2, U32, List.set(&2, U32, rg, rr, D.Fd(2n, m, root)), rt) == Some{root} : Maybe<&2, U32>},
  +hp1: {List.get(&2, U32, List.set(&2, U32, rg, rr, D.Fd(2n, m, root)), 3n) == Some{pend} : Maybe<&2, U32>},
  +hups: {List.set(&2, U32, List.set(&2, U32, rg, rr, D.Fd(2n, m, root)), 3n, root) == D.Ups(ups, D.Rg.ex(63n, regs, 0n)) : List<&2, U32>},
  +hin: {D.Ups.in(ups, scr) == True{} : Bool},
  +hrr: {T.tm.reg(List.set(&2, U32, List.set(&2, U32, rg, rr, D.Fd(2n, m, root)), 3n, root), rr) == D.Fd(2n, m, root) : U32},
  +h3: {T.tm.reg(List.set(&2, U32, List.set(&2, U32, rg, rr, D.Fd(2n, m, root)), 3n, root), 3n) == root : U32},
  +hbc: {Nat.add(B0, Nat.add(e, 1n+Pg.Term.size(D.Mo.F(mo, t, 0n)))) == Bc : Nat},
  +hk: {U32.is_le(290, K) == True{} : Bool}, +hkf: {U32.is_lt(K, F) == True{} : Bool}, +hfn: {U32.is_le(F, nx) == True{} : Bool},
  +hrc: {Cr.Cir.is_cell(root, K, F, nx) == True{} : Bool}, +hfr: {U32.is_le(F, root) == True{} : Bool},
  hdj: {W.Dj(Con{root, Nil{}}, List.append(&2, U32, P, E)) == True{} : Bool},
  hroot: W.Root(mo, m, ks, img, K, F, List.append(&2, U32, P, Con{root, E}), nx, hx, Nil{}, root, x, t),
  hal: {D.AL(m, pend, P, Q, zs, K, F, nx) == True{} : Bool},
  hincl: {D.Incl(P0, N0, List.append(&2, U32, P, Con{root, E}), nx) == True{} : Bool},
  htb: D.Tb(m),
  hrts: D.Rts(m, ks, img, K, F, List.append(&2, U32, P0, E), N0, List.append(&2, D.Rt, rs, D.Tmp.held(ts))),
  hkcs: D.Kcs(m, K, F, List.append(&2, U32, P0, E), N0, E, kc),
  hpz: {W.Pz(Con{root, Nil{}}, P, m) == True{} : Bool},
  hacc: W.Acc(mo, m0, K, F, P0, Q0, N0, E, rs, ts, B0, e, t, hx, S, cs, ks, img, m, nx, Nil{}, P, Q, root, T)) ->
  D.Ok(Cr.Cir.exec(1n+f, Cr.Cir.Stmt.seq{Mc.M.copy.end(rr, rt), Cr.Cir.Stmt.nop{}}, D.S(rg, m, nx, F, K, pg, L, I)), F, K, L, I, Bu,
    rg => ms => nx3 => pg3 => D.Ex(D.Wt, w => D.Post(hx, mo, t, regs, scr, rr, ks, img, K, F, m0, P0, Q0, E, N0, Bc, rs, ts, kc, S, w, rg, ms, nx3))):
  (ht11, rhx) = hroot
  (acv, a1) = hacc
  (aclo, a2) = a1
  (_, a3) = a2
  (acnt, a4) = a3
  (_, a5) = a4
  (aincl, a6) = a5
  (asubw, a7) = a6
  (anfx, a8) = a7
  (asame, a9) = a8
  (akept, a10) = a9
  (_, a11) = a10
  (amds, a12) = a11
  (anx, a13) = a12
  (atkw, a14) = a13
  (agw, a15) = a14
  (asub, a16) = a15
  (ainall, a17) = a16
  (atcw, a18) = a17
  (apc, a19) = a18
  (ab214, abc) = a19
  +htb2 = htb
  +agw2 = agw
  +apc2 = apc
  +anx2 = anx
  +aincl2 = aincl
  +X = {List.append(&2, U32, P, Con{root, E}) : List<&2, U32>}
  +r = D.Fd(2n, m, root)
  +u = D.Mo.F(mo, t, 0n)
  +n = Nat.sub(U32.to_nat(nx), U32.to_nat(F))
  +n0 = Nat.sub(U32.to_nat(N0), U32.to_nat(F))
  +hl0 = D.Tmp.held(ts)
  +RH = List.append(&2, D.Rt, rs, hl0)
  +xc = Ec(m, root, pend)
  +ms = Cr.Cir.Cells.set(m, root, xc)
  +Pn = {Con{root, P} : List<&2, U32>}
  +Qn = {Con{root, Q} : List<&2, U32>}
  +h0 = {end.c0(Cr.Cir.Cells.get(m, root), pend) : {Cr.Cir.Cell.get(0n, xc) == 45 : U32}}
  +h1 = {end.c1(Cr.Cir.Cells.get(m, root), pend) : {Cr.Cir.Cell.get(1n, xc) == pend : U32}}
  +hz = end.hz(K, F, root, hk, hkf, hfr)
  +hzn = cell.own(root, K, F, nx, hkf, hfr, hrc)
  +eFn = K.Ar.sub.add(U32.to_nat(F), U32.to_nat(nx), K.U.le(F, nx, hfn))
  +eNF = Equal.sym(Nat, Nat.add(U32.to_nat(F), n), U32.to_nat(nx), eFn)
  +honce = W.once.at(n, F, root, nx, K.U.le(F, root, hfr),
    N.le_rw_r(1n+U32.to_nat(root), U32.to_nat(nx), Nat.add(U32.to_nat(F), n), eNF, K.U.lt(root, nx, hzn)),
    N.le_rw_l(U32.to_nat(nx), Nat.add(U32.to_nat(F), n), U32.to_nat(nx), eNF, N.le_refl(U32.to_nat(nx))))
  +hps = ps.prj(m, Q, root, ht11, htb2)
  +hPE = K.Bo.not_t(D.Has(List.append(&2, U32, P, E), root), K.Bo.and_l(Bool.not(D.Has(List.append(&2, U32, P, E), root)),
    W.Dj(Nil{}, List.append(&2, U32, P, E)), hdj))
  +hPEo = Equal.trans(Bool, Bool.or(D.Has(P, root), D.Has(E, root)), D.Has(List.append(&2, U32, P, E), root), False{},
    Equal.sym(Bool, D.Has(List.append(&2, U32, P, E), root), Bool.or(D.Has(P, root), D.Has(E, root)), K.has.app(P, E, root)), hPE)
  +hPz = K.or.fl(D.Has(P, root), D.Has(E, root), hPEo)
  +hEz = K.or.fr(D.Has(P, root), D.Has(E, root), hPEo)
  +hTz = K.Bo.and_l(D.Has(T, root), D.Sub(Nil{}, T), asubw)
  +hpzP = K.Na.eq(D.Pp(P, m, root), 0n, K.Bo.and_l(Nat.is_eq(D.Pp(P, m, root), 0n), W.Pz(Nil{}, P, m), hpz))
  +nxa = K.Bo.and_l(W.Nx.at(X, u, m, r), W.Nx(RH, m, X), anx2)
  +hnz = nxat.has(X, u, m, r, root, has.mid(P, root, E), nxa)
  +hNrz = nx.has(Con{D.Rt{0n, r, u}, RH}, m, X, root, has.mid(P, root, E), anx2)
  +hXr = Equal.trans(Bool, Bool.or(D.Has(P, r), D.Has(Con{root, E}, r)), D.Has(X, r), False{},
    Equal.sym(Bool, D.Has(X, r), Bool.or(D.Has(P, r), D.Has(Con{root, E}, r)), K.has.app(P, Con{root, E}, r)), nxat.out(X, u, m, r, nxa))
  +hPr = K.or.fl(D.Has(P, r), D.Has(Con{root, E}, r), hXr)
  +hinT = C.Has.incl(T, P0, N0, root, aincl2, hTz)
  +hal0 = al.out(K, F, P0, E, N0, root, K.U.lt_le(K, F, root, hkf, hfr), hinT)
  +hkn = K.U.lt_le(K, F, nx, hkf, hfn)
  +rh = rhx
  +g = end.g(hx, m, ks, img, K, F, P, E, nx, root, u, rh)
  +htm2 = end.tm(hx, m, ks, img, K, F, P, E, nx, root, xc, u, hkn, rh)
  +rg2 = List.set(&2, U32, List.set(&2, U32, rg, rr, r), 3n, root)
  +st = D.S(rg, m, nx, F, K, pg, L, I)
  +ce = Mc.M.copy.end(rr, rt)
  +st1 = D.S(rg2, EndM(m, root, pend), nx, F, K, pg, L, I)
  +hrun = W.end.run(1n+f, rr, rt, rg, m, nx, F, K, pg, L, I, root, pend, hl, hr, hrt, hrt1, hp1, hrc)
  +hseq = K.X.seq(f, ce, Cr.Cir.Stmt.nop{}, st, st1, Equal.sym(Cr.Cir.Out, Cr.Cir.exec(1n+f, ce, st), Cr.Cir.Out.next{st1}, hrun))
  +hone = Equal.cong(Cr.Cir.Cells, Cr.Cir.Out, w => Cr.Cir.Out.next{D.S(rg2, w, nx, F, K, pg, L, I)}, EndM(m, root, pend), ms, end.one(m, root, pend))
  +eo = Equal.trans(Cr.Cir.Out, Cr.Cir.exec(1n+f, Cr.Cir.Stmt.seq{ce, Cr.Cir.Stmt.nop{}}, st), Cr.Cir.exec(1n+f, Cr.Cir.Stmt.nop{}, st1),
    Cr.Cir.Out.next{D.S(rg2, ms, nx, F, K, pg, L, I)}, hseq,
    Equal.trans(Cr.Cir.Out, Cr.Cir.exec(1n+f, Cr.Cir.Stmt.nop{}, st1), Cr.Cir.Out.next{st1}, Cr.Cir.Out.next{D.S(rg2, ms, nx, F, K, pg, L, I)},
      Sr.run.nop(1n+f, st1), hone))
  +c5 = {(%Equal.sym(U32, T.tm.reg(rg2, 3n), root, h3) : {D.AL(ms, _, Pn, Qn, zs, K, F, nx) == True{} : Bool};
      al.end(m, pend, P, Q, zs, K, F, nx, root, xc, r, hkf, hfr, hzn, hz, h0, h1, honce, hps, hpzP, apc2, hPz, hPr, hal)) :
    {D.AL(ms, T.tm.reg(rg2, 3n), Pn, Qn, zs, K, F, nx) == True{} : Bool}}
  +c6 = K.Bo.and_i(U32.is_le(N0, nx), D.Incl.go(Pn, P0, N0), K.Bo.and_l(U32.is_le(N0, nx), D.Incl.go(X, P0, N0), hincl),
    K.Bo.and_i(Bool.or(D.Has(P0, root), U32.is_le(N0, root)), D.Incl.go(P, P0, N0), hinT, incl.gw(P, P0, T, N0, agw2)))
  +G0 = Bool.and(D.Has(T, root), Bool.and(U32.is_eq(D.Fd(0n, ms, root), 45), D.Has(Qn, root)))
  +c14 = K.Bo.and_i(Bool.or(Bool.and(D.Has(P0, root), Bool.not(D.Has(T, root))), G0), D.Gb(P, P0, T, Qn, ms),
    K.Bo.or_ir(Bool.and(D.Has(P0, root), Bool.not(D.Has(T, root))), G0,
      K.Bo.and_i(D.Has(T, root), Bool.and(U32.is_eq(D.Fd(0n, ms, root), 45), D.Has(Qn, root)), hTz,
        K.Bo.and_i(U32.is_eq(D.Fd(0n, ms, root), 45), D.Has(Qn, root),
          (%Equal.sym(U32, D.Fd(0n, ms, root), 45, f0.z(m, root, xc, h0)) : {U32.is_eq(_, 45) == True{} : Bool}; {==}), has.cons.eq(root, Q)))),
    gb.gw(P, P0, T, Qn, ms, agw2))
  +hne = K.Ar.ne.all(U32.to_nat(K), 1, root, N.le_trans(Nat.add(U32.to_nat(1), U32.to_nat(K)), U32.to_nat(F), U32.to_nat(root),
    K.U.lt(K, F, hkf), K.U.le(F, root, hfr)))
  +c23 = {(%hbc : {Bool.or(U32.is_eq(nx, N0), Nat.is_le(n, _)) == True{} : Bool}; abc) : {Bool.or(U32.is_eq(nx, N0), Nat.is_le(n, Bc)) == True{} : Bool}}
  +acnt2 = N.le_rw_l(Nat.add(U32.to_nat(nx), Nat.add(List.length(&2, U32, P0), 0n)), Nat.add(U32.to_nat(nx), List.length(&2, U32, P0)),
    Nat.add(U32.to_nat(N0), Nat.add(List.length(&2, U32, P), 1n+Pg.Term.size(u))),
    Equal.cong(Nat, Nat, w => Nat.add(U32.to_nat(nx), w), Nat.add(List.length(&2, U32, P0), 0n), List.length(&2, U32, P0),
      N.add_zero(List.length(&2, U32, P0))), acnt)
  +c24 = N.le_rw_r(Nat.add(U32.to_nat(nx), List.length(&2, U32, P0)), Nat.add(U32.to_nat(N0), Nat.add(List.length(&2, U32, P), 1n+Pg.Term.size(u))),
    Nat.add(U32.to_nat(N0), 1n+Nat.add(List.length(&2, U32, P), Pg.Term.size(u))),
    Equal.cong(Nat, Nat, w => Nat.add(U32.to_nat(N0), w), Nat.add(List.length(&2, U32, P), 1n+Pg.Term.size(u)),
      1n+Nat.add(List.length(&2, U32, P), Pg.Term.size(u)), N.add_succ_r(List.length(&2, U32, P), Pg.Term.size(u))), acnt2)
  K.Ok.eq(Cr.Cir.exec(1n+f, Cr.Cir.Stmt.seq{ce, Cr.Cir.Stmt.nop{}}, st), Cr.Cir.Out.next{D.S(rg2, ms, nx, F, K, pg, L, I)}, F, K, L, I, Bu,
    rg => ms => nx3 => pg3 => D.Ex(D.Wt, w => D.Post(hx, mo, t, regs, scr, rr, ks, img, K, F, m0, P0, Q0, E, N0, Bc, rs, ts, kc, S, w, rg, ms, nx3)),
    Equal.sym(Cr.Cir.Out, Cr.Cir.exec(1n+f, Cr.Cir.Stmt.seq{ce, Cr.Cir.Stmt.nop{}}, st), Cr.Cir.Out.next{D.S(rg2, ms, nx, F, K, pg, L, I)}, eo),
    K.Ok.next(rg2, ms, nx, F, K, pg, L, I, Bu,
      rg => ms => nx3 => pg3 => D.Ex(D.Wt, w => D.Post(hx, mo, t, regs, scr, rr, ks, img, K, F, m0, P0, Q0, E, N0, Bc, rs, ts, kc, S, w, rg, ms, nx3)),
      (D.Wt{ups, r, g, Pn, Qn, zs, T, cs},
        (hups, (hin, (hrr, (htm2, (c5, (c6, (K.tb.set(m, root, xc, hz, htb2),
        (rts.wx(RH, m, ks, img, K, F, List.append(&2, U32, P0, E), N0, root, xc, Equal.sym(Bool, D.Al(K, F, List.append(&2, U32, P0, E), N0, root), False{}, hal0), hrts),
        (kcs.wx(kc, m, K, F, List.append(&2, U32, P0, E), N0, E, root, xc, hal0, hEz, hkcs),
        (cv.end(n, m, F, P, root, xc, g, r, u, RH, List.append(&2, U32, D.Tmp.cells(ts), E), hNrz, acv),
        (clo.end(n, m, F, Q, root, xc, D.Tmp.cells(ts), D.Rt.cells(hl0), E, hz, h0, apc2, aclo),
        (made.set(u, m, m0, r, S, T, cs, root, xc, hnz, K.Bo.and_l(D.Made(u, m, m0, r, S, T, cs), W.Mds(Nil{}, m, m0, S, T, cs), amds)),
        (tk.end(T, m, P, root, xc, r, u, hnz, h0, atkw),
        (c14,
        (sub.ins(P0, T, root, P, asub),
        (aincl2,
        (ainall,
        (nf.end(T, m, root, xc, h0, anfx),
        (tc.end(T, m, P, Q, n, F, root, xc, r, hz, h0, honce, hps, atcw),
        (same.ne(U32.to_nat(K), m0, m, root, xc, 1, hne, asame),
        (kept.end(n0, m0, m, F, T, P, F, n0, n, Q0, Q, root, xc, r, hTz, hz, h0, honce, hps, akept),
        (ab214, (c23, c24))))))))))))))))))))))))))
