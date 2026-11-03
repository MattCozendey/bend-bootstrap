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
