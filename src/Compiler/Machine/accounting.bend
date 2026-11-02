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

# Bool and Nat kit
# ----------------

def or.assoc(a: Bool, -b: Bool, -c: Bool) -> {Bool.or(Bool.or(a, b), c) == Bool.or(a, Bool.or(b, c)) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def or.swap(a: Bool, b: Bool, -c: Bool) -> {Bool.or(a, Bool.or(b, c)) == Bool.or(b, Bool.or(a, c)) : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def or.cong2(-a1: Bool, -a2: Bool, -b1: Bool, -b2: Bool, e1: {a1 == a2 : Bool}, e2: {b1 == b2 : Bool}) ->
  {Bool.or(a1, b1) == Bool.or(a2, b2) : Bool}:
  %e1 : {Bool.or(a1, b1) == Bool.or(_, b2) : Bool}
  %e2 : {Bool.or(a1, b1) == Bool.or(a1, _) : Bool}
  {==}

def and.false(a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def or.true(a: Bool) -> {Bool.or(a, True{}) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def or.mono.r(a: Bool, -b: Bool, -b2: Bool, h: {Bool.or(a, b) == True{} : Bool}, k: {b == True{} : Bool} -> {b2 == True{} : Bool}) ->
  {Bool.or(a, b2) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      k(h)


def of.or(a: Bool, b: Bool) -> N.Le(D.Nat.of(Bool.or(a, b)), Nat.add(D.Nat.of(a), D.Nat.of(b))):
  match a b:
    case True{} True{}:
      Unit{}
    case True{} False{}:
      Unit{}
    case False{} True{}:
      Unit{}
    case False{} False{}:
      Unit{}

def of3(a: Bool, b: Bool, c: Bool, h: {Bool.or(a, Bool.or(b, c)) == True{} : Bool}) ->
  N.Le(1n, Nat.add(D.Nat.of(a), Nat.add(D.Nat.of(b), D.Nat.of(c)))):
  match a b c:
    case True{} True{} True{}:
      Unit{}
    case True{} True{} False{}:
      Unit{}
    case True{} False{} True{}:
      Unit{}
    case True{} False{} False{}:
      Unit{}
    case False{} True{} True{}:
      Unit{}
    case False{} True{} False{}:
      Unit{}
    case False{} False{} True{}:
      Unit{}
    case False{} False{} False{}:
      D.bool.ft(N.Le(1n, 0n), h)

def add.comm(a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, N.add_zero(b))
    case 1n+(+q):
      %Equal.sym(Nat, Nat.add(q, b), Nat.add(b, q), add.comm(q, b)) : {1n+_ == Nat.add(b, 1n+q) : Nat}
      Equal.sym(Nat, Nat.add(b, 1n+q), 1n+Nat.add(b, q), N.add_succ_r(b, q))

def add4(+a: Nat, +b: Nat, +c: Nat, +d: Nat) -> {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(a, b), Nat.add(c, d)), Nat.add(a, Nat.add(b, Nat.add(c, d))), Nat.add(Nat.add(a, c), Nat.add(b, d)),
    N.add_assoc(a, b, Nat.add(c, d)),
    Equal.trans(Nat, Nat.add(a, Nat.add(b, Nat.add(c, d))), Nat.add(a, Nat.add(c, Nat.add(b, d))), Nat.add(Nat.add(a, c), Nat.add(b, d)),
      Equal.cong(Nat, Nat, x => Nat.add(a, x), Nat.add(b, Nat.add(c, d)), Nat.add(c, Nat.add(b, d)), N.add_swap(b, c, d)),
      Equal.sym(Nat, Nat.add(Nat.add(a, c), Nat.add(b, d)), Nat.add(a, Nat.add(c, Nat.add(b, d))), N.add_assoc(a, c, Nat.add(b, d)))))

# the n cells from c do not wrap: 1 + c is the next one's number
def inc.nat(+c: U32, +k: Nat, +e: U32, hw: N.Le(Nat.add(U32.to_nat(c), 1n+k), U32.to_nat(e))) ->
  {U32.to_nat(U32.inc(c)) == 1n+U32.to_nat(c) : Nat}:
  D.u.inc(c, e, N.le_trans(1n+U32.to_nat(c), Nat.add(U32.to_nat(c), 1n+k), U32.to_nat(e), N.lt_add(U32.to_nat(c), k), hw))

# and the cells after the first do not wrap either
def hw.inc(+c: U32, +k: Nat, +e: U32, hw: N.Le(Nat.add(U32.to_nat(c), 1n+k), U32.to_nat(e))) ->
  N.Le(Nat.add(U32.to_nat(U32.inc(c)), k), U32.to_nat(e)):
  +hw2 = hw
  %Equal.sym(Nat, U32.to_nat(U32.inc(c)), 1n+U32.to_nat(c), inc.nat(c, k, e, hw2)) : N.Le(Nat.add(_, k), U32.to_nat(e))
  N.le_rw_l(Nat.add(U32.to_nat(c), 1n+k), 1n+Nat.add(U32.to_nat(c), k), U32.to_nat(e), N.add_succ_r(U32.to_nat(c), k), hw2)

def ne.lt.b(b: Bool, +y: U32, +c: U32, eb: {U32.is_eq(y, c) == b : Bool}, h: N.Le(1n+U32.to_nat(y), U32.to_nat(c))) ->
  {U32.is_eq(y, c) == False{} : Bool}:
  match b:
    case False{}:
      eb
    case True{}:
      Empty.absurd({U32.is_eq(y, c) == False{} : Bool},
        N.not_succ_le(U32.to_nat(c), (%D.u32.eq(y, c, eb) : N.Le(1n+U32.to_nat(_), U32.to_nat(c)); h)))

# a cell below c is not c
def ne.lt(+y: U32, +c: U32, h: N.Le(1n+U32.to_nat(y), U32.to_nat(c))) -> {U32.is_eq(y, c) == False{} : Bool}:
  ne.lt.b(U32.is_eq(y, c), y, c, {==}, h)

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

# Node, one step unfolded
def node.step.at(t: Bk.Term, +m: Cr.Cir.Cells, +r: U32, +x: U32) -> {D.Node(t, m, r, x) == CP.at(CP.node.step(t, m, r), x) : Bool}:
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

# Nodes, one step unfolded
def nodes.step.at(rs: List<&2, D.Rt>, +m: Cr.Cir.Cells, +x: U32) -> {D.Nodes(rs, m, x) == CP.at(CP.nodes.step(rs, m), x) : Bool}:
  match rs:
    case Nil{}:
      {==}
    case Con{D.Rt{_, _}, _}:
      {==}

# Mem, one step unfolded
def mem.step.at(xs: List<&2, U32>, +x: U32) -> {D.Mem(xs, x) == CP.at(CP.mem.step(xs), x) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{_, _}:
      {==}

# p and its step hold of the same cells
def cp.step.at(p: CP, +x: U32) -> {CP.at(p, x) == CP.at(CP.step(p), x) : Bool}:
  match p:
    case CP.node{t, +m, +r}:
      node.step.at(t, m, r, x)
    case CP.nodes{rs, +m}:
      nodes.step.at(rs, m, x)
    case CP.mem{xs}:
      mem.step.at(xs, x)
    case CP.eq{y}:
      {==}
    case CP.or{a, b}:
      {==}
    case CP.none{}:
      {==}

# so they count the same cells
def many.step(n: Nat, +c: U32, +p: CP) -> {Many(n, c, p) == Many(n, c, CP.step(p)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+(+k):
      %cp.step.at(p, c) : {Nat.add(D.Nat.of(CP.at(p, c)), Many(k, U32.inc(c), p)) == Nat.add(D.Nat.of(_), Many(k, U32.inc(c), CP.step(p))) : Nat}
      %many.step(k, U32.inc(c), p) : {Nat.add(D.Nat.of(CP.at(p, c)), Many(k, U32.inc(c), p)) == Nat.add(D.Nat.of(CP.at(p, c)), _) : Nat}
      {==}

# either of a and b holds of at most the cells that a holds of and those that
# b holds of
def many.or(n: Nat, +c: U32, +a: CP, +b: CP) -> N.Le(Many(n, c, CP.or{a, b}), Nat.add(Many(n, c, a), Many(n, c, b))):
  match n:
    case 0n:
      Unit{}
    case 1n+(+k):
      +A = CP.at(a, c)
      +B = CP.at(b, c)
      +Ma = Many(k, U32.inc(c), a)
      +Mb = Many(k, U32.inc(c), b)
      N.le_rw_r(Nat.add(D.Nat.of(Bool.or(A, B)), Many(k, U32.inc(c), CP.or{a, b})), Nat.add(Nat.add(D.Nat.of(A), D.Nat.of(B)), Nat.add(Ma, Mb)),
        Nat.add(Nat.add(D.Nat.of(A), Ma), Nat.add(D.Nat.of(B), Mb)), add4(D.Nat.of(A), D.Nat.of(B), Ma, Mb),
        N.add_mono(D.Nat.of(Bool.or(A, B)), Nat.add(D.Nat.of(A), D.Nat.of(B)), Many(k, U32.inc(c), CP.or{a, b}), Nat.add(Ma, Mb),
          of.or(A, B), many.or(k, U32.inc(c), a, b)))

# none of the k cells from c, all above y (no wrap), is y
def many.eq.past(k: Nat, +c: U32, +y: U32, +e: U32, hlt: N.Le(1n+U32.to_nat(y), U32.to_nat(c)),
  hw: N.Le(Nat.add(U32.to_nat(c), k), U32.to_nat(e))) -> {Many(k, c, CP.eq{y}) == 0n : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+(+j):
      +hw2 = hw
      +hlt2 = hlt
      +hlt3 = N.le_rw_r(1n+U32.to_nat(y), 1n+U32.to_nat(c), U32.to_nat(U32.inc(c)),
        Equal.sym(Nat, U32.to_nat(U32.inc(c)), 1n+U32.to_nat(c), inc.nat(c, j, e, hw2)), N.le_succ(1n+U32.to_nat(y), U32.to_nat(c), hlt2))
      %Equal.sym(Bool, U32.is_eq(y, c), False{}, ne.lt(y, c, hlt2)) : {Nat.add(D.Nat.of(_), Many(j, U32.inc(c), CP.eq{y})) == 0n : Nat}
      many.eq.past(j, U32.inc(c), y, e, hlt3, hw.inc(c, j, e, hw2))

def many.eq.b(b: Bool, +k: Nat, +c: U32, +y: U32, +e: U32, eb: {U32.is_eq(y, c) == b : Bool},
  hw: N.Le(Nat.add(U32.to_nat(c), 1n+k), U32.to_nat(e)), ih: N.Le(Many(k, U32.inc(c), CP.eq{y}), 1n)) ->
  N.Le(Nat.add(D.Nat.of(b), Many(k, U32.inc(c), CP.eq{y})), 1n):
  match b:
    case True{}:
      +hw2 = hw
      +hlt = N.le_rw_r(1n+U32.to_nat(y), 1n+U32.to_nat(c), U32.to_nat(U32.inc(c)),
        Equal.sym(Nat, U32.to_nat(U32.inc(c)), 1n+U32.to_nat(c), inc.nat(c, k, e, hw2)),
        (%D.u32.eq(y, c, eb) : N.Le(1n+U32.to_nat(y), 1n+U32.to_nat(_)); N.le_refl(1n+U32.to_nat(y))))
      %Equal.sym(Nat, Many(k, U32.inc(c), CP.eq{y}), 0n, many.eq.past(k, U32.inc(c), y, e, hlt, hw.inc(c, k, e, hw2))) : N.Le(Nat.add(1n, _), 1n)
      Unit{}
    case False{}:
      ih

# the n cells from c, which end at or before the cell e (they do not wrap):
# at most one of them is y
def many.eq(n: Nat, +c: U32, +y: U32, +e: U32, hw: N.Le(Nat.add(U32.to_nat(c), n), U32.to_nat(e))) ->
  N.Le(Many(n, c, CP.eq{y}), 1n):
  match n:
    case 0n:
      Unit{}
    case 1n+(+k):
      +hw2 = hw
      many.eq.b(U32.is_eq(y, c), k, c, y, e, {==}, hw2, many.eq(k, U32.inc(c), y, e, hw.inc(c, k, e, hw2)))

# none of the cells
def many.none(n: Nat, +c: U32) -> N.Le(Many(n, c, CP.none{}), 0n):
  match n:
    case 0n:
      Unit{}
    case 1n+(+k):
      many.none(k, U32.inc(c))

# the cell r, or a: at most 1 + sa
def le1(+n: Nat, +c: U32, +r: U32, +a: CP, +sa: Nat, +e: U32, ha: N.Le(Many(n, c, a), sa),
  hw: N.Le(Nat.add(U32.to_nat(c), n), U32.to_nat(e))) -> N.Le(Many(n, c, CP.or{CP.eq{r}, a}), 1n+sa):
  N.le_trans(Many(n, c, CP.or{CP.eq{r}, a}), Nat.add(Many(n, c, CP.eq{r}), Many(n, c, a)), 1n+sa,
    many.or(n, c, CP.eq{r}, a),
    N.add_mono(Many(n, c, CP.eq{r}), 1n, Many(n, c, a), sa, many.eq(n, c, r, e, hw), ha))

# the cell r, or a, or b: at most 1 + sa + sb
def le2(+n: Nat, +c: U32, +r: U32, +a: CP, +b: CP, +sa: Nat, +sb: Nat, +e: U32, ha: N.Le(Many(n, c, a), sa),
  hb: N.Le(Many(n, c, b), sb), hw: N.Le(Nat.add(U32.to_nat(c), n), U32.to_nat(e))) ->
  N.Le(Many(n, c, CP.or{CP.eq{r}, CP.or{a, b}}), 1n+Nat.add(sa, sb)):
  le1(n, c, r, CP.or{a, b}, Nat.add(sa, sb), e,
    N.le_trans(Many(n, c, CP.or{a, b}), Nat.add(Many(n, c, a), Many(n, c, b)), Nat.add(sa, sb), many.or(n, c, a, b),
      N.add_mono(Many(n, c, a), sa, Many(n, c, b), sb, ha, hb)), hw)

# the cell r, or a, b or d: at most 1 + sa + sb + sd
def le3(+n: Nat, +c: U32, +r: U32, +a: CP, +b: CP, +d: CP, +sa: Nat, +sb: Nat, +sd: Nat, +e: U32, ha: N.Le(Many(n, c, a), sa),
  hb: N.Le(Many(n, c, b), sb), hd: N.Le(Many(n, c, d), sd), hw: N.Le(Nat.add(U32.to_nat(c), n), U32.to_nat(e))) ->
  N.Le(Many(n, c, CP.or{CP.eq{r}, CP.or{a, CP.or{b, d}}}), 1n+Nat.add(sa, Nat.add(sb, sd))):
  le1(n, c, r, CP.or{a, CP.or{b, d}}, Nat.add(sa, Nat.add(sb, sd)), e,
    N.le_trans(Many(n, c, CP.or{a, CP.or{b, d}}), Nat.add(Many(n, c, a), Many(n, c, CP.or{b, d})), Nat.add(sa, Nat.add(sb, sd)),
      many.or(n, c, a, CP.or{b, d}),
      N.add_mono(Many(n, c, a), sa, Many(n, c, CP.or{b, d}), Nat.add(sb, sd), ha,
        N.le_trans(Many(n, c, CP.or{b, d}), Nat.add(Many(n, c, b), Many(n, c, d)), Nat.add(sb, sd), many.or(n, c, b, d),
          N.add_mono(Many(n, c, b), sb, Many(n, c, d), sd, hb, hd)))), hw)

# the nodes of t at r are at most |t| of the n cells from c (no wrap)
def node.many(t: Bk.Term, +m: Cr.Cir.Cells, +r: U32, +n: Nat, +c: U32, +e: U32,
  hw: N.Le(Nat.add(U32.to_nat(c), n), U32.to_nat(e))) -> N.Le(Many(n, c, CP.node{t, m, r}), Pg.Term.size(t)):
  match t:
    case Bk.Term.Var{+i}:
      %Equal.sym(Nat, Many(n, c, CP.node{Bk.Term.Var{i}, m, r}), Many(n, c, CP.eq{r}), many.step(n, c, CP.node{Bk.Term.Var{i}, m, r})) : N.Le(_, 1n)
      many.eq(n, c, r, e, hw)
    case Bk.Term.Ref{+k}:
      %Equal.sym(Nat, Many(n, c, CP.node{Bk.Term.Ref{k}, m, r}), Many(n, c, CP.eq{r}), many.step(n, c, CP.node{Bk.Term.Ref{k}, m, r})) : N.Le(_, 1n)
      many.eq(n, c, r, e, hw)
    case Bk.Term.Ann{+y, +z}:
      +hw2 = hw
      %Equal.sym(Nat, Many(n, c, CP.node{Bk.Term.Ann{y, z}, m, r}), Many(n, c, CP.or{CP.eq{r}, CP.or{CP.node{y, m, D.Fd(2n, m, r)}, CP.node{z, m, D.Fd(3n, m, r)}}}),
        many.step(n, c, CP.node{Bk.Term.Ann{y, z}, m, r})) : N.Le(_, 1n+Nat.add(Pg.Term.size(y), Pg.Term.size(z)))
      le2(n, c, r, CP.node{y, m, D.Fd(2n, m, r)}, CP.node{z, m, D.Fd(3n, m, r)}, Pg.Term.size(y), Pg.Term.size(z), e,
        node.many(y, m, D.Fd(2n, m, r), n, c, e, hw2), node.many(z, m, D.Fd(3n, m, r), n, c, e, hw2), hw2)
    case Bk.Term.Let{+q, +v, +f}:
      +hw2 = hw
      %Equal.sym(Nat, Many(n, c, CP.node{Bk.Term.Let{q, v, f}, m, r}), Many(n, c, CP.or{CP.eq{r}, CP.or{CP.node{v, m, D.Fd(2n, m, r)}, CP.node{f, m, D.Fd(3n, m, r)}}}),
        many.step(n, c, CP.node{Bk.Term.Let{q, v, f}, m, r})) : N.Le(_, 1n+Nat.add(Pg.Term.size(v), Pg.Term.size(f)))
      le2(n, c, r, CP.node{v, m, D.Fd(2n, m, r)}, CP.node{f, m, D.Fd(3n, m, r)}, Pg.Term.size(v), Pg.Term.size(f), e,
        node.many(v, m, D.Fd(2n, m, r), n, c, e, hw2), node.many(f, m, D.Fd(3n, m, r), n, c, e, hw2), hw2)
    case Bk.Term.Typ{+y}:
      +hw2 = hw
      %Equal.sym(Nat, Many(n, c, CP.node{Bk.Term.Typ{y}, m, r}), Many(n, c, CP.or{CP.eq{r}, CP.node{y, m, D.Fd(2n, m, r)}}),
        many.step(n, c, CP.node{Bk.Term.Typ{y}, m, r})) : N.Le(_, 1n+Pg.Term.size(y))
      le1(n, c, r, CP.node{y, m, D.Fd(2n, m, r)}, Pg.Term.size(y), e, node.many(y, m, D.Fd(2n, m, r), n, c, e, hw2), hw2)
    case Bk.Term.Min{+a, +b}:
      +hw2 = hw
      %Equal.sym(Nat, Many(n, c, CP.node{Bk.Term.Min{a, b}, m, r}), Many(n, c, CP.or{CP.eq{r}, CP.or{CP.node{a, m, D.Fd(2n, m, r)}, CP.node{b, m, D.Fd(3n, m, r)}}}),
        many.step(n, c, CP.node{Bk.Term.Min{a, b}, m, r})) : N.Le(_, 1n+Nat.add(Pg.Term.size(a), Pg.Term.size(b)))
      le2(n, c, r, CP.node{a, m, D.Fd(2n, m, r)}, CP.node{b, m, D.Fd(3n, m, r)}, Pg.Term.size(a), Pg.Term.size(b), e,
        node.many(a, m, D.Fd(2n, m, r), n, c, e, hw2), node.many(b, m, D.Fd(3n, m, r), n, c, e, hw2), hw2)
    case Bk.Term.All{+q, +a, +b}:
      +hw2 = hw
      %Equal.sym(Nat, Many(n, c, CP.node{Bk.Term.All{q, a, b}, m, r}), Many(n, c, CP.or{CP.eq{r}, CP.or{CP.node{a, m, D.Fd(2n, m, r)}, CP.node{b, m, D.Fd(3n, m, r)}}}),
        many.step(n, c, CP.node{Bk.Term.All{q, a, b}, m, r})) : N.Le(_, 1n+Nat.add(Pg.Term.size(a), Pg.Term.size(b)))
      le2(n, c, r, CP.node{a, m, D.Fd(2n, m, r)}, CP.node{b, m, D.Fd(3n, m, r)}, Pg.Term.size(a), Pg.Term.size(b), e,
        node.many(a, m, D.Fd(2n, m, r), n, c, e, hw2), node.many(b, m, D.Fd(3n, m, r), n, c, e, hw2), hw2)
    case Bk.Term.Lam{+q, +f}:
      +hw2 = hw
      %Equal.sym(Nat, Many(n, c, CP.node{Bk.Term.Lam{q, f}, m, r}), Many(n, c, CP.or{CP.eq{r}, CP.node{f, m, D.Fd(2n, m, r)}}),
        many.step(n, c, CP.node{Bk.Term.Lam{q, f}, m, r})) : N.Le(_, 1n+Pg.Term.size(f))
      le1(n, c, r, CP.node{f, m, D.Fd(2n, m, r)}, Pg.Term.size(f), e, node.many(f, m, D.Fd(2n, m, r), n, c, e, hw2), hw2)
    case Bk.Term.App{+q, +f, +y}:
      +hw2 = hw
      %Equal.sym(Nat, Many(n, c, CP.node{Bk.Term.App{q, f, y}, m, r}), Many(n, c, CP.or{CP.eq{r}, CP.or{CP.node{f, m, D.Fd(2n, m, r)}, CP.node{y, m, D.Fd(3n, m, r)}}}),
        many.step(n, c, CP.node{Bk.Term.App{q, f, y}, m, r})) : N.Le(_, 1n+Nat.add(Pg.Term.size(f), Pg.Term.size(y)))
      le2(n, c, r, CP.node{f, m, D.Fd(2n, m, r)}, CP.node{y, m, D.Fd(3n, m, r)}, Pg.Term.size(f), Pg.Term.size(y), e,
        node.many(f, m, D.Fd(2n, m, r), n, c, e, hw2), node.many(y, m, D.Fd(3n, m, r), n, c, e, hw2), hw2)
    case Bk.Term.Sig{+q, +a, +b}:
      +hw2 = hw
      %Equal.sym(Nat, Many(n, c, CP.node{Bk.Term.Sig{q, a, b}, m, r}), Many(n, c, CP.or{CP.eq{r}, CP.or{CP.node{a, m, D.Fd(2n, m, r)}, CP.node{b, m, D.Fd(3n, m, r)}}}),
        many.step(n, c, CP.node{Bk.Term.Sig{q, a, b}, m, r})) : N.Le(_, 1n+Nat.add(Pg.Term.size(a), Pg.Term.size(b)))
      le2(n, c, r, CP.node{a, m, D.Fd(2n, m, r)}, CP.node{b, m, D.Fd(3n, m, r)}, Pg.Term.size(a), Pg.Term.size(b), e,
        node.many(a, m, D.Fd(2n, m, r), n, c, e, hw2), node.many(b, m, D.Fd(3n, m, r), n, c, e, hw2), hw2)
    case Bk.Term.Tup{+q, +a, +b}:
      +hw2 = hw
      %Equal.sym(Nat, Many(n, c, CP.node{Bk.Term.Tup{q, a, b}, m, r}), Many(n, c, CP.or{CP.eq{r}, CP.or{CP.node{a, m, D.Fd(2n, m, r)}, CP.node{b, m, D.Fd(3n, m, r)}}}),
        many.step(n, c, CP.node{Bk.Term.Tup{q, a, b}, m, r})) : N.Le(_, 1n+Nat.add(Pg.Term.size(a), Pg.Term.size(b)))
      le2(n, c, r, CP.node{a, m, D.Fd(2n, m, r)}, CP.node{b, m, D.Fd(3n, m, r)}, Pg.Term.size(a), Pg.Term.size(b), e,
        node.many(a, m, D.Fd(2n, m, r), n, c, e, hw2), node.many(b, m, D.Fd(3n, m, r), n, c, e, hw2), hw2)
    case Bk.Term.Prj{+h}:
      +hw2 = hw
      %Equal.sym(Nat, Many(n, c, CP.node{Bk.Term.Prj{h}, m, r}), Many(n, c, CP.or{CP.eq{r}, CP.node{h, m, D.Fd(2n, m, r)}}),
        many.step(n, c, CP.node{Bk.Term.Prj{h}, m, r})) : N.Le(_, 1n+Pg.Term.size(h))
      le1(n, c, r, CP.node{h, m, D.Fd(2n, m, r)}, Pg.Term.size(h), e, node.many(h, m, D.Fd(2n, m, r), n, c, e, hw2), hw2)
    case Bk.Term.Enu{+k}:
      %Equal.sym(Nat, Many(n, c, CP.node{Bk.Term.Enu{k}, m, r}), Many(n, c, CP.eq{r}), many.step(n, c, CP.node{Bk.Term.Enu{k}, m, r})) : N.Le(_, 1n)
      many.eq(n, c, r, e, hw)
    case Bk.Term.Lab{+k}:
      %Equal.sym(Nat, Many(n, c, CP.node{Bk.Term.Lab{k}, m, r}), Many(n, c, CP.eq{r}), many.step(n, c, CP.node{Bk.Term.Lab{k}, m, r})) : N.Le(_, 1n)
      many.eq(n, c, r, e, hw)
    case Bk.Term.Mat{+k, +h, +o}:
      +hw2 = hw
      %Equal.sym(Nat, Many(n, c, CP.node{Bk.Term.Mat{k, h, o}, m, r}), Many(n, c, CP.or{CP.eq{r}, CP.or{CP.node{h, m, D.Fd(3n, m, r)}, CP.node{o, m, D.Fd(4n, m, r)}}}),
        many.step(n, c, CP.node{Bk.Term.Mat{k, h, o}, m, r})) : N.Le(_, 1n+Nat.add(Pg.Term.size(h), Pg.Term.size(o)))
      le2(n, c, r, CP.node{h, m, D.Fd(3n, m, r)}, CP.node{o, m, D.Fd(4n, m, r)}, Pg.Term.size(h), Pg.Term.size(o), e,
        node.many(h, m, D.Fd(3n, m, r), n, c, e, hw2), node.many(o, m, D.Fd(4n, m, r), n, c, e, hw2), hw2)
    case Bk.Term.Efq{}:
      %Equal.sym(Nat, Many(n, c, CP.node{Bk.Term.Efq{}, m, r}), Many(n, c, CP.eq{r}), many.step(n, c, CP.node{Bk.Term.Efq{}, m, r})) : N.Le(_, 1n)
      many.eq(n, c, r, e, hw)
    case Bk.Term.Eql{+a, +b, +y}:
      +hw2 = hw
      %Equal.sym(Nat, Many(n, c, CP.node{Bk.Term.Eql{a, b, y}, m, r}),
        Many(n, c, CP.or{CP.eq{r}, CP.or{CP.node{a, m, D.Fd(2n, m, r)}, CP.or{CP.node{b, m, D.Fd(3n, m, r)}, CP.node{y, m, D.Fd(4n, m, r)}}}}),
        many.step(n, c, CP.node{Bk.Term.Eql{a, b, y}, m, r})) : N.Le(_, 1n+Nat.add(Pg.Term.size(a), Nat.add(Pg.Term.size(b), Pg.Term.size(y))))
      le3(n, c, r, CP.node{a, m, D.Fd(2n, m, r)}, CP.node{b, m, D.Fd(3n, m, r)}, CP.node{y, m, D.Fd(4n, m, r)},
        Pg.Term.size(a), Pg.Term.size(b), Pg.Term.size(y), e,
        node.many(a, m, D.Fd(2n, m, r), n, c, e, hw2), node.many(b, m, D.Fd(3n, m, r), n, c, e, hw2),
        node.many(y, m, D.Fd(4n, m, r), n, c, e, hw2), hw2)
    case Bk.Term.Rfl{}:
      %Equal.sym(Nat, Many(n, c, CP.node{Bk.Term.Rfl{}, m, r}), Many(n, c, CP.eq{r}), many.step(n, c, CP.node{Bk.Term.Rfl{}, m, r})) : N.Le(_, 1n)
      many.eq(n, c, r, e, hw)
    case Bk.Term.Rwt{+a, +b, +y}:
      +hw2 = hw
      %Equal.sym(Nat, Many(n, c, CP.node{Bk.Term.Rwt{a, b, y}, m, r}),
        Many(n, c, CP.or{CP.eq{r}, CP.or{CP.node{a, m, D.Fd(2n, m, r)}, CP.or{CP.node{b, m, D.Fd(3n, m, r)}, CP.node{y, m, D.Fd(4n, m, r)}}}}),
        many.step(n, c, CP.node{Bk.Term.Rwt{a, b, y}, m, r})) : N.Le(_, 1n+Nat.add(Pg.Term.size(a), Nat.add(Pg.Term.size(b), Pg.Term.size(y))))
      le3(n, c, r, CP.node{a, m, D.Fd(2n, m, r)}, CP.node{b, m, D.Fd(3n, m, r)}, CP.node{y, m, D.Fd(4n, m, r)},
        Pg.Term.size(a), Pg.Term.size(b), Pg.Term.size(y), e,
        node.many(a, m, D.Fd(2n, m, r), n, c, e, hw2), node.many(b, m, D.Fd(3n, m, r), n, c, e, hw2),
        node.many(y, m, D.Fd(4n, m, r), n, c, e, hw2), hw2)

# the nodes of the roots' terms are at most their nodes
def nodes.many(rs: List<&2, D.Rt>, +m: Cr.Cir.Cells, +n: Nat, +c: U32, +e: U32,
  hw: N.Le(Nat.add(U32.to_nat(c), n), U32.to_nat(e))) -> N.Le(Many(n, c, CP.nodes{rs, m}), D.Rts.size(rs)):
  match rs:
    case Nil{}:
      %Equal.sym(Nat, Many(n, c, CP.nodes{Nil{}, m}), Many(n, c, CP.none{}), many.step(n, c, CP.nodes{Nil{}, m})) : N.Le(_, 0n)
      many.none(n, c)
    case Con{D.Rt{+r, +u}, +rest}:
      +hw2 = hw
      %Equal.sym(Nat, Many(n, c, CP.nodes{Con{D.Rt{r, u}, rest}, m}), Many(n, c, CP.or{CP.node{u, m, r}, CP.nodes{rest, m}}),
        many.step(n, c, CP.nodes{Con{D.Rt{r, u}, rest}, m})) : N.Le(_, Nat.add(Pg.Term.size(u), D.Rts.size(rest)))
      N.le_trans(Many(n, c, CP.or{CP.node{u, m, r}, CP.nodes{rest, m}}), Nat.add(Many(n, c, CP.node{u, m, r}), Many(n, c, CP.nodes{rest, m})),
        Nat.add(Pg.Term.size(u), D.Rts.size(rest)), many.or(n, c, CP.node{u, m, r}, CP.nodes{rest, m}),
        N.add_mono(Many(n, c, CP.node{u, m, r}), Pg.Term.size(u), Many(n, c, CP.nodes{rest, m}), D.Rts.size(rest),
          node.many(u, m, r, n, c, e, hw2), nodes.many(rest, m, n, c, e, hw2)))

# the cells xs are at most |xs| of them
def mem.many(xs: List<&2, U32>, +n: Nat, +c: U32, +e: U32, hw: N.Le(Nat.add(U32.to_nat(c), n), U32.to_nat(e))) ->
  N.Le(Many(n, c, CP.mem{xs}), List.length(&2, U32, xs)):
  match xs:
    case Nil{}:
      %Equal.sym(Nat, Many(n, c, CP.mem{Nil{}}), Many(n, c, CP.none{}), many.step(n, c, CP.mem{Nil{}})) : N.Le(_, 0n)
      many.none(n, c)
    case Con{+y, +rest}:
      +hw2 = hw
      %Equal.sym(Nat, Many(n, c, CP.mem{Con{y, rest}}), Many(n, c, CP.or{CP.eq{y}, CP.mem{rest}}), many.step(n, c, CP.mem{Con{y, rest}})) :
        N.Le(_, 1n+List.length(&2, U32, rest))
      N.le_trans(Many(n, c, CP.or{CP.eq{y}, CP.mem{rest}}), Nat.add(Many(n, c, CP.eq{y}), Many(n, c, CP.mem{rest})),
        1n+List.length(&2, U32, rest), many.or(n, c, CP.eq{y}, CP.mem{rest}),
        N.add_mono(Many(n, c, CP.eq{y}), 1n, Many(n, c, CP.mem{rest}), List.length(&2, U32, rest), many.eq(n, c, y, e, hw2),
          mem.many(rest, n, c, e, hw2)))

# each of the n cells that Cov covers is STATIC, a node of a root's term or
# one of xs
def cov.many(n: Nat, +m: Cr.Cir.Cells, +c: U32, +rs: List<&2, D.Rt>, +xs: List<&2, U32>,
  h: {D.Cov(n, m, c, rs, xs) == True{} : Bool}) ->
  N.Le(n, Nat.add(D.Stat(n, m, c), Nat.add(Many(n, c, CP.nodes{rs, m}), Many(n, c, CP.mem{xs})))):
  match n:
    case 0n:
      Unit{}
    case 1n+(+k):
      +h2 = h
      +F = D.Fl(m, c, 1024)
      +Nd = D.Nodes(rs, m, c)
      +Mm = D.Mem(xs, c)
      +S = D.Stat(k, m, U32.inc(c))
      +A = Many(k, U32.inc(c), CP.nodes{rs, m})
      +B = Many(k, U32.inc(c), CP.mem{xs})
      +h0 = D.and.l(Bool.or(F, Bool.or(Nd, Mm)), D.Cov(k, m, U32.inc(c), rs, xs), h2)
      +ih = cov.many(k, m, U32.inc(c), rs, xs, D.and.r(Bool.or(F, Bool.or(Nd, Mm)), D.Cov(k, m, U32.inc(c), rs, xs), h2))
      N.le_rw_r(1n+k, Nat.add(Nat.add(D.Nat.of(F), Nat.add(D.Nat.of(Nd), D.Nat.of(Mm))), Nat.add(S, Nat.add(A, B))),
        Nat.add(Nat.add(D.Nat.of(F), S), Nat.add(Nat.add(D.Nat.of(Nd), A), Nat.add(D.Nat.of(Mm), B))),
        Equal.trans(Nat, Nat.add(Nat.add(D.Nat.of(F), Nat.add(D.Nat.of(Nd), D.Nat.of(Mm))), Nat.add(S, Nat.add(A, B))),
          Nat.add(Nat.add(D.Nat.of(F), S), Nat.add(Nat.add(D.Nat.of(Nd), D.Nat.of(Mm)), Nat.add(A, B))),
          Nat.add(Nat.add(D.Nat.of(F), S), Nat.add(Nat.add(D.Nat.of(Nd), A), Nat.add(D.Nat.of(Mm), B))),
          add4(D.Nat.of(F), Nat.add(D.Nat.of(Nd), D.Nat.of(Mm)), S, Nat.add(A, B)),
          Equal.cong(Nat, Nat, w => Nat.add(Nat.add(D.Nat.of(F), S), w), Nat.add(Nat.add(D.Nat.of(Nd), D.Nat.of(Mm)), Nat.add(A, B)),
            Nat.add(Nat.add(D.Nat.of(Nd), A), Nat.add(D.Nat.of(Mm), B)), add4(D.Nat.of(Nd), D.Nat.of(Mm), A, B))),
        N.add_mono(1n, Nat.add(D.Nat.of(F), Nat.add(D.Nat.of(Nd), D.Nat.of(Mm))), k, Nat.add(S, Nat.add(A, B)), of3(F, Nd, Mm, h0), ih))

# the n cells that Cov covers (no wrap) are at most the STATIC ones, the
# roots' nodes and the cells xs
def cov.count(+n: Nat, +m: Cr.Cir.Cells, +c: U32, +rs: List<&2, D.Rt>, +xs: List<&2, U32>, +e: U32,
  h: {D.Cov(n, m, c, rs, xs) == True{} : Bool}, hw: N.Le(Nat.add(U32.to_nat(c), n), U32.to_nat(e))) ->
  N.Le(n, Nat.add(D.Stat(n, m, c), Nat.add(D.Rts.size(rs), List.length(&2, U32, xs)))):
  +hw2 = hw
  N.le_trans(n, Nat.add(D.Stat(n, m, c), Nat.add(Many(n, c, CP.nodes{rs, m}), Many(n, c, CP.mem{xs}))),
    Nat.add(D.Stat(n, m, c), Nat.add(D.Rts.size(rs), List.length(&2, U32, xs))), cov.many(n, m, c, rs, xs, h),
    N.add_mono(D.Stat(n, m, c), D.Stat(n, m, c), Nat.add(Many(n, c, CP.nodes{rs, m}), Many(n, c, CP.mem{xs})),
      Nat.add(D.Rts.size(rs), List.length(&2, U32, xs)), N.le_refl(D.Stat(n, m, c)),
      N.add_mono(Many(n, c, CP.nodes{rs, m}), D.Rts.size(rs), Many(n, c, CP.mem{xs}), List.length(&2, U32, xs),
        nodes.many(rs, m, n, c, e, hw2), mem.many(xs, n, c, e, hw2))))

# a <= b gives a - b = 0
def sub.le(a: Nat, b: Nat, h: N.Le(a, b)) -> {Nat.sub(a, b) == 0n : Nat}:
  match a b:
    case 0n _:
      {==}
    case 1n+q 0n:
      Empty.absurd({Nat.sub(1n+q, 0n) == 0n : Nat}, h)
    case 1n+q 1n+r:
      sub.le(q, r, h)

def len.app(A: List<&2, U32>, +B: List<&2, U32>) ->
  {List.length(&2, U32, List.append(&2, U32, A, B)) == Nat.add(List.length(&2, U32, A), List.length(&2, U32, B)) : Nat}:
  match A:
    case Nil{}:
      {==}
    case Con{_, +rest}:
      %len.app(rest, B) : {1n+List.length(&2, U32, List.append(&2, U32, rest, B)) == 1n+_ : Nat}
      {==}

def rts.size.app(X: List<&2, D.Rt>, +Y: List<&2, D.Rt>) ->
  {D.Rts.size(List.append(&2, D.Rt, X, Y)) == Nat.add(D.Rts.size(X), D.Rts.size(Y)) : Nat}:
  match X:
    case Nil{}:
      {==}
    case Con{D.Rt{_, +u}, +rest}:
      %Equal.sym(Nat, D.Rts.size(List.append(&2, D.Rt, rest, Y)), Nat.add(D.Rts.size(rest), D.Rts.size(Y)), rts.size.app(rest, Y)) :
        {Nat.add(Pg.Term.size(u), _) == Nat.add(Nat.add(Pg.Term.size(u), D.Rts.size(rest)), D.Rts.size(Y)) : Nat}
      Equal.sym(Nat, Nat.add(Nat.add(Pg.Term.size(u), D.Rts.size(rest)), D.Rts.size(Y)),
        Nat.add(Pg.Term.size(u), Nat.add(D.Rts.size(rest), D.Rts.size(Y))), N.add_assoc(Pg.Term.size(u), D.Rts.size(rest), D.Rts.size(Y)))

def tmp.cells.len(xs: List<&2, D.TmpE>) -> {List.length(&2, U32, D.Tmp.cells(xs)) == List.length(&2, D.TmpE, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{D.TmpE{_, _}, +rest}:
      %tmp.cells.len(rest) : {1n+List.length(&2, U32, D.Tmp.cells(rest)) == 1n+_ : Nat}
      {==}

def is.cons(xs: List<&2, U32>) -> Type:
  match xs:
    case Nil{}:
      Empty
    case Con{_, _}:
      Unit

# no zombie cell: no zombie
def rts.size.zero(zs: List<&2, D.Rt>, h: {D.Rt.cells(zs) == Nil{} : List<&2, U32>}) -> {D.Rts.size(zs) == 0n : Nat}:
  match zs:
    case Nil{}:
      {==}
    case Con{D.Rt{+c, +u}, +rest}:
      Empty.absurd({D.Rts.size(Con{D.Rt{c, u}, rest}) == 0n : Nat}, (%h : is.cons(_); Unit{}))

def need.arith(+R: Nat, +H: Nat, +F: Nat, +Lf: Nat, +Lx: Nat) ->
  {Nat.add(Nat.add(R, Nat.add(H, Nat.add(F, 0n))), Nat.add(Lf, Nat.add(Lx, 0n))) == Nat.add(R, Nat.add(H, Nat.add(F, Nat.add(Lf, Lx)))) : Nat}:
  %Equal.sym(Nat, Nat.add(F, 0n), F, N.add_zero(F)) :
    {Nat.add(Nat.add(R, Nat.add(H, _)), Nat.add(Lf, Nat.add(Lx, 0n))) == Nat.add(R, Nat.add(H, Nat.add(F, Nat.add(Lf, Lx)))) : Nat}
  %Equal.sym(Nat, Nat.add(Lx, 0n), Lx, N.add_zero(Lx)) :
    {Nat.add(Nat.add(R, Nat.add(H, F)), Nat.add(Lf, _)) == Nat.add(R, Nat.add(H, Nat.add(F, Nat.add(Lf, Lx)))) : Nat}
  Equal.trans(Nat, Nat.add(Nat.add(R, Nat.add(H, F)), Nat.add(Lf, Lx)), Nat.add(R, Nat.add(Nat.add(H, F), Nat.add(Lf, Lx))),
    Nat.add(R, Nat.add(H, Nat.add(F, Nat.add(Lf, Lx)))), N.add_assoc(R, Nat.add(H, F), Nat.add(Lf, Lx)),
    Equal.cong(Nat, Nat, w => Nat.add(R, w), Nat.add(Nat.add(H, F), Nat.add(Lf, Lx)), Nat.add(H, Nat.add(F, Nat.add(Lf, Lx))),
      N.add_assoc(H, F, Nat.add(Lf, Lx))))

def acc.count.eq(-RSs: Nat, -XSl: Nat, +R: Nat, +H: Nat, +F: Nat, -Z: Nat, +Lf: Nat, -Lc: Nat, +Lx: Nat,
  e1: {RSs == Nat.add(R, Nat.add(H, Nat.add(F, Z))) : Nat}, e2: {XSl == Nat.add(Lf, Nat.add(Lc, 0n)) : Nat},
  ez: {Z == 0n : Nat}, ec: {Lc == Lx : Nat}) -> {Nat.add(RSs, XSl) == Nat.add(R, Nat.add(H, Nat.add(F, Nat.add(Lf, Lx)))) : Nat}:
  %Equal.sym(Nat, RSs, Nat.add(R, Nat.add(H, Nat.add(F, Z))), e1) :
    {Nat.add(_, XSl) == Nat.add(R, Nat.add(H, Nat.add(F, Nat.add(Lf, Lx)))) : Nat}
  %Equal.sym(Nat, XSl, Nat.add(Lf, Nat.add(Lc, 0n)), e2) :
    {Nat.add(Nat.add(R, Nat.add(H, Nat.add(F, Z))), _) == Nat.add(R, Nat.add(H, Nat.add(F, Nat.add(Lf, Lx)))) : Nat}
  %Equal.sym(Nat, Z, 0n, ez) :
    {Nat.add(Nat.add(R, Nat.add(H, Nat.add(F, _))), Nat.add(Lf, Nat.add(Lc, 0n))) == Nat.add(R, Nat.add(H, Nat.add(F, Nat.add(Lf, Lx)))) : Nat}
  %Equal.sym(Nat, Lc, Lx, ec) :
    {Nat.add(Nat.add(R, Nat.add(H, Nat.add(F, 0n))), Nat.add(Lf, Nat.add(_, 0n))) == Nat.add(R, Nat.add(H, Nat.add(F, Nat.add(Lf, Lx)))) : Nat}
  need.arith(R, H, F, Lf, Lx)

# the own cells, from fi to nx, do not wrap; or there are none
def acc.count.cov(c: Cmp, +m: Cr.Cir.Cells, +fi: U32, +nx: U32, +RS: List<&2, D.Rt>, +XS: List<&2, U32>,
  r: N.Rel(c, U32.to_nat(fi), U32.to_nat(nx)),
  h: {D.Cov(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, RS, XS) == True{} : Bool}) ->
  N.Le(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)),
    Nat.add(D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi), Nat.add(D.Rts.size(RS), List.length(&2, U32, XS)))):
  match c:
    case LT{}:
      +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
      +le = N.weaken(U32.to_nat(fi), U32.to_nat(nx), r)
      cov.count(n, m, fi, RS, XS, nx, h,
        N.le_rw_l(U32.to_nat(nx), Nat.add(U32.to_nat(fi), n), U32.to_nat(nx),
          Equal.sym(Nat, Nat.add(U32.to_nat(fi), n), U32.to_nat(nx), D.add.sub(U32.to_nat(fi), U32.to_nat(nx), le)), N.le_refl(U32.to_nat(nx))))
    case EQ{}:
      +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
      +le = {(%r : N.Le(U32.to_nat(fi), _); N.le_refl(U32.to_nat(fi))) : N.Le(U32.to_nat(fi), U32.to_nat(nx))}
      cov.count(n, m, fi, RS, XS, nx, h,
        N.le_rw_l(U32.to_nat(nx), Nat.add(U32.to_nat(fi), n), U32.to_nat(nx),
          Equal.sym(Nat, Nat.add(U32.to_nat(fi), n), U32.to_nat(nx), D.add.sub(U32.to_nat(fi), U32.to_nat(nx), le)), N.le_refl(U32.to_nat(nx))))
    case GT{}:
      +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
      %Equal.sym(Nat, n, 0n, sub.le(U32.to_nat(nx), U32.to_nat(fi), N.weaken(U32.to_nat(nx), U32.to_nat(fi), r))) :
        N.Le(_, Nat.add(D.Stat(n, m, fi), Nat.add(D.Rts.size(RS), List.length(&2, U32, XS))))
      N.le_zero(Nat.add(D.Stat(n, m, fi), Nat.add(D.Rts.size(RS), List.length(&2, U32, XS))))

# with no pending cell (and so no zombie), the own cells are at most
# Acc.need: the STATIC ones, the nodes of the roots, of the temporaries'
# terms and of the frames' terms, the frames and the temporaries
def acc.count(+dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +rs: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +sp: U32,
  +fs: List<&2, D.AF>, +zs: List<&2, D.Rt>,
  h: D.AccK(dk, ds, ks, img, m, nx, fi, im, rs, xs, sp, fs, Nil{}, zs)) ->
  N.Le(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), D.Acc.need(m, nx, fi, rs, xs, sp, fs)):
  (_, r1) = h
  (_, r2) = r1
  (hzc, r3) = r2
  (hcov, _) = r3
  +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
  +cs = D.Tmp.cells(xs)
  +hl = D.Tmp.held(xs)
  +frt = D.Fr.rts(fs, m, sp)
  +frc = D.Fr.cells(fs, m, sp)
  +RS = List.append(&2, D.Rt, rs, List.append(&2, D.Rt, hl, List.append(&2, D.Rt, frt, zs)))
  +XS = List.append(&2, U32, frc, List.append(&2, U32, cs, Nil{}))
  +c1 = acc.count.cov(U32.cmp(fi, nx), m, fi, nx, RS, XS, N.U32.rel(fi, nx), hcov)
  +e1 = Equal.trans(Nat, D.Rts.size(RS), Nat.add(D.Rts.size(rs), D.Rts.size(List.append(&2, D.Rt, hl, List.append(&2, D.Rt, frt, zs)))),
    Nat.add(D.Rts.size(rs), Nat.add(D.Rts.size(hl), Nat.add(D.Rts.size(frt), D.Rts.size(zs)))),
    rts.size.app(rs, List.append(&2, D.Rt, hl, List.append(&2, D.Rt, frt, zs))),
    Equal.cong(Nat, Nat, w => Nat.add(D.Rts.size(rs), w), D.Rts.size(List.append(&2, D.Rt, hl, List.append(&2, D.Rt, frt, zs))),
      Nat.add(D.Rts.size(hl), Nat.add(D.Rts.size(frt), D.Rts.size(zs))),
      Equal.trans(Nat, D.Rts.size(List.append(&2, D.Rt, hl, List.append(&2, D.Rt, frt, zs))),
        Nat.add(D.Rts.size(hl), D.Rts.size(List.append(&2, D.Rt, frt, zs))), Nat.add(D.Rts.size(hl), Nat.add(D.Rts.size(frt), D.Rts.size(zs))),
        rts.size.app(hl, List.append(&2, D.Rt, frt, zs)),
        Equal.cong(Nat, Nat, w => Nat.add(D.Rts.size(hl), w), D.Rts.size(List.append(&2, D.Rt, frt, zs)),
          Nat.add(D.Rts.size(frt), D.Rts.size(zs)), rts.size.app(frt, zs)))))
  +e2 = Equal.trans(Nat, List.length(&2, U32, XS), Nat.add(List.length(&2, U32, frc), List.length(&2, U32, List.append(&2, U32, cs, Nil{}))),
    Nat.add(List.length(&2, U32, frc), Nat.add(List.length(&2, U32, cs), 0n)), len.app(frc, List.append(&2, U32, cs, Nil{})),
    Equal.cong(Nat, Nat, w => Nat.add(List.length(&2, U32, frc), w), List.length(&2, U32, List.append(&2, U32, cs, Nil{})),
      Nat.add(List.length(&2, U32, cs), 0n), len.app(cs, Nil{})))
  N.le_rw_r(n, Nat.add(D.Stat(n, m, fi), Nat.add(D.Rts.size(RS), List.length(&2, U32, XS))), D.Acc.need(m, nx, fi, rs, xs, sp, fs),
    Equal.cong(Nat, Nat, w => Nat.add(D.Stat(n, m, fi), w), Nat.add(D.Rts.size(RS), List.length(&2, U32, XS)),
      Nat.add(D.Rts.size(rs), Nat.add(D.Rts.size(hl), Nat.add(D.Rts.size(frt), Nat.add(List.length(&2, U32, frc), List.length(&2, D.TmpE, xs))))),
      acc.count.eq(D.Rts.size(RS), List.length(&2, U32, XS), D.Rts.size(rs), D.Rts.size(hl), D.Rts.size(frt), D.Rts.size(zs),
        List.length(&2, U32, frc), List.length(&2, U32, cs), List.length(&2, D.TmpE, xs), e1, e2, rts.size.zero(zs, hzc), tmp.cells.len(xs))),
    c1)

# The frames and the focus
# ------------------------

# a frame around v: its node, v, its term a and, for Rwt, its term b
def plug.size(kind: D.FK, +q: Bk.Quan, +k: Bool, +a: Bk.Term, +b: Bk.Term, +m: Cr.Cir.Cells, +fr: U32, +v: Bk.Term) ->
  {Pg.Term.size(D.A.plug(D.AF{kind, q, k, a, b}, v)) ==
    1n+Nat.add(Pg.Term.size(v), Nat.add(Pg.Term.size(a), D.Rts.size(D.Fr.rts.b(m, fr, kind, b)))) : Nat}:
  match kind:
    case D.FK.arg{}:
      %Equal.sym(Nat, Nat.add(Pg.Term.size(a), 0n), Pg.Term.size(a), N.add_zero(Pg.Term.size(a))) : {1n+Nat.add(Pg.Term.size(v), Pg.Term.size(a)) == 1n+Nat.add(Pg.Term.size(v), _) : Nat}
      {==}
    case D.FK.val{}:
      %Equal.sym(Nat, Nat.add(Pg.Term.size(a), 0n), Pg.Term.size(a), N.add_zero(Pg.Term.size(a))) : {1n+Nat.add(Pg.Term.size(v), Pg.Term.size(a)) == 1n+Nat.add(Pg.Term.size(v), _) : Nat}
      {==}
    case D.FK.fun{}:
      %Equal.sym(Nat, Nat.add(Pg.Term.size(a), 0n), Pg.Term.size(a), N.add_zero(Pg.Term.size(a))) : {1n+Nat.add(Pg.Term.size(a), Pg.Term.size(v)) == 1n+Nat.add(Pg.Term.size(v), _) : Nat}
      Equal.cong(Nat, Nat, w => 1n+w, Nat.add(Pg.Term.size(a), Pg.Term.size(v)), Nat.add(Pg.Term.size(v), Pg.Term.size(a)), add.comm(Pg.Term.size(a), Pg.Term.size(v)))
    case D.FK.let{}:
      %Equal.sym(Nat, Nat.add(Pg.Term.size(a), 0n), Pg.Term.size(a), N.add_zero(Pg.Term.size(a))) : {1n+Nat.add(Pg.Term.size(v), Pg.Term.size(a)) == 1n+Nat.add(Pg.Term.size(v), _) : Nat}
      {==}
    case D.FK.tupb{}:
      %Equal.sym(Nat, Nat.add(Pg.Term.size(a), 0n), Pg.Term.size(a), N.add_zero(Pg.Term.size(a))) : {1n+Nat.add(Pg.Term.size(v), Pg.Term.size(a)) == 1n+Nat.add(Pg.Term.size(v), _) : Nat}
      {==}
    case D.FK.tupa{}:
      %Equal.sym(Nat, Nat.add(Pg.Term.size(a), 0n), Pg.Term.size(a), N.add_zero(Pg.Term.size(a))) : {1n+Nat.add(Pg.Term.size(a), Pg.Term.size(v)) == 1n+Nat.add(Pg.Term.size(v), _) : Nat}
      Equal.cong(Nat, Nat, w => 1n+w, Nat.add(Pg.Term.size(a), Pg.Term.size(v)), Nat.add(Pg.Term.size(v), Pg.Term.size(a)), add.comm(Pg.Term.size(a), Pg.Term.size(v)))
    case D.FK.rwt{}:
      %Equal.sym(Nat, Nat.add(Pg.Term.size(b), 0n), Pg.Term.size(b), N.add_zero(Pg.Term.size(b))) :
        {1n+Nat.add(Pg.Term.size(v), Nat.add(Pg.Term.size(a), Pg.Term.size(b))) == 1n+Nat.add(Pg.Term.size(v), Nat.add(Pg.Term.size(a), _)) : Nat}
      {==}
    case D.FK.minb{}:
      %Equal.sym(Nat, Nat.add(Pg.Term.size(a), 0n), Pg.Term.size(a), N.add_zero(Pg.Term.size(a))) : {1n+Nat.add(Pg.Term.size(v), Pg.Term.size(a)) == 1n+Nat.add(Pg.Term.size(v), _) : Nat}
      {==}
    case D.FK.mina{}:
      %Equal.sym(Nat, Nat.add(Pg.Term.size(a), 0n), Pg.Term.size(a), N.add_zero(Pg.Term.size(a))) : {1n+Nat.add(Pg.Term.size(a), Pg.Term.size(v)) == 1n+Nat.add(Pg.Term.size(v), _) : Nat}
      Equal.cong(Nat, Nat, w => 1n+w, Nat.add(Pg.Term.size(a), Pg.Term.size(v)), Nat.add(Pg.Term.size(v), Pg.Term.size(a)), add.comm(Pg.Term.size(a), Pg.Term.size(v)))

def plugs.arith(+V: Nat, +A: Nat, +B: Nat, +R: Nat, +L: Nat) ->
  {Nat.add(1n+Nat.add(V, Nat.add(A, B)), Nat.add(R, L)) == Nat.add(V, Nat.add(Nat.add(A, Nat.add(B, R)), 1n+L)) : Nat}:
  +S4 = Nat.add(B, Nat.add(R, L))
  +S3 = Nat.add(A, S4)
  +C = Nat.add(V, S3)
  +e1 = Equal.trans(Nat, Nat.add(Nat.add(V, Nat.add(A, B)), Nat.add(R, L)), Nat.add(V, Nat.add(Nat.add(A, B), Nat.add(R, L))), C,
    N.add_assoc(V, Nat.add(A, B), Nat.add(R, L)),
    Equal.cong(Nat, Nat, w => Nat.add(V, w), Nat.add(Nat.add(A, B), Nat.add(R, L)), S3, N.add_assoc(A, B, Nat.add(R, L))))
  +inner = Equal.trans(Nat, Nat.add(Nat.add(B, R), 1n+L), Nat.add(B, Nat.add(R, 1n+L)), 1n+S4, N.add_assoc(B, R, 1n+L),
    Equal.trans(Nat, Nat.add(B, Nat.add(R, 1n+L)), Nat.add(B, 1n+Nat.add(R, L)), 1n+S4,
      Equal.cong(Nat, Nat, w => Nat.add(B, w), Nat.add(R, 1n+L), 1n+Nat.add(R, L), N.add_succ_r(R, L)),
      N.add_succ_r(B, Nat.add(R, L))))
  +ey = Equal.trans(Nat, Nat.add(Nat.add(A, Nat.add(B, R)), 1n+L), Nat.add(A, Nat.add(Nat.add(B, R), 1n+L)), 1n+S3,
    N.add_assoc(A, Nat.add(B, R), 1n+L),
    Equal.trans(Nat, Nat.add(A, Nat.add(Nat.add(B, R), 1n+L)), Nat.add(A, 1n+S4), 1n+S3,
      Equal.cong(Nat, Nat, w => Nat.add(A, w), Nat.add(Nat.add(B, R), 1n+L), 1n+S4, inner), N.add_succ_r(A, S4)))
  +e2 = Equal.trans(Nat, Nat.add(V, Nat.add(Nat.add(A, Nat.add(B, R)), 1n+L)), Nat.add(V, 1n+S3), 1n+C,
    Equal.cong(Nat, Nat, w => Nat.add(V, w), Nat.add(Nat.add(A, Nat.add(B, R)), 1n+L), 1n+S3, ey), N.add_succ_r(V, S3))
  Equal.trans(Nat, 1n+Nat.add(Nat.add(V, Nat.add(A, B)), Nat.add(R, L)), 1n+C, Nat.add(V, Nat.add(Nat.add(A, Nat.add(B, R)), 1n+L)),
    Equal.cong(Nat, Nat, w => 1n+w, Nat.add(Nat.add(V, Nat.add(A, B)), Nat.add(R, L)), C, e1),
    Equal.sym(Nat, Nat.add(V, Nat.add(Nat.add(A, Nat.add(B, R)), 1n+L)), 1n+C, e2))

# the term of a state has the nodes of its focus, of its frames' terms, and
# one for each frame
def plugs.size(fs: List<&2, D.AF>, +m: Cr.Cir.Cells, +fr: U32, +v: Bk.Term) ->
  {Pg.Term.size(D.A.plugs(fs, v)) ==
    Nat.add(Pg.Term.size(v), Nat.add(D.Rts.size(D.Fr.rts(fs, m, fr)), List.length(&2, U32, D.Fr.cells(fs, m, fr)))) : Nat}:
  match fs:
    case Nil{}:
      Equal.sym(Nat, Nat.add(Pg.Term.size(v), 0n), Pg.Term.size(v), N.add_zero(Pg.Term.size(v)))
    case Con{D.AF{+kind, +q, +k, +a, +b}, +rest}:
      +f1 = D.Fd(1n, m, fr)
      +V = Pg.Term.size(v)
      +A = Pg.Term.size(a)
      +Fb = D.Fr.rts.b(m, fr, kind, b)
      +Bb = D.Rts.size(Fb)
      +R = D.Rts.size(D.Fr.rts(rest, m, f1))
      +L = List.length(&2, U32, D.Fr.cells(rest, m, f1))
      +pl = D.A.plug(D.AF{kind, q, k, a, b}, v)
      +E = Nat.add(V, Nat.add(Nat.add(A, D.Rts.size(List.append(&2, D.Rt, Fb, D.Fr.rts(rest, m, f1)))), 1n+L))
      Equal.trans(Nat, Pg.Term.size(D.A.plugs(rest, pl)), Nat.add(Pg.Term.size(pl), Nat.add(R, L)), E,
        plugs.size(rest, m, f1, pl),
        Equal.trans(Nat, Nat.add(Pg.Term.size(pl), Nat.add(R, L)), Nat.add(1n+Nat.add(V, Nat.add(A, Bb)), Nat.add(R, L)), E,
          Equal.cong(Nat, Nat, w => Nat.add(w, Nat.add(R, L)), Pg.Term.size(pl), 1n+Nat.add(V, Nat.add(A, Bb)),
            plug.size(kind, q, k, a, b, m, fr, v)),
          Equal.trans(Nat, Nat.add(1n+Nat.add(V, Nat.add(A, Bb)), Nat.add(R, L)), Nat.add(V, Nat.add(Nat.add(A, Nat.add(Bb, R)), 1n+L)), E,
            plugs.arith(V, A, Bb, R, L),
            Equal.cong(Nat, Nat, w => Nat.add(V, Nat.add(Nat.add(A, w), 1n+L)), Nat.add(Bb, R),
              D.Rts.size(List.append(&2, D.Rt, Fb, D.Fr.rts(rest, m, f1))),
              Equal.sym(Nat, D.Rts.size(List.append(&2, D.Rt, Fb, D.Fr.rts(rest, m, f1))), Nat.add(Bb, R), rts.size.app(Fb, D.Fr.rts(rest, m, f1)))))))

# Cov's roots and cells are sets
# ------------------------------

# the nodes of A ++ B are those of A and of B
def nodes.app(A: List<&2, D.Rt>, +B: List<&2, D.Rt>, +m: Cr.Cir.Cells, +x: U32) ->
  {D.Nodes(List.append(&2, D.Rt, A, B), m, x) == Bool.or(D.Nodes(A, m, x), D.Nodes(B, m, x)) : Bool}:
  match A:
    case Nil{}:
      {==}
    case Con{D.Rt{+r, +u}, +rest}:
      %Equal.sym(Bool, D.Nodes(List.append(&2, D.Rt, rest, B), m, x), Bool.or(D.Nodes(rest, m, x), D.Nodes(B, m, x)), nodes.app(rest, B, m, x)) :
        {Bool.or(D.Node(u, m, r, x), _) == Bool.or(Bool.or(D.Node(u, m, r, x), D.Nodes(rest, m, x)), D.Nodes(B, m, x)) : Bool}
      Equal.sym(Bool, Bool.or(Bool.or(D.Node(u, m, r, x), D.Nodes(rest, m, x)), D.Nodes(B, m, x)),
        Bool.or(D.Node(u, m, r, x), Bool.or(D.Nodes(rest, m, x), D.Nodes(B, m, x))), or.assoc(D.Node(u, m, r, x), D.Nodes(rest, m, x), D.Nodes(B, m, x)))

# and the cells of A ++ B are those of A and of B
def mem.app(A: List<&2, U32>, +B: List<&2, U32>, +x: U32) ->
  {D.Mem(List.append(&2, U32, A, B), x) == Bool.or(D.Mem(A, x), D.Mem(B, x)) : Bool}:
  match A:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      %Equal.sym(Bool, D.Mem(List.append(&2, U32, rest, B), x), Bool.or(D.Mem(rest, x), D.Mem(B, x)), mem.app(rest, B, x)) :
        {Bool.or(U32.is_eq(y, x), _) == Bool.or(Bool.or(U32.is_eq(y, x), D.Mem(rest, x)), D.Mem(B, x)) : Bool}
      Equal.sym(Bool, Bool.or(Bool.or(U32.is_eq(y, x), D.Mem(rest, x)), D.Mem(B, x)),
        Bool.or(U32.is_eq(y, x), Bool.or(D.Mem(rest, x), D.Mem(B, x))), or.assoc(U32.is_eq(y, x), D.Mem(rest, x), D.Mem(B, x)))

def nodes.swap(+A: List<&2, D.Rt>, +B: List<&2, D.Rt>, +C: List<&2, D.Rt>, +m: Cr.Cir.Cells, +x: U32) ->
  {D.Nodes(List.append(&2, D.Rt, A, List.append(&2, D.Rt, B, C)), m, x) == D.Nodes(List.append(&2, D.Rt, B, List.append(&2, D.Rt, A, C)), m, x) : Bool}:
  +NA = D.Nodes(A, m, x)
  +NB = D.Nodes(B, m, x)
  +NC = D.Nodes(C, m, x)
  +X4 = D.Nodes(List.append(&2, D.Rt, B, List.append(&2, D.Rt, A, C)), m, x)
  Equal.trans(Bool, D.Nodes(List.append(&2, D.Rt, A, List.append(&2, D.Rt, B, C)), m, x), Bool.or(NA, D.Nodes(List.append(&2, D.Rt, B, C), m, x)), X4,
    nodes.app(A, List.append(&2, D.Rt, B, C), m, x),
    Equal.trans(Bool, Bool.or(NA, D.Nodes(List.append(&2, D.Rt, B, C), m, x)), Bool.or(NA, Bool.or(NB, NC)), X4,
      Equal.cong(Bool, Bool, w => Bool.or(NA, w), D.Nodes(List.append(&2, D.Rt, B, C), m, x), Bool.or(NB, NC), nodes.app(B, C, m, x)),
      Equal.trans(Bool, Bool.or(NA, Bool.or(NB, NC)), Bool.or(NB, Bool.or(NA, NC)), X4, or.swap(NA, NB, NC),
        Equal.trans(Bool, Bool.or(NB, Bool.or(NA, NC)), Bool.or(NB, D.Nodes(List.append(&2, D.Rt, A, C), m, x)), X4,
          Equal.cong(Bool, Bool, w => Bool.or(NB, w), Bool.or(NA, NC), D.Nodes(List.append(&2, D.Rt, A, C), m, x),
            Equal.sym(Bool, D.Nodes(List.append(&2, D.Rt, A, C), m, x), Bool.or(NA, NC), nodes.app(A, C, m, x))),
          Equal.sym(Bool, X4, Bool.or(NB, D.Nodes(List.append(&2, D.Rt, A, C), m, x)), nodes.app(B, List.append(&2, D.Rt, A, C), m, x))))))

def mem.swap(+A: List<&2, U32>, +B: List<&2, U32>, +C: List<&2, U32>, +x: U32) ->
  {D.Mem(List.append(&2, U32, A, List.append(&2, U32, B, C)), x) == D.Mem(List.append(&2, U32, B, List.append(&2, U32, A, C)), x) : Bool}:
  +NA = D.Mem(A, x)
  +NB = D.Mem(B, x)
  +NC = D.Mem(C, x)
  +X4 = D.Mem(List.append(&2, U32, B, List.append(&2, U32, A, C)), x)
  Equal.trans(Bool, D.Mem(List.append(&2, U32, A, List.append(&2, U32, B, C)), x), Bool.or(NA, D.Mem(List.append(&2, U32, B, C), x)), X4,
    mem.app(A, List.append(&2, U32, B, C), x),
    Equal.trans(Bool, Bool.or(NA, D.Mem(List.append(&2, U32, B, C), x)), Bool.or(NA, Bool.or(NB, NC)), X4,
      Equal.cong(Bool, Bool, w => Bool.or(NA, w), D.Mem(List.append(&2, U32, B, C), x), Bool.or(NB, NC), mem.app(B, C, x)),
      Equal.trans(Bool, Bool.or(NA, Bool.or(NB, NC)), Bool.or(NB, Bool.or(NA, NC)), X4, or.swap(NA, NB, NC),
        Equal.trans(Bool, Bool.or(NB, Bool.or(NA, NC)), Bool.or(NB, D.Mem(List.append(&2, U32, A, C), x)), X4,
          Equal.cong(Bool, Bool, w => Bool.or(NB, w), Bool.or(NA, NC), D.Mem(List.append(&2, U32, A, C), x),
            Equal.sym(Bool, D.Mem(List.append(&2, U32, A, C), x), Bool.or(NA, NC), mem.app(A, C, x))),
          Equal.sym(Bool, X4, Bool.or(NB, D.Mem(List.append(&2, U32, A, C), x)), mem.app(B, List.append(&2, U32, A, C), x))))))

def nodes.perm(P: List<&2, D.Rt>, +A: List<&2, D.Rt>, +B: List<&2, D.Rt>, +C: List<&2, D.Rt>, +m: Cr.Cir.Cells, +x: U32) ->
  {D.Nodes(List.append(&2, D.Rt, P, List.append(&2, D.Rt, A, List.append(&2, D.Rt, B, C))), m, x) ==
    D.Nodes(List.append(&2, D.Rt, P, List.append(&2, D.Rt, B, List.append(&2, D.Rt, A, C))), m, x) : Bool}:
  match P:
    case Nil{}:
      nodes.swap(A, B, C, m, x)
    case Con{D.Rt{+r, +u}, +rest}:
      %nodes.perm(rest, A, B, C, m, x) :
        {Bool.or(D.Node(u, m, r, x), D.Nodes(List.append(&2, D.Rt, rest, List.append(&2, D.Rt, A, List.append(&2, D.Rt, B, C))), m, x)) ==
          Bool.or(D.Node(u, m, r, x), _) : Bool}
      {==}

def mem.perm(P: List<&2, U32>, +A: List<&2, U32>, +B: List<&2, U32>, +C: List<&2, U32>, +x: U32) ->
  {D.Mem(List.append(&2, U32, P, List.append(&2, U32, A, List.append(&2, U32, B, C))), x) ==
    D.Mem(List.append(&2, U32, P, List.append(&2, U32, B, List.append(&2, U32, A, C))), x) : Bool}:
  match P:
    case Nil{}:
      mem.swap(A, B, C, x)
    case Con{+y, +rest}:
      %mem.perm(rest, A, B, C, x) :
        {Bool.or(U32.is_eq(y, x), D.Mem(List.append(&2, U32, rest, List.append(&2, U32, A, List.append(&2, U32, B, C))), x)) ==
          Bool.or(U32.is_eq(y, x), _) : Bool}
      {==}

def or.root(f: Bool, x: Bool, -nd: Bool, -mm: Bool, h: {Bool.or(f, Bool.or(nd, mm)) == True{} : Bool}) ->
  {Bool.or(f, Bool.or(Bool.or(x, nd), mm)) == True{} : Bool}:
  match f x:
    case True{} _:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      h

def or.cell(f: Bool, nd: Bool, x: Bool, -mm: Bool, h: {Bool.or(f, Bool.or(nd, mm)) == True{} : Bool}) ->
  {Bool.or(f, Bool.or(nd, Bool.or(x, mm))) == True{} : Bool}:
  match f nd x:
    case True{} _ _:
      {==}
    case False{} True{} _:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      h

def cov.root.go(n: Nat, +m: Cr.Cir.Cells, +c: U32, +r0: U32, +u: Bk.Term, +rs: List<&2, D.Rt>, +xs: List<&2, U32>,
  h: {D.Cov(n, m, c, rs, xs) == True{} : Bool}) -> {D.Cov(n, m, c, Con{D.Rt{r0, u}, rs}, xs) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+(+k):
      +h2 = h
      +T = Bool.or(D.Fl(m, c, 1024), Bool.or(D.Nodes(rs, m, c), D.Mem(xs, c)))
      D.and.i(Bool.or(D.Fl(m, c, 1024), Bool.or(Bool.or(D.Node(u, m, r0, c), D.Nodes(rs, m, c)), D.Mem(xs, c))),
        D.Cov(k, m, U32.inc(c), Con{D.Rt{r0, u}, rs}, xs),
        or.root(D.Fl(m, c, 1024), D.Node(u, m, r0, c), D.Nodes(rs, m, c), D.Mem(xs, c), D.and.l(T, D.Cov(k, m, U32.inc(c), rs, xs), h2)),
        cov.root.go(k, m, U32.inc(c), r0, u, rs, xs, D.and.r(T, D.Cov(k, m, U32.inc(c), rs, xs), h2)))

# two blocks A and B of the roots, after the roots P, trade places: Cov is
# the same
def cov.perm(n: Nat, +m: Cr.Cir.Cells, +c: U32, +P: List<&2, D.Rt>, +A: List<&2, D.Rt>, +B: List<&2, D.Rt>,
  +C: List<&2, D.Rt>, +xs: List<&2, U32>) ->
  {D.Cov(n, m, c, List.append(&2, D.Rt, P, List.append(&2, D.Rt, A, List.append(&2, D.Rt, B, C))), xs) ==
    D.Cov(n, m, c, List.append(&2, D.Rt, P, List.append(&2, D.Rt, B, List.append(&2, D.Rt, A, C))), xs) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+(+k):
      +R1 = List.append(&2, D.Rt, P, List.append(&2, D.Rt, A, List.append(&2, D.Rt, B, C)))
      +R2 = List.append(&2, D.Rt, P, List.append(&2, D.Rt, B, List.append(&2, D.Rt, A, C)))
      %nodes.perm(P, A, B, C, m, c) :
        {Bool.and(Bool.or(D.Fl(m, c, 1024), Bool.or(D.Nodes(R1, m, c), D.Mem(xs, c))), D.Cov(k, m, U32.inc(c), R1, xs)) ==
          Bool.and(Bool.or(D.Fl(m, c, 1024), Bool.or(_, D.Mem(xs, c))), D.Cov(k, m, U32.inc(c), R2, xs)) : Bool}
      %cov.perm(k, m, U32.inc(c), P, A, B, C, xs) :
        {Bool.and(Bool.or(D.Fl(m, c, 1024), Bool.or(D.Nodes(R1, m, c), D.Mem(xs, c))), D.Cov(k, m, U32.inc(c), R1, xs)) ==
          Bool.and(Bool.or(D.Fl(m, c, 1024), Bool.or(D.Nodes(R1, m, c), D.Mem(xs, c))), _) : Bool}
      {==}

# two blocks A and B of the cells, after the cells P, trade places: Cov is
# the same
def cov.perm.x(n: Nat, +m: Cr.Cir.Cells, +c: U32, +rs: List<&2, D.Rt>, +P: List<&2, U32>, +A: List<&2, U32>,
  +B: List<&2, U32>, +C: List<&2, U32>) ->
  {D.Cov(n, m, c, rs, List.append(&2, U32, P, List.append(&2, U32, A, List.append(&2, U32, B, C)))) ==
    D.Cov(n, m, c, rs, List.append(&2, U32, P, List.append(&2, U32, B, List.append(&2, U32, A, C)))) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+(+k):
      +X1 = List.append(&2, U32, P, List.append(&2, U32, A, List.append(&2, U32, B, C)))
      +X2 = List.append(&2, U32, P, List.append(&2, U32, B, List.append(&2, U32, A, C)))
      %mem.perm(P, A, B, C, c) :
        {Bool.and(Bool.or(D.Fl(m, c, 1024), Bool.or(D.Nodes(rs, m, c), D.Mem(X1, c))), D.Cov(k, m, U32.inc(c), rs, X1)) ==
          Bool.and(Bool.or(D.Fl(m, c, 1024), Bool.or(D.Nodes(rs, m, c), _)), D.Cov(k, m, U32.inc(c), rs, X2)) : Bool}
      %cov.perm.x(k, m, U32.inc(c), rs, P, A, B, C) :
        {Bool.and(Bool.or(D.Fl(m, c, 1024), Bool.or(D.Nodes(rs, m, c), D.Mem(X1, c))), D.Cov(k, m, U32.inc(c), rs, X1)) ==
          Bool.and(Bool.or(D.Fl(m, c, 1024), Bool.or(D.Nodes(rs, m, c), D.Mem(X1, c))), _) : Bool}
      {==}

# one more root keeps Cov
def cov.root(n: Nat, +m: Cr.Cir.Cells, +c: U32, +r: D.Rt, +rs: List<&2, D.Rt>, +xs: List<&2, U32>,
  h: {D.Cov(n, m, c, rs, xs) == True{} : Bool}) -> {D.Cov(n, m, c, Con{r, rs}, xs) == True{} : Bool}:
  match r:
    case D.Rt{+r0, +u}:
      cov.root.go(n, m, c, r0, u, rs, xs, h)

# one more cell keeps Cov
def cov.cell(n: Nat, +m: Cr.Cir.Cells, +c: U32, +x: U32, +rs: List<&2, D.Rt>, +xs: List<&2, U32>,
  h: {D.Cov(n, m, c, rs, xs) == True{} : Bool}) -> {D.Cov(n, m, c, rs, Con{x, xs}) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+(+k):
      +h2 = h
      +T = Bool.or(D.Fl(m, c, 1024), Bool.or(D.Nodes(rs, m, c), D.Mem(xs, c)))
      D.and.i(Bool.or(D.Fl(m, c, 1024), Bool.or(D.Nodes(rs, m, c), Bool.or(U32.is_eq(x, c), D.Mem(xs, c)))),
        D.Cov(k, m, U32.inc(c), rs, Con{x, xs}),
        or.cell(D.Fl(m, c, 1024), D.Nodes(rs, m, c), U32.is_eq(x, c), D.Mem(xs, c), D.and.l(T, D.Cov(k, m, U32.inc(c), rs, xs), h2)),
        cov.cell(k, m, U32.inc(c), x, rs, xs, D.and.r(T, D.Cov(k, m, U32.inc(c), rs, xs), h2)))

# Stores at a cell that is no node
# --------------------------------

def cell.ne.b(b: Bool, +r: U32, +z: U32, +im: U32, +fi: U32, +nx: U32, eb: {U32.is_eq(r, z) == b : Bool},
  hr: {Cr.Cir.is_cell(r, im, fi, nx) == True{} : Bool}, hz: {Cr.Cir.is_cell(z, im, fi, nx) == False{} : Bool}) -> {U32.is_eq(r, z) == False{} : Bool}:
  match b:
    case False{}:
      eb
    case True{}:
      D.bool.ft({U32.is_eq(r, z) == False{} : Bool}, Equal.trans(Bool, False{}, Cr.Cir.is_cell(r, im, fi, nx), True{},
        (%Equal.sym(U32, r, z, D.u32.eq(r, z, eb)) : {False{} == Cr.Cir.is_cell(_, im, fi, nx) : Bool}; Equal.sym(Bool, Cr.Cir.is_cell(z, im, fi, nx), False{}, hz)), hr))

# a cell is not one that is no cell
def cell.ne(+r: U32, +z: U32, +im: U32, +fi: U32, +nx: U32, hr: {Cr.Cir.is_cell(r, im, fi, nx) == True{} : Bool},
  hz: {Cr.Cir.is_cell(z, im, fi, nx) == False{} : Bool}) -> {U32.is_eq(r, z) == False{} : Bool}:
  cell.ne.b(U32.is_eq(r, z), r, z, im, fi, nx, {==}, hr, hz)

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
      +ner = D.or.f.l(U32.is_eq(r, z), Bool.or(D.Node(y, m, D.Fd(2n, m, r), z), D.Node(y2, m, D.Fd(3n, m, r), z)), hn2)
      +nrest = D.or.f.r(U32.is_eq(r, z), Bool.or(D.Node(y, m, D.Fd(2n, m, r), z), D.Node(y2, m, D.Fd(3n, m, r), z)), hn2)
      +hp0 = D.or.f.l(D.Node(y, m, D.Fd(2n, m, r), z), D.Node(y2, m, D.Fd(3n, m, r), z), nrest)
      +hq0 = D.or.f.r(D.Node(y, m, D.Fd(2n, m, r), z), D.Node(y2, m, D.Fd(3n, m, r), z), nrest)
      Equal.cong(Bool, Bool, w => Bool.or(U32.is_eq(r, x), w), Bool.or(D.Node(y, M2, D.Fd(2n, M2, r), x), D.Node(y2, M2, D.Fd(3n, M2, r), x)), Bool.or(D.Node(y, m, D.Fd(2n, m, r), x), D.Node(y2, m, D.Fd(3n, m, r), x)),
        or.cong2(D.Node(y, M2, D.Fd(2n, M2, r), x), D.Node(y, m, D.Fd(2n, m, r), x), D.Node(y2, M2, D.Fd(3n, M2, r), x), D.Node(y2, m, D.Fd(3n, m, r), x),
        Equal.trans(Bool, D.Node(y, M2, D.Fd(2n, M2, r), x), D.Node(y, M2, D.Fd(2n, m, r), x), D.Node(y, m, D.Fd(2n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(y, M2, w, x), D.Fd(2n, M2, r), D.Fd(2n, m, r),
            Equal.cong(Cr.Cir.Cell, U32, w => Cr.Cir.Cell.get(2n, w), Cr.Cir.Cells.get(M2, r), Cr.Cir.Cells.get(m, r), D.cl.go(m, r, z, xc, ner))),
          node.set(y, m, z, xc, D.Fd(2n, m, r), x, hp0)),
        Equal.trans(Bool, D.Node(y2, M2, D.Fd(3n, M2, r), x), D.Node(y2, M2, D.Fd(3n, m, r), x), D.Node(y2, m, D.Fd(3n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(y2, M2, w, x), D.Fd(3n, M2, r), D.Fd(3n, m, r),
            Equal.cong(Cr.Cir.Cell, U32, w => Cr.Cir.Cell.get(3n, w), Cr.Cir.Cells.get(M2, r), Cr.Cir.Cells.get(m, r), D.cl.go(m, r, z, xc, ner))),
          node.set(y2, m, z, xc, D.Fd(3n, m, r), x, hq0))))
    case Bk.Term.Let{+q, +v, +f}:
      +M2 = Cr.Cir.Cells.set(m, z, xc)
      +hn2 = hn
      +ner = D.or.f.l(U32.is_eq(r, z), Bool.or(D.Node(v, m, D.Fd(2n, m, r), z), D.Node(f, m, D.Fd(3n, m, r), z)), hn2)
      +nrest = D.or.f.r(U32.is_eq(r, z), Bool.or(D.Node(v, m, D.Fd(2n, m, r), z), D.Node(f, m, D.Fd(3n, m, r), z)), hn2)
      +hp0 = D.or.f.l(D.Node(v, m, D.Fd(2n, m, r), z), D.Node(f, m, D.Fd(3n, m, r), z), nrest)
      +hq0 = D.or.f.r(D.Node(v, m, D.Fd(2n, m, r), z), D.Node(f, m, D.Fd(3n, m, r), z), nrest)
      Equal.cong(Bool, Bool, w => Bool.or(U32.is_eq(r, x), w), Bool.or(D.Node(v, M2, D.Fd(2n, M2, r), x), D.Node(f, M2, D.Fd(3n, M2, r), x)), Bool.or(D.Node(v, m, D.Fd(2n, m, r), x), D.Node(f, m, D.Fd(3n, m, r), x)),
        or.cong2(D.Node(v, M2, D.Fd(2n, M2, r), x), D.Node(v, m, D.Fd(2n, m, r), x), D.Node(f, M2, D.Fd(3n, M2, r), x), D.Node(f, m, D.Fd(3n, m, r), x),
        Equal.trans(Bool, D.Node(v, M2, D.Fd(2n, M2, r), x), D.Node(v, M2, D.Fd(2n, m, r), x), D.Node(v, m, D.Fd(2n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(v, M2, w, x), D.Fd(2n, M2, r), D.Fd(2n, m, r),
            Equal.cong(Cr.Cir.Cell, U32, w => Cr.Cir.Cell.get(2n, w), Cr.Cir.Cells.get(M2, r), Cr.Cir.Cells.get(m, r), D.cl.go(m, r, z, xc, ner))),
          node.set(v, m, z, xc, D.Fd(2n, m, r), x, hp0)),
        Equal.trans(Bool, D.Node(f, M2, D.Fd(3n, M2, r), x), D.Node(f, M2, D.Fd(3n, m, r), x), D.Node(f, m, D.Fd(3n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(f, M2, w, x), D.Fd(3n, M2, r), D.Fd(3n, m, r),
            Equal.cong(Cr.Cir.Cell, U32, w => Cr.Cir.Cell.get(3n, w), Cr.Cir.Cells.get(M2, r), Cr.Cir.Cells.get(m, r), D.cl.go(m, r, z, xc, ner))),
          node.set(f, m, z, xc, D.Fd(3n, m, r), x, hq0))))
    case Bk.Term.Typ{+y}:
      +M2 = Cr.Cir.Cells.set(m, z, xc)
      +hn2 = hn
      +ner = D.or.f.l(U32.is_eq(r, z), D.Node(y, m, D.Fd(2n, m, r), z), hn2)
      +nrest = D.or.f.r(U32.is_eq(r, z), D.Node(y, m, D.Fd(2n, m, r), z), hn2)
      Equal.cong(Bool, Bool, w => Bool.or(U32.is_eq(r, x), w), D.Node(y, M2, D.Fd(2n, M2, r), x), D.Node(y, m, D.Fd(2n, m, r), x),
        Equal.trans(Bool, D.Node(y, M2, D.Fd(2n, M2, r), x), D.Node(y, M2, D.Fd(2n, m, r), x), D.Node(y, m, D.Fd(2n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(y, M2, w, x), D.Fd(2n, M2, r), D.Fd(2n, m, r),
            Equal.cong(Cr.Cir.Cell, U32, w => Cr.Cir.Cell.get(2n, w), Cr.Cir.Cells.get(M2, r), Cr.Cir.Cells.get(m, r), D.cl.go(m, r, z, xc, ner))),
          node.set(y, m, z, xc, D.Fd(2n, m, r), x, nrest)))
    case Bk.Term.Min{+a, +b}:
      +M2 = Cr.Cir.Cells.set(m, z, xc)
      +hn2 = hn
      +ner = D.or.f.l(U32.is_eq(r, z), Bool.or(D.Node(a, m, D.Fd(2n, m, r), z), D.Node(b, m, D.Fd(3n, m, r), z)), hn2)
      +nrest = D.or.f.r(U32.is_eq(r, z), Bool.or(D.Node(a, m, D.Fd(2n, m, r), z), D.Node(b, m, D.Fd(3n, m, r), z)), hn2)
      +hp0 = D.or.f.l(D.Node(a, m, D.Fd(2n, m, r), z), D.Node(b, m, D.Fd(3n, m, r), z), nrest)
      +hq0 = D.or.f.r(D.Node(a, m, D.Fd(2n, m, r), z), D.Node(b, m, D.Fd(3n, m, r), z), nrest)
      Equal.cong(Bool, Bool, w => Bool.or(U32.is_eq(r, x), w), Bool.or(D.Node(a, M2, D.Fd(2n, M2, r), x), D.Node(b, M2, D.Fd(3n, M2, r), x)), Bool.or(D.Node(a, m, D.Fd(2n, m, r), x), D.Node(b, m, D.Fd(3n, m, r), x)),
        or.cong2(D.Node(a, M2, D.Fd(2n, M2, r), x), D.Node(a, m, D.Fd(2n, m, r), x), D.Node(b, M2, D.Fd(3n, M2, r), x), D.Node(b, m, D.Fd(3n, m, r), x),
        Equal.trans(Bool, D.Node(a, M2, D.Fd(2n, M2, r), x), D.Node(a, M2, D.Fd(2n, m, r), x), D.Node(a, m, D.Fd(2n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(a, M2, w, x), D.Fd(2n, M2, r), D.Fd(2n, m, r),
            Equal.cong(Cr.Cir.Cell, U32, w => Cr.Cir.Cell.get(2n, w), Cr.Cir.Cells.get(M2, r), Cr.Cir.Cells.get(m, r), D.cl.go(m, r, z, xc, ner))),
          node.set(a, m, z, xc, D.Fd(2n, m, r), x, hp0)),
        Equal.trans(Bool, D.Node(b, M2, D.Fd(3n, M2, r), x), D.Node(b, M2, D.Fd(3n, m, r), x), D.Node(b, m, D.Fd(3n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(b, M2, w, x), D.Fd(3n, M2, r), D.Fd(3n, m, r),
            Equal.cong(Cr.Cir.Cell, U32, w => Cr.Cir.Cell.get(3n, w), Cr.Cir.Cells.get(M2, r), Cr.Cir.Cells.get(m, r), D.cl.go(m, r, z, xc, ner))),
          node.set(b, m, z, xc, D.Fd(3n, m, r), x, hq0))))
    case Bk.Term.All{+q, +a, +b}:
      +M2 = Cr.Cir.Cells.set(m, z, xc)
      +hn2 = hn
      +ner = D.or.f.l(U32.is_eq(r, z), Bool.or(D.Node(a, m, D.Fd(2n, m, r), z), D.Node(b, m, D.Fd(3n, m, r), z)), hn2)
      +nrest = D.or.f.r(U32.is_eq(r, z), Bool.or(D.Node(a, m, D.Fd(2n, m, r), z), D.Node(b, m, D.Fd(3n, m, r), z)), hn2)
      +hp0 = D.or.f.l(D.Node(a, m, D.Fd(2n, m, r), z), D.Node(b, m, D.Fd(3n, m, r), z), nrest)
      +hq0 = D.or.f.r(D.Node(a, m, D.Fd(2n, m, r), z), D.Node(b, m, D.Fd(3n, m, r), z), nrest)
      Equal.cong(Bool, Bool, w => Bool.or(U32.is_eq(r, x), w), Bool.or(D.Node(a, M2, D.Fd(2n, M2, r), x), D.Node(b, M2, D.Fd(3n, M2, r), x)), Bool.or(D.Node(a, m, D.Fd(2n, m, r), x), D.Node(b, m, D.Fd(3n, m, r), x)),
        or.cong2(D.Node(a, M2, D.Fd(2n, M2, r), x), D.Node(a, m, D.Fd(2n, m, r), x), D.Node(b, M2, D.Fd(3n, M2, r), x), D.Node(b, m, D.Fd(3n, m, r), x),
        Equal.trans(Bool, D.Node(a, M2, D.Fd(2n, M2, r), x), D.Node(a, M2, D.Fd(2n, m, r), x), D.Node(a, m, D.Fd(2n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(a, M2, w, x), D.Fd(2n, M2, r), D.Fd(2n, m, r),
            Equal.cong(Cr.Cir.Cell, U32, w => Cr.Cir.Cell.get(2n, w), Cr.Cir.Cells.get(M2, r), Cr.Cir.Cells.get(m, r), D.cl.go(m, r, z, xc, ner))),
          node.set(a, m, z, xc, D.Fd(2n, m, r), x, hp0)),
        Equal.trans(Bool, D.Node(b, M2, D.Fd(3n, M2, r), x), D.Node(b, M2, D.Fd(3n, m, r), x), D.Node(b, m, D.Fd(3n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(b, M2, w, x), D.Fd(3n, M2, r), D.Fd(3n, m, r),
            Equal.cong(Cr.Cir.Cell, U32, w => Cr.Cir.Cell.get(3n, w), Cr.Cir.Cells.get(M2, r), Cr.Cir.Cells.get(m, r), D.cl.go(m, r, z, xc, ner))),
          node.set(b, m, z, xc, D.Fd(3n, m, r), x, hq0))))
    case Bk.Term.Lam{+q, +f}:
      +M2 = Cr.Cir.Cells.set(m, z, xc)
      +hn2 = hn
      +ner = D.or.f.l(U32.is_eq(r, z), D.Node(f, m, D.Fd(2n, m, r), z), hn2)
      +nrest = D.or.f.r(U32.is_eq(r, z), D.Node(f, m, D.Fd(2n, m, r), z), hn2)
      Equal.cong(Bool, Bool, w => Bool.or(U32.is_eq(r, x), w), D.Node(f, M2, D.Fd(2n, M2, r), x), D.Node(f, m, D.Fd(2n, m, r), x),
        Equal.trans(Bool, D.Node(f, M2, D.Fd(2n, M2, r), x), D.Node(f, M2, D.Fd(2n, m, r), x), D.Node(f, m, D.Fd(2n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(f, M2, w, x), D.Fd(2n, M2, r), D.Fd(2n, m, r),
            Equal.cong(Cr.Cir.Cell, U32, w => Cr.Cir.Cell.get(2n, w), Cr.Cir.Cells.get(M2, r), Cr.Cir.Cells.get(m, r), D.cl.go(m, r, z, xc, ner))),
          node.set(f, m, z, xc, D.Fd(2n, m, r), x, nrest)))
    case Bk.Term.App{+q, +f, +y}:
      +M2 = Cr.Cir.Cells.set(m, z, xc)
      +hn2 = hn
      +ner = D.or.f.l(U32.is_eq(r, z), Bool.or(D.Node(f, m, D.Fd(2n, m, r), z), D.Node(y, m, D.Fd(3n, m, r), z)), hn2)
      +nrest = D.or.f.r(U32.is_eq(r, z), Bool.or(D.Node(f, m, D.Fd(2n, m, r), z), D.Node(y, m, D.Fd(3n, m, r), z)), hn2)
      +hp0 = D.or.f.l(D.Node(f, m, D.Fd(2n, m, r), z), D.Node(y, m, D.Fd(3n, m, r), z), nrest)
      +hq0 = D.or.f.r(D.Node(f, m, D.Fd(2n, m, r), z), D.Node(y, m, D.Fd(3n, m, r), z), nrest)
      Equal.cong(Bool, Bool, w => Bool.or(U32.is_eq(r, x), w), Bool.or(D.Node(f, M2, D.Fd(2n, M2, r), x), D.Node(y, M2, D.Fd(3n, M2, r), x)), Bool.or(D.Node(f, m, D.Fd(2n, m, r), x), D.Node(y, m, D.Fd(3n, m, r), x)),
        or.cong2(D.Node(f, M2, D.Fd(2n, M2, r), x), D.Node(f, m, D.Fd(2n, m, r), x), D.Node(y, M2, D.Fd(3n, M2, r), x), D.Node(y, m, D.Fd(3n, m, r), x),
        Equal.trans(Bool, D.Node(f, M2, D.Fd(2n, M2, r), x), D.Node(f, M2, D.Fd(2n, m, r), x), D.Node(f, m, D.Fd(2n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(f, M2, w, x), D.Fd(2n, M2, r), D.Fd(2n, m, r),
            Equal.cong(Cr.Cir.Cell, U32, w => Cr.Cir.Cell.get(2n, w), Cr.Cir.Cells.get(M2, r), Cr.Cir.Cells.get(m, r), D.cl.go(m, r, z, xc, ner))),
          node.set(f, m, z, xc, D.Fd(2n, m, r), x, hp0)),
        Equal.trans(Bool, D.Node(y, M2, D.Fd(3n, M2, r), x), D.Node(y, M2, D.Fd(3n, m, r), x), D.Node(y, m, D.Fd(3n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(y, M2, w, x), D.Fd(3n, M2, r), D.Fd(3n, m, r),
            Equal.cong(Cr.Cir.Cell, U32, w => Cr.Cir.Cell.get(3n, w), Cr.Cir.Cells.get(M2, r), Cr.Cir.Cells.get(m, r), D.cl.go(m, r, z, xc, ner))),
          node.set(y, m, z, xc, D.Fd(3n, m, r), x, hq0))))
    case Bk.Term.Sig{+q, +a, +b}:
      +M2 = Cr.Cir.Cells.set(m, z, xc)
      +hn2 = hn
      +ner = D.or.f.l(U32.is_eq(r, z), Bool.or(D.Node(a, m, D.Fd(2n, m, r), z), D.Node(b, m, D.Fd(3n, m, r), z)), hn2)
      +nrest = D.or.f.r(U32.is_eq(r, z), Bool.or(D.Node(a, m, D.Fd(2n, m, r), z), D.Node(b, m, D.Fd(3n, m, r), z)), hn2)
      +hp0 = D.or.f.l(D.Node(a, m, D.Fd(2n, m, r), z), D.Node(b, m, D.Fd(3n, m, r), z), nrest)
      +hq0 = D.or.f.r(D.Node(a, m, D.Fd(2n, m, r), z), D.Node(b, m, D.Fd(3n, m, r), z), nrest)
      Equal.cong(Bool, Bool, w => Bool.or(U32.is_eq(r, x), w), Bool.or(D.Node(a, M2, D.Fd(2n, M2, r), x), D.Node(b, M2, D.Fd(3n, M2, r), x)), Bool.or(D.Node(a, m, D.Fd(2n, m, r), x), D.Node(b, m, D.Fd(3n, m, r), x)),
        or.cong2(D.Node(a, M2, D.Fd(2n, M2, r), x), D.Node(a, m, D.Fd(2n, m, r), x), D.Node(b, M2, D.Fd(3n, M2, r), x), D.Node(b, m, D.Fd(3n, m, r), x),
        Equal.trans(Bool, D.Node(a, M2, D.Fd(2n, M2, r), x), D.Node(a, M2, D.Fd(2n, m, r), x), D.Node(a, m, D.Fd(2n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(a, M2, w, x), D.Fd(2n, M2, r), D.Fd(2n, m, r),
            Equal.cong(Cr.Cir.Cell, U32, w => Cr.Cir.Cell.get(2n, w), Cr.Cir.Cells.get(M2, r), Cr.Cir.Cells.get(m, r), D.cl.go(m, r, z, xc, ner))),
          node.set(a, m, z, xc, D.Fd(2n, m, r), x, hp0)),
        Equal.trans(Bool, D.Node(b, M2, D.Fd(3n, M2, r), x), D.Node(b, M2, D.Fd(3n, m, r), x), D.Node(b, m, D.Fd(3n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(b, M2, w, x), D.Fd(3n, M2, r), D.Fd(3n, m, r),
            Equal.cong(Cr.Cir.Cell, U32, w => Cr.Cir.Cell.get(3n, w), Cr.Cir.Cells.get(M2, r), Cr.Cir.Cells.get(m, r), D.cl.go(m, r, z, xc, ner))),
          node.set(b, m, z, xc, D.Fd(3n, m, r), x, hq0))))
    case Bk.Term.Tup{+q, +a, +b}:
      +M2 = Cr.Cir.Cells.set(m, z, xc)
      +hn2 = hn
      +ner = D.or.f.l(U32.is_eq(r, z), Bool.or(D.Node(a, m, D.Fd(2n, m, r), z), D.Node(b, m, D.Fd(3n, m, r), z)), hn2)
      +nrest = D.or.f.r(U32.is_eq(r, z), Bool.or(D.Node(a, m, D.Fd(2n, m, r), z), D.Node(b, m, D.Fd(3n, m, r), z)), hn2)
      +hp0 = D.or.f.l(D.Node(a, m, D.Fd(2n, m, r), z), D.Node(b, m, D.Fd(3n, m, r), z), nrest)
      +hq0 = D.or.f.r(D.Node(a, m, D.Fd(2n, m, r), z), D.Node(b, m, D.Fd(3n, m, r), z), nrest)
      Equal.cong(Bool, Bool, w => Bool.or(U32.is_eq(r, x), w), Bool.or(D.Node(a, M2, D.Fd(2n, M2, r), x), D.Node(b, M2, D.Fd(3n, M2, r), x)), Bool.or(D.Node(a, m, D.Fd(2n, m, r), x), D.Node(b, m, D.Fd(3n, m, r), x)),
        or.cong2(D.Node(a, M2, D.Fd(2n, M2, r), x), D.Node(a, m, D.Fd(2n, m, r), x), D.Node(b, M2, D.Fd(3n, M2, r), x), D.Node(b, m, D.Fd(3n, m, r), x),
        Equal.trans(Bool, D.Node(a, M2, D.Fd(2n, M2, r), x), D.Node(a, M2, D.Fd(2n, m, r), x), D.Node(a, m, D.Fd(2n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(a, M2, w, x), D.Fd(2n, M2, r), D.Fd(2n, m, r),
            Equal.cong(Cr.Cir.Cell, U32, w => Cr.Cir.Cell.get(2n, w), Cr.Cir.Cells.get(M2, r), Cr.Cir.Cells.get(m, r), D.cl.go(m, r, z, xc, ner))),
          node.set(a, m, z, xc, D.Fd(2n, m, r), x, hp0)),
        Equal.trans(Bool, D.Node(b, M2, D.Fd(3n, M2, r), x), D.Node(b, M2, D.Fd(3n, m, r), x), D.Node(b, m, D.Fd(3n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(b, M2, w, x), D.Fd(3n, M2, r), D.Fd(3n, m, r),
            Equal.cong(Cr.Cir.Cell, U32, w => Cr.Cir.Cell.get(3n, w), Cr.Cir.Cells.get(M2, r), Cr.Cir.Cells.get(m, r), D.cl.go(m, r, z, xc, ner))),
          node.set(b, m, z, xc, D.Fd(3n, m, r), x, hq0))))
    case Bk.Term.Prj{+h}:
      +M2 = Cr.Cir.Cells.set(m, z, xc)
      +hn2 = hn
      +ner = D.or.f.l(U32.is_eq(r, z), D.Node(h, m, D.Fd(2n, m, r), z), hn2)
      +nrest = D.or.f.r(U32.is_eq(r, z), D.Node(h, m, D.Fd(2n, m, r), z), hn2)
      Equal.cong(Bool, Bool, w => Bool.or(U32.is_eq(r, x), w), D.Node(h, M2, D.Fd(2n, M2, r), x), D.Node(h, m, D.Fd(2n, m, r), x),
        Equal.trans(Bool, D.Node(h, M2, D.Fd(2n, M2, r), x), D.Node(h, M2, D.Fd(2n, m, r), x), D.Node(h, m, D.Fd(2n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(h, M2, w, x), D.Fd(2n, M2, r), D.Fd(2n, m, r),
            Equal.cong(Cr.Cir.Cell, U32, w => Cr.Cir.Cell.get(2n, w), Cr.Cir.Cells.get(M2, r), Cr.Cir.Cells.get(m, r), D.cl.go(m, r, z, xc, ner))),
          node.set(h, m, z, xc, D.Fd(2n, m, r), x, nrest)))
    case Bk.Term.Enu{+e}:
      {==}
    case Bk.Term.Lab{+k}:
      {==}
    case Bk.Term.Mat{+k, +h, +o}:
      +M2 = Cr.Cir.Cells.set(m, z, xc)
      +hn2 = hn
      +ner = D.or.f.l(U32.is_eq(r, z), Bool.or(D.Node(h, m, D.Fd(3n, m, r), z), D.Node(o, m, D.Fd(4n, m, r), z)), hn2)
      +nrest = D.or.f.r(U32.is_eq(r, z), Bool.or(D.Node(h, m, D.Fd(3n, m, r), z), D.Node(o, m, D.Fd(4n, m, r), z)), hn2)
      +hp0 = D.or.f.l(D.Node(h, m, D.Fd(3n, m, r), z), D.Node(o, m, D.Fd(4n, m, r), z), nrest)
      +hq0 = D.or.f.r(D.Node(h, m, D.Fd(3n, m, r), z), D.Node(o, m, D.Fd(4n, m, r), z), nrest)
      Equal.cong(Bool, Bool, w => Bool.or(U32.is_eq(r, x), w), Bool.or(D.Node(h, M2, D.Fd(3n, M2, r), x), D.Node(o, M2, D.Fd(4n, M2, r), x)), Bool.or(D.Node(h, m, D.Fd(3n, m, r), x), D.Node(o, m, D.Fd(4n, m, r), x)),
        or.cong2(D.Node(h, M2, D.Fd(3n, M2, r), x), D.Node(h, m, D.Fd(3n, m, r), x), D.Node(o, M2, D.Fd(4n, M2, r), x), D.Node(o, m, D.Fd(4n, m, r), x),
        Equal.trans(Bool, D.Node(h, M2, D.Fd(3n, M2, r), x), D.Node(h, M2, D.Fd(3n, m, r), x), D.Node(h, m, D.Fd(3n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(h, M2, w, x), D.Fd(3n, M2, r), D.Fd(3n, m, r),
            Equal.cong(Cr.Cir.Cell, U32, w => Cr.Cir.Cell.get(3n, w), Cr.Cir.Cells.get(M2, r), Cr.Cir.Cells.get(m, r), D.cl.go(m, r, z, xc, ner))),
          node.set(h, m, z, xc, D.Fd(3n, m, r), x, hp0)),
        Equal.trans(Bool, D.Node(o, M2, D.Fd(4n, M2, r), x), D.Node(o, M2, D.Fd(4n, m, r), x), D.Node(o, m, D.Fd(4n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(o, M2, w, x), D.Fd(4n, M2, r), D.Fd(4n, m, r),
            Equal.cong(Cr.Cir.Cell, U32, w => Cr.Cir.Cell.get(4n, w), Cr.Cir.Cells.get(M2, r), Cr.Cir.Cells.get(m, r), D.cl.go(m, r, z, xc, ner))),
          node.set(o, m, z, xc, D.Fd(4n, m, r), x, hq0))))
    case Bk.Term.Efq{}:
      {==}
    case Bk.Term.Eql{+a, +b, +y}:
      +M2 = Cr.Cir.Cells.set(m, z, xc)
      +hn2 = hn
      +ner = D.or.f.l(U32.is_eq(r, z), Bool.or(D.Node(a, m, D.Fd(2n, m, r), z), Bool.or(D.Node(b, m, D.Fd(3n, m, r), z), D.Node(y, m, D.Fd(4n, m, r), z))), hn2)
      +nrest = D.or.f.r(U32.is_eq(r, z), Bool.or(D.Node(a, m, D.Fd(2n, m, r), z), Bool.or(D.Node(b, m, D.Fd(3n, m, r), z), D.Node(y, m, D.Fd(4n, m, r), z))), hn2)
      +hp0 = D.or.f.l(D.Node(a, m, D.Fd(2n, m, r), z), Bool.or(D.Node(b, m, D.Fd(3n, m, r), z), D.Node(y, m, D.Fd(4n, m, r), z)), nrest)
      +hq0 = D.or.f.r(D.Node(a, m, D.Fd(2n, m, r), z), Bool.or(D.Node(b, m, D.Fd(3n, m, r), z), D.Node(y, m, D.Fd(4n, m, r), z)), nrest)
      +hp1 = D.or.f.l(D.Node(b, m, D.Fd(3n, m, r), z), D.Node(y, m, D.Fd(4n, m, r), z), hq0)
      +hq1 = D.or.f.r(D.Node(b, m, D.Fd(3n, m, r), z), D.Node(y, m, D.Fd(4n, m, r), z), hq0)
      Equal.cong(Bool, Bool, w => Bool.or(U32.is_eq(r, x), w), Bool.or(D.Node(a, M2, D.Fd(2n, M2, r), x), Bool.or(D.Node(b, M2, D.Fd(3n, M2, r), x), D.Node(y, M2, D.Fd(4n, M2, r), x))), Bool.or(D.Node(a, m, D.Fd(2n, m, r), x), Bool.or(D.Node(b, m, D.Fd(3n, m, r), x), D.Node(y, m, D.Fd(4n, m, r), x))),
        or.cong2(D.Node(a, M2, D.Fd(2n, M2, r), x), D.Node(a, m, D.Fd(2n, m, r), x), Bool.or(D.Node(b, M2, D.Fd(3n, M2, r), x), D.Node(y, M2, D.Fd(4n, M2, r), x)), Bool.or(D.Node(b, m, D.Fd(3n, m, r), x), D.Node(y, m, D.Fd(4n, m, r), x)),
        Equal.trans(Bool, D.Node(a, M2, D.Fd(2n, M2, r), x), D.Node(a, M2, D.Fd(2n, m, r), x), D.Node(a, m, D.Fd(2n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(a, M2, w, x), D.Fd(2n, M2, r), D.Fd(2n, m, r),
            Equal.cong(Cr.Cir.Cell, U32, w => Cr.Cir.Cell.get(2n, w), Cr.Cir.Cells.get(M2, r), Cr.Cir.Cells.get(m, r), D.cl.go(m, r, z, xc, ner))),
          node.set(a, m, z, xc, D.Fd(2n, m, r), x, hp0)),
        or.cong2(D.Node(b, M2, D.Fd(3n, M2, r), x), D.Node(b, m, D.Fd(3n, m, r), x), D.Node(y, M2, D.Fd(4n, M2, r), x), D.Node(y, m, D.Fd(4n, m, r), x),
        Equal.trans(Bool, D.Node(b, M2, D.Fd(3n, M2, r), x), D.Node(b, M2, D.Fd(3n, m, r), x), D.Node(b, m, D.Fd(3n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(b, M2, w, x), D.Fd(3n, M2, r), D.Fd(3n, m, r),
            Equal.cong(Cr.Cir.Cell, U32, w => Cr.Cir.Cell.get(3n, w), Cr.Cir.Cells.get(M2, r), Cr.Cir.Cells.get(m, r), D.cl.go(m, r, z, xc, ner))),
          node.set(b, m, z, xc, D.Fd(3n, m, r), x, hp1)),
        Equal.trans(Bool, D.Node(y, M2, D.Fd(4n, M2, r), x), D.Node(y, M2, D.Fd(4n, m, r), x), D.Node(y, m, D.Fd(4n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(y, M2, w, x), D.Fd(4n, M2, r), D.Fd(4n, m, r),
            Equal.cong(Cr.Cir.Cell, U32, w => Cr.Cir.Cell.get(4n, w), Cr.Cir.Cells.get(M2, r), Cr.Cir.Cells.get(m, r), D.cl.go(m, r, z, xc, ner))),
          node.set(y, m, z, xc, D.Fd(4n, m, r), x, hq1)))))
    case Bk.Term.Rfl{}:
      {==}
    case Bk.Term.Rwt{+e, +p, +f}:
      +M2 = Cr.Cir.Cells.set(m, z, xc)
      +hn2 = hn
      +ner = D.or.f.l(U32.is_eq(r, z), Bool.or(D.Node(e, m, D.Fd(2n, m, r), z), Bool.or(D.Node(p, m, D.Fd(3n, m, r), z), D.Node(f, m, D.Fd(4n, m, r), z))), hn2)
      +nrest = D.or.f.r(U32.is_eq(r, z), Bool.or(D.Node(e, m, D.Fd(2n, m, r), z), Bool.or(D.Node(p, m, D.Fd(3n, m, r), z), D.Node(f, m, D.Fd(4n, m, r), z))), hn2)
      +hp0 = D.or.f.l(D.Node(e, m, D.Fd(2n, m, r), z), Bool.or(D.Node(p, m, D.Fd(3n, m, r), z), D.Node(f, m, D.Fd(4n, m, r), z)), nrest)
      +hq0 = D.or.f.r(D.Node(e, m, D.Fd(2n, m, r), z), Bool.or(D.Node(p, m, D.Fd(3n, m, r), z), D.Node(f, m, D.Fd(4n, m, r), z)), nrest)
      +hp1 = D.or.f.l(D.Node(p, m, D.Fd(3n, m, r), z), D.Node(f, m, D.Fd(4n, m, r), z), hq0)
      +hq1 = D.or.f.r(D.Node(p, m, D.Fd(3n, m, r), z), D.Node(f, m, D.Fd(4n, m, r), z), hq0)
      Equal.cong(Bool, Bool, w => Bool.or(U32.is_eq(r, x), w), Bool.or(D.Node(e, M2, D.Fd(2n, M2, r), x), Bool.or(D.Node(p, M2, D.Fd(3n, M2, r), x), D.Node(f, M2, D.Fd(4n, M2, r), x))), Bool.or(D.Node(e, m, D.Fd(2n, m, r), x), Bool.or(D.Node(p, m, D.Fd(3n, m, r), x), D.Node(f, m, D.Fd(4n, m, r), x))),
        or.cong2(D.Node(e, M2, D.Fd(2n, M2, r), x), D.Node(e, m, D.Fd(2n, m, r), x), Bool.or(D.Node(p, M2, D.Fd(3n, M2, r), x), D.Node(f, M2, D.Fd(4n, M2, r), x)), Bool.or(D.Node(p, m, D.Fd(3n, m, r), x), D.Node(f, m, D.Fd(4n, m, r), x)),
        Equal.trans(Bool, D.Node(e, M2, D.Fd(2n, M2, r), x), D.Node(e, M2, D.Fd(2n, m, r), x), D.Node(e, m, D.Fd(2n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(e, M2, w, x), D.Fd(2n, M2, r), D.Fd(2n, m, r),
            Equal.cong(Cr.Cir.Cell, U32, w => Cr.Cir.Cell.get(2n, w), Cr.Cir.Cells.get(M2, r), Cr.Cir.Cells.get(m, r), D.cl.go(m, r, z, xc, ner))),
          node.set(e, m, z, xc, D.Fd(2n, m, r), x, hp0)),
        or.cong2(D.Node(p, M2, D.Fd(3n, M2, r), x), D.Node(p, m, D.Fd(3n, m, r), x), D.Node(f, M2, D.Fd(4n, M2, r), x), D.Node(f, m, D.Fd(4n, m, r), x),
        Equal.trans(Bool, D.Node(p, M2, D.Fd(3n, M2, r), x), D.Node(p, M2, D.Fd(3n, m, r), x), D.Node(p, m, D.Fd(3n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(p, M2, w, x), D.Fd(3n, M2, r), D.Fd(3n, m, r),
            Equal.cong(Cr.Cir.Cell, U32, w => Cr.Cir.Cell.get(3n, w), Cr.Cir.Cells.get(M2, r), Cr.Cir.Cells.get(m, r), D.cl.go(m, r, z, xc, ner))),
          node.set(p, m, z, xc, D.Fd(3n, m, r), x, hp1)),
        Equal.trans(Bool, D.Node(f, M2, D.Fd(4n, M2, r), x), D.Node(f, M2, D.Fd(4n, m, r), x), D.Node(f, m, D.Fd(4n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(f, M2, w, x), D.Fd(4n, M2, r), D.Fd(4n, m, r),
            Equal.cong(Cr.Cir.Cell, U32, w => Cr.Cir.Cell.get(4n, w), Cr.Cir.Cells.get(M2, r), Cr.Cir.Cells.get(m, r), D.cl.go(m, r, z, xc, ner))),
          node.set(f, m, z, xc, D.Fd(4n, m, r), x, hq1)))))

# a cell that is no cell (Cir.is_cell) is no node of a term that IsK says
def node.notcell(t: Bk.Term, +dk: Bool, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +r: U32, +z: U32, hk: D.IsK(dk, ds, m, im, fi, nx, ks, img, r, t),
  hz: {Cr.Cir.is_cell(z, im, fi, nx) == False{} : Bool}) -> {D.Node(t, m, r, z) == False{} : Bool}:
  match t:
    case Bk.Term.Var{+i}:
      match hk:
        case Tuple{Tuple{hcell, _}, _}:
          cell.ne(r, z, im, fi, nx, hcell, hz)
    case Bk.Term.Ref{+k}:
      match hk:
        case Tuple{Tuple{hcell, _}, _}:
          cell.ne(r, z, im, fi, nx, hcell, hz)
    case Bk.Term.Ann{+y, +y2}:
      match hk:
        case Tuple{Tuple{hcell, _}, Tuple{Tuple{_, h1}, Tuple{_, h2}}}:
          +hz2 = hz
          +ne = cell.ne(r, z, im, fi, nx, hcell, hz2)
          %Equal.sym(Bool, U32.is_eq(r, z), False{}, ne) : {Bool.or(_, Bool.or(D.Node(y, m, D.Fd(2n, m, r), z), D.Node(y2, m, D.Fd(3n, m, r), z))) == False{} : Bool}
          %Equal.sym(Bool, D.Node(y, m, D.Fd(2n, m, r), z), False{}, node.notcell(y, dk, ds, m, im, fi, nx, ks, img, D.Fd(2n, m, r), z, h1, hz2)) : {Bool.or(False{}, Bool.or(_, D.Node(y2, m, D.Fd(3n, m, r), z))) == False{} : Bool}
          %Equal.sym(Bool, D.Node(y2, m, D.Fd(3n, m, r), z), False{}, node.notcell(y2, dk, ds, m, im, fi, nx, ks, img, D.Fd(3n, m, r), z, h2, hz2)) : {Bool.or(False{}, Bool.or(False{}, _)) == False{} : Bool}
          {==}
    case Bk.Term.Let{+q, +v, +f}:
      match hk:
        case Tuple{Tuple{hcell, _}, Tuple{_, Tuple{Tuple{_, h1}, Tuple{_, h2}}}}:
          +hz2 = hz
          +ne = cell.ne(r, z, im, fi, nx, hcell, hz2)
          %Equal.sym(Bool, U32.is_eq(r, z), False{}, ne) : {Bool.or(_, Bool.or(D.Node(v, m, D.Fd(2n, m, r), z), D.Node(f, m, D.Fd(3n, m, r), z))) == False{} : Bool}
          %Equal.sym(Bool, D.Node(v, m, D.Fd(2n, m, r), z), False{}, node.notcell(v, dk, ds, m, im, fi, nx, ks, img, D.Fd(2n, m, r), z, h1, hz2)) : {Bool.or(False{}, Bool.or(_, D.Node(f, m, D.Fd(3n, m, r), z))) == False{} : Bool}
          %Equal.sym(Bool, D.Node(f, m, D.Fd(3n, m, r), z), False{}, node.notcell(f, dk, ds, m, im, fi, nx, ks, img, D.Fd(3n, m, r), z, h2, hz2)) : {Bool.or(False{}, Bool.or(False{}, _)) == False{} : Bool}
          {==}
    case Bk.Term.Typ{+y}:
      match hk:
        case Tuple{Tuple{hcell, _}, Tuple{_, h1}}:
          +hz2 = hz
          +ne = cell.ne(r, z, im, fi, nx, hcell, hz2)
          %Equal.sym(Bool, U32.is_eq(r, z), False{}, ne) : {Bool.or(_, D.Node(y, m, D.Fd(2n, m, r), z)) == False{} : Bool}
          %Equal.sym(Bool, D.Node(y, m, D.Fd(2n, m, r), z), False{}, node.notcell(y, dk, ds, m, im, fi, nx, ks, img, D.Fd(2n, m, r), z, h1, hz2)) : {Bool.or(False{}, _) == False{} : Bool}
          {==}
    case Bk.Term.Min{+a, +b}:
      match hk:
        case Tuple{Tuple{hcell, _}, Tuple{Tuple{_, h1}, Tuple{_, h2}}}:
          +hz2 = hz
          +ne = cell.ne(r, z, im, fi, nx, hcell, hz2)
          %Equal.sym(Bool, U32.is_eq(r, z), False{}, ne) : {Bool.or(_, Bool.or(D.Node(a, m, D.Fd(2n, m, r), z), D.Node(b, m, D.Fd(3n, m, r), z))) == False{} : Bool}
          %Equal.sym(Bool, D.Node(a, m, D.Fd(2n, m, r), z), False{}, node.notcell(a, dk, ds, m, im, fi, nx, ks, img, D.Fd(2n, m, r), z, h1, hz2)) : {Bool.or(False{}, Bool.or(_, D.Node(b, m, D.Fd(3n, m, r), z))) == False{} : Bool}
          %Equal.sym(Bool, D.Node(b, m, D.Fd(3n, m, r), z), False{}, node.notcell(b, dk, ds, m, im, fi, nx, ks, img, D.Fd(3n, m, r), z, h2, hz2)) : {Bool.or(False{}, Bool.or(False{}, _)) == False{} : Bool}
          {==}
    case Bk.Term.All{+q, +a, +b}:
      match hk:
        case Tuple{Tuple{hcell, _}, Tuple{_, Tuple{Tuple{_, h1}, Tuple{_, h2}}}}:
          +hz2 = hz
          +ne = cell.ne(r, z, im, fi, nx, hcell, hz2)
          %Equal.sym(Bool, U32.is_eq(r, z), False{}, ne) : {Bool.or(_, Bool.or(D.Node(a, m, D.Fd(2n, m, r), z), D.Node(b, m, D.Fd(3n, m, r), z))) == False{} : Bool}
          %Equal.sym(Bool, D.Node(a, m, D.Fd(2n, m, r), z), False{}, node.notcell(a, dk, ds, m, im, fi, nx, ks, img, D.Fd(2n, m, r), z, h1, hz2)) : {Bool.or(False{}, Bool.or(_, D.Node(b, m, D.Fd(3n, m, r), z))) == False{} : Bool}
          %Equal.sym(Bool, D.Node(b, m, D.Fd(3n, m, r), z), False{}, node.notcell(b, dk, ds, m, im, fi, nx, ks, img, D.Fd(3n, m, r), z, h2, hz2)) : {Bool.or(False{}, Bool.or(False{}, _)) == False{} : Bool}
          {==}
    case Bk.Term.Lam{+q, +f}:
      match hk:
        case Tuple{Tuple{hcell, _}, Tuple{_, Tuple{_, h1}}}:
          +hz2 = hz
          +ne = cell.ne(r, z, im, fi, nx, hcell, hz2)
          %Equal.sym(Bool, U32.is_eq(r, z), False{}, ne) : {Bool.or(_, D.Node(f, m, D.Fd(2n, m, r), z)) == False{} : Bool}
          %Equal.sym(Bool, D.Node(f, m, D.Fd(2n, m, r), z), False{}, node.notcell(f, dk, ds, m, im, fi, nx, ks, img, D.Fd(2n, m, r), z, h1, hz2)) : {Bool.or(False{}, _) == False{} : Bool}
          {==}
    case Bk.Term.App{+q, +f, +y}:
      match hk:
        case Tuple{Tuple{hcell, _}, Tuple{_, Tuple{Tuple{_, h1}, Tuple{_, h2}}}}:
          +hz2 = hz
          +ne = cell.ne(r, z, im, fi, nx, hcell, hz2)
          %Equal.sym(Bool, U32.is_eq(r, z), False{}, ne) : {Bool.or(_, Bool.or(D.Node(f, m, D.Fd(2n, m, r), z), D.Node(y, m, D.Fd(3n, m, r), z))) == False{} : Bool}
          %Equal.sym(Bool, D.Node(f, m, D.Fd(2n, m, r), z), False{}, node.notcell(f, dk, ds, m, im, fi, nx, ks, img, D.Fd(2n, m, r), z, h1, hz2)) : {Bool.or(False{}, Bool.or(_, D.Node(y, m, D.Fd(3n, m, r), z))) == False{} : Bool}
          %Equal.sym(Bool, D.Node(y, m, D.Fd(3n, m, r), z), False{}, node.notcell(y, dk, ds, m, im, fi, nx, ks, img, D.Fd(3n, m, r), z, h2, hz2)) : {Bool.or(False{}, Bool.or(False{}, _)) == False{} : Bool}
          {==}
    case Bk.Term.Sig{+q, +a, +b}:
      match hk:
        case Tuple{Tuple{hcell, _}, Tuple{_, Tuple{Tuple{_, h1}, Tuple{_, h2}}}}:
          +hz2 = hz
          +ne = cell.ne(r, z, im, fi, nx, hcell, hz2)
          %Equal.sym(Bool, U32.is_eq(r, z), False{}, ne) : {Bool.or(_, Bool.or(D.Node(a, m, D.Fd(2n, m, r), z), D.Node(b, m, D.Fd(3n, m, r), z))) == False{} : Bool}
          %Equal.sym(Bool, D.Node(a, m, D.Fd(2n, m, r), z), False{}, node.notcell(a, dk, ds, m, im, fi, nx, ks, img, D.Fd(2n, m, r), z, h1, hz2)) : {Bool.or(False{}, Bool.or(_, D.Node(b, m, D.Fd(3n, m, r), z))) == False{} : Bool}
          %Equal.sym(Bool, D.Node(b, m, D.Fd(3n, m, r), z), False{}, node.notcell(b, dk, ds, m, im, fi, nx, ks, img, D.Fd(3n, m, r), z, h2, hz2)) : {Bool.or(False{}, Bool.or(False{}, _)) == False{} : Bool}
          {==}
    case Bk.Term.Tup{+q, +a, +b}:
      match hk:
        case Tuple{Tuple{hcell, _}, Tuple{_, Tuple{Tuple{_, h1}, Tuple{_, h2}}}}:
          +hz2 = hz
          +ne = cell.ne(r, z, im, fi, nx, hcell, hz2)
          %Equal.sym(Bool, U32.is_eq(r, z), False{}, ne) : {Bool.or(_, Bool.or(D.Node(a, m, D.Fd(2n, m, r), z), D.Node(b, m, D.Fd(3n, m, r), z))) == False{} : Bool}
          %Equal.sym(Bool, D.Node(a, m, D.Fd(2n, m, r), z), False{}, node.notcell(a, dk, ds, m, im, fi, nx, ks, img, D.Fd(2n, m, r), z, h1, hz2)) : {Bool.or(False{}, Bool.or(_, D.Node(b, m, D.Fd(3n, m, r), z))) == False{} : Bool}
          %Equal.sym(Bool, D.Node(b, m, D.Fd(3n, m, r), z), False{}, node.notcell(b, dk, ds, m, im, fi, nx, ks, img, D.Fd(3n, m, r), z, h2, hz2)) : {Bool.or(False{}, Bool.or(False{}, _)) == False{} : Bool}
          {==}
    case Bk.Term.Prj{+h}:
      match hk:
        case Tuple{Tuple{hcell, _}, Tuple{_, h1}}:
          +hz2 = hz
          +ne = cell.ne(r, z, im, fi, nx, hcell, hz2)
          %Equal.sym(Bool, U32.is_eq(r, z), False{}, ne) : {Bool.or(_, D.Node(h, m, D.Fd(2n, m, r), z)) == False{} : Bool}
          %Equal.sym(Bool, D.Node(h, m, D.Fd(2n, m, r), z), False{}, node.notcell(h, dk, ds, m, im, fi, nx, ks, img, D.Fd(2n, m, r), z, h1, hz2)) : {Bool.or(False{}, _) == False{} : Bool}
          {==}
    case Bk.Term.Enu{+e}:
      match hk:
        case Tuple{Tuple{hcell, _}, _}:
          cell.ne(r, z, im, fi, nx, hcell, hz)
    case Bk.Term.Lab{+k}:
      match hk:
        case Tuple{Tuple{hcell, _}, _}:
          cell.ne(r, z, im, fi, nx, hcell, hz)
    case Bk.Term.Mat{+k, +h, +o}:
      match hk:
        case Tuple{Tuple{hcell, _}, Tuple{_, Tuple{Tuple{_, h1}, Tuple{_, h2}}}}:
          +hz2 = hz
          +ne = cell.ne(r, z, im, fi, nx, hcell, hz2)
          %Equal.sym(Bool, U32.is_eq(r, z), False{}, ne) : {Bool.or(_, Bool.or(D.Node(h, m, D.Fd(3n, m, r), z), D.Node(o, m, D.Fd(4n, m, r), z))) == False{} : Bool}
          %Equal.sym(Bool, D.Node(h, m, D.Fd(3n, m, r), z), False{}, node.notcell(h, dk, ds, m, im, fi, nx, ks, img, D.Fd(3n, m, r), z, h1, hz2)) : {Bool.or(False{}, Bool.or(_, D.Node(o, m, D.Fd(4n, m, r), z))) == False{} : Bool}
          %Equal.sym(Bool, D.Node(o, m, D.Fd(4n, m, r), z), False{}, node.notcell(o, dk, ds, m, im, fi, nx, ks, img, D.Fd(4n, m, r), z, h2, hz2)) : {Bool.or(False{}, Bool.or(False{}, _)) == False{} : Bool}
          {==}
    case Bk.Term.Efq{}:
      match hk:
        case Tuple{hcell, _}:
          cell.ne(r, z, im, fi, nx, hcell, hz)
    case Bk.Term.Eql{+a, +b, +y}:
      match hk:
        case Tuple{Tuple{hcell, _}, Tuple{Tuple{_, h1}, Tuple{Tuple{_, h2}, Tuple{_, h3}}}}:
          +hz2 = hz
          +ne = cell.ne(r, z, im, fi, nx, hcell, hz2)
          %Equal.sym(Bool, U32.is_eq(r, z), False{}, ne) : {Bool.or(_, Bool.or(D.Node(a, m, D.Fd(2n, m, r), z), Bool.or(D.Node(b, m, D.Fd(3n, m, r), z), D.Node(y, m, D.Fd(4n, m, r), z)))) == False{} : Bool}
          %Equal.sym(Bool, D.Node(a, m, D.Fd(2n, m, r), z), False{}, node.notcell(a, dk, ds, m, im, fi, nx, ks, img, D.Fd(2n, m, r), z, h1, hz2)) : {Bool.or(False{}, Bool.or(_, Bool.or(D.Node(b, m, D.Fd(3n, m, r), z), D.Node(y, m, D.Fd(4n, m, r), z)))) == False{} : Bool}
          %Equal.sym(Bool, D.Node(b, m, D.Fd(3n, m, r), z), False{}, node.notcell(b, dk, ds, m, im, fi, nx, ks, img, D.Fd(3n, m, r), z, h2, hz2)) : {Bool.or(False{}, Bool.or(False{}, Bool.or(_, D.Node(y, m, D.Fd(4n, m, r), z)))) == False{} : Bool}
          %Equal.sym(Bool, D.Node(y, m, D.Fd(4n, m, r), z), False{}, node.notcell(y, dk, ds, m, im, fi, nx, ks, img, D.Fd(4n, m, r), z, h3, hz2)) : {Bool.or(False{}, Bool.or(False{}, Bool.or(False{}, _))) == False{} : Bool}
          {==}
    case Bk.Term.Rfl{}:
      match hk:
        case Tuple{hcell, _}:
          cell.ne(r, z, im, fi, nx, hcell, hz)
    case Bk.Term.Rwt{+e, +p, +f}:
      match hk:
        case Tuple{Tuple{hcell, _}, Tuple{Tuple{_, h1}, Tuple{Tuple{_, h2}, Tuple{_, h3}}}}:
          +hz2 = hz
          +ne = cell.ne(r, z, im, fi, nx, hcell, hz2)
          %Equal.sym(Bool, U32.is_eq(r, z), False{}, ne) : {Bool.or(_, Bool.or(D.Node(e, m, D.Fd(2n, m, r), z), Bool.or(D.Node(p, m, D.Fd(3n, m, r), z), D.Node(f, m, D.Fd(4n, m, r), z)))) == False{} : Bool}
          %Equal.sym(Bool, D.Node(e, m, D.Fd(2n, m, r), z), False{}, node.notcell(e, dk, ds, m, im, fi, nx, ks, img, D.Fd(2n, m, r), z, h1, hz2)) : {Bool.or(False{}, Bool.or(_, Bool.or(D.Node(p, m, D.Fd(3n, m, r), z), D.Node(f, m, D.Fd(4n, m, r), z)))) == False{} : Bool}
          %Equal.sym(Bool, D.Node(p, m, D.Fd(3n, m, r), z), False{}, node.notcell(p, dk, ds, m, im, fi, nx, ks, img, D.Fd(3n, m, r), z, h2, hz2)) : {Bool.or(False{}, Bool.or(False{}, Bool.or(_, D.Node(f, m, D.Fd(4n, m, r), z)))) == False{} : Bool}
          %Equal.sym(Bool, D.Node(f, m, D.Fd(4n, m, r), z), False{}, node.notcell(f, dk, ds, m, im, fi, nx, ks, img, D.Fd(4n, m, r), z, h3, hz2)) : {Bool.or(False{}, Bool.or(False{}, Bool.or(False{}, _))) == False{} : Bool}
          {==}

def nodes.set(rs: List<&2, D.Rt>, +m: Cr.Cir.Cells, +z: U32, +xc: Cr.Cir.Cell, +x: U32, hn: {D.Nodes(rs, m, z) == False{} : Bool}) ->
  {D.Nodes(rs, Cr.Cir.Cells.set(m, z, xc), x) == D.Nodes(rs, m, x) : Bool}:
  match rs:
    case Nil{}:
      {==}
    case Con{D.Rt{+r, +u}, +rest}:
      +hn2 = hn
      or.cong2(D.Node(u, Cr.Cir.Cells.set(m, z, xc), r, x), D.Node(u, m, r, x), D.Nodes(rest, Cr.Cir.Cells.set(m, z, xc), x), D.Nodes(rest, m, x),
        node.set(u, m, z, xc, r, x, D.or.f.l(D.Node(u, m, r, z), D.Nodes(rest, m, z), hn2)),
        nodes.set(rest, m, z, xc, x, D.or.f.r(D.Node(u, m, r, z), D.Nodes(rest, m, z), hn2)))

def nodes.notcell(rs: List<&2, D.Rt>, +dk: Bool, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +z: U32, h: D.RtsK(dk, ds, m, im, fi, nx, ks, img, rs),
  hz: {Cr.Cir.is_cell(z, im, fi, nx) == False{} : Bool}) -> {D.Nodes(rs, m, z) == False{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case Con{D.Rt{+r, +u}, +rest}:
      match h:
        case Tuple{hu, hr}:
          +hz2 = hz
          %Equal.sym(Bool, D.Node(u, m, r, z), False{}, node.notcell(u, dk, ds, m, im, fi, nx, ks, img, r, z, hu, hz2)) :
            {Bool.or(_, D.Nodes(rest, m, z)) == False{} : Bool}
          nodes.notcell(rest, dk, ds, m, im, fi, nx, ks, img, z, hr, hz2)

def rtsk.app(+dk: Bool, A: List<&2, D.Rt>, +B: List<&2, D.Rt>, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, ha: D.RtsK(dk, ds, m, im, fi, nx, ks, img, A),
  hb: D.RtsK(dk, ds, m, im, fi, nx, ks, img, B)) -> D.RtsK(dk, ds, m, im, fi, nx, ks, img, List.append(&2, D.Rt, A, B)):
  match A:
    case Nil{}:
      hb
    case Con{D.Rt{+c, +u}, +rest}:
      match ha:
        case Tuple{hu, hr}:
          (hu, rtsk.app(dk, rest, B, ds, m, im, fi, nx, ks, img, hr, hb))

def rtsk.b(kind: D.FK, +dk: Bool, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +fr: U32, +b: Bk.Term,
  h: D.Frs.bK(dk, ds, m, im, fi, nx, ks, img, D.Fd(3n, m, fr), kind, b)) -> D.RtsK(dk, ds, m, im, fi, nx, ks, img, D.Fr.rts.b(m, fr, kind, b)):
  match kind:
    case D.FK.rwt{}:
      (h, Unit{})
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

# the frames' terms stand for their terms
def frs.rtsk(+dk: Bool, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +ps: List<&2, U32>, fs: List<&2, D.AF>, +sp: U32, h: D.FrsK(dk, ds, m, im, fi, nx, ks, img, ps, sp, fs)) ->
  D.RtsK(dk, ds, m, im, fi, nx, ks, img, D.Fr.rts(fs, m, sp)):
  match fs:
    case Nil{}:
      Unit{}
    case Con{D.AF{+kind, +q, +k, +a, +b}, +rest}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{ia, Tuple{ib, hr}}}}}}}}}}:
          (ia, rtsk.app(dk, D.Fr.rts.b(m, sp, kind, b), D.Fr.rts(rest, m, D.Fd(1n, m, sp)), ds, m, im, fi, nx, ks, img,
            rtsk.b(kind, dk, ds, m, im, fi, nx, ks, img, sp, b, ib), frs.rtsk(dk, ds, m, im, fi, nx, ks, img, ps, rest, D.Fd(1n, m, sp), hr)))

# a cell that is no cell is no frame
def fr.out.cell(+dk: Bool, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +ps: List<&2, U32>, fs: List<&2, D.AF>, +sp: U32, +z: U32, hf: D.FrsK(dk, ds, m, im, fi, nx, ks, img, ps, sp, fs),
  hz: {Cr.Cir.is_cell(z, im, fi, nx) == False{} : Bool}) -> {D.Mem(D.Fr.cells(fs, m, sp), z) == False{} : Bool}:
  match fs:
    case Nil{}:
      {==}
    case Con{D.AF{+kind, +q, +k, +a, +b}, +rest}:
      match hf:
        case Tuple{_, Tuple{hc, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, hr}}}}}}}}}}:
          +hz2 = hz
          %Equal.sym(Bool, U32.is_eq(sp, z), False{}, cell.ne(sp, z, im, fi, nx, hc, hz2)) :
            {Bool.or(_, D.Mem(D.Fr.cells(rest, m, D.Fd(1n, m, sp)), z)) == False{} : Bool}
          fr.out.cell(dk, ds, m, im, fi, nx, ks, img, ps, rest, D.Fd(1n, m, sp), z, hr, hz2)

# Fr.rts.b reads field 3 only
def frb.eq(kind: D.FK, -m: Cr.Cir.Cells, -M2: Cr.Cir.Cells, +fr: U32, +b: Bk.Term, e3: {D.Fd(3n, M2, fr) == D.Fd(3n, m, fr) : U32}) ->
  {D.Fr.rts.b(M2, fr, kind, b) == D.Fr.rts.b(m, fr, kind, b) : List<&2, D.Rt>}:
  match kind:
    case D.FK.rwt{}:
      %Equal.sym(U32, D.Fd(3n, M2, fr), D.Fd(3n, m, fr), e3) : {[D.Rt{_, b}] == [D.Rt{D.Fd(3n, m, fr), b}] : List<&2, D.Rt>}
      {==}
    case D.FK.arg{}:
      {==}
    case D.FK.val{}:
      {==}
    case D.FK.fun{}:
      {==}
    case D.FK.let{}:
      {==}
    case D.FK.tupb{}:
      {==}
    case D.FK.tupa{}:
      {==}
    case D.FK.minb{}:
      {==}
    case D.FK.mina{}:
      {==}

# a store at a cell that is no frame keeps the frames' cells and terms
def fr.set(fs: List<&2, D.AF>, +m: Cr.Cir.Cells, +fr: U32, +z: U32, +xc: Cr.Cir.Cell, h: {D.Mem(D.Fr.cells(fs, m, fr), z) == False{} : Bool}) ->
  D.P2({D.Fr.cells(fs, Cr.Cir.Cells.set(m, z, xc), fr) == D.Fr.cells(fs, m, fr) : List<&2, U32>},
    {D.Fr.rts(fs, Cr.Cir.Cells.set(m, z, xc), fr) == D.Fr.rts(fs, m, fr) : List<&2, D.Rt>}):
  match fs:
    case Nil{}:
      ({==}, {==})
    case Con{D.AF{+kind, +q, +k, +a, +b}, +rest}:
      +M2 = Cr.Cir.Cells.set(m, z, xc)
      +h2 = h
      +f1 = D.Fd(1n, m, fr)
      +ec = D.cl.go(m, fr, z, xc, D.or.f.l(U32.is_eq(fr, z), D.Mem(D.Fr.cells(rest, m, f1), z), h2))
      +e1 = {Equal.cong(Cr.Cir.Cell, U32, y => Cr.Cir.Cell.get(1n, y), Cr.Cir.Cells.get(M2, fr), Cr.Cir.Cells.get(m, fr), ec) : {D.Fd(1n, M2, fr) == f1 : U32}}
      +e2 = {Equal.cong(Cr.Cir.Cell, U32, y => Cr.Cir.Cell.get(2n, y), Cr.Cir.Cells.get(M2, fr), Cr.Cir.Cells.get(m, fr), ec) : {D.Fd(2n, M2, fr) == D.Fd(2n, m, fr) : U32}}
      +e3 = {Equal.cong(Cr.Cir.Cell, U32, y => Cr.Cir.Cell.get(3n, y), Cr.Cir.Cells.get(M2, fr), Cr.Cir.Cells.get(m, fr), ec) : {D.Fd(3n, M2, fr) == D.Fd(3n, m, fr) : U32}}
      +ih = fr.set(rest, m, f1, z, xc, D.or.f.r(U32.is_eq(fr, z), D.Mem(D.Fr.cells(rest, m, f1), z), h2))
      +ihc = D.Ex.fst({D.Fr.cells(rest, M2, f1) == D.Fr.cells(rest, m, f1) : List<&2, U32>}, _ => {D.Fr.rts(rest, M2, f1) == D.Fr.rts(rest, m, f1) : List<&2, D.Rt>}, ih)
      +ihr = D.Ex.snd({D.Fr.cells(rest, M2, f1) == D.Fr.cells(rest, m, f1) : List<&2, U32>}, _ => {D.Fr.rts(rest, M2, f1) == D.Fr.rts(rest, m, f1) : List<&2, D.Rt>}, ih)
      +eb = frb.eq(kind, m, M2, fr, b, e3)
      ({(%Equal.sym(U32, D.Fd(1n, M2, fr), f1, e1) : {Con{fr, D.Fr.cells(rest, M2, _)} == Con{fr, D.Fr.cells(rest, m, f1)} : List<&2, U32>};
          %Equal.sym(List<&2, U32>, D.Fr.cells(rest, M2, f1), D.Fr.cells(rest, m, f1), ihc) : {Con{fr, _} == Con{fr, D.Fr.cells(rest, m, f1)} : List<&2, U32>};
          {==}) : {D.Fr.cells(Con{D.AF{kind, q, k, a, b}, rest}, M2, fr) == D.Fr.cells(Con{D.AF{kind, q, k, a, b}, rest}, m, fr) : List<&2, U32>}},
        {(%Equal.sym(U32, D.Fd(1n, M2, fr), f1, e1) :
            {Con{D.Rt{D.Fd(2n, M2, fr), a}, List.append(&2, D.Rt, D.Fr.rts.b(M2, fr, kind, b), D.Fr.rts(rest, M2, _))} ==
              Con{D.Rt{D.Fd(2n, m, fr), a}, List.append(&2, D.Rt, D.Fr.rts.b(m, fr, kind, b), D.Fr.rts(rest, m, f1))} : List<&2, D.Rt>};
          %Equal.sym(U32, D.Fd(2n, M2, fr), D.Fd(2n, m, fr), e2) :
            {Con{D.Rt{_, a}, List.append(&2, D.Rt, D.Fr.rts.b(M2, fr, kind, b), D.Fr.rts(rest, M2, f1))} ==
              Con{D.Rt{D.Fd(2n, m, fr), a}, List.append(&2, D.Rt, D.Fr.rts.b(m, fr, kind, b), D.Fr.rts(rest, m, f1))} : List<&2, D.Rt>};
          %Equal.sym(List<&2, D.Rt>, D.Fr.rts.b(M2, fr, kind, b), D.Fr.rts.b(m, fr, kind, b), eb) :
            {Con{D.Rt{D.Fd(2n, m, fr), a}, List.append(&2, D.Rt, _, D.Fr.rts(rest, M2, f1))} ==
              Con{D.Rt{D.Fd(2n, m, fr), a}, List.append(&2, D.Rt, D.Fr.rts.b(m, fr, kind, b), D.Fr.rts(rest, m, f1))} : List<&2, D.Rt>};
          %Equal.sym(List<&2, D.Rt>, D.Fr.rts(rest, M2, f1), D.Fr.rts(rest, m, f1), ihr) :
            {Con{D.Rt{D.Fd(2n, m, fr), a}, List.append(&2, D.Rt, D.Fr.rts.b(m, fr, kind, b), _)} ==
              Con{D.Rt{D.Fd(2n, m, fr), a}, List.append(&2, D.Rt, D.Fr.rts.b(m, fr, kind, b), D.Fr.rts(rest, m, f1))} : List<&2, D.Rt>};
          {==}) : {D.Fr.rts(Con{D.AF{kind, q, k, a, b}, rest}, M2, fr) == D.Fr.rts(Con{D.AF{kind, q, k, a, b}, rest}, m, fr) : List<&2, D.Rt>}})

# The flag DATA
# -------------

def W.hd(+p: Nat, w: Word(1n+p)) -> Bool:
  match w:
    case WCon{x, _}:
      x

def W.tl(+p: Nat, w: Word(1n+p)) -> Word(p):
  match w:
    case WCon{_, t}:
      t

def bit.and.or(a: Bool, b: Bool, c: Bool, h: {Bool.and(b, c) == False{} : Bool}) -> {Bool.and(Bool.or(a, b), c) == Bool.and(a, c) : Bool}:
  match a b c:
    case True{} True{} True{}:
      Empty.absurd({True{} == True{} : Bool}, N.true_ne_false(h))
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      Empty.absurd({True{} == False{} : Bool}, N.true_ne_false(h))
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

# (a | b) & c = a & c, when b & c = 0
def wand.or(n: Nat, a: Word(n), b: Word(n), c: Word(n), h: {Word.and(n, b, c) == Word.zero(n) : Word(n)}) ->
  {Word.and(n, Word.or(n, a, b), c) == Word.and(n, a, c) : Word(n)}:
  match n:
    case 0n:
      match a b c:
        case WNil{} WNil{} WNil{}:
          {==}
    case 1n+(+p):
      match a b c:
        case WCon{+ab, +at} WCon{+bb, +bt} WCon{+cb, +ct}:
          +h2 = h
          +hb = Equal.cong(Word(1n+p), Bool, w => W.hd(p, w), WCon{Bool.and(bb, cb), Word.and(p, bt, ct)}, WCon{False{}, Word.zero(p)}, h2)
          +ht = Equal.cong(Word(1n+p), Word(p), w => W.tl(p, w), WCon{Bool.and(bb, cb), Word.and(p, bt, ct)}, WCon{False{}, Word.zero(p)}, h2)
          %Equal.sym(Bool, Bool.and(Bool.or(ab, bb), cb), Bool.and(ab, cb), bit.and.or(ab, bb, cb, hb)) :
            {WCon{_, Word.and(p, Word.or(p, at, bt), ct)} == WCon{Bool.and(ab, cb), Word.and(p, at, ct)} : Word(1n+p)}
          %Equal.sym(Word(p), Word.and(p, Word.or(p, at, bt), ct), Word.and(p, at, ct), wand.or(p, at, bt, ct, ht)) :
            {WCon{Bool.and(ab, cb), _} == WCon{Bool.and(ab, cb), Word.and(p, at, ct)} : Word(1n+p)}
          {==}

def U32.w(u: U32) -> Word(32n):
  match u:
    case U32{w}:
      w

def u32.and.or(+a: U32, +b: U32, +c: U32, h: {U32.and(b, c) == 0 : U32}) -> {U32.and(U32.or(a, b), c) == U32.and(a, c) : U32}:
  match a b c:
    case U32{+x} U32{+y} U32{+z}:
      Equal.cong(Word(32n), U32, w => U32{w}, Word.and(32n, Word.or(32n, x, y), z), Word.and(32n, x, z),
        wand.or(32n, x, y, z, Equal.cong(U32, Word(32n), u => U32.w(u), U32{Word.and(32n, y, z)}, 0, h)))

def and.dat.st() -> {U32.and(512, 1024) == 0 : U32}:
  {==}

def and.dat.tg() -> {U32.and(512, 63) == 0 : U32}:
  {==}

def and.dat.own() -> {U32.and(512, 4096) == 0 : U32}:
  {==}

def s0g0(+y: Cr.Cir.Cell, -w: U32) -> {Cr.Cir.Cell.get(0n, Cr.Cir.Cell.set(0n, y, w)) == w : U32}:
  match y:
    case Cr.Cir.Cell{a, b, c2, c3, c4}:
      {==}

def s0g1(+y: Cr.Cir.Cell, -w: U32) -> {Cr.Cir.Cell.get(1n, Cr.Cir.Cell.set(0n, y, w)) == Cr.Cir.Cell.get(1n, y) : U32}:
  match y:
    case Cr.Cir.Cell{a, b, c2, c3, c4}:
      {==}

def s0g2(+y: Cr.Cir.Cell, -w: U32) -> {Cr.Cir.Cell.get(2n, Cr.Cir.Cell.set(0n, y, w)) == Cr.Cir.Cell.get(2n, y) : U32}:
  match y:
    case Cr.Cir.Cell{a, b, c2, c3, c4}:
      {==}

def s0g3(+y: Cr.Cir.Cell, -w: U32) -> {Cr.Cir.Cell.get(3n, Cr.Cir.Cell.set(0n, y, w)) == Cr.Cir.Cell.get(3n, y) : U32}:
  match y:
    case Cr.Cir.Cell{a, b, c2, c3, c4}:
      {==}

def s0g4(+y: Cr.Cir.Cell, -w: U32) -> {Cr.Cir.Cell.get(4n, Cr.Cir.Cell.set(0n, y, w)) == Cr.Cir.Cell.get(4n, y) : U32}:
  match y:
    case Cr.Cir.Cell{a, b, c2, c3, c4}:
      {==}

# the cells m with the flag DATA set at the cell cf
def Flag(+m: Cr.Cir.Cells, +cf: U32) -> Cr.Cir.Cells:
  Cr.Cir.Cells.set(m, cf, Cr.Cir.Cell.set(0n, Cr.Cir.Cells.get(m, cf), U32.or(D.Fd(0n, m, cf), 512)))

def fd.flag1.b(b: Bool, +m: Cr.Cir.Cells, +cf: U32, +o: U32, eb: {U32.is_eq(o, cf) == b : Bool}) ->
  {D.Fd(1n, Flag(m, cf), o) == D.Fd(1n, m, o) : U32}:
  match b:
    case True{}:
      %Equal.sym(U32, o, cf, D.u32.eq(o, cf, eb)) : {D.Fd(1n, Flag(m, cf), _) == D.Fd(1n, m, _) : U32}
      Equal.trans(U32, D.Fd(1n, Flag(m, cf), cf), Cr.Cir.Cell.get(1n, Cr.Cir.Cell.set(0n, Cr.Cir.Cells.get(m, cf), U32.or(D.Fd(0n, m, cf), 512))), D.Fd(1n, m, cf),
        Equal.cong(Cr.Cir.Cell, U32, y => Cr.Cir.Cell.get(1n, y), Cr.Cir.Cells.get(Flag(m, cf), cf), Cr.Cir.Cell.set(0n, Cr.Cir.Cells.get(m, cf), U32.or(D.Fd(0n, m, cf), 512)), D.cl.gs(m, cf, Cr.Cir.Cell.set(0n, Cr.Cir.Cells.get(m, cf), U32.or(D.Fd(0n, m, cf), 512)))),
        s0g1(Cr.Cir.Cells.get(m, cf), U32.or(D.Fd(0n, m, cf), 512)))
    case False{}:
      Equal.cong(Cr.Cir.Cell, U32, y => Cr.Cir.Cell.get(1n, y), Cr.Cir.Cells.get(Flag(m, cf), o), Cr.Cir.Cells.get(m, o), D.cl.go(m, o, cf, Cr.Cir.Cell.set(0n, Cr.Cir.Cells.get(m, cf), U32.or(D.Fd(0n, m, cf), 512)), eb))

# the flag DATA keeps field 1 of every cell
def fd.flag1(+m: Cr.Cir.Cells, +cf: U32, +o: U32) -> {D.Fd(1n, Flag(m, cf), o) == D.Fd(1n, m, o) : U32}:
  fd.flag1.b(U32.is_eq(o, cf), m, cf, o, {==})

def fd.flag2.b(b: Bool, +m: Cr.Cir.Cells, +cf: U32, +o: U32, eb: {U32.is_eq(o, cf) == b : Bool}) ->
  {D.Fd(2n, Flag(m, cf), o) == D.Fd(2n, m, o) : U32}:
  match b:
    case True{}:
      %Equal.sym(U32, o, cf, D.u32.eq(o, cf, eb)) : {D.Fd(2n, Flag(m, cf), _) == D.Fd(2n, m, _) : U32}
      Equal.trans(U32, D.Fd(2n, Flag(m, cf), cf), Cr.Cir.Cell.get(2n, Cr.Cir.Cell.set(0n, Cr.Cir.Cells.get(m, cf), U32.or(D.Fd(0n, m, cf), 512))), D.Fd(2n, m, cf),
        Equal.cong(Cr.Cir.Cell, U32, y => Cr.Cir.Cell.get(2n, y), Cr.Cir.Cells.get(Flag(m, cf), cf), Cr.Cir.Cell.set(0n, Cr.Cir.Cells.get(m, cf), U32.or(D.Fd(0n, m, cf), 512)), D.cl.gs(m, cf, Cr.Cir.Cell.set(0n, Cr.Cir.Cells.get(m, cf), U32.or(D.Fd(0n, m, cf), 512)))),
        s0g2(Cr.Cir.Cells.get(m, cf), U32.or(D.Fd(0n, m, cf), 512)))
    case False{}:
      Equal.cong(Cr.Cir.Cell, U32, y => Cr.Cir.Cell.get(2n, y), Cr.Cir.Cells.get(Flag(m, cf), o), Cr.Cir.Cells.get(m, o), D.cl.go(m, o, cf, Cr.Cir.Cell.set(0n, Cr.Cir.Cells.get(m, cf), U32.or(D.Fd(0n, m, cf), 512)), eb))

# the flag DATA keeps field 2 of every cell
def fd.flag2(+m: Cr.Cir.Cells, +cf: U32, +o: U32) -> {D.Fd(2n, Flag(m, cf), o) == D.Fd(2n, m, o) : U32}:
  fd.flag2.b(U32.is_eq(o, cf), m, cf, o, {==})

def fd.flag3.b(b: Bool, +m: Cr.Cir.Cells, +cf: U32, +o: U32, eb: {U32.is_eq(o, cf) == b : Bool}) ->
  {D.Fd(3n, Flag(m, cf), o) == D.Fd(3n, m, o) : U32}:
  match b:
    case True{}:
      %Equal.sym(U32, o, cf, D.u32.eq(o, cf, eb)) : {D.Fd(3n, Flag(m, cf), _) == D.Fd(3n, m, _) : U32}
      Equal.trans(U32, D.Fd(3n, Flag(m, cf), cf), Cr.Cir.Cell.get(3n, Cr.Cir.Cell.set(0n, Cr.Cir.Cells.get(m, cf), U32.or(D.Fd(0n, m, cf), 512))), D.Fd(3n, m, cf),
        Equal.cong(Cr.Cir.Cell, U32, y => Cr.Cir.Cell.get(3n, y), Cr.Cir.Cells.get(Flag(m, cf), cf), Cr.Cir.Cell.set(0n, Cr.Cir.Cells.get(m, cf), U32.or(D.Fd(0n, m, cf), 512)), D.cl.gs(m, cf, Cr.Cir.Cell.set(0n, Cr.Cir.Cells.get(m, cf), U32.or(D.Fd(0n, m, cf), 512)))),
        s0g3(Cr.Cir.Cells.get(m, cf), U32.or(D.Fd(0n, m, cf), 512)))
    case False{}:
      Equal.cong(Cr.Cir.Cell, U32, y => Cr.Cir.Cell.get(3n, y), Cr.Cir.Cells.get(Flag(m, cf), o), Cr.Cir.Cells.get(m, o), D.cl.go(m, o, cf, Cr.Cir.Cell.set(0n, Cr.Cir.Cells.get(m, cf), U32.or(D.Fd(0n, m, cf), 512)), eb))

# the flag DATA keeps field 3 of every cell
def fd.flag3(+m: Cr.Cir.Cells, +cf: U32, +o: U32) -> {D.Fd(3n, Flag(m, cf), o) == D.Fd(3n, m, o) : U32}:
  fd.flag3.b(U32.is_eq(o, cf), m, cf, o, {==})

def fd.flag4.b(b: Bool, +m: Cr.Cir.Cells, +cf: U32, +o: U32, eb: {U32.is_eq(o, cf) == b : Bool}) ->
  {D.Fd(4n, Flag(m, cf), o) == D.Fd(4n, m, o) : U32}:
  match b:
    case True{}:
      %Equal.sym(U32, o, cf, D.u32.eq(o, cf, eb)) : {D.Fd(4n, Flag(m, cf), _) == D.Fd(4n, m, _) : U32}
      Equal.trans(U32, D.Fd(4n, Flag(m, cf), cf), Cr.Cir.Cell.get(4n, Cr.Cir.Cell.set(0n, Cr.Cir.Cells.get(m, cf), U32.or(D.Fd(0n, m, cf), 512))), D.Fd(4n, m, cf),
        Equal.cong(Cr.Cir.Cell, U32, y => Cr.Cir.Cell.get(4n, y), Cr.Cir.Cells.get(Flag(m, cf), cf), Cr.Cir.Cell.set(0n, Cr.Cir.Cells.get(m, cf), U32.or(D.Fd(0n, m, cf), 512)), D.cl.gs(m, cf, Cr.Cir.Cell.set(0n, Cr.Cir.Cells.get(m, cf), U32.or(D.Fd(0n, m, cf), 512)))),
        s0g4(Cr.Cir.Cells.get(m, cf), U32.or(D.Fd(0n, m, cf), 512)))
    case False{}:
      Equal.cong(Cr.Cir.Cell, U32, y => Cr.Cir.Cell.get(4n, y), Cr.Cir.Cells.get(Flag(m, cf), o), Cr.Cir.Cells.get(m, o), D.cl.go(m, o, cf, Cr.Cir.Cell.set(0n, Cr.Cir.Cells.get(m, cf), U32.or(D.Fd(0n, m, cf), 512)), eb))

# the flag DATA keeps field 4 of every cell
def fd.flag4(+m: Cr.Cir.Cells, +cf: U32, +o: U32) -> {D.Fd(4n, Flag(m, cf), o) == D.Fd(4n, m, o) : U32}:
  fd.flag4.b(U32.is_eq(o, cf), m, cf, o, {==})

# and the bits of field 0 that are not DATA
def fl.flag.b(b: Bool, +m: Cr.Cir.Cells, +cf: U32, +o: U32, +fl: U32, eb: {U32.is_eq(o, cf) == b : Bool}, h0: {U32.and(512, fl) == 0 : U32}) ->
  {U32.and(D.Fd(0n, Flag(m, cf), o), fl) == U32.and(D.Fd(0n, m, o), fl) : U32}:
  match b:
    case True{}:
      %Equal.sym(U32, o, cf, D.u32.eq(o, cf, eb)) : {U32.and(D.Fd(0n, Flag(m, cf), _), fl) == U32.and(D.Fd(0n, m, _), fl) : U32}
      Equal.trans(U32, U32.and(D.Fd(0n, Flag(m, cf), cf), fl), U32.and(U32.or(D.Fd(0n, m, cf), 512), fl), U32.and(D.Fd(0n, m, cf), fl),
        Equal.cong(U32, U32, w => U32.and(w, fl), D.Fd(0n, Flag(m, cf), cf), U32.or(D.Fd(0n, m, cf), 512),
          Equal.trans(U32, D.Fd(0n, Flag(m, cf), cf), Cr.Cir.Cell.get(0n, Cr.Cir.Cell.set(0n, Cr.Cir.Cells.get(m, cf), U32.or(D.Fd(0n, m, cf), 512))), U32.or(D.Fd(0n, m, cf), 512),
            Equal.cong(Cr.Cir.Cell, U32, y => Cr.Cir.Cell.get(0n, y), Cr.Cir.Cells.get(Flag(m, cf), cf), Cr.Cir.Cell.set(0n, Cr.Cir.Cells.get(m, cf), U32.or(D.Fd(0n, m, cf), 512)), D.cl.gs(m, cf, Cr.Cir.Cell.set(0n, Cr.Cir.Cells.get(m, cf), U32.or(D.Fd(0n, m, cf), 512)))),
            s0g0(Cr.Cir.Cells.get(m, cf), U32.or(D.Fd(0n, m, cf), 512)))),
        u32.and.or(D.Fd(0n, m, cf), 512, fl, h0))
    case False{}:
      Equal.cong(Cr.Cir.Cell, U32, y => U32.and(Cr.Cir.Cell.get(0n, y), fl), Cr.Cir.Cells.get(Flag(m, cf), o), Cr.Cir.Cells.get(m, o), D.cl.go(m, o, cf, Cr.Cir.Cell.set(0n, Cr.Cir.Cells.get(m, cf), U32.or(D.Fd(0n, m, cf), 512)), eb))

def fl.flag(+m: Cr.Cir.Cells, +cf: U32, +o: U32, +fl: U32, h0: {U32.and(512, fl) == 0 : U32}) ->
  {D.Fl(Flag(m, cf), o, fl) == D.Fl(m, o, fl) : Bool}:
  Equal.cong(U32, Bool, w => U32.is_ne(w, 0), U32.and(D.Fd(0n, Flag(m, cf), o), fl), U32.and(D.Fd(0n, m, o), fl),
    fl.flag.b(U32.is_eq(o, cf), m, cf, o, fl, {==}, h0))

def tg.flag(+m: Cr.Cir.Cells, +cf: U32, +o: U32) -> {D.TgW(D.Fd(0n, Flag(m, cf), o)) == D.TgW(D.Fd(0n, m, o)) : U32}:
  fl.flag.b(U32.is_eq(o, cf), m, cf, o, 63, {==}, and.dat.tg())

# the flag DATA keeps which cells are nodes of a term
def node.flag(t: Bk.Term, +m: Cr.Cir.Cells, +cf: U32, +r: U32, +x: U32) ->
  {D.Node(t, Flag(m, cf), r, x) == D.Node(t, m, r, x) : Bool}:
  match t:
    case Bk.Term.Var{+i}:
      {==}
    case Bk.Term.Ref{+k}:
      {==}
    case Bk.Term.Ann{+y, +z}:
      +M2 = Flag(m, cf)
      Equal.cong(Bool, Bool, w => Bool.or(U32.is_eq(r, x), w), Bool.or(D.Node(y, M2, D.Fd(2n, M2, r), x), D.Node(z, M2, D.Fd(3n, M2, r), x)), Bool.or(D.Node(y, m, D.Fd(2n, m, r), x), D.Node(z, m, D.Fd(3n, m, r), x)),
        or.cong2(D.Node(y, M2, D.Fd(2n, M2, r), x), D.Node(y, m, D.Fd(2n, m, r), x), D.Node(z, M2, D.Fd(3n, M2, r), x), D.Node(z, m, D.Fd(3n, m, r), x),
        Equal.trans(Bool, D.Node(y, M2, D.Fd(2n, M2, r), x), D.Node(y, M2, D.Fd(2n, m, r), x), D.Node(y, m, D.Fd(2n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(y, M2, w, x), D.Fd(2n, M2, r), D.Fd(2n, m, r), fd.flag2(m, cf, r)),
          node.flag(y, m, cf, D.Fd(2n, m, r), x)),
        Equal.trans(Bool, D.Node(z, M2, D.Fd(3n, M2, r), x), D.Node(z, M2, D.Fd(3n, m, r), x), D.Node(z, m, D.Fd(3n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(z, M2, w, x), D.Fd(3n, M2, r), D.Fd(3n, m, r), fd.flag3(m, cf, r)),
          node.flag(z, m, cf, D.Fd(3n, m, r), x))))
    case Bk.Term.Let{+q, +v, +f}:
      +M2 = Flag(m, cf)
      Equal.cong(Bool, Bool, w => Bool.or(U32.is_eq(r, x), w), Bool.or(D.Node(v, M2, D.Fd(2n, M2, r), x), D.Node(f, M2, D.Fd(3n, M2, r), x)), Bool.or(D.Node(v, m, D.Fd(2n, m, r), x), D.Node(f, m, D.Fd(3n, m, r), x)),
        or.cong2(D.Node(v, M2, D.Fd(2n, M2, r), x), D.Node(v, m, D.Fd(2n, m, r), x), D.Node(f, M2, D.Fd(3n, M2, r), x), D.Node(f, m, D.Fd(3n, m, r), x),
        Equal.trans(Bool, D.Node(v, M2, D.Fd(2n, M2, r), x), D.Node(v, M2, D.Fd(2n, m, r), x), D.Node(v, m, D.Fd(2n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(v, M2, w, x), D.Fd(2n, M2, r), D.Fd(2n, m, r), fd.flag2(m, cf, r)),
          node.flag(v, m, cf, D.Fd(2n, m, r), x)),
        Equal.trans(Bool, D.Node(f, M2, D.Fd(3n, M2, r), x), D.Node(f, M2, D.Fd(3n, m, r), x), D.Node(f, m, D.Fd(3n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(f, M2, w, x), D.Fd(3n, M2, r), D.Fd(3n, m, r), fd.flag3(m, cf, r)),
          node.flag(f, m, cf, D.Fd(3n, m, r), x))))
    case Bk.Term.Typ{+y}:
      +M2 = Flag(m, cf)
      Equal.cong(Bool, Bool, w => Bool.or(U32.is_eq(r, x), w), D.Node(y, M2, D.Fd(2n, M2, r), x), D.Node(y, m, D.Fd(2n, m, r), x),
        Equal.trans(Bool, D.Node(y, M2, D.Fd(2n, M2, r), x), D.Node(y, M2, D.Fd(2n, m, r), x), D.Node(y, m, D.Fd(2n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(y, M2, w, x), D.Fd(2n, M2, r), D.Fd(2n, m, r), fd.flag2(m, cf, r)),
          node.flag(y, m, cf, D.Fd(2n, m, r), x)))
    case Bk.Term.Min{+a, +b}:
      +M2 = Flag(m, cf)
      Equal.cong(Bool, Bool, w => Bool.or(U32.is_eq(r, x), w), Bool.or(D.Node(a, M2, D.Fd(2n, M2, r), x), D.Node(b, M2, D.Fd(3n, M2, r), x)), Bool.or(D.Node(a, m, D.Fd(2n, m, r), x), D.Node(b, m, D.Fd(3n, m, r), x)),
        or.cong2(D.Node(a, M2, D.Fd(2n, M2, r), x), D.Node(a, m, D.Fd(2n, m, r), x), D.Node(b, M2, D.Fd(3n, M2, r), x), D.Node(b, m, D.Fd(3n, m, r), x),
        Equal.trans(Bool, D.Node(a, M2, D.Fd(2n, M2, r), x), D.Node(a, M2, D.Fd(2n, m, r), x), D.Node(a, m, D.Fd(2n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(a, M2, w, x), D.Fd(2n, M2, r), D.Fd(2n, m, r), fd.flag2(m, cf, r)),
          node.flag(a, m, cf, D.Fd(2n, m, r), x)),
        Equal.trans(Bool, D.Node(b, M2, D.Fd(3n, M2, r), x), D.Node(b, M2, D.Fd(3n, m, r), x), D.Node(b, m, D.Fd(3n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(b, M2, w, x), D.Fd(3n, M2, r), D.Fd(3n, m, r), fd.flag3(m, cf, r)),
          node.flag(b, m, cf, D.Fd(3n, m, r), x))))
    case Bk.Term.All{+q, +a, +b}:
      +M2 = Flag(m, cf)
      Equal.cong(Bool, Bool, w => Bool.or(U32.is_eq(r, x), w), Bool.or(D.Node(a, M2, D.Fd(2n, M2, r), x), D.Node(b, M2, D.Fd(3n, M2, r), x)), Bool.or(D.Node(a, m, D.Fd(2n, m, r), x), D.Node(b, m, D.Fd(3n, m, r), x)),
        or.cong2(D.Node(a, M2, D.Fd(2n, M2, r), x), D.Node(a, m, D.Fd(2n, m, r), x), D.Node(b, M2, D.Fd(3n, M2, r), x), D.Node(b, m, D.Fd(3n, m, r), x),
        Equal.trans(Bool, D.Node(a, M2, D.Fd(2n, M2, r), x), D.Node(a, M2, D.Fd(2n, m, r), x), D.Node(a, m, D.Fd(2n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(a, M2, w, x), D.Fd(2n, M2, r), D.Fd(2n, m, r), fd.flag2(m, cf, r)),
          node.flag(a, m, cf, D.Fd(2n, m, r), x)),
        Equal.trans(Bool, D.Node(b, M2, D.Fd(3n, M2, r), x), D.Node(b, M2, D.Fd(3n, m, r), x), D.Node(b, m, D.Fd(3n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(b, M2, w, x), D.Fd(3n, M2, r), D.Fd(3n, m, r), fd.flag3(m, cf, r)),
          node.flag(b, m, cf, D.Fd(3n, m, r), x))))
    case Bk.Term.Lam{+q, +f}:
      +M2 = Flag(m, cf)
      Equal.cong(Bool, Bool, w => Bool.or(U32.is_eq(r, x), w), D.Node(f, M2, D.Fd(2n, M2, r), x), D.Node(f, m, D.Fd(2n, m, r), x),
        Equal.trans(Bool, D.Node(f, M2, D.Fd(2n, M2, r), x), D.Node(f, M2, D.Fd(2n, m, r), x), D.Node(f, m, D.Fd(2n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(f, M2, w, x), D.Fd(2n, M2, r), D.Fd(2n, m, r), fd.flag2(m, cf, r)),
          node.flag(f, m, cf, D.Fd(2n, m, r), x)))
    case Bk.Term.App{+q, +f, +y}:
      +M2 = Flag(m, cf)
      Equal.cong(Bool, Bool, w => Bool.or(U32.is_eq(r, x), w), Bool.or(D.Node(f, M2, D.Fd(2n, M2, r), x), D.Node(y, M2, D.Fd(3n, M2, r), x)), Bool.or(D.Node(f, m, D.Fd(2n, m, r), x), D.Node(y, m, D.Fd(3n, m, r), x)),
        or.cong2(D.Node(f, M2, D.Fd(2n, M2, r), x), D.Node(f, m, D.Fd(2n, m, r), x), D.Node(y, M2, D.Fd(3n, M2, r), x), D.Node(y, m, D.Fd(3n, m, r), x),
        Equal.trans(Bool, D.Node(f, M2, D.Fd(2n, M2, r), x), D.Node(f, M2, D.Fd(2n, m, r), x), D.Node(f, m, D.Fd(2n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(f, M2, w, x), D.Fd(2n, M2, r), D.Fd(2n, m, r), fd.flag2(m, cf, r)),
          node.flag(f, m, cf, D.Fd(2n, m, r), x)),
        Equal.trans(Bool, D.Node(y, M2, D.Fd(3n, M2, r), x), D.Node(y, M2, D.Fd(3n, m, r), x), D.Node(y, m, D.Fd(3n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(y, M2, w, x), D.Fd(3n, M2, r), D.Fd(3n, m, r), fd.flag3(m, cf, r)),
          node.flag(y, m, cf, D.Fd(3n, m, r), x))))
    case Bk.Term.Sig{+q, +a, +b}:
      +M2 = Flag(m, cf)
      Equal.cong(Bool, Bool, w => Bool.or(U32.is_eq(r, x), w), Bool.or(D.Node(a, M2, D.Fd(2n, M2, r), x), D.Node(b, M2, D.Fd(3n, M2, r), x)), Bool.or(D.Node(a, m, D.Fd(2n, m, r), x), D.Node(b, m, D.Fd(3n, m, r), x)),
        or.cong2(D.Node(a, M2, D.Fd(2n, M2, r), x), D.Node(a, m, D.Fd(2n, m, r), x), D.Node(b, M2, D.Fd(3n, M2, r), x), D.Node(b, m, D.Fd(3n, m, r), x),
        Equal.trans(Bool, D.Node(a, M2, D.Fd(2n, M2, r), x), D.Node(a, M2, D.Fd(2n, m, r), x), D.Node(a, m, D.Fd(2n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(a, M2, w, x), D.Fd(2n, M2, r), D.Fd(2n, m, r), fd.flag2(m, cf, r)),
          node.flag(a, m, cf, D.Fd(2n, m, r), x)),
        Equal.trans(Bool, D.Node(b, M2, D.Fd(3n, M2, r), x), D.Node(b, M2, D.Fd(3n, m, r), x), D.Node(b, m, D.Fd(3n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(b, M2, w, x), D.Fd(3n, M2, r), D.Fd(3n, m, r), fd.flag3(m, cf, r)),
          node.flag(b, m, cf, D.Fd(3n, m, r), x))))
    case Bk.Term.Tup{+q, +a, +b}:
      +M2 = Flag(m, cf)
      Equal.cong(Bool, Bool, w => Bool.or(U32.is_eq(r, x), w), Bool.or(D.Node(a, M2, D.Fd(2n, M2, r), x), D.Node(b, M2, D.Fd(3n, M2, r), x)), Bool.or(D.Node(a, m, D.Fd(2n, m, r), x), D.Node(b, m, D.Fd(3n, m, r), x)),
        or.cong2(D.Node(a, M2, D.Fd(2n, M2, r), x), D.Node(a, m, D.Fd(2n, m, r), x), D.Node(b, M2, D.Fd(3n, M2, r), x), D.Node(b, m, D.Fd(3n, m, r), x),
        Equal.trans(Bool, D.Node(a, M2, D.Fd(2n, M2, r), x), D.Node(a, M2, D.Fd(2n, m, r), x), D.Node(a, m, D.Fd(2n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(a, M2, w, x), D.Fd(2n, M2, r), D.Fd(2n, m, r), fd.flag2(m, cf, r)),
          node.flag(a, m, cf, D.Fd(2n, m, r), x)),
        Equal.trans(Bool, D.Node(b, M2, D.Fd(3n, M2, r), x), D.Node(b, M2, D.Fd(3n, m, r), x), D.Node(b, m, D.Fd(3n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(b, M2, w, x), D.Fd(3n, M2, r), D.Fd(3n, m, r), fd.flag3(m, cf, r)),
          node.flag(b, m, cf, D.Fd(3n, m, r), x))))
    case Bk.Term.Prj{+h}:
      +M2 = Flag(m, cf)
      Equal.cong(Bool, Bool, w => Bool.or(U32.is_eq(r, x), w), D.Node(h, M2, D.Fd(2n, M2, r), x), D.Node(h, m, D.Fd(2n, m, r), x),
        Equal.trans(Bool, D.Node(h, M2, D.Fd(2n, M2, r), x), D.Node(h, M2, D.Fd(2n, m, r), x), D.Node(h, m, D.Fd(2n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(h, M2, w, x), D.Fd(2n, M2, r), D.Fd(2n, m, r), fd.flag2(m, cf, r)),
          node.flag(h, m, cf, D.Fd(2n, m, r), x)))
    case Bk.Term.Enu{+e}:
      {==}
    case Bk.Term.Lab{+k}:
      {==}
    case Bk.Term.Mat{+k, +h, +o}:
      +M2 = Flag(m, cf)
      Equal.cong(Bool, Bool, w => Bool.or(U32.is_eq(r, x), w), Bool.or(D.Node(h, M2, D.Fd(3n, M2, r), x), D.Node(o, M2, D.Fd(4n, M2, r), x)), Bool.or(D.Node(h, m, D.Fd(3n, m, r), x), D.Node(o, m, D.Fd(4n, m, r), x)),
        or.cong2(D.Node(h, M2, D.Fd(3n, M2, r), x), D.Node(h, m, D.Fd(3n, m, r), x), D.Node(o, M2, D.Fd(4n, M2, r), x), D.Node(o, m, D.Fd(4n, m, r), x),
        Equal.trans(Bool, D.Node(h, M2, D.Fd(3n, M2, r), x), D.Node(h, M2, D.Fd(3n, m, r), x), D.Node(h, m, D.Fd(3n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(h, M2, w, x), D.Fd(3n, M2, r), D.Fd(3n, m, r), fd.flag3(m, cf, r)),
          node.flag(h, m, cf, D.Fd(3n, m, r), x)),
        Equal.trans(Bool, D.Node(o, M2, D.Fd(4n, M2, r), x), D.Node(o, M2, D.Fd(4n, m, r), x), D.Node(o, m, D.Fd(4n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(o, M2, w, x), D.Fd(4n, M2, r), D.Fd(4n, m, r), fd.flag4(m, cf, r)),
          node.flag(o, m, cf, D.Fd(4n, m, r), x))))
    case Bk.Term.Efq{}:
      {==}
    case Bk.Term.Eql{+a, +b, +y}:
      +M2 = Flag(m, cf)
      Equal.cong(Bool, Bool, w => Bool.or(U32.is_eq(r, x), w), Bool.or(D.Node(a, M2, D.Fd(2n, M2, r), x), Bool.or(D.Node(b, M2, D.Fd(3n, M2, r), x), D.Node(y, M2, D.Fd(4n, M2, r), x))), Bool.or(D.Node(a, m, D.Fd(2n, m, r), x), Bool.or(D.Node(b, m, D.Fd(3n, m, r), x), D.Node(y, m, D.Fd(4n, m, r), x))),
        or.cong2(D.Node(a, M2, D.Fd(2n, M2, r), x), D.Node(a, m, D.Fd(2n, m, r), x), Bool.or(D.Node(b, M2, D.Fd(3n, M2, r), x), D.Node(y, M2, D.Fd(4n, M2, r), x)), Bool.or(D.Node(b, m, D.Fd(3n, m, r), x), D.Node(y, m, D.Fd(4n, m, r), x)),
        Equal.trans(Bool, D.Node(a, M2, D.Fd(2n, M2, r), x), D.Node(a, M2, D.Fd(2n, m, r), x), D.Node(a, m, D.Fd(2n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(a, M2, w, x), D.Fd(2n, M2, r), D.Fd(2n, m, r), fd.flag2(m, cf, r)),
          node.flag(a, m, cf, D.Fd(2n, m, r), x)),
        or.cong2(D.Node(b, M2, D.Fd(3n, M2, r), x), D.Node(b, m, D.Fd(3n, m, r), x), D.Node(y, M2, D.Fd(4n, M2, r), x), D.Node(y, m, D.Fd(4n, m, r), x),
        Equal.trans(Bool, D.Node(b, M2, D.Fd(3n, M2, r), x), D.Node(b, M2, D.Fd(3n, m, r), x), D.Node(b, m, D.Fd(3n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(b, M2, w, x), D.Fd(3n, M2, r), D.Fd(3n, m, r), fd.flag3(m, cf, r)),
          node.flag(b, m, cf, D.Fd(3n, m, r), x)),
        Equal.trans(Bool, D.Node(y, M2, D.Fd(4n, M2, r), x), D.Node(y, M2, D.Fd(4n, m, r), x), D.Node(y, m, D.Fd(4n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(y, M2, w, x), D.Fd(4n, M2, r), D.Fd(4n, m, r), fd.flag4(m, cf, r)),
          node.flag(y, m, cf, D.Fd(4n, m, r), x)))))
    case Bk.Term.Rfl{}:
      {==}
    case Bk.Term.Rwt{+e, +p, +f}:
      +M2 = Flag(m, cf)
      Equal.cong(Bool, Bool, w => Bool.or(U32.is_eq(r, x), w), Bool.or(D.Node(e, M2, D.Fd(2n, M2, r), x), Bool.or(D.Node(p, M2, D.Fd(3n, M2, r), x), D.Node(f, M2, D.Fd(4n, M2, r), x))), Bool.or(D.Node(e, m, D.Fd(2n, m, r), x), Bool.or(D.Node(p, m, D.Fd(3n, m, r), x), D.Node(f, m, D.Fd(4n, m, r), x))),
        or.cong2(D.Node(e, M2, D.Fd(2n, M2, r), x), D.Node(e, m, D.Fd(2n, m, r), x), Bool.or(D.Node(p, M2, D.Fd(3n, M2, r), x), D.Node(f, M2, D.Fd(4n, M2, r), x)), Bool.or(D.Node(p, m, D.Fd(3n, m, r), x), D.Node(f, m, D.Fd(4n, m, r), x)),
        Equal.trans(Bool, D.Node(e, M2, D.Fd(2n, M2, r), x), D.Node(e, M2, D.Fd(2n, m, r), x), D.Node(e, m, D.Fd(2n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(e, M2, w, x), D.Fd(2n, M2, r), D.Fd(2n, m, r), fd.flag2(m, cf, r)),
          node.flag(e, m, cf, D.Fd(2n, m, r), x)),
        or.cong2(D.Node(p, M2, D.Fd(3n, M2, r), x), D.Node(p, m, D.Fd(3n, m, r), x), D.Node(f, M2, D.Fd(4n, M2, r), x), D.Node(f, m, D.Fd(4n, m, r), x),
        Equal.trans(Bool, D.Node(p, M2, D.Fd(3n, M2, r), x), D.Node(p, M2, D.Fd(3n, m, r), x), D.Node(p, m, D.Fd(3n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(p, M2, w, x), D.Fd(3n, M2, r), D.Fd(3n, m, r), fd.flag3(m, cf, r)),
          node.flag(p, m, cf, D.Fd(3n, m, r), x)),
        Equal.trans(Bool, D.Node(f, M2, D.Fd(4n, M2, r), x), D.Node(f, M2, D.Fd(4n, m, r), x), D.Node(f, m, D.Fd(4n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(f, M2, w, x), D.Fd(4n, M2, r), D.Fd(4n, m, r), fd.flag4(m, cf, r)),
          node.flag(f, m, cf, D.Fd(4n, m, r), x)))))

def nodes.flag(rs: List<&2, D.Rt>, +m: Cr.Cir.Cells, +cf: U32, +x: U32) -> {D.Nodes(rs, Flag(m, cf), x) == D.Nodes(rs, m, x) : Bool}:
  match rs:
    case Nil{}:
      {==}
    case Con{D.Rt{+r, +u}, +rest}:
      or.cong2(D.Node(u, Flag(m, cf), r, x), D.Node(u, m, r, x), D.Nodes(rest, Flag(m, cf), x), D.Nodes(rest, m, x),
        node.flag(u, m, cf, r, x), nodes.flag(rest, m, cf, x))

def cov.flag(n: Nat, +m: Cr.Cir.Cells, +cf: U32, +c: U32, +rs: List<&2, D.Rt>, +xs: List<&2, U32>) ->
  {D.Cov(n, Flag(m, cf), c, rs, xs) == D.Cov(n, m, c, rs, xs) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+(+k):
      +M2 = Flag(m, cf)
      +RHS = D.Cov(1n+k, m, c, rs, xs)
      %Equal.sym(Bool, D.Fl(M2, c, 1024), D.Fl(m, c, 1024), fl.flag(m, cf, c, 1024, and.dat.st())) :
        {Bool.and(Bool.or(_, Bool.or(D.Nodes(rs, M2, c), D.Mem(xs, c))), D.Cov(k, M2, U32.inc(c), rs, xs)) == RHS : Bool}
      %Equal.sym(Bool, D.Nodes(rs, M2, c), D.Nodes(rs, m, c), nodes.flag(rs, m, cf, c)) :
        {Bool.and(Bool.or(D.Fl(m, c, 1024), Bool.or(_, D.Mem(xs, c))), D.Cov(k, M2, U32.inc(c), rs, xs)) == RHS : Bool}
      %Equal.sym(Bool, D.Cov(k, M2, U32.inc(c), rs, xs), D.Cov(k, m, U32.inc(c), rs, xs), cov.flag(k, m, cf, U32.inc(c), rs, xs)) :
        {Bool.and(Bool.or(D.Fl(m, c, 1024), Bool.or(D.Nodes(rs, m, c), D.Mem(xs, c))), _) == RHS : Bool}
      {==}

def pend.terms.flag(ps: List<&2, U32>, +m: Cr.Cir.Cells, +cf: U32) -> {D.Pend.terms(ps, Flag(m, cf)) == D.Pend.terms(ps, m) : List<&2, U32>}:
  match ps:
    case Nil{}:
      {==}
    case Con{+q, +rest}:
      +M2 = Flag(m, cf)
      %Equal.sym(U32, D.TgW(D.Fd(0n, M2, q)), D.TgW(D.Fd(0n, m, q)), tg.flag(m, cf, q)) :
        {Bool.pick(List<&2, U32>, U32.is_lt(_, 19), Con{q, D.Pend.terms(rest, M2)}, D.Pend.terms(rest, M2)) == D.Pend.terms(Con{q, rest}, m) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, D.Pend.terms(rest, M2), D.Pend.terms(rest, m), pend.terms.flag(rest, m, cf)) :
        {Bool.pick(List<&2, U32>, U32.is_lt(D.TgW(D.Fd(0n, m, q)), 19), Con{q, _}, _) == D.Pend.terms(Con{q, rest}, m) : List<&2, U32>}
      {==}

def frb.flag(kind: D.FK, +m: Cr.Cir.Cells, +cf: U32, +fr: U32, +b: Bk.Term) ->
  {D.Fr.rts.b(Flag(m, cf), fr, kind, b) == D.Fr.rts.b(m, fr, kind, b) : List<&2, D.Rt>}:
  match kind:
    case D.FK.rwt{}:
      %Equal.sym(U32, D.Fd(3n, Flag(m, cf), fr), D.Fd(3n, m, fr), fd.flag3(m, cf, fr)) : {[D.Rt{_, b}] == [D.Rt{D.Fd(3n, m, fr), b}] : List<&2, D.Rt>}
      {==}
    case D.FK.arg{}:
      {==}
    case D.FK.val{}:
      {==}
    case D.FK.fun{}:
      {==}
    case D.FK.let{}:
      {==}
    case D.FK.tupb{}:
      {==}
    case D.FK.tupa{}:
      {==}
    case D.FK.minb{}:
      {==}
    case D.FK.mina{}:
      {==}

def fr.flag(fs: List<&2, D.AF>, +m: Cr.Cir.Cells, +cf: U32, +fr: U32) ->
  D.P2({D.Fr.cells(fs, Flag(m, cf), fr) == D.Fr.cells(fs, m, fr) : List<&2, U32>}, {D.Fr.rts(fs, Flag(m, cf), fr) == D.Fr.rts(fs, m, fr) : List<&2, D.Rt>}):
  match fs:
    case Nil{}:
      ({==}, {==})
    case Con{D.AF{+kind, +q, +k, +a, +b}, +rest}:
      +M2 = Flag(m, cf)
      +f1 = D.Fd(1n, m, fr)
      +ih = fr.flag(rest, m, cf, f1)
      +ihc = D.Ex.fst({D.Fr.cells(rest, M2, f1) == D.Fr.cells(rest, m, f1) : List<&2, U32>}, _ => {D.Fr.rts(rest, M2, f1) == D.Fr.rts(rest, m, f1) : List<&2, D.Rt>}, ih)
      +ihr = D.Ex.snd({D.Fr.cells(rest, M2, f1) == D.Fr.cells(rest, m, f1) : List<&2, U32>}, _ => {D.Fr.rts(rest, M2, f1) == D.Fr.rts(rest, m, f1) : List<&2, D.Rt>}, ih)
      ({(%Equal.sym(U32, D.Fd(1n, M2, fr), f1, fd.flag1(m, cf, fr)) : {Con{fr, D.Fr.cells(rest, M2, _)} == Con{fr, D.Fr.cells(rest, m, f1)} : List<&2, U32>};
          %Equal.sym(List<&2, U32>, D.Fr.cells(rest, M2, f1), D.Fr.cells(rest, m, f1), ihc) : {Con{fr, _} == Con{fr, D.Fr.cells(rest, m, f1)} : List<&2, U32>};
          {==}) : {D.Fr.cells(Con{D.AF{kind, q, k, a, b}, rest}, M2, fr) == D.Fr.cells(Con{D.AF{kind, q, k, a, b}, rest}, m, fr) : List<&2, U32>}},
        {(%Equal.sym(U32, D.Fd(1n, M2, fr), f1, fd.flag1(m, cf, fr)) :
            {Con{D.Rt{D.Fd(2n, M2, fr), a}, List.append(&2, D.Rt, D.Fr.rts.b(M2, fr, kind, b), D.Fr.rts(rest, M2, _))} ==
              Con{D.Rt{D.Fd(2n, m, fr), a}, List.append(&2, D.Rt, D.Fr.rts.b(m, fr, kind, b), D.Fr.rts(rest, m, f1))} : List<&2, D.Rt>};
          %Equal.sym(U32, D.Fd(2n, M2, fr), D.Fd(2n, m, fr), fd.flag2(m, cf, fr)) :
            {Con{D.Rt{_, a}, List.append(&2, D.Rt, D.Fr.rts.b(M2, fr, kind, b), D.Fr.rts(rest, M2, f1))} ==
              Con{D.Rt{D.Fd(2n, m, fr), a}, List.append(&2, D.Rt, D.Fr.rts.b(m, fr, kind, b), D.Fr.rts(rest, m, f1))} : List<&2, D.Rt>};
          %Equal.sym(List<&2, D.Rt>, D.Fr.rts.b(M2, fr, kind, b), D.Fr.rts.b(m, fr, kind, b), frb.flag(kind, m, cf, fr, b)) :
            {Con{D.Rt{D.Fd(2n, m, fr), a}, List.append(&2, D.Rt, _, D.Fr.rts(rest, M2, f1))} ==
              Con{D.Rt{D.Fd(2n, m, fr), a}, List.append(&2, D.Rt, D.Fr.rts.b(m, fr, kind, b), D.Fr.rts(rest, m, f1))} : List<&2, D.Rt>};
          %Equal.sym(List<&2, D.Rt>, D.Fr.rts(rest, M2, f1), D.Fr.rts(rest, m, f1), ihr) :
            {Con{D.Rt{D.Fd(2n, m, fr), a}, List.append(&2, D.Rt, D.Fr.rts.b(m, fr, kind, b), _)} ==
              Con{D.Rt{D.Fd(2n, m, fr), a}, List.append(&2, D.Rt, D.Fr.rts.b(m, fr, kind, b), D.Fr.rts(rest, m, f1))} : List<&2, D.Rt>};
          {==}) : {D.Fr.rts(Con{D.AF{kind, q, k, a, b}, rest}, M2, fr) == D.Fr.rts(Con{D.AF{kind, q, k, a, b}, rest}, m, fr) : List<&2, D.Rt>}})

# Fs's body, by the fields it reads
def FsN(+b: Bool, +mem: Bool, +a: U32, +x2: U32, +x3: U32, +x4: U32, +own: Bool, +tg: U32) -> List<&2, U32>:
  Bool.pick(List<&2, U32>, b, D.Fs.term(a, x2, x3, x4),
    Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_le(32, tg), U32.is_le(tg, 40)), Bool.not(mem)), Con{x2, D.Fs.opt(U32.is_eq(tg, 38), x3, Nil{})},
      Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_eq(tg, 41), own), Bool.not(mem)), [x2], Nil{})))

def fsn.cong(+b: Bool, +mem: Bool, -a: U32, -a2: U32, -x2: U32, -y2: U32, -x3: U32, -y3: U32, -x4: U32, -y4: U32, -o1: Bool, -o2: Bool, +tg: U32,
  ea: {a == a2 : U32}, e2: {x2 == y2 : U32}, e3: {x3 == y3 : U32}, e4: {x4 == y4 : U32}, eo: {o1 == o2 : Bool}) ->
  {FsN(b, mem, a, x2, x3, x4, o1, tg) == FsN(b, mem, a2, y2, y3, y4, o2, tg) : List<&2, U32>}:
  %ea : {FsN(b, mem, a, x2, x3, x4, o1, tg) == FsN(b, mem, _, y2, y3, y4, o2, tg) : List<&2, U32>}
  %e2 : {FsN(b, mem, a, x2, x3, x4, o1, tg) == FsN(b, mem, a, _, y3, y4, o2, tg) : List<&2, U32>}
  %e3 : {FsN(b, mem, a, x2, x3, x4, o1, tg) == FsN(b, mem, a, x2, _, y4, o2, tg) : List<&2, U32>}
  %e4 : {FsN(b, mem, a, x2, x3, x4, o1, tg) == FsN(b, mem, a, x2, x3, _, o2, tg) : List<&2, U32>}
  %eo : {FsN(b, mem, a, x2, x3, x4, o1, tg) == FsN(b, mem, a, x2, x3, x4, _, tg) : List<&2, U32>}
  {==}

def fs.flag(+m: Cr.Cir.Cells, +cf: U32, +ps: List<&2, U32>, +o: U32) -> {D.Fs(Flag(m, cf), ps, o) == D.Fs(m, ps, o) : List<&2, U32>}:
  +M2 = Flag(m, cf)
  +T = D.TgW(D.Fd(0n, m, o))
  %Equal.sym(U32, D.TgW(D.Fd(0n, M2, o)), T, tg.flag(m, cf, o)) :
    {FsN(U32.is_lt(_, 19), D.Mem(ps, o), D.Fd(2n, M2, U32.add(272, _)), D.Fd(2n, M2, o), D.Fd(3n, M2, o), D.Fd(4n, M2, o),
      D.FlW(D.Fd(0n, M2, o), 4096), _) == D.Fs(m, ps, o) : List<&2, U32>}
  fsn.cong(U32.is_lt(T, 19), D.Mem(ps, o), D.Fd(2n, M2, U32.add(272, T)), D.Fd(2n, m, U32.add(272, T)), D.Fd(2n, M2, o), D.Fd(2n, m, o),
    D.Fd(3n, M2, o), D.Fd(3n, m, o), D.Fd(4n, M2, o), D.Fd(4n, m, o), D.FlW(D.Fd(0n, M2, o), 4096), D.FlW(D.Fd(0n, m, o), 4096), T,
    fd.flag2(m, cf, U32.add(272, T)), fd.flag2(m, cf, o), fd.flag3(m, cf, o), fd.flag4(m, cf, o), fl.flag(m, cf, o, 4096, and.dat.own()))

def static.all.flag(ys: List<&2, U32>, +m: Cr.Cir.Cells, +cf: U32) -> {D.All.static(ys, Flag(m, cf)) == D.All.static(ys, m) : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      %Equal.sym(Bool, D.Fl(Flag(m, cf), y, 1024), D.Fl(m, y, 1024), fl.flag(m, cf, y, 1024, and.dat.st())) :
        {Bool.and(_, D.All.static(rest, Flag(m, cf))) == D.All.static(Con{y, rest}, m) : Bool}
      %Equal.sym(Bool, D.All.static(rest, Flag(m, cf)), D.All.static(rest, m), static.all.flag(rest, m, cf)) :
        {Bool.and(D.Fl(m, y, 1024), _) == D.All.static(Con{y, rest}, m) : Bool}
      {==}

def held.all.flag(ys: List<&2, U32>, +m: Cr.Cir.Cells, +cf: U32, +cs: List<&2, U32>, +hc: List<&2, U32>) ->
  {D.All.held(ys, Flag(m, cf), cs, hc) == D.All.held(ys, m, cs, hc) : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      %Equal.sym(Bool, D.Fl(Flag(m, cf), y, 1024), D.Fl(m, y, 1024), fl.flag(m, cf, y, 1024, and.dat.st())) :
        {Bool.and(Bool.or(_, Bool.or(D.Mem(cs, y), D.Mem(hc, y))), D.All.held(rest, Flag(m, cf), cs, hc)) == D.All.held(Con{y, rest}, m, cs, hc) : Bool}
      %Equal.sym(Bool, D.All.held(rest, Flag(m, cf), cs, hc), D.All.held(rest, m, cs, hc), held.all.flag(rest, m, cf, cs, hc)) :
        {Bool.and(Bool.or(D.Fl(m, y, 1024), Bool.or(D.Mem(cs, y), D.Mem(hc, y))), _) == D.All.held(Con{y, rest}, m, cs, hc) : Bool}
      {==}

def clo.flag(n: Nat, +m: Cr.Cir.Cells, +cf: U32, +c: U32, +ps: List<&2, U32>, +cs: List<&2, U32>, +hc: List<&2, U32>) ->
  {D.Clo(n, Flag(m, cf), c, ps, cs, hc) == D.Clo(n, m, c, ps, cs, hc) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+(+k):
      +M2 = Flag(m, cf)
      +RHS = D.Clo(1n+k, m, c, ps, cs, hc)
      %Equal.sym(Bool, D.Fl(M2, c, 1024), D.Fl(m, c, 1024), fl.flag(m, cf, c, 1024, and.dat.st())) :
        {Bool.and(Bool.and(Bool.or(Bool.not(_), D.All.static(D.Fs(M2, ps, c), M2)),
          Bool.or(Bool.not(D.Mem(cs, c)), D.All.held(D.Fs(M2, ps, c), M2, cs, hc))), D.Clo(k, M2, U32.inc(c), ps, cs, hc)) == RHS : Bool}
      %Equal.sym(List<&2, U32>, D.Fs(M2, ps, c), D.Fs(m, ps, c), fs.flag(m, cf, ps, c)) :
        {Bool.and(Bool.and(Bool.or(Bool.not(D.Fl(m, c, 1024)), D.All.static(_, M2)),
          Bool.or(Bool.not(D.Mem(cs, c)), D.All.held(_, M2, cs, hc))), D.Clo(k, M2, U32.inc(c), ps, cs, hc)) == RHS : Bool}
      %Equal.sym(Bool, D.All.static(D.Fs(m, ps, c), M2), D.All.static(D.Fs(m, ps, c), m), static.all.flag(D.Fs(m, ps, c), m, cf)) :
        {Bool.and(Bool.and(Bool.or(Bool.not(D.Fl(m, c, 1024)), _),
          Bool.or(Bool.not(D.Mem(cs, c)), D.All.held(D.Fs(m, ps, c), M2, cs, hc))), D.Clo(k, M2, U32.inc(c), ps, cs, hc)) == RHS : Bool}
      %Equal.sym(Bool, D.All.held(D.Fs(m, ps, c), M2, cs, hc), D.All.held(D.Fs(m, ps, c), m, cs, hc), held.all.flag(D.Fs(m, ps, c), m, cf, cs, hc)) :
        {Bool.and(Bool.and(Bool.or(Bool.not(D.Fl(m, c, 1024)), D.All.static(D.Fs(m, ps, c), m)),
          Bool.or(Bool.not(D.Mem(cs, c)), _)), D.Clo(k, M2, U32.inc(c), ps, cs, hc)) == RHS : Bool}
      %Equal.sym(Bool, D.Clo(k, M2, U32.inc(c), ps, cs, hc), D.Clo(k, m, U32.inc(c), ps, cs, hc), clo.flag(k, m, cf, U32.inc(c), ps, cs, hc)) :
        {Bool.and(Bool.and(Bool.or(Bool.not(D.Fl(m, c, 1024)), D.All.static(D.Fs(m, ps, c), m)),
          Bool.or(Bool.not(D.Mem(cs, c)), D.All.held(D.Fs(m, ps, c), m, cs, hc))), _) == RHS : Bool}
      {==}

# A new cell at next
# ------------------

# (a + 1) - b = (a - b) + 1, when b <= a
def sub.succ(a: Nat, b: Nat, h: N.Le(b, a)) -> {Nat.sub(1n+a, b) == 1n+Nat.sub(a, b) : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({Nat.sub(1n, 1n+q) == 1n+Nat.sub(0n, 1n+q) : Nat}, h)
    case 1n+q 0n:
      {==}
    case 1n+q 1n+r:
      sub.succ(q, r, h)

# the n cells from c end at z: c is z when n is 0
def at.end(+c: U32, +z: U32, hz: {Nat.add(U32.to_nat(c), 0n) == U32.to_nat(z) : Nat}) -> {c == z : U32}:
  D.u32.eq(c, z, D.u.nat.eq(c, z, Equal.trans(Nat, U32.to_nat(c), Nat.add(U32.to_nat(c), 0n), U32.to_nat(z),
    Equal.sym(Nat, Nat.add(U32.to_nat(c), 0n), U32.to_nat(c), N.add_zero(U32.to_nat(c))), hz)))

# and before z, when n is 1 + k
def at.lt(+c: U32, +k: Nat, +z: U32, hz: {Nat.add(U32.to_nat(c), 1n+k) == U32.to_nat(z) : Nat}) -> N.Le(1n+U32.to_nat(c), U32.to_nat(z)):
  N.le_rw_r(1n+U32.to_nat(c), Nat.add(U32.to_nat(c), 1n+k), U32.to_nat(z), hz, N.lt_add(U32.to_nat(c), k))

def at.hw(+c: U32, +k: Nat, +z: U32, hz: {Nat.add(U32.to_nat(c), 1n+k) == U32.to_nat(z) : Nat}) -> N.Le(Nat.add(U32.to_nat(c), 1n+k), U32.to_nat(z)):
  N.le_rw_r(Nat.add(U32.to_nat(c), 1n+k), Nat.add(U32.to_nat(c), 1n+k), U32.to_nat(z), hz, N.le_refl(Nat.add(U32.to_nat(c), 1n+k)))

# the next cell's k cells end at z too
def at.next(+c: U32, +k: Nat, +z: U32, hz: {Nat.add(U32.to_nat(c), 1n+k) == U32.to_nat(z) : Nat}) ->
  {Nat.add(U32.to_nat(U32.inc(c)), k) == U32.to_nat(z) : Nat}:
  +hz2 = hz
  %Equal.sym(Nat, U32.to_nat(U32.inc(c)), 1n+U32.to_nat(c), inc.nat(c, k, z, at.hw(c, k, z, hz2))) : {Nat.add(_, k) == U32.to_nat(z) : Nat}
  Equal.trans(Nat, 1n+Nat.add(U32.to_nat(c), k), Nat.add(U32.to_nat(c), 1n+k), U32.to_nat(z),
    Equal.sym(Nat, Nat.add(U32.to_nat(c), 1n+k), 1n+Nat.add(U32.to_nat(c), k), N.add_succ_r(U32.to_nat(c), k)), hz2)

# a store, at the cell z after the n cells from c, of a cell that is not
# STATIC: one more cell, none more STATIC
def stat.snoc(n: Nat, +m: Cr.Cir.Cells, +c: U32, +z: U32, +x: Cr.Cir.Cell, hz: {Nat.add(U32.to_nat(c), n) == U32.to_nat(z) : Nat},
  hx: {D.FlW(Cr.Cir.Cell.get(0n, x), 1024) == False{} : Bool}) -> {D.Stat(1n+n, Cr.Cir.Cells.set(m, z, x), c) == D.Stat(n, m, c) : Nat}:
  match n:
    case 0n:
      %Equal.sym(U32, c, z, at.end(c, z, hz)) : {Nat.add(D.Nat.of(D.Fl(Cr.Cir.Cells.set(m, z, x), _, 1024)), 0n) == 0n : Nat}
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, x), z), x, D.cl.gs(m, z, x)) :
        {Nat.add(D.Nat.of(U32.is_ne(U32.and(Cr.Cir.Cell.get(0n, _), 1024), 0)), 0n) == 0n : Nat}
      %Equal.sym(Bool, D.FlW(Cr.Cir.Cell.get(0n, x), 1024), False{}, hx) : {Nat.add(D.Nat.of(_), 0n) == 0n : Nat}
      {==}
    case 1n+(+k):
      +hz2 = hz
      +hx2 = hx
      +ne = ne.lt(c, z, at.lt(c, k, z, hz2))
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, x), c), Cr.Cir.Cells.get(m, c), D.cl.go(m, c, z, x, ne)) :
        {Nat.add(D.Nat.of(U32.is_ne(U32.and(Cr.Cir.Cell.get(0n, _), 1024), 0)), D.Stat(1n+k, Cr.Cir.Cells.set(m, z, x), U32.inc(c))) == D.Stat(1n+k, m, c) : Nat}
      %Equal.sym(Nat, D.Stat(1n+k, Cr.Cir.Cells.set(m, z, x), U32.inc(c)), D.Stat(k, m, U32.inc(c)), stat.snoc(k, m, U32.inc(c), z, x, at.next(c, k, z, hz2), hx2)) :
        {Nat.add(D.Nat.of(D.Fl(m, c, 1024)), _) == D.Stat(1n+k, m, c) : Nat}
      {==}

# each pointer below nx is not nx
def lt.neall(L: List<&2, U32>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, h: {D.Lt.all(L, m, im, fi, nx) == True{} : Bool}) ->
  {D.NeAll(L, nx) == True{} : Bool}:
  match L:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      +h2 = h
      +lc = D.and.l(D.LtC(y, Cr.Cir.Cells.get(m, y), im, fi, nx), D.Lt.all(rest, m, im, fi, nx), h2)
      +hy = D.and.l(U32.is_lt(y, nx), U32.is_lt(D.TgW(Cr.Cir.Cell.get(0n, Cr.Cir.Cells.get(m, y))), 19),
        D.and.l(Bool.and(U32.is_lt(y, nx), U32.is_lt(D.TgW(Cr.Cir.Cell.get(0n, Cr.Cir.Cells.get(m, y))), 19)),
          Bool.and(Cr.Cir.is_cell(y, im, fi, nx), Bool.or(D.Own(fi, nx, y), D.FlW(Cr.Cir.Cell.get(0n, Cr.Cir.Cells.get(m, y)), 1024))), lc))
      D.neall.cons(y, nx, rest, ne.lt(y, nx, D.u.lt(y, nx, hy)),
        lt.neall(rest, m, im, fi, nx, D.and.r(D.LtC(y, Cr.Cir.Cells.get(m, y), im, fi, nx), D.Lt.all(rest, m, im, fi, nx), h2)))

# a store at a cell that none of the cells L is keeps their flags
def static.all.set(L: List<&2, U32>, +m: Cr.Cir.Cells, +z: U32, +xc: Cr.Cir.Cell, h: {D.NeAll(L, z) == True{} : Bool}) ->
  {D.All.static(L, Cr.Cir.Cells.set(m, z, xc)) == D.All.static(L, m) : Bool}:
  match L:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      +h2 = h
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, xc), y), Cr.Cir.Cells.get(m, y), D.cl.go(m, y, z, xc, D.neall.hd(y, z, rest, h2))) :
        {Bool.and(U32.is_ne(U32.and(Cr.Cir.Cell.get(0n, _), 1024), 0), D.All.static(rest, Cr.Cir.Cells.set(m, z, xc))) == D.All.static(Con{y, rest}, m) : Bool}
      %Equal.sym(Bool, D.All.static(rest, Cr.Cir.Cells.set(m, z, xc)), D.All.static(rest, m), static.all.set(rest, m, z, xc, D.neall.tl(y, z, rest, h2))) :
        {Bool.and(D.Fl(m, y, 1024), _) == D.All.static(Con{y, rest}, m) : Bool}
      {==}

def held.all.set(L: List<&2, U32>, +m: Cr.Cir.Cells, +z: U32, +xc: Cr.Cir.Cell, +cs: List<&2, U32>, +hc: List<&2, U32>,
  h: {D.NeAll(L, z) == True{} : Bool}) -> {D.All.held(L, Cr.Cir.Cells.set(m, z, xc), cs, hc) == D.All.held(L, m, cs, hc) : Bool}:
  match L:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      +h2 = h
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, xc), y), Cr.Cir.Cells.get(m, y), D.cl.go(m, y, z, xc, D.neall.hd(y, z, rest, h2))) :
        {Bool.and(Bool.or(U32.is_ne(U32.and(Cr.Cir.Cell.get(0n, _), 1024), 0), Bool.or(D.Mem(cs, y), D.Mem(hc, y))), D.All.held(rest, Cr.Cir.Cells.set(m, z, xc), cs, hc)) ==
          D.All.held(Con{y, rest}, m, cs, hc) : Bool}
      %Equal.sym(Bool, D.All.held(rest, Cr.Cir.Cells.set(m, z, xc), cs, hc), D.All.held(rest, m, cs, hc), held.all.set(rest, m, z, xc, cs, hc, D.neall.tl(y, z, rest, h2))) :
        {Bool.and(Bool.or(D.Fl(m, y, 1024), Bool.or(D.Mem(cs, y), D.Mem(hc, y))), _) == D.All.held(Con{y, rest}, m, cs, hc) : Bool}
      {==}

# one more temporary keeps All.held
def held.grow(L: List<&2, U32>, +m: Cr.Cir.Cells, +z: U32, +cs: List<&2, U32>, +hc: List<&2, U32>, h: {D.All.held(L, m, cs, hc) == True{} : Bool}) ->
  {D.All.held(L, m, Con{z, cs}, hc) == True{} : Bool}:
  match L:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      +h2 = h
      D.and.i(Bool.or(D.Fl(m, y, 1024), Bool.or(D.Mem(Con{z, cs}, y), D.Mem(hc, y))), D.All.held(rest, m, Con{z, cs}, hc),
        or.root(D.Fl(m, y, 1024), U32.is_eq(z, y), D.Mem(cs, y), D.Mem(hc, y),
          D.and.l(Bool.or(D.Fl(m, y, 1024), Bool.or(D.Mem(cs, y), D.Mem(hc, y))), D.All.held(rest, m, cs, hc), h2)),
        held.grow(rest, m, z, cs, hc, D.and.r(Bool.or(D.Fl(m, y, 1024), Bool.or(D.Mem(cs, y), D.Mem(hc, y))), D.All.held(rest, m, cs, hc), h2)))

# Fs, by the fields that it reads
def fsn.of(+m: Cr.Cir.Cells, +ps: List<&2, U32>, +o: U32) ->
  {D.Fs(m, ps, o) == FsN(U32.is_lt(D.TgW(D.Fd(0n, m, o)), 19), D.Mem(ps, o), D.Fd(2n, m, U32.add(272, D.TgW(D.Fd(0n, m, o)))), D.Fd(2n, m, o),
    D.Fd(3n, m, o), D.Fd(4n, m, o), D.FlW(D.Fd(0n, m, o), 4096), D.TgW(D.Fd(0n, m, o))) : List<&2, U32>}:
  {==}

# the new cell (zeros) holds no pointer
def fs.zero(+m: Cr.Cir.Cells, +z: U32, h272: {D.Fd(2n, Cr.Cir.Cells.set(m, z, Cr.Cir.Cell.zero()), 272) == 0 : U32}) ->
  {D.Fs(Cr.Cir.Cells.set(m, z, Cr.Cir.Cell.zero()), Nil{}, z) == Nil{} : List<&2, U32>}:
  +M2 = Cr.Cir.Cells.set(m, z, Cr.Cir.Cell.zero())
  +Z = Cr.Cir.Cell.zero()
  %Equal.sym(List<&2, U32>, D.Fs(M2, Nil{}, z), FsN(U32.is_lt(D.TgW(D.Fd(0n, M2, z)), 19), D.Mem(Nil{}, z), D.Fd(2n, M2, U32.add(272, D.TgW(D.Fd(0n, M2, z)))),
      D.Fd(2n, M2, z), D.Fd(3n, M2, z), D.Fd(4n, M2, z), D.FlW(D.Fd(0n, M2, z), 4096), D.TgW(D.Fd(0n, M2, z))), fsn.of(M2, Nil{}, z)) :
    {_ == Nil{} : List<&2, U32>}
  %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, z), Z, D.cl.gs(m, z, Z)) :
    {FsN(U32.is_lt(D.TgW(Cr.Cir.Cell.get(0n, _)), 19), D.Mem(Nil{}, z), D.Fd(2n, M2, U32.add(272, D.TgW(Cr.Cir.Cell.get(0n, _)))),
      Cr.Cir.Cell.get(2n, _), Cr.Cir.Cell.get(3n, _), Cr.Cir.Cell.get(4n, _), D.FlW(Cr.Cir.Cell.get(0n, _), 4096), D.TgW(Cr.Cir.Cell.get(0n, _))) == Nil{} : List<&2, U32>}
  %Equal.sym(U32, D.Fd(2n, M2, 272), 0, h272) :
    {FsN(U32.is_lt(D.TgW(Cr.Cir.Cell.get(0n, Z)), 19), D.Mem(Nil{}, z), _,
      Cr.Cir.Cell.get(2n, Z), Cr.Cir.Cell.get(3n, Z), Cr.Cir.Cell.get(4n, Z), D.FlW(Cr.Cir.Cell.get(0n, Z), 4096), D.TgW(Cr.Cir.Cell.get(0n, Z))) == Nil{} : List<&2, U32>}
  {==}

# a new cell, all zeros, at z after the n cells from c, a temporary: Clo
def clo.fresh(n: Nat, +m: Cr.Cir.Cells, +c: U32, +z: U32, +cs: List<&2, U32>, +hc: List<&2, U32>, +im: U32, +fi: U32,
  hz: {Nat.add(U32.to_nat(c), n) == U32.to_nat(z) : Nat}, htb: {D.TblR(n, m, c, z) == True{} : Bool},
  +h272: {D.Fd(2n, Cr.Cir.Cells.set(m, z, Cr.Cir.Cell.zero()), 272) == 0 : U32},
  hp: {D.Pts(n, m, Nil{}, c, im, fi, z) == True{} : Bool}, h: {D.Clo(n, m, c, Nil{}, cs, hc) == True{} : Bool}) ->
  {D.Clo(1n+n, Cr.Cir.Cells.set(m, z, Cr.Cir.Cell.zero()), c, Nil{}, Con{z, cs}, hc) == True{} : Bool}:
  match n:
    case 0n:
      +M2 = Cr.Cir.Cells.set(m, z, Cr.Cir.Cell.zero())
      %Equal.sym(U32, c, z, at.end(c, z, hz)) : {D.Clo(1n, M2, _, Nil{}, Con{z, cs}, hc) == True{} : Bool}
      %Equal.sym(List<&2, U32>, D.Fs(M2, Nil{}, z), Nil{}, fs.zero(m, z, h272)) :
        {Bool.and(Bool.and(Bool.or(Bool.not(D.Fl(M2, z, 1024)), D.All.static(_, M2)), Bool.or(Bool.not(D.Mem(Con{z, cs}, z)), D.All.held(_, M2, Con{z, cs}, hc))),
          True{}) == True{} : Bool}
      %Equal.sym(Bool, Bool.or(Bool.not(D.Fl(M2, z, 1024)), True{}), True{}, or.true(Bool.not(D.Fl(M2, z, 1024)))) :
        {Bool.and(Bool.and(_, Bool.or(Bool.not(D.Mem(Con{z, cs}, z)), True{})), True{}) == True{} : Bool}
      %Equal.sym(Bool, Bool.or(Bool.not(D.Mem(Con{z, cs}, z)), True{}), True{}, or.true(Bool.not(D.Mem(Con{z, cs}, z)))) :
        {Bool.and(Bool.and(True{}, _), True{}) == True{} : Bool}
      {==}
    case 1n+(+k):
      +M2 = Cr.Cir.Cells.set(m, z, Cr.Cir.Cell.zero())
      +hz2 = hz
      +htb2 = htb
      +hp2 = hp
      +h2 = h
      +ne = ne.lt(c, z, at.lt(c, k, z, hz2))
      +F = D.Fs(m, Nil{}, c)
      +hlt = D.and.l(D.Lt.all(F, m, im, fi, z), D.Pts(k, m, Nil{}, U32.inc(c), im, fi, z), hp2)
      +nl = lt.neall(F, m, im, fi, z, hlt)
      +at = D.and.l(D.Clo.at(m, c, Nil{}, cs, hc), D.Clo(k, m, U32.inc(c), Nil{}, cs, hc), h2)
      +S1 = Bool.or(Bool.not(D.Fl(m, c, 1024)), D.All.static(F, m))
      +S2 = Bool.or(Bool.not(D.Mem(cs, c)), D.All.held(F, m, cs, hc))
      +efs = D.fs.eq(m, z, Cr.Cir.Cell.zero(), Nil{}, c, ne, D.and.l(D.TblAt(m, c, z), D.TblR(k, m, U32.inc(c), z), htb2))
      +efl = {Equal.cong(Cr.Cir.Cell, Bool, y => U32.is_ne(U32.and(Cr.Cir.Cell.get(0n, y), 1024), 0), Cr.Cir.Cells.get(M2, c), Cr.Cir.Cells.get(m, c),
        D.cl.go(m, c, z, Cr.Cir.Cell.zero(), ne)) : {D.Fl(M2, c, 1024) == D.Fl(m, c, 1024) : Bool}}
      D.and.i(D.Clo.at(M2, c, Nil{}, Con{z, cs}, hc), D.Clo(1n+k, M2, U32.inc(c), Nil{}, Con{z, cs}, hc),
        {(%Equal.sym(List<&2, U32>, D.Fs(M2, Nil{}, c), F, efs) :
            {Bool.and(Bool.or(Bool.not(D.Fl(M2, c, 1024)), D.All.static(_, M2)), Bool.or(Bool.not(D.Mem(Con{z, cs}, c)), D.All.held(_, M2, Con{z, cs}, hc))) == True{} : Bool};
          %Equal.sym(Bool, D.Fl(M2, c, 1024), D.Fl(m, c, 1024), efl) :
            {Bool.and(Bool.or(Bool.not(_), D.All.static(F, M2)), Bool.or(Bool.not(D.Mem(Con{z, cs}, c)), D.All.held(F, M2, Con{z, cs}, hc))) == True{} : Bool};
          %Equal.sym(Bool, D.All.static(F, M2), D.All.static(F, m), static.all.set(F, m, z, Cr.Cir.Cell.zero(), nl)) :
            {Bool.and(Bool.or(Bool.not(D.Fl(m, c, 1024)), _), Bool.or(Bool.not(D.Mem(Con{z, cs}, c)), D.All.held(F, M2, Con{z, cs}, hc))) == True{} : Bool};
          %Equal.sym(Bool, D.All.held(F, M2, Con{z, cs}, hc), D.All.held(F, m, Con{z, cs}, hc), held.all.set(F, m, z, Cr.Cir.Cell.zero(), Con{z, cs}, hc, nl)) :
            {Bool.and(S1, Bool.or(Bool.not(D.Mem(Con{z, cs}, c)), _)) == True{} : Bool};
          %Equal.sym(Bool, U32.is_eq(z, c), False{}, D.ne.sym(c, z, ne)) :
            {Bool.and(S1, Bool.or(Bool.not(Bool.or(_, D.Mem(cs, c))), D.All.held(F, m, Con{z, cs}, hc))) == True{} : Bool};
          D.and.i(S1, Bool.or(Bool.not(D.Mem(cs, c)), D.All.held(F, m, Con{z, cs}, hc)), D.and.l(S1, S2, at),
            or.mono.r(Bool.not(D.Mem(cs, c)), D.All.held(F, m, cs, hc), D.All.held(F, m, Con{z, cs}, hc), D.and.r(S1, S2, at),
              e => held.grow(F, m, z, cs, hc, e)))) : {D.Clo.at(M2, c, Nil{}, Con{z, cs}, hc) == True{} : Bool}},
        clo.fresh(k, m, U32.inc(c), z, cs, hc, im, fi, at.next(c, k, z, hz2), D.and.r(D.TblAt(m, c, z), D.TblR(k, m, U32.inc(c), z), htb2), h272,
          D.and.r(D.Lt.all(F, m, im, fi, z), D.Pts(k, m, Nil{}, U32.inc(c), im, fi, z), hp2),
          D.and.r(D.Clo.at(m, c, Nil{}, cs, hc), D.Clo(k, m, U32.inc(c), Nil{}, cs, hc), h2)))

# a store at z after the n cells from c (z no node of the roots): Cov with z among the cells
def cov.fresh(n: Nat, +m: Cr.Cir.Cells, +c: U32, +z: U32, +xc: Cr.Cir.Cell, +rs: List<&2, D.Rt>, +xs: List<&2, U32>,
  hz: {Nat.add(U32.to_nat(c), n) == U32.to_nat(z) : Nat}, +hn: {D.Nodes(rs, m, z) == False{} : Bool},
  h: {D.Cov(n, m, c, rs, xs) == True{} : Bool}) -> {D.Cov(1n+n, Cr.Cir.Cells.set(m, z, xc), c, rs, Con{z, xs}) == True{} : Bool}:
  match n:
    case 0n:
      +M2 = Cr.Cir.Cells.set(m, z, xc)
      %Equal.sym(U32, c, z, at.end(c, z, hz)) : {D.Cov(1n, M2, _, rs, Con{z, xs}) == True{} : Bool}
      %Equal.sym(Bool, U32.is_eq(z, z), True{}, D.u32.refl(z)) :
        {Bool.and(Bool.or(D.Fl(M2, z, 1024), Bool.or(D.Nodes(rs, M2, z), Bool.or(_, D.Mem(xs, z)))), True{}) == True{} : Bool}
      %Equal.sym(Bool, Bool.or(D.Nodes(rs, M2, z), True{}), True{}, or.true(D.Nodes(rs, M2, z))) :
        {Bool.and(Bool.or(D.Fl(M2, z, 1024), _), True{}) == True{} : Bool}
      %Equal.sym(Bool, Bool.or(D.Fl(M2, z, 1024), True{}), True{}, or.true(D.Fl(M2, z, 1024))) : {Bool.and(_, True{}) == True{} : Bool}
      {==}
    case 1n+(+k):
      +M2 = Cr.Cir.Cells.set(m, z, xc)
      +hz2 = hz
      +h2 = h
      +ne = ne.lt(c, z, at.lt(c, k, z, hz2))
      +T0 = Bool.or(D.Fl(m, c, 1024), Bool.or(D.Nodes(rs, m, c), D.Mem(xs, c)))
      +efl = {Equal.cong(Cr.Cir.Cell, Bool, y => U32.is_ne(U32.and(Cr.Cir.Cell.get(0n, y), 1024), 0), Cr.Cir.Cells.get(M2, c), Cr.Cir.Cells.get(m, c),
        D.cl.go(m, c, z, xc, ne)) : {D.Fl(M2, c, 1024) == D.Fl(m, c, 1024) : Bool}}
      D.and.i(Bool.or(D.Fl(M2, c, 1024), Bool.or(D.Nodes(rs, M2, c), Bool.or(U32.is_eq(z, c), D.Mem(xs, c)))), D.Cov(1n+k, M2, U32.inc(c), rs, Con{z, xs}),
        {(%Equal.sym(Bool, D.Fl(M2, c, 1024), D.Fl(m, c, 1024), efl) :
            {Bool.or(_, Bool.or(D.Nodes(rs, M2, c), Bool.or(U32.is_eq(z, c), D.Mem(xs, c)))) == True{} : Bool};
          %Equal.sym(Bool, D.Nodes(rs, M2, c), D.Nodes(rs, m, c), nodes.set(rs, m, z, xc, c, hn)) :
            {Bool.or(D.Fl(m, c, 1024), Bool.or(_, Bool.or(U32.is_eq(z, c), D.Mem(xs, c)))) == True{} : Bool};
          or.cell(D.Fl(m, c, 1024), D.Nodes(rs, m, c), U32.is_eq(z, c), D.Mem(xs, c), D.and.l(T0, D.Cov(k, m, U32.inc(c), rs, xs), h2))) :
          {Bool.or(D.Fl(M2, c, 1024), Bool.or(D.Nodes(rs, M2, c), Bool.or(U32.is_eq(z, c), D.Mem(xs, c)))) == True{} : Bool}},
        cov.fresh(k, m, U32.inc(c), z, xc, rs, xs, at.next(c, k, z, hz2), hn, D.and.r(T0, D.Cov(k, m, U32.inc(c), rs, xs), h2)))

# no zombie cell: no zombie
def zs.nil(zs: List<&2, D.Rt>, h: {D.Rt.cells(zs) == Nil{} : List<&2, U32>}) -> {zs == Nil{} : List<&2, D.Rt>}:
  match zs:
    case Nil{}:
      {==}
    case Con{D.Rt{+c, +u}, +rest}:
      Empty.absurd({Con{D.Rt{c, u}, rest} == Nil{} : List<&2, D.Rt>}, (%h : is.cons(_); Unit{}))

# No store makes a STATIC own cell
# --------------------------------

def stat.at(b: Bool, +m: Cr.Cir.Cells, +z: U32, +x: Cr.Cir.Cell, +c: U32, eb: {U32.is_eq(c, z) == b : Bool},
  hx: {D.FlW(Cr.Cir.Cell.get(0n, x), 1024) == False{} : Bool}) ->
  N.Le(D.Nat.of(D.Fl(Cr.Cir.Cells.set(m, z, x), c, 1024)), D.Nat.of(D.Fl(m, c, 1024))):
  match b:
    case True{}:
      %Equal.sym(U32, c, z, D.u32.eq(c, z, eb)) :
        N.Le(D.Nat.of(D.Fl(Cr.Cir.Cells.set(m, z, x), _, 1024)), D.Nat.of(D.Fl(m, c, 1024)))
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, x), z), x, D.cl.gs(m, z, x)) :
        N.Le(D.Nat.of(U32.is_ne(U32.and(Cr.Cir.Cell.get(0n, _), 1024), 0)), D.Nat.of(D.Fl(m, c, 1024)))
      %Equal.sym(Bool, D.FlW(Cr.Cir.Cell.get(0n, x), 1024), False{}, hx) : N.Le(D.Nat.of(_), D.Nat.of(D.Fl(m, c, 1024)))
      N.le_zero(D.Nat.of(D.Fl(m, c, 1024)))
    case False{}:
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, x), c), Cr.Cir.Cells.get(m, c), D.cl.go(m, c, z, x, eb)) :
        N.Le(D.Nat.of(U32.is_ne(U32.and(Cr.Cir.Cell.get(0n, _), 1024), 0)), D.Nat.of(D.Fl(m, c, 1024)))
      N.le_refl(D.Nat.of(D.Fl(m, c, 1024)))

# a store of a cell that is not STATIC: no more STATIC cells
def stat.set(n: Nat, +m: Cr.Cir.Cells, +c: U32, +z: U32, +x: Cr.Cir.Cell,
  hx: {D.FlW(Cr.Cir.Cell.get(0n, x), 1024) == False{} : Bool}) ->
  N.Le(D.Stat(n, Cr.Cir.Cells.set(m, z, x), c), D.Stat(n, m, c)):
  match n:
    case 0n:
      Unit{}
    case 1n+(+k):
      +hx2 = hx
      N.add_mono(D.Nat.of(D.Fl(Cr.Cir.Cells.set(m, z, x), c, 1024)), D.Nat.of(D.Fl(m, c, 1024)),
        D.Stat(k, Cr.Cir.Cells.set(m, z, x), U32.inc(c)), D.Stat(k, m, U32.inc(c)),
        stat.at(U32.is_eq(c, z), m, z, x, c, {==}, hx2), stat.set(k, m, U32.inc(c), z, x, hx2))

# stores to field 1: the same STATIC cells
def stat.put1(n: Nat, +ws: List<&2, D.W1>, +m: Cr.Cir.Cells, +c: U32) ->
  {D.Stat(n, D.Put1(ws, m), c) == D.Stat(n, m, c) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+(+k):
      +M2 = D.Put1(ws, m)
      %D.put1.f0(ws, m, c) :
        {Nat.add(D.Nat.of(U32.is_ne(U32.and(D.Fd(0n, M2, c), 1024), 0)), D.Stat(k, M2, U32.inc(c))) ==
          Nat.add(D.Nat.of(U32.is_ne(U32.and(_, 1024), 0)), D.Stat(k, m, U32.inc(c))) : Nat}
      %stat.put1(k, ws, m, U32.inc(c)) :
        {Nat.add(D.Nat.of(U32.is_ne(U32.and(D.Fd(0n, M2, c), 1024), 0)), D.Stat(k, M2, U32.inc(c))) ==
          Nat.add(D.Nat.of(U32.is_ne(U32.and(D.Fd(0n, M2, c), 1024), 0)), _) : Nat}
      {==}

# the flag DATA of the cell z: the same STATIC cells
def stat.flag(n: Nat, +m: Cr.Cir.Cells, +c: U32, +z: U32) ->
  {D.Stat(n, Cr.Cir.Cells.set(m, z, Cr.Cir.Cell.set(0n, Cr.Cir.Cells.get(m, z), U32.or(D.Fd(0n, m, z), 512))), c) ==
    D.Stat(n, m, c) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+(+k):
      %Equal.sym(Bool, D.Fl(Flag(m, z), c, 1024), D.Fl(m, c, 1024), fl.flag(m, z, c, 1024, and.dat.st())) :
        {Nat.add(D.Nat.of(_), D.Stat(k, Flag(m, z), U32.inc(c))) == D.Stat(1n+k, m, c) : Nat}
      %Equal.sym(Nat, D.Stat(k, Flag(m, z), U32.inc(c)), D.Stat(k, m, U32.inc(c)), stat.flag(k, m, U32.inc(c), z)) :
        {Nat.add(D.Nat.of(D.Fl(m, c, 1024)), _) == D.Stat(1n+k, m, c) : Nat}
      {==}

# a new cell, all zeros, at next nx (from fi on, below the cell e): one more
# own cell, not STATIC
def stat.fresh(+m: Cr.Cir.Cells, +nx: U32, +fi: U32, +e: U32, hfn: {U32.is_le(fi, nx) == True{} : Bool},
  hl: {U32.is_lt(nx, e) == True{} : Bool}) ->
  {D.Stat(Nat.sub(U32.to_nat(U32.inc(nx)), U32.to_nat(fi)), Cr.Cir.Cells.set(m, nx, Cr.Cir.Cell.zero()), fi) ==
    D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi) : Nat}:
  +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
  +hl2 = hl
  +le = D.u.le(fi, nx, hfn)
  %Equal.sym(Nat, U32.to_nat(U32.inc(nx)), 1n+U32.to_nat(nx), D.u.inc(nx, e, D.u.lt(nx, e, hl2))) :
    {D.Stat(Nat.sub(_, U32.to_nat(fi)), Cr.Cir.Cells.set(m, nx, Cr.Cir.Cell.zero()), fi) == D.Stat(n, m, fi) : Nat}
  %Equal.sym(Nat, Nat.sub(1n+U32.to_nat(nx), U32.to_nat(fi)), 1n+n, sub.succ(U32.to_nat(nx), U32.to_nat(fi), le)) :
    {D.Stat(_, Cr.Cir.Cells.set(m, nx, Cr.Cir.Cell.zero()), fi) == D.Stat(n, m, fi) : Nat}
  stat.snoc(n, m, fi, nx, Cr.Cir.Cell.zero(), D.add.sub(U32.to_nat(fi), U32.to_nat(nx), le), {==})

# Stores to field 1
# -----------------

# each of the cells xs is none of ys
def Outs(xs: List<&2, U32>, +ys: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, rest}:
      Bool.and(Bool.not(D.Mem(ys, x)), Outs(rest, ys))

# stores to field 1 keep which cells are nodes of a term (Node reads fields 2 to 4)
def node.put1(t: Bk.Term, +ws: List<&2, D.W1>, +m: Cr.Cir.Cells, +r: U32, +x: U32) ->
  {D.Node(t, D.Put1(ws, m), r, x) == D.Node(t, m, r, x) : Bool}:
  match t:
    case Bk.Term.Var{+i}:
      {==}
    case Bk.Term.Ref{+k}:
      {==}
    case Bk.Term.Ann{+y, +z}:
      +M2 = D.Put1(ws, m)
      Equal.cong(Bool, Bool, w => Bool.or(U32.is_eq(r, x), w), Bool.or(D.Node(y, M2, D.Fd(2n, M2, r), x), D.Node(z, M2, D.Fd(3n, M2, r), x)), Bool.or(D.Node(y, m, D.Fd(2n, m, r), x), D.Node(z, m, D.Fd(3n, m, r), x)),
        or.cong2(D.Node(y, M2, D.Fd(2n, M2, r), x), D.Node(y, m, D.Fd(2n, m, r), x), D.Node(z, M2, D.Fd(3n, M2, r), x), D.Node(z, m, D.Fd(3n, m, r), x),
        Equal.trans(Bool, D.Node(y, M2, D.Fd(2n, M2, r), x), D.Node(y, M2, D.Fd(2n, m, r), x), D.Node(y, m, D.Fd(2n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(y, M2, w, x), D.Fd(2n, M2, r), D.Fd(2n, m, r), D.put1.f2(ws, m, r)),
          node.put1(y, ws, m, D.Fd(2n, m, r), x)),
        Equal.trans(Bool, D.Node(z, M2, D.Fd(3n, M2, r), x), D.Node(z, M2, D.Fd(3n, m, r), x), D.Node(z, m, D.Fd(3n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(z, M2, w, x), D.Fd(3n, M2, r), D.Fd(3n, m, r), D.put1.f3(ws, m, r)),
          node.put1(z, ws, m, D.Fd(3n, m, r), x))))
    case Bk.Term.Let{+q, +v, +f}:
      +M2 = D.Put1(ws, m)
      Equal.cong(Bool, Bool, w => Bool.or(U32.is_eq(r, x), w), Bool.or(D.Node(v, M2, D.Fd(2n, M2, r), x), D.Node(f, M2, D.Fd(3n, M2, r), x)), Bool.or(D.Node(v, m, D.Fd(2n, m, r), x), D.Node(f, m, D.Fd(3n, m, r), x)),
        or.cong2(D.Node(v, M2, D.Fd(2n, M2, r), x), D.Node(v, m, D.Fd(2n, m, r), x), D.Node(f, M2, D.Fd(3n, M2, r), x), D.Node(f, m, D.Fd(3n, m, r), x),
        Equal.trans(Bool, D.Node(v, M2, D.Fd(2n, M2, r), x), D.Node(v, M2, D.Fd(2n, m, r), x), D.Node(v, m, D.Fd(2n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(v, M2, w, x), D.Fd(2n, M2, r), D.Fd(2n, m, r), D.put1.f2(ws, m, r)),
          node.put1(v, ws, m, D.Fd(2n, m, r), x)),
        Equal.trans(Bool, D.Node(f, M2, D.Fd(3n, M2, r), x), D.Node(f, M2, D.Fd(3n, m, r), x), D.Node(f, m, D.Fd(3n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(f, M2, w, x), D.Fd(3n, M2, r), D.Fd(3n, m, r), D.put1.f3(ws, m, r)),
          node.put1(f, ws, m, D.Fd(3n, m, r), x))))
    case Bk.Term.Typ{+y}:
      +M2 = D.Put1(ws, m)
      Equal.cong(Bool, Bool, w => Bool.or(U32.is_eq(r, x), w), D.Node(y, M2, D.Fd(2n, M2, r), x), D.Node(y, m, D.Fd(2n, m, r), x),
        Equal.trans(Bool, D.Node(y, M2, D.Fd(2n, M2, r), x), D.Node(y, M2, D.Fd(2n, m, r), x), D.Node(y, m, D.Fd(2n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(y, M2, w, x), D.Fd(2n, M2, r), D.Fd(2n, m, r), D.put1.f2(ws, m, r)),
          node.put1(y, ws, m, D.Fd(2n, m, r), x)))
    case Bk.Term.Min{+a, +b}:
      +M2 = D.Put1(ws, m)
      Equal.cong(Bool, Bool, w => Bool.or(U32.is_eq(r, x), w), Bool.or(D.Node(a, M2, D.Fd(2n, M2, r), x), D.Node(b, M2, D.Fd(3n, M2, r), x)), Bool.or(D.Node(a, m, D.Fd(2n, m, r), x), D.Node(b, m, D.Fd(3n, m, r), x)),
        or.cong2(D.Node(a, M2, D.Fd(2n, M2, r), x), D.Node(a, m, D.Fd(2n, m, r), x), D.Node(b, M2, D.Fd(3n, M2, r), x), D.Node(b, m, D.Fd(3n, m, r), x),
        Equal.trans(Bool, D.Node(a, M2, D.Fd(2n, M2, r), x), D.Node(a, M2, D.Fd(2n, m, r), x), D.Node(a, m, D.Fd(2n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(a, M2, w, x), D.Fd(2n, M2, r), D.Fd(2n, m, r), D.put1.f2(ws, m, r)),
          node.put1(a, ws, m, D.Fd(2n, m, r), x)),
        Equal.trans(Bool, D.Node(b, M2, D.Fd(3n, M2, r), x), D.Node(b, M2, D.Fd(3n, m, r), x), D.Node(b, m, D.Fd(3n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(b, M2, w, x), D.Fd(3n, M2, r), D.Fd(3n, m, r), D.put1.f3(ws, m, r)),
          node.put1(b, ws, m, D.Fd(3n, m, r), x))))
    case Bk.Term.All{+q, +a, +b}:
      +M2 = D.Put1(ws, m)
      Equal.cong(Bool, Bool, w => Bool.or(U32.is_eq(r, x), w), Bool.or(D.Node(a, M2, D.Fd(2n, M2, r), x), D.Node(b, M2, D.Fd(3n, M2, r), x)), Bool.or(D.Node(a, m, D.Fd(2n, m, r), x), D.Node(b, m, D.Fd(3n, m, r), x)),
        or.cong2(D.Node(a, M2, D.Fd(2n, M2, r), x), D.Node(a, m, D.Fd(2n, m, r), x), D.Node(b, M2, D.Fd(3n, M2, r), x), D.Node(b, m, D.Fd(3n, m, r), x),
        Equal.trans(Bool, D.Node(a, M2, D.Fd(2n, M2, r), x), D.Node(a, M2, D.Fd(2n, m, r), x), D.Node(a, m, D.Fd(2n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(a, M2, w, x), D.Fd(2n, M2, r), D.Fd(2n, m, r), D.put1.f2(ws, m, r)),
          node.put1(a, ws, m, D.Fd(2n, m, r), x)),
        Equal.trans(Bool, D.Node(b, M2, D.Fd(3n, M2, r), x), D.Node(b, M2, D.Fd(3n, m, r), x), D.Node(b, m, D.Fd(3n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(b, M2, w, x), D.Fd(3n, M2, r), D.Fd(3n, m, r), D.put1.f3(ws, m, r)),
          node.put1(b, ws, m, D.Fd(3n, m, r), x))))
    case Bk.Term.Lam{+q, +f}:
      +M2 = D.Put1(ws, m)
      Equal.cong(Bool, Bool, w => Bool.or(U32.is_eq(r, x), w), D.Node(f, M2, D.Fd(2n, M2, r), x), D.Node(f, m, D.Fd(2n, m, r), x),
        Equal.trans(Bool, D.Node(f, M2, D.Fd(2n, M2, r), x), D.Node(f, M2, D.Fd(2n, m, r), x), D.Node(f, m, D.Fd(2n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(f, M2, w, x), D.Fd(2n, M2, r), D.Fd(2n, m, r), D.put1.f2(ws, m, r)),
          node.put1(f, ws, m, D.Fd(2n, m, r), x)))
    case Bk.Term.App{+q, +f, +y}:
      +M2 = D.Put1(ws, m)
      Equal.cong(Bool, Bool, w => Bool.or(U32.is_eq(r, x), w), Bool.or(D.Node(f, M2, D.Fd(2n, M2, r), x), D.Node(y, M2, D.Fd(3n, M2, r), x)), Bool.or(D.Node(f, m, D.Fd(2n, m, r), x), D.Node(y, m, D.Fd(3n, m, r), x)),
        or.cong2(D.Node(f, M2, D.Fd(2n, M2, r), x), D.Node(f, m, D.Fd(2n, m, r), x), D.Node(y, M2, D.Fd(3n, M2, r), x), D.Node(y, m, D.Fd(3n, m, r), x),
        Equal.trans(Bool, D.Node(f, M2, D.Fd(2n, M2, r), x), D.Node(f, M2, D.Fd(2n, m, r), x), D.Node(f, m, D.Fd(2n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(f, M2, w, x), D.Fd(2n, M2, r), D.Fd(2n, m, r), D.put1.f2(ws, m, r)),
          node.put1(f, ws, m, D.Fd(2n, m, r), x)),
        Equal.trans(Bool, D.Node(y, M2, D.Fd(3n, M2, r), x), D.Node(y, M2, D.Fd(3n, m, r), x), D.Node(y, m, D.Fd(3n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(y, M2, w, x), D.Fd(3n, M2, r), D.Fd(3n, m, r), D.put1.f3(ws, m, r)),
          node.put1(y, ws, m, D.Fd(3n, m, r), x))))
    case Bk.Term.Sig{+q, +a, +b}:
      +M2 = D.Put1(ws, m)
      Equal.cong(Bool, Bool, w => Bool.or(U32.is_eq(r, x), w), Bool.or(D.Node(a, M2, D.Fd(2n, M2, r), x), D.Node(b, M2, D.Fd(3n, M2, r), x)), Bool.or(D.Node(a, m, D.Fd(2n, m, r), x), D.Node(b, m, D.Fd(3n, m, r), x)),
        or.cong2(D.Node(a, M2, D.Fd(2n, M2, r), x), D.Node(a, m, D.Fd(2n, m, r), x), D.Node(b, M2, D.Fd(3n, M2, r), x), D.Node(b, m, D.Fd(3n, m, r), x),
        Equal.trans(Bool, D.Node(a, M2, D.Fd(2n, M2, r), x), D.Node(a, M2, D.Fd(2n, m, r), x), D.Node(a, m, D.Fd(2n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(a, M2, w, x), D.Fd(2n, M2, r), D.Fd(2n, m, r), D.put1.f2(ws, m, r)),
          node.put1(a, ws, m, D.Fd(2n, m, r), x)),
        Equal.trans(Bool, D.Node(b, M2, D.Fd(3n, M2, r), x), D.Node(b, M2, D.Fd(3n, m, r), x), D.Node(b, m, D.Fd(3n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(b, M2, w, x), D.Fd(3n, M2, r), D.Fd(3n, m, r), D.put1.f3(ws, m, r)),
          node.put1(b, ws, m, D.Fd(3n, m, r), x))))
    case Bk.Term.Tup{+q, +a, +b}:
      +M2 = D.Put1(ws, m)
      Equal.cong(Bool, Bool, w => Bool.or(U32.is_eq(r, x), w), Bool.or(D.Node(a, M2, D.Fd(2n, M2, r), x), D.Node(b, M2, D.Fd(3n, M2, r), x)), Bool.or(D.Node(a, m, D.Fd(2n, m, r), x), D.Node(b, m, D.Fd(3n, m, r), x)),
        or.cong2(D.Node(a, M2, D.Fd(2n, M2, r), x), D.Node(a, m, D.Fd(2n, m, r), x), D.Node(b, M2, D.Fd(3n, M2, r), x), D.Node(b, m, D.Fd(3n, m, r), x),
        Equal.trans(Bool, D.Node(a, M2, D.Fd(2n, M2, r), x), D.Node(a, M2, D.Fd(2n, m, r), x), D.Node(a, m, D.Fd(2n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(a, M2, w, x), D.Fd(2n, M2, r), D.Fd(2n, m, r), D.put1.f2(ws, m, r)),
          node.put1(a, ws, m, D.Fd(2n, m, r), x)),
        Equal.trans(Bool, D.Node(b, M2, D.Fd(3n, M2, r), x), D.Node(b, M2, D.Fd(3n, m, r), x), D.Node(b, m, D.Fd(3n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(b, M2, w, x), D.Fd(3n, M2, r), D.Fd(3n, m, r), D.put1.f3(ws, m, r)),
          node.put1(b, ws, m, D.Fd(3n, m, r), x))))
    case Bk.Term.Prj{+h}:
      +M2 = D.Put1(ws, m)
      Equal.cong(Bool, Bool, w => Bool.or(U32.is_eq(r, x), w), D.Node(h, M2, D.Fd(2n, M2, r), x), D.Node(h, m, D.Fd(2n, m, r), x),
        Equal.trans(Bool, D.Node(h, M2, D.Fd(2n, M2, r), x), D.Node(h, M2, D.Fd(2n, m, r), x), D.Node(h, m, D.Fd(2n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(h, M2, w, x), D.Fd(2n, M2, r), D.Fd(2n, m, r), D.put1.f2(ws, m, r)),
          node.put1(h, ws, m, D.Fd(2n, m, r), x)))
    case Bk.Term.Enu{+e}:
      {==}
    case Bk.Term.Lab{+k}:
      {==}
    case Bk.Term.Mat{+k, +h, +o}:
      +M2 = D.Put1(ws, m)
      Equal.cong(Bool, Bool, w => Bool.or(U32.is_eq(r, x), w), Bool.or(D.Node(h, M2, D.Fd(3n, M2, r), x), D.Node(o, M2, D.Fd(4n, M2, r), x)), Bool.or(D.Node(h, m, D.Fd(3n, m, r), x), D.Node(o, m, D.Fd(4n, m, r), x)),
        or.cong2(D.Node(h, M2, D.Fd(3n, M2, r), x), D.Node(h, m, D.Fd(3n, m, r), x), D.Node(o, M2, D.Fd(4n, M2, r), x), D.Node(o, m, D.Fd(4n, m, r), x),
        Equal.trans(Bool, D.Node(h, M2, D.Fd(3n, M2, r), x), D.Node(h, M2, D.Fd(3n, m, r), x), D.Node(h, m, D.Fd(3n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(h, M2, w, x), D.Fd(3n, M2, r), D.Fd(3n, m, r), D.put1.f3(ws, m, r)),
          node.put1(h, ws, m, D.Fd(3n, m, r), x)),
        Equal.trans(Bool, D.Node(o, M2, D.Fd(4n, M2, r), x), D.Node(o, M2, D.Fd(4n, m, r), x), D.Node(o, m, D.Fd(4n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(o, M2, w, x), D.Fd(4n, M2, r), D.Fd(4n, m, r), D.put1.f4(ws, m, r)),
          node.put1(o, ws, m, D.Fd(4n, m, r), x))))
    case Bk.Term.Efq{}:
      {==}
    case Bk.Term.Eql{+a, +b, +y}:
      +M2 = D.Put1(ws, m)
      Equal.cong(Bool, Bool, w => Bool.or(U32.is_eq(r, x), w), Bool.or(D.Node(a, M2, D.Fd(2n, M2, r), x), Bool.or(D.Node(b, M2, D.Fd(3n, M2, r), x), D.Node(y, M2, D.Fd(4n, M2, r), x))), Bool.or(D.Node(a, m, D.Fd(2n, m, r), x), Bool.or(D.Node(b, m, D.Fd(3n, m, r), x), D.Node(y, m, D.Fd(4n, m, r), x))),
        or.cong2(D.Node(a, M2, D.Fd(2n, M2, r), x), D.Node(a, m, D.Fd(2n, m, r), x), Bool.or(D.Node(b, M2, D.Fd(3n, M2, r), x), D.Node(y, M2, D.Fd(4n, M2, r), x)), Bool.or(D.Node(b, m, D.Fd(3n, m, r), x), D.Node(y, m, D.Fd(4n, m, r), x)),
        Equal.trans(Bool, D.Node(a, M2, D.Fd(2n, M2, r), x), D.Node(a, M2, D.Fd(2n, m, r), x), D.Node(a, m, D.Fd(2n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(a, M2, w, x), D.Fd(2n, M2, r), D.Fd(2n, m, r), D.put1.f2(ws, m, r)),
          node.put1(a, ws, m, D.Fd(2n, m, r), x)),
        or.cong2(D.Node(b, M2, D.Fd(3n, M2, r), x), D.Node(b, m, D.Fd(3n, m, r), x), D.Node(y, M2, D.Fd(4n, M2, r), x), D.Node(y, m, D.Fd(4n, m, r), x),
        Equal.trans(Bool, D.Node(b, M2, D.Fd(3n, M2, r), x), D.Node(b, M2, D.Fd(3n, m, r), x), D.Node(b, m, D.Fd(3n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(b, M2, w, x), D.Fd(3n, M2, r), D.Fd(3n, m, r), D.put1.f3(ws, m, r)),
          node.put1(b, ws, m, D.Fd(3n, m, r), x)),
        Equal.trans(Bool, D.Node(y, M2, D.Fd(4n, M2, r), x), D.Node(y, M2, D.Fd(4n, m, r), x), D.Node(y, m, D.Fd(4n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(y, M2, w, x), D.Fd(4n, M2, r), D.Fd(4n, m, r), D.put1.f4(ws, m, r)),
          node.put1(y, ws, m, D.Fd(4n, m, r), x)))))
    case Bk.Term.Rfl{}:
      {==}
    case Bk.Term.Rwt{+e, +p, +f}:
      +M2 = D.Put1(ws, m)
      Equal.cong(Bool, Bool, w => Bool.or(U32.is_eq(r, x), w), Bool.or(D.Node(e, M2, D.Fd(2n, M2, r), x), Bool.or(D.Node(p, M2, D.Fd(3n, M2, r), x), D.Node(f, M2, D.Fd(4n, M2, r), x))), Bool.or(D.Node(e, m, D.Fd(2n, m, r), x), Bool.or(D.Node(p, m, D.Fd(3n, m, r), x), D.Node(f, m, D.Fd(4n, m, r), x))),
        or.cong2(D.Node(e, M2, D.Fd(2n, M2, r), x), D.Node(e, m, D.Fd(2n, m, r), x), Bool.or(D.Node(p, M2, D.Fd(3n, M2, r), x), D.Node(f, M2, D.Fd(4n, M2, r), x)), Bool.or(D.Node(p, m, D.Fd(3n, m, r), x), D.Node(f, m, D.Fd(4n, m, r), x)),
        Equal.trans(Bool, D.Node(e, M2, D.Fd(2n, M2, r), x), D.Node(e, M2, D.Fd(2n, m, r), x), D.Node(e, m, D.Fd(2n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(e, M2, w, x), D.Fd(2n, M2, r), D.Fd(2n, m, r), D.put1.f2(ws, m, r)),
          node.put1(e, ws, m, D.Fd(2n, m, r), x)),
        or.cong2(D.Node(p, M2, D.Fd(3n, M2, r), x), D.Node(p, m, D.Fd(3n, m, r), x), D.Node(f, M2, D.Fd(4n, M2, r), x), D.Node(f, m, D.Fd(4n, m, r), x),
        Equal.trans(Bool, D.Node(p, M2, D.Fd(3n, M2, r), x), D.Node(p, M2, D.Fd(3n, m, r), x), D.Node(p, m, D.Fd(3n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(p, M2, w, x), D.Fd(3n, M2, r), D.Fd(3n, m, r), D.put1.f3(ws, m, r)),
          node.put1(p, ws, m, D.Fd(3n, m, r), x)),
        Equal.trans(Bool, D.Node(f, M2, D.Fd(4n, M2, r), x), D.Node(f, M2, D.Fd(4n, m, r), x), D.Node(f, m, D.Fd(4n, m, r), x),
          Equal.cong(U32, Bool, w => D.Node(f, M2, w, x), D.Fd(4n, M2, r), D.Fd(4n, m, r), D.put1.f4(ws, m, r)),
          node.put1(f, ws, m, D.Fd(4n, m, r), x)))))

# a part of a cell after stores to field 1: its STATIC flag, and its term
def part.put1(+dk: Bool, +ds: List<&2, Bk.Def>, +ws: List<&2, D.W1>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +y: U32, -t: Bk.Term,
  ih: D.IsCK(dk, ds, D.Put1(ws, m), im, fi, nx, ks, img, y, Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, y), D.Fd(1n, D.Put1(ws, m), y)), t),
  sp: D.Sp(fi, nx, c, Cr.Cir.Cells.get(m, y))) ->
  D.P2(D.Sp(fi, nx, c, Cr.Cir.Cells.get(D.Put1(ws, m), y)), D.IsCK(dk, ds, D.Put1(ws, m), im, fi, nx, ks, img, y, Cr.Cir.Cells.get(D.Put1(ws, m), y), t)):
  (D.sp.at0(fi, nx, c, Cr.Cir.Cells.get(D.Put1(ws, m), y), Cr.Cir.Cells.get(m, y), D.put1.f0(ws, m, y), sp),
    D.isc.atk(dk, ds, D.Put1(ws, m), im, fi, nx, ks, img, y, Cr.Cir.Cells.get(D.Put1(ws, m), y),
      Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, y), D.Fd(1n, D.Put1(ws, m), y)), t, D.put1.at(ws, m, y), ih))

# a cell whose field 1 changed, in the cells after stores to field 1: the
# same term (IsCK reads fields 0, 2, 3 and 4)
def isk.put1(t: Bk.Term, +dk: Bool, +ds: List<&2, Bk.Def>, +ws: List<&2, D.W1>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, x: Cr.Cir.Cell, +w: U32,
  hx: D.IsCK(dk, ds, m, im, fi, nx, ks, img, c, x, t)) ->
  D.IsCK(dk, ds, D.Put1(ws, m), im, fi, nx, ks, img, c, Cr.Cir.Cell.set(1n, x, w), t):
  match t:
    case Bk.Term.Var{+i}:
      match x:
        case Cr.Cir.Cell{+c0, c1, +c2, +c3, +c4}:
          hx
    case Bk.Term.Ref{+k}:
      match x:
        case Cr.Cir.Cell{+c0, c1, +c2, +c3, +c4}:
          hx
    case Bk.Term.Ann{+y, +z}:
      match x:
        case Cr.Cir.Cell{+c0, c1, +c2, +c3, +c4}:
          match hx:
            case Tuple{nd, Tuple{Tuple{sp1, h1}, Tuple{sp2, h2}}}:
              (nd, (part.put1(dk, ds, ws, m, im, fi, nx, ks, img, c, c2, y,
              isk.put1(y, dk, ds, ws, m, im, fi, nx, ks, img, c2, Cr.Cir.Cells.get(m, c2), D.Fd(1n, D.Put1(ws, m), c2), h1), sp1),
                part.put1(dk, ds, ws, m, im, fi, nx, ks, img, c, c3, z,
              isk.put1(z, dk, ds, ws, m, im, fi, nx, ks, img, c3, Cr.Cir.Cells.get(m, c3), D.Fd(1n, D.Put1(ws, m), c3), h2), sp2)))
    case Bk.Term.Let{+q, +v, +f}:
      match x:
        case Cr.Cir.Cell{+c0, c1, +c2, +c3, +c4}:
          match hx:
            case Tuple{nd, Tuple{qn, Tuple{Tuple{sp1, h1}, Tuple{sp2, h2}}}}:
              (nd, (qn, (part.put1(dk, ds, ws, m, im, fi, nx, ks, img, c, c2, v,
              isk.put1(v, dk, ds, ws, m, im, fi, nx, ks, img, c2, Cr.Cir.Cells.get(m, c2), D.Fd(1n, D.Put1(ws, m), c2), h1), sp1),
                part.put1(dk, ds, ws, m, im, fi, nx, ks, img, c, c3, f,
              isk.put1(f, dk, ds, ws, m, im, fi, nx, ks, img, c3, Cr.Cir.Cells.get(m, c3), D.Fd(1n, D.Put1(ws, m), c3), h2), sp2))))
    case Bk.Term.Typ{+y}:
      match x:
        case Cr.Cir.Cell{+c0, c1, +c2, +c3, +c4}:
          match hx:
            case Tuple{nd, Tuple{sp1, h1}}:
              (nd, part.put1(dk, ds, ws, m, im, fi, nx, ks, img, c, c2, y,
              isk.put1(y, dk, ds, ws, m, im, fi, nx, ks, img, c2, Cr.Cir.Cells.get(m, c2), D.Fd(1n, D.Put1(ws, m), c2), h1), sp1))
    case Bk.Term.Min{+a, +b}:
      match x:
        case Cr.Cir.Cell{+c0, c1, +c2, +c3, +c4}:
          match hx:
            case Tuple{nd, Tuple{Tuple{sp1, h1}, Tuple{sp2, h2}}}:
              (nd, (part.put1(dk, ds, ws, m, im, fi, nx, ks, img, c, c2, a,
              isk.put1(a, dk, ds, ws, m, im, fi, nx, ks, img, c2, Cr.Cir.Cells.get(m, c2), D.Fd(1n, D.Put1(ws, m), c2), h1), sp1),
                part.put1(dk, ds, ws, m, im, fi, nx, ks, img, c, c3, b,
              isk.put1(b, dk, ds, ws, m, im, fi, nx, ks, img, c3, Cr.Cir.Cells.get(m, c3), D.Fd(1n, D.Put1(ws, m), c3), h2), sp2)))
    case Bk.Term.All{+q, +a, +b}:
      match x:
        case Cr.Cir.Cell{+c0, c1, +c2, +c3, +c4}:
          match hx:
            case Tuple{nd, Tuple{qn, Tuple{Tuple{sp1, h1}, Tuple{sp2, h2}}}}:
              (nd, (qn, (part.put1(dk, ds, ws, m, im, fi, nx, ks, img, c, c2, a,
              isk.put1(a, dk, ds, ws, m, im, fi, nx, ks, img, c2, Cr.Cir.Cells.get(m, c2), D.Fd(1n, D.Put1(ws, m), c2), h1), sp1),
                part.put1(dk, ds, ws, m, im, fi, nx, ks, img, c, c3, b,
              isk.put1(b, dk, ds, ws, m, im, fi, nx, ks, img, c3, Cr.Cir.Cells.get(m, c3), D.Fd(1n, D.Put1(ws, m), c3), h2), sp2))))
    case Bk.Term.Lam{+q, +f}:
      match x:
        case Cr.Cir.Cell{+c0, c1, +c2, +c3, +c4}:
          match hx:
            case Tuple{nd, Tuple{qs, Tuple{sp1, h1}}}:
              (nd, (qs, part.put1(dk, ds, ws, m, im, fi, nx, ks, img, c, c2, f,
              isk.put1(f, dk, ds, ws, m, im, fi, nx, ks, img, c2, Cr.Cir.Cells.get(m, c2), D.Fd(1n, D.Put1(ws, m), c2), h1), sp1)))
    case Bk.Term.App{+q, +f, +y}:
      match x:
        case Cr.Cir.Cell{+c0, c1, +c2, +c3, +c4}:
          match hx:
            case Tuple{nd, Tuple{qn, Tuple{Tuple{sp1, h1}, Tuple{sp2, h2}}}}:
              (nd, (qn, (part.put1(dk, ds, ws, m, im, fi, nx, ks, img, c, c2, f,
              isk.put1(f, dk, ds, ws, m, im, fi, nx, ks, img, c2, Cr.Cir.Cells.get(m, c2), D.Fd(1n, D.Put1(ws, m), c2), h1), sp1),
                part.put1(dk, ds, ws, m, im, fi, nx, ks, img, c, c3, y,
              isk.put1(y, dk, ds, ws, m, im, fi, nx, ks, img, c3, Cr.Cir.Cells.get(m, c3), D.Fd(1n, D.Put1(ws, m), c3), h2), sp2))))
    case Bk.Term.Sig{+q, +a, +b}:
      match x:
        case Cr.Cir.Cell{+c0, c1, +c2, +c3, +c4}:
          match hx:
            case Tuple{nd, Tuple{qn, Tuple{Tuple{sp1, h1}, Tuple{sp2, h2}}}}:
              (nd, (qn, (part.put1(dk, ds, ws, m, im, fi, nx, ks, img, c, c2, a,
              isk.put1(a, dk, ds, ws, m, im, fi, nx, ks, img, c2, Cr.Cir.Cells.get(m, c2), D.Fd(1n, D.Put1(ws, m), c2), h1), sp1),
                part.put1(dk, ds, ws, m, im, fi, nx, ks, img, c, c3, b,
              isk.put1(b, dk, ds, ws, m, im, fi, nx, ks, img, c3, Cr.Cir.Cells.get(m, c3), D.Fd(1n, D.Put1(ws, m), c3), h2), sp2))))
    case Bk.Term.Tup{+q, +a, +b}:
      match x:
        case Cr.Cir.Cell{+c0, c1, +c2, +c3, +c4}:
          match hx:
            case Tuple{nd, Tuple{qn, Tuple{Tuple{sp1, h1}, Tuple{sp2, h2}}}}:
              (nd, (qn, (part.put1(dk, ds, ws, m, im, fi, nx, ks, img, c, c2, a,
              isk.put1(a, dk, ds, ws, m, im, fi, nx, ks, img, c2, Cr.Cir.Cells.get(m, c2), D.Fd(1n, D.Put1(ws, m), c2), h1), sp1),
                part.put1(dk, ds, ws, m, im, fi, nx, ks, img, c, c3, b,
              isk.put1(b, dk, ds, ws, m, im, fi, nx, ks, img, c3, Cr.Cir.Cells.get(m, c3), D.Fd(1n, D.Put1(ws, m), c3), h2), sp2))))
    case Bk.Term.Prj{+h}:
      match x:
        case Cr.Cir.Cell{+c0, c1, +c2, +c3, +c4}:
          match hx:
            case Tuple{nd, Tuple{sp1, h1}}:
              (nd, part.put1(dk, ds, ws, m, im, fi, nx, ks, img, c, c2, h,
              isk.put1(h, dk, ds, ws, m, im, fi, nx, ks, img, c2, Cr.Cir.Cells.get(m, c2), D.Fd(1n, D.Put1(ws, m), c2), h1), sp1))
    case Bk.Term.Enu{+e}:
      match x:
        case Cr.Cir.Cell{+c0, c1, +c2, +c3, +c4}:
          hx
    case Bk.Term.Lab{+k}:
      match x:
        case Cr.Cir.Cell{+c0, c1, +c2, +c3, +c4}:
          hx
    case Bk.Term.Mat{+k, +h, +o}:
      match x:
        case Cr.Cir.Cell{+c0, c1, +c2, +c3, +c4}:
          match hx:
            case Tuple{nd, Tuple{qn, Tuple{Tuple{sp1, h1}, Tuple{sp2, h2}}}}:
              (nd, (qn, (part.put1(dk, ds, ws, m, im, fi, nx, ks, img, c, c3, h,
              isk.put1(h, dk, ds, ws, m, im, fi, nx, ks, img, c3, Cr.Cir.Cells.get(m, c3), D.Fd(1n, D.Put1(ws, m), c3), h1), sp1),
                part.put1(dk, ds, ws, m, im, fi, nx, ks, img, c, c4, o,
              isk.put1(o, dk, ds, ws, m, im, fi, nx, ks, img, c4, Cr.Cir.Cells.get(m, c4), D.Fd(1n, D.Put1(ws, m), c4), h2), sp2))))
    case Bk.Term.Efq{}:
      match x:
        case Cr.Cir.Cell{+c0, c1, +c2, +c3, +c4}:
          hx
    case Bk.Term.Eql{+a, +b, +y}:
      match x:
        case Cr.Cir.Cell{+c0, c1, +c2, +c3, +c4}:
          match hx:
            case Tuple{nd, Tuple{Tuple{sp1, h1}, Tuple{Tuple{sp2, h2}, Tuple{sp3, h3}}}}:
              (nd, (part.put1(dk, ds, ws, m, im, fi, nx, ks, img, c, c2, a,
              isk.put1(a, dk, ds, ws, m, im, fi, nx, ks, img, c2, Cr.Cir.Cells.get(m, c2), D.Fd(1n, D.Put1(ws, m), c2), h1), sp1),
                (part.put1(dk, ds, ws, m, im, fi, nx, ks, img, c, c3, b,
              isk.put1(b, dk, ds, ws, m, im, fi, nx, ks, img, c3, Cr.Cir.Cells.get(m, c3), D.Fd(1n, D.Put1(ws, m), c3), h2), sp2),
                part.put1(dk, ds, ws, m, im, fi, nx, ks, img, c, c4, y,
              isk.put1(y, dk, ds, ws, m, im, fi, nx, ks, img, c4, Cr.Cir.Cells.get(m, c4), D.Fd(1n, D.Put1(ws, m), c4), h3), sp3))))
    case Bk.Term.Rfl{}:
      match x:
        case Cr.Cir.Cell{+c0, c1, +c2, +c3, +c4}:
          hx
    case Bk.Term.Rwt{+e, +p, +f}:
      match x:
        case Cr.Cir.Cell{+c0, c1, +c2, +c3, +c4}:
          match hx:
            case Tuple{nd, Tuple{Tuple{sp1, h1}, Tuple{Tuple{sp2, h2}, Tuple{sp3, h3}}}}:
              (nd, (part.put1(dk, ds, ws, m, im, fi, nx, ks, img, c, c2, e,
              isk.put1(e, dk, ds, ws, m, im, fi, nx, ks, img, c2, Cr.Cir.Cells.get(m, c2), D.Fd(1n, D.Put1(ws, m), c2), h1), sp1),
                (part.put1(dk, ds, ws, m, im, fi, nx, ks, img, c, c3, p,
              isk.put1(p, dk, ds, ws, m, im, fi, nx, ks, img, c3, Cr.Cir.Cells.get(m, c3), D.Fd(1n, D.Put1(ws, m), c3), h2), sp2),
                part.put1(dk, ds, ws, m, im, fi, nx, ks, img, c, c4, f,
              isk.put1(f, dk, ds, ws, m, im, fi, nx, ks, img, c4, Cr.Cir.Cells.get(m, c4), D.Fd(1n, D.Put1(ws, m), c4), h3), sp3))))

# stores to field 1 keep every term (IsCK reads fields 0, 2, 3 and 4)
def rts.put1(+dk: Bool, xs: List<&2, D.Rt>, +ds: List<&2, Bk.Def>, +ws: List<&2, D.W1>, +m: Cr.Cir.Cells, +im: U32, +fi: U32,
  +nx: U32, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, h: D.RtsK(dk, ds, m, im, fi, nx, ks, img, xs)) ->
  D.RtsK(dk, ds, D.Put1(ws, m), im, fi, nx, ks, img, xs):
  match xs:
    case Nil{}:
      Unit{}
    case Con{D.Rt{+c, +u}, +rest}:
      match h:
        case Tuple{hu, hr}:
          (D.isc.atk(dk, ds, D.Put1(ws, m), im, fi, nx, ks, img, c, Cr.Cir.Cells.get(D.Put1(ws, m), c),
              Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, c), D.Fd(1n, D.Put1(ws, m), c)), u, D.put1.at(ws, m, c),
              isk.put1(u, dk, ds, ws, m, im, fi, nx, ks, img, c, Cr.Cir.Cells.get(m, c), D.Fd(1n, D.Put1(ws, m), c), hu)),
            rts.put1(dk, rest, ds, ws, m, im, fi, nx, ks, img, hr))

def nodes.put1(rs: List<&2, D.Rt>, +ws: List<&2, D.W1>, +m: Cr.Cir.Cells, +x: U32) ->
  {D.Nodes(rs, D.Put1(ws, m), x) == D.Nodes(rs, m, x) : Bool}:
  match rs:
    case Nil{}:
      {==}
    case Con{D.Rt{+r, +u}, +rest}:
      or.cong2(D.Node(u, D.Put1(ws, m), r, x), D.Node(u, m, r, x), D.Nodes(rest, D.Put1(ws, m), x), D.Nodes(rest, m, x),
        node.put1(u, ws, m, r, x), nodes.put1(rest, ws, m, x))

def cov.put1(n: Nat, +ws: List<&2, D.W1>, +m: Cr.Cir.Cells, +c: U32, +rs: List<&2, D.Rt>, +xs: List<&2, U32>) ->
  {D.Cov(n, D.Put1(ws, m), c, rs, xs) == D.Cov(n, m, c, rs, xs) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+(+k):
      +M2 = D.Put1(ws, m)
      +RHS = Bool.and(Bool.or(U32.is_ne(U32.and(D.Fd(0n, m, c), 1024), 0), Bool.or(D.Nodes(rs, m, c), D.Mem(xs, c))), D.Cov(k, m, U32.inc(c), rs, xs))
      %Equal.sym(U32, D.Fd(0n, M2, c), D.Fd(0n, m, c), D.put1.f0(ws, m, c)) :
        {Bool.and(Bool.or(U32.is_ne(U32.and(_, 1024), 0), Bool.or(D.Nodes(rs, M2, c), D.Mem(xs, c))), D.Cov(k, M2, U32.inc(c), rs, xs)) == RHS : Bool}
      %Equal.sym(Bool, D.Nodes(rs, M2, c), D.Nodes(rs, m, c), nodes.put1(rs, ws, m, c)) :
        {Bool.and(Bool.or(U32.is_ne(U32.and(D.Fd(0n, m, c), 1024), 0), Bool.or(_, D.Mem(xs, c))), D.Cov(k, M2, U32.inc(c), rs, xs)) == RHS : Bool}
      %Equal.sym(Bool, D.Cov(k, M2, U32.inc(c), rs, xs), D.Cov(k, m, U32.inc(c), rs, xs), cov.put1(k, ws, m, U32.inc(c), rs, xs)) :
        {Bool.and(Bool.or(U32.is_ne(U32.and(D.Fd(0n, m, c), 1024), 0), Bool.or(D.Nodes(rs, m, c), D.Mem(xs, c))), _) == RHS : Bool}
      {==}

def pend.terms.put1(ps: List<&2, U32>, +ws: List<&2, D.W1>, +m: Cr.Cir.Cells) ->
  {D.Pend.terms(ps, D.Put1(ws, m)) == D.Pend.terms(ps, m) : List<&2, U32>}:
  match ps:
    case Nil{}:
      {==}
    case Con{+q, +rest}:
      +M2 = D.Put1(ws, m)
      %Equal.sym(U32, D.Fd(0n, M2, q), D.Fd(0n, m, q), D.put1.f0(ws, m, q)) :
        {Bool.pick(List<&2, U32>, U32.is_lt(U32.and(_, 63), 19), Con{q, D.Pend.terms(rest, M2)}, D.Pend.terms(rest, M2)) ==
          D.Pend.terms(Con{q, rest}, m) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, D.Pend.terms(rest, M2), D.Pend.terms(rest, m), pend.terms.put1(rest, ws, m)) :
        {Bool.pick(List<&2, U32>, U32.is_lt(U32.and(D.Fd(0n, m, q), 63), 19), Con{q, _}, _) == D.Pend.terms(Con{q, rest}, m) : List<&2, U32>}
      {==}

def static.all.put1(ys: List<&2, U32>, +ws: List<&2, D.W1>, +m: Cr.Cir.Cells) ->
  {D.All.static(ys, D.Put1(ws, m)) == D.All.static(ys, m) : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      %Equal.sym(U32, D.Fd(0n, D.Put1(ws, m), y), D.Fd(0n, m, y), D.put1.f0(ws, m, y)) :
        {Bool.and(U32.is_ne(U32.and(_, 1024), 0), D.All.static(rest, D.Put1(ws, m))) == D.All.static(Con{y, rest}, m) : Bool}
      %Equal.sym(Bool, D.All.static(rest, D.Put1(ws, m)), D.All.static(rest, m), static.all.put1(rest, ws, m)) :
        {Bool.and(U32.is_ne(U32.and(D.Fd(0n, m, y), 1024), 0), _) == D.All.static(Con{y, rest}, m) : Bool}
      {==}

def held.all.put1(ys: List<&2, U32>, +ws: List<&2, D.W1>, +m: Cr.Cir.Cells, +cs: List<&2, U32>, +hc: List<&2, U32>) ->
  {D.All.held(ys, D.Put1(ws, m), cs, hc) == D.All.held(ys, m, cs, hc) : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      %Equal.sym(U32, D.Fd(0n, D.Put1(ws, m), y), D.Fd(0n, m, y), D.put1.f0(ws, m, y)) :
        {Bool.and(Bool.or(U32.is_ne(U32.and(_, 1024), 0), Bool.or(D.Mem(cs, y), D.Mem(hc, y))), D.All.held(rest, D.Put1(ws, m), cs, hc)) ==
          D.All.held(Con{y, rest}, m, cs, hc) : Bool}
      %Equal.sym(Bool, D.All.held(rest, D.Put1(ws, m), cs, hc), D.All.held(rest, m, cs, hc), held.all.put1(rest, ws, m, cs, hc)) :
        {Bool.and(Bool.or(U32.is_ne(U32.and(D.Fd(0n, m, y), 1024), 0), Bool.or(D.Mem(cs, y), D.Mem(hc, y))), _) == D.All.held(Con{y, rest}, m, cs, hc) : Bool}
      {==}

def clo.put1(n: Nat, +ws: List<&2, D.W1>, +m: Cr.Cir.Cells, +c: U32, +ps: List<&2, U32>, +cs: List<&2, U32>, +hc: List<&2, U32>) ->
  {D.Clo(n, D.Put1(ws, m), c, ps, cs, hc) == D.Clo(n, m, c, ps, cs, hc) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+(+k):
      +M2 = D.Put1(ws, m)
      +RHS = D.Clo(1n+k, m, c, ps, cs, hc)
      %Equal.sym(U32, D.Fd(0n, M2, c), D.Fd(0n, m, c), D.put1.f0(ws, m, c)) :
        {Bool.and(Bool.and(Bool.or(Bool.not(U32.is_ne(U32.and(_, 1024), 0)), D.All.static(D.Fs(M2, ps, c), M2)),
          Bool.or(Bool.not(D.Mem(cs, c)), D.All.held(D.Fs(M2, ps, c), M2, cs, hc))), D.Clo(k, M2, U32.inc(c), ps, cs, hc)) == RHS : Bool}
      %Equal.sym(List<&2, U32>, D.Fs(M2, ps, c), D.Fs(m, ps, c), D.fs.put1(ws, m, ps, c)) :
        {Bool.and(Bool.and(Bool.or(Bool.not(U32.is_ne(U32.and(D.Fd(0n, m, c), 1024), 0)), D.All.static(_, M2)),
          Bool.or(Bool.not(D.Mem(cs, c)), D.All.held(_, M2, cs, hc))), D.Clo(k, M2, U32.inc(c), ps, cs, hc)) == RHS : Bool}
      %Equal.sym(Bool, D.All.static(D.Fs(m, ps, c), M2), D.All.static(D.Fs(m, ps, c), m), static.all.put1(D.Fs(m, ps, c), ws, m)) :
        {Bool.and(Bool.and(Bool.or(Bool.not(U32.is_ne(U32.and(D.Fd(0n, m, c), 1024), 0)), _),
          Bool.or(Bool.not(D.Mem(cs, c)), D.All.held(D.Fs(m, ps, c), M2, cs, hc))), D.Clo(k, M2, U32.inc(c), ps, cs, hc)) == RHS : Bool}
      %Equal.sym(Bool, D.All.held(D.Fs(m, ps, c), M2, cs, hc), D.All.held(D.Fs(m, ps, c), m, cs, hc), held.all.put1(D.Fs(m, ps, c), ws, m, cs, hc)) :
        {Bool.and(Bool.and(Bool.or(Bool.not(U32.is_ne(U32.and(D.Fd(0n, m, c), 1024), 0)), D.All.static(D.Fs(m, ps, c), m)),
          Bool.or(Bool.not(D.Mem(cs, c)), _)), D.Clo(k, M2, U32.inc(c), ps, cs, hc)) == RHS : Bool}
      %Equal.sym(Bool, D.Clo(k, M2, U32.inc(c), ps, cs, hc), D.Clo(k, m, U32.inc(c), ps, cs, hc), clo.put1(k, ws, m, U32.inc(c), ps, cs, hc)) :
        {Bool.and(Bool.and(Bool.or(Bool.not(U32.is_ne(U32.and(D.Fd(0n, m, c), 1024), 0)), D.All.static(D.Fs(m, ps, c), m)),
          Bool.or(Bool.not(D.Mem(cs, c)), D.All.held(D.Fs(m, ps, c), m, cs, hc))), _) == RHS : Bool}
      {==}

def frb.put1(kind: D.FK, +ws: List<&2, D.W1>, +m: Cr.Cir.Cells, +fr: U32, +b: Bk.Term) ->
  {D.Fr.rts.b(D.Put1(ws, m), fr, kind, b) == D.Fr.rts.b(m, fr, kind, b) : List<&2, D.Rt>}:
  match kind:
    case D.FK.rwt{}:
      %Equal.sym(U32, D.Fd(3n, D.Put1(ws, m), fr), D.Fd(3n, m, fr), D.put1.f3(ws, m, fr)) :
        {[D.Rt{_, b}] == [D.Rt{D.Fd(3n, m, fr), b}] : List<&2, D.Rt>}
      {==}
    case D.FK.arg{}:
      {==}
    case D.FK.val{}:
      {==}
    case D.FK.fun{}:
      {==}
    case D.FK.let{}:
      {==}
    case D.FK.tupb{}:
      {==}
    case D.FK.tupa{}:
      {==}
    case D.FK.minb{}:
      {==}
    case D.FK.mina{}:
      {==}

# stores to field 1 of cells that are no frames keep the frames' cells and terms
def fr.put1(fs: List<&2, D.AF>, +ws: List<&2, D.W1>, +m: Cr.Cir.Cells, +fr: U32,
  hw: {Outs(D.Fr.cells(fs, m, fr), D.W1.cells(ws)) == True{} : Bool}) ->
  D.P2({D.Fr.cells(fs, D.Put1(ws, m), fr) == D.Fr.cells(fs, m, fr) : List<&2, U32>},
    {D.Fr.rts(fs, D.Put1(ws, m), fr) == D.Fr.rts(fs, m, fr) : List<&2, D.Rt>}):
  match fs:
    case Nil{}:
      ({==}, {==})
    case Con{D.AF{+kind, +q, +k, +a, +b}, +rest}:
      +M2 = D.Put1(ws, m)
      +hw2 = hw
      +f1 = D.Fd(1n, m, fr)
      +nf = D.not.t(D.Mem(D.W1.cells(ws), fr), D.and.l(Bool.not(D.Mem(D.W1.cells(ws), fr)), Outs(D.Fr.cells(rest, m, f1), D.W1.cells(ws)), hw2))
      +e1 = {Equal.cong(Cr.Cir.Cell, U32, y => Cr.Cir.Cell.get(1n, y), Cr.Cir.Cells.get(M2, fr), Cr.Cir.Cells.get(m, fr), D.put1.out(ws, m, fr, nf)) :
        {D.Fd(1n, M2, fr) == f1 : U32}}
      +ih = fr.put1(rest, ws, m, f1, D.and.r(Bool.not(D.Mem(D.W1.cells(ws), fr)), Outs(D.Fr.cells(rest, m, f1), D.W1.cells(ws)), hw2))
      +ihc = D.Ex.fst({D.Fr.cells(rest, M2, f1) == D.Fr.cells(rest, m, f1) : List<&2, U32>}, _ => {D.Fr.rts(rest, M2, f1) == D.Fr.rts(rest, m, f1) : List<&2, D.Rt>}, ih)
      +ihr = D.Ex.snd({D.Fr.cells(rest, M2, f1) == D.Fr.cells(rest, m, f1) : List<&2, U32>}, _ => {D.Fr.rts(rest, M2, f1) == D.Fr.rts(rest, m, f1) : List<&2, D.Rt>}, ih)
      ({(%Equal.sym(U32, D.Fd(1n, M2, fr), f1, e1) : {Con{fr, D.Fr.cells(rest, M2, _)} == Con{fr, D.Fr.cells(rest, m, f1)} : List<&2, U32>};
          %Equal.sym(List<&2, U32>, D.Fr.cells(rest, M2, f1), D.Fr.cells(rest, m, f1), ihc) : {Con{fr, _} == Con{fr, D.Fr.cells(rest, m, f1)} : List<&2, U32>};
          {==}) : {D.Fr.cells(Con{D.AF{kind, q, k, a, b}, rest}, M2, fr) == D.Fr.cells(Con{D.AF{kind, q, k, a, b}, rest}, m, fr) : List<&2, U32>}},
        {(%Equal.sym(U32, D.Fd(1n, M2, fr), f1, e1) :
            {Con{D.Rt{D.Fd(2n, M2, fr), a}, List.append(&2, D.Rt, D.Fr.rts.b(M2, fr, kind, b), D.Fr.rts(rest, M2, _))} ==
              Con{D.Rt{D.Fd(2n, m, fr), a}, List.append(&2, D.Rt, D.Fr.rts.b(m, fr, kind, b), D.Fr.rts(rest, m, f1))} : List<&2, D.Rt>};
          %Equal.sym(U32, D.Fd(2n, M2, fr), D.Fd(2n, m, fr), D.put1.f2(ws, m, fr)) :
            {Con{D.Rt{_, a}, List.append(&2, D.Rt, D.Fr.rts.b(M2, fr, kind, b), D.Fr.rts(rest, M2, f1))} ==
              Con{D.Rt{D.Fd(2n, m, fr), a}, List.append(&2, D.Rt, D.Fr.rts.b(m, fr, kind, b), D.Fr.rts(rest, m, f1))} : List<&2, D.Rt>};
          %Equal.sym(List<&2, D.Rt>, D.Fr.rts.b(M2, fr, kind, b), D.Fr.rts.b(m, fr, kind, b), frb.put1(kind, ws, m, fr, b)) :
            {Con{D.Rt{D.Fd(2n, m, fr), a}, List.append(&2, D.Rt, _, D.Fr.rts(rest, M2, f1))} ==
              Con{D.Rt{D.Fd(2n, m, fr), a}, List.append(&2, D.Rt, D.Fr.rts.b(m, fr, kind, b), D.Fr.rts(rest, m, f1))} : List<&2, D.Rt>};
          %Equal.sym(List<&2, D.Rt>, D.Fr.rts(rest, M2, f1), D.Fr.rts(rest, m, f1), ihr) :
            {Con{D.Rt{D.Fd(2n, m, fr), a}, List.append(&2, D.Rt, D.Fr.rts.b(m, fr, kind, b), _)} ==
              Con{D.Rt{D.Fd(2n, m, fr), a}, List.append(&2, D.Rt, D.Fr.rts.b(m, fr, kind, b), D.Fr.rts(rest, m, f1))} : List<&2, D.Rt>};
          {==}) : {D.Fr.rts(Con{D.AF{kind, q, k, a, b}, rest}, M2, fr) == D.Fr.rts(Con{D.AF{kind, q, k, a, b}, rest}, m, fr) : List<&2, D.Rt>}})

# no frame is c, which a list of cells shows once or twice
def outs.one(L: List<&2, U32>, +c: U32, h: {D.Mem(L, c) == False{} : Bool}) -> {Outs(L, [c]) == True{} : Bool}:
  match L:
    case Nil{}:
      {==}
    case Con{+f, +rest}:
      +h2 = h
      %Equal.sym(Bool, U32.is_eq(c, f), False{}, D.ne.sym(f, c, D.or.f.l(U32.is_eq(f, c), D.Mem(rest, c), h2))) :
        {Bool.and(Bool.not(Bool.or(_, False{})), Outs(rest, [c])) == True{} : Bool}
      outs.one(rest, c, D.or.f.r(U32.is_eq(f, c), D.Mem(rest, c), h2))

def outs.two(L: List<&2, U32>, +c: U32, h: {D.Mem(L, c) == False{} : Bool}) -> {Outs(L, [c, c]) == True{} : Bool}:
  match L:
    case Nil{}:
      {==}
    case Con{+f, +rest}:
      +h2 = h
      %Equal.sym(Bool, U32.is_eq(c, f), False{}, D.ne.sym(f, c, D.or.f.l(U32.is_eq(f, c), D.Mem(rest, c), h2))) :
        {Bool.and(Bool.not(Bool.or(_, Bool.or(_, False{}))), Outs(rest, [c, c])) == True{} : Bool}
      outs.two(rest, c, D.or.f.r(U32.is_eq(f, c), D.Mem(rest, c), h2))

# U32 comparisons: below a is below b when a <= b
def lt.mono.b(c: Cmp, +t: U32, +b: U32, r: N.Rel(c, U32.to_nat(t), U32.to_nat(b)), h: N.Le(1n+U32.to_nat(t), U32.to_nat(b))) ->
  {Cmp.is_lt(c) == True{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({False{} == True{} : Bool}, N.not_succ_le(U32.to_nat(b), (%r : N.Le(1n+_, U32.to_nat(b)); h)))
    case GT{}:
      Empty.absurd({False{} == True{} : Bool}, N.not_succ_le(U32.to_nat(b),
        N.le_trans(1n+U32.to_nat(b), U32.to_nat(t), U32.to_nat(b), r, N.weaken(U32.to_nat(t), U32.to_nat(b), h))))

def lt.mono(+t: U32, +a: U32, +b: U32, h: {U32.is_lt(t, a) == True{} : Bool}, hab: N.Le(U32.to_nat(a), U32.to_nat(b))) ->
  {U32.is_lt(t, b) == True{} : Bool}:
  lt.mono.b(U32.cmp(t, b), t, b, N.U32.rel(t, b), N.le_trans(1n+U32.to_nat(t), U32.to_nat(a), U32.to_nat(b), D.u.lt(t, a, h), hab))

def le.nineteen() -> N.Le(U32.to_nat(19), U32.to_nat(32)):
  Unit{}

def lt.below32(+t: U32, h: {U32.is_lt(t, 19) == True{} : Bool}) -> {U32.is_lt(t, 32) == True{} : Bool}:
  lt.mono(t, 19, 32, h, le.nineteen())

def nlt.b(b: Bool, +t: U32, eb: {U32.is_lt(t, 19) == b : Bool}, h: {U32.is_lt(t, 32) == False{} : Bool}) ->
  {U32.is_lt(t, 19) == False{} : Bool}:
  match b:
    case False{}:
      eb
    case True{}:
      D.bool.ft({U32.is_lt(t, 19) == False{} : Bool}, Equal.trans(Bool, False{}, U32.is_lt(t, 32), True{}, Equal.sym(Bool, U32.is_lt(t, 32), False{}, h),
        lt.below32(t, eb)))

# a tag of 32 or more is no tag below 19
def nlt.below19(+t: U32, h: {U32.is_lt(t, 32) == False{} : Bool}) -> {U32.is_lt(t, 19) == False{} : Bool}:
  nlt.b(U32.is_lt(t, 19), t, {==}, h)

# a cell of a tag below 32 is no frame
def fr.out.lo(+dk: Bool, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +ps: List<&2, U32>, fs: List<&2, D.AF>, +sp: U32, +c: U32,
  hf: D.FrsK(dk, ds, m, im, fi, nx, ks, img, ps, sp, fs), ht: {U32.is_lt(D.Tg(m, c), 32) == True{} : Bool}) ->
  {D.Mem(D.Fr.cells(fs, m, sp), c) == False{} : Bool}:
  match fs:
    case Nil{}:
      {==}
    case Con{D.AF{+kind, +q, +k, +a, +b}, +rest}:
      match hf:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{+etg, Tuple{_, Tuple{_, Tuple{_, Tuple{_, hr}}}}}}}}}}:
          +ht2 = ht
          %Equal.sym(Bool, U32.is_eq(sp, c), False{}, D.ne.fr(U32.is_eq(sp, c), m, sp, c, kind, {==}, etg, ht2)) :
            {Bool.or(_, D.Mem(D.Fr.cells(rest, m, D.Fd(1n, m, sp)), c)) == False{} : Bool}
          fr.out.lo(dk, ds, m, im, fi, nx, ks, img, ps, rest, D.Fd(1n, m, sp), c, hr, ht2)

def fr.ne.nil(b: Bool, +m: Cr.Cir.Cells, +ps: List<&2, U32>, +fr: U32, +c: U32, +kind: D.FK, eb: {U32.is_eq(fr, c) == b : Bool},
  etg: {D.Tg(m, fr) == D.FK.tag(kind) : U32}, em: {D.Mem(ps, fr) == False{} : Bool}, hfs: {D.Fs(m, ps, c) == Nil{} : List<&2, U32>}) ->
  {U32.is_eq(fr, c) == False{} : Bool}:
  match b:
    case False{}:
      eb
    case True{}:
      +L = {Con{D.Fd(2n, m, fr), D.Fs.opt(U32.is_eq(D.FK.tag(kind), 38), D.Fd(3n, m, fr), Nil{})} : List<&2, U32>}
      +e = D.fs.frame(m, ps, fr, D.FK.tag(kind), etg, D.fk.lt(kind), D.fk.ge(kind), D.fk.le(kind), em)
      +h2 = {(%Equal.sym(U32, fr, c, D.u32.eq(fr, c, eb)) : {D.Fs(m, ps, _) == Nil{} : List<&2, U32>}; hfs) : {D.Fs(m, ps, fr) == Nil{} : List<&2, U32>}}
      Empty.absurd({U32.is_eq(fr, c) == False{} : Bool},
        (%Equal.trans(List<&2, U32>, L, D.Fs(m, ps, fr), Nil{}, Equal.sym(List<&2, U32>, D.Fs(m, ps, fr), L, e), h2) : is.cons(_); Unit{}))

# a cell out of the pend list that holds no pointer is no frame
def fr.out.nil(+dk: Bool, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +ps: List<&2, U32>, fs: List<&2, D.AF>, +sp: U32, +c: U32,
  hf: D.FrsK(dk, ds, m, im, fi, nx, ks, img, ps, sp, fs), hm: {D.Mem(ps, c) == False{} : Bool},
  hfs: {D.Fs(m, ps, c) == Nil{} : List<&2, U32>}) ->
  {D.Mem(D.Fr.cells(fs, m, sp), c) == False{} : Bool}:
  match fs:
    case Nil{}:
      {==}
    case Con{D.AF{+kind, +q, +k, +a, +b}, +rest}:
      match hf:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{+em, Tuple{+etg, Tuple{_, Tuple{_, Tuple{_, Tuple{_, hr}}}}}}}}}}:
          +hm2 = hm
          +hfs2 = hfs
          %Equal.sym(Bool, U32.is_eq(sp, c), False{}, fr.ne.nil(U32.is_eq(sp, c), m, ps, sp, c, kind, {==}, etg, em, hfs2)) :
            {Bool.or(_, D.Mem(D.Fr.cells(rest, m, D.Fd(1n, m, sp)), c)) == False{} : Bool}
          fr.out.nil(dk, ds, m, im, fi, nx, ks, img, ps, rest, D.Fd(1n, m, sp), c, hr, hm2, hfs2)

# The pend list's new cells
# -------------------------

# Cov with the same covers
def cov.mv(-A: Bool, -B: Bool, e: {A == B : Bool}, h: {A == True{} : Bool}) -> {B == True{} : Bool}:
  Equal.trans(Bool, B, A, True{}, Equal.sym(Bool, A, B, e), h)

def app.assoc(A: List<&2, D.Rt>, +B: List<&2, D.Rt>, +C: List<&2, D.Rt>) ->
  {List.append(&2, D.Rt, List.append(&2, D.Rt, A, B), C) == List.append(&2, D.Rt, A, List.append(&2, D.Rt, B, C)) : List<&2, D.Rt>}:
  match A:
    case Nil{}:
      {==}
    case Con{+r, +rest}:
      %app.assoc(rest, B, C) : {Con{r, List.append(&2, D.Rt, List.append(&2, D.Rt, rest, B), C)} == Con{r, _} : List<&2, D.Rt>}
      {==}

# Fs's body, with mem for Mem(ps, o)
def FsM(+b: Bool, +mem: Bool, +m: Cr.Cir.Cells, +o: U32, +tg: U32) -> List<&2, U32>:
  Bool.pick(List<&2, U32>, b, D.Fs.term(D.Fd(2n, m, U32.add(272, tg)), D.Fd(2n, m, o), D.Fd(3n, m, o), D.Fd(4n, m, o)),
    Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_le(32, tg), U32.is_le(tg, 40)), Bool.not(mem)),
      Con{D.Fd(2n, m, o), D.Fs.opt(U32.is_eq(tg, 38), D.Fd(3n, m, o), Nil{})},
      Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_eq(tg, 41), D.FlW(D.Fd(0n, m, o), 4096)), Bool.not(mem)), [D.Fd(2n, m, o)], Nil{})))

# a term cell c that joins the pend list changes no cell's pointers
def fs.pend.b(b: Bool, +m: Cr.Cir.Cells, +ps: List<&2, U32>, +c: U32, +o: U32, eb: {U32.is_eq(c, o) == b : Bool},
  ht: {U32.is_lt(D.Tg(m, c), 19) == True{} : Bool}) -> {D.Fs(m, Con{c, ps}, o) == D.Fs(m, ps, o) : List<&2, U32>}:
  match b:
    case True{}:
      %D.u32.eq(c, o, eb) : {D.Fs(m, Con{c, ps}, _) == D.Fs(m, ps, _) : List<&2, U32>}
      %Equal.sym(Bool, U32.is_lt(D.Tg(m, c), 19), True{}, ht) :
        {FsM(_, D.Mem(Con{c, ps}, c), m, c, D.TgW(D.Fd(0n, m, c))) == FsM(_, D.Mem(ps, c), m, c, D.TgW(D.Fd(0n, m, c))) : List<&2, U32>}
      {==}
    case False{}:
      %Equal.sym(Bool, U32.is_eq(c, o), False{}, eb) :
        {FsM(U32.is_lt(D.TgW(D.Fd(0n, m, o)), 19), Bool.or(_, D.Mem(ps, o)), m, o, D.TgW(D.Fd(0n, m, o))) == D.Fs(m, ps, o) : List<&2, U32>}
      {==}

def clo.pend(n: Nat, +m: Cr.Cir.Cells, +c: U32, +ps: List<&2, U32>, +z: U32, +cs: List<&2, U32>, +hc: List<&2, U32>,
  ht: {U32.is_lt(D.Tg(m, z), 19) == True{} : Bool}) -> {D.Clo(n, m, c, Con{z, ps}, cs, hc) == D.Clo(n, m, c, ps, cs, hc) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+(+k):
      +ht2 = ht
      +RHS = D.Clo(1n+k, m, c, ps, cs, hc)
      %Equal.sym(List<&2, U32>, D.Fs(m, Con{z, ps}, c), D.Fs(m, ps, c), fs.pend.b(U32.is_eq(z, c), m, ps, z, c, {==}, ht2)) :
        {Bool.and(Bool.and(Bool.or(Bool.not(D.Fl(m, c, 1024)), D.All.static(_, m)), Bool.or(Bool.not(D.Mem(cs, c)), D.All.held(_, m, cs, hc))),
          D.Clo(k, m, U32.inc(c), Con{z, ps}, cs, hc)) == RHS : Bool}
      %Equal.sym(Bool, D.Clo(k, m, U32.inc(c), Con{z, ps}, cs, hc), D.Clo(k, m, U32.inc(c), ps, cs, hc), clo.pend(k, m, U32.inc(c), ps, z, cs, hc, ht2)) :
        {Bool.and(Bool.and(Bool.or(Bool.not(D.Fl(m, c, 1024)), D.All.static(D.Fs(m, ps, c), m)),
          Bool.or(Bool.not(D.Mem(cs, c)), D.All.held(D.Fs(m, ps, c), m, cs, hc))), _) == RHS : Bool}
      {==}

# a released cell z (no term cell), which held no pointer, has none in the
# pend list; and no other cell's pointers change
def fs.pend2.b(b: Bool, +m: Cr.Cir.Cells, +ps: List<&2, U32>, +z: U32, +o: U32, eb: {U32.is_eq(z, o) == b : Bool},
  hnt: {U32.is_lt(D.Tg(m, z), 19) == False{} : Bool}, hfs: {D.Fs(m, ps, z) == Nil{} : List<&2, U32>}) ->
  {D.Fs(m, Con{z, ps}, o) == D.Fs(m, ps, o) : List<&2, U32>}:
  match b:
    case True{}:
      +T = D.TgW(D.Fd(0n, m, z))
      %D.u32.eq(z, o, eb) : {D.Fs(m, Con{z, ps}, _) == D.Fs(m, ps, _) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, D.Fs(m, ps, z), Nil{}, hfs) : {D.Fs(m, Con{z, ps}, z) == _ : List<&2, U32>}
      %Equal.sym(Bool, U32.is_lt(D.Tg(m, z), 19), False{}, hnt) : {FsM(_, D.Mem(Con{z, ps}, z), m, z, T) == Nil{} : List<&2, U32>}
      %Equal.sym(Bool, U32.is_eq(z, z), True{}, D.u32.refl(z)) : {FsM(False{}, Bool.or(_, D.Mem(ps, z)), m, z, T) == Nil{} : List<&2, U32>}
      %Equal.sym(Bool, Bool.and(Bool.and(U32.is_le(32, T), U32.is_le(T, 40)), False{}), False{}, and.false(Bool.and(U32.is_le(32, T), U32.is_le(T, 40)))) :
        {Bool.pick(List<&2, U32>, _, Con{D.Fd(2n, m, z), D.Fs.opt(U32.is_eq(T, 38), D.Fd(3n, m, z), Nil{})},
          Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_eq(T, 41), D.FlW(D.Fd(0n, m, z), 4096)), False{}), [D.Fd(2n, m, z)], Nil{})) == Nil{} : List<&2, U32>}
      %Equal.sym(Bool, Bool.and(Bool.and(U32.is_eq(T, 41), D.FlW(D.Fd(0n, m, z), 4096)), False{}), False{}, and.false(Bool.and(U32.is_eq(T, 41), D.FlW(D.Fd(0n, m, z), 4096)))) :
        {Bool.pick(List<&2, U32>, _, [D.Fd(2n, m, z)], Nil{}) == Nil{} : List<&2, U32>}
      {==}
    case False{}:
      %Equal.sym(Bool, U32.is_eq(z, o), False{}, eb) :
        {FsM(U32.is_lt(D.TgW(D.Fd(0n, m, o)), 19), Bool.or(_, D.Mem(ps, o)), m, o, D.TgW(D.Fd(0n, m, o))) == D.Fs(m, ps, o) : List<&2, U32>}
      {==}

def ne.tag.b(b: Bool, +m: Cr.Cir.Cells, +y: U32, +z: U32, eb: {U32.is_eq(z, y) == b : Bool}, hy: {U32.is_lt(D.Tg(m, y), 19) == True{} : Bool},
  hz: {U32.is_lt(D.Tg(m, z), 19) == False{} : Bool}) -> {U32.is_eq(z, y) == False{} : Bool}:
  match b:
    case False{}:
      eb
    case True{}:
      D.bool.ft({U32.is_eq(z, y) == False{} : Bool}, Equal.trans(Bool, False{}, U32.is_lt(D.Tg(m, y), 19), True{},
        (%D.u32.eq(z, y, eb) : {False{} == U32.is_lt(D.Tg(m, _), 19) : Bool}; Equal.sym(Bool, U32.is_lt(D.Tg(m, z), 19), False{}, hz)), hy))

# a term cell is not z, which is none
def ne.tag(+m: Cr.Cir.Cells, +y: U32, +z: U32, hy: {U32.is_lt(D.Tg(m, y), 19) == True{} : Bool},
  hz: {U32.is_lt(D.Tg(m, z), 19) == False{} : Bool}) -> {U32.is_eq(z, y) == False{} : Bool}:
  ne.tag.b(U32.is_eq(z, y), m, y, z, {==}, hy, hz)

# pointers to term cells reach no cell z that is none: z can leave the temporaries
def held.drop(L: List<&2, U32>, +m: Cr.Cir.Cells, +z: U32, +cs: List<&2, U32>, +hc: List<&2, U32>, +im: U32, +fi: U32, +nx: U32,
  +hz: {U32.is_lt(D.Tg(m, z), 19) == False{} : Bool}, hlt: {D.Lt.all(L, m, im, fi, nx) == True{} : Bool},
  h: {D.All.held(L, m, Con{z, cs}, hc) == True{} : Bool}) -> {D.All.held(L, m, cs, hc) == True{} : Bool}:
  match L:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      +hlt2 = hlt
      +h2 = h
      +lc = D.and.l(D.LtC(y, Cr.Cir.Cells.get(m, y), im, fi, nx), D.Lt.all(rest, m, im, fi, nx), hlt2)
      +htg = D.and.r(U32.is_lt(y, nx), U32.is_lt(D.TgW(Cr.Cir.Cell.get(0n, Cr.Cir.Cells.get(m, y))), 19),
        D.and.l(Bool.and(U32.is_lt(y, nx), U32.is_lt(D.TgW(Cr.Cir.Cell.get(0n, Cr.Cir.Cells.get(m, y))), 19)),
          Bool.and(Cr.Cir.is_cell(y, im, fi, nx), Bool.or(D.Own(fi, nx, y), D.FlW(Cr.Cir.Cell.get(0n, Cr.Cir.Cells.get(m, y)), 1024))), lc))
      +hy = D.and.l(Bool.or(D.Fl(m, y, 1024), Bool.or(D.Mem(Con{z, cs}, y), D.Mem(hc, y))), D.All.held(rest, m, Con{z, cs}, hc), h2)
      D.and.i(Bool.or(D.Fl(m, y, 1024), Bool.or(D.Mem(cs, y), D.Mem(hc, y))), D.All.held(rest, m, cs, hc),
        {(%ne.tag(m, y, z, htg, hz) :
            {Bool.or(D.Fl(m, y, 1024), Bool.or(Bool.or(_, D.Mem(cs, y)), D.Mem(hc, y))) == True{} : Bool}; hy) :
          {Bool.or(D.Fl(m, y, 1024), Bool.or(D.Mem(cs, y), D.Mem(hc, y))) == True{} : Bool}},
        held.drop(rest, m, z, cs, hc, im, fi, nx, hz, D.and.r(D.LtC(y, Cr.Cir.Cells.get(m, y), im, fi, nx), D.Lt.all(rest, m, im, fi, nx), hlt2),
          D.and.r(Bool.or(D.Fl(m, y, 1024), Bool.or(D.Mem(Con{z, cs}, y), D.Mem(hc, y))), D.All.held(rest, m, Con{z, cs}, hc), h2)))

def clo.at.release.b(b: Bool, +m: Cr.Cir.Cells, +o: U32, +ps: List<&2, U32>, +z: U32, +cs: List<&2, U32>, +hc: List<&2, U32>,
  +im: U32, +fi: U32, +nx: U32, eb: {U32.is_eq(z, o) == b : Bool},
  hnt: {U32.is_lt(D.Tg(m, z), 19) == False{} : Bool}, hfs: {D.Fs(m, ps, z) == Nil{} : List<&2, U32>},
  hlt: {D.Lt.all(D.Fs(m, ps, o), m, im, fi, nx) == True{} : Bool},
  h: {Bool.or(Bool.not(D.Mem(Con{z, cs}, o)), D.All.held(D.Fs(m, ps, o), m, Con{z, cs}, hc)) == True{} : Bool}) ->
  {Bool.or(Bool.not(D.Mem(cs, o)), D.All.held(D.Fs(m, ps, o), m, cs, hc)) == True{} : Bool}:
  match b:
    case True{}:
      %D.u32.eq(z, o, eb) : {Bool.or(Bool.not(D.Mem(cs, _)), D.All.held(D.Fs(m, ps, _), m, cs, hc)) == True{} : Bool}
      %Equal.sym(List<&2, U32>, D.Fs(m, ps, z), Nil{}, hfs) : {Bool.or(Bool.not(D.Mem(cs, z)), D.All.held(_, m, cs, hc)) == True{} : Bool}
      or.true(Bool.not(D.Mem(cs, z)))
    case False{}:
      or.mono.r(Bool.not(D.Mem(cs, o)), D.All.held(D.Fs(m, ps, o), m, Con{z, cs}, hc), D.All.held(D.Fs(m, ps, o), m, cs, hc),
        {(%eb : {Bool.or(Bool.not(Bool.or(_, D.Mem(cs, o))), D.All.held(D.Fs(m, ps, o), m, Con{z, cs}, hc)) == True{} : Bool}; h) :
          {Bool.or(Bool.not(D.Mem(cs, o)), D.All.held(D.Fs(m, ps, o), m, Con{z, cs}, hc)) == True{} : Bool}},
        e => held.drop(D.Fs(m, ps, o), m, z, cs, hc, im, fi, nx, hnt, hlt, e))

# M.release's Clo: z leaves the temporaries for the pend list
def clo.release(n: Nat, +m: Cr.Cir.Cells, +c: U32, +ps: List<&2, U32>, +z: U32, +cs: List<&2, U32>, +hc: List<&2, U32>,
  +im: U32, +fi: U32, +nx: U32, +hnt: {U32.is_lt(D.Tg(m, z), 19) == False{} : Bool}, +hfs: {D.Fs(m, ps, z) == Nil{} : List<&2, U32>},
  hp: {D.Pts(n, m, ps, c, im, fi, nx) == True{} : Bool}, h: {D.Clo(n, m, c, ps, Con{z, cs}, hc) == True{} : Bool}) ->
  {D.Clo(n, m, c, Con{z, ps}, cs, hc) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+(+k):
      +hp2 = hp
      +h2 = h
      +F = D.Fs(m, ps, c)
      +S1 = Bool.or(Bool.not(D.Fl(m, c, 1024)), D.All.static(F, m))
      +at = D.and.l(Bool.and(S1, Bool.or(Bool.not(D.Mem(Con{z, cs}, c)), D.All.held(F, m, Con{z, cs}, hc))), D.Clo(k, m, U32.inc(c), ps, Con{z, cs}, hc), h2)
      +ef = fs.pend2.b(U32.is_eq(z, c), m, ps, z, c, {==}, hnt, hfs)
      D.and.i(D.Clo.at(m, c, Con{z, ps}, cs, hc), D.Clo(k, m, U32.inc(c), Con{z, ps}, cs, hc),
        {(%Equal.sym(List<&2, U32>, D.Fs(m, Con{z, ps}, c), F, ef) :
            {Bool.and(Bool.or(Bool.not(D.Fl(m, c, 1024)), D.All.static(_, m)), Bool.or(Bool.not(D.Mem(cs, c)), D.All.held(_, m, cs, hc))) == True{} : Bool};
          D.and.i(S1, Bool.or(Bool.not(D.Mem(cs, c)), D.All.held(F, m, cs, hc)),
            D.and.l(S1, Bool.or(Bool.not(D.Mem(Con{z, cs}, c)), D.All.held(F, m, Con{z, cs}, hc)), at),
            clo.at.release.b(U32.is_eq(z, c), m, c, ps, z, cs, hc, im, fi, nx, {==}, hnt, hfs,
              D.and.l(D.Lt.all(F, m, im, fi, nx), D.Pts(k, m, ps, U32.inc(c), im, fi, nx), hp2),
              D.and.r(S1, Bool.or(Bool.not(D.Mem(Con{z, cs}, c)), D.All.held(F, m, Con{z, cs}, hc)), at)))) :
          {D.Clo.at(m, c, Con{z, ps}, cs, hc) == True{} : Bool}},
        clo.release(k, m, U32.inc(c), ps, z, cs, hc, im, fi, nx, hnt, hfs,
          D.and.r(D.Lt.all(F, m, im, fi, nx), D.Pts(k, m, ps, U32.inc(c), im, fi, nx), hp2),
          D.and.r(D.Clo.at(m, c, ps, Con{z, cs}, hc), D.Clo(k, m, U32.inc(c), ps, Con{z, cs}, hc), h2)))

# A new cell's number
# --------------------

def le.false.b(c: Cmp, +a: U32, +b: U32, r: N.Rel(c, U32.to_nat(a), U32.to_nat(b)), h: N.Le(1n+U32.to_nat(b), U32.to_nat(a))) ->
  {Cmp.is_le(c) == False{} : Bool}:
  match c:
    case LT{}:
      Empty.absurd({True{} == False{} : Bool}, N.not_succ_le(U32.to_nat(a),
        N.le_trans(1n+U32.to_nat(a), U32.to_nat(b), U32.to_nat(a), r, N.weaken(U32.to_nat(b), U32.to_nat(a), h))))
    case EQ{}:
      Empty.absurd({True{} == False{} : Bool}, N.not_succ_le(U32.to_nat(a), (%Equal.sym(Nat, U32.to_nat(a), U32.to_nat(b), r) : N.Le(1n+_, U32.to_nat(a)); h)))
    case GT{}:
      {==}

# a is not at most b, when b is below a
def le.false(+a: U32, +b: U32, h: N.Le(1n+U32.to_nat(b), U32.to_nat(a))) -> {U32.is_le(a, b) == False{} : Bool}:
  le.false.b(U32.cmp(a, b), a, b, N.U32.rel(a, b), h)

def lt.irr.b(c: Cmp, +a: U32, r: N.Rel(c, U32.to_nat(a), U32.to_nat(a))) -> {Cmp.is_lt(c) == False{} : Bool}:
  match c:
    case LT{}:
      Empty.absurd({True{} == False{} : Bool}, N.not_succ_le(U32.to_nat(a), r))
    case EQ{}:
      {==}
    case GT{}:
      {==}

def lt.irr(+a: U32) -> {U32.is_lt(a, a) == False{} : Bool}:
  lt.irr.b(U32.cmp(a, a), a, N.U32.rel(a, a))

# next is no cell yet: past the image, and not below itself
def ncell.next(+nx: U32, +im: U32, +fi: U32, him: N.Le(1n+U32.to_nat(im), U32.to_nat(nx))) -> {Cr.Cir.is_cell(nx, im, fi, nx) == False{} : Bool}:
  %Equal.sym(Bool, U32.is_le(nx, im), False{}, le.false(nx, im, him)) :
    {Bool.or(Bool.and(Bool.not(U32.is_zero(nx)), _), Bool.and(U32.is_le(fi, nx), U32.is_lt(nx, nx))) == False{} : Bool}
  %Equal.sym(Bool, U32.is_lt(nx, nx), False{}, lt.irr(nx)) :
    {Bool.or(Bool.and(Bool.not(U32.is_zero(nx)), False{}), Bool.and(U32.is_le(fi, nx), _)) == False{} : Bool}
  %Equal.sym(Bool, Bool.and(Bool.not(U32.is_zero(nx)), False{}), False{}, and.false(Bool.not(U32.is_zero(nx)))) :
    {Bool.or(_, Bool.and(U32.is_le(fi, nx), False{})) == False{} : Bool}
  %Equal.sym(Bool, Bool.and(U32.is_le(fi, nx), False{}), False{}, and.false(U32.is_le(fi, nx))) : {Bool.or(False{}, _) == False{} : Bool}
  {==}

# the cells from fi to next + 1: one more
def cnt.inc(+nx: U32, +fi: U32, +e: U32, hl: {U32.is_lt(nx, e) == True{} : Bool}, hfn: {U32.is_le(fi, nx) == True{} : Bool}) ->
  {Nat.sub(U32.to_nat(U32.inc(nx)), U32.to_nat(fi)) == 1n+Nat.sub(U32.to_nat(nx), U32.to_nat(fi)) : Nat}:
  Equal.trans(Nat, Nat.sub(U32.to_nat(U32.inc(nx)), U32.to_nat(fi)), Nat.sub(1n+U32.to_nat(nx), U32.to_nat(fi)), 1n+Nat.sub(U32.to_nat(nx), U32.to_nat(fi)),
    Equal.cong(Nat, Nat, w => Nat.sub(w, U32.to_nat(fi)), U32.to_nat(U32.inc(nx)), 1n+U32.to_nat(nx), D.u.inc(nx, e, D.u.lt(nx, e, hl))),
    sub.succ(U32.to_nat(nx), U32.to_nat(fi), D.u.le(fi, nx, hfn)))

def le.tbl.top() -> N.Le(1n+U32.to_nat(272), 1n+U32.to_nat(290)):
  Unit{}

# The Acc step of each heap operation (for heap_ops.bend)
# -------------------------------------------------------
#
# Each takes the operation's HSK and AccK, as its law does, and gives AccK
# after it.

# a new root keeps Acc (M.inc of a STATIC cell changes no cell)
def acc.root(+dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +r: D.Rt, +rs: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +sp: U32,
  +fs: List<&2, D.AF>, +ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  h: D.AccK(dk, ds, ks, img, m, nx, fi, im, rs, xs, sp, fs, ps, zs)) ->
  D.AccK(dk, ds, ks, img, m, nx, fi, im, Con{r, rs}, xs, sp, fs, ps, zs):
  match h:
    case Tuple{hz, Tuple{hh, Tuple{he, Tuple{hc, hcl}}}}:
      (hz, (hh, (he, (cov.root(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, r,
        List.append(&2, D.Rt, rs, List.append(&2, D.Rt, D.Tmp.held(xs), List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs))),
        List.append(&2, U32, D.Fr.cells(fs, m, sp), List.append(&2, U32, D.Tmp.cells(xs), ps)), hc), hcl))))

# stores to field 1 of cells that are no frames (no frame is one of them) keep Acc
def acc.f1(+dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +rs: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +sp: U32,
  +fs: List<&2, D.AF>, +ps: List<&2, U32>, +zs: List<&2, D.Rt>, +ws: List<&2, D.W1>,
  hac: D.AccK(dk, ds, ks, img, m, nx, fi, im, rs, xs, sp, fs, ps, zs),
  hw: {Outs(D.Fr.cells(fs, m, sp), D.W1.cells(ws)) == True{} : Bool}) ->
  D.AccK(dk, ds, ks, img, D.Put1(ws, m), nx, fi, im, rs, xs, sp, fs, ps, zs):
  match hac:
    case Tuple{hz, Tuple{hh, Tuple{he, Tuple{hc, hcl}}}}:
      +M2 = D.Put1(ws, m)
      +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
      +cs = D.Tmp.cells(xs)
      +hl = D.Tmp.held(xs)
      +ef = fr.put1(fs, ws, m, sp, hw)
      +efc = D.Ex.fst({D.Fr.cells(fs, M2, sp) == D.Fr.cells(fs, m, sp) : List<&2, U32>}, _ => {D.Fr.rts(fs, M2, sp) == D.Fr.rts(fs, m, sp) : List<&2, D.Rt>}, ef)
      +efr = D.Ex.snd({D.Fr.cells(fs, M2, sp) == D.Fr.cells(fs, m, sp) : List<&2, U32>}, _ => {D.Fr.rts(fs, M2, sp) == D.Fr.rts(fs, m, sp) : List<&2, D.Rt>}, ef)
      +RS = List.append(&2, D.Rt, rs, List.append(&2, D.Rt, hl, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)))
      +XS = List.append(&2, U32, D.Fr.cells(fs, m, sp), List.append(&2, U32, cs, ps))
      (rts.put1(dk, zs, ds, ws, m, im, fi, nx, ks, img, hz),
        (rts.put1(dk, hl, ds, ws, m, im, fi, nx, ks, img, hh),
          ({(%Equal.sym(List<&2, U32>, D.Pend.terms(ps, M2), D.Pend.terms(ps, m), pend.terms.put1(ps, ws, m)) : {D.Rt.cells(zs) == _ : List<&2, U32>}; he) :
              {D.Rt.cells(zs) == D.Pend.terms(ps, M2) : List<&2, U32>}},
            ({(%Equal.sym(List<&2, D.Rt>, D.Fr.rts(fs, M2, sp), D.Fr.rts(fs, m, sp), efr) :
                  {D.Cov(n, M2, fi, List.append(&2, D.Rt, rs, List.append(&2, D.Rt, hl, List.append(&2, D.Rt, _, zs))),
                    List.append(&2, U32, D.Fr.cells(fs, M2, sp), List.append(&2, U32, cs, ps))) == True{} : Bool};
                %Equal.sym(List<&2, U32>, D.Fr.cells(fs, M2, sp), D.Fr.cells(fs, m, sp), efc) :
                  {D.Cov(n, M2, fi, RS, List.append(&2, U32, _, List.append(&2, U32, cs, ps))) == True{} : Bool};
                %Equal.sym(Bool, D.Cov(n, M2, fi, RS, XS), D.Cov(n, m, fi, RS, XS), cov.put1(n, ws, m, fi, RS, XS)) : {_ == True{} : Bool};
                hc) :
                {D.Cov(n, M2, fi, List.append(&2, D.Rt, rs, List.append(&2, D.Rt, hl, List.append(&2, D.Rt, D.Fr.rts(fs, M2, sp), zs))),
                  List.append(&2, U32, D.Fr.cells(fs, M2, sp), List.append(&2, U32, cs, ps))) == True{} : Bool}},
              {(%Equal.sym(Bool, D.Clo(n, M2, fi, ps, cs, D.Rt.cells(hl)), D.Clo(n, m, fi, ps, cs, D.Rt.cells(hl)), clo.put1(n, ws, m, fi, ps, cs, D.Rt.cells(hl))) :
                  {_ == True{} : Bool}; hcl) : {D.Clo(n, M2, fi, ps, cs, D.Rt.cells(hl)) == True{} : Bool}}))))

# M.inc of the held term cell c of u (a tag below 19): c is a root, and its
# count (field 1) gets v
def acc.inc(+dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>,
  +sp: U32, +pend: U32, +ps: List<&2, U32>, +c: U32, +u: Bk.Term, +v: U32, +xs: List<&2, D.TmpE>, +zs: List<&2, D.Rt>,
  hs: D.HSK(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps),
  hac: D.AccK(dk, ds, ks, img, m, nx, fi, im, os, xs, sp, fs, ps, zs),
  ht: {U32.is_lt(D.Tg(m, c), 19) == True{} : Bool}) ->
  D.AccK(dk, ds, ks, img, X.X.put(m, 1n, c, v), nx, fi, im, Con{D.Rt{c, u}, os}, xs, sp, fs, ps, zs):
  match hs:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{hf, _}}}}:
      acc.f1(dk, ds, ks, img, m, nx, fi, im, Con{D.Rt{c, u}, os}, xs, sp, fs, ps, zs, [D.W1{c, v}],
        acc.root(dk, ds, ks, img, m, nx, fi, im, D.Rt{c, u}, os, xs, sp, fs, ps, zs, hac),
        outs.one(D.Fr.cells(fs, m, sp), c, fr.out.lo(dk, ds, m, im, fi, nx, ks, img, ps, fs, sp, c, hf, lt.below32(D.Tg(m, c), ht))))

# M.dec of the root c of u, a term cell, to the count 0: field 1 gets d, then
# pend; c goes to the pend list, and its root to the zombies
def acc.dec.pend(+dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>,
  +sp: U32, +pend: U32, +ps: List<&2, U32>, +c: U32, +u: Bk.Term, +d: U32, +xs: List<&2, D.TmpE>, +zs: List<&2, D.Rt>,
  hs: D.HSK(dk, ds, ks, img, m, nx, fi, im, Con{D.Rt{c, u}, os}, bs, fs, sp, pend, ps),
  hac: D.AccK(dk, ds, ks, img, m, nx, fi, im, Con{D.Rt{c, u}, os}, xs, sp, fs, ps, zs),
  ht: {U32.is_lt(D.Tg(m, c), 19) == True{} : Bool}) ->
  D.AccK(dk, ds, ks, img, X.X.put(X.X.put(m, 1n, c, d), 1n, c, pend), nx, fi, im, os, xs, sp, fs, Con{c, ps},
    Con{D.Rt{c, u}, zs}):
  match hs hac:
    case Tuple{Tuple{hcu, _}, Tuple{_, Tuple{_, Tuple{hf, _}}}} Tuple{hz, Tuple{hh, Tuple{he, Tuple{hc, hcl}}}}:
      +r = {D.Rt{c, u} : D.Rt}
      +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
      +cs = D.Tmp.cells(xs)
      +hl = D.Tmp.held(xs)
      +frt = D.Fr.rts(fs, m, sp)
      +frc = D.Fr.cells(fs, m, sp)
      +RS0 = List.append(&2, D.Rt, Con{r, os}, List.append(&2, D.Rt, hl, List.append(&2, D.Rt, frt, zs)))
      +XS1 = List.append(&2, U32, frc, List.append(&2, U32, cs, Con{c, ps}))
      +ht2 = ht
      +hc1 = cov.cell(n, m, fi, c, RS0, List.append(&2, U32, frc, List.append(&2, U32, cs, ps)), hc)
      +hc2 = cov.mv(D.Cov(n, m, fi, RS0, Con{c, List.append(&2, U32, frc, List.append(&2, U32, cs, ps))}),
        D.Cov(n, m, fi, RS0, List.append(&2, U32, frc, Con{c, List.append(&2, U32, cs, ps)})),
        cov.perm.x(n, m, fi, RS0, Nil{}, [c], frc, List.append(&2, U32, cs, ps)), hc1)
      +hc3 = cov.mv(D.Cov(n, m, fi, RS0, List.append(&2, U32, frc, Con{c, List.append(&2, U32, cs, ps)})), D.Cov(n, m, fi, RS0, XS1),
        cov.perm.x(n, m, fi, RS0, frc, [c], cs, ps), hc2)
      +W = List.append(&2, D.Rt, frt, zs)
      +hr1 = cov.mv(D.Cov(n, m, fi, RS0, XS1), D.Cov(n, m, fi, List.append(&2, D.Rt, os, Con{r, List.append(&2, D.Rt, hl, W)}), XS1),
        cov.perm(n, m, fi, Nil{}, [r], os, List.append(&2, D.Rt, hl, W), XS1), hc3)
      +hr2 = cov.mv(D.Cov(n, m, fi, List.append(&2, D.Rt, os, Con{r, List.append(&2, D.Rt, hl, W)}), XS1),
        D.Cov(n, m, fi, List.append(&2, D.Rt, os, List.append(&2, D.Rt, hl, Con{r, W})), XS1), cov.perm(n, m, fi, os, [r], hl, W, XS1), hr1)
      +hr3 = cov.mv(D.Cov(n, m, fi, List.append(&2, D.Rt, os, List.append(&2, D.Rt, hl, Con{r, W})), XS1),
        D.Cov(n, m, fi, List.append(&2, D.Rt, List.append(&2, D.Rt, os, hl), Con{r, W}), XS1),
        Equal.cong(List<&2, D.Rt>, Bool, L => D.Cov(n, m, fi, L, XS1), List.append(&2, D.Rt, os, List.append(&2, D.Rt, hl, Con{r, W})),
          List.append(&2, D.Rt, List.append(&2, D.Rt, os, hl), Con{r, W}),
          Equal.sym(List<&2, D.Rt>, List.append(&2, D.Rt, List.append(&2, D.Rt, os, hl), Con{r, W}), List.append(&2, D.Rt, os, List.append(&2, D.Rt, hl, Con{r, W})),
            app.assoc(os, hl, Con{r, W}))), hr2)
      +hr4 = cov.mv(D.Cov(n, m, fi, List.append(&2, D.Rt, List.append(&2, D.Rt, os, hl), Con{r, W}), XS1),
        D.Cov(n, m, fi, List.append(&2, D.Rt, List.append(&2, D.Rt, os, hl), List.append(&2, D.Rt, frt, Con{r, zs})), XS1),
        cov.perm(n, m, fi, List.append(&2, D.Rt, os, hl), [r], frt, zs, XS1), hr3)
      +hr5 = cov.mv(D.Cov(n, m, fi, List.append(&2, D.Rt, List.append(&2, D.Rt, os, hl), List.append(&2, D.Rt, frt, Con{r, zs})), XS1),
        D.Cov(n, m, fi, List.append(&2, D.Rt, os, List.append(&2, D.Rt, hl, List.append(&2, D.Rt, frt, Con{r, zs}))), XS1),
        Equal.cong(List<&2, D.Rt>, Bool, L => D.Cov(n, m, fi, L, XS1), List.append(&2, D.Rt, List.append(&2, D.Rt, os, hl), List.append(&2, D.Rt, frt, Con{r, zs})),
          List.append(&2, D.Rt, os, List.append(&2, D.Rt, hl, List.append(&2, D.Rt, frt, Con{r, zs}))),
          app.assoc(os, hl, List.append(&2, D.Rt, frt, Con{r, zs}))), hr4)
      +hcl2 = cov.mv(D.Clo(n, m, fi, ps, cs, D.Rt.cells(hl)), D.Clo(n, m, fi, Con{c, ps}, cs, D.Rt.cells(hl)),
        Equal.sym(Bool, D.Clo(n, m, fi, Con{c, ps}, cs, D.Rt.cells(hl)), D.Clo(n, m, fi, ps, cs, D.Rt.cells(hl)), clo.pend(n, m, fi, ps, c, cs, D.Rt.cells(hl), ht2)),
        hcl)
      +pt = {(%Equal.sym(Bool, U32.is_lt(D.Tg(m, c), 19), True{}, ht2) :
          {Con{c, D.Rt.cells(zs)} == Bool.pick(List<&2, U32>, _, Con{c, D.Pend.terms(ps, m)}, D.Pend.terms(ps, m)) : List<&2, U32>};
        Equal.cong(List<&2, U32>, List<&2, U32>, l => Con{c, l}, D.Rt.cells(zs), D.Pend.terms(ps, m), he)) :
        {D.Rt.cells(Con{r, zs}) == D.Pend.terms(Con{c, ps}, m) : List<&2, U32>}}
      +acc1 = {((hcu, hz), (hh, (pt, (hr5, hcl2)))) : D.AccK(dk, ds, ks, img, m, nx, fi, im, os, xs, sp, fs, Con{c, ps}, Con{r, zs})}
      acc.f1(dk, ds, ks, img, m, nx, fi, im, os, xs, sp, fs, Con{c, ps}, Con{r, zs}, [D.W1{c, pend}, D.W1{c, d}], acc1,
        outs.two(D.Fr.cells(fs, m, sp), c, fr.out.lo(dk, ds, m, im, fi, nx, ks, img, ps, fs, sp, c, hf, lt.below32(D.Tg(m, c), ht2))))

# a root whose cell is STATIC or keeps a pointer without it leaves the roots:
# each of its nodes is still accounted for, through the cell that points to it
def acc.drop(+dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>,
  +sp: U32, +pend: U32, +ps: List<&2, U32>, +c: U32, +u: Bk.Term, +xs: List<&2, D.TmpE>, +zs: List<&2, D.Rt>,
  hs: D.HSK(dk, ds, ks, img, m, nx, fi, im, Con{D.Rt{c, u}, os}, bs, fs, sp, pend, ps),
  hac: D.AccK(dk, ds, ks, img, m, nx, fi, im, Con{D.Rt{c, u}, os}, xs, sp, fs, ps, zs),
  hd: {D.Hd(m, nx, fi, ps, D.Rt.cells(os), c) == True{} : Bool}) ->
  D.AccK(dk, ds, ks, img, m, nx, fi, im, os, xs, sp, fs, ps, zs):
  ?TODO

# M.dec of the root c of u, a term cell, to a count above 0 (c keeps a
# pointer): c is no root, and its count gets d
def acc.dec.keep(+dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>,
  +sp: U32, +pend: U32, +ps: List<&2, U32>, +c: U32, +u: Bk.Term, +d: U32, +xs: List<&2, D.TmpE>, +zs: List<&2, D.Rt>,
  hs: D.HSK(dk, ds, ks, img, m, nx, fi, im, Con{D.Rt{c, u}, os}, bs, fs, sp, pend, ps),
  hac: D.AccK(dk, ds, ks, img, m, nx, fi, im, Con{D.Rt{c, u}, os}, xs, sp, fs, ps, zs),
  ht: {U32.is_lt(D.Tg(m, c), 19) == True{} : Bool},
  hd: {D.Hd(m, nx, fi, ps, D.Rt.cells(os), c) == True{} : Bool}) ->
  D.AccK(dk, ds, ks, img, X.X.put(m, 1n, c, d), nx, fi, im, os, xs, sp, fs, ps, zs):
  ?TODO

# M.release of z, of the machine's own kinds (tag 32 or more), out of the pend
# list and holding no pointer (so no frame): z leaves the temporaries for the
# pend list, and its field 1 gets pend
def acc.release(+dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>,
  +sp: U32, +pend: U32, +ps: List<&2, U32>, +z: U32, +xs: List<&2, D.TmpE>, +zs: List<&2, D.Rt>,
  hs: D.HSK(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps),
  hac: D.AccK(dk, ds, ks, img, m, nx, fi, im, os, Con{D.TmpE{z, Nil{}}, xs}, sp, fs, ps, zs),
  ht: {U32.is_lt(D.Tg(m, z), 32) == False{} : Bool},
  hm: {D.Mem(ps, z) == False{} : Bool},
  hfs: {D.Fs(m, ps, z) == Nil{} : List<&2, U32>}) ->
  D.AccK(dk, ds, ks, img, X.X.put(m, 1n, z, pend), nx, fi, im, os, xs, sp, fs, Con{z, ps}, zs):
  match hs hac:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{hf, Tuple{Tuple{_, Tuple{_, Tuple{_, Tuple{hpts, _}}}}, _}}}}} Tuple{hz, Tuple{hh, Tuple{he, Tuple{hc, hcl}}}}:
      +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
      +cs = D.Tmp.cells(xs)
      +hl = D.Tmp.held(xs)
      +RS = List.append(&2, D.Rt, os, List.append(&2, D.Rt, hl, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)))
      +frc = D.Fr.cells(fs, m, sp)
      +hnt = nlt.below19(D.Tg(m, z), ht)
      +hm2 = hm
      +hfs2 = hfs
      +pt = {(%Equal.sym(Bool, U32.is_lt(D.Tg(m, z), 19), False{}, hnt) :
          {D.Rt.cells(zs) == Bool.pick(List<&2, U32>, _, Con{z, D.Pend.terms(ps, m)}, D.Pend.terms(ps, m)) : List<&2, U32>}; he) :
        {D.Rt.cells(zs) == D.Pend.terms(Con{z, ps}, m) : List<&2, U32>}}
      +hc2 = cov.mv(D.Cov(n, m, fi, RS, List.append(&2, U32, frc, Con{z, List.append(&2, U32, cs, ps)})),
        D.Cov(n, m, fi, RS, List.append(&2, U32, frc, List.append(&2, U32, cs, Con{z, ps}))), cov.perm.x(n, m, fi, RS, frc, [z], cs, ps), hc)
      +hcl2 = clo.release(n, m, fi, ps, z, cs, D.Rt.cells(hl), im, fi, nx, hnt, hfs2, hpts, hcl)
      +acc1 = {(hz, (hh, (pt, (hc2, hcl2)))) : D.AccK(dk, ds, ks, img, m, nx, fi, im, os, xs, sp, fs, Con{z, ps}, zs)}
      acc.f1(dk, ds, ks, img, m, nx, fi, im, os, xs, sp, fs, Con{z, ps}, zs, [D.W1{z, pend}], acc1,
        outs.one(D.Fr.cells(fs, m, sp), z, fr.out.nil(dk, ds, m, im, fi, nx, ks, img, ps, fs, sp, z, hf, hm2, hfs2)))

# a store at z, the first temporary, which nothing points to, is not STATIC,
# is out of the pend list, holds no pointer (so no frame) and is no root of a
# temporary's term, of a cell x that is not STATIC whose pointers are those
# of the roots us: the roots us become z's terms
def acc.store(+dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +us: List<&2, D.Rt>, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>,
  +fs: List<&2, D.AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>, +z: U32, +x: Cr.Cir.Cell, +xs: List<&2, D.TmpE>,
  +zs: List<&2, D.Rt>,
  hs: D.HSK(dk, ds, ks, img, m, nx, fi, im, List.append(&2, D.Rt, us, os), bs, fs, sp, pend, ps),
  hac: D.AccK(dk, ds, ks, img, m, nx, fi, im, List.append(&2, D.Rt, us, os), xs, sp, fs, ps, zs),
  hzx: {D.Tmp.head(xs) == Some{z} : Maybe<&2, U32>},
  hm: {D.Mem(ps, z) == False{} : Bool},
  hzs: {D.Fl(m, z, 1024) == False{} : Bool},
  hz0: {D.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, D.Rt.cells(List.append(&2, D.Rt, us, os)), z) == 0n : Nat},
  hzf: {D.Fs(m, ps, z) == Nil{} : List<&2, U32>},
  hnh: {D.NeAll(D.Rt.cells(D.Tmp.held(xs)), z) == True{} : Bool},
  hxs: {D.FlW(Cr.Cir.Cell.get(0n, x), 1024) == False{} : Bool},
  hf: {D.Fs(Cr.Cir.Cells.set(m, z, x), ps, z) == D.Rt.cells(us) : List<&2, U32>}) ->
  D.AccK(dk, ds, ks, img, Cr.Cir.Cells.set(m, z, x), nx, fi, im, os, D.Tmp.hold(us, xs), sp, fs, ps, zs):
  ?TODO

# the flag DATA of the cell c: the tag, the flag STATIC and fields 1 to 4
# stay; the zombies and the temporaries' terms are given after it
def acc.flag(+dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +rs: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +sp: U32,
  +fs: List<&2, D.AF>, +ps: List<&2, U32>, +zs: List<&2, D.Rt>, +c: U32,
  hac: D.AccK(dk, ds, ks, img, m, nx, fi, im, rs, xs, sp, fs, ps, zs),
  hz: D.RtsK(dk, ds, Cr.Cir.Cells.set(m, c, Cr.Cir.Cell.set(0n, Cr.Cir.Cells.get(m, c), U32.or(D.Fd(0n, m, c), 512))), im, fi, nx,
    ks, img, zs),
  hh: D.RtsK(dk, ds, Cr.Cir.Cells.set(m, c, Cr.Cir.Cell.set(0n, Cr.Cir.Cells.get(m, c), U32.or(D.Fd(0n, m, c), 512))), im, fi, nx,
    ks, img, D.Tmp.held(xs))) ->
  D.AccK(dk, ds, ks, img, Cr.Cir.Cells.set(m, c, Cr.Cir.Cell.set(0n, Cr.Cir.Cells.get(m, c), U32.or(D.Fd(0n, m, c), 512))), nx, fi,
    im, rs, xs, sp, fs, ps, zs):
  match hac:
    case Tuple{_, Tuple{_, Tuple{he, Tuple{hc, hcl}}}}:
      +M2 = Flag(m, c)
      +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
      +cs = D.Tmp.cells(xs)
      +hl = D.Tmp.held(xs)
      +ef = fr.flag(fs, m, c, sp)
      +efc = D.Ex.fst({D.Fr.cells(fs, M2, sp) == D.Fr.cells(fs, m, sp) : List<&2, U32>}, _ => {D.Fr.rts(fs, M2, sp) == D.Fr.rts(fs, m, sp) : List<&2, D.Rt>}, ef)
      +efr = D.Ex.snd({D.Fr.cells(fs, M2, sp) == D.Fr.cells(fs, m, sp) : List<&2, U32>}, _ => {D.Fr.rts(fs, M2, sp) == D.Fr.rts(fs, m, sp) : List<&2, D.Rt>}, ef)
      +RS = List.append(&2, D.Rt, rs, List.append(&2, D.Rt, hl, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)))
      +XS = List.append(&2, U32, D.Fr.cells(fs, m, sp), List.append(&2, U32, cs, ps))
      (hz, (hh,
        ({(%Equal.sym(List<&2, U32>, D.Pend.terms(ps, M2), D.Pend.terms(ps, m), pend.terms.flag(ps, m, c)) : {D.Rt.cells(zs) == _ : List<&2, U32>}; he) :
            {D.Rt.cells(zs) == D.Pend.terms(ps, M2) : List<&2, U32>}},
          ({(%Equal.sym(List<&2, D.Rt>, D.Fr.rts(fs, M2, sp), D.Fr.rts(fs, m, sp), efr) :
                {D.Cov(n, M2, fi, List.append(&2, D.Rt, rs, List.append(&2, D.Rt, hl, List.append(&2, D.Rt, _, zs))),
                  List.append(&2, U32, D.Fr.cells(fs, M2, sp), List.append(&2, U32, cs, ps))) == True{} : Bool};
              %Equal.sym(List<&2, U32>, D.Fr.cells(fs, M2, sp), D.Fr.cells(fs, m, sp), efc) :
                {D.Cov(n, M2, fi, RS, List.append(&2, U32, _, List.append(&2, U32, cs, ps))) == True{} : Bool};
              %Equal.sym(Bool, D.Cov(n, M2, fi, RS, XS), D.Cov(n, m, fi, RS, XS), cov.flag(n, m, c, fi, RS, XS)) : {_ == True{} : Bool};
              hc) :
              {D.Cov(n, M2, fi, List.append(&2, D.Rt, rs, List.append(&2, D.Rt, hl, List.append(&2, D.Rt, D.Fr.rts(fs, M2, sp), zs))),
                List.append(&2, U32, D.Fr.cells(fs, M2, sp), List.append(&2, U32, cs, ps))) == True{} : Bool}},
            {(%Equal.sym(Bool, D.Clo(n, M2, fi, ps, cs, D.Rt.cells(hl)), D.Clo(n, m, fi, ps, cs, D.Rt.cells(hl)), clo.flag(n, m, c, fi, ps, cs, D.Rt.cells(hl))) :
                {_ == True{} : Bool}; hcl) : {D.Clo(n, M2, fi, ps, cs, D.Rt.cells(hl)) == True{} : Bool}}))))

# a new cell, all zeros, at next nx (the pend list is empty; nx is below the
# cell e): it is a temporary, and next grows; the temporaries' terms are
# given after it
def acc.fresh(+dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>,
  +sp: U32, +pend: U32, +xs: List<&2, D.TmpE>, +zs: List<&2, D.Rt>, +e: U32,
  hs: D.HSK(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, Nil{}),
  hac: D.AccK(dk, ds, ks, img, m, nx, fi, im, os, xs, sp, fs, Nil{}, zs),
  hl: {U32.is_lt(nx, e) == True{} : Bool},
  hh: D.RtsK(dk, ds, Cr.Cir.Cells.set(m, nx, Cr.Cir.Cell.zero()), im, fi, U32.inc(nx), ks, img, D.Tmp.held(xs))) ->
  D.AccK(dk, ds, ks, img, Cr.Cir.Cells.set(m, nx, Cr.Cir.Cell.zero()), U32.inc(nx), fi, im, os, Con{D.TmpE{nx, Nil{}}, xs}, sp,
    fs, Nil{}, Nil{}):
  match hs hac:
    case Tuple{hro, Tuple{_, Tuple{_, Tuple{+hf, Tuple{Tuple{_, Tuple{_, Tuple{_, Tuple{hpts, Tuple{_, hfn}}}}}, Tuple{tb, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e290, eim}}}}}}}}}}}} Tuple{hz, Tuple{hhl, Tuple{he, Tuple{hc, hcl}}}}:
      +Z = Cr.Cir.Cell.zero()
      +M2 = Cr.Cir.Cells.set(m, nx, Z)
      +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
      +cs = D.Tmp.cells(xs)
      +hl0 = D.Tmp.held(xs)
      +frt = D.Fr.rts(fs, m, sp)
      +frc = D.Fr.cells(fs, m, sp)
      +hfn2 = {hfn : {U32.is_le(fi, nx) == True{} : Bool}}
      +le = D.u.le(fi, nx, hfn2)
      +hz0 = D.add.sub(U32.to_nat(fi), U32.to_nat(nx), le)
      +him = N.le_trans(1n+U32.to_nat(im), U32.to_nat(fi), U32.to_nat(nx), D.u.lt(im, fi, eim), le)
      +h290 = N.le_trans(1n+U32.to_nat(290), 1n+U32.to_nat(im), U32.to_nat(nx), D.u.le(290, im, e290), him)
      +hnc = ncell.next(nx, im, fi, him)
      +zn = zs.nil(zs, he)
      +RS0 = List.append(&2, D.Rt, os, List.append(&2, D.Rt, hl0, List.append(&2, D.Rt, frt, Nil{})))
      +XS0 = List.append(&2, U32, frc, List.append(&2, U32, cs, Nil{}))
      +hrs = rtsk.app(dk, os, List.append(&2, D.Rt, hl0, List.append(&2, D.Rt, frt, Nil{})), ds, m, im, fi, nx, ks, img, hro,
        rtsk.app(dk, hl0, List.append(&2, D.Rt, frt, Nil{}), ds, m, im, fi, nx, ks, img, hhl,
          rtsk.app(dk, frt, Nil{}, ds, m, im, fi, nx, ks, img, frs.rtsk(dk, ds, m, im, fi, nx, ks, img, Nil{}, fs, sp, hf), Unit{})))
      +hn0 = nodes.notcell(RS0, dk, ds, m, im, fi, nx, ks, img, nx, hrs, hnc)
      +hc0 = {(%zn : {D.Cov(n, m, fi, List.append(&2, D.Rt, os, List.append(&2, D.Rt, hl0, List.append(&2, D.Rt, frt, _))), XS0) == True{} : Bool}; hc) :
        {D.Cov(n, m, fi, RS0, XS0) == True{} : Bool}}
      +hc1 = cov.fresh(n, m, fi, nx, Z, RS0, XS0, hz0, hn0, hc0)
      +hc2 = cov.mv(D.Cov(1n+n, M2, fi, RS0, Con{nx, XS0}), D.Cov(1n+n, M2, fi, RS0, List.append(&2, U32, frc, Con{nx, List.append(&2, U32, cs, Nil{})})),
        cov.perm.x(1n+n, M2, fi, RS0, Nil{}, [nx], frc, List.append(&2, U32, cs, Nil{})), hc1)
      +ef = fr.set(fs, m, sp, nx, Z, fr.out.cell(dk, ds, m, im, fi, nx, ks, img, Nil{}, fs, sp, nx, hf, hnc))
      +efc = D.Ex.fst({D.Fr.cells(fs, M2, sp) == frc : List<&2, U32>}, _ => {D.Fr.rts(fs, M2, sp) == frt : List<&2, D.Rt>}, ef)
      +efr = D.Ex.snd({D.Fr.cells(fs, M2, sp) == frc : List<&2, U32>}, _ => {D.Fr.rts(fs, M2, sp) == frt : List<&2, D.Rt>}, ef)
      +ecnt = cnt.inc(nx, fi, e, hl, hfn2)
      +h272 = Equal.trans(U32, D.Fd(2n, M2, 272), D.Fd(2n, m, 272), 0,
        Equal.cong(Cr.Cir.Cell, U32, y => Cr.Cir.Cell.get(2n, y), Cr.Cir.Cells.get(M2, 272), Cr.Cir.Cells.get(m, 272),
          D.cl.go(m, 272, nx, Z, ne.lt(272, nx, N.le_trans(1n+U32.to_nat(272), 1n+U32.to_nat(290), U32.to_nat(nx), le.tbl.top(), h290)))),
        {D.tbl.mask(m, im, fi, nx, Bk.Term.Var{0n}, tb) : {D.Fd(2n, m, 272) == 0 : U32}})
      +hcl1 = clo.fresh(n, m, fi, nx, cs, D.Rt.cells(hl0), im, fi, hz0, D.TblR.of(n, m, fi, nx, h290), h272, hpts, hcl)
      +N2 = Nat.sub(U32.to_nat(U32.inc(nx)), U32.to_nat(fi))
      +scnt = Equal.sym(Nat, N2, 1n+n, ecnt)
      +sfr = Equal.sym(List<&2, D.Rt>, D.Fr.rts(fs, M2, sp), frt, efr)
      +sfc = Equal.sym(List<&2, U32>, D.Fr.cells(fs, M2, sp), frc, efc)
      +hc3 = {(%scnt : {D.Cov(_, M2, fi, List.append(&2, D.Rt, os, List.append(&2, D.Rt, hl0, List.append(&2, D.Rt, D.Fr.rts(fs, M2, sp), Nil{}))),
              List.append(&2, U32, D.Fr.cells(fs, M2, sp), Con{nx, List.append(&2, U32, cs, Nil{})})) == True{} : Bool};
            %sfr : {D.Cov(1n+n, M2, fi, List.append(&2, D.Rt, os, List.append(&2, D.Rt, hl0, List.append(&2, D.Rt, _, Nil{}))),
              List.append(&2, U32, D.Fr.cells(fs, M2, sp), Con{nx, List.append(&2, U32, cs, Nil{})})) == True{} : Bool};
            %sfc : {D.Cov(1n+n, M2, fi, RS0, List.append(&2, U32, _, Con{nx, List.append(&2, U32, cs, Nil{})})) == True{} : Bool};
            hc2) :
          {D.Cov(N2, M2, fi, List.append(&2, D.Rt, os, List.append(&2, D.Rt, hl0, List.append(&2, D.Rt, D.Fr.rts(fs, M2, sp), Nil{}))),
            List.append(&2, U32, D.Fr.cells(fs, M2, sp), Con{nx, List.append(&2, U32, cs, Nil{})})) == True{} : Bool}}
      +hcl2 = {(%scnt : {D.Clo(_, M2, fi, Nil{}, Con{nx, cs}, D.Rt.cells(hl0)) == True{} : Bool}; hcl1) :
        {D.Clo(N2, M2, fi, Nil{}, Con{nx, cs}, D.Rt.cells(hl0)) == True{} : Bool}}
      (Unit{}, (hh, ({==}, (hc3, hcl2))))

# each of the cells ys is one of P, or STATIC or has a pointer (Hd)
def Kept(ys: List<&2, U32>, +P: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +ps: List<&2, U32>, +rs: List<&2, U32>) ->
  Bool:
  match ys:
    case Nil{}:
      True{}
    case Con{+y, rest}:
      Bool.and(Bool.or(D.Mem(P, y), D.Hd(m, nx, fi, ps, rs, y)), Kept(rest, P, m, nx, fi, ps, rs))

# M.alloc from the pend list (cov.reuse): its first cell p, which nothing
# points to and no temporary's term has as its root, gets zeros after its
# parts lost a pointer (ws: the stores to their field 1); the parts P went
# to the pend list (P ++ ps1), each other part keeps a pointer after: Acc
# holds with p a temporary, and the parts P zombies
def acc.reuse(+dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>,
  +sp: U32, +pend: U32, +p: U32, +ps1: List<&2, U32>, +ws: List<&2, D.W1>, +P: List<&2, U32>, +pend2: U32,
  +xs: List<&2, D.TmpE>, +zs: List<&2, D.Rt>,
  hs: D.HSK(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, Con{p, ps1}),
  hac: D.AccK(dk, ds, ks, img, m, nx, fi, im, os, xs, sp, fs, Con{p, ps1}, zs),
  hpn: {D.Mem(ps1, p) == False{} : Bool},
  hnh: {D.NeAll(D.Rt.cells(D.Tmp.held(xs)), p) == True{} : Bool},
  hw: {D.Took(ws, Con{p, ps1}, m) == True{} : Bool},
  hPp: {D.AllIn(P, D.Fs(m, Con{p, ps1}, p)) == True{} : Bool},
  hs2: D.HSK(dk, ds, ks, img, Cr.Cir.Cells.set(D.Put1(ws, m), p, Cr.Cir.Cell.zero()), nx, fi, im, os, bs, fs, sp, pend2,
    List.append(&2, U32, P, ps1)),
  hk: {Kept(D.Fs(m, Con{p, ps1}, p), P, Cr.Cir.Cells.set(D.Put1(ws, m), p, Cr.Cir.Cell.zero()), nx, fi, List.append(&2, U32, P, ps1),
    D.Rt.cells(os)) == True{} : Bool}) ->
  D.Ex(List<&2, D.Rt>, zs2 => D.AccK(dk, ds, ks, img, Cr.Cir.Cells.set(D.Put1(ws, m), p, Cr.Cir.Cell.zero()), nx, fi, im, os,
    Con{D.TmpE{p, Nil{}}, xs}, sp, fs, List.append(&2, U32, P, ps1), zs2)):
  ?TODO
