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
  ?TODO

# a new cell, all zeros, at next nx (from fi on, below the cell e): one more
# own cell, not STATIC
def stat.fresh(+m: Cr.Cir.Cells, +nx: U32, +fi: U32, +e: U32, hfn: {U32.is_le(fi, nx) == True{} : Bool},
  hl: {U32.is_lt(nx, e) == True{} : Bool}) ->
  {D.Stat(Nat.sub(U32.to_nat(U32.inc(nx)), U32.to_nat(fi)), Cr.Cir.Cells.set(m, nx, Cr.Cir.Cell.zero()), fi) ==
    D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi) : Nat}:
  ?TODO

# Stores to field 1
# -----------------

# each of the cells xs is none of ys
def Outs(xs: List<&2, U32>, +ys: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, rest}:
      Bool.and(Bool.not(D.Mem(ys, x)), Outs(rest, ys))

# stores to field 1 keep every term (IsCK reads fields 0, 2, 3 and 4)
def rts.put1(+dk: Bool, xs: List<&2, D.Rt>, +ds: List<&2, Bk.Def>, +ws: List<&2, D.W1>, +m: Cr.Cir.Cells, +im: U32, +fi: U32,
  +nx: U32, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, h: D.RtsK(dk, ds, m, im, fi, nx, ks, img, xs)) ->
  D.RtsK(dk, ds, D.Put1(ws, m), im, fi, nx, ks, img, xs):
  ?TODO

# a cell of a tag below 32 is no frame
def fr.out.lo(+dk: Bool, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +sp: U32, fs: List<&2, D.AF>, +c: U32,
  hf: D.FrsK(dk, ds, m, im, fi, nx, ks, img, ps, sp, fs), ht: {U32.is_lt(D.Tg(m, c), 32) == True{} : Bool}) ->
  {D.Mem(D.Fr.cells(fs, m, sp), c) == False{} : Bool}:
  ?TODO

# a cell out of the pend list that holds no pointer is no frame
def fr.out.nil(+dk: Bool, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +sp: U32, fs: List<&2, D.AF>, +c: U32,
  hf: D.FrsK(dk, ds, m, im, fi, nx, ks, img, ps, sp, fs), hm: {D.Mem(ps, c) == False{} : Bool},
  hfs: {D.Fs(m, ps, c) == Nil{} : List<&2, U32>}) ->
  {D.Mem(D.Fr.cells(fs, m, sp), c) == False{} : Bool}:
  ?TODO

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
  ?TODO

# stores to field 1 of cells that are no frames keep Acc
def acc.f1(+dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +rs: List<&2, D.Rt>, +xs: List<&2, D.TmpE>, +sp: U32,
  +fs: List<&2, D.AF>, +ps: List<&2, U32>, +zs: List<&2, D.Rt>, +ws: List<&2, D.W1>,
  hac: D.AccK(dk, ds, ks, img, m, nx, fi, im, rs, xs, sp, fs, ps, zs),
  hw: {Outs(D.W1.cells(ws), D.Fr.cells(fs, m, sp)) == True{} : Bool}) ->
  D.AccK(dk, ds, ks, img, D.Put1(ws, m), nx, fi, im, rs, xs, sp, fs, ps, zs):
  ?TODO

# M.inc of the held term cell c of u (a tag below 19): c is a root, and its
# count (field 1) gets v
def acc.inc(+dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>,
  +sp: U32, +pend: U32, +ps: List<&2, U32>, +c: U32, +u: Bk.Term, +v: U32, +xs: List<&2, D.TmpE>, +zs: List<&2, D.Rt>,
  hs: D.HSK(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps),
  hac: D.AccK(dk, ds, ks, img, m, nx, fi, im, os, xs, sp, fs, ps, zs),
  ht: {U32.is_lt(D.Tg(m, c), 19) == True{} : Bool}) ->
  D.AccK(dk, ds, ks, img, X.X.put(m, 1n, c, v), nx, fi, im, Con{D.Rt{c, u}, os}, xs, sp, fs, ps, zs):
  ?TODO

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
  ?TODO

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
  ?TODO

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
  ?TODO

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
  ?TODO

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
