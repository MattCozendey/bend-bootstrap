# compiler: the free variables of Eval's terms
# ============================================
#
# The machine's copy needs the locals' free variables below 2^31, so layer B
# bounds the free variables (PM.Term.below) of every term that Eval reaches:
#
# - Defs.below(ds, B): the body of every def of ds is below B;
# - (a) Eval never raises the bound (fv.step, fv.steps), and the start term
#   is closed (fv.start): a call unfolds a body whose leaf, under the env e
#   of the case tree's binders, is below B + |e|; Term.subst(u, e, 0) puts in
#   e's arguments, parts of the call and so below B, and moves the rest down
#   by |e| (fv.walk, fv.sb). Every other step's result is made of the
#   redex's parts (fv.st);
# - (b) the reader's bound (fv.read): a book of fewer than 2^26 bytes
#   (Img.small) holds every Var index as a unary Nat of one 2-byte token per
#   unit, so each index is below 2^25. The reader's invariant (fv.Sok): after
#   c tokens, every Nat of its stack is below c and every term below c.
import Base
import ../../Shared/shared.bend as Sd
import ../../Book/impl.bend as Bk
import ../../Eval/impl.bend as El
import ../../Program/impl.bend as Pg
import ../need_big.bend as N
import ./definitions.bend as PM
import ./copy_terms.bend as CT
import ../img_small.bend as I

# The bound of the defs
# ---------------------

# every def's body is below B
def Defs.below(ds: List<&2, Bk.Def>, +B: Nat) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case Con{Bk.Def{_, _, v, _}, rest}:
      Bool.and(PM.Term.below(v, B), Defs.below(rest, B))

# Kit
# ---

def fv.tf(-G: Type, h: {False{} == True{} : Bool}) -> G:
  Empty.absurd(G, N.false_ne_true(h))

def fv.ft(-G: Type, h: {True{} == False{} : Bool}) -> G:
  Empty.absurd(G, N.true_ne_false(h))

def fv.and_l(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      fv.tf({False{} == True{} : Bool}, h)

def fv.and_r(a: Bool, b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      fv.tf({b == True{} : Bool}, h)

def fv.and_i(-a: Bool, -b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  %Equal.sym(Bool, b, True{}, hb) : {Bool.and(True{}, _) == True{} : Bool}
  {==}

# a Bool whose truth holds is True
def fv.ofT(x: Bool, t: N.T(x)) -> {x == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, t)

# a <= b, as a Bool
def fv.toB(a: Nat, b: Nat, h: N.Le(a, b)) -> {Nat.is_le(a, b) == True{} : Bool}:
  fv.ofT(Nat.is_le(a, b), h)

# i < c gives i < c + X
def fv.lt_add(i: Nat, c: Nat, +X: Nat, h: {Nat.is_lt(i, c) == True{} : Bool}) ->
  {Nat.is_lt(i, Nat.add(c, X)) == True{} : Bool}:
  match i:
    case 0n:
      match c:
        case 0n:
          fv.tf({Nat.is_lt(0n, Nat.add(0n, X)) == True{} : Bool}, h)
        case 1n++cp:
          {==}
    case 1n++ip:
      match c:
        case 0n:
          fv.tf({Nat.is_lt(1n+ip, Nat.add(0n, X)) == True{} : Bool}, h)
        case 1n++cp:
          fv.lt_add(ip, cp, X, h)

# i < n gives i + d < d + n
def fv.lt_ar(+i: Nat, +n: Nat, d: Nat, h: {Nat.is_lt(i, n) == True{} : Bool}) ->
  {Nat.is_lt(Nat.add(i, d), Nat.add(d, n)) == True{} : Bool}:
  match d:
    case 0n:
      %Equal.sym(Nat, Nat.add(i, 0n), i, N.add_zero(i)) : {Nat.is_lt(_, n) == True{} : Bool}
      h
    case 1n++dp:
      %Equal.sym(Nat, Nat.add(i, 1n+dp), 1n+Nat.add(i, dp), N.add_succ_r(i, dp)) :
        {Nat.is_lt(_, 1n+Nat.add(dp, n)) == True{} : Bool}
      fv.lt_ar(i, n, dp, h)

# c <= i < c + n gives i + d < c + (d + n)
def fv.lt_sh(
  c: Nat,
  i: Nat,
  +n: Nat,
  +d: Nat,
  h1: {Nat.is_lt(i, c) == False{} : Bool},
  h2: {Nat.is_lt(i, Nat.add(c, n)) == True{} : Bool}
) -> {Nat.is_lt(Nat.add(i, d), Nat.add(c, Nat.add(d, n))) == True{} : Bool}:
  match c:
    case 0n:
      fv.lt_ar(i, n, d, h2)
    case 1n++cp:
      match i:
        case 0n:
          fv.ft({Nat.is_lt(Nat.add(0n, d), Nat.add(1n+cp, Nat.add(d, n))) == True{} : Bool}, h1)
        case 1n++ip:
          fv.lt_sh(cp, ip, n, d, h1, h2)

# d <= i < d + X gives i - d < X
def fv.lt_sub(
  d: Nat,
  i: Nat,
  +X: Nat,
  h1: {Nat.is_lt(i, d) == False{} : Bool},
  h2: {Nat.is_lt(i, Nat.add(d, X)) == True{} : Bool}
) -> {Nat.is_lt(Nat.sub(i, d), X) == True{} : Bool}:
  match d:
    case 0n:
      match i:
        case 0n:
          h2
        case 1n++ip:
          h2
    case 1n++dp:
      match i:
        case 0n:
          fv.ft({Nat.is_lt(Nat.sub(0n, 1n+dp), X) == True{} : Bool}, h1)
        case 1n++ip:
          fv.lt_sub(dp, ip, X, h1, h2)

# c <= 1 + c
def fv.le_up(c: Nat) -> {Nat.is_le(c, 1n+c) == True{} : Bool}:
  match c:
    case 0n:
      {==}
    case 1n++p:
      fv.le_up(p)

# n < c gives n < 1 + c
def fv.lt_up(n: Nat, c: Nat, h: {Nat.is_lt(n, c) == True{} : Bool}) -> {Nat.is_lt(n, 1n+c) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++np:
      match c:
        case 0n:
          fv.tf({Nat.is_lt(1n+np, 1n) == True{} : Bool}, h)
        case 1n++cp:
          fv.lt_up(np, cp, h)

# a term below c is below 1 + c, 2 + c and 3 + c
def fv.up1(t: Bk.Term, +c: Nat, +h: {PM.Term.below(t, c) == True{} : Bool}) -> {PM.Term.below(t, 1n+c) == True{} : Bool}:
  CT.Tz.below_mono(t, c, 1n+c, fv.le_up(c), h)

def fv.up2(+t: Bk.Term, +c: Nat, +h: {PM.Term.below(t, c) == True{} : Bool}) -> {PM.Term.below(t, 2n+c) == True{} : Bool}:
  fv.up1(t, 1n+c, fv.up1(t, c, h))

def fv.up3(+t: Bk.Term, +c: Nat, +h: {PM.Term.below(t, c) == True{} : Bool}) -> {PM.Term.below(t, 3n+c) == True{} : Bool}:
  fv.up1(t, 2n+c, fv.up2(t, c, h))

# a higher bound keeps Defs.below
def Defs.mono(
  ds: List<&2, Bk.Def>,
  +n: Nat,
  +m: Nat,
  +h: {Nat.is_le(n, m) == True{} : Bool},
  +hd: {Defs.below(ds, n) == True{} : Bool}
) -> {Defs.below(ds, m) == True{} : Bool}:
  match ds:
    case Nil{}:
      {==}
    case Con{Bk.Def{_, _, +v, _}, +rest}:
      fv.and_i(
        PM.Term.below(v, m),
        Defs.below(rest, m),
        CT.Tz.below_mono(v, n, m, h, fv.and_l(PM.Term.below(v, n), Defs.below(rest, n), hd)),
        Defs.mono(rest, n, m, h, fv.and_r(PM.Term.below(v, n), Defs.below(rest, n), hd)))

# Shifts and substitutions
# ------------------------

# the variable i of a shift by d at the cutoff c, from i < c + n
def fv.sh.at(
  b: Bool,
  +i: Nat,
  +c: Nat,
  +d: Nat,
  +n: Nat,
  eb: {Nat.is_lt(i, c) == b : Bool},
  h: {Nat.is_lt(i, Nat.add(c, n)) == True{} : Bool}
) -> {Nat.is_lt(El.Term.shift.at(b, i, d), Nat.add(c, Nat.add(d, n))) == True{} : Bool}:
  match b:
    case True{}:
      fv.lt_add(i, c, Nat.add(d, n), eb)
    case False{}:
      fv.lt_sh(c, i, n, d, eb, h)

# a shift by d at the cutoff c of a term below c + n is below c + (d + n)
def fv.sh(
  t: Bk.Term,
  +d: Nat,
  +c: Nat,
  +n: Nat,
  +hb: {PM.Term.below(t, Nat.add(c, n)) == True{} : Bool}
) -> {PM.Term.below(El.Term.shift(t, d, c), Nat.add(c, Nat.add(d, n))) == True{} : Bool}:
  match t:
    case Bk.Term.Var{+i}:
      fv.sh.at(Nat.is_lt(i, c), i, c, d, n, {==}, hb)
    case Bk.Term.Ann{+x, +y}:
      fv.and_i(
        PM.Term.below(El.Term.shift(x, d, c), Nat.add(c, Nat.add(d, n))),
        PM.Term.below(El.Term.shift(y, d, c), Nat.add(c, Nat.add(d, n))),
        fv.sh(x, d, c, n, fv.and_l(PM.Term.below(x, Nat.add(c, n)), PM.Term.below(y, Nat.add(c, n)), hb)),
        fv.sh(y, d, c, n, fv.and_r(PM.Term.below(x, Nat.add(c, n)), PM.Term.below(y, Nat.add(c, n)), hb)))
    case Bk.Term.Let{_, +x, +y}:
      fv.and_i(
        PM.Term.below(El.Term.shift(x, d, c), Nat.add(c, Nat.add(d, n))),
        PM.Term.below(El.Term.shift(y, d, 1n+c), 1n+Nat.add(c, Nat.add(d, n))),
        fv.sh(x, d, c, n, fv.and_l(PM.Term.below(x, Nat.add(c, n)), PM.Term.below(y, 1n+Nat.add(c, n)), hb)),
        fv.sh(y, d, 1n+c, n, fv.and_r(PM.Term.below(x, Nat.add(c, n)), PM.Term.below(y, 1n+Nat.add(c, n)), hb)))
    case Bk.Term.Typ{+x}:
      fv.sh(x, d, c, n, hb)
    case Bk.Term.Min{+x, +y}:
      fv.and_i(
        PM.Term.below(El.Term.shift(x, d, c), Nat.add(c, Nat.add(d, n))),
        PM.Term.below(El.Term.shift(y, d, c), Nat.add(c, Nat.add(d, n))),
        fv.sh(x, d, c, n, fv.and_l(PM.Term.below(x, Nat.add(c, n)), PM.Term.below(y, Nat.add(c, n)), hb)),
        fv.sh(y, d, c, n, fv.and_r(PM.Term.below(x, Nat.add(c, n)), PM.Term.below(y, Nat.add(c, n)), hb)))
    case Bk.Term.All{_, +x, +y}:
      fv.and_i(
        PM.Term.below(El.Term.shift(x, d, c), Nat.add(c, Nat.add(d, n))),
        PM.Term.below(El.Term.shift(y, d, 1n+c), 1n+Nat.add(c, Nat.add(d, n))),
        fv.sh(x, d, c, n, fv.and_l(PM.Term.below(x, Nat.add(c, n)), PM.Term.below(y, 1n+Nat.add(c, n)), hb)),
        fv.sh(y, d, 1n+c, n, fv.and_r(PM.Term.below(x, Nat.add(c, n)), PM.Term.below(y, 1n+Nat.add(c, n)), hb)))
    case Bk.Term.Lam{_, +x}:
      fv.sh(x, d, 1n+c, n, hb)
    case Bk.Term.App{_, +x, +y}:
      fv.and_i(
        PM.Term.below(El.Term.shift(x, d, c), Nat.add(c, Nat.add(d, n))),
        PM.Term.below(El.Term.shift(y, d, c), Nat.add(c, Nat.add(d, n))),
        fv.sh(x, d, c, n, fv.and_l(PM.Term.below(x, Nat.add(c, n)), PM.Term.below(y, Nat.add(c, n)), hb)),
        fv.sh(y, d, c, n, fv.and_r(PM.Term.below(x, Nat.add(c, n)), PM.Term.below(y, Nat.add(c, n)), hb)))
    case Bk.Term.Sig{_, +x, +y}:
      fv.and_i(
        PM.Term.below(El.Term.shift(x, d, c), Nat.add(c, Nat.add(d, n))),
        PM.Term.below(El.Term.shift(y, d, 1n+c), 1n+Nat.add(c, Nat.add(d, n))),
        fv.sh(x, d, c, n, fv.and_l(PM.Term.below(x, Nat.add(c, n)), PM.Term.below(y, 1n+Nat.add(c, n)), hb)),
        fv.sh(y, d, 1n+c, n, fv.and_r(PM.Term.below(x, Nat.add(c, n)), PM.Term.below(y, 1n+Nat.add(c, n)), hb)))
    case Bk.Term.Tup{_, +x, +y}:
      fv.and_i(
        PM.Term.below(El.Term.shift(x, d, c), Nat.add(c, Nat.add(d, n))),
        PM.Term.below(El.Term.shift(y, d, c), Nat.add(c, Nat.add(d, n))),
        fv.sh(x, d, c, n, fv.and_l(PM.Term.below(x, Nat.add(c, n)), PM.Term.below(y, Nat.add(c, n)), hb)),
        fv.sh(y, d, c, n, fv.and_r(PM.Term.below(x, Nat.add(c, n)), PM.Term.below(y, Nat.add(c, n)), hb)))
    case Bk.Term.Prj{+x}:
      fv.sh(x, d, c, n, hb)
    case Bk.Term.Mat{_, +x, +y}:
      fv.and_i(
        PM.Term.below(El.Term.shift(x, d, c), Nat.add(c, Nat.add(d, n))),
        PM.Term.below(El.Term.shift(y, d, c), Nat.add(c, Nat.add(d, n))),
        fv.sh(x, d, c, n, fv.and_l(PM.Term.below(x, Nat.add(c, n)), PM.Term.below(y, Nat.add(c, n)), hb)),
        fv.sh(y, d, c, n, fv.and_r(PM.Term.below(x, Nat.add(c, n)), PM.Term.below(y, Nat.add(c, n)), hb)))
    case Bk.Term.Eql{+x, +y, +z}:
      +r = fv.and_r(PM.Term.below(x, Nat.add(c, n)), Bool.and(PM.Term.below(y, Nat.add(c, n)), PM.Term.below(z, Nat.add(c, n))), hb)
      fv.and_i(
        PM.Term.below(El.Term.shift(x, d, c), Nat.add(c, Nat.add(d, n))),
        Bool.and(PM.Term.below(El.Term.shift(y, d, c), Nat.add(c, Nat.add(d, n))), PM.Term.below(El.Term.shift(z, d, c), Nat.add(c, Nat.add(d, n)))),
        fv.sh(x, d, c, n, fv.and_l(PM.Term.below(x, Nat.add(c, n)), Bool.and(PM.Term.below(y, Nat.add(c, n)), PM.Term.below(z, Nat.add(c, n))), hb)),
        fv.and_i(
          PM.Term.below(El.Term.shift(y, d, c), Nat.add(c, Nat.add(d, n))),
          PM.Term.below(El.Term.shift(z, d, c), Nat.add(c, Nat.add(d, n))),
          fv.sh(y, d, c, n, fv.and_l(PM.Term.below(y, Nat.add(c, n)), PM.Term.below(z, Nat.add(c, n)), r)),
          fv.sh(z, d, c, n, fv.and_r(PM.Term.below(y, Nat.add(c, n)), PM.Term.below(z, Nat.add(c, n)), r))))
    case Bk.Term.Rwt{+x, +y, +z}:
      +r = fv.and_r(PM.Term.below(x, Nat.add(c, n)), Bool.and(PM.Term.below(y, 2n+Nat.add(c, n)), PM.Term.below(z, Nat.add(c, n))), hb)
      fv.and_i(
        PM.Term.below(El.Term.shift(x, d, c), Nat.add(c, Nat.add(d, n))),
        Bool.and(PM.Term.below(El.Term.shift(y, d, 2n+c), 2n+Nat.add(c, Nat.add(d, n))), PM.Term.below(El.Term.shift(z, d, c), Nat.add(c, Nat.add(d, n)))),
        fv.sh(x, d, c, n, fv.and_l(PM.Term.below(x, Nat.add(c, n)), Bool.and(PM.Term.below(y, 2n+Nat.add(c, n)), PM.Term.below(z, Nat.add(c, n))), hb)),
        fv.and_i(
          PM.Term.below(El.Term.shift(y, d, 2n+c), 2n+Nat.add(c, Nat.add(d, n))),
          PM.Term.below(El.Term.shift(z, d, c), Nat.add(c, Nat.add(d, n))),
          fv.sh(y, d, 2n+c, n, fv.and_l(PM.Term.below(y, 2n+Nat.add(c, n)), PM.Term.below(z, Nat.add(c, n)), r)),
          fv.sh(z, d, c, n, fv.and_r(PM.Term.below(y, 2n+Nat.add(c, n)), PM.Term.below(z, Nat.add(c, n)), r))))
    case Bk.Term.Ref{_}:
      {==}
    case Bk.Term.Enu{_}:
      {==}
    case Bk.Term.Lab{_}:
      {==}
    case Bk.Term.Efq{}:
      {==}
    case Bk.Term.Rfl{}:
      {==}

# the term of the variable i in e, with i < |e| + n and e below n, is below n
def fv.env(
  e: List<&2, Bk.Term>,
  i: Nat,
  +n: Nat,
  hi: {Nat.is_lt(i, Nat.add(List.length(&2, Bk.Term, e), n)) == True{} : Bool},
  +he: {PM.Terms.below(e, n) == True{} : Bool}
) -> {PM.Term.below(El.Env.sub(e, i), n) == True{} : Bool}:
  match e:
    case Nil{}:
      hi
    case Con{+x, +rest}:
      match i:
        case 0n:
          fv.and_l(PM.Term.below(x, n), PM.Terms.below(rest, n), he)
        case 1n++j:
          fv.env(rest, j, n, hi, fv.and_r(PM.Term.below(x, n), PM.Terms.below(rest, n), he))

# the variable i under 1 + p binders, by the branch of i < 1 + p
def fv.lift.at(
  b: Bool,
  +i: Nat,
  +p: Nat,
  +e: List<&2, Bk.Term>,
  +n: Nat,
  eb: {Nat.is_lt(i, 1n+p) == b : Bool},
  hi: {Nat.is_lt(i, Nat.add(1n+p, Nat.add(List.length(&2, Bk.Term, e), n))) == True{} : Bool},
  +he: {PM.Terms.below(e, n) == True{} : Bool}
) -> {
  PM.Term.below(El.Term.lift.at(b, i, El.Term.shift(El.Env.sub(e, Nat.sub(i, 1n+p)), 1n+p, 0n)), Nat.add(1n+p, n))
    == True{} : Bool
}:
  match b:
    case True{}:
      fv.lt_add(i, 1n+p, n, eb)
    case False{}:
      fv.sh(
        El.Env.sub(e, Nat.sub(i, 1n+p)),
        1n+p,
        0n,
        n,
        fv.env(e, Nat.sub(i, 1n+p), n, fv.lt_sub(1n+p, i, Nat.add(List.length(&2, Bk.Term, e), n), eb, hi), he))

# the variable i under d binders, with e below n put in: below d + n
def fv.lift(
  +e: List<&2, Bk.Term>,
  d: Nat,
  +i: Nat,
  +n: Nat,
  hi: {Nat.is_lt(i, Nat.add(d, Nat.add(List.length(&2, Bk.Term, e), n))) == True{} : Bool},
  +he: {PM.Terms.below(e, n) == True{} : Bool}
) -> {PM.Term.below(El.Term.lift(e, d, i), Nat.add(d, n)) == True{} : Bool}:
  match d:
    case 0n:
      fv.env(e, i, n, hi, he)
    case 1n++p:
      fv.lift.at(Nat.is_lt(i, 1n+p), i, p, e, n, {==}, hi, he)

# a term below d + (|e| + n), under d binders, with e below n put in for its
# free variables: below d + n
def fv.sb(
  t: Bk.Term,
  +e: List<&2, Bk.Term>,
  +d: Nat,
  +n: Nat,
  +hb: {PM.Term.below(t, Nat.add(d, Nat.add(List.length(&2, Bk.Term, e), n))) == True{} : Bool},
  +he: {PM.Terms.below(e, n) == True{} : Bool}
) -> {PM.Term.below(El.Term.subst(t, e, d), Nat.add(d, n)) == True{} : Bool}:
  match t:
    case Bk.Term.Var{+i}:
      fv.lift(e, d, i, n, hb, he)
    case Bk.Term.Ann{+x, +y}:
      fv.and_i(
        PM.Term.below(El.Term.subst(x, e, d), Nat.add(d, n)),
        PM.Term.below(El.Term.subst(y, e, d), Nat.add(d, n)),
        fv.sb(x, e, d, n, fv.and_l(PM.Term.below(x, Nat.add(d, Nat.add(List.length(&2, Bk.Term, e), n))), PM.Term.below(y, Nat.add(d, Nat.add(List.length(&2, Bk.Term, e), n))), hb), he),
        fv.sb(y, e, d, n, fv.and_r(PM.Term.below(x, Nat.add(d, Nat.add(List.length(&2, Bk.Term, e), n))), PM.Term.below(y, Nat.add(d, Nat.add(List.length(&2, Bk.Term, e), n))), hb), he))
    case Bk.Term.Let{_, +x, +y}:
      fv.and_i(
        PM.Term.below(El.Term.subst(x, e, d), Nat.add(d, n)),
        PM.Term.below(El.Term.subst(y, e, 1n+d), 1n+Nat.add(d, n)),
        fv.sb(x, e, d, n, fv.and_l(PM.Term.below(x, Nat.add(d, Nat.add(List.length(&2, Bk.Term, e), n))), PM.Term.below(y, 1n+Nat.add(d, Nat.add(List.length(&2, Bk.Term, e), n))), hb), he),
        fv.sb(y, e, 1n+d, n, fv.and_r(PM.Term.below(x, Nat.add(d, Nat.add(List.length(&2, Bk.Term, e), n))), PM.Term.below(y, 1n+Nat.add(d, Nat.add(List.length(&2, Bk.Term, e), n))), hb), he))
    case Bk.Term.Typ{+x}:
      fv.sb(x, e, d, n, hb, he)
    case Bk.Term.Min{+x, +y}:
      fv.and_i(
        PM.Term.below(El.Term.subst(x, e, d), Nat.add(d, n)),
        PM.Term.below(El.Term.subst(y, e, d), Nat.add(d, n)),
        fv.sb(x, e, d, n, fv.and_l(PM.Term.below(x, Nat.add(d, Nat.add(List.length(&2, Bk.Term, e), n))), PM.Term.below(y, Nat.add(d, Nat.add(List.length(&2, Bk.Term, e), n))), hb), he),
        fv.sb(y, e, d, n, fv.and_r(PM.Term.below(x, Nat.add(d, Nat.add(List.length(&2, Bk.Term, e), n))), PM.Term.below(y, Nat.add(d, Nat.add(List.length(&2, Bk.Term, e), n))), hb), he))
    case Bk.Term.All{_, +x, +y}:
      fv.and_i(
        PM.Term.below(El.Term.subst(x, e, d), Nat.add(d, n)),
        PM.Term.below(El.Term.subst(y, e, 1n+d), 1n+Nat.add(d, n)),
        fv.sb(x, e, d, n, fv.and_l(PM.Term.below(x, Nat.add(d, Nat.add(List.length(&2, Bk.Term, e), n))), PM.Term.below(y, 1n+Nat.add(d, Nat.add(List.length(&2, Bk.Term, e), n))), hb), he),
        fv.sb(y, e, 1n+d, n, fv.and_r(PM.Term.below(x, Nat.add(d, Nat.add(List.length(&2, Bk.Term, e), n))), PM.Term.below(y, 1n+Nat.add(d, Nat.add(List.length(&2, Bk.Term, e), n))), hb), he))
    case Bk.Term.Lam{_, +x}:
      fv.sb(x, e, 1n+d, n, hb, he)
    case Bk.Term.App{_, +x, +y}:
      fv.and_i(
        PM.Term.below(El.Term.subst(x, e, d), Nat.add(d, n)),
        PM.Term.below(El.Term.subst(y, e, d), Nat.add(d, n)),
        fv.sb(x, e, d, n, fv.and_l(PM.Term.below(x, Nat.add(d, Nat.add(List.length(&2, Bk.Term, e), n))), PM.Term.below(y, Nat.add(d, Nat.add(List.length(&2, Bk.Term, e), n))), hb), he),
        fv.sb(y, e, d, n, fv.and_r(PM.Term.below(x, Nat.add(d, Nat.add(List.length(&2, Bk.Term, e), n))), PM.Term.below(y, Nat.add(d, Nat.add(List.length(&2, Bk.Term, e), n))), hb), he))
    case Bk.Term.Sig{_, +x, +y}:
      fv.and_i(
        PM.Term.below(El.Term.subst(x, e, d), Nat.add(d, n)),
        PM.Term.below(El.Term.subst(y, e, 1n+d), 1n+Nat.add(d, n)),
        fv.sb(x, e, d, n, fv.and_l(PM.Term.below(x, Nat.add(d, Nat.add(List.length(&2, Bk.Term, e), n))), PM.Term.below(y, 1n+Nat.add(d, Nat.add(List.length(&2, Bk.Term, e), n))), hb), he),
        fv.sb(y, e, 1n+d, n, fv.and_r(PM.Term.below(x, Nat.add(d, Nat.add(List.length(&2, Bk.Term, e), n))), PM.Term.below(y, 1n+Nat.add(d, Nat.add(List.length(&2, Bk.Term, e), n))), hb), he))
    case Bk.Term.Tup{_, +x, +y}:
      fv.and_i(
        PM.Term.below(El.Term.subst(x, e, d), Nat.add(d, n)),
        PM.Term.below(El.Term.subst(y, e, d), Nat.add(d, n)),
        fv.sb(x, e, d, n, fv.and_l(PM.Term.below(x, Nat.add(d, Nat.add(List.length(&2, Bk.Term, e), n))), PM.Term.below(y, Nat.add(d, Nat.add(List.length(&2, Bk.Term, e), n))), hb), he),
        fv.sb(y, e, d, n, fv.and_r(PM.Term.below(x, Nat.add(d, Nat.add(List.length(&2, Bk.Term, e), n))), PM.Term.below(y, Nat.add(d, Nat.add(List.length(&2, Bk.Term, e), n))), hb), he))
    case Bk.Term.Prj{+x}:
      fv.sb(x, e, d, n, hb, he)
    case Bk.Term.Mat{_, +x, +y}:
      fv.and_i(
        PM.Term.below(El.Term.subst(x, e, d), Nat.add(d, n)),
        PM.Term.below(El.Term.subst(y, e, d), Nat.add(d, n)),
        fv.sb(x, e, d, n, fv.and_l(PM.Term.below(x, Nat.add(d, Nat.add(List.length(&2, Bk.Term, e), n))), PM.Term.below(y, Nat.add(d, Nat.add(List.length(&2, Bk.Term, e), n))), hb), he),
        fv.sb(y, e, d, n, fv.and_r(PM.Term.below(x, Nat.add(d, Nat.add(List.length(&2, Bk.Term, e), n))), PM.Term.below(y, Nat.add(d, Nat.add(List.length(&2, Bk.Term, e), n))), hb), he))
    case Bk.Term.Eql{+x, +y, +z}:
      +r = fv.and_r(PM.Term.below(x, Nat.add(d, Nat.add(List.length(&2, Bk.Term, e), n))), Bool.and(PM.Term.below(y, Nat.add(d, Nat.add(List.length(&2, Bk.Term, e), n))), PM.Term.below(z, Nat.add(d, Nat.add(List.length(&2, Bk.Term, e), n)))), hb)
      fv.and_i(
        PM.Term.below(El.Term.subst(x, e, d), Nat.add(d, n)),
        Bool.and(PM.Term.below(El.Term.subst(y, e, d), Nat.add(d, n)), PM.Term.below(El.Term.subst(z, e, d), Nat.add(d, n))),
        fv.sb(x, e, d, n, fv.and_l(PM.Term.below(x, Nat.add(d, Nat.add(List.length(&2, Bk.Term, e), n))), Bool.and(PM.Term.below(y, Nat.add(d, Nat.add(List.length(&2, Bk.Term, e), n))), PM.Term.below(z, Nat.add(d, Nat.add(List.length(&2, Bk.Term, e), n)))), hb), he),
        fv.and_i(
          PM.Term.below(El.Term.subst(y, e, d), Nat.add(d, n)),
          PM.Term.below(El.Term.subst(z, e, d), Nat.add(d, n)),
          fv.sb(y, e, d, n, fv.and_l(PM.Term.below(y, Nat.add(d, Nat.add(List.length(&2, Bk.Term, e), n))), PM.Term.below(z, Nat.add(d, Nat.add(List.length(&2, Bk.Term, e), n))), r), he),
          fv.sb(z, e, d, n, fv.and_r(PM.Term.below(y, Nat.add(d, Nat.add(List.length(&2, Bk.Term, e), n))), PM.Term.below(z, Nat.add(d, Nat.add(List.length(&2, Bk.Term, e), n))), r), he)))
    case Bk.Term.Rwt{+x, +y, +z}:
      +r = fv.and_r(PM.Term.below(x, Nat.add(d, Nat.add(List.length(&2, Bk.Term, e), n))), Bool.and(PM.Term.below(y, 2n+Nat.add(d, Nat.add(List.length(&2, Bk.Term, e), n))), PM.Term.below(z, Nat.add(d, Nat.add(List.length(&2, Bk.Term, e), n)))), hb)
      fv.and_i(
        PM.Term.below(El.Term.subst(x, e, d), Nat.add(d, n)),
        Bool.and(PM.Term.below(El.Term.subst(y, e, 2n+d), 2n+Nat.add(d, n)), PM.Term.below(El.Term.subst(z, e, d), Nat.add(d, n))),
        fv.sb(x, e, d, n, fv.and_l(PM.Term.below(x, Nat.add(d, Nat.add(List.length(&2, Bk.Term, e), n))), Bool.and(PM.Term.below(y, 2n+Nat.add(d, Nat.add(List.length(&2, Bk.Term, e), n))), PM.Term.below(z, Nat.add(d, Nat.add(List.length(&2, Bk.Term, e), n)))), hb), he),
        fv.and_i(
          PM.Term.below(El.Term.subst(y, e, 2n+d), 2n+Nat.add(d, n)),
          PM.Term.below(El.Term.subst(z, e, d), Nat.add(d, n)),
          fv.sb(y, e, 2n+d, n, fv.and_l(PM.Term.below(y, 2n+Nat.add(d, Nat.add(List.length(&2, Bk.Term, e), n))), PM.Term.below(z, Nat.add(d, Nat.add(List.length(&2, Bk.Term, e), n))), r), he),
          fv.sb(z, e, d, n, fv.and_r(PM.Term.below(y, 2n+Nat.add(d, Nat.add(List.length(&2, Bk.Term, e), n))), PM.Term.below(z, Nat.add(d, Nat.add(List.length(&2, Bk.Term, e), n))), r), he)))
    case Bk.Term.Ref{_}:
      {==}
    case Bk.Term.Enu{_}:
      {==}
    case Bk.Term.Lab{_}:
      {==}
    case Bk.Term.Efq{}:
      {==}
    case Bk.Term.Rfl{}:
      {==}

# f with v put in for its variable 0: below B
def fv.inst(
  f: Bk.Term,
  +v: Bk.Term,
  +B: Nat,
  hf: {PM.Term.below(f, 1n+B) == True{} : Bool},
  hv: {PM.Term.below(v, B) == True{} : Bool}
) -> {PM.Term.below(El.Term.inst(f, v), B) == True{} : Bool}:
  fv.sb(f, Con{v, Nil{}}, 0n, B, hf, fv.and_i(PM.Term.below(v, B), True{}, hv, {==}))

# Spines
# ------

# t applied to arguments below B
def fv.spine(
  xs: List<&2, El.Arg>,
  +t: Bk.Term,
  +B: Nat,
  ht: {PM.Term.below(t, B) == True{} : Bool},
  +hx: {PM.Terms.below(PM.Arg.terms(xs), B) == True{} : Bool}
) -> {PM.Term.below(El.Term.spine(xs, t), B) == True{} : Bool}:
  match xs:
    case Nil{}:
      ht
    case Con{El.Arg{+q, +x}, +rest}:
      +rs = PM.Terms.below(PM.Arg.terms(rest), B)
      fv.spine(
        rest,
        Bk.Term.App{q, t, x},
        B,
        fv.and_i(PM.Term.below(t, B), PM.Term.below(x, B), ht, fv.and_l(PM.Term.below(x, B), rs, hx)),
        fv.and_r(PM.Term.below(x, B), rs, hx))

# the arguments of a spine below B, in front of xs
def fv.args(
  +t: Bk.Term,
  +xs: List<&2, El.Arg>,
  +B: Nat,
  +ht: {PM.Term.below(t, B) == True{} : Bool},
  +hx: {PM.Terms.below(PM.Arg.terms(xs), B) == True{} : Bool}
) -> {PM.Terms.below(PM.Arg.terms(El.Term.args(t, xs)), B) == True{} : Bool}:
  match t:
    case Bk.Term.App{+q, +f, +x}:
      fv.args(
        f,
        Con{El.Arg{q, x}, xs},
        B,
        fv.and_l(PM.Term.below(f, B), PM.Term.below(x, B), ht),
        fv.and_i(
          PM.Term.below(x, B),
          PM.Terms.below(PM.Arg.terms(xs), B),
          fv.and_r(PM.Term.below(f, B), PM.Term.below(x, B), ht),
          hx))
    case _:
      hx

# Eval's results
# --------------

# a step's result, when there is one, is below B
def fv.Mt(m: Maybe<Bk.Term>, +B: Nat) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{u}:
      PM.Term.below(u, B)

# a walk's leaf, when there is one, is below B
def fv.Mm(m: Maybe<Maybe<Bk.Term>>, +B: Nat) -> Bool:
  match m:
    case Some{Some{u}}:
      PM.Term.below(u, B)
    case _:
      True{}

# a def's body, when there is one, is below B
def fv.Md(m: Maybe<Bk.Def>, +B: Nat) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{Bk.Def{_, _, v, _}}:
      PM.Term.below(v, B)

# The walk
# --------

def fv.walk.if(
  b: Bool,
  r: Maybe<Maybe<Bk.Term>>,
  +B: Nat,
  h: {fv.Mm(r, B) == True{} : Bool}
) -> {fv.Mm(El.Eval.walk.if(b, r), B) == True{} : Bool}:
  match b:
    case True{}:
      h
    case False{}:
      {==}

def fv.walk.pick(
  b: Bool,
  r: Maybe<Maybe<Bk.Term>>,
  s: Maybe<Maybe<Bk.Term>>,
  +B: Nat,
  hr: {fv.Mm(r, B) == True{} : Bool},
  hs: {fv.Mm(s, B) == True{} : Bool}
) -> {fv.Mm(El.Eval.walk.pick(b, r, s), B) == True{} : Bool}:
  match b:
    case True{}:
      hr
    case False{}:
      hs

def fv.walk.app(
  node: Bool,
  r: Maybe<Maybe<Bk.Term>>,
  u: Bk.Term,
  +B: Nat,
  hr: {fv.Mm(r, B) == True{} : Bool},
  hu: {PM.Term.below(u, B) == True{} : Bool}
) -> {fv.Mm(El.Eval.walk.app(node, r, u), B) == True{} : Bool}:
  match node:
    case True{}:
      hr
    case False{}:
      hu

def fv.walk.leaf(
  node: Bool,
  xs: List<&2, El.Arg>,
  u: Bk.Term,
  +B: Nat,
  hu: {PM.Term.below(u, B) == True{} : Bool}
) -> {fv.Mm(El.Eval.walk.leaf(node, xs, u), B) == True{} : Bool}:
  match node:
    case True{}:
      match xs:
        case Nil{}:
          {==}
        case Con{_, _}:
          {==}
    case False{}:
      hu

# the walk of a case tree t below |e| + B, with e bound below B, on arguments
# below B: its leaf is below B
def fv.walk(
  +t: Bk.Term,
  +e: List<&2, Bk.Term>,
  +xs: List<&2, El.Arg>,
  +B: Nat,
  +ht: {PM.Term.below(t, Nat.add(List.length(&2, Bk.Term, e), B)) == True{} : Bool},
  +he: {PM.Terms.below(e, B) == True{} : Bool},
  +hx: {PM.Terms.below(PM.Arg.terms(xs), B) == True{} : Bool}
) -> {fv.Mm(El.Eval.walk(t, e, xs), B) == True{} : Bool}:
  match t xs:
    case Bk.Term.Lam{+p, +f} Con{El.Arg{+q, +x}, +rest}:
      +rs = PM.Terms.below(PM.Arg.terms(rest), B)
      fv.walk.if(
        El.Quan.binds(p, q, x),
        El.Eval.walk(f, Con{x, e}, rest),
        B,
        fv.walk(
          f,
          Con{x, e},
          rest,
          B,
          ht,
          fv.and_i(PM.Term.below(x, B), PM.Terms.below(e, B), fv.and_l(PM.Term.below(x, B), rs, hx), he),
          fv.and_r(PM.Term.below(x, B), rs, hx)))
    case Bk.Term.Prj{+hh} Con{El.Arg{+q, Bk.Term.Tup{+r, +a, +b}}, +rest}:
      +rs = PM.Terms.below(PM.Arg.terms(rest), B)
      +ab = Bool.and(PM.Term.below(a, B), PM.Term.below(b, B))
      +hab = fv.and_l(ab, rs, hx)
      +ys = Con{El.Arg{El.Quan.fld(r, q), a}, Con{El.Arg{q, b}, rest}}
      fv.walk.if(
        El.Quan.live(q),
        El.Eval.walk(hh, e, ys),
        B,
        fv.walk(
          hh,
          e,
          ys,
          B,
          ht,
          he,
          fv.and_i(
            PM.Term.below(a, B),
            Bool.and(PM.Term.below(b, B), rs),
            fv.and_l(PM.Term.below(a, B), PM.Term.below(b, B), hab),
            fv.and_i(
              PM.Term.below(b, B),
              rs,
              fv.and_r(PM.Term.below(a, B), PM.Term.below(b, B), hab),
              fv.and_r(ab, rs, hx)))))
    case Bk.Term.Mat{+k, +hh, +mm} Con{El.Arg{+q, Bk.Term.Lab{+j}}, +rest}:
      +L = Nat.add(List.length(&2, Bk.Term, e), B)
      +ys = Con{El.Arg{q, Bk.Term.Lab{j}}, rest}
      fv.walk.if(
        El.Quan.live(q),
        El.Eval.walk.pick(Sd.Name.is_eq(j, k), El.Eval.walk(hh, e, rest), El.Eval.walk(mm, e, ys)),
        B,
        fv.walk.pick(
          Sd.Name.is_eq(j, k),
          El.Eval.walk(hh, e, rest),
          El.Eval.walk(mm, e, ys),
          B,
          fv.walk(hh, e, rest, B, fv.and_l(PM.Term.below(hh, L), PM.Term.below(mm, L), ht), he, hx),
          fv.walk(mm, e, ys, B, fv.and_r(PM.Term.below(hh, L), PM.Term.below(mm, L), ht), he, hx)))
    case Bk.Term.App{+q, +f, Bk.Term.Var{+v}} ys:
      +L = Nat.add(List.length(&2, Bk.Term, e), B)
      +u = Bk.Term.App{q, f, Bk.Term.Var{v}}
      +zs = Con{El.Arg{q, El.Env.sub(e, v)}, ys}
      fv.walk.app(
        El.Term.takes(El.Term.head(f)),
        El.Eval.walk(f, e, zs),
        El.Term.spine(ys, El.Term.subst(u, e, 0n)),
        B,
        fv.walk(
          f,
          e,
          zs,
          B,
          fv.and_l(PM.Term.below(f, L), Nat.is_lt(v, L), ht),
          he,
          fv.and_i(
            PM.Term.below(El.Env.sub(e, v), B),
            PM.Terms.below(PM.Arg.terms(ys), B),
            fv.env(e, v, B, fv.and_r(PM.Term.below(f, L), Nat.is_lt(v, L), ht), he),
            hx)),
        fv.spine(ys, El.Term.subst(u, e, 0n), B, fv.sb(u, e, 0n, B, ht, he), hx))
    case u ys:
      fv.walk.leaf(
        El.Term.takes(u),
        ys,
        El.Term.spine(ys, El.Term.subst(u, e, 0n)),
        B,
        fv.spine(ys, El.Term.subst(u, e, 0n), B, fv.sb(u, e, 0n, B, ht, he), hx))

# Calls
# -----

def fv.get.if(
  b: Bool,
  d: Bk.Def,
  r: Maybe<Bk.Def>,
  +B: Nat,
  hd: {fv.Md(Some{d}, B) == True{} : Bool},
  hr: {fv.Md(r, B) == True{} : Bool}
) -> {fv.Md(El.Book.get.if(b, d, r), B) == True{} : Bool}:
  match b:
    case True{}:
      hd
    case False{}:
      hr

# the def of a name, in defs below B, has a body below B
def fv.get(
  ds: List<&2, Bk.Def>,
  +k: List<&2, Word(8n)>,
  +B: Nat,
  +hd: {Defs.below(ds, B) == True{} : Bool}
) -> {fv.Md(El.Book.get(ds, k), B) == True{} : Bool}:
  match ds:
    case Nil{}:
      {==}
    case Con{Bk.Def{+n, +T, +v, +o}, +rest}:
      fv.get.if(
        Sd.Name.is_eq(n, k),
        Bk.Def{n, T, v, o},
        El.Book.get(rest, k),
        B,
        fv.and_l(PM.Term.below(v, B), Defs.below(rest, B), hd),
        fv.get(rest, k, B, fv.and_r(PM.Term.below(v, B), Defs.below(rest, B), hd)))

def fv.cw.def(
  m: Maybe<Bk.Def>,
  +xs: List<&2, El.Arg>,
  +B: Nat,
  hm: {fv.Md(m, B) == True{} : Bool},
  hx: {PM.Terms.below(PM.Arg.terms(xs), B) == True{} : Bool}
) -> {fv.Mm(El.Eval.callWalk.def(m, xs), B) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{Bk.Def{_, _, +v, _}}:
      fv.walk(v, Nil{}, xs, B, hm, {==}, hx)

def fv.cw.head(
  +ds: List<&2, Bk.Def>,
  h: Bk.Term,
  +xs: List<&2, El.Arg>,
  +B: Nat,
  +hd: {Defs.below(ds, B) == True{} : Bool},
  +hx: {PM.Terms.below(PM.Arg.terms(xs), B) == True{} : Bool}
) -> {fv.Mm(El.Eval.callWalk.head(ds, h, xs), B) == True{} : Bool}:
  match h:
    case Bk.Term.Ref{+k}:
      fv.cw.def(El.Book.get(ds, k), xs, B, fv.get(ds, k, B, hd), hx)
    case _:
      {==}

# the walk of a call below B, in defs below B: its leaf is below B
def fv.cw(
  +ds: List<&2, Bk.Def>,
  +t: Bk.Term,
  +B: Nat,
  +hd: {Defs.below(ds, B) == True{} : Bool},
  +ht: {PM.Term.below(t, B) == True{} : Bool}
) -> {fv.Mm(El.Eval.callWalk(ds, t), B) == True{} : Bool}:
  fv.cw.head(ds, El.Term.head(t), El.Term.args(t, Nil{}), B, hd, fv.args(t, Nil{}, B, ht, {==}))

def fv.call.if(
  ok: Bool,
  r: Maybe<Maybe<Bk.Term>>,
  +B: Nat,
  hr: {fv.Mm(r, B) == True{} : Bool}
) -> {fv.Mt(El.Eval.call.if(ok, r), B) == True{} : Bool}:
  match ok r:
    case True{} Some{Some{u}}:
      hr
    case _ _:
      {==}

# the step of a call below B, in defs below B
def fv.call(
  +ds: List<&2, Bk.Def>,
  +t: Bk.Term,
  +B: Nat,
  +hd: {Defs.below(ds, B) == True{} : Bool},
  +ht: {PM.Term.below(t, B) == True{} : Bool}
) -> {fv.Mt(El.Eval.call(ds, t), B) == True{} : Bool}:
  fv.call.if(El.Eval.vals(ds, t, True{}), El.Eval.callWalk(ds, t), B, fv.cw(ds, t, B, hd, ht))

# Redexes
# -------

def fv.redex.if(
  b: Bool,
  u: Bk.Term,
  +B: Nat,
  hu: {PM.Term.below(u, B) == True{} : Bool}
) -> {fv.Mt(El.Eval.redex.if(b, u), B) == True{} : Bool}:
  match b:
    case True{}:
      hu
    case False{}:
      {==}

def fv.redex.pick(
  b: Bool,
  h: Bk.Term,
  m: Bk.Term,
  +B: Nat,
  hh: {PM.Term.below(h, B) == True{} : Bool},
  hm: {PM.Term.below(m, B) == True{} : Bool}
) -> {PM.Term.below(El.Eval.redex.pick(b, h, m), B) == True{} : Bool}:
  match b:
    case True{}:
      hh
    case False{}:
      hm

# the step of App q f x, f and x below B
def fv.redex(
  +ds: List<&2, Bk.Def>,
  +q: Bk.Quan,
  +f: Bk.Term,
  +x: Bk.Term,
  +B: Nat,
  +hd: {Defs.below(ds, B) == True{} : Bool},
  +hf: {PM.Term.below(f, B) == True{} : Bool},
  +hx: {PM.Term.below(x, B) == True{} : Bool}
) -> {fv.Mt(El.Eval.redex(ds, q, f, x), B) == True{} : Bool}:
  match f x:
    case Bk.Term.Lam{+p, +b} y:
      fv.redex.if(El.Quan.binds(p, q, y), El.Term.inst(b, y), B, fv.inst(b, y, B, hf, hx))
    case Bk.Term.Prj{+h} Bk.Term.Tup{+r, +a, +b}:
      +g = Bk.Term.App{El.Quan.fld(r, q), h, a}
      fv.redex.if(
        El.Quan.live(q),
        Bk.Term.App{q, g, b},
        B,
        fv.and_i(
          PM.Term.below(g, B),
          PM.Term.below(b, B),
          fv.and_i(PM.Term.below(h, B), PM.Term.below(a, B), hf, fv.and_l(PM.Term.below(a, B), PM.Term.below(b, B), hx)),
          fv.and_r(PM.Term.below(a, B), PM.Term.below(b, B), hx)))
    case Bk.Term.Mat{+k, +h, +m} Bk.Term.Lab{+j}:
      +w = Bk.Term.App{q, m, Bk.Term.Lab{j}}
      fv.redex.if(
        El.Quan.live(q),
        El.Eval.redex.pick(Sd.Name.is_eq(j, k), h, w),
        B,
        fv.redex.pick(
          Sd.Name.is_eq(j, k),
          h,
          w,
          B,
          fv.and_l(PM.Term.below(h, B), PM.Term.below(m, B), hf),
          fv.and_i(PM.Term.below(m, B), True{}, fv.and_r(PM.Term.below(h, B), PM.Term.below(m, B), hf), {==})))
    case g y:
      fv.call(ds, Bk.Term.App{q, g, y}, B, hd, fv.and_i(PM.Term.below(g, B), PM.Term.below(y, B), hf, hx))

# Steps
# -----

def fv.step.app(
  q: Bk.Quan,
  +f: Bk.Term,
  +x: Bk.Term,
  sf: Maybe<Bk.Term>,
  vf: Bool,
  live: Bool,
  sx: Maybe<Bk.Term>,
  vx: Bool,
  +r: Maybe<Bk.Term>,
  +B: Nat,
  +hf: {PM.Term.below(f, B) == True{} : Bool},
  +hx: {PM.Term.below(x, B) == True{} : Bool},
  hsf: {fv.Mt(sf, B) == True{} : Bool},
  hsx: {fv.Mt(sx, B) == True{} : Bool},
  +hr: {fv.Mt(r, B) == True{} : Bool}
) -> {fv.Mt(El.Eval.step.app(q, f, x, sf, vf, live, sx, vx, r), B) == True{} : Bool}:
  match sf:
    case Some{+f2}:
      fv.and_i(PM.Term.below(f2, B), PM.Term.below(x, B), hsf, hx)
    case None{}:
      match vf:
        case False{}:
          {==}
        case True{}:
          match live:
            case False{}:
              hr
            case True{}:
              match sx:
                case Some{+x2}:
                  fv.and_i(PM.Term.below(f, B), PM.Term.below(x2, B), hf, hsx)
                case None{}:
                  match vx:
                    case True{}:
                      hr
                    case False{}:
                      {==}

def fv.step.unlet(
  fits: Bool,
  f: Bk.Term,
  +v: Bk.Term,
  +B: Nat,
  hf: {PM.Term.below(f, 1n+B) == True{} : Bool},
  hv: {PM.Term.below(v, B) == True{} : Bool}
) -> {fv.Mt(El.Eval.step.unlet(fits, f, v), B) == True{} : Bool}:
  match fits:
    case True{}:
      fv.inst(f, v, B, hf, hv)
    case False{}:
      {==}

def fv.step.let(
  +q: Bk.Quan,
  +v: Bk.Term,
  +f: Bk.Term,
  live: Bool,
  sv: Maybe<Bk.Term>,
  vv: Bool,
  +fits: Bool,
  +B: Nat,
  +hv: {PM.Term.below(v, B) == True{} : Bool},
  +hf: {PM.Term.below(f, 1n+B) == True{} : Bool},
  hsv: {fv.Mt(sv, B) == True{} : Bool}
) -> {fv.Mt(El.Eval.step.let(q, v, f, live, sv, vv, fits), B) == True{} : Bool}:
  match live:
    case False{}:
      fv.step.unlet(fits, f, v, B, hf, hv)
    case True{}:
      match sv:
        case Some{+v2}:
          fv.and_i(PM.Term.below(v2, B), PM.Term.below(f, 1n+B), hsv, hf)
        case None{}:
          match vv:
            case True{}:
              fv.step.unlet(fits, f, v, B, hf, hv)
            case False{}:
              {==}

def fv.step.tup_b(
  q: Bk.Quan,
  +a: Bk.Term,
  sb: Maybe<Bk.Term>,
  +B: Nat,
  ha: {PM.Term.below(a, B) == True{} : Bool},
  hsb: {fv.Mt(sb, B) == True{} : Bool}
) -> {fv.Mt(El.Eval.step.tup_b(q, a, sb), B) == True{} : Bool}:
  match sb:
    case Some{+b2}:
      fv.and_i(PM.Term.below(a, B), PM.Term.below(b2, B), ha, hsb)
    case None{}:
      {==}

def fv.step.tup(
  +q: Bk.Quan,
  +a: Bk.Term,
  +b: Bk.Term,
  live: Bool,
  sa: Maybe<Bk.Term>,
  va: Bool,
  +sb: Maybe<Bk.Term>,
  +B: Nat,
  +ha: {PM.Term.below(a, B) == True{} : Bool},
  +hb: {PM.Term.below(b, B) == True{} : Bool},
  hsa: {fv.Mt(sa, B) == True{} : Bool},
  +hsb: {fv.Mt(sb, B) == True{} : Bool}
) -> {fv.Mt(El.Eval.step.tup(q, a, b, live, sa, va, sb), B) == True{} : Bool}:
  match live:
    case False{}:
      fv.step.tup_b(q, a, sb, B, ha, hsb)
    case True{}:
      match sa:
        case Some{+a2}:
          fv.and_i(PM.Term.below(a2, B), PM.Term.below(b, B), hsa, hb)
        case None{}:
          match va:
            case True{}:
              fv.step.tup_b(q, a, sb, B, ha, hsb)
            case False{}:
              {==}

def fv.step.cast(e: Bk.Term, f: Bk.Term, +B: Nat, hf: {PM.Term.below(f, B) == True{} : Bool}) ->
  {fv.Mt(El.Eval.step.cast(e, f), B) == True{} : Bool}:
  match e:
    case Bk.Term.Rfl{}:
      hf
    case _:
      {==}

def fv.step.rwt(
  +e: Bk.Term,
  +P: Bk.Term,
  +f: Bk.Term,
  se: Maybe<Bk.Term>,
  ve: Bool,
  +B: Nat,
  hP: {PM.Term.below(P, 2n+B) == True{} : Bool},
  +hf: {PM.Term.below(f, B) == True{} : Bool},
  hse: {fv.Mt(se, B) == True{} : Bool}
) -> {fv.Mt(El.Eval.step.rwt(e, P, f, se, ve), B) == True{} : Bool}:
  match se:
    case Some{+e2}:
      fv.and_i(
        PM.Term.below(e2, B),
        Bool.and(PM.Term.below(P, 2n+B), PM.Term.below(f, B)),
        hse,
        fv.and_i(PM.Term.below(P, 2n+B), PM.Term.below(f, B), hP, hf))
    case None{}:
      match ve:
        case True{}:
          fv.step.cast(e, f, B, hf)
        case False{}:
          {==}

def fv.meet.of(i: Maybe<Bk.Quan>, j: Maybe<Bk.Quan>, +B: Nat) -> {fv.Mt(El.Eval.meet.of(i, j), B) == True{} : Bool}:
  match i j:
    case Some{_} Some{_}:
      {==}
    case _ _:
      {==}

# the meet of two terms is a label, or none
def fv.meet(a: Bk.Term, b: Bk.Term, +B: Nat) -> {fv.Mt(El.Eval.meet(a, b), B) == True{} : Bool}:
  match a b:
    case Bk.Term.Lab{+i} Bk.Term.Lab{+j}:
      fv.meet.of(El.Quan.read(i), El.Quan.read(j), B)
    case _ _:
      {==}

def fv.step.min(
  +a: Bk.Term,
  +b: Bk.Term,
  sa: Maybe<Bk.Term>,
  va: Bool,
  sb: Maybe<Bk.Term>,
  vb: Bool,
  m: Maybe<Bk.Term>,
  +B: Nat,
  +ha: {PM.Term.below(a, B) == True{} : Bool},
  +hb: {PM.Term.below(b, B) == True{} : Bool},
  hsa: {fv.Mt(sa, B) == True{} : Bool},
  hsb: {fv.Mt(sb, B) == True{} : Bool},
  hm: {fv.Mt(m, B) == True{} : Bool}
) -> {fv.Mt(El.Eval.step.min(a, b, sa, va, sb, vb, m), B) == True{} : Bool}:
  match sa:
    case Some{+a2}:
      fv.and_i(PM.Term.below(a2, B), PM.Term.below(b, B), hsa, hb)
    case None{}:
      match va:
        case False{}:
          {==}
        case True{}:
          match sb:
            case Some{+b2}:
              fv.and_i(PM.Term.below(a, B), PM.Term.below(b2, B), ha, hsb)
            case None{}:
              match vb:
                case True{}:
                  hm
                case False{}:
                  {==}

# one step of a term below B, in defs below B: below B
def fv.st(
  +ds: List<&2, Bk.Def>,
  t: Bk.Term,
  +B: Nat,
  +hd: {Defs.below(ds, B) == True{} : Bool},
  +ht: {PM.Term.below(t, B) == True{} : Bool}
) -> {fv.Mt(El.Eval.step(ds, t), B) == True{} : Bool}:
  match t:
    case Bk.Term.Ann{+x, +y}:
      fv.and_l(PM.Term.below(x, B), PM.Term.below(y, B), ht)
    case Bk.Term.Ref{+k}:
      fv.call(ds, Bk.Term.Ref{k}, B, hd, {==})
    case Bk.Term.App{+q, +f, +x}:
      +hf = fv.and_l(PM.Term.below(f, B), PM.Term.below(x, B), ht)
      +hx = fv.and_r(PM.Term.below(f, B), PM.Term.below(x, B), ht)
      fv.step.app(
        q,
        f,
        x,
        El.Eval.step(ds, f),
        El.Eval.vals(ds, f, False{}),
        El.Quan.live(q),
        El.Eval.step(ds, x),
        El.Eval.vals(ds, x, False{}),
        El.Eval.redex(ds, q, f, x),
        B,
        hf,
        hx,
        fv.st(ds, f, B, hd, hf),
        fv.st(ds, x, B, hd, hx),
        fv.redex(ds, q, f, x, B, hd, hf, hx))
    case Bk.Term.Let{+q, +v, +f}:
      +hv = fv.and_l(PM.Term.below(v, B), PM.Term.below(f, 1n+B), ht)
      fv.step.let(
        q,
        v,
        f,
        El.Quan.live(q),
        El.Eval.step(ds, v),
        El.Eval.vals(ds, v, False{}),
        El.Quan.fits(q, v),
        B,
        hv,
        fv.and_r(PM.Term.below(v, B), PM.Term.below(f, 1n+B), ht),
        fv.st(ds, v, B, hd, hv))
    case Bk.Term.Tup{+q, +a, +b}:
      +ha = fv.and_l(PM.Term.below(a, B), PM.Term.below(b, B), ht)
      +hb = fv.and_r(PM.Term.below(a, B), PM.Term.below(b, B), ht)
      fv.step.tup(
        q,
        a,
        b,
        El.Quan.live(q),
        El.Eval.step(ds, a),
        El.Eval.vals(ds, a, False{}),
        El.Eval.step(ds, b),
        B,
        ha,
        hb,
        fv.st(ds, a, B, hd, ha),
        fv.st(ds, b, B, hd, hb))
    case Bk.Term.Rwt{+e, +P, +f}:
      +he = fv.and_l(PM.Term.below(e, B), Bool.and(PM.Term.below(P, 2n+B), PM.Term.below(f, B)), ht)
      +hr = fv.and_r(PM.Term.below(e, B), Bool.and(PM.Term.below(P, 2n+B), PM.Term.below(f, B)), ht)
      fv.step.rwt(
        e,
        P,
        f,
        El.Eval.step(ds, e),
        El.Eval.vals(ds, e, False{}),
        B,
        fv.and_l(PM.Term.below(P, 2n+B), PM.Term.below(f, B), hr),
        fv.and_r(PM.Term.below(P, 2n+B), PM.Term.below(f, B), hr),
        fv.st(ds, e, B, hd, he))
    case Bk.Term.Min{+a, +b}:
      +ha = fv.and_l(PM.Term.below(a, B), PM.Term.below(b, B), ht)
      +hb = fv.and_r(PM.Term.below(a, B), PM.Term.below(b, B), ht)
      fv.step.min(
        a,
        b,
        El.Eval.step(ds, a),
        El.Eval.vals(ds, a, False{}),
        El.Eval.step(ds, b),
        El.Eval.vals(ds, b, False{}),
        El.Eval.meet(a, b),
        B,
        ha,
        hb,
        fv.st(ds, a, B, hd, ha),
        fv.st(ds, b, B, hd, hb),
        fv.meet(a, b, B))
    case _:
      {==}

# (a) Eval never raises the largest free variable
# -----------------------------------------------

# a step of a term below B, in defs below B, is below B
def fv.step(
  ds: List<&2, Bk.Def>,
  t: Bk.Term,
  u: Bk.Term,
  +B: Nat,
  hd: {Defs.below(ds, B) == True{} : Bool},
  ht: {PM.Term.below(t, B) == True{} : Bool},
  h: {El.Eval.step(ds, t) == Some{u} : Maybe<Bk.Term>}
) -> {PM.Term.below(u, B) == True{} : Bool}:
  %h : {fv.Mt(_, B) == True{} : Bool}
  fv.st(ds, t, B, hd, ht)

def fv.run(
  n: Nat,
  +ds: List<&2, Bk.Def>,
  r: Maybe<Bk.Term>,
  +B: Nat,
  +hd: {Defs.below(ds, B) == True{} : Bool},
  hr: {fv.Mt(r, B) == True{} : Bool}
) -> {fv.Mt(El.Eval.run(n, ds, r), B) == True{} : Bool}:
  match n r:
    case 0n s:
      hr
    case 1n+_ None{}:
      {==}
    case 1n++m Some{+t}:
      fv.run(m, ds, El.Eval.step(ds, t), B, hd, fv.st(ds, t, B, hd, hr))

# n steps of a term below B, in defs below B, give a term below B
def fv.steps(
  n: Nat,
  ds: List<&2, Bk.Def>,
  t: Bk.Term,
  u: Bk.Term,
  +B: Nat,
  hd: {Defs.below(ds, B) == True{} : Bool},
  ht: {PM.Term.below(t, B) == True{} : Bool},
  h: {El.Eval.steps(n, ds, t) == Some{u} : Maybe<Bk.Term>}
) -> {PM.Term.below(u, B) == True{} : Bool}:
  %h : {fv.Mt(_, B) == True{} : Bool}
  fv.run(n, ds, Some{t}, B, hd, ht)

# The start term
# --------------

def fv.bit(b: Bool) -> {PM.Term.below(Pg.Program.bit(b), 0n) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def fv.word(n: Nat, w: Word(n)) -> {PM.Term.below(Pg.Program.word(n, w), 0n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      match w:
        case WCon{+b, +t}:
          fv.and_i(
            PM.Term.below(Pg.Program.bit(b), 0n),
            Bool.and(PM.Term.below(Pg.Program.word(p, t), 0n), True{}),
            fv.bit(b),
            fv.and_i(PM.Term.below(Pg.Program.word(p, t), 0n), True{}, fv.word(p, t), {==}))

def fv.bytes(i: List<&2, Word(8n)>) -> {PM.Term.below(Pg.Program.bytes(i), 0n) == True{} : Bool}:
  match i:
    case Nil{}:
      {==}
    case Con{+b, +rest}:
      fv.and_i(
        PM.Term.below(Pg.Program.word(8n, b), 0n),
        Bool.and(PM.Term.below(Pg.Program.bytes(rest), 0n), True{}),
        fv.word(8n, b),
        fv.and_i(PM.Term.below(Pg.Program.bytes(rest), 0n), True{}, fv.bytes(rest), {==}))

# the start term is closed
def fv.start(i: List<&2, Word(8n)>) -> {PM.Term.below(Pg.Program.start(i), 0n) == True{} : Bool}:
  fv.bytes(i)
