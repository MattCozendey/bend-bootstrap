# compiler: layer B5, the canonical form of a term (D6)
# =====================================================
#
# Eval never sees the index of a free variable: it makes no step under a
# binder, and it only moves a free variable (Term.subst, Term.shift, Env.sub)
# or asks whether a term is one (it is no value, no pair, no label, and no
# Data). So the machine runs each free variable as one poison cell, whose term
# at the depth d is the canonical free variable Var{d}. The canonical form of
# a term makes each of its free variables so; Eval's step from it is, made
# canonical, the canonical form of Eval's step (canon.step). So a run of
# canonical steps follows Eval's run step for step, and gives its result.
#
# Pure term meta-theory: it imports Base, Book, Eval and Program only.

import Base
import ../../../Shared/shared.bend as Sd
import ../../../Book/impl.bend as Bk
import ../../../Eval/impl.bend as El
import ../../../Program/impl.bend as Pg

# Terms
# -----

def Quan.is_eq(p: Bk.Quan, q: Bk.Quan) -> Bool:
  match p q:
    case Bk.Quan.Q0{} Bk.Quan.Q0{}:
      True{}
    case Bk.Quan.Q1{} Bk.Quan.Q1{}:
      True{}
    case Bk.Quan.Q2{} Bk.Quan.Q2{}:
      True{}
    case _ _:
      False{}

def Names.is_eq(ks: List<&2, List<&2, Word(8n)>>, js: List<&2, List<&2, Word(8n)>>) -> Bool:
  match ks js:
    case Nil{} Nil{}:
      True{}
    case Con{k, kr} Con{j, jr}:
      Sd.Name.is_eq(k, j) && Names.is_eq(kr, jr)
    case _ _:
      False{}

# a Bool equality of terms
def Term.is_eq(a: Bk.Term, b: Bk.Term) -> Bool:
  match a b:
    case Bk.Term.Var{i} Bk.Term.Var{j}:
      Nat.is_eq(i, j)
    case Bk.Term.Ref{k} Bk.Term.Ref{j}:
      Sd.Name.is_eq(k, j)
    case Bk.Term.Ann{x, T} Bk.Term.Ann{y, U}:
      Term.is_eq(x, y) && Term.is_eq(T, U)
    case Bk.Term.Let{q, v, f} Bk.Term.Let{p, w, g}:
      Quan.is_eq(q, p) && Term.is_eq(v, w) && Term.is_eq(f, g)
    case Bk.Term.Typ{q} Bk.Term.Typ{p}:
      Term.is_eq(q, p)
    case Bk.Term.Min{a1, b1} Bk.Term.Min{a2, b2}:
      Term.is_eq(a1, a2) && Term.is_eq(b1, b2)
    case Bk.Term.All{q, A1, B1} Bk.Term.All{p, A2, B2}:
      Quan.is_eq(q, p) && Term.is_eq(A1, A2) && Term.is_eq(B1, B2)
    case Bk.Term.Lam{q, f} Bk.Term.Lam{p, g}:
      Quan.is_eq(q, p) && Term.is_eq(f, g)
    case Bk.Term.App{q, f, x} Bk.Term.App{p, g, y}:
      Quan.is_eq(q, p) && Term.is_eq(f, g) && Term.is_eq(x, y)
    case Bk.Term.Sig{q, A1, B1} Bk.Term.Sig{p, A2, B2}:
      Quan.is_eq(q, p) && Term.is_eq(A1, A2) && Term.is_eq(B1, B2)
    case Bk.Term.Tup{q, a1, b1} Bk.Term.Tup{p, a2, b2}:
      Quan.is_eq(q, p) && Term.is_eq(a1, a2) && Term.is_eq(b1, b2)
    case Bk.Term.Prj{h} Bk.Term.Prj{g}:
      Term.is_eq(h, g)
    case Bk.Term.Enu{ks} Bk.Term.Enu{js}:
      Names.is_eq(ks, js)
    case Bk.Term.Lab{k} Bk.Term.Lab{j}:
      Sd.Name.is_eq(k, j)
    case Bk.Term.Mat{k, h1, m1} Bk.Term.Mat{j, h2, m2}:
      Sd.Name.is_eq(k, j) && Term.is_eq(h1, h2) && Term.is_eq(m1, m2)
    case Bk.Term.Efq{} Bk.Term.Efq{}:
      True{}
    case Bk.Term.Eql{a1, b1, T1} Bk.Term.Eql{a2, b2, T2}:
      Term.is_eq(a1, a2) && Term.is_eq(b1, b2) && Term.is_eq(T1, T2)
    case Bk.Term.Rfl{} Bk.Term.Rfl{}:
      True{}
    case Bk.Term.Rwt{e1, P1, f1} Bk.Term.Rwt{e2, P2, f2}:
      Term.is_eq(e1, e2) && Term.is_eq(P1, P2) && Term.is_eq(f1, f2)
    case _ _:
      False{}

# r is Some of t
def Tm.is(r: Maybe<Bk.Term>, t: Bk.Term) -> Bool:
  match r:
    case Some{u}:
      Term.is_eq(u, t)
    case None{}:
      False{}

# r is None
def Tm.none(r: Maybe<Bk.Term>) -> Bool:
  match r:
    case Some{_}:
      False{}
    case None{}:
      True{}

# t at the depth d has no free variable: at the inner depth e, each index is
# below d + e
def Term.closed(t: Bk.Term, +d: Nat) -> Bool:
  match t:
    case Bk.Term.Var{i}:
      Nat.is_lt(i, d)
    case Bk.Term.Ref{_}:
      True{}
    case Bk.Term.Ann{x, T}:
      Term.closed(x, d) && Term.closed(T, d)
    case Bk.Term.Let{_, v, f}:
      Term.closed(v, d) && Term.closed(f, 1n+d)
    case Bk.Term.Typ{q}:
      Term.closed(q, d)
    case Bk.Term.Min{a, b}:
      Term.closed(a, d) && Term.closed(b, d)
    case Bk.Term.All{_, A, B}:
      Term.closed(A, d) && Term.closed(B, 1n+d)
    case Bk.Term.Lam{_, f}:
      Term.closed(f, 1n+d)
    case Bk.Term.App{_, f, x}:
      Term.closed(f, d) && Term.closed(x, d)
    case Bk.Term.Sig{_, A, B}:
      Term.closed(A, d) && Term.closed(B, 1n+d)
    case Bk.Term.Tup{_, a, b}:
      Term.closed(a, d) && Term.closed(b, d)
    case Bk.Term.Prj{h}:
      Term.closed(h, d)
    case Bk.Term.Enu{_}:
      True{}
    case Bk.Term.Lab{_}:
      True{}
    case Bk.Term.Mat{_, h, m}:
      Term.closed(h, d) && Term.closed(m, d)
    case Bk.Term.Efq{}:
      True{}
    case Bk.Term.Eql{a, b, T}:
      Term.closed(a, d) && Term.closed(b, d) && Term.closed(T, d)
    case Bk.Term.Rfl{}:
      True{}
    case Bk.Term.Rwt{e, P, f}:
      Term.closed(e, d) && Term.closed(P, 2n+d) && Term.closed(f, d)

# The canonical form
# ------------------

def Canon.var(lt: Bool, i: Nat, d: Nat) -> Nat:
  match lt:
    case True{}:
      i
    case False{}:
      d

# t at the depth d: each variable free there (at the inner depth e, an index
# of d + e or more) becomes the one canonical free variable Var{d + e}; the
# others stay
def Canon.term(t: Bk.Term, +d: Nat) -> Bk.Term:
  match t:
    case Bk.Term.Var{+i}:
      Bk.Term.Var{Canon.var(Nat.is_lt(i, d), i, d)}
    case Bk.Term.Ref{k}:
      Bk.Term.Ref{k}
    case Bk.Term.Ann{x, T}:
      Bk.Term.Ann{Canon.term(x, d), Canon.term(T, d)}
    case Bk.Term.Let{q, v, f}:
      Bk.Term.Let{q, Canon.term(v, d), Canon.term(f, 1n+d)}
    case Bk.Term.Typ{q}:
      Bk.Term.Typ{Canon.term(q, d)}
    case Bk.Term.Min{a, b}:
      Bk.Term.Min{Canon.term(a, d), Canon.term(b, d)}
    case Bk.Term.All{q, A, B}:
      Bk.Term.All{q, Canon.term(A, d), Canon.term(B, 1n+d)}
    case Bk.Term.Lam{q, f}:
      Bk.Term.Lam{q, Canon.term(f, 1n+d)}
    case Bk.Term.App{q, f, x}:
      Bk.Term.App{q, Canon.term(f, d), Canon.term(x, d)}
    case Bk.Term.Sig{q, A, B}:
      Bk.Term.Sig{q, Canon.term(A, d), Canon.term(B, 1n+d)}
    case Bk.Term.Tup{q, a, b}:
      Bk.Term.Tup{q, Canon.term(a, d), Canon.term(b, d)}
    case Bk.Term.Prj{h}:
      Bk.Term.Prj{Canon.term(h, d)}
    case Bk.Term.Enu{ks}:
      Bk.Term.Enu{ks}
    case Bk.Term.Lab{k}:
      Bk.Term.Lab{k}
    case Bk.Term.Mat{k, h, m}:
      Bk.Term.Mat{k, Canon.term(h, d), Canon.term(m, d)}
    case Bk.Term.Efq{}:
      Bk.Term.Efq{}
    case Bk.Term.Eql{a, b, T}:
      Bk.Term.Eql{Canon.term(a, d), Canon.term(b, d), Canon.term(T, d)}
    case Bk.Term.Rfl{}:
      Bk.Term.Rfl{}
    case Bk.Term.Rwt{e, P, f}:
      Bk.Term.Rwt{Canon.term(e, d), Canon.term(P, 2n+d), Canon.term(f, d)}

def Canon.opt(r: Maybe<Bk.Term>) -> Maybe<Bk.Term>:
  match r:
    case None{}:
      None{}
    case Some{t}:
      Some{Canon.term(t, 0n)}

# the leaf of a walk (Eval.walk), made canonical
def Canon.walk(r: Maybe<Maybe<Bk.Term>>) -> Maybe<Maybe<Bk.Term>>:
  match r:
    case Some{Some{t}}:
      Some{Some{Canon.term(t, 0n)}}
    case Some{None{}}:
      Some{None{}}
    case None{}:
      None{}

# t is canonical at the depth d
def Canon.is_at(+t: Bk.Term, +d: Nat) -> Bool:
  Term.is_eq(Canon.term(t, d), t)

# t is canonical at the depth 0
def Canon.is(+t: Bk.Term) -> Bool:
  Canon.is_at(t, 0n)

# a step of Eval, made canonical
def CStep(+ds: List<&2, Bk.Def>, +t: Bk.Term) -> Maybe<Bk.Term>:
  Canon.opt(El.Eval.step(ds, t))

# n canonical steps from r
def CSteps(n: Nat, +ds: List<&2, Bk.Def>, r: Maybe<Bk.Term>) -> Maybe<Bk.Term>:
  match n r:
    case 0n s:
      s
    case 1n+_ None{}:
      None{}
    case 1n+m Some{t}:
      CSteps(m, ds, CStep(ds, t))

# Laws
# ----

# LAW: Term.is_eq says True only of equal terms
law term.is_eq_ok:
  for +a: Bk.Term
  for +b: Bk.Term
  for e: {Term.is_eq(a, b) == True{} : Bool}
  {a == b : Bk.Term}

# LAW: Term.is_eq says True of equal terms
law term.is_eq_refl:
  for +a: Bk.Term
  {Term.is_eq(a, a) == True{} : Bool}

# LAW: Eval does not see the index of a free variable: a canonical step from
# the canonical form of t is the canonical form of t's step
law canon.step:
  for +ds: List<&2, Bk.Def>
  for +t: Bk.Term
  {CStep(ds, Canon.term(t, 0n)) == CStep(ds, t) : Maybe<Bk.Term>}

# LAW: n canonical steps from the canonical form of t are the canonical form
# of n of Eval's steps from t
law canon.steps:
  for +n: Nat
  for +ds: List<&2, Bk.Def>
  for +t: Bk.Term
  {CSteps(n, ds, Some{Canon.term(t, 0n)}) == Canon.opt(El.Eval.steps(n, ds, t)) : Maybe<Bk.Term>}

# LAW: the result does not see free variables
law canon.result:
  for +ds: List<&2, Bk.Def>
  for r: Maybe<Bk.Term>
  {Pg.Program.result(ds, Canon.opt(r)) == Pg.Program.result(ds, r) : Maybe<&2, List<&2, Word(8n)>>}

# LAW: nor the size
law canon.size:
  for +t: Bk.Term
  for +d: Nat
  {Pg.Term.size(Canon.term(t, d)) == Pg.Term.size(t) : Nat}

# LAW: nor whether a term is a value
law canon.vals:
  for +ds: List<&2, Bk.Def>
  for +t: Bk.Term
  for +d: Nat
  for a: Bool
  {El.Eval.vals(ds, Canon.term(t, d), a) == El.Eval.vals(ds, t, a) : Bool}

# LAW: nor whether a term is Data
law canon.data:
  for +t: Bk.Term
  for +d: Nat
  {El.Term.is_data(Canon.term(t, d)) == El.Term.is_data(t) : Bool}

# LAW: the canonical form is canonical
law canon.idem:
  for +t: Bk.Term
  for +d: Nat
  {Canon.term(Canon.term(t, d), d) == Canon.term(t, d) : Bk.Term}

# LAW: the start term of a run is canonical
law canon.start:
  for +i: List<&2, Word(8n)>
  {Canon.is(Pg.Program.start(i)) == True{} : Bool}

# LAW: a substitution under d binders of the terms es does not see what the
# canonical form at d + |es| changes in t
law canon.subst:
  for +t: Bk.Term
  for +es: List<&2, Bk.Term>
  for +d: Nat
  {Canon.term(El.Term.subst(Canon.term(t, Nat.add(d, List.length(&2, Bk.Term, es))), es, d), d) ==
    Canon.term(El.Term.subst(t, es, d), d) : Bk.Term}

# LAW: a term t canonical at d, moved up by n (n at least |es|) and then
# substituted at d by es, is t again, once made canonical: its free variables
# stay free (the copy's sharing of a part with a poison cell rests on this)
law canon.subst_below:
  for +t: Bk.Term
  for +es: List<&2, Bk.Term>
  for +n: Nat
  for +d: Nat
  for hc: {Canon.is_at(t, d) == True{} : Bool}
  for hn: {Nat.is_le(List.length(&2, Bk.Term, es), n) == True{} : Bool}
  {Canon.term(El.Term.subst(El.Term.shift(t, n, d), es, d), d) == t : Bk.Term}

# LAW: a term with no free variable at d is its own substitution at d, and
# its own canonical form (the copy's sharing of an image's part)
law canon.subst_closed:
  for +t: Bk.Term
  for +es: List<&2, Bk.Term>
  for +d: Nat
  for hc: {Term.closed(t, d) == True{} : Bool}
  {Canon.term(El.Term.subst(t, es, d), d) == t : Bk.Term}

# LAW: the local j, as the substitution under k binders puts it in, made
# canonical, is the local moved up by k, when the local is canonical (the
# copy's sharing of a local, with no shift)
law canon.lift:
  for +es: List<&2, Bk.Term>
  for +k: Nat
  for +j: Nat
  for hc: {Canon.is(El.Env.sub(es, j)) == True{} : Bool}
  {Canon.term(El.Term.lift(es, k, Nat.add(k, j)), k) == El.Term.shift(El.Env.sub(es, j), k, 0n) : Bk.Term}
