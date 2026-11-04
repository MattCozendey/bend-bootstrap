# compiler: layer B5, the proofs of canon/spec.bend
# =================================================
#
# One def per law of canon/spec.bend. The route for the open ones: a relation
# Rel(d, t, u) (the same shape; a variable bound below d + e is the same in
# both; above, both are free), kept by Term.shift, Term.subst, Env.sub,
# Eval.walk, Eval.vals, Eval.callWalk, Eval.redex and Eval.step; and
# Canon.term(t, d) = Canon.term(u, d) iff Rel(d, t, u).

import Base
import ../../../Book/impl.bend as Bk
import ../../../Eval/impl.bend as El
import ../../../Program/impl.bend as Pg
import ./spec.bend as C

def C.term.is_eq_ok(a, b, e):
  ?TODO

def C.term.is_eq_refl(a):
  ?TODO

def C.canon.step(ds, t):
  ?TODO

# CSteps follows Eval.run, from any start, by canon.step at each step
def canon.steps.go(m: Nat, +ds: List<&2, Bk.Def>, r: Maybe<Bk.Term>) ->
  {C.CSteps(m, ds, C.Canon.opt(r)) == C.Canon.opt(El.Eval.run(m, ds, r)) : Maybe<Bk.Term>}:
  match m r:
    case 0n _:
      {==}
    case 1n+k None{}:
      {==}
    case 1n+k Some{+t}:
      %Equal.sym(Maybe<Bk.Term>, C.CStep(ds, C.Canon.term(t, 0n)), C.CStep(ds, t), C.canon.step(ds, t)) :
        {C.CSteps(k, ds, _) == C.Canon.opt(El.Eval.run(k, ds, El.Eval.step(ds, t))) : Maybe<Bk.Term>}
      canon.steps.go(k, ds, El.Eval.step(ds, t))

def C.canon.steps(n, ds, t):
  canon.steps.go(n, ds, Some{t})

def C.canon.result(ds, r):
  ?TODO

def C.canon.size(t, d):
  match t:
    case Bk.Term.Var{i}:
      {==}
    case Bk.Term.Ref{k}:
      {==}
    case Bk.Term.Ann{x, T}:
      %C.canon.size(x, d) : {1n+Nat.add(Pg.Term.size(C.Canon.term(x, d)), Pg.Term.size(C.Canon.term(T, d))) == 1n+Nat.add(_, Pg.Term.size(T)) : Nat}
      %C.canon.size(T, d) : {1n+Nat.add(Pg.Term.size(C.Canon.term(x, d)), Pg.Term.size(C.Canon.term(T, d))) == 1n+Nat.add(Pg.Term.size(C.Canon.term(x, d)), _) : Nat}
      {==}
    case Bk.Term.Let{q, v, f}:
      %C.canon.size(v, d) : {1n+Nat.add(Pg.Term.size(C.Canon.term(v, d)), Pg.Term.size(C.Canon.term(f, 1n+d))) == 1n+Nat.add(_, Pg.Term.size(f)) : Nat}
      %C.canon.size(f, 1n+d) : {1n+Nat.add(Pg.Term.size(C.Canon.term(v, d)), Pg.Term.size(C.Canon.term(f, 1n+d))) == 1n+Nat.add(Pg.Term.size(C.Canon.term(v, d)), _) : Nat}
      {==}
    case Bk.Term.Typ{q}:
      %C.canon.size(q, d) : {1n+Pg.Term.size(C.Canon.term(q, d)) == 1n+_ : Nat}
      {==}
    case Bk.Term.Min{a, b}:
      %C.canon.size(a, d) : {1n+Nat.add(Pg.Term.size(C.Canon.term(a, d)), Pg.Term.size(C.Canon.term(b, d))) == 1n+Nat.add(_, Pg.Term.size(b)) : Nat}
      %C.canon.size(b, d) : {1n+Nat.add(Pg.Term.size(C.Canon.term(a, d)), Pg.Term.size(C.Canon.term(b, d))) == 1n+Nat.add(Pg.Term.size(C.Canon.term(a, d)), _) : Nat}
      {==}
    case Bk.Term.All{q, A, B}:
      %C.canon.size(A, d) : {1n+Nat.add(Pg.Term.size(C.Canon.term(A, d)), Pg.Term.size(C.Canon.term(B, 1n+d))) == 1n+Nat.add(_, Pg.Term.size(B)) : Nat}
      %C.canon.size(B, 1n+d) : {1n+Nat.add(Pg.Term.size(C.Canon.term(A, d)), Pg.Term.size(C.Canon.term(B, 1n+d))) == 1n+Nat.add(Pg.Term.size(C.Canon.term(A, d)), _) : Nat}
      {==}
    case Bk.Term.Lam{q, f}:
      %C.canon.size(f, 1n+d) : {1n+Pg.Term.size(C.Canon.term(f, 1n+d)) == 1n+_ : Nat}
      {==}
    case Bk.Term.App{q, f, x}:
      %C.canon.size(f, d) : {1n+Nat.add(Pg.Term.size(C.Canon.term(f, d)), Pg.Term.size(C.Canon.term(x, d))) == 1n+Nat.add(_, Pg.Term.size(x)) : Nat}
      %C.canon.size(x, d) : {1n+Nat.add(Pg.Term.size(C.Canon.term(f, d)), Pg.Term.size(C.Canon.term(x, d))) == 1n+Nat.add(Pg.Term.size(C.Canon.term(f, d)), _) : Nat}
      {==}
    case Bk.Term.Sig{q, A, B}:
      %C.canon.size(A, d) : {1n+Nat.add(Pg.Term.size(C.Canon.term(A, d)), Pg.Term.size(C.Canon.term(B, 1n+d))) == 1n+Nat.add(_, Pg.Term.size(B)) : Nat}
      %C.canon.size(B, 1n+d) : {1n+Nat.add(Pg.Term.size(C.Canon.term(A, d)), Pg.Term.size(C.Canon.term(B, 1n+d))) == 1n+Nat.add(Pg.Term.size(C.Canon.term(A, d)), _) : Nat}
      {==}
    case Bk.Term.Tup{q, a, b}:
      %C.canon.size(a, d) : {1n+Nat.add(Pg.Term.size(C.Canon.term(a, d)), Pg.Term.size(C.Canon.term(b, d))) == 1n+Nat.add(_, Pg.Term.size(b)) : Nat}
      %C.canon.size(b, d) : {1n+Nat.add(Pg.Term.size(C.Canon.term(a, d)), Pg.Term.size(C.Canon.term(b, d))) == 1n+Nat.add(Pg.Term.size(C.Canon.term(a, d)), _) : Nat}
      {==}
    case Bk.Term.Prj{h}:
      %C.canon.size(h, d) : {1n+Pg.Term.size(C.Canon.term(h, d)) == 1n+_ : Nat}
      {==}
    case Bk.Term.Enu{ks}:
      {==}
    case Bk.Term.Lab{k}:
      {==}
    case Bk.Term.Mat{k, h, m}:
      %C.canon.size(h, d) : {1n+Nat.add(Pg.Term.size(C.Canon.term(h, d)), Pg.Term.size(C.Canon.term(m, d))) == 1n+Nat.add(_, Pg.Term.size(m)) : Nat}
      %C.canon.size(m, d) : {1n+Nat.add(Pg.Term.size(C.Canon.term(h, d)), Pg.Term.size(C.Canon.term(m, d))) == 1n+Nat.add(Pg.Term.size(C.Canon.term(h, d)), _) : Nat}
      {==}
    case Bk.Term.Efq{}:
      {==}
    case Bk.Term.Eql{a, b, T}:
      %C.canon.size(a, d) : {1n+Nat.add(Pg.Term.size(C.Canon.term(a, d)), Nat.add(Pg.Term.size(C.Canon.term(b, d)), Pg.Term.size(C.Canon.term(T, d)))) == 1n+Nat.add(_, Nat.add(Pg.Term.size(b), Pg.Term.size(T))) : Nat}
      %C.canon.size(b, d) : {1n+Nat.add(Pg.Term.size(C.Canon.term(a, d)), Nat.add(Pg.Term.size(C.Canon.term(b, d)), Pg.Term.size(C.Canon.term(T, d)))) == 1n+Nat.add(Pg.Term.size(C.Canon.term(a, d)), Nat.add(_, Pg.Term.size(T))) : Nat}
      %C.canon.size(T, d) : {1n+Nat.add(Pg.Term.size(C.Canon.term(a, d)), Nat.add(Pg.Term.size(C.Canon.term(b, d)), Pg.Term.size(C.Canon.term(T, d)))) == 1n+Nat.add(Pg.Term.size(C.Canon.term(a, d)), Nat.add(Pg.Term.size(C.Canon.term(b, d)), _)) : Nat}
      {==}
    case Bk.Term.Rfl{}:
      {==}
    case Bk.Term.Rwt{e, P, f}:
      %C.canon.size(e, d) : {1n+Nat.add(Pg.Term.size(C.Canon.term(e, d)), Nat.add(Pg.Term.size(C.Canon.term(P, 2n+d)), Pg.Term.size(C.Canon.term(f, d)))) == 1n+Nat.add(_, Nat.add(Pg.Term.size(P), Pg.Term.size(f))) : Nat}
      %C.canon.size(P, 2n+d) : {1n+Nat.add(Pg.Term.size(C.Canon.term(e, d)), Nat.add(Pg.Term.size(C.Canon.term(P, 2n+d)), Pg.Term.size(C.Canon.term(f, d)))) == 1n+Nat.add(Pg.Term.size(C.Canon.term(e, d)), Nat.add(_, Pg.Term.size(f))) : Nat}
      %C.canon.size(f, d) : {1n+Nat.add(Pg.Term.size(C.Canon.term(e, d)), Nat.add(Pg.Term.size(C.Canon.term(P, 2n+d)), Pg.Term.size(C.Canon.term(f, d)))) == 1n+Nat.add(Pg.Term.size(C.Canon.term(e, d)), Nat.add(Pg.Term.size(C.Canon.term(P, 2n+d)), _)) : Nat}
      {==}

def C.canon.vals(ds, t, d, a):
  ?TODO

def C.canon.data(t, d):
  match t:
    case Bk.Term.Var{i}:
      {==}
    case Bk.Term.Ref{k}:
      {==}
    case Bk.Term.Ann{x, T}:
      {==}
    case Bk.Term.Let{q, v, f}:
      {==}
    case Bk.Term.Typ{q}:
      {==}
    case Bk.Term.Min{a, b}:
      {==}
    case Bk.Term.All{q, A, B}:
      {==}
    case Bk.Term.Lam{q, f}:
      {==}
    case Bk.Term.App{q, f, x}:
      {==}
    case Bk.Term.Sig{q, A, B}:
      {==}
    case Bk.Term.Tup{q, a, b}:
      %C.canon.data(a, d) : {(Bool.not(El.Quan.live(q)) || El.Term.is_data(C.Canon.term(a, d))) && El.Term.is_data(C.Canon.term(b, d)) == (Bool.not(El.Quan.live(q)) || _) && El.Term.is_data(b) : Bool}
      %C.canon.data(b, d) : {(Bool.not(El.Quan.live(q)) || El.Term.is_data(C.Canon.term(a, d))) && El.Term.is_data(C.Canon.term(b, d)) == (Bool.not(El.Quan.live(q)) || El.Term.is_data(C.Canon.term(a, d))) && _ : Bool}
      {==}
    case Bk.Term.Prj{h}:
      {==}
    case Bk.Term.Enu{ks}:
      {==}
    case Bk.Term.Lab{k}:
      {==}
    case Bk.Term.Mat{k, h, m}:
      {==}
    case Bk.Term.Efq{}:
      {==}
    case Bk.Term.Eql{a, b, T}:
      {==}
    case Bk.Term.Rfl{}:
      {==}
    case Bk.Term.Rwt{e, P, f}:
      {==}

# Canon.var is its own canonical form
def canon.var.dd(b: Bool, +d: Nat) -> {C.Canon.var(b, d, d) == d : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def canon.var.idem(lt: Bool, +i: Nat, +d: Nat, e: {Nat.is_lt(i, d) == lt : Bool}) ->
  {C.Canon.var(Nat.is_lt(C.Canon.var(lt, i, d), d), C.Canon.var(lt, i, d), d) == C.Canon.var(lt, i, d) : Nat}:
  match lt:
    case True{}:
      %Equal.sym(Bool, Nat.is_lt(i, d), True{}, e) : {C.Canon.var(_, i, d) == i : Nat}
      {==}
    case False{}:
      canon.var.dd(Nat.is_lt(d, d), d)

def C.canon.idem(t, d):
  match t:
    case Bk.Term.Var{+i}:
      Equal.cong(Nat, Bk.Term, n => Bk.Term.Var{n}, C.Canon.var(Nat.is_lt(C.Canon.var(Nat.is_lt(i, d), i, d), d), C.Canon.var(Nat.is_lt(i, d), i, d), d),
        C.Canon.var(Nat.is_lt(i, d), i, d), canon.var.idem(Nat.is_lt(i, d), i, d, {==}))
    case Bk.Term.Ref{k}:
      {==}
    case Bk.Term.Ann{x, T}:
      %C.canon.idem(x, d) : {Bk.Term.Ann{C.Canon.term(C.Canon.term(x, d), d), C.Canon.term(C.Canon.term(T, d), d)} == Bk.Term.Ann{_, C.Canon.term(T, d)} : Bk.Term}
      %C.canon.idem(T, d) : {Bk.Term.Ann{C.Canon.term(C.Canon.term(x, d), d), C.Canon.term(C.Canon.term(T, d), d)} == Bk.Term.Ann{C.Canon.term(C.Canon.term(x, d), d), _} : Bk.Term}
      {==}
    case Bk.Term.Let{q, v, f}:
      %C.canon.idem(v, d) : {Bk.Term.Let{q, C.Canon.term(C.Canon.term(v, d), d), C.Canon.term(C.Canon.term(f, 1n+d), 1n+d)} == Bk.Term.Let{q, _, C.Canon.term(f, 1n+d)} : Bk.Term}
      %C.canon.idem(f, 1n+d) : {Bk.Term.Let{q, C.Canon.term(C.Canon.term(v, d), d), C.Canon.term(C.Canon.term(f, 1n+d), 1n+d)} == Bk.Term.Let{q, C.Canon.term(C.Canon.term(v, d), d), _} : Bk.Term}
      {==}
    case Bk.Term.Typ{q}:
      %C.canon.idem(q, d) : {Bk.Term.Typ{C.Canon.term(C.Canon.term(q, d), d)} == Bk.Term.Typ{_} : Bk.Term}
      {==}
    case Bk.Term.Min{a, b}:
      %C.canon.idem(a, d) : {Bk.Term.Min{C.Canon.term(C.Canon.term(a, d), d), C.Canon.term(C.Canon.term(b, d), d)} == Bk.Term.Min{_, C.Canon.term(b, d)} : Bk.Term}
      %C.canon.idem(b, d) : {Bk.Term.Min{C.Canon.term(C.Canon.term(a, d), d), C.Canon.term(C.Canon.term(b, d), d)} == Bk.Term.Min{C.Canon.term(C.Canon.term(a, d), d), _} : Bk.Term}
      {==}
    case Bk.Term.All{q, A, B}:
      %C.canon.idem(A, d) : {Bk.Term.All{q, C.Canon.term(C.Canon.term(A, d), d), C.Canon.term(C.Canon.term(B, 1n+d), 1n+d)} == Bk.Term.All{q, _, C.Canon.term(B, 1n+d)} : Bk.Term}
      %C.canon.idem(B, 1n+d) : {Bk.Term.All{q, C.Canon.term(C.Canon.term(A, d), d), C.Canon.term(C.Canon.term(B, 1n+d), 1n+d)} == Bk.Term.All{q, C.Canon.term(C.Canon.term(A, d), d), _} : Bk.Term}
      {==}
    case Bk.Term.Lam{q, f}:
      %C.canon.idem(f, 1n+d) : {Bk.Term.Lam{q, C.Canon.term(C.Canon.term(f, 1n+d), 1n+d)} == Bk.Term.Lam{q, _} : Bk.Term}
      {==}
    case Bk.Term.App{q, f, x}:
      %C.canon.idem(f, d) : {Bk.Term.App{q, C.Canon.term(C.Canon.term(f, d), d), C.Canon.term(C.Canon.term(x, d), d)} == Bk.Term.App{q, _, C.Canon.term(x, d)} : Bk.Term}
      %C.canon.idem(x, d) : {Bk.Term.App{q, C.Canon.term(C.Canon.term(f, d), d), C.Canon.term(C.Canon.term(x, d), d)} == Bk.Term.App{q, C.Canon.term(C.Canon.term(f, d), d), _} : Bk.Term}
      {==}
    case Bk.Term.Sig{q, A, B}:
      %C.canon.idem(A, d) : {Bk.Term.Sig{q, C.Canon.term(C.Canon.term(A, d), d), C.Canon.term(C.Canon.term(B, 1n+d), 1n+d)} == Bk.Term.Sig{q, _, C.Canon.term(B, 1n+d)} : Bk.Term}
      %C.canon.idem(B, 1n+d) : {Bk.Term.Sig{q, C.Canon.term(C.Canon.term(A, d), d), C.Canon.term(C.Canon.term(B, 1n+d), 1n+d)} == Bk.Term.Sig{q, C.Canon.term(C.Canon.term(A, d), d), _} : Bk.Term}
      {==}
    case Bk.Term.Tup{q, a, b}:
      %C.canon.idem(a, d) : {Bk.Term.Tup{q, C.Canon.term(C.Canon.term(a, d), d), C.Canon.term(C.Canon.term(b, d), d)} == Bk.Term.Tup{q, _, C.Canon.term(b, d)} : Bk.Term}
      %C.canon.idem(b, d) : {Bk.Term.Tup{q, C.Canon.term(C.Canon.term(a, d), d), C.Canon.term(C.Canon.term(b, d), d)} == Bk.Term.Tup{q, C.Canon.term(C.Canon.term(a, d), d), _} : Bk.Term}
      {==}
    case Bk.Term.Prj{h}:
      %C.canon.idem(h, d) : {Bk.Term.Prj{C.Canon.term(C.Canon.term(h, d), d)} == Bk.Term.Prj{_} : Bk.Term}
      {==}
    case Bk.Term.Enu{ks}:
      {==}
    case Bk.Term.Lab{k}:
      {==}
    case Bk.Term.Mat{k, h, m}:
      %C.canon.idem(h, d) : {Bk.Term.Mat{k, C.Canon.term(C.Canon.term(h, d), d), C.Canon.term(C.Canon.term(m, d), d)} == Bk.Term.Mat{k, _, C.Canon.term(m, d)} : Bk.Term}
      %C.canon.idem(m, d) : {Bk.Term.Mat{k, C.Canon.term(C.Canon.term(h, d), d), C.Canon.term(C.Canon.term(m, d), d)} == Bk.Term.Mat{k, C.Canon.term(C.Canon.term(h, d), d), _} : Bk.Term}
      {==}
    case Bk.Term.Efq{}:
      {==}
    case Bk.Term.Eql{a, b, T}:
      %C.canon.idem(a, d) : {Bk.Term.Eql{C.Canon.term(C.Canon.term(a, d), d), C.Canon.term(C.Canon.term(b, d), d), C.Canon.term(C.Canon.term(T, d), d)} == Bk.Term.Eql{_, C.Canon.term(b, d), C.Canon.term(T, d)} : Bk.Term}
      %C.canon.idem(b, d) : {Bk.Term.Eql{C.Canon.term(C.Canon.term(a, d), d), C.Canon.term(C.Canon.term(b, d), d), C.Canon.term(C.Canon.term(T, d), d)} == Bk.Term.Eql{C.Canon.term(C.Canon.term(a, d), d), _, C.Canon.term(T, d)} : Bk.Term}
      %C.canon.idem(T, d) : {Bk.Term.Eql{C.Canon.term(C.Canon.term(a, d), d), C.Canon.term(C.Canon.term(b, d), d), C.Canon.term(C.Canon.term(T, d), d)} == Bk.Term.Eql{C.Canon.term(C.Canon.term(a, d), d), C.Canon.term(C.Canon.term(b, d), d), _} : Bk.Term}
      {==}
    case Bk.Term.Rfl{}:
      {==}
    case Bk.Term.Rwt{e, P, f}:
      %C.canon.idem(e, d) : {Bk.Term.Rwt{C.Canon.term(C.Canon.term(e, d), d), C.Canon.term(C.Canon.term(P, 2n+d), 2n+d), C.Canon.term(C.Canon.term(f, d), d)} == Bk.Term.Rwt{_, C.Canon.term(P, 2n+d), C.Canon.term(f, d)} : Bk.Term}
      %C.canon.idem(P, 2n+d) : {Bk.Term.Rwt{C.Canon.term(C.Canon.term(e, d), d), C.Canon.term(C.Canon.term(P, 2n+d), 2n+d), C.Canon.term(C.Canon.term(f, d), d)} == Bk.Term.Rwt{C.Canon.term(C.Canon.term(e, d), d), _, C.Canon.term(f, d)} : Bk.Term}
      %C.canon.idem(f, d) : {Bk.Term.Rwt{C.Canon.term(C.Canon.term(e, d), d), C.Canon.term(C.Canon.term(P, 2n+d), 2n+d), C.Canon.term(C.Canon.term(f, d), d)} == Bk.Term.Rwt{C.Canon.term(C.Canon.term(e, d), d), C.Canon.term(C.Canon.term(P, 2n+d), 2n+d), _} : Bk.Term}
      {==}

def C.canon.start(i):
  ?TODO

def C.canon.subst(t, es, d):
  ?TODO

def C.canon.subst_below(t, es, n, d, hc, hn):
  ?TODO

def C.canon.subst_closed(t, es, d, hc):
  ?TODO

def C.canon.lift(es, k, j, hc):
  ?TODO
