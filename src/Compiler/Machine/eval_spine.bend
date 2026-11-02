# compiler: layer B, a value's spine is short (U7)
# ================================================
#
# A walk that waits for more arguments had fewer arguments than its case
# tree has nodes (walk.waits): each round goes one node down the tree and
# takes at most one argument, and the wait comes at a node that takes one.
# So a value's spine, whose call waits, has at most Defs.big(ds) arguments
# (spine.big); a spine of a def, one argument more, still fits (spine.call):
# the K.arg chain that a call builds. A def's body is at most Defs.big(ds)
# too (get.big): the rounds of the call's walk.

import Base
import ../../Shared/shared.bend as Sd
import ../../Book/impl.bend as Bk
import ../../Eval/impl.bend as El
import ../../Program/impl.bend as Pg
import ../need_big.bend as N
import ./definitions.bend as D

# Kit
# ---

def le.max.l(+a: Nat, +b: Nat) -> N.Le(a, Nat.max(a, b)):
  match a:
    case 0n:
      N.le_zero(b)
    case 1n+p:
      match b:
        case 0n:
          N.le_refl(1n+p)
        case 1n+q:
          le.max.l(p, q)

def le.max.r(+a: Nat, +b: Nat) -> N.Le(b, Nat.max(a, b)):
  match a:
    case 0n:
      N.le_refl(b)
    case 1n+p:
      match b:
        case 0n:
          N.le_zero(1n+p)
        case 1n+q:
          le.max.r(p, q)

def is.ref(t: Bk.Term) -> Bool:
  match t:
    case Bk.Term.Ref{_}:
      True{}
    case _:
      False{}

# a term that is no Ref is not Ref{k}
def ref.ne(-G: Type, +t: Bk.Term, -k: List<&2, Word(8n)>, e: {t == Bk.Term.Ref{k} : Bk.Term}, ht: {is.ref(t) == False{} : Bool}) -> G:
  D.bool.ft(G, Equal.trans(Bool, False{}, is.ref(t), True{}, Equal.sym(Bool, is.ref(t), False{}, ht),
    (%Equal.sym(Bk.Term, t, Bk.Term.Ref{k}, e) : {is.ref(_) == True{} : Bool}; {==})))

# the walk behind a test that passes, an App whose head takes an argument,
# a λ-match's pick, a def's lookup
def wt.if(b: Bool, -r: Maybe<Maybe<Bk.Term>>, h: {El.Eval.waits(El.Eval.walk.if(b, r)) == True{} : Bool}) ->
  {El.Eval.waits(r) == True{} : Bool}:
  match b:
    case True{}:
      h
    case False{}:
      D.bool.ft({El.Eval.waits(r) == True{} : Bool}, h)

def wt.app(b: Bool, -r: Maybe<Maybe<Bk.Term>>, -u: Bk.Term, h: {El.Eval.waits(El.Eval.walk.app(b, r, u)) == True{} : Bool}) ->
  {El.Eval.waits(r) == True{} : Bool}:
  match b:
    case True{}:
      h
    case False{}:
      D.bool.ft({El.Eval.waits(r) == True{} : Bool}, h)

def wt.pick(b: Bool, -r: Maybe<Maybe<Bk.Term>>, -s: Maybe<Maybe<Bk.Term>>, -G: Type,
  h: {El.Eval.waits(El.Eval.walk.pick(b, r, s)) == True{} : Bool},
  g1: {El.Eval.waits(r) == True{} : Bool} -> G, g2: {El.Eval.waits(s) == True{} : Bool} -> G) -> G:
  match b:
    case True{}:
      g1(h)
    case False{}:
      g2(h)

def wt.get(b: Bool, +n: List<&2, Word(8n)>, +t: Bk.Term, +v: Bk.Term, +o: Bool, -r: Maybe<Bk.Def>, +xs: List<&2, El.Arg>, -G: Type,
  h: {El.Eval.waits(El.Eval.callWalk.def(El.Book.get.if(b, Bk.Def{n, t, v, o}, r), xs)) == True{} : Bool},
  g1: {El.Eval.waits(El.Eval.walk(v, Nil{}, xs)) == True{} : Bool} -> G,
  g2: {El.Eval.waits(El.Eval.callWalk.def(r, xs)) == True{} : Bool} -> G) -> G:
  match b:
    case True{}:
      g1(h)
    case False{}:
      g2(h)

# A walk that waits is shorter than its tree
# ------------------------------------------

def walk.waits(t: Bk.Term, +e: List<&2, Bk.Term>, +xs: List<&2, El.Arg>,
  h: {El.Eval.waits(El.Eval.walk(t, e, xs)) == True{} : Bool}) ->
  N.Le(1n+List.length(&2, El.Arg, xs), Pg.Term.size(t)):
  match t:
    case Bk.Term.Var{+z0}:
      D.bool.ft(N.Le(1n+List.length(&2, El.Arg, xs), Pg.Term.size(Bk.Term.Var{z0})), h)
    case Bk.Term.Ref{+z0}:
      D.bool.ft(N.Le(1n+List.length(&2, El.Arg, xs), Pg.Term.size(Bk.Term.Ref{z0})), h)
    case Bk.Term.Ann{+z0, +z1}:
      D.bool.ft(N.Le(1n+List.length(&2, El.Arg, xs), Pg.Term.size(Bk.Term.Ann{z0, z1})), h)
    case Bk.Term.Let{+z0, +z1, +z2}:
      D.bool.ft(N.Le(1n+List.length(&2, El.Arg, xs), Pg.Term.size(Bk.Term.Let{z0, z1, z2})), h)
    case Bk.Term.Typ{+z0}:
      D.bool.ft(N.Le(1n+List.length(&2, El.Arg, xs), Pg.Term.size(Bk.Term.Typ{z0})), h)
    case Bk.Term.Min{+z0, +z1}:
      D.bool.ft(N.Le(1n+List.length(&2, El.Arg, xs), Pg.Term.size(Bk.Term.Min{z0, z1})), h)
    case Bk.Term.All{+z0, +z1, +z2}:
      D.bool.ft(N.Le(1n+List.length(&2, El.Arg, xs), Pg.Term.size(Bk.Term.All{z0, z1, z2})), h)
    case Bk.Term.Lam{+z0, +z1}:
      match xs:
        case Nil{}:
          N.le_zero(Pg.Term.size(z1))
        case Con{El.Arg{+q, +x}, +rest}:
          walk.waits(z1, Con{x, e}, rest, wt.if(El.Quan.binds(z0, q, x), El.Eval.walk(z1, Con{x, e}, rest), h))
    case Bk.Term.App{+z0, +z1, +z2}:
      match z2:
        case Bk.Term.Var{+y0}:
          +ih = walk.waits(z1, e, Con{El.Arg{z0, El.Env.sub(e, y0)}, xs},
            wt.app(El.Term.takes(El.Term.head(z1)), El.Eval.walk(z1, e, Con{El.Arg{z0, El.Env.sub(e, y0)}, xs}),
              El.Term.spine(xs, El.Term.subst(Bk.Term.App{z0, z1, Bk.Term.Var{y0}}, e, 0n)), h))
          N.le_trans(List.length(&2, El.Arg, xs), Pg.Term.size(z1), Nat.add(Pg.Term.size(z1), 1n),
            N.weaken(List.length(&2, El.Arg, xs), Pg.Term.size(z1), N.weaken(1n+List.length(&2, El.Arg, xs), Pg.Term.size(z1), ih)),
            N.le_add_r(Pg.Term.size(z1), 1n))
        case Bk.Term.Ref{+y0}:
          D.bool.ft(N.Le(1n+List.length(&2, El.Arg, xs), Pg.Term.size(Bk.Term.App{z0, z1, Bk.Term.Ref{y0}})), h)
        case Bk.Term.Ann{+y0, +y1}:
          D.bool.ft(N.Le(1n+List.length(&2, El.Arg, xs), Pg.Term.size(Bk.Term.App{z0, z1, Bk.Term.Ann{y0, y1}})), h)
        case Bk.Term.Let{+y0, +y1, +y2}:
          D.bool.ft(N.Le(1n+List.length(&2, El.Arg, xs), Pg.Term.size(Bk.Term.App{z0, z1, Bk.Term.Let{y0, y1, y2}})), h)
        case Bk.Term.Typ{+y0}:
          D.bool.ft(N.Le(1n+List.length(&2, El.Arg, xs), Pg.Term.size(Bk.Term.App{z0, z1, Bk.Term.Typ{y0}})), h)
        case Bk.Term.Min{+y0, +y1}:
          D.bool.ft(N.Le(1n+List.length(&2, El.Arg, xs), Pg.Term.size(Bk.Term.App{z0, z1, Bk.Term.Min{y0, y1}})), h)
        case Bk.Term.All{+y0, +y1, +y2}:
          D.bool.ft(N.Le(1n+List.length(&2, El.Arg, xs), Pg.Term.size(Bk.Term.App{z0, z1, Bk.Term.All{y0, y1, y2}})), h)
        case Bk.Term.Lam{+y0, +y1}:
          D.bool.ft(N.Le(1n+List.length(&2, El.Arg, xs), Pg.Term.size(Bk.Term.App{z0, z1, Bk.Term.Lam{y0, y1}})), h)
        case Bk.Term.App{+y0, +y1, +y2}:
          D.bool.ft(N.Le(1n+List.length(&2, El.Arg, xs), Pg.Term.size(Bk.Term.App{z0, z1, Bk.Term.App{y0, y1, y2}})), h)
        case Bk.Term.Sig{+y0, +y1, +y2}:
          D.bool.ft(N.Le(1n+List.length(&2, El.Arg, xs), Pg.Term.size(Bk.Term.App{z0, z1, Bk.Term.Sig{y0, y1, y2}})), h)
        case Bk.Term.Tup{+y0, +y1, +y2}:
          D.bool.ft(N.Le(1n+List.length(&2, El.Arg, xs), Pg.Term.size(Bk.Term.App{z0, z1, Bk.Term.Tup{y0, y1, y2}})), h)
        case Bk.Term.Prj{+y0}:
          D.bool.ft(N.Le(1n+List.length(&2, El.Arg, xs), Pg.Term.size(Bk.Term.App{z0, z1, Bk.Term.Prj{y0}})), h)
        case Bk.Term.Enu{+y0}:
          D.bool.ft(N.Le(1n+List.length(&2, El.Arg, xs), Pg.Term.size(Bk.Term.App{z0, z1, Bk.Term.Enu{y0}})), h)
        case Bk.Term.Lab{+y0}:
          D.bool.ft(N.Le(1n+List.length(&2, El.Arg, xs), Pg.Term.size(Bk.Term.App{z0, z1, Bk.Term.Lab{y0}})), h)
        case Bk.Term.Mat{+y0, +y1, +y2}:
          D.bool.ft(N.Le(1n+List.length(&2, El.Arg, xs), Pg.Term.size(Bk.Term.App{z0, z1, Bk.Term.Mat{y0, y1, y2}})), h)
        case Bk.Term.Efq{}:
          D.bool.ft(N.Le(1n+List.length(&2, El.Arg, xs), Pg.Term.size(Bk.Term.App{z0, z1, Bk.Term.Efq{}})), h)
        case Bk.Term.Eql{+y0, +y1, +y2}:
          D.bool.ft(N.Le(1n+List.length(&2, El.Arg, xs), Pg.Term.size(Bk.Term.App{z0, z1, Bk.Term.Eql{y0, y1, y2}})), h)
        case Bk.Term.Rfl{}:
          D.bool.ft(N.Le(1n+List.length(&2, El.Arg, xs), Pg.Term.size(Bk.Term.App{z0, z1, Bk.Term.Rfl{}})), h)
        case Bk.Term.Rwt{+y0, +y1, +y2}:
          D.bool.ft(N.Le(1n+List.length(&2, El.Arg, xs), Pg.Term.size(Bk.Term.App{z0, z1, Bk.Term.Rwt{y0, y1, y2}})), h)
    case Bk.Term.Sig{+z0, +z1, +z2}:
      D.bool.ft(N.Le(1n+List.length(&2, El.Arg, xs), Pg.Term.size(Bk.Term.Sig{z0, z1, z2})), h)
    case Bk.Term.Tup{+z0, +z1, +z2}:
      D.bool.ft(N.Le(1n+List.length(&2, El.Arg, xs), Pg.Term.size(Bk.Term.Tup{z0, z1, z2})), h)
    case Bk.Term.Prj{+z0}:
      match xs:
        case Nil{}:
          N.le_zero(Pg.Term.size(z0))
        case Con{El.Arg{+q, +x}, +rest}:
          match x:
            case Bk.Term.Tup{+y0, +y1, +y2}:
              +ih = walk.waits(z0, e, Con{El.Arg{El.Quan.fld(y0, q), y1}, Con{El.Arg{q, y2}, rest}},
                wt.if(El.Quan.live(q), El.Eval.walk(z0, e, Con{El.Arg{El.Quan.fld(y0, q), y1}, Con{El.Arg{q, y2}, rest}}), h))
              N.weaken(1n+List.length(&2, El.Arg, rest), Pg.Term.size(z0), N.weaken(2n+List.length(&2, El.Arg, rest), Pg.Term.size(z0), ih))
            case Bk.Term.Var{+y0}:
              D.bool.ft(N.Le(1n+List.length(&2, El.Arg, Con{El.Arg{q, Bk.Term.Var{y0}}, rest}), Pg.Term.size(Bk.Term.Prj{z0})), h)
            case Bk.Term.Ref{+y0}:
              D.bool.ft(N.Le(1n+List.length(&2, El.Arg, Con{El.Arg{q, Bk.Term.Ref{y0}}, rest}), Pg.Term.size(Bk.Term.Prj{z0})), h)
            case Bk.Term.Ann{+y0, +y1}:
              D.bool.ft(N.Le(1n+List.length(&2, El.Arg, Con{El.Arg{q, Bk.Term.Ann{y0, y1}}, rest}), Pg.Term.size(Bk.Term.Prj{z0})), h)
            case Bk.Term.Let{+y0, +y1, +y2}:
              D.bool.ft(N.Le(1n+List.length(&2, El.Arg, Con{El.Arg{q, Bk.Term.Let{y0, y1, y2}}, rest}), Pg.Term.size(Bk.Term.Prj{z0})), h)
            case Bk.Term.Typ{+y0}:
              D.bool.ft(N.Le(1n+List.length(&2, El.Arg, Con{El.Arg{q, Bk.Term.Typ{y0}}, rest}), Pg.Term.size(Bk.Term.Prj{z0})), h)
            case Bk.Term.Min{+y0, +y1}:
              D.bool.ft(N.Le(1n+List.length(&2, El.Arg, Con{El.Arg{q, Bk.Term.Min{y0, y1}}, rest}), Pg.Term.size(Bk.Term.Prj{z0})), h)
            case Bk.Term.All{+y0, +y1, +y2}:
              D.bool.ft(N.Le(1n+List.length(&2, El.Arg, Con{El.Arg{q, Bk.Term.All{y0, y1, y2}}, rest}), Pg.Term.size(Bk.Term.Prj{z0})), h)
            case Bk.Term.Lam{+y0, +y1}:
              D.bool.ft(N.Le(1n+List.length(&2, El.Arg, Con{El.Arg{q, Bk.Term.Lam{y0, y1}}, rest}), Pg.Term.size(Bk.Term.Prj{z0})), h)
            case Bk.Term.App{+y0, +y1, +y2}:
              D.bool.ft(N.Le(1n+List.length(&2, El.Arg, Con{El.Arg{q, Bk.Term.App{y0, y1, y2}}, rest}), Pg.Term.size(Bk.Term.Prj{z0})), h)
            case Bk.Term.Sig{+y0, +y1, +y2}:
              D.bool.ft(N.Le(1n+List.length(&2, El.Arg, Con{El.Arg{q, Bk.Term.Sig{y0, y1, y2}}, rest}), Pg.Term.size(Bk.Term.Prj{z0})), h)
            case Bk.Term.Prj{+y0}:
              D.bool.ft(N.Le(1n+List.length(&2, El.Arg, Con{El.Arg{q, Bk.Term.Prj{y0}}, rest}), Pg.Term.size(Bk.Term.Prj{z0})), h)
            case Bk.Term.Enu{+y0}:
              D.bool.ft(N.Le(1n+List.length(&2, El.Arg, Con{El.Arg{q, Bk.Term.Enu{y0}}, rest}), Pg.Term.size(Bk.Term.Prj{z0})), h)
            case Bk.Term.Lab{+y0}:
              D.bool.ft(N.Le(1n+List.length(&2, El.Arg, Con{El.Arg{q, Bk.Term.Lab{y0}}, rest}), Pg.Term.size(Bk.Term.Prj{z0})), h)
            case Bk.Term.Mat{+y0, +y1, +y2}:
              D.bool.ft(N.Le(1n+List.length(&2, El.Arg, Con{El.Arg{q, Bk.Term.Mat{y0, y1, y2}}, rest}), Pg.Term.size(Bk.Term.Prj{z0})), h)
            case Bk.Term.Efq{}:
              D.bool.ft(N.Le(1n+List.length(&2, El.Arg, Con{El.Arg{q, Bk.Term.Efq{}}, rest}), Pg.Term.size(Bk.Term.Prj{z0})), h)
            case Bk.Term.Eql{+y0, +y1, +y2}:
              D.bool.ft(N.Le(1n+List.length(&2, El.Arg, Con{El.Arg{q, Bk.Term.Eql{y0, y1, y2}}, rest}), Pg.Term.size(Bk.Term.Prj{z0})), h)
            case Bk.Term.Rfl{}:
              D.bool.ft(N.Le(1n+List.length(&2, El.Arg, Con{El.Arg{q, Bk.Term.Rfl{}}, rest}), Pg.Term.size(Bk.Term.Prj{z0})), h)
            case Bk.Term.Rwt{+y0, +y1, +y2}:
              D.bool.ft(N.Le(1n+List.length(&2, El.Arg, Con{El.Arg{q, Bk.Term.Rwt{y0, y1, y2}}, rest}), Pg.Term.size(Bk.Term.Prj{z0})), h)
    case Bk.Term.Enu{+z0}:
      D.bool.ft(N.Le(1n+List.length(&2, El.Arg, xs), Pg.Term.size(Bk.Term.Enu{z0})), h)
    case Bk.Term.Lab{+z0}:
      D.bool.ft(N.Le(1n+List.length(&2, El.Arg, xs), Pg.Term.size(Bk.Term.Lab{z0})), h)
    case Bk.Term.Mat{+z0, +z1, +z2}:
      match xs:
        case Nil{}:
          N.le_zero(Nat.add(Pg.Term.size(z1), Pg.Term.size(z2)))
        case Con{El.Arg{+q, +x}, +rest}:
          match x:
            case Bk.Term.Lab{+y0}:
              wt.pick(Sd.Name.is_eq(y0, z0), El.Eval.walk(z1, e, rest), El.Eval.walk(z2, e, Con{El.Arg{q, Bk.Term.Lab{y0}}, rest}),
                N.Le(1n+List.length(&2, El.Arg, Con{El.Arg{q, Bk.Term.Lab{y0}}, rest}), Pg.Term.size(Bk.Term.Mat{z0, z1, z2})),
                wt.if(El.Quan.live(q), El.Eval.walk.pick(Sd.Name.is_eq(y0, z0), El.Eval.walk(z1, e, rest), El.Eval.walk(z2, e, Con{El.Arg{q, Bk.Term.Lab{y0}}, rest})), h),
                a1 => N.le_trans(1n+List.length(&2, El.Arg, rest), Pg.Term.size(z1), Nat.add(Pg.Term.size(z1), Pg.Term.size(z2)),
                  walk.waits(z1, e, rest, a1), N.le_add_r(Pg.Term.size(z1), Pg.Term.size(z2))),
                a2 => N.le_trans(1n+List.length(&2, El.Arg, rest), Pg.Term.size(z2), Nat.add(Pg.Term.size(z1), Pg.Term.size(z2)),
                  N.weaken(1n+List.length(&2, El.Arg, rest), Pg.Term.size(z2), walk.waits(z2, e, Con{El.Arg{q, Bk.Term.Lab{y0}}, rest}, a2)),
                  N.le_add_l(Pg.Term.size(z1), Pg.Term.size(z2))))
            case Bk.Term.Var{+y0}:
              D.bool.ft(N.Le(1n+List.length(&2, El.Arg, Con{El.Arg{q, Bk.Term.Var{y0}}, rest}), Pg.Term.size(Bk.Term.Mat{z0, z1, z2})), h)
            case Bk.Term.Ref{+y0}:
              D.bool.ft(N.Le(1n+List.length(&2, El.Arg, Con{El.Arg{q, Bk.Term.Ref{y0}}, rest}), Pg.Term.size(Bk.Term.Mat{z0, z1, z2})), h)
            case Bk.Term.Ann{+y0, +y1}:
              D.bool.ft(N.Le(1n+List.length(&2, El.Arg, Con{El.Arg{q, Bk.Term.Ann{y0, y1}}, rest}), Pg.Term.size(Bk.Term.Mat{z0, z1, z2})), h)
            case Bk.Term.Let{+y0, +y1, +y2}:
              D.bool.ft(N.Le(1n+List.length(&2, El.Arg, Con{El.Arg{q, Bk.Term.Let{y0, y1, y2}}, rest}), Pg.Term.size(Bk.Term.Mat{z0, z1, z2})), h)
            case Bk.Term.Typ{+y0}:
              D.bool.ft(N.Le(1n+List.length(&2, El.Arg, Con{El.Arg{q, Bk.Term.Typ{y0}}, rest}), Pg.Term.size(Bk.Term.Mat{z0, z1, z2})), h)
            case Bk.Term.Min{+y0, +y1}:
              D.bool.ft(N.Le(1n+List.length(&2, El.Arg, Con{El.Arg{q, Bk.Term.Min{y0, y1}}, rest}), Pg.Term.size(Bk.Term.Mat{z0, z1, z2})), h)
            case Bk.Term.All{+y0, +y1, +y2}:
              D.bool.ft(N.Le(1n+List.length(&2, El.Arg, Con{El.Arg{q, Bk.Term.All{y0, y1, y2}}, rest}), Pg.Term.size(Bk.Term.Mat{z0, z1, z2})), h)
            case Bk.Term.Lam{+y0, +y1}:
              D.bool.ft(N.Le(1n+List.length(&2, El.Arg, Con{El.Arg{q, Bk.Term.Lam{y0, y1}}, rest}), Pg.Term.size(Bk.Term.Mat{z0, z1, z2})), h)
            case Bk.Term.App{+y0, +y1, +y2}:
              D.bool.ft(N.Le(1n+List.length(&2, El.Arg, Con{El.Arg{q, Bk.Term.App{y0, y1, y2}}, rest}), Pg.Term.size(Bk.Term.Mat{z0, z1, z2})), h)
            case Bk.Term.Sig{+y0, +y1, +y2}:
              D.bool.ft(N.Le(1n+List.length(&2, El.Arg, Con{El.Arg{q, Bk.Term.Sig{y0, y1, y2}}, rest}), Pg.Term.size(Bk.Term.Mat{z0, z1, z2})), h)
            case Bk.Term.Tup{+y0, +y1, +y2}:
              D.bool.ft(N.Le(1n+List.length(&2, El.Arg, Con{El.Arg{q, Bk.Term.Tup{y0, y1, y2}}, rest}), Pg.Term.size(Bk.Term.Mat{z0, z1, z2})), h)
            case Bk.Term.Prj{+y0}:
              D.bool.ft(N.Le(1n+List.length(&2, El.Arg, Con{El.Arg{q, Bk.Term.Prj{y0}}, rest}), Pg.Term.size(Bk.Term.Mat{z0, z1, z2})), h)
            case Bk.Term.Enu{+y0}:
              D.bool.ft(N.Le(1n+List.length(&2, El.Arg, Con{El.Arg{q, Bk.Term.Enu{y0}}, rest}), Pg.Term.size(Bk.Term.Mat{z0, z1, z2})), h)
            case Bk.Term.Mat{+y0, +y1, +y2}:
              D.bool.ft(N.Le(1n+List.length(&2, El.Arg, Con{El.Arg{q, Bk.Term.Mat{y0, y1, y2}}, rest}), Pg.Term.size(Bk.Term.Mat{z0, z1, z2})), h)
            case Bk.Term.Efq{}:
              D.bool.ft(N.Le(1n+List.length(&2, El.Arg, Con{El.Arg{q, Bk.Term.Efq{}}, rest}), Pg.Term.size(Bk.Term.Mat{z0, z1, z2})), h)
            case Bk.Term.Eql{+y0, +y1, +y2}:
              D.bool.ft(N.Le(1n+List.length(&2, El.Arg, Con{El.Arg{q, Bk.Term.Eql{y0, y1, y2}}, rest}), Pg.Term.size(Bk.Term.Mat{z0, z1, z2})), h)
            case Bk.Term.Rfl{}:
              D.bool.ft(N.Le(1n+List.length(&2, El.Arg, Con{El.Arg{q, Bk.Term.Rfl{}}, rest}), Pg.Term.size(Bk.Term.Mat{z0, z1, z2})), h)
            case Bk.Term.Rwt{+y0, +y1, +y2}:
              D.bool.ft(N.Le(1n+List.length(&2, El.Arg, Con{El.Arg{q, Bk.Term.Rwt{y0, y1, y2}}, rest}), Pg.Term.size(Bk.Term.Mat{z0, z1, z2})), h)
    case Bk.Term.Efq{}:
      match xs:
        case Nil{}:
          N.le_zero(0n)
        case Con{+x, +rest}:
          D.bool.ft(N.Le(1n+List.length(&2, El.Arg, Con{x, rest}), Pg.Term.size(Bk.Term.Efq{})), h)
    case Bk.Term.Eql{+z0, +z1, +z2}:
      D.bool.ft(N.Le(1n+List.length(&2, El.Arg, xs), Pg.Term.size(Bk.Term.Eql{z0, z1, z2})), h)
    case Bk.Term.Rfl{}:
      D.bool.ft(N.Le(1n+List.length(&2, El.Arg, xs), Pg.Term.size(Bk.Term.Rfl{})), h)
    case Bk.Term.Rwt{+z0, +z1, +z2}:
      D.bool.ft(N.Le(1n+List.length(&2, El.Arg, xs), Pg.Term.size(Bk.Term.Rwt{z0, z1, z2})), h)

# A call's walk
# -------------

# the walk of the first def of the name k, when it waits
def get.walk(ds: List<&2, Bk.Def>, +k: List<&2, Word(8n)>, +xs: List<&2, El.Arg>,
  h: {El.Eval.waits(El.Eval.callWalk.def(El.Book.get(ds, k), xs)) == True{} : Bool}) ->
  N.Le(1n+List.length(&2, El.Arg, xs), D.Defs.big(ds)):
  match ds:
    case Nil{}:
      D.bool.ft(N.Le(1n+List.length(&2, El.Arg, xs), D.Defs.big(Nil{})), h)
    case Con{Bk.Def{+n, +t, +v, +o}, +rest}:
      wt.get(Sd.Name.is_eq(n, k), n, t, v, o, El.Book.get(rest, k), xs,
        N.Le(1n+List.length(&2, El.Arg, xs), D.Defs.big(Con{Bk.Def{n, t, v, o}, rest})), h,
        a1 => N.le_trans(1n+List.length(&2, El.Arg, xs), Pg.Term.size(v), D.Defs.big(Con{Bk.Def{n, t, v, o}, rest}),
          walk.waits(v, Nil{}, xs, a1), le.max.l(Pg.Term.size(v), D.Defs.big(rest))),
        a2 => N.le_trans(1n+List.length(&2, El.Arg, xs), D.Defs.big(rest), D.Defs.big(Con{Bk.Def{n, t, v, o}, rest}),
          get.walk(rest, k, xs, a2), le.max.r(Pg.Term.size(v), D.Defs.big(rest))))

# the walk from the head of a spine, when it waits: the head is a Ref
def call.head(+ds: List<&2, Bk.Def>, hd: Bk.Term, +xs: List<&2, El.Arg>,
  h: {El.Eval.waits(El.Eval.callWalk.head(ds, hd, xs)) == True{} : Bool}) ->
  N.Le(1n+List.length(&2, El.Arg, xs), D.Defs.big(ds)):
  match hd:
    case Bk.Term.Ref{+z0}:
      get.walk(ds, z0, xs, h)
    case Bk.Term.Var{+z0}:
      D.bool.ft(N.Le(1n+List.length(&2, El.Arg, xs), D.Defs.big(ds)), h)
    case Bk.Term.Ann{+z0, +z1}:
      D.bool.ft(N.Le(1n+List.length(&2, El.Arg, xs), D.Defs.big(ds)), h)
    case Bk.Term.Let{+z0, +z1, +z2}:
      D.bool.ft(N.Le(1n+List.length(&2, El.Arg, xs), D.Defs.big(ds)), h)
    case Bk.Term.Typ{+z0}:
      D.bool.ft(N.Le(1n+List.length(&2, El.Arg, xs), D.Defs.big(ds)), h)
    case Bk.Term.Min{+z0, +z1}:
      D.bool.ft(N.Le(1n+List.length(&2, El.Arg, xs), D.Defs.big(ds)), h)
    case Bk.Term.All{+z0, +z1, +z2}:
      D.bool.ft(N.Le(1n+List.length(&2, El.Arg, xs), D.Defs.big(ds)), h)
    case Bk.Term.Lam{+z0, +z1}:
      D.bool.ft(N.Le(1n+List.length(&2, El.Arg, xs), D.Defs.big(ds)), h)
    case Bk.Term.App{+z0, +z1, +z2}:
      D.bool.ft(N.Le(1n+List.length(&2, El.Arg, xs), D.Defs.big(ds)), h)
    case Bk.Term.Sig{+z0, +z1, +z2}:
      D.bool.ft(N.Le(1n+List.length(&2, El.Arg, xs), D.Defs.big(ds)), h)
    case Bk.Term.Tup{+z0, +z1, +z2}:
      D.bool.ft(N.Le(1n+List.length(&2, El.Arg, xs), D.Defs.big(ds)), h)
    case Bk.Term.Prj{+z0}:
      D.bool.ft(N.Le(1n+List.length(&2, El.Arg, xs), D.Defs.big(ds)), h)
    case Bk.Term.Enu{+z0}:
      D.bool.ft(N.Le(1n+List.length(&2, El.Arg, xs), D.Defs.big(ds)), h)
    case Bk.Term.Lab{+z0}:
      D.bool.ft(N.Le(1n+List.length(&2, El.Arg, xs), D.Defs.big(ds)), h)
    case Bk.Term.Mat{+z0, +z1, +z2}:
      D.bool.ft(N.Le(1n+List.length(&2, El.Arg, xs), D.Defs.big(ds)), h)
    case Bk.Term.Efq{}:
      D.bool.ft(N.Le(1n+List.length(&2, El.Arg, xs), D.Defs.big(ds)), h)
    case Bk.Term.Eql{+z0, +z1, +z2}:
      D.bool.ft(N.Le(1n+List.length(&2, El.Arg, xs), D.Defs.big(ds)), h)
    case Bk.Term.Rfl{}:
      D.bool.ft(N.Le(1n+List.length(&2, El.Arg, xs), D.Defs.big(ds)), h)
    case Bk.Term.Rwt{+z0, +z1, +z2}:
      D.bool.ft(N.Le(1n+List.length(&2, El.Arg, xs), D.Defs.big(ds)), h)

# a call whose walk waits has fewer arguments than Defs.big(ds)
def call.waits(+ds: List<&2, Bk.Def>, +f: Bk.Term, h: {El.Eval.waits(El.Eval.callWalk(ds, f)) == True{} : Bool}) ->
  N.Le(1n+List.length(&2, El.Arg, El.Term.args(f, Nil{})), D.Defs.big(ds)):
  call.head(ds, El.Term.head(f), El.Term.args(f, Nil{}), h)

# Values
# ------

# a value's spine has at most Defs.big(ds) arguments: an App is a value
# only when its call waits
def spine.big(+ds: List<&2, Bk.Def>, v: Bk.Term, h: {El.Eval.vals(ds, v, False{}) == True{} : Bool}) ->
  N.Le(List.length(&2, El.Arg, El.Term.args(v, Nil{})), D.Defs.big(ds)):
  match v:
    case Bk.Term.App{+z0, +z1, +z2}:
      N.weaken(List.length(&2, El.Arg, El.Term.args(Bk.Term.App{z0, z1, z2}, Nil{})), D.Defs.big(ds),
        call.waits(ds, Bk.Term.App{z0, z1, z2},
          D.and.r(Bool.and(El.Eval.vals(ds, z1, True{}), Bool.or(Bool.not(El.Quan.live(z0)), El.Eval.vals(ds, z2, False{}))),
            El.Eval.waits(El.Eval.callWalk(ds, Bk.Term.App{z0, z1, z2})), h)))
    case Bk.Term.Var{+z0}:
      N.le_zero(D.Defs.big(ds))
    case Bk.Term.Ref{+z0}:
      N.le_zero(D.Defs.big(ds))
    case Bk.Term.Ann{+z0, +z1}:
      N.le_zero(D.Defs.big(ds))
    case Bk.Term.Let{+z0, +z1, +z2}:
      N.le_zero(D.Defs.big(ds))
    case Bk.Term.Typ{+z0}:
      N.le_zero(D.Defs.big(ds))
    case Bk.Term.Min{+z0, +z1}:
      N.le_zero(D.Defs.big(ds))
    case Bk.Term.All{+z0, +z1, +z2}:
      N.le_zero(D.Defs.big(ds))
    case Bk.Term.Lam{+z0, +z1}:
      N.le_zero(D.Defs.big(ds))
    case Bk.Term.Sig{+z0, +z1, +z2}:
      N.le_zero(D.Defs.big(ds))
    case Bk.Term.Tup{+z0, +z1, +z2}:
      N.le_zero(D.Defs.big(ds))
    case Bk.Term.Prj{+z0}:
      N.le_zero(D.Defs.big(ds))
    case Bk.Term.Enu{+z0}:
      N.le_zero(D.Defs.big(ds))
    case Bk.Term.Lab{+z0}:
      N.le_zero(D.Defs.big(ds))
    case Bk.Term.Mat{+z0, +z1, +z2}:
      N.le_zero(D.Defs.big(ds))
    case Bk.Term.Efq{}:
      N.le_zero(D.Defs.big(ds))
    case Bk.Term.Eql{+z0, +z1, +z2}:
      N.le_zero(D.Defs.big(ds))
    case Bk.Term.Rfl{}:
      N.le_zero(D.Defs.big(ds))
    case Bk.Term.Rwt{+z0, +z1, +z2}:
      N.le_zero(D.Defs.big(ds))

# a value whose head is a Ref (a def's spine) has fewer arguments than
# Defs.big(ds): its call, with one argument more, fits
def spine.call(+ds: List<&2, Bk.Def>, v: Bk.Term, -k: List<&2, Word(8n)>, h: {El.Eval.vals(ds, v, False{}) == True{} : Bool},
  hh: {El.Term.head(v) == Bk.Term.Ref{k} : Bk.Term}) ->
  N.Le(1n+List.length(&2, El.Arg, El.Term.args(v, Nil{})), D.Defs.big(ds)):
  match v:
    case Bk.Term.App{+z0, +z1, +z2}:
      call.waits(ds, Bk.Term.App{z0, z1, z2},
        D.and.r(Bool.and(El.Eval.vals(ds, z1, True{}), Bool.or(Bool.not(El.Quan.live(z0)), El.Eval.vals(ds, z2, False{}))),
          El.Eval.waits(El.Eval.callWalk(ds, Bk.Term.App{z0, z1, z2})), h))
    case Bk.Term.Ref{+z0}:
      call.waits(ds, Bk.Term.Ref{z0}, h)
    case Bk.Term.Var{+z0}:
      ref.ne(N.Le(1n+List.length(&2, El.Arg, El.Term.args(Bk.Term.Var{z0}, Nil{})), D.Defs.big(ds)), Bk.Term.Var{z0}, k, hh, {==})
    case Bk.Term.Ann{+z0, +z1}:
      ref.ne(N.Le(1n+List.length(&2, El.Arg, El.Term.args(Bk.Term.Ann{z0, z1}, Nil{})), D.Defs.big(ds)), Bk.Term.Ann{z0, z1}, k, hh, {==})
    case Bk.Term.Let{+z0, +z1, +z2}:
      ref.ne(N.Le(1n+List.length(&2, El.Arg, El.Term.args(Bk.Term.Let{z0, z1, z2}, Nil{})), D.Defs.big(ds)), Bk.Term.Let{z0, z1, z2}, k, hh, {==})
    case Bk.Term.Typ{+z0}:
      ref.ne(N.Le(1n+List.length(&2, El.Arg, El.Term.args(Bk.Term.Typ{z0}, Nil{})), D.Defs.big(ds)), Bk.Term.Typ{z0}, k, hh, {==})
    case Bk.Term.Min{+z0, +z1}:
      ref.ne(N.Le(1n+List.length(&2, El.Arg, El.Term.args(Bk.Term.Min{z0, z1}, Nil{})), D.Defs.big(ds)), Bk.Term.Min{z0, z1}, k, hh, {==})
    case Bk.Term.All{+z0, +z1, +z2}:
      ref.ne(N.Le(1n+List.length(&2, El.Arg, El.Term.args(Bk.Term.All{z0, z1, z2}, Nil{})), D.Defs.big(ds)), Bk.Term.All{z0, z1, z2}, k, hh, {==})
    case Bk.Term.Lam{+z0, +z1}:
      ref.ne(N.Le(1n+List.length(&2, El.Arg, El.Term.args(Bk.Term.Lam{z0, z1}, Nil{})), D.Defs.big(ds)), Bk.Term.Lam{z0, z1}, k, hh, {==})
    case Bk.Term.Sig{+z0, +z1, +z2}:
      ref.ne(N.Le(1n+List.length(&2, El.Arg, El.Term.args(Bk.Term.Sig{z0, z1, z2}, Nil{})), D.Defs.big(ds)), Bk.Term.Sig{z0, z1, z2}, k, hh, {==})
    case Bk.Term.Tup{+z0, +z1, +z2}:
      ref.ne(N.Le(1n+List.length(&2, El.Arg, El.Term.args(Bk.Term.Tup{z0, z1, z2}, Nil{})), D.Defs.big(ds)), Bk.Term.Tup{z0, z1, z2}, k, hh, {==})
    case Bk.Term.Prj{+z0}:
      ref.ne(N.Le(1n+List.length(&2, El.Arg, El.Term.args(Bk.Term.Prj{z0}, Nil{})), D.Defs.big(ds)), Bk.Term.Prj{z0}, k, hh, {==})
    case Bk.Term.Enu{+z0}:
      ref.ne(N.Le(1n+List.length(&2, El.Arg, El.Term.args(Bk.Term.Enu{z0}, Nil{})), D.Defs.big(ds)), Bk.Term.Enu{z0}, k, hh, {==})
    case Bk.Term.Lab{+z0}:
      ref.ne(N.Le(1n+List.length(&2, El.Arg, El.Term.args(Bk.Term.Lab{z0}, Nil{})), D.Defs.big(ds)), Bk.Term.Lab{z0}, k, hh, {==})
    case Bk.Term.Mat{+z0, +z1, +z2}:
      ref.ne(N.Le(1n+List.length(&2, El.Arg, El.Term.args(Bk.Term.Mat{z0, z1, z2}, Nil{})), D.Defs.big(ds)), Bk.Term.Mat{z0, z1, z2}, k, hh, {==})
    case Bk.Term.Efq{}:
      ref.ne(N.Le(1n+List.length(&2, El.Arg, El.Term.args(Bk.Term.Efq{}, Nil{})), D.Defs.big(ds)), Bk.Term.Efq{}, k, hh, {==})
    case Bk.Term.Eql{+z0, +z1, +z2}:
      ref.ne(N.Le(1n+List.length(&2, El.Arg, El.Term.args(Bk.Term.Eql{z0, z1, z2}, Nil{})), D.Defs.big(ds)), Bk.Term.Eql{z0, z1, z2}, k, hh, {==})
    case Bk.Term.Rfl{}:
      ref.ne(N.Le(1n+List.length(&2, El.Arg, El.Term.args(Bk.Term.Rfl{}, Nil{})), D.Defs.big(ds)), Bk.Term.Rfl{}, k, hh, {==})
    case Bk.Term.Rwt{+z0, +z1, +z2}:
      ref.ne(N.Le(1n+List.length(&2, El.Arg, El.Term.args(Bk.Term.Rwt{z0, z1, z2}, Nil{})), D.Defs.big(ds)), Bk.Term.Rwt{z0, z1, z2}, k, hh, {==})

# Bodies
# ------

# the lookup of a def gives one, and its body
def got(r: Maybe<Bk.Def>) -> Bool:
  match r:
    case Some{_}:
      True{}
    case None{}:
      False{}

def got.body(r: Maybe<Bk.Def>) -> Bk.Term:
  match r:
    case Some{Bk.Def{_, _, v, _}}:
      v
    case None{}:
      Bk.Term.Efq{}

def gb.if(b: Bool, +n: List<&2, Word(8n)>, +t: Bk.Term, +v: Bk.Term, +o: Bool, -r: Maybe<Bk.Def>, -d: Bk.Def, +B: Nat,
  h: {El.Book.get.if(b, Bk.Def{n, t, v, o}, r) == Some{d} : Maybe<Bk.Def>},
  g2: {r == Some{d} : Maybe<Bk.Def>} -> N.Le(Pg.Term.size(got.body(Some{d})), Nat.max(Pg.Term.size(v), B))) ->
  N.Le(Pg.Term.size(got.body(Some{d})), Nat.max(Pg.Term.size(v), B)):
  match b:
    case True{}:
      (%h : N.Le(Pg.Term.size(got.body(_)), Nat.max(Pg.Term.size(v), B)); le.max.l(Pg.Term.size(v), B))
    case False{}:
      g2(h)

def get.big(ds: List<&2, Bk.Def>, +k: List<&2, Word(8n)>, +d: Bk.Def, h: {El.Book.get(ds, k) == Some{d} : Maybe<Bk.Def>}) ->
  N.Le(Pg.Term.size(got.body(Some{d})), D.Defs.big(ds)):
  match ds:
    case Nil{}:
      D.bool.ft(N.Le(Pg.Term.size(got.body(Some{d})), D.Defs.big(Nil{})),
        Equal.sym(Bool, True{}, False{}, (%h : {got(_) == False{} : Bool}; {==})))
    case Con{Bk.Def{+n, +t, +v, +o}, +rest}:
      gb.if(Sd.Name.is_eq(n, k), n, t, v, o, El.Book.get(rest, k), d, D.Defs.big(rest), h,
        e => N.le_trans(Pg.Term.size(got.body(Some{d})), D.Defs.big(rest), Nat.max(Pg.Term.size(v), D.Defs.big(rest)),
          get.big(rest, k, d, e), le.max.r(Pg.Term.size(v), D.Defs.big(rest))))

# the body of the first def of a name has at most Defs.big(ds) nodes
def body.big(ds: List<&2, Bk.Def>, +k: List<&2, Word(8n)>, +n: List<&2, Word(8n)>, +t: Bk.Term, +v: Bk.Term, +o: Bool,
  h: {El.Book.get(ds, k) == Some{Bk.Def{n, t, v, o}} : Maybe<Bk.Def>}) -> N.Le(Pg.Term.size(v), D.Defs.big(ds)):
  get.big(ds, k, Bk.Def{n, t, v, o}, h)
