import Base
import ../shared/shared.bend as Sd
import ../book/impl.bend as Bk

# Eval
# ====
#
# A version of the kernel's Eval: Eval.steps(n, ds, t) gives the term that t
# reaches after exactly n steps, in the book of the defs ds (AGENTS.md 3.4.2). It
# follows step of lean/src/Bootstrap/Shared/Interp.lean case for
# case, and works out each part that a case may need before it picks one.

# an argument of a spine, at its quantity
type Arg is Data:
  Arg{q: Bk.Quan, x: Bk.Term}

def Quan.live(q: Bk.Quan) -> Bool:
  match q:
    case Bk.Quan.Q0{}:
      False{}
    case Bk.Quan.Q1{}:
      True{}
    case Bk.Quan.Q2{}:
      True{}

# p and q are both live or both dead
def Quan.lives_as(p: Bk.Quan, q: Bk.Quan) -> Bool:
  match p q:
    case Bk.Quan.Q0{} Bk.Quan.Q0{}:
      True{}
    case Bk.Quan.Q0{} _:
      False{}
    case _ Bk.Quan.Q0{}:
      False{}
    case _ _:
      True{}

# the quantity of a pair's first field, when the pair is used at q
def Quan.fld(r: Bk.Quan, q: Bk.Quan) -> Bk.Quan:
  match r:
    case Bk.Quan.Q0{}:
      Bk.Quan.Q0{}
    case Bk.Quan.Q1{}:
      q
    case Bk.Quan.Q2{}:
      Bk.Quan.Q2{}

def Term.is_data(t: Bk.Term) -> Bool:
  match t:
    case Bk.Term.Lab{_}:
      True{}
    case Bk.Term.Rfl{}:
      True{}
    case Bk.Term.Tup{q, a, b}:
      (Bool.not(Quan.live(q)) || Term.is_data(a)) && Term.is_data(b)
    case _:
      False{}

# q may hold v: v is Data when q is 2
def Quan.fits(q: Bk.Quan, v: Bk.Term) -> Bool:
  match q:
    case Bk.Quan.Q2{}:
      Term.is_data(v)
    case _:
      True{}

# a λ of quantity p binds x at quantity q
def Quan.binds(+p: Bk.Quan, q: Bk.Quan, x: Bk.Term) -> Bool:
  Quan.lives_as(p, q) && Quan.fits(p, x)

# a former: a term that is a value by its form
def Term.is_former(t: Bk.Term) -> Bool:
  match t:
    case Bk.Term.Typ{_}:
      True{}
    case Bk.Term.All{_, _, _}:
      True{}
    case Bk.Term.Sig{_, _, _}:
      True{}
    case Bk.Term.Enu{_}:
      True{}
    case Bk.Term.Eql{_, _, _}:
      True{}
    case Bk.Term.Lam{_, _}:
      True{}
    case Bk.Term.Prj{_}:
      True{}
    case Bk.Term.Mat{_, _, _}:
      True{}
    case Bk.Term.Efq{}:
      True{}
    case Bk.Term.Tup{_, _, _}:
      True{}
    case Bk.Term.Lab{_}:
      True{}
    case Bk.Term.Rfl{}:
      True{}
    case _:
      False{}

# a λ or a λ-match: a node of a case tree, which takes an argument
def Term.takes(t: Bk.Term) -> Bool:
  match t:
    case Bk.Term.Lam{_, _}:
      True{}
    case Bk.Term.Prj{_}:
      True{}
    case Bk.Term.Mat{_, _, _}:
      True{}
    case Bk.Term.Efq{}:
      True{}
    case _:
      False{}

# the head of a spine
def Term.head(t: Bk.Term) -> Bk.Term:
  match t:
    case Bk.Term.App{_, f, _}:
      Term.head(f)
    case u:
      u

# the arguments of a spine, in front of xs
def Term.args(t: Bk.Term, xs: List<&2, Arg>) -> List<&2, Arg>:
  match t:
    case Bk.Term.App{q, f, x}:
      Term.args(f, Con{Arg{q, x}, xs})
    case _:
      xs

# t applied to xs
def Term.spine(xs: List<&2, Arg>, t: Bk.Term) -> Bk.Term:
  match xs:
    case Nil{}:
      t
    case Con{Arg{q, x}, rest}:
      Term.spine(rest, Bk.Term.App{q, t, x})

# the term of the variable i, in e
def Env.sub(e: List<&2, Bk.Term>, i: Nat) -> Bk.Term:
  match e i:
    case Nil{} j:
      Bk.Term.Var{j}
    case Con{x, _} 0n:
      x
    case Con{_, rest} 1n+j:
      Env.sub(rest, j)

def Term.shift.at(lt: Bool, i: Nat, d: Nat) -> Nat:
  match lt:
    case True{}:
      i
    case False{}:
      Nat.add(i, d)

# t with each variable from c on moved up by d
def Term.shift(t: Bk.Term, +d: Nat, +c: Nat) -> Bk.Term:
  match t:
    case Bk.Term.Var{+i}:
      Bk.Term.Var{Term.shift.at(Nat.is_lt(i, c), i, d)}
    case Bk.Term.Ref{k}:
      Bk.Term.Ref{k}
    case Bk.Term.Ann{x, T}:
      Bk.Term.Ann{Term.shift(x, d, c), Term.shift(T, d, c)}
    case Bk.Term.Let{q, v, f}:
      Bk.Term.Let{q, Term.shift(v, d, c), Term.shift(f, d, 1n+c)}
    case Bk.Term.Typ{q}:
      Bk.Term.Typ{Term.shift(q, d, c)}
    case Bk.Term.Min{a, b}:
      Bk.Term.Min{Term.shift(a, d, c), Term.shift(b, d, c)}
    case Bk.Term.All{q, A, B}:
      Bk.Term.All{q, Term.shift(A, d, c), Term.shift(B, d, 1n+c)}
    case Bk.Term.Lam{q, f}:
      Bk.Term.Lam{q, Term.shift(f, d, 1n+c)}
    case Bk.Term.App{q, f, x}:
      Bk.Term.App{q, Term.shift(f, d, c), Term.shift(x, d, c)}
    case Bk.Term.Sig{q, A, B}:
      Bk.Term.Sig{q, Term.shift(A, d, c), Term.shift(B, d, 1n+c)}
    case Bk.Term.Tup{q, a, b}:
      Bk.Term.Tup{q, Term.shift(a, d, c), Term.shift(b, d, c)}
    case Bk.Term.Prj{h}:
      Bk.Term.Prj{Term.shift(h, d, c)}
    case Bk.Term.Enu{ks}:
      Bk.Term.Enu{ks}
    case Bk.Term.Lab{k}:
      Bk.Term.Lab{k}
    case Bk.Term.Mat{k, h, m}:
      Bk.Term.Mat{k, Term.shift(h, d, c), Term.shift(m, d, c)}
    case Bk.Term.Efq{}:
      Bk.Term.Efq{}
    case Bk.Term.Eql{a, b, T}:
      Bk.Term.Eql{Term.shift(a, d, c), Term.shift(b, d, c), Term.shift(T, d, c)}
    case Bk.Term.Rfl{}:
      Bk.Term.Rfl{}
    case Bk.Term.Rwt{e, P, f}:
      Bk.Term.Rwt{Term.shift(e, d, c), Term.shift(P, d, 2n+c), Term.shift(f, d, c)}

def Term.lift.at(lt: Bool, i: Nat, v: Bk.Term) -> Bk.Term:
  match lt:
    case True{}:
      Bk.Term.Var{i}
    case False{}:
      v

# the variable i under d binders, with e put in for the free variables
def Term.lift(+e: List<&2, Bk.Term>, +d: Nat, +i: Nat) -> Bk.Term:
  match d:
    case 0n:
      Env.sub(e, i)
    case 1n+p:
      Term.lift.at(Nat.is_lt(i, 1n+p), i, Term.shift(Env.sub(e, Nat.sub(i, 1n+p)), 1n+p, 0n))

# t under d binders, with e put in for the free variables
def Term.subst(t: Bk.Term, +e: List<&2, Bk.Term>, +d: Nat) -> Bk.Term:
  match t:
    case Bk.Term.Var{i}:
      Term.lift(e, d, i)
    case Bk.Term.Ref{k}:
      Bk.Term.Ref{k}
    case Bk.Term.Ann{x, T}:
      Bk.Term.Ann{Term.subst(x, e, d), Term.subst(T, e, d)}
    case Bk.Term.Let{q, v, f}:
      Bk.Term.Let{q, Term.subst(v, e, d), Term.subst(f, e, 1n+d)}
    case Bk.Term.Typ{q}:
      Bk.Term.Typ{Term.subst(q, e, d)}
    case Bk.Term.Min{a, b}:
      Bk.Term.Min{Term.subst(a, e, d), Term.subst(b, e, d)}
    case Bk.Term.All{q, A, B}:
      Bk.Term.All{q, Term.subst(A, e, d), Term.subst(B, e, 1n+d)}
    case Bk.Term.Lam{q, f}:
      Bk.Term.Lam{q, Term.subst(f, e, 1n+d)}
    case Bk.Term.App{q, f, x}:
      Bk.Term.App{q, Term.subst(f, e, d), Term.subst(x, e, d)}
    case Bk.Term.Sig{q, A, B}:
      Bk.Term.Sig{q, Term.subst(A, e, d), Term.subst(B, e, 1n+d)}
    case Bk.Term.Tup{q, a, b}:
      Bk.Term.Tup{q, Term.subst(a, e, d), Term.subst(b, e, d)}
    case Bk.Term.Prj{h}:
      Bk.Term.Prj{Term.subst(h, e, d)}
    case Bk.Term.Enu{ks}:
      Bk.Term.Enu{ks}
    case Bk.Term.Lab{k}:
      Bk.Term.Lab{k}
    case Bk.Term.Mat{k, h, m}:
      Bk.Term.Mat{k, Term.subst(h, e, d), Term.subst(m, e, d)}
    case Bk.Term.Efq{}:
      Bk.Term.Efq{}
    case Bk.Term.Eql{a, b, T}:
      Bk.Term.Eql{Term.subst(a, e, d), Term.subst(b, e, d), Term.subst(T, e, d)}
    case Bk.Term.Rfl{}:
      Bk.Term.Rfl{}
    case Bk.Term.Rwt{x, P, f}:
      Bk.Term.Rwt{Term.subst(x, e, d), Term.subst(P, e, 2n+d), Term.subst(f, e, d)}

# f with v put in for its variable 0
def Term.inst(f: Bk.Term, v: Bk.Term) -> Bk.Term:
  Term.subst(f, Con{v, Nil{}}, 0n)

def Book.get.if(is_k: Bool, d: Bk.Def, r: Maybe<Bk.Def>) -> Maybe<Bk.Def>:
  match is_k:
    case True{}:
      Some{d}
    case False{}:
      r

# the first def of the name k
def Book.get(ds: List<&2, Bk.Def>, +k: List<&2, Word(8n)>) -> Maybe<Bk.Def>:
  match ds:
    case Nil{}:
      None{}
    case Con{Bk.Def{+n, T, v, o}, rest}:
      Book.get.if(Sd.Name.is_eq(n, k), Bk.Def{n, T, v, o}, Book.get(rest, k))

def Eval.walk.if(b: Bool, r: Maybe<Maybe<Bk.Term>>) -> Maybe<Maybe<Bk.Term>>:
  match b:
    case True{}:
      r
    case False{}:
      None{}

def Eval.walk.pick(b: Bool, r: Maybe<Maybe<Bk.Term>>, s: Maybe<Maybe<Bk.Term>>) -> Maybe<Maybe<Bk.Term>>:
  match b:
    case True{}:
      r
    case False{}:
      s

def Eval.walk.app(node: Bool, r: Maybe<Maybe<Bk.Term>>, u: Bk.Term) -> Maybe<Maybe<Bk.Term>>:
  match node:
    case True{}:
      r
    case False{}:
      Some{Some{u}}

def Eval.walk.leaf(node: Bool, xs: List<&2, Arg>, u: Bk.Term) -> Maybe<Maybe<Bk.Term>>:
  match node:
    case True{}:
      match xs:
        case Nil{}:
          Some{None{}}
        case _:
          None{}
    case False{}:
      Some{Some{u}}

# the walk of the case tree t on the arguments xs, with e bound: its leaf;
# None{} inside, when it needs more arguments; or None{}, when no walk exists
def Eval.walk(+t: Bk.Term, +e: List<&2, Bk.Term>, +xs: List<&2, Arg>) -> Maybe<Maybe<Bk.Term>>:
  match t xs:
    case Bk.Term.Lam{p, f} Con{Arg{q, x}, rest}:
      Eval.walk.if(Quan.binds(p, q, x), Eval.walk(f, Con{x, e}, rest))
    case Bk.Term.Prj{h} Con{Arg{q, Bk.Term.Tup{r, a, b}}, rest}:
      Eval.walk.if(Quan.live(q), Eval.walk(h, e, Con{Arg{Quan.fld(r, q), a}, Con{Arg{q, b}, rest}}))
    case Bk.Term.Mat{k, h, m} Con{Arg{q, Bk.Term.Lab{j}}, rest}:
      Eval.walk.if(Quan.live(q), Eval.walk.pick(Sd.Name.is_eq(j, k), Eval.walk(h, e, rest), Eval.walk(m, e, Con{Arg{q, Bk.Term.Lab{j}}, rest})))
    case Bk.Term.App{q, f, Bk.Term.Var{v}} ys:
      Eval.walk.app(Term.takes(Term.head(f)), Eval.walk(f, e, Con{Arg{q, Env.sub(e, v)}, ys}), Term.spine(ys, Term.subst(Bk.Term.App{q, f, Bk.Term.Var{v}}, e, 0n)))
    case u ys:
      Eval.walk.leaf(Term.takes(u), ys, Term.spine(ys, Term.subst(u, e, 0n)))

def Eval.callWalk.def(m: Maybe<Bk.Def>, xs: List<&2, Arg>) -> Maybe<Maybe<Bk.Term>>:
  match m:
    case None{}:
      None{}
    case Some{Bk.Def{_, _, v, _}}:
      Eval.walk(v, Nil{}, xs)

def Eval.callWalk.head(ds: List<&2, Bk.Def>, h: Bk.Term, xs: List<&2, Arg>) -> Maybe<Maybe<Bk.Term>>:
  match h:
    case Bk.Term.Ref{k}:
      Eval.callWalk.def(Book.get(ds, k), xs)
    case _:
      None{}

# the walk of a call's case tree on its arguments
def Eval.callWalk(ds: List<&2, Bk.Def>, +t: Bk.Term) -> Maybe<Maybe<Bk.Term>>:
  Eval.callWalk.head(ds, Term.head(t), Term.args(t, Nil{}))

# the walk needs more arguments
def Eval.waits(r: Maybe<Maybe<Bk.Term>>) -> Bool:
  match r:
    case Some{None{}}:
      True{}
    case _:
      False{}

def Eval.vals.app(as_args: Bool, ok: Bool, r: Maybe<Maybe<Bk.Term>>) -> Bool:
  match as_args:
    case True{}:
      ok
    case False{}:
      ok && Eval.waits(r)

def Eval.vals.ref(as_args: Bool, r: Maybe<Maybe<Bk.Term>>) -> Bool:
  match as_args:
    case True{}:
      True{}
    case False{}:
      Eval.waits(r)

def Eval.vals.other(as_args: Bool, former: Bool) -> Bool:
  match as_args:
    case True{}:
      False{}
    case False{}:
      former

# t is a value, or, when as_args, a spine of a def on arguments whose live ones
# are values
def Eval.vals(+ds: List<&2, Bk.Def>, +t: Bk.Term, as_args: Bool) -> Bool:
  match t:
    case Bk.Term.Tup{q, a, b}:
      match as_args:
        case True{}:
          False{}
        case False{}:
          (Bool.not(Quan.live(q)) || Eval.vals(ds, a, False{})) && Eval.vals(ds, b, False{})
    case Bk.Term.App{q, f, x}:
      Eval.vals.app(as_args, Eval.vals(ds, f, True{}) && (Bool.not(Quan.live(q)) || Eval.vals(ds, x, False{})), Eval.callWalk(ds, Bk.Term.App{q, f, x}))
    case Bk.Term.Ref{k}:
      Eval.vals.ref(as_args, Eval.callWalk(ds, Bk.Term.Ref{k}))
    case u:
      Eval.vals.other(as_args, Term.is_former(u))

def Eval.call.if(ok: Bool, r: Maybe<Maybe<Bk.Term>>) -> Maybe<Bk.Term>:
  match ok r:
    case True{} Some{Some{u}}:
      Some{u}
    case _ _:
      None{}

# the step of a call whose case tree takes the whole walk
def Eval.call(+ds: List<&2, Bk.Def>, +t: Bk.Term) -> Maybe<Bk.Term>:
  Eval.call.if(Eval.vals(ds, t, True{}), Eval.callWalk(ds, t))

def Eval.redex.if(b: Bool, u: Bk.Term) -> Maybe<Bk.Term>:
  match b:
    case True{}:
      Some{u}
    case False{}:
      None{}

def Eval.redex.pick(b: Bool, h: Bk.Term, m: Bk.Term) -> Bk.Term:
  match b:
    case True{}:
      h
    case False{}:
      m

# the step of App q f x, with f a value, and x a value when q is live
def Eval.redex(ds: List<&2, Bk.Def>, +q: Bk.Quan, +f: Bk.Term, +x: Bk.Term) -> Maybe<Bk.Term>:
  match f x:
    case Bk.Term.Lam{p, b} y:
      Eval.redex.if(Quan.binds(p, q, y), Term.inst(b, y))
    case Bk.Term.Prj{h} Bk.Term.Tup{r, a, b}:
      Eval.redex.if(Quan.live(q), Bk.Term.App{q, Bk.Term.App{Quan.fld(r, q), h, a}, b})
    case Bk.Term.Mat{k, h, m} Bk.Term.Lab{j}:
      Eval.redex.if(Quan.live(q), Eval.redex.pick(Sd.Name.is_eq(j, k), h, Bk.Term.App{q, m, Bk.Term.Lab{j}}))
    case g y:
      Eval.call(ds, Bk.Term.App{q, g, y})

def Quan.read.if(is_q: Bool, q: Bk.Quan, r: Maybe<Bk.Quan>) -> Maybe<Bk.Quan>:
  match is_q:
    case True{}:
      Some{q}
    case False{}:
      r

def Quan.name(q: Bk.Quan) -> List<&2, Word(8n)>:
  match q:
    case Bk.Quan.Q0{}:
      [Sd.Byte.from_u32(81), Sd.Byte.from_u32(48)]
    case Bk.Quan.Q1{}:
      [Sd.Byte.from_u32(81), Sd.Byte.from_u32(49)]
    case Bk.Quan.Q2{}:
      [Sd.Byte.from_u32(81), Sd.Byte.from_u32(50)]

# the quantity that a label names: Q0, Q1 or Q2
def Quan.read(+k: List<&2, Word(8n)>) -> Maybe<Bk.Quan>:
  Quan.read.if(Sd.Name.is_eq(k, Quan.name(Bk.Quan.Q0{})), Bk.Quan.Q0{},
    Quan.read.if(Sd.Name.is_eq(k, Quan.name(Bk.Quan.Q1{})), Bk.Quan.Q1{},
      Quan.read.if(Sd.Name.is_eq(k, Quan.name(Bk.Quan.Q2{})), Bk.Quan.Q2{}, None{})))

# the least of two quantities: 2 below none, and 0 below all
def Quan.min(p: Bk.Quan, q: Bk.Quan) -> Bk.Quan:
  match p q:
    case Bk.Quan.Q2{} r:
      r
    case r Bk.Quan.Q2{}:
      r
    case Bk.Quan.Q0{} _:
      Bk.Quan.Q0{}
    case _ Bk.Quan.Q0{}:
      Bk.Quan.Q0{}
    case _ _:
      Bk.Quan.Q1{}

def Eval.meet.of(i: Maybe<Bk.Quan>, j: Maybe<Bk.Quan>) -> Maybe<Bk.Term>:
  match i j:
    case Some{p} Some{q}:
      Some{Bk.Term.Lab{Quan.name(Quan.min(p, q))}}
    case _ _:
      None{}

# the meet of two quantity labels
def Eval.meet(a: Bk.Term, b: Bk.Term) -> Maybe<Bk.Term>:
  match a b:
    case Bk.Term.Lab{i} Bk.Term.Lab{j}:
      Eval.meet.of(Quan.read(i), Quan.read(j))
    case _ _:
      None{}

# App q f x: the step of f; or, once f is a value, the step of x when q is
# live; or, once x is a value too, the redex r
def Eval.step.app(q: Bk.Quan, f: Bk.Term, x: Bk.Term, sf: Maybe<Bk.Term>, vf: Bool, live: Bool, sx: Maybe<Bk.Term>, vx: Bool, r: Maybe<Bk.Term>) -> Maybe<Bk.Term>:
  match sf:
    case Some{f2}:
      Some{Bk.Term.App{q, f2, x}}
    case None{}:
      match vf:
        case False{}:
          None{}
        case True{}:
          match live:
            case False{}:
              r
            case True{}:
              match sx:
                case Some{x2}:
                  Some{Bk.Term.App{q, f, x2}}
                case None{}:
                  match vx:
                    case True{}:
                      r
                    case False{}:
                      None{}

def Eval.step.unlet(fits: Bool, f: Bk.Term, v: Bk.Term) -> Maybe<Bk.Term>:
  match fits:
    case True{}:
      Some{Term.inst(f, v)}
    case False{}:
      None{}

# Let q v f: the step of v, when q is live; or, once v is a value, f with v put
# in, when q may hold v
def Eval.step.let(q: Bk.Quan, v: Bk.Term, f: Bk.Term, live: Bool, sv: Maybe<Bk.Term>, vv: Bool, fits: Bool) -> Maybe<Bk.Term>:
  match live:
    case False{}:
      Eval.step.unlet(fits, f, v)
    case True{}:
      match sv:
        case Some{v2}:
          Some{Bk.Term.Let{q, v2, f}}
        case None{}:
          match vv:
            case True{}:
              Eval.step.unlet(fits, f, v)
            case False{}:
              None{}

def Eval.step.tup_b(q: Bk.Quan, a: Bk.Term, sb: Maybe<Bk.Term>) -> Maybe<Bk.Term>:
  match sb:
    case Some{b2}:
      Some{Bk.Term.Tup{q, a, b2}}
    case None{}:
      None{}

# Tup q a b: the step of a, when q is live; or, once a is a value, the step of b
def Eval.step.tup(q: Bk.Quan, a: Bk.Term, b: Bk.Term, live: Bool, sa: Maybe<Bk.Term>, va: Bool, sb: Maybe<Bk.Term>) -> Maybe<Bk.Term>:
  match live:
    case False{}:
      Eval.step.tup_b(q, a, sb)
    case True{}:
      match sa:
        case Some{a2}:
          Some{Bk.Term.Tup{q, a2, b}}
        case None{}:
          match va:
            case True{}:
              Eval.step.tup_b(q, a, sb)
            case False{}:
              None{}

def Eval.step.cast(e: Bk.Term, f: Bk.Term) -> Maybe<Bk.Term>:
  match e:
    case Bk.Term.Rfl{}:
      Some{f}
    case _:
      None{}

# Rwt e P f: the step of e; or, once e is Rfl, f
def Eval.step.rwt(e: Bk.Term, P: Bk.Term, f: Bk.Term, se: Maybe<Bk.Term>, ve: Bool) -> Maybe<Bk.Term>:
  match se:
    case Some{e2}:
      Some{Bk.Term.Rwt{e2, P, f}}
    case None{}:
      match ve:
        case True{}:
          Eval.step.cast(e, f)
        case False{}:
          None{}

# Min a b: the step of a; or, once a is a value, the step of b; or, once b is
# a value too, their meet m
def Eval.step.min(a: Bk.Term, b: Bk.Term, sa: Maybe<Bk.Term>, va: Bool, sb: Maybe<Bk.Term>, vb: Bool, m: Maybe<Bk.Term>) -> Maybe<Bk.Term>:
  match sa:
    case Some{a2}:
      Some{Bk.Term.Min{a2, b}}
    case None{}:
      match va:
        case False{}:
          None{}
        case True{}:
          match sb:
            case Some{b2}:
              Some{Bk.Term.Min{a, b2}}
            case None{}:
              match vb:
                case True{}:
                  m
                case False{}:
                  None{}

# one step of Eval
def Eval.step(+ds: List<&2, Bk.Def>, +t: Bk.Term) -> Maybe<Bk.Term>:
  match t:
    case Bk.Term.Ann{x, _}:
      Some{x}
    case Bk.Term.Ref{k}:
      Eval.call(ds, Bk.Term.Ref{k})
    case Bk.Term.App{q, f, x}:
      Eval.step.app(q, f, x, Eval.step(ds, f), Eval.vals(ds, f, False{}), Quan.live(q), Eval.step(ds, x), Eval.vals(ds, x, False{}), Eval.redex(ds, q, f, x))
    case Bk.Term.Let{q, v, f}:
      Eval.step.let(q, v, f, Quan.live(q), Eval.step(ds, v), Eval.vals(ds, v, False{}), Quan.fits(q, v))
    case Bk.Term.Tup{q, a, b}:
      Eval.step.tup(q, a, b, Quan.live(q), Eval.step(ds, a), Eval.vals(ds, a, False{}), Eval.step(ds, b))
    case Bk.Term.Rwt{e, P, f}:
      Eval.step.rwt(e, P, f, Eval.step(ds, e), Eval.vals(ds, e, False{}))
    case Bk.Term.Min{a, b}:
      Eval.step.min(a, b, Eval.step(ds, a), Eval.vals(ds, a, False{}), Eval.step(ds, b), Eval.vals(ds, b, False{}), Eval.meet(a, b))
    case _:
      None{}

# the state r after n more steps
def Eval.run(n: Nat, +ds: List<&2, Bk.Def>, r: Maybe<Bk.Term>) -> Maybe<Bk.Term>:
  match n r:
    case 0n s:
      s
    case 1n+_ None{}:
      None{}
    case 1n+m Some{t}:
      Eval.run(m, ds, Eval.step(ds, t))

def Eval.steps(n: Nat, ds: List<&2, Bk.Def>, t: Bk.Term) -> Maybe<Bk.Term>:
  Eval.run(n, ds, Some{t})
