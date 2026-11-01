# compiler: layer B, Eval's meta-theory for the moves
# ===================================================
#
# What the moves of moves.bend need of Eval: a value has no step
# (ev.stops, Lean's eval_value), and a focus with no step that is no value
# makes its frames' term so (ev.stuck). Both rest on walk.more: a walk of a
# case tree that does not wait for more arguments does not wait with more
# either (a walk that fails still fails; one that reaches its leaf still
# does).

import Base
import ../../shared/shared.bend as Sd
import ../../book/impl.bend as Bk
import ../../eval/impl.bend as El
import ./definitions.bend as D

# Kit
# ---

def ft(-G: Type, e: {True{} == False{} : Bool}) -> G:
  D.bool.ft(G, Equal.sym(Bool, True{}, False{}, e))

def and.l(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def and.r(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      D.bool.ft({b == True{} : Bool}, h)

def and.f(a: Bool, -b: Bool, h: {b == False{} : Bool}) -> {Bool.and(a, b) == False{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      {==}

# a step is not none
def sm.ne(-u: Bk.Term, e: {Some{u} == None{} : Maybe<Bk.Term>}) -> Empty:
  D.st.ne(u, Equal.sym(Maybe<Bk.Term>, Some{u}, None{}, e))

# x is True when y is, and y is False when x is
def bool.back(b: Bool, -x: Bool, -y: Bool, eb: {x == b : Bool}, more: {x == False{} : Bool} -> {y == False{} : Bool},
  hy: {y == True{} : Bool}) -> {x == True{} : Bool}:
  match b:
    case True{}:
      eb
    case False{}:
      D.bool.ft({x == True{} : Bool}, Equal.trans(Bool, False{}, y, True{}, Equal.sym(Bool, y, False{}, more(eb)), hy))

# A walk that does not wait does not wait with more arguments
# ------------------------------------------------------------

def w.if(b: Bool, -r: Maybe<Maybe<Bk.Term>>, -s: Maybe<Maybe<Bk.Term>>,
  h: {El.Eval.waits(El.Eval.walk.if(b, r)) == False{} : Bool},
  g: {El.Eval.waits(r) == False{} : Bool} -> {El.Eval.waits(s) == False{} : Bool}) ->
  {El.Eval.waits(El.Eval.walk.if(b, s)) == False{} : Bool}:
  match b:
    case True{}:
      g(h)
    case False{}:
      {==}

def w.pick(b: Bool, -r1: Maybe<Maybe<Bk.Term>>, -s1: Maybe<Maybe<Bk.Term>>, -r2: Maybe<Maybe<Bk.Term>>, -s2: Maybe<Maybe<Bk.Term>>,
  h: {El.Eval.waits(El.Eval.walk.pick(b, r1, s1)) == False{} : Bool},
  g1: {El.Eval.waits(r1) == False{} : Bool} -> {El.Eval.waits(r2) == False{} : Bool},
  g2: {El.Eval.waits(s1) == False{} : Bool} -> {El.Eval.waits(s2) == False{} : Bool}) ->
  {El.Eval.waits(El.Eval.walk.pick(b, r2, s2)) == False{} : Bool}:
  match b:
    case True{}:
      g1(h)
    case False{}:
      g2(h)

def w.app(b: Bool, -r: Maybe<Maybe<Bk.Term>>, -s: Maybe<Maybe<Bk.Term>>, -u: Bk.Term, -v: Bk.Term,
  h: {El.Eval.waits(El.Eval.walk.app(b, r, u)) == False{} : Bool},
  g: {El.Eval.waits(r) == False{} : Bool} -> {El.Eval.waits(s) == False{} : Bool}) ->
  {El.Eval.waits(El.Eval.walk.app(b, s, v)) == False{} : Bool}:
  match b:
    case True{}:
      g(h)
    case False{}:
      {==}

# the walk of the case tree t, with e bound, on xs then ys
def WM(t: Bk.Term, e: List<&2, Bk.Term>, xs: List<&2, El.Arg>, ys: List<&2, El.Arg>) -> Type:
  {El.Eval.waits(El.Eval.walk(t, e, List.append(&2, El.Arg, xs, ys))) == False{} : Bool}

def walk.more(t: Bk.Term, +e: List<&2, Bk.Term>, xs: List<&2, El.Arg>, +ys: List<&2, El.Arg>,
  h: {El.Eval.waits(El.Eval.walk(t, e, xs)) == False{} : Bool}) -> WM(t, e, xs, ys):
  match t:
    case Bk.Term.Var{+z0}:
      {==}
    case Bk.Term.Ref{+z0}:
      {==}
    case Bk.Term.Ann{+z0, +z1}:
      {==}
    case Bk.Term.Let{+z0, +z1, +z2}:
      {==}
    case Bk.Term.Typ{+z0}:
      {==}
    case Bk.Term.Min{+z0, +z1}:
      {==}
    case Bk.Term.All{+z0, +z1, +z2}:
      {==}
    case Bk.Term.Lam{+z0, +z1}:
      match xs:
        case Nil{}:
          ft(WM(Bk.Term.Lam{z0, z1}, e, Nil{}, ys), h)
        case Con{El.Arg{+q, +x}, +rest}:
          w.if(El.Quan.binds(z0, q, x), El.Eval.walk(z1, Con{x, e}, rest), El.Eval.walk(z1, Con{x, e}, List.append(&2, El.Arg, rest, ys)), h,
            hr => walk.more(z1, Con{x, e}, rest, ys, hr))
    case Bk.Term.App{+z0, +z1, +z2}:
      match z2:
        case Bk.Term.Var{+y0}:
          w.app(El.Term.takes(El.Term.head(z1)), El.Eval.walk(z1, e, Con{El.Arg{z0, El.Env.sub(e, y0)}, xs}),
            El.Eval.walk(z1, e, Con{El.Arg{z0, El.Env.sub(e, y0)}, List.append(&2, El.Arg, xs, ys)}),
            El.Term.spine(xs, El.Term.subst(Bk.Term.App{z0, z1, Bk.Term.Var{y0}}, e, 0n)),
            El.Term.spine(List.append(&2, El.Arg, xs, ys), El.Term.subst(Bk.Term.App{z0, z1, Bk.Term.Var{y0}}, e, 0n)), h,
            hr => walk.more(z1, e, Con{El.Arg{z0, El.Env.sub(e, y0)}, xs}, ys, hr))
        case Bk.Term.Ref{+y0}:
          {==}
        case Bk.Term.Ann{+y0, +y1}:
          {==}
        case Bk.Term.Let{+y0, +y1, +y2}:
          {==}
        case Bk.Term.Typ{+y0}:
          {==}
        case Bk.Term.Min{+y0, +y1}:
          {==}
        case Bk.Term.All{+y0, +y1, +y2}:
          {==}
        case Bk.Term.Lam{+y0, +y1}:
          {==}
        case Bk.Term.App{+y0, +y1, +y2}:
          {==}
        case Bk.Term.Sig{+y0, +y1, +y2}:
          {==}
        case Bk.Term.Tup{+y0, +y1, +y2}:
          {==}
        case Bk.Term.Prj{+y0}:
          {==}
        case Bk.Term.Enu{+y0}:
          {==}
        case Bk.Term.Lab{+y0}:
          {==}
        case Bk.Term.Mat{+y0, +y1, +y2}:
          {==}
        case Bk.Term.Efq{}:
          {==}
        case Bk.Term.Eql{+y0, +y1, +y2}:
          {==}
        case Bk.Term.Rfl{}:
          {==}
        case Bk.Term.Rwt{+y0, +y1, +y2}:
          {==}
    case Bk.Term.Sig{+z0, +z1, +z2}:
      {==}
    case Bk.Term.Tup{+z0, +z1, +z2}:
      {==}
    case Bk.Term.Prj{+z0}:
      match xs:
        case Nil{}:
          ft(WM(Bk.Term.Prj{z0}, e, Nil{}, ys), h)
        case Con{El.Arg{+q, +x}, +rest}:
          match x:
            case Bk.Term.Var{+y0}:
              {==}
            case Bk.Term.Ref{+y0}:
              {==}
            case Bk.Term.Ann{+y0, +y1}:
              {==}
            case Bk.Term.Let{+y0, +y1, +y2}:
              {==}
            case Bk.Term.Typ{+y0}:
              {==}
            case Bk.Term.Min{+y0, +y1}:
              {==}
            case Bk.Term.All{+y0, +y1, +y2}:
              {==}
            case Bk.Term.Lam{+y0, +y1}:
              {==}
            case Bk.Term.App{+y0, +y1, +y2}:
              {==}
            case Bk.Term.Sig{+y0, +y1, +y2}:
              {==}
            case Bk.Term.Tup{+y0, +y1, +y2}:
              w.if(El.Quan.live(q), El.Eval.walk(z0, e, Con{El.Arg{El.Quan.fld(y0, q), y1}, Con{El.Arg{q, y2}, rest}}),
                El.Eval.walk(z0, e, Con{El.Arg{El.Quan.fld(y0, q), y1}, Con{El.Arg{q, y2}, List.append(&2, El.Arg, rest, ys)}}), h,
                hr => walk.more(z0, e, Con{El.Arg{El.Quan.fld(y0, q), y1}, Con{El.Arg{q, y2}, rest}}, ys, hr))
            case Bk.Term.Prj{+y0}:
              {==}
            case Bk.Term.Enu{+y0}:
              {==}
            case Bk.Term.Lab{+y0}:
              {==}
            case Bk.Term.Mat{+y0, +y1, +y2}:
              {==}
            case Bk.Term.Efq{}:
              {==}
            case Bk.Term.Eql{+y0, +y1, +y2}:
              {==}
            case Bk.Term.Rfl{}:
              {==}
            case Bk.Term.Rwt{+y0, +y1, +y2}:
              {==}
    case Bk.Term.Enu{+z0}:
      {==}
    case Bk.Term.Lab{+z0}:
      {==}
    case Bk.Term.Mat{+z0, +z1, +z2}:
      match xs:
        case Nil{}:
          ft(WM(Bk.Term.Mat{z0, z1, z2}, e, Nil{}, ys), h)
        case Con{El.Arg{+q, +x}, +rest}:
          match x:
            case Bk.Term.Var{+y0}:
              {==}
            case Bk.Term.Ref{+y0}:
              {==}
            case Bk.Term.Ann{+y0, +y1}:
              {==}
            case Bk.Term.Let{+y0, +y1, +y2}:
              {==}
            case Bk.Term.Typ{+y0}:
              {==}
            case Bk.Term.Min{+y0, +y1}:
              {==}
            case Bk.Term.All{+y0, +y1, +y2}:
              {==}
            case Bk.Term.Lam{+y0, +y1}:
              {==}
            case Bk.Term.App{+y0, +y1, +y2}:
              {==}
            case Bk.Term.Sig{+y0, +y1, +y2}:
              {==}
            case Bk.Term.Tup{+y0, +y1, +y2}:
              {==}
            case Bk.Term.Prj{+y0}:
              {==}
            case Bk.Term.Enu{+y0}:
              {==}
            case Bk.Term.Lab{+y0}:
              w.if(El.Quan.live(q), El.Eval.walk.pick(Sd.Name.is_eq(y0, z0), El.Eval.walk(z1, e, rest), El.Eval.walk(z2, e, Con{El.Arg{q, Bk.Term.Lab{y0}}, rest})),
                El.Eval.walk.pick(Sd.Name.is_eq(y0, z0), El.Eval.walk(z1, e, List.append(&2, El.Arg, rest, ys)), El.Eval.walk(z2, e, Con{El.Arg{q, Bk.Term.Lab{y0}}, List.append(&2, El.Arg, rest, ys)})), h,
                hr => w.pick(Sd.Name.is_eq(y0, z0), El.Eval.walk(z1, e, rest), El.Eval.walk(z2, e, Con{El.Arg{q, Bk.Term.Lab{y0}}, rest}),
                  El.Eval.walk(z1, e, List.append(&2, El.Arg, rest, ys)), El.Eval.walk(z2, e, Con{El.Arg{q, Bk.Term.Lab{y0}}, List.append(&2, El.Arg, rest, ys)}), hr,
                  a1 => walk.more(z1, e, rest, ys, a1), a2 => walk.more(z2, e, Con{El.Arg{q, Bk.Term.Lab{y0}}, rest}, ys, a2)))
            case Bk.Term.Mat{+y0, +y1, +y2}:
              {==}
            case Bk.Term.Efq{}:
              {==}
            case Bk.Term.Eql{+y0, +y1, +y2}:
              {==}
            case Bk.Term.Rfl{}:
              {==}
            case Bk.Term.Rwt{+y0, +y1, +y2}:
              {==}
    case Bk.Term.Efq{}:
      match xs:
        case Nil{}:
          ft(WM(Bk.Term.Efq{}, e, Nil{}, ys), h)
        case Con{+x, +rest}:
          {==}
    case Bk.Term.Eql{+z0, +z1, +z2}:
      {==}
    case Bk.Term.Rfl{}:
      {==}
    case Bk.Term.Rwt{+z0, +z1, +z2}:
      {==}

# the same for a call's walk, from the head of its spine
def cwd.more(mb: Maybe<Bk.Def>, xs: List<&2, El.Arg>, +ys: List<&2, El.Arg>,
  h: {El.Eval.waits(El.Eval.callWalk.def(mb, xs)) == False{} : Bool}) ->
  {El.Eval.waits(El.Eval.callWalk.def(mb, List.append(&2, El.Arg, xs, ys))) == False{} : Bool}:
  match mb:
    case None{}:
      {==}
    case Some{Bk.Def{+k, +T, +v, +o}}:
      walk.more(v, Nil{}, xs, ys, h)

def cwh.more(+ds: List<&2, Bk.Def>, hd: Bk.Term, xs: List<&2, El.Arg>, +ys: List<&2, El.Arg>,
  h: {El.Eval.waits(El.Eval.callWalk.head(ds, hd, xs)) == False{} : Bool}) ->
  {El.Eval.waits(El.Eval.callWalk.head(ds, hd, List.append(&2, El.Arg, xs, ys))) == False{} : Bool}:
  match hd:
    case Bk.Term.Var{+z0}:
      {==}
    case Bk.Term.Ref{+z0}:
      cwd.more(El.Book.get(ds, z0), xs, ys, h)
    case Bk.Term.Ann{+z0, +z1}:
      {==}
    case Bk.Term.Let{+z0, +z1, +z2}:
      {==}
    case Bk.Term.Typ{+z0}:
      {==}
    case Bk.Term.Min{+z0, +z1}:
      {==}
    case Bk.Term.All{+z0, +z1, +z2}:
      {==}
    case Bk.Term.Lam{+z0, +z1}:
      {==}
    case Bk.Term.App{+z0, +z1, +z2}:
      {==}
    case Bk.Term.Sig{+z0, +z1, +z2}:
      {==}
    case Bk.Term.Tup{+z0, +z1, +z2}:
      {==}
    case Bk.Term.Prj{+z0}:
      {==}
    case Bk.Term.Enu{+z0}:
      {==}
    case Bk.Term.Lab{+z0}:
      {==}
    case Bk.Term.Mat{+z0, +z1, +z2}:
      {==}
    case Bk.Term.Efq{}:
      {==}
    case Bk.Term.Eql{+z0, +z1, +z2}:
      {==}
    case Bk.Term.Rfl{}:
      {==}
    case Bk.Term.Rwt{+z0, +z1, +z2}:
      {==}

# the arguments of a spine, in front of xs then ys
def args.app(t: Bk.Term, xs: List<&2, El.Arg>, +ys: List<&2, El.Arg>) ->
  {El.Term.args(t, List.append(&2, El.Arg, xs, ys)) == List.append(&2, El.Arg, El.Term.args(t, xs), ys) : List<&2, El.Arg>}:
  match t:
    case Bk.Term.Var{+z0}:
      {==}
    case Bk.Term.Ref{+z0}:
      {==}
    case Bk.Term.Ann{+z0, +z1}:
      {==}
    case Bk.Term.Let{+z0, +z1, +z2}:
      {==}
    case Bk.Term.Typ{+z0}:
      {==}
    case Bk.Term.Min{+z0, +z1}:
      {==}
    case Bk.Term.All{+z0, +z1, +z2}:
      {==}
    case Bk.Term.Lam{+z0, +z1}:
      {==}
    case Bk.Term.App{+z0, +z1, +z2}:
      args.app(z1, Con{El.Arg{z0, z2}, xs}, ys)
    case Bk.Term.Sig{+z0, +z1, +z2}:
      {==}
    case Bk.Term.Tup{+z0, +z1, +z2}:
      {==}
    case Bk.Term.Prj{+z0}:
      {==}
    case Bk.Term.Enu{+z0}:
      {==}
    case Bk.Term.Lab{+z0}:
      {==}
    case Bk.Term.Mat{+z0, +z1, +z2}:
      {==}
    case Bk.Term.Efq{}:
      {==}
    case Bk.Term.Eql{+z0, +z1, +z2}:
      {==}
    case Bk.Term.Rfl{}:
      {==}
    case Bk.Term.Rwt{+z0, +z1, +z2}:
      {==}

# a call's walk that does not wait does not wait with one more argument
def cw.app(+ds: List<&2, Bk.Def>, +u: Bk.Term, +q: Bk.Quan, +a: Bk.Term,
  h: {El.Eval.waits(El.Eval.callWalk(ds, u)) == False{} : Bool}) ->
  {El.Eval.waits(El.Eval.callWalk(ds, Bk.Term.App{q, u, a})) == False{} : Bool}:
  %Equal.sym(List<&2, El.Arg>, El.Term.args(u, List.append(&2, El.Arg, Nil{}, [El.Arg{q, a}])), List.append(&2, El.Arg, El.Term.args(u, Nil{}), [El.Arg{q, a}]),
    args.app(u, Nil{}, [El.Arg{q, a}])) : {El.Eval.waits(El.Eval.callWalk.head(ds, El.Term.head(u), _)) == False{} : Bool}
  cwh.more(ds, El.Term.head(u), El.Term.args(u, Nil{}), [El.Arg{q, a}], h)

def cw.acc(+ds: List<&2, Bk.Def>, +f: Bk.Term, +acc: List<&2, El.Arg>,
  hw: {El.Eval.waits(El.Eval.callWalk.head(ds, El.Term.head(f), El.Term.args(f, acc))) == True{} : Bool}) ->
  {El.Eval.waits(El.Eval.callWalk.head(ds, El.Term.head(f), List.append(&2, El.Arg, El.Term.args(f, Nil{}), acc))) == True{} : Bool}:
  %args.app(f, Nil{}, acc) : {El.Eval.waits(El.Eval.callWalk.head(ds, El.Term.head(f), _)) == True{} : Bool}
  hw

# a call's walk that waits with more arguments waits with none
def cw.back(+ds: List<&2, Bk.Def>, +f: Bk.Term, +acc: List<&2, El.Arg>,
  hw: {El.Eval.waits(El.Eval.callWalk.head(ds, El.Term.head(f), El.Term.args(f, acc))) == True{} : Bool}) ->
  {El.Eval.waits(El.Eval.callWalk(ds, f)) == True{} : Bool}:
  +hw2 = cw.acc(ds, f, acc, hw)
  bool.back(El.Eval.waits(El.Eval.callWalk(ds, f)), El.Eval.waits(El.Eval.callWalk(ds, f)),
    El.Eval.waits(El.Eval.callWalk.head(ds, El.Term.head(f), List.append(&2, El.Arg, El.Term.args(f, Nil{}), acc))), {==},
    e => cwh.more(ds, El.Term.head(f), El.Term.args(f, Nil{}), acc, e), hw2)

# Values
# ------

# a spine of a def on arguments that are values is a value when its walk waits
def vals.tf(+ds: List<&2, Bk.Def>, u: Bk.Term, ht: {El.Eval.vals(ds, u, True{}) == True{} : Bool}) ->
  {El.Eval.vals(ds, u, False{}) == El.Eval.waits(El.Eval.callWalk(ds, u)) : Bool}:
  match u:
    case Bk.Term.Var{+z0}:
      D.bool.ft({El.Eval.vals(ds, Bk.Term.Var{z0}, False{}) == El.Eval.waits(El.Eval.callWalk(ds, Bk.Term.Var{z0})) : Bool}, ht)
    case Bk.Term.Ref{+z0}:
      {==}
    case Bk.Term.Ann{+z0, +z1}:
      D.bool.ft({El.Eval.vals(ds, Bk.Term.Ann{z0, z1}, False{}) == El.Eval.waits(El.Eval.callWalk(ds, Bk.Term.Ann{z0, z1})) : Bool}, ht)
    case Bk.Term.Let{+z0, +z1, +z2}:
      D.bool.ft({El.Eval.vals(ds, Bk.Term.Let{z0, z1, z2}, False{}) == El.Eval.waits(El.Eval.callWalk(ds, Bk.Term.Let{z0, z1, z2})) : Bool}, ht)
    case Bk.Term.Typ{+z0}:
      D.bool.ft({El.Eval.vals(ds, Bk.Term.Typ{z0}, False{}) == El.Eval.waits(El.Eval.callWalk(ds, Bk.Term.Typ{z0})) : Bool}, ht)
    case Bk.Term.Min{+z0, +z1}:
      D.bool.ft({El.Eval.vals(ds, Bk.Term.Min{z0, z1}, False{}) == El.Eval.waits(El.Eval.callWalk(ds, Bk.Term.Min{z0, z1})) : Bool}, ht)
    case Bk.Term.All{+z0, +z1, +z2}:
      D.bool.ft({El.Eval.vals(ds, Bk.Term.All{z0, z1, z2}, False{}) == El.Eval.waits(El.Eval.callWalk(ds, Bk.Term.All{z0, z1, z2})) : Bool}, ht)
    case Bk.Term.Lam{+z0, +z1}:
      D.bool.ft({El.Eval.vals(ds, Bk.Term.Lam{z0, z1}, False{}) == El.Eval.waits(El.Eval.callWalk(ds, Bk.Term.Lam{z0, z1})) : Bool}, ht)
    case Bk.Term.App{+z0, +z1, +z2}:
      %Equal.sym(Bool, Bool.and(El.Eval.vals(ds, z1, True{}), Bool.or(Bool.not(El.Quan.live(z0)), El.Eval.vals(ds, z2, False{}))), True{}, ht) :
        {Bool.and(_, El.Eval.waits(El.Eval.callWalk(ds, Bk.Term.App{z0, z1, z2}))) == El.Eval.waits(El.Eval.callWalk(ds, Bk.Term.App{z0, z1, z2})) : Bool}
      {==}
    case Bk.Term.Sig{+z0, +z1, +z2}:
      D.bool.ft({El.Eval.vals(ds, Bk.Term.Sig{z0, z1, z2}, False{}) == El.Eval.waits(El.Eval.callWalk(ds, Bk.Term.Sig{z0, z1, z2})) : Bool}, ht)
    case Bk.Term.Tup{+z0, +z1, +z2}:
      D.bool.ft({El.Eval.vals(ds, Bk.Term.Tup{z0, z1, z2}, False{}) == El.Eval.waits(El.Eval.callWalk(ds, Bk.Term.Tup{z0, z1, z2})) : Bool}, ht)
    case Bk.Term.Prj{+z0}:
      D.bool.ft({El.Eval.vals(ds, Bk.Term.Prj{z0}, False{}) == El.Eval.waits(El.Eval.callWalk(ds, Bk.Term.Prj{z0})) : Bool}, ht)
    case Bk.Term.Enu{+z0}:
      D.bool.ft({El.Eval.vals(ds, Bk.Term.Enu{z0}, False{}) == El.Eval.waits(El.Eval.callWalk(ds, Bk.Term.Enu{z0})) : Bool}, ht)
    case Bk.Term.Lab{+z0}:
      D.bool.ft({El.Eval.vals(ds, Bk.Term.Lab{z0}, False{}) == El.Eval.waits(El.Eval.callWalk(ds, Bk.Term.Lab{z0})) : Bool}, ht)
    case Bk.Term.Mat{+z0, +z1, +z2}:
      D.bool.ft({El.Eval.vals(ds, Bk.Term.Mat{z0, z1, z2}, False{}) == El.Eval.waits(El.Eval.callWalk(ds, Bk.Term.Mat{z0, z1, z2})) : Bool}, ht)
    case Bk.Term.Efq{}:
      D.bool.ft({El.Eval.vals(ds, Bk.Term.Efq{}, False{}) == El.Eval.waits(El.Eval.callWalk(ds, Bk.Term.Efq{})) : Bool}, ht)
    case Bk.Term.Eql{+z0, +z1, +z2}:
      D.bool.ft({El.Eval.vals(ds, Bk.Term.Eql{z0, z1, z2}, False{}) == El.Eval.waits(El.Eval.callWalk(ds, Bk.Term.Eql{z0, z1, z2})) : Bool}, ht)
    case Bk.Term.Rfl{}:
      D.bool.ft({El.Eval.vals(ds, Bk.Term.Rfl{}, False{}) == El.Eval.waits(El.Eval.callWalk(ds, Bk.Term.Rfl{})) : Bool}, ht)
    case Bk.Term.Rwt{+z0, +z1, +z2}:
      D.bool.ft({El.Eval.vals(ds, Bk.Term.Rwt{z0, z1, z2}, False{}) == El.Eval.waits(El.Eval.callWalk(ds, Bk.Term.Rwt{z0, z1, z2})) : Bool}, ht)

# the call of a walk that waits is none
def call.none(ok: Bool, r: Maybe<Maybe<Bk.Term>>, h: {El.Eval.waits(r) == True{} : Bool}) -> {El.Eval.call.if(ok, r) == None{} : Maybe<Bk.Term>}:
  match ok:
    case True{}:
      match r:
        case None{}:
          D.bool.ft({El.Eval.call.if(True{}, None{}) == None{} : Maybe<Bk.Term>}, h)
        case Some{+s}:
          match s:
            case None{}:
              {==}
            case Some{+u}:
              D.bool.ft({El.Eval.call.if(True{}, Some{Some{u}}) == None{} : Maybe<Bk.Term>}, h)
    case False{}:
      {==}

# the redex of a spine of a def is its call
def redex.call(+ds: List<&2, Bk.Def>, g: Bk.Term, +q: Bk.Quan, +x: Bk.Term, ht: {El.Eval.vals(ds, g, True{}) == True{} : Bool}) ->
  {El.Eval.redex(ds, q, g, x) == El.Eval.call(ds, Bk.Term.App{q, g, x}) : Maybe<Bk.Term>}:
  match g:
    case Bk.Term.Var{+z0}:
      D.bool.ft({El.Eval.redex(ds, q, Bk.Term.Var{z0}, x) == El.Eval.call(ds, Bk.Term.App{q, Bk.Term.Var{z0}, x}) : Maybe<Bk.Term>}, ht)
    case Bk.Term.Ref{+z0}:
      {==}
    case Bk.Term.Ann{+z0, +z1}:
      D.bool.ft({El.Eval.redex(ds, q, Bk.Term.Ann{z0, z1}, x) == El.Eval.call(ds, Bk.Term.App{q, Bk.Term.Ann{z0, z1}, x}) : Maybe<Bk.Term>}, ht)
    case Bk.Term.Let{+z0, +z1, +z2}:
      D.bool.ft({El.Eval.redex(ds, q, Bk.Term.Let{z0, z1, z2}, x) == El.Eval.call(ds, Bk.Term.App{q, Bk.Term.Let{z0, z1, z2}, x}) : Maybe<Bk.Term>}, ht)
    case Bk.Term.Typ{+z0}:
      D.bool.ft({El.Eval.redex(ds, q, Bk.Term.Typ{z0}, x) == El.Eval.call(ds, Bk.Term.App{q, Bk.Term.Typ{z0}, x}) : Maybe<Bk.Term>}, ht)
    case Bk.Term.Min{+z0, +z1}:
      D.bool.ft({El.Eval.redex(ds, q, Bk.Term.Min{z0, z1}, x) == El.Eval.call(ds, Bk.Term.App{q, Bk.Term.Min{z0, z1}, x}) : Maybe<Bk.Term>}, ht)
    case Bk.Term.All{+z0, +z1, +z2}:
      D.bool.ft({El.Eval.redex(ds, q, Bk.Term.All{z0, z1, z2}, x) == El.Eval.call(ds, Bk.Term.App{q, Bk.Term.All{z0, z1, z2}, x}) : Maybe<Bk.Term>}, ht)
    case Bk.Term.Lam{+z0, +z1}:
      D.bool.ft({El.Eval.redex(ds, q, Bk.Term.Lam{z0, z1}, x) == El.Eval.call(ds, Bk.Term.App{q, Bk.Term.Lam{z0, z1}, x}) : Maybe<Bk.Term>}, ht)
    case Bk.Term.App{+z0, +z1, +z2}:
      {==}
    case Bk.Term.Sig{+z0, +z1, +z2}:
      D.bool.ft({El.Eval.redex(ds, q, Bk.Term.Sig{z0, z1, z2}, x) == El.Eval.call(ds, Bk.Term.App{q, Bk.Term.Sig{z0, z1, z2}, x}) : Maybe<Bk.Term>}, ht)
    case Bk.Term.Tup{+z0, +z1, +z2}:
      D.bool.ft({El.Eval.redex(ds, q, Bk.Term.Tup{z0, z1, z2}, x) == El.Eval.call(ds, Bk.Term.App{q, Bk.Term.Tup{z0, z1, z2}, x}) : Maybe<Bk.Term>}, ht)
    case Bk.Term.Prj{+z0}:
      D.bool.ft({El.Eval.redex(ds, q, Bk.Term.Prj{z0}, x) == El.Eval.call(ds, Bk.Term.App{q, Bk.Term.Prj{z0}, x}) : Maybe<Bk.Term>}, ht)
    case Bk.Term.Enu{+z0}:
      D.bool.ft({El.Eval.redex(ds, q, Bk.Term.Enu{z0}, x) == El.Eval.call(ds, Bk.Term.App{q, Bk.Term.Enu{z0}, x}) : Maybe<Bk.Term>}, ht)
    case Bk.Term.Lab{+z0}:
      D.bool.ft({El.Eval.redex(ds, q, Bk.Term.Lab{z0}, x) == El.Eval.call(ds, Bk.Term.App{q, Bk.Term.Lab{z0}, x}) : Maybe<Bk.Term>}, ht)
    case Bk.Term.Mat{+z0, +z1, +z2}:
      D.bool.ft({El.Eval.redex(ds, q, Bk.Term.Mat{z0, z1, z2}, x) == El.Eval.call(ds, Bk.Term.App{q, Bk.Term.Mat{z0, z1, z2}, x}) : Maybe<Bk.Term>}, ht)
    case Bk.Term.Efq{}:
      D.bool.ft({El.Eval.redex(ds, q, Bk.Term.Efq{}, x) == El.Eval.call(ds, Bk.Term.App{q, Bk.Term.Efq{}, x}) : Maybe<Bk.Term>}, ht)
    case Bk.Term.Eql{+z0, +z1, +z2}:
      D.bool.ft({El.Eval.redex(ds, q, Bk.Term.Eql{z0, z1, z2}, x) == El.Eval.call(ds, Bk.Term.App{q, Bk.Term.Eql{z0, z1, z2}, x}) : Maybe<Bk.Term>}, ht)
    case Bk.Term.Rfl{}:
      D.bool.ft({El.Eval.redex(ds, q, Bk.Term.Rfl{}, x) == El.Eval.call(ds, Bk.Term.App{q, Bk.Term.Rfl{}, x}) : Maybe<Bk.Term>}, ht)
    case Bk.Term.Rwt{+z0, +z1, +z2}:
      D.bool.ft({El.Eval.redex(ds, q, Bk.Term.Rwt{z0, z1, z2}, x) == El.Eval.call(ds, Bk.Term.App{q, Bk.Term.Rwt{z0, z1, z2}, x}) : Maybe<Bk.Term>}, ht)

# App q f x has no step, when f has none, is a value, and x has none and is a
# value when q is live, and the redex is none
def app.none(+q: Bk.Quan, +f: Bk.Term, +x: Bk.Term, sf: Maybe<Bk.Term>, vf: Bool, live: Bool, sx: Maybe<Bk.Term>, vx: Bool, -r: Maybe<Bk.Term>,
  esf: {sf == None{} : Maybe<Bk.Term>}, hx: {Bool.or(Bool.not(live), vx) == True{} : Bool},
  esx: {vx == True{} : Bool} -> {sx == None{} : Maybe<Bk.Term>}, er: {r == None{} : Maybe<Bk.Term>}) ->
  {El.Eval.step.app(q, f, x, sf, vf, live, sx, vx, r) == None{} : Maybe<Bk.Term>}:
  match sf:
    case Some{+f2}:
      Empty.absurd({El.Eval.step.app(q, f, x, Some{f2}, vf, live, sx, vx, r) == None{} : Maybe<Bk.Term>}, sm.ne(f2, esf))
    case None{}:
      match vf:
        case False{}:
          {==}
        case True{}:
          match live:
            case False{}:
              er
            case True{}:
              match sx:
                case Some{+x2}:
                  Empty.absurd({El.Eval.step.app(q, f, x, None{}, True{}, True{}, Some{x2}, vx, r) == None{} : Maybe<Bk.Term>}, sm.ne(x2, esx(hx)))
                case None{}:
                  match vx:
                    case True{}:
                      er
                    case False{}:
                      {==}

# Tup q a b has no step, when a has none when it is a value and q live, and b
# has none
def tup.none(+q: Bk.Quan, +a: Bk.Term, +b: Bk.Term, live: Bool, sa: Maybe<Bk.Term>, va: Bool, sb: Maybe<Bk.Term>,
  hx: {Bool.or(Bool.not(live), va) == True{} : Bool}, esa: {va == True{} : Bool} -> {sa == None{} : Maybe<Bk.Term>},
  esb: {sb == None{} : Maybe<Bk.Term>}) -> {El.Eval.step.tup(q, a, b, live, sa, va, sb) == None{} : Maybe<Bk.Term>}:
  match live:
    case False{}:
      %Equal.sym(Maybe<Bk.Term>, sb, None{}, esb) : {El.Eval.step.tup_b(q, a, _) == None{} : Maybe<Bk.Term>}
      {==}
    case True{}:
      match sa:
        case Some{+a2}:
          Empty.absurd({El.Eval.step.tup(q, a, b, True{}, Some{a2}, va, sb) == None{} : Maybe<Bk.Term>}, sm.ne(a2, esa(hx)))
        case None{}:
          match va:
            case True{}:
              %Equal.sym(Maybe<Bk.Term>, sb, None{}, esb) : {El.Eval.step.tup_b(q, a, _) == None{} : Maybe<Bk.Term>}
              {==}
            case False{}:
              {==}

# A value has no step
# -------------------

# what stops says has no step: a value (a False), or a spine of a def on
# arguments that are values, whose walk with more arguments acc waits (a True)
def SH(a: Bool, +ds: List<&2, Bk.Def>, +t: Bk.Term, +acc: List<&2, El.Arg>) -> Data:
  match a:
    case False{}:
      {El.Eval.vals(ds, t, False{}) == True{} : Bool}
    case True{}:
      D.P2({El.Eval.vals(ds, t, True{}) == True{} : Bool},
        {El.Eval.waits(El.Eval.callWalk.head(ds, El.Term.head(t), El.Term.args(t, acc))) == True{} : Bool})

def stops(t: Bk.Term, a: Bool, +ds: List<&2, Bk.Def>, +acc: List<&2, El.Arg>, +h: SH(a, ds, t, acc)) ->
  {El.Eval.step(ds, t) == None{} : Maybe<Bk.Term>}:
  match t:
    case Bk.Term.Var{+z0}:
      match a:
        case False{}:
          {==}
        case True{}:
          (ht, hw) = h
          D.bool.ft({El.Eval.step(ds, Bk.Term.Var{z0}) == None{} : Maybe<Bk.Term>}, ht)
    case Bk.Term.Ref{+z0}:
      match a:
        case False{}:
          call.none(True{}, El.Eval.callWalk(ds, Bk.Term.Ref{z0}), h)
        case True{}:
          (ht, hw) = h
          call.none(True{}, El.Eval.callWalk(ds, Bk.Term.Ref{z0}), cw.back(ds, Bk.Term.Ref{z0}, acc, hw))
    case Bk.Term.Ann{+z0, +z1}:
      match a:
        case False{}:
          D.bool.ft({El.Eval.step(ds, Bk.Term.Ann{z0, z1}) == None{} : Maybe<Bk.Term>}, h)
        case True{}:
          (ht, hw) = h
          D.bool.ft({El.Eval.step(ds, Bk.Term.Ann{z0, z1}) == None{} : Maybe<Bk.Term>}, ht)
    case Bk.Term.Let{+z0, +z1, +z2}:
      match a:
        case False{}:
          D.bool.ft({El.Eval.step(ds, Bk.Term.Let{z0, z1, z2}) == None{} : Maybe<Bk.Term>}, h)
        case True{}:
          (ht, hw) = h
          D.bool.ft({El.Eval.step(ds, Bk.Term.Let{z0, z1, z2}) == None{} : Maybe<Bk.Term>}, ht)
    case Bk.Term.Typ{+z0}:
      match a:
        case False{}:
          {==}
        case True{}:
          (ht, hw) = h
          D.bool.ft({El.Eval.step(ds, Bk.Term.Typ{z0}) == None{} : Maybe<Bk.Term>}, ht)
    case Bk.Term.Min{+z0, +z1}:
      match a:
        case False{}:
          D.bool.ft({El.Eval.step(ds, Bk.Term.Min{z0, z1}) == None{} : Maybe<Bk.Term>}, h)
        case True{}:
          (ht, hw) = h
          D.bool.ft({El.Eval.step(ds, Bk.Term.Min{z0, z1}) == None{} : Maybe<Bk.Term>}, ht)
    case Bk.Term.All{+z0, +z1, +z2}:
      match a:
        case False{}:
          {==}
        case True{}:
          (ht, hw) = h
          D.bool.ft({El.Eval.step(ds, Bk.Term.All{z0, z1, z2}) == None{} : Maybe<Bk.Term>}, ht)
    case Bk.Term.Lam{+z0, +z1}:
      match a:
        case False{}:
          {==}
        case True{}:
          (ht, hw) = h
          D.bool.ft({El.Eval.step(ds, Bk.Term.Lam{z0, z1}) == None{} : Maybe<Bk.Term>}, ht)
    case Bk.Term.App{+z0, +z1, +z2}:
      match a:
        case False{}:
          +ok = and.l(Bool.and(El.Eval.vals(ds, z1, True{}), Bool.or(Bool.not(El.Quan.live(z0)), El.Eval.vals(ds, z2, False{}))), El.Eval.waits(El.Eval.callWalk(ds, Bk.Term.App{z0, z1, z2})), h)
          +hw = and.r(Bool.and(El.Eval.vals(ds, z1, True{}), Bool.or(Bool.not(El.Quan.live(z0)), El.Eval.vals(ds, z2, False{}))), El.Eval.waits(El.Eval.callWalk(ds, Bk.Term.App{z0, z1, z2})), h)
          +hg = and.l(El.Eval.vals(ds, z1, True{}), Bool.or(Bool.not(El.Quan.live(z0)), El.Eval.vals(ds, z2, False{})), ok)
          +hx = and.r(El.Eval.vals(ds, z1, True{}), Bool.or(Bool.not(El.Quan.live(z0)), El.Eval.vals(ds, z2, False{})), ok)
          +er = Equal.trans(Maybe<Bk.Term>, El.Eval.redex(ds, z0, z1, z2), El.Eval.call(ds, Bk.Term.App{z0, z1, z2}), None{},
            redex.call(ds, z1, z0, z2, hg),
            call.none(El.Eval.vals(ds, Bk.Term.App{z0, z1, z2}, True{}), El.Eval.callWalk(ds, Bk.Term.App{z0, z1, z2}), hw))
          app.none(z0, z1, z2, El.Eval.step(ds, z1), El.Eval.vals(ds, z1, False{}), El.Quan.live(z0), El.Eval.step(ds, z2), El.Eval.vals(ds, z2, False{}),
            El.Eval.redex(ds, z0, z1, z2), stops(z1, True{}, ds, [El.Arg{z0, z2}], (hg, hw)), hx, e => stops(z2, False{}, ds, Nil{}, e), er)
        case True{}:
          (+ht, +hw) = h
          +hg = and.l(El.Eval.vals(ds, z1, True{}), Bool.or(Bool.not(El.Quan.live(z0)), El.Eval.vals(ds, z2, False{})), ht)
          +hx = and.r(El.Eval.vals(ds, z1, True{}), Bool.or(Bool.not(El.Quan.live(z0)), El.Eval.vals(ds, z2, False{})), ht)
          +er = Equal.trans(Maybe<Bk.Term>, El.Eval.redex(ds, z0, z1, z2), El.Eval.call(ds, Bk.Term.App{z0, z1, z2}), None{},
            redex.call(ds, z1, z0, z2, hg),
            call.none(El.Eval.vals(ds, Bk.Term.App{z0, z1, z2}, True{}), El.Eval.callWalk(ds, Bk.Term.App{z0, z1, z2}), cw.back(ds, Bk.Term.App{z0, z1, z2}, acc, hw)))
          app.none(z0, z1, z2, El.Eval.step(ds, z1), El.Eval.vals(ds, z1, False{}), El.Quan.live(z0), El.Eval.step(ds, z2), El.Eval.vals(ds, z2, False{}),
            El.Eval.redex(ds, z0, z1, z2), stops(z1, True{}, ds, Con{El.Arg{z0, z2}, acc}, (hg, hw)), hx, e => stops(z2, False{}, ds, Nil{}, e), er)
    case Bk.Term.Sig{+z0, +z1, +z2}:
      match a:
        case False{}:
          {==}
        case True{}:
          (ht, hw) = h
          D.bool.ft({El.Eval.step(ds, Bk.Term.Sig{z0, z1, z2}) == None{} : Maybe<Bk.Term>}, ht)
    case Bk.Term.Tup{+z0, +z1, +z2}:
      match a:
        case False{}:
          +hx = and.l(Bool.or(Bool.not(El.Quan.live(z0)), El.Eval.vals(ds, z1, False{})), El.Eval.vals(ds, z2, False{}), h)
          +hb = and.r(Bool.or(Bool.not(El.Quan.live(z0)), El.Eval.vals(ds, z1, False{})), El.Eval.vals(ds, z2, False{}), h)
          tup.none(z0, z1, z2, El.Quan.live(z0), El.Eval.step(ds, z1), El.Eval.vals(ds, z1, False{}), El.Eval.step(ds, z2), hx,
            e => stops(z1, False{}, ds, Nil{}, e), stops(z2, False{}, ds, Nil{}, hb))
        case True{}:
          (ht, hw) = h
          D.bool.ft({El.Eval.step(ds, Bk.Term.Tup{z0, z1, z2}) == None{} : Maybe<Bk.Term>}, ht)
    case Bk.Term.Prj{+z0}:
      match a:
        case False{}:
          {==}
        case True{}:
          (ht, hw) = h
          D.bool.ft({El.Eval.step(ds, Bk.Term.Prj{z0}) == None{} : Maybe<Bk.Term>}, ht)
    case Bk.Term.Enu{+z0}:
      match a:
        case False{}:
          {==}
        case True{}:
          (ht, hw) = h
          D.bool.ft({El.Eval.step(ds, Bk.Term.Enu{z0}) == None{} : Maybe<Bk.Term>}, ht)
    case Bk.Term.Lab{+z0}:
      match a:
        case False{}:
          {==}
        case True{}:
          (ht, hw) = h
          D.bool.ft({El.Eval.step(ds, Bk.Term.Lab{z0}) == None{} : Maybe<Bk.Term>}, ht)
    case Bk.Term.Mat{+z0, +z1, +z2}:
      match a:
        case False{}:
          {==}
        case True{}:
          (ht, hw) = h
          D.bool.ft({El.Eval.step(ds, Bk.Term.Mat{z0, z1, z2}) == None{} : Maybe<Bk.Term>}, ht)
    case Bk.Term.Efq{}:
      match a:
        case False{}:
          {==}
        case True{}:
          (ht, hw) = h
          D.bool.ft({El.Eval.step(ds, Bk.Term.Efq{}) == None{} : Maybe<Bk.Term>}, ht)
    case Bk.Term.Eql{+z0, +z1, +z2}:
      match a:
        case False{}:
          {==}
        case True{}:
          (ht, hw) = h
          D.bool.ft({El.Eval.step(ds, Bk.Term.Eql{z0, z1, z2}) == None{} : Maybe<Bk.Term>}, ht)
    case Bk.Term.Rfl{}:
      match a:
        case False{}:
          {==}
        case True{}:
          (ht, hw) = h
          D.bool.ft({El.Eval.step(ds, Bk.Term.Rfl{}) == None{} : Maybe<Bk.Term>}, ht)
    case Bk.Term.Rwt{+z0, +z1, +z2}:
      match a:
        case False{}:
          D.bool.ft({El.Eval.step(ds, Bk.Term.Rwt{z0, z1, z2}) == None{} : Maybe<Bk.Term>}, h)
        case True{}:
          (ht, hw) = h
          D.bool.ft({El.Eval.step(ds, Bk.Term.Rwt{z0, z1, z2}) == None{} : Maybe<Bk.Term>}, ht)

# a value has no step (Lean's eval_value)
def ev.stops(+ds: List<&2, Bk.Def>, +t: Bk.Term, h: {El.Eval.vals(ds, t, False{}) == True{} : Bool}) ->
  {El.Eval.step(ds, t) == None{} : Maybe<Bk.Term>}:
  stops(t, False{}, ds, Nil{}, h)


# A stuck focus makes its frames' term stuck
# ------------------------------------------

# Rwt e P f, Min a b and Let q v f, with a first part that has no step and is
# no value, have no step
def rwt.none(+e: Bk.Term, +p: Bk.Term, +f: Bk.Term, se: Maybe<Bk.Term>, ve: Bool, ese: {se == None{} : Maybe<Bk.Term>},
  eve: {ve == False{} : Bool}) -> {El.Eval.step.rwt(e, p, f, se, ve) == None{} : Maybe<Bk.Term>}:
  match se:
    case Some{+e2}:
      Empty.absurd({El.Eval.step.rwt(e, p, f, Some{e2}, ve) == None{} : Maybe<Bk.Term>}, sm.ne(e2, ese))
    case None{}:
      match ve:
        case True{}:
          D.bool.ft({El.Eval.step.rwt(e, p, f, None{}, True{}) == None{} : Maybe<Bk.Term>}, Equal.sym(Bool, True{}, False{}, eve))
        case False{}:
          {==}

def min.none(+a: Bk.Term, +b: Bk.Term, sa: Maybe<Bk.Term>, va: Bool, sb: Maybe<Bk.Term>, +vb: Bool, mt: Maybe<Bk.Term>,
  esa: {sa == None{} : Maybe<Bk.Term>}, eva: {va == False{} : Bool}) -> {El.Eval.step.min(a, b, sa, va, sb, vb, mt) == None{} : Maybe<Bk.Term>}:
  match sa:
    case Some{+a2}:
      Empty.absurd({El.Eval.step.min(a, b, Some{a2}, va, sb, vb, mt) == None{} : Maybe<Bk.Term>}, sm.ne(a2, esa))
    case None{}:
      match va:
        case True{}:
          D.bool.ft({El.Eval.step.min(a, b, None{}, True{}, sb, vb, mt) == None{} : Maybe<Bk.Term>}, Equal.sym(Bool, True{}, False{}, eva))
        case False{}:
          {==}

# Min a b, with a value a with no step and a b with no step that is no value
def min.none2(+a: Bk.Term, +b: Bk.Term, sa: Maybe<Bk.Term>, va: Bool, sb: Maybe<Bk.Term>, vb: Bool, mt: Maybe<Bk.Term>,
  esa: {sa == None{} : Maybe<Bk.Term>}, eva: {va == True{} : Bool}, esb: {sb == None{} : Maybe<Bk.Term>}, evb: {vb == False{} : Bool}) ->
  {El.Eval.step.min(a, b, sa, va, sb, vb, mt) == None{} : Maybe<Bk.Term>}:
  match sa:
    case Some{+a2}:
      Empty.absurd({El.Eval.step.min(a, b, Some{a2}, va, sb, vb, mt) == None{} : Maybe<Bk.Term>}, sm.ne(a2, esa))
    case None{}:
      match va:
        case False{}:
          {==}
        case True{}:
          match sb:
            case Some{+b2}:
              Empty.absurd({El.Eval.step.min(a, b, None{}, True{}, Some{b2}, vb, mt) == None{} : Maybe<Bk.Term>}, sm.ne(b2, esb))
            case None{}:
              match vb:
                case True{}:
                  D.bool.ft({El.Eval.step.min(a, b, None{}, True{}, None{}, True{}, mt) == None{} : Maybe<Bk.Term>}, Equal.sym(Bool, True{}, False{}, evb))
                case False{}:
                  {==}

def let.none(+q: Bk.Quan, +v: Bk.Term, +f: Bk.Term, live: Bool, sv: Maybe<Bk.Term>, vv: Bool, +fits: Bool, el: {live == True{} : Bool},
  esv: {sv == None{} : Maybe<Bk.Term>}, evv: {vv == False{} : Bool}) -> {El.Eval.step.let(q, v, f, live, sv, vv, fits) == None{} : Maybe<Bk.Term>}:
  match live:
    case False{}:
      D.bool.ft({El.Eval.step.let(q, v, f, False{}, sv, vv, fits) == None{} : Maybe<Bk.Term>}, el)
    case True{}:
      match sv:
        case Some{+v2}:
          Empty.absurd({El.Eval.step.let(q, v, f, True{}, Some{v2}, vv, fits) == None{} : Maybe<Bk.Term>}, sm.ne(v2, esv))
        case None{}:
          match vv:
            case True{}:
              D.bool.ft({El.Eval.step.let(q, v, f, True{}, None{}, True{}, fits) == None{} : Maybe<Bk.Term>}, Equal.sym(Bool, True{}, False{}, evv))
            case False{}:
              {==}

# Tup q a b, q live, with an a with no step that is no value
def tupb.none(+q: Bk.Quan, +a: Bk.Term, +b: Bk.Term, live: Bool, sa: Maybe<Bk.Term>, va: Bool, sb: Maybe<Bk.Term>, el: {live == True{} : Bool},
  esa: {sa == None{} : Maybe<Bk.Term>}, eva: {va == False{} : Bool}) -> {El.Eval.step.tup(q, a, b, live, sa, va, sb) == None{} : Maybe<Bk.Term>}:
  match live:
    case False{}:
      D.bool.ft({El.Eval.step.tup(q, a, b, False{}, sa, va, sb) == None{} : Maybe<Bk.Term>}, el)
    case True{}:
      match sa:
        case Some{+a2}:
          Empty.absurd({El.Eval.step.tup(q, a, b, True{}, Some{a2}, va, sb) == None{} : Maybe<Bk.Term>}, sm.ne(a2, esa))
        case None{}:
          match va:
            case True{}:
              D.bool.ft({El.Eval.step.tup(q, a, b, True{}, None{}, True{}, sb) == None{} : Maybe<Bk.Term>}, Equal.sym(Bool, True{}, False{}, eva))
            case False{}:
              {==}

# App q f x, with an f with no step that is no value
def appf.none(+q: Bk.Quan, +f: Bk.Term, +x: Bk.Term, sf: Maybe<Bk.Term>, vf: Bool, +live: Bool, sx: Maybe<Bk.Term>, +vx: Bool, r: Maybe<Bk.Term>,
  esf: {sf == None{} : Maybe<Bk.Term>}, evf: {vf == False{} : Bool}) -> {El.Eval.step.app(q, f, x, sf, vf, live, sx, vx, r) == None{} : Maybe<Bk.Term>}:
  match sf:
    case Some{+f2}:
      Empty.absurd({El.Eval.step.app(q, f, x, Some{f2}, vf, live, sx, vx, r) == None{} : Maybe<Bk.Term>}, sm.ne(f2, esf))
    case None{}:
      match vf:
        case True{}:
          D.bool.ft({El.Eval.step.app(q, f, x, None{}, True{}, live, sx, vx, r) == None{} : Maybe<Bk.Term>}, Equal.sym(Bool, True{}, False{}, evf))
        case False{}:
          {==}

# App q f x, with a live q, a value f with no step and an x with no step that
# is no value
def appx.none(+q: Bk.Quan, +f: Bk.Term, +x: Bk.Term, sf: Maybe<Bk.Term>, vf: Bool, live: Bool, sx: Maybe<Bk.Term>, vx: Bool, r: Maybe<Bk.Term>,
  el: {live == True{} : Bool}, esf: {sf == None{} : Maybe<Bk.Term>}, esx: {sx == None{} : Maybe<Bk.Term>},
  evx: {vx == False{} : Bool}) -> {El.Eval.step.app(q, f, x, sf, vf, live, sx, vx, r) == None{} : Maybe<Bk.Term>}:
  match sf:
    case Some{+f2}:
      Empty.absurd({El.Eval.step.app(q, f, x, Some{f2}, vf, live, sx, vx, r) == None{} : Maybe<Bk.Term>}, sm.ne(f2, esf))
    case None{}:
      match vf:
        case False{}:
          {==}
        case True{}:
          match live:
            case False{}:
              D.bool.ft({El.Eval.step.app(q, f, x, None{}, True{}, False{}, sx, vx, r) == None{} : Maybe<Bk.Term>}, el)
            case True{}:
              match sx:
                case Some{+x2}:
                  Empty.absurd({El.Eval.step.app(q, f, x, None{}, True{}, True{}, Some{x2}, vx, r) == None{} : Maybe<Bk.Term>}, sm.ne(x2, esx))
                case None{}:
                  match vx:
                    case True{}:
                      D.bool.ft({El.Eval.step.app(q, f, x, None{}, True{}, True{}, None{}, True{}, r) == None{} : Maybe<Bk.Term>}, Equal.sym(Bool, True{}, False{}, evx))
                    case False{}:
                      {==}


# the stuck facts of a term
def Stk(+ds: List<&2, Bk.Def>, t: Bk.Term) -> Data:
  D.P2({El.Eval.step(ds, t) == None{} : Maybe<Bk.Term>}, {El.Eval.vals(ds, t, False{}) == False{} : Bool})

# App q u a is no value, when u is none
def vapp.f(b: Bool, +ds: List<&2, Bk.Def>, +q: Bk.Quan, +u: Bk.Term, +a: Bk.Term, +eb: {El.Eval.vals(ds, u, True{}) == b : Bool},
  hv: {El.Eval.vals(ds, u, False{}) == False{} : Bool}) -> {El.Eval.vals(ds, Bk.Term.App{q, u, a}, False{}) == False{} : Bool}:
  match b:
    case False{}:
      %Equal.sym(Bool, El.Eval.vals(ds, u, True{}), False{}, eb) :
        {Bool.and(Bool.and(_, Bool.or(Bool.not(El.Quan.live(q)), El.Eval.vals(ds, a, False{}))), El.Eval.waits(El.Eval.callWalk(ds, Bk.Term.App{q, u, a}))) == False{} : Bool}
      {==}
    case True{}:
      +ew = Equal.trans(Bool, El.Eval.waits(El.Eval.callWalk(ds, u)), El.Eval.vals(ds, u, False{}), False{},
        Equal.sym(Bool, El.Eval.vals(ds, u, False{}), El.Eval.waits(El.Eval.callWalk(ds, u)), vals.tf(ds, u, eb)), hv)
      %Equal.sym(Bool, El.Eval.vals(ds, u, True{}), True{}, eb) :
        {Bool.and(Bool.and(_, Bool.or(Bool.not(El.Quan.live(q)), El.Eval.vals(ds, a, False{}))), El.Eval.waits(El.Eval.callWalk(ds, Bk.Term.App{q, u, a}))) == False{} : Bool}
      and.f(Bool.or(Bool.not(El.Quan.live(q)), El.Eval.vals(ds, a, False{})), El.Eval.waits(El.Eval.callWalk(ds, Bk.Term.App{q, u, a})), cw.app(ds, u, q, a, ew))

# App q a u, with q live, is no value when u is none
def vfun.f(l: Bool, va: Bool, vu: Bool, +w: Bool, el: {l == True{} : Bool}, ev: {vu == False{} : Bool}) ->
  {Bool.and(Bool.and(va, Bool.or(Bool.not(l), vu)), w) == False{} : Bool}:
  match l:
    case False{}:
      D.bool.ft({Bool.and(Bool.and(va, Bool.or(Bool.not(False{}), vu)), w) == False{} : Bool}, el)
    case True{}:
      match va:
        case True{}:
          match vu:
            case True{}:
              D.bool.ft({Bool.and(Bool.and(True{}, Bool.or(Bool.not(True{}), True{})), w) == False{} : Bool}, Equal.sym(Bool, True{}, False{}, ev))
            case False{}:
              {==}
        case False{}:
          {==}

# Tup q u a, q live, is no value when u is none
def vtup.f(l: Bool, vu: Bool, +vb: Bool, el: {l == True{} : Bool}, ev: {vu == False{} : Bool}) ->
  {Bool.and(Bool.or(Bool.not(l), vu), vb) == False{} : Bool}:
  match l:
    case False{}:
      D.bool.ft({Bool.and(Bool.or(Bool.not(False{}), vu), vb) == False{} : Bool}, el)
    case True{}:
      match vu:
        case True{}:
          D.bool.ft({Bool.and(Bool.or(Bool.not(True{}), True{}), vb) == False{} : Bool}, Equal.sym(Bool, True{}, False{}, ev))
        case False{}:
          {==}

# one frame around a focus with no step that is no value
def stuck1(+ds: List<&2, Bk.Def>, fr: D.AF, +u: Bk.Term, +ok: D.AF.ok(ds, fr),
  +hs: {El.Eval.step(ds, u) == None{} : Maybe<Bk.Term>}, +hv: {El.Eval.vals(ds, u, False{}) == False{} : Bool}) ->
  Stk(ds, D.A.plug(fr, u)):
  match fr:
    case D.AF{+kind, +q, +k, +a, +b}:
      match kind:
        case D.FK.arg{}:
          (appf.none(q, u, a, El.Eval.step(ds, u), El.Eval.vals(ds, u, False{}), El.Quan.live(q), El.Eval.step(ds, a), El.Eval.vals(ds, a, False{}),
            El.Eval.redex(ds, q, u, a), hs, hv),
           vapp.f(El.Eval.vals(ds, u, True{}), ds, q, u, a, {==}, hv))
        case D.FK.val{}:
          (appf.none(q, u, a, El.Eval.step(ds, u), El.Eval.vals(ds, u, False{}), El.Quan.live(q), El.Eval.step(ds, a), El.Eval.vals(ds, a, False{}),
            El.Eval.redex(ds, q, u, a), hs, hv),
           vapp.f(El.Eval.vals(ds, u, True{}), ds, q, u, a, {==}, hv))
        case D.FK.fun{}:
          +el = and.l(El.Quan.live(q), El.Eval.vals(ds, a, False{}), ok)
          +ea = and.r(El.Quan.live(q), El.Eval.vals(ds, a, False{}), ok)
          (appx.none(q, a, u, El.Eval.step(ds, a), El.Eval.vals(ds, a, False{}), El.Quan.live(q), El.Eval.step(ds, u), El.Eval.vals(ds, u, False{}),
            El.Eval.redex(ds, q, a, u), el, ev.stops(ds, a, ea), hs, hv),
           vfun.f(El.Quan.live(q), El.Eval.vals(ds, a, True{}), El.Eval.vals(ds, u, False{}), El.Eval.waits(El.Eval.callWalk(ds, Bk.Term.App{q, a, u})), el, hv))
        case D.FK.let{}:
          (let.none(q, u, a, El.Quan.live(q), El.Eval.step(ds, u), El.Eval.vals(ds, u, False{}), El.Quan.fits(q, u), ok, hs, hv), {==})
        case D.FK.tupb{}:
          (tupb.none(q, u, a, El.Quan.live(q), El.Eval.step(ds, u), El.Eval.vals(ds, u, False{}), El.Eval.step(ds, a), ok, hs, hv),
           vtup.f(El.Quan.live(q), El.Eval.vals(ds, u, False{}), El.Eval.vals(ds, a, False{}), ok, hv))
        case D.FK.tupa{}:
          (tup.none(q, a, u, El.Quan.live(q), El.Eval.step(ds, a), El.Eval.vals(ds, a, False{}), El.Eval.step(ds, u), ok, e => ev.stops(ds, a, e), hs),
           and.f(Bool.or(Bool.not(El.Quan.live(q)), El.Eval.vals(ds, a, False{})), El.Eval.vals(ds, u, False{}), hv))
        case D.FK.rwt{}:
          (rwt.none(u, a, b, El.Eval.step(ds, u), El.Eval.vals(ds, u, False{}), hs, hv), {==})
        case D.FK.minb{}:
          (min.none(u, a, El.Eval.step(ds, u), El.Eval.vals(ds, u, False{}), El.Eval.step(ds, a), El.Eval.vals(ds, a, False{}), El.Eval.meet(u, a), hs, hv), {==})
        case D.FK.mina{}:
          (min.none2(a, u, El.Eval.step(ds, a), El.Eval.vals(ds, a, False{}), El.Eval.step(ds, u), El.Eval.vals(ds, u, False{}), El.Eval.meet(a, u),
            ev.stops(ds, a, ok), ok, hs, hv), {==})

def ev.stuck.go(+ds: List<&2, Bk.Def>, fs: List<&2, D.AF>, +u: Bk.Term, hfs: D.AFs.ok(ds, fs), st: Stk(ds, u)) ->
  Stk(ds, D.A.plugs(fs, u)):
  match fs:
    case Nil{}:
      st
    case Con{+fr, +rest}:
      (ok, oks) = hfs
      (hs, hv) = st
      ev.stuck.go(ds, rest, D.A.plug(fr, u), oks, stuck1(ds, fr, u, ok, hs, hv))

# a focus with no step that is no value makes its frames' term so
def ev.stuck(+ds: List<&2, Bk.Def>, fs: List<&2, D.AF>, +u: Bk.Term, hfs: D.AFs.ok(ds, fs),
  hs: {El.Eval.step(ds, u) == None{} : Maybe<Bk.Term>}, hv: {El.Eval.vals(ds, u, False{}) == False{} : Bool}) ->
  Stk(ds, D.A.plugs(fs, u)):
  ev.stuck.go(ds, fs, u, hfs, (hs, hv))
