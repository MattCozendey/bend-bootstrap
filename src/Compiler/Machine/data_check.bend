# compiler: the data check of the machine (layer B)
# ===================================================
#
# data.post and data.done of moves.bend (PM.DataPost, PM.DataDone), for
# M.data of impl.bend's Machine.
#
# The check's stack is a chain of K.check cells from register ds. Each one
# holds, in field 2, the cell of a part of v: the cell that a path of pair
# fields from c reaches (Cl), whose term is the path's part of v (Sub). A
# path from c keeps its cells across the run: M.alloc keeps each cell out of
# the pend list (AlFr), and the other stores are to K.check cells or set the
# flag DATA.
#
# When v is Data, every part on the stack is Data (data.sub), so each flag
# that the check sets is true (data.flag) and HS holds throughout. When it is
# not, the run goes on under HSK(False) and a witness says the check fails:
# a path to a part of v that is not Data, and on to a cell that is not a
# pair, a label or Rfl, all of its cells unflagged, the first on the stack.

import Base
import ../../Book/impl.bend as Bk
import ../../Eval/impl.bend as El
import ../Cir/impl.bend as Cr
import ./cell_terms.bend as T
import ../need_big.bend as N
import ./definitions.bend as PM
import ./statement_runs.bend as X
import ./move_kit.bend as K
import ./data_walk.bend as W

# Kit
# ---

def mt.get(x: Maybe<&2, Bk.Term>, d: Bk.Term) -> Bk.Term:
  match x:
    case None{}:
      d
    case Some{y}:
      y

def mt.inj(+a: Bk.Term, -b: Bk.Term, e: {Some{a} == Some{b} : Maybe<&2, Bk.Term>}) -> {a == b : Bk.Term}:
  Equal.cong(Maybe<&2, Bk.Term>, Bk.Term, x => mt.get(x, a), Some{a}, Some{b}, e)

def mt.ms(x: Maybe<&2, Bk.Term>) -> Type:
  match x:
    case None{}:
      Unit
    case Some{_}:
      Empty

def mt.ne(-u: Bk.Term, e: {None{} == Some{u} : Maybe<&2, Bk.Term>}) -> Empty:
  %e : mt.ms(_)
  Unit{}

# Paths
# -----

# the cell that the path p of pair fields reaches from c: True for field 2
# (the first field), False for field 3 (the second)
def Cl(+m: Cr.Cir.Cells, p: List<&2, Bool>, +c: U32) -> U32:
  match p:
    case Nil{}:
      c
    case Con{True{}, rest}:
      Cl(m, rest, PM.Fd(2n, m, c))
    case Con{False{}, rest}:
      Cl(m, rest, PM.Fd(3n, m, c))

def Sub.a(l: Bool, r: Maybe<&2, Bk.Term>) -> Maybe<&2, Bk.Term>:
  match l:
    case True{}:
      r
    case False{}:
      None{}

# the part of v at the path p: through pairs only, and through a first field
# only when it is live
def Sub(p: List<&2, Bool>, v: Bk.Term) -> Maybe<&2, Bk.Term>:
  match p v:
    case Nil{} x:
      Some{x}
    case Con{True{}, rest} Bk.Term.Tup{q, a, b}:
      Sub.a(El.Quan.live(q), Sub(rest, a))
    case Con{False{}, rest} Bk.Term.Tup{q, a, b}:
      Sub(rest, b)
    case Con{_, _} _:
      None{}

# a first field on a path is live
def sub.l(l: Bool, -rest: List<&2, Bool>, -a: Bk.Term, -u: Bk.Term, -G: Type, e: {Sub.a(l, Sub(rest, a)) == Some{u} : Maybe<&2, Bk.Term>},
  k: {l == True{} : Bool} -> {Sub(rest, a) == Some{u} : Maybe<&2, Bk.Term>} -> G) -> G:
  match l:
    case True{}:
      k({==}, e)
    case False{}:
      Empty.absurd(G, mt.ne(u, e))

# the cell at a path of v's cell stands for v's part there
def is.sub(+dk: Bool, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, p: List<&2, Bool>, v: Bk.Term, +c: U32, -u: Bk.Term,
  h: PM.IsK(dk, ds, m, im, fi, nx, ks, img, c, v), e: {Sub(p, v) == Some{u} : Maybe<&2, Bk.Term>}) ->
  PM.IsK(dk, ds, m, im, fi, nx, ks, img, Cl(m, p, c), u):
  match p v:
    case Nil{} +x:
      %mt.inj(x, u, e) : PM.IsK(dk, ds, m, im, fi, nx, ks, img, c, _)
      h
    case Con{True{}, +rest} Bk.Term.Tup{+q, +a, +b}:
      (nd, r1) = h
      (hq, r2) = r1
      (pa, pb) = r2
      (spa, ia) = pa
      sub.l(El.Quan.live(q), rest, a, u, PM.IsK(dk, ds, m, im, fi, nx, ks, img, Cl(m, rest, PM.Fd(2n, m, c)), u), e,
        el => e2 => is.sub(dk, ds, m, im, fi, nx, ks, img, rest, a, PM.Fd(2n, m, c), u, ia, e2))
    case Con{False{}, rest} Bk.Term.Tup{+q, +a, +b}:
      (nd, r1) = h
      (hq, r2) = r1
      (pa, pb) = r2
      (spb, ib) = pb
      is.sub(dk, ds, m, im, fi, nx, ks, img, rest, b, PM.Fd(3n, m, c), u, ib, e)
    case Con{d, rest} Bk.Term.Var{+o0}:
      Empty.absurd(PM.IsK(dk, ds, m, im, fi, nx, ks, img, Cl(m, Con{d, rest}, c), u), mt.ne(u, e))
    case Con{d, rest} Bk.Term.Ref{+o0}:
      Empty.absurd(PM.IsK(dk, ds, m, im, fi, nx, ks, img, Cl(m, Con{d, rest}, c), u), mt.ne(u, e))
    case Con{d, rest} Bk.Term.Ann{+o0, +o1}:
      Empty.absurd(PM.IsK(dk, ds, m, im, fi, nx, ks, img, Cl(m, Con{d, rest}, c), u), mt.ne(u, e))
    case Con{d, rest} Bk.Term.Let{+o0, +o1, +o2}:
      Empty.absurd(PM.IsK(dk, ds, m, im, fi, nx, ks, img, Cl(m, Con{d, rest}, c), u), mt.ne(u, e))
    case Con{d, rest} Bk.Term.Typ{+o0}:
      Empty.absurd(PM.IsK(dk, ds, m, im, fi, nx, ks, img, Cl(m, Con{d, rest}, c), u), mt.ne(u, e))
    case Con{d, rest} Bk.Term.Min{+o0, +o1}:
      Empty.absurd(PM.IsK(dk, ds, m, im, fi, nx, ks, img, Cl(m, Con{d, rest}, c), u), mt.ne(u, e))
    case Con{d, rest} Bk.Term.All{+o0, +o1, +o2}:
      Empty.absurd(PM.IsK(dk, ds, m, im, fi, nx, ks, img, Cl(m, Con{d, rest}, c), u), mt.ne(u, e))
    case Con{d, rest} Bk.Term.Lam{+o0, +o1}:
      Empty.absurd(PM.IsK(dk, ds, m, im, fi, nx, ks, img, Cl(m, Con{d, rest}, c), u), mt.ne(u, e))
    case Con{d, rest} Bk.Term.App{+o0, +o1, +o2}:
      Empty.absurd(PM.IsK(dk, ds, m, im, fi, nx, ks, img, Cl(m, Con{d, rest}, c), u), mt.ne(u, e))
    case Con{d, rest} Bk.Term.Sig{+o0, +o1, +o2}:
      Empty.absurd(PM.IsK(dk, ds, m, im, fi, nx, ks, img, Cl(m, Con{d, rest}, c), u), mt.ne(u, e))
    case Con{d, rest} Bk.Term.Prj{+o0}:
      Empty.absurd(PM.IsK(dk, ds, m, im, fi, nx, ks, img, Cl(m, Con{d, rest}, c), u), mt.ne(u, e))
    case Con{d, rest} Bk.Term.Enu{+o0}:
      Empty.absurd(PM.IsK(dk, ds, m, im, fi, nx, ks, img, Cl(m, Con{d, rest}, c), u), mt.ne(u, e))
    case Con{d, rest} Bk.Term.Lab{+o0}:
      Empty.absurd(PM.IsK(dk, ds, m, im, fi, nx, ks, img, Cl(m, Con{d, rest}, c), u), mt.ne(u, e))
    case Con{d, rest} Bk.Term.Mat{+o0, +o1, +o2}:
      Empty.absurd(PM.IsK(dk, ds, m, im, fi, nx, ks, img, Cl(m, Con{d, rest}, c), u), mt.ne(u, e))
    case Con{d, rest} Bk.Term.Efq{}:
      Empty.absurd(PM.IsK(dk, ds, m, im, fi, nx, ks, img, Cl(m, Con{d, rest}, c), u), mt.ne(u, e))
    case Con{d, rest} Bk.Term.Eql{+o0, +o1, +o2}:
      Empty.absurd(PM.IsK(dk, ds, m, im, fi, nx, ks, img, Cl(m, Con{d, rest}, c), u), mt.ne(u, e))
    case Con{d, rest} Bk.Term.Rfl{}:
      Empty.absurd(PM.IsK(dk, ds, m, im, fi, nx, ks, img, Cl(m, Con{d, rest}, c), u), mt.ne(u, e))
    case Con{d, rest} Bk.Term.Rwt{+o0, +o1, +o2}:
      Empty.absurd(PM.IsK(dk, ds, m, im, fi, nx, ks, img, Cl(m, Con{d, rest}, c), u), mt.ne(u, e))

# a path, then another
def cl.app(+m: Cr.Cir.Cells, p: List<&2, Bool>, +s: List<&2, Bool>, +c: U32) ->
  {Cl(m, List.append(&2, Bool, p, s), c) == Cl(m, s, Cl(m, p, c)) : U32}:
  match p:
    case Nil{}:
      {==}
    case Con{True{}, rest}:
      cl.app(m, rest, s, PM.Fd(2n, m, c))
    case Con{False{}, rest}:
      cl.app(m, rest, s, PM.Fd(3n, m, c))

def sub.app(p: List<&2, Bool>, v: Bk.Term, +s: List<&2, Bool>, -u: Bk.Term, e: {Sub(p, v) == Some{u} : Maybe<&2, Bk.Term>}) ->
  {Sub(List.append(&2, Bool, p, s), v) == Sub(s, u) : Maybe<&2, Bk.Term>}:
  match p v:
    case Nil{} +x:
      %mt.inj(x, u, e) : {Sub(s, x) == Sub(s, _) : Maybe<&2, Bk.Term>}
      {==}
    case Con{True{}, +rest} Bk.Term.Tup{+q, +a, +b}:
      sub.l(El.Quan.live(q), rest, a, u, {Sub(List.append(&2, Bool, Con{True{}, rest}, s), Bk.Term.Tup{q, a, b}) == Sub(s, u) : Maybe<&2, Bk.Term>}, e,
        el => e2 => (%Equal.sym(Bool, El.Quan.live(q), True{}, el) : {Sub.a(_, Sub(List.append(&2, Bool, rest, s), a)) == Sub(s, u) : Maybe<&2, Bk.Term>}; sub.app(rest, a, s, u, e2)))
    case Con{False{}, rest} Bk.Term.Tup{+q, +a, +b}:
      sub.app(rest, b, s, u, e)
    case Con{d, rest} Bk.Term.Var{+o0}:
      Empty.absurd({Sub(List.append(&2, Bool, Con{d, rest}, s), Bk.Term.Var{o0}) == Sub(s, u) : Maybe<&2, Bk.Term>}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Ref{+o0}:
      Empty.absurd({Sub(List.append(&2, Bool, Con{d, rest}, s), Bk.Term.Ref{o0}) == Sub(s, u) : Maybe<&2, Bk.Term>}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Ann{+o0, +o1}:
      Empty.absurd({Sub(List.append(&2, Bool, Con{d, rest}, s), Bk.Term.Ann{o0, o1}) == Sub(s, u) : Maybe<&2, Bk.Term>}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Let{+o0, +o1, +o2}:
      Empty.absurd({Sub(List.append(&2, Bool, Con{d, rest}, s), Bk.Term.Let{o0, o1, o2}) == Sub(s, u) : Maybe<&2, Bk.Term>}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Typ{+o0}:
      Empty.absurd({Sub(List.append(&2, Bool, Con{d, rest}, s), Bk.Term.Typ{o0}) == Sub(s, u) : Maybe<&2, Bk.Term>}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Min{+o0, +o1}:
      Empty.absurd({Sub(List.append(&2, Bool, Con{d, rest}, s), Bk.Term.Min{o0, o1}) == Sub(s, u) : Maybe<&2, Bk.Term>}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.All{+o0, +o1, +o2}:
      Empty.absurd({Sub(List.append(&2, Bool, Con{d, rest}, s), Bk.Term.All{o0, o1, o2}) == Sub(s, u) : Maybe<&2, Bk.Term>}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Lam{+o0, +o1}:
      Empty.absurd({Sub(List.append(&2, Bool, Con{d, rest}, s), Bk.Term.Lam{o0, o1}) == Sub(s, u) : Maybe<&2, Bk.Term>}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.App{+o0, +o1, +o2}:
      Empty.absurd({Sub(List.append(&2, Bool, Con{d, rest}, s), Bk.Term.App{o0, o1, o2}) == Sub(s, u) : Maybe<&2, Bk.Term>}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Sig{+o0, +o1, +o2}:
      Empty.absurd({Sub(List.append(&2, Bool, Con{d, rest}, s), Bk.Term.Sig{o0, o1, o2}) == Sub(s, u) : Maybe<&2, Bk.Term>}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Prj{+o0}:
      Empty.absurd({Sub(List.append(&2, Bool, Con{d, rest}, s), Bk.Term.Prj{o0}) == Sub(s, u) : Maybe<&2, Bk.Term>}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Enu{+o0}:
      Empty.absurd({Sub(List.append(&2, Bool, Con{d, rest}, s), Bk.Term.Enu{o0}) == Sub(s, u) : Maybe<&2, Bk.Term>}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Lab{+o0}:
      Empty.absurd({Sub(List.append(&2, Bool, Con{d, rest}, s), Bk.Term.Lab{o0}) == Sub(s, u) : Maybe<&2, Bk.Term>}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Mat{+o0, +o1, +o2}:
      Empty.absurd({Sub(List.append(&2, Bool, Con{d, rest}, s), Bk.Term.Mat{o0, o1, o2}) == Sub(s, u) : Maybe<&2, Bk.Term>}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Efq{}:
      Empty.absurd({Sub(List.append(&2, Bool, Con{d, rest}, s), Bk.Term.Efq{}) == Sub(s, u) : Maybe<&2, Bk.Term>}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Eql{+o0, +o1, +o2}:
      Empty.absurd({Sub(List.append(&2, Bool, Con{d, rest}, s), Bk.Term.Eql{o0, o1, o2}) == Sub(s, u) : Maybe<&2, Bk.Term>}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Rfl{}:
      Empty.absurd({Sub(List.append(&2, Bool, Con{d, rest}, s), Bk.Term.Rfl{}) == Sub(s, u) : Maybe<&2, Bk.Term>}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Rwt{+o0, +o1, +o2}:
      Empty.absurd({Sub(List.append(&2, Bool, Con{d, rest}, s), Bk.Term.Rwt{o0, o1, o2}) == Sub(s, u) : Maybe<&2, Bk.Term>}, mt.ne(u, e))

def data.fst(l: Bool, x: Bool, -y: Bool, h: {Bool.and(Bool.or(Bool.not(l), x), y) == True{} : Bool}, el: {l == True{} : Bool}) ->
  {x == True{} : Bool}:
  match l:
    case True{}:
      PM.and.l(x, y, h)
    case False{}:
      PM.bool.ft({x == True{} : Bool}, el)

# the parts of Data on a path are Data
def data.sub(p: List<&2, Bool>, v: Bk.Term, -u: Bk.Term, hv: {El.Term.is_data(v) == True{} : Bool}, e: {Sub(p, v) == Some{u} : Maybe<&2, Bk.Term>}) ->
  {El.Term.is_data(u) == True{} : Bool}:
  match p v:
    case Nil{} +x:
      %mt.inj(x, u, e) : {El.Term.is_data(_) == True{} : Bool}
      hv
    case Con{True{}, +rest} Bk.Term.Tup{+q, +a, +b}:
      sub.l(El.Quan.live(q), rest, a, u, {El.Term.is_data(u) == True{} : Bool}, e,
        el => e2 => data.sub(rest, a, u, data.fst(El.Quan.live(q), El.Term.is_data(a), El.Term.is_data(b), hv, el), e2))
    case Con{False{}, rest} Bk.Term.Tup{+q, +a, +b}:
      data.sub(rest, b, u, PM.and.r(Bool.or(Bool.not(El.Quan.live(q)), El.Term.is_data(a)), El.Term.is_data(b), hv), e)
    case Con{d, rest} Bk.Term.Var{+o0}:
      Empty.absurd({El.Term.is_data(u) == True{} : Bool}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Ref{+o0}:
      Empty.absurd({El.Term.is_data(u) == True{} : Bool}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Ann{+o0, +o1}:
      Empty.absurd({El.Term.is_data(u) == True{} : Bool}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Let{+o0, +o1, +o2}:
      Empty.absurd({El.Term.is_data(u) == True{} : Bool}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Typ{+o0}:
      Empty.absurd({El.Term.is_data(u) == True{} : Bool}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Min{+o0, +o1}:
      Empty.absurd({El.Term.is_data(u) == True{} : Bool}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.All{+o0, +o1, +o2}:
      Empty.absurd({El.Term.is_data(u) == True{} : Bool}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Lam{+o0, +o1}:
      Empty.absurd({El.Term.is_data(u) == True{} : Bool}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.App{+o0, +o1, +o2}:
      Empty.absurd({El.Term.is_data(u) == True{} : Bool}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Sig{+o0, +o1, +o2}:
      Empty.absurd({El.Term.is_data(u) == True{} : Bool}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Prj{+o0}:
      Empty.absurd({El.Term.is_data(u) == True{} : Bool}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Enu{+o0}:
      Empty.absurd({El.Term.is_data(u) == True{} : Bool}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Lab{+o0}:
      Empty.absurd({El.Term.is_data(u) == True{} : Bool}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Mat{+o0, +o1, +o2}:
      Empty.absurd({El.Term.is_data(u) == True{} : Bool}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Efq{}:
      Empty.absurd({El.Term.is_data(u) == True{} : Bool}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Eql{+o0, +o1, +o2}:
      Empty.absurd({El.Term.is_data(u) == True{} : Bool}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Rfl{}:
      Empty.absurd({El.Term.is_data(u) == True{} : Bool}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Rwt{+o0, +o1, +o2}:
      Empty.absurd({El.Term.is_data(u) == True{} : Bool}, mt.ne(u, e))

# what the cell of a term says of itself, for either dk
def isk.nd(+dk: Bool, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +c: U32, t: Bk.Term, h: PM.IsK(dk, ds, m, im, fi, nx, ks, img, c, t)) ->
  PM.NdK(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), t, PM.A.tag(t)):
  match t:
    case Bk.Term.Var{+i}:
      match h:
        case Tuple{nd, _}:
          nd
    case Bk.Term.Ref{+k}:
      match h:
        case Tuple{nd, _}:
          nd
    case Bk.Term.Ann{+x, +y}:
      match h:
        case Tuple{nd, _}:
          nd
    case Bk.Term.Let{+q, +x, +y}:
      match h:
        case Tuple{nd, _}:
          nd
    case Bk.Term.Typ{+x}:
      match h:
        case Tuple{nd, _}:
          nd
    case Bk.Term.Min{+x, +y}:
      match h:
        case Tuple{nd, _}:
          nd
    case Bk.Term.All{+q, +x, +y}:
      match h:
        case Tuple{nd, _}:
          nd
    case Bk.Term.Lam{+q, +x}:
      match h:
        case Tuple{nd, _}:
          nd
    case Bk.Term.App{+q, +x, +y}:
      match h:
        case Tuple{nd, _}:
          nd
    case Bk.Term.Sig{+q, +x, +y}:
      match h:
        case Tuple{nd, _}:
          nd
    case Bk.Term.Tup{+q, +x, +y}:
      match h:
        case Tuple{nd, _}:
          nd
    case Bk.Term.Prj{+x}:
      match h:
        case Tuple{nd, _}:
          nd
    case Bk.Term.Enu{+k}:
      match h:
        case Tuple{nd, _}:
          nd
    case Bk.Term.Lab{+k}:
      match h:
        case Tuple{nd, _}:
          nd
    case Bk.Term.Mat{+k, +x, +y}:
      match h:
        case Tuple{nd, _}:
          nd
    case Bk.Term.Efq{}:
      h
    case Bk.Term.Eql{+x, +y, +z}:
      match h:
        case Tuple{nd, _}:
          nd
    case Bk.Term.Rfl{}:
      h
    case Bk.Term.Rwt{+x, +y, +z}:
      match h:
        case Tuple{nd, _}:
          nd

def ndk.cell(-dk: Bool, -ds: List<&2, Bk.Def>, -im: U32, -fi: U32, -nx: U32, -c: U32, -x: Cr.Cir.Cell, -t: Bk.Term, -tag: U32,
  h: PM.NdK(dk, ds, im, fi, nx, c, x, t, tag)) -> {Cr.Cir.is_cell(c, im, fi, nx) == True{} : Bool}:
  (e0, r0) = h
  e0

def isk.cell(+dk: Bool, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +c: U32, +t: Bk.Term, h: PM.IsK(dk, ds, m, im, fi, nx, ks, img, c, t)) ->
  {Cr.Cir.is_cell(c, im, fi, nx) == True{} : Bool}:
  ndk.cell(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), t, PM.A.tag(t), isk.nd(dk, ds, m, im, fi, nx, ks, img, c, t, h))

def isk.tag(+dk: Bool, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +c: U32, +t: Bk.Term, h: PM.IsK(dk, ds, m, im, fi, nx, ks, img, c, t)) ->
  {PM.TgW(PM.Fd(0n, m, c)) == PM.A.tag(t) : U32}:
  PM.nd.tgk(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), t, PM.A.tag(t), isk.nd(dk, ds, m, im, fi, nx, ks, img, c, t, h))

# the parts of a pair's cell are STATIC or have a pointer
def tup.hd(+dk: Bool, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +rs: List<&2, U32>, +c: U32, +q: Bk.Quan, +a: Bk.Term, +b: Bk.Term,
  tbl: PM.Tbl(m, im, fi, nx), h: PM.IsK(dk, ds, m, im, fi, nx, ks, img, c, Bk.Term.Tup{q, a, b})) ->
  PM.P2({PM.Hd(m, nx, fi, ps, rs, PM.Fd(2n, m, c)) == True{} : Bool}, {PM.Hd(m, nx, fi, ps, rs, PM.Fd(3n, m, c)) == True{} : Bool}):
  (nd, r1) = h
  (hq, r2) = r1
  (pa, pb) = r2
  (spa, ia) = pa
  (spb, ib) = pb
  +et = PM.nd.tgk(dk, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Tup{q, a, b}, 10, nd)
  +em = PM.tbl.mask(m, im, fi, nx, Bk.Term.Tup{q, a, b}, tbl)
  (PM.part.held(PM.Own(fi, nx, c), m, nx, fi, ps, rs, c, PM.Fd(2n, m, c), {==}, spa,
     PM.hm.at(m, ps, c, 10, 3, PM.Fd(2n, m, c), et, {==}, em, PM.mem.hd(PM.Fd(2n, m, c), Con{PM.Fd(3n, m, c), Nil{}}))),
   PM.part.held(PM.Own(fi, nx, c), m, nx, fi, ps, rs, c, PM.Fd(3n, m, c), {==}, spb,
     PM.hm.at(m, ps, c, 10, 3, PM.Fd(3n, m, c), et, {==}, em, PM.mem.tl(PM.Fd(2n, m, c), PM.Fd(3n, m, c), Con{PM.Fd(3n, m, c), Nil{}}, PM.mem.hd(PM.Fd(3n, m, c), Nil{})))))

# Frames
# ------
#
# A store keeps the fields 0, 2 and 3 of the cells that a path or the
# witness reads: cells that are STATIC or have a pointer (Hd). Each store of
# the run is one of these frames (Fr), with what it needs of the cells.

# a store of field 1 or field 0 keeps the other fields
def s1.f0(c: Cr.Cir.Cell, +v: U32) -> {Cr.Cir.Cell.get(0n, Cr.Cir.Cell.set(1n, c, v)) == Cr.Cir.Cell.get(0n, c) : U32}:
  match c:
    case Cr.Cir.Cell{a, b, x, y, z}:
      {==}

def s1.f2(c: Cr.Cir.Cell, +v: U32) -> {Cr.Cir.Cell.get(2n, Cr.Cir.Cell.set(1n, c, v)) == Cr.Cir.Cell.get(2n, c) : U32}:
  match c:
    case Cr.Cir.Cell{a, b, x, y, z}:
      {==}

def s1.f3(c: Cr.Cir.Cell, +v: U32) -> {Cr.Cir.Cell.get(3n, Cr.Cir.Cell.set(1n, c, v)) == Cr.Cir.Cell.get(3n, c) : U32}:
  match c:
    case Cr.Cir.Cell{a, b, x, y, z}:
      {==}

def s0.f2(c: Cr.Cir.Cell, +v: U32) -> {Cr.Cir.Cell.get(2n, Cr.Cir.Cell.set(0n, c, v)) == Cr.Cir.Cell.get(2n, c) : U32}:
  match c:
    case Cr.Cir.Cell{a, b, x, y, z}:
      {==}

def s0.f3(c: Cr.Cir.Cell, +v: U32) -> {Cr.Cir.Cell.get(3n, Cr.Cir.Cell.set(0n, c, v)) == Cr.Cir.Cell.get(3n, c) : U32}:
  match c:
    case Cr.Cir.Cell{a, b, x, y, z}:
      {==}

# fields 2 and 3 of x kept from m to m2, and with field 0
def FC(+m: Cr.Cir.Cells, +m2: Cr.Cir.Cells, +x: U32) -> Data:
  PM.P2({PM.Fd(2n, m2, x) == PM.Fd(2n, m, x) : U32}, {PM.Fd(3n, m2, x) == PM.Fd(3n, m, x) : U32})

def FF(+m: Cr.Cir.Cells, +m2: Cr.Cir.Cells, +x: U32) -> Data:
  PM.P2({PM.Fd(0n, m2, x) == PM.Fd(0n, m, x) : U32}, FC(m, m2, x))

def FF.c(-m: Cr.Cir.Cells, -m2: Cr.Cir.Cells, -x: U32, h: FF(m, m2, x)) -> FC(m, m2, x):
  (h0, hc) = h
  hc

# a store at z keeps every other cell
def ff.go(+m: Cr.Cir.Cells, +z: U32, +y: Cr.Cir.Cell, +x: U32, h: {U32.is_eq(x, z) == False{} : Bool}) ->
  FF(m, Cr.Cir.Cells.set(m, z, y), x):
  +e = PM.cl.go(m, x, z, y, h)
  (Equal.cong(Cr.Cir.Cell, U32, w => Cr.Cir.Cell.get(0n, w), Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, y), x), Cr.Cir.Cells.get(m, x), e),
   (Equal.cong(Cr.Cir.Cell, U32, w => Cr.Cir.Cell.get(2n, w), Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, y), x), Cr.Cir.Cells.get(m, x), e),
    Equal.cong(Cr.Cir.Cell, U32, w => Cr.Cir.Cell.get(3n, w), Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, y), x), Cr.Cir.Cells.get(m, x), e)))

def ff.trans(-m: Cr.Cir.Cells, -m1: Cr.Cir.Cells, -m2: Cr.Cir.Cells, +x: U32, a: FF(m1, m2, x), b: FF(m, m1, x)) -> FF(m, m2, x):
  (a0, ac) = a
  (a2, a3) = ac
  (b0, bc) = b
  (b2, b3) = bc
  (Equal.trans(U32, PM.Fd(0n, m2, x), PM.Fd(0n, m1, x), PM.Fd(0n, m, x), a0, b0),
   (Equal.trans(U32, PM.Fd(2n, m2, x), PM.Fd(2n, m1, x), PM.Fd(2n, m, x), a2, b2),
    Equal.trans(U32, PM.Fd(3n, m2, x), PM.Fd(3n, m1, x), PM.Fd(3n, m, x), a3, b3)))

def ff.refl(+m: Cr.Cir.Cells, +x: U32) -> FF(m, m, x):
  ({==}, ({==}, {==}))

def ff.of(b: Bool, +m: Cr.Cir.Cells, +z: U32, +y: Cr.Cir.Cell, +x: U32, eb: {U32.is_eq(x, z) == b : Bool},
  ht: {b == True{} : Bool} -> FF(m, Cr.Cir.Cells.set(m, z, y), z)) -> FF(m, Cr.Cir.Cells.set(m, z, y), x):
  match b:
    case True{}:
      %Equal.sym(U32, x, z, PM.u32.eq(x, z, eb)) : FF(m, Cr.Cir.Cells.set(m, z, y), _)
      ht({==})
    case False{}:
      ff.go(m, z, y, x, eb)

# a store of field 1 keeps fields 0, 2 and 3 of every cell
def ff.put1(+m: Cr.Cir.Cells, +z: U32, +v: U32, +x: U32) -> FF(m, X.X.put(m, 1n, z, v), x):
  +y = Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, z), v)
  +gs = PM.cl.gs(m, z, y)
  ff.of(U32.is_eq(x, z), m, z, y, x, {==},
    e => (Equal.trans(U32, PM.Fd(0n, Cr.Cir.Cells.set(m, z, y), z), Cr.Cir.Cell.get(0n, y), PM.Fd(0n, m, z),
            Equal.cong(Cr.Cir.Cell, U32, w => Cr.Cir.Cell.get(0n, w), Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, y), z), y, gs),
            s1.f0(Cr.Cir.Cells.get(m, z), v)),
          (Equal.trans(U32, PM.Fd(2n, Cr.Cir.Cells.set(m, z, y), z), Cr.Cir.Cell.get(2n, y), PM.Fd(2n, m, z),
            Equal.cong(Cr.Cir.Cell, U32, w => Cr.Cir.Cell.get(2n, w), Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, y), z), y, gs),
            s1.f2(Cr.Cir.Cells.get(m, z), v)),
           Equal.trans(U32, PM.Fd(3n, Cr.Cir.Cells.set(m, z, y), z), Cr.Cir.Cell.get(3n, y), PM.Fd(3n, m, z),
            Equal.cong(Cr.Cir.Cell, U32, w => Cr.Cir.Cell.get(3n, w), Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, y), z), y, gs),
            s1.f3(Cr.Cir.Cells.get(m, z), v)))))

# writes of field 1 keep fields 0, 2 and 3 of every cell
def ff.put1s(ws: List<&2, PM.W1>, +m: Cr.Cir.Cells, +x: U32) -> FF(m, PM.Put1(ws, m), x):
  match ws:
    case Nil{}:
      ff.refl(m, x)
    case Con{PM.W1{+c, +v}, +rest}:
      ff.trans(m, PM.Put1(rest, m), PM.Put1(Con{PM.W1{c, v}, rest}, m), x, ff.put1(PM.Put1(rest, m), c, v, x), ff.put1s(rest, m, x))

# Runs by WP
# ----------
#
# The steps of a run of the machine's code, as data_walk.bend's WP takes
# them: a set and a store of known values, an if and a while by the value
# of their test. A state is X.X.st of its registers and cells (no output).

# the statement has an alloc (or an emit) in it
def Al(s: Cr.Cir.Stmt) -> Bool:
  match s:
    case Cr.Cir.Stmt.nop{}:
      False{}
    case Cr.Cir.Stmt.set{_, _}:
      False{}
    case Cr.Cir.Stmt.store{_, _, _}:
      False{}
    case Cr.Cir.Stmt.alloc{_}:
      True{}
    case Cr.Cir.Stmt.emit{_}:
      True{}
    case Cr.Cir.Stmt.seq{a, b}:
      Bool.or(Al(a), Al(b))
    case Cr.Cir.Stmt.if{_, t, e}:
      Bool.or(Al(t), Al(e))
    case Cr.Cir.Stmt.while{_, b}:
      Al(b)
    case Cr.Cir.Stmt.halt{_}:
      False{}

def wp.tr(+r: Nat, +regs: List<&2, U32>, hl: {List.length(&2, U32, regs) == 63n : Nat}, hr: {Nat.is_lt(r, 63n) == True{} : Bool}) ->
  W.Tr(Nat.is_lt(r, List.length(&2, U32, regs))):
  %Equal.sym(Nat, List.length(&2, U32, regs), 63n, hl) : W.Tr(Nat.is_lt(r, _))
  %Equal.sym(Bool, Nat.is_lt(r, 63n), True{}, hr) : W.Tr(_)
  Unit{}

# a set of r to the value v of e
def wp.set(+F: Nat, +r: Nat, +e: Cr.Cir.Expr, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32,
  +lim: U32, +inp: List<&2, Word(8n)>, -Q: Cr.Cir.State -> Type, +B: Nat, +lb: U32, +v: U32,
  ob: W.Ob(e, X.X.st(regs, m, nx, fi, im, pg, lim, inp)), ev: {W.Ev(e, X.X.st(regs, m, nx, fi, im, pg, lim, inp)) == v : U32},
  hl: {List.length(&2, U32, regs) == 63n : Nat}, hr: {Nat.is_lt(r, 63n) == True{} : Bool},
  k: Q(X.X.st(List.set(&2, U32, regs, r, v), m, nx, fi, im, pg, lim, inp))) ->
  W.WP(Cr.Cir.Stmt.set{r, e}, F, X.X.st(regs, m, nx, fi, im, pg, lim, inp), Q, B, lb):
  +S = X.X.st(regs, m, nx, fi, im, pg, lim, inp)
  (ob, (wp.tr(r, regs, hl, hr),
    (%Equal.sym(U32, W.Ev(e, S), v, ev) : Q(X.X.st(List.set(&2, U32, regs, r, _), m, nx, fi, im, pg, lim, inp)); k)))

# a store of the value x of v in field k of the cell i, the value of c
def wp.store(+F: Nat, +k: Nat, +c: Cr.Cir.Expr, +v: Cr.Cir.Expr, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, -Q: Cr.Cir.State -> Type, +B: Nat, +lb: U32, +i: U32, +x: U32,
  oc: W.Ob(c, X.X.st(regs, m, nx, fi, im, pg, lim, inp)), ov: W.Ob(v, X.X.st(regs, m, nx, fi, im, pg, lim, inp)),
  ec: {W.Ev(c, X.X.st(regs, m, nx, fi, im, pg, lim, inp)) == i : U32}, evv: {W.Ev(v, X.X.st(regs, m, nx, fi, im, pg, lim, inp)) == x : U32},
  hc: {Cr.Cir.is_cell(i, im, fi, nx) == True{} : Bool},
  q: Q(X.X.st(regs, X.X.put(m, k, i, x), nx, fi, im, pg, lim, inp))) ->
  W.WP(Cr.Cir.Stmt.store{k, c, v}, F, X.X.st(regs, m, nx, fi, im, pg, lim, inp), Q, B, lb):
  +S = X.X.st(regs, m, nx, fi, im, pg, lim, inp)
  %Equal.sym(U32, W.Ev(c, S), i, ec) : W.Ob(c, S) & (W.Ob(v, S) & W.WP.store(k, _, W.Ev(v, S), S, Q))
  %Equal.sym(U32, W.Ev(v, S), x, evv) : W.Ob(c, S) & (W.Ob(v, S) & W.WP.store(k, i, _, S, Q))
  (oc, (ov, (Equal.sym(Bool, Cr.Cir.is_cell(i, im, fi, nx), True{}, hc), q)))

# the branch of an if or a while that its test takes
def wp.ift(z: Bool, -ka: (Cr.Cir.State -> Type) -> Type, -kb: (Cr.Cir.State -> Type) -> Type, -Q: Cr.Cir.State -> Type,
  hz: {z == False{} : Bool}, k: ka(Q)) -> W.IfQ(z, ka, kb, Q):
  match z:
    case False{}:
      k
    case True{}:
      Empty.absurd(W.IfQ(True{}, ka, kb, Q), N.true_ne_false(hz))

def wp.ife(z: Bool, -ka: (Cr.Cir.State -> Type) -> Type, -kb: (Cr.Cir.State -> Type) -> Type, -Q: Cr.Cir.State -> Type,
  hz: {z == True{} : Bool}, k: kb(Q)) -> W.IfQ(z, ka, kb, Q):
  match z:
    case False{}:
      Empty.absurd(W.IfQ(False{}, ka, kb, Q), N.false_ne_true(hz))
    case True{}:
      k

def wp.wht(z: Bool, -kb: (Cr.Cir.State -> Type) -> Type, -Q: Cr.Cir.State -> Type, -st: Cr.Cir.State,
  hz: {z == False{} : Bool}, k: kb(Q)) -> W.WhQ(z, kb, Q, st):
  match z:
    case False{}:
      k
    case True{}:
      Empty.absurd(W.WhQ(True{}, kb, Q, st), N.true_ne_false(hz))

def wp.whe(z: Bool, -kb: (Cr.Cir.State -> Type) -> Type, -Q: Cr.Cir.State -> Type, -st: Cr.Cir.State,
  hz: {z == True{} : Bool}, k: Q(st)) -> W.WhQ(z, kb, Q, st):
  match z:
    case False{}:
      Empty.absurd(W.WhQ(False{}, kb, Q, st), N.false_ne_true(hz))
    case True{}:
      k

# an if whose else is no alloc, by its test
def wp.if.t(+e: Cr.Cir.Stmt, +F: Nat, +c: Cr.Cir.Expr, +t: Cr.Cir.Stmt, +st: Cr.Cir.State, -Q: Cr.Cir.State -> Type, +B: Nat, +lb: U32,
  he: {Al(e) == False{} : Bool}, oc: W.Ob(c, st), hz: {U32.is_zero(W.Ev(c, st)) == False{} : Bool}, k: W.WP(t, F, st, Q, B, lb)) ->
  W.WP(Cr.Cir.Stmt.if{c, t, e}, F, st, Q, B, lb):
  match e:
    case Cr.Cir.Stmt.alloc{r}:
      Empty.absurd(W.WP(Cr.Cir.Stmt.if{c, t, Cr.Cir.Stmt.alloc{r}}, F, st, Q, B, lb), N.true_ne_false(he))
    case Cr.Cir.Stmt.nop{}:
      (oc, wp.ift(U32.is_zero(W.Ev(c, st)), q => W.WP(t, F, st, x => q(x), B, lb), q => W.WP(Cr.Cir.Stmt.nop{}, F, st, x => q(x), B, lb), Q, hz, k))
    case Cr.Cir.Stmt.set{r2, e2}:
      (oc, wp.ift(U32.is_zero(W.Ev(c, st)), q => W.WP(t, F, st, x => q(x), B, lb), q => W.WP(Cr.Cir.Stmt.set{r2, e2}, F, st, x => q(x), B, lb), Q, hz, k))
    case Cr.Cir.Stmt.store{k2, c2, v2}:
      (oc, wp.ift(U32.is_zero(W.Ev(c, st)), q => W.WP(t, F, st, x => q(x), B, lb), q => W.WP(Cr.Cir.Stmt.store{k2, c2, v2}, F, st, x => q(x), B, lb), Q, hz, k))
    case Cr.Cir.Stmt.emit{v2}:
      (oc, wp.ift(U32.is_zero(W.Ev(c, st)), q => W.WP(t, F, st, x => q(x), B, lb), q => W.WP(Cr.Cir.Stmt.emit{v2}, F, st, x => q(x), B, lb), Q, hz, k))
    case Cr.Cir.Stmt.seq{a2, b2}:
      (oc, wp.ift(U32.is_zero(W.Ev(c, st)), q => W.WP(t, F, st, x => q(x), B, lb), q => W.WP(Cr.Cir.Stmt.seq{a2, b2}, F, st, x => q(x), B, lb), Q, hz, k))
    case Cr.Cir.Stmt.if{c2, t2, e2}:
      (oc, wp.ift(U32.is_zero(W.Ev(c, st)), q => W.WP(t, F, st, x => q(x), B, lb), q => W.WP(Cr.Cir.Stmt.if{c2, t2, e2}, F, st, x => q(x), B, lb), Q, hz, k))
    case Cr.Cir.Stmt.while{c2, b2}:
      (oc, wp.ift(U32.is_zero(W.Ev(c, st)), q => W.WP(t, F, st, x => q(x), B, lb), q => W.WP(Cr.Cir.Stmt.while{c2, b2}, F, st, x => q(x), B, lb), Q, hz, k))
    case Cr.Cir.Stmt.halt{s2}:
      (oc, wp.ift(U32.is_zero(W.Ev(c, st)), q => W.WP(t, F, st, x => q(x), B, lb), q => W.WP(Cr.Cir.Stmt.halt{s2}, F, st, x => q(x), B, lb), Q, hz, k))

def wp.if.e(+e: Cr.Cir.Stmt, +F: Nat, +c: Cr.Cir.Expr, +t: Cr.Cir.Stmt, +st: Cr.Cir.State, -Q: Cr.Cir.State -> Type, +B: Nat, +lb: U32,
  he: {Al(e) == False{} : Bool}, oc: W.Ob(c, st), hz: {U32.is_zero(W.Ev(c, st)) == True{} : Bool}, k: W.WP(e, F, st, Q, B, lb)) ->
  W.WP(Cr.Cir.Stmt.if{c, t, e}, F, st, Q, B, lb):
  match e:
    case Cr.Cir.Stmt.alloc{r}:
      Empty.absurd(W.WP(Cr.Cir.Stmt.if{c, t, Cr.Cir.Stmt.alloc{r}}, F, st, Q, B, lb), N.true_ne_false(he))
    case Cr.Cir.Stmt.nop{}:
      (oc, wp.ife(U32.is_zero(W.Ev(c, st)), q => W.WP(t, F, st, x => q(x), B, lb), q => W.WP(Cr.Cir.Stmt.nop{}, F, st, x => q(x), B, lb), Q, hz, k))
    case Cr.Cir.Stmt.set{r2, e2}:
      (oc, wp.ife(U32.is_zero(W.Ev(c, st)), q => W.WP(t, F, st, x => q(x), B, lb), q => W.WP(Cr.Cir.Stmt.set{r2, e2}, F, st, x => q(x), B, lb), Q, hz, k))
    case Cr.Cir.Stmt.store{k2, c2, v2}:
      (oc, wp.ife(U32.is_zero(W.Ev(c, st)), q => W.WP(t, F, st, x => q(x), B, lb), q => W.WP(Cr.Cir.Stmt.store{k2, c2, v2}, F, st, x => q(x), B, lb), Q, hz, k))
    case Cr.Cir.Stmt.emit{v2}:
      (oc, wp.ife(U32.is_zero(W.Ev(c, st)), q => W.WP(t, F, st, x => q(x), B, lb), q => W.WP(Cr.Cir.Stmt.emit{v2}, F, st, x => q(x), B, lb), Q, hz, k))
    case Cr.Cir.Stmt.seq{a2, b2}:
      (oc, wp.ife(U32.is_zero(W.Ev(c, st)), q => W.WP(t, F, st, x => q(x), B, lb), q => W.WP(Cr.Cir.Stmt.seq{a2, b2}, F, st, x => q(x), B, lb), Q, hz, k))
    case Cr.Cir.Stmt.if{c2, t2, e2}:
      (oc, wp.ife(U32.is_zero(W.Ev(c, st)), q => W.WP(t, F, st, x => q(x), B, lb), q => W.WP(Cr.Cir.Stmt.if{c2, t2, e2}, F, st, x => q(x), B, lb), Q, hz, k))
    case Cr.Cir.Stmt.while{c2, b2}:
      (oc, wp.ife(U32.is_zero(W.Ev(c, st)), q => W.WP(t, F, st, x => q(x), B, lb), q => W.WP(Cr.Cir.Stmt.while{c2, b2}, F, st, x => q(x), B, lb), Q, hz, k))
    case Cr.Cir.Stmt.halt{s2}:
      (oc, wp.ife(U32.is_zero(W.Ev(c, st)), q => W.WP(t, F, st, x => q(x), B, lb), q => W.WP(Cr.Cir.Stmt.halt{s2}, F, st, x => q(x), B, lb), Q, hz, k))

# a round of a while, and its end
def wp.wh.t(+g: Nat, +c: Cr.Cir.Expr, +b: Cr.Cir.Stmt, +st: Cr.Cir.State, -Q: Cr.Cir.State -> Type, +B: Nat, +lb: U32,
  oc: W.Ob(c, st), hz: {U32.is_zero(W.Ev(c, st)) == False{} : Bool},
  k: W.WP(b, g, st, t => W.WP(Cr.Cir.Stmt.while{c, b}, g, t, Q, B, lb), B, lb)) ->
  W.WP(Cr.Cir.Stmt.while{c, b}, 1n+g, st, Q, B, lb):
  (oc, wp.wht(U32.is_zero(W.Ev(c, st)), q => W.WP(b, g, st, t => W.WP(Cr.Cir.Stmt.while{c, b}, g, t, x => q(x), B, lb), B, lb), Q, st, hz, k))

def wp.wh.e(+g: Nat, +c: Cr.Cir.Expr, +b: Cr.Cir.Stmt, +st: Cr.Cir.State, -Q: Cr.Cir.State -> Type, +B: Nat, +lb: U32,
  oc: W.Ob(c, st), hz: {U32.is_zero(W.Ev(c, st)) == True{} : Bool}, k: Q(st)) ->
  W.WP(Cr.Cir.Stmt.while{c, b}, 1n+g, st, Q, B, lb):
  (oc, wp.whe(U32.is_zero(W.Ev(c, st)), q => W.WP(b, g, st, t => W.WP(Cr.Cir.Stmt.while{c, b}, g, t, x => q(x), B, lb), B, lb), Q, st, hz, k))

# A run with no alloc never runs out of memory
# --------------------------------------------

def noal.then(o: Cr.Cir.Out, -k: Cr.Cir.State -> Cr.Cir.Out, h: PM.NoOom(o), g: @st: Cr.Cir.State -> PM.NoOom(k(st))) ->
  PM.NoOom(Cr.Cir.exec.then(o, k)):
  match o:
    case Cr.Cir.Out.next{st}:
      g(st)
    case Cr.Cir.Out.halt{s, st}:
      Unit{}
    case Cr.Cir.Out.out_of_memory{}:
      h
    case Cr.Cir.Out.trap{}:
      Unit{}
    case Cr.Cir.Out.not_done{}:
      Unit{}

def noal.if.of(z: Bool, -yes: Unit -> Cr.Cir.Out, -no: Unit -> Cr.Cir.Out, hy: PM.NoOom(yes(Unit{})), hn: PM.NoOom(no(Unit{}))) ->
  PM.NoOom(Cr.Cir.exec.if.of(z, yes, no)):
  match z:
    case False{}:
      hy
    case True{}:
      hn

def noal.if(c: Maybe<&2, U32>, -yes: Unit -> Cr.Cir.Out, -no: Unit -> Cr.Cir.Out, hy: PM.NoOom(yes(Unit{})), hn: PM.NoOom(no(Unit{}))) ->
  PM.NoOom(Cr.Cir.exec.if(c, yes, no)):
  match c:
    case Some{x}:
      noal.if.of(U32.is_zero(x), yes, no, hy, hn)
    case None{}:
      Unit{}

def noal.set.of(regs: Maybe<&2, List<&2, U32>>, st: Cr.Cir.State) -> PM.NoOom(Cr.Cir.exec.set.of(regs, st)):
  match regs st:
    case Some{rs} Cr.Cir.State{_, cells, next, first, image, pages, limit, input, out, outn}:
      Unit{}
    case None{} _:
      Unit{}

def noal.set(+r: Nat, v: Maybe<&2, U32>, +st: Cr.Cir.State) -> PM.NoOom(Cr.Cir.exec.set(r, v, st)):
  match v st:
    case Some{x} Cr.Cir.State{+regs, cells, next, first, image, pages, limit, input, out, outn}:
      noal.set.of(Cr.Cir.regs.set(regs, r, x), Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn})
    case None{} _:
      Unit{}

def noal.store.if(ok: Bool, +k: Nat, +i: U32, +v: U32, st: Cr.Cir.State) -> PM.NoOom(Cr.Cir.exec.store.if(ok, k, i, v, st)):
  match ok st:
    case True{} Cr.Cir.State{regs, +cells, next, first, image, pages, limit, input, out, outn}:
      Unit{}
    case False{} _:
      Unit{}

def noal.store(+k: Nat, c: Maybe<&2, U32>, v: Maybe<&2, U32>, +st: Cr.Cir.State) -> PM.NoOom(Cr.Cir.exec.store(k, c, v, st)):
  match c:
    case None{}:
      Unit{}
    case Some{+i}:
      match v:
        case None{}:
          Unit{}
        case Some{+x}:
          match st:
            case Cr.Cir.State{+regs, +cells, +next, +first, +image, +pages, +limit, +input, +out, +outn}:
              noal.store.if(Cr.Cir.is_cell(i, image, first, next), k, i, x, Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn})

# a statement with no alloc and no emit never runs out of memory
def noal(+F: Nat, +s: Cr.Cir.Stmt, +st: Cr.Cir.State, +h: {Al(s) == False{} : Bool}) -> PM.NoOom(Cr.Cir.exec(F, s, st)):
  match F:
    case 0n:
      match s:
        case Cr.Cir.Stmt.nop{}:
          Unit{}
        case Cr.Cir.Stmt.set{+r, +e}:
          noal.set(r, Cr.Cir.eval(e, st), st)
        case Cr.Cir.Stmt.store{+k, +c, +v}:
          noal.store(k, Cr.Cir.eval(c, st), Cr.Cir.eval(v, st), st)
        case Cr.Cir.Stmt.alloc{+r}:
          Empty.absurd(PM.NoOom(Cr.Cir.exec(0n, Cr.Cir.Stmt.alloc{r}, st)), N.true_ne_false(h))
        case Cr.Cir.Stmt.emit{+v}:
          Empty.absurd(PM.NoOom(Cr.Cir.exec(0n, Cr.Cir.Stmt.emit{v}, st)), N.true_ne_false(h))
        case Cr.Cir.Stmt.seq{+a, +b}:
          noal.then(Cr.Cir.exec(F, a, st), t => Cr.Cir.exec(F, b, t), noal(F, a, st, PM.or.f.l(Al(a), Al(b), h)),
            t => noal(F, b, t, PM.or.f.r(Al(a), Al(b), h)))
        case Cr.Cir.Stmt.if{+c, +t, +e}:
          noal.if(Cr.Cir.eval(c, st), u => Cr.Cir.exec(F, t, st), u => Cr.Cir.exec(F, e, st), noal(F, t, st, PM.or.f.l(Al(t), Al(e), h)),
            noal(F, e, st, PM.or.f.r(Al(t), Al(e), h)))
        case Cr.Cir.Stmt.while{_, _}:
          Unit{}
        case Cr.Cir.Stmt.halt{_}:
          Unit{}
    case 1n+(+g):
      match s:
        case Cr.Cir.Stmt.nop{}:
          Unit{}
        case Cr.Cir.Stmt.set{+r, +e}:
          noal.set(r, Cr.Cir.eval(e, st), st)
        case Cr.Cir.Stmt.store{+k, +c, +v}:
          noal.store(k, Cr.Cir.eval(c, st), Cr.Cir.eval(v, st), st)
        case Cr.Cir.Stmt.alloc{+r}:
          Empty.absurd(PM.NoOom(Cr.Cir.exec(1n+g, Cr.Cir.Stmt.alloc{r}, st)), N.true_ne_false(h))
        case Cr.Cir.Stmt.emit{+v}:
          Empty.absurd(PM.NoOom(Cr.Cir.exec(1n+g, Cr.Cir.Stmt.emit{v}, st)), N.true_ne_false(h))
        case Cr.Cir.Stmt.seq{+a, +b}:
          noal.then(Cr.Cir.exec(F, a, st), t => Cr.Cir.exec(F, b, t), noal(F, a, st, PM.or.f.l(Al(a), Al(b), h)),
            t => noal(F, b, t, PM.or.f.r(Al(a), Al(b), h)))
        case Cr.Cir.Stmt.if{+c, +t, +e}:
          noal.if(Cr.Cir.eval(c, st), u => Cr.Cir.exec(F, t, st), u => Cr.Cir.exec(F, e, st), noal(F, t, st, PM.or.f.l(Al(t), Al(e), h)),
            noal(F, e, st, PM.or.f.r(Al(t), Al(e), h)))
        case Cr.Cir.Stmt.while{+c, +b}:
          noal.if(Cr.Cir.eval(c, st), u => Cr.Cir.exec.then(Cr.Cir.exec(g, b, st), t => Cr.Cir.exec(g, Cr.Cir.Stmt.while{c, b}, t)),
            u => Cr.Cir.Out.next{st},
            noal.then(Cr.Cir.exec(g, b, st), t => Cr.Cir.exec(g, Cr.Cir.Stmt.while{c, b}, t), noal(g, b, st, h),
              t => noal(g, Cr.Cir.Stmt.while{c, b}, t, h)), Unit{})
        case Cr.Cir.Stmt.halt{_}:
          Unit{}

# a run that cannot run out of memory keeps PostB with any budget
def postb.no(o: Cr.Cir.Out, -Q: Cr.Cir.State -> Type, -H: U32 -> Cr.Cir.State -> Type, -B: Nat, -B2: Nat, -lim: U32,
  h: PM.PostB(False{}, o, Q, H, B, lim), n: PM.NoOom(o)) -> PM.PostB(False{}, o, Q, H, B2, lim):
  match o:
    case Cr.Cir.Out.next{st}:
      h
    case Cr.Cir.Out.halt{s, st}:
      h
    case Cr.Cir.Out.out_of_memory{}:
      match n:
    case Cr.Cir.Out.trap{}:
      h
    case Cr.Cir.Out.not_done{}:
      h

# The premises data.post and data.done of move_kit.bend (U6; U0 left them as ?TODO)
# -------------------------------------------------------------------------------

def K.data.post(f, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, r, keep, os, bs, fs, sp, pend, ps, c, v, xs, zs, hs, hac, hl, hc, hp, hr, hk):
  ?TODO

def K.data.done(ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, r, os, bs, fs, sp, pend, ps, c, v, hs, hl, hc, hp, hr):
  ?TODO
