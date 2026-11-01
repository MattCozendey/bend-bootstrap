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
import ../../book/impl.bend as Bk
import ../../eval/impl.bend as El
import ../cir/impl.bend as Cr
import ./cell_terms.bend as T
import ../need_big.bend as N
import ./definitions.bend as PM
import ./statement_runs.bend as X

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
