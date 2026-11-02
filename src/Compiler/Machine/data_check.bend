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
import ./impl.bend as Mc
import ./cell_terms.bend as T
import ../need_big.bend as N
import ./definitions.bend as PM
import ./statement_runs.bend as X
import ./move_kit.bend as K
import ./data_walk.bend as W
import ./heap_ops.bend as HO

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

# The heap's parts
# ----------------

def hsk.held(-dk: Bool, -ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -m: Cr.Cir.Cells, -nx: U32,
  -fi: U32, -im: U32, -os: List<&2, PM.Rt>, -bs: List<&2, PM.Rt>, -fs: List<&2, PM.AF>, -sp: U32, -pend: U32, -ps: List<&2, U32>,
  h: PM.HSK(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps)) -> PM.Held(m, os, bs):
  match h:
    case Tuple{_, Tuple{_, Tuple{hh, _}}}:
      hh

def hsk.heap(-dk: Bool, -ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -m: Cr.Cir.Cells, -nx: U32,
  -fi: U32, -im: U32, -os: List<&2, PM.Rt>, -bs: List<&2, PM.Rt>, -fs: List<&2, PM.AF>, -sp: U32, -pend: U32, -ps: List<&2, U32>,
  h: PM.HSK(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps)) -> PM.Heap(m, nx, fi, im, PM.Rt.cells(os), pend, ps):
  match h:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{hp, _}}}}}:
      hp

def hsk.img(-dk: Bool, -ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -m: Cr.Cir.Cells, -nx: U32,
  -fi: U32, -im: U32, -os: List<&2, PM.Rt>, -bs: List<&2, PM.Rt>, -fs: List<&2, PM.AF>, -sp: U32, -pend: U32, -ps: List<&2, U32>,
  h: PM.HSK(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps)) -> PM.ImgOKK(dk, ds, ks, img, m, im, fi, nx):
  match h:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, hi}}}}}:
      hi

def hsk.bs(-dk: Bool, -ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -m: Cr.Cir.Cells, -nx: U32,
  -fi: U32, -im: U32, -os: List<&2, PM.Rt>, -bs: List<&2, PM.Rt>, -fs: List<&2, PM.AF>, -sp: U32, -pend: U32, -ps: List<&2, U32>,
  h: PM.HSK(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps)) -> PM.RtsK(dk, ds, m, im, fi, nx, ks, img, bs):
  match h:
    case Tuple{_, Tuple{hb, _}}:
      hb

def heap.chain(-m: Cr.Cir.Cells, -nx: U32, -fi: U32, -im: U32, -rs: List<&2, U32>, -pend: U32, -ps: List<&2, U32>,
  h: PM.Heap(m, nx, fi, im, rs, pend, ps)) -> PM.Chain(ps, m, pend):
  match h:
    case Tuple{hc, _}:
      hc

def heap.fin(-m: Cr.Cir.Cells, -nx: U32, -fi: U32, -im: U32, -rs: List<&2, U32>, -pend: U32, -ps: List<&2, U32>,
  h: PM.Heap(m, nx, fi, im, rs, pend, ps)) -> {U32.is_le(fi, nx) == True{} : Bool}:
  match h:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, hf}}}}}:
      hf

# a pend list from 0 is empty
def chain.none(ps: List<&2, U32>, +m: Cr.Cir.Cells, +p: U32, h: PM.Chain(ps, m, p), hz: {U32.is_eq(p, 0) == True{} : Bool}) ->
  {PM.Pend.none(ps) == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case Con{+x, rest}:
      (hx, r1) = h
      (hn, r2) = r1
      Empty.absurd({PM.Pend.none(Con{x, rest}) == True{} : Bool},
        N.true_ne_false(Equal.trans(Bool, True{}, U32.is_eq(x, 0), False{},
          Equal.sym(Bool, U32.is_eq(x, 0), True{}, (%hx : {U32.is_eq(_, 0) == True{} : Bool}; hz)), hn)))

# a pending cell (not STATIC, no pointer) is not held
def hd.np.no(+p: U32, +ps: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +rs: List<&2, U32>,
  hs: {PM.Fl(m, p, 1024) == False{} : Bool}, hp0: {PM.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, rs, p) == 0n : Nat},
  hd: {PM.Hd(m, nx, fi, ps, rs, p) == True{} : Bool}) -> Empty:
  +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
  N.false_ne_true((%hs : {Bool.or(_, Nat.is_lt(0n, 0n)) == True{} : Bool};
    (%hp0 : {Bool.or(PM.Fl(m, p, 1024), Nat.is_lt(0n, _)) == True{} : Bool}; hd)))

def hd.np.at(b: Bool, +p: U32, +rest: List<&2, U32>, +ps: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +rs: List<&2, U32>, +x: U32,
  eb: {U32.is_eq(p, x) == b : Bool}, hs: {PM.Fl(m, p, 1024) == False{} : Bool},
  hp0: {PM.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, rs, p) == 0n : Nat},
  hd: {PM.Hd(m, nx, fi, ps, rs, x) == True{} : Bool}, hr: {PM.Mem(rest, x) == False{} : Bool}) ->
  {Bool.or(b, PM.Mem(rest, x)) == False{} : Bool}:
  match b:
    case False{}:
      hr
    case True{}:
      Empty.absurd({Bool.or(True{}, PM.Mem(rest, x)) == False{} : Bool},
        hd.np.no(p, ps, m, nx, fi, rs, hs, hp0, (%Equal.sym(U32, p, x, PM.u32.eq(p, x, eb)) : {PM.Hd(m, nx, fi, ps, rs, _) == True{} : Bool}; hd)))

# a held cell (STATIC or with a pointer) is in no pend list
def hd.np(qs: List<&2, U32>, +ps: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +rs: List<&2, U32>, +x: U32,
  h: PM.PendOK(qs, ps, m, fi, nx, rs), +hd: {PM.Hd(m, nx, fi, ps, rs, x) == True{} : Bool}) -> {PM.Mem(qs, x) == False{} : Bool}:
  match qs:
    case Nil{}:
      {==}
    case Con{+p, +rest}:
      (ho, r1) = h
      (hs, r2) = r1
      (ht, r3) = r2
      (hp0, r4) = r3
      hd.np.at(U32.is_eq(p, x), p, rest, ps, m, nx, fi, rs, x, {==}, hs, hp0, hd, hd.np(rest, ps, m, nx, fi, rs, x, r4, hd))


# Cells of v's tree
# ----------------

# a term's cell is a node of it
def node.self(t: Bk.Term, +m: Cr.Cir.Cells, +r: U32) -> {PM.Node(t, m, r, r) == True{} : Bool}:
  match t:
    case Bk.Term.Var{+o0}:
      PM.u32.refl(r)
    case Bk.Term.Ref{+o0}:
      PM.u32.refl(r)
    case Bk.Term.Ann{+y, +z}:
      PM.or.l(U32.is_eq(r, r), Bool.or(PM.Node(y, m, PM.Fd(2n, m, r), r), PM.Node(z, m, PM.Fd(3n, m, r), r)), PM.u32.refl(r))
    case Bk.Term.Let{+q, +y, +z}:
      PM.or.l(U32.is_eq(r, r), Bool.or(PM.Node(y, m, PM.Fd(2n, m, r), r), PM.Node(z, m, PM.Fd(3n, m, r), r)), PM.u32.refl(r))
    case Bk.Term.Typ{+y}:
      PM.or.l(U32.is_eq(r, r), PM.Node(y, m, PM.Fd(2n, m, r), r), PM.u32.refl(r))
    case Bk.Term.Min{+y, +z}:
      PM.or.l(U32.is_eq(r, r), Bool.or(PM.Node(y, m, PM.Fd(2n, m, r), r), PM.Node(z, m, PM.Fd(3n, m, r), r)), PM.u32.refl(r))
    case Bk.Term.All{+q, +y, +z}:
      PM.or.l(U32.is_eq(r, r), Bool.or(PM.Node(y, m, PM.Fd(2n, m, r), r), PM.Node(z, m, PM.Fd(3n, m, r), r)), PM.u32.refl(r))
    case Bk.Term.Lam{+q, +y}:
      PM.or.l(U32.is_eq(r, r), PM.Node(y, m, PM.Fd(2n, m, r), r), PM.u32.refl(r))
    case Bk.Term.App{+q, +y, +z}:
      PM.or.l(U32.is_eq(r, r), Bool.or(PM.Node(y, m, PM.Fd(2n, m, r), r), PM.Node(z, m, PM.Fd(3n, m, r), r)), PM.u32.refl(r))
    case Bk.Term.Sig{+q, +y, +z}:
      PM.or.l(U32.is_eq(r, r), Bool.or(PM.Node(y, m, PM.Fd(2n, m, r), r), PM.Node(z, m, PM.Fd(3n, m, r), r)), PM.u32.refl(r))
    case Bk.Term.Tup{+q, +y, +z}:
      PM.or.l(U32.is_eq(r, r), Bool.or(PM.Node(y, m, PM.Fd(2n, m, r), r), PM.Node(z, m, PM.Fd(3n, m, r), r)), PM.u32.refl(r))
    case Bk.Term.Prj{+y}:
      PM.or.l(U32.is_eq(r, r), PM.Node(y, m, PM.Fd(2n, m, r), r), PM.u32.refl(r))
    case Bk.Term.Enu{+o0}:
      PM.u32.refl(r)
    case Bk.Term.Lab{+o0}:
      PM.u32.refl(r)
    case Bk.Term.Mat{+k, +y, +z}:
      PM.or.l(U32.is_eq(r, r), Bool.or(PM.Node(y, m, PM.Fd(3n, m, r), r), PM.Node(z, m, PM.Fd(4n, m, r), r)), PM.u32.refl(r))
    case Bk.Term.Efq{}:
      PM.u32.refl(r)
    case Bk.Term.Eql{+y, +z, +w}:
      PM.or.l(U32.is_eq(r, r), Bool.or(PM.Node(y, m, PM.Fd(2n, m, r), r), Bool.or(PM.Node(z, m, PM.Fd(3n, m, r), r), PM.Node(w, m, PM.Fd(4n, m, r), r))), PM.u32.refl(r))
    case Bk.Term.Rfl{}:
      PM.u32.refl(r)
    case Bk.Term.Rwt{+y, +z, +w}:
      PM.or.l(U32.is_eq(r, r), Bool.or(PM.Node(y, m, PM.Fd(2n, m, r), r), Bool.or(PM.Node(z, m, PM.Fd(3n, m, r), r), PM.Node(w, m, PM.Fd(4n, m, r), r))), PM.u32.refl(r))

# the cell at a path of v's cell is a node of v
def path.node(p: List<&2, Bool>, v: Bk.Term, +m: Cr.Cir.Cells, +c: U32, -u: Bk.Term, e: {Sub(p, v) == Some{u} : Maybe<&2, Bk.Term>}) ->
  {PM.Node(v, m, c, Cl(m, p, c)) == True{} : Bool}:
  match p v:
    case Nil{} +x:
      node.self(x, m, c)
    case Con{True{}, +rest} Bk.Term.Tup{+q, +a, +b}:
      +y = Cl(m, rest, PM.Fd(2n, m, c))
      sub.l(El.Quan.live(q), rest, a, u, {PM.Node(Bk.Term.Tup{q, a, b}, m, c, y) == True{} : Bool}, e,
        el => e2 => PM.or.r(U32.is_eq(c, y), Bool.or(PM.Node(a, m, PM.Fd(2n, m, c), y), PM.Node(b, m, PM.Fd(3n, m, c), y)),
          PM.or.l(PM.Node(a, m, PM.Fd(2n, m, c), y), PM.Node(b, m, PM.Fd(3n, m, c), y), path.node(rest, a, m, PM.Fd(2n, m, c), u, e2))))
    case Con{False{}, +rest} Bk.Term.Tup{+q, +a, +b}:
      +y = Cl(m, rest, PM.Fd(3n, m, c))
      PM.or.r(U32.is_eq(c, y), Bool.or(PM.Node(a, m, PM.Fd(2n, m, c), y), PM.Node(b, m, PM.Fd(3n, m, c), y)),
        PM.or.r(PM.Node(a, m, PM.Fd(2n, m, c), y), PM.Node(b, m, PM.Fd(3n, m, c), y), path.node(rest, b, m, PM.Fd(3n, m, c), u, e)))
    case Con{d, rest} Bk.Term.Var{+o0}:
      Empty.absurd({PM.Node(Bk.Term.Var{o0}, m, c, Cl(m, Con{d, rest}, c)) == True{} : Bool}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Ref{+o0}:
      Empty.absurd({PM.Node(Bk.Term.Ref{o0}, m, c, Cl(m, Con{d, rest}, c)) == True{} : Bool}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Ann{+o0, +o1}:
      Empty.absurd({PM.Node(Bk.Term.Ann{o0, o1}, m, c, Cl(m, Con{d, rest}, c)) == True{} : Bool}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Let{+o0, +o1, +o2}:
      Empty.absurd({PM.Node(Bk.Term.Let{o0, o1, o2}, m, c, Cl(m, Con{d, rest}, c)) == True{} : Bool}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Typ{+o0}:
      Empty.absurd({PM.Node(Bk.Term.Typ{o0}, m, c, Cl(m, Con{d, rest}, c)) == True{} : Bool}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Min{+o0, +o1}:
      Empty.absurd({PM.Node(Bk.Term.Min{o0, o1}, m, c, Cl(m, Con{d, rest}, c)) == True{} : Bool}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.All{+o0, +o1, +o2}:
      Empty.absurd({PM.Node(Bk.Term.All{o0, o1, o2}, m, c, Cl(m, Con{d, rest}, c)) == True{} : Bool}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Lam{+o0, +o1}:
      Empty.absurd({PM.Node(Bk.Term.Lam{o0, o1}, m, c, Cl(m, Con{d, rest}, c)) == True{} : Bool}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.App{+o0, +o1, +o2}:
      Empty.absurd({PM.Node(Bk.Term.App{o0, o1, o2}, m, c, Cl(m, Con{d, rest}, c)) == True{} : Bool}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Sig{+o0, +o1, +o2}:
      Empty.absurd({PM.Node(Bk.Term.Sig{o0, o1, o2}, m, c, Cl(m, Con{d, rest}, c)) == True{} : Bool}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Prj{+o0}:
      Empty.absurd({PM.Node(Bk.Term.Prj{o0}, m, c, Cl(m, Con{d, rest}, c)) == True{} : Bool}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Enu{+o0}:
      Empty.absurd({PM.Node(Bk.Term.Enu{o0}, m, c, Cl(m, Con{d, rest}, c)) == True{} : Bool}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Lab{+o0}:
      Empty.absurd({PM.Node(Bk.Term.Lab{o0}, m, c, Cl(m, Con{d, rest}, c)) == True{} : Bool}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Mat{+o0, +o1, +o2}:
      Empty.absurd({PM.Node(Bk.Term.Mat{o0, o1, o2}, m, c, Cl(m, Con{d, rest}, c)) == True{} : Bool}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Efq{}:
      Empty.absurd({PM.Node(Bk.Term.Efq{}, m, c, Cl(m, Con{d, rest}, c)) == True{} : Bool}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Eql{+o0, +o1, +o2}:
      Empty.absurd({PM.Node(Bk.Term.Eql{o0, o1, o2}, m, c, Cl(m, Con{d, rest}, c)) == True{} : Bool}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Rfl{}:
      Empty.absurd({PM.Node(Bk.Term.Rfl{}, m, c, Cl(m, Con{d, rest}, c)) == True{} : Bool}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Rwt{+o0, +o1, +o2}:
      Empty.absurd({PM.Node(Bk.Term.Rwt{o0, o1, o2}, m, c, Cl(m, Con{d, rest}, c)) == True{} : Bool}, mt.ne(u, e))

# the cells of v's tree are STATIC or have a pointer, when v's cell is
def path.hd(+dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32,
  +fi: U32, +im: U32, +ps: List<&2, U32>, +rs: List<&2, U32>, +p: List<&2, Bool>, +v: Bk.Term, +c: U32, -u: Bk.Term,
  tbl: PM.Tbl(m, im, fi, nx), h: PM.IsK(dk, ds, m, im, fi, nx, ks, img, c, v), hc: {PM.Hd(m, nx, fi, ps, rs, c) == True{} : Bool},
  e: {Sub(p, v) == Some{u} : Maybe<&2, Bk.Term>}) -> {PM.Hd(m, nx, fi, ps, rs, Cl(m, p, c)) == True{} : Bool}:
  PM.node.ptr(v, dk, ds, m, im, fi, nx, ks, img, ps, rs, tbl, c, Cl(m, p, c), h, hc, path.node(p, v, m, c, u, e))

# the first borrowed cell is held, and stands for its term
def held.hd(-m: Cr.Cir.Cells, -os: List<&2, PM.Rt>, -c: U32, -v: Bk.Term, -bs: List<&2, PM.Rt>, h: PM.Held(m, os, Con{PM.Rt{c, v}, bs})) ->
  {Bool.or(PM.Fl(m, c, 1024), PM.Nodes(os, m, c)) == True{} : Bool}:
  match h:
    case Tuple{hn, _}:
      hn

def rtsk.hd(-dk: Bool, -ds: List<&2, Bk.Def>, -m: Cr.Cir.Cells, -im: U32, -fi: U32, -nx: U32, -ks: List<&2, List<&2, Word(8n)>>,
  -img: List<&2, Bk.Term>, -c: U32, -v: Bk.Term, -bs: List<&2, PM.Rt>, h: PM.RtsK(dk, ds, m, im, fi, nx, ks, img, Con{PM.Rt{c, v}, bs})) ->
  PM.IsK(dk, ds, m, im, fi, nx, ks, img, c, v):
  match h:
    case Tuple{hv, _}:
      hv

# the cells of the tree of a borrowed v are held
def vh.hd(+dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32,
  +fi: U32, +im: U32, +os: List<&2, PM.Rt>, +bs: List<&2, PM.Rt>, +fs: List<&2, PM.AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>,
  +c: U32, +v: Bk.Term, +p: List<&2, Bool>, -u: Bk.Term,
  +hs: PM.HSK(dk, ds, ks, img, m, nx, fi, im, os, Con{PM.Rt{c, v}, bs}, fs, sp, pend, ps), e: {Sub(p, v) == Some{u} : Maybe<&2, Bk.Term>}) ->
  {PM.Hd(m, nx, fi, ps, PM.Rt.cells(os), Cl(m, p, c)) == True{} : Bool}:
  +hn = held.hd(m, os, c, v, bs, hsk.held(dk, ds, ks, img, m, nx, fi, im, os, Con{PM.Rt{c, v}, bs}, fs, sp, pend, ps, hs))
  +hv = rtsk.hd(dk, ds, m, im, fi, nx, ks, img, c, v, bs, hsk.bs(dk, ds, ks, img, m, nx, fi, im, os, Con{PM.Rt{c, v}, bs}, fs, sp, pend, ps, hs))
  +tbl = PM.img.tbl(dk, ds, ks, img, m, im, fi, nx, hsk.img(dk, ds, ks, img, m, nx, fi, im, os, Con{PM.Rt{c, v}, bs}, fs, sp, pend, ps, hs))
  path.hd(dk, ds, ks, img, m, nx, fi, im, ps, PM.Rt.cells(os), p, v, c, u, tbl, hv,
    PM.held.ptr(dk, ds, ks, img, m, nx, fi, im, os, Con{PM.Rt{c, v}, bs}, fs, sp, pend, ps, c, hs, hn), e)


# The frame of v's tree
# ---------------------
#
# The check reads, of each cell of v's tree (through pairs, from c, at the
# fields that the cells m0 give where the check begins), field 0 and fields 2
# and 3. Each store of the run keeps them, but the flag DATA, which the check
# sets on the cells ns: KV, by structure on v (a fact on every cell must be
# Data: a function could be used once).

# field 0 of the cell x of v's tree: as at the start, with DATA if x is in ns
def F0(+m0: Cr.Cir.Cells, +x: U32, +ns: List<&2, U32>) -> U32:
  Bool.pick(U32, PM.Mem(ns, x), U32.or(PM.Fd(0n, m0, x), 512), PM.Fd(0n, m0, x))

# the cell x keeps in m what the check reads of it in m0
def FV(+m0: Cr.Cir.Cells, +m: Cr.Cir.Cells, +x: U32, +ns: List<&2, U32>) -> Data:
  PM.P2({PM.Fd(0n, m, x) == F0(m0, x, ns) : U32}, FC(m0, m, x))

def KV(v: Bk.Term, +m0: Cr.Cir.Cells, +m: Cr.Cir.Cells, +x: U32, +ns: List<&2, U32>) -> Data:
  match v:
    case Bk.Term.Tup{_, a, b}:
      PM.P2(FV(m0, m, x, ns), PM.P2(KV(a, m0, m, PM.Fd(2n, m0, x), ns), KV(b, m0, m, PM.Fd(3n, m0, x), ns)))
    case Bk.Term.Var{_}:
      FV(m0, m, x, ns)
    case Bk.Term.Ref{_}:
      FV(m0, m, x, ns)
    case Bk.Term.Ann{_, _}:
      FV(m0, m, x, ns)
    case Bk.Term.Let{_, _, _}:
      FV(m0, m, x, ns)
    case Bk.Term.Typ{_}:
      FV(m0, m, x, ns)
    case Bk.Term.Min{_, _}:
      FV(m0, m, x, ns)
    case Bk.Term.All{_, _, _}:
      FV(m0, m, x, ns)
    case Bk.Term.Lam{_, _}:
      FV(m0, m, x, ns)
    case Bk.Term.App{_, _, _}:
      FV(m0, m, x, ns)
    case Bk.Term.Sig{_, _, _}:
      FV(m0, m, x, ns)
    case Bk.Term.Prj{_}:
      FV(m0, m, x, ns)
    case Bk.Term.Enu{_}:
      FV(m0, m, x, ns)
    case Bk.Term.Lab{_}:
      FV(m0, m, x, ns)
    case Bk.Term.Mat{_, _, _}:
      FV(m0, m, x, ns)
    case Bk.Term.Efq{}:
      FV(m0, m, x, ns)
    case Bk.Term.Eql{_, _, _}:
      FV(m0, m, x, ns)
    case Bk.Term.Rfl{}:
      FV(m0, m, x, ns)
    case Bk.Term.Rwt{_, _, _}:
      FV(m0, m, x, ns)

# fields 0, 2 and 3 of each cell of v's tree kept from m to m2
def FT(v: Bk.Term, +m0: Cr.Cir.Cells, +m: Cr.Cir.Cells, +m2: Cr.Cir.Cells, +x: U32) -> Data:
  match v:
    case Bk.Term.Tup{_, a, b}:
      PM.P2(FF(m, m2, x), PM.P2(FT(a, m0, m, m2, PM.Fd(2n, m0, x)), FT(b, m0, m, m2, PM.Fd(3n, m0, x))))
    case Bk.Term.Var{_}:
      FF(m, m2, x)
    case Bk.Term.Ref{_}:
      FF(m, m2, x)
    case Bk.Term.Ann{_, _}:
      FF(m, m2, x)
    case Bk.Term.Let{_, _, _}:
      FF(m, m2, x)
    case Bk.Term.Typ{_}:
      FF(m, m2, x)
    case Bk.Term.Min{_, _}:
      FF(m, m2, x)
    case Bk.Term.All{_, _, _}:
      FF(m, m2, x)
    case Bk.Term.Lam{_, _}:
      FF(m, m2, x)
    case Bk.Term.App{_, _, _}:
      FF(m, m2, x)
    case Bk.Term.Sig{_, _, _}:
      FF(m, m2, x)
    case Bk.Term.Prj{_}:
      FF(m, m2, x)
    case Bk.Term.Enu{_}:
      FF(m, m2, x)
    case Bk.Term.Lab{_}:
      FF(m, m2, x)
    case Bk.Term.Mat{_, _, _}:
      FF(m, m2, x)
    case Bk.Term.Efq{}:
      FF(m, m2, x)
    case Bk.Term.Eql{_, _, _}:
      FF(m, m2, x)
    case Bk.Term.Rfl{}:
      FF(m, m2, x)
    case Bk.Term.Rwt{_, _, _}:
      FF(m, m2, x)

# no cell of v's tree is z
def TN(v: Bk.Term, +m0: Cr.Cir.Cells, +x: U32, +z: U32) -> Bool:
  match v:
    case Bk.Term.Tup{_, a, b}:
      Bool.and(Bool.not(U32.is_eq(x, z)), Bool.and(TN(a, m0, PM.Fd(2n, m0, x), z), TN(b, m0, PM.Fd(3n, m0, x), z)))
    case Bk.Term.Var{_}:
      Bool.not(U32.is_eq(x, z))
    case Bk.Term.Ref{_}:
      Bool.not(U32.is_eq(x, z))
    case Bk.Term.Ann{_, _}:
      Bool.not(U32.is_eq(x, z))
    case Bk.Term.Let{_, _, _}:
      Bool.not(U32.is_eq(x, z))
    case Bk.Term.Typ{_}:
      Bool.not(U32.is_eq(x, z))
    case Bk.Term.Min{_, _}:
      Bool.not(U32.is_eq(x, z))
    case Bk.Term.All{_, _, _}:
      Bool.not(U32.is_eq(x, z))
    case Bk.Term.Lam{_, _}:
      Bool.not(U32.is_eq(x, z))
    case Bk.Term.App{_, _, _}:
      Bool.not(U32.is_eq(x, z))
    case Bk.Term.Sig{_, _, _}:
      Bool.not(U32.is_eq(x, z))
    case Bk.Term.Prj{_}:
      Bool.not(U32.is_eq(x, z))
    case Bk.Term.Enu{_}:
      Bool.not(U32.is_eq(x, z))
    case Bk.Term.Lab{_}:
      Bool.not(U32.is_eq(x, z))
    case Bk.Term.Mat{_, _, _}:
      Bool.not(U32.is_eq(x, z))
    case Bk.Term.Efq{}:
      Bool.not(U32.is_eq(x, z))
    case Bk.Term.Eql{_, _, _}:
      Bool.not(U32.is_eq(x, z))
    case Bk.Term.Rfl{}:
      Bool.not(U32.is_eq(x, z))
    case Bk.Term.Rwt{_, _, _}:
      Bool.not(U32.is_eq(x, z))

# the frame at the root
def kv.top(v: Bk.Term, +m0: Cr.Cir.Cells, +m: Cr.Cir.Cells, +x: U32, +ns: List<&2, U32>, k: KV(v, m0, m, x, ns)) -> FV(m0, m, x, ns):
  match v:
    case Bk.Term.Tup{+q, +a, +b}:
      (f, _) = k
      f
    case Bk.Term.Var{+o0}:
      k
    case Bk.Term.Ref{+o0}:
      k
    case Bk.Term.Ann{+o0, +o1}:
      k
    case Bk.Term.Let{+o0, +o1, +o2}:
      k
    case Bk.Term.Typ{+o0}:
      k
    case Bk.Term.Min{+o0, +o1}:
      k
    case Bk.Term.All{+o0, +o1, +o2}:
      k
    case Bk.Term.Lam{+o0, +o1}:
      k
    case Bk.Term.App{+o0, +o1, +o2}:
      k
    case Bk.Term.Sig{+o0, +o1, +o2}:
      k
    case Bk.Term.Prj{+o0}:
      k
    case Bk.Term.Enu{+o0}:
      k
    case Bk.Term.Lab{+o0}:
      k
    case Bk.Term.Mat{+o0, +o1, +o2}:
      k
    case Bk.Term.Efq{}:
      k
    case Bk.Term.Eql{+o0, +o1, +o2}:
      k
    case Bk.Term.Rfl{}:
      k
    case Bk.Term.Rwt{+o0, +o1, +o2}:
      k

# the frame at the cell of a path
def kv.at(p: List<&2, Bool>, v: Bk.Term, +m0: Cr.Cir.Cells, +m: Cr.Cir.Cells, +x: U32, +ns: List<&2, U32>, -u: Bk.Term,
  k: KV(v, m0, m, x, ns), e: {Sub(p, v) == Some{u} : Maybe<&2, Bk.Term>}) -> FV(m0, m, Cl(m0, p, x), ns):
  match p v:
    case Nil{} +y:
      kv.top(y, m0, m, x, ns, k)
    case Con{True{}, +rest} Bk.Term.Tup{+q, +a, +b}:
      (_, r) = k
      (ka, _) = r
      sub.l(El.Quan.live(q), rest, a, u, FV(m0, m, Cl(m0, rest, PM.Fd(2n, m0, x)), ns), e,
        el => e2 => kv.at(rest, a, m0, m, PM.Fd(2n, m0, x), ns, u, ka, e2))
    case Con{False{}, +rest} Bk.Term.Tup{+q, +a, +b}:
      (_, r) = k
      (_, kb) = r
      kv.at(rest, b, m0, m, PM.Fd(3n, m0, x), ns, u, kb, e)
    case Con{d, rest} Bk.Term.Var{+o0}:
      Empty.absurd(FV(m0, m, Cl(m0, Con{d, rest}, x), ns), mt.ne(u, e))
    case Con{d, rest} Bk.Term.Ref{+o0}:
      Empty.absurd(FV(m0, m, Cl(m0, Con{d, rest}, x), ns), mt.ne(u, e))
    case Con{d, rest} Bk.Term.Ann{+o0, +o1}:
      Empty.absurd(FV(m0, m, Cl(m0, Con{d, rest}, x), ns), mt.ne(u, e))
    case Con{d, rest} Bk.Term.Let{+o0, +o1, +o2}:
      Empty.absurd(FV(m0, m, Cl(m0, Con{d, rest}, x), ns), mt.ne(u, e))
    case Con{d, rest} Bk.Term.Typ{+o0}:
      Empty.absurd(FV(m0, m, Cl(m0, Con{d, rest}, x), ns), mt.ne(u, e))
    case Con{d, rest} Bk.Term.Min{+o0, +o1}:
      Empty.absurd(FV(m0, m, Cl(m0, Con{d, rest}, x), ns), mt.ne(u, e))
    case Con{d, rest} Bk.Term.All{+o0, +o1, +o2}:
      Empty.absurd(FV(m0, m, Cl(m0, Con{d, rest}, x), ns), mt.ne(u, e))
    case Con{d, rest} Bk.Term.Lam{+o0, +o1}:
      Empty.absurd(FV(m0, m, Cl(m0, Con{d, rest}, x), ns), mt.ne(u, e))
    case Con{d, rest} Bk.Term.App{+o0, +o1, +o2}:
      Empty.absurd(FV(m0, m, Cl(m0, Con{d, rest}, x), ns), mt.ne(u, e))
    case Con{d, rest} Bk.Term.Sig{+o0, +o1, +o2}:
      Empty.absurd(FV(m0, m, Cl(m0, Con{d, rest}, x), ns), mt.ne(u, e))
    case Con{d, rest} Bk.Term.Prj{+o0}:
      Empty.absurd(FV(m0, m, Cl(m0, Con{d, rest}, x), ns), mt.ne(u, e))
    case Con{d, rest} Bk.Term.Enu{+o0}:
      Empty.absurd(FV(m0, m, Cl(m0, Con{d, rest}, x), ns), mt.ne(u, e))
    case Con{d, rest} Bk.Term.Lab{+o0}:
      Empty.absurd(FV(m0, m, Cl(m0, Con{d, rest}, x), ns), mt.ne(u, e))
    case Con{d, rest} Bk.Term.Mat{+o0, +o1, +o2}:
      Empty.absurd(FV(m0, m, Cl(m0, Con{d, rest}, x), ns), mt.ne(u, e))
    case Con{d, rest} Bk.Term.Efq{}:
      Empty.absurd(FV(m0, m, Cl(m0, Con{d, rest}, x), ns), mt.ne(u, e))
    case Con{d, rest} Bk.Term.Eql{+o0, +o1, +o2}:
      Empty.absurd(FV(m0, m, Cl(m0, Con{d, rest}, x), ns), mt.ne(u, e))
    case Con{d, rest} Bk.Term.Rfl{}:
      Empty.absurd(FV(m0, m, Cl(m0, Con{d, rest}, x), ns), mt.ne(u, e))
    case Con{d, rest} Bk.Term.Rwt{+o0, +o1, +o2}:
      Empty.absurd(FV(m0, m, Cl(m0, Con{d, rest}, x), ns), mt.ne(u, e))

# a path reaches the same cell in m as in m0
def cl.keep(p: List<&2, Bool>, v: Bk.Term, +m0: Cr.Cir.Cells, +m: Cr.Cir.Cells, +x: U32, +ns: List<&2, U32>, -u: Bk.Term,
  k: KV(v, m0, m, x, ns), e: {Sub(p, v) == Some{u} : Maybe<&2, Bk.Term>}) -> {Cl(m, p, x) == Cl(m0, p, x) : U32}:
  match p v:
    case Nil{} +y:
      {==}
    case Con{True{}, +rest} Bk.Term.Tup{+q, +a, +b}:
      (f, r) = k
      (_, fc) = f
      (e2c, _) = fc
      (ka, _) = r
      %Equal.sym(U32, PM.Fd(2n, m, x), PM.Fd(2n, m0, x), e2c) : {Cl(m, rest, _) == Cl(m0, rest, PM.Fd(2n, m0, x)) : U32}
      sub.l(El.Quan.live(q), rest, a, u, {Cl(m, rest, PM.Fd(2n, m0, x)) == Cl(m0, rest, PM.Fd(2n, m0, x)) : U32}, e,
        el => e2 => cl.keep(rest, a, m0, m, PM.Fd(2n, m0, x), ns, u, ka, e2))
    case Con{False{}, +rest} Bk.Term.Tup{+q, +a, +b}:
      (f, r) = k
      (_, fc) = f
      (_, e3c) = fc
      (_, kb) = r
      %Equal.sym(U32, PM.Fd(3n, m, x), PM.Fd(3n, m0, x), e3c) : {Cl(m, rest, _) == Cl(m0, rest, PM.Fd(3n, m0, x)) : U32}
      cl.keep(rest, b, m0, m, PM.Fd(3n, m0, x), ns, u, kb, e)
    case Con{d, rest} Bk.Term.Var{+o0}:
      Empty.absurd({Cl(m, Con{d, rest}, x) == Cl(m0, Con{d, rest}, x) : U32}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Ref{+o0}:
      Empty.absurd({Cl(m, Con{d, rest}, x) == Cl(m0, Con{d, rest}, x) : U32}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Ann{+o0, +o1}:
      Empty.absurd({Cl(m, Con{d, rest}, x) == Cl(m0, Con{d, rest}, x) : U32}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Let{+o0, +o1, +o2}:
      Empty.absurd({Cl(m, Con{d, rest}, x) == Cl(m0, Con{d, rest}, x) : U32}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Typ{+o0}:
      Empty.absurd({Cl(m, Con{d, rest}, x) == Cl(m0, Con{d, rest}, x) : U32}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Min{+o0, +o1}:
      Empty.absurd({Cl(m, Con{d, rest}, x) == Cl(m0, Con{d, rest}, x) : U32}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.All{+o0, +o1, +o2}:
      Empty.absurd({Cl(m, Con{d, rest}, x) == Cl(m0, Con{d, rest}, x) : U32}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Lam{+o0, +o1}:
      Empty.absurd({Cl(m, Con{d, rest}, x) == Cl(m0, Con{d, rest}, x) : U32}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.App{+o0, +o1, +o2}:
      Empty.absurd({Cl(m, Con{d, rest}, x) == Cl(m0, Con{d, rest}, x) : U32}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Sig{+o0, +o1, +o2}:
      Empty.absurd({Cl(m, Con{d, rest}, x) == Cl(m0, Con{d, rest}, x) : U32}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Prj{+o0}:
      Empty.absurd({Cl(m, Con{d, rest}, x) == Cl(m0, Con{d, rest}, x) : U32}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Enu{+o0}:
      Empty.absurd({Cl(m, Con{d, rest}, x) == Cl(m0, Con{d, rest}, x) : U32}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Lab{+o0}:
      Empty.absurd({Cl(m, Con{d, rest}, x) == Cl(m0, Con{d, rest}, x) : U32}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Mat{+o0, +o1, +o2}:
      Empty.absurd({Cl(m, Con{d, rest}, x) == Cl(m0, Con{d, rest}, x) : U32}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Efq{}:
      Empty.absurd({Cl(m, Con{d, rest}, x) == Cl(m0, Con{d, rest}, x) : U32}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Eql{+o0, +o1, +o2}:
      Empty.absurd({Cl(m, Con{d, rest}, x) == Cl(m0, Con{d, rest}, x) : U32}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Rfl{}:
      Empty.absurd({Cl(m, Con{d, rest}, x) == Cl(m0, Con{d, rest}, x) : U32}, mt.ne(u, e))
    case Con{d, rest} Bk.Term.Rwt{+o0, +o1, +o2}:
      Empty.absurd({Cl(m, Con{d, rest}, x) == Cl(m0, Con{d, rest}, x) : U32}, mt.ne(u, e))

# the frame from m to m2 extends one from m0 to m
def fv.ff(+m0: Cr.Cir.Cells, +m: Cr.Cir.Cells, +m2: Cr.Cir.Cells, +x: U32, +ns: List<&2, U32>, f: FV(m0, m, x, ns), g: FF(m, m2, x)) ->
  FV(m0, m2, x, ns):
  (f0, fc) = f
  (f2, f3) = fc
  (g0, gc) = g
  (g2, g3) = gc
  (Equal.trans(U32, PM.Fd(0n, m2, x), PM.Fd(0n, m, x), F0(m0, x, ns), g0, f0),
   (Equal.trans(U32, PM.Fd(2n, m2, x), PM.Fd(2n, m, x), PM.Fd(2n, m0, x), g2, f2),
    Equal.trans(U32, PM.Fd(3n, m2, x), PM.Fd(3n, m, x), PM.Fd(3n, m0, x), g3, f3)))

def kv.ft(v: Bk.Term, +m0: Cr.Cir.Cells, +m: Cr.Cir.Cells, +m2: Cr.Cir.Cells, +x: U32, +ns: List<&2, U32>, k: KV(v, m0, m, x, ns),
  g: FT(v, m0, m, m2, x)) -> KV(v, m0, m2, x, ns):
  match v:
    case Bk.Term.Tup{+q, +a, +b}:
      (f, r) = k
      (ka, kb) = r
      (gf, gr) = g
      (ga, gb) = gr
      (fv.ff(m0, m, m2, x, ns, f, gf), (kv.ft(a, m0, m, m2, PM.Fd(2n, m0, x), ns, ka, ga), kv.ft(b, m0, m, m2, PM.Fd(3n, m0, x), ns, kb, gb)))
    case Bk.Term.Var{+o0}:
      fv.ff(m0, m, m2, x, ns, k, g)
    case Bk.Term.Ref{+o0}:
      fv.ff(m0, m, m2, x, ns, k, g)
    case Bk.Term.Ann{+o0, +o1}:
      fv.ff(m0, m, m2, x, ns, k, g)
    case Bk.Term.Let{+o0, +o1, +o2}:
      fv.ff(m0, m, m2, x, ns, k, g)
    case Bk.Term.Typ{+o0}:
      fv.ff(m0, m, m2, x, ns, k, g)
    case Bk.Term.Min{+o0, +o1}:
      fv.ff(m0, m, m2, x, ns, k, g)
    case Bk.Term.All{+o0, +o1, +o2}:
      fv.ff(m0, m, m2, x, ns, k, g)
    case Bk.Term.Lam{+o0, +o1}:
      fv.ff(m0, m, m2, x, ns, k, g)
    case Bk.Term.App{+o0, +o1, +o2}:
      fv.ff(m0, m, m2, x, ns, k, g)
    case Bk.Term.Sig{+o0, +o1, +o2}:
      fv.ff(m0, m, m2, x, ns, k, g)
    case Bk.Term.Prj{+o0}:
      fv.ff(m0, m, m2, x, ns, k, g)
    case Bk.Term.Enu{+o0}:
      fv.ff(m0, m, m2, x, ns, k, g)
    case Bk.Term.Lab{+o0}:
      fv.ff(m0, m, m2, x, ns, k, g)
    case Bk.Term.Mat{+o0, +o1, +o2}:
      fv.ff(m0, m, m2, x, ns, k, g)
    case Bk.Term.Efq{}:
      fv.ff(m0, m, m2, x, ns, k, g)
    case Bk.Term.Eql{+o0, +o1, +o2}:
      fv.ff(m0, m, m2, x, ns, k, g)
    case Bk.Term.Rfl{}:
      fv.ff(m0, m, m2, x, ns, k, g)
    case Bk.Term.Rwt{+o0, +o1, +o2}:
      fv.ff(m0, m, m2, x, ns, k, g)

# writes of field 1 keep v's tree
def ft.put1(v: Bk.Term, +m0: Cr.Cir.Cells, +m: Cr.Cir.Cells, +ws: List<&2, PM.W1>, +x: U32) -> FT(v, m0, m, PM.Put1(ws, m), x):
  match v:
    case Bk.Term.Tup{+q, +a, +b}:
      (ff.put1s(ws, m, x), (ft.put1(a, m0, m, ws, PM.Fd(2n, m0, x)), ft.put1(b, m0, m, ws, PM.Fd(3n, m0, x))))
    case Bk.Term.Var{+o0}:
      ff.put1s(ws, m, x)
    case Bk.Term.Ref{+o0}:
      ff.put1s(ws, m, x)
    case Bk.Term.Ann{+o0, +o1}:
      ff.put1s(ws, m, x)
    case Bk.Term.Let{+o0, +o1, +o2}:
      ff.put1s(ws, m, x)
    case Bk.Term.Typ{+o0}:
      ff.put1s(ws, m, x)
    case Bk.Term.Min{+o0, +o1}:
      ff.put1s(ws, m, x)
    case Bk.Term.All{+o0, +o1, +o2}:
      ff.put1s(ws, m, x)
    case Bk.Term.Lam{+o0, +o1}:
      ff.put1s(ws, m, x)
    case Bk.Term.App{+o0, +o1, +o2}:
      ff.put1s(ws, m, x)
    case Bk.Term.Sig{+o0, +o1, +o2}:
      ff.put1s(ws, m, x)
    case Bk.Term.Prj{+o0}:
      ff.put1s(ws, m, x)
    case Bk.Term.Enu{+o0}:
      ff.put1s(ws, m, x)
    case Bk.Term.Lab{+o0}:
      ff.put1s(ws, m, x)
    case Bk.Term.Mat{+o0, +o1, +o2}:
      ff.put1s(ws, m, x)
    case Bk.Term.Efq{}:
      ff.put1s(ws, m, x)
    case Bk.Term.Eql{+o0, +o1, +o2}:
      ff.put1s(ws, m, x)
    case Bk.Term.Rfl{}:
      ff.put1s(ws, m, x)
    case Bk.Term.Rwt{+o0, +o1, +o2}:
      ff.put1s(ws, m, x)

# so does a store of field 1
def ft.f1(v: Bk.Term, +m0: Cr.Cir.Cells, +m: Cr.Cir.Cells, +z: U32, +w: U32, +x: U32) -> FT(v, m0, m, X.X.put(m, 1n, z, w), x):
  match v:
    case Bk.Term.Tup{+q, +a, +b}:
      (ff.put1(m, z, w, x), (ft.f1(a, m0, m, z, w, PM.Fd(2n, m0, x)), ft.f1(b, m0, m, z, w, PM.Fd(3n, m0, x))))
    case Bk.Term.Var{+o0}:
      ff.put1(m, z, w, x)
    case Bk.Term.Ref{+o0}:
      ff.put1(m, z, w, x)
    case Bk.Term.Ann{+o0, +o1}:
      ff.put1(m, z, w, x)
    case Bk.Term.Let{+o0, +o1, +o2}:
      ff.put1(m, z, w, x)
    case Bk.Term.Typ{+o0}:
      ff.put1(m, z, w, x)
    case Bk.Term.Min{+o0, +o1}:
      ff.put1(m, z, w, x)
    case Bk.Term.All{+o0, +o1, +o2}:
      ff.put1(m, z, w, x)
    case Bk.Term.Lam{+o0, +o1}:
      ff.put1(m, z, w, x)
    case Bk.Term.App{+o0, +o1, +o2}:
      ff.put1(m, z, w, x)
    case Bk.Term.Sig{+o0, +o1, +o2}:
      ff.put1(m, z, w, x)
    case Bk.Term.Prj{+o0}:
      ff.put1(m, z, w, x)
    case Bk.Term.Enu{+o0}:
      ff.put1(m, z, w, x)
    case Bk.Term.Lab{+o0}:
      ff.put1(m, z, w, x)
    case Bk.Term.Mat{+o0, +o1, +o2}:
      ff.put1(m, z, w, x)
    case Bk.Term.Efq{}:
      ff.put1(m, z, w, x)
    case Bk.Term.Eql{+o0, +o1, +o2}:
      ff.put1(m, z, w, x)
    case Bk.Term.Rfl{}:
      ff.put1(m, z, w, x)
    case Bk.Term.Rwt{+o0, +o1, +o2}:
      ff.put1(m, z, w, x)

# a store at a cell z that is none of v's tree keeps it
def ft.st(v: Bk.Term, +m0: Cr.Cir.Cells, +m: Cr.Cir.Cells, +z: U32, +y: Cr.Cir.Cell, +x: U32, +h: {TN(v, m0, x, z) == True{} : Bool}) ->
  FT(v, m0, m, Cr.Cir.Cells.set(m, z, y), x):
  match v:
    case Bk.Term.Tup{+q, +a, +b}:
      +hx = PM.not.t(U32.is_eq(x, z), PM.and.l(Bool.not(U32.is_eq(x, z)), Bool.and(TN(a, m0, PM.Fd(2n, m0, x), z), TN(b, m0, PM.Fd(3n, m0, x), z)), h))
      +hr = PM.and.r(Bool.not(U32.is_eq(x, z)), Bool.and(TN(a, m0, PM.Fd(2n, m0, x), z), TN(b, m0, PM.Fd(3n, m0, x), z)), h)
      (ff.go(m, z, y, x, hx), (ft.st(a, m0, m, z, y, PM.Fd(2n, m0, x), PM.and.l(TN(a, m0, PM.Fd(2n, m0, x), z), TN(b, m0, PM.Fd(3n, m0, x), z), hr)),
        ft.st(b, m0, m, z, y, PM.Fd(3n, m0, x), PM.and.r(TN(a, m0, PM.Fd(2n, m0, x), z), TN(b, m0, PM.Fd(3n, m0, x), z), hr))))
    case Bk.Term.Var{+o0}:
      ff.go(m, z, y, x, PM.not.t(U32.is_eq(x, z), h))
    case Bk.Term.Ref{+o0}:
      ff.go(m, z, y, x, PM.not.t(U32.is_eq(x, z), h))
    case Bk.Term.Ann{+o0, +o1}:
      ff.go(m, z, y, x, PM.not.t(U32.is_eq(x, z), h))
    case Bk.Term.Let{+o0, +o1, +o2}:
      ff.go(m, z, y, x, PM.not.t(U32.is_eq(x, z), h))
    case Bk.Term.Typ{+o0}:
      ff.go(m, z, y, x, PM.not.t(U32.is_eq(x, z), h))
    case Bk.Term.Min{+o0, +o1}:
      ff.go(m, z, y, x, PM.not.t(U32.is_eq(x, z), h))
    case Bk.Term.All{+o0, +o1, +o2}:
      ff.go(m, z, y, x, PM.not.t(U32.is_eq(x, z), h))
    case Bk.Term.Lam{+o0, +o1}:
      ff.go(m, z, y, x, PM.not.t(U32.is_eq(x, z), h))
    case Bk.Term.App{+o0, +o1, +o2}:
      ff.go(m, z, y, x, PM.not.t(U32.is_eq(x, z), h))
    case Bk.Term.Sig{+o0, +o1, +o2}:
      ff.go(m, z, y, x, PM.not.t(U32.is_eq(x, z), h))
    case Bk.Term.Prj{+o0}:
      ff.go(m, z, y, x, PM.not.t(U32.is_eq(x, z), h))
    case Bk.Term.Enu{+o0}:
      ff.go(m, z, y, x, PM.not.t(U32.is_eq(x, z), h))
    case Bk.Term.Lab{+o0}:
      ff.go(m, z, y, x, PM.not.t(U32.is_eq(x, z), h))
    case Bk.Term.Mat{+o0, +o1, +o2}:
      ff.go(m, z, y, x, PM.not.t(U32.is_eq(x, z), h))
    case Bk.Term.Efq{}:
      ff.go(m, z, y, x, PM.not.t(U32.is_eq(x, z), h))
    case Bk.Term.Eql{+o0, +o1, +o2}:
      ff.go(m, z, y, x, PM.not.t(U32.is_eq(x, z), h))
    case Bk.Term.Rfl{}:
      ff.go(m, z, y, x, PM.not.t(U32.is_eq(x, z), h))
    case Bk.Term.Rwt{+o0, +o1, +o2}:
      ff.go(m, z, y, x, PM.not.t(U32.is_eq(x, z), h))

# two frames in turn
def ft.trans(v: Bk.Term, +m0: Cr.Cir.Cells, +m: Cr.Cir.Cells, +m1: Cr.Cir.Cells, +m2: Cr.Cir.Cells, +x: U32,
  a: FT(v, m0, m1, m2, x), b: FT(v, m0, m, m1, x)) -> FT(v, m0, m, m2, x):
  match v:
    case Bk.Term.Tup{+q, +p, +r}:
      (af, ar) = a
      (ap, aq) = ar
      (bf, br) = b
      (bp, bq) = br
      (ff.trans(m, m1, m2, x, af, bf), (ft.trans(p, m0, m, m1, m2, PM.Fd(2n, m0, x), ap, bp), ft.trans(r, m0, m, m1, m2, PM.Fd(3n, m0, x), aq, bq)))
    case Bk.Term.Var{+o0}:
      ff.trans(m, m1, m2, x, a, b)
    case Bk.Term.Ref{+o0}:
      ff.trans(m, m1, m2, x, a, b)
    case Bk.Term.Ann{+o0, +o1}:
      ff.trans(m, m1, m2, x, a, b)
    case Bk.Term.Let{+o0, +o1, +o2}:
      ff.trans(m, m1, m2, x, a, b)
    case Bk.Term.Typ{+o0}:
      ff.trans(m, m1, m2, x, a, b)
    case Bk.Term.Min{+o0, +o1}:
      ff.trans(m, m1, m2, x, a, b)
    case Bk.Term.All{+o0, +o1, +o2}:
      ff.trans(m, m1, m2, x, a, b)
    case Bk.Term.Lam{+o0, +o1}:
      ff.trans(m, m1, m2, x, a, b)
    case Bk.Term.App{+o0, +o1, +o2}:
      ff.trans(m, m1, m2, x, a, b)
    case Bk.Term.Sig{+o0, +o1, +o2}:
      ff.trans(m, m1, m2, x, a, b)
    case Bk.Term.Prj{+o0}:
      ff.trans(m, m1, m2, x, a, b)
    case Bk.Term.Enu{+o0}:
      ff.trans(m, m1, m2, x, a, b)
    case Bk.Term.Lab{+o0}:
      ff.trans(m, m1, m2, x, a, b)
    case Bk.Term.Mat{+o0, +o1, +o2}:
      ff.trans(m, m1, m2, x, a, b)
    case Bk.Term.Efq{}:
      ff.trans(m, m1, m2, x, a, b)
    case Bk.Term.Eql{+o0, +o1, +o2}:
      ff.trans(m, m1, m2, x, a, b)
    case Bk.Term.Rfl{}:
      ff.trans(m, m1, m2, x, a, b)
    case Bk.Term.Rwt{+o0, +o1, +o2}:
      ff.trans(m, m1, m2, x, a, b)

# Allocation
# ----------
#
# M.alloc by alloc.post, within a budget B: with a cell in the pend list
# (pend /= 0) M.alloc takes it and runs no Stmt.alloc, so it does not run out
# of memory; with none (pend = 0, so ps is empty) out of memory needs fewer
# than 20 (nx + 1) bytes, which the caller's hb puts within B.

# what alloc.post says of the state st2 after M.alloc(r)
def AlQ(+dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +r: Nat, +keep: List<&2, Nat>,
  +os: List<&2, PM.Rt>, +bs: List<&2, PM.Rt>, +fs: List<&2, PM.AF>, +sp: U32, +ps: List<&2, U32>, +xs: List<&2, PM.TmpE>,
  +st2: Cr.Cir.State) -> Type:
  PM.P2(PM.Same(regs, fi, im, lim, inp, keep, st2),
    PM.Ex(U32, z => PM.Ex(U32, pend2 => PM.Ex(List<&2, U32>, ps2 =>
      PM.P2(PM.Reg(st2, r, z), PM.P2(PM.Reg(st2, 3n, pend2),
      PM.P2({Cr.Cir.Cells.get(PM.St.cells(st2), z) == Cr.Cir.Cell.zero() : Cr.Cir.Cell},
      PM.P2({PM.Own(fi, PM.St.next(st2), z) == True{} : Bool}, PM.P2({PM.Mem(ps2, z) == False{} : Bool},
      PM.P2({Bool.or(PM.Mem(ps, z), U32.is_eq(z, nx)) == True{} : Bool},
      PM.P2({Bool.or(Bool.and(PM.Mem(ps, z), U32.is_eq(PM.St.next(st2), nx)),
           Bool.and(PM.Pend.none(ps), Bool.and(U32.is_eq(z, nx), U32.is_eq(PM.St.next(st2), U32.inc(nx))))) == True{} : Bool},
      PM.P2(PM.Ex(List<&2, PM.W1>, ws => PM.P2({PM.St.cells(st2) == Cr.Cir.Cells.set(PM.Put1(ws, m), z, Cr.Cir.Cell.zero()) : Cr.Cir.Cells},
        {PM.Took(ws, ps, m) == True{} : Bool})),
      PM.P2({PM.PsSub(ps2, ps, m) == True{} : Bool},
      PM.P2({PM.Ptr(Nat.sub(U32.to_nat(PM.St.next(st2)), U32.to_nat(fi)), PM.St.cells(st2), fi, ps2, PM.Rt.cells(os), z) == 0n : Nat},
      PM.P2(PM.HSK(dk, ds, ks, img, PM.St.cells(st2), PM.St.next(st2), fi, im, os, bs, fs, sp, pend2, ps2),
        PM.Ex(List<&2, PM.Rt>, zs2 => PM.AccK(dk, ds, ks, img, PM.St.cells(st2), PM.St.next(st2), fi, im, os, Con{PM.TmpE{z, Nil{}}, xs}, sp, fs, ps2, zs2))))))))))))))))) & PM.AlFr(m, ps, nx, st2)

# with a cell in the pend list, M.alloc runs no Stmt.alloc
def al.nooom(+F: Nat, +r: Nat, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32,
  +inp: List<&2, Word(8n)>, +pend: U32, hp: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>},
  hz: {U32.is_eq(pend, 0) == False{} : Bool}) -> PM.NoOom(Cr.Cir.exec(F, Mc.M.alloc(r), X.X.st(regs, m, nx, fi, im, pg, lim, inp))):
  +S = X.X.st(regs, m, nx, fi, im, pg, lim, inp)
  +a = Mc.M.alloc(r)
  %X.rw.if.t(F, X.sel.c(a), X.sel.t(a), X.sel.e(a), S, 1, X.ev.ne0(3n, S, pend, hp, hz), {==}) : PM.NoOom(_)
  noal(F, X.sel.t(a), S, {==})

# alloc.post's PostB within the budget B
def al.bud(b: Bool, +F: Nat, +r: Nat, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32,
  +inp: List<&2, Word(8n)>, +pend: U32, +ps: List<&2, U32>, -Q: Cr.Cir.State -> Type, +B: Nat,
  eb: {U32.is_eq(pend, 0) == b : Bool}, hp: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>}, hc: PM.Chain(ps, m, pend),
  hb: {PM.Pend.none(ps) == True{} : Bool} -> N.Le(Nat.mul(20n, Nat.add(U32.to_nat(nx), 1n)), B),
  h: PM.PostB(False{}, Cr.Cir.exec(F, Mc.M.alloc(r), X.X.st(regs, m, nx, fi, im, pg, lim, inp)), Q, s => st2 => Empty,
    Nat.mul(20n, Nat.add(U32.to_nat(nx), 1n)), lim)) ->
  PM.PostB(False{}, Cr.Cir.exec(F, Mc.M.alloc(r), X.X.st(regs, m, nx, fi, im, pg, lim, inp)), Q, s => st2 => Empty, B, lim):
  match b:
    case True{}:
      PM.postb.wk(False{}, Cr.Cir.exec(F, Mc.M.alloc(r), X.X.st(regs, m, nx, fi, im, pg, lim, inp)), Q, s => st2 => Empty,
        Nat.mul(20n, Nat.add(U32.to_nat(nx), 1n)), B, lim, h, hb(chain.none(ps, m, pend, hc, eb)))
    case False{}:
      postb.no(Cr.Cir.exec(F, Mc.M.alloc(r), X.X.st(regs, m, nx, fi, im, pg, lim, inp)), Q, s => st2 => Empty,
        Nat.mul(20n, Nat.add(U32.to_nat(nx), 1n)), B, lim, h, al.nooom(F, r, regs, m, nx, fi, im, pg, lim, inp, pend, hp, eb))

# M.alloc(r) gives what alloc.post says, within the budget B when a new cell
# fits it
def al.ok(+F: Nat, +dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +r: Nat, +keep: List<&2, Nat>,
  +os: List<&2, PM.Rt>, +bs: List<&2, PM.Rt>, +fs: List<&2, PM.AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>, +xs: List<&2, PM.TmpE>,
  +zs: List<&2, PM.Rt>, -R: Cr.Cir.State -> Type, +B: Nat,
  +hs: PM.HSK(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps),
  hac: PM.AccK(dk, ds, ks, img, m, nx, fi, im, os, xs, sp, fs, ps, zs),
  hl: {List.length(&2, U32, regs) == 63n : Nat},
  +hp: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>},
  hr: {Bool.and(Nat.is_lt(r, 63n), Bool.not(Nat.is_eq(r, 3n))) == True{} : Bool},
  hk: {PM.Disj(keep, [r, 3n, 4n, 5n, 6n, 7n]) == True{} : Bool},
  hb: {PM.Pend.none(ps) == True{} : Bool} -> N.Le(Nat.mul(20n, Nat.add(U32.to_nat(nx), 1n)), B),
  k: @st2: Cr.Cir.State -> AlQ(dk, ds, ks, img, regs, m, nx, fi, im, lim, inp, r, keep, os, bs, fs, sp, ps, xs, st2) -> R(st2)) ->
  W.Ok(Cr.Cir.exec(F, Mc.M.alloc(r), X.X.st(regs, m, nx, fi, im, pg, lim, inp)), R, B, lim):
  +o = Cr.Cir.exec(F, Mc.M.alloc(r), X.X.st(regs, m, nx, fi, im, pg, lim, inp))
  W.OkMono(o, st2 => AlQ(dk, ds, ks, img, regs, m, nx, fi, im, lim, inp, r, keep, os, bs, fs, sp, ps, xs, st2), R, B, lim,
    al.bud(U32.is_eq(pend, 0), F, r, regs, m, nx, fi, im, pg, lim, inp, pend, ps,
      st2 => AlQ(dk, ds, ks, img, regs, m, nx, fi, im, lim, inp, r, keep, os, bs, fs, sp, ps, xs, st2), B, {==}, hp,
      heap.chain(m, nx, fi, im, PM.Rt.cells(os), pend, ps, hsk.heap(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps, hs)), hb,
      PM.alloc.post(F, dk, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, r, keep, os, bs, fs, sp, pend, ps, xs, zs, hs, hac, hl, hp, hr, hk)),
    k)

# The K.check cells
# -----------------
#
# A K.check cell, made at the cell z that M.alloc gives (all zeros, nothing
# points to it, the first temporary), holds the cell of a part of v in field
# 2 and the next entry of the stack in field 1; it holds no pointer that Fs
# counts. Its six stores (M.make's five and the link) are one store of the
# whole cell, which store.post takes.

# a cell of the machine's own is a cell
def own.cell(+i: U32, +im: U32, +fi: U32, +nx: U32, h: {PM.Own(fi, nx, i) == True{} : Bool}) -> {Cr.Cir.is_cell(i, im, fi, nx) == True{} : Bool}:
  PM.or.r(Bool.and(Bool.not(U32.is_zero(i)), U32.is_le(i, im)), Bool.and(U32.is_le(fi, i), U32.is_lt(i, nx)), h)

# a zero cell holds no pointer (the table's mask of tag 0 is 0)
def zero.fs(+m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ps: List<&2, U32>, +z: U32, tbl: PM.Tbl(m, im, fi, nx),
  ez: {Cr.Cir.Cells.get(m, z) == Cr.Cir.Cell.zero() : Cr.Cir.Cell}) -> {PM.Fs(m, ps, z) == Nil{} : List<&2, U32>}:
  %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(m, z), Cr.Cir.Cell.zero(), ez) :
    {PM.FsK(U32.is_lt(PM.TgW(Cr.Cir.Cell.get(0n, _)), 19), PM.Fd(2n, m, U32.add(272, PM.TgW(Cr.Cir.Cell.get(0n, _)))), _, ps, z) == Nil{} : List<&2, U32>}
  %Equal.sym(U32, PM.Fd(2n, m, U32.add(272, PM.A.tag(Bk.Term.Var{0n}))), PM.Mask(Bk.Term.Var{0n}), PM.tbl.mask(m, im, fi, nx, Bk.Term.Var{0n}, tbl)) :
    {PM.Fs.term(_, 0, 0, 0) == Nil{} : List<&2, U32>}
  {==}

# the K.check cell with the part y and the link w
def CK(+w: U32, +y: U32) -> Cr.Cir.Cell:
  Cr.Cir.Cell{44, w, y, 0, 0}

# M.make's stores and the link, at the zero cell z: one store of CK
def ck.cells(+m: Cr.Cir.Cells, +z: U32, +y: U32, +w: U32) ->
  {X.X.put(X.X.put(X.X.put(X.X.put(X.X.put(X.X.put(Cr.Cir.Cells.set(m, z, Cr.Cir.Cell.zero()), 0n, z, 44), 1n, z, 1), 2n, z, y), 3n, z, 0), 4n, z, 0), 1n, z, w) ==
    Cr.Cir.Cells.set(Cr.Cir.Cells.set(m, z, Cr.Cir.Cell.zero()), z, CK(w, y)) : Cr.Cir.Cells}:
  +c0 = Cr.Cir.Cell.zero()
  +c1 = Cr.Cir.Cell.set(0n, c0, 44)
  +c2 = Cr.Cir.Cell.set(1n, c1, 1)
  +c3 = Cr.Cir.Cell.set(2n, c2, y)
  +c4 = Cr.Cir.Cell.set(3n, c3, 0)
  +c5 = Cr.Cir.Cell.set(4n, c4, 0)
  +rhs = Cr.Cir.Cells.set(Cr.Cir.Cells.set(m, z, c0), z, CK(w, y))
  %X.Ce.put_set(m, z, c0, 0n, 44) :
    {X.X.put(X.X.put(X.X.put(X.X.put(X.X.put(_, 1n, z, 1), 2n, z, y), 3n, z, 0), 4n, z, 0), 1n, z, w) == rhs : Cr.Cir.Cells}
  %X.Ce.put_set(m, z, c1, 1n, 1) :
    {X.X.put(X.X.put(X.X.put(X.X.put(_, 2n, z, y), 3n, z, 0), 4n, z, 0), 1n, z, w) == rhs : Cr.Cir.Cells}
  %X.Ce.put_set(m, z, c2, 2n, y) :
    {X.X.put(X.X.put(X.X.put(_, 3n, z, 0), 4n, z, 0), 1n, z, w) == rhs : Cr.Cir.Cells}
  %X.Ce.put_set(m, z, c3, 3n, 0) :
    {X.X.put(X.X.put(_, 4n, z, 0), 1n, z, w) == rhs : Cr.Cir.Cells}
  %X.Ce.put_set(m, z, c4, 4n, 0) :
    {X.X.put(_, 1n, z, w) == rhs : Cr.Cir.Cells}
  %X.Ce.put_set(m, z, c5, 1n, w) :
    {_ == rhs : Cr.Cir.Cells}
  X.Ce.set_set(m, z, c0, CK(w, y))

# store.post at a K.check cell: HSK and AccK hold with it
def ck.post(+dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32,
  +fi: U32, +im: U32, +os: List<&2, PM.Rt>, +bs: List<&2, PM.Rt>, +fs: List<&2, PM.AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>,
  +z: U32, +y: U32, +w: U32, +xs: List<&2, PM.TmpE>, +zs: List<&2, PM.Rt>,
  +hs: PM.HSK(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps),
  hac: PM.AccK(dk, ds, ks, img, m, nx, fi, im, os, Con{PM.TmpE{z, Nil{}}, xs}, sp, fs, ps, zs),
  +ez: {Cr.Cir.Cells.get(m, z) == Cr.Cir.Cell.zero() : Cr.Cir.Cell}, ho: {PM.Own(fi, nx, z) == True{} : Bool},
  hm: {PM.Mem(ps, z) == False{} : Bool},
  hz0: {PM.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, PM.Rt.cells(os), z) == 0n : Nat}) ->
  PM.P2(PM.HSK(dk, ds, ks, img, Cr.Cir.Cells.set(m, z, CK(w, y)), nx, fi, im, os, bs, fs, sp, pend, ps),
    PM.AccK(dk, ds, ks, img, Cr.Cir.Cells.set(m, z, CK(w, y)), nx, fi, im, os, Con{PM.TmpE{z, Nil{}}, xs}, sp, fs, ps, zs)):
  +x = CK(w, y)
  +M = Cr.Cir.Cells.set(m, z, x)
  +tbl = PM.img.tbl(dk, ds, ks, img, m, im, fi, nx, hsk.img(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps, hs))
  +ez2 = Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(m, z), Cr.Cir.Cell.zero(), ez)
  PM.store.post(dk, ds, ks, img, m, nx, fi, im, Nil{}, os, bs, fs, sp, pend, ps, z, x, Con{PM.TmpE{z, Nil{}}, xs}, zs, hs, hac, {==},
    hsk.held(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps, hs), ho, hm,
    (%ez2 : {U32.is_ne(U32.and(Cr.Cir.Cell.get(0n, _), 1024), 0) == False{} : Bool}; {==}),
    (%ez2 : {Bool.or(U32.is_lt(U32.and(Cr.Cir.Cell.get(0n, _), 63), 32), U32.is_le(41, U32.and(Cr.Cir.Cell.get(0n, _), 63))) == True{} : Bool}; {==}),
    hz0, zero.fs(m, im, fi, nx, ps, z, tbl, ez), {==}, {==},
    (%Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M, z), x, X.Ce.get_set(m, z, x)) :
      {PM.FsK(U32.is_lt(PM.TgW(Cr.Cir.Cell.get(0n, _)), 19), PM.Fd(2n, M, U32.add(272, PM.TgW(Cr.Cir.Cell.get(0n, _)))), _, ps, z) == Nil{} : List<&2, U32>};
      {==}))

# Release
# -------

# a PostB of an outcome known to be next{st} is its Q of st
def postb.at(o: Cr.Cir.Out, +st: Cr.Cir.State, -Q: Cr.Cir.State -> Type, -H: U32 -> Cr.Cir.State -> Type, -B: Nat, -lim: U32,
  eo: {o == Cr.Cir.Out.next{st} : Cr.Cir.Out}, h: PM.PostB(False{}, o, Q, H, B, lim)) -> Q(st):
  (%eo : PM.PostB(False{}, _, Q, H, B, lim); h)

# M.release(r) of the cell z: a store of field 1, and pend gets z
def rl.eq(+f: Nat, +r: Nat, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32,
  +inp: List<&2, Word(8n)>, +z: U32, +pend: U32, hl: {List.length(&2, U32, regs) == 63n : Nat},
  +hc: {List.get(&2, U32, regs, r) == Some{z} : Maybe<&2, U32>}, hp: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>},
  hz: {Cr.Cir.is_cell(z, im, fi, nx) == True{} : Bool}) ->
  {Cr.Cir.exec(f, Mc.M.release(r), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) ==
    Cr.Cir.Out.next{X.X.st(List.set(&2, U32, regs, 3n, z), X.X.put(m, 1n, z, pend), nx, fi, im, pg, lim, inp)} : Cr.Cir.Out}:
  +S0 = X.X.st(regs, m, nx, fi, im, pg, lim, inp)
  +S1 = X.X.st(regs, X.X.put(m, 1n, z, pend), nx, fi, im, pg, lim, inp)
  +S2 = X.X.st(List.set(&2, U32, regs, 3n, z), X.X.put(m, 1n, z, pend), nx, fi, im, pg, lim, inp)
  +a = Mc.M.release(r)
  +rhs = {Cr.Cir.Out.next{S2} : Cr.Cir.Out}
  %X.rw.seq(f, X.sel.a(a), X.sel.b(a), S0, S1, X.run.store(f, 1n, Mc.M.g(r), Mc.M.g(3n), S0, z, pend, hc, hp, hz)) : {_ == rhs : Cr.Cir.Out}
  %X.rw.seq(f, X.sel.a(X.sel.b(a)), X.sel.b(X.sel.b(a)), S1, S2, X.run.set(f, 3n, Mc.M.g(r), S1, z, hc, hl, {==})) :
    {_ == rhs : Cr.Cir.Out}
  X.run.nop(f, S2)

# what release.post says of the state st2 after M.release
def RlQ(+dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +os: List<&2, PM.Rt>,
  +bs: List<&2, PM.Rt>, +fs: List<&2, PM.AF>, +sp: U32, +ps: List<&2, U32>, +z: U32, +xs: List<&2, PM.TmpE>,
  +zs: List<&2, PM.Rt>, +st2: Cr.Cir.State) -> Data:
  PM.Ex(Cr.Cir.Cells, m2 => PM.P2({st2 == Cr.Cir.State{List.set(&2, U32, regs, 3n, z), m2, nx, fi, im, pg, lim, inp, Nil{}, 0} : Cr.Cir.State},
    PM.P2({PM.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m2, fi) == PM.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi) : Nat},
    PM.P2(PM.HSK(dk, ds, ks, img, m2, nx, fi, im, os, bs, fs, sp, z, Con{z, ps}),
      PM.AccK(dk, ds, ks, img, m2, nx, fi, im, os, xs, sp, fs, Con{z, ps}, zs)))))

# release.post's cells are the store's
def rl.cells(+dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +os: List<&2, PM.Rt>,
  +bs: List<&2, PM.Rt>, +fs: List<&2, PM.AF>, +sp: U32, +ps: List<&2, U32>, +z: U32, +pend: U32, +xs: List<&2, PM.TmpE>,
  +zs: List<&2, PM.Rt>,
  q: RlQ(dk, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, os, bs, fs, sp, ps, z, xs, zs,
    X.X.st(List.set(&2, U32, regs, 3n, z), X.X.put(m, 1n, z, pend), nx, fi, im, pg, lim, inp))) ->
  PM.P2({PM.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), X.X.put(m, 1n, z, pend), fi) == PM.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi) : Nat},
    PM.P2(PM.HSK(dk, ds, ks, img, X.X.put(m, 1n, z, pend), nx, fi, im, os, bs, fs, sp, z, Con{z, ps}),
      PM.AccK(dk, ds, ks, img, X.X.put(m, 1n, z, pend), nx, fi, im, os, xs, sp, fs, Con{z, ps}, zs))):
  match q:
    case Tuple{m2, Tuple{e, h}}:
      +ec = Equal.cong(Cr.Cir.State, Cr.Cir.Cells, st => PM.St.cells(st),
        X.X.st(List.set(&2, U32, regs, 3n, z), X.X.put(m, 1n, z, pend), nx, fi, im, pg, lim, inp),
        Cr.Cir.State{List.set(&2, U32, regs, 3n, z), m2, nx, fi, im, pg, lim, inp, Nil{}, 0}, e)
      (%Equal.sym(Cr.Cir.Cells, X.X.put(m, 1n, z, pend), m2, ec) :
        PM.P2({PM.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), _, fi) == PM.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi) : Nat},
          PM.P2(PM.HSK(dk, ds, ks, img, _, nx, fi, im, os, bs, fs, sp, z, Con{z, ps}),
            PM.AccK(dk, ds, ks, img, _, nx, fi, im, os, xs, sp, fs, Con{z, ps}, zs))); h)

# M.release(r) of the first temporary z: release.post at the store's cells
def rl.at(+dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +r: Nat, +os: List<&2, PM.Rt>,
  +bs: List<&2, PM.Rt>, +fs: List<&2, PM.AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>, +z: U32, +xs: List<&2, PM.TmpE>,
  +zs: List<&2, PM.Rt>,
  hs: PM.HSK(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps),
  hac: PM.AccK(dk, ds, ks, img, m, nx, fi, im, os, Con{PM.TmpE{z, Nil{}}, xs}, sp, fs, ps, zs),
  +hz: {PM.Own(fi, nx, z) == True{} : Bool}, ht: {U32.is_lt(PM.Tg(m, z), 32) == False{} : Bool},
  hf: {PM.Fl(m, z, 1024) == False{} : Bool}, hm: {PM.Mem(ps, z) == False{} : Bool}, hfs: {PM.Fs(m, ps, z) == Nil{} : List<&2, U32>},
  +hl: {List.length(&2, U32, regs) == 63n : Nat}, +hc: {List.get(&2, U32, regs, r) == Some{z} : Maybe<&2, U32>},
  +hp: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>}) ->
  PM.P2({PM.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), X.X.put(m, 1n, z, pend), fi) == PM.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi) : Nat},
    PM.P2(PM.HSK(dk, ds, ks, img, X.X.put(m, 1n, z, pend), nx, fi, im, os, bs, fs, sp, z, Con{z, ps}),
      PM.AccK(dk, ds, ks, img, X.X.put(m, 1n, z, pend), nx, fi, im, os, xs, sp, fs, Con{z, ps}, zs))):
  +S2 = X.X.st(List.set(&2, U32, regs, 3n, z), X.X.put(m, 1n, z, pend), nx, fi, im, pg, lim, inp)
  rl.cells(dk, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, os, bs, fs, sp, ps, z, pend, xs, zs,
    postb.at(Cr.Cir.exec(0n, Mc.M.release(r), X.X.st(regs, m, nx, fi, im, pg, lim, inp)), S2,
      st2 => RlQ(dk, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, os, bs, fs, sp, ps, z, xs, zs, st2),
      s => st2 => Empty, 0n, lim,
      rl.eq(0n, r, regs, m, nx, fi, im, pg, lim, inp, z, pend, hl, hc, hp, own.cell(z, im, fi, nx, hz)),
      PM.release.post(0n, dk, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, r, os, bs, fs, sp, pend, ps, z, xs, zs, hs, hac, hz, ht, hf, hm,
        hfs, hl, hc, hp)))

# The flag DATA
# -------------

# is_eq is symmetric
def u32.ne.sym.at(c: Bool, +a: U32, +b: U32, ec: {U32.is_eq(b, a) == c : Bool}, h: {U32.is_eq(a, b) == False{} : Bool}) ->
  {c == False{} : Bool}:
  match c:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, PM.u32.ne(a, b, h, Equal.sym(U32, b, a, PM.u32.eq(b, a, ec))))

def u32.ne.sym(+a: U32, +b: U32, h: {U32.is_eq(a, b) == False{} : Bool}) -> {U32.is_eq(b, a) == False{} : Bool}:
  u32.ne.sym.at(U32.is_eq(b, a), a, b, {==}, h)

# field 0 of a cell after a store of field 0
def cs00(c: Cr.Cir.Cell, +v: U32) -> {Cr.Cir.Cell.get(0n, Cr.Cir.Cell.set(0n, c, v)) == v : U32}:
  match c:
    case Cr.Cir.Cell{a, b, x, y, z}:
      {==}

# the flagged cell y keeps fields 2 and 3, and field 0 gains DATA: y joins ns
def fv.flag.y(+m0: Cr.Cir.Cells, +m: Cr.Cir.Cells, +y: U32, +ns: List<&2, U32>, f: FV(m0, m, y, ns), hy: {PM.Mem(ns, y) == False{} : Bool}) ->
  FV(m0, X.X.put(m, 0n, y, U32.or(PM.Fd(0n, m, y), 512)), y, Con{y, ns}):
  (f0, fc) = f
  (f2, f3) = fc
  +V = U32.or(PM.Fd(0n, m, y), 512)
  +C = Cr.Cir.Cell.set(0n, Cr.Cir.Cells.get(m, y), V)
  +M = Cr.Cir.Cells.set(m, y, C)
  +gs = X.Ce.get_set(m, y, C)
  +A = U32.or(PM.Fd(0n, m0, y), 512)
  +B = PM.Fd(0n, m0, y)
  +e0 = Equal.trans(U32, PM.Fd(0n, M, y), Cr.Cir.Cell.get(0n, C), V,
    Equal.cong(Cr.Cir.Cell, U32, w => Cr.Cir.Cell.get(0n, w), Cr.Cir.Cells.get(M, y), C, gs), cs00(Cr.Cir.Cells.get(m, y), V))
  +e1 = Equal.cong(U32, U32, w => U32.or(w, 512), PM.Fd(0n, m, y), F0(m0, y, ns), f0)
  +e2 = Equal.cong(Bool, U32, b => U32.or(Bool.pick(U32, b, A, B), 512), PM.Mem(ns, y), False{}, hy)
  +e3 = Equal.cong(Bool, U32, b => Bool.pick(U32, Bool.or(b, PM.Mem(ns, y)), A, B), True{}, U32.is_eq(y, y),
    Equal.sym(Bool, U32.is_eq(y, y), True{}, PM.u32.refl(y)))
  (Equal.trans(U32, PM.Fd(0n, M, y), V, F0(m0, y, Con{y, ns}), e0,
     Equal.trans(U32, V, U32.or(F0(m0, y, ns), 512), F0(m0, y, Con{y, ns}), e1, Equal.trans(U32, U32.or(F0(m0, y, ns), 512), A, F0(m0, y, Con{y, ns}), e2, e3))),
   (Equal.trans(U32, PM.Fd(2n, M, y), PM.Fd(2n, m, y), PM.Fd(2n, m0, y),
      Equal.trans(U32, PM.Fd(2n, M, y), Cr.Cir.Cell.get(2n, C), PM.Fd(2n, m, y),
        Equal.cong(Cr.Cir.Cell, U32, w => Cr.Cir.Cell.get(2n, w), Cr.Cir.Cells.get(M, y), C, gs), s0.f2(Cr.Cir.Cells.get(m, y), V)), f2),
    Equal.trans(U32, PM.Fd(3n, M, y), PM.Fd(3n, m, y), PM.Fd(3n, m0, y),
      Equal.trans(U32, PM.Fd(3n, M, y), Cr.Cir.Cell.get(3n, C), PM.Fd(3n, m, y),
        Equal.cong(Cr.Cir.Cell, U32, w => Cr.Cir.Cell.get(3n, w), Cr.Cir.Cells.get(M, y), C, gs), s0.f3(Cr.Cir.Cells.get(m, y), V)), f3)))

def fv.flag.of(+m0: Cr.Cir.Cells, +M: Cr.Cir.Cells, +x: U32, +ns: List<&2, U32>, +y: U32, ey: {U32.is_eq(y, x) == False{} : Bool},
  h: FV(m0, M, x, ns)) -> FV(m0, M, x, Con{y, ns}):
  (h0, hc) = h
  (Equal.trans(U32, PM.Fd(0n, M, x), F0(m0, x, ns), F0(m0, x, Con{y, ns}), h0,
     Equal.cong(Bool, U32, b => Bool.pick(U32, Bool.or(b, PM.Mem(ns, x)), U32.or(PM.Fd(0n, m0, x), 512), PM.Fd(0n, m0, x)), False{},
       U32.is_eq(y, x), Equal.sym(Bool, U32.is_eq(y, x), False{}, ey))), hc)

# another cell of the tree keeps all it had
def fv.flag.ne(+m0: Cr.Cir.Cells, +m: Cr.Cir.Cells, +x: U32, +ns: List<&2, U32>, +y: U32, +eb: {U32.is_eq(x, y) == False{} : Bool},
  f: FV(m0, m, x, ns)) -> FV(m0, X.X.put(m, 0n, y, U32.or(PM.Fd(0n, m, y), 512)), x, Con{y, ns}):
  +V = U32.or(PM.Fd(0n, m, y), 512)
  +C = Cr.Cir.Cell.set(0n, Cr.Cir.Cells.get(m, y), V)
  +M = Cr.Cir.Cells.set(m, y, C)
  fv.flag.of(m0, M, x, ns, y, u32.ne.sym(x, y, eb), fv.ff(m0, m, M, x, ns, f, ff.go(m, y, C, x, eb)))

def fv.flag(b: Bool, +m0: Cr.Cir.Cells, +m: Cr.Cir.Cells, +x: U32, +ns: List<&2, U32>, +y: U32, eb: {U32.is_eq(x, y) == b : Bool},
  f: FV(m0, m, x, ns), hy: {PM.Mem(ns, y) == False{} : Bool}) -> FV(m0, X.X.put(m, 0n, y, U32.or(PM.Fd(0n, m, y), 512)), x, Con{y, ns}):
  match b:
    case True{}:
      +e = PM.u32.eq(x, y, eb)
      (%Equal.sym(U32, x, y, e) : FV(m0, X.X.put(m, 0n, y, U32.or(PM.Fd(0n, m, y), 512)), _, Con{y, ns});
        fv.flag.y(m0, m, y, ns, (%e : FV(m0, m, _, ns); f), hy))
    case False{}:
      fv.flag.ne(m0, m, x, ns, y, eb, f)

# the flag DATA at a cell y out of ns keeps v's tree, with y in ns
def kv.flag(v: Bk.Term, +m0: Cr.Cir.Cells, +m: Cr.Cir.Cells, +x: U32, +ns: List<&2, U32>, +y: U32, k: KV(v, m0, m, x, ns),
  +hy: {PM.Mem(ns, y) == False{} : Bool}) -> KV(v, m0, X.X.put(m, 0n, y, U32.or(PM.Fd(0n, m, y), 512)), x, Con{y, ns}):
  match v:
    case Bk.Term.Tup{+q, +a, +b}:
      (f, r) = k
      (ka, kb) = r
      (fv.flag(U32.is_eq(x, y), m0, m, x, ns, y, {==}, f, hy),
        (kv.flag(a, m0, m, PM.Fd(2n, m0, x), ns, y, ka, hy), kv.flag(b, m0, m, PM.Fd(3n, m0, x), ns, y, kb, hy)))

    case Bk.Term.Var{+o0}:
      fv.flag(U32.is_eq(x, y), m0, m, x, ns, y, {==}, k, hy)
    case Bk.Term.Ref{+o0}:
      fv.flag(U32.is_eq(x, y), m0, m, x, ns, y, {==}, k, hy)
    case Bk.Term.Ann{+o0, +o1}:
      fv.flag(U32.is_eq(x, y), m0, m, x, ns, y, {==}, k, hy)
    case Bk.Term.Let{+o0, +o1, +o2}:
      fv.flag(U32.is_eq(x, y), m0, m, x, ns, y, {==}, k, hy)
    case Bk.Term.Typ{+o0}:
      fv.flag(U32.is_eq(x, y), m0, m, x, ns, y, {==}, k, hy)
    case Bk.Term.Min{+o0, +o1}:
      fv.flag(U32.is_eq(x, y), m0, m, x, ns, y, {==}, k, hy)
    case Bk.Term.All{+o0, +o1, +o2}:
      fv.flag(U32.is_eq(x, y), m0, m, x, ns, y, {==}, k, hy)
    case Bk.Term.Lam{+o0, +o1}:
      fv.flag(U32.is_eq(x, y), m0, m, x, ns, y, {==}, k, hy)
    case Bk.Term.App{+o0, +o1, +o2}:
      fv.flag(U32.is_eq(x, y), m0, m, x, ns, y, {==}, k, hy)
    case Bk.Term.Sig{+o0, +o1, +o2}:
      fv.flag(U32.is_eq(x, y), m0, m, x, ns, y, {==}, k, hy)
    case Bk.Term.Prj{+o0}:
      fv.flag(U32.is_eq(x, y), m0, m, x, ns, y, {==}, k, hy)
    case Bk.Term.Enu{+o0}:
      fv.flag(U32.is_eq(x, y), m0, m, x, ns, y, {==}, k, hy)
    case Bk.Term.Lab{+o0}:
      fv.flag(U32.is_eq(x, y), m0, m, x, ns, y, {==}, k, hy)
    case Bk.Term.Mat{+o0, +o1, +o2}:
      fv.flag(U32.is_eq(x, y), m0, m, x, ns, y, {==}, k, hy)
    case Bk.Term.Efq{}:
      fv.flag(U32.is_eq(x, y), m0, m, x, ns, y, {==}, k, hy)
    case Bk.Term.Eql{+o0, +o1, +o2}:
      fv.flag(U32.is_eq(x, y), m0, m, x, ns, y, {==}, k, hy)
    case Bk.Term.Rfl{}:
      fv.flag(U32.is_eq(x, y), m0, m, x, ns, y, {==}, k, hy)
    case Bk.Term.Rwt{+o0, +o1, +o2}:
      fv.flag(U32.is_eq(x, y), m0, m, x, ns, y, {==}, k, hy)

# The cell that M.alloc takes is none of v's tree
# -----------------------------------------------

# a number below another is not it
def lt.neq.at(b: Bool, +x: U32, +y: U32, eb: {U32.is_eq(x, y) == b : Bool}, h: N.Le(1n+U32.to_nat(x), U32.to_nat(y))) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, N.not_succ_le(U32.to_nat(y), (%PM.u32.eq(x, y, eb) : N.Le(1n+U32.to_nat(_), U32.to_nat(y)); h)))

def lt.neq(+x: U32, +y: U32, h: N.Le(1n+U32.to_nat(x), U32.to_nat(y))) -> {U32.is_eq(x, y) == False{} : Bool}:
  lt.neq.at(U32.is_eq(x, y), x, y, {==}, h)

# a cell is not next, which is past the image and the cells from first
def cell.nx(+x: U32, +im: U32, +fi: U32, +nx: U32, hc: {Cr.Cir.is_cell(x, im, fi, nx) == True{} : Bool},
  +hif: {U32.is_lt(im, fi) == True{} : Bool}, +hfn: {U32.is_le(fi, nx) == True{} : Bool}) -> {U32.is_eq(x, nx) == False{} : Bool}:
  PM.or.cases(Bool.and(Bool.not(U32.is_zero(x)), U32.is_le(x, im)), Bool.and(U32.is_le(fi, x), U32.is_lt(x, nx)),
    {U32.is_eq(x, nx) == False{} : Bool}, hc,
    e => lt.neq(x, nx, N.le_trans(1n+U32.to_nat(x), U32.to_nat(fi), U32.to_nat(nx),
      N.le_trans(1n+U32.to_nat(x), 1n+U32.to_nat(im), U32.to_nat(fi),
        PM.u.le(x, im, PM.and.r(Bool.not(U32.is_zero(x)), U32.is_le(x, im), e)), PM.u.lt(im, fi, hif)), PM.u.le(fi, nx, hfn))),
    e => lt.neq(x, nx, PM.u.lt(x, nx, PM.and.r(U32.is_le(fi, x), U32.is_lt(x, nx), e))))

# x, out of ps and not nx, is not z, which is in ps or nx
def ne.z.at(b: Bool, +x: U32, +z: U32, +ps: List<&2, U32>, +nx: U32, eb: {U32.is_eq(x, z) == b : Bool},
  hpx: {PM.Mem(ps, x) == False{} : Bool}, hnx: {U32.is_eq(x, nx) == False{} : Bool},
  hz: {Bool.or(PM.Mem(ps, z), U32.is_eq(z, nx)) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      +e = PM.u32.eq(x, z, eb)
      Empty.absurd({True{} == False{} : Bool}, N.false_ne_true((%hnx : {Bool.or(False{}, _) == True{} : Bool};
        (%hpx : {Bool.or(_, U32.is_eq(x, nx)) == True{} : Bool};
          (%Equal.sym(U32, x, z, e) : {Bool.or(PM.Mem(ps, _), U32.is_eq(_, nx)) == True{} : Bool}; hz)))))

def ne.z(+x: U32, +z: U32, +ps: List<&2, U32>, +nx: U32, hpx: {PM.Mem(ps, x) == False{} : Bool}, hnx: {U32.is_eq(x, nx) == False{} : Bool},
  hz: {Bool.or(PM.Mem(ps, z), U32.is_eq(z, nx)) == True{} : Bool}) -> {Bool.not(U32.is_eq(x, z)) == True{} : Bool}:
  (%Equal.sym(Bool, U32.is_eq(x, z), False{}, ne.z.at(U32.is_eq(x, z), x, z, ps, nx, {==}, hpx, hnx, hz)) : {Bool.not(_) == True{} : Bool}; {==})

# the cell x of a term, held, is not M.alloc's cell z
def tn.nd(+dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32,
  +fi: U32, +im: U32, +ps: List<&2, U32>, +rs: List<&2, U32>, +x: U32, +z: U32, +t: Bk.Term, +h: PM.IsK(dk, ds, m, im, fi, nx, ks, img, x, t),
  +hx: {PM.Hd(m, nx, fi, ps, rs, x) == True{} : Bool}, +hp: PM.PendOK(ps, ps, m, fi, nx, rs), +hif: {U32.is_lt(im, fi) == True{} : Bool},
  +hfn: {U32.is_le(fi, nx) == True{} : Bool}, +hz: {Bool.or(PM.Mem(ps, z), U32.is_eq(z, nx)) == True{} : Bool}) ->
  {Bool.not(U32.is_eq(x, z)) == True{} : Bool}:
  ne.z(x, z, ps, nx, hd.np(ps, ps, m, nx, fi, rs, x, hp, hx), cell.nx(x, im, fi, nx, isk.cell(dk, ds, m, im, fi, nx, ks, img, x, t, h), hif, hfn), hz)

# the two parts of a pair of facts
def fst2(-A: Data, -B: Data, p: PM.P2(A, B)) -> A:
  match p:
    case Tuple{a, _}:
      a

def snd2(-A: Data, -B: Data, p: PM.P2(A, B)) -> B:
  match p:
    case Tuple{_, b}:
      b

# M.alloc's cell z (in ps, or nx) is none of the tree of v at x, a held cell of v
def tn.al(v: Bk.Term, +dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m0: Cr.Cir.Cells,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +ps: List<&2, U32>, +rs: List<&2, U32>, +x: U32, +ns: List<&2, U32>, +z: U32,
  k: KV(v, m0, m, x, ns), +h: PM.IsK(dk, ds, m, im, fi, nx, ks, img, x, v), +hx: {PM.Hd(m, nx, fi, ps, rs, x) == True{} : Bool},
  +hp: PM.PendOK(ps, ps, m, fi, nx, rs), +tbl: PM.Tbl(m, im, fi, nx), +hif: {U32.is_lt(im, fi) == True{} : Bool},
  +hfn: {U32.is_le(fi, nx) == True{} : Bool}, +hz: {Bool.or(PM.Mem(ps, z), U32.is_eq(z, nx)) == True{} : Bool}) ->
  {TN(v, m0, x, z) == True{} : Bool}:
  match v:
    case Bk.Term.Tup{+q, +a, +b}:
      (f, r) = k
      (_, fc) = f
      (e2a, e3a) = fc
      (ka, kb) = r
      (nd, r1) = h
      (hq, r2) = r1
      (pa, pb) = r2
      (spa, ia) = pa
      (spb, ib) = pb
      +e2 = {e2a : {PM.Fd(2n, m, x) == PM.Fd(2n, m0, x) : U32}}
      +e3 = {e3a : {PM.Fd(3n, m, x) == PM.Fd(3n, m0, x) : U32}}
      +hh = tup.hd(dk, ds, m, im, fi, nx, ks, img, ps, rs, x, q, a, b, tbl, h)
      +x2 = PM.Fd(2n, m0, x)
      +x3 = PM.Fd(3n, m0, x)
      +ta = tn.al(a, dk, ds, ks, img, m0, m, nx, fi, im, ps, rs, x2, ns, z, ka, (%e2 : PM.IsK(dk, ds, m, im, fi, nx, ks, img, _, a); ia),
        (%e2 : {PM.Hd(m, nx, fi, ps, rs, _) == True{} : Bool}; fst2({PM.Hd(m, nx, fi, ps, rs, PM.Fd(2n, m, x)) == True{} : Bool},
          {PM.Hd(m, nx, fi, ps, rs, PM.Fd(3n, m, x)) == True{} : Bool}, hh)), hp, tbl, hif, hfn, hz)
      +tb = tn.al(b, dk, ds, ks, img, m0, m, nx, fi, im, ps, rs, x3, ns, z, kb, (%e3 : PM.IsK(dk, ds, m, im, fi, nx, ks, img, _, b); ib),
        (%e3 : {PM.Hd(m, nx, fi, ps, rs, _) == True{} : Bool}; snd2({PM.Hd(m, nx, fi, ps, rs, PM.Fd(2n, m, x)) == True{} : Bool},
          {PM.Hd(m, nx, fi, ps, rs, PM.Fd(3n, m, x)) == True{} : Bool}, hh)), hp, tbl, hif, hfn, hz)
      PM.and.i(Bool.not(U32.is_eq(x, z)), Bool.and(TN(a, m0, x2, z), TN(b, m0, x3, z)),
        tn.nd(dk, ds, ks, img, m, nx, fi, im, ps, rs, x, z, Bk.Term.Tup{q, a, b}, h, hx, hp, hif, hfn, hz),
        PM.and.i(TN(a, m0, x2, z), TN(b, m0, x3, z), ta, tb))
    case Bk.Term.Var{+o0}:
      tn.nd(dk, ds, ks, img, m, nx, fi, im, ps, rs, x, z, Bk.Term.Var{o0}, h, hx, hp, hif, hfn, hz)
    case Bk.Term.Ref{+o0}:
      tn.nd(dk, ds, ks, img, m, nx, fi, im, ps, rs, x, z, Bk.Term.Ref{o0}, h, hx, hp, hif, hfn, hz)
    case Bk.Term.Ann{+o0, +o1}:
      tn.nd(dk, ds, ks, img, m, nx, fi, im, ps, rs, x, z, Bk.Term.Ann{o0, o1}, h, hx, hp, hif, hfn, hz)
    case Bk.Term.Let{+o0, +o1, +o2}:
      tn.nd(dk, ds, ks, img, m, nx, fi, im, ps, rs, x, z, Bk.Term.Let{o0, o1, o2}, h, hx, hp, hif, hfn, hz)
    case Bk.Term.Typ{+o0}:
      tn.nd(dk, ds, ks, img, m, nx, fi, im, ps, rs, x, z, Bk.Term.Typ{o0}, h, hx, hp, hif, hfn, hz)
    case Bk.Term.Min{+o0, +o1}:
      tn.nd(dk, ds, ks, img, m, nx, fi, im, ps, rs, x, z, Bk.Term.Min{o0, o1}, h, hx, hp, hif, hfn, hz)
    case Bk.Term.All{+o0, +o1, +o2}:
      tn.nd(dk, ds, ks, img, m, nx, fi, im, ps, rs, x, z, Bk.Term.All{o0, o1, o2}, h, hx, hp, hif, hfn, hz)
    case Bk.Term.Lam{+o0, +o1}:
      tn.nd(dk, ds, ks, img, m, nx, fi, im, ps, rs, x, z, Bk.Term.Lam{o0, o1}, h, hx, hp, hif, hfn, hz)
    case Bk.Term.App{+o0, +o1, +o2}:
      tn.nd(dk, ds, ks, img, m, nx, fi, im, ps, rs, x, z, Bk.Term.App{o0, o1, o2}, h, hx, hp, hif, hfn, hz)
    case Bk.Term.Sig{+o0, +o1, +o2}:
      tn.nd(dk, ds, ks, img, m, nx, fi, im, ps, rs, x, z, Bk.Term.Sig{o0, o1, o2}, h, hx, hp, hif, hfn, hz)
    case Bk.Term.Prj{+o0}:
      tn.nd(dk, ds, ks, img, m, nx, fi, im, ps, rs, x, z, Bk.Term.Prj{o0}, h, hx, hp, hif, hfn, hz)
    case Bk.Term.Enu{+o0}:
      tn.nd(dk, ds, ks, img, m, nx, fi, im, ps, rs, x, z, Bk.Term.Enu{o0}, h, hx, hp, hif, hfn, hz)
    case Bk.Term.Lab{+o0}:
      tn.nd(dk, ds, ks, img, m, nx, fi, im, ps, rs, x, z, Bk.Term.Lab{o0}, h, hx, hp, hif, hfn, hz)
    case Bk.Term.Mat{+o0, +o1, +o2}:
      tn.nd(dk, ds, ks, img, m, nx, fi, im, ps, rs, x, z, Bk.Term.Mat{o0, o1, o2}, h, hx, hp, hif, hfn, hz)
    case Bk.Term.Efq{}:
      tn.nd(dk, ds, ks, img, m, nx, fi, im, ps, rs, x, z, Bk.Term.Efq{}, h, hx, hp, hif, hfn, hz)
    case Bk.Term.Eql{+o0, +o1, +o2}:
      tn.nd(dk, ds, ks, img, m, nx, fi, im, ps, rs, x, z, Bk.Term.Eql{o0, o1, o2}, h, hx, hp, hif, hfn, hz)
    case Bk.Term.Rfl{}:
      tn.nd(dk, ds, ks, img, m, nx, fi, im, ps, rs, x, z, Bk.Term.Rfl{}, h, hx, hp, hif, hfn, hz)
    case Bk.Term.Rwt{+o0, +o1, +o2}:
      tn.nd(dk, ds, ks, img, m, nx, fi, im, ps, rs, x, z, Bk.Term.Rwt{o0, o1, o2}, h, hx, hp, hif, hfn, hz)

# The premises data.post and data.done of move_kit.bend (U6; U0 left them as ?TODO)
# -------------------------------------------------------------------------------

def K.data.post(f, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, r, keep, os, bs, fs, sp, pend, ps, c, v, xs, zs, hs, hac, hl, hc, hp, hr, hk):
  ?TODO

def K.data.done(ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, r, os, bs, fs, sp, pend, ps, c, v, hs, hl, hc, hp, hr):
  ?TODO
