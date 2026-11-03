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
import ./accounting.bend as A

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

# Registers
# ---------

# two Nats that is_eq says are equal are
def nat.eq(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({0n == 1n+q : Nat}, N.false_ne_true(h))
    case 1n+p 0n:
      Empty.absurd({1n+p == 0n : Nat}, N.false_ne_true(h))
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, x => 1n+x, p, q, nat.eq(p, q, h))

def mem.ne.b(b: Bool, +x: Nat, -rest: List<&2, Nat>, +r: Nat, +j: Nat, eb: {Nat.is_eq(x, r) == b : Bool},
  hm: {Bool.or(b, PM.Nat.mem(rest, r)) == True{} : Bool}, hx: {Nat.is_eq(x, j) == False{} : Bool},
  ih: {PM.Nat.mem(rest, r) == True{} : Bool} -> {Nat.is_eq(r, j) == False{} : Bool}) -> {Nat.is_eq(r, j) == False{} : Bool}:
  match b:
    case True{}:
      (%nat.eq(x, r, eb) : {Nat.is_eq(_, j) == False{} : Bool}; hx)
    case False{}:
      ih(hm)

# r is one of xs and j is not: r is not j
def mem.ne(xs: List<&2, Nat>, +r: Nat, +j: Nat, hm: {PM.Nat.mem(xs, r) == True{} : Bool}, +hj: {PM.Nat.mem(xs, j) == False{} : Bool}) ->
  {Nat.is_eq(r, j) == False{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({Nat.is_eq(r, j) == False{} : Bool}, N.false_ne_true(hm))
    case Con{+x, rest}:
      mem.ne.b(Nat.is_eq(x, r), x, rest, r, j, {==}, hm, PM.or.f.l(Nat.is_eq(x, j), PM.Nat.mem(rest, j), hj),
        e => mem.ne(rest, r, j, e, PM.or.f.r(Nat.is_eq(x, j), PM.Nat.mem(rest, j), hj)))

# a set of the register r keeps the register j
def get.set.ne(xs: List<&2, U32>, r: Nat, j: Nat, +v: U32, ne: {Nat.is_eq(r, j) == False{} : Bool}) ->
  {List.get(&2, U32, List.set(&2, U32, xs, r, v), j) == List.get(&2, U32, xs, j) : Maybe<&2, U32>}:
  match xs r j:
    case Nil{} _ _:
      {==}
    case Con{x, t} 0n 0n:
      Empty.absurd({Some{v} == Some{x} : Maybe<&2, U32>}, N.true_ne_false(ne))
    case Con{x, t} 0n 1n+q:
      {==}
    case Con{x, t} 1n+p 0n:
      {==}
    case Con{x, t} 1n+p 1n+q:
      get.set.ne(t, p, q, v, ne)

# a set of a register of scr keeps the registers of keep, none of scr
def kept.set(+regs: List<&2, U32>, +regs2: List<&2, U32>, keep: List<&2, Nat>, +scr: List<&2, Nat>, +r: Nat, +v: U32,
  +hm: {PM.Nat.mem(scr, r) == True{} : Bool}, +hd: {PM.Disj(keep, scr) == True{} : Bool}, a: PM.Kept(regs, regs2, keep)) ->
  PM.Kept(regs, List.set(&2, U32, regs2, r, v), keep):
  match keep:
    case Nil{}:
      Unit{}
    case Con{+j, rest}:
      (a1, ar) = a
      +hn = PM.not.t(PM.Nat.mem(scr, j), PM.and.l(Bool.not(PM.Nat.mem(scr, j)), PM.Disj(rest, scr), hd))
      (Equal.trans(Maybe<&2, U32>, List.get(&2, U32, List.set(&2, U32, regs2, r, v), j), List.get(&2, U32, regs2, j), List.get(&2, U32, regs, j),
         get.set.ne(regs2, r, j, v, mem.ne(scr, r, j, hm, hn)), a1),
        kept.set(regs, regs2, rest, scr, r, v, hm, PM.and.r(Bool.not(PM.Nat.mem(scr, j)), PM.Disj(rest, scr), hd), ar))

# the registers of keep kept from regs to regs2, then to regs3
def kept.trans(+regs: List<&2, U32>, +regs2: List<&2, U32>, +regs3: List<&2, U32>, keep: List<&2, Nat>,
  a: PM.Kept(regs, regs2, keep), b: PM.Kept(regs2, regs3, keep)) -> PM.Kept(regs, regs3, keep):
  match keep:
    case Nil{}:
      Unit{}
    case Con{+j, rest}:
      (a1, ar) = a
      (b1, br) = b
      (Equal.trans(Maybe<&2, U32>, List.get(&2, U32, regs3, j), List.get(&2, U32, regs2, j), List.get(&2, U32, regs, j), b1, a1),
        kept.trans(regs, regs2, regs3, rest, ar, br))

# every register of small is one of big
def Disj.in(small: List<&2, Nat>, +big: List<&2, Nat>) -> Bool:
  match small:
    case Nil{}:
      True{}
    case Con{+x, rest}:
      Bool.and(PM.Nat.mem(big, x), Disj.in(rest, big))

# both sides of an or are False
def or.ff(-a: Bool, -b: Bool, ha: {a == False{} : Bool}, hb: {b == False{} : Bool}) -> {Bool.or(a, b) == False{} : Bool}:
  %Equal.sym(Bool, a, False{}, ha) : {Bool.or(_, b) == False{} : Bool}
  %Equal.sym(Bool, b, False{}, hb) : {Bool.or(False{}, _) == False{} : Bool}
  {==}

# j, none of big, is none of small
def nmem.sub(small: List<&2, Nat>, +big: List<&2, Nat>, +j: Nat, +hs: {Disj.in(small, big) == True{} : Bool},
  +hn: {PM.Nat.mem(big, j) == False{} : Bool}) -> {PM.Nat.mem(small, j) == False{} : Bool}:
  match small:
    case Nil{}:
      {==}
    case Con{+x, rest}:
      or.ff(Nat.is_eq(x, j), PM.Nat.mem(rest, j), mem.ne(big, x, j, PM.and.l(PM.Nat.mem(big, x), Disj.in(rest, big), hs), hn),
        nmem.sub(rest, big, j, PM.and.r(PM.Nat.mem(big, x), Disj.in(rest, big), hs), hn))

# the registers of keep, none of the big list, are none of the small one
def disj.sub(keep: List<&2, Nat>, +big: List<&2, Nat>, +small: List<&2, Nat>, +hs: {Disj.in(small, big) == True{} : Bool},
  +hd: {PM.Disj(keep, big) == True{} : Bool}) -> {PM.Disj(keep, small) == True{} : Bool}:
  match keep:
    case Nil{}:
      {==}
    case Con{+j, rest}:
      +hn = PM.not.t(PM.Nat.mem(big, j), PM.and.l(Bool.not(PM.Nat.mem(big, j)), PM.Disj(rest, big), hd))
      PM.and.i(Bool.not(PM.Nat.mem(small, j)), PM.Disj(rest, small),
        (%Equal.sym(Bool, PM.Nat.mem(small, j), False{}, nmem.sub(small, big, j, hs, hn)) : {Bool.not(_) == True{} : Bool}; {==}),
        disj.sub(rest, big, small, hs, PM.and.r(Bool.not(PM.Nat.mem(big, j)), PM.Disj(rest, big), hd)))

# The temporaries
# ---------------

# what Tmp.ok says of the first temporary e: one of the machine's own, out of
# the pend list, none of the others; and Tmp.ok of the others
def tmp.hd(+e: U32, +h: List<&2, PM.Rt>, +rest: List<&2, PM.TmpE>, +m: Cr.Cir.Cells, +fi: U32, +nx: U32, +ps: List<&2, U32>,
  +R: List<&2, PM.Rt>, +hok: {PM.Tmp.ok(Con{PM.TmpE{e, h}, rest}, m, fi, nx, ps, R) == True{} : Bool}, -G: Type,
  k: {PM.Own(fi, nx, e) == True{} : Bool} -> {PM.Mem(ps, e) == False{} : Bool} -> {PM.Mem(PM.Tmp.cells(rest), e) == False{} : Bool} ->
    {PM.Tmp.ok(rest, m, fi, nx, ps, R) == True{} : Bool} -> G) -> G:
  +A = PM.Own(fi, nx, e)
  +B1 = Bool.not(PM.Fl(m, e, 1024))
  +B2 = Bool.not(PM.Mem(ps, e))
  +B3 = Bool.not(PM.Mem(PM.Tmp.cells(rest), e))
  +B4 = Bool.not(PM.Nodes(R, m, e))
  +B5 = PM.AllIn(PM.Rt.cells(h), PM.Fs(m, ps, e))
  +T = PM.Tmp.ok(rest, m, fi, nx, ps, R)
  +r1 = PM.and.r(A, Bool.and(B1, Bool.and(B2, Bool.and(B3, Bool.and(B4, Bool.and(B5, T))))), hok)
  +r2 = PM.and.r(B1, Bool.and(B2, Bool.and(B3, Bool.and(B4, Bool.and(B5, T)))), r1)
  +r3 = PM.and.r(B2, Bool.and(B3, Bool.and(B4, Bool.and(B5, T))), r2)
  +r4 = PM.and.r(B3, Bool.and(B4, Bool.and(B5, T)), r3)
  +r5 = PM.and.r(B4, Bool.and(B5, T), r4)
  k(PM.and.l(A, Bool.and(B1, Bool.and(B2, Bool.and(B3, Bool.and(B4, Bool.and(B5, T))))), hok),
    PM.not.t(PM.Mem(ps, e), PM.and.l(B2, Bool.and(B3, Bool.and(B4, Bool.and(B5, T))), r2)),
    PM.not.t(PM.Mem(PM.Tmp.cells(rest), e), PM.and.l(B3, Bool.and(B4, Bool.and(B5, T)), r3)),
    PM.and.r(B5, T, r5))

# an own cell is not next
def own.nx(+e: U32, +fi: U32, +nx: U32, h: {PM.Own(fi, nx, e) == True{} : Bool}) -> {U32.is_eq(e, nx) == False{} : Bool}:
  lt.neq(e, nx, PM.u.lt(e, nx, PM.and.r(U32.is_le(fi, e), U32.is_lt(e, nx), h)))

# M.alloc's cell z (in ps, or nx) is none of the temporaries
def tmp.nz(ys: List<&2, PM.TmpE>, +m: Cr.Cir.Cells, +fi: U32, +nx: U32, +ps: List<&2, U32>, +R: List<&2, PM.Rt>, +z: U32,
  +hok: {PM.Tmp.ok(ys, m, fi, nx, ps, R) == True{} : Bool}, +hz: {Bool.or(PM.Mem(ps, z), U32.is_eq(z, nx)) == True{} : Bool}) ->
  {PM.Mem(PM.Tmp.cells(ys), z) == False{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{PM.TmpE{+e, +h}, +rest}:
      tmp.hd(e, h, rest, m, fi, nx, ps, R, hok, {PM.Mem(PM.Tmp.cells(Con{PM.TmpE{e, h}, rest}), z) == False{} : Bool},
        ho => hp => hn => hr => or.ff(U32.is_eq(e, z), PM.Mem(PM.Tmp.cells(rest), z),
          PM.not.t(U32.is_eq(e, z), ne.z(e, z, ps, nx, hp, own.nx(e, fi, nx, ho), hz)),
          tmp.nz(rest, m, fi, nx, ps, R, z, hr, hz)))

# The check's stack
# -----------------
#
# A chain of K.check cells from register ds, linked by field 1, each of them
# a temporary that holds no term. An entry holds, in field 2, the cell of a
# part of v, by its path from c at the fields of the cells m0 where the
# check begins; the part is v's at that path; and the cell is one that the
# check may write (Kept.cells): a new one, of the pend list where the check
# begins, or a term cell there.

type DE is Data:
  DE{k: U32, p: List<&2, Bool>, u: Bk.Term}

# the stack's first cell, 0 when it is empty
def DE.top(es: List<&2, DE>) -> U32:
  match es:
    case Nil{}:
      0
    case Con{DE{k, _, _}, _}:
      k

# the stack's cells, as temporaries that hold no term
def DE.tmps(es: List<&2, DE>) -> List<&2, PM.TmpE>:
  match es:
    case Nil{}:
      Nil{}
    case Con{DE{k, _, _}, rest}:
      Con{PM.TmpE{k, Nil{}}, DE.tmps(rest)}

# a cell that the check may write, as Kept.cells has it: from nx0 on, one of
# xs0 (the pend list where it begins), or a term cell of m0
def Wr(+m0: Cr.Cir.Cells, +nx0: U32, +xs0: List<&2, U32>, +z: U32) -> Bool:
  Bool.or(Bool.not(U32.is_lt(z, nx0)), Bool.or(PM.Mem(xs0, z), U32.is_lt(PM.Tg(m0, z), 19)))

def DS(es: List<&2, DE>, +m: Cr.Cir.Cells, +m0: Cr.Cir.Cells, +c: U32, +v: Bk.Term, +nx0: U32, +xs0: List<&2, U32>) -> Data:
  match es:
    case Nil{}:
      Unit
    case Con{DE{+e, +p, u}, +rest}:
      PM.P2({U32.is_eq(e, 0) == False{} : Bool},
      PM.P2({Cr.Cir.Cells.get(m, e) == CK(DE.top(rest), Cl(m0, p, c)) : Cr.Cir.Cell},
      PM.P2({Sub(p, v) == Some{u} : Maybe<&2, Bk.Term>},
      PM.P2({Wr(m0, nx0, xs0, e) == True{} : Bool},
        DS(rest, m, m0, c, v, nx0, xs0)))))

# a store at a cell z that is none of the stack's keeps it
def ds.set(es: List<&2, DE>, +m: Cr.Cir.Cells, +m0: Cr.Cir.Cells, +c: U32, +v: Bk.Term, +nx0: U32, +xs0: List<&2, U32>,
  +xs: List<&2, PM.TmpE>, +z: U32, +y: Cr.Cir.Cell,
  hz: {PM.Mem(PM.Tmp.cells(List.append(&2, PM.TmpE, DE.tmps(es), xs)), z) == False{} : Bool},
  h: DS(es, m, m0, c, v, nx0, xs0)) -> DS(es, Cr.Cir.Cells.set(m, z, y), m0, c, v, nx0, xs0):
  match es:
    case Nil{}:
      Unit{}
    case Con{DE{+e, +p, +u}, +rest}:
      (h0, r1) = h
      (h1, r2) = r1
      (h2, r3) = r2
      (h3, hr) = r3
      +hz2 = hz
      +L = PM.Mem(PM.Tmp.cells(List.append(&2, PM.TmpE, DE.tmps(rest), xs)), z)
      (h0, (Equal.trans(Cr.Cir.Cell, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, y), e), Cr.Cir.Cells.get(m, e), CK(DE.top(rest), Cl(m0, p, c)),
         PM.cl.go(m, e, z, y, PM.or.f.l(U32.is_eq(e, z), L, hz2)), h1),
        (h2, (h3, ds.set(rest, m, m0, c, v, nx0, xs0, xs, z, y, PM.or.f.r(U32.is_eq(e, z), L, hz2), hr)))))

# a cell with a term's tag is not one with K.check's
def ne.tg(b: Bool, +x: U32, +e: U32, +m: Cr.Cir.Cells, eb: {U32.is_eq(x, e) == b : Bool},
  hx: {U32.is_lt(PM.Tg(m, x), 19) == True{} : Bool}, he: {U32.is_lt(PM.Tg(m, e), 19) == False{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, N.true_ne_false(Equal.trans(Bool, True{}, U32.is_lt(PM.Tg(m, e), 19), False{},
        (%PM.u32.eq(x, e, eb) : {True{} == U32.is_lt(PM.Tg(m, _), 19) : Bool}; Equal.sym(Bool, U32.is_lt(PM.Tg(m, x), 19), True{}, hx)), he)))

# the cells whose field 1 M.alloc's reuse writes (term cells) are none of a cell of tag 19 or more
def took.out(ws: List<&2, PM.W1>, +ps: List<&2, U32>, +m: Cr.Cir.Cells, +e: U32, +he: {U32.is_lt(PM.Tg(m, e), 19) == False{} : Bool},
  hw: {PM.Took(ws, ps, m) == True{} : Bool}) -> {PM.Mem(PM.W1.cells(ws), e) == False{} : Bool}:
  match ws:
    case Nil{}:
      {==}
    case Con{PM.W1{+x, _}, rest}:
      +A = Bool.and(U32.is_lt(PM.Tg(m, x), 19), PM.Taken(ps, m, x))
      +hw2 = hw
      or.ff(U32.is_eq(x, e), PM.Mem(PM.W1.cells(rest), e),
        ne.tg(U32.is_eq(x, e), x, e, m, {==}, PM.and.l(U32.is_lt(PM.Tg(m, x), 19), PM.Taken(ps, m, x), PM.and.l(A, PM.Took(rest, ps, m), hw2)), he),
        took.out(rest, ps, m, e, he, PM.and.r(A, PM.Took(rest, ps, m), hw2)))

# a K.check cell's tag is 44
def ck.tg(+m: Cr.Cir.Cells, +e: U32, +w: U32, +y: U32, h: {Cr.Cir.Cells.get(m, e) == CK(w, y) : Cr.Cir.Cell}) ->
  {U32.is_lt(PM.Tg(m, e), 19) == False{} : Bool}:
  (%Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(m, e), CK(w, y), h) : {U32.is_lt(U32.and(Cr.Cir.Cell.get(0n, _), 63), 19) == False{} : Bool}; {==})

# M.alloc's stores of field 1 (to term cells) keep the stack
def ds.put1(es: List<&2, DE>, +m: Cr.Cir.Cells, +m0: Cr.Cir.Cells, +c: U32, +v: Bk.Term, +nx0: U32, +xs0: List<&2, U32>,
  +ws: List<&2, PM.W1>, +ps: List<&2, U32>, +hw: {PM.Took(ws, ps, m) == True{} : Bool},
  h: DS(es, m, m0, c, v, nx0, xs0)) -> DS(es, PM.Put1(ws, m), m0, c, v, nx0, xs0):
  match es:
    case Nil{}:
      Unit{}
    case Con{DE{+e, +p, +u}, +rest}:
      (h0, r1) = h
      (h1, r2) = r1
      (h2, r3) = r2
      (h3, hr) = r3
      +h1b = h1
      (h0, (Equal.trans(Cr.Cir.Cell, Cr.Cir.Cells.get(PM.Put1(ws, m), e), Cr.Cir.Cells.get(m, e), CK(DE.top(rest), Cl(m0, p, c)),
         PM.put1.out(ws, m, e, took.out(ws, ps, m, e, ck.tg(m, e, DE.top(rest), Cl(m0, p, c), h1b), hw)), h1b),
        (h2, (h3, ds.put1(rest, m, m0, c, v, nx0, xs0, ws, ps, hw, hr)))))

# What the check keeps (Kept.cells)
# ---------------------------------
#
# The check writes the cells that it may (Wr: new ones, of the pend list where
# it begins, or term cells there) and sets DATA on term cells: so each cell
# that Kept.cells keeps (an own cell below nx0, out of xs, of tag 19 or more
# in m0) keeps its value. A kept cell keeps its tag, so it is no term cell now
# either (NK).

# z is a cell that the check may write, or a term cell of m
def NK(+m0: Cr.Cir.Cells, +m: Cr.Cir.Cells, +nx0: U32, +xs: List<&2, U32>, +z: U32) -> Bool:
  Bool.or(Wr(m0, nx0, xs, z), U32.is_lt(PM.Tg(m, z), 19))

# a cell q below nx0, out of xs, of no term in m0 nor in m, is none of them
def nk.ne.b(b: Bool, +q: U32, +z: U32, +m0: Cr.Cir.Cells, +m: Cr.Cir.Cells, +nx0: U32, +xs: List<&2, U32>, eb: {U32.is_eq(q, z) == b : Bool},
  hz: {NK(m0, m, nx0, xs, z) == True{} : Bool}, hq: {U32.is_lt(q, nx0) == True{} : Bool}, hx: {PM.Mem(xs, q) == False{} : Bool},
  h0: {U32.is_lt(PM.Tg(m0, q), 19) == False{} : Bool}, h1: {U32.is_lt(PM.Tg(m, q), 19) == False{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      +e = PM.u32.eq(q, z, eb)
      +L = Bool.not(U32.is_lt(q, nx0))
      +M = Bool.or(PM.Mem(xs, q), U32.is_lt(PM.Tg(m0, q), 19))
      +nkf = or.ff(Bool.or(L, M), U32.is_lt(PM.Tg(m, q), 19),
        or.ff(L, M, (%Equal.sym(Bool, U32.is_lt(q, nx0), True{}, hq) : {Bool.not(_) == False{} : Bool}; {==}),
          or.ff(PM.Mem(xs, q), U32.is_lt(PM.Tg(m0, q), 19), hx, h0)), h1)
      Equal.trans(Bool, True{}, NK(m0, m, nx0, xs, q), False{},
        Equal.sym(Bool, NK(m0, m, nx0, xs, q), True{}, (%Equal.sym(U32, q, z, e) : {NK(m0, m, nx0, xs, _) == True{} : Bool}; hz)), nkf)

# a kept cell (its value is m0's) keeps m0's tag
def kt.tg(+m: Cr.Cir.Cells, +m0: Cr.Cir.Cells, +q: U32, h: {Cr.Cir.Cells.get(m, q) == Cr.Cir.Cells.get(m0, q) : Cr.Cir.Cell},
  h0: {U32.is_lt(PM.Tg(m0, q), 19) == False{} : Bool}) -> {U32.is_lt(PM.Tg(m, q), 19) == False{} : Bool}:
  (%Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(m, q), Cr.Cir.Cells.get(m0, q), h) : {U32.is_lt(U32.and(Cr.Cir.Cell.get(0n, _), 63), 19) == False{} : Bool}; h0)

# Kept.at of q under a store at a cell z that NK says is none of the kept ones
def kat.set.b(b: Bool, +m0: Cr.Cir.Cells, +m: Cr.Cir.Cells, +xs: List<&2, U32>, +q: U32, +z: U32, +Y: Cr.Cir.Cell, +nx0: U32,
  eb: {Bool.or(PM.Mem(xs, q), U32.is_lt(PM.Tg(m0, q), 19)) == b : Bool}, hz: {NK(m0, m, nx0, xs, z) == True{} : Bool},
  hq: {U32.is_lt(q, nx0) == True{} : Bool}, h: PM.Kept.if(b, {Cr.Cir.Cells.get(m, q) == Cr.Cir.Cells.get(m0, q) : Cr.Cir.Cell})) ->
  PM.Kept.if(b, {Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, Y), q) == Cr.Cir.Cells.get(m0, q) : Cr.Cir.Cell}):
  match b:
    case True{}:
      Unit{}
    case False{}:
      +h2 = h
      +eb2 = eb
      +h0 = PM.or.f.r(PM.Mem(xs, q), U32.is_lt(PM.Tg(m0, q), 19), eb2)
      +ne = nk.ne.b(U32.is_eq(q, z), q, z, m0, m, nx0, xs, {==}, hz, hq, PM.or.f.l(PM.Mem(xs, q), U32.is_lt(PM.Tg(m0, q), 19), eb2), h0,
        kt.tg(m, m0, q, h2, h0))
      Equal.trans(Cr.Cir.Cell, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, Y), q), Cr.Cir.Cells.get(m, q), Cr.Cir.Cells.get(m0, q),
        PM.cl.go(m, q, z, Y, ne), h2)

# q + (1 + p) = n0 gives q < n0, and inc(q) + p = n0
def nat.lt.of(+x: Nat, +p: Nat, -n0: Nat, h: {Nat.add(x, 1n+p) == n0 : Nat}) -> N.Le(1n+x, n0):
  N.le_rw_r(1n+x, 1n+Nat.add(x, p), n0, Equal.trans(Nat, 1n+Nat.add(x, p), Nat.add(x, 1n+p), n0, Equal.sym(Nat, Nat.add(x, 1n+p), 1n+Nat.add(x, p), N.add_succ_r(x, p)), h),
    N.le_add_r(x, p))

def kg.next(+q: U32, +p: Nat, +nx0: U32, +hn: {Nat.add(U32.to_nat(q), 1n+p) == U32.to_nat(nx0) : Nat}) ->
  {Nat.add(U32.to_nat(U32.inc(q)), p) == U32.to_nat(nx0) : Nat}:
  %Equal.sym(Nat, U32.to_nat(U32.inc(q)), 1n+U32.to_nat(q), PM.u.inc(q, nx0, nat.lt.of(U32.to_nat(q), p, U32.to_nat(nx0), hn))) :
    {Nat.add(_, p) == U32.to_nat(nx0) : Nat}
  Equal.trans(Nat, 1n+Nat.add(U32.to_nat(q), p), Nat.add(U32.to_nat(q), 1n+p), U32.to_nat(nx0),
    Equal.sym(Nat, Nat.add(U32.to_nat(q), 1n+p), 1n+Nat.add(U32.to_nat(q), p), N.add_succ_r(U32.to_nat(q), p)), hn)

# Kept.go under a store at a cell z that NK says is none of the kept ones
def kg.set(n: Nat, +m0: Cr.Cir.Cells, +m: Cr.Cir.Cells, +xs: List<&2, U32>, +q: U32, +z: U32, +Y: Cr.Cir.Cell, +nx0: U32,
  +hz: {NK(m0, m, nx0, xs, z) == True{} : Bool}, +hn: {Nat.add(U32.to_nat(q), n) == U32.to_nat(nx0) : Nat},
  h: PM.Kept.go(n, m0, m, xs, q)) -> PM.Kept.go(n, m0, Cr.Cir.Cells.set(m, z, Y), xs, q):
  match n:
    case 0n:
      Unit{}
    case 1n+(+p):
      (ha, hr) = h
      (kat.set.b(Bool.or(PM.Mem(xs, q), U32.is_lt(PM.Tg(m0, q), 19)), m0, m, xs, q, z, Y, nx0, {==}, hz,
         A.lt.of(q, nx0, nat.lt.of(U32.to_nat(q), p, U32.to_nat(nx0), hn)), ha),
        kg.set(p, m0, m, xs, U32.inc(q), z, Y, nx0, hz, kg.next(q, p, nx0, hn), hr))

# Kept.at of q under M.alloc's stores of field 1 (to term cells)
def kat.put1.b(b: Bool, +m0: Cr.Cir.Cells, +m: Cr.Cir.Cells, +xs: List<&2, U32>, +q: U32, +ws: List<&2, PM.W1>, +ps: List<&2, U32>,
  eb: {Bool.or(PM.Mem(xs, q), U32.is_lt(PM.Tg(m0, q), 19)) == b : Bool}, hw: {PM.Took(ws, ps, m) == True{} : Bool},
  h: PM.Kept.if(b, {Cr.Cir.Cells.get(m, q) == Cr.Cir.Cells.get(m0, q) : Cr.Cir.Cell})) ->
  PM.Kept.if(b, {Cr.Cir.Cells.get(PM.Put1(ws, m), q) == Cr.Cir.Cells.get(m0, q) : Cr.Cir.Cell}):
  match b:
    case True{}:
      Unit{}
    case False{}:
      +h2 = h
      Equal.trans(Cr.Cir.Cell, Cr.Cir.Cells.get(PM.Put1(ws, m), q), Cr.Cir.Cells.get(m, q), Cr.Cir.Cells.get(m0, q),
        PM.put1.out(ws, m, q, took.out(ws, ps, m, q, kt.tg(m, m0, q, h2, PM.or.f.r(PM.Mem(xs, q), U32.is_lt(PM.Tg(m0, q), 19), eb)), hw)), h2)

def kg.put1(n: Nat, +m0: Cr.Cir.Cells, +m: Cr.Cir.Cells, +xs: List<&2, U32>, +q: U32, +ws: List<&2, PM.W1>, +ps: List<&2, U32>,
  +hw: {PM.Took(ws, ps, m) == True{} : Bool}, h: PM.Kept.go(n, m0, m, xs, q)) -> PM.Kept.go(n, m0, PM.Put1(ws, m), xs, q):
  match n:
    case 0n:
      Unit{}
    case 1n+p:
      (ha, hr) = h
      (kat.put1.b(Bool.or(PM.Mem(xs, q), U32.is_lt(PM.Tg(m0, q), 19)), m0, m, xs, q, ws, ps, {==}, hw, ha),
        kg.put1(p, m0, m, xs, U32.inc(q), ws, ps, hw, hr))

# the cell q, from base on and below base + n, is one that Kept.go keeps
def kg.at.b(b: Bool, +n: Nat, +m0: Cr.Cir.Cells, +m: Cr.Cir.Cells, +xs: List<&2, U32>, +base: U32, +q: U32,
  eb: {U32.is_eq(base, q) == b : Bool}, h1: N.Le(U32.to_nat(base), U32.to_nat(q)), h2: N.Le(1n+U32.to_nat(q), Nat.add(U32.to_nat(base), 1n+n)),
  ha: PM.Kept.at(m0, m, xs, base),
  ih: N.Le(U32.to_nat(U32.inc(base)), U32.to_nat(q)) -> N.Le(1n+U32.to_nat(q), Nat.add(U32.to_nat(U32.inc(base)), n)) -> PM.Kept.at(m0, m, xs, q)) ->
  PM.Kept.at(m0, m, xs, q):
  match b:
    case True{}:
      (%PM.u32.eq(base, q, eb) : PM.Kept.at(m0, m, xs, _); ha)
    case False{}:
      +lt = PM.lt.ne(U32.cmp(base, q), U32.to_nat(base), U32.to_nat(q), N.U32.rel(base, q), eb, h1)
      +ei = PM.u.inc(base, q, lt)
      ih((%Equal.sym(Nat, U32.to_nat(U32.inc(base)), 1n+U32.to_nat(base), ei) : N.Le(_, U32.to_nat(q)); lt),
        (%Equal.sym(Nat, U32.to_nat(U32.inc(base)), 1n+U32.to_nat(base), ei) : N.Le(1n+U32.to_nat(q), Nat.add(_, n));
          N.le_rw_r(1n+U32.to_nat(q), Nat.add(U32.to_nat(base), 1n+n), 1n+Nat.add(U32.to_nat(base), n), N.add_succ_r(U32.to_nat(base), n), h2)))

def kg.at(n: Nat, +m0: Cr.Cir.Cells, +m: Cr.Cir.Cells, +xs: List<&2, U32>, +base: U32, +q: U32,
  h1: N.Le(U32.to_nat(base), U32.to_nat(q)), h2: N.Le(1n+U32.to_nat(q), Nat.add(U32.to_nat(base), n)),
  h: PM.Kept.go(n, m0, m, xs, base)) -> PM.Kept.at(m0, m, xs, q):
  match n:
    case 0n:
      Empty.absurd(PM.Kept.at(m0, m, xs, q), N.not_succ_le(U32.to_nat(q),
        N.le_trans(1n+U32.to_nat(q), U32.to_nat(base), U32.to_nat(q), N.le_rw_r(1n+U32.to_nat(q), Nat.add(U32.to_nat(base), 0n), U32.to_nat(base), N.add_zero(U32.to_nat(base)), h2), h1)))
    case 1n+(+p):
      (ha, hr) = h
      kg.at.b(U32.is_eq(base, q), p, m0, m, xs, base, q, {==}, h1, h2, ha,
        g1 => g2 => kg.at(p, m0, m, xs, U32.inc(base), q, g1, g2, hr))

# a <= b of U32s, from their Nats
def le.of.b(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), h: N.Le(x, y)) -> {Cmp.is_le(c) == True{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({False{} == True{} : Bool}, N.not_succ_le(y, N.le_trans(1n+y, x, y, r, h)))

def le.of(+a: U32, +b: U32, h: N.Le(U32.to_nat(a), U32.to_nat(b))) -> {U32.is_le(a, b) == True{} : Bool}:
  le.of.b(U32.cmp(a, b), U32.to_nat(a), U32.to_nat(b), N.U32.rel(a, b), h)

# a is not below c when c <= a
def lt.le.f(b: Bool, +a: U32, +c: U32, eb: {U32.is_lt(a, c) == b : Bool}, h: N.Le(U32.to_nat(c), U32.to_nat(a))) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, N.not_succ_le(U32.to_nat(a), N.le_trans(1n+U32.to_nat(a), U32.to_nat(c), U32.to_nat(a), PM.u.lt(a, c, eb), h)))

# a cell of the pend list ps, whose cells below nx0 PsSub.lt bounds, is one that the check may write
def pssub.wr.b(b: Bool, +q: U32, -rest: List<&2, U32>, +xs: List<&2, U32>, +m0: Cr.Cir.Cells, +nx0: U32, +z: U32,
  eb: {U32.is_eq(q, z) == b : Bool}, hm: {Bool.or(b, PM.Mem(rest, z)) == True{} : Bool}, hq: {Wr(m0, nx0, xs, q) == True{} : Bool},
  ih: {PM.Mem(rest, z) == True{} : Bool} -> {Wr(m0, nx0, xs, z) == True{} : Bool}) -> {Wr(m0, nx0, xs, z) == True{} : Bool}:
  match b:
    case True{}:
      (%PM.u32.eq(q, z, eb) : {Wr(m0, nx0, xs, _) == True{} : Bool}; hq)
    case False{}:
      ih(hm)

def pssub.wr(ps: List<&2, U32>, +xs: List<&2, U32>, +m0: Cr.Cir.Cells, +nx0: U32, +z: U32, hm: {PM.Mem(ps, z) == True{} : Bool},
  +hp: {PM.PsSub.lt(ps, xs, m0, nx0) == True{} : Bool}) -> {Wr(m0, nx0, xs, z) == True{} : Bool}:
  match ps:
    case Nil{}:
      Empty.absurd({Wr(m0, nx0, xs, z) == True{} : Bool}, N.false_ne_true(hm))
    case Con{+q, rest}:
      +C = Wr(m0, nx0, xs, q)
      pssub.wr.b(U32.is_eq(q, z), q, rest, xs, m0, nx0, z, {==}, hm, PM.and.l(C, PM.PsSub.lt(rest, xs, m0, nx0), hp),
        e => pssub.wr(rest, xs, m0, nx0, z, e, PM.and.r(C, PM.PsSub.lt(rest, xs, m0, nx0), hp)))

# next, from nx0 on, is a cell that the check may write
def wr.nx(+z: U32, +nx: U32, +nx0: U32, +xs: List<&2, U32>, +m0: Cr.Cir.Cells, ez: {U32.is_eq(z, nx) == True{} : Bool},
  hn: {U32.is_le(nx0, nx) == True{} : Bool}) -> {Wr(m0, nx0, xs, z) == True{} : Bool}:
  (%Equal.sym(U32, z, nx, PM.u32.eq(z, nx, ez)) : {Wr(m0, nx0, xs, _) == True{} : Bool};
    PM.or.l(Bool.not(U32.is_lt(nx, nx0)), Bool.or(PM.Mem(xs, nx), U32.is_lt(PM.Tg(m0, nx), 19)),
      (%Equal.sym(Bool, U32.is_lt(nx, nx0), False{}, lt.le.f(U32.is_lt(nx, nx0), nx, nx0, {==}, PM.u.le(nx0, nx, hn))) : {Bool.not(_) == True{} : Bool}; {==})))

# M.alloc's cell (in ps, or next) is one that the check may write
def al.wr(+z: U32, +ps: List<&2, U32>, +nx: U32, +xs: List<&2, U32>, +m0: Cr.Cir.Cells, +nx0: U32,
  hz: {Bool.or(PM.Mem(ps, z), U32.is_eq(z, nx)) == True{} : Bool}, +hp: {PM.PsSub.lt(ps, xs, m0, nx0) == True{} : Bool},
  +hn: {U32.is_le(nx0, nx) == True{} : Bool}) -> {Wr(m0, nx0, xs, z) == True{} : Bool}:
  PM.or.cases(PM.Mem(ps, z), U32.is_eq(z, nx), {Wr(m0, nx0, xs, z) == True{} : Bool}, hz,
    e => pssub.wr(ps, xs, m0, nx0, z, e, hp), e => wr.nx(z, nx, nx0, xs, m0, e, hn))

# a term cell of m below nx0, kept by Kept.go, is out of xs only when it was one in m0
def wr.kept.b(b: Bool, +q: U32, +m: Cr.Cir.Cells, +m0: Cr.Cir.Cells, +xs: List<&2, U32>,
  eb: {Bool.or(PM.Mem(xs, q), U32.is_lt(PM.Tg(m0, q), 19)) == b : Bool}, ht: {U32.is_lt(PM.Tg(m, q), 19) == True{} : Bool},
  h: PM.Kept.if(b, {Cr.Cir.Cells.get(m, q) == Cr.Cir.Cells.get(m0, q) : Cr.Cir.Cell})) ->
  {Bool.or(PM.Mem(xs, q), U32.is_lt(PM.Tg(m0, q), 19)) == True{} : Bool}:
  match b:
    case True{}:
      eb
    case False{}:
      Empty.absurd({Bool.or(PM.Mem(xs, q), U32.is_lt(PM.Tg(m0, q), 19)) == True{} : Bool}, N.true_ne_false(
        Equal.trans(Bool, True{}, U32.is_lt(PM.Tg(m, q), 19), False{}, Equal.sym(Bool, U32.is_lt(PM.Tg(m, q), 19), True{}, ht),
          kt.tg(m, m0, q, h, PM.or.f.r(PM.Mem(xs, q), U32.is_lt(PM.Tg(m0, q), 19), eb)))))

# a term cell of m, an own cell, is one that the check may write
def wr.lt.b(b: Bool, +q: U32, +m: Cr.Cir.Cells, +m0: Cr.Cir.Cells, +xs: List<&2, U32>, +fi: U32, +nx0: U32, +n0: Nat,
  eb: {U32.is_lt(q, nx0) == b : Bool}, hf: {U32.is_le(fi, q) == True{} : Bool}, ht: {U32.is_lt(PM.Tg(m, q), 19) == True{} : Bool},
  +hn0: {Nat.add(U32.to_nat(fi), n0) == U32.to_nat(nx0) : Nat}, +hk: PM.Kept.go(n0, m0, m, xs, fi)) -> {Wr(m0, nx0, xs, q) == True{} : Bool}:
  match b:
    case False{}:
      (%Equal.sym(Bool, U32.is_lt(q, nx0), False{}, eb) : {Bool.or(Bool.not(_), Bool.or(PM.Mem(xs, q), U32.is_lt(PM.Tg(m0, q), 19))) == True{} : Bool}; {==})
    case True{}:
      +ka = kg.at(n0, m0, m, xs, fi, q, PM.u.le(fi, q, hf),
        N.le_rw_r(1n+U32.to_nat(q), U32.to_nat(nx0), Nat.add(U32.to_nat(fi), n0), Equal.sym(Nat, Nat.add(U32.to_nat(fi), n0), U32.to_nat(nx0), hn0),
          PM.u.lt(q, nx0, eb)), hk)
      PM.or.r(Bool.not(U32.is_lt(q, nx0)), Bool.or(PM.Mem(xs, q), U32.is_lt(PM.Tg(m0, q), 19)),
        wr.kept.b(Bool.or(PM.Mem(xs, q), U32.is_lt(PM.Tg(m0, q), 19)), q, m, m0, xs, {==}, ht, ka))

# the pend list after M.alloc (cells of ps, or term cells of m): each cell of
# it below nx0 is still one that the check may write
def pssub.al(ps2: List<&2, U32>, +qs: List<&2, U32>, +ps: List<&2, U32>, +m: Cr.Cir.Cells, +m2: Cr.Cir.Cells, +m0: Cr.Cir.Cells,
  +xs: List<&2, U32>, +fi: U32, +nx2: U32, +nx0: U32, +n0: Nat, +rs: List<&2, U32>,
  hs: {PM.PsSub(ps2, ps, m) == True{} : Bool}, ho: PM.PendOK(ps2, qs, m2, fi, nx2, rs), +hp: {PM.PsSub.lt(ps, xs, m0, nx0) == True{} : Bool},
  +hn0: {Nat.add(U32.to_nat(fi), n0) == U32.to_nat(nx0) : Nat}, +hk: PM.Kept.go(n0, m0, m, xs, fi)) ->
  {PM.PsSub.lt(ps2, xs, m0, nx0) == True{} : Bool}:
  match ps2:
    case Nil{}:
      {==}
    case Con{+q, rest}:
      (hq, r1) = ho
      (_, r2) = r1
      (_, r3) = r2
      (_, hr) = r3
      +hs2 = hs
      +S = Bool.or(PM.Mem(ps, q), U32.is_lt(PM.Tg(m, q), 19))
      +hf = PM.and.l(U32.is_le(fi, q), U32.is_lt(q, nx2), hq)
      PM.and.i(Wr(m0, nx0, xs, q), PM.PsSub.lt(rest, xs, m0, nx0),
        PM.or.cases(PM.Mem(ps, q), U32.is_lt(PM.Tg(m, q), 19), {Wr(m0, nx0, xs, q) == True{} : Bool}, PM.and.l(S, PM.PsSub(rest, ps, m), hs2),
          e => pssub.wr(ps, xs, m0, nx0, q, e, hp),
          e => wr.lt.b(U32.is_lt(q, nx0), q, m, m0, xs, fi, nx0, n0, {==}, hf, e, hn0, hk)),
        pssub.al(rest, qs, ps, m, m2, m0, xs, fi, nx2, nx0, n0, rs, PM.and.r(S, PM.PsSub(rest, ps, m), hs2), hr, hp, hn0, hk))

# The values that the check reads
# -------------------------------

# register r, which holds v
def ob.g(+r: Nat, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>,
  -v: U32, h: {List.get(&2, U32, regs, r) == Some{v} : Maybe<&2, U32>}) -> W.Ob(Mc.M.g(r), X.X.st(regs, m, nx, fi, im, pg, lim, inp)):
  %Equal.sym(Maybe<&2, U32>, List.get(&2, U32, regs, r), Some{v}, h) : W.IsSome(_)
  Unit{}

def ev.g(+r: Nat, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>,
  +v: U32, h: {List.get(&2, U32, regs, r) == Some{v} : Maybe<&2, U32>}) -> {W.Ev(Mc.M.g(r), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) == v : U32}:
  %Equal.sym(Maybe<&2, U32>, List.get(&2, U32, regs, r), Some{v}, h) : {Maybe.default(&2, U32, _, 0) == v : U32}
  {==}

# field k of the cell i in register r
def ob.f(+k: Nat, +r: Nat, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>,
  +i: U32, +h: {List.get(&2, U32, regs, r) == Some{i} : Maybe<&2, U32>}, hc: {Cr.Cir.is_cell(i, im, fi, nx) == True{} : Bool}) ->
  W.Ob(Mc.M.f(k, Mc.M.g(r)), X.X.st(regs, m, nx, fi, im, pg, lim, inp)):
  +S = X.X.st(regs, m, nx, fi, im, pg, lim, inp)
  (ob.g(r, regs, m, nx, fi, im, pg, lim, inp, i, h),
    (%Equal.sym(U32, W.Ev(Mc.M.g(r), S), i, ev.g(r, regs, m, nx, fi, im, pg, lim, inp, i, h)) : W.CellOk(_, S);
      Equal.sym(Bool, Cr.Cir.is_cell(i, im, fi, nx), True{}, hc)))

def ev.f(+k: Nat, +r: Nat, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>,
  +i: U32, h: {List.get(&2, U32, regs, r) == Some{i} : Maybe<&2, U32>}) ->
  {W.Ev(Mc.M.f(k, Mc.M.g(r)), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) == PM.Fd(k, m, i) : U32}:
  +S = X.X.st(regs, m, nx, fi, im, pg, lim, inp)
  %Equal.sym(U32, W.Ev(Mc.M.g(r), S), i, ev.g(r, regs, m, nx, fi, im, pg, lim, inp, i, h)) : {W.Ev.field(k, _, S) == PM.Fd(k, m, i) : U32}
  {==}

# M.alloc's outcome, as alloc.post gives it
# ---------------------------------------

# what alloc.post says of the state X.X.st(regs2, m2, nx2, ..) after M.alloc(r)
# from the cells m (next nx, pend list ps): its cell z, its pend list ps2
def AlP(+dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +r: Nat, +keep: List<&2, Nat>, +os: List<&2, PM.Rt>, +bs: List<&2, PM.Rt>,
  +fs: List<&2, PM.AF>, +sp: U32, +ps: List<&2, U32>, +xs: List<&2, PM.TmpE>, +regs2: List<&2, U32>, +m2: Cr.Cir.Cells, +nx2: U32,
  +z: U32, +pend2: U32, +ps2: List<&2, U32>, +ws: List<&2, PM.W1>, +zs2: List<&2, PM.Rt>) -> Data:
  PM.P2(PM.Kept(regs, regs2, keep), PM.P2({List.length(&2, U32, regs2) == 63n : Nat},
  PM.P2({List.get(&2, U32, regs2, r) == Some{z} : Maybe<&2, U32>}, PM.P2({List.get(&2, U32, regs2, 3n) == Some{pend2} : Maybe<&2, U32>},
  PM.P2({Cr.Cir.Cells.get(m2, z) == Cr.Cir.Cell.zero() : Cr.Cir.Cell},
  PM.P2({PM.Own(fi, nx2, z) == True{} : Bool}, PM.P2({PM.Mem(ps2, z) == False{} : Bool},
  PM.P2({Bool.or(PM.Mem(ps, z), U32.is_eq(z, nx)) == True{} : Bool},
  PM.P2({Bool.or(Bool.and(PM.Mem(ps, z), U32.is_eq(nx2, nx)), Bool.and(PM.Pend.none(ps), Bool.and(U32.is_eq(z, nx), U32.is_eq(nx2, U32.inc(nx))))) == True{} : Bool},
  PM.P2({m2 == Cr.Cir.Cells.set(PM.Put1(ws, m), z, Cr.Cir.Cell.zero()) : Cr.Cir.Cells}, PM.P2({PM.Took(ws, ps, m) == True{} : Bool},
  PM.P2({PM.PsSub(ps2, ps, m) == True{} : Bool},
  PM.P2({PM.Ptr(Nat.sub(U32.to_nat(nx2), U32.to_nat(fi)), m2, fi, ps2, PM.Rt.cells(os), z) == 0n : Nat},
  PM.P2(PM.HSK(dk, ds, ks, img, m2, nx2, fi, im, os, bs, fs, sp, pend2, ps2),
  PM.P2(PM.AccK(dk, ds, ks, img, m2, nx2, fi, im, os, Con{PM.TmpE{z, Nil{}}, xs}, sp, fs, ps2, zs2),
    {U32.is_le(nx, nx2) == True{} : Bool})))))))))))))))

# M.alloc's next does not go down
def alfr.le(-m: Cr.Cir.Cells, -ps: List<&2, U32>, -nx: U32, -st2: Cr.Cir.State, af: PM.AlFr(m, ps, nx, st2)) ->
  {U32.is_le(nx, PM.St.next(st2)) == True{} : Bool}:
  match af:
    case Tuple{a, _}:
      a

# alloc.post's state, as X.X.st of its registers, cells and next, with AlP
def alq.st(+dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +r: Nat, +keep: List<&2, Nat>,
  +os: List<&2, PM.Rt>, +bs: List<&2, PM.Rt>, +fs: List<&2, PM.AF>, +sp: U32, +ps: List<&2, U32>, +xs: List<&2, PM.TmpE>,
  st2: Cr.Cir.State, -R: Cr.Cir.State -> Type,
  h: AlQ(dk, ds, ks, img, regs, m, nx, fi, im, lim, inp, r, keep, os, bs, fs, sp, ps, xs, st2),
  k: @regs2: List<&2, U32> -> @m2: Cr.Cir.Cells -> @nx2: U32 -> @pg2: U32 -> @z: U32 -> @pend2: U32 -> @ps2: List<&2, U32> ->
    @ws: List<&2, PM.W1> -> @zs2: List<&2, PM.Rt> ->
    AlP(dk, ds, ks, img, regs, m, nx, fi, im, r, keep, os, bs, fs, sp, ps, xs, regs2, m2, nx2, z, pend2, ps2, ws, zs2) ->
    R(X.X.st(regs2, m2, nx2, fi, im, pg2, lim, inp))) -> R(st2):
  match st2:
    case Cr.Cir.State{+regs2, +m2, +nx2, +fi2, +im2, +pg2, +lim2, +inp2, +out2, +outn2}:
      (q, af) = h
      (sm, e1) = q
      (efi, s1) = sm
      (eim, s2) = s1
      (elim, s3) = s2
      (einp, s4) = s3
      (eout, s5) = s4
      (eoutn, s6) = s5
      (hl2, hk2) = s6
      (z, e2) = e1
      (pend2, e3) = e2
      (ps2, f1) = e3
      (hr, f2) = f1
      (hp, f3) = f2
      (hz0, f4) = f3
      (ho, f5) = f4
      (hm, f6) = f5
      (hzp, f7) = f6
      (hnx, f8) = f7
      (wx, f9) = f8
      (ws, wf) = wx
      (hcs, htk) = wf
      (hps, f10) = f9
      (hpt, f11) = f10
      (hs2, ex) = f11
      (zs2, hac2) = ex
      +hle = alfr.le(m, ps, nx, Cr.Cir.State{regs2, m2, nx2, fi2, im2, pg2, lim2, inp2, out2, outn2}, af)
      %Equal.sym(U32, fi2, fi, efi) : R(Cr.Cir.State{regs2, m2, nx2, _, im2, pg2, lim2, inp2, out2, outn2})
      %Equal.sym(U32, im2, im, eim) : R(Cr.Cir.State{regs2, m2, nx2, fi, _, pg2, lim2, inp2, out2, outn2})
      %Equal.sym(U32, lim2, lim, elim) : R(Cr.Cir.State{regs2, m2, nx2, fi, im, pg2, _, inp2, out2, outn2})
      %Equal.sym(List<&2, Word(8n)>, inp2, inp, einp) : R(Cr.Cir.State{regs2, m2, nx2, fi, im, pg2, lim, _, out2, outn2})
      %Equal.sym(List<&2, Word(8n)>, out2, Nil{}, eout) : R(Cr.Cir.State{regs2, m2, nx2, fi, im, pg2, lim, inp, _, outn2})
      %Equal.sym(U32, outn2, 0, eoutn) : R(Cr.Cir.State{regs2, m2, nx2, fi, im, pg2, lim, inp, Nil{}, _})
      k(regs2, m2, nx2, pg2, z, pend2, ps2, ws, zs2,
        (hk2, (hl2, (hr, (hp, (hz0, (ho, (hm, (hzp, (hnx, (hcs, (htk, (hps, (hpt, (hs2, (hac2, hle))))))))))))))))

# The premises data.post and data.done of move_kit.bend (U6; U0 left them as ?TODO)
# -------------------------------------------------------------------------------

def K.data.post(f, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, r, keep, os, bs, fs, sp, pend, ps, c, v, xs, zs, hs, hac, hl, hc, hp, hr, hk):
  ?TODO

def K.data.done(ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, r, os, bs, fs, sp, pend, ps, c, v, hs, hl, hc, hp, hr):
  ?TODO
