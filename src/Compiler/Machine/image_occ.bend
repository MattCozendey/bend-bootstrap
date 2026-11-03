# compiler: a name of the image is in the image's names (layer B)
# =================================================================
#
# The image's names ks (T.tm.names, Img.known of the book's) hold every name
# of every label and λ-match of every body: Img.names lists them, Img.names.defs
# the book's, and Img.known puts the machine's own in front. Nm (definitions.bend)
# reads a cell's number back through ks; its proof needs the name's place in ks,
# so it needs the fact that the name is there.
#
# A name's copy in ks, as Data: Occ(ks, k) is Empty when ks is empty, and a
# choice of the head's name or the tail's copy otherwise (OrD, Either&2). The
# kit lifts a copy through append (occ.append.l/r) and through a term's own
# names (occ.names), and occ.first turns it into the Maybe that TR.first gives.
#
# GAll(t, ks) is the same fact for every name of the term t, as a P2 tree that
# mirrors the term: a leaf is Unit, a label's name is Occ(ks, k), a λ-match's is
# Occ(ks, k) then its two parts', and a node of two parts pairs its parts'.
# gall.prefix moves the list (occ.append.r at each leaf), gall.names moves it
# by a term's names (occ.names), names.all builds it for a term's own names
# (gall.prefix at the head of each part), and gall.defs builds the whole book's,
# from the names of the defs before it (names.app, app.assoc).

import Base
import ../../Shared/shared.bend as Sd
import ../../Book/impl.bend as Bk
import ./definitions.bend as D
import ./impl.bend as Mc
import ./image_names.bend as Nm
import ./image_tries.bend as TR
import ../need_big.bend as N

# a name's copy in a list of names, as Data
# -----------------------------------------

def OrD(-A: Data, -B: Data) -> Data:
  Either<&2, &2, A, B>

def Occ(ks: List<&2, List<&2, Word(8n)>>, +k: List<&2, Word(8n)>) -> Data:
  match ks:
    case Nil{}:
      Empty
    case Con{+n, +rest}:
      OrD({Sd.Name.is_eq(n, k) == True{} : Bool}, Occ(rest, k))

# k is the head
def occ.head(k: List<&2, Word(8n)>, rest: List<&2, List<&2, Word(8n)>>) -> Occ(Con{k, rest}, k):
  Inl{Nm.Name.eq.refl(k)}

# k is in the tail
def occ.cons(n: List<&2, Word(8n)>, rest: List<&2, List<&2, Word(8n)>>, +k: List<&2, Word(8n)>,
  o: Occ(rest, k)) -> Occ(Con{n, rest}, k):
  Inr{o}

# a copy in xs is a copy in xs, then ys
def occ.append.l(xs: List<&2, List<&2, Word(8n)>>, ys: List<&2, List<&2, Word(8n)>>, +k: List<&2, Word(8n)>,
  o: Occ(xs, k)) -> Occ(List.append(&2, List<&2, Word(8n)>, xs, ys), k):
  match xs:
    case Nil{}:
      Empty.absurd(Occ(ys, k), o)
    case Con{+n, +rest}:
      match o:
        case Inl{e}:
          Inl{e}
        case Inr{o2}:
          Inr{occ.append.l(rest, ys, k, o2)}

# a copy in ys is a copy in xs, then ys
def occ.append.r(xs: List<&2, List<&2, Word(8n)>>, ys: List<&2, List<&2, Word(8n)>>, +k: List<&2, Word(8n)>,
  o: Occ(ys, k)) -> Occ(List.append(&2, List<&2, Word(8n)>, xs, ys), k):
  match xs:
    case Nil{}:
      o
    case Con{+n, +rest}:
      Inr{occ.append.r(rest, ys, k, o)}

# a copy in ys is a copy in the names of t, then ys
def occ.names(t: Bk.Term, +ys: List<&2, List<&2, Word(8n)>>, +k: List<&2, Word(8n)>, o: Occ(ys, k)) ->
  Occ(Mc.Img.names(t, ys), k):
  match t:
    case Bk.Term.Var{_}:
      o
    case Bk.Term.Ref{_}:
      o
    case Bk.Term.Ann{+x, +y}:
      occ.names(x, Mc.Img.names(y, ys), k, occ.names(y, ys, k, o))
    case Bk.Term.Let{_, +x, +y}:
      occ.names(x, Mc.Img.names(y, ys), k, occ.names(y, ys, k, o))
    case Bk.Term.Typ{+x}:
      occ.names(x, ys, k, o)
    case Bk.Term.Min{+x, +y}:
      occ.names(x, Mc.Img.names(y, ys), k, occ.names(y, ys, k, o))
    case Bk.Term.All{_, +x, +y}:
      occ.names(x, Mc.Img.names(y, ys), k, occ.names(y, ys, k, o))
    case Bk.Term.Lam{_, +x}:
      occ.names(x, ys, k, o)
    case Bk.Term.App{_, +x, +y}:
      occ.names(x, Mc.Img.names(y, ys), k, occ.names(y, ys, k, o))
    case Bk.Term.Sig{_, +x, +y}:
      occ.names(x, Mc.Img.names(y, ys), k, occ.names(y, ys, k, o))
    case Bk.Term.Tup{_, +x, +y}:
      occ.names(x, Mc.Img.names(y, ys), k, occ.names(y, ys, k, o))
    case Bk.Term.Prj{+x}:
      occ.names(x, ys, k, o)
    case Bk.Term.Enu{_}:
      o
    case Bk.Term.Lab{+n}:
      occ.cons(n, ys, k, o)
    case Bk.Term.Mat{+n, +x, +y}:
      occ.cons(n, Mc.Img.names(x, Mc.Img.names(y, ys)), k,
        occ.names(x, Mc.Img.names(y, ys), k, occ.names(y, ys, k, o)))
    case Bk.Term.Efq{}:
      o
    case Bk.Term.Eql{+x, +y, +z}:
      occ.names(x, Mc.Img.names(y, Mc.Img.names(z, ys)), k,
        occ.names(y, Mc.Img.names(z, ys), k, occ.names(z, ys, k, o)))
    case Bk.Term.Rfl{}:
      o
    case Bk.Term.Rwt{+x, +y, +z}:
      occ.names(x, Mc.Img.names(y, Mc.Img.names(z, ys)), k,
        occ.names(y, Mc.Img.names(z, ys), k, occ.names(z, ys, k, o)))

# every name of a term is in a list, as a P2 tree
# ------------------------------------------------

def GAll(t: Bk.Term, +ks: List<&2, List<&2, Word(8n)>>) -> Data:
  match t:
    case Bk.Term.Var{_}:
      Unit
    case Bk.Term.Ref{_}:
      Unit
    case Bk.Term.Ann{+x, +y}:
      D.P2(GAll(x, ks), GAll(y, ks))
    case Bk.Term.Let{_, +x, +y}:
      D.P2(GAll(x, ks), GAll(y, ks))
    case Bk.Term.Typ{+x}:
      GAll(x, ks)
    case Bk.Term.Min{+x, +y}:
      D.P2(GAll(x, ks), GAll(y, ks))
    case Bk.Term.All{_, +x, +y}:
      D.P2(GAll(x, ks), GAll(y, ks))
    case Bk.Term.Lam{_, +x}:
      GAll(x, ks)
    case Bk.Term.App{_, +x, +y}:
      D.P2(GAll(x, ks), GAll(y, ks))
    case Bk.Term.Sig{_, +x, +y}:
      D.P2(GAll(x, ks), GAll(y, ks))
    case Bk.Term.Tup{_, +x, +y}:
      D.P2(GAll(x, ks), GAll(y, ks))
    case Bk.Term.Prj{+x}:
      GAll(x, ks)
    case Bk.Term.Enu{_}:
      Unit
    case Bk.Term.Lab{+k}:
      Occ(ks, k)
    case Bk.Term.Mat{+k, +x, +y}:
      D.P2(Occ(ks, k), D.P2(GAll(x, ks), GAll(y, ks)))
    case Bk.Term.Efq{}:
      Unit
    case Bk.Term.Eql{+x, +y, +z}:
      D.P2(GAll(x, ks), D.P2(GAll(y, ks), GAll(z, ks)))
    case Bk.Term.Rfl{}:
      Unit
    case Bk.Term.Rwt{+x, +y, +z}:
      D.P2(GAll(x, ks), D.P2(GAll(y, ks), GAll(z, ks)))

# a copy in ks is a copy in p, then ks
def gall.prefix(+p: List<&2, List<&2, Word(8n)>>, t: Bk.Term, +ks: List<&2, List<&2, Word(8n)>>,
  g: GAll(t, ks)) -> GAll(t, List.append(&2, List<&2, Word(8n)>, p, ks)):
  match t:
    case Bk.Term.Var{_}:
      Unit{}
    case Bk.Term.Ref{_}:
      Unit{}
    case Bk.Term.Ann{+x, +y}:
      (gx, gy) = g
      Tuple{gall.prefix(p, x, ks, gx), gall.prefix(p, y, ks, gy)}
    case Bk.Term.Let{_, +x, +y}:
      (gx, gy) = g
      Tuple{gall.prefix(p, x, ks, gx), gall.prefix(p, y, ks, gy)}
    case Bk.Term.Typ{+x}:
      gall.prefix(p, x, ks, g)
    case Bk.Term.Min{+x, +y}:
      (gx, gy) = g
      Tuple{gall.prefix(p, x, ks, gx), gall.prefix(p, y, ks, gy)}
    case Bk.Term.All{_, +x, +y}:
      (gx, gy) = g
      Tuple{gall.prefix(p, x, ks, gx), gall.prefix(p, y, ks, gy)}
    case Bk.Term.Lam{_, +x}:
      gall.prefix(p, x, ks, g)
    case Bk.Term.App{_, +x, +y}:
      (gx, gy) = g
      Tuple{gall.prefix(p, x, ks, gx), gall.prefix(p, y, ks, gy)}
    case Bk.Term.Sig{_, +x, +y}:
      (gx, gy) = g
      Tuple{gall.prefix(p, x, ks, gx), gall.prefix(p, y, ks, gy)}
    case Bk.Term.Tup{_, +x, +y}:
      (gx, gy) = g
      Tuple{gall.prefix(p, x, ks, gx), gall.prefix(p, y, ks, gy)}
    case Bk.Term.Prj{+x}:
      gall.prefix(p, x, ks, g)
    case Bk.Term.Enu{_}:
      Unit{}
    case Bk.Term.Lab{+k}:
      occ.append.r(p, ks, k, g)
    case Bk.Term.Mat{+k, +x, +y}:
      (gk, r) = g
      (gx, gy) = r
      Tuple{occ.append.r(p, ks, k, gk), Tuple{gall.prefix(p, x, ks, gx), gall.prefix(p, y, ks, gy)}}
    case Bk.Term.Efq{}:
      Unit{}
    case Bk.Term.Eql{+x, +y, +z}:
      (gx, r) = g
      (gy, gz) = r
      Tuple{gall.prefix(p, x, ks, gx), Tuple{gall.prefix(p, y, ks, gy), gall.prefix(p, z, ks, gz)}}
    case Bk.Term.Rfl{}:
      Unit{}
    case Bk.Term.Rwt{+x, +y, +z}:
      (gx, r) = g
      (gy, gz) = r
      Tuple{gall.prefix(p, x, ks, gx), Tuple{gall.prefix(p, y, ks, gy), gall.prefix(p, z, ks, gz)}}

# a copy in ks is a copy in the names of h, then ks
def gall.names(+h: Bk.Term, t: Bk.Term, +ks: List<&2, List<&2, Word(8n)>>, g: GAll(t, ks)) ->
  GAll(t, Mc.Img.names(h, ks)):
  match t:
    case Bk.Term.Var{_}:
      Unit{}
    case Bk.Term.Ref{_}:
      Unit{}
    case Bk.Term.Ann{+x, +y}:
      (gx, gy) = g
      Tuple{gall.names(h, x, ks, gx), gall.names(h, y, ks, gy)}
    case Bk.Term.Let{_, +x, +y}:
      (gx, gy) = g
      Tuple{gall.names(h, x, ks, gx), gall.names(h, y, ks, gy)}
    case Bk.Term.Typ{+x}:
      gall.names(h, x, ks, g)
    case Bk.Term.Min{+x, +y}:
      (gx, gy) = g
      Tuple{gall.names(h, x, ks, gx), gall.names(h, y, ks, gy)}
    case Bk.Term.All{_, +x, +y}:
      (gx, gy) = g
      Tuple{gall.names(h, x, ks, gx), gall.names(h, y, ks, gy)}
    case Bk.Term.Lam{_, +x}:
      gall.names(h, x, ks, g)
    case Bk.Term.App{_, +x, +y}:
      (gx, gy) = g
      Tuple{gall.names(h, x, ks, gx), gall.names(h, y, ks, gy)}
    case Bk.Term.Sig{_, +x, +y}:
      (gx, gy) = g
      Tuple{gall.names(h, x, ks, gx), gall.names(h, y, ks, gy)}
    case Bk.Term.Tup{_, +x, +y}:
      (gx, gy) = g
      Tuple{gall.names(h, x, ks, gx), gall.names(h, y, ks, gy)}
    case Bk.Term.Prj{+x}:
      gall.names(h, x, ks, g)
    case Bk.Term.Enu{_}:
      Unit{}
    case Bk.Term.Lab{+k}:
      occ.names(h, ks, k, g)
    case Bk.Term.Mat{+k, +x, +y}:
      (gk, r) = g
      (gx, gy) = r
      Tuple{occ.names(h, ks, k, gk), Tuple{gall.names(h, x, ks, gx), gall.names(h, y, ks, gy)}}
    case Bk.Term.Efq{}:
      Unit{}
    case Bk.Term.Eql{+x, +y, +z}:
      (gx, r) = g
      (gy, gz) = r
      Tuple{gall.names(h, x, ks, gx), Tuple{gall.names(h, y, ks, gy), gall.names(h, z, ks, gz)}}
    case Bk.Term.Rfl{}:
      Unit{}
    case Bk.Term.Rwt{+x, +y, +z}:
      (gx, r) = g
      (gy, gz) = r
      Tuple{gall.names(h, x, ks, gx), Tuple{gall.names(h, y, ks, gy), gall.names(h, z, ks, gz)}}

# a copy in ks is a copy in n, then ks
def gall.cons(n: List<&2, Word(8n)>, t: Bk.Term, +ks: List<&2, List<&2, Word(8n)>>, g: GAll(t, ks)) ->
  GAll(t, Con{n, ks}):
  gall.prefix(Con{n, Nil{}}, t, ks, g)

# every name of a term is in the term's names, then x
def names.all(t: Bk.Term, +x: List<&2, List<&2, Word(8n)>>) -> GAll(t, Mc.Img.names(t, x)):
  match t:
    case Bk.Term.Var{_}:
      Unit{}
    case Bk.Term.Ref{_}:
      Unit{}
    case Bk.Term.Ann{+a, +b}:
      Tuple{names.all(a, Mc.Img.names(b, x)), gall.names(a, b, Mc.Img.names(b, x), names.all(b, x))}
    case Bk.Term.Let{_, +a, +b}:
      Tuple{names.all(a, Mc.Img.names(b, x)), gall.names(a, b, Mc.Img.names(b, x), names.all(b, x))}
    case Bk.Term.Typ{+a}:
      names.all(a, x)
    case Bk.Term.Min{+a, +b}:
      Tuple{names.all(a, Mc.Img.names(b, x)), gall.names(a, b, Mc.Img.names(b, x), names.all(b, x))}
    case Bk.Term.All{_, +a, +b}:
      Tuple{names.all(a, Mc.Img.names(b, x)), gall.names(a, b, Mc.Img.names(b, x), names.all(b, x))}
    case Bk.Term.Lam{_, +a}:
      names.all(a, x)
    case Bk.Term.App{_, +a, +b}:
      Tuple{names.all(a, Mc.Img.names(b, x)), gall.names(a, b, Mc.Img.names(b, x), names.all(b, x))}
    case Bk.Term.Sig{_, +a, +b}:
      Tuple{names.all(a, Mc.Img.names(b, x)), gall.names(a, b, Mc.Img.names(b, x), names.all(b, x))}
    case Bk.Term.Tup{_, +a, +b}:
      Tuple{names.all(a, Mc.Img.names(b, x)), gall.names(a, b, Mc.Img.names(b, x), names.all(b, x))}
    case Bk.Term.Prj{+a}:
      names.all(a, x)
    case Bk.Term.Enu{_}:
      Unit{}
    case Bk.Term.Lab{+k}:
      occ.head(k, x)
    case Bk.Term.Mat{+k, +a, +b}:
      Tuple{occ.head(k, Mc.Img.names(a, Mc.Img.names(b, x))),
        Tuple{gall.cons(k, a, Mc.Img.names(a, Mc.Img.names(b, x)), names.all(a, Mc.Img.names(b, x))),
          gall.cons(k, b, Mc.Img.names(a, Mc.Img.names(b, x)),
            gall.names(a, b, Mc.Img.names(b, x), names.all(b, x)))}}
    case Bk.Term.Efq{}:
      Unit{}
    case Bk.Term.Eql{+a, +b, +c}:
      Tuple{names.all(a, Mc.Img.names(b, Mc.Img.names(c, x))),
        Tuple{gall.names(a, b, Mc.Img.names(b, Mc.Img.names(c, x)), names.all(b, Mc.Img.names(c, x))),
          gall.names(a, c, Mc.Img.names(b, Mc.Img.names(c, x)),
            gall.names(b, c, Mc.Img.names(c, x), names.all(c, x)))}}
    case Bk.Term.Rfl{}:
      Unit{}
    case Bk.Term.Rwt{+a, +b, +c}:
      Tuple{names.all(a, Mc.Img.names(b, Mc.Img.names(c, x))),
        Tuple{gall.names(a, b, Mc.Img.names(b, Mc.Img.names(c, x)), names.all(b, Mc.Img.names(c, x))),
          gall.names(a, c, Mc.Img.names(b, Mc.Img.names(c, x)),
            gall.names(b, c, Mc.Img.names(c, x), names.all(c, x)))}}

# a term's names, then ys, split as the term's names alone, then ys
# ------------------------------------------------------------------

# (xs, then ys), then zs is xs, then (ys, then zs)
def app.assoc(xs: List<&2, List<&2, Word(8n)>>, +ys: List<&2, List<&2, Word(8n)>>,
  +zs: List<&2, List<&2, Word(8n)>>) ->
  {List.append(&2, List<&2, Word(8n)>, List.append(&2, List<&2, Word(8n)>, xs, ys), zs) ==
   List.append(&2, List<&2, Word(8n)>, xs, List.append(&2, List<&2, Word(8n)>, ys, zs)) :
    List<&2, List<&2, Word(8n)>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+n, +rest}:
      %app.assoc(rest, ys, zs) :
        {Con{n, List.append(&2, List<&2, Word(8n)>, List.append(&2, List<&2, Word(8n)>, rest, ys), zs)} ==
         Con{n, _} : List<&2, List<&2, Word(8n)>>}
      {==}

def names.app(t: Bk.Term, +ys: List<&2, List<&2, Word(8n)>>) ->
  {Mc.Img.names(t, ys) == List.append(&2, List<&2, Word(8n)>, Mc.Img.names(t, Nil{}), ys) :
    List<&2, List<&2, Word(8n)>>}:
  match t:
    case Bk.Term.Var{_}:
      {==}
    case Bk.Term.Ref{_}:
      {==}
    case Bk.Term.Ann{+a, +b}:
      +na = Mc.Img.names(a, Nil{})
      +nb = Mc.Img.names(b, Nil{})
      %Equal.sym(List<&2, List<&2, Word(8n)>>, Mc.Img.names(b, ys),
          List.append(&2, List<&2, Word(8n)>, nb, ys), names.app(b, ys)) :
        {Mc.Img.names(a, _) == List.append(&2, List<&2, Word(8n)>, Mc.Img.names(a, nb), ys) :
          List<&2, List<&2, Word(8n)>>}
      %Equal.sym(List<&2, List<&2, Word(8n)>>, Mc.Img.names(a, List.append(&2, List<&2, Word(8n)>, nb, ys)),
          List.append(&2, List<&2, Word(8n)>, na, List.append(&2, List<&2, Word(8n)>, nb, ys)),
          names.app(a, List.append(&2, List<&2, Word(8n)>, nb, ys))) :
        {_ == List.append(&2, List<&2, Word(8n)>, Mc.Img.names(a, nb), ys) : List<&2, List<&2, Word(8n)>>}
      %app.assoc(na, nb, ys) :
        {_ == List.append(&2, List<&2, Word(8n)>, Mc.Img.names(a, nb), ys) : List<&2, List<&2, Word(8n)>>}
      %Equal.sym(List<&2, List<&2, Word(8n)>>, Mc.Img.names(a, nb),
          List.append(&2, List<&2, Word(8n)>, na, nb), names.app(a, nb)) :
        {List.append(&2, List<&2, Word(8n)>, List.append(&2, List<&2, Word(8n)>, na, nb), ys) ==
         List.append(&2, List<&2, Word(8n)>, _, ys) : List<&2, List<&2, Word(8n)>>}
      {==}
    case Bk.Term.Let{_, +a, +b}:
      +na = Mc.Img.names(a, Nil{})
      +nb = Mc.Img.names(b, Nil{})
      %Equal.sym(List<&2, List<&2, Word(8n)>>, Mc.Img.names(b, ys),
          List.append(&2, List<&2, Word(8n)>, nb, ys), names.app(b, ys)) :
        {Mc.Img.names(a, _) == List.append(&2, List<&2, Word(8n)>, Mc.Img.names(a, nb), ys) :
          List<&2, List<&2, Word(8n)>>}
      %Equal.sym(List<&2, List<&2, Word(8n)>>, Mc.Img.names(a, List.append(&2, List<&2, Word(8n)>, nb, ys)),
          List.append(&2, List<&2, Word(8n)>, na, List.append(&2, List<&2, Word(8n)>, nb, ys)),
          names.app(a, List.append(&2, List<&2, Word(8n)>, nb, ys))) :
        {_ == List.append(&2, List<&2, Word(8n)>, Mc.Img.names(a, nb), ys) : List<&2, List<&2, Word(8n)>>}
      %app.assoc(na, nb, ys) :
        {_ == List.append(&2, List<&2, Word(8n)>, Mc.Img.names(a, nb), ys) : List<&2, List<&2, Word(8n)>>}
      %Equal.sym(List<&2, List<&2, Word(8n)>>, Mc.Img.names(a, nb),
          List.append(&2, List<&2, Word(8n)>, na, nb), names.app(a, nb)) :
        {List.append(&2, List<&2, Word(8n)>, List.append(&2, List<&2, Word(8n)>, na, nb), ys) ==
         List.append(&2, List<&2, Word(8n)>, _, ys) : List<&2, List<&2, Word(8n)>>}
      {==}
    case Bk.Term.Typ{+a}:
      names.app(a, ys)
    case Bk.Term.Min{+a, +b}:
      +na = Mc.Img.names(a, Nil{})
      +nb = Mc.Img.names(b, Nil{})
      %Equal.sym(List<&2, List<&2, Word(8n)>>, Mc.Img.names(b, ys),
          List.append(&2, List<&2, Word(8n)>, nb, ys), names.app(b, ys)) :
        {Mc.Img.names(a, _) == List.append(&2, List<&2, Word(8n)>, Mc.Img.names(a, nb), ys) :
          List<&2, List<&2, Word(8n)>>}
      %Equal.sym(List<&2, List<&2, Word(8n)>>, Mc.Img.names(a, List.append(&2, List<&2, Word(8n)>, nb, ys)),
          List.append(&2, List<&2, Word(8n)>, na, List.append(&2, List<&2, Word(8n)>, nb, ys)),
          names.app(a, List.append(&2, List<&2, Word(8n)>, nb, ys))) :
        {_ == List.append(&2, List<&2, Word(8n)>, Mc.Img.names(a, nb), ys) : List<&2, List<&2, Word(8n)>>}
      %app.assoc(na, nb, ys) :
        {_ == List.append(&2, List<&2, Word(8n)>, Mc.Img.names(a, nb), ys) : List<&2, List<&2, Word(8n)>>}
      %Equal.sym(List<&2, List<&2, Word(8n)>>, Mc.Img.names(a, nb),
          List.append(&2, List<&2, Word(8n)>, na, nb), names.app(a, nb)) :
        {List.append(&2, List<&2, Word(8n)>, List.append(&2, List<&2, Word(8n)>, na, nb), ys) ==
         List.append(&2, List<&2, Word(8n)>, _, ys) : List<&2, List<&2, Word(8n)>>}
      {==}
    case Bk.Term.All{_, +a, +b}:
      +na = Mc.Img.names(a, Nil{})
      +nb = Mc.Img.names(b, Nil{})
      %Equal.sym(List<&2, List<&2, Word(8n)>>, Mc.Img.names(b, ys),
          List.append(&2, List<&2, Word(8n)>, nb, ys), names.app(b, ys)) :
        {Mc.Img.names(a, _) == List.append(&2, List<&2, Word(8n)>, Mc.Img.names(a, nb), ys) :
          List<&2, List<&2, Word(8n)>>}
      %Equal.sym(List<&2, List<&2, Word(8n)>>, Mc.Img.names(a, List.append(&2, List<&2, Word(8n)>, nb, ys)),
          List.append(&2, List<&2, Word(8n)>, na, List.append(&2, List<&2, Word(8n)>, nb, ys)),
          names.app(a, List.append(&2, List<&2, Word(8n)>, nb, ys))) :
        {_ == List.append(&2, List<&2, Word(8n)>, Mc.Img.names(a, nb), ys) : List<&2, List<&2, Word(8n)>>}
      %app.assoc(na, nb, ys) :
        {_ == List.append(&2, List<&2, Word(8n)>, Mc.Img.names(a, nb), ys) : List<&2, List<&2, Word(8n)>>}
      %Equal.sym(List<&2, List<&2, Word(8n)>>, Mc.Img.names(a, nb),
          List.append(&2, List<&2, Word(8n)>, na, nb), names.app(a, nb)) :
        {List.append(&2, List<&2, Word(8n)>, List.append(&2, List<&2, Word(8n)>, na, nb), ys) ==
         List.append(&2, List<&2, Word(8n)>, _, ys) : List<&2, List<&2, Word(8n)>>}
      {==}
    case Bk.Term.Lam{_, +a}:
      names.app(a, ys)
    case Bk.Term.App{_, +a, +b}:
      +na = Mc.Img.names(a, Nil{})
      +nb = Mc.Img.names(b, Nil{})
      %Equal.sym(List<&2, List<&2, Word(8n)>>, Mc.Img.names(b, ys),
          List.append(&2, List<&2, Word(8n)>, nb, ys), names.app(b, ys)) :
        {Mc.Img.names(a, _) == List.append(&2, List<&2, Word(8n)>, Mc.Img.names(a, nb), ys) :
          List<&2, List<&2, Word(8n)>>}
      %Equal.sym(List<&2, List<&2, Word(8n)>>, Mc.Img.names(a, List.append(&2, List<&2, Word(8n)>, nb, ys)),
          List.append(&2, List<&2, Word(8n)>, na, List.append(&2, List<&2, Word(8n)>, nb, ys)),
          names.app(a, List.append(&2, List<&2, Word(8n)>, nb, ys))) :
        {_ == List.append(&2, List<&2, Word(8n)>, Mc.Img.names(a, nb), ys) : List<&2, List<&2, Word(8n)>>}
      %app.assoc(na, nb, ys) :
        {_ == List.append(&2, List<&2, Word(8n)>, Mc.Img.names(a, nb), ys) : List<&2, List<&2, Word(8n)>>}
      %Equal.sym(List<&2, List<&2, Word(8n)>>, Mc.Img.names(a, nb),
          List.append(&2, List<&2, Word(8n)>, na, nb), names.app(a, nb)) :
        {List.append(&2, List<&2, Word(8n)>, List.append(&2, List<&2, Word(8n)>, na, nb), ys) ==
         List.append(&2, List<&2, Word(8n)>, _, ys) : List<&2, List<&2, Word(8n)>>}
      {==}
    case Bk.Term.Sig{_, +a, +b}:
      +na = Mc.Img.names(a, Nil{})
      +nb = Mc.Img.names(b, Nil{})
      %Equal.sym(List<&2, List<&2, Word(8n)>>, Mc.Img.names(b, ys),
          List.append(&2, List<&2, Word(8n)>, nb, ys), names.app(b, ys)) :
        {Mc.Img.names(a, _) == List.append(&2, List<&2, Word(8n)>, Mc.Img.names(a, nb), ys) :
          List<&2, List<&2, Word(8n)>>}
      %Equal.sym(List<&2, List<&2, Word(8n)>>, Mc.Img.names(a, List.append(&2, List<&2, Word(8n)>, nb, ys)),
          List.append(&2, List<&2, Word(8n)>, na, List.append(&2, List<&2, Word(8n)>, nb, ys)),
          names.app(a, List.append(&2, List<&2, Word(8n)>, nb, ys))) :
        {_ == List.append(&2, List<&2, Word(8n)>, Mc.Img.names(a, nb), ys) : List<&2, List<&2, Word(8n)>>}
      %app.assoc(na, nb, ys) :
        {_ == List.append(&2, List<&2, Word(8n)>, Mc.Img.names(a, nb), ys) : List<&2, List<&2, Word(8n)>>}
      %Equal.sym(List<&2, List<&2, Word(8n)>>, Mc.Img.names(a, nb),
          List.append(&2, List<&2, Word(8n)>, na, nb), names.app(a, nb)) :
        {List.append(&2, List<&2, Word(8n)>, List.append(&2, List<&2, Word(8n)>, na, nb), ys) ==
         List.append(&2, List<&2, Word(8n)>, _, ys) : List<&2, List<&2, Word(8n)>>}
      {==}
    case Bk.Term.Tup{_, +a, +b}:
      +na = Mc.Img.names(a, Nil{})
      +nb = Mc.Img.names(b, Nil{})
      %Equal.sym(List<&2, List<&2, Word(8n)>>, Mc.Img.names(b, ys),
          List.append(&2, List<&2, Word(8n)>, nb, ys), names.app(b, ys)) :
        {Mc.Img.names(a, _) == List.append(&2, List<&2, Word(8n)>, Mc.Img.names(a, nb), ys) :
          List<&2, List<&2, Word(8n)>>}
      %Equal.sym(List<&2, List<&2, Word(8n)>>, Mc.Img.names(a, List.append(&2, List<&2, Word(8n)>, nb, ys)),
          List.append(&2, List<&2, Word(8n)>, na, List.append(&2, List<&2, Word(8n)>, nb, ys)),
          names.app(a, List.append(&2, List<&2, Word(8n)>, nb, ys))) :
        {_ == List.append(&2, List<&2, Word(8n)>, Mc.Img.names(a, nb), ys) : List<&2, List<&2, Word(8n)>>}
      %app.assoc(na, nb, ys) :
        {_ == List.append(&2, List<&2, Word(8n)>, Mc.Img.names(a, nb), ys) : List<&2, List<&2, Word(8n)>>}
      %Equal.sym(List<&2, List<&2, Word(8n)>>, Mc.Img.names(a, nb),
          List.append(&2, List<&2, Word(8n)>, na, nb), names.app(a, nb)) :
        {List.append(&2, List<&2, Word(8n)>, List.append(&2, List<&2, Word(8n)>, na, nb), ys) ==
         List.append(&2, List<&2, Word(8n)>, _, ys) : List<&2, List<&2, Word(8n)>>}
      {==}
    case Bk.Term.Prj{+a}:
      names.app(a, ys)
    case Bk.Term.Enu{_}:
      {==}
    case Bk.Term.Lab{+k}:
      {==}
    case Bk.Term.Mat{+k, +a, +b}:
      +na = Mc.Img.names(a, Nil{})
      +nb = Mc.Img.names(b, Nil{})
      %Equal.sym(List<&2, List<&2, Word(8n)>>, Mc.Img.names(b, ys),
          List.append(&2, List<&2, Word(8n)>, nb, ys), names.app(b, ys)) :
        {Con{k, Mc.Img.names(a, _)} ==
         Con{k, List.append(&2, List<&2, Word(8n)>, Mc.Img.names(a, nb), ys)} : List<&2, List<&2, Word(8n)>>}
      %Equal.sym(List<&2, List<&2, Word(8n)>>, Mc.Img.names(a, List.append(&2, List<&2, Word(8n)>, nb, ys)),
          List.append(&2, List<&2, Word(8n)>, na, List.append(&2, List<&2, Word(8n)>, nb, ys)),
          names.app(a, List.append(&2, List<&2, Word(8n)>, nb, ys))) :
        {Con{k, _} == Con{k, List.append(&2, List<&2, Word(8n)>, Mc.Img.names(a, nb), ys)} :
          List<&2, List<&2, Word(8n)>>}
      %app.assoc(na, nb, ys) :
        {Con{k, _} == Con{k, List.append(&2, List<&2, Word(8n)>, Mc.Img.names(a, nb), ys)} :
          List<&2, List<&2, Word(8n)>>}
      %Equal.sym(List<&2, List<&2, Word(8n)>>, Mc.Img.names(a, nb),
          List.append(&2, List<&2, Word(8n)>, na, nb), names.app(a, nb)) :
        {Con{k, List.append(&2, List<&2, Word(8n)>, List.append(&2, List<&2, Word(8n)>, na, nb), ys)} ==
         Con{k, List.append(&2, List<&2, Word(8n)>, _, ys)} : List<&2, List<&2, Word(8n)>>}
      {==}
    case Bk.Term.Efq{}:
      {==}
    case Bk.Term.Eql{+a, +b, +c}:
      +na = Mc.Img.names(a, Nil{})
      +nb = Mc.Img.names(b, Nil{})
      +nc = Mc.Img.names(c, Nil{})
      %Equal.sym(List<&2, List<&2, Word(8n)>>, Mc.Img.names(c, ys),
          List.append(&2, List<&2, Word(8n)>, nc, ys), names.app(c, ys)) :
        {Mc.Img.names(a, Mc.Img.names(b, _)) ==
         List.append(&2, List<&2, Word(8n)>, Mc.Img.names(a, Mc.Img.names(b, nc)), ys) : List<&2, List<&2, Word(8n)>>}
      %Equal.sym(List<&2, List<&2, Word(8n)>>, Mc.Img.names(b, List.append(&2, List<&2, Word(8n)>, nc, ys)),
          List.append(&2, List<&2, Word(8n)>, nb, List.append(&2, List<&2, Word(8n)>, nc, ys)),
          names.app(b, List.append(&2, List<&2, Word(8n)>, nc, ys))) :
        {Mc.Img.names(a, _) ==
         List.append(&2, List<&2, Word(8n)>, Mc.Img.names(a, Mc.Img.names(b, nc)), ys) : List<&2, List<&2, Word(8n)>>}
      %Equal.sym(List<&2, List<&2, Word(8n)>>,
          Mc.Img.names(a, List.append(&2, List<&2, Word(8n)>, nb, List.append(&2, List<&2, Word(8n)>, nc, ys))),
          List.append(&2, List<&2, Word(8n)>, na, List.append(&2, List<&2, Word(8n)>, nb, List.append(&2, List<&2, Word(8n)>, nc, ys))),
          names.app(a, List.append(&2, List<&2, Word(8n)>, nb, List.append(&2, List<&2, Word(8n)>, nc, ys)))) :
        {_ == List.append(&2, List<&2, Word(8n)>, Mc.Img.names(a, Mc.Img.names(b, nc)), ys) :
          List<&2, List<&2, Word(8n)>>}
      %app.assoc(na, nb, List.append(&2, List<&2, Word(8n)>, nc, ys)) :
        {_ == List.append(&2, List<&2, Word(8n)>, Mc.Img.names(a, Mc.Img.names(b, nc)), ys) :
          List<&2, List<&2, Word(8n)>>}
      %app.assoc(List.append(&2, List<&2, Word(8n)>, na, nb), nc, ys) :
        {_ == List.append(&2, List<&2, Word(8n)>, Mc.Img.names(a, Mc.Img.names(b, nc)), ys) :
          List<&2, List<&2, Word(8n)>>}
      %Equal.sym(List<&2, List<&2, Word(8n)>>, Mc.Img.names(b, nc),
          List.append(&2, List<&2, Word(8n)>, nb, nc), names.app(b, nc)) :
        {List.append(&2, List<&2, Word(8n)>, List.append(&2, List<&2, Word(8n)>, List.append(&2, List<&2, Word(8n)>, na, nb), nc), ys) ==
         List.append(&2, List<&2, Word(8n)>, Mc.Img.names(a, _), ys) : List<&2, List<&2, Word(8n)>>}
      %Equal.sym(List<&2, List<&2, Word(8n)>>, Mc.Img.names(a, List.append(&2, List<&2, Word(8n)>, nb, nc)),
          List.append(&2, List<&2, Word(8n)>, na, List.append(&2, List<&2, Word(8n)>, nb, nc)),
          names.app(a, List.append(&2, List<&2, Word(8n)>, nb, nc))) :
        {List.append(&2, List<&2, Word(8n)>, List.append(&2, List<&2, Word(8n)>, List.append(&2, List<&2, Word(8n)>, na, nb), nc), ys) ==
         List.append(&2, List<&2, Word(8n)>, _, ys) : List<&2, List<&2, Word(8n)>>}
      %app.assoc(na, nb, nc) :
        {List.append(&2, List<&2, Word(8n)>, List.append(&2, List<&2, Word(8n)>, List.append(&2, List<&2, Word(8n)>, na, nb), nc), ys) ==
         List.append(&2, List<&2, Word(8n)>, _, ys) : List<&2, List<&2, Word(8n)>>}
      {==}
    case Bk.Term.Rfl{}:
      {==}
    case Bk.Term.Rwt{+a, +b, +c}:
      +na = Mc.Img.names(a, Nil{})
      +nb = Mc.Img.names(b, Nil{})
      +nc = Mc.Img.names(c, Nil{})
      %Equal.sym(List<&2, List<&2, Word(8n)>>, Mc.Img.names(c, ys),
          List.append(&2, List<&2, Word(8n)>, nc, ys), names.app(c, ys)) :
        {Mc.Img.names(a, Mc.Img.names(b, _)) ==
         List.append(&2, List<&2, Word(8n)>, Mc.Img.names(a, Mc.Img.names(b, nc)), ys) : List<&2, List<&2, Word(8n)>>}
      %Equal.sym(List<&2, List<&2, Word(8n)>>, Mc.Img.names(b, List.append(&2, List<&2, Word(8n)>, nc, ys)),
          List.append(&2, List<&2, Word(8n)>, nb, List.append(&2, List<&2, Word(8n)>, nc, ys)),
          names.app(b, List.append(&2, List<&2, Word(8n)>, nc, ys))) :
        {Mc.Img.names(a, _) ==
         List.append(&2, List<&2, Word(8n)>, Mc.Img.names(a, Mc.Img.names(b, nc)), ys) : List<&2, List<&2, Word(8n)>>}
      %Equal.sym(List<&2, List<&2, Word(8n)>>,
          Mc.Img.names(a, List.append(&2, List<&2, Word(8n)>, nb, List.append(&2, List<&2, Word(8n)>, nc, ys))),
          List.append(&2, List<&2, Word(8n)>, na, List.append(&2, List<&2, Word(8n)>, nb, List.append(&2, List<&2, Word(8n)>, nc, ys))),
          names.app(a, List.append(&2, List<&2, Word(8n)>, nb, List.append(&2, List<&2, Word(8n)>, nc, ys)))) :
        {_ == List.append(&2, List<&2, Word(8n)>, Mc.Img.names(a, Mc.Img.names(b, nc)), ys) :
          List<&2, List<&2, Word(8n)>>}
      %app.assoc(na, nb, List.append(&2, List<&2, Word(8n)>, nc, ys)) :
        {_ == List.append(&2, List<&2, Word(8n)>, Mc.Img.names(a, Mc.Img.names(b, nc)), ys) :
          List<&2, List<&2, Word(8n)>>}
      %app.assoc(List.append(&2, List<&2, Word(8n)>, na, nb), nc, ys) :
        {_ == List.append(&2, List<&2, Word(8n)>, Mc.Img.names(a, Mc.Img.names(b, nc)), ys) :
          List<&2, List<&2, Word(8n)>>}
      %Equal.sym(List<&2, List<&2, Word(8n)>>, Mc.Img.names(b, nc),
          List.append(&2, List<&2, Word(8n)>, nb, nc), names.app(b, nc)) :
        {List.append(&2, List<&2, Word(8n)>, List.append(&2, List<&2, Word(8n)>, List.append(&2, List<&2, Word(8n)>, na, nb), nc), ys) ==
         List.append(&2, List<&2, Word(8n)>, Mc.Img.names(a, _), ys) : List<&2, List<&2, Word(8n)>>}
      %Equal.sym(List<&2, List<&2, Word(8n)>>, Mc.Img.names(a, List.append(&2, List<&2, Word(8n)>, nb, nc)),
          List.append(&2, List<&2, Word(8n)>, na, List.append(&2, List<&2, Word(8n)>, nb, nc)),
          names.app(a, List.append(&2, List<&2, Word(8n)>, nb, nc))) :
        {List.append(&2, List<&2, Word(8n)>, List.append(&2, List<&2, Word(8n)>, List.append(&2, List<&2, Word(8n)>, na, nb), nc), ys) ==
         List.append(&2, List<&2, Word(8n)>, _, ys) : List<&2, List<&2, Word(8n)>>}
      %app.assoc(na, nb, nc) :
        {List.append(&2, List<&2, Word(8n)>, List.append(&2, List<&2, Word(8n)>, List.append(&2, List<&2, Word(8n)>, na, nb), nc), ys) ==
         List.append(&2, List<&2, Word(8n)>, _, ys) : List<&2, List<&2, Word(8n)>>}
      {==}

# every body's names are in ks
# -----------------------------

def GallD(dl: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>) -> Data:
  match dl:
    case Nil{}:
      Unit
    case Con{Bk.Def{_, _, +v, _}, +rest}:
      D.P2(GAll(v, ks), GallD(rest, ks))

# a copy in ks0 is a copy in ks
def gall.rw(+t: Bk.Term, +ks0: List<&2, List<&2, Word(8n)>>, +ks: List<&2, List<&2, Word(8n)>>,
  +e: {ks0 == ks : List<&2, List<&2, Word(8n)>>}, g: GAll(t, ks0)) -> GAll(t, ks):
  %e : GAll(t, _)
  g

# every body's names are in acc, then the defs' names
def gall.defs(dl: List<&2, Bk.Def>, +acc: List<&2, List<&2, Word(8n)>>, +ks: List<&2, List<&2, Word(8n)>>,
  +e: {List.append(&2, List<&2, Word(8n)>, acc, Mc.Img.names.defs(dl)) == ks : List<&2, List<&2, Word(8n)>>}) ->
  GallD(dl, ks):
  match dl:
    case Nil{}:
      Unit{}
    case Con{Bk.Def{_, _, +v, _}, +rest}:
      +nv = Mc.Img.names(v, Nil{})
      +c = Mc.Img.names.defs(rest)
      +hg = gall.rw(v, List.append(&2, List<&2, Word(8n)>, acc, Mc.Img.names(v, c)), ks, e,
        gall.prefix(acc, v, Mc.Img.names(v, c), names.all(v, c)))
      +ea = Equal.cong(List<&2, List<&2, Word(8n)>>, List<&2, List<&2, Word(8n)>>,
        z => List.append(&2, List<&2, Word(8n)>, acc, z),
        Mc.Img.names(v, c), List.append(&2, List<&2, Word(8n)>, nv, c), names.app(v, c))
      +eb = app.assoc(acc, nv, c)
      +et = Equal.trans(List<&2, List<&2, Word(8n)>>,
        List.append(&2, List<&2, Word(8n)>, List.append(&2, List<&2, Word(8n)>, acc, nv), c),
        List.append(&2, List<&2, Word(8n)>, acc, List.append(&2, List<&2, Word(8n)>, nv, c)),
        ks, eb,
        Equal.trans(List<&2, List<&2, Word(8n)>>,
          List.append(&2, List<&2, Word(8n)>, acc, List.append(&2, List<&2, Word(8n)>, nv, c)),
          List.append(&2, List<&2, Word(8n)>, acc, Mc.Img.names(v, c)),
          ks,
          Equal.sym(List<&2, List<&2, Word(8n)>>,
            List.append(&2, List<&2, Word(8n)>, acc, Mc.Img.names(v, c)),
            List.append(&2, List<&2, Word(8n)>, acc, List.append(&2, List<&2, Word(8n)>, nv, c)), ea),
          e))
      Tuple{hg, gall.defs(rest, List.append(&2, List<&2, Word(8n)>, acc, nv), ks, et)}

# the first copy of k in ks, from a copy in ks
# ---------------------------------------------

def occ.first(ks: List<&2, List<&2, Word(8n)>>, +k: List<&2, Word(8n)>, o: Occ(ks, k)) ->
  {TR.first(ks, k) == Some{k} : Maybe<&2, List<&2, Word(8n)>>}:
  match ks:
    case Nil{}:
      Empty.absurd({TR.first(Nil{}, k) == Some{k} : Maybe<&2, List<&2, Word(8n)>>}, o)
    case Con{+n, +rest}:
      match o:
        case Inl{e}:
          +hb = e
          %Equal.sym(Maybe<&2, List<&2, Word(8n)>>, TR.first(Con{n, rest}, k), Some{n},
              TR.pick.true(Maybe<&2, List<&2, Word(8n)>>, Sd.Name.is_eq(n, k), Some{n}, TR.first(rest, k), hb)) :
            {_ == Some{k} : Maybe<&2, List<&2, Word(8n)>>}
          Equal.cong(List<&2, Word(8n)>, Maybe<&2, List<&2, Word(8n)>>, z => Some{z}, n, k,
            Nm.Name.eq.true(n, k, hb))
        case Inr{o2}:
          TR.name.split(n, k, Sd.Name.is_eq(n, k), {==},
            {TR.first(Con{n, rest}, k) == Some{k} : Maybe<&2, List<&2, Word(8n)>>},
            +eq => +hb2 =>
              %Equal.sym(Maybe<&2, List<&2, Word(8n)>>, TR.first(Con{n, rest}, k), Some{n},
                  TR.pick.true(Maybe<&2, List<&2, Word(8n)>>, Sd.Name.is_eq(n, k), Some{n}, TR.first(rest, k), hb2)) :
                {_ == Some{k} : Maybe<&2, List<&2, Word(8n)>>}
              Equal.cong(List<&2, Word(8n)>, Maybe<&2, List<&2, Word(8n)>>, z => Some{z}, n, k, eq),
            ne => +hb2 =>
              %Equal.sym(Maybe<&2, List<&2, Word(8n)>>, TR.first(Con{n, rest}, k), TR.first(rest, k),
                  TR.pick.false(Maybe<&2, List<&2, Word(8n)>>, Sd.Name.is_eq(n, k), Some{n}, TR.first(rest, k), hb2)) :
                {_ == Some{k} : Maybe<&2, List<&2, Word(8n)>>}
              occ.first(rest, k, o2))
