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
