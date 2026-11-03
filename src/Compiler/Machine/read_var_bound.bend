# compiler: the Var indices of a book that Book.read reads (layer B)
# =================================================================
#
# VB(t, B): every Var index of t is below B. The image holds a Var's index
# as a U32 (Img.go), so the machine reads it back only below 2^32.

import Base
import ../../Book/impl.bend as Bk

# every Var index of t is below B
def VB(t: Bk.Term, +B: Nat) -> Bool:
  match t:
    case Bk.Term.Var{i}:
      Nat.is_lt(i, B)
    case Bk.Term.Ref{_}:
      True{}
    case Bk.Term.Ann{x, y}:
      Bool.and(VB(x, B), VB(y, B))
    case Bk.Term.Let{_, v, f}:
      Bool.and(VB(v, B), VB(f, B))
    case Bk.Term.Typ{x}:
      VB(x, B)
    case Bk.Term.Min{a, b}:
      Bool.and(VB(a, B), VB(b, B))
    case Bk.Term.All{_, a, b}:
      Bool.and(VB(a, B), VB(b, B))
    case Bk.Term.Lam{_, f}:
      VB(f, B)
    case Bk.Term.App{_, f, x}:
      Bool.and(VB(f, B), VB(x, B))
    case Bk.Term.Sig{_, a, b}:
      Bool.and(VB(a, B), VB(b, B))
    case Bk.Term.Tup{_, a, b}:
      Bool.and(VB(a, B), VB(b, B))
    case Bk.Term.Prj{h}:
      VB(h, B)
    case Bk.Term.Enu{_}:
      True{}
    case Bk.Term.Lab{_}:
      True{}
    case Bk.Term.Mat{_, h, m}:
      Bool.and(VB(h, B), VB(m, B))
    case Bk.Term.Efq{}:
      True{}
    case Bk.Term.Eql{a, b, y}:
      Bool.and(VB(a, B), Bool.and(VB(b, B), VB(y, B)))
    case Bk.Term.Rfl{}:
      True{}
    case Bk.Term.Rwt{e, p, f}:
      Bool.and(VB(e, B), Bool.and(VB(p, B), VB(f, B)))
