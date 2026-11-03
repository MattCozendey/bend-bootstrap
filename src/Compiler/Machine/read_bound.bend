# compiler: the reader's bound
# ============================
#
# A book that Book.read reads from p has every Var index of every body below
# 2^31, so Defs.below(ds, 2^31) holds, and so every term that Eval reaches
# from the start term stays below 2^31 (free_variables.bend).
#
# need_big.bend's G counts the bytes that the writer writes for a term of a
# stack: each token of the reading adds 2 to the stack's G (N.Ge, the .ge
# lemmas). This file proves the other side (Gx.R, the .le lemmas: each token
# adds at most 2), so a book read from p has a G of at most |p|. Gt(t, a) is
# t's own bytes plus a, a Var index is below its own bytes (Term.below(t, 1 +
# Gt(t, 0))), and the bytes are below |p|, which Img.small (img_small.bend)
# keeps below 2^26.

import Base
import ../../Book/impl.bend as Bk
import ../need_big.bend as N
import ../img_small.bend as I
import ./impl.bend as Mc
import ./definitions.bend as PM
import ./free_variables.bend as Fv

# The other side of the token's G
# -------------------------------

# a token's result: none, or a stack of G at most 2 more than w
def Gx.R(r: Maybe<List<&2, Bk.Item>>, w: Nat) -> Type:
  match r:
    case None{}:
      Unit
    case Some{s}:
      N.Le(N.Gs(s, 0n), 2n+w)

# Each token adds at most 2 to G
# ------------------------------

def Gx.succ(s0: List<&2, Bk.Item>) -> Gx.R(Bk.Book.read.succ(s0), N.Gs(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{Bk.Item.quan{_}, _}:
      Unit{}
    case Con{Bk.Item.nat{+x1}, +rest}:
      N.le_refl(N.Gs(Con{Bk.Item.nat{1n+x1}, rest}, 0n))
    case Con{Bk.Item.name{_}, _}:
      Unit{}
    case Con{Bk.Item.names{_}, _}:
      Unit{}
    case Con{Bk.Item.bool{_}, _}:
      Unit{}
    case Con{Bk.Item.term{_}, _}:
      Unit{}
    case Con{Bk.Item.def{_}, _}:
      Unit{}
    case Con{Bk.Item.defs{_}, _}:
      Unit{}

def Gx.byte(s0: List<&2, Bk.Item>, b: Word(8n)) -> Gx.R(Bk.Book.read.byte(s0, b), N.Gs(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{Bk.Item.quan{_}, _}:
      Unit{}
    case Con{Bk.Item.nat{_}, _}:
      Unit{}
    case Con{Bk.Item.name{+x1}, +rest}:
      N.le_refl(N.Gs(Con{Bk.Item.name{Con{b, x1}}, rest}, 0n))
    case Con{Bk.Item.names{_}, _}:
      Unit{}
    case Con{Bk.Item.bool{_}, _}:
      Unit{}
    case Con{Bk.Item.term{_}, _}:
      Unit{}
    case Con{Bk.Item.def{_}, _}:
      Unit{}
    case Con{Bk.Item.defs{_}, _}:
      Unit{}

def Gx.names(s0: List<&2, Bk.Item>) -> Gx.R(Bk.Book.read.names(s0), N.Gs(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{Bk.Item.quan{_}, _}:
      Unit{}
    case Con{Bk.Item.nat{_}, _}:
      Unit{}
    case Con{Bk.Item.name{+x1}, +s1}:
      match s1:
        case Nil{}:
          Unit{}
        case Con{Bk.Item.quan{_}, _}:
          Unit{}
        case Con{Bk.Item.nat{_}, _}:
          Unit{}
        case Con{Bk.Item.name{_}, _}:
          Unit{}
        case Con{Bk.Item.names{+x2}, +rest}:
          N.le_refl(N.Gs(Con{Bk.Item.names{Con{x1, x2}}, rest}, 0n))
        case Con{Bk.Item.bool{_}, _}:
          Unit{}
        case Con{Bk.Item.term{_}, _}:
          Unit{}
        case Con{Bk.Item.def{_}, _}:
          Unit{}
        case Con{Bk.Item.defs{_}, _}:
          Unit{}
    case Con{Bk.Item.names{_}, _}:
      Unit{}
    case Con{Bk.Item.bool{_}, _}:
      Unit{}
    case Con{Bk.Item.term{_}, _}:
      Unit{}
    case Con{Bk.Item.def{_}, _}:
      Unit{}
    case Con{Bk.Item.defs{_}, _}:
      Unit{}

def Gx.defs(s0: List<&2, Bk.Item>) -> Gx.R(Bk.Book.read.defs(s0), N.Gs(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{Bk.Item.quan{_}, _}:
      Unit{}
    case Con{Bk.Item.nat{_}, _}:
      Unit{}
    case Con{Bk.Item.name{_}, _}:
      Unit{}
    case Con{Bk.Item.names{_}, _}:
      Unit{}
    case Con{Bk.Item.bool{_}, _}:
      Unit{}
    case Con{Bk.Item.term{_}, _}:
      Unit{}
    case Con{Bk.Item.def{+x1}, +s1}:
      match s1:
        case Nil{}:
          Unit{}
        case Con{Bk.Item.quan{_}, _}:
          Unit{}
        case Con{Bk.Item.nat{_}, _}:
          Unit{}
        case Con{Bk.Item.name{_}, _}:
          Unit{}
        case Con{Bk.Item.names{_}, _}:
          Unit{}
        case Con{Bk.Item.bool{_}, _}:
          Unit{}
        case Con{Bk.Item.term{_}, _}:
          Unit{}
        case Con{Bk.Item.def{_}, _}:
          Unit{}
        case Con{Bk.Item.defs{+x2}, +rest}:
          N.le_refl(N.Gs(Con{Bk.Item.defs{Con{x1, x2}}, rest}, 0n))
    case Con{Bk.Item.defs{_}, _}:
      Unit{}

def Gx.def(s0: List<&2, Bk.Item>) -> Gx.R(Bk.Book.read.def(s0), N.Gs(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{Bk.Item.quan{_}, _}:
      Unit{}
    case Con{Bk.Item.nat{_}, _}:
      Unit{}
    case Con{Bk.Item.name{_}, _}:
      Unit{}
    case Con{Bk.Item.names{_}, _}:
      Unit{}
    case Con{Bk.Item.bool{+x1}, +s1}:
      match s1:
        case Nil{}:
          Unit{}
        case Con{Bk.Item.quan{_}, _}:
          Unit{}
        case Con{Bk.Item.nat{_}, _}:
          Unit{}
        case Con{Bk.Item.name{_}, _}:
          Unit{}
        case Con{Bk.Item.names{_}, _}:
          Unit{}
        case Con{Bk.Item.bool{_}, _}:
          Unit{}
        case Con{Bk.Item.term{+x2}, +s2}:
          match s2:
            case Nil{}:
              Unit{}
            case Con{Bk.Item.quan{_}, _}:
              Unit{}
            case Con{Bk.Item.nat{_}, _}:
              Unit{}
            case Con{Bk.Item.name{_}, _}:
              Unit{}
            case Con{Bk.Item.names{_}, _}:
              Unit{}
            case Con{Bk.Item.bool{_}, _}:
              Unit{}
            case Con{Bk.Item.term{+x3}, +s3}:
              match s3:
                case Nil{}:
                  Unit{}
                case Con{Bk.Item.quan{_}, _}:
                  Unit{}
                case Con{Bk.Item.nat{_}, _}:
                  Unit{}
                case Con{Bk.Item.name{+x4}, +rest}:
                  N.le_refl(N.Gs(Con{Bk.Item.def{Bk.Def{x4, x3, x2, x1}}, rest}, 0n))
                case Con{Bk.Item.names{_}, _}:
                  Unit{}
                case Con{Bk.Item.bool{_}, _}:
                  Unit{}
                case Con{Bk.Item.term{_}, _}:
                  Unit{}
                case Con{Bk.Item.def{_}, _}:
                  Unit{}
                case Con{Bk.Item.defs{_}, _}:
                  Unit{}
            case Con{Bk.Item.def{_}, _}:
              Unit{}
            case Con{Bk.Item.defs{_}, _}:
              Unit{}
        case Con{Bk.Item.def{_}, _}:
          Unit{}
        case Con{Bk.Item.defs{_}, _}:
          Unit{}
    case Con{Bk.Item.term{_}, _}:
      Unit{}
    case Con{Bk.Item.def{_}, _}:
      Unit{}
    case Con{Bk.Item.defs{_}, _}:
      Unit{}

def Gx.var(s0: List<&2, Bk.Item>) -> Gx.R(Bk.Book.read.var(s0), N.Gs(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{Bk.Item.quan{_}, _}:
      Unit{}
    case Con{Bk.Item.nat{+x1}, +rest}:
      N.le_refl(N.Gs(Con{Bk.Item.term{Bk.Term.Var{x1}}, rest}, 0n))
    case Con{Bk.Item.name{_}, _}:
      Unit{}
    case Con{Bk.Item.names{_}, _}:
      Unit{}
    case Con{Bk.Item.bool{_}, _}:
      Unit{}
    case Con{Bk.Item.term{_}, _}:
      Unit{}
    case Con{Bk.Item.def{_}, _}:
      Unit{}
    case Con{Bk.Item.defs{_}, _}:
      Unit{}

def Gx.ref(s0: List<&2, Bk.Item>) -> Gx.R(Bk.Book.read.ref(s0), N.Gs(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{Bk.Item.quan{_}, _}:
      Unit{}
    case Con{Bk.Item.nat{_}, _}:
      Unit{}
    case Con{Bk.Item.name{+x1}, +rest}:
      N.le_refl(N.Gs(Con{Bk.Item.term{Bk.Term.Ref{x1}}, rest}, 0n))
    case Con{Bk.Item.names{_}, _}:
      Unit{}
    case Con{Bk.Item.bool{_}, _}:
      Unit{}
    case Con{Bk.Item.term{_}, _}:
      Unit{}
    case Con{Bk.Item.def{_}, _}:
      Unit{}
    case Con{Bk.Item.defs{_}, _}:
      Unit{}

def Gx.ann(s0: List<&2, Bk.Item>) -> Gx.R(Bk.Book.read.ann(s0), N.Gs(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{Bk.Item.quan{_}, _}:
      Unit{}
    case Con{Bk.Item.nat{_}, _}:
      Unit{}
    case Con{Bk.Item.name{_}, _}:
      Unit{}
    case Con{Bk.Item.names{_}, _}:
      Unit{}
    case Con{Bk.Item.bool{_}, _}:
      Unit{}
    case Con{Bk.Item.term{+x1}, +s1}:
      match s1:
        case Nil{}:
          Unit{}
        case Con{Bk.Item.quan{_}, _}:
          Unit{}
        case Con{Bk.Item.nat{_}, _}:
          Unit{}
        case Con{Bk.Item.name{_}, _}:
          Unit{}
        case Con{Bk.Item.names{_}, _}:
          Unit{}
        case Con{Bk.Item.bool{_}, _}:
          Unit{}
        case Con{Bk.Item.term{+x2}, +rest}:
          N.le_refl(N.Gs(Con{Bk.Item.term{Bk.Term.Ann{x2, x1}}, rest}, 0n))
        case Con{Bk.Item.def{_}, _}:
          Unit{}
        case Con{Bk.Item.defs{_}, _}:
          Unit{}
    case Con{Bk.Item.def{_}, _}:
      Unit{}
    case Con{Bk.Item.defs{_}, _}:
      Unit{}

def Gx.let(s0: List<&2, Bk.Item>) -> Gx.R(Bk.Book.read.let(s0), N.Gs(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{Bk.Item.quan{_}, _}:
      Unit{}
    case Con{Bk.Item.nat{_}, _}:
      Unit{}
    case Con{Bk.Item.name{_}, _}:
      Unit{}
    case Con{Bk.Item.names{_}, _}:
      Unit{}
    case Con{Bk.Item.bool{_}, _}:
      Unit{}
    case Con{Bk.Item.term{+x1}, +s1}:
      match s1:
        case Nil{}:
          Unit{}
        case Con{Bk.Item.quan{_}, _}:
          Unit{}
        case Con{Bk.Item.nat{_}, _}:
          Unit{}
        case Con{Bk.Item.name{_}, _}:
          Unit{}
        case Con{Bk.Item.names{_}, _}:
          Unit{}
        case Con{Bk.Item.bool{_}, _}:
          Unit{}
        case Con{Bk.Item.term{+x2}, +s2}:
          match s2:
            case Nil{}:
              Unit{}
            case Con{Bk.Item.quan{+x3}, +rest}:
              N.le_refl(N.Gs(Con{Bk.Item.term{Bk.Term.Let{x3, x2, x1}}, rest}, 0n))
            case Con{Bk.Item.nat{_}, _}:
              Unit{}
            case Con{Bk.Item.name{_}, _}:
              Unit{}
            case Con{Bk.Item.names{_}, _}:
              Unit{}
            case Con{Bk.Item.bool{_}, _}:
              Unit{}
            case Con{Bk.Item.term{_}, _}:
              Unit{}
            case Con{Bk.Item.def{_}, _}:
              Unit{}
            case Con{Bk.Item.defs{_}, _}:
              Unit{}
        case Con{Bk.Item.def{_}, _}:
          Unit{}
        case Con{Bk.Item.defs{_}, _}:
          Unit{}
    case Con{Bk.Item.def{_}, _}:
      Unit{}
    case Con{Bk.Item.defs{_}, _}:
      Unit{}

def Gx.typ(s0: List<&2, Bk.Item>) -> Gx.R(Bk.Book.read.typ(s0), N.Gs(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{Bk.Item.quan{_}, _}:
      Unit{}
    case Con{Bk.Item.nat{_}, _}:
      Unit{}
    case Con{Bk.Item.name{_}, _}:
      Unit{}
    case Con{Bk.Item.names{_}, _}:
      Unit{}
    case Con{Bk.Item.bool{_}, _}:
      Unit{}
    case Con{Bk.Item.term{+x1}, +rest}:
      N.le_refl(N.Gs(Con{Bk.Item.term{Bk.Term.Typ{x1}}, rest}, 0n))
    case Con{Bk.Item.def{_}, _}:
      Unit{}
    case Con{Bk.Item.defs{_}, _}:
      Unit{}

def Gx.min(s0: List<&2, Bk.Item>) -> Gx.R(Bk.Book.read.min(s0), N.Gs(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{Bk.Item.quan{_}, _}:
      Unit{}
    case Con{Bk.Item.nat{_}, _}:
      Unit{}
    case Con{Bk.Item.name{_}, _}:
      Unit{}
    case Con{Bk.Item.names{_}, _}:
      Unit{}
    case Con{Bk.Item.bool{_}, _}:
      Unit{}
    case Con{Bk.Item.term{+x1}, +s1}:
      match s1:
        case Nil{}:
          Unit{}
        case Con{Bk.Item.quan{_}, _}:
          Unit{}
        case Con{Bk.Item.nat{_}, _}:
          Unit{}
        case Con{Bk.Item.name{_}, _}:
          Unit{}
        case Con{Bk.Item.names{_}, _}:
          Unit{}
        case Con{Bk.Item.bool{_}, _}:
          Unit{}
        case Con{Bk.Item.term{+x2}, +rest}:
          N.le_refl(N.Gs(Con{Bk.Item.term{Bk.Term.Min{x2, x1}}, rest}, 0n))
        case Con{Bk.Item.def{_}, _}:
          Unit{}
        case Con{Bk.Item.defs{_}, _}:
          Unit{}
    case Con{Bk.Item.def{_}, _}:
      Unit{}
    case Con{Bk.Item.defs{_}, _}:
      Unit{}

def Gx.all(s0: List<&2, Bk.Item>) -> Gx.R(Bk.Book.read.all(s0), N.Gs(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{Bk.Item.quan{_}, _}:
      Unit{}
    case Con{Bk.Item.nat{_}, _}:
      Unit{}
    case Con{Bk.Item.name{_}, _}:
      Unit{}
    case Con{Bk.Item.names{_}, _}:
      Unit{}
    case Con{Bk.Item.bool{_}, _}:
      Unit{}
    case Con{Bk.Item.term{+x1}, +s1}:
      match s1:
        case Nil{}:
          Unit{}
        case Con{Bk.Item.quan{_}, _}:
          Unit{}
        case Con{Bk.Item.nat{_}, _}:
          Unit{}
        case Con{Bk.Item.name{_}, _}:
          Unit{}
        case Con{Bk.Item.names{_}, _}:
          Unit{}
        case Con{Bk.Item.bool{_}, _}:
          Unit{}
        case Con{Bk.Item.term{+x2}, +s2}:
          match s2:
            case Nil{}:
              Unit{}
            case Con{Bk.Item.quan{+x3}, +rest}:
              N.le_refl(N.Gs(Con{Bk.Item.term{Bk.Term.All{x3, x2, x1}}, rest}, 0n))
            case Con{Bk.Item.nat{_}, _}:
              Unit{}
            case Con{Bk.Item.name{_}, _}:
              Unit{}
            case Con{Bk.Item.names{_}, _}:
              Unit{}
            case Con{Bk.Item.bool{_}, _}:
              Unit{}
            case Con{Bk.Item.term{_}, _}:
              Unit{}
            case Con{Bk.Item.def{_}, _}:
              Unit{}
            case Con{Bk.Item.defs{_}, _}:
              Unit{}
        case Con{Bk.Item.def{_}, _}:
          Unit{}
        case Con{Bk.Item.defs{_}, _}:
          Unit{}
    case Con{Bk.Item.def{_}, _}:
      Unit{}
    case Con{Bk.Item.defs{_}, _}:
      Unit{}

def Gx.lam(s0: List<&2, Bk.Item>) -> Gx.R(Bk.Book.read.lam(s0), N.Gs(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{Bk.Item.quan{_}, _}:
      Unit{}
    case Con{Bk.Item.nat{_}, _}:
      Unit{}
    case Con{Bk.Item.name{_}, _}:
      Unit{}
    case Con{Bk.Item.names{_}, _}:
      Unit{}
    case Con{Bk.Item.bool{_}, _}:
      Unit{}
    case Con{Bk.Item.term{+x1}, +s1}:
      match s1:
        case Nil{}:
          Unit{}
        case Con{Bk.Item.quan{+x2}, +rest}:
          N.le_refl(N.Gs(Con{Bk.Item.term{Bk.Term.Lam{x2, x1}}, rest}, 0n))
        case Con{Bk.Item.nat{_}, _}:
          Unit{}
        case Con{Bk.Item.name{_}, _}:
          Unit{}
        case Con{Bk.Item.names{_}, _}:
          Unit{}
        case Con{Bk.Item.bool{_}, _}:
          Unit{}
        case Con{Bk.Item.term{_}, _}:
          Unit{}
        case Con{Bk.Item.def{_}, _}:
          Unit{}
        case Con{Bk.Item.defs{_}, _}:
          Unit{}
    case Con{Bk.Item.def{_}, _}:
      Unit{}
    case Con{Bk.Item.defs{_}, _}:
      Unit{}

def Gx.app(s0: List<&2, Bk.Item>) -> Gx.R(Bk.Book.read.app(s0), N.Gs(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{Bk.Item.quan{_}, _}:
      Unit{}
    case Con{Bk.Item.nat{_}, _}:
      Unit{}
    case Con{Bk.Item.name{_}, _}:
      Unit{}
    case Con{Bk.Item.names{_}, _}:
      Unit{}
    case Con{Bk.Item.bool{_}, _}:
      Unit{}
    case Con{Bk.Item.term{+x1}, +s1}:
      match s1:
        case Nil{}:
          Unit{}
        case Con{Bk.Item.quan{_}, _}:
          Unit{}
        case Con{Bk.Item.nat{_}, _}:
          Unit{}
        case Con{Bk.Item.name{_}, _}:
          Unit{}
        case Con{Bk.Item.names{_}, _}:
          Unit{}
        case Con{Bk.Item.bool{_}, _}:
          Unit{}
        case Con{Bk.Item.term{+x2}, +s2}:
          match s2:
            case Nil{}:
              Unit{}
            case Con{Bk.Item.quan{+x3}, +rest}:
              N.le_refl(N.Gs(Con{Bk.Item.term{Bk.Term.App{x3, x2, x1}}, rest}, 0n))
            case Con{Bk.Item.nat{_}, _}:
              Unit{}
            case Con{Bk.Item.name{_}, _}:
              Unit{}
            case Con{Bk.Item.names{_}, _}:
              Unit{}
            case Con{Bk.Item.bool{_}, _}:
              Unit{}
            case Con{Bk.Item.term{_}, _}:
              Unit{}
            case Con{Bk.Item.def{_}, _}:
              Unit{}
            case Con{Bk.Item.defs{_}, _}:
              Unit{}
        case Con{Bk.Item.def{_}, _}:
          Unit{}
        case Con{Bk.Item.defs{_}, _}:
          Unit{}
    case Con{Bk.Item.def{_}, _}:
      Unit{}
    case Con{Bk.Item.defs{_}, _}:
      Unit{}

def Gx.sig(s0: List<&2, Bk.Item>) -> Gx.R(Bk.Book.read.sig(s0), N.Gs(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{Bk.Item.quan{_}, _}:
      Unit{}
    case Con{Bk.Item.nat{_}, _}:
      Unit{}
    case Con{Bk.Item.name{_}, _}:
      Unit{}
    case Con{Bk.Item.names{_}, _}:
      Unit{}
    case Con{Bk.Item.bool{_}, _}:
      Unit{}
    case Con{Bk.Item.term{+x1}, +s1}:
      match s1:
        case Nil{}:
          Unit{}
        case Con{Bk.Item.quan{_}, _}:
          Unit{}
        case Con{Bk.Item.nat{_}, _}:
          Unit{}
        case Con{Bk.Item.name{_}, _}:
          Unit{}
        case Con{Bk.Item.names{_}, _}:
          Unit{}
        case Con{Bk.Item.bool{_}, _}:
          Unit{}
        case Con{Bk.Item.term{+x2}, +s2}:
          match s2:
            case Nil{}:
              Unit{}
            case Con{Bk.Item.quan{+x3}, +rest}:
              N.le_refl(N.Gs(Con{Bk.Item.term{Bk.Term.Sig{x3, x2, x1}}, rest}, 0n))
            case Con{Bk.Item.nat{_}, _}:
              Unit{}
            case Con{Bk.Item.name{_}, _}:
              Unit{}
            case Con{Bk.Item.names{_}, _}:
              Unit{}
            case Con{Bk.Item.bool{_}, _}:
              Unit{}
            case Con{Bk.Item.term{_}, _}:
              Unit{}
            case Con{Bk.Item.def{_}, _}:
              Unit{}
            case Con{Bk.Item.defs{_}, _}:
              Unit{}
        case Con{Bk.Item.def{_}, _}:
          Unit{}
        case Con{Bk.Item.defs{_}, _}:
          Unit{}
    case Con{Bk.Item.def{_}, _}:
      Unit{}
    case Con{Bk.Item.defs{_}, _}:
      Unit{}

def Gx.tup(s0: List<&2, Bk.Item>) -> Gx.R(Bk.Book.read.tup(s0), N.Gs(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{Bk.Item.quan{_}, _}:
      Unit{}
    case Con{Bk.Item.nat{_}, _}:
      Unit{}
    case Con{Bk.Item.name{_}, _}:
      Unit{}
    case Con{Bk.Item.names{_}, _}:
      Unit{}
    case Con{Bk.Item.bool{_}, _}:
      Unit{}
    case Con{Bk.Item.term{+x1}, +s1}:
      match s1:
        case Nil{}:
          Unit{}
        case Con{Bk.Item.quan{_}, _}:
          Unit{}
        case Con{Bk.Item.nat{_}, _}:
          Unit{}
        case Con{Bk.Item.name{_}, _}:
          Unit{}
        case Con{Bk.Item.names{_}, _}:
          Unit{}
        case Con{Bk.Item.bool{_}, _}:
          Unit{}
        case Con{Bk.Item.term{+x2}, +s2}:
          match s2:
            case Nil{}:
              Unit{}
            case Con{Bk.Item.quan{+x3}, +rest}:
              N.le_refl(N.Gs(Con{Bk.Item.term{Bk.Term.Tup{x3, x2, x1}}, rest}, 0n))
            case Con{Bk.Item.nat{_}, _}:
              Unit{}
            case Con{Bk.Item.name{_}, _}:
              Unit{}
            case Con{Bk.Item.names{_}, _}:
              Unit{}
            case Con{Bk.Item.bool{_}, _}:
              Unit{}
            case Con{Bk.Item.term{_}, _}:
              Unit{}
            case Con{Bk.Item.def{_}, _}:
              Unit{}
            case Con{Bk.Item.defs{_}, _}:
              Unit{}
        case Con{Bk.Item.def{_}, _}:
          Unit{}
        case Con{Bk.Item.defs{_}, _}:
          Unit{}
    case Con{Bk.Item.def{_}, _}:
      Unit{}
    case Con{Bk.Item.defs{_}, _}:
      Unit{}

def Gx.prj(s0: List<&2, Bk.Item>) -> Gx.R(Bk.Book.read.prj(s0), N.Gs(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{Bk.Item.quan{_}, _}:
      Unit{}
    case Con{Bk.Item.nat{_}, _}:
      Unit{}
    case Con{Bk.Item.name{_}, _}:
      Unit{}
    case Con{Bk.Item.names{_}, _}:
      Unit{}
    case Con{Bk.Item.bool{_}, _}:
      Unit{}
    case Con{Bk.Item.term{+x1}, +rest}:
      N.le_refl(N.Gs(Con{Bk.Item.term{Bk.Term.Prj{x1}}, rest}, 0n))
    case Con{Bk.Item.def{_}, _}:
      Unit{}
    case Con{Bk.Item.defs{_}, _}:
      Unit{}

def Gx.enu(s0: List<&2, Bk.Item>) -> Gx.R(Bk.Book.read.enu(s0), N.Gs(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{Bk.Item.quan{_}, _}:
      Unit{}
    case Con{Bk.Item.nat{_}, _}:
      Unit{}
    case Con{Bk.Item.name{_}, _}:
      Unit{}
    case Con{Bk.Item.names{+x1}, +rest}:
      N.le_refl(N.Gs(Con{Bk.Item.term{Bk.Term.Enu{x1}}, rest}, 0n))
    case Con{Bk.Item.bool{_}, _}:
      Unit{}
    case Con{Bk.Item.term{_}, _}:
      Unit{}
    case Con{Bk.Item.def{_}, _}:
      Unit{}
    case Con{Bk.Item.defs{_}, _}:
      Unit{}

def Gx.lab(s0: List<&2, Bk.Item>) -> Gx.R(Bk.Book.read.lab(s0), N.Gs(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{Bk.Item.quan{_}, _}:
      Unit{}
    case Con{Bk.Item.nat{_}, _}:
      Unit{}
    case Con{Bk.Item.name{+x1}, +rest}:
      N.le_refl(N.Gs(Con{Bk.Item.term{Bk.Term.Lab{x1}}, rest}, 0n))
    case Con{Bk.Item.names{_}, _}:
      Unit{}
    case Con{Bk.Item.bool{_}, _}:
      Unit{}
    case Con{Bk.Item.term{_}, _}:
      Unit{}
    case Con{Bk.Item.def{_}, _}:
      Unit{}
    case Con{Bk.Item.defs{_}, _}:
      Unit{}

def Gx.mat(s0: List<&2, Bk.Item>) -> Gx.R(Bk.Book.read.mat(s0), N.Gs(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{Bk.Item.quan{_}, _}:
      Unit{}
    case Con{Bk.Item.nat{_}, _}:
      Unit{}
    case Con{Bk.Item.name{_}, _}:
      Unit{}
    case Con{Bk.Item.names{_}, _}:
      Unit{}
    case Con{Bk.Item.bool{_}, _}:
      Unit{}
    case Con{Bk.Item.term{+x1}, +s1}:
      match s1:
        case Nil{}:
          Unit{}
        case Con{Bk.Item.quan{_}, _}:
          Unit{}
        case Con{Bk.Item.nat{_}, _}:
          Unit{}
        case Con{Bk.Item.name{_}, _}:
          Unit{}
        case Con{Bk.Item.names{_}, _}:
          Unit{}
        case Con{Bk.Item.bool{_}, _}:
          Unit{}
        case Con{Bk.Item.term{+x2}, +s2}:
          match s2:
            case Nil{}:
              Unit{}
            case Con{Bk.Item.quan{_}, _}:
              Unit{}
            case Con{Bk.Item.nat{_}, _}:
              Unit{}
            case Con{Bk.Item.name{+x3}, +rest}:
              N.le_refl(N.Gs(Con{Bk.Item.term{Bk.Term.Mat{x3, x2, x1}}, rest}, 0n))
            case Con{Bk.Item.names{_}, _}:
              Unit{}
            case Con{Bk.Item.bool{_}, _}:
              Unit{}
            case Con{Bk.Item.term{_}, _}:
              Unit{}
            case Con{Bk.Item.def{_}, _}:
              Unit{}
            case Con{Bk.Item.defs{_}, _}:
              Unit{}
        case Con{Bk.Item.def{_}, _}:
          Unit{}
        case Con{Bk.Item.defs{_}, _}:
          Unit{}
    case Con{Bk.Item.def{_}, _}:
      Unit{}
    case Con{Bk.Item.defs{_}, _}:
      Unit{}

def Gx.eql(s0: List<&2, Bk.Item>) -> Gx.R(Bk.Book.read.eql(s0), N.Gs(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{Bk.Item.quan{_}, _}:
      Unit{}
    case Con{Bk.Item.nat{_}, _}:
      Unit{}
    case Con{Bk.Item.name{_}, _}:
      Unit{}
    case Con{Bk.Item.names{_}, _}:
      Unit{}
    case Con{Bk.Item.bool{_}, _}:
      Unit{}
    case Con{Bk.Item.term{+x1}, +s1}:
      match s1:
        case Nil{}:
          Unit{}
        case Con{Bk.Item.quan{_}, _}:
          Unit{}
        case Con{Bk.Item.nat{_}, _}:
          Unit{}
        case Con{Bk.Item.name{_}, _}:
          Unit{}
        case Con{Bk.Item.names{_}, _}:
          Unit{}
        case Con{Bk.Item.bool{_}, _}:
          Unit{}
        case Con{Bk.Item.term{+x2}, +s2}:
          match s2:
            case Nil{}:
              Unit{}
            case Con{Bk.Item.quan{_}, _}:
              Unit{}
            case Con{Bk.Item.nat{_}, _}:
              Unit{}
            case Con{Bk.Item.name{_}, _}:
              Unit{}
            case Con{Bk.Item.names{_}, _}:
              Unit{}
            case Con{Bk.Item.bool{_}, _}:
              Unit{}
            case Con{Bk.Item.term{+x3}, +rest}:
              N.le_refl(N.Gs(Con{Bk.Item.term{Bk.Term.Eql{x3, x2, x1}}, rest}, 0n))
            case Con{Bk.Item.def{_}, _}:
              Unit{}
            case Con{Bk.Item.defs{_}, _}:
              Unit{}
        case Con{Bk.Item.def{_}, _}:
          Unit{}
        case Con{Bk.Item.defs{_}, _}:
          Unit{}
    case Con{Bk.Item.def{_}, _}:
      Unit{}
    case Con{Bk.Item.defs{_}, _}:
      Unit{}

def Gx.rwt(s0: List<&2, Bk.Item>) -> Gx.R(Bk.Book.read.rwt(s0), N.Gs(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{Bk.Item.quan{_}, _}:
      Unit{}
    case Con{Bk.Item.nat{_}, _}:
      Unit{}
    case Con{Bk.Item.name{_}, _}:
      Unit{}
    case Con{Bk.Item.names{_}, _}:
      Unit{}
    case Con{Bk.Item.bool{_}, _}:
      Unit{}
    case Con{Bk.Item.term{+x1}, +s1}:
      match s1:
        case Nil{}:
          Unit{}
        case Con{Bk.Item.quan{_}, _}:
          Unit{}
        case Con{Bk.Item.nat{_}, _}:
          Unit{}
        case Con{Bk.Item.name{_}, _}:
          Unit{}
        case Con{Bk.Item.names{_}, _}:
          Unit{}
        case Con{Bk.Item.bool{_}, _}:
          Unit{}
        case Con{Bk.Item.term{+x2}, +s2}:
          match s2:
            case Nil{}:
              Unit{}
            case Con{Bk.Item.quan{_}, _}:
              Unit{}
            case Con{Bk.Item.nat{_}, _}:
              Unit{}
            case Con{Bk.Item.name{_}, _}:
              Unit{}
            case Con{Bk.Item.names{_}, _}:
              Unit{}
            case Con{Bk.Item.bool{_}, _}:
              Unit{}
            case Con{Bk.Item.term{+x3}, +rest}:
              N.le_refl(N.Gs(Con{Bk.Item.term{Bk.Term.Rwt{x3, x2, x1}}, rest}, 0n))
            case Con{Bk.Item.def{_}, _}:
              Unit{}
            case Con{Bk.Item.defs{_}, _}:
              Unit{}
        case Con{Bk.Item.def{_}, _}:
          Unit{}
        case Con{Bk.Item.defs{_}, _}:
          Unit{}
    case Con{Bk.Item.def{_}, _}:
      Unit{}
    case Con{Bk.Item.defs{_}, _}:
      Unit{}

def Gx.token32(n: Nat, +st: List<&2, Bk.Item>) -> Gx.R(Bk.Book.read.token32(n, st), N.Gs(st, 0n)):
  match n:
    case 0n:
      Gx.rwt(st)
    case 1n+_:
      Unit{}

def Gx.token24(n: Nat, +st: List<&2, Bk.Item>) -> Gx.R(Bk.Book.read.token24(n, st), N.Gs(st, 0n)):
  match n:
    case 0n:
      Gx.tup(st)
    case 1n:
      Gx.prj(st)
    case 2n:
      Gx.enu(st)
    case 3n:
      Gx.lab(st)
    case 4n:
      Gx.mat(st)
    case 5n:
      N.le_refl(2n+N.Gs(st, 0n))
    case 6n:
      Gx.eql(st)
    case 7n:
      N.le_refl(2n+N.Gs(st, 0n))
    case 8n+p:
      Gx.token32(p, st)

def Gx.token16(n: Nat, +st: List<&2, Bk.Item>) -> Gx.R(Bk.Book.read.token16(n, st), N.Gs(st, 0n)):
  match n:
    case 0n:
      Gx.ann(st)
    case 1n:
      Gx.let(st)
    case 2n:
      Gx.typ(st)
    case 3n:
      Gx.min(st)
    case 4n:
      Gx.all(st)
    case 5n:
      Gx.lam(st)
    case 6n:
      Gx.app(st)
    case 7n:
      Gx.sig(st)
    case 8n+p:
      Gx.token24(p, st)

def Gx.token8(n: Nat, +st: List<&2, Bk.Item>) -> Gx.R(Bk.Book.read.token8(n, st), N.Gs(st, 0n)):
  match n:
    case 0n:
      Gx.names(st)
    case 1n:
      N.le_refl(2n+N.Gs(st, 0n))
    case 2n:
      N.le_refl(2n+N.Gs(st, 0n))
    case 3n:
      N.le_refl(2n+N.Gs(st, 0n))
    case 4n:
      Gx.defs(st)
    case 5n:
      Gx.def(st)
    case 6n:
      Gx.var(st)
    case 7n:
      Gx.ref(st)
    case 8n+p:
      Gx.token16(p, st)

def Gx.token(n: Nat, +st: List<&2, Bk.Item>, b: Word(8n)) -> Gx.R(Bk.Book.read.token(n, st, b), N.Gs(st, 0n)):
  match n:
    case 0n:
      N.le_refl(2n+N.Gs(st, 0n))
    case 1n:
      N.le_refl(2n+N.Gs(st, 0n))
    case 2n:
      N.le_refl(2n+N.Gs(st, 0n))
    case 3n:
      N.le_refl(2n+N.Gs(st, 0n))
    case 4n:
      Gx.succ(st)
    case 5n:
      N.le_refl(2n+N.Gs(st, 0n))
    case 6n:
      Gx.byte(st, b)
    case 7n:
      N.le_refl(2n+N.Gs(st, 0n))
    case 8n+p:
      Gx.token8(p, st)


# Reading a book
# --------------

# G of a reader's result: its book's
def Gx.Vd(m: Maybe<List<&2, Bk.Def>>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{ds}:
      N.Gd(ds, 0n)

# the end of the reading: the book's G is at most the stack's
def Gx.done(st: Maybe<List<&2, Bk.Item>>, +ds: List<&2, Bk.Def>,
  e: {Bk.Book.read.done(st) == Some{ds} : Maybe<List<&2, Bk.Def>>}
) -> N.Le(Gx.Vd(Some{ds}), Nat.add(0n, N.Gm(st))):
  match st:
    case None{}:
      Empty.absurd(N.Le(Gx.Vd(Some{ds}), Nat.add(0n, N.Gm(st))), N.none_ne_some(ds, e))
    case Some{s}:
      match s:
        case Nil{}:
          Empty.absurd(N.Le(Gx.Vd(Some{ds}), Nat.add(0n, N.Gm(st))), N.none_ne_some(ds, e))
        case Con{Bk.Item.quan{_}, _}:
          Empty.absurd(N.Le(Gx.Vd(Some{ds}), Nat.add(0n, N.Gm(st))), N.none_ne_some(ds, e))
        case Con{Bk.Item.nat{_}, _}:
          Empty.absurd(N.Le(Gx.Vd(Some{ds}), Nat.add(0n, N.Gm(st))), N.none_ne_some(ds, e))
        case Con{Bk.Item.name{_}, _}:
          Empty.absurd(N.Le(Gx.Vd(Some{ds}), Nat.add(0n, N.Gm(st))), N.none_ne_some(ds, e))
        case Con{Bk.Item.names{_}, _}:
          Empty.absurd(N.Le(Gx.Vd(Some{ds}), Nat.add(0n, N.Gm(st))), N.none_ne_some(ds, e))
        case Con{Bk.Item.bool{_}, _}:
          Empty.absurd(N.Le(Gx.Vd(Some{ds}), Nat.add(0n, N.Gm(st))), N.none_ne_some(ds, e))
        case Con{Bk.Item.term{_}, _}:
          Empty.absurd(N.Le(Gx.Vd(Some{ds}), Nat.add(0n, N.Gm(st))), N.none_ne_some(ds, e))
        case Con{Bk.Item.def{_}, _}:
          Empty.absurd(N.Le(Gx.Vd(Some{ds}), Nat.add(0n, N.Gm(st))), N.none_ne_some(ds, e))
        case Con{Bk.Item.defs{+ds0}, t}:
          match t:
            case Nil{}:
              %e : N.Le(Gx.Vd(_), Nat.add(0n, N.Gm(st)))
              N.le_refl(N.Gd(ds0, 0n))
            case Con{_, _}:
              Empty.absurd(N.Le(Gx.Vd(Some{ds}), Nat.add(0n, N.Gm(st))), N.none_ne_some(ds, e))

# one token of the reading: 2 bytes, and at most 2 more G
def Gx.next(r: Maybe<List<&2, Bk.Item>>, +rest: List<&2, Word(8n)>, +w: Nat, +ds: List<&2, Bk.Def>,
  g: Gx.R(r, w),
  ih: N.Le(N.Gd(ds, 0n), Nat.add(List.length(&2, Word(8n), rest), N.Gm(r))),
  e: {Bk.Book.read.go(rest, r) == Some{ds} : Maybe<List<&2, Bk.Def>>}
) -> N.Le(N.Gd(ds, 0n), 2n+Nat.add(List.length(&2, Word(8n), rest), w)):
  match r:
    case None{}:
      Empty.absurd(N.Le(N.Gd(ds, 0n), 2n+Nat.add(List.length(&2, Word(8n), rest), w)), N.go.none(rest, ds, e))
    case Some{+s}:
      +l = List.length(&2, Word(8n), rest)
      +h = N.le_trans(N.Gd(ds, 0n), Nat.add(l, N.Gs(s, 0n)), Nat.add(l, 2n+w), ih,
        N.add_mono(l, l, N.Gs(s, 0n), 2n+w, N.le_refl(l), g))
      N.le_rw_r(N.Gd(ds, 0n), Nat.add(l, 2n+w), 2n+Nat.add(l, w),
        Equal.sym(Nat, 2n+Nat.add(l, w), Nat.add(l, 2n+w), N.add_two(l, w)), h)

# the reading: the book's G is at most the bytes left plus the stack's G
def Gx.go(xs: List<&2, Word(8n)>, st: Maybe<List<&2, Bk.Item>>, +ds: List<&2, Bk.Def>,
  +e: {Bk.Book.read.go(xs, st) == Some{ds} : Maybe<List<&2, Bk.Def>>}
) -> N.Le(N.Gd(ds, 0n), Nat.add(List.length(&2, Word(8n), xs), N.Gm(st))):
  match xs:
    case Nil{}:
      Gx.done(st, ds, e)
    case Con{_, Nil{}}:
      Empty.absurd(N.Le(N.Gd(ds, 0n), Nat.add(1n, N.Gm(st))), N.none_ne_some(ds, e))
    case Con{+tag, Con{+b, +rest}}:
      match st:
        case None{}:
          Empty.absurd(N.Le(N.Gd(ds, 0n), Nat.add(2n+List.length(&2, Word(8n), rest), N.Gm(st))), N.go.none(rest, ds, e))
        case Some{+s}:
          Gx.next(Bk.Book.read.token(Word.to_nat(8n, tag), s, b), rest, N.Gs(s, 0n), ds, Gx.token(Word.to_nat(8n, tag), s, b),
            Gx.go(rest, Bk.Book.read.token(Word.to_nat(8n, tag), s, b), ds, e), e)

# a book read from p has a G of at most |p|
def Gx.read.le(+p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>,
  rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>}
) -> N.Le(N.Gd(ds, 0n), List.length(&2, Word(8n), p)):
  +l = List.length(&2, Word(8n), p)
  N.le_rw_r(N.Gd(ds, 0n), Nat.add(l, 0n), l, N.add_zero(l), Gx.go(p, Some{Nil{}}, ds, rd))

# G grows with its addend
# -----------------------

def Gx.Gn.mono(+i: Nat, +a: Nat, +b: Nat, h: N.Le(a, b)) -> N.Le(N.Gn(i, a), N.Gn(i, b)):
  match i:
    case 0n:
      h
    case 1n+q:
      Gx.Gn.mono(q, a, b, h)

def Gx.Gk.mono(k: List<&2, Word(8n)>, +a: Nat, +b: Nat, h: N.Le(a, b)) -> N.Le(N.Gk(k, a), N.Gk(k, b)):
  match k:
    case Nil{}:
      h
    case Con{_, +rest}:
      Gx.Gk.mono(rest, a, b, h)

def Gx.Gks.mono(ks: List<&2, List<&2, Word(8n)>>, +a: Nat, +b: Nat, h: N.Le(a, b)) -> N.Le(N.Gks(ks, a), N.Gks(ks, b)):
  match ks:
    case Nil{}:
      h
    case Con{+k, +rest}:
      Gx.Gk.mono(k, N.Gks(rest, a), N.Gks(rest, b), Gx.Gks.mono(rest, a, b, h))

def Gx.Gt.mono(t: Bk.Term, +a: Nat, +b: Nat, h: N.Le(a, b)) -> N.Le(N.Gt(t, a), N.Gt(t, b)):
  match t:
    case Bk.Term.Var{+i}:
      Gx.Gn.mono(i, a, b, h)
    case Bk.Term.Ref{+k}:
      Gx.Gk.mono(k, a, b, h)
    case Bk.Term.Ann{+x, +T}:
      Gx.Gt.mono(T, N.Gt(x, a), N.Gt(x, b), Gx.Gt.mono(x, a, b, h))
    case Bk.Term.Let{_, +v, +f}:
      Gx.Gt.mono(f, N.Gt(v, 2n+a), N.Gt(v, 2n+b), Gx.Gt.mono(v, 2n+a, 2n+b, h))
    case Bk.Term.Typ{+q}:
      Gx.Gt.mono(q, a, b, h)
    case Bk.Term.Min{+x, +y}:
      Gx.Gt.mono(y, N.Gt(x, a), N.Gt(x, b), Gx.Gt.mono(x, a, b, h))
    case Bk.Term.All{_, +A, +B}:
      Gx.Gt.mono(B, N.Gt(A, 2n+a), N.Gt(A, 2n+b), Gx.Gt.mono(A, 2n+a, 2n+b, h))
    case Bk.Term.Lam{_, +f}:
      Gx.Gt.mono(f, 2n+a, 2n+b, h)
    case Bk.Term.App{_, +f, +x}:
      Gx.Gt.mono(x, N.Gt(f, 2n+a), N.Gt(f, 2n+b), Gx.Gt.mono(f, 2n+a, 2n+b, h))
    case Bk.Term.Sig{_, +A, +B}:
      Gx.Gt.mono(B, N.Gt(A, 2n+a), N.Gt(A, 2n+b), Gx.Gt.mono(A, 2n+a, 2n+b, h))
    case Bk.Term.Tup{_, +p, +q}:
      Gx.Gt.mono(q, N.Gt(p, 2n+a), N.Gt(p, 2n+b), Gx.Gt.mono(p, 2n+a, 2n+b, h))
    case Bk.Term.Prj{+h0}:
      Gx.Gt.mono(h0, a, b, h)
    case Bk.Term.Enu{+ks}:
      Gx.Gks.mono(ks, a, b, h)
    case Bk.Term.Lab{+k}:
      Gx.Gk.mono(k, a, b, h)
    case Bk.Term.Mat{+k, +h0, +m}:
      Gx.Gt.mono(m, N.Gt(h0, N.Gk(k, a)), N.Gt(h0, N.Gk(k, b)),
        Gx.Gt.mono(h0, N.Gk(k, a), N.Gk(k, b), Gx.Gk.mono(k, a, b, h)))
    case Bk.Term.Efq{}:
      h
    case Bk.Term.Eql{+x, +y, +T}:
      Gx.Gt.mono(T, N.Gt(y, N.Gt(x, a)), N.Gt(y, N.Gt(x, b)),
        Gx.Gt.mono(y, N.Gt(x, a), N.Gt(x, b), Gx.Gt.mono(x, a, b, h)))
    case Bk.Term.Rfl{}:
      h
    case Bk.Term.Rwt{+e, +P, +f}:
      Gx.Gt.mono(f, N.Gt(P, N.Gt(e, a)), N.Gt(P, N.Gt(e, b)),
        Gx.Gt.mono(P, N.Gt(e, a), N.Gt(e, b), Gx.Gt.mono(e, a, b, h)))

# a term's G is at least its addend
# ---------------------------------

def Gx.Gn.ge(+i: Nat, +a: Nat) -> N.Le(a, N.Gn(i, a)):
  match i:
    case 0n:
      N.le_add_l(2n, a)
    case 1n+q:
      N.le_trans(a, N.Gn(q, a), 2n+N.Gn(q, a), Gx.Gn.ge(q, a), N.le_add_l(2n, N.Gn(q, a)))

def Gx.Gk.ge(k: List<&2, Word(8n)>, +a: Nat) -> N.Le(a, N.Gk(k, a)):
  match k:
    case Nil{}:
      N.le_add_l(2n, a)
    case Con{_, +rest}:
      N.le_trans(a, N.Gk(rest, a), 2n+N.Gk(rest, a), Gx.Gk.ge(rest, a), N.le_add_l(2n, N.Gk(rest, a)))

def Gx.Gks.ge(ks: List<&2, List<&2, Word(8n)>>, +a: Nat) -> N.Le(a, N.Gks(ks, a)):
  match ks:
    case Nil{}:
      N.le_add_l(2n, a)
    case Con{+k, +rest}:
      N.le_trans(a, N.Gks(rest, a), N.Gks(Con{k, rest}, a), Gx.Gks.ge(rest, a),
        N.le_trans(N.Gks(rest, a), N.Gk(k, N.Gks(rest, a)), 2n+N.Gk(k, N.Gks(rest, a)),
          Gx.Gk.ge(k, N.Gks(rest, a)), N.le_add_l(2n, N.Gk(k, N.Gks(rest, a)))))

def Gx.Gt.ge(t: Bk.Term, +a: Nat) -> N.Le(a, N.Gt(t, a)):
  match t:
    case Bk.Term.Var{+i}:
      N.le_trans(a, N.Gn(i, a), 2n+N.Gn(i, a), Gx.Gn.ge(i, a), N.le_add_l(2n, N.Gn(i, a)))
    case Bk.Term.Ref{+k}:
      N.le_trans(a, N.Gk(k, a), 2n+N.Gk(k, a), Gx.Gk.ge(k, a), N.le_add_l(2n, N.Gk(k, a)))
    case Bk.Term.Ann{+x, +T}:
      N.le_trans(a, N.Gt(T, N.Gt(x, a)), 2n+N.Gt(T, N.Gt(x, a)),
        N.le_trans(a, N.Gt(x, a), N.Gt(T, N.Gt(x, a)),
          Gx.Gt.ge(x, a), Gx.Gt.ge(T, N.Gt(x, a))),
        N.le_add_l(2n, N.Gt(T, N.Gt(x, a))))
    case Bk.Term.Let{_, +v, +f}:
      N.le_trans(a, N.Gt(f, N.Gt(v, 2n+a)), 2n+N.Gt(f, N.Gt(v, 2n+a)),
        N.le_trans(a, N.Gt(v, 2n+a), N.Gt(f, N.Gt(v, 2n+a)),
          N.le_trans(a, 2n+a, N.Gt(v, 2n+a), N.le_add_l(2n, a), Gx.Gt.ge(v, 2n+a)),
          Gx.Gt.ge(f, N.Gt(v, 2n+a))),
        N.le_add_l(2n, N.Gt(f, N.Gt(v, 2n+a))))
    case Bk.Term.Typ{+q}:
      N.le_trans(a, N.Gt(q, a), 2n+N.Gt(q, a), Gx.Gt.ge(q, a), N.le_add_l(2n, N.Gt(q, a)))
    case Bk.Term.Min{+x, +y}:
      N.le_trans(a, N.Gt(y, N.Gt(x, a)), 2n+N.Gt(y, N.Gt(x, a)),
        N.le_trans(a, N.Gt(x, a), N.Gt(y, N.Gt(x, a)),
          Gx.Gt.ge(x, a), Gx.Gt.ge(y, N.Gt(x, a))),
        N.le_add_l(2n, N.Gt(y, N.Gt(x, a))))
    case Bk.Term.All{_, +A, +B}:
      N.le_trans(a, N.Gt(B, N.Gt(A, 2n+a)), 2n+N.Gt(B, N.Gt(A, 2n+a)),
        N.le_trans(a, N.Gt(A, 2n+a), N.Gt(B, N.Gt(A, 2n+a)),
          N.le_trans(a, 2n+a, N.Gt(A, 2n+a), N.le_add_l(2n, a), Gx.Gt.ge(A, 2n+a)),
          Gx.Gt.ge(B, N.Gt(A, 2n+a))),
        N.le_add_l(2n, N.Gt(B, N.Gt(A, 2n+a))))
    case Bk.Term.Lam{_, +f}:
      N.le_trans(a, N.Gt(f, 2n+a), 2n+N.Gt(f, 2n+a),
        N.le_trans(a, 2n+a, N.Gt(f, 2n+a), N.le_add_l(2n, a), Gx.Gt.ge(f, 2n+a)),
        N.le_add_l(2n, N.Gt(f, 2n+a)))
    case Bk.Term.App{_, +f, +x}:
      N.le_trans(a, N.Gt(x, N.Gt(f, 2n+a)), 2n+N.Gt(x, N.Gt(f, 2n+a)),
        N.le_trans(a, N.Gt(f, 2n+a), N.Gt(x, N.Gt(f, 2n+a)),
          N.le_trans(a, 2n+a, N.Gt(f, 2n+a), N.le_add_l(2n, a), Gx.Gt.ge(f, 2n+a)),
          Gx.Gt.ge(x, N.Gt(f, 2n+a))),
        N.le_add_l(2n, N.Gt(x, N.Gt(f, 2n+a))))
    case Bk.Term.Sig{_, +A, +B}:
      N.le_trans(a, N.Gt(B, N.Gt(A, 2n+a)), 2n+N.Gt(B, N.Gt(A, 2n+a)),
        N.le_trans(a, N.Gt(A, 2n+a), N.Gt(B, N.Gt(A, 2n+a)),
          N.le_trans(a, 2n+a, N.Gt(A, 2n+a), N.le_add_l(2n, a), Gx.Gt.ge(A, 2n+a)),
          Gx.Gt.ge(B, N.Gt(A, 2n+a))),
        N.le_add_l(2n, N.Gt(B, N.Gt(A, 2n+a))))
    case Bk.Term.Tup{_, +p, +q}:
      N.le_trans(a, N.Gt(q, N.Gt(p, 2n+a)), 2n+N.Gt(q, N.Gt(p, 2n+a)),
        N.le_trans(a, N.Gt(p, 2n+a), N.Gt(q, N.Gt(p, 2n+a)),
          N.le_trans(a, 2n+a, N.Gt(p, 2n+a), N.le_add_l(2n, a), Gx.Gt.ge(p, 2n+a)),
          Gx.Gt.ge(q, N.Gt(p, 2n+a))),
        N.le_add_l(2n, N.Gt(q, N.Gt(p, 2n+a))))
    case Bk.Term.Prj{+h0}:
      N.le_trans(a, N.Gt(h0, a), 2n+N.Gt(h0, a), Gx.Gt.ge(h0, a), N.le_add_l(2n, N.Gt(h0, a)))
    case Bk.Term.Enu{+ks}:
      N.le_trans(a, N.Gks(ks, a), 2n+N.Gks(ks, a), Gx.Gks.ge(ks, a), N.le_add_l(2n, N.Gks(ks, a)))
    case Bk.Term.Lab{+k}:
      N.le_trans(a, N.Gk(k, a), 2n+N.Gk(k, a), Gx.Gk.ge(k, a), N.le_add_l(2n, N.Gk(k, a)))
    case Bk.Term.Mat{+k, +h0, +m}:
      N.le_trans(a, N.Gt(m, N.Gt(h0, N.Gk(k, a))), 2n+N.Gt(m, N.Gt(h0, N.Gk(k, a))),
        N.le_trans(a, N.Gt(h0, N.Gk(k, a)), N.Gt(m, N.Gt(h0, N.Gk(k, a))),
          N.le_trans(a, N.Gk(k, a), N.Gt(h0, N.Gk(k, a)), Gx.Gk.ge(k, a), Gx.Gt.ge(h0, N.Gk(k, a))),
          Gx.Gt.ge(m, N.Gt(h0, N.Gk(k, a)))),
        N.le_add_l(2n, N.Gt(m, N.Gt(h0, N.Gk(k, a)))))
    case Bk.Term.Efq{}:
      N.le_add_l(2n, a)
    case Bk.Term.Eql{+x, +y, +T}:
      N.le_trans(a, N.Gt(T, N.Gt(y, N.Gt(x, a))), 2n+N.Gt(T, N.Gt(y, N.Gt(x, a))),
        N.le_trans(a, N.Gt(y, N.Gt(x, a)), N.Gt(T, N.Gt(y, N.Gt(x, a))),
          N.le_trans(a, N.Gt(x, a), N.Gt(y, N.Gt(x, a)), Gx.Gt.ge(x, a), Gx.Gt.ge(y, N.Gt(x, a))),
          Gx.Gt.ge(T, N.Gt(y, N.Gt(x, a)))),
        N.le_add_l(2n, N.Gt(T, N.Gt(y, N.Gt(x, a)))))
    case Bk.Term.Rfl{}:
      N.le_add_l(2n, a)
    case Bk.Term.Rwt{+e, +P, +f}:
      N.le_trans(a, N.Gt(f, N.Gt(P, N.Gt(e, a))), 2n+N.Gt(f, N.Gt(P, N.Gt(e, a))),
        N.le_trans(a, N.Gt(P, N.Gt(e, a)), N.Gt(f, N.Gt(P, N.Gt(e, a))),
          N.le_trans(a, N.Gt(e, a), N.Gt(P, N.Gt(e, a)), Gx.Gt.ge(e, a), Gx.Gt.ge(P, N.Gt(e, a))),
          Gx.Gt.ge(f, N.Gt(P, N.Gt(e, a)))),
        N.le_add_l(2n, N.Gt(f, N.Gt(P, N.Gt(e, a)))))
# Var indices are below their G
# -----------------------------

def Gx.lt.gn(+i: Nat) -> N.Le(1n+i, 2n+N.Gn(i, 0n)):
  match i:
    case 0n:
      N.toLe(1n, 4n, {==})
    case 1n+q:
      N.le_succ(Nat.add(1n, 1n+q), Nat.add(1n, 2n+N.Gn(q, 0n)),
        N.add_mono(1n, 1n, 1n+q, 2n+N.Gn(q, 0n), N.le_refl(1n), Gx.lt.gn(q)))

# a term's own G, at a bigger addend
def Gx.mono0(t: Bk.Term, +c: Nat) -> N.Le(N.Gt(t, 0n), N.Gt(t, c)):
  Gx.Gt.mono(t, 0n, c, N.le_zero(c))

# a child's G is at most 2 plus its parent's
def Gx.to2(x: Bk.Term, +t1: Bk.Term, +c: Nat, h: N.Le(N.Gt(x, 0n), N.Gt(t1, c))) ->
  N.Le(N.Gt(x, 0n), 2n+N.Gt(t1, c)):
  N.le_trans(N.Gt(x, 0n), N.Gt(t1, c), 2n+N.Gt(t1, c), h, N.le_add_l(2n, N.Gt(t1, c)))

def Gx.hup(+n: Nat) -> N.Le(n, 1n+n):
  N.le_succ(n, n, N.le_refl(n))

def Gx.hup2(+n: Nat) -> N.Le(n, 2n+n):
  N.le_succ(n, 1n+n, Gx.hup(n))

# a bound grows with G: every term is below 2 plus its own G
def Gx.below(t: Bk.Term, +n: Nat, +h: N.Le(N.Gt(t, 0n), n)) -> {PM.Term.below(t, n) == True{} : Bool}:
  match t:
    case Bk.Term.Var{+i}:
      I.lt_nat(i, n, N.le_trans(1n+i, 2n+N.Gn(i, 0n), n, Gx.lt.gn(i), h))
    case Bk.Term.Ref{_}:
      {==}
    case Bk.Term.Ann{+x, +T}:
      +gx = N.Gt(x, 0n)
      +hx = N.le_trans(gx, 2n+N.Gt(T, gx), n, Gx.to2(x, T, gx, Gx.Gt.ge(T, gx)), h)
      +hT = N.le_trans(N.Gt(T, 0n), 2n+N.Gt(T, gx), n, Gx.to2(T, T, gx, Gx.mono0(T, gx)), h)
      Fv.fv.and_i(PM.Term.below(x, n), PM.Term.below(T, n), Gx.below(x, n, hx), Gx.below(T, n, hT))
    case Bk.Term.Let{_, +v, +f}:
      +gv = N.Gt(v, 0n)
      +gv2 = N.Gt(v, 2n)
      +g = N.Gt(f, gv2)
      +gp = {2n+g : Nat}
      +hv = N.le_trans(gv, gp, n,
        Gx.to2(v, f, gv2, N.le_trans(gv, gv2, g, Gx.mono0(v, 2n), Gx.Gt.ge(f, gv2))), h)
      +hf = N.le_trans(N.Gt(f, 0n), gp, 1n+n, Gx.to2(f, f, gv2, Gx.mono0(f, gv2)),
        N.le_trans(gp, n, 1n+n, h, Gx.hup(n)))
      Fv.fv.and_i(PM.Term.below(v, n), PM.Term.below(f, 1n+n), Gx.below(v, n, hv), Gx.below(f, 1n+n, hf))
    case Bk.Term.Typ{+q}:
      Gx.below(q, n, N.le_trans(N.Gt(q, 0n), 2n+N.Gt(q, 0n), n, N.le_add_l(2n, N.Gt(q, 0n)), h))
    case Bk.Term.Min{+a, +b}:
      +ga = N.Gt(a, 0n)
      +ha = N.le_trans(ga, 2n+N.Gt(b, ga), n, Gx.to2(a, b, ga, Gx.Gt.ge(b, ga)), h)
      +hb = N.le_trans(N.Gt(b, 0n), 2n+N.Gt(b, ga), n, Gx.to2(b, b, ga, Gx.mono0(b, ga)), h)
      Fv.fv.and_i(PM.Term.below(a, n), PM.Term.below(b, n), Gx.below(a, n, ha), Gx.below(b, n, hb))
    case Bk.Term.All{_, +A, +B}:
      +gA = N.Gt(A, 0n)
      +gA2 = N.Gt(A, 2n)
      +g = N.Gt(B, gA2)
      +gp = {2n+g : Nat}
      +hA = N.le_trans(gA, gp, n,
        Gx.to2(A, B, gA2, N.le_trans(gA, gA2, g, Gx.mono0(A, 2n), Gx.Gt.ge(B, gA2))), h)
      +hB = N.le_trans(N.Gt(B, 0n), gp, 1n+n, Gx.to2(B, B, gA2, Gx.mono0(B, gA2)),
        N.le_trans(gp, n, 1n+n, h, Gx.hup(n)))
      Fv.fv.and_i(PM.Term.below(A, n), PM.Term.below(B, 1n+n), Gx.below(A, n, hA), Gx.below(B, 1n+n, hB))
    case Bk.Term.Lam{_, +f}:
      +hf = N.le_trans(N.Gt(f, 0n), 2n+N.Gt(f, 2n), 1n+n, Gx.to2(f, f, 2n, Gx.mono0(f, 2n)),
        N.le_trans(2n+N.Gt(f, 2n), n, 1n+n, h, Gx.hup(n)))
      Gx.below(f, 1n+n, hf)
    case Bk.Term.App{_, +f, +x}:
      +gf = N.Gt(f, 2n)
      +gfx = N.Gt(x, gf)
      +hf = N.le_trans(N.Gt(f, 0n), 2n+gfx, n,
        Gx.to2(f, x, gf, N.le_trans(N.Gt(f, 0n), gf, gfx, Gx.mono0(f, 2n), Gx.Gt.ge(x, gf))), h)
      +hx = N.le_trans(N.Gt(x, 0n), 2n+gfx, n, Gx.to2(x, x, gf, Gx.mono0(x, gf)), h)
      Fv.fv.and_i(PM.Term.below(f, n), PM.Term.below(x, n), Gx.below(f, n, hf), Gx.below(x, n, hx))
    case Bk.Term.Sig{_, +A, +B}:
      +gA = N.Gt(A, 0n)
      +gA2 = N.Gt(A, 2n)
      +g = N.Gt(B, gA2)
      +gp = {2n+g : Nat}
      +hA = N.le_trans(gA, gp, n,
        Gx.to2(A, B, gA2, N.le_trans(gA, gA2, g, Gx.mono0(A, 2n), Gx.Gt.ge(B, gA2))), h)
      +hB = N.le_trans(N.Gt(B, 0n), gp, 1n+n, Gx.to2(B, B, gA2, Gx.mono0(B, gA2)),
        N.le_trans(gp, n, 1n+n, h, Gx.hup(n)))
      Fv.fv.and_i(PM.Term.below(A, n), PM.Term.below(B, 1n+n), Gx.below(A, n, hA), Gx.below(B, 1n+n, hB))
    case Bk.Term.Tup{_, +a, +b}:
      +ga = N.Gt(a, 2n)
      +gab = N.Gt(b, ga)
      +ha = N.le_trans(N.Gt(a, 0n), 2n+gab, n,
        Gx.to2(a, b, ga, N.le_trans(N.Gt(a, 0n), ga, gab, Gx.mono0(a, 2n), Gx.Gt.ge(b, ga))), h)
      +hb = N.le_trans(N.Gt(b, 0n), 2n+gab, n, Gx.to2(b, b, ga, Gx.mono0(b, ga)), h)
      Fv.fv.and_i(PM.Term.below(a, n), PM.Term.below(b, n), Gx.below(a, n, ha), Gx.below(b, n, hb))
    case Bk.Term.Prj{+h0}:
      Gx.below(h0, n, N.le_trans(N.Gt(h0, 0n), 2n+N.Gt(h0, 0n), n, N.le_add_l(2n, N.Gt(h0, 0n)), h))
    case Bk.Term.Enu{_}:
      {==}
    case Bk.Term.Lab{_}:
      {==}
    case Bk.Term.Mat{+k, +h0, +m}:
      +gk = N.Gk(k, 0n)
      +gh = N.Gt(h0, gk)
      +gm = N.Gt(m, gh)
      +hh = N.le_trans(N.Gt(h0, 0n), 2n+gm, n,
        Gx.to2(h0, m, gh, N.le_trans(N.Gt(h0, 0n), gh, gm, Gx.mono0(h0, gk), Gx.Gt.ge(m, gh))), h)
      +hm = N.le_trans(N.Gt(m, 0n), 2n+gm, n, Gx.to2(m, m, gh, Gx.mono0(m, gh)), h)
      Fv.fv.and_i(PM.Term.below(h0, n), PM.Term.below(m, n), Gx.below(h0, n, hh), Gx.below(m, n, hm))
    case Bk.Term.Efq{}:
      {==}
    case Bk.Term.Eql{+x, +y, +T}:
      +gx = N.Gt(x, 0n)
      +gyx = N.Gt(y, gx)
      +g = N.Gt(T, gyx)
      +hx = N.le_trans(gx, 2n+g, n,
        Gx.to2(x, T, gyx, N.le_trans(gx, gyx, g, Gx.Gt.ge(y, gx), Gx.Gt.ge(T, gyx))), h)
      +hy = N.le_trans(N.Gt(y, 0n), 2n+g, n,
        Gx.to2(y, T, gyx, N.le_trans(N.Gt(y, 0n), gyx, g, Gx.mono0(y, gx), Gx.Gt.ge(T, gyx))), h)
      +hT = N.le_trans(N.Gt(T, 0n), 2n+g, n, Gx.to2(T, T, gyx, Gx.mono0(T, gyx)), h)
      Fv.fv.and_i(PM.Term.below(x, n), Bool.and(PM.Term.below(y, n), PM.Term.below(T, n)),
        Gx.below(x, n, hx),
        Fv.fv.and_i(PM.Term.below(y, n), PM.Term.below(T, n), Gx.below(y, n, hy), Gx.below(T, n, hT)))
    case Bk.Term.Rfl{}:
      {==}
    case Bk.Term.Rwt{+e, +P, +f}:
      +ge = N.Gt(e, 0n)
      +gpe = N.Gt(P, ge)
      +g = N.Gt(f, gpe)
      +he = N.le_trans(ge, 2n+g, n,
        Gx.to2(e, f, gpe, N.le_trans(ge, gpe, g, Gx.Gt.ge(P, ge), Gx.Gt.ge(f, gpe))), h)
      +hP = N.le_trans(N.Gt(P, 0n), 2n+g, 2n+n,
        Gx.to2(P, f, gpe, N.le_trans(N.Gt(P, 0n), gpe, g, Gx.mono0(P, ge), Gx.Gt.ge(f, gpe))),
        N.le_trans(2n+g, n, 2n+n, h, Gx.hup2(n)))
      +hf = N.le_trans(N.Gt(f, 0n), 2n+g, n, Gx.to2(f, f, gpe, Gx.mono0(f, gpe)), h)
      Fv.fv.and_i(PM.Term.below(e, n), Bool.and(PM.Term.below(P, 2n+n), PM.Term.below(f, n)),
        Gx.below(e, n, he),
        Fv.fv.and_i(PM.Term.below(P, 2n+n), PM.Term.below(f, n), Gx.below(P, 2n+n, hP), Gx.below(f, n, hf)))

# a bound on the book's G bounds every def's body
# -----------------------------------------------

def Gx.Gdef.ge(d: Bk.Def, +a: Nat) -> N.Le(a, N.Gdef(d, a)):
  match d:
    case Bk.Def{+k, +ty, +v, _}:
      +gk = N.Gk(k, a)
      +gh = N.Gt(ty, gk)
      +gv = N.Gt(v, gh)
      N.le_trans(a, gv, 4n+gv,
        N.le_trans(a, gh, gv,
          N.le_trans(a, gk, gh, Gx.Gk.ge(k, a), Gx.Gt.ge(ty, gk)),
          Gx.Gt.ge(v, gh)),
        N.le_add_l(4n, gv))

def Gx.Gd.ge(ds: List<&2, Bk.Def>, +a: Nat) -> N.Le(a, N.Gd(ds, a)):
  match ds:
    case Nil{}:
      N.le_add_l(2n, a)
    case Con{+d, +rest}:
      +grest = N.Gd(rest, a)
      N.le_trans(a, N.Gdef(d, grest), 2n+N.Gdef(d, grest),
        N.le_trans(a, grest, N.Gdef(d, grest), Gx.Gd.ge(rest, a), Gx.Gdef.ge(d, grest)),
        N.le_add_l(2n, N.Gdef(d, grest)))

def Gx.Gd.tail(+d: Bk.Def, +rest: List<&2, Bk.Def>) -> N.Le(N.Gd(rest, 0n), N.Gd(Con{d, rest}, 0n)):
  +grest = N.Gd(rest, 0n)
  N.le_trans(grest, N.Gdef(d, grest), 2n+N.Gdef(d, grest),
    Gx.Gdef.ge(d, grest), N.le_add_l(2n, N.Gdef(d, grest)))

def Gx.defs.below(ds: List<&2, Bk.Def>, +B: Nat, +h: N.Le(N.Gd(ds, 0n), B)) ->
  {Fv.Defs.below(ds, B) == True{} : Bool}:
  match ds:
    case Nil{}:
      {==}
    case Con{Bk.Def{+k, +ty, +v, +o}, +rest}:
      +grest = N.Gd(rest, 0n)
      +x = N.Gt(ty, N.Gk(k, grest))
      +gdef = N.Gdef(Bk.Def{k, ty, v, o}, grest)
      +hv = N.le_trans(N.Gt(v, 0n), 2n+gdef, B,
        N.le_trans(N.Gt(v, 0n), gdef, 2n+gdef,
          N.le_trans(N.Gt(v, 0n), N.Gt(v, x), gdef, Gx.mono0(v, x), N.le_add_l(4n, N.Gt(v, x))),
          N.le_add_l(2n, gdef)),
        h)
      +hrest = N.le_trans(grest, 2n+gdef, B, Gx.Gd.tail(Bk.Def{k, ty, v, o}, rest), h)
      Fv.fv.and_i(PM.Term.below(v, B), Fv.Defs.below(rest, B),
        Gx.below(v, B, hv), Gx.defs.below(rest, B, hrest))

# the image is at most 2^26-1 long
# --------------------------------

def Gx.bound.small(+p: List<&2, Word(8n)>, small: {Mc.Img.small(p, 0) == True{} : Bool}) ->
  N.Le(List.length(&2, Word(8n), p), U32.to_nat(67108863)):
  +l = List.length(&2, Word(8n), p)
  +m = U32.to_nat(67108863)
  N.le_rw_l(Nat.add(U32.to_nat(0), l), l, m, N.zero_add(l),
    I.small.le(p, 0, 67108863, {==}, I.le_zero_u32(67108863), small))

# 2^31 as a word and as a natural, with no large unary comparison
def Gx.lit.b31() -> {2147483648 == U32{N.bit(32n, 31n)} : U32}:
  {==}

def Gx.val.b31() -> {U32.to_nat(2147483648) == N.D(31n, 1n) : Nat}:
  %Equal.sym(U32, 2147483648, U32{N.bit(32n, 31n)}, Gx.lit.b31()) : {U32.to_nat(_) == N.D(31n, 1n) : Nat}
  %Equal.sym(Nat, U32.to_nat(U32{N.bit(32n, 31n)}), Word.to_nat(32n, N.bit(32n, 31n)), N.u32_to_nat(N.bit(32n, 31n))) :
    {_ == N.D(31n, 1n) : Nat}
  N.bit_val(32n, 31n, Unit{})

# 2^26-1 is below 2^31
# --------------------

# m + 1 = h = 2^26 and big = 2^31 give m <= big, over the variables m, h and
# big: the checker never expands the powers of two
def Gx.bound.big(+m: Nat, +h: Nat, +big: Nat, vm: {1n+m == h : Nat}, eh: {h == N.D(26n, 1n) : Nat},
  vb: {big == N.D(31n, 1n) : Nat}) -> N.Le(m, big):
  +v1 = N.weaken(m, h, N.le_rw_r(1n+m, 1n+m, h, vm, N.le_refl(1n+m)))
  +v2 = N.le_rw_r(h, N.D(5n, h), N.D(31n, 1n),
    (%Equal.sym(Nat, h, N.D(26n, 1n), eh) : {N.D(5n, _) == N.D(31n, 1n) : Nat}; N.D_add(5n, 26n, 31n, 1n, {==})),
    I.D_ge(5n, h))
  +v3 = N.le_rw_r(h, N.D(31n, 1n), big, Equal.sym(Nat, big, N.D(31n, 1n), vb), v2)
  N.le_trans(m, h, big, v1, v3)

# the book that p reads: every body is below 2^31
# ----------------------------------------------

def Gx.read.below(
  +p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>,
  rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  small: {Mc.Img.small(p, 0) == True{} : Bool}
) -> {Fv.Defs.below(ds, U32.to_nat(2147483648)) == True{} : Bool}:
  +l = List.length(&2, Word(8n), p)
  +big = U32.to_nat(2147483648)
  +v8 = N.le_trans(l, U32.to_nat(67108863), big, Gx.bound.small(p, small),
    Gx.bound.big(U32.to_nat(67108863), N.D(26n, 1n), big, N.val_M(), {==}, Gx.val.b31()))
  +v9 = N.le_trans(N.Gd(ds, 0n), l, big, Gx.read.le(p, ds, rd), v8)
  Gx.defs.below(ds, big, v9)
