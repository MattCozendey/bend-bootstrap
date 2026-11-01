import Base
import ../../Book/impl.bend as Bk

def isApp(t: Bk.Term) -> Bool:
  match t:
    case Bk.Term.App{_, _, _}:
      True{}
    case _:
      False{}

def t.k(+t: Bk.Term) -> {isApp(t) == isApp(t) : Bool}:
  match t:
    case Bk.Term.Var{i}:
      ?h
    case _:
      {==}
