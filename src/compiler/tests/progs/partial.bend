# each byte plus 3: a def applied to 2 of its 3 arguments
import Base

def add3(a: Word(8n), b: Word(8n), c: Word(8n)) -> Word(8n):
  Word.add(8n, a, Word.add(8n, b, c))

def apply(~f: Word(8n) -> Word(8n), xs: List<&2, Word(8n)>) -> List<&2, Word(8n)>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, rest}:
      Con{f(x), apply(~f, rest)}

def one() -> Word(8n):
  WCon{True{}, Word.zero(7n)}

def two() -> Word(8n):
  WCon{False{}, WCon{True{}, Word.zero(6n)}}

def main(i: List<&2, Word(8n)>) -> List<&2, Word(8n)>:
  apply(~add3(one(), two()), i)
