# each byte plus 3: a closure that holds the 3
import Base

def adds(~f: Word(8n) -> Word(8n), xs: List<&2, Word(8n)>) -> List<&2, Word(8n)>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, rest}:
      Con{f(x), adds(~f, rest)}

def adder(n: Word(8n)) -> Word(8n) -> Word(8n):
  x => Word.add(8n, x, n)

def three() -> Word(8n):
  WCon{True{}, WCon{True{}, Word.zero(6n)}}

def main(i: List<&2, Word(8n)>) -> List<&2, Word(8n)>:
  adds(~adder(three()), i)
