# each byte plus 1: Word(8n) arithmetic, bit by bit
import Base

def incs(xs: List<&2, Word(8n)>) -> List<&2, Word(8n)>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, rest}:
      Con{Word.inc(8n, x), incs(rest)}

def main(i: List<&2, Word(8n)>) -> List<&2, Word(8n)>:
  incs(i)
