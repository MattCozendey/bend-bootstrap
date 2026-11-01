# erased and Data parameters, and a list used twice
import Base

def keep(-n: Nat, +x: Word(8n), y: Word(8n)) -> Word(8n):
  Word.add(8n, x, Word.add(8n, x, y))

def twice(+xs: List<&2, Word(8n)>) -> List<&2, Word(8n)>:
  List.append(&2, Word(8n), xs, xs)

def one() -> Word(8n):
  WCon{True{}, Word.zero(7n)}

def go(xs: List<&2, Word(8n)>) -> List<&2, Word(8n)>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, rest}:
      Con{keep(5n, x, one()), go(rest)}

def main(+i: List<&2, Word(8n)>) -> List<&2, Word(8n)>:
  twice(go(i))
