# the number of bytes, in decimal, by a recursion that is not a tail call: its
# frames grow with the input
import Base

# the low n bits of a word of n + 24 bits
def low(n: Nat, w: Word(Nat.add(n, 24n))) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match w:
        case WCon{b, t}:
          WCon{b, low(p, t)}

# the ASCII bytes of a string of digits
def bytes(s: String) -> List<&2, Word(8n)>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{Chr{U32{c}}, rest}:
      Con{low(8n, c), bytes(rest)}

def len(xs: List<&2, Word(8n)>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{_, rest}:
      1n+len(rest)

def main(i: List<&2, Word(8n)>) -> List<&2, Word(8n)>:
  bytes(Nat.show(len(i)))
