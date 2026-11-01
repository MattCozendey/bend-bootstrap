# the number of bytes, in decimal: Nat.show divides a unary Nat by 10, and binds
# its rest at quantity 2 at each step
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

def main(i: List<&2, Word(8n)>) -> List<&2, Word(8n)>:
  bytes(Nat.show(List.length(&2, Word(8n), i)))
