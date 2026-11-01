import Base

# Bytes
# =====
#
# A byte is a Word(8n), its lowest bit first (AGENTS.md 3.3.1). Where the
# WASM spec reads a byte as a number, the version of WASM takes its value
# (Byte.to_u32); where it writes a number as a byte, its low byte
# (Byte.from_u32), as load8_u and store8 do (spec 4.4.7).

# the low n bits of a word of n + m bits
def Word.low(n: Nat, m: Nat, w: Word(Nat.add(n, m))) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match w:
        case WCon{b, t}:
          WCon{b, Word.low(p, m, t)}

# the word w of n bits, then m bits 0
def Word.pad(n: Nat, m: Nat, w: Word(n)) -> Word(Nat.add(n, m)):
  match n:
    case 0n:
      Word.zero(m)
    case 1n+p:
      match w:
        case WCon{b, t}:
          WCon{b, Word.pad(p, m, t)}

# the low byte of x
def Byte.from_u32(x: U32) -> Word(8n):
  match x:
    case U32{w}:
      Word.low(8n, 24n, w)

# the value of the byte b
def Byte.to_u32(b: Word(8n)) -> U32:
  U32{Word.pad(8n, 24n, b)}

def Byte.is_eq(a: Word(8n), b: Word(8n)) -> Bool:
  Cmp.is_eq(Word.cmp(8n, a, b))

def Name.is_eq(a: List<&2, Word(8n)>, b: List<&2, Word(8n)>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Con{x, xs} Con{y, ys}:
      Byte.is_eq(x, y) && Name.is_eq(xs, ys)
    case _ _:
      False{}
