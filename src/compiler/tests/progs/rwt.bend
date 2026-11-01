# the first byte, after a rewrite that runs as code: Rwt evaluates its proof
import Base

def two() -> {Nat.add(1n, 1n) == 2n : Nat}:
  {==}

def first(xs: List<&2, Word(8n)>) -> List<&2, Word(8n)>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, _}:
      [{x : Word(8n)}]

def main(i: List<&2, Word(8n)>) -> List<&2, Word(8n)>:
  %two() : List<&2, Word(8n)>
  first(i)
