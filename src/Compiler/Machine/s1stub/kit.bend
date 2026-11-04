# STUB of lane S1's Machine/shared.bend (P2): the names that lane S2 uses, as S1's work in progress
# writes them, so that S2's files load before S1 lands. At the merge with w/s1, each import of this
# file becomes an import of Machine/shared.bend, and this file is deleted.

import Base

# a pair of two Data types, itself Data
def P2(-A: Data, -B: Data) -> Data:
  Sigma<&2, &2, A, _ => B>

# the register r is in xs
def Has(xs: List<&2, Nat>, +r: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{x, rest}:
      Nat.is_eq(x, r) || Has(rest, r)

# the cell c is in xs
def Mem(xs: List<&2, U32>, +c: U32) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{x, rest}:
      U32.is_eq(x, c) || Mem(rest, c)
