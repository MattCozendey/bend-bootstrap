# STUB of lane S1's Machine/header/spec.bend (P2): the table as Bend functions of the tag (redesign
# plan §4.2), which lane S2 uses, so that S2's files load before S1 lands. At the merge with w/s1,
# each import of this file becomes an import of Machine/header/spec.bend (with S1's names), and
# this file is deleted.

import Base

# the fields that hold counted pointers, by tag: 1 field 2, 2 field 3, 4 field 4. Terms as the
# image's table; frames and argument cells: field 2 (Rwt's frame: fields 2 and 3); FREE: none
def Tbl.mask.of(n: Nat, +t: U32) -> U32:
  match n:
    case 0n:
      0
    case 1n:
      0
    case 2n:
      3
    case 3n:
      3
    case 4n:
      1
    case 5n:
      3
    case 6n:
      3
    case 7n:
      1
    case 8n:
      3
    case 9n:
      3
    case 10n:
      3
    case 11n:
      1
    case 12n:
      0
    case 13n:
      0
    case 14n:
      6
    case 15n:
      0
    case 16n:
      7
    case 17n:
      0
    case 18n:
      7
    case 38n:
      3
    case _:
      Bool.pick(U32, U32.is_le(32, t) && U32.is_le(t, 41), 1, 0)

def Tbl.mask(+t: U32) -> U32:
  Tbl.mask.of(U32.to_nat(t), t)

def Tbl.bind.of(n: Nat, k: Nat) -> Nat:
  match n k:
    case 3n 3n:
      1n
    case 6n 3n:
      1n
    case 7n 2n:
      1n
    case 9n 3n:
      1n
    case 18n 3n:
      2n
    case _ _:
      0n

# the binders above field k of a term of tag t
def Tbl.bind(+t: U32, k: Nat) -> Nat:
  Tbl.bind.of(U32.to_nat(t), k)

def Tbl.former.of(n: Nat) -> Bool:
  match n:
    case 4n:
      True{}
    case 6n:
      True{}
    case 7n:
      True{}
    case 9n:
      True{}
    case 11n:
      True{}
    case 12n:
      True{}
    case 13n:
      True{}
    case 14n:
      True{}
    case 15n:
      True{}
    case 16n:
      True{}
    case 17n:
      True{}
    case _:
      False{}

# a term of tag t is a value by its form (the table's field 4: every former but Tup)
def Tbl.former(+t: U32) -> Bool:
  Tbl.former.of(U32.to_nat(t))
