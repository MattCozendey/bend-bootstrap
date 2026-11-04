# compiler: layer B2, the header of a cell, and the table by tag
# ==============================================================
#
# The only layer with 32-bit bit-blasting. A cell's field 0 (Machine/impl.bend's
# header) holds its tag (bits 0 to 5), its quantity (bits 6 and 7), its flags
# (bits 8 to 12: VALUE, DATA, STATIC, KNOWN, BUILD) and fv (bits 13 up); while
# BUILD, bits 13 to 15 are the todo bits of fields 2 to 4. Hd.* read the parts;
# the image's encoder Img.header writes them (hd.*_of read them back); the
# mask laws (mask.*), each proven once by its 32 bits, rewrite every other
# header that the machine makes.
#
# The table by tag (Tbl.*): which fields of a cell hold counted pointers, the
# binders above each, and whether a term of the tag is a value by its form.
# For a term (tags 0 to 18) it is what the image's table (Img.table, cells
# 272 to 290) holds; for the machine's own cells, the fields that hold terms.

import Base
import ../shared.bend as K
import ../../Cir/impl.bend as Cr
import ../impl.bend as Mc

# The header
# ----------

def Hd.tag(h: U32) -> U32:
  U32.and(h, 63)

def Hd.q(h: U32) -> U32:
  U32.and(U32.shrn(h, 6n), 3)

# the header h has the flag bit
def Hd.has(h: U32, +bit: U32) -> Bool:
  U32.is_ne(U32.and(h, bit), 0)

def Hd.fv(h: U32) -> U32:
  U32.shrn(h, 13n)

# the todo bits of a BUILD header (8192, 16384, 32768 for fields 2, 3, 4)
def Hd.todo(h: U32) -> U32:
  U32.and(h, 57344)

# bit is one flag: VALUE, DATA, STATIC, KNOWN or BUILD
def Hd.flag_bit(+bit: U32) -> Bool:
  U32.is_eq(bit, 256) || U32.is_eq(bit, 512) || U32.is_eq(bit, 1024) || U32.is_eq(bit, 2048) || U32.is_eq(bit, 4096)

# the header's parts fit: a tag below 64, a quantity below 4, flags only in
# bits 8 to 12, fv below 2^19
def Hd.fits(+t: U32, +q: U32, +fl: U32, +fv: U32) -> Bool:
  U32.is_lt(t, 64) && U32.is_lt(q, 4) && U32.is_eq(U32.and(fl, 4294959359), 0) && U32.is_lt(fv, 524288)

# The table
# ---------

# the cell of the image's table for the term tag t (below 19), as Img.table
# writes it: the mask of its pointers in field 2, the binders above each in
# field 3 (2 bits a field, field 2's lowest), 1 in field 4 for a former; all
# zeros for any other tag
def Tbl.cell(+t: U32) -> Cr.Cir.Cell:
  Bool.pick(Cr.Cir.Cell, U32.is_lt(t, 19),
    Maybe.default(&2, Cr.Cir.Cell, List.get(&2, Cr.Cir.Cell, Mc.Img.table([]), U32.to_nat(t)), Cr.Cir.Cell.zero()),
    Cr.Cir.Cell.zero())

# the fields of a cell of tag t that hold counted pointers: 1 field 2, 2
# field 3, 4 field 4. A term: as the image's table; a frame and an argument
# cell: field 2 (Rwt's frame: fields 2 and 3); a FREE cell and any other: none
def Tbl.mask(+t: U32) -> U32:
  Bool.pick(U32, U32.is_lt(t, 19), Cr.Cir.Cell.get(2n, Tbl.cell(t)),
    Bool.pick(U32, U32.is_eq(t, Mc.K.rwt()), 3,
      Bool.pick(U32, U32.is_le(Mc.K.app_arg(), t) && U32.is_le(t, Mc.K.arg()), 1, 0)))

# the binders above field k (2, 3 or 4) of a term of tag t
def Tbl.bind(+t: U32, +k: Nat) -> Nat:
  U32.to_nat(U32.and(U32.shrn(Cr.Cir.Cell.get(3n, Tbl.cell(t)), Nat.mul(2n, Nat.sub(k, 2n))), 3))

# a term of tag t is a value by its form (a Tup is not: its parts decide)
def Tbl.former(+t: U32) -> Bool:
  U32.is_ne(Cr.Cir.Cell.get(4n, Tbl.cell(t)), 0)

# Laws: the header's parts
# ------------------------

# LAW: the tag of a header
law hd.tag_of:
  for +t: U32
  for +q: U32
  for +fl: U32
  for +fv: U32
  for h: {Hd.fits(t, q, fl, fv) == True{} : Bool}
  {Hd.tag(Mc.Img.header(t, q, fl, fv)) == t : U32}

# LAW: the quantity of a header
law hd.q_of:
  for +t: U32
  for +q: U32
  for +fl: U32
  for +fv: U32
  for h: {Hd.fits(t, q, fl, fv) == True{} : Bool}
  {Hd.q(Mc.Img.header(t, q, fl, fv)) == q : U32}

# LAW: fv of a header
law hd.fv_of:
  for +t: U32
  for +q: U32
  for +fl: U32
  for +fv: U32
  for h: {Hd.fits(t, q, fl, fv) == True{} : Bool}
  {Hd.fv(Mc.Img.header(t, q, fl, fv)) == fv : U32}

# LAW: a flag of a header is the flag of fl
law hd.has_of:
  for +t: U32
  for +q: U32
  for +fl: U32
  for +fv: U32
  for +bit: U32
  for h: {Hd.fits(t, q, fl, fv) == True{} : Bool}
  for hb: {Hd.flag_bit(bit) == True{} : Bool}
  {Hd.has(Mc.Img.header(t, q, fl, fv), bit) == Hd.has(fl, bit) : Bool}

# LAW: the todo bits of a header are the bits 13 to 15 of fv's place
law hd.todo_of:
  for +t: U32
  for +q: U32
  for +fl: U32
  for +fv: U32
  for h: {Hd.fits(t, q, fl, fv) == True{} : Bool}
  {Hd.todo(Mc.Img.header(t, q, fl, fv)) == U32.shln(U32.and(fv, 7), 13n) : U32}

# Laws: masks
# -----------
#
# The algebra of and, or and the shifts by a constant, each proven once by
# its 32 bits; with the constants that the machine uses, they rewrite each
# header it makes to the parts that Hd.* read.

# LAW: and distributes over or
law mask.and_or:
  for +a: U32
  for +b: U32
  for +m: U32
  {U32.and(U32.or(a, b), m) == U32.or(U32.and(a, m), U32.and(b, m)) : U32}

# LAW: and is associative (two masks are one)
law mask.and_and:
  for +a: U32
  for +b: U32
  for +c: U32
  {U32.and(U32.and(a, b), c) == U32.and(a, U32.and(b, c)) : U32}

# LAW: a mask of a shifted word is the shift of the word's mask
law mask.and_shl:
  for +a: U32
  for +n: Nat
  for +m: U32
  {U32.and(U32.shln(a, n), m) == U32.shln(U32.and(a, U32.shrn(m, n)), n) : U32}

# LAW: a shift right of an or, and of an and
law mask.shr_or:
  for +a: U32
  for +b: U32
  for +n: Nat
  {U32.shrn(U32.or(a, b), n) == U32.or(U32.shrn(a, n), U32.shrn(b, n)) : U32}

law mask.shr_and:
  for +a: U32
  for +m: U32
  for +n: Nat
  {U32.shrn(U32.and(a, m), n) == U32.and(U32.shrn(a, n), U32.shrn(m, n)) : U32}

# LAW: a shift left then right keeps the bits that stay in the word
law mask.shr_shl:
  for +a: U32
  for +n: Nat
  {U32.shrn(U32.shln(a, n), n) == U32.and(a, U32.shrn(4294967295, n)) : U32}

# LAW: 0 is the unit of or, and the zero of and
law mask.or_zero:
  for +a: U32
  {U32.or(a, 0) == a : U32}

law mask.zero_or:
  for +a: U32
  {U32.or(0, a) == a : U32}

law mask.and_zero:
  for +a: U32
  {U32.and(a, 0) == 0 : U32}

law mask.zero_and:
  for +a: U32
  {U32.and(0, a) == 0 : U32}

# LAW: a word below 2^k keeps its value under the mask of its k bits, and has
# none from bit k
law mask.and_low:
  for +a: U32
  for +k: Nat
  for h: {U32.is_lt(a, U32.shln(1, k)) == True{} : Bool}
  {U32.and(a, U32.sub(U32.shln(1, k), 1)) == a : U32}

law mask.shr_low:
  for +a: U32
  for +k: Nat
  for h: {U32.is_lt(a, U32.shln(1, k)) == True{} : Bool}
  {U32.shrn(a, k) == 0 : U32}

# LAW: taking a bit that is set is clearing it
law mask.sub_bit:
  for +h: U32
  for +b: U32
  for e: {U32.and(h, b) == b : U32}
  {U32.sub(h, b) == U32.and(h, U32.not(b)) : U32}
