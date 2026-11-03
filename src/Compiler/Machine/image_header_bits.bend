# compiler: what the machine reads of the image's headers (layer B)
# ================================================================
#
# Img.header(t, q, fl, fv) is lo | fv << 13, with lo = t | q << 6 | fl in its
# 13 low bits. What TgW, QnW, FlW and FvW read of it is what they read of lo,
# and fv's 19 low bits (hdr), and those are fv when fv < 2^19 (b19).
#
# Proof: lo | fv << 13 is a blend of lo and fv << 13 under the mask 8191
# (copy_header_bits.bend's U.blend, which reads the mask first), and with lo
# and fv split into their bits every reading of the blend computes (hdr.f).

import Base
import ../Cir/leb_round_trip.bend as L
import ./definitions.bend as D
import ./copy_header_bits.bend as HB
import ../need_big.bend as N

# The blend
# ---------

# fv << 13 has no bit under the mask 8191
def s13.sel(fv: U32) -> {U32.shln(fv, 13n) == HB.U.sel(U32.shln(fv, 13n), 8191) : U32}:
  match fv:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

# lo | fv << 13, for lo of 13 bits, blends lo and fv << 13
def hd.blend(+lo: U32, +fv: U32, +h: {U32.and(lo, 8191) == lo : U32}) ->
  {U32.or(lo, U32.shln(fv, 13n)) == HB.U.blend(lo, U32.shln(fv, 13n), 8191) : U32}:
  %h : {U32.or(_, U32.shln(fv, 13n)) == HB.U.blend(lo, U32.shln(fv, 13n), 8191) : U32}
  %Equal.sym(U32, U32.and(lo, 8191), HB.U.andm(lo, 8191), HB.U.am(lo, 8191)) :
    {U32.or(_, U32.shln(fv, 13n)) == HB.U.blend(lo, U32.shln(fv, 13n), 8191) : U32}
  %Equal.sym(U32, U32.shln(fv, 13n), HB.U.sel(U32.shln(fv, 13n), 8191), s13.sel(fv)) :
    {U32.or(HB.U.andm(lo, 8191), _) == HB.U.blend(lo, U32.shln(fv, 13n), 8191) : U32}
  HB.U.bl(lo, U32.shln(fv, 13n), 8191)

# what the masks read of the blend
def HdrB(+lo: U32, +fv: U32) -> Data:
  D.P2({HB.U.andm(HB.U.blend(lo, U32.shln(fv, 13n), 8191), 63) == HB.U.andm(lo, 63) : U32},
  D.P2({HB.U.andm(U32.shrn(HB.U.blend(lo, U32.shln(fv, 13n), 8191), 6n), 3) == HB.U.andm(U32.shrn(lo, 6n), 3) : U32},
  D.P2({HB.U.andm(HB.U.blend(lo, U32.shln(fv, 13n), 8191), 256) == HB.U.andm(lo, 256) : U32},
  D.P2({HB.U.andm(HB.U.blend(lo, U32.shln(fv, 13n), 8191), 512) == HB.U.andm(lo, 512) : U32},
  D.P2({HB.U.andm(HB.U.blend(lo, U32.shln(fv, 13n), 8191), 1024) == HB.U.andm(lo, 1024) : U32},
    {U32.shrn(HB.U.blend(lo, U32.shln(fv, 13n), 8191), 13n) == HB.U.andm(fv, 524287) : U32})))))

def hdr.f(lo: U32, fv: U32) -> HdrB(lo, fv):
  match lo fv:
    case U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{a8, WCon{a9, WCon{a10, WCon{a11, WCon{a12, WCon{a13, WCon{a14, WCon{a15, WCon{a16, WCon{a17, WCon{a18, WCon{a19, WCon{a20, WCon{a21, WCon{a22, WCon{a23, WCon{a24, WCon{a25, WCon{a26, WCon{a27, WCon{a28, WCon{a29, WCon{a30, WCon{a31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      ({==}, ({==}, ({==}, ({==}, ({==}, {==})))))

# The header
# ----------

# what the machine reads of the header f0 of the low part lo and the fv fv
def HdrX(+lo: U32, +fv: U32, +f0: U32) -> Data:
  D.P2({D.TgW(f0) == U32.and(lo, 63) : U32},
  D.P2({D.QnW(f0) == U32.and(U32.shrn(lo, 6n), 3) : U32},
  D.P2({D.FlW(f0, 256) == D.FlW(lo, 256) : Bool},
  D.P2({D.FlW(f0, 512) == D.FlW(lo, 512) : Bool},
  D.P2({D.FlW(f0, 1024) == D.FlW(lo, 1024) : Bool},
    {D.FvW(f0) == U32.and(fv, 524287) : U32})))))

def Hdr(+lo: U32, +fv: U32) -> Data:
  HdrX(lo, fv, U32.or(lo, U32.shln(fv, 13n)))

# x and y agree under the mask k, as U32.and reads them
def and.eq(+x: U32, +y: U32, +k: U32, e: {HB.U.andm(x, k) == HB.U.andm(y, k) : U32}) -> {U32.and(x, k) == U32.and(y, k) : U32}:
  Equal.trans(U32, U32.and(x, k), HB.U.andm(x, k), U32.and(y, k), HB.U.am(x, k),
    Equal.trans(U32, HB.U.andm(x, k), HB.U.andm(y, k), U32.and(y, k), e, Equal.sym(U32, U32.and(y, k), HB.U.andm(y, k), HB.U.am(y, k))))

# the header lo | fv << 13, for lo of 13 bits, from what the masks read of the blend
def hdr.of(+lo: U32, +fv: U32, +h: {U32.and(lo, 8191) == lo : U32}, hb: HdrB(lo, fv)) -> Hdr(lo, fv):
  match hb:
    case Tuple{e1, Tuple{e2, Tuple{e3, Tuple{e4, Tuple{e5, e6}}}}}:
      +B = HB.U.blend(lo, U32.shln(fv, 13n), 8191)
      %Equal.sym(U32, U32.or(lo, U32.shln(fv, 13n)), B, hd.blend(lo, fv, h)) : HdrX(lo, fv, _)
      (and.eq(B, lo, 63, e1),
      (and.eq(U32.shrn(B, 6n), U32.shrn(lo, 6n), 3, e2),
      (Equal.cong(U32, Bool, z => U32.is_ne(z, 0), U32.and(B, 256), U32.and(lo, 256), and.eq(B, lo, 256, e3)),
      (Equal.cong(U32, Bool, z => U32.is_ne(z, 0), U32.and(B, 512), U32.and(lo, 512), and.eq(B, lo, 512, e4)),
      (Equal.cong(U32, Bool, z => U32.is_ne(z, 0), U32.and(B, 1024), U32.and(lo, 1024), and.eq(B, lo, 1024, e5)),
        Equal.trans(U32, U32.shrn(B, 13n), HB.U.andm(fv, 524287), U32.and(fv, 524287), e6,
          Equal.sym(U32, U32.and(fv, 524287), HB.U.andm(fv, 524287), HB.U.am(fv, 524287))))))))

def hdr(+lo: U32, +fv: U32, +h: {U32.and(lo, 8191) == lo : U32}) -> Hdr(lo, fv):
  hdr.of(lo, fv, h, hdr.f(lo, fv))

# 19 bits
# -------

# 2a <= 1 + 2b gives a <= b
def dle.odd(a: Nat, b: Nat, h: N.Le(Nat.double(a), 1n+Nat.double(b))) -> N.Le(a, b):
  match a:
    case 0n:
      N.le_zero(b)
    case 1n+p:
      match b:
        case 0n:
          Empty.absurd(N.Le(1n+p, 0n), h)
        case 1n+q:
          dle.odd(p, q, h)

# the word of no low bit set counts 0
def low0(n: Nat) -> {Word.to_nat(n, L.Word.low(n, 0n)) == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => Nat.double(z), Word.to_nat(p, L.Word.low(p, 0n)), 0n, low0(p))

# a word at most the word of its k low bits set keeps its bits under it
def am.low(n: Nat, w: Word(n), k: Nat, h: N.Le(Word.to_nat(n, w), Word.to_nat(n, L.Word.low(n, k)))) ->
  {L.Word.andm(n, w, L.Word.low(n, k)) == w : Word(n)}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+(+p):
      match w k:
        case WCon{False{}, +t} 0n:
          Equal.cong(Word(p), Word(1n+p), z => WCon{False{}, z}, L.Word.andm(p, t, L.Word.low(p, 0n)), t,
            am.low(p, t, 0n, D.dle(Word.to_nat(p, t), Word.to_nat(p, L.Word.low(p, 0n)), h)))
        case WCon{True{}, +t} 0n:
          Empty.absurd({L.Word.andm(1n+p, WCon{True{}, t}, L.Word.low(1n+p, 0n)) == WCon{True{}, t} : Word(1n+p)},
            (%low0(p) : N.Le(1n+Nat.double(Word.to_nat(p, t)), Nat.double(_)); h))
        case WCon{False{}, +t} 1n+(+q):
          Equal.cong(Word(p), Word(1n+p), z => WCon{False{}, z}, L.Word.andm(p, t, L.Word.low(p, q)), t,
            am.low(p, t, q, dle.odd(Word.to_nat(p, t), Word.to_nat(p, L.Word.low(p, q)), h)))
        case WCon{True{}, +t} 1n+(+q):
          Equal.cong(Word(p), Word(1n+p), z => WCon{True{}, z}, L.Word.andm(p, t, L.Word.low(p, q)), t,
            am.low(p, t, q, D.dle(Word.to_nat(p, t), Word.to_nat(p, L.Word.low(p, q)), h)))

# 524287, the word of 19 low bits set
def lit19() -> {524287 == U32{L.Word.low(32n, 19n)} : U32}:
  {==}

# fv's 19 low bits are fv, when fv <= Z = 2^19 - 1 (Z stays a variable: the
# checkers never expand it)
def b19(+fv: U32, +Z: Nat, +eZ: {Z == Word.to_nat(32n, L.Word.low(32n, 19n)) : Nat}, h: N.Le(U32.to_nat(fv), Z)) ->
  {U32.and(fv, 524287) == fv : U32}:
  match fv:
    case U32{+w}:
      +lw = L.Word.low(32n, 19n)
      +h2 = {(%N.u32_to_nat(w) : N.Le(_, Z); h) : N.Le(Word.to_nat(32n, w), Z)}
      +h3 = {(%eZ : N.Le(Word.to_nat(32n, w), _); h2) : N.Le(Word.to_nat(32n, w), Word.to_nat(32n, lw))}
      %Equal.sym(U32, 524287, U32{lw}, lit19()) : {U32.and(U32{w}, _) == U32{w} : U32}
      Equal.trans(U32, U32{Word.and(32n, w, lw)}, U32{L.Word.andm(32n, w, lw)}, U32{w},
        Equal.cong(Word(32n), U32, z => U32{z}, Word.and(32n, w, lw), L.Word.andm(32n, w, lw), L.Word.and_is_andm(32n, w, lw)),
        Equal.cong(Word(32n), U32, z => U32{z}, L.Word.andm(32n, w, lw), w, am.low(32n, w, 19n, h3)))
