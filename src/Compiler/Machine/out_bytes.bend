# compiler: M.out gives the bytes of the focus' term, for layer B
# ===============================================================
#
# When the stack is empty and the focus is a value, the machine runs M.out:
# it walks the value as a list of bytes, emits each byte and halts with 0, or
# halts with 2 when the value is no list of bytes. out.run (and out.gives,
# out.some, out.none, out.known) proves that it gives Program.unbytes(v), for
# the term v of the focus' cell c (T.tm.of): a halt with 0 and the bytes out,
# a halt with 2 when there are none, or out of memory (Gives). out.any holds
# for any fuel (EM: more fuel keeps an ended run); out.post.of and
# out.done.of are out.post and out.done of moves.bend, over T.tm.of and
# okn in place of Is; tm.more, okn.mono, okn.node, oimg.*, olab.*, okids.*
# and tm.at are the parts of the bridge from Is that do not need Is.
#
# The proof has three layers, joined by readers of the same shape:
#   - terms: U and Wd read a term as the machine does (V1, VL), one cell at a
#     time; UE and WE prove that they read what Program.unbytes and
#     Program.unword read;
#   - cells: CB, GB, CW and Step read the cells by the machine's tests (Pm,
#     Lm, LAST, ISLAB), CU a whole list; BB, WB and LB prove that they read
#     what U and Wd read of the cells' terms, under ok (every cell that the
#     walk reads is a cell the state lets the machine read, Ref and Enu have
#     no pair or label term, and a label's number compares with the machine's
#     names as its name does);
#   - runs: MB (M.out.bit), ML and MWd (M.out.byte), MCon (M.out.con), LO (the
#     loop of M.out) and MOUT (M.out) run the statements on states ST, whose
#     registers have an explicit spine (RG), so that reading and setting a
#     register computes. Wp(o, K, H) says what the outcome may be; each test
#     is split by CasesK, and the continuation kk gets what the reader read.

import Base
import ../../Shared/shared.bend as Sd
import ../../Book/impl.bend as Bk
import ../../Wasm/impl.bend as Wa
import ../../Program/impl.bend as Pg
import ../Cir/impl.bend as Cr
import ./impl.bend as Mc
import ./cell_terms.bend as T
import ../need_big.bend as PN
import ../Cir/halt.bend as PH

# Kit
# ---

def isQ1(q: Bk.Quan) -> Bool:
  match q:
    case Bk.Quan.Q1{}:
      True{}
    case _:
      False{}

# the test of M.pair on field 0 of a cell
def FP.l(+f0: U32) -> Bool:
  U32.is_eq(U32.and(f0, 255), 74)

# tag 10 at quantity 1
def FP.r(+f0: U32) -> Bool:
  Bool.and(isQ1(T.tm.quan(U32.and(U32.shrn(f0, 6n), 3))), U32.is_eq(U32.and(f0, 63), 10))

def FPS(+f0: U32) -> Type:
  {FP.l(f0) == FP.r(f0) : Bool}

def fp.h7(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool) -> FPS(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}):
  match b6 b7:
    case _ True{}:
      {==}
    case False{} False{}:
      {==}
    case True{} False{}:
      {==}

def fp.h8(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool) -> FPS(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}):
  match b8:
    case True{}:
      fp.h7(b0, b1, b2, b3, b4, b5, b6, b7)
    case False{}:
      fp.h7(b0, b1, b2, b3, b4, b5, b6, b7)

def fp.h9(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool) -> FPS(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}):
  match b9:
    case True{}:
      fp.h8(b0, b1, b2, b3, b4, b5, b6, b7, b8)
    case False{}:
      fp.h8(b0, b1, b2, b3, b4, b5, b6, b7, b8)

def fp.h10(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool) -> FPS(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}):
  match b10:
    case True{}:
      fp.h9(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9)
    case False{}:
      fp.h9(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9)

def fp.h11(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool) -> FPS(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}):
  match b11:
    case True{}:
      fp.h10(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10)
    case False{}:
      fp.h10(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10)

def fp.h12(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool) -> FPS(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}):
  match b12:
    case True{}:
      fp.h11(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11)
    case False{}:
      fp.h11(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11)

def fp.h13(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool) -> FPS(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}):
  match b13:
    case True{}:
      fp.h12(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12)
    case False{}:
      fp.h12(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12)

def fp.h14(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool) -> FPS(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}):
  match b14:
    case True{}:
      fp.h13(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13)
    case False{}:
      fp.h13(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13)

def fp.h15(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool) -> FPS(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}):
  match b15:
    case True{}:
      fp.h14(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14)
    case False{}:
      fp.h14(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14)

def fp.h16(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool) -> FPS(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}):
  match b16:
    case True{}:
      fp.h15(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15)
    case False{}:
      fp.h15(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15)

def fp.h17(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool) -> FPS(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}):
  match b17:
    case True{}:
      fp.h16(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16)
    case False{}:
      fp.h16(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16)

def fp.h18(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool) -> FPS(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}):
  match b18:
    case True{}:
      fp.h17(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17)
    case False{}:
      fp.h17(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17)

def fp.h19(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool) -> FPS(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}):
  match b19:
    case True{}:
      fp.h18(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18)
    case False{}:
      fp.h18(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18)

def fp.h20(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool) -> FPS(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}):
  match b20:
    case True{}:
      fp.h19(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19)
    case False{}:
      fp.h19(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19)

def fp.h21(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +b21: Bool) -> FPS(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}):
  match b21:
    case True{}:
      fp.h20(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20)
    case False{}:
      fp.h20(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20)

def fp.h22(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +b21: Bool, +b22: Bool) -> FPS(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}):
  match b22:
    case True{}:
      fp.h21(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21)
    case False{}:
      fp.h21(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21)

def fp.h23(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +b21: Bool, +b22: Bool, +b23: Bool) -> FPS(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}):
  match b23:
    case True{}:
      fp.h22(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22)
    case False{}:
      fp.h22(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22)

def fp.h24(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +b21: Bool, +b22: Bool, +b23: Bool, +b24: Bool) -> FPS(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}):
  match b24:
    case True{}:
      fp.h23(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23)
    case False{}:
      fp.h23(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23)

def fp.h25(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +b21: Bool, +b22: Bool, +b23: Bool, +b24: Bool, +b25: Bool) -> FPS(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}):
  match b25:
    case True{}:
      fp.h24(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24)
    case False{}:
      fp.h24(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24)

def fp.h26(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +b21: Bool, +b22: Bool, +b23: Bool, +b24: Bool, +b25: Bool, +b26: Bool) -> FPS(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}):
  match b26:
    case True{}:
      fp.h25(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25)
    case False{}:
      fp.h25(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25)

def fp.h27(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +b21: Bool, +b22: Bool, +b23: Bool, +b24: Bool, +b25: Bool, +b26: Bool, +b27: Bool) -> FPS(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}):
  match b27:
    case True{}:
      fp.h26(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26)
    case False{}:
      fp.h26(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26)

def fp.h28(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +b21: Bool, +b22: Bool, +b23: Bool, +b24: Bool, +b25: Bool, +b26: Bool, +b27: Bool, +b28: Bool) -> FPS(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}):
  match b28:
    case True{}:
      fp.h27(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27)
    case False{}:
      fp.h27(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27)

def fp.h29(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +b21: Bool, +b22: Bool, +b23: Bool, +b24: Bool, +b25: Bool, +b26: Bool, +b27: Bool, +b28: Bool, +b29: Bool) -> FPS(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}):
  match b29:
    case True{}:
      fp.h28(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28)
    case False{}:
      fp.h28(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28)

def fp.h30(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +b21: Bool, +b22: Bool, +b23: Bool, +b24: Bool, +b25: Bool, +b26: Bool, +b27: Bool, +b28: Bool, +b29: Bool, +b30: Bool) -> FPS(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}):
  match b30:
    case True{}:
      fp.h29(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29)
    case False{}:
      fp.h29(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29)

def fp.h31(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +b21: Bool, +b22: Bool, +b23: Bool, +b24: Bool, +b25: Bool, +b26: Bool, +b27: Bool, +b28: Bool, +b29: Bool, +b30: Bool, +b31: Bool) -> FPS(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}):
  match b31:
    case True{}:
      fp.h30(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30)
    case False{}:
      fp.h30(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30)

# the pair test of a cell's field 0 is its tag's and its quantity's
def fp(+f0: U32) -> FPS(f0):
  match f0:
    case U32{WCon{+b0, WCon{+b1, WCon{+b2, WCon{+b3, WCon{+b4, WCon{+b5, WCon{+b6, WCon{+b7, WCon{+b8, WCon{+b9, WCon{+b10, WCon{+b11, WCon{+b12, WCon{+b13, WCon{+b14, WCon{+b15, WCon{+b16, WCon{+b17, WCon{+b18, WCon{+b19, WCon{+b20, WCon{+b21, WCon{+b22, WCon{+b23, WCon{+b24, WCon{+b25, WCon{+b26, WCon{+b27, WCon{+b28, WCon{+b29, WCon{+b30, WCon{+b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      fp.h31(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31)
# Words
# -----

# the word of n bits all 0
def zeros(n: Nat) -> Word(n):
  PN.ones(n, 0n)


# The term side
# -------------
#
# Program.unbytes and Program.unword read a term by one nested pattern. U and
# Wd read it as the machine does, one cell at a time, in the machine's order:
# V1 views a pair at quantity 1, VL a label.

type TP is Data:
  TP{a: Bk.Term, b: Bk.Term}

def V1(t: Bk.Term) -> Maybe<&2, TP>:
  match t:
    case Bk.Term.Tup{Bk.Quan.Q1{}, a, b}:
      Some{TP{a, b}}
    case _:
      None{}

def VL(t: Bk.Term) -> Maybe<&2, List<&2, Word(8n)>>:
  match t:
    case Bk.Term.Lab{k}:
      Some{k}
    case _:
      None{}

def U.c5(v: Word(8n), mr: Maybe<&2, List<&2, Word(8n)>>) -> Maybe<&2, List<&2, Word(8n)>>:
  match mr:
    case Some{bs}:
      Some{Con{v, bs}}
    case None{}:
      None{}

def U.c4(mw: Maybe<&2, Word(8n)>, rest: Bk.Term) -> Maybe<&2, List<&2, Word(8n)>>:
  match mw:
    case Some{x}:
      U.c5(x, Pg.Program.unbytes(rest))
    case None{}:
      None{}

def U.c3(ok: Bool, x: Bk.Term, rest: Bk.Term) -> Maybe<&2, List<&2, Word(8n)>>:
  match ok:
    case True{}:
      U.c4(Pg.Program.unword(8n, x), rest)
    case False{}:
      None{}

def U.c2(x: Bk.Term, rest: Bk.Term, m: Maybe<&2, List<&2, Word(8n)>>) -> Maybe<&2, List<&2, Word(8n)>>:
  match m:
    case Some{u2}:
      U.c3(Sd.Name.is_eq(u2, Pg.Program.name.unit()), x, rest)
    case None{}:
      None{}

def U.c1(x: Bk.Term, m: Maybe<&2, TP>) -> Maybe<&2, List<&2, Word(8n)>>:
  match m:
    case Some{TP{rest, z}}:
      U.c2(x, rest, VL(z))
    case None{}:
      None{}

def U.con(m: Maybe<&2, TP>) -> Maybe<&2, List<&2, Word(8n)>>:
  match m:
    case Some{TP{x, y}}:
      U.c1(x, V1(y))
    case None{}:
      None{}

def U.nil(m: Maybe<&2, List<&2, Word(8n)>>) -> Maybe<&2, List<&2, Word(8n)>>:
  match m:
    case Some{u}:
      Pg.Program.unbytes.nil(Sd.Name.is_eq(u, Pg.Program.name.unit()))
    case None{}:
      None{}

def U.k2(iscon: Bool, b: Bk.Term) -> Maybe<&2, List<&2, Word(8n)>>:
  match iscon:
    case True{}:
      U.con(V1(b))
    case False{}:
      None{}

def U.k(isnil: Bool, iscon: Bool, b: Bk.Term) -> Maybe<&2, List<&2, Word(8n)>>:
  match isnil:
    case True{}:
      U.nil(VL(b))
    case False{}:
      U.k2(iscon, b)

def U.a(m: Maybe<&2, List<&2, Word(8n)>>, b: Bk.Term) -> Maybe<&2, List<&2, Word(8n)>>:
  match m:
    case Some{+k}:
      U.k(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b)
    case None{}:
      None{}

def U.r(m: Maybe<&2, TP>) -> Maybe<&2, List<&2, Word(8n)>>:
  match m:
    case Some{TP{a, b}}:
      U.a(VL(a), b)
    case None{}:
      None{}

# the bytes of t, read in the machine's order
def U(t: Bk.Term) -> Maybe<&2, List<&2, Word(8n)>>:
  U.r(V1(t))

# a bit, read in the machine's order
def Ub.x(m: Maybe<&2, List<&2, Word(8n)>>) -> Maybe<&2, Bool>:
  match m:
    case Some{b}:
      Pg.Program.unbit(b)
    case None{}:
      None{}

def Ub.u(ok: Bool, x: Bk.Term) -> Maybe<&2, Bool>:
  match ok:
    case True{}:
      Ub.x(VL(x))
    case False{}:
      None{}

def Ub.y(m: Maybe<&2, List<&2, Word(8n)>>, x: Bk.Term) -> Maybe<&2, Bool>:
  match m:
    case Some{u}:
      Ub.u(Sd.Name.is_eq(u, Pg.Program.name.unit()), x)
    case None{}:
      None{}

def Ub.r(m: Maybe<&2, TP>) -> Maybe<&2, Bool>:
  match m:
    case Some{TP{x, y}}:
      Ub.y(VL(y), x)
    case None{}:
      None{}

def Ub(t: Bk.Term) -> Maybe<&2, Bool>:
  Ub.r(V1(t))

# a word, read in the machine's order
def W0.z(m: Maybe<&2, List<&2, Word(8n)>>) -> Maybe<&2, Word(0n)>:
  match m:
    case Some{u}:
      Pg.Program.unword.nil(Sd.Name.is_eq(u, Pg.Program.name.unit()))
    case None{}:
      None{}

def W0.k(ok: Bool, z: Bk.Term) -> Maybe<&2, Word(0n)>:
  match ok:
    case True{}:
      W0.z(VL(z))
    case False{}:
      None{}

def W0.a(m: Maybe<&2, List<&2, Word(8n)>>, z: Bk.Term) -> Maybe<&2, Word(0n)>:
  match m:
    case Some{k}:
      W0.k(Sd.Name.is_eq(k, Pg.Program.name.wnil()), z)
    case None{}:
      None{}

def W0.r(m: Maybe<&2, TP>) -> Maybe<&2, Word(0n)>:
  match m:
    case Some{TP{a, z}}:
      W0.a(VL(a), z)
    case None{}:
      None{}

def W1.w(-p: Nat, b: Bool, m: Maybe<&2, Word(p)>) -> Maybe<&2, Word(1n+p)>:
  match m:
    case Some{y}:
      Some{WCon{b, y}}
    case None{}:
      None{}

def W1.u(p: Nat, b: Bool, ok: Bool, w: Bk.Term) -> Maybe<&2, Word(1n+p)>:
  match ok:
    case True{}:
      W1.w(p, b, Pg.Program.unword(p, w))
    case False{}:
      None{}

def W1.z(p: Nat, b: Bool, w: Bk.Term, m: Maybe<&2, List<&2, Word(8n)>>) -> Maybe<&2, Word(1n+p)>:
  match m:
    case Some{u2}:
      W1.u(p, b, Sd.Name.is_eq(u2, Pg.Program.name.unit()), w)
    case None{}:
      None{}

def W1.r2(p: Nat, b: Bool, m: Maybe<&2, TP>) -> Maybe<&2, Word(1n+p)>:
  match m:
    case Some{TP{w, z}}:
      W1.z(p, b, w, VL(z))
    case None{}:
      None{}

def W1.b(p: Nat, mb: Maybe<&2, Bool>, r: Bk.Term) -> Maybe<&2, Word(1n+p)>:
  match mb:
    case Some{b}:
      W1.r2(p, b, V1(r))
    case None{}:
      None{}

def W1.f(p: Nat, m: Maybe<&2, TP>) -> Maybe<&2, Word(1n+p)>:
  match m:
    case Some{TP{bt, r}}:
      W1.b(p, Ub(bt), r)
    case None{}:
      None{}

def W1.k(p: Nat, ok: Bool, f: Bk.Term) -> Maybe<&2, Word(1n+p)>:
  match ok:
    case True{}:
      W1.f(p, V1(f))
    case False{}:
      None{}

def W1.a(p: Nat, m: Maybe<&2, List<&2, Word(8n)>>, f: Bk.Term) -> Maybe<&2, Word(1n+p)>:
  match m:
    case Some{k}:
      W1.k(p, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f)
    case None{}:
      None{}

def W1.r(p: Nat, m: Maybe<&2, TP>) -> Maybe<&2, Word(1n+p)>:
  match m:
    case Some{TP{a, f}}:
      W1.a(p, VL(a), f)
    case None{}:
      None{}

# the word of n bits of t, read in the machine's order
def Wd(n: Nat, t: Bk.Term) -> Maybe<&2, Word(n)>:
  match n:
    case 0n:
      W0.r(V1(t))
    case 1n+p:
      W1.r(p, V1(t))

# U reads what Program.unbytes reads
# ----------------------------------

# a and b true gives a true
def and_l(a: Bool, b: Bool, +e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, PN.false_ne_true(e))

def and_r(a: Bool, b: Bool, +e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      Empty.absurd({b == True{} : Bool}, PN.false_ne_true(e))

# a U32 equal to n has the number of n
def eq_nat(+x: U32, +n: U32, +e: {U32.is_eq(x, n) == True{} : Bool}) -> {U32.to_nat(x) == U32.to_nat(n) : Nat}:
  PN.rel_eq(U32.cmp(x, n), U32.to_nat(x), U32.to_nat(n), PN.U32.rel(x, n), PN.toT(U32.is_eq(x, n), e))

def ne_78_67(+e: {78n == 67n : Nat}) -> Empty:
  %e : PN.T(Nat.is_eq(_, 78n))
  Unit{}

# a byte equal to n has the number of n
def beq_nat(+x: Word(8n), +n: Word(8n), +e: {Sd.Byte.is_eq(x, n) == True{} : Bool}) -> {Word.to_nat(8n, x) == Word.to_nat(8n, n) : Nat}:
  PN.rel_eq(Word.cmp(8n, x, n), Word.to_nat(8n, x), Word.to_nat(8n, n), PN.Word.rel(8n, x, n), PN.toT(Sd.Byte.is_eq(x, n), e))

def nilcon.c(b: Bool, +x: Word(8n), +xs: List<&2, Word(8n)>, +e78: {Word.to_nat(8n, x) == 78n : Nat},
  +eb: {Sd.Byte.is_eq(x, Sd.Byte.from_u32(67)) == b : Bool}) ->
  {False{} == Bool.and(b, Sd.Name.is_eq(xs, [Sd.Byte.from_u32(111), Sd.Byte.from_u32(110)])) : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({False{} == Bool.and(True{}, Sd.Name.is_eq(xs, [Sd.Byte.from_u32(111), Sd.Byte.from_u32(110)])) : Bool},
        ne_78_67(Equal.trans(Nat, 78n, Word.to_nat(8n, x), 67n, Equal.sym(Nat, Word.to_nat(8n, x), 78n, e78), beq_nat(x, Sd.Byte.from_u32(67), eb))))

# a name that is Nil is not Con
def nilcon(k: List<&2, Word(8n)>, +e: {Sd.Name.is_eq(k, Pg.Program.name.nil()) == True{} : Bool}) ->
  {False{} == Sd.Name.is_eq(k, Pg.Program.name.con()) : Bool}:
  match k:
    case Nil{}:
      Empty.absurd({False{} == Sd.Name.is_eq(Nil{}, Pg.Program.name.con()) : Bool}, PN.false_ne_true(e))
    case Con{+x, +xs}:
      nilcon.c(Sd.Byte.is_eq(x, Sd.Byte.from_u32(67)), x, xs,
        beq_nat(x, Sd.Byte.from_u32(78), and_l(Sd.Byte.is_eq(x, Sd.Byte.from_u32(78)), Sd.Name.is_eq(xs, [Sd.Byte.from_u32(105), Sd.Byte.from_u32(108)]), e)), {==})

def Uk_none(isnil: Bool, iscon: Bool, -b: Bk.Term, +h1: {None{} == U.nil(VL(b)) : Maybe<&2, List<&2, Word(8n)>>},
  +h2: {None{} == U.con(V1(b)) : Maybe<&2, List<&2, Word(8n)>>}) -> {None{} == U.k(isnil, iscon, b) : Maybe<&2, List<&2, Word(8n)>>}:
  match isnil:
    case True{}:
      h1
    case False{}:
      match iscon:
        case True{}:
          h2
        case False{}:
          {==}

def LN(isnil: Bool, iscon: Bool, +u: List<&2, Word(8n)>) ->
  {Pg.Program.unbytes.nil(Bool.and(isnil, Sd.Name.is_eq(u, Pg.Program.name.unit()))) == U.k(isnil, iscon, Bk.Term.Lab{u}) : Maybe<&2, List<&2, Word(8n)>>}:
  match isnil:
    case True{}:
      {==}
    case False{}:
      match iscon:
        case True{}:
          {==}
        case False{}:
          {==}

def LF.r(+x: Word(8n), mr: Maybe<&2, List<&2, Word(8n)>>) ->
  {Pg.Program.unbytes.con(True{}, Some{x}, mr) == U.c5(x, mr) : Maybe<&2, List<&2, Word(8n)>>}:
  match mr:
    case None{}:
      {==}
    case Some{+bs}:
      {==}

def LF.w(mw: Maybe<&2, Word(8n)>, +rest: Bk.Term) ->
  {Pg.Program.unbytes.con(True{}, mw, Pg.Program.unbytes(rest)) == U.c4(mw, rest) : Maybe<&2, List<&2, Word(8n)>>}:
  match mw:
    case None{}:
      {==}
    case Some{+x}:
      LF.r(x, Pg.Program.unbytes(rest))

def LF.o(o: Bool, +w: Bk.Term, +rest: Bk.Term) ->
  {Pg.Program.unbytes.con(o, Pg.Program.unword(8n, w), Pg.Program.unbytes(rest)) == U.c3(o, w, rest) : Maybe<&2, List<&2, Word(8n)>>}:
  match o:
    case False{}:
      {==}
    case True{}:
      LF.w(Pg.Program.unword(8n, w), rest)

def LF.k2(iscon: Bool, +w: Bk.Term, +rest: Bk.Term, +u: List<&2, Word(8n)>) ->
  {Pg.Program.unbytes.con(Bool.and(iscon, Sd.Name.is_eq(u, Pg.Program.name.unit())), Pg.Program.unword(8n, w), Pg.Program.unbytes(rest)) ==
   U.k2(iscon, Bk.Term.Tup{Bk.Quan.Q1{}, w, Bk.Term.Tup{Bk.Quan.Q1{}, rest, Bk.Term.Lab{u}}}) : Maybe<&2, List<&2, Word(8n)>>}:
  match iscon:
    case False{}:
      {==}
    case True{}:
      LF.o(Sd.Name.is_eq(u, Pg.Program.name.unit()), w, rest)

def LF.n(isnil: Bool, +k: List<&2, Word(8n)>, +w: Bk.Term, +rest: Bk.Term, +u: List<&2, Word(8n)>,
  +e: {Sd.Name.is_eq(k, Pg.Program.name.nil()) == isnil : Bool}) ->
  {Pg.Program.unbytes.con(Bool.and(Sd.Name.is_eq(k, Pg.Program.name.con()), Sd.Name.is_eq(u, Pg.Program.name.unit())), Pg.Program.unword(8n, w), Pg.Program.unbytes(rest)) ==
   U.k(isnil, Sd.Name.is_eq(k, Pg.Program.name.con()), Bk.Term.Tup{Bk.Quan.Q1{}, w, Bk.Term.Tup{Bk.Quan.Q1{}, rest, Bk.Term.Lab{u}}}) : Maybe<&2, List<&2, Word(8n)>>}:
  match isnil:
    case True{}:
      %nilcon(k, e) : {Pg.Program.unbytes.con(Bool.and(_, Sd.Name.is_eq(u, Pg.Program.name.unit())), Pg.Program.unword(8n, w), Pg.Program.unbytes(rest)) ==
        U.k(True{}, Sd.Name.is_eq(k, Pg.Program.name.con()), Bk.Term.Tup{Bk.Quan.Q1{}, w, Bk.Term.Tup{Bk.Quan.Q1{}, rest, Bk.Term.Lab{u}}}) : Maybe<&2, List<&2, Word(8n)>>}
      {==}
    case False{}:
      LF.k2(Sd.Name.is_eq(k, Pg.Program.name.con()), w, rest, u)

def LF(+k: List<&2, Word(8n)>, +w: Bk.Term, +rest: Bk.Term, +u: List<&2, Word(8n)>) ->
  {Pg.Program.unbytes(Bk.Term.Tup{Bk.Quan.Q1{}, Bk.Term.Lab{k}, Bk.Term.Tup{Bk.Quan.Q1{}, w, Bk.Term.Tup{Bk.Quan.Q1{}, rest, Bk.Term.Lab{u}}}}) ==
   U(Bk.Term.Tup{Bk.Quan.Q1{}, Bk.Term.Lab{k}, Bk.Term.Tup{Bk.Quan.Q1{}, w, Bk.Term.Tup{Bk.Quan.Q1{}, rest, Bk.Term.Lab{u}}}}) : Maybe<&2, List<&2, Word(8n)>>}:
  LF.n(Sd.Name.is_eq(k, Pg.Program.name.nil()), k, w, rest, u, {==})

# Cells
# -----

# field k of the cell c
def Fd(k: Nat, +m: Cr.Cir.Cells, +c: U32) -> U32:
  Cr.Cir.Cell.get(k, Cr.Cir.Cells.get(m, c))

# the tag of the cell c (bits 0 to 5 of field 0)
def Tg(+m: Cr.Cir.Cells, +c: U32) -> U32:
  U32.and(Fd(0n, m, c), 63)

# M.pair holds of the cell c: a pair at quantity 1
def Pm(+m: Cr.Cir.Cells, +c: U32) -> Bool:
  FP.l(Fd(0n, m, c))

# the cell c is a label
def Lm(+m: Cr.Cir.Cells, +c: U32) -> Bool:
  U32.is_eq(Tg(m, c), 13)

# M.last holds of the cell c: its field 3 is the label of the name 0, ()
def LAST(+m: Cr.Cir.Cells, +c: U32) -> Bool:
  Bool.and(Lm(m, Fd(3n, m, c)), U32.is_eq(Fd(2n, m, Fd(3n, m, c)), 0))

# M.is_lab holds of field 2 of the cell c and the name n
def ISLAB(+m: Cr.Cir.Cells, +c: U32, +n: U32) -> Bool:
  Bool.and(Lm(m, Fd(2n, m, c)), U32.is_eq(Fd(2n, m, Fd(2n, m, c)), n))

def iff(a: Bool, b: Bool) -> Bool:
  match a b:
    case True{} True{}:
      True{}
    case False{} False{}:
      True{}
    case True{} False{}:
      False{}
    case False{} True{}:
      False{}

def iff_eq(a: Bool, b: Bool, +e: {iff(a, b) == True{} : Bool}) -> {a == b : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case False{} False{}:
      {==}
    case True{} False{}:
      Empty.absurd({True{} == False{} : Bool}, PN.false_ne_true(e))
    case False{} True{}:
      Empty.absurd({False{} == True{} : Bool}, PN.false_ne_true(e))

# the name b of the number j compares with the machine's names 0 to 6 as j
# compares with their numbers
def known.ok(+j: U32, +b: List<&2, Word(8n)>) -> Bool:
  iff(Sd.Name.is_eq(b, Pg.Program.name.unit()), U32.is_eq(j, 0)) &&
  iff(Sd.Name.is_eq(b, Pg.Program.name.nil()), U32.is_eq(j, 1)) &&
  iff(Sd.Name.is_eq(b, Pg.Program.name.con()), U32.is_eq(j, 2)) &&
  iff(Sd.Name.is_eq(b, Pg.Program.name.wnil()), U32.is_eq(j, 3)) &&
  iff(Sd.Name.is_eq(b, Pg.Program.name.wcon()), U32.is_eq(j, 4)) &&
  iff(Sd.Name.is_eq(b, Pg.Program.name.true()), U32.is_eq(j, 5)) &&
  iff(Sd.Name.is_eq(b, Pg.Program.name.false()), U32.is_eq(j, 6))

def labok.of(n: Maybe<&2, List<&2, Word(8n)>>, +j: U32) -> Bool:
  match n:
    case None{}:
      True{}
    case Some{b}:
      known.ok(j, b)

# the number j of a label is one whose name compares as known.ok says
def labok(+ks: List<&2, List<&2, Word(8n)>>, +j: U32) -> Bool:
  labok.of(T.tm.name(ks, j), j)

def noT1(r: Maybe<&2, Bk.Term>) -> Bool:
  match r:
    case None{}:
      True{}
    case Some{v}:
      Maybe.is_none(&2, TP, V1(v))

def noL(r: Maybe<&2, Bk.Term>) -> Bool:
  match r:
    case None{}:
      True{}
    case Some{v}:
      Maybe.is_none(&2, List<&2, Word(8n)>, VL(v))

def ok.img(+t: U32, +r: Maybe<&2, Bk.Term>) -> Bool:
  Bool.or(Bool.not(Bool.or(U32.is_eq(t, 1), U32.is_eq(t, 12))), Bool.and(noT1(r), noL(r)))

def ok.lab(+t: U32, +ks: List<&2, List<&2, Word(8n)>>, +j: U32) -> Bool:
  Bool.or(Bool.not(U32.is_eq(t, 13)), labok(ks, j))

# the cells that the walk of M.out reads from c, within fuel levels: each is
# a cell of the state (Cir.is_cell), a Ref or an Enu has an image's term
# that is no pair nor label, a label's number names it (labok), and the
# parts of a pair (tag 10) are such cells too, a level less deep
def ok(+fuel: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32,
  +fs: U32, +nx: U32) -> Bool:
  match fuel:
    case 0n:
      False{}
    case 1n+f:
      +t = Tg(m, c)
      Bool.and(Bool.and(Bool.and(Cr.Cir.is_cell(c, im, fs, nx), ok.img(t, T.tm.image(img, c))), ok.lab(t, ks, Fd(2n, m, c))),
        Bool.or(Bool.not(U32.is_eq(t, 10)),
          Bool.and(ok(f, m, ks, img, Fd(2n, m, c), im, fs, nx), ok(f, m, ks, img, Fd(3n, m, c), im, fs, nx))))

def or_not(x: Bool, y: Bool, +e1: {Bool.or(Bool.not(x), y) == True{} : Bool}, +e2: {x == True{} : Bool}) -> {y == True{} : Bool}:
  match x:
    case True{}:
      e1
    case False{}:
      Empty.absurd({y == True{} : Bool}, PN.false_ne_true(e2))

def ok.cell(+f: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32,
  +h: {ok(1n+f, m, ks, img, c, im, fs, nx) == True{} : Bool}) -> {Cr.Cir.is_cell(c, im, fs, nx) == True{} : Bool}:
  +t = Tg(m, c)
  +h1 = and_l(Bool.and(Bool.and(Cr.Cir.is_cell(c, im, fs, nx), ok.img(t, T.tm.image(img, c))), ok.lab(t, ks, Fd(2n, m, c))),
        Bool.or(Bool.not(U32.is_eq(t, 10)),
          Bool.and(ok(f, m, ks, img, Fd(2n, m, c), im, fs, nx), ok(f, m, ks, img, Fd(3n, m, c), im, fs, nx))), h)
  +h2 = and_l(Bool.and(Cr.Cir.is_cell(c, im, fs, nx), ok.img(t, T.tm.image(img, c))), ok.lab(t, ks, Fd(2n, m, c)), h1)
  and_l(Cr.Cir.is_cell(c, im, fs, nx), ok.img(t, T.tm.image(img, c)), h2)

def ok.im(+f: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32,
  +h: {ok(1n+f, m, ks, img, c, im, fs, nx) == True{} : Bool},
  +e: {Bool.or(U32.is_eq(Tg(m, c), 1), U32.is_eq(Tg(m, c), 12)) == True{} : Bool}) ->
  {Bool.and(noT1(T.tm.image(img, c)), noL(T.tm.image(img, c))) == True{} : Bool}:
  +t = Tg(m, c)
  +h1 = and_l(Bool.and(Bool.and(Cr.Cir.is_cell(c, im, fs, nx), ok.img(t, T.tm.image(img, c))), ok.lab(t, ks, Fd(2n, m, c))),
        Bool.or(Bool.not(U32.is_eq(t, 10)),
          Bool.and(ok(f, m, ks, img, Fd(2n, m, c), im, fs, nx), ok(f, m, ks, img, Fd(3n, m, c), im, fs, nx))), h)
  +h2 = and_l(Bool.and(Cr.Cir.is_cell(c, im, fs, nx), ok.img(t, T.tm.image(img, c))), ok.lab(t, ks, Fd(2n, m, c)), h1)
  or_not(Bool.or(U32.is_eq(t, 1), U32.is_eq(t, 12)), Bool.and(noT1(T.tm.image(img, c)), noL(T.tm.image(img, c))),
    and_r(Cr.Cir.is_cell(c, im, fs, nx), ok.img(t, T.tm.image(img, c)), h2), e)

def ok.lb(+f: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32,
  +h: {ok(1n+f, m, ks, img, c, im, fs, nx) == True{} : Bool},
  +e: {U32.is_eq(Tg(m, c), 13) == True{} : Bool}) -> {labok(ks, Fd(2n, m, c)) == True{} : Bool}:
  +t = Tg(m, c)
  +h1 = and_l(Bool.and(Bool.and(Cr.Cir.is_cell(c, im, fs, nx), ok.img(t, T.tm.image(img, c))), ok.lab(t, ks, Fd(2n, m, c))),
        Bool.or(Bool.not(U32.is_eq(t, 10)),
          Bool.and(ok(f, m, ks, img, Fd(2n, m, c), im, fs, nx), ok(f, m, ks, img, Fd(3n, m, c), im, fs, nx))), h)
  or_not(U32.is_eq(t, 13), labok(ks, Fd(2n, m, c)),
    and_r(Bool.and(Cr.Cir.is_cell(c, im, fs, nx), ok.img(t, T.tm.image(img, c))), ok.lab(t, ks, Fd(2n, m, c)), h1), e)

def ok.kids(+f: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32,
  +h: {ok(1n+f, m, ks, img, c, im, fs, nx) == True{} : Bool},
  +e: {U32.is_eq(Tg(m, c), 10) == True{} : Bool}) ->
  {Bool.and(ok(f, m, ks, img, Fd(2n, m, c), im, fs, nx), ok(f, m, ks, img, Fd(3n, m, c), im, fs, nx)) == True{} : Bool}:
  +t = Tg(m, c)
  or_not(U32.is_eq(t, 10), Bool.and(ok(f, m, ks, img, Fd(2n, m, c), im, fs, nx), ok(f, m, ks, img, Fd(3n, m, c), im, fs, nx)),
    and_r(Bool.and(Bool.and(Cr.Cir.is_cell(c, im, fs, nx), ok.img(t, T.tm.image(img, c))), ok.lab(t, ks, Fd(2n, m, c))),
        Bool.or(Bool.not(U32.is_eq(t, 10)),
          Bool.and(ok(f, m, ks, img, Fd(2n, m, c), im, fs, nx), ok(f, m, ks, img, Fd(3n, m, c), im, fs, nx))), h), e)

# a U32 of the number of n is equal to n
def ion(c: Cmp, +x: Nat, +y: Nat, h: PN.Rel(c, x, y), +e: {x == y : Nat}) -> {Cmp.is_eq(c) == True{} : Bool}:
  match c:
    case LT{}:
      Empty.absurd({Cmp.is_eq(LT{}) == True{} : Bool},
        PN.not_succ_le(x, PN.le_rw_r(1n+x, y, x, Equal.sym(Nat, x, y, e), h)))
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({Cmp.is_eq(GT{}) == True{} : Bool},
        PN.not_succ_le(y, PN.le_rw_r(1n+y, x, y, e, h)))

def nat_eq(+x: U32, +n: U32, +e: {U32.to_nat(x) == U32.to_nat(n) : Nat}) -> {U32.is_eq(x, n) == True{} : Bool}:
  ion(U32.cmp(x, n), U32.to_nat(x), U32.to_nat(n), PN.U32.rel(x, n), e)

# the term of a Maybe, when there is one, has the property K
def SpecM(r: Maybe<&2, Bk.Term>, K: Bk.Term -> Type) -> Type:
  match r:
    case None{}:
      Unit
    case Some{v}:
      K(v)

def SpecM.all(r: Maybe<&2, Bk.Term>, -K: Bk.Term -> Type, h: @v: Bk.Term -> K(v)) -> SpecM(r, K):
  match r:
    case None{}:
      Unit{}
    case Some{v}:
      h(v)

def SpecM.map(r: Maybe<&2, Bk.Term>, -K1: Bk.Term -> Type, -K2: Bk.Term -> Type, h1: SpecM(r, K1), h: @v: Bk.Term -> K1(v) -> K2(v)) -> SpecM(r, K2):
  match r:
    case None{}:
      Unit{}
    case Some{v}:
      h(v, h1)

def SpecM.swap(r: Maybe<&2, Bk.Term>, s: Maybe<&2, Bk.Term>, -K: Bk.Term -> Bk.Term -> Type,
  h: SpecM(s, b => SpecM(r, a => K(a, b)))) -> SpecM(r, a => SpecM(s, b => K(a, b))):
  match r s:
    case None{} _:
      Unit{}
    case Some{a} None{}:
      Unit{}
    case Some{a} Some{b}:
      h

def sp.one(k: Bk.Term -> Bk.Term, r: Maybe<&2, Bk.Term>, -K: Bk.Term -> Type, h: @a: Bk.Term -> K(k(a))) -> SpecM(T.tm.one(k, r), K):
  match r:
    case None{}:
      Unit{}
    case Some{a}:
      h(a)

def sp.two(k: Bk.Term -> Bk.Term -> Bk.Term, r: Maybe<&2, Bk.Term>, s: Maybe<&2, Bk.Term>, -K: Bk.Term -> Type,
  h: @a: Bk.Term -> @b: Bk.Term -> K(k(a, b))) -> SpecM(T.tm.two(k, r, s), K):
  match r s:
    case Some{a} Some{b}:
      h(a, b)
    case Some{a} None{}:
      Unit{}
    case None{} _:
      Unit{}

def sp.three(k: Bk.Term -> Bk.Term -> Bk.Term -> Bk.Term, r: Maybe<&2, Bk.Term>, s: Maybe<&2, Bk.Term>, t: Maybe<&2, Bk.Term>,
  -K: Bk.Term -> Type, h: @a: Bk.Term -> @b: Bk.Term -> @c: Bk.Term -> K(k(a, b, c))) -> SpecM(T.tm.three(k, r, s, t), K):
  match r s t:
    case Some{a} Some{b} Some{c}:
      h(a, b, c)
    case Some{a} Some{b} None{}:
      Unit{}
    case Some{a} None{} _:
      Unit{}
    case None{} _ _:
      Unit{}

def sp.named(n: Maybe<&2, List<&2, Word(8n)>>, k: List<&2, Word(8n)> -> Bk.Term, -K: Bk.Term -> Type, h: @x: List<&2, Word(8n)> -> K(k(x))) ->
  SpecM(T.tm.named(n, k), K):
  match n:
    case None{}:
      Unit{}
    case Some{x}:
      h(x)

def sp.mat(n: Maybe<&2, List<&2, Word(8n)>>, r: Maybe<&2, Bk.Term>, s: Maybe<&2, Bk.Term>, -K: Bk.Term -> Type,
  h: @x: List<&2, Word(8n)> -> @a: Bk.Term -> @b: Bk.Term -> K(Bk.Term.Mat{x, a, b})) -> SpecM(T.tm.mat(n, r, s), K):
  match n r s:
    case Some{x} Some{a} Some{b}:
      h(x, a, b)
    case Some{x} Some{a} None{}:
      Unit{}
    case Some{x} None{} _:
      Unit{}
    case None{} _ _:
      Unit{}

def isnone(m: Maybe<&2, TP>, +e: {Maybe.is_none(&2, TP, m) == True{} : Bool}) -> {m == None{} : Maybe<&2, TP>}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      Empty.absurd({Some{x} == None{} : Maybe<&2, TP>}, PN.false_ne_true(e))

def isnoneL(m: Maybe<&2, List<&2, Word(8n)>>, +e: {Maybe.is_none(&2, List<&2, Word(8n)>, m) == True{} : Bool}) -> {m == None{} : Maybe<&2, List<&2, Word(8n)>>}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      Empty.absurd({Some{x} == None{} : Maybe<&2, List<&2, Word(8n)>>}, PN.false_ne_true(e))

# an image's term that is no pair at quantity 1
def sp.imgT(r: Maybe<&2, Bk.Term>, -K: Bk.Term -> Type, +e: {Bool.and(noT1(r), noL(r)) == True{} : Bool},
  h: @v: Bk.Term -> {V1(v) == None{} : Maybe<&2, TP>} -> K(v)) -> SpecM(r, K):
  match r:
    case None{}:
      Unit{}
    case Some{+v}:
      h(v, isnone(V1(v), and_l(Maybe.is_none(&2, TP, V1(v)), Maybe.is_none(&2, List<&2, Word(8n)>, VL(v)), e)))

def sp.imgL(r: Maybe<&2, Bk.Term>, -K: Bk.Term -> Type, +e: {Bool.and(noT1(r), noL(r)) == True{} : Bool},
  h: @v: Bk.Term -> {VL(v) == None{} : Maybe<&2, List<&2, Word(8n)>>} -> K(v)) -> SpecM(r, K):
  match r:
    case None{}:
      Unit{}
    case Some{+v}:
      h(v, isnoneL(VL(v), and_r(Maybe.is_none(&2, TP, V1(v)), Maybe.is_none(&2, List<&2, Word(8n)>, VL(v)), e)))

def or_true_r(a: Bool) -> {Bool.or(a, True{}) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# the goal of a cell's term, by its tag and quantity
def CG(tag: Nat, +q: Bk.Quan, +f: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32,
  K: Bk.Term -> Type) -> Type:
  SpecM(T.tm.cell(tag, q, c, Fd(2n, m, c), ks, img, u => T.tm.of(f, m, ks, img, Fd(2n, m, c)),
    u => T.tm.of(f, m, ks, img, Fd(3n, m, c)), u => T.tm.of(f, m, ks, img, Fd(4n, m, c))), K)

def or_l_true(a: Bool, b: Bool, +e: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({Bool.or(False{}, b) == True{} : Bool}, PN.false_ne_true(e))

def or_r_true(a: Bool, b: Bool, +e: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      e

def sp.two2(k: Bk.Term -> Bk.Term -> Bk.Term, r: Maybe<&2, Bk.Term>, s: Maybe<&2, Bk.Term>, -K: Bk.Term -> Type,
  h: SpecM(r, a => SpecM(s, b => K(k(a, b))))) -> SpecM(T.tm.two(k, r, s), K):
  match r s:
    case Some{a} Some{b}:
      h
    case Some{a} None{}:
      Unit{}
    case None{} _:
      Unit{}

def sp.namedE(n: Maybe<&2, List<&2, Word(8n)>>, -K: Bk.Term -> Type, h: @k: List<&2, Word(8n)> -> {n == Some{k} : Maybe<&2, List<&2, Word(8n)>>} -> K(Bk.Term.Lab{k})) ->
  SpecM(T.tm.named(n, k => Bk.Term.Lab{k}), K):
  match n:
    case None{}:
      Unit{}
    case Some{+k}:
      h(k, {==})

def cellT1.go(tag: Nat, q: Bk.Quan, +f: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32,
  -K: Bk.Term -> Type, +et: {10n == tag : Nat}, +eq: {isQ1(q) == True{} : Bool},
  h: SpecM(T.tm.of(f, m, ks, img, Fd(2n, m, c)), a => SpecM(T.tm.of(f, m, ks, img, Fd(3n, m, c)), b => K(Bk.Term.Tup{Bk.Quan.Q1{}, a, b})))) ->
  CG(tag, q, f, m, ks, img, c, K):
  match q:
    case Bk.Quan.Q1{}:
      %et : CG(_, Bk.Quan.Q1{}, f, m, ks, img, c, K)
      sp.two2(a => b => Bk.Term.Tup{Bk.Quan.Q1{}, a, b}, T.tm.of(f, m, ks, img, Fd(2n, m, c)), T.tm.of(f, m, ks, img, Fd(3n, m, c)), K, h)
    case Bk.Quan.Q0{}:
      Empty.absurd(CG(tag, Bk.Quan.Q0{}, f, m, ks, img, c, K), PN.false_ne_true(eq))
    case Bk.Quan.Q2{}:
      Empty.absurd(CG(tag, Bk.Quan.Q2{}, f, m, ks, img, c, K), PN.false_ne_true(eq))

# the term of a cell that M.pair accepts is a pair at quantity 1 of the terms
# of its fields 2 and 3
def cellT1(+f: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, -K: Bk.Term -> Type,
  +eP: {Pm(m, c) == True{} : Bool},
  h: SpecM(T.tm.of(f, m, ks, img, Fd(2n, m, c)), a => SpecM(T.tm.of(f, m, ks, img, Fd(3n, m, c)), b => K(Bk.Term.Tup{Bk.Quan.Q1{}, a, b})))) ->
  SpecM(T.tm.of(1n+f, m, ks, img, c), K):
  +f0 = Fd(0n, m, c)
  +q = T.tm.quan(U32.and(U32.shrn(f0, 6n), 3))
  +fr = Equal.trans(Bool, FP.r(f0), FP.l(f0), True{}, Equal.sym(Bool, FP.l(f0), FP.r(f0), fp(f0)), eP)
  +e10 = and_r(isQ1(q), U32.is_eq(U32.and(f0, 63), 10), fr)
  cellT1.go(U32.to_nat(U32.and(f0, 63)), q, f, m, ks, img, c, K,
    Equal.sym(Nat, U32.to_nat(U32.and(f0, 63)), 10n, eq_nat(U32.and(f0, 63), 10, e10)),
    and_l(isQ1(q), U32.is_eq(U32.and(f0, 63), 10), fr), h)

def cellLab.go(tag: Nat, +q: Bk.Quan, +f: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32,
  -K: Bk.Term -> Type, +et: {13n == tag : Nat},
  h: @k: List<&2, Word(8n)> -> {T.tm.name(ks, Fd(2n, m, c)) == Some{k} : Maybe<&2, List<&2, Word(8n)>>} -> K(Bk.Term.Lab{k})) ->
  CG(tag, q, f, m, ks, img, c, K):
  %et : CG(_, q, f, m, ks, img, c, K)
  sp.namedE(T.tm.name(ks, Fd(2n, m, c)), K, h)

# the term of a label cell is the label of the name of its number
def cellLab(+f: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, -K: Bk.Term -> Type,
  +eL: {Lm(m, c) == True{} : Bool},
  h: @k: List<&2, Word(8n)> -> {T.tm.name(ks, Fd(2n, m, c)) == Some{k} : Maybe<&2, List<&2, Word(8n)>>} -> K(Bk.Term.Lab{k})) ->
  SpecM(T.tm.of(1n+f, m, ks, img, c), K):
  +f0 = Fd(0n, m, c)
  cellLab.go(U32.to_nat(U32.and(f0, 63)), T.tm.quan(U32.and(U32.shrn(f0, 6n), 3)), f, m, ks, img, c, K,
    Equal.sym(Nat, U32.to_nat(U32.and(f0, 63)), 13n, eq_nat(U32.and(f0, 63), 13, eL)), h)

def cellNotT1.go(tag: Nat, +q: Bk.Quan, +f: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32, -K: Bk.Term -> Type, +et: {U32.to_nat(Tg(m, c)) == tag : Nat},
  +eF: {Bool.and(isQ1(q), U32.is_eq(Tg(m, c), 10)) == False{} : Bool}, +hok: {ok(1n+f, m, ks, img, c, im, fs, nx) == True{} : Bool},
  h: @v: Bk.Term -> {V1(v) == None{} : Maybe<&2, TP>} -> K(v)) -> CG(tag, q, f, m, ks, img, c, K):
  match tag:
    case 0n:
      h(Bk.Term.Var{U32.to_nat(Fd(2n, m, c))}, {==})
    case 1n+t1:
      match t1:
        case 0n:
          sp.imgT(T.tm.image(img, c), K, ok.im(f, m, ks, img, c, im, fs, nx, hok, or_l_true(U32.is_eq(Tg(m, c), 1), U32.is_eq(Tg(m, c), 12), nat_eq(Tg(m, c), 1, et))), h)
        case 1n+t2:
          match t2:
            case 0n:
              sp.two(a => b => Bk.Term.Ann{a, b}, T.tm.of(f, m, ks, img, Fd(2n, m, c)), T.tm.of(f, m, ks, img, Fd(3n, m, c)), K, a => b => h(Bk.Term.Ann{a, b}, {==}))
            case 1n+t3:
              match t3:
                case 0n:
                  sp.two(a => b => Bk.Term.Let{q, a, b}, T.tm.of(f, m, ks, img, Fd(2n, m, c)), T.tm.of(f, m, ks, img, Fd(3n, m, c)), K, a => b => h(Bk.Term.Let{q, a, b}, {==}))
                case 1n+t4:
                  match t4:
                    case 0n:
                      sp.one(a => Bk.Term.Typ{a}, T.tm.of(f, m, ks, img, Fd(2n, m, c)), K, a => h(Bk.Term.Typ{a}, {==}))
                    case 1n+t5:
                      match t5:
                        case 0n:
                          sp.two(a => b => Bk.Term.Min{a, b}, T.tm.of(f, m, ks, img, Fd(2n, m, c)), T.tm.of(f, m, ks, img, Fd(3n, m, c)), K, a => b => h(Bk.Term.Min{a, b}, {==}))
                        case 1n+t6:
                          match t6:
                            case 0n:
                              sp.two(a => b => Bk.Term.All{q, a, b}, T.tm.of(f, m, ks, img, Fd(2n, m, c)), T.tm.of(f, m, ks, img, Fd(3n, m, c)), K, a => b => h(Bk.Term.All{q, a, b}, {==}))
                            case 1n+t7:
                              match t7:
                                case 0n:
                                  sp.one(a => Bk.Term.Lam{q, a}, T.tm.of(f, m, ks, img, Fd(2n, m, c)), K, a => h(Bk.Term.Lam{q, a}, {==}))
                                case 1n+t8:
                                  match t8:
                                    case 0n:
                                      sp.two(a => b => Bk.Term.App{q, a, b}, T.tm.of(f, m, ks, img, Fd(2n, m, c)), T.tm.of(f, m, ks, img, Fd(3n, m, c)), K, a => b => h(Bk.Term.App{q, a, b}, {==}))
                                    case 1n+t9:
                                      match t9:
                                        case 0n:
                                          sp.two(a => b => Bk.Term.Sig{q, a, b}, T.tm.of(f, m, ks, img, Fd(2n, m, c)), T.tm.of(f, m, ks, img, Fd(3n, m, c)), K, a => b => h(Bk.Term.Sig{q, a, b}, {==}))
                                        case 1n+t10:
                                          match t10:
                                            case 0n:
                                              match q:
                                                case Bk.Quan.Q0{}:
                                                  sp.two(a => b => Bk.Term.Tup{Bk.Quan.Q0{}, a, b}, T.tm.of(f, m, ks, img, Fd(2n, m, c)), T.tm.of(f, m, ks, img, Fd(3n, m, c)), K, a => b => h(Bk.Term.Tup{Bk.Quan.Q0{}, a, b}, {==}))
                                                case Bk.Quan.Q2{}:
                                                  sp.two(a => b => Bk.Term.Tup{Bk.Quan.Q2{}, a, b}, T.tm.of(f, m, ks, img, Fd(2n, m, c)), T.tm.of(f, m, ks, img, Fd(3n, m, c)), K, a => b => h(Bk.Term.Tup{Bk.Quan.Q2{}, a, b}, {==}))
                                                case Bk.Quan.Q1{}:
                                                  Empty.absurd(CG(10n, Bk.Quan.Q1{}, f, m, ks, img, c, K), PN.true_ne_false(Equal.trans(Bool, True{}, U32.is_eq(Tg(m, c), 10), False{}, Equal.sym(Bool, U32.is_eq(Tg(m, c), 10), True{}, nat_eq(Tg(m, c), 10, et)), eF)))
                                            case 1n+t11:
                                              match t11:
                                                case 0n:
                                                  sp.one(a => Bk.Term.Prj{a}, T.tm.of(f, m, ks, img, Fd(2n, m, c)), K, a => h(Bk.Term.Prj{a}, {==}))
                                                case 1n+t12:
                                                  match t12:
                                                    case 0n:
                                                      sp.imgT(T.tm.image(img, c), K, ok.im(f, m, ks, img, c, im, fs, nx, hok, or_r_true(U32.is_eq(Tg(m, c), 1), U32.is_eq(Tg(m, c), 12), nat_eq(Tg(m, c), 12, et))), h)
                                                    case 1n+t13:
                                                      match t13:
                                                        case 0n:
                                                          sp.named(T.tm.name(ks, Fd(2n, m, c)), k => Bk.Term.Lab{k}, K, x => h(Bk.Term.Lab{x}, {==}))
                                                        case 1n+t14:
                                                          match t14:
                                                            case 0n:
                                                              sp.mat(T.tm.name(ks, Fd(2n, m, c)), T.tm.of(f, m, ks, img, Fd(3n, m, c)), T.tm.of(f, m, ks, img, Fd(4n, m, c)), K, x => a => b => h(Bk.Term.Mat{x, a, b}, {==}))
                                                            case 1n+t15:
                                                              match t15:
                                                                case 0n:
                                                                  h(Bk.Term.Efq{}, {==})
                                                                case 1n+t16:
                                                                  match t16:
                                                                    case 0n:
                                                                      sp.three(a => b => d => Bk.Term.Eql{a, b, d}, T.tm.of(f, m, ks, img, Fd(2n, m, c)), T.tm.of(f, m, ks, img, Fd(3n, m, c)), T.tm.of(f, m, ks, img, Fd(4n, m, c)), K, a => b => d => h(Bk.Term.Eql{a, b, d}, {==}))
                                                                    case 1n+t17:
                                                                      match t17:
                                                                        case 0n:
                                                                          h(Bk.Term.Rfl{}, {==})
                                                                        case 1n+t18:
                                                                          match t18:
                                                                            case 0n:
                                                                              sp.three(a => b => d => Bk.Term.Rwt{a, b, d}, T.tm.of(f, m, ks, img, Fd(2n, m, c)), T.tm.of(f, m, ks, img, Fd(3n, m, c)), T.tm.of(f, m, ks, img, Fd(4n, m, c)), K, a => b => d => h(Bk.Term.Rwt{a, b, d}, {==}))
                                                                            case 1n+t19:
                                                                              Unit{}

def cellNotL.go(tag: Nat, +q: Bk.Quan, +f: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32, -K: Bk.Term -> Type, +et: {U32.to_nat(Tg(m, c)) == tag : Nat},
  +eF: {U32.is_eq(Tg(m, c), 13) == False{} : Bool}, +hok: {ok(1n+f, m, ks, img, c, im, fs, nx) == True{} : Bool},
  h: @v: Bk.Term -> {VL(v) == None{} : Maybe<&2, List<&2, Word(8n)>>} -> K(v)) -> CG(tag, q, f, m, ks, img, c, K):
  match tag:
    case 0n:
      h(Bk.Term.Var{U32.to_nat(Fd(2n, m, c))}, {==})
    case 1n+t1:
      match t1:
        case 0n:
          sp.imgL(T.tm.image(img, c), K, ok.im(f, m, ks, img, c, im, fs, nx, hok, or_l_true(U32.is_eq(Tg(m, c), 1), U32.is_eq(Tg(m, c), 12), nat_eq(Tg(m, c), 1, et))), h)
        case 1n+t2:
          match t2:
            case 0n:
              sp.two(a => b => Bk.Term.Ann{a, b}, T.tm.of(f, m, ks, img, Fd(2n, m, c)), T.tm.of(f, m, ks, img, Fd(3n, m, c)), K, a => b => h(Bk.Term.Ann{a, b}, {==}))
            case 1n+t3:
              match t3:
                case 0n:
                  sp.two(a => b => Bk.Term.Let{q, a, b}, T.tm.of(f, m, ks, img, Fd(2n, m, c)), T.tm.of(f, m, ks, img, Fd(3n, m, c)), K, a => b => h(Bk.Term.Let{q, a, b}, {==}))
                case 1n+t4:
                  match t4:
                    case 0n:
                      sp.one(a => Bk.Term.Typ{a}, T.tm.of(f, m, ks, img, Fd(2n, m, c)), K, a => h(Bk.Term.Typ{a}, {==}))
                    case 1n+t5:
                      match t5:
                        case 0n:
                          sp.two(a => b => Bk.Term.Min{a, b}, T.tm.of(f, m, ks, img, Fd(2n, m, c)), T.tm.of(f, m, ks, img, Fd(3n, m, c)), K, a => b => h(Bk.Term.Min{a, b}, {==}))
                        case 1n+t6:
                          match t6:
                            case 0n:
                              sp.two(a => b => Bk.Term.All{q, a, b}, T.tm.of(f, m, ks, img, Fd(2n, m, c)), T.tm.of(f, m, ks, img, Fd(3n, m, c)), K, a => b => h(Bk.Term.All{q, a, b}, {==}))
                            case 1n+t7:
                              match t7:
                                case 0n:
                                  sp.one(a => Bk.Term.Lam{q, a}, T.tm.of(f, m, ks, img, Fd(2n, m, c)), K, a => h(Bk.Term.Lam{q, a}, {==}))
                                case 1n+t8:
                                  match t8:
                                    case 0n:
                                      sp.two(a => b => Bk.Term.App{q, a, b}, T.tm.of(f, m, ks, img, Fd(2n, m, c)), T.tm.of(f, m, ks, img, Fd(3n, m, c)), K, a => b => h(Bk.Term.App{q, a, b}, {==}))
                                    case 1n+t9:
                                      match t9:
                                        case 0n:
                                          sp.two(a => b => Bk.Term.Sig{q, a, b}, T.tm.of(f, m, ks, img, Fd(2n, m, c)), T.tm.of(f, m, ks, img, Fd(3n, m, c)), K, a => b => h(Bk.Term.Sig{q, a, b}, {==}))
                                        case 1n+t10:
                                          match t10:
                                            case 0n:
                                              sp.two(a => b => Bk.Term.Tup{q, a, b}, T.tm.of(f, m, ks, img, Fd(2n, m, c)), T.tm.of(f, m, ks, img, Fd(3n, m, c)), K, a => b => h(Bk.Term.Tup{q, a, b}, {==}))
                                            case 1n+t11:
                                              match t11:
                                                case 0n:
                                                  sp.one(a => Bk.Term.Prj{a}, T.tm.of(f, m, ks, img, Fd(2n, m, c)), K, a => h(Bk.Term.Prj{a}, {==}))
                                                case 1n+t12:
                                                  match t12:
                                                    case 0n:
                                                      sp.imgL(T.tm.image(img, c), K, ok.im(f, m, ks, img, c, im, fs, nx, hok, or_r_true(U32.is_eq(Tg(m, c), 1), U32.is_eq(Tg(m, c), 12), nat_eq(Tg(m, c), 12, et))), h)
                                                    case 1n+t13:
                                                      match t13:
                                                        case 0n:
                                                          Empty.absurd(CG(13n, q, f, m, ks, img, c, K), PN.true_ne_false(Equal.trans(Bool, True{}, U32.is_eq(Tg(m, c), 13), False{}, Equal.sym(Bool, U32.is_eq(Tg(m, c), 13), True{}, nat_eq(Tg(m, c), 13, et)), eF)))
                                                        case 1n+t14:
                                                          match t14:
                                                            case 0n:
                                                              sp.mat(T.tm.name(ks, Fd(2n, m, c)), T.tm.of(f, m, ks, img, Fd(3n, m, c)), T.tm.of(f, m, ks, img, Fd(4n, m, c)), K, x => a => b => h(Bk.Term.Mat{x, a, b}, {==}))
                                                            case 1n+t15:
                                                              match t15:
                                                                case 0n:
                                                                  h(Bk.Term.Efq{}, {==})
                                                                case 1n+t16:
                                                                  match t16:
                                                                    case 0n:
                                                                      sp.three(a => b => d => Bk.Term.Eql{a, b, d}, T.tm.of(f, m, ks, img, Fd(2n, m, c)), T.tm.of(f, m, ks, img, Fd(3n, m, c)), T.tm.of(f, m, ks, img, Fd(4n, m, c)), K, a => b => d => h(Bk.Term.Eql{a, b, d}, {==}))
                                                                    case 1n+t17:
                                                                      match t17:
                                                                        case 0n:
                                                                          h(Bk.Term.Rfl{}, {==})
                                                                        case 1n+t18:
                                                                          match t18:
                                                                            case 0n:
                                                                              sp.three(a => b => d => Bk.Term.Rwt{a, b, d}, T.tm.of(f, m, ks, img, Fd(2n, m, c)), T.tm.of(f, m, ks, img, Fd(3n, m, c)), T.tm.of(f, m, ks, img, Fd(4n, m, c)), K, a => b => d => h(Bk.Term.Rwt{a, b, d}, {==}))
                                                                            case 1n+t19:
                                                                              Unit{}
# the term of a cell that M.pair rejects is no pair at quantity 1
def cellNotT1(+f: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32,
  -K: Bk.Term -> Type, +eP: {Pm(m, c) == False{} : Bool}, +hok: {ok(1n+f, m, ks, img, c, im, fs, nx) == True{} : Bool},
  h: @v: Bk.Term -> {V1(v) == None{} : Maybe<&2, TP>} -> K(v)) -> SpecM(T.tm.of(1n+f, m, ks, img, c), K):
  +f0 = Fd(0n, m, c)
  cellNotT1.go(U32.to_nat(U32.and(f0, 63)), T.tm.quan(U32.and(U32.shrn(f0, 6n), 3)), f, m, ks, img, c, im, fs, nx, K, {==},
    Equal.trans(Bool, FP.r(f0), FP.l(f0), False{}, Equal.sym(Bool, FP.l(f0), FP.r(f0), fp(f0)), eP), hok, h)

# the term of a cell whose tag is not 13 is no label
def cellNotL(+f: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32,
  -K: Bk.Term -> Type, +eL: {Lm(m, c) == False{} : Bool}, +hok: {ok(1n+f, m, ks, img, c, im, fs, nx) == True{} : Bool},
  h: @v: Bk.Term -> {VL(v) == None{} : Maybe<&2, List<&2, Word(8n)>>} -> K(v)) -> SpecM(T.tm.of(1n+f, m, ks, img, c), K):
  +f0 = Fd(0n, m, c)
  cellNotL.go(U32.to_nat(U32.and(f0, 63)), T.tm.quan(U32.and(U32.shrn(f0, 6n), 3)), f, m, ks, img, c, im, fs, nx, K, {==}, eL, hok, h)

# The cells, read as the machine reads them
# -----------------------------------------
#
# CB, CW and Step read the cells by the machine's tests, in its order; CU
# reads a list. They take each test's value as a Bool: Pm (M.pair), Lm (a
# label's tag), LAST (M.last), ISLAB (M.is_lab).

# a bit: Some of whether its name is True (number 5)
def CB.t(b: Bool, x6: Bool) -> Maybe<&2, Bool>:
  match b:
    case True{}:
      Some{x6}
    case False{}:
      None{}

def CB.x(b: Bool, +t2: U32) -> Maybe<&2, Bool>:
  match b:
    case True{}:
      CB.t(Bool.or(U32.is_eq(t2, 5), U32.is_eq(t2, 6)), U32.is_eq(t2, 5))
    case False{}:
      None{}

def CB.l(b: Bool, +m: Cr.Cir.Cells, +c: U32) -> Maybe<&2, Bool>:
  match b:
    case True{}:
      CB.x(Lm(m, Fd(2n, m, c)), Fd(2n, m, Fd(2n, m, c)))
    case False{}:
      None{}

def CB.p(b: Bool, +m: Cr.Cir.Cells, +c: U32) -> Maybe<&2, Bool>:
  match b:
    case True{}:
      CB.l(LAST(m, c), m, c)
    case False{}:
      None{}

def CB(+m: Cr.Cir.Cells, +c: U32) -> Maybe<&2, Bool>:
  CB.p(Pm(m, c), m, c)

# a word of n bits
def CW0.z(b: Bool) -> Maybe<&2, Word(0n)>:
  match b:
    case True{}:
      Some{WNil{}}
    case False{}:
      None{}

def CW0.l(b: Bool, +m: Cr.Cir.Cells, +c: U32) -> Maybe<&2, Word(0n)>:
  match b:
    case True{}:
      CW0.z(LAST(m, c))
    case False{}:
      None{}

def CW0.p(b: Bool, +m: Cr.Cir.Cells, +c: U32) -> Maybe<&2, Word(0n)>:
  match b:
    case True{}:
      CW0.l(ISLAB(m, c, 3), m, c)
    case False{}:
      None{}

# a bit of a word, the cell c holding WCon: Some of its bit when the cells
# have the form that the machine reads
def GB.z(x: Bool, b: Bool) -> Maybe<&2, Bool>:
  match b:
    case True{}:
      Some{x}
    case False{}:
      None{}

def GB.r(x: Bool, b: Bool, +m: Cr.Cir.Cells, +rc: U32) -> Maybe<&2, Bool>:
  match b:
    case True{}:
      GB.z(x, LAST(m, rc))
    case False{}:
      None{}

def GB.b(mb: Maybe<&2, Bool>, +m: Cr.Cir.Cells, +rc: U32) -> Maybe<&2, Bool>:
  match mb:
    case Some{x}:
      GB.r(x, Pm(m, rc), m, rc)
    case None{}:
      None{}

def GB.f(b: Bool, +m: Cr.Cir.Cells, +fc: U32) -> Maybe<&2, Bool>:
  match b:
    case True{}:
      GB.b(CB(m, Fd(2n, m, fc)), m, Fd(3n, m, fc))
    case False{}:
      None{}

def GB.l(b: Bool, +m: Cr.Cir.Cells, +fc: U32) -> Maybe<&2, Bool>:
  match b:
    case True{}:
      GB.f(Pm(m, fc), m, fc)
    case False{}:
      None{}

def GB.p(b: Bool, +m: Cr.Cir.Cells, +c: U32) -> Maybe<&2, Bool>:
  match b:
    case True{}:
      GB.l(ISLAB(m, c, 4), m, Fd(3n, m, c))
    case False{}:
      None{}

def GB(+m: Cr.Cir.Cells, +c: U32) -> Maybe<&2, Bool>:
  GB.p(Pm(m, c), m, c)

# the bit g, below the word rec
def W1.g(-q: Nat, g: Maybe<&2, Bool>, rec: Maybe<&2, Word(q)>) -> Maybe<&2, Word(1n+q)>:
  match g:
    case Some{x}:
      W1.w(q, x, rec)
    case None{}:
      None{}

# the cell of the word after the word of the cell c
def CW.next(+m: Cr.Cir.Cells, +c: U32) -> U32:
  Fd(2n, m, Fd(3n, m, Fd(3n, m, c)))

def CW(p: Nat, +m: Cr.Cir.Cells, +c: U32) -> Maybe<&2, Word(p)>:
  match p:
    case 0n:
      CW0.p(Pm(m, c), m, c)
    case 1n+q:
      W1.g(q, GB(m, c), CW(q, m, CW.next(m, c)))

# the p bits of the word of the cell c, with no WNil after them
def CWb(p: Nat, +m: Cr.Cir.Cells, +c: U32) -> Maybe<&2, Word(p)>:
  match p:
    case 0n:
      Some{WNil{}}
    case 1n+q:
      W1.g(q, GB(m, c), CWb(q, m, CW.next(m, c)))

# the cell after p bits of the word of the cell c
def Nx(p: Nat, +m: Cr.Cir.Cells, +c: U32) -> U32:
  match p:
    case 0n:
      c
    case 1n+q:
      Nx(q, m, CW.next(m, c))

# the word r, when the end t is there
def CWt(-p: Nat, r: Maybe<&2, Word(p)>, t: Maybe<&2, Word(0n)>) -> Maybe<&2, Word(p)>:
  match r t:
    case Some{w} Some{_}:
      Some{w}
    case _ _:
      None{}

# a step of the list: its end, with its result, or a byte and the cell of
# the rest
type SR is Data:
  SR.done{r: Maybe<&2, List<&2, Word(8n)>>}
  SR.more{v: Word(8n), rest: U32}

def S.c3(mw: Maybe<&2, Word(8n)>, +restc: U32) -> SR:
  match mw:
    case Some{x}:
      SR.more{x, restc}
    case None{}:
      SR.done{None{}}

def S.c2(b: Bool, +m: Cr.Cir.Cells, +xc: U32, +restc: U32) -> SR:
  match b:
    case True{}:
      S.c3(CW(8n, m, xc), restc)
    case False{}:
      SR.done{None{}}

def S.c1(b: Bool, +m: Cr.Cir.Cells, +xc: U32, +yc: U32) -> SR:
  match b:
    case True{}:
      S.c2(LAST(m, yc), m, xc, Fd(2n, m, yc))
    case False{}:
      SR.done{None{}}

def S.c0(b: Bool, +m: Cr.Cir.Cells, +bc: U32) -> SR:
  match b:
    case True{}:
      S.c1(Pm(m, Fd(3n, m, bc)), m, Fd(2n, m, bc), Fd(3n, m, bc))
    case False{}:
      SR.done{None{}}

def S.k2(iscon: Bool, +m: Cr.Cir.Cells, +bc: U32) -> SR:
  match iscon:
    case True{}:
      S.c0(Pm(m, bc), m, bc)
    case False{}:
      SR.done{None{}}

def S.nil(b: Bool) -> SR:
  match b:
    case True{}:
      SR.done{Some{Nil{}}}
    case False{}:
      SR.done{None{}}

def S.w(isnil: Bool, iscon: Bool, +m: Cr.Cir.Cells, +c: U32) -> SR:
  match isnil:
    case True{}:
      S.nil(LAST(m, c))
    case False{}:
      S.k2(iscon, m, Fd(3n, m, c))

def S.l(b: Bool, +m: Cr.Cir.Cells, +c: U32) -> SR:
  match b:
    case True{}:
      S.w(U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 1), U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 2), m, c)
    case False{}:
      SR.done{None{}}

def S.p(b: Bool, +m: Cr.Cir.Cells, +c: U32) -> SR:
  match b:
    case True{}:
      S.l(Lm(m, Fd(2n, m, c)), m, c)
    case False{}:
      SR.done{None{}}

def Step(+m: Cr.Cir.Cells, +c: U32) -> SR:
  S.p(Pm(m, c), m, c)

# the list from a step, with fuel levels as T.tm.of reads them: its rest is
# 3 levels below its cell
def CU.d(s: SR) -> Maybe<&2, List<&2, Word(8n)>>:
  match s:
    case SR.done{r}:
      r
    case SR.more{v, rest}:
      None{}

def CU(n: Nat, +m: Cr.Cir.Cells, s: SR) -> Maybe<&2, List<&2, Word(8n)>>:
  match n:
    case 0n:
      None{}
    case 1n+a:
      match a:
        case 0n:
          CU.d(s)
        case 1n+b:
          match b:
            case 0n:
              CU.d(s)
            case 1n+d:
              match s:
                case SR.done{r}:
                  r
                case SR.more{v, rest}:
                  U.c5(v, CU(d, m, Step(m, rest)))

# the names of the machine's numbers 0 to 6 compare as their numbers
def kn0(+j: U32, +b: List<&2, Word(8n)>, +h: {known.ok(j, b) == True{} : Bool}) ->
  {Sd.Name.is_eq(b, Pg.Program.name.unit()) == U32.is_eq(j, 0) : Bool}:
  iff_eq(Sd.Name.is_eq(b, Pg.Program.name.unit()), U32.is_eq(j, 0), and_l(iff(Sd.Name.is_eq(b, Pg.Program.name.unit()), U32.is_eq(j, 0)), iff(Sd.Name.is_eq(b, Pg.Program.name.nil()), U32.is_eq(j, 1)), and_l(Bool.and(iff(Sd.Name.is_eq(b, Pg.Program.name.unit()), U32.is_eq(j, 0)), iff(Sd.Name.is_eq(b, Pg.Program.name.nil()), U32.is_eq(j, 1))), iff(Sd.Name.is_eq(b, Pg.Program.name.con()), U32.is_eq(j, 2)), and_l(Bool.and(Bool.and(iff(Sd.Name.is_eq(b, Pg.Program.name.unit()), U32.is_eq(j, 0)), iff(Sd.Name.is_eq(b, Pg.Program.name.nil()), U32.is_eq(j, 1))), iff(Sd.Name.is_eq(b, Pg.Program.name.con()), U32.is_eq(j, 2))), iff(Sd.Name.is_eq(b, Pg.Program.name.wnil()), U32.is_eq(j, 3)), and_l(Bool.and(Bool.and(Bool.and(iff(Sd.Name.is_eq(b, Pg.Program.name.unit()), U32.is_eq(j, 0)), iff(Sd.Name.is_eq(b, Pg.Program.name.nil()), U32.is_eq(j, 1))), iff(Sd.Name.is_eq(b, Pg.Program.name.con()), U32.is_eq(j, 2))), iff(Sd.Name.is_eq(b, Pg.Program.name.wnil()), U32.is_eq(j, 3))), iff(Sd.Name.is_eq(b, Pg.Program.name.wcon()), U32.is_eq(j, 4)), and_l(Bool.and(Bool.and(Bool.and(Bool.and(iff(Sd.Name.is_eq(b, Pg.Program.name.unit()), U32.is_eq(j, 0)), iff(Sd.Name.is_eq(b, Pg.Program.name.nil()), U32.is_eq(j, 1))), iff(Sd.Name.is_eq(b, Pg.Program.name.con()), U32.is_eq(j, 2))), iff(Sd.Name.is_eq(b, Pg.Program.name.wnil()), U32.is_eq(j, 3))), iff(Sd.Name.is_eq(b, Pg.Program.name.wcon()), U32.is_eq(j, 4))), iff(Sd.Name.is_eq(b, Pg.Program.name.true()), U32.is_eq(j, 5)), and_l(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(iff(Sd.Name.is_eq(b, Pg.Program.name.unit()), U32.is_eq(j, 0)), iff(Sd.Name.is_eq(b, Pg.Program.name.nil()), U32.is_eq(j, 1))), iff(Sd.Name.is_eq(b, Pg.Program.name.con()), U32.is_eq(j, 2))), iff(Sd.Name.is_eq(b, Pg.Program.name.wnil()), U32.is_eq(j, 3))), iff(Sd.Name.is_eq(b, Pg.Program.name.wcon()), U32.is_eq(j, 4))), iff(Sd.Name.is_eq(b, Pg.Program.name.true()), U32.is_eq(j, 5))), iff(Sd.Name.is_eq(b, Pg.Program.name.false()), U32.is_eq(j, 6)), h)))))))

def kn1(+j: U32, +b: List<&2, Word(8n)>, +h: {known.ok(j, b) == True{} : Bool}) ->
  {Sd.Name.is_eq(b, Pg.Program.name.nil()) == U32.is_eq(j, 1) : Bool}:
  iff_eq(Sd.Name.is_eq(b, Pg.Program.name.nil()), U32.is_eq(j, 1), and_r(iff(Sd.Name.is_eq(b, Pg.Program.name.unit()), U32.is_eq(j, 0)), iff(Sd.Name.is_eq(b, Pg.Program.name.nil()), U32.is_eq(j, 1)), and_l(Bool.and(iff(Sd.Name.is_eq(b, Pg.Program.name.unit()), U32.is_eq(j, 0)), iff(Sd.Name.is_eq(b, Pg.Program.name.nil()), U32.is_eq(j, 1))), iff(Sd.Name.is_eq(b, Pg.Program.name.con()), U32.is_eq(j, 2)), and_l(Bool.and(Bool.and(iff(Sd.Name.is_eq(b, Pg.Program.name.unit()), U32.is_eq(j, 0)), iff(Sd.Name.is_eq(b, Pg.Program.name.nil()), U32.is_eq(j, 1))), iff(Sd.Name.is_eq(b, Pg.Program.name.con()), U32.is_eq(j, 2))), iff(Sd.Name.is_eq(b, Pg.Program.name.wnil()), U32.is_eq(j, 3)), and_l(Bool.and(Bool.and(Bool.and(iff(Sd.Name.is_eq(b, Pg.Program.name.unit()), U32.is_eq(j, 0)), iff(Sd.Name.is_eq(b, Pg.Program.name.nil()), U32.is_eq(j, 1))), iff(Sd.Name.is_eq(b, Pg.Program.name.con()), U32.is_eq(j, 2))), iff(Sd.Name.is_eq(b, Pg.Program.name.wnil()), U32.is_eq(j, 3))), iff(Sd.Name.is_eq(b, Pg.Program.name.wcon()), U32.is_eq(j, 4)), and_l(Bool.and(Bool.and(Bool.and(Bool.and(iff(Sd.Name.is_eq(b, Pg.Program.name.unit()), U32.is_eq(j, 0)), iff(Sd.Name.is_eq(b, Pg.Program.name.nil()), U32.is_eq(j, 1))), iff(Sd.Name.is_eq(b, Pg.Program.name.con()), U32.is_eq(j, 2))), iff(Sd.Name.is_eq(b, Pg.Program.name.wnil()), U32.is_eq(j, 3))), iff(Sd.Name.is_eq(b, Pg.Program.name.wcon()), U32.is_eq(j, 4))), iff(Sd.Name.is_eq(b, Pg.Program.name.true()), U32.is_eq(j, 5)), and_l(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(iff(Sd.Name.is_eq(b, Pg.Program.name.unit()), U32.is_eq(j, 0)), iff(Sd.Name.is_eq(b, Pg.Program.name.nil()), U32.is_eq(j, 1))), iff(Sd.Name.is_eq(b, Pg.Program.name.con()), U32.is_eq(j, 2))), iff(Sd.Name.is_eq(b, Pg.Program.name.wnil()), U32.is_eq(j, 3))), iff(Sd.Name.is_eq(b, Pg.Program.name.wcon()), U32.is_eq(j, 4))), iff(Sd.Name.is_eq(b, Pg.Program.name.true()), U32.is_eq(j, 5))), iff(Sd.Name.is_eq(b, Pg.Program.name.false()), U32.is_eq(j, 6)), h)))))))

def kn2(+j: U32, +b: List<&2, Word(8n)>, +h: {known.ok(j, b) == True{} : Bool}) ->
  {Sd.Name.is_eq(b, Pg.Program.name.con()) == U32.is_eq(j, 2) : Bool}:
  iff_eq(Sd.Name.is_eq(b, Pg.Program.name.con()), U32.is_eq(j, 2), and_r(Bool.and(iff(Sd.Name.is_eq(b, Pg.Program.name.unit()), U32.is_eq(j, 0)), iff(Sd.Name.is_eq(b, Pg.Program.name.nil()), U32.is_eq(j, 1))), iff(Sd.Name.is_eq(b, Pg.Program.name.con()), U32.is_eq(j, 2)), and_l(Bool.and(Bool.and(iff(Sd.Name.is_eq(b, Pg.Program.name.unit()), U32.is_eq(j, 0)), iff(Sd.Name.is_eq(b, Pg.Program.name.nil()), U32.is_eq(j, 1))), iff(Sd.Name.is_eq(b, Pg.Program.name.con()), U32.is_eq(j, 2))), iff(Sd.Name.is_eq(b, Pg.Program.name.wnil()), U32.is_eq(j, 3)), and_l(Bool.and(Bool.and(Bool.and(iff(Sd.Name.is_eq(b, Pg.Program.name.unit()), U32.is_eq(j, 0)), iff(Sd.Name.is_eq(b, Pg.Program.name.nil()), U32.is_eq(j, 1))), iff(Sd.Name.is_eq(b, Pg.Program.name.con()), U32.is_eq(j, 2))), iff(Sd.Name.is_eq(b, Pg.Program.name.wnil()), U32.is_eq(j, 3))), iff(Sd.Name.is_eq(b, Pg.Program.name.wcon()), U32.is_eq(j, 4)), and_l(Bool.and(Bool.and(Bool.and(Bool.and(iff(Sd.Name.is_eq(b, Pg.Program.name.unit()), U32.is_eq(j, 0)), iff(Sd.Name.is_eq(b, Pg.Program.name.nil()), U32.is_eq(j, 1))), iff(Sd.Name.is_eq(b, Pg.Program.name.con()), U32.is_eq(j, 2))), iff(Sd.Name.is_eq(b, Pg.Program.name.wnil()), U32.is_eq(j, 3))), iff(Sd.Name.is_eq(b, Pg.Program.name.wcon()), U32.is_eq(j, 4))), iff(Sd.Name.is_eq(b, Pg.Program.name.true()), U32.is_eq(j, 5)), and_l(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(iff(Sd.Name.is_eq(b, Pg.Program.name.unit()), U32.is_eq(j, 0)), iff(Sd.Name.is_eq(b, Pg.Program.name.nil()), U32.is_eq(j, 1))), iff(Sd.Name.is_eq(b, Pg.Program.name.con()), U32.is_eq(j, 2))), iff(Sd.Name.is_eq(b, Pg.Program.name.wnil()), U32.is_eq(j, 3))), iff(Sd.Name.is_eq(b, Pg.Program.name.wcon()), U32.is_eq(j, 4))), iff(Sd.Name.is_eq(b, Pg.Program.name.true()), U32.is_eq(j, 5))), iff(Sd.Name.is_eq(b, Pg.Program.name.false()), U32.is_eq(j, 6)), h))))))

def kn3(+j: U32, +b: List<&2, Word(8n)>, +h: {known.ok(j, b) == True{} : Bool}) ->
  {Sd.Name.is_eq(b, Pg.Program.name.wnil()) == U32.is_eq(j, 3) : Bool}:
  iff_eq(Sd.Name.is_eq(b, Pg.Program.name.wnil()), U32.is_eq(j, 3), and_r(Bool.and(Bool.and(iff(Sd.Name.is_eq(b, Pg.Program.name.unit()), U32.is_eq(j, 0)), iff(Sd.Name.is_eq(b, Pg.Program.name.nil()), U32.is_eq(j, 1))), iff(Sd.Name.is_eq(b, Pg.Program.name.con()), U32.is_eq(j, 2))), iff(Sd.Name.is_eq(b, Pg.Program.name.wnil()), U32.is_eq(j, 3)), and_l(Bool.and(Bool.and(Bool.and(iff(Sd.Name.is_eq(b, Pg.Program.name.unit()), U32.is_eq(j, 0)), iff(Sd.Name.is_eq(b, Pg.Program.name.nil()), U32.is_eq(j, 1))), iff(Sd.Name.is_eq(b, Pg.Program.name.con()), U32.is_eq(j, 2))), iff(Sd.Name.is_eq(b, Pg.Program.name.wnil()), U32.is_eq(j, 3))), iff(Sd.Name.is_eq(b, Pg.Program.name.wcon()), U32.is_eq(j, 4)), and_l(Bool.and(Bool.and(Bool.and(Bool.and(iff(Sd.Name.is_eq(b, Pg.Program.name.unit()), U32.is_eq(j, 0)), iff(Sd.Name.is_eq(b, Pg.Program.name.nil()), U32.is_eq(j, 1))), iff(Sd.Name.is_eq(b, Pg.Program.name.con()), U32.is_eq(j, 2))), iff(Sd.Name.is_eq(b, Pg.Program.name.wnil()), U32.is_eq(j, 3))), iff(Sd.Name.is_eq(b, Pg.Program.name.wcon()), U32.is_eq(j, 4))), iff(Sd.Name.is_eq(b, Pg.Program.name.true()), U32.is_eq(j, 5)), and_l(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(iff(Sd.Name.is_eq(b, Pg.Program.name.unit()), U32.is_eq(j, 0)), iff(Sd.Name.is_eq(b, Pg.Program.name.nil()), U32.is_eq(j, 1))), iff(Sd.Name.is_eq(b, Pg.Program.name.con()), U32.is_eq(j, 2))), iff(Sd.Name.is_eq(b, Pg.Program.name.wnil()), U32.is_eq(j, 3))), iff(Sd.Name.is_eq(b, Pg.Program.name.wcon()), U32.is_eq(j, 4))), iff(Sd.Name.is_eq(b, Pg.Program.name.true()), U32.is_eq(j, 5))), iff(Sd.Name.is_eq(b, Pg.Program.name.false()), U32.is_eq(j, 6)), h)))))

def kn4(+j: U32, +b: List<&2, Word(8n)>, +h: {known.ok(j, b) == True{} : Bool}) ->
  {Sd.Name.is_eq(b, Pg.Program.name.wcon()) == U32.is_eq(j, 4) : Bool}:
  iff_eq(Sd.Name.is_eq(b, Pg.Program.name.wcon()), U32.is_eq(j, 4), and_r(Bool.and(Bool.and(Bool.and(iff(Sd.Name.is_eq(b, Pg.Program.name.unit()), U32.is_eq(j, 0)), iff(Sd.Name.is_eq(b, Pg.Program.name.nil()), U32.is_eq(j, 1))), iff(Sd.Name.is_eq(b, Pg.Program.name.con()), U32.is_eq(j, 2))), iff(Sd.Name.is_eq(b, Pg.Program.name.wnil()), U32.is_eq(j, 3))), iff(Sd.Name.is_eq(b, Pg.Program.name.wcon()), U32.is_eq(j, 4)), and_l(Bool.and(Bool.and(Bool.and(Bool.and(iff(Sd.Name.is_eq(b, Pg.Program.name.unit()), U32.is_eq(j, 0)), iff(Sd.Name.is_eq(b, Pg.Program.name.nil()), U32.is_eq(j, 1))), iff(Sd.Name.is_eq(b, Pg.Program.name.con()), U32.is_eq(j, 2))), iff(Sd.Name.is_eq(b, Pg.Program.name.wnil()), U32.is_eq(j, 3))), iff(Sd.Name.is_eq(b, Pg.Program.name.wcon()), U32.is_eq(j, 4))), iff(Sd.Name.is_eq(b, Pg.Program.name.true()), U32.is_eq(j, 5)), and_l(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(iff(Sd.Name.is_eq(b, Pg.Program.name.unit()), U32.is_eq(j, 0)), iff(Sd.Name.is_eq(b, Pg.Program.name.nil()), U32.is_eq(j, 1))), iff(Sd.Name.is_eq(b, Pg.Program.name.con()), U32.is_eq(j, 2))), iff(Sd.Name.is_eq(b, Pg.Program.name.wnil()), U32.is_eq(j, 3))), iff(Sd.Name.is_eq(b, Pg.Program.name.wcon()), U32.is_eq(j, 4))), iff(Sd.Name.is_eq(b, Pg.Program.name.true()), U32.is_eq(j, 5))), iff(Sd.Name.is_eq(b, Pg.Program.name.false()), U32.is_eq(j, 6)), h))))

def kn5(+j: U32, +b: List<&2, Word(8n)>, +h: {known.ok(j, b) == True{} : Bool}) ->
  {Sd.Name.is_eq(b, Pg.Program.name.true()) == U32.is_eq(j, 5) : Bool}:
  iff_eq(Sd.Name.is_eq(b, Pg.Program.name.true()), U32.is_eq(j, 5), and_r(Bool.and(Bool.and(Bool.and(Bool.and(iff(Sd.Name.is_eq(b, Pg.Program.name.unit()), U32.is_eq(j, 0)), iff(Sd.Name.is_eq(b, Pg.Program.name.nil()), U32.is_eq(j, 1))), iff(Sd.Name.is_eq(b, Pg.Program.name.con()), U32.is_eq(j, 2))), iff(Sd.Name.is_eq(b, Pg.Program.name.wnil()), U32.is_eq(j, 3))), iff(Sd.Name.is_eq(b, Pg.Program.name.wcon()), U32.is_eq(j, 4))), iff(Sd.Name.is_eq(b, Pg.Program.name.true()), U32.is_eq(j, 5)), and_l(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(iff(Sd.Name.is_eq(b, Pg.Program.name.unit()), U32.is_eq(j, 0)), iff(Sd.Name.is_eq(b, Pg.Program.name.nil()), U32.is_eq(j, 1))), iff(Sd.Name.is_eq(b, Pg.Program.name.con()), U32.is_eq(j, 2))), iff(Sd.Name.is_eq(b, Pg.Program.name.wnil()), U32.is_eq(j, 3))), iff(Sd.Name.is_eq(b, Pg.Program.name.wcon()), U32.is_eq(j, 4))), iff(Sd.Name.is_eq(b, Pg.Program.name.true()), U32.is_eq(j, 5))), iff(Sd.Name.is_eq(b, Pg.Program.name.false()), U32.is_eq(j, 6)), h)))

def kn6(+j: U32, +b: List<&2, Word(8n)>, +h: {known.ok(j, b) == True{} : Bool}) ->
  {Sd.Name.is_eq(b, Pg.Program.name.false()) == U32.is_eq(j, 6) : Bool}:
  iff_eq(Sd.Name.is_eq(b, Pg.Program.name.false()), U32.is_eq(j, 6), and_r(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(iff(Sd.Name.is_eq(b, Pg.Program.name.unit()), U32.is_eq(j, 0)), iff(Sd.Name.is_eq(b, Pg.Program.name.nil()), U32.is_eq(j, 1))), iff(Sd.Name.is_eq(b, Pg.Program.name.con()), U32.is_eq(j, 2))), iff(Sd.Name.is_eq(b, Pg.Program.name.wnil()), U32.is_eq(j, 3))), iff(Sd.Name.is_eq(b, Pg.Program.name.wcon()), U32.is_eq(j, 4))), iff(Sd.Name.is_eq(b, Pg.Program.name.true()), U32.is_eq(j, 5))), iff(Sd.Name.is_eq(b, Pg.Program.name.false()), U32.is_eq(j, 6)), h))

def lk(n: Maybe<&2, List<&2, Word(8n)>>, +j: U32, -k: List<&2, Word(8n)>, +e: {n == Some{k} : Maybe<&2, List<&2, Word(8n)>>},
  +h: {labok.of(n, j) == True{} : Bool}) -> {known.ok(j, k) == True{} : Bool}:
  %e : {labok.of(_, j) == True{} : Bool}
  h

# the name of a label cell compares as known.ok says
def LK(+f: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32,
  +hok: {ok(1n+f, m, ks, img, c, im, fs, nx) == True{} : Bool}, +eL: {Lm(m, c) == True{} : Bool},
  -k: List<&2, Word(8n)>, +e: {T.tm.name(ks, Fd(2n, m, c)) == Some{k} : Maybe<&2, List<&2, Word(8n)>>}) ->
  {known.ok(Fd(2n, m, c), k) == True{} : Bool}:
  lk(T.tm.name(ks, Fd(2n, m, c)), Fd(2n, m, c), k, e, ok.lb(f, m, ks, img, c, im, fs, nx, hok, eL))

# a pair cell has the tag 10
def P_tag(+m: Cr.Cir.Cells, +c: U32, +eP: {Pm(m, c) == True{} : Bool}) -> {U32.is_eq(Tg(m, c), 10) == True{} : Bool}:
  +f0 = Fd(0n, m, c)
  +q = T.tm.quan(U32.and(U32.shrn(f0, 6n), 3))
  and_r(isQ1(q), U32.is_eq(U32.and(f0, 63), 10), Equal.trans(Bool, FP.r(f0), FP.l(f0), True{}, Equal.sym(Bool, FP.l(f0), FP.r(f0), fp(f0)), eP))

# the parts of a pair cell are cells that ok accepts, a level less deep
def ok.l(+f: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32,
  +hok: {ok(1n+f, m, ks, img, c, im, fs, nx) == True{} : Bool}, +eP: {Pm(m, c) == True{} : Bool}) ->
  {ok(f, m, ks, img, Fd(2n, m, c), im, fs, nx) == True{} : Bool}:
  and_l(ok(f, m, ks, img, Fd(2n, m, c), im, fs, nx), ok(f, m, ks, img, Fd(3n, m, c), im, fs, nx), ok.kids(f, m, ks, img, c, im, fs, nx, hok, P_tag(m, c, eP)))

def ok.r(+f: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32,
  +hok: {ok(1n+f, m, ks, img, c, im, fs, nx) == True{} : Bool}, +eP: {Pm(m, c) == True{} : Bool}) ->
  {ok(f, m, ks, img, Fd(3n, m, c), im, fs, nx) == True{} : Bool}:
  and_r(ok(f, m, ks, img, Fd(2n, m, c), im, fs, nx), ok(f, m, ks, img, Fd(3n, m, c), im, fs, nx), ok.kids(f, m, ks, img, c, im, fs, nx, hok, P_tag(m, c, eP)))

# ok fails with no fuel
def ok.zero(-m: Cr.Cir.Cells, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -c: U32, -im: U32, -fs: U32, -nx: U32,
  +h: {ok(0n, m, ks, img, c, im, fs, nx) == True{} : Bool}) -> Empty:
  PN.false_ne_true(h)
# A bit's term is what CB reads
# ------------------------------

def unbit_eq(x6: Bool, x7: Bool) -> {Pg.Program.unbit.if(x6, x7) == CB.t(Bool.or(x6, x7), x6) : Maybe<&2, Bool>}:
  match x6 x7:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def BB.b(+k: List<&2, Word(8n)>, +g: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32, +hok2: {ok(1n+g, m, ks, img, Fd(2n, m, c), im, fs, nx) == True{} : Bool}, +eL: {Lm(m, Fd(2n, m, c)) == True{} : Bool},
  +ek: {T.tm.name(ks, Fd(2n, m, Fd(2n, m, c))) == Some{k} : Maybe<&2, List<&2, Word(8n)>>}) -> {Ub.x(Some{k}) == CB.x(True{}, Fd(2n, m, Fd(2n, m, c))) : Maybe<&2, Bool>}:
  +h = LK(g, m, ks, img, Fd(2n, m, c), im, fs, nx, hok2, eL, k, ek)
  %Equal.sym(Bool, Sd.Name.is_eq(k, Pg.Program.name.true()), U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 5), kn5(Fd(2n, m, Fd(2n, m, c)), k, h)) : {Pg.Program.unbit.if(_, Sd.Name.is_eq(k, Pg.Program.name.false())) == CB.x(True{}, Fd(2n, m, Fd(2n, m, c))) : Maybe<&2, Bool>}
  %Equal.sym(Bool, Sd.Name.is_eq(k, Pg.Program.name.false()), U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 6), kn6(Fd(2n, m, Fd(2n, m, c)), k, h)) : {Pg.Program.unbit.if(U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 5), _) == CB.x(True{}, Fd(2n, m, Fd(2n, m, c))) : Maybe<&2, Bool>}
  unbit_eq(U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 5), U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 6))

def BB.x(bx: Bool, +g: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32, +hok2: {ok(1n+g, m, ks, img, Fd(2n, m, c), im, fs, nx) == True{} : Bool}, +e: {Lm(m, Fd(2n, m, c)) == bx : Bool}) ->
  SpecM(T.tm.of(1n+g, m, ks, img, Fd(2n, m, c)), x => {Ub.x(VL(x)) == CB.x(bx, Fd(2n, m, Fd(2n, m, c))) : Maybe<&2, Bool>}):
  match bx:
    case False{}:
      cellNotL(g, m, ks, img, Fd(2n, m, c), im, fs, nx, x => {Ub.x(VL(x)) == CB.x(False{}, Fd(2n, m, Fd(2n, m, c))) : Maybe<&2, Bool>}, e, hok2,
        v => ev => Equal.cong(Maybe<&2, List<&2, Word(8n)>>, Maybe<&2, Bool>, mm => Ub.x(mm), VL(v), None{}, ev))
    case True{}:
      cellLab(g, m, ks, img, Fd(2n, m, c), x => {Ub.x(VL(x)) == CB.x(True{}, Fd(2n, m, Fd(2n, m, c))) : Maybe<&2, Bool>}, e,
        k => ek => BB.b(k, g, m, ks, img, c, im, fs, nx, hok2, e, ek))

def BB.u(o: Bool, +g: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32, +hok2: {ok(1n+g, m, ks, img, Fd(2n, m, c), im, fs, nx) == True{} : Bool}) ->
  SpecM(T.tm.of(1n+g, m, ks, img, Fd(2n, m, c)), x => {Ub.u(o, x) == CB.l(o, m, c) : Maybe<&2, Bool>}):
  match o:
    case False{}:
      SpecM.all(T.tm.of(1n+g, m, ks, img, Fd(2n, m, c)), x => {Ub.u(False{}, x) == CB.l(False{}, m, c) : Maybe<&2, Bool>}, x => {==})
    case True{}:
      BB.x(Lm(m, Fd(2n, m, c)), g, m, ks, img, c, im, fs, nx, hok2, {==})

def BB.k(+k: List<&2, Word(8n)>, +g: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32, +hok3: {ok(1n+g, m, ks, img, Fd(3n, m, c), im, fs, nx) == True{} : Bool}, +hok2: {ok(1n+g, m, ks, img, Fd(2n, m, c), im, fs, nx) == True{} : Bool},
  +eL: {Lm(m, Fd(3n, m, c)) == True{} : Bool}, +ek: {T.tm.name(ks, Fd(2n, m, Fd(3n, m, c))) == Some{k} : Maybe<&2, List<&2, Word(8n)>>}) ->
  SpecM(T.tm.of(1n+g, m, ks, img, Fd(2n, m, c)), x => {Ub.y(Some{k}, x) == CB.l(Bool.and(True{}, U32.is_eq(Fd(2n, m, Fd(3n, m, c)), 0)), m, c) : Maybe<&2, Bool>}):
  %Equal.sym(Bool, Sd.Name.is_eq(k, Pg.Program.name.unit()), U32.is_eq(Fd(2n, m, Fd(3n, m, c)), 0), kn0(Fd(2n, m, Fd(3n, m, c)), k, LK(g, m, ks, img, Fd(3n, m, c), im, fs, nx, hok3, eL, k, ek))) :
    SpecM(T.tm.of(1n+g, m, ks, img, Fd(2n, m, c)), x => {Ub.u(_, x) == CB.l(U32.is_eq(Fd(2n, m, Fd(3n, m, c)), 0), m, c) : Maybe<&2, Bool>})
  BB.u(U32.is_eq(Fd(2n, m, Fd(3n, m, c)), 0), g, m, ks, img, c, im, fs, nx, hok2)

def BB.y(by: Bool, +g: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32, +hok3: {ok(1n+g, m, ks, img, Fd(3n, m, c), im, fs, nx) == True{} : Bool}, +hok2: {ok(1n+g, m, ks, img, Fd(2n, m, c), im, fs, nx) == True{} : Bool}, +e: {Lm(m, Fd(3n, m, c)) == by : Bool}) ->
  SpecM(T.tm.of(1n+g, m, ks, img, Fd(3n, m, c)), y => SpecM(T.tm.of(1n+g, m, ks, img, Fd(2n, m, c)), x => {Ub.y(VL(y), x) == CB.l(Bool.and(by, U32.is_eq(Fd(2n, m, Fd(3n, m, c)), 0)), m, c) : Maybe<&2, Bool>})):
  match by:
    case False{}:
      cellNotL(g, m, ks, img, Fd(3n, m, c), im, fs, nx, y => SpecM(T.tm.of(1n+g, m, ks, img, Fd(2n, m, c)), x => {Ub.y(VL(y), x) == CB.l(Bool.and(False{}, U32.is_eq(Fd(2n, m, Fd(3n, m, c)), 0)), m, c) : Maybe<&2, Bool>}), e, hok3,
        v => ev => SpecM.all(T.tm.of(1n+g, m, ks, img, Fd(2n, m, c)), x => {Ub.y(VL(v), x) == CB.l(Bool.and(False{}, U32.is_eq(Fd(2n, m, Fd(3n, m, c)), 0)), m, c) : Maybe<&2, Bool>},
          x => Equal.cong(Maybe<&2, List<&2, Word(8n)>>, Maybe<&2, Bool>, mm => Ub.y(mm, x), VL(v), None{}, ev)))
    case True{}:
      cellLab(g, m, ks, img, Fd(3n, m, c), y => SpecM(T.tm.of(1n+g, m, ks, img, Fd(2n, m, c)), x => {Ub.y(VL(y), x) == CB.l(Bool.and(True{}, U32.is_eq(Fd(2n, m, Fd(3n, m, c)), 0)), m, c) : Maybe<&2, Bool>}), e,
        k => ek => BB.k(k, g, m, ks, img, c, im, fs, nx, hok3, hok2, e, ek))

def BB.p(b: Bool, +f: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32, +hok: {ok(1n+f, m, ks, img, c, im, fs, nx) == True{} : Bool}, +eb: {Pm(m, c) == b : Bool}) ->
  SpecM(T.tm.of(1n+f, m, ks, img, c), t => {Ub(t) == CB.p(b, m, c) : Maybe<&2, Bool>}):
  match b:
    case False{}:
      cellNotT1(f, m, ks, img, c, im, fs, nx, t => {Ub(t) == CB.p(False{}, m, c) : Maybe<&2, Bool>}, eb, hok,
        v => ev => Equal.cong(Maybe<&2, TP>, Maybe<&2, Bool>, mm => Ub.r(mm), V1(v), None{}, ev))
    case True{}:
      match f:
        case 0n:
          cellT1(0n, m, ks, img, c, t => {Ub(t) == CB.p(True{}, m, c) : Maybe<&2, Bool>}, eb, Unit{})
        case 1n+g:
          cellT1(1n+g, m, ks, img, c, t => {Ub(t) == CB.p(True{}, m, c) : Maybe<&2, Bool>}, eb,
            SpecM.swap(T.tm.of(1n+g, m, ks, img, Fd(2n, m, c)), T.tm.of(1n+g, m, ks, img, Fd(3n, m, c)), x => y => {Ub(Bk.Term.Tup{Bk.Quan.Q1{}, x, y}) == CB.p(True{}, m, c) : Maybe<&2, Bool>},
              BB.y(Lm(m, Fd(3n, m, c)), g, m, ks, img, c, im, fs, nx, ok.r(1n+g, m, ks, img, c, im, fs, nx, hok, eb), ok.l(1n+g, m, ks, img, c, im, fs, nx, hok, eb), {==})))

# the term of a cell is a bit as CB reads it
def BB(+fb: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32, +hok: {ok(fb, m, ks, img, c, im, fs, nx) == True{} : Bool}) -> SpecM(T.tm.of(fb, m, ks, img, c), t => {Ub(t) == CB(m, c) : Maybe<&2, Bool>}):
  match fb:
    case 0n:
      Empty.absurd(SpecM(T.tm.of(0n, m, ks, img, c), t => {Ub(t) == CB(m, c) : Maybe<&2, Bool>}), ok.zero(m, ks, img, c, im, fs, nx, hok))
    case 1n+f:
      BB.p(Pm(m, c), f, m, ks, img, c, im, fs, nx, hok, {==})

# The budget of an emit
# ---------------------
#
# An emit at the next cell nx, with outn bytes out, runs out of memory only
# when the limit has at most 20 nx + outn bytes (EB): its byte at 20 nx + outn
# would pass 2^32, which no limit passes (LB <= 2^32), or the memory cannot
# grow to hold that byte.

# the bytes of a limit of lim pages (Lim.bytes of definitions.bend), its
# minimum spelled as the checker evaluates it (as need_big.bend's memory_le)
def Lim.bytes(+lim: U32) -> Nat:
  PN.D(16n, U32.to_nat(Wa.Wasm.min.if(Cmp.is_le(U32.cmp(lim, 65536)), lim, 65536)))

# the limit lim has at most 20 nx + outn bytes
def EB(+lim: U32, +nx: U32, +outn: U32) -> Data:
  PN.Le(Lim.bytes(lim), Nat.add(Nat.mul(20n, U32.to_nat(nx)), U32.to_nat(outn)))

# 2^k x is monotone in x
def D.mono(+k: Nat, +x: Nat, +y: Nat, h: PN.Le(x, y)) -> PN.Le(PN.D(k, x), PN.D(k, y)):
  match k:
    case 0n:
      h
    case 1n+q:
      PN.double_mono(PN.D(q, x), PN.D(q, y), D.mono(q, x, y, h))

# 2^k (2 x) = 2 (2^k x)
def D.dbl(+k: Nat, +x: Nat) -> {PN.D(k, Nat.double(x)) == Nat.double(PN.D(k, x)) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+q:
      Equal.cong(Nat, Nat, z => Nat.double(z), PN.D(q, Nat.double(x)), Nat.double(PN.D(q, x)), D.dbl(q, x))

# a × (1 + b) = a + a × b
def mul_succ_r(+a: Nat, +b: Nat) -> {Nat.mul(a, 1n+b) == Nat.add(a, Nat.mul(a, b)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.trans(Nat, 1n+Nat.add(b, Nat.mul(p, 1n+b)), 1n+Nat.add(b, Nat.add(p, Nat.mul(p, b))), 1n+Nat.add(p, Nat.add(b, Nat.mul(p, b))),
        Equal.cong(Nat, Nat, z => 1n+Nat.add(b, z), Nat.mul(p, 1n+b), Nat.add(p, Nat.mul(p, b)), mul_succ_r(p, b)),
        Equal.cong(Nat, Nat, z => 1n+z, Nat.add(b, Nat.add(p, Nat.mul(p, b))), Nat.add(p, Nat.add(b, Nat.mul(p, b))), PN.add_swap(b, p, Nat.mul(p, b))))

# 20 x, as halt.bend counts it, is 20 × x
def t20.mul(+x: Nat) -> {PH.H.t20(x) == Nat.mul(20n, x) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      Equal.trans(Nat, 20n+PH.H.t20(p), 20n+Nat.mul(20n, p), Nat.mul(20n, 1n+p),
        Equal.cong(Nat, Nat, z => 20n+z, PH.H.t20(p), Nat.mul(20n, p), t20.mul(p)),
        Equal.sym(Nat, Nat.mul(20n, 1n+p), Nat.add(20n, Nat.mul(20n, p)), mul_succ_r(20n, p)))

# a Some is no None
def MS(x: Maybe<&2, U32>) -> Type:
  match x:
    case Some{_}:
      Unit
    case None{}:
      Empty

def some_ne_none(+p: U32, e: {Some{p} == None{} : Maybe<&2, U32>}) -> Empty:
  %e : MS(_)
  Unit{}

# what a comparison that is no LT says
def rel.nlt(c: Cmp, +x: Nat, +y: Nat, h: PN.Rel(c, x, y), e: {Cmp.is_lt(c) == False{} : Bool}) -> PN.Le(y, x):
  match c:
    case LT{}:
      Empty.absurd(PN.Le(y, x), PN.true_ne_false(e))
    case EQ{}:
      %h : PN.Le(_, x)
      PN.le_refl(x)
    case GT{}:
      PN.weaken(y, x, h)

# what a comparison that is no LE says
def rel.nle(c: Cmp, +x: Nat, +y: Nat, h: PN.Rel(c, x, y), e: {Cmp.is_le(c) == False{} : Bool}) -> PN.Le(1n+y, x):
  match c:
    case LT{}:
      Empty.absurd(PN.Le(1n+y, x), PN.true_ne_false(e))
    case EQ{}:
      Empty.absurd(PN.Le(1n+y, x), PN.true_ne_false(e))
    case GT{}:
      h

# a comparison GE, from the numbers
def rel.ge(c: Cmp, +x: Nat, +y: Nat, r: PN.Rel(c, x, y), h: PN.Le(y, x)) -> {Cmp.is_ge(c) == True{} : Bool}:
  match c:
    case LT{}:
      Empty.absurd({False{} == True{} : Bool}, PN.not_succ_le(x, PN.le_trans(1n+x, y, x, r, h)))
    case EQ{}:
      {==}
    case GT{}:
      {==}

# the minimum of a and b is at most a
def min.l.go(c: Bool, +a: U32, +b: U32, e: {U32.is_le(a, b) == c : Bool}) -> PN.Le(U32.to_nat(Wa.Wasm.min.if(c, a, b)), U32.to_nat(a)):
  match c:
    case True{}:
      PN.le_refl(U32.to_nat(a))
    case False{}:
      PN.weaken(U32.to_nat(b), U32.to_nat(a), rel.nle(U32.cmp(a, b), U32.to_nat(a), U32.to_nat(b), PN.U32.rel(a, b), e))

# Shifts and sums of words
# ------------------------

# a shift right with a 0 in at the top keeps the value
def pad.val(+p: Nat, t: Word(p)) -> {Word.to_nat(1n+p, Word.shr.pad(p, t)) == Word.to_nat(p, t) : Nat}:
  match p:
    case 0n:
      {==}
    case 1n+q:
      match t:
        case WCon{False{}, +u}:
          Equal.cong(Nat, Nat, z => Nat.double(z), Word.to_nat(1n+q, Word.shr.pad(q, u)), Word.to_nat(q, u), pad.val(q, u))
        case WCon{True{}, +u}:
          Equal.cong(Nat, Nat, z => 1n+Nat.double(z), Word.to_nat(1n+q, Word.shr.pad(q, u)), Word.to_nat(q, u), pad.val(q, u))

# 2 (x >> 1) <= x
def shr.down(x: U32) -> PN.Le(Nat.double(U32.to_nat(U32.shr(x))), U32.to_nat(x)):
  match x:
    case U32{w}:
      match w:
        case WCon{False{}, +t}:
          PN.le_rw_l(Nat.double(Word.to_nat(31n, t)), Nat.double(Word.to_nat(32n, Word.shr.pad(31n, t))), Nat.double(Word.to_nat(31n, t)),
            Equal.cong(Nat, Nat, z => Nat.double(z), Word.to_nat(31n, t), Word.to_nat(32n, Word.shr.pad(31n, t)),
              Equal.sym(Nat, Word.to_nat(32n, Word.shr.pad(31n, t)), Word.to_nat(31n, t), pad.val(31n, t))),
            PN.le_refl(Nat.double(Word.to_nat(31n, t))))
        case WCon{True{}, +t}:
          PN.le_rw_l(Nat.double(Word.to_nat(31n, t)), Nat.double(Word.to_nat(32n, Word.shr.pad(31n, t))), 1n+Nat.double(Word.to_nat(31n, t)),
            Equal.cong(Nat, Nat, z => Nat.double(z), Word.to_nat(31n, t), Word.to_nat(32n, Word.shr.pad(31n, t)),
              Equal.sym(Nat, Word.to_nat(32n, Word.shr.pad(31n, t)), Word.to_nat(31n, t), pad.val(31n, t))),
            PN.le_succ(Nat.double(Word.to_nat(31n, t)), Nat.double(Word.to_nat(31n, t)), PN.le_refl(Nat.double(Word.to_nat(31n, t)))))

# 2^k (x >> k) <= x
def shrn.down(+k: Nat, +x: U32) -> PN.Le(PN.D(k, U32.to_nat(U32.shrn(x, k))), U32.to_nat(x)):
  match k:
    case 0n:
      PN.le_refl(U32.to_nat(x))
    case 1n+q:
      +y = U32.shrn(x, q)
      +s = U32.to_nat(U32.shr(y))
      PN.le_rw_l(PN.D(q, Nat.double(s)), Nat.double(PN.D(q, s)), U32.to_nat(x), D.dbl(q, s),
        PN.le_trans(PN.D(q, Nat.double(s)), PN.D(q, U32.to_nat(y)), U32.to_nat(x), D.mono(q, Nat.double(s), U32.to_nat(y), shr.down(y)),
          shrn.down(q, x)))

# x << 1 <= 2 x
def shl.le(a: U32) -> PN.Le(U32.to_nat(U32.shl(a)), Nat.double(U32.to_nat(a))):
  match a:
    case U32{+x}:
      +V = Word.to_nat(32n, Word.shl(32n, x))
      +Dc = PN.D(32n, PH.H.bn(PH.H.sout(32n, x)))
      PN.le_rw_r(V, Nat.add(V, Dc), Nat.double(Word.to_nat(32n, x)), PH.H.shl(32n, x), PN.le_add_r(V, Dc))

# x << k <= 2^k x
def shln.le(+k: Nat, +a: U32) -> PN.Le(U32.to_nat(U32.shln(a, k)), PN.D(k, U32.to_nat(a))):
  match k:
    case 0n:
      PN.le_refl(U32.to_nat(a))
    case 1n+q:
      PN.le_trans(U32.to_nat(U32.shl(U32.shln(a, q))), Nat.double(U32.to_nat(U32.shln(a, q))), Nat.double(PN.D(q, U32.to_nat(a))),
        shl.le(U32.shln(a, q)), PN.double_mono(U32.to_nat(U32.shln(a, q)), PN.D(q, U32.to_nat(a)), shln.le(q, a)))

# a + b, as a word, is at most the sum
def add.le(a: U32, b: U32) -> PN.Le(U32.to_nat(U32.add(a, b)), Nat.add(U32.to_nat(a), U32.to_nat(b))):
  match a b:
    case U32{+x} U32{+y}:
      PH.H.add_le(32n, x, y)

# the first byte of the cell c is at most 20 c
def at.le(+c: U32) -> PN.Le(U32.to_nat(Cr.Cir.at(c)), Nat.mul(20n, U32.to_nat(c))):
  +x = U32.to_nat(c)
  PN.le_trans(U32.to_nat(Cr.Cir.at(c)), Nat.add(U32.to_nat(U32.shln(c, 4n)), U32.to_nat(U32.shln(c, 2n))), Nat.mul(20n, x),
    add.le(U32.shln(c, 4n), U32.shln(c, 2n)),
    PN.le_rw_r(Nat.add(U32.to_nat(U32.shln(c, 4n)), U32.to_nat(U32.shln(c, 2n))), Nat.add(PN.D(4n, x), PN.D(2n, x)), Nat.mul(20n, x),
      Equal.trans(Nat, Nat.add(PN.D(4n, x), PN.D(2n, x)), PH.H.t20(x), Nat.mul(20n, x), PH.H.t20_shifts(x), t20.mul(x)),
      PN.add_mono(U32.to_nat(U32.shln(c, 4n)), PN.D(4n, x), U32.to_nat(U32.shln(c, 2n)), PN.D(2n, x), shln.le(4n, c), shln.le(2n, c))))

# 2^k 0 = 0
def D.zero(+n: Nat) -> {PN.D(n, 0n) == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+q:
      Equal.cong(Nat, Nat, z => Nat.double(z), PN.D(q, 0n), 0n, D.zero(q))

# a sum S of n-bit words is V plus its carry out: without a carry V = S, so
# a part Y <= S that V is below has a carry, and S >= 2^n
def wrap.go(co: Bool, +n: Nat, +V: Nat, +S: Nat, +Y: Nat, ea: {Nat.add(V, PN.D(n, PH.H.bn(co))) == S : Nat}, hy: PN.Le(Y, S),
  nge: PN.Le(Y, V) -> Empty) -> PN.Le(PH.H.W(n), S):
  match co:
    case True{}:
      PN.le_rw_r(PH.H.W(n), Nat.add(V, PH.H.W(n)), S, ea, PN.le_add_l(V, PH.H.W(n)))
    case False{}:
      Empty.absurd(PN.Le(PH.H.W(n), S), nge(PN.le_rw_r(Y, S, V,
        Equal.trans(Nat, S, Nat.add(V, PN.D(n, 0n)), V, Equal.sym(Nat, Nat.add(V, PN.D(n, 0n)), S, ea),
          Equal.trans(Nat, Nat.add(V, PN.D(n, 0n)), Nat.add(V, 0n), V, Equal.cong(Nat, Nat, z => Nat.add(V, z), PN.D(n, 0n), 0n, D.zero(n)), PN.add_zero(V))),
        hy)))

# a + b of n-bit words, below b: the sum is at least 2^n
def wadd.wrap(+n: Nat, +x: Word(n), +y: Word(n), nge: PN.Le(Word.to_nat(n, y), Word.to_nat(n, Word.add(n, x, y))) -> Empty) ->
  PN.Le(PH.H.W(n), Nat.add(Word.to_nat(n, x), Word.to_nat(n, y))):
  wrap.go(PH.H.cout(n, x, y, False{}), n, Word.to_nat(n, Word.add(n, x, y)), Nat.add(Word.to_nat(n, x), Word.to_nat(n, y)), Word.to_nat(n, y),
    PH.H.adc(n, x, y, False{}), PN.le_add_l(Word.to_nat(n, x), Word.to_nat(n, y)), nge)

# a + b, as a U32, below b: the sum is at least W = 2^32 (W stays a variable
# in the match, so that no check expands 2^32)
def add.wrap(a: U32, b: U32, +W: Nat, hW: {W == PH.H.W(32n) : Nat}, e: {U32.is_ge(U32.add(a, b), b) == False{} : Bool}) ->
  PN.Le(W, Nat.add(U32.to_nat(a), U32.to_nat(b))):
  match a b:
    case U32{+x} U32{+y}:
      PN.le_rw_l(PH.H.W(32n), W, Nat.add(Word.to_nat(32n, x), Word.to_nat(32n, y)), Equal.sym(Nat, W, PH.H.W(32n), hW),
        wadd.wrap(32n, x, y, h => PN.true_ne_false(Equal.trans(Bool, True{}, U32.is_ge(U32{Word.add(32n, x, y)}, U32{y}), False{},
          Equal.sym(Bool, U32.is_ge(U32{Word.add(32n, x, y)}, U32{y}), True{},
            rel.ge(U32.cmp(U32{Word.add(32n, x, y)}, U32{y}), Word.to_nat(32n, Word.add(32n, x, y)), Word.to_nat(32n, y),
              PN.U32.rel(U32{Word.add(32n, x, y)}, U32{y}), h)), e))))

# The literals of the emit's test
# -------------------------------

def q4(j: Nat) -> Nat:
  match j:
    case 0n:
      0n
    case 1n+q:
      4n+q4(q)

# n bits of 0x0CCC...C with j nibbles of 12 at the bottom, its lowest bit
# first (as simulation_alloc_emit.bend writes 214748364)
def wb(n: Nat, j: Nat) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n:
      WCon{False{}, WNil{}}
    case 2n:
      WCon{False{}, WCon{False{}, WNil{}}}
    case 3n:
      WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}
    case 4n+p:
      match j:
        case 0n:
          WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, wb(p, 0n)}}}}
        case 1n+q:
          WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, wb(p, q)}}}}

def wb.val(j: Nat, +n: Nat, e: {n == 4n+q4(j) : Nat}) -> {Word.to_nat(n, wb(n, j)) == PH.H.pat(j) : Nat}:
  match j:
    case 0n:
      %Equal.sym(Nat, n, 4n, e) : {Word.to_nat(_, wb(_, 0n)) == PH.H.pat(0n) : Nat}
      {==}
    case 1n+(+q):
      %Equal.sym(Nat, n, 4n+q4(1n+q), e) : {Word.to_nat(_, wb(_, 1n+q)) == PH.H.pat(1n+q) : Nat}
      %Equal.sym(Nat, Word.to_nat(q4(1n+q), wb(q4(1n+q), q)), PH.H.pat(q), wb.val(q, q4(1n+q), {==})) :
        {Nat.double(Nat.double(1n+Nat.double(1n+Nat.double(_)))) == Nat.add(12n, PN.D(4n, PH.H.pat(q))) : Nat}
      {==}

def lit.wb() -> {214748364 == U32{wb(32n, 7n)} : U32}:
  {==}

def lit.pat() -> {U32.to_nat(214748364) == PH.H.pat(7n) : Nat}:
  %Equal.sym(U32, 214748364, U32{wb(32n, 7n)}, lit.wb()) : {U32.to_nat(_) == PH.H.pat(7n) : Nat}
  Equal.trans(Nat, U32.to_nat(U32{wb(32n, 7n)}), Word.to_nat(32n, wb(32n, 7n)), PH.H.pat(7n), PN.u32_to_nat(wb(32n, 7n)),
    wb.val(7n, 32n, {==}))

def Cmp.fin_ff(c: Cmp) -> {Cmp.is_eq(Word.cmp.fin(False{}, False{}, c)) == Cmp.is_eq(c) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

# t + 1, when not 0, counts one more than t
def Word.inc_nat(n: Nat, t: Word(n), h: {False{} == Cmp.is_eq(Word.cmp(n, Word.inc(n, t), Word.zero(n))) : Bool}) ->
  {Word.to_nat(n, Word.inc(n, t)) == 1n+Word.to_nat(n, t) : Nat}:
  match n:
    case 0n:
      match t:
        case WNil{}:
          Empty.absurd({Word.to_nat(0n, WNil{}) == 1n : Nat}, PN.true_ne_false(Equal.sym(Bool, False{}, True{}, h)))
    case 1n+(+p):
      match t:
        case WCon{False{}, r}:
          {==}
        case WCon{True{}, +r}:
          +c = Word.cmp(p, Word.inc(p, r), Word.zero(p))
          +ih = Word.inc_nat(p, r, Equal.trans(Bool, False{}, Cmp.is_eq(Word.cmp.fin(False{}, False{}, c)), Cmp.is_eq(c), h, Cmp.fin_ff(c)))
          %Equal.sym(Nat, Word.to_nat(p, Word.inc(p, r)), 1n+Word.to_nat(p, r), ih) : {Nat.double(_) == 2n+Nat.double(Word.to_nat(p, r)) : Nat}
          {==}

def U32.inc_nat(a: U32, h: {False{} == U32.is_zero(U32.inc(a)) : Bool}) -> {U32.to_nat(U32.inc(a)) == 1n+U32.to_nat(a) : Nat}:
  match a:
    case U32{x}:
      Word.inc_nat(32n, x, h)

# 214748365 is 214748364 + 1
def lit.k5() -> {214748365 == U32.inc(214748364) : U32}:
  {==}

# the value of 214748365: 1 + P, where 16 + 20 P = 2^32 (H.hP)
def lit.val() -> {U32.to_nat(214748365) == 1n+PH.H.pat(7n) : Nat}:
  %Equal.sym(U32, 214748365, U32.inc(214748364), lit.k5()) : {U32.to_nat(_) == 1n+PH.H.pat(7n) : Nat}
  Equal.trans(Nat, U32.to_nat(U32.inc(214748364)), 1n+U32.to_nat(214748364), 1n+PH.H.pat(7n), U32.inc_nat(214748364, {==}),
    Equal.cong(Nat, Nat, z => 1n+z, U32.to_nat(214748364), PH.H.pat(7n), lit.pat()))

# The budget of an emit, proven
# -----------------------------

# the two spellings of 2^n
def w.d(+n: Nat) -> {PH.H.W(n) == PN.D(n, 1n) : Nat}:
  {==}

# a limit has at most W = 2^32 bytes. 2^32 stays a variable: a check that
# compares a type holding it with another spelling evaluates it
def lb.top(+lim: U32, +W: Nat, hW: {PN.D(32n, 1n) == W : Nat}) -> PN.Le(Lim.bytes(lim), W):
  +y = U32.to_nat(Wa.Wasm.min.if(Cmp.is_le(U32.cmp(lim, 65536)), lim, 65536))
  +h1 = D.mono(16n, y, U32.to_nat(65536), PN.min.case(Cmp.is_le(U32.cmp(lim, 65536)), lim, 65536, {==}))
  +h2 = PN.le_rw_r(PN.D(16n, y), PN.D(16n, U32.to_nat(65536)), PN.D(32n, 1n),
    Equal.trans(Nat, PN.D(16n, U32.to_nat(65536)), PN.D(16n, PN.D(16n, 1n)), PN.D(32n, 1n),
      Equal.cong(Nat, Nat, z => PN.D(16n, z), U32.to_nat(65536), PN.D(16n, 1n), PN.val_65536()), PN.D_add(16n, 16n, 32n, 1n, {==})), h1)
  PN.le_rw_r(PN.D(16n, y), PN.D(32n, 1n), W, hW, h2)

# below W = 2^32 is below the limit's bytes too
def lb.le(+lim: U32, +W: Nat, hW: {PN.D(32n, 1n) == W : Nat}, +X: Nat, h: PN.Le(W, X)) -> PN.Le(Lim.bytes(lim), X):
  PN.le_trans(Lim.bytes(lim), W, X, lb.top(lim, W, hW), h)

# an emit whose next cell is 214748365 = 1 + P or more, where 16 + 20 P = 2^32:
# 20 nx is at least 2^32 (P stays a variable too)
def eb.big(+nx: U32, +lim: U32, +P: Nat, +W: Nat, hW: {PN.D(32n, 1n) == W : Nat}, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == W : Nat},
  +eP: {U32.to_nat(214748365) == 1n+P : Nat}, e: {U32.is_lt(nx, 214748365) == False{} : Bool}) -> PN.Le(Lim.bytes(lim), Nat.mul(20n, U32.to_nat(nx))):
  +hk = PN.le_rw_l(U32.to_nat(214748365), 1n+P, U32.to_nat(nx), eP,
    rel.nlt(U32.cmp(nx, 214748365), U32.to_nat(nx), U32.to_nat(214748365), PN.U32.rel(nx, 214748365), e))
  +ht = PN.le_rw_r(PH.H.t20(1n+P), PH.H.t20(U32.to_nat(nx)), Nat.mul(20n, U32.to_nat(nx)), t20.mul(U32.to_nat(nx)),
    PH.H.t20_mono(1n+P, U32.to_nat(nx), hk))
  +hw = PN.le_rw_l(Nat.add(PH.H.W(4n), PH.H.t20(P)), W, 20n+PH.H.t20(P), hP, PN.le_add_l(4n, PH.H.t20(P)))
  lb.le(lim, W, hW, Nat.mul(20n, U32.to_nat(nx)), PN.le_trans(W, 20n+PH.H.t20(P), Nat.mul(20n, U32.to_nat(nx)), hw, ht))

# eb.big at P = H.pat(7) and W = 2^32
def eb.big7(+nx: U32, +lim: U32, e: {U32.is_lt(nx, 214748365) == False{} : Bool}) -> PN.Le(Lim.bytes(lim), Nat.mul(20n, U32.to_nat(nx))):
  eb.big(nx, lim, PH.H.pat(7n), PH.H.W(32n), Equal.sym(Nat, PH.H.W(32n), PN.D(32n, 1n), w.d(32n)), PH.H.hP(), lit.val(), e)

# the byte of an emit is at most 20 nx + outn
def eb.sum(+nx: U32, +outn: U32) -> PN.Le(U32.to_nat(U32.add(Cr.Cir.at(nx), outn)), Nat.add(Nat.mul(20n, U32.to_nat(nx)), U32.to_nat(outn))):
  PN.le_trans(U32.to_nat(U32.add(Cr.Cir.at(nx), outn)), Nat.add(U32.to_nat(Cr.Cir.at(nx)), U32.to_nat(outn)),
    Nat.add(Nat.mul(20n, U32.to_nat(nx)), U32.to_nat(outn)), add.le(Cr.Cir.at(nx), outn),
    PN.add_mono(U32.to_nat(Cr.Cir.at(nx)), Nat.mul(20n, U32.to_nat(nx)), U32.to_nat(outn), U32.to_nat(outn), at.le(nx), PN.le_refl(U32.to_nat(outn))))

# an emit whose byte wraps W = 2^32: EB
def eb.wrap(+nx: U32, +outn: U32, +lim: U32, +W: Nat, hW: {PN.D(32n, 1n) == W : Nat}, hW2: {W == PH.H.W(32n) : Nat},
  e: {U32.is_ge(U32.add(Cr.Cir.at(nx), outn), outn) == False{} : Bool}) -> EB(lim, nx, outn):
  lb.le(lim, W, hW, Nat.add(Nat.mul(20n, U32.to_nat(nx)), U32.to_nat(outn)),
    PN.le_trans(W, Nat.add(U32.to_nat(Cr.Cir.at(nx)), U32.to_nat(outn)), Nat.add(Nat.mul(20n, U32.to_nat(nx)), U32.to_nat(outn)),
      add.wrap(Cr.Cir.at(nx), outn, W, hW2, e),
      PN.add_mono(U32.to_nat(Cr.Cir.at(nx)), Nat.mul(20n, U32.to_nat(nx)), U32.to_nat(outn), U32.to_nat(outn), at.le(nx), PN.le_refl(U32.to_nat(outn)))))

# eb.wrap at W = 2^32
def eb.wrap32(+nx: U32, +outn: U32, +lim: U32, e: {U32.is_ge(U32.add(Cr.Cir.at(nx), outn), outn) == False{} : Bool}) -> EB(lim, nx, outn):
  eb.wrap(nx, outn, lim, PH.H.W(32n), Equal.sym(Nat, PH.H.W(32n), PN.D(32n, 1n), w.d(32n)), {==}, e)

# the emit's test fails: EB
def eb.test(c: Bool, +nx: U32, +outn: U32, +lim: U32, ec: {U32.is_lt(nx, 214748365) == c : Bool},
  e: {Bool.and(c, U32.is_ge(U32.add(Cr.Cir.at(nx), outn), outn)) == False{} : Bool}) -> EB(lim, nx, outn):
  match c:
    case False{}:
      PN.le_trans(Lim.bytes(lim), Nat.mul(20n, U32.to_nat(nx)), Nat.add(Nat.mul(20n, U32.to_nat(nx)), U32.to_nat(outn)), eb.big7(nx, lim, ec),
        PN.le_add_r(Nat.mul(20n, U32.to_nat(nx)), U32.to_nat(outn)))
    case True{}:
      eb.wrap32(nx, outn, lim, e)

# room for the byte b fails only when lim can not grow to it: the limit has at
# most b bytes
def room.grow(i: Bool, g: Bool, +p: U32, +nd: U32, e: {Cr.Cir.room.if(i, g, p, nd) == None{} : Maybe<&2, U32>}) -> {g == False{} : Bool}:
  match i g:
    case True{} _:
      Empty.absurd({g == False{} : Bool}, some_ne_none(p, e))
    case False{} True{}:
      Empty.absurd({True{} == False{} : Bool}, some_ne_none(nd, e))
    case False{} False{}:
      {==}

def eb.room(+b: U32, +pg: U32, +lim: U32, e: {Cr.Cir.room(b, pg, lim) == None{} : Maybe<&2, U32>}) -> PN.Le(Lim.bytes(lim), U32.to_nat(b)):
  +s = U32.shrn(b, 16n)
  +nd = U32.inc(s)
  +eg = room.grow(U32.is_le(nd, pg), U32.is_le(nd, lim), pg, nd, e)
  +hl = PN.le_trans(1n+U32.to_nat(lim), U32.to_nat(nd), 1n+U32.to_nat(s),
    rel.nle(U32.cmp(nd, lim), U32.to_nat(nd), U32.to_nat(lim), PN.U32.rel(nd, lim), eg), PN.U32.inc_le(s))
  PN.le_trans(Lim.bytes(lim), PN.D(16n, U32.to_nat(s)), U32.to_nat(b),
    D.mono(16n, U32.to_nat(Wa.Wasm.min.if(Cmp.is_le(U32.cmp(lim, 65536)), lim, 65536)), U32.to_nat(s),
      PN.le_trans(U32.to_nat(Wa.Wasm.min.if(Cmp.is_le(U32.cmp(lim, 65536)), lim, 65536)), U32.to_nat(lim), U32.to_nat(s),
        min.l.go(Cmp.is_le(U32.cmp(lim, 65536)), lim, 65536, {==}), hl)),
    shrn.down(16n, b))

# Runs
# ----
#
# Wp(o, K, H): the run o goes on with a state of which K holds, halts with a
# status and a state of which H holds, or runs out of memory; it never traps
# and never runs out of fuel. A run needs fuel of the form 1 + f to take a
# step. The registers of a state are RG: the registers xs with the spine of
# their first 63 made explicit, and those that M.out sets (oc, ow, ov, oi,
# t1, t2) put in, so that reading and setting a register computes.

def Wp(o: Cr.Cir.Out, K: Cr.Cir.State -> Type, H: U32 -> Cr.Cir.State -> Type, O: Type) -> Type:
  match o:
    case Cr.Cir.Out.next{st}:
      K(st)
    case Cr.Cir.Out.halt{s, st}:
      H(s, st)
    case Cr.Cir.Out.out_of_memory{}:
      O
    case Cr.Cir.Out.trap{}:
      Empty
    case Cr.Cir.Out.not_done{}:
      Empty

def Wp.then(o: Cr.Cir.Out, -k: Cr.Cir.State -> Cr.Cir.Out, -K: Cr.Cir.State -> Type, -H: U32 -> Cr.Cir.State -> Type, -O: Type,
  h: Wp(o, t => Wp(k(t), K, H, O), H, O)) -> Wp(Cr.Cir.exec.then(o, k), K, H, O):
  match o:
    case Cr.Cir.Out.next{st}:
      h
    case Cr.Cir.Out.halt{s, st}:
      h
    case Cr.Cir.Out.out_of_memory{}:
      h
    case Cr.Cir.Out.trap{}:
      match h:
    case Cr.Cir.Out.not_done{}:
      match h:

# a then b
def Wp.seq(+f: Nat, +a: Cr.Cir.Stmt, +b: Cr.Cir.Stmt, +st: Cr.Cir.State, -K: Cr.Cir.State -> Type, -H: U32 -> Cr.Cir.State -> Type, -O: Type,
  h: Wp(Cr.Cir.exec(1n+f, a, st), t => Wp(Cr.Cir.exec(1n+f, b, t), K, H, O), H, O)) -> Wp(Cr.Cir.exec(1n+f, Cr.Cir.Stmt.seq{a, b}, st), K, H, O):
  Wp.then(Cr.Cir.exec(1n+f, a, st), t => Cr.Cir.exec(1n+f, b, t), K, H, O, h)

# the parts of a state
def St.rg(st: Cr.Cir.State) -> List<&2, U32>:
  match st:
    case Cr.Cir.State{x, _, _, _, _, _, _, _, _, _}:
      x

def St.cl(st: Cr.Cir.State) -> Cr.Cir.Cells:
  match st:
    case Cr.Cir.State{_, x, _, _, _, _, _, _, _, _}:
      x

def St.nx(st: Cr.Cir.State) -> U32:
  match st:
    case Cr.Cir.State{_, _, x, _, _, _, _, _, _, _}:
      x

def St.fs(st: Cr.Cir.State) -> U32:
  match st:
    case Cr.Cir.State{_, _, _, x, _, _, _, _, _, _}:
      x

def St.im(st: Cr.Cir.State) -> U32:
  match st:
    case Cr.Cir.State{_, _, _, _, x, _, _, _, _, _}:
      x

def St.pg(st: Cr.Cir.State) -> U32:
  match st:
    case Cr.Cir.State{_, _, _, _, _, x, _, _, _, _}:
      x

def St.lim(st: Cr.Cir.State) -> U32:
  match st:
    case Cr.Cir.State{_, _, _, _, _, _, x, _, _, _}:
      x

def St.inp(st: Cr.Cir.State) -> List<&2, Word(8n)>:
  match st:
    case Cr.Cir.State{_, _, _, _, _, _, _, x, _, _}:
      x

def St.out(st: Cr.Cir.State) -> List<&2, Word(8n)>:
  match st:
    case Cr.Cir.State{_, _, _, _, _, _, _, _, x, _}:
      x

def St.outn(st: Cr.Cir.State) -> U32:
  match st:
    case Cr.Cir.State{_, _, _, _, _, _, _, _, _, x}:
      x

# the cell i is one that the state lets the machine read
def St.ok(+i: U32, +st: Cr.Cir.State) -> Bool:
  Cr.Cir.is_cell(i, St.im(st), St.fs(st), St.nx(st))

# the registers
def Rg.hd(xs: List<&2, U32>) -> U32:
  match xs:
    case Nil{}:
      0
    case Con{h, _}:
      h

def Rg.tl(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{_, t}:
      t

def Rg.pre(n: Nat, +xs: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Con{Rg.hd(xs), Rg.pre(p, Rg.tl(xs))}

def Rg.drop(n: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      xs
    case 1n+p:
      Rg.drop(p, Rg.tl(xs))

def Rg.sp(+xs: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, Rg.pre(63n, xs), Rg.drop(63n, xs))

# a list of n registers or more is its first n, then the rest
def Rg.sp_eq(n: Nat, +xs: List<&2, U32>, h: PN.Le(n, List.length(&2, U32, xs))) ->
  {List.append(&2, U32, Rg.pre(n, xs), Rg.drop(n, xs)) == xs : List<&2, U32>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match xs:
        case Nil{}:
          Empty.absurd({List.append(&2, U32, Rg.pre(1n+p, Nil{}), Rg.drop(1n+p, Nil{})) == Nil{} : List<&2, U32>}, h)
        case Con{+x, +t}:
          %Rg.sp_eq(p, t, h) : {Con{x, List.append(&2, U32, Rg.pre(p, t), Rg.drop(p, t))} == Con{x, _} : List<&2, U32>}
          {==}

def RG(+xs: List<&2, U32>, +oc: U32, +ow: U32, +ov: U32, +oi: U32, +t1: U32, +t2: U32) -> List<&2, U32>:
  List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32,
    Rg.sp(xs), 45n, oc), 46n, ow), 47n, ov), 48n, oi), 61n, t1), 62n, t2)

# the state b with the registers of M.out, the pages and the output
def ST(+b: Cr.Cir.State, +oc: U32, +ow: U32, +ov: U32, +oi: U32, +t1: U32, +t2: U32, +pg: U32, +out: List<&2, Word(8n)>, +outn: U32) ->
  Cr.Cir.State:
  Cr.Cir.State{RG(St.rg(b), oc, ow, ov, oi, t1, t2), St.cl(b), St.nx(b), St.fs(b), St.im(b), pg, St.lim(b), St.inp(b), out, outn}

# the state after the byte v goes out, with p pages
def St.emit(st: Cr.Cir.State, +p: U32, +v: U32) -> Cr.Cir.State:
  match st:
    case Cr.Cir.State{rg, cl, nx, fs, im, _, lim, inp, out, outn}:
      Cr.Cir.State{rg, cl, nx, fs, im, p, lim, inp, Con{Sd.Byte.from_u32(v), out}, U32.inc(outn)}

# the field k of the cell that e gives
def ev.f(+k: Nat, +e: Cr.Cir.Expr, +st: Cr.Cir.State, +i: U32, +ei: {Some{i} == Cr.Cir.eval(e, st) : Maybe<&2, U32>},
  +ec: {True{} == St.ok(i, st) : Bool}) -> {Some{Fd(k, St.cl(st), i)} == Cr.Cir.eval(Cr.Cir.Expr.field{k, e}, st) : Maybe<&2, U32>}:
  match st:
    case Cr.Cir.State{+rg, +cl, +nx, +fs, +im, +pg, +lim, +inp, +out, +outn}:
      %ei : {Some{Fd(k, cl, i)} == Cr.Cir.eval.field(k, _, Cr.Cir.State{rg, cl, nx, fs, im, pg, lim, inp, out, outn}) : Maybe<&2, U32>}
      %ec : {Some{Fd(k, cl, i)} == Cr.Cir.eval.field.if(_, k, cl, i) : Maybe<&2, U32>}
      {==}

def and_u32(a: Bool, b: Bool) -> {Bool.to_u32(Bool.and(a, b)) == U32.and(Bool.to_u32(a), Bool.to_u32(b)) : U32}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def or_u32(a: Bool, b: Bool) -> {Bool.to_u32(Bool.or(a, b)) == U32.or(Bool.to_u32(a), Bool.to_u32(b)) : U32}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# M.pair on the cell of register r
def ev.pair(+r: Nat, +st: Cr.Cir.State, +i: U32, +er: {Some{i} == Cr.Cir.eval(Mc.M.g(r), st) : Maybe<&2, U32>},
  +ec: {True{} == St.ok(i, st) : Bool}) -> {Some{Bool.to_u32(Pm(St.cl(st), i))} == Cr.Cir.eval(Mc.M.pair(r), st) : Maybe<&2, U32>}:
  %ev.f(0n, Mc.M.g(r), st, i, er, ec) :
    {Some{Bool.to_u32(Pm(St.cl(st), i))} == Cr.Cir.eval.op(Wa.Wasm.Op.eq{}, Cr.Cir.eval.op(Wa.Wasm.Op.and{}, _, Some{255}), Some{74}) : Maybe<&2, U32>}
  {==}

# M.is_lab on field k of the cell of register r
def ev.islab(+k: Nat, +r: Nat, +n: U32, +st: Cr.Cir.State, +i: U32, +er: {Some{i} == Cr.Cir.eval(Mc.M.g(r), st) : Maybe<&2, U32>},
  +ec: {True{} == St.ok(i, st) : Bool}, +eck: {True{} == St.ok(Fd(k, St.cl(st), i), st) : Bool}) ->
  {Some{Bool.to_u32(Bool.and(Lm(St.cl(st), Fd(k, St.cl(st), i)), U32.is_eq(Fd(2n, St.cl(st), Fd(k, St.cl(st), i)), n)))} == Cr.Cir.eval(Mc.M.is_lab(Mc.M.f(k, Mc.M.g(r)), n), st) : Maybe<&2, U32>}:
  +m = St.cl(st)
  +j = Fd(k, m, i)
  +ej = ev.f(k, Mc.M.g(r), st, i, er, ec)
  %ev.f(0n, Mc.M.f(k, Mc.M.g(r)), st, j, ej, eck) :
    {Some{Bool.to_u32(Bool.and(Lm(m, j), U32.is_eq(Fd(2n, m, j), n)))} == Cr.Cir.eval.op(Wa.Wasm.Op.and{}, Cr.Cir.eval.op(Wa.Wasm.Op.eq{}, Cr.Cir.eval.op(Wa.Wasm.Op.and{}, _, Some{63}), Some{13}),
      Cr.Cir.eval.op(Wa.Wasm.Op.eq{}, Cr.Cir.eval(Mc.M.f(2n, Mc.M.f(k, Mc.M.g(r))), st), Some{n})) : Maybe<&2, U32>}
  %ev.f(2n, Mc.M.f(k, Mc.M.g(r)), st, j, ej, eck) :
    {Some{Bool.to_u32(Bool.and(Lm(m, j), U32.is_eq(Fd(2n, m, j), n)))} == Cr.Cir.eval.op(Wa.Wasm.Op.and{}, Some{Bool.to_u32(Lm(m, j))},
      Cr.Cir.eval.op(Wa.Wasm.Op.eq{}, _, Some{n})) : Maybe<&2, U32>}
  %and_u32(Lm(m, j), U32.is_eq(Fd(2n, m, j), n)) : {Some{Bool.to_u32(Bool.and(Lm(m, j), U32.is_eq(Fd(2n, m, j), n)))} == Some{_} : Maybe<&2, U32>}
  {==}

# M.eq(M.tag(field k), lab) on the cell of register r
def ev.tag(+k: Nat, +r: Nat, +st: Cr.Cir.State, +i: U32, +er: {Some{i} == Cr.Cir.eval(Mc.M.g(r), st) : Maybe<&2, U32>},
  +ec: {True{} == St.ok(i, st) : Bool}, +eck: {True{} == St.ok(Fd(k, St.cl(st), i), st) : Bool}) ->
  {Some{Bool.to_u32(Lm(St.cl(st), Fd(k, St.cl(st), i)))} == Cr.Cir.eval(Mc.M.eq(Mc.M.tag(Mc.M.f(k, Mc.M.g(r))), Mc.M.c(13)), st) : Maybe<&2, U32>}:
  +m = St.cl(st)
  +j = Fd(k, m, i)
  %ev.f(0n, Mc.M.f(k, Mc.M.g(r)), st, j, ev.f(k, Mc.M.g(r), st, i, er, ec), eck) :
    {Some{Bool.to_u32(Lm(m, j))} == Cr.Cir.eval.op(Wa.Wasm.Op.eq{}, Cr.Cir.eval.op(Wa.Wasm.Op.and{}, _, Some{63}), Some{13}) : Maybe<&2, U32>}
  {==}

# field k2 of field k1 of the cell of register r
def ev.ff(+k1: Nat, +k2: Nat, +r: Nat, +st: Cr.Cir.State, +i: U32, +er: {Some{i} == Cr.Cir.eval(Mc.M.g(r), st) : Maybe<&2, U32>},
  +ec: {True{} == St.ok(i, st) : Bool}, +eck: {True{} == St.ok(Fd(k1, St.cl(st), i), st) : Bool}) ->
  {Some{Fd(k2, St.cl(st), Fd(k1, St.cl(st), i))} == Cr.Cir.eval(Mc.M.f(k2, Mc.M.f(k1, Mc.M.g(r))), st) : Maybe<&2, U32>}:
  ev.f(k2, Mc.M.f(k1, Mc.M.g(r)), st, Fd(k1, St.cl(st), i), ev.f(k1, Mc.M.g(r), st, i, er, ec), eck)

# Statements
def Wp.set(+f: Nat, +r: Nat, +e: Cr.Cir.Expr, +st: Cr.Cir.State, -K: Cr.Cir.State -> Type, -H: U32 -> Cr.Cir.State -> Type, -O: Type, +v: U32,
  +ev: {Some{v} == Cr.Cir.eval(e, st) : Maybe<&2, U32>}, h: Wp(Cr.Cir.exec.set(r, Some{v}, st), K, H, O)) ->
  Wp(Cr.Cir.exec(1n+f, Cr.Cir.Stmt.set{r, e}, st), K, H, O):
  %ev : Wp(Cr.Cir.exec.set(r, _, st), K, H, O)
  h

# X when b holds, else Y
def IFT(b: Bool, X: Type, Y: Type) -> Type:
  match b:
    case True{}:
      X
    case False{}:
      Y

# the case of b, with a passed to it
def CasesK(b: Bool, -A: Type, a: A, -X: Type, -Y: Type, t: A -> {b == True{} : Bool} -> X, e: A -> {b == False{} : Bool} -> Y) ->
  IFT(b, X, Y):
  match b:
    case True{}:
      t(a, {==})
    case False{}:
      e(a, {==})

def Wp.if(+f: Nat, +c: Cr.Cir.Expr, +t: Cr.Cir.Stmt, +e: Cr.Cir.Stmt, +st: Cr.Cir.State, -K: Cr.Cir.State -> Type, -H: U32 -> Cr.Cir.State -> Type, -O: Type,
  b: Bool, +ev: {Some{Bool.to_u32(b)} == Cr.Cir.eval(c, st) : Maybe<&2, U32>},
  g: IFT(b, Wp(Cr.Cir.exec(1n+f, t, st), K, H, O), Wp(Cr.Cir.exec(1n+f, e, st), K, H, O))) ->
  Wp(Cr.Cir.exec(1n+f, Cr.Cir.Stmt.if{c, t, e}, st), K, H, O):
  match b:
    case True{}:
      %ev : Wp(Cr.Cir.exec.if(_, u => Cr.Cir.exec(1n+f, t, st), u => Cr.Cir.exec(1n+f, e, st)), K, H, O)
      g
    case False{}:
      %ev : Wp(Cr.Cir.exec.if(_, u => Cr.Cir.exec(1n+f, t, st), u => Cr.Cir.exec(1n+f, e, st)), K, H, O)
      g

def Wp.need(+f: Nat, +c: Cr.Cir.Expr, +t: Cr.Cir.Stmt, +st: Cr.Cir.State, -K: Cr.Cir.State -> Type, -H: U32 -> Cr.Cir.State -> Type, -O: Type,
  b: Bool, +ev: {Some{Bool.to_u32(b)} == Cr.Cir.eval(c, st) : Maybe<&2, U32>},
  g: IFT(b, Wp(Cr.Cir.exec(1n+f, t, st), K, H, O), H(2, st))) ->
  Wp(Cr.Cir.exec(1n+f, Mc.M.need(c, t), st), K, H, O):
  Wp.if(f, c, t, Mc.M.halt(2), st, K, H, O, b, ev, g)

def Wp.emit.of(pages: Maybe<&2, U32>, +v: U32, +st: Cr.Cir.State, -K: Cr.Cir.State -> Type, -H: U32 -> Cr.Cir.State -> Type, -O: Type,
  hn: {pages == None{} : Maybe<&2, U32>} -> O, h: @p: U32 -> K(St.emit(st, p, v))) -> Wp(Cr.Cir.exec.emit.of(pages, v, st), K, H, O):
  match pages:
    case None{}:
      hn({==})
    case Some{+p}:
      match st:
        case Cr.Cir.State{+rg, +cl, +nx, +fs, +im, +pg, +lim, +inp, +out, +outn}:
          h(p)

def Wp.emit.if(ok: Bool, +bb: U32, +v: U32, +st: Cr.Cir.State, -K: Cr.Cir.State -> Type, -H: U32 -> Cr.Cir.State -> Type, -O: Type,
  ef: {ok == False{} : Bool} -> EB(St.lim(st), St.nx(st), St.outn(st)),
  er: {Cr.Cir.room(bb, St.pg(st), St.lim(st)) == None{} : Maybe<&2, U32>} -> EB(St.lim(st), St.nx(st), St.outn(st)),
  ho: EB(St.lim(st), St.nx(st), St.outn(st)) -> O, h: @p: U32 -> K(St.emit(st, p, v))) -> Wp(Cr.Cir.exec.emit.if(ok, bb, v, st), K, H, O):
  match ok:
    case False{}:
      ho(ef({==}))
    case True{}:
      match st:
        case Cr.Cir.State{+rg, +cl, +nx, +fs, +im, +pg, +lim, +inp, +out, +outn}:
          Wp.emit.of(Cr.Cir.room(bb, pg, lim), v, Cr.Cir.State{rg, cl, nx, fs, im, pg, lim, inp, out, outn}, K, H, O, e => ho(er(e)), h)

def Wp.emit(+f: Nat, +e: Cr.Cir.Expr, +st: Cr.Cir.State, -K: Cr.Cir.State -> Type, -H: U32 -> Cr.Cir.State -> Type, -O: Type, +v: U32,
  +ev: {Some{v} == Cr.Cir.eval(e, st) : Maybe<&2, U32>}, ho: EB(St.lim(st), St.nx(st), St.outn(st)) -> O, h: @p: U32 -> K(St.emit(st, p, v))) ->
  Wp(Cr.Cir.exec(1n+f, Cr.Cir.Stmt.emit{e}, st), K, H, O):
  match st:
    case Cr.Cir.State{+rg, +cl, +nx, +fs, +im, +pg, +lim, +inp, +out, +outn}:
      +bb = U32.add(Cr.Cir.at(nx), outn)
      %ev : Wp(Cr.Cir.exec.emit(_, Cr.Cir.State{rg, cl, nx, fs, im, pg, lim, inp, out, outn}), K, H, O)
      Wp.emit.if(Bool.and(U32.is_lt(nx, 214748365), U32.is_ge(bb, outn)), bb, v,
        Cr.Cir.State{rg, cl, nx, fs, im, pg, lim, inp, out, outn}, K, H, O,
        ef => eb.test(U32.is_lt(nx, 214748365), nx, outn, lim, {==}, ef),
        er => PN.le_trans(Lim.bytes(lim), U32.to_nat(bb), Nat.add(Nat.mul(20n, U32.to_nat(nx)), U32.to_nat(outn)), eb.room(bb, pg, lim, er), eb.sum(nx, outn)),
        ho, h)

# ok, read with any fuel
def Pr(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def ok.isc(+n: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32,
  +h: {ok(n, m, ks, img, c, im, fs, nx) == True{} : Bool}) -> {True{} == Cr.Cir.is_cell(c, im, fs, nx) : Bool}:
  match n:
    case 0n:
      Empty.absurd({True{} == Cr.Cir.is_cell(c, im, fs, nx) : Bool}, ok.zero(m, ks, img, c, im, fs, nx, h))
    case 1n+f:
      Equal.sym(Bool, Cr.Cir.is_cell(c, im, fs, nx), True{}, ok.cell(f, m, ks, img, c, im, fs, nx, h))

def ok.L(+n: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32,
  +h: {ok(n, m, ks, img, c, im, fs, nx) == True{} : Bool}, +eP: {Pm(m, c) == True{} : Bool}) ->
  {ok(Pr(n), m, ks, img, Fd(2n, m, c), im, fs, nx) == True{} : Bool}:
  match n:
    case 0n:
      Empty.absurd({ok(0n, m, ks, img, Fd(2n, m, c), im, fs, nx) == True{} : Bool}, ok.zero(m, ks, img, c, im, fs, nx, h))
    case 1n+f:
      ok.l(f, m, ks, img, c, im, fs, nx, h, eP)

def ok.R(+n: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32,
  +h: {ok(n, m, ks, img, c, im, fs, nx) == True{} : Bool}, +eP: {Pm(m, c) == True{} : Bool}) ->
  {ok(Pr(n), m, ks, img, Fd(3n, m, c), im, fs, nx) == True{} : Bool}:
  match n:
    case 0n:
      Empty.absurd({ok(0n, m, ks, img, Fd(3n, m, c), im, fs, nx) == True{} : Bool}, ok.zero(m, ks, img, c, im, fs, nx, h))
    case 1n+f:
      ok.r(f, m, ks, img, c, im, fs, nx, h, eP)

# The bit
# -------

# the value of ov once the bit x is read, at the index oi
def OV(x: Bool, +ov: U32, +oi: U32) -> U32:
  match x:
    case True{}:
      U32.or(ov, Wa.Wasm.op(Wa.Wasm.Op.shl{}, 1, oi))
    case False{}:
      ov

def MB.o() -> Cr.Cir.Stmt:
  Mc.M.set(Mc.R.ov(), Mc.M.or(Mc.M.g(Mc.R.ov()), Mc.M.shl(Mc.M.c(1), Mc.M.g(Mc.R.oi()))))

def MB.b() -> Cr.Cir.Stmt:
  Mc.M.need(Mc.M.or(Mc.M.eq(Mc.M.g(Mc.R.t2()), Mc.M.c(Mc.N.true())), Mc.M.eq(Mc.M.g(Mc.R.t2()), Mc.M.c(Mc.N.false()))),
    Mc.M.when(Mc.M.eq(Mc.M.g(Mc.R.t2()), Mc.M.c(Mc.N.true())), MB.o()))

def MB.a() -> Cr.Cir.Stmt:
  Mc.M.set(Mc.R.t2(), Mc.M.f(2n, Mc.M.f(2n, Mc.M.g(Mc.R.t1()))))

def MB.s2() -> Cr.Cir.Stmt:
  Mc.M.need(Mc.M.eq(Mc.M.tag(Mc.M.f(2n, Mc.M.g(Mc.R.t1()))), Mc.M.c(Mc.T.lab())), Mc.M.do([MB.a(), MB.b()]))

def MB.s1() -> Cr.Cir.Stmt:
  Mc.M.need(Mc.M.last(Mc.R.t1()), MB.s2())

# CB's value, once its tests pass
def CB.ok(+m: Cr.Cir.Cells, +c: U32, +eP: {Pm(m, c) == True{} : Bool}, +eL: {LAST(m, c) == True{} : Bool},
  +eM: {Lm(m, Fd(2n, m, c)) == True{} : Bool},
  +eO: {Bool.or(U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 5), U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 6)) == True{} : Bool}) ->
  {CB(m, c) == Some{U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 5)} : Maybe<&2, Bool>}:
  +x2 = Fd(2n, m, Fd(2n, m, c))
  %Equal.sym(Bool, Pm(m, c), True{}, eP) : {CB.p(_, m, c) == Some{U32.is_eq(x2, 5)} : Maybe<&2, Bool>}
  %Equal.sym(Bool, LAST(m, c), True{}, eL) : {CB.l(_, m, c) == Some{U32.is_eq(x2, 5)} : Maybe<&2, Bool>}
  %Equal.sym(Bool, Lm(m, Fd(2n, m, c)), True{}, eM) : {CB.x(_, x2) == Some{U32.is_eq(x2, 5)} : Maybe<&2, Bool>}
  %Equal.sym(Bool, Bool.or(U32.is_eq(x2, 5), U32.is_eq(x2, 6)), True{}, eO) : {CB.t(_, U32.is_eq(x2, 5)) == Some{U32.is_eq(x2, 5)} : Maybe<&2, Bool>}
  {==}

def CB.n1(+m: Cr.Cir.Cells, +c: U32, +eP: {Pm(m, c) == False{} : Bool}) -> {CB(m, c) == None{} : Maybe<&2, Bool>}:
  Equal.cong(Bool, Maybe<&2, Bool>, x => CB.p(x, m, c), Pm(m, c), False{}, eP)

def CB.n2(+m: Cr.Cir.Cells, +c: U32, +eP: {Pm(m, c) == True{} : Bool}, +eL: {LAST(m, c) == False{} : Bool}) -> {CB(m, c) == None{} : Maybe<&2, Bool>}:
  %Equal.sym(Bool, Pm(m, c), True{}, eP) : {CB.p(_, m, c) == None{} : Maybe<&2, Bool>}
  Equal.cong(Bool, Maybe<&2, Bool>, x => CB.l(x, m, c), LAST(m, c), False{}, eL)

def CB.n3(+m: Cr.Cir.Cells, +c: U32, +eP: {Pm(m, c) == True{} : Bool}, +eL: {LAST(m, c) == True{} : Bool},
  +eM: {Lm(m, Fd(2n, m, c)) == False{} : Bool}) -> {CB(m, c) == None{} : Maybe<&2, Bool>}:
  %Equal.sym(Bool, Pm(m, c), True{}, eP) : {CB.p(_, m, c) == None{} : Maybe<&2, Bool>}
  %Equal.sym(Bool, LAST(m, c), True{}, eL) : {CB.l(_, m, c) == None{} : Maybe<&2, Bool>}
  Equal.cong(Bool, Maybe<&2, Bool>, x => CB.x(x, Fd(2n, m, Fd(2n, m, c))), Lm(m, Fd(2n, m, c)), False{}, eM)

def CB.n4(+m: Cr.Cir.Cells, +c: U32, +eP: {Pm(m, c) == True{} : Bool}, +eL: {LAST(m, c) == True{} : Bool},
  +eM: {Lm(m, Fd(2n, m, c)) == True{} : Bool},
  +eO: {Bool.or(U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 5), U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 6)) == False{} : Bool}) ->
  {CB(m, c) == None{} : Maybe<&2, Bool>}:
  +x2 = Fd(2n, m, Fd(2n, m, c))
  %Equal.sym(Bool, Pm(m, c), True{}, eP) : {CB.p(_, m, c) == None{} : Maybe<&2, Bool>}
  %Equal.sym(Bool, LAST(m, c), True{}, eL) : {CB.l(_, m, c) == None{} : Maybe<&2, Bool>}
  %Equal.sym(Bool, Lm(m, Fd(2n, m, c)), True{}, eM) : {CB.x(_, x2) == None{} : Maybe<&2, Bool>}
  Equal.cong(Bool, Maybe<&2, Bool>, x => CB.t(x, U32.is_eq(x2, 5)), Bool.or(U32.is_eq(x2, 5), U32.is_eq(x2, 6)), False{}, eO)

# X(x) for Some{x}, else Y
def MC(r: Maybe<&2, Bool>, X: Bool -> Type, Y: Type) -> Type:
  match r:
    case Some{x}:
      X(x)
    case None{}:
      Y

# the case of r, with a passed to it
def CasesM(r: Maybe<&2, Bool>, -A: Type, a: A, -X: Bool -> Type, -Y: Type, s: A -> @x: Bool -> {r == Some{x} : Maybe<&2, Bool>} -> X(x),
  n: A -> {r == None{} : Maybe<&2, Bool>} -> Y) -> MC(r, X, Y):
  match r:
    case Some{x}:
      s(a, x, {==})
    case None{}:
      n(a, {==})

# what the run of a bit goes on with, by what CB reads: its value in ov, or
# no result
def MB.Kc(+b: Cr.Cir.State, +oc: U32, +ow: U32, +ov: U32, +oi: U32, +c: U32, +pg: U32, +out: List<&2, Word(8n)>, +outn: U32,
  -K: Cr.Cir.State -> Type, -H: U32 -> Cr.Cir.State -> Type) -> Type:
  @r: Maybe<&2, Bool> -> {CB(St.cl(b), c) == r : Maybe<&2, Bool>} ->
    MC(r, x => K(ST(b, oc, ow, OV(x, ov, oi), oi, c, Fd(2n, St.cl(b), Fd(2n, St.cl(b), c)), pg, out, outn)), @st: Cr.Cir.State -> H(2, st))

# M.out.bit on the cell c in t1: the bit that CB reads goes into ov, or the
# run ends with no result
def MB(+f: Nat, +b: Cr.Cir.State, +oc: U32, +ow: U32, +ov: U32, +oi: U32, +c: U32, +t2: U32, +pg: U32, +out: List<&2, Word(8n)>, +outn: U32,
  +nb: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, -K: Cr.Cir.State -> Type, -H: U32 -> Cr.Cir.State -> Type, -O: Type,
  +hok: {ok(nb, St.cl(b), ks, img, c, St.im(b), St.fs(b), St.nx(b)) == True{} : Bool},
  kk: MB.Kc(b, oc, ow, ov, oi, c, pg, out, outn, K, H)) ->
  Wp(Cr.Cir.exec(1n+f, Mc.M.out.bit(), ST(b, oc, ow, ov, oi, c, t2, pg, out, outn)), K, H, O):
  +m = St.cl(b)
  +s0 = ST(b, oc, ow, ov, oi, c, t2, pg, out, outn)
  +x2 = Fd(2n, m, Fd(2n, m, c))
  +s1 = ST(b, oc, ow, ov, oi, c, x2, pg, out, outn)
  +hc = ok.isc(nb, m, ks, img, c, St.im(b), St.fs(b), St.nx(b), hok)
  -A = MB.Kc(b, oc, ow, ov, oi, c, pg, out, outn, K, H)
  Wp.need(f, Mc.M.pair(Mc.R.t1()), MB.s1(), s0, K, H, O, Pm(m, c), ev.pair(61n, s0, c, {==}, hc),
   CasesK(Pm(m, c), A, kk, Wp(Cr.Cir.exec(1n+f, MB.s1(), s0), K, H, O), H(2, s0),
    kk => +eP =>
      Wp.need(f, Mc.M.last(Mc.R.t1()), MB.s2(), s0, K, H, O, LAST(m, c),
        ev.islab(3n, 61n, 0, s0, c, {==}, hc, ok.isc(Pr(nb), m, ks, img, Fd(3n, m, c), St.im(b), St.fs(b), St.nx(b), ok.R(nb, m, ks, img, c, St.im(b), St.fs(b), St.nx(b), hok, eP))),
       CasesK(LAST(m, c), A, kk, Wp(Cr.Cir.exec(1n+f, MB.s2(), s0), K, H, O), H(2, s0),
        kk => +eL =>
          Wp.need(f, Mc.M.eq(Mc.M.tag(Mc.M.f(2n, Mc.M.g(Mc.R.t1()))), Mc.M.c(Mc.T.lab())), Mc.M.do([MB.a(), MB.b()]), s0, K, H, O, Lm(m, Fd(2n, m, c)),
            ev.tag(2n, 61n, s0, c, {==}, hc, ok.isc(Pr(nb), m, ks, img, Fd(2n, m, c), St.im(b), St.fs(b), St.nx(b), ok.L(nb, m, ks, img, c, St.im(b), St.fs(b), St.nx(b), hok, eP))),
           CasesK(Lm(m, Fd(2n, m, c)), A, kk, Wp(Cr.Cir.exec(1n+f, Mc.M.do([MB.a(), MB.b()]), s0), K, H, O), H(2, s0),
            kk => +eM =>
              Wp.seq(f, MB.a(), Mc.M.do([MB.b()]), s0, K, H, O,
                Wp.set(f, 62n, Mc.M.f(2n, Mc.M.f(2n, Mc.M.g(Mc.R.t1()))), s0, t => Wp(Cr.Cir.exec(1n+f, Mc.M.do([MB.b()]), t), K, H, O), H, O, x2,
                  ev.ff(2n, 2n, 61n, s0, c, {==}, hc, ok.isc(Pr(nb), m, ks, img, Fd(2n, m, c), St.im(b), St.fs(b), St.nx(b), ok.L(nb, m, ks, img, c, St.im(b), St.fs(b), St.nx(b), hok, eP))),
                  Wp.seq(f, MB.b(), Cr.Cir.Stmt.nop{}, s1, K, H, O,
                    Wp.need(f, Mc.M.or(Mc.M.eq(Mc.M.g(Mc.R.t2()), Mc.M.c(Mc.N.true())), Mc.M.eq(Mc.M.g(Mc.R.t2()), Mc.M.c(Mc.N.false()))),
                      Mc.M.when(Mc.M.eq(Mc.M.g(Mc.R.t2()), Mc.M.c(Mc.N.true())), MB.o()), s1, t => Wp(Cr.Cir.exec(1n+f, Cr.Cir.Stmt.nop{}, t), K, H, O), H, O,
                      Bool.or(U32.is_eq(x2, 5), U32.is_eq(x2, 6)),
                      Equal.cong(U32, Maybe<&2, U32>, x => Some{x}, Bool.to_u32(Bool.or(U32.is_eq(x2, 5), U32.is_eq(x2, 6))),
                        U32.or(Bool.to_u32(U32.is_eq(x2, 5)), Bool.to_u32(U32.is_eq(x2, 6))), or_u32(U32.is_eq(x2, 5), U32.is_eq(x2, 6))),
                     CasesK(Bool.or(U32.is_eq(x2, 5), U32.is_eq(x2, 6)), A, kk,
                      Wp(Cr.Cir.exec(1n+f, Mc.M.when(Mc.M.eq(Mc.M.g(Mc.R.t2()), Mc.M.c(Mc.N.true())), MB.o()), s1), t => Wp(Cr.Cir.exec(1n+f, Cr.Cir.Stmt.nop{}, t), K, H, O), H, O), H(2, s1),
                      kk => +eO =>
                        Wp.if(f, Mc.M.eq(Mc.M.g(Mc.R.t2()), Mc.M.c(Mc.N.true())), MB.o(), Cr.Cir.Stmt.nop{}, s1, t => Wp(Cr.Cir.exec(1n+f, Cr.Cir.Stmt.nop{}, t), K, H, O), H, O,
                          U32.is_eq(x2, 5), {==},
                         CasesK(U32.is_eq(x2, 5), A, kk,
                          Wp(Cr.Cir.exec(1n+f, MB.o(), s1), t => Wp(Cr.Cir.exec(1n+f, Cr.Cir.Stmt.nop{}, t), K, H, O), H, O),
                          Wp(Cr.Cir.exec(1n+f, Cr.Cir.Stmt.nop{}, s1), t => Wp(Cr.Cir.exec(1n+f, Cr.Cir.Stmt.nop{}, t), K, H, O), H, O),
                          kk => +eT =>
                            Wp.set(f, 47n, Mc.M.or(Mc.M.g(Mc.R.ov()), Mc.M.shl(Mc.M.c(1), Mc.M.g(Mc.R.oi()))), s1, t => Wp(Cr.Cir.exec(1n+f, Cr.Cir.Stmt.nop{}, t), K, H, O), H, O,
                              OV(True{}, ov, oi), {==},
                              kk(Some{True{}}, Equal.trans(Maybe<&2, Bool>, CB(m, c), Some{U32.is_eq(x2, 5)}, Some{True{}}, CB.ok(m, c, eP, eL, eM, eO),
                                Equal.cong(Bool, Maybe<&2, Bool>, x => Some{x}, U32.is_eq(x2, 5), True{}, eT)))),
                          kk => +eT =>
                            kk(Some{False{}}, Equal.trans(Maybe<&2, Bool>, CB(m, c), Some{U32.is_eq(x2, 5)}, Some{False{}}, CB.ok(m, c, eP, eL, eM, eO),
                              Equal.cong(Bool, Maybe<&2, Bool>, x => Some{x}, U32.is_eq(x2, 5), False{}, eT))))),
                      kk => +eO =>
                        kk(None{}, CB.n4(m, c, eP, eL, eM, eO), s1)))))),
            kk => +eM =>
              kk(None{}, CB.n3(m, c, eP, eL, eM), s0))),
        kk => +eL =>
          kk(None{}, CB.n2(m, c, eP, eL), s0))),
    kk => +eP =>
      kk(None{}, CB.n1(m, c, eP), s0)))

# The word
# --------

# a word is its bits, then its WNil
def CWt.nil(t: Maybe<&2, Word(0n)>) -> {t == CWt(0n, Some{WNil{}}, t) : Maybe<&2, Word(0n)>}:
  match t:
    case None{}:
      {==}
    case Some{y}:
      match y:
        case WNil{}:
          {==}

def CWt.w(-q: Nat, x: Bool, rb: Maybe<&2, Word(q)>, t: Maybe<&2, Word(0n)>) ->
  {W1.w(q, x, CWt(q, rb, t)) == CWt(1n+q, W1.w(q, x, rb), t) : Maybe<&2, Word(1n+q)>}:
  match rb:
    case None{}:
      {==}
    case Some{y}:
      match t:
        case None{}:
          {==}
        case Some{z}:
          {==}

def CWt.g(-q: Nat, g: Maybe<&2, Bool>, rb: Maybe<&2, Word(q)>, t: Maybe<&2, Word(0n)>) ->
  {W1.g(q, g, CWt(q, rb, t)) == CWt(1n+q, W1.g(q, g, rb), t) : Maybe<&2, Word(1n+q)>}:
  match g:
    case None{}:
      {==}
    case Some{x}:
      CWt.w(q, x, rb, t)

def CW.split(+p: Nat, +m: Cr.Cir.Cells, +c: U32) -> {CW(p, m, c) == CWt(p, CWb(p, m, c), CW(0n, m, Nx(p, m, c))) : Maybe<&2, Word(p)>}:
  match p:
    case 0n:
      CWt.nil(CW(0n, m, c))
    case 1n+q:
      %Equal.sym(Maybe<&2, Word(q)>, CW(q, m, CW.next(m, c)), CWt(q, CWb(q, m, CW.next(m, c)), CW(0n, m, Nx(q, m, CW.next(m, c)))), CW.split(q, m, CW.next(m, c))) :
        {W1.g(q, GB(m, c), _) == CWt(1n+q, W1.g(q, GB(m, c), CWb(q, m, CW.next(m, c))), CW(0n, m, Nx(q, m, CW.next(m, c)))) : Maybe<&2, Word(1n+q)>}
      CWt.g(q, GB(m, c), CWb(q, m, CW.next(m, c)), CW(0n, m, Nx(q, m, CW.next(m, c))))

# GB's value, once its tests pass, or none when one fails
def GB.ok(+m: Cr.Cir.Cells, +c: U32, +eP: {Pm(m, c) == True{} : Bool}, +eI: {ISLAB(m, c, 4) == True{} : Bool},
  +eF: {Pm(m, Fd(3n, m, c)) == True{} : Bool}, +x: Bool, +eB: {CB(m, Fd(2n, m, Fd(3n, m, c))) == Some{x} : Maybe<&2, Bool>},
  +eR: {Pm(m, Fd(3n, m, Fd(3n, m, c))) == True{} : Bool}, +eZ: {LAST(m, Fd(3n, m, Fd(3n, m, c))) == True{} : Bool}) ->
  {GB(m, c) == Some{x} : Maybe<&2, Bool>}:
  +fc = Fd(3n, m, c)
  +rc = Fd(3n, m, fc)
  %Equal.sym(Bool, Pm(m, c), True{}, eP) : {GB.p(_, m, c) == Some{x} : Maybe<&2, Bool>}
  %Equal.sym(Bool, ISLAB(m, c, 4), True{}, eI) : {GB.l(_, m, fc) == Some{x} : Maybe<&2, Bool>}
  %Equal.sym(Bool, Pm(m, fc), True{}, eF) : {GB.f(_, m, fc) == Some{x} : Maybe<&2, Bool>}
  %Equal.sym(Maybe<&2, Bool>, CB(m, Fd(2n, m, fc)), Some{x}, eB) : {GB.b(_, m, rc) == Some{x} : Maybe<&2, Bool>}
  %Equal.sym(Bool, Pm(m, rc), True{}, eR) : {GB.r(x, _, m, rc) == Some{x} : Maybe<&2, Bool>}
  %Equal.sym(Bool, LAST(m, rc), True{}, eZ) : {GB.z(x, _) == Some{x} : Maybe<&2, Bool>}
  {==}

def GB.n1(+m: Cr.Cir.Cells, +c: U32, +eP: {Pm(m, c) == False{} : Bool}) -> {GB(m, c) == None{} : Maybe<&2, Bool>}:
  Equal.cong(Bool, Maybe<&2, Bool>, y => GB.p(y, m, c), Pm(m, c), False{}, eP)

def GB.n2(+m: Cr.Cir.Cells, +c: U32, +eP: {Pm(m, c) == True{} : Bool}, +eI: {ISLAB(m, c, 4) == False{} : Bool}) ->
  {GB(m, c) == None{} : Maybe<&2, Bool>}:
  %Equal.sym(Bool, Pm(m, c), True{}, eP) : {GB.p(_, m, c) == None{} : Maybe<&2, Bool>}
  Equal.cong(Bool, Maybe<&2, Bool>, y => GB.l(y, m, Fd(3n, m, c)), ISLAB(m, c, 4), False{}, eI)

def GB.n3(+m: Cr.Cir.Cells, +c: U32, +eP: {Pm(m, c) == True{} : Bool}, +eI: {ISLAB(m, c, 4) == True{} : Bool},
  +eF: {Pm(m, Fd(3n, m, c)) == False{} : Bool}) -> {GB(m, c) == None{} : Maybe<&2, Bool>}:
  +fc = Fd(3n, m, c)
  %Equal.sym(Bool, Pm(m, c), True{}, eP) : {GB.p(_, m, c) == None{} : Maybe<&2, Bool>}
  %Equal.sym(Bool, ISLAB(m, c, 4), True{}, eI) : {GB.l(_, m, fc) == None{} : Maybe<&2, Bool>}
  Equal.cong(Bool, Maybe<&2, Bool>, y => GB.f(y, m, fc), Pm(m, fc), False{}, eF)

def GB.n4(+m: Cr.Cir.Cells, +c: U32, +eP: {Pm(m, c) == True{} : Bool}, +eI: {ISLAB(m, c, 4) == True{} : Bool},
  +eF: {Pm(m, Fd(3n, m, c)) == True{} : Bool}, +eB: {CB(m, Fd(2n, m, Fd(3n, m, c))) == None{} : Maybe<&2, Bool>}) ->
  {GB(m, c) == None{} : Maybe<&2, Bool>}:
  +fc = Fd(3n, m, c)
  %Equal.sym(Bool, Pm(m, c), True{}, eP) : {GB.p(_, m, c) == None{} : Maybe<&2, Bool>}
  %Equal.sym(Bool, ISLAB(m, c, 4), True{}, eI) : {GB.l(_, m, fc) == None{} : Maybe<&2, Bool>}
  %Equal.sym(Bool, Pm(m, fc), True{}, eF) : {GB.f(_, m, fc) == None{} : Maybe<&2, Bool>}
  Equal.cong(Maybe<&2, Bool>, Maybe<&2, Bool>, y => GB.b(y, m, Fd(3n, m, fc)), CB(m, Fd(2n, m, fc)), None{}, eB)

def GB.n5(+m: Cr.Cir.Cells, +c: U32, +eP: {Pm(m, c) == True{} : Bool}, +eI: {ISLAB(m, c, 4) == True{} : Bool},
  +eF: {Pm(m, Fd(3n, m, c)) == True{} : Bool}, +x: Bool, +eB: {CB(m, Fd(2n, m, Fd(3n, m, c))) == Some{x} : Maybe<&2, Bool>},
  +eR: {Pm(m, Fd(3n, m, Fd(3n, m, c))) == False{} : Bool}) -> {GB(m, c) == None{} : Maybe<&2, Bool>}:
  +fc = Fd(3n, m, c)
  +rc = Fd(3n, m, fc)
  %Equal.sym(Bool, Pm(m, c), True{}, eP) : {GB.p(_, m, c) == None{} : Maybe<&2, Bool>}
  %Equal.sym(Bool, ISLAB(m, c, 4), True{}, eI) : {GB.l(_, m, fc) == None{} : Maybe<&2, Bool>}
  %Equal.sym(Bool, Pm(m, fc), True{}, eF) : {GB.f(_, m, fc) == None{} : Maybe<&2, Bool>}
  %Equal.sym(Maybe<&2, Bool>, CB(m, Fd(2n, m, fc)), Some{x}, eB) : {GB.b(_, m, rc) == None{} : Maybe<&2, Bool>}
  Equal.cong(Bool, Maybe<&2, Bool>, y => GB.r(x, y, m, rc), Pm(m, rc), False{}, eR)

def GB.n6(+m: Cr.Cir.Cells, +c: U32, +eP: {Pm(m, c) == True{} : Bool}, +eI: {ISLAB(m, c, 4) == True{} : Bool},
  +eF: {Pm(m, Fd(3n, m, c)) == True{} : Bool}, +x: Bool, +eB: {CB(m, Fd(2n, m, Fd(3n, m, c))) == Some{x} : Maybe<&2, Bool>},
  +eR: {Pm(m, Fd(3n, m, Fd(3n, m, c))) == True{} : Bool}, +eZ: {LAST(m, Fd(3n, m, Fd(3n, m, c))) == False{} : Bool}) ->
  {GB(m, c) == None{} : Maybe<&2, Bool>}:
  +fc = Fd(3n, m, c)
  +rc = Fd(3n, m, fc)
  %Equal.sym(Bool, Pm(m, c), True{}, eP) : {GB.p(_, m, c) == None{} : Maybe<&2, Bool>}
  %Equal.sym(Bool, ISLAB(m, c, 4), True{}, eI) : {GB.l(_, m, fc) == None{} : Maybe<&2, Bool>}
  %Equal.sym(Bool, Pm(m, fc), True{}, eF) : {GB.f(_, m, fc) == None{} : Maybe<&2, Bool>}
  %Equal.sym(Maybe<&2, Bool>, CB(m, Fd(2n, m, fc)), Some{x}, eB) : {GB.b(_, m, rc) == None{} : Maybe<&2, Bool>}
  %Equal.sym(Bool, Pm(m, rc), True{}, eR) : {GB.r(x, _, m, rc) == None{} : Maybe<&2, Bool>}
  Equal.cong(Bool, Maybe<&2, Bool>, y => GB.z(x, y), LAST(m, rc), False{}, eZ)

# the loop of M.out.byte, and its parts
def MW.a1() -> Cr.Cir.Stmt:
  Mc.M.set(Mc.R.ow(), Mc.M.f(3n, Mc.M.g(Mc.R.ow())))

def MW.a2() -> Cr.Cir.Stmt:
  Mc.M.set(Mc.R.t1(), Mc.M.f(2n, Mc.M.g(Mc.R.ow())))

def MW.a3() -> Cr.Cir.Stmt:
  Mc.M.set(Mc.R.ow(), Mc.M.f(3n, Mc.M.g(Mc.R.ow())))

def MW.a4() -> Cr.Cir.Stmt:
  Mc.M.set(Mc.R.ow(), Mc.M.f(2n, Mc.M.g(Mc.R.ow())))

def MW.a5() -> Cr.Cir.Stmt:
  Mc.M.set(Mc.R.oi(), Mc.M.add(Mc.M.g(Mc.R.oi()), Mc.M.c(1)))

def MW.s4() -> Cr.Cir.Stmt:
  Mc.M.need(Mc.M.last(Mc.R.ow()), Mc.M.do([MW.a4(), MW.a5()]))

def MW.s3() -> Cr.Cir.Stmt:
  Mc.M.need(Mc.M.pair(Mc.R.ow()), MW.s4())

def MW.r3() -> Cr.Cir.Stmt:
  Mc.M.do([MW.a3(), MW.s3()])

def MW.r2() -> Cr.Cir.Stmt:
  Mc.M.do([Mc.M.out.bit(), MW.a3(), MW.s3()])

def MW.r1() -> Cr.Cir.Stmt:
  Mc.M.do([MW.a2(), Mc.M.out.bit(), MW.a3(), MW.s3()])

def MW.s2() -> Cr.Cir.Stmt:
  Mc.M.need(Mc.M.pair(Mc.R.ow()), MW.r1())

def MW.s1() -> Cr.Cir.Stmt:
  Mc.M.need(Mc.M.is_lab(Mc.M.f(2n, Mc.M.g(Mc.R.ow())), Mc.N.wcon()), Mc.M.do([MW.a1(), MW.s2()]))

def MW.body() -> Cr.Cir.Stmt:
  Mc.M.need(Mc.M.pair(Mc.R.ow()), MW.s1())

def MW.loop() -> Cr.Cir.Stmt:
  Mc.M.while(Mc.M.lt(Mc.M.g(Mc.R.oi()), Mc.M.c(8)), MW.body())

def MW.end() -> Cr.Cir.Stmt:
  Mc.M.need(Mc.M.pair(Mc.R.ow()), Mc.M.need(Mc.M.is_lab(Mc.M.f(2n, Mc.M.g(Mc.R.ow())), Mc.N.wnil()), Mc.M.need(Mc.M.last(Mc.R.ow()), Cr.Cir.Stmt.nop{})))

# what a round of the loop goes on with, by what GB reads: the bit in ov and
# the next cell in ow, or no result
def MI.Kc(+b: Cr.Cir.State, +oc: U32, +c: U32, +ov: U32, +oi: U32, +pg: U32, +out: List<&2, Word(8n)>, +outn: U32,
  +nw: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, -K: Cr.Cir.State -> Type, -H: U32 -> Cr.Cir.State -> Type) -> Type:
  @g: Maybe<&2, Bool> -> {GB(St.cl(b), c) == g : Maybe<&2, Bool>} ->
    MC(g, x => {ok(Pr(Pr(Pr(nw))), St.cl(b), ks, img, CW.next(St.cl(b), c), St.im(b), St.fs(b), St.nx(b)) == True{} : Bool} ->
      K(ST(b, oc, CW.next(St.cl(b), c), OV(x, ov, oi), U32.add(oi, 1), Fd(2n, St.cl(b), Fd(3n, St.cl(b), c)),
        Fd(2n, St.cl(b), Fd(2n, St.cl(b), Fd(2n, St.cl(b), Fd(3n, St.cl(b), c)))), pg, out, outn)),
      @st: Cr.Cir.State -> H(2, st))

# the round, once its bit is read: the rest of its tests
def MI.end(+f: Nat, +b: Cr.Cir.State, +oc: U32, +c: U32, +ov: U32, +oi: U32, +pg: U32, +out: List<&2, Word(8n)>, +outn: U32,
  +nw: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, -K: Cr.Cir.State -> Type, -H: U32 -> Cr.Cir.State -> Type, -O: Type,
  +hok: {ok(nw, St.cl(b), ks, img, c, St.im(b), St.fs(b), St.nx(b)) == True{} : Bool},
  +eP: {Pm(St.cl(b), c) == True{} : Bool}, +eI: {ISLAB(St.cl(b), c, 4) == True{} : Bool},
  +eF: {Pm(St.cl(b), Fd(3n, St.cl(b), c)) == True{} : Bool}, +x: Bool,
  +eB: {CB(St.cl(b), Fd(2n, St.cl(b), Fd(3n, St.cl(b), c))) == Some{x} : Maybe<&2, Bool>},
  kk: MI.Kc(b, oc, c, ov, oi, pg, out, outn, nw, ks, img, K, H)) ->
  Wp(Cr.Cir.exec(1n+f, MW.r3(), ST(b, oc, Fd(3n, St.cl(b), c), OV(x, ov, oi), oi, Fd(2n, St.cl(b), Fd(3n, St.cl(b), c)),
      Fd(2n, St.cl(b), Fd(2n, St.cl(b), Fd(2n, St.cl(b), Fd(3n, St.cl(b), c)))), pg, out, outn)),
    t => Wp(Cr.Cir.exec(1n+f, Cr.Cir.Stmt.nop{}, t), K, H, O), H, O):
  +m = St.cl(b)
  +im = St.im(b)
  +fs = St.fs(b)
  +nx = St.nx(b)
  +fc = Fd(3n, m, c)
  +bc = Fd(2n, m, fc)
  +rc = Fd(3n, m, fc)
  +nc = Fd(2n, m, rc)
  +x2 = Fd(2n, m, Fd(2n, m, bc))
  +v = OV(x, ov, oi)
  +hokf = ok.R(nw, m, ks, img, c, im, fs, nx, hok, eP)
  +hcf = ok.isc(Pr(nw), m, ks, img, fc, im, fs, nx, hokf)
  +hokr = ok.R(Pr(nw), m, ks, img, fc, im, fs, nx, hokf, eF)
  +hcr = ok.isc(Pr(Pr(nw)), m, ks, img, rc, im, fs, nx, hokr)
  +s3 = ST(b, oc, fc, v, oi, bc, x2, pg, out, outn)
  +s4 = ST(b, oc, rc, v, oi, bc, x2, pg, out, outn)
  +s5 = ST(b, oc, nc, v, oi, bc, x2, pg, out, outn)
  -K1 = {t => Wp(Cr.Cir.exec(1n+f, Cr.Cir.Stmt.nop{}, t), K, H, O) : Cr.Cir.State -> Type}
  -K2 = {t => Wp(Cr.Cir.exec(1n+f, Cr.Cir.Stmt.nop{}, t), K1, H, O) : Cr.Cir.State -> Type}
  -A = MI.Kc(b, oc, c, ov, oi, pg, out, outn, nw, ks, img, K, H)
  Wp.seq(f, MW.a3(), Mc.M.do([MW.s3()]), s3, K1, H, O,
    Wp.set(f, 46n, Mc.M.f(3n, Mc.M.g(Mc.R.ow())), s3, t => Wp(Cr.Cir.exec(1n+f, Mc.M.do([MW.s3()]), t), K1, H, O), H, O, rc,
      ev.f(3n, Mc.M.g(Mc.R.ow()), s3, fc, {==}, hcf),
      Wp.seq(f, MW.s3(), Cr.Cir.Stmt.nop{}, s4, K1, H, O,
        Wp.need(f, Mc.M.pair(Mc.R.ow()), MW.s4(), s4, K2, H, O, Pm(m, rc), ev.pair(46n, s4, rc, {==}, hcr),
         CasesK(Pm(m, rc), A, kk, Wp(Cr.Cir.exec(1n+f, MW.s4(), s4), K2, H, O), H(2, s4),
          kk => +eR =>
            Wp.need(f, Mc.M.last(Mc.R.ow()), Mc.M.do([MW.a4(), MW.a5()]), s4, K2, H, O, LAST(m, rc),
              ev.islab(3n, 46n, 0, s4, rc, {==}, hcr, ok.isc(Pr(Pr(Pr(nw))), m, ks, img, Fd(3n, m, rc), im, fs, nx, ok.R(Pr(Pr(nw)), m, ks, img, rc, im, fs, nx, hokr, eR))),
             CasesK(LAST(m, rc), A, kk, Wp(Cr.Cir.exec(1n+f, Mc.M.do([MW.a4(), MW.a5()]), s4), K2, H, O), H(2, s4),
              kk => +eZ =>
                Wp.seq(f, MW.a4(), Mc.M.do([MW.a5()]), s4, K2, H, O,
                  Wp.set(f, 46n, Mc.M.f(2n, Mc.M.g(Mc.R.ow())), s4, t => Wp(Cr.Cir.exec(1n+f, Mc.M.do([MW.a5()]), t), K2, H, O), H, O, nc,
                    ev.f(2n, Mc.M.g(Mc.R.ow()), s4, rc, {==}, hcr),
                    Wp.seq(f, MW.a5(), Cr.Cir.Stmt.nop{}, s5, K2, H, O,
                      Wp.set(f, 48n, Mc.M.add(Mc.M.g(Mc.R.oi()), Mc.M.c(1)), s5, t => Wp(Cr.Cir.exec(1n+f, Cr.Cir.Stmt.nop{}, t), K2, H, O), H, O, U32.add(oi, 1), {==},
                        kk(Some{x}, GB.ok(m, c, eP, eI, eF, x, eB, eR, eZ), ok.L(Pr(Pr(nw)), m, ks, img, rc, im, fs, nx, hokr, eR)))))),
              kk => +eZ =>
                kk(None{}, GB.n6(m, c, eP, eI, eF, x, eB, eR, eZ), s4))),
          kk => +eR =>
            kk(None{}, GB.n5(m, c, eP, eI, eF, x, eB, eR), s4))))))

# the round, once its first tests pass: the bit, then the rest of its tests
def MI.bit(+f: Nat, +b: Cr.Cir.State, +oc: U32, +c: U32, +ov: U32, +oi: U32, +t1: U32, +t2: U32, +pg: U32, +out: List<&2, Word(8n)>, +outn: U32,
  +nw: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, -K: Cr.Cir.State -> Type, -H: U32 -> Cr.Cir.State -> Type, -O: Type,
  +hok: {ok(nw, St.cl(b), ks, img, c, St.im(b), St.fs(b), St.nx(b)) == True{} : Bool},
  +eP: {Pm(St.cl(b), c) == True{} : Bool}, +eI: {ISLAB(St.cl(b), c, 4) == True{} : Bool},
  +eF: {Pm(St.cl(b), Fd(3n, St.cl(b), c)) == True{} : Bool},
  kk: MI.Kc(b, oc, c, ov, oi, pg, out, outn, nw, ks, img, K, H)) ->
  Wp(Cr.Cir.exec(1n+f, MW.r1(), ST(b, oc, Fd(3n, St.cl(b), c), ov, oi, t1, t2, pg, out, outn)),
    t => Wp(Cr.Cir.exec(1n+f, Cr.Cir.Stmt.nop{}, t), K, H, O), H, O):
  +m = St.cl(b)
  +im = St.im(b)
  +fs = St.fs(b)
  +nx = St.nx(b)
  +fc = Fd(3n, m, c)
  +bc = Fd(2n, m, fc)
  +rc = Fd(3n, m, fc)
  +nc = Fd(2n, m, rc)
  +x2 = Fd(2n, m, Fd(2n, m, bc))
  +hokf = ok.R(nw, m, ks, img, c, im, fs, nx, hok, eP)
  +hcf = ok.isc(Pr(nw), m, ks, img, fc, im, fs, nx, hokf)
  +hokr = ok.R(Pr(nw), m, ks, img, fc, im, fs, nx, hokf, eF)
  +hcr = ok.isc(Pr(Pr(nw)), m, ks, img, rc, im, fs, nx, hokr)
  +s1 = ST(b, oc, fc, ov, oi, t1, t2, pg, out, outn)
  -K1 = {t => Wp(Cr.Cir.exec(1n+f, Cr.Cir.Stmt.nop{}, t), K, H, O) : Cr.Cir.State -> Type}
  -A = MI.Kc(b, oc, c, ov, oi, pg, out, outn, nw, ks, img, K, H)
  Wp.seq(f, MW.a2(), MW.r2(), s1, K1, H, O,
    Wp.set(f, 61n, Mc.M.f(2n, Mc.M.g(Mc.R.ow())), s1, t => Wp(Cr.Cir.exec(1n+f, MW.r2(), t), K1, H, O), H, O, bc,
      ev.f(2n, Mc.M.g(Mc.R.ow()), s1, fc, {==}, hcf),
      Wp.seq(f, Mc.M.out.bit(), MW.r3(), ST(b, oc, fc, ov, oi, bc, t2, pg, out, outn), K1, H, O,
        MB(f, b, oc, fc, ov, oi, bc, t2, pg, out, outn, Pr(Pr(nw)), ks, img, t => Wp(Cr.Cir.exec(1n+f, MW.r3(), t), K1, H, O), H, O,
          ok.L(Pr(nw), m, ks, img, fc, im, fs, nx, hokf, eF),
          rB => +eB => CasesM(rB, A, kk, x => Wp(Cr.Cir.exec(1n+f, MW.r3(), ST(b, oc, fc, OV(x, ov, oi), oi, bc, x2, pg, out, outn)), K1, H, O),
            @st: Cr.Cir.State -> H(2, st),
            kk => +x => +ex =>
              MI.end(f, b, oc, c, ov, oi, pg, out, outn, nw, ks, img, K, H, O, hok, eP, eI, eF, x,
                Equal.trans(Maybe<&2, Bool>, CB(m, bc), rB, Some{x}, eB, ex), kk),
            kk => +ex =>
              st => kk(None{}, GB.n4(m, c, eP, eI, eF, Equal.trans(Maybe<&2, Bool>, CB(m, bc), rB, None{}, eB, ex)), st))))))

# a round of the loop of M.out.byte, on the cell c in ow: the bit that GB
# reads goes into ov, and ow gets the cell after it; or the run ends with no
# result
def MI(+f: Nat, +b: Cr.Cir.State, +oc: U32, +c: U32, +ov: U32, +oi: U32, +t1: U32, +t2: U32, +pg: U32, +out: List<&2, Word(8n)>, +outn: U32,
  +nw: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, -K: Cr.Cir.State -> Type, -H: U32 -> Cr.Cir.State -> Type, -O: Type,
  +hok: {ok(nw, St.cl(b), ks, img, c, St.im(b), St.fs(b), St.nx(b)) == True{} : Bool},
  kk: MI.Kc(b, oc, c, ov, oi, pg, out, outn, nw, ks, img, K, H)) ->
  Wp(Cr.Cir.exec(1n+f, MW.body(), ST(b, oc, c, ov, oi, t1, t2, pg, out, outn)), K, H, O):
  +m = St.cl(b)
  +im = St.im(b)
  +fs = St.fs(b)
  +nx = St.nx(b)
  +fc = Fd(3n, m, c)
  +bc = Fd(2n, m, fc)
  +rc = Fd(3n, m, fc)
  +nc = Fd(2n, m, rc)
  +x2 = Fd(2n, m, Fd(2n, m, bc))
  +s0 = ST(b, oc, c, ov, oi, t1, t2, pg, out, outn)
  +s1 = ST(b, oc, fc, ov, oi, t1, t2, pg, out, outn)
  +s2 = ST(b, oc, fc, ov, oi, bc, t2, pg, out, outn)
  +hc = ok.isc(nw, m, ks, img, c, im, fs, nx, hok)
  -A = MI.Kc(b, oc, c, ov, oi, pg, out, outn, nw, ks, img, K, H)
  Wp.need(f, Mc.M.pair(Mc.R.ow()), MW.s1(), s0, K, H, O, Pm(m, c), ev.pair(46n, s0, c, {==}, hc),
   CasesK(Pm(m, c), A, kk, Wp(Cr.Cir.exec(1n+f, MW.s1(), s0), K, H, O), H(2, s0),
    kk => +eP =>
      Wp.need(f, Mc.M.is_lab(Mc.M.f(2n, Mc.M.g(Mc.R.ow())), Mc.N.wcon()), Mc.M.do([MW.a1(), MW.s2()]), s0, K, H, O, ISLAB(m, c, 4),
        ev.islab(2n, 46n, 4, s0, c, {==}, hc, ok.isc(Pr(nw), m, ks, img, Fd(2n, m, c), im, fs, nx, ok.L(nw, m, ks, img, c, im, fs, nx, hok, eP))),
       CasesK(ISLAB(m, c, 4), A, kk, Wp(Cr.Cir.exec(1n+f, Mc.M.do([MW.a1(), MW.s2()]), s0), K, H, O), H(2, s0),
        kk => +eI =>
          Wp.seq(f, MW.a1(), Mc.M.do([MW.s2()]), s0, K, H, O,
            Wp.set(f, 46n, Mc.M.f(3n, Mc.M.g(Mc.R.ow())), s0, t => Wp(Cr.Cir.exec(1n+f, Mc.M.do([MW.s2()]), t), K, H, O), H, O, fc,
              ev.f(3n, Mc.M.g(Mc.R.ow()), s0, c, {==}, hc),
              Wp.seq(f, MW.s2(), Cr.Cir.Stmt.nop{}, s1, K, H, O,
                Wp.need(f, Mc.M.pair(Mc.R.ow()), MW.r1(), s1, t => Wp(Cr.Cir.exec(1n+f, Cr.Cir.Stmt.nop{}, t), K, H, O), H, O, Pm(m, fc),
                  ev.pair(46n, s1, fc, {==}, ok.isc(Pr(nw), m, ks, img, fc, im, fs, nx, ok.R(nw, m, ks, img, c, im, fs, nx, hok, eP))),
                 CasesK(Pm(m, fc), A, kk, Wp(Cr.Cir.exec(1n+f, MW.r1(), s1), t => Wp(Cr.Cir.exec(1n+f, Cr.Cir.Stmt.nop{}, t), K, H, O), H, O), H(2, s1),
                  kk => +eF =>
                    MI.bit(f, b, oc, c, ov, oi, t1, t2, pg, out, outn, nw, ks, img, K, H, O, hok, eP, eI, eF, kk),
                  kk => +eF =>
                    kk(None{}, GB.n3(m, c, eP, eI, eF), s1)))))),
        kk => +eI =>
          kk(None{}, GB.n2(m, c, eP, eI), s0))),
    kk => +eP =>
      kk(None{}, GB.n1(m, c, eP), s0)))

# The loop of the word
# --------------------
#
# Each round reads a bit x into ov (M.out.bit sets bit oi of ov when x is
# True). With r bits left, ov holds Byte.to_u32(K(zeros(r))): K puts the bits read
# so far below its argument, and Kz puts zeros there, so that or-ing 1 << oi,
# which is Byte.to_u32(Kz(WCon{True, zeros})) (Good), sets the next bit (HKT).

def SH(+idx: U32) -> U32:
  Wa.Wasm.op(Wa.Wasm.Op.shl{}, 1, idx)

# h, moved along the equation e
def Tr(-A: Type, -P: A -> Type, -a: A, -b: A, +e: {a == b : A}, h: P(a)) -> P(b):
  %e : P(_)
  h

# a pair of two Data types, itself Data, and its parts
def PD(-A: Data, -B: Data) -> Data:
  Sigma<&2, &2, A, _ => B>

def D1(-A: Data, -B: Data, +p: PD(A, B)) -> A:
  (a, b) = p
  a

def D2(-A: Data, -B: Data, +p: PD(A, B)) -> B:
  (a, b) = p
  b

# K at the bit x, then w. Good and HKT apply their functions only through it: bend -o writes a
# function argument η-long, and a call of that λ on a constructor, opened in a type the kernel
# checks, is a term the kernel cannot infer
def Kb(x: Bool, -q: Nat, K: Word(1n+q) -> Word(8n), w: Word(q)) -> Word(8n):
  K(WCon{x, w})

def Good(r: Nat, +idx: U32, Kz: Word(r) -> Word(8n)) -> Data:
  match r:
    case 0n:
      {U32.is_lt(idx, 8) == False{} : Bool}
    case 1n+q:
      PD({U32.is_lt(idx, 8) == True{} : Bool}, PD({Sd.Byte.to_u32(Kb(True{}, q, Kz, zeros(q))) == SH(idx) : U32}, Good(q, U32.add(idx, 1), y => Kb(False{}, q, Kz, y))))

# the value with a bit set is the value with it clear, or-ed with the bit
# alone, for each choice of the bits not yet read: a tree, by those bits
def HKT(r: Nat, K: Word(r) -> Word(8n), Kz: Word(r) -> Word(8n)) -> Data:
  match r:
    case 0n:
      Unit
    case 1n+q:
      PD({Sd.Byte.to_u32(Kb(True{}, q, K, zeros(q))) == U32.or(Sd.Byte.to_u32(Kb(False{}, q, K, zeros(q))), Sd.Byte.to_u32(Kb(True{}, q, Kz, zeros(q)))) : U32},
        PD(HKT(q, y => Kb(True{}, q, K, y), y => Kb(False{}, q, Kz, y)), HKT(q, y => Kb(False{}, q, K, y), y => Kb(False{}, q, Kz, y))))

# the low n bits of w, then m bits 0, are w
def low_pad(+n: Nat, +m: Nat, w: Word(n)) -> {Sd.Word.low(n, m, Sd.Word.pad(n, m, w)) == w : Word(n)}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{+x, +t}:
          Equal.cong(Word(p), Word(1n+p), y => WCon{x, y}, Sd.Word.low(p, m, Sd.Word.pad(p, m, t)), t, low_pad(p, m, t))

# the value of ov after the bit x
def acc_step(x: Bool, +q: Nat, -K: Word(1n+q) -> Word(8n), -Kz: Word(1n+q) -> Word(8n), +idx: U32, +HK: HKT(1n+q, K, Kz),
  +esh: {Sd.Byte.to_u32(Kz(WCon{True{}, zeros(q)})) == SH(idx) : U32}) ->
  {Sd.Byte.to_u32(K(WCon{x, zeros(q)})) == OV(x, Sd.Byte.to_u32(K(zeros(1n+q))), idx) : U32}:
  match x:
    case False{}:
      {==}
    case True{}:
      %esh : {Sd.Byte.to_u32(K(WCon{True{}, zeros(q)})) == U32.or(Sd.Byte.to_u32(K(zeros(1n+q))), _) : U32}
      D1({Sd.Byte.to_u32(K(WCon{True{}, zeros(q)})) == U32.or(Sd.Byte.to_u32(K(WCon{False{}, zeros(q)})), Sd.Byte.to_u32(Kz(WCon{True{}, zeros(q)}))) : U32},
        PD(HKT(q, y => K(WCon{True{}, y}), y => Kz(WCon{False{}, y})), HKT(q, y => K(WCon{False{}, y}), y => Kz(WCon{False{}, y}))), HK)

# HKT holds after the bit x
def HK.step(+q: Nat, +x: Bool, -K: Word(1n+q) -> Word(8n), -Kz: Word(1n+q) -> Word(8n), +HK: HKT(1n+q, K, Kz)) ->
  HKT(q, y => K(WCon{x, y}), y => Kz(WCon{False{}, y})):
  match x:
    case True{}:
      D1(HKT(q, y => K(WCon{True{}, y}), y => Kz(WCon{False{}, y})), HKT(q, y => K(WCon{False{}, y}), y => Kz(WCon{False{}, y})),
        D2({Sd.Byte.to_u32(K(WCon{True{}, zeros(q)})) == U32.or(Sd.Byte.to_u32(K(WCon{False{}, zeros(q)})), Sd.Byte.to_u32(Kz(WCon{True{}, zeros(q)}))) : U32},
          PD(HKT(q, y => K(WCon{True{}, y}), y => Kz(WCon{False{}, y})), HKT(q, y => K(WCon{False{}, y}), y => Kz(WCon{False{}, y}))), HK))
    case False{}:
      D2(HKT(q, y => K(WCon{True{}, y}), y => Kz(WCon{False{}, y})), HKT(q, y => K(WCon{False{}, y}), y => Kz(WCon{False{}, y})),
        D2({Sd.Byte.to_u32(K(WCon{True{}, zeros(q)})) == U32.or(Sd.Byte.to_u32(K(WCon{False{}, zeros(q)})), Sd.Byte.to_u32(Kz(WCon{True{}, zeros(q)}))) : U32},
          PD(HKT(q, y => K(WCon{True{}, y}), y => Kz(WCon{False{}, y})), HKT(q, y => K(WCon{False{}, y}), y => Kz(WCon{False{}, y}))), HK))

# HKT for the 8 bits of a byte, from 0
def HK8() -> HKT(8n, y => y, y => y):
  ({==}, (({==}, (({==}, (({==}, (({==}, (({==}, (({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))), ({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))))), ({==}, (({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))), ({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))))))), ({==}, (({==}, (({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))), ({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))))), ({==}, (({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))), ({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))))))))), ({==}, (({==}, (({==}, (({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))), ({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))))), ({==}, (({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))), ({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))))))), ({==}, (({==}, (({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))), ({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))))), ({==}, (({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))), ({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))))))))))), ({==}, (({==}, (({==}, (({==}, (({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))), ({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))))), ({==}, (({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))), ({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))))))), ({==}, (({==}, (({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))), ({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))))), ({==}, (({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))), ({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))))))))), ({==}, (({==}, (({==}, (({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))), ({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))))), ({==}, (({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))), ({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))))))), ({==}, (({==}, (({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))), ({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))))), ({==}, (({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))), ({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))))))))))))), ({==}, (({==}, (({==}, (({==}, (({==}, (({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))), ({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))))), ({==}, (({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))), ({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))))))), ({==}, (({==}, (({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))), ({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))))), ({==}, (({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))), ({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))))))))), ({==}, (({==}, (({==}, (({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))), ({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))))), ({==}, (({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))), ({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))))))), ({==}, (({==}, (({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))), ({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))))), ({==}, (({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))), ({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))))))))))), ({==}, (({==}, (({==}, (({==}, (({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))), ({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))))), ({==}, (({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))), ({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))))))), ({==}, (({==}, (({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))), ({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))))), ({==}, (({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))), ({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))))))))), ({==}, (({==}, (({==}, (({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))), ({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))))), ({==}, (({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))), ({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))))))), ({==}, (({==}, (({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))), ({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))))), ({==}, (({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{})))), ({==}, (({==}, (Unit{}, Unit{})), ({==}, (Unit{}, Unit{}))))))))))))))))

# X(w) for Some{w}, else Y
def MCW(-p: Nat, rr: Maybe<&2, Word(p)>, X: Word(p) -> Type, Y: Type) -> Type:
  match rr:
    case Some{w}:
      X(w)
    case None{}:
      Y

def CasesW(-p: Nat, rr: Maybe<&2, Word(p)>, -A: Type, a: A, -X: Word(p) -> Type, -Y: Type,
  s: A -> @w: Word(p) -> {rr == Some{w} : Maybe<&2, Word(p)>} -> X(w), n: A -> {rr == None{} : Maybe<&2, Word(p)>} -> Y) -> MCW(p, rr, X, Y):
  match rr:
    case Some{w}:
      s(a, w, {==})
    case None{}:
      n(a, {==})

def CWb.some(+q: Nat, +m: Cr.Cir.Cells, +c: U32, +x: Bool, +w: Word(q), +e1: {GB(m, c) == Some{x} : Maybe<&2, Bool>},
  +e2: {CWb(q, m, CW.next(m, c)) == Some{w} : Maybe<&2, Word(q)>}) -> {CWb(1n+q, m, c) == Some{WCon{x, w}} : Maybe<&2, Word(1n+q)>}:
  %Equal.sym(Maybe<&2, Bool>, GB(m, c), Some{x}, e1) : {W1.g(q, _, CWb(q, m, CW.next(m, c))) == Some{WCon{x, w}} : Maybe<&2, Word(1n+q)>}
  %Equal.sym(Maybe<&2, Word(q)>, CWb(q, m, CW.next(m, c)), Some{w}, e2) : {W1.w(q, x, _) == Some{WCon{x, w}} : Maybe<&2, Word(1n+q)>}
  {==}

def CWb.none2(+q: Nat, +m: Cr.Cir.Cells, +c: U32, +x: Bool, +e1: {GB(m, c) == Some{x} : Maybe<&2, Bool>},
  +e2: {CWb(q, m, CW.next(m, c)) == None{} : Maybe<&2, Word(q)>}) -> {CWb(1n+q, m, c) == None{} : Maybe<&2, Word(1n+q)>}:
  %Equal.sym(Maybe<&2, Bool>, GB(m, c), Some{x}, e1) : {W1.g(q, _, CWb(q, m, CW.next(m, c))) == None{} : Maybe<&2, Word(1n+q)>}
  %Equal.sym(Maybe<&2, Word(q)>, CWb(q, m, CW.next(m, c)), None{}, e2) : {W1.w(q, x, _) == None{} : Maybe<&2, Word(1n+q)>}
  {==}

def CWb.none1(+q: Nat, +m: Cr.Cir.Cells, +c: U32, +e1: {GB(m, c) == None{} : Maybe<&2, Bool>}) ->
  {CWb(1n+q, m, c) == None{} : Maybe<&2, Word(1n+q)>}:
  Equal.cong(Maybe<&2, Bool>, Maybe<&2, Word(1n+q)>, g => W1.g(q, g, CWb(q, m, CW.next(m, c))), GB(m, c), None{}, e1)

# M.lt on register r
def ev.lt(+r: Nat, +n: U32, +st: Cr.Cir.State, +i: U32, +er: {Some{i} == Cr.Cir.eval(Mc.M.g(r), st) : Maybe<&2, U32>}, -b: Bool,
  +eb: {U32.is_lt(i, n) == b : Bool}) -> {Some{Bool.to_u32(b)} == Cr.Cir.eval(Mc.M.lt(Mc.M.g(r), Mc.M.c(n)), st) : Maybe<&2, U32>}:
  %er : {Some{Bool.to_u32(b)} == Cr.Cir.eval.op(Wa.Wasm.Op.lt_u{}, _, Some{n}) : Maybe<&2, U32>}
  %eb : {Some{Bool.to_u32(_)} == Some{Bool.to_u32(U32.is_lt(i, n))} : Maybe<&2, U32>}
  {==}

def Wp.while(+f: Nat, +c: Cr.Cir.Expr, +body: Cr.Cir.Stmt, +st: Cr.Cir.State, -K: Cr.Cir.State -> Type, -H: U32 -> Cr.Cir.State -> Type, -O: Type,
  b: Bool, +ev: {Some{Bool.to_u32(b)} == Cr.Cir.eval(c, st) : Maybe<&2, U32>},
  g: IFT(b, Wp(Cr.Cir.exec.then(Cr.Cir.exec(f, body, st), t => Cr.Cir.exec(f, Cr.Cir.Stmt.while{c, body}, t)), K, H, O), K(st))) ->
  Wp(Cr.Cir.exec(1n+f, Cr.Cir.Stmt.while{c, body}, st), K, H, O):
  match b:
    case True{}:
      %ev : Wp(Cr.Cir.exec.if(_, u => Cr.Cir.exec.then(Cr.Cir.exec(f, body, st), t => Cr.Cir.exec(f, Cr.Cir.Stmt.while{c, body}, t)), u => Cr.Cir.Out.next{st}), K, H, O)
      g
    case False{}:
      %ev : Wp(Cr.Cir.exec.if(_, u => Cr.Cir.exec.then(Cr.Cir.exec(f, body, st), t => Cr.Cir.exec(f, Cr.Cir.Stmt.while{c, body}, t)), u => Cr.Cir.Out.next{st}), K, H, O)
      g

# the fuel of ok left after r bits of a word
def Pn(r: Nat, +n: Nat) -> Nat:
  match r:
    case 0n:
      n
    case 1n+q:
      Pn(q, Pr(Pr(Pr(n))))

# what the loop goes on with, by what CWb reads: its r bits below K in ov,
# with ow at the cell after them, or no result
def ML.Kc(r: Nat, +b: Cr.Cir.State, +oc: U32, +c: U32, -K: Word(r) -> Word(8n), +pg: U32, +out: List<&2, Word(8n)>, +outn: U32,
  +nw: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, -KK: Cr.Cir.State -> Type, -H: U32 -> Cr.Cir.State -> Type) -> Type:
  @rr: Maybe<&2, Word(r)> -> {CWb(r, St.cl(b), c) == rr : Maybe<&2, Word(r)>} ->
    MCW(r, rr, w => {ok(Pn(r, nw), St.cl(b), ks, img, Nx(r, St.cl(b), c), St.im(b), St.fs(b), St.nx(b)) == True{} : Bool} ->
      @oi: U32 -> @t1: U32 -> @t2: U32 -> KK(ST(b, oc, Nx(r, St.cl(b), c), Sd.Byte.to_u32(K(w)), oi, t1, t2, pg, out, outn)),
      @st: Cr.Cir.State -> H(2, st))

# the loop goes on after a round that read the bit x
def ML.next(+q: Nat, +g: Nat, +b: Cr.Cir.State, +oc: U32, +c: U32, +ov: U32, +idx: U32, +pg: U32,
  +out: List<&2, Word(8n)>, +outn: U32, +nw: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  -K: Word(1n+q) -> Word(8n), -Kz: Word(1n+q) -> Word(8n), +HK: HKT(1n+q, K, Kz), +G: Good(1n+q, idx, Kz),
  -KK: Cr.Cir.State -> Type, -H: U32 -> Cr.Cir.State -> Type, -O: Type, +eov: {Sd.Byte.to_u32(K(zeros(1n+q))) == ov : U32}, +x: Bool,
  +ex: {GB(St.cl(b), c) == Some{x} : Maybe<&2, Bool>},
  +hokn: {ok(Pr(Pr(Pr(nw))), St.cl(b), ks, img, CW.next(St.cl(b), c), St.im(b), St.fs(b), St.nx(b)) == True{} : Bool},
  kk: ML.Kc(1n+q, b, oc, c, K, pg, out, outn, nw, ks, img, KK, H),
  ih: @nc: U32 -> @x: Bool -> {ok(Pr(Pr(Pr(nw))), St.cl(b), ks, img, nc, St.im(b), St.fs(b), St.nx(b)) == True{} : Bool} ->
    @ov2: U32 -> {Sd.Byte.to_u32(K(WCon{x, zeros(q)})) == ov2 : U32} ->
    ML.Kc(q, b, oc, nc, y => K(WCon{x, y}), pg, out, outn, Pr(Pr(Pr(nw))), ks, img, KK, H) ->
    Wp(Cr.Cir.exec(1n+g, MW.loop(), ST(b, oc, nc, ov2, U32.add(idx, 1), Fd(2n, St.cl(b), Fd(3n, St.cl(b), c)),
      Fd(2n, St.cl(b), Fd(2n, St.cl(b), Fd(2n, St.cl(b), Fd(3n, St.cl(b), c)))), pg, out, outn)), KK, H, O)) ->
  Wp(Cr.Cir.exec(1n+g, MW.loop(), ST(b, oc, CW.next(St.cl(b), c), OV(x, ov, idx), U32.add(idx, 1), Fd(2n, St.cl(b), Fd(3n, St.cl(b), c)),
    Fd(2n, St.cl(b), Fd(2n, St.cl(b), Fd(2n, St.cl(b), Fd(3n, St.cl(b), c)))), pg, out, outn)), KK, H, O):
  +m = St.cl(b)
  +nc = CW.next(m, c)
  -A = ML.Kc(1n+q, b, oc, c, K, pg, out, outn, nw, ks, img, KK, H)
  ih(nc, x, hokn, OV(x, ov, idx),
    Equal.trans(U32, Sd.Byte.to_u32(K(WCon{x, zeros(q)})), OV(x, Sd.Byte.to_u32(K(zeros(1n+q))), idx), OV(x, ov, idx),
      acc_step(x, q, K, Kz, idx, HK, D1({Sd.Byte.to_u32(Kz(WCon{True{}, zeros(q)})) == SH(idx) : U32}, Good(q, U32.add(idx, 1), y => Kz(WCon{False{}, y})), D2({U32.is_lt(idx, 8) == True{} : Bool}, PD({Sd.Byte.to_u32(Kz(WCon{True{}, zeros(q)})) == SH(idx) : U32}, Good(q, U32.add(idx, 1), y => Kz(WCon{False{}, y}))), G))),
      Equal.cong(U32, U32, v => OV(x, v, idx), Sd.Byte.to_u32(K(zeros(1n+q))), ov, eov)),
    rr => +err => CasesW(q, rr, A, kk,
      w => {ok(Pn(q, Pr(Pr(Pr(nw)))), m, ks, img, Nx(q, m, nc), St.im(b), St.fs(b), St.nx(b)) == True{} : Bool} ->
        @oi: U32 -> @t1: U32 -> @t2: U32 -> KK(ST(b, oc, Nx(q, m, nc), Sd.Byte.to_u32(K(WCon{x, w})), oi, t1, t2, pg, out, outn)),
      @st: Cr.Cir.State -> H(2, st),
      kk => +w => +ew => kk(Some{WCon{x, w}}, CWb.some(q, m, c, x, w, ex, Equal.trans(Maybe<&2, Word(q)>, CWb(q, m, nc), rr, Some{w}, err, ew))),
      kk => +ew => kk(None{}, CWb.none2(q, m, c, x, ex, Equal.trans(Maybe<&2, Word(q)>, CWb(q, m, nc), rr, None{}, err, ew)))))

# a round of the loop, then the rest of it
def ML.go(+q: Nat, +g: Nat, +b: Cr.Cir.State, +oc: U32, +c: U32, +ov: U32, +idx: U32, +pg: U32,
  +out: List<&2, Word(8n)>, +outn: U32, +nw: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  -K: Word(1n+q) -> Word(8n), -Kz: Word(1n+q) -> Word(8n), +HK: HKT(1n+q, K, Kz), +G: Good(1n+q, idx, Kz),
  -KK: Cr.Cir.State -> Type, -H: U32 -> Cr.Cir.State -> Type, -O: Type, +eov: {Sd.Byte.to_u32(K(zeros(1n+q))) == ov : U32}, +t1: U32, +t2: U32, +hF: PN.Le(1n+q, 1n+g),
  +hok: {ok(nw, St.cl(b), ks, img, c, St.im(b), St.fs(b), St.nx(b)) == True{} : Bool},
  kk: ML.Kc(1n+q, b, oc, c, K, pg, out, outn, nw, ks, img, KK, H),
  ih: @nc: U32 -> @x: Bool -> {ok(Pr(Pr(Pr(nw))), St.cl(b), ks, img, nc, St.im(b), St.fs(b), St.nx(b)) == True{} : Bool} ->
    @ov2: U32 -> {Sd.Byte.to_u32(K(WCon{x, zeros(q)})) == ov2 : U32} ->
    ML.Kc(q, b, oc, nc, y => K(WCon{x, y}), pg, out, outn, Pr(Pr(Pr(nw))), ks, img, KK, H) ->
    Wp(Cr.Cir.exec(1n+g, MW.loop(), ST(b, oc, nc, ov2, U32.add(idx, 1), Fd(2n, St.cl(b), Fd(3n, St.cl(b), c)),
      Fd(2n, St.cl(b), Fd(2n, St.cl(b), Fd(2n, St.cl(b), Fd(3n, St.cl(b), c)))), pg, out, outn)), KK, H, O)) ->
  Wp(Cr.Cir.exec(1n+1n+g, MW.loop(), ST(b, oc, c, ov, idx, t1, t2, pg, out, outn)), KK, H, O):
  +m = St.cl(b)
  +s0 = ST(b, oc, c, ov, idx, t1, t2, pg, out, outn)
  +bc = Fd(2n, m, Fd(3n, m, c))
  +x2 = Fd(2n, m, Fd(2n, m, bc))
  -A = ML.Kc(1n+q, b, oc, c, K, pg, out, outn, nw, ks, img, KK, H)
  Wp.while(1n+g, Mc.M.lt(Mc.M.g(Mc.R.oi()), Mc.M.c(8)), MW.body(), s0, KK, H, O, True{},
    ev.lt(48n, 8, s0, idx, {==}, True{}, D1({U32.is_lt(idx, 8) == True{} : Bool}, PD({Sd.Byte.to_u32(Kz(WCon{True{}, zeros(q)})) == SH(idx) : U32}, Good(q, U32.add(idx, 1), y => Kz(WCon{False{}, y}))), G)),
    Wp.then(Cr.Cir.exec(1n+g, MW.body(), s0), t => Cr.Cir.exec(1n+g, MW.loop(), t), KK, H, O,
      MI(g, b, oc, c, ov, idx, t1, t2, pg, out, outn, nw, ks, img, t => Wp(Cr.Cir.exec(1n+g, MW.loop(), t), KK, H, O), H, O, hok,
        gb => +egb => CasesM(gb, A, kk,
          x => {ok(Pr(Pr(Pr(nw))), m, ks, img, CW.next(m, c), St.im(b), St.fs(b), St.nx(b)) == True{} : Bool} ->
            Wp(Cr.Cir.exec(1n+g, MW.loop(), ST(b, oc, CW.next(m, c), OV(x, ov, idx), U32.add(idx, 1), bc, x2, pg, out, outn)), KK, H, O),
          @st: Cr.Cir.State -> H(2, st),
          kk => +x => +ex => +hokn =>
            ML.next(q, g, b, oc, c, ov, idx, pg, out, outn, nw, ks, img, K, Kz, HK, G, KK, H, O, eov, x,
              Equal.trans(Maybe<&2, Bool>, GB(m, c), gb, Some{x}, egb, ex), hokn, kk, ih),
          kk => +ex =>
            st => kk(None{}, CWb.none1(q, m, c, Equal.trans(Maybe<&2, Bool>, GB(m, c), gb, None{}, egb, ex)), st)))))

# the loop of M.out.byte, with r bits left, from the cell c in ow
def ML(+r: Nat, +F: Nat, +hF: PN.Le(1n+r, F), +b: Cr.Cir.State, +oc: U32, +c: U32, +ov: U32, +idx: U32, +t1: U32, +t2: U32, +pg: U32,
  +out: List<&2, Word(8n)>, +outn: U32, +nw: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  -K: Word(r) -> Word(8n), -Kz: Word(r) -> Word(8n), +HK: HKT(r, K, Kz), +G: Good(r, idx, Kz),
  -KK: Cr.Cir.State -> Type, -H: U32 -> Cr.Cir.State -> Type, -O: Type, +eov: {Sd.Byte.to_u32(K(zeros(r))) == ov : U32},
  +hok: {ok(nw, St.cl(b), ks, img, c, St.im(b), St.fs(b), St.nx(b)) == True{} : Bool},
  kk: ML.Kc(r, b, oc, c, K, pg, out, outn, nw, ks, img, KK, H)) ->
  Wp(Cr.Cir.exec(F, MW.loop(), ST(b, oc, c, ov, idx, t1, t2, pg, out, outn)), KK, H, O):
  match r:
    case 0n:
      match F:
        case 0n:
          Empty.absurd(Wp(Cr.Cir.exec(0n, MW.loop(), ST(b, oc, c, ov, idx, t1, t2, pg, out, outn)), KK, H, O), hF)
        case 1n+f:
          Wp.while(f, Mc.M.lt(Mc.M.g(Mc.R.oi()), Mc.M.c(8)), MW.body(), ST(b, oc, c, ov, idx, t1, t2, pg, out, outn), KK, H, O, False{},
            ev.lt(48n, 8, ST(b, oc, c, ov, idx, t1, t2, pg, out, outn), idx, {==}, False{}, G),
            Tr(U32, v => KK(ST(b, oc, c, v, idx, t1, t2, pg, out, outn)), Sd.Byte.to_u32(K(zeros(0n))), ov, eov, kk(Some{WNil{}}, {==}, hok, idx, t1, t2)))
    case 1n+q:
      match F:
        case 0n:
          Empty.absurd(Wp(Cr.Cir.exec(0n, MW.loop(), ST(b, oc, c, ov, idx, t1, t2, pg, out, outn)), KK, H, O), hF)
        case 1n+f:
          match f:
            case 0n:
              Empty.absurd(Wp(Cr.Cir.exec(1n, MW.loop(), ST(b, oc, c, ov, idx, t1, t2, pg, out, outn)), KK, H, O), hF)
            case 1n+g:
              ML.go(q, g, b, oc, c, ov, idx, pg, out, outn, nw, ks, img, K, Kz, HK, G, KK, H, O, eov, t1, t2, hF, hok, kk,
                nc => +x => +hokn => +ov2 => +eov2 => kk2 =>
                  ML(q, 1n+g, hF, b, oc, nc, ov2, U32.add(idx, 1), Fd(2n, St.cl(b), Fd(3n, St.cl(b), c)),
                    Fd(2n, St.cl(b), Fd(2n, St.cl(b), Fd(2n, St.cl(b), Fd(3n, St.cl(b), c)))), pg, out, outn, Pr(Pr(Pr(nw))), ks, img,
                    y => K(WCon{x, y}), y => Kz(WCon{False{}, y}), HK.step(q, x, K, Kz, HK),
                    D2({Sd.Byte.to_u32(Kz(WCon{True{}, zeros(q)})) == SH(idx) : U32}, Good(q, U32.add(idx, 1), y => Kz(WCon{False{}, y})),
                      D2({U32.is_lt(idx, 8) == True{} : Bool}, PD({Sd.Byte.to_u32(Kz(WCon{True{}, zeros(q)})) == SH(idx) : U32}, Good(q, U32.add(idx, 1), y => Kz(WCon{False{}, y}))), G)),
                    KK, H, O, eov2, hokn, kk2))

# The word
# --------

def CW0.ok(+m: Cr.Cir.Cells, +d: U32, +eP: {Pm(m, d) == True{} : Bool}, +eI: {ISLAB(m, d, 3) == True{} : Bool},
  +eL: {LAST(m, d) == True{} : Bool}) -> {CW(0n, m, d) == Some{WNil{}} : Maybe<&2, Word(0n)>}:
  %Equal.sym(Bool, Pm(m, d), True{}, eP) : {CW0.p(_, m, d) == Some{WNil{}} : Maybe<&2, Word(0n)>}
  %Equal.sym(Bool, ISLAB(m, d, 3), True{}, eI) : {CW0.l(_, m, d) == Some{WNil{}} : Maybe<&2, Word(0n)>}
  %Equal.sym(Bool, LAST(m, d), True{}, eL) : {CW0.z(_) == Some{WNil{}} : Maybe<&2, Word(0n)>}
  {==}

def CW0.n1(+m: Cr.Cir.Cells, +d: U32, +eP: {Pm(m, d) == False{} : Bool}) -> {CW(0n, m, d) == None{} : Maybe<&2, Word(0n)>}:
  Equal.cong(Bool, Maybe<&2, Word(0n)>, y => CW0.p(y, m, d), Pm(m, d), False{}, eP)

def CW0.n2(+m: Cr.Cir.Cells, +d: U32, +eP: {Pm(m, d) == True{} : Bool}, +eI: {ISLAB(m, d, 3) == False{} : Bool}) ->
  {CW(0n, m, d) == None{} : Maybe<&2, Word(0n)>}:
  %Equal.sym(Bool, Pm(m, d), True{}, eP) : {CW0.p(_, m, d) == None{} : Maybe<&2, Word(0n)>}
  Equal.cong(Bool, Maybe<&2, Word(0n)>, y => CW0.l(y, m, d), ISLAB(m, d, 3), False{}, eI)

def CW0.n3(+m: Cr.Cir.Cells, +d: U32, +eP: {Pm(m, d) == True{} : Bool}, +eI: {ISLAB(m, d, 3) == True{} : Bool},
  +eL: {LAST(m, d) == False{} : Bool}) -> {CW(0n, m, d) == None{} : Maybe<&2, Word(0n)>}:
  %Equal.sym(Bool, Pm(m, d), True{}, eP) : {CW0.p(_, m, d) == None{} : Maybe<&2, Word(0n)>}
  %Equal.sym(Bool, ISLAB(m, d, 3), True{}, eI) : {CW0.l(_, m, d) == None{} : Maybe<&2, Word(0n)>}
  Equal.cong(Bool, Maybe<&2, Word(0n)>, y => CW0.z(y), LAST(m, d), False{}, eL)

# CW, from its bits and its WNil
def CWs.some(+p: Nat, +m: Cr.Cir.Cells, +c: U32, +w: Word(p), +ew: {CWb(p, m, c) == Some{w} : Maybe<&2, Word(p)>},
  +et: {CW(0n, m, Nx(p, m, c)) == Some{WNil{}} : Maybe<&2, Word(0n)>}) -> {CW(p, m, c) == Some{w} : Maybe<&2, Word(p)>}:
  %Equal.sym(Maybe<&2, Word(p)>, CW(p, m, c), CWt(p, CWb(p, m, c), CW(0n, m, Nx(p, m, c))), CW.split(p, m, c)) : {_ == Some{w} : Maybe<&2, Word(p)>}
  %Equal.sym(Maybe<&2, Word(p)>, CWb(p, m, c), Some{w}, ew) : {CWt(p, _, CW(0n, m, Nx(p, m, c))) == Some{w} : Maybe<&2, Word(p)>}
  %Equal.sym(Maybe<&2, Word(0n)>, CW(0n, m, Nx(p, m, c)), Some{WNil{}}, et) : {CWt(p, Some{w}, _) == Some{w} : Maybe<&2, Word(p)>}
  {==}

def CWs.none(+p: Nat, +m: Cr.Cir.Cells, +c: U32, +w: Word(p), +ew: {CWb(p, m, c) == Some{w} : Maybe<&2, Word(p)>},
  +et: {CW(0n, m, Nx(p, m, c)) == None{} : Maybe<&2, Word(0n)>}) -> {CW(p, m, c) == None{} : Maybe<&2, Word(p)>}:
  %Equal.sym(Maybe<&2, Word(p)>, CW(p, m, c), CWt(p, CWb(p, m, c), CW(0n, m, Nx(p, m, c))), CW.split(p, m, c)) : {_ == None{} : Maybe<&2, Word(p)>}
  %Equal.sym(Maybe<&2, Word(p)>, CWb(p, m, c), Some{w}, ew) : {CWt(p, _, CW(0n, m, Nx(p, m, c))) == None{} : Maybe<&2, Word(p)>}
  %Equal.sym(Maybe<&2, Word(0n)>, CW(0n, m, Nx(p, m, c)), None{}, et) : {CWt(p, Some{w}, _) == None{} : Maybe<&2, Word(p)>}
  {==}

def CWs.none0(+p: Nat, +m: Cr.Cir.Cells, +c: U32, +ew: {CWb(p, m, c) == None{} : Maybe<&2, Word(p)>}) -> {CW(p, m, c) == None{} : Maybe<&2, Word(p)>}:
  %Equal.sym(Maybe<&2, Word(p)>, CW(p, m, c), CWt(p, CWb(p, m, c), CW(0n, m, Nx(p, m, c))), CW.split(p, m, c)) : {_ == None{} : Maybe<&2, Word(p)>}
  %Equal.sym(Maybe<&2, Word(p)>, CWb(p, m, c), None{}, ew) : {CWt(p, _, CW(0n, m, Nx(p, m, c))) == None{} : Maybe<&2, Word(p)>}
  {==}

# the index of the loop from 0: its 8 rounds, and the bit each sets
def Good8() -> Good(8n, 0, y => y):
  ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, {==}))))))))))))))))

# what the run of a byte goes on with, by what CW reads: its value in ov,
# or no result
def MWd.Kc(+b: Cr.Cir.State, +oc: U32, +c: U32, +pg: U32, +out: List<&2, Word(8n)>, +outn: U32,
  -K: Cr.Cir.State -> Type, -H: U32 -> Cr.Cir.State -> Type) -> Type:
  @rr: Maybe<&2, Word(8n)> -> {CW(8n, St.cl(b), c) == rr : Maybe<&2, Word(8n)>} ->
    MCW(8n, rr, w => @ow: U32 -> @oi: U32 -> @t1: U32 -> @t2: U32 -> K(ST(b, oc, ow, Sd.Byte.to_u32(w), oi, t1, t2, pg, out, outn)),
      @st: Cr.Cir.State -> H(2, st))

# the end of a byte: its WNil
def MWd.end(+f: Nat, +b: Cr.Cir.State, +oc: U32, +c: U32, +w: Word(8n), +oi: U32, +t1: U32, +t2: U32, +pg: U32, +out: List<&2, Word(8n)>, +outn: U32,
  +nw: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, -K: Cr.Cir.State -> Type, -H: U32 -> Cr.Cir.State -> Type, -O: Type,
  +ew: {CWb(8n, St.cl(b), c) == Some{w} : Maybe<&2, Word(8n)>},
  +hok: {ok(Pn(8n, nw), St.cl(b), ks, img, Nx(8n, St.cl(b), c), St.im(b), St.fs(b), St.nx(b)) == True{} : Bool},
  kk: MWd.Kc(b, oc, c, pg, out, outn, K, H)) ->
  Wp(Cr.Cir.exec(1n+f, Mc.M.do([MW.end()]), ST(b, oc, Nx(8n, St.cl(b), c), Sd.Byte.to_u32(w), oi, t1, t2, pg, out, outn)), K, H, O):
  +m = St.cl(b)
  +d = Nx(8n, m, c)
  +s0 = ST(b, oc, d, Sd.Byte.to_u32(w), oi, t1, t2, pg, out, outn)
  +hc = ok.isc(Pn(8n, nw), m, ks, img, d, St.im(b), St.fs(b), St.nx(b), hok)
  -K1 = {t => Wp(Cr.Cir.exec(1n+f, Cr.Cir.Stmt.nop{}, t), K, H, O) : Cr.Cir.State -> Type}
  -A = MWd.Kc(b, oc, c, pg, out, outn, K, H)
  Wp.seq(f, MW.end(), Cr.Cir.Stmt.nop{}, s0, K, H, O,
    Wp.need(f, Mc.M.pair(Mc.R.ow()), Mc.M.need(Mc.M.is_lab(Mc.M.f(2n, Mc.M.g(Mc.R.ow())), Mc.N.wnil()), Mc.M.need(Mc.M.last(Mc.R.ow()), Cr.Cir.Stmt.nop{})), s0, K1, H, O,
      Pm(m, d), ev.pair(46n, s0, d, {==}, hc),
     CasesK(Pm(m, d), A, kk, Wp(Cr.Cir.exec(1n+f, Mc.M.need(Mc.M.is_lab(Mc.M.f(2n, Mc.M.g(Mc.R.ow())), Mc.N.wnil()), Mc.M.need(Mc.M.last(Mc.R.ow()), Cr.Cir.Stmt.nop{})), s0), K1, H, O), H(2, s0),
      kk => +eP =>
        Wp.need(f, Mc.M.is_lab(Mc.M.f(2n, Mc.M.g(Mc.R.ow())), Mc.N.wnil()), Mc.M.need(Mc.M.last(Mc.R.ow()), Cr.Cir.Stmt.nop{}), s0, K1, H, O, ISLAB(m, d, 3),
          ev.islab(2n, 46n, 3, s0, d, {==}, hc, ok.isc(Pr(Pn(8n, nw)), m, ks, img, Fd(2n, m, d), St.im(b), St.fs(b), St.nx(b), ok.L(Pn(8n, nw), m, ks, img, d, St.im(b), St.fs(b), St.nx(b), hok, eP))),
         CasesK(ISLAB(m, d, 3), A, kk, Wp(Cr.Cir.exec(1n+f, Mc.M.need(Mc.M.last(Mc.R.ow()), Cr.Cir.Stmt.nop{}), s0), K1, H, O), H(2, s0),
          kk => +eI =>
            Wp.need(f, Mc.M.last(Mc.R.ow()), Cr.Cir.Stmt.nop{}, s0, K1, H, O, LAST(m, d),
              ev.islab(3n, 46n, 0, s0, d, {==}, hc, ok.isc(Pr(Pn(8n, nw)), m, ks, img, Fd(3n, m, d), St.im(b), St.fs(b), St.nx(b), ok.R(Pn(8n, nw), m, ks, img, d, St.im(b), St.fs(b), St.nx(b), hok, eP))),
             CasesK(LAST(m, d), A, kk, Wp(Cr.Cir.exec(1n+f, Cr.Cir.Stmt.nop{}, s0), K1, H, O), H(2, s0),
              kk => +eL =>
                kk(Some{w}, CWs.some(8n, m, c, w, ew, CW0.ok(m, d, eP, eI, eL)), d, oi, t1, t2),
              kk => +eL =>
                kk(None{}, CWs.none(8n, m, c, w, ew, CW0.n3(m, d, eP, eI, eL)), s0))),
          kk => +eI =>
            kk(None{}, CWs.none(8n, m, c, w, ew, CW0.n2(m, d, eP, eI)), s0))),
      kk => +eP =>
        kk(None{}, CWs.none(8n, m, c, w, ew, CW0.n1(m, d, eP)), s0))))

# M.out.byte on the cell c in ow: the value of the byte that CW reads goes
# into ov, or the run ends with no result
def MWd(+f: Nat, +hF: PN.Le(33n, 1n+f), +b: Cr.Cir.State, +oc: U32, +c: U32, +ov: U32, +oi: U32, +t1: U32, +t2: U32, +pg: U32,
  +out: List<&2, Word(8n)>, +outn: U32, +nw: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  -K: Cr.Cir.State -> Type, -H: U32 -> Cr.Cir.State -> Type, -O: Type,
  +hok: {ok(nw, St.cl(b), ks, img, c, St.im(b), St.fs(b), St.nx(b)) == True{} : Bool},
  kk: MWd.Kc(b, oc, c, pg, out, outn, K, H)) ->
  Wp(Cr.Cir.exec(1n+f, Mc.M.out.byte(), ST(b, oc, c, ov, oi, t1, t2, pg, out, outn)), K, H, O):
  +m = St.cl(b)
  +s1 = ST(b, oc, c, 0, oi, t1, t2, pg, out, outn)
  +s2 = ST(b, oc, c, 0, 0, t1, t2, pg, out, outn)
  -K1 = {t => Wp(Cr.Cir.exec(1n+f, Mc.M.do([MW.end()]), t), K, H, O) : Cr.Cir.State -> Type}
  -A = MWd.Kc(b, oc, c, pg, out, outn, K, H)
  Wp.seq(f, Mc.M.set(Mc.R.ov(), Mc.M.c(0)), Mc.M.do([Mc.M.set(Mc.R.oi(), Mc.M.c(0)), MW.loop(), MW.end()]), ST(b, oc, c, ov, oi, t1, t2, pg, out, outn), K, H, O,
    Wp.set(f, 47n, Mc.M.c(0), ST(b, oc, c, ov, oi, t1, t2, pg, out, outn), t => Wp(Cr.Cir.exec(1n+f, Mc.M.do([Mc.M.set(Mc.R.oi(), Mc.M.c(0)), MW.loop(), MW.end()]), t), K, H, O), H, O, 0, {==},
      Wp.seq(f, Mc.M.set(Mc.R.oi(), Mc.M.c(0)), Mc.M.do([MW.loop(), MW.end()]), s1, K, H, O,
        Wp.set(f, 48n, Mc.M.c(0), s1, t => Wp(Cr.Cir.exec(1n+f, Mc.M.do([MW.loop(), MW.end()]), t), K, H, O), H, O, 0, {==},
          Wp.seq(f, MW.loop(), Mc.M.do([MW.end()]), s2, K, H, O,
            ML(8n, 1n+f, PN.le_trans(9n, 33n, 1n+f, PN.le_add_r(9n, 24n), hF), b, oc, c, 0, 0, t1, t2, pg, out, outn, nw, ks, img, y => y, y => y, HK8(), Good8(), K1, H, O, {==}, hok,
              rr => +err => CasesW(8n, rr, A, kk,
                w => {ok(Pn(8n, nw), m, ks, img, Nx(8n, m, c), St.im(b), St.fs(b), St.nx(b)) == True{} : Bool} ->
                  @oi: U32 -> @t1: U32 -> @t2: U32 -> K1(ST(b, oc, Nx(8n, m, c), Sd.Byte.to_u32(w), oi, t1, t2, pg, out, outn)),
                @st: Cr.Cir.State -> H(2, st),
                kk => +w => +ew => +hokd => +oi2 => +t12 => +t22 =>
                  MWd.end(f, b, oc, c, w, oi2, t12, t22, pg, out, outn, nw, ks, img, K, H, O,
                    Equal.trans(Maybe<&2, Word(8n)>, CWb(8n, m, c), rr, Some{w}, err, ew), hokd, kk),
                kk => +ew =>
                  st => kk(None{}, CWs.none0(8n, m, c, Equal.trans(Maybe<&2, Word(8n)>, CWb(8n, m, c), rr, None{}, err, ew)), st))))))))

# the steps of S.c0: its value once its tests pass, or none when one fails
def Sc.ok(+m: Cr.Cir.Cells, +bc: U32, +w: Word(8n),
  +ePb: {Pm(m, bc) == True{} : Bool},
  +ePy: {Pm(m, Fd(3n, m, bc)) == True{} : Bool},
  +eLy: {LAST(m, Fd(3n, m, bc)) == True{} : Bool},
  +eW: {CW(8n, m, Fd(2n, m, bc)) == Some{w} : Maybe<&2, Word(8n)>}) ->
  {S.c0(Pm(m, bc), m, bc) == SR.more{w, Fd(2n, m, Fd(3n, m, bc))} : SR}:
  +xc = Fd(2n, m, bc)
  +yc = Fd(3n, m, bc)
  +rc = Fd(2n, m, yc)
  %Equal.sym(Bool, Pm(m, bc), True{}, ePb) : {S.c0(_, m, bc) == SR.more{w, rc} : SR}
  %Equal.sym(Bool, Pm(m, yc), True{}, ePy) : {S.c1(_, m, xc, yc) == SR.more{w, rc} : SR}
  %Equal.sym(Bool, LAST(m, yc), True{}, eLy) : {S.c2(_, m, xc, rc) == SR.more{w, rc} : SR}
  %Equal.sym(Maybe<&2, Word(8n)>, CW(8n, m, xc), Some{w}, eW) : {S.c3(_, rc) == SR.more{w, rc} : SR}
  {==}

def Sc.n1(+m: Cr.Cir.Cells, +bc: U32,
  +ePb: {Pm(m, bc) == False{} : Bool}) ->
  {S.c0(Pm(m, bc), m, bc) == SR.done{None{}} : SR}:
  Equal.cong(Bool, SR, yy => S.c0(yy, m, bc), Pm(m, bc), False{}, ePb)

def Sc.n2(+m: Cr.Cir.Cells, +bc: U32,
  +ePb: {Pm(m, bc) == True{} : Bool},
  +ePy: {Pm(m, Fd(3n, m, bc)) == False{} : Bool}) ->
  {S.c0(Pm(m, bc), m, bc) == SR.done{None{}} : SR}:
  +xc = Fd(2n, m, bc)
  +yc = Fd(3n, m, bc)
  %Equal.sym(Bool, Pm(m, bc), True{}, ePb) : {S.c0(_, m, bc) == SR.done{None{}} : SR}
  Equal.cong(Bool, SR, yy => S.c1(yy, m, xc, yc), Pm(m, yc), False{}, ePy)

def Sc.n3(+m: Cr.Cir.Cells, +bc: U32,
  +ePb: {Pm(m, bc) == True{} : Bool},
  +ePy: {Pm(m, Fd(3n, m, bc)) == True{} : Bool},
  +eLy: {LAST(m, Fd(3n, m, bc)) == False{} : Bool}) ->
  {S.c0(Pm(m, bc), m, bc) == SR.done{None{}} : SR}:
  +xc = Fd(2n, m, bc)
  +yc = Fd(3n, m, bc)
  +rc = Fd(2n, m, yc)
  %Equal.sym(Bool, Pm(m, bc), True{}, ePb) : {S.c0(_, m, bc) == SR.done{None{}} : SR}
  %Equal.sym(Bool, Pm(m, yc), True{}, ePy) : {S.c1(_, m, xc, yc) == SR.done{None{}} : SR}
  Equal.cong(Bool, SR, yy => S.c2(yy, m, xc, rc), LAST(m, yc), False{}, eLy)

def Sc.n4(+m: Cr.Cir.Cells, +bc: U32,
  +ePb: {Pm(m, bc) == True{} : Bool},
  +ePy: {Pm(m, Fd(3n, m, bc)) == True{} : Bool},
  +eLy: {LAST(m, Fd(3n, m, bc)) == True{} : Bool},
  +eW: {CW(8n, m, Fd(2n, m, bc)) == None{} : Maybe<&2, Word(8n)>}) ->
  {S.c0(Pm(m, bc), m, bc) == SR.done{None{}} : SR}:
  +xc = Fd(2n, m, bc)
  +yc = Fd(3n, m, bc)
  +rc = Fd(2n, m, yc)
  %Equal.sym(Bool, Pm(m, bc), True{}, ePb) : {S.c0(_, m, bc) == SR.done{None{}} : SR}
  %Equal.sym(Bool, Pm(m, yc), True{}, ePy) : {S.c1(_, m, xc, yc) == SR.done{None{}} : SR}
  %Equal.sym(Bool, LAST(m, yc), True{}, eLy) : {S.c2(_, m, xc, rc) == SR.done{None{}} : SR}
  Equal.cong(Maybe<&2, Word(8n)>, SR, yy => S.c3(yy, rc), CW(8n, m, xc), None{}, eW)

# The byte
# --------

# the statements of M.out.con
def OC.A1() -> Cr.Cir.Stmt:
  Mc.M.set(Mc.R.oc(), Mc.M.f(3n, Mc.M.g(Mc.R.oc())))

def OC.B1() -> Cr.Cir.Stmt:
  Mc.M.set(Mc.R.ow(), Mc.M.f(2n, Mc.M.g(Mc.R.oc())))

def OC.B2() -> Cr.Cir.Stmt:
  Mc.M.set(Mc.R.oc(), Mc.M.f(3n, Mc.M.g(Mc.R.oc())))

def OC.C1() -> Cr.Cir.Stmt:
  Mc.M.set(Mc.R.oc(), Mc.M.f(2n, Mc.M.g(Mc.R.oc())))

def OC.E() -> Cr.Cir.Stmt:
  Cr.Cir.Stmt.emit{Mc.M.g(Mc.R.ov())}

def OC.C() -> Cr.Cir.Stmt:
  Mc.M.do([OC.C1(), Mc.M.out.byte(), OC.E()])

def OC.B3() -> Cr.Cir.Stmt:
  Mc.M.need(Mc.M.pair(Mc.R.oc()), Mc.M.need(Mc.M.last(Mc.R.oc()), OC.C()))

def OC.B() -> Cr.Cir.Stmt:
  Mc.M.do([OC.B1(), OC.B2(), OC.B3()])

# Y for a list's end, X(v, rest) for a byte v and the cell of the rest
def MSR(s: SR, X: Word(8n) -> U32 -> Type, Y: Maybe<&2, List<&2, Word(8n)>> -> Type) -> Type:
  match s:
    case SR.more{v, rest}:
      X(v, rest)
    case SR.done{r}:
      Y(r)

def CasesS(s: SR, -A: Type, a: A, -X: Word(8n) -> U32 -> Type, -Y: Maybe<&2, List<&2, Word(8n)>> -> Type,
  sm: A -> @v: Word(8n) -> @rest: U32 -> {s == SR.more{v, rest} : SR} -> X(v, rest),
  sd: A -> @r: Maybe<&2, List<&2, Word(8n)>> -> {s == SR.done{r} : SR} -> Y(r)) -> MSR(s, X, Y):
  match s:
    case SR.more{v, rest}:
      sm(a, v, rest, {==})
    case SR.done{r}:
      sd(a, r, {==})

# what the run of M.out.con goes on with, by what S.c0 reads at the fields
# of the cell c: its byte out, with oc at the rest of the list, or no result
def MC.Kc(+b: Cr.Cir.State, +c: U32, +pg: U32, +out: List<&2, Word(8n)>, +outn: U32, +n1: Nat, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, -K: Cr.Cir.State -> Type, -H: U32 -> Cr.Cir.State -> Type) -> Type:
  @s: SR -> {S.c0(Pm(St.cl(b), Fd(3n, St.cl(b), c)), St.cl(b), Fd(3n, St.cl(b), c)) == s : SR} ->
    MSR(s, v => rest => {ok(Pr(Pr(n1)), St.cl(b), ks, img, rest, St.im(b), St.fs(b), St.nx(b)) == True{} : Bool} ->
      @pg2: U32 -> @ow: U32 -> @ov: U32 -> @oi: U32 -> @t1: U32 -> @t2: U32 -> K(ST(b, rest, ow, ov, oi, t1, t2, pg2, Con{v, out}, U32.inc(outn))),
      r => {r == None{} : Maybe<&2, List<&2, Word(8n)>>} -> @st: Cr.Cir.State -> H(2, st))

# the byte goes out: the low byte of its value, which is the byte
def MC.emit(+f: Nat, +b: Cr.Cir.State, +c: U32, +ow: U32, +w: Word(8n), +oi: U32, +t1: U32, +t2: U32, +pg: U32,
  +out: List<&2, Word(8n)>, +outn: U32, +n1: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  -K: Cr.Cir.State -> Type, -H: U32 -> Cr.Cir.State -> Type, -O: Type,
  +hok1: {ok(n1, St.cl(b), ks, img, Fd(3n, St.cl(b), c), St.im(b), St.fs(b), St.nx(b)) == True{} : Bool},
  +ePb: {Pm(St.cl(b), Fd(3n, St.cl(b), c)) == True{} : Bool},
  +ePy: {Pm(St.cl(b), Fd(3n, St.cl(b), Fd(3n, St.cl(b), c))) == True{} : Bool},
  +eLy: {LAST(St.cl(b), Fd(3n, St.cl(b), Fd(3n, St.cl(b), c))) == True{} : Bool},
  +eW: {CW(8n, St.cl(b), Fd(2n, St.cl(b), Fd(3n, St.cl(b), c))) == Some{w} : Maybe<&2, Word(8n)>},
  ho: EB(St.lim(b), St.nx(b), outn) -> O, kk: MC.Kc(b, c, pg, out, outn, n1, ks, img, K, H)) ->
  Wp(Cr.Cir.exec(1n+f, Mc.M.do([OC.E()]), ST(b, Fd(2n, St.cl(b), Fd(3n, St.cl(b), Fd(3n, St.cl(b), c))), ow, Sd.Byte.to_u32(w), oi, t1, t2, pg, out, outn)), K, H, O):
  +m = St.cl(b)
  +bc = Fd(3n, m, c)
  +yc = Fd(3n, m, bc)
  +rc = Fd(2n, m, yc)
  +v = Sd.Byte.to_u32(w)
  +s = ST(b, rc, ow, v, oi, t1, t2, pg, out, outn)
  -K1 = {t => Wp(Cr.Cir.exec(1n+f, Cr.Cir.Stmt.nop{}, t), K, H, O) : Cr.Cir.State -> Type}
  Wp.seq(f, OC.E(), Cr.Cir.Stmt.nop{}, s, K, H, O,
    Wp.emit(f, Mc.M.g(Mc.R.ov()), s, K1, H, O, v, {==}, ho,
      p => Tr(Word(8n), y => K(ST(b, rc, ow, v, oi, t1, t2, p, Con{y, out}, U32.inc(outn))), w, Sd.Byte.from_u32(v),
        Equal.sym(Word(8n), Sd.Byte.from_u32(v), w, low_pad(8n, 24n, w)),
        kk(SR.more{w, rc}, Sc.ok(m, bc, w, ePb, ePy, eLy, eW), ok.L(Pr(n1), m, ks, img, yc, St.im(b), St.fs(b), St.nx(b), ok.R(n1, m, ks, img, bc, St.im(b), St.fs(b), St.nx(b), hok1, ePb), ePy), p, ow, v, oi, t1, t2))))

# the rest of the list goes into oc, and the byte into ov
def MC.C(+f: Nat, +hF: PN.Le(33n, 1n+f), +b: Cr.Cir.State, +c: U32, +ov: U32, +oi: U32, +t1: U32, +t2: U32, +pg: U32,
  +out: List<&2, Word(8n)>, +outn: U32, +n1: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  -K: Cr.Cir.State -> Type, -H: U32 -> Cr.Cir.State -> Type, -O: Type,
  +hok1: {ok(n1, St.cl(b), ks, img, Fd(3n, St.cl(b), c), St.im(b), St.fs(b), St.nx(b)) == True{} : Bool},
  +ePb: {Pm(St.cl(b), Fd(3n, St.cl(b), c)) == True{} : Bool},
  +ePy: {Pm(St.cl(b), Fd(3n, St.cl(b), Fd(3n, St.cl(b), c))) == True{} : Bool},
  +eLy: {LAST(St.cl(b), Fd(3n, St.cl(b), Fd(3n, St.cl(b), c))) == True{} : Bool},
  ho: EB(St.lim(b), St.nx(b), outn) -> O, kk: MC.Kc(b, c, pg, out, outn, n1, ks, img, K, H)) ->
  Wp(Cr.Cir.exec(1n+f, OC.C(), ST(b, Fd(3n, St.cl(b), Fd(3n, St.cl(b), c)), Fd(2n, St.cl(b), Fd(3n, St.cl(b), c)), ov, oi, t1, t2, pg, out, outn)), K, H, O):
  +m = St.cl(b)
  +bc = Fd(3n, m, c)
  +xc = Fd(2n, m, bc)
  +yc = Fd(3n, m, bc)
  +rc = Fd(2n, m, yc)
  -A = MC.Kc(b, c, pg, out, outn, n1, ks, img, K, H)
  +s3 = ST(b, yc, xc, ov, oi, t1, t2, pg, out, outn)
  +s4 = ST(b, rc, xc, ov, oi, t1, t2, pg, out, outn)
  -KE = {t => Wp(Cr.Cir.exec(1n+f, Mc.M.do([OC.E()]), t), K, H, O) : Cr.Cir.State -> Type}
  Wp.seq(f, OC.C1(), Mc.M.do([Mc.M.out.byte(), OC.E()]), s3, K, H, O,
    Wp.set(f, 45n, Mc.M.f(2n, Mc.M.g(Mc.R.oc())), s3, t => Wp(Cr.Cir.exec(1n+f, Mc.M.do([Mc.M.out.byte(), OC.E()]), t), K, H, O), H, O, rc,
      ev.f(2n, Mc.M.g(Mc.R.oc()), s3, yc, {==}, ok.isc(Pr(n1), m, ks, img, yc, St.im(b), St.fs(b), St.nx(b), ok.R(n1, m, ks, img, bc, St.im(b), St.fs(b), St.nx(b), hok1, ePb))),
      Wp.seq(f, Mc.M.out.byte(), Mc.M.do([OC.E()]), s4, K, H, O,
        MWd(f, hF, b, rc, xc, ov, oi, t1, t2, pg, out, outn, Pr(n1), ks, img, KE, H, O,
          ok.L(n1, m, ks, img, bc, St.im(b), St.fs(b), St.nx(b), hok1, ePb),
          rr => +err => CasesW(8n, rr, A, kk,
            w => @ow: U32 -> @oi: U32 -> @t1: U32 -> @t2: U32 -> KE(ST(b, rc, ow, Sd.Byte.to_u32(w), oi, t1, t2, pg, out, outn)),
            @st: Cr.Cir.State -> H(2, st),
            kk => +w => +ew => +ow2 => +oi2 => +t12 => +t22 =>
              MC.emit(f, b, c, ow2, w, oi2, t12, t22, pg, out, outn, n1, ks, img, K, H, O, hok1, ePb, ePy, eLy,
                Equal.trans(Maybe<&2, Word(8n)>, CW(8n, m, xc), rr, Some{w}, err, ew), ho, kk),
            kk => +ew =>
              st => kk(SR.done{None{}}, Sc.n4(m, bc, ePb, ePy, eLy, Equal.trans(Maybe<&2, Word(8n)>, CW(8n, m, xc), rr, None{}, err, ew)), {==}, st))))))

# M.out.con on the cell c in oc, a list's Con: its byte goes out, and oc
# gets the rest of the list; or the run ends with no result
def MCon(+f: Nat, +hF: PN.Le(33n, 1n+f), +b: Cr.Cir.State, +c: U32, +ow: U32, +ov: U32, +oi: U32, +t1: U32, +t2: U32, +pg: U32,
  +out: List<&2, Word(8n)>, +outn: U32, +n1: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  -K: Cr.Cir.State -> Type, -H: U32 -> Cr.Cir.State -> Type, -O: Type,
  +hc: {True{} == Cr.Cir.is_cell(c, St.im(b), St.fs(b), St.nx(b)) : Bool},
  +hok1: {ok(n1, St.cl(b), ks, img, Fd(3n, St.cl(b), c), St.im(b), St.fs(b), St.nx(b)) == True{} : Bool},
  ho: EB(St.lim(b), St.nx(b), outn) -> O, kk: MC.Kc(b, c, pg, out, outn, n1, ks, img, K, H)) ->
  Wp(Cr.Cir.exec(1n+f, Mc.M.out.con(), ST(b, c, ow, ov, oi, t1, t2, pg, out, outn)), K, H, O):
  +m = St.cl(b)
  +bc = Fd(3n, m, c)
  +xc = Fd(2n, m, bc)
  +yc = Fd(3n, m, bc)
  +rc = Fd(2n, m, yc)
  -A = MC.Kc(b, c, pg, out, outn, n1, ks, img, K, H)
  +s0 = ST(b, c, ow, ov, oi, t1, t2, pg, out, outn)
  +s1 = ST(b, bc, ow, ov, oi, t1, t2, pg, out, outn)
  +s2 = ST(b, bc, xc, ov, oi, t1, t2, pg, out, outn)
  +s3 = ST(b, yc, xc, ov, oi, t1, t2, pg, out, outn)
  +hcb = ok.isc(n1, m, ks, img, bc, St.im(b), St.fs(b), St.nx(b), hok1)
  -K1 = {t => Wp(Cr.Cir.exec(1n+f, Cr.Cir.Stmt.nop{}, t), K, H, O) : Cr.Cir.State -> Type}
  -K2 = {t => Wp(Cr.Cir.exec(1n+f, Cr.Cir.Stmt.nop{}, t), K1, H, O) : Cr.Cir.State -> Type}
  Wp.seq(f, OC.A1(), Mc.M.do([Mc.M.need(Mc.M.pair(Mc.R.oc()), OC.B())]), s0, K, H, O,
    Wp.set(f, 45n, Mc.M.f(3n, Mc.M.g(Mc.R.oc())), s0, t => Wp(Cr.Cir.exec(1n+f, Mc.M.do([Mc.M.need(Mc.M.pair(Mc.R.oc()), OC.B())]), t), K, H, O), H, O, bc,
      ev.f(3n, Mc.M.g(Mc.R.oc()), s0, c, {==}, hc),
      Wp.seq(f, Mc.M.need(Mc.M.pair(Mc.R.oc()), OC.B()), Cr.Cir.Stmt.nop{}, s1, K, H, O,
        Wp.need(f, Mc.M.pair(Mc.R.oc()), OC.B(), s1, K1, H, O, Pm(m, bc), ev.pair(45n, s1, bc, {==}, hcb),
         CasesK(Pm(m, bc), A, kk, Wp(Cr.Cir.exec(1n+f, OC.B(), s1), K1, H, O), H(2, s1),
          kk => +ePb =>
            Wp.seq(f, OC.B1(), Mc.M.do([OC.B2(), OC.B3()]), s1, K1, H, O,
              Wp.set(f, 46n, Mc.M.f(2n, Mc.M.g(Mc.R.oc())), s1, t => Wp(Cr.Cir.exec(1n+f, Mc.M.do([OC.B2(), OC.B3()]), t), K1, H, O), H, O, xc,
                ev.f(2n, Mc.M.g(Mc.R.oc()), s1, bc, {==}, hcb),
                Wp.seq(f, OC.B2(), Mc.M.do([OC.B3()]), s2, K1, H, O,
                  Wp.set(f, 45n, Mc.M.f(3n, Mc.M.g(Mc.R.oc())), s2, t => Wp(Cr.Cir.exec(1n+f, Mc.M.do([OC.B3()]), t), K1, H, O), H, O, yc,
                    ev.f(3n, Mc.M.g(Mc.R.oc()), s2, bc, {==}, hcb),
                    Wp.seq(f, OC.B3(), Cr.Cir.Stmt.nop{}, s3, K1, H, O,
                      Wp.need(f, Mc.M.pair(Mc.R.oc()), Mc.M.need(Mc.M.last(Mc.R.oc()), OC.C()), s3, K2, H, O, Pm(m, yc), ev.pair(45n, s3, yc, {==}, ok.isc(Pr(n1), m, ks, img, yc, St.im(b), St.fs(b), St.nx(b), ok.R(n1, m, ks, img, bc, St.im(b), St.fs(b), St.nx(b), hok1, ePb))),
                       CasesK(Pm(m, yc), A, kk, Wp(Cr.Cir.exec(1n+f, Mc.M.need(Mc.M.last(Mc.R.oc()), OC.C()), s3), K2, H, O), H(2, s3),
                        kk => +ePy =>
                          Wp.need(f, Mc.M.last(Mc.R.oc()), OC.C(), s3, K2, H, O, LAST(m, yc), ev.islab(3n, 45n, 0, s3, yc, {==}, ok.isc(Pr(n1), m, ks, img, yc, St.im(b), St.fs(b), St.nx(b), ok.R(n1, m, ks, img, bc, St.im(b), St.fs(b), St.nx(b), hok1, ePb)), ok.isc(Pr(Pr(n1)), m, ks, img, Fd(3n, m, yc), St.im(b), St.fs(b), St.nx(b), ok.R(Pr(n1), m, ks, img, yc, St.im(b), St.fs(b), St.nx(b), ok.R(n1, m, ks, img, bc, St.im(b), St.fs(b), St.nx(b), hok1, ePb), ePy))),
                           CasesK(LAST(m, yc), A, kk, Wp(Cr.Cir.exec(1n+f, OC.C(), s3), K2, H, O), H(2, s3),
                            kk => +eLy =>
                              MC.C(f, hF, b, c, ov, oi, t1, t2, pg, out, outn, n1, ks, img, K2, H, O, hok1, ePb, ePy, eLy, ho, kk),
                            kk => +eLy =>
                              kk(SR.done{None{}}, Sc.n3(m, bc, ePb, ePy, eLy), {==}, s3))),
                        kk => +ePy =>
                          kk(SR.done{None{}}, Sc.n2(m, bc, ePb, ePy), {==}, s3)))))))),
          kk => +ePb =>
            kk(SR.done{None{}}, Sc.n1(m, bc, ePb), {==}, s1))))))

# The list
# --------

# the steps of Step at a list cell: its end, its Con, or none when a test fails
def StN.ok(+m: Cr.Cir.Cells, +c: U32,
  +eP: {Pm(m, c) == True{} : Bool},
  +eM: {Lm(m, Fd(2n, m, c)) == True{} : Bool},
  +eN: {U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 1) == True{} : Bool},
  +eL: {LAST(m, c) == True{} : Bool}) ->
  {Step(m, c) == SR.done{Some{Nil{}}} : SR}:
  +x22 = Fd(2n, m, Fd(2n, m, c))
  %Equal.sym(Bool, Pm(m, c), True{}, eP) : {S.p(_, m, c) == SR.done{Some{Nil{}}} : SR}
  %Equal.sym(Bool, Lm(m, Fd(2n, m, c)), True{}, eM) : {S.l(_, m, c) == SR.done{Some{Nil{}}} : SR}
  %Equal.sym(Bool, U32.is_eq(x22, 1), True{}, eN) : {S.w(_, U32.is_eq(x22, 2), m, c) == SR.done{Some{Nil{}}} : SR}
  %Equal.sym(Bool, LAST(m, c), True{}, eL) : {S.nil(_) == SR.done{Some{Nil{}}} : SR}
  {==}

def StN.n1(+m: Cr.Cir.Cells, +c: U32,
  +eP: {Pm(m, c) == False{} : Bool}) ->
  {Step(m, c) == SR.done{None{}} : SR}:
  +x22 = Fd(2n, m, Fd(2n, m, c))
  Equal.cong(Bool, SR, yy => S.p(yy, m, c), Pm(m, c), False{}, eP)

def StN.n2(+m: Cr.Cir.Cells, +c: U32,
  +eP: {Pm(m, c) == True{} : Bool},
  +eM: {Lm(m, Fd(2n, m, c)) == False{} : Bool}) ->
  {Step(m, c) == SR.done{None{}} : SR}:
  +x22 = Fd(2n, m, Fd(2n, m, c))
  %Equal.sym(Bool, Pm(m, c), True{}, eP) : {S.p(_, m, c) == SR.done{None{}} : SR}
  Equal.cong(Bool, SR, yy => S.l(yy, m, c), Lm(m, Fd(2n, m, c)), False{}, eM)

def StN.n4(+m: Cr.Cir.Cells, +c: U32,
  +eP: {Pm(m, c) == True{} : Bool},
  +eM: {Lm(m, Fd(2n, m, c)) == True{} : Bool},
  +eN: {U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 1) == True{} : Bool},
  +eL: {LAST(m, c) == False{} : Bool}) ->
  {Step(m, c) == SR.done{None{}} : SR}:
  +x22 = Fd(2n, m, Fd(2n, m, c))
  %Equal.sym(Bool, Pm(m, c), True{}, eP) : {S.p(_, m, c) == SR.done{None{}} : SR}
  %Equal.sym(Bool, Lm(m, Fd(2n, m, c)), True{}, eM) : {S.l(_, m, c) == SR.done{None{}} : SR}
  %Equal.sym(Bool, U32.is_eq(x22, 1), True{}, eN) : {S.w(_, U32.is_eq(x22, 2), m, c) == SR.done{None{}} : SR}
  Equal.cong(Bool, SR, yy => S.nil(yy), LAST(m, c), False{}, eL)

def StC.ok(+m: Cr.Cir.Cells, +c: U32,
  +eP: {Pm(m, c) == True{} : Bool},
  +eM: {Lm(m, Fd(2n, m, c)) == True{} : Bool},
  +eN: {U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 1) == False{} : Bool},
  +eC: {U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 2) == True{} : Bool}) ->
  {Step(m, c) == S.c0(Pm(m, Fd(3n, m, c)), m, Fd(3n, m, c)) : SR}:
  +x22 = Fd(2n, m, Fd(2n, m, c))
  %Equal.sym(Bool, Pm(m, c), True{}, eP) : {S.p(_, m, c) == S.c0(Pm(m, Fd(3n, m, c)), m, Fd(3n, m, c)) : SR}
  %Equal.sym(Bool, Lm(m, Fd(2n, m, c)), True{}, eM) : {S.l(_, m, c) == S.c0(Pm(m, Fd(3n, m, c)), m, Fd(3n, m, c)) : SR}
  %Equal.sym(Bool, U32.is_eq(x22, 1), False{}, eN) : {S.w(_, U32.is_eq(x22, 2), m, c) == S.c0(Pm(m, Fd(3n, m, c)), m, Fd(3n, m, c)) : SR}
  %Equal.sym(Bool, U32.is_eq(x22, 2), True{}, eC) : {S.k2(_, m, Fd(3n, m, c)) == S.c0(Pm(m, Fd(3n, m, c)), m, Fd(3n, m, c)) : SR}
  {==}

def StC.n4(+m: Cr.Cir.Cells, +c: U32,
  +eP: {Pm(m, c) == True{} : Bool},
  +eM: {Lm(m, Fd(2n, m, c)) == True{} : Bool},
  +eN: {U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 1) == False{} : Bool},
  +eC: {U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 2) == False{} : Bool}) ->
  {Step(m, c) == SR.done{None{}} : SR}:
  +x22 = Fd(2n, m, Fd(2n, m, c))
  %Equal.sym(Bool, Pm(m, c), True{}, eP) : {S.p(_, m, c) == SR.done{None{}} : SR}
  %Equal.sym(Bool, Lm(m, Fd(2n, m, c)), True{}, eM) : {S.l(_, m, c) == SR.done{None{}} : SR}
  %Equal.sym(Bool, U32.is_eq(x22, 1), False{}, eN) : {S.w(_, U32.is_eq(x22, 2), m, c) == SR.done{None{}} : SR}
  Equal.cong(Bool, SR, yy => S.k2(yy, m, Fd(3n, m, c)), U32.is_eq(x22, 2), False{}, eC)

# n increments of x, one for each byte of bs
def Incs(bs: List<&2, Word(8n)>, x: U32) -> U32:
  match bs:
    case Nil{}:
      x
    case Con{_, t}:
      Incs(t, U32.inc(x))

# a halt of the run of M.out, with the status s and the state st, says what
# r says: the bytes of r out (the last first, before out0) and their number
# added to outn0, with the status 0; the status 2 when r is none
def Fin(r: Maybe<&2, List<&2, Word(8n)>>, out0: List<&2, Word(8n)>, outn0: U32, s: U32, st: Cr.Cir.State) -> Type:
  match r:
    case Some{bs}:
      {s == 0 : U32} & ({St.out(st) == List.reverse.go(&2, Word(8n), bs, out0) : List<&2, Word(8n)>} & {St.outn(st) == Incs(bs, outn0) : U32})
    case None{}:
      {s == 2 : U32}

def Fin.cons(r: Maybe<&2, List<&2, Word(8n)>>, +v: Word(8n), +out: List<&2, Word(8n)>, +outn: U32, +s: U32, +st: Cr.Cir.State,
  h: Fin(r, Con{v, out}, U32.inc(outn), s, st)) -> Fin(U.c5(v, r), out, outn, s, st):
  match r:
    case Some{bs}:
      h
    case None{}:
      h

def Wp.mapH(o: Cr.Cir.Out, -K: Cr.Cir.State -> Type, -H1: U32 -> Cr.Cir.State -> Type, -H2: U32 -> Cr.Cir.State -> Type, -O: Type,
  f: @s: U32 -> @st: Cr.Cir.State -> H1(s, st) -> H2(s, st), h: Wp(o, K, H1, O)) -> Wp(o, K, H2, O):
  match o:
    case Cr.Cir.Out.next{st}:
      h
    case Cr.Cir.Out.halt{s, st}:
      f(s, st, h)
    case Cr.Cir.Out.out_of_memory{}:
      h
    case Cr.Cir.Out.trap{}:
      match h:
    case Cr.Cir.Out.not_done{}:
      match h:

# CU at the end of a list
def CUd(+a: Nat, +m: Cr.Cir.Cells, +r: Maybe<&2, List<&2, Word(8n)>>) -> {CU(1n+a, m, SR.done{r}) == r : Maybe<&2, List<&2, Word(8n)>>}:
  match a:
    case 0n:
      {==}
    case 1n+b:
      match b:
        case 0n:
          {==}
        case 1n+d:
          {==}

# CU at a byte, with the fuel that ok grants the rest
def CUm(+n1: Nat, +m: Cr.Cir.Cells, +v: Word(8n), +rc: U32, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +im: U32, +fs: U32, +nx: U32,
  +h: {ok(Pr(Pr(n1)), m, ks, img, rc, im, fs, nx) == True{} : Bool}) ->
  {U.c5(v, CU(Pr(Pr(n1)), m, Step(m, rc))) == CU(1n+n1, m, SR.more{v, rc}) : Maybe<&2, List<&2, Word(8n)>>}:
  match n1:
    case 0n:
      Empty.absurd({U.c5(v, CU(0n, m, Step(m, rc))) == CU(1n, m, SR.more{v, rc}) : Maybe<&2, List<&2, Word(8n)>>}, ok.zero(m, ks, img, rc, im, fs, nx, h))
    case 1n+n2:
      match n2:
        case 0n:
          Empty.absurd({U.c5(v, CU(0n, m, Step(m, rc))) == CU(2n, m, SR.more{v, rc}) : Maybe<&2, List<&2, Word(8n)>>}, ok.zero(m, ks, img, rc, im, fs, nx, h))
        case 1n+d:
          {==}

def Fin.none(+n1: Nat, +m: Cr.Cir.Cells, +c: U32, +out: List<&2, Word(8n)>, +outn: U32, +st: Cr.Cir.State,
  +e: {Step(m, c) == SR.done{None{}} : SR}) -> Fin(CU(1n+n1, m, Step(m, c)), out, outn, 2, st):
  %Equal.sym(SR, Step(m, c), SR.done{None{}}, e) : Fin(CU(1n+n1, m, _), out, outn, 2, st)
  %Equal.sym(Maybe<&2, List<&2, Word(8n)>>, CU(1n+n1, m, SR.done{None{}}), None{}, CUd(n1, m, None{})) : Fin(_, out, outn, 2, st)
  {==}

def Fin.nil(+n1: Nat, +b: Cr.Cir.State, +c: U32, +ow: U32, +ov: U32, +oi: U32, +t1: U32, +t2: U32, +pg: U32, +out: List<&2, Word(8n)>, +outn: U32,
  +e: {Step(St.cl(b), c) == SR.done{Some{Nil{}}} : SR}) ->
  Fin(CU(1n+n1, St.cl(b), Step(St.cl(b), c)), out, outn, 0, ST(b, c, ow, ov, oi, t1, t2, pg, out, outn)):
  %Equal.sym(SR, Step(St.cl(b), c), SR.done{Some{Nil{}}}, e) : Fin(CU(1n+n1, St.cl(b), _), out, outn, 0, ST(b, c, ow, ov, oi, t1, t2, pg, out, outn))
  %Equal.sym(Maybe<&2, List<&2, Word(8n)>>, CU(1n+n1, St.cl(b), SR.done{Some{Nil{}}}), Some{Nil{}}, CUd(n1, St.cl(b), Some{Nil{}})) :
    Fin(_, out, outn, 0, ST(b, c, ow, ov, oi, t1, t2, pg, out, outn))
  ({==}, ({==}, {==}))

def Fin.step(+n1: Nat, +m: Cr.Cir.Cells, +c: U32, +v: Word(8n), +rc: U32, +out: List<&2, Word(8n)>, +outn: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +im: U32, +fs: U32, +nx: U32,
  +e: {Step(m, c) == SR.more{v, rc} : SR}, +hokr: {ok(Pr(Pr(n1)), m, ks, img, rc, im, fs, nx) == True{} : Bool}, +s: U32, +st: Cr.Cir.State,
  h: Fin(CU(Pr(Pr(n1)), m, Step(m, rc)), Con{v, out}, U32.inc(outn), s, st)) -> Fin(CU(1n+n1, m, Step(m, c)), out, outn, s, st):
  %Equal.sym(SR, Step(m, c), SR.more{v, rc}, e) : Fin(CU(1n+n1, m, _), out, outn, s, st)
  %CUm(n1, m, v, rc, ks, img, im, fs, nx, hokr) : Fin(_, out, outn, s, st)
  Fin.cons(CU(Pr(Pr(n1)), m, Step(m, rc)), v, out, outn, s, st, h)

def le_pr(+n: Nat) -> PN.Le(Pr(n), n):
  match n:
    case 0n:
      Unit{}
    case 1n+p:
      PN.le_succ(p, p, PN.le_refl(p))

def le_pr2(+n: Nat) -> PN.Le(Nat.add(Pr(Pr(n)), 34n), Nat.add(n, 34n)):
  PN.add_mono(Pr(Pr(n)), n, 34n, 34n, PN.le_trans(Pr(Pr(n)), Pr(n), n, le_pr(Pr(n)), le_pr(n)), PN.le_refl(34n))

# the loop of M.out and its body
def BO.a() -> Cr.Cir.Stmt:
  Mc.M.set(Mc.R.ow(), Mc.M.f(2n, Mc.M.f(2n, Mc.M.g(Mc.R.oc()))))

def BO.i() -> Cr.Cir.Stmt:
  Mc.M.if(Mc.M.eq(Mc.M.g(Mc.R.ow()), Mc.M.c(Mc.N.nil())), Mc.M.need(Mc.M.last(Mc.R.oc()), Mc.M.halt(0)),
    Mc.M.need(Mc.M.eq(Mc.M.g(Mc.R.ow()), Mc.M.c(Mc.N.con())), Mc.M.out.con()))

def BO.s1() -> Cr.Cir.Stmt:
  Mc.M.need(Mc.M.eq(Mc.M.tag(Mc.M.f(2n, Mc.M.g(Mc.R.oc()))), Mc.M.c(Mc.T.lab())), Mc.M.do([BO.a(), BO.i()]))

def BO() -> Cr.Cir.Stmt:
  Mc.M.need(Mc.M.pair(Mc.R.oc()), BO.s1())

def WO() -> Cr.Cir.Stmt:
  Mc.M.while(Mc.M.c(1), BO())

# what a run of M.out from the state b gives when it runs out of memory: the
# limit has fewer bytes than 20 next + N0, where N0 bounds the bytes out and
# the ok level of the rest of the list (EB at each emit, ob.of)
def OBn(+lim: U32, +nx: U32, +N0: Nat) -> Type:
  PN.Le(1n+Lim.bytes(lim), Nat.add(Nat.mul(20n, U32.to_nat(nx)), N0))

def OB(+b: Cr.Cir.State, +N0: Nat) -> Type:
  OBn(St.lim(b), St.nx(b), N0)

# Pr twice is at most the number
def pr2.le(+k: Nat) -> PN.Le(Pr(Pr(k)), k):
  match k:
    case 0n:
      PN.le_refl(0n)
    case 1n+(+p):
      match p:
        case 0n:
          PN.le_zero(1n)
        case 1n+(+q):
          PN.le_succ(q, 1n+q, PN.le_succ(q, q, PN.le_refl(q)))

# an emit at a Con of the ok level 1 + k, with outn + 1 + k <= N0: EB gives OB
def ob.of(+L: Nat, +A: Nat, +o: Nat, +k: Nat, +N0: Nat, e: PN.Le(L, Nat.add(A, o)), hn: PN.Le(Nat.add(o, 1n+k), N0)) -> PN.Le(1n+L, Nat.add(A, N0)):
  +h1 = PN.le_trans(1n+o, Nat.add(o, 1n+k), N0,
    PN.le_rw_r(1n+o, 1n+Nat.add(o, k), Nat.add(o, 1n+k), Equal.sym(Nat, Nat.add(o, 1n+k), 1n+Nat.add(o, k), PN.add_succ_r(o, k)), PN.le_add_r(o, k)), hn)
  PN.le_trans(1n+L, 1n+Nat.add(A, o), Nat.add(A, N0), e,
    PN.le_rw_l(Nat.add(A, 1n+o), 1n+Nat.add(A, o), Nat.add(A, N0), PN.add_succ_r(A, o), PN.add_mono(A, A, 1n+o, N0, PN.le_refl(A), h1)))

# after that emit, the invariant holds of the rest, at the level Pr(Pr(k))
def ob.step(+o: U32, +k: Nat, +N0: Nat, hn: PN.Le(Nat.add(U32.to_nat(o), 1n+k), N0)) -> PN.Le(Nat.add(U32.to_nat(U32.inc(o)), Pr(Pr(k))), N0):
  PN.le_trans(Nat.add(U32.to_nat(U32.inc(o)), Pr(Pr(k))), 1n+Nat.add(U32.to_nat(o), k), N0,
    PN.add_mono(U32.to_nat(U32.inc(o)), 1n+U32.to_nat(o), Pr(Pr(k)), k, PN.U32.inc_le(o), pr2.le(k)),
    PN.le_rw_l(Nat.add(U32.to_nat(o), 1n+k), 1n+Nat.add(U32.to_nat(o), k), N0, PN.add_succ_r(U32.to_nat(o), k), hn))

# the claim of the loop of M.out for the rest of the list, at any cell rc
# that ok grants, with the fuel f2
def LO.IH(+n1: Nat, +b: Cr.Cir.State, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +N0: Nat) -> Type:
  @rc: U32 -> {ok(Pr(Pr(n1)), St.cl(b), ks, img, rc, St.im(b), St.fs(b), St.nx(b)) == True{} : Bool} ->
    @f2: Nat -> PN.Le(Nat.add(Pr(Pr(n1)), 34n), f2) -> @pg2: U32 -> @ow2: U32 -> @ov2: U32 -> @oi2: U32 -> @t12: U32 -> @t22: U32 ->
    @out2: List<&2, Word(8n)> -> @outn2: U32 -> PN.Le(Nat.add(U32.to_nat(outn2), Pr(Pr(n1))), N0) ->
    Wp(Cr.Cir.exec(f2, WO(), ST(b, rc, ow2, ov2, oi2, t12, t22, pg2, out2, outn2)), st => Empty,
      s => st => Fin(CU(Pr(Pr(n1)), St.cl(b), Step(St.cl(b), rc)), out2, outn2, s, st), OB(b, N0))

# the round of a Con: its byte goes out (MCon), then the rest of the list
def LO.con(+n1: Nat, +g: Nat, +hF: PN.Le(Nat.add(n1, 34n), 1n+g), +b: Cr.Cir.State, +c: U32, +ow: U32, +ov: U32, +oi: U32, +t1: U32, +t2: U32,
  +pg: U32, +out: List<&2, Word(8n)>, +outn: U32, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +N0: Nat,
  +hok: {ok(1n+n1, St.cl(b), ks, img, c, St.im(b), St.fs(b), St.nx(b)) == True{} : Bool},
  +hn: PN.Le(Nat.add(U32.to_nat(outn), 1n+n1), N0),
  +hc: {True{} == Cr.Cir.is_cell(c, St.im(b), St.fs(b), St.nx(b)) : Bool},
  +eP: {Pm(St.cl(b), c) == True{} : Bool}, +eM: {Lm(St.cl(b), Fd(2n, St.cl(b), c)) == True{} : Bool},
  +eN: {U32.is_eq(Fd(2n, St.cl(b), Fd(2n, St.cl(b), c)), 1) == False{} : Bool},
  +eC: {U32.is_eq(Fd(2n, St.cl(b), Fd(2n, St.cl(b), c)), 2) == True{} : Bool},
  ih: LO.IH(n1, b, ks, img, N0)) ->
  Wp(Cr.Cir.exec(1n+g, Mc.M.out.con(), ST(b, c, ow, ov, oi, t1, t2, pg, out, outn)),
    t => Wp(Cr.Cir.exec(1n+g, Cr.Cir.Stmt.nop{}, t), u => Wp(Cr.Cir.exec(1n+g, WO(), u), st => Empty,
      s => st => Fin(CU(1n+n1, St.cl(b), Step(St.cl(b), c)), out, outn, s, st), OB(b, N0)),
      s => st => Fin(CU(1n+n1, St.cl(b), Step(St.cl(b), c)), out, outn, s, st), OB(b, N0)),
    s => st => Fin(CU(1n+n1, St.cl(b), Step(St.cl(b), c)), out, outn, s, st), OB(b, N0)):
  +m = St.cl(b)
  +im = St.im(b)
  +fs = St.fs(b)
  +nx = St.nx(b)
  +bc = Fd(3n, m, c)
  +estep = StC.ok(m, c, eP, eM, eN, eC)
  -K0 = {st => Empty : Cr.Cir.State -> Type}
  -H0 = {s => st => Fin(CU(1n+n1, m, Step(m, c)), out, outn, s, st) : U32 -> Cr.Cir.State -> Type}
  -KW = {t => Wp(Cr.Cir.exec(1n+g, WO(), t), K0, H0, OB(b, N0)) : Cr.Cir.State -> Type}
  -KB = {t => Wp(Cr.Cir.exec(1n+g, Cr.Cir.Stmt.nop{}, t), KW, H0, OB(b, N0)) : Cr.Cir.State -> Type}
  -IH = LO.IH(n1, b, ks, img, N0)
  MCon(g, PN.weaken(33n, 1n+g, PN.le_trans(34n, Nat.add(n1, 34n), 1n+g, PN.le_add_l(n1, 34n), hF)),
    b, c, ow, ov, oi, t1, t2, pg, out, outn, n1, ks, img, KB, H0, OB(b, N0), hc, ok.R(1n+n1, m, ks, img, c, im, fs, nx, hok, eP),
    e => ob.of(Lim.bytes(St.lim(b)), Nat.mul(20n, U32.to_nat(nx)), U32.to_nat(outn), n1, N0, e, hn),
    sr => +esr => CasesS(sr, IH, ih,
      v => rest => {ok(Pr(Pr(n1)), m, ks, img, rest, im, fs, nx) == True{} : Bool} ->
        @pg2: U32 -> @ow2: U32 -> @ov2: U32 -> @oi2: U32 -> @t12: U32 -> @t22: U32 -> KB(ST(b, rest, ow2, ov2, oi2, t12, t22, pg2, Con{v, out}, U32.inc(outn))),
      r => {r == None{} : Maybe<&2, List<&2, Word(8n)>>} -> @st: Cr.Cir.State -> H0(2, st),
      ih => +v => +rest => +emv => +hokr => +pg2 => +ow2 => +ov2 => +oi2 => +t12 => +t22 =>
        Wp.mapH(Cr.Cir.exec(1n+g, WO(), ST(b, rest, ow2, ov2, oi2, t12, t22, pg2, Con{v, out}, U32.inc(outn))), K0,
          s => st => Fin(CU(Pr(Pr(n1)), m, Step(m, rest)), Con{v, out}, U32.inc(outn), s, st), H0, OB(b, N0),
          s => st => hf => Fin.step(n1, m, c, v, rest, out, outn, ks, img, im, fs, nx,
            Equal.trans(SR, Step(m, c), sr, SR.more{v, rest}, Equal.trans(SR, Step(m, c), S.c0(Pm(m, bc), m, bc), sr, estep, esr), emv),
            hokr, s, st, hf),
          ih(rest, hokr, 1n+g, PN.le_trans(Nat.add(Pr(Pr(n1)), 34n), Nat.add(n1, 34n), 1n+g, le_pr2(n1), hF),
            pg2, ow2, ov2, oi2, t12, t22, Con{v, out}, U32.inc(outn), ob.step(outn, n1, N0, hn))),
      ih => +r => +ed => +er => st =>
        Fin.none(n1, m, c, out, outn, st,
          Equal.trans(SR, Step(m, c), sr, SR.done{None{}}, Equal.trans(SR, Step(m, c), S.c0(Pm(m, bc), m, bc), sr, estep, esr),
            Equal.trans(SR, sr, SR.done{r}, SR.done{None{}}, ed, Equal.cong(Maybe<&2, List<&2, Word(8n)>>, SR, x => SR.done{x}, r, None{}, er))))))

# a round of the loop of M.out at the list cell c, then, by ih, the rest
def LO.run(+n1: Nat, +g: Nat, +hF: PN.Le(Nat.add(n1, 34n), 1n+g), +b: Cr.Cir.State, +c: U32, +ow: U32, +ov: U32, +oi: U32, +t1: U32, +t2: U32,
  +pg: U32, +out: List<&2, Word(8n)>, +outn: U32, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +N0: Nat,
  +hok: {ok(1n+n1, St.cl(b), ks, img, c, St.im(b), St.fs(b), St.nx(b)) == True{} : Bool},
  +hn: PN.Le(Nat.add(U32.to_nat(outn), 1n+n1), N0),
  ih: LO.IH(n1, b, ks, img, N0)) ->
  Wp(Cr.Cir.exec(1n+1n+g, WO(), ST(b, c, ow, ov, oi, t1, t2, pg, out, outn)), st => Empty,
    s => st => Fin(CU(1n+n1, St.cl(b), Step(St.cl(b), c)), out, outn, s, st), OB(b, N0)):
  +m = St.cl(b)
  +im = St.im(b)
  +fs = St.fs(b)
  +nx = St.nx(b)
  +x22 = Fd(2n, m, Fd(2n, m, c))
  +s0 = ST(b, c, ow, ov, oi, t1, t2, pg, out, outn)
  +s1 = ST(b, c, x22, ov, oi, t1, t2, pg, out, outn)
  +hc = ok.isc(1n+n1, m, ks, img, c, im, fs, nx, hok)
  -K0 = {st => Empty : Cr.Cir.State -> Type}
  -H0 = {s => st => Fin(CU(1n+n1, m, Step(m, c)), out, outn, s, st) : U32 -> Cr.Cir.State -> Type}
  -KW = {t => Wp(Cr.Cir.exec(1n+g, WO(), t), K0, H0, OB(b, N0)) : Cr.Cir.State -> Type}
  -KB = {t => Wp(Cr.Cir.exec(1n+g, Cr.Cir.Stmt.nop{}, t), KW, H0, OB(b, N0)) : Cr.Cir.State -> Type}
  -IH = LO.IH(n1, b, ks, img, N0)
  Wp.while(1n+g, Mc.M.c(1), BO(), s0, K0, H0, OB(b, N0), True{}, {==},
    Wp.then(Cr.Cir.exec(1n+g, BO(), s0), t => Cr.Cir.exec(1n+g, WO(), t), K0, H0, OB(b, N0),
      Wp.need(g, Mc.M.pair(Mc.R.oc()), BO.s1(), s0, KW, H0, OB(b, N0), Pm(m, c), ev.pair(45n, s0, c, {==}, hc),
       CasesK(Pm(m, c), IH, ih, Wp(Cr.Cir.exec(1n+g, BO.s1(), s0), KW, H0, OB(b, N0)), H0(2, s0),
        ih => +eP =>
          Wp.need(g, Mc.M.eq(Mc.M.tag(Mc.M.f(2n, Mc.M.g(Mc.R.oc()))), Mc.M.c(Mc.T.lab())), Mc.M.do([BO.a(), BO.i()]), s0, KW, H0, OB(b, N0), Lm(m, Fd(2n, m, c)),
            ev.tag(2n, 45n, s0, c, {==}, hc, ok.isc(n1, m, ks, img, Fd(2n, m, c), im, fs, nx, ok.L(1n+n1, m, ks, img, c, im, fs, nx, hok, eP))),
           CasesK(Lm(m, Fd(2n, m, c)), IH, ih, Wp(Cr.Cir.exec(1n+g, Mc.M.do([BO.a(), BO.i()]), s0), KW, H0, OB(b, N0)), H0(2, s0),
            ih => +eM =>
              Wp.seq(g, BO.a(), Mc.M.do([BO.i()]), s0, KW, H0, OB(b, N0),
                Wp.set(g, 46n, Mc.M.f(2n, Mc.M.f(2n, Mc.M.g(Mc.R.oc()))), s0, t => Wp(Cr.Cir.exec(1n+g, Mc.M.do([BO.i()]), t), KW, H0, OB(b, N0)), H0, OB(b, N0), x22,
                  ev.ff(2n, 2n, 45n, s0, c, {==}, hc, ok.isc(n1, m, ks, img, Fd(2n, m, c), im, fs, nx, ok.L(1n+n1, m, ks, img, c, im, fs, nx, hok, eP))),
                  Wp.seq(g, BO.i(), Cr.Cir.Stmt.nop{}, s1, KW, H0, OB(b, N0),
                    Wp.if(g, Mc.M.eq(Mc.M.g(Mc.R.ow()), Mc.M.c(Mc.N.nil())), Mc.M.need(Mc.M.last(Mc.R.oc()), Mc.M.halt(0)),
                      Mc.M.need(Mc.M.eq(Mc.M.g(Mc.R.ow()), Mc.M.c(Mc.N.con())), Mc.M.out.con()), s1, KB, H0, OB(b, N0), U32.is_eq(x22, 1), {==},
                     CasesK(U32.is_eq(x22, 1), IH, ih, Wp(Cr.Cir.exec(1n+g, Mc.M.need(Mc.M.last(Mc.R.oc()), Mc.M.halt(0)), s1), KB, H0, OB(b, N0)),
                      Wp(Cr.Cir.exec(1n+g, Mc.M.need(Mc.M.eq(Mc.M.g(Mc.R.ow()), Mc.M.c(Mc.N.con())), Mc.M.out.con()), s1), KB, H0, OB(b, N0)),
                      ih => +eN =>
                        Wp.need(g, Mc.M.last(Mc.R.oc()), Mc.M.halt(0), s1, KB, H0, OB(b, N0), LAST(m, c),
                          ev.islab(3n, 45n, 0, s1, c, {==}, hc, ok.isc(n1, m, ks, img, Fd(3n, m, c), im, fs, nx, ok.R(1n+n1, m, ks, img, c, im, fs, nx, hok, eP))),
                         CasesK(LAST(m, c), IH, ih, Wp(Cr.Cir.exec(1n+g, Mc.M.halt(0), s1), KB, H0, OB(b, N0)), H0(2, s1),
                          ih => +eL =>
                            Fin.nil(n1, b, c, x22, ov, oi, t1, t2, pg, out, outn, StN.ok(m, c, eP, eM, eN, eL)),
                          ih => +eL =>
                            Fin.none(n1, m, c, out, outn, s1, StN.n4(m, c, eP, eM, eN, eL)))),
                      ih => +eN =>
                        Wp.need(g, Mc.M.eq(Mc.M.g(Mc.R.ow()), Mc.M.c(Mc.N.con())), Mc.M.out.con(), s1, KB, H0, OB(b, N0), U32.is_eq(x22, 2), {==},
                         CasesK(U32.is_eq(x22, 2), IH, ih, Wp(Cr.Cir.exec(1n+g, Mc.M.out.con(), s1), KB, H0, OB(b, N0)), H0(2, s1),
                          ih => +eC =>
                            LO.con(n1, g, hF, b, c, x22, ov, oi, t1, t2, pg, out, outn, ks, img, N0, hok, hn, hc, eP, eM, eN, eC, ih),
                          ih => +eC =>
                            Fin.none(n1, m, c, out, outn, s1, StC.n4(m, c, eP, eM, eN, eC))))))))),
            ih => +eM =>
              Fin.none(n1, m, c, out, outn, s0, StN.n2(m, c, eP, eM)))),
        ih => +eP =>
          Fin.none(n1, m, c, out, outn, s0, StN.n1(m, c, eP))))))

# the loop of M.out from the list cell c, with fuel F
def LO.body(+n1: Nat, +F: Nat, +hF: PN.Le(Nat.add(1n+n1, 34n), F), +b: Cr.Cir.State, +c: U32, +ow: U32, +ov: U32, +oi: U32, +t1: U32, +t2: U32,
  +pg: U32, +out: List<&2, Word(8n)>, +outn: U32, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +N0: Nat,
  +hok: {ok(1n+n1, St.cl(b), ks, img, c, St.im(b), St.fs(b), St.nx(b)) == True{} : Bool},
  +hn: PN.Le(Nat.add(U32.to_nat(outn), 1n+n1), N0),
  ih: LO.IH(n1, b, ks, img, N0)) ->
  Wp(Cr.Cir.exec(F, WO(), ST(b, c, ow, ov, oi, t1, t2, pg, out, outn)), st => Empty, s => st => Fin(CU(1n+n1, St.cl(b), Step(St.cl(b), c)), out, outn, s, st), OB(b, N0)):
  match F:
    case 0n:
      Empty.absurd(Wp(Cr.Cir.exec(0n, WO(), ST(b, c, ow, ov, oi, t1, t2, pg, out, outn)), st => Empty, s => st => Fin(CU(1n+n1, St.cl(b), Step(St.cl(b), c)), out, outn, s, st), OB(b, N0)), hF)
    case 1n+f:
      match f:
        case 0n:
          Empty.absurd(Wp(Cr.Cir.exec(1n, WO(), ST(b, c, ow, ov, oi, t1, t2, pg, out, outn)), st => Empty, s => st => Fin(CU(1n+n1, St.cl(b), Step(St.cl(b), c)), out, outn, s, st), OB(b, N0)), PN.le_trans(34n, Nat.add(n1, 34n), 0n, PN.le_add_l(n1, 34n), hF))
        case 1n+g:
          LO.run(n1, g, hF, b, c, ow, ov, oi, t1, t2, pg, out, outn, ks, img, N0, hok, hn, ih)

# the loop of M.out from the list cell c: the run halts as CU says, or runs
# out of memory
def LO(+n: Nat, +F: Nat, +hF: PN.Le(Nat.add(n, 34n), F), +b: Cr.Cir.State, +c: U32, +ow: U32, +ov: U32, +oi: U32, +t1: U32, +t2: U32,
  +pg: U32, +out: List<&2, Word(8n)>, +outn: U32, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +N0: Nat,
  +hok: {ok(n, St.cl(b), ks, img, c, St.im(b), St.fs(b), St.nx(b)) == True{} : Bool},
  +hn: PN.Le(Nat.add(U32.to_nat(outn), n), N0)) ->
  Wp(Cr.Cir.exec(F, WO(), ST(b, c, ow, ov, oi, t1, t2, pg, out, outn)), st => Empty, s => st => Fin(CU(n, St.cl(b), Step(St.cl(b), c)), out, outn, s, st), OB(b, N0)):
  match n:
    case 0n:
      Empty.absurd(Wp(Cr.Cir.exec(F, WO(), ST(b, c, ow, ov, oi, t1, t2, pg, out, outn)), st => Empty, s => st => Fin(CU(0n, St.cl(b), Step(St.cl(b), c)), out, outn, s, st), OB(b, N0)), ok.zero(St.cl(b), ks, img, c, St.im(b), St.fs(b), St.nx(b), hok))
    case 1n+n1:
      match n1:
        case 0n:
          LO.body(0n, F, hF, b, c, ow, ov, oi, t1, t2, pg, out, outn, ks, img, N0, hok, hn,
            rc => +hokr => +f2 => +hF2 => +pg2 => +ow2 => +ov2 => +oi2 => +t12 => +t22 => +out2 => +outn2 => +hnr =>
            Empty.absurd(Wp(Cr.Cir.exec(f2, WO(), ST(b, rc, ow2, ov2, oi2, t12, t22, pg2, out2, outn2)), st => Empty,
              s => st => Fin(CU(0n, St.cl(b), Step(St.cl(b), rc)), out2, outn2, s, st), OB(b, N0)), ok.zero(St.cl(b), ks, img, rc, St.im(b), St.fs(b), St.nx(b), hokr)))
        case 1n+n2:
          match n2:
            case 0n:
              LO.body(1n, F, hF, b, c, ow, ov, oi, t1, t2, pg, out, outn, ks, img, N0, hok, hn,
                rc => +hokr => +f2 => +hF2 => +pg2 => +ow2 => +ov2 => +oi2 => +t12 => +t22 => +out2 => +outn2 => +hnr =>
            Empty.absurd(Wp(Cr.Cir.exec(f2, WO(), ST(b, rc, ow2, ov2, oi2, t12, t22, pg2, out2, outn2)), st => Empty,
              s => st => Fin(CU(0n, St.cl(b), Step(St.cl(b), rc)), out2, outn2, s, st), OB(b, N0)), ok.zero(St.cl(b), ks, img, rc, St.im(b), St.fs(b), St.nx(b), hokr)))
            case 1n+n3:
              LO.body(1n+1n+n3, F, hF, b, c, ow, ov, oi, t1, t2, pg, out, outn, ks, img, N0, hok, hn,
                rc => +hokr => +f2 => +hF2 => +pg2 => +ow2 => +ov2 => +oi2 => +t12 => +t22 => +out2 => +outn2 => +hnr =>
                  LO(n3, f2, hF2, b, rc, ow2, ov2, oi2, t12, t22, pg2, out2, outn2, ks, img, N0, hokr, hnr))

# The run of M.out
# ----------------

# register k of xs
def At(+k: Nat, +xs: List<&2, U32>) -> U32:
  Rg.hd(Rg.drop(k, xs))

# M.out from a state whose focus register holds the cell c, with fuel 1 + f
# of n + 34 or more: the run halts as CU says of the list of c, or runs out
# of memory
def MOUT(+n: Nat, +f: Nat, +hF: PN.Le(Nat.add(n, 34n), 1n+f), +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fs: U32, +im: U32,
  +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +out: List<&2, Word(8n)>, +outn: U32, +c: U32, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +N0: Nat,
  +hreg: {List.get(&2, U32, regs, Mc.R.focus()) == Some{c} : Maybe<&2, U32>},
  +hlen: {Nat.is_le(Mc.Mach.regs(), List.length(&2, U32, regs)) == True{} : Bool},
  +hok: {ok(n, m, ks, img, c, im, fs, nx) == True{} : Bool}, +hn: PN.Le(Nat.add(U32.to_nat(outn), n), N0)) ->
  Wp(Cr.Cir.exec(1n+f, Mc.M.out(), Cr.Cir.State{regs, m, nx, fs, im, pg, lim, inp, out, outn}), st => Empty,
    s => st => Fin(CU(n, m, Step(m, c)), out, outn, s, st), OB(Cr.Cir.State{regs, m, nx, fs, im, pg, lim, inp, out, outn}, N0)):
  +b = {Cr.Cir.State{regs, m, nx, fs, im, pg, lim, inp, out, outn} : Cr.Cir.State}
  +esp = Rg.sp_eq(63n, regs, PN.toLe(63n, List.length(&2, U32, regs), hlen))
  +ec = Equal.cong(Maybe<&2, U32>, U32, x => Maybe.default(&2, U32, x, 0), Some{Rg.hd(regs)}, Some{c},
    Equal.trans(Maybe<&2, U32>, Some{Rg.hd(regs)}, List.get(&2, U32, regs, 0n), Some{c},
      Equal.cong(List<&2, U32>, Maybe<&2, U32>, xs => List.get(&2, U32, xs, 0n), Rg.sp(regs), regs, esp), hreg))
  -K0 = {st => Empty : Cr.Cir.State -> Type}
  -H0 = {s => st => Fin(CU(n, m, Step(m, Rg.hd(regs))), out, outn, s, st) : U32 -> Cr.Cir.State -> Type}
  %ec : Wp(Cr.Cir.exec(1n+f, Mc.M.out(), b), st => Empty, s => st => Fin(CU(n, m, Step(m, _)), out, outn, s, st), OB(b, N0))
  %esp : Wp(Cr.Cir.exec(1n+f, Mc.M.out(), Cr.Cir.State{_, m, nx, fs, im, pg, lim, inp, out, outn}), K0, H0, OB(b, N0))
  Wp.seq(f, Mc.M.set(Mc.R.oc(), Mc.M.g(Mc.R.focus())), Mc.M.do([WO()]), Cr.Cir.State{Rg.sp(regs), m, nx, fs, im, pg, lim, inp, out, outn}, K0, H0, OB(b, N0),
    Wp.set(f, 45n, Mc.M.g(Mc.R.focus()), Cr.Cir.State{Rg.sp(regs), m, nx, fs, im, pg, lim, inp, out, outn},
      t => Wp(Cr.Cir.exec(1n+f, Mc.M.do([WO()]), t), K0, H0, OB(b, N0)), H0, OB(b, N0), Rg.hd(regs), {==},
      Wp.seq(f, WO(), Cr.Cir.Stmt.nop{}, ST(b, Rg.hd(regs), At(46n, regs), At(47n, regs), At(48n, regs), At(61n, regs), At(62n, regs), pg, out, outn), K0, H0, OB(b, N0),
        LO(n, 1n+f, hF, b, Rg.hd(regs), At(46n, regs), At(47n, regs), At(48n, regs), At(61n, regs), At(62n, regs),
          pg, out, outn, ks, img, N0,
          Tr(U32, x => {ok(n, m, ks, img, x, im, fs, nx) == True{} : Bool}, c, Rg.hd(regs), Equal.sym(U32, Rg.hd(regs), c, ec), hok), hn))))

# U reads what Program.unbytes reads, for every term
def UE(+t: Bk.Term) -> {Pg.Program.unbytes(t) == U(t) : Maybe<&2, List<&2, Word(8n)>>}:
  match t:
    case Bk.Term.Var{_}:
      {==}
    case Bk.Term.Ref{_}:
      {==}
    case Bk.Term.Ann{_, _}:
      {==}
    case Bk.Term.Let{_, _, _}:
      {==}
    case Bk.Term.Typ{_}:
      {==}
    case Bk.Term.Min{_, _}:
      {==}
    case Bk.Term.All{_, _, _}:
      {==}
    case Bk.Term.Lam{_, _}:
      {==}
    case Bk.Term.App{_, _, _}:
      {==}
    case Bk.Term.Sig{_, _, _}:
      {==}
    case Bk.Term.Tup{+q, +a, +b}:
      match q:
        case Bk.Quan.Q0{}:
          {==}
        case Bk.Quan.Q1{}:
          match a:
            case Bk.Term.Var{_}:
              {==}
            case Bk.Term.Ref{_}:
              {==}
            case Bk.Term.Ann{_, _}:
              {==}
            case Bk.Term.Let{_, _, _}:
              {==}
            case Bk.Term.Typ{_}:
              {==}
            case Bk.Term.Min{_, _}:
              {==}
            case Bk.Term.All{_, _, _}:
              {==}
            case Bk.Term.Lam{_, _}:
              {==}
            case Bk.Term.App{_, _, _}:
              {==}
            case Bk.Term.Sig{_, _, _}:
              {==}
            case Bk.Term.Tup{_, _, _}:
              {==}
            case Bk.Term.Prj{_}:
              {==}
            case Bk.Term.Enu{_}:
              {==}
            case Bk.Term.Lab{+k}:
              match b:
                case Bk.Term.Var{_}:
                  Uk_none(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b, {==}, {==})
                case Bk.Term.Ref{_}:
                  Uk_none(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b, {==}, {==})
                case Bk.Term.Ann{_, _}:
                  Uk_none(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b, {==}, {==})
                case Bk.Term.Let{_, _, _}:
                  Uk_none(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b, {==}, {==})
                case Bk.Term.Typ{_}:
                  Uk_none(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b, {==}, {==})
                case Bk.Term.Min{_, _}:
                  Uk_none(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b, {==}, {==})
                case Bk.Term.All{_, _, _}:
                  Uk_none(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b, {==}, {==})
                case Bk.Term.Lam{_, _}:
                  Uk_none(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b, {==}, {==})
                case Bk.Term.App{_, _, _}:
                  Uk_none(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b, {==}, {==})
                case Bk.Term.Sig{_, _, _}:
                  Uk_none(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b, {==}, {==})
                case Bk.Term.Tup{+q2, +x, +y}:
                  match q2:
                    case Bk.Quan.Q0{}:
                      Uk_none(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b, {==}, {==})
                    case Bk.Quan.Q1{}:
                      match y:
                        case Bk.Term.Var{_}:
                          Uk_none(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b, {==}, {==})
                        case Bk.Term.Ref{_}:
                          Uk_none(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b, {==}, {==})
                        case Bk.Term.Ann{_, _}:
                          Uk_none(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b, {==}, {==})
                        case Bk.Term.Let{_, _, _}:
                          Uk_none(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b, {==}, {==})
                        case Bk.Term.Typ{_}:
                          Uk_none(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b, {==}, {==})
                        case Bk.Term.Min{_, _}:
                          Uk_none(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b, {==}, {==})
                        case Bk.Term.All{_, _, _}:
                          Uk_none(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b, {==}, {==})
                        case Bk.Term.Lam{_, _}:
                          Uk_none(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b, {==}, {==})
                        case Bk.Term.App{_, _, _}:
                          Uk_none(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b, {==}, {==})
                        case Bk.Term.Sig{_, _, _}:
                          Uk_none(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b, {==}, {==})
                        case Bk.Term.Tup{+q3, +rest, +z}:
                          match q3:
                            case Bk.Quan.Q0{}:
                              Uk_none(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b, {==}, {==})
                            case Bk.Quan.Q1{}:
                              match z:
                                case Bk.Term.Var{_}:
                                  Uk_none(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b, {==}, {==})
                                case Bk.Term.Ref{_}:
                                  Uk_none(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b, {==}, {==})
                                case Bk.Term.Ann{_, _}:
                                  Uk_none(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b, {==}, {==})
                                case Bk.Term.Let{_, _, _}:
                                  Uk_none(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b, {==}, {==})
                                case Bk.Term.Typ{_}:
                                  Uk_none(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b, {==}, {==})
                                case Bk.Term.Min{_, _}:
                                  Uk_none(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b, {==}, {==})
                                case Bk.Term.All{_, _, _}:
                                  Uk_none(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b, {==}, {==})
                                case Bk.Term.Lam{_, _}:
                                  Uk_none(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b, {==}, {==})
                                case Bk.Term.App{_, _, _}:
                                  Uk_none(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b, {==}, {==})
                                case Bk.Term.Sig{_, _, _}:
                                  Uk_none(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b, {==}, {==})
                                case Bk.Term.Tup{_, _, _}:
                                  Uk_none(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b, {==}, {==})
                                case Bk.Term.Prj{_}:
                                  Uk_none(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b, {==}, {==})
                                case Bk.Term.Enu{_}:
                                  Uk_none(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b, {==}, {==})
                                case Bk.Term.Lab{+u}:
                                  LF(k, x, rest, u)
                                case Bk.Term.Mat{_, _, _}:
                                  Uk_none(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b, {==}, {==})
                                case Bk.Term.Efq{}:
                                  Uk_none(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b, {==}, {==})
                                case Bk.Term.Eql{_, _, _}:
                                  Uk_none(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b, {==}, {==})
                                case Bk.Term.Rfl{}:
                                  Uk_none(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b, {==}, {==})
                                case Bk.Term.Rwt{_, _, _}:
                                  Uk_none(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b, {==}, {==})
                            case Bk.Quan.Q2{}:
                              Uk_none(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b, {==}, {==})
                        case Bk.Term.Prj{_}:
                          Uk_none(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b, {==}, {==})
                        case Bk.Term.Enu{_}:
                          Uk_none(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b, {==}, {==})
                        case Bk.Term.Lab{_}:
                          Uk_none(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b, {==}, {==})
                        case Bk.Term.Mat{_, _, _}:
                          Uk_none(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b, {==}, {==})
                        case Bk.Term.Efq{}:
                          Uk_none(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b, {==}, {==})
                        case Bk.Term.Eql{_, _, _}:
                          Uk_none(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b, {==}, {==})
                        case Bk.Term.Rfl{}:
                          Uk_none(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b, {==}, {==})
                        case Bk.Term.Rwt{_, _, _}:
                          Uk_none(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b, {==}, {==})
                    case Bk.Quan.Q2{}:
                      Uk_none(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b, {==}, {==})
                case Bk.Term.Prj{_}:
                  Uk_none(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b, {==}, {==})
                case Bk.Term.Enu{_}:
                  Uk_none(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b, {==}, {==})
                case Bk.Term.Lab{+u}:
                  LN(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), u)
                case Bk.Term.Mat{_, _, _}:
                  Uk_none(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b, {==}, {==})
                case Bk.Term.Efq{}:
                  Uk_none(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b, {==}, {==})
                case Bk.Term.Eql{_, _, _}:
                  Uk_none(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b, {==}, {==})
                case Bk.Term.Rfl{}:
                  Uk_none(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b, {==}, {==})
                case Bk.Term.Rwt{_, _, _}:
                  Uk_none(Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(k, Pg.Program.name.con()), b, {==}, {==})
            case Bk.Term.Mat{_, _, _}:
              {==}
            case Bk.Term.Efq{}:
              {==}
            case Bk.Term.Eql{_, _, _}:
              {==}
            case Bk.Term.Rfl{}:
              {==}
            case Bk.Term.Rwt{_, _, _}:
              {==}
        case Bk.Quan.Q2{}:
          {==}
    case Bk.Term.Prj{_}:
      {==}
    case Bk.Term.Enu{_}:
      {==}
    case Bk.Term.Lab{_}:
      {==}
    case Bk.Term.Mat{_, _, _}:
      {==}
    case Bk.Term.Efq{}:
      {==}
    case Bk.Term.Eql{_, _, _}:
      {==}
    case Bk.Term.Rfl{}:
      {==}
    case Bk.Term.Rwt{_, _, _}:
      {==}

# Wd reads what Program.unword reads, for every term
def W0N(A: Bool, +u: List<&2, Word(8n)>) ->
  {Pg.Program.unword.nil(Bool.and(A, Sd.Name.is_eq(u, Pg.Program.name.unit()))) == W0.k(A, Bk.Term.Lab{u}) : Maybe<&2, Word(0n)>}:
  match A:
    case True{}:
      {==}
    case False{}:
      {==}

def W0K_none(A: Bool, -z: Bk.Term, +h: {None{} == W0.z(VL(z)) : Maybe<&2, Word(0n)>}) -> {None{} == W0.k(A, z) : Maybe<&2, Word(0n)>}:
  match A:
    case True{}:
      h
    case False{}:
      {==}

def W1K_none(+q: Nat, A: Bool, -f: Bk.Term, +h: {None{} == W1.f(q, V1(f)) : Maybe<&2, Word(1n+q)>}) -> {None{} == W1.k(q, A, f) : Maybe<&2, Word(1n+q)>}:
  match A:
    case True{}:
      h
    case False{}:
      {==}

def W1BU_none(+q: Nat, B: Bool, -x: Bk.Term, -r: Bk.Term, +h: {None{} == Ub.x(VL(x)) : Maybe<&2, Bool>}) ->
  {None{} == W1.b(q, Ub.u(B, x), r) : Maybe<&2, Word(1n+q)>}:
  match B:
    case True{}:
      Equal.cong(Maybe<&2, Bool>, Maybe<&2, Word(1n+q)>, mb => W1.b(q, mb, r), None{}, Ub.x(VL(x)), h)
    case False{}:
      {==}

def W1BY_none(+q: Nat, my: Maybe<&2, List<&2, Word(8n)>>, -x: Bk.Term, -r: Bk.Term,
  h: @u: List<&2, Word(8n)> -> {None{} == W1.b(q, Ub.u(Sd.Name.is_eq(u, Pg.Program.name.unit()), x), r) : Maybe<&2, Word(1n+q)>}) ->
  {None{} == W1.b(q, Ub.y(my, x), r) : Maybe<&2, Word(1n+q)>}:
  match my:
    case Some{u}:
      h(u)
    case None{}:
      {==}

def W1B_none(+q: Nat, mb: Maybe<&2, Bool>, -r: Bk.Term, h: @bb: Bool -> {None{} == W1.r2(q, bb, V1(r)) : Maybe<&2, Word(1n+q)>}) ->
  {None{} == W1.b(q, mb, r) : Maybe<&2, Word(1n+q)>}:
  match mb:
    case Some{bb}:
      h(bb)
    case None{}:
      {==}

def LW.W(+q: Nat, bb: Bool, mw: Maybe<&2, Word(q)>) -> {Pg.Program.unword.con(q, True{}, Some{bb}, mw) == W1.w(q, bb, mw) : Maybe<&2, Word(1n+q)>}:
  match mw:
    case Some{y}:
      {==}
    case None{}:
      {==}

def LW.C(C: Bool, +q: Nat, bb: Bool, +w: Bk.Term) ->
  {Pg.Program.unword.con(q, C, Some{bb}, Pg.Program.unword(q, w)) == W1.u(q, bb, C, w) : Maybe<&2, Word(1n+q)>}:
  match C:
    case True{}:
      LW.W(q, bb, Pg.Program.unword(q, w))
    case False{}:
      {==}

def LW.N(C: Bool, +q: Nat, mw: Maybe<&2, Word(q)>) -> {Pg.Program.unword.con(q, C, None{}, mw) == None{} : Maybe<&2, Word(1n+q)>}:
  match C:
    case True{}:
      {==}
    case False{}:
      {==}

def LW.M(mb: Maybe<&2, Bool>, +q: Nat, +w: Bk.Term, +u2: List<&2, Word(8n)>) ->
  {Pg.Program.unword.con(q, Sd.Name.is_eq(u2, Pg.Program.name.unit()), mb, Pg.Program.unword(q, w)) ==
   W1.b(q, mb, Bk.Term.Tup{Bk.Quan.Q1{}, w, Bk.Term.Lab{u2}}) : Maybe<&2, Word(1n+q)>}:
  match mb:
    case None{}:
      LW.N(Sd.Name.is_eq(u2, Pg.Program.name.unit()), q, Pg.Program.unword(q, w))
    case Some{bb}:
      LW.C(Sd.Name.is_eq(u2, Pg.Program.name.unit()), q, bb, w)

def LW.B(B: Bool, +q: Nat, +bn: List<&2, Word(8n)>, +w: Bk.Term, +u2: List<&2, Word(8n)>) ->
  {Pg.Program.unword.con(q, Bool.and(B, Sd.Name.is_eq(u2, Pg.Program.name.unit())), Pg.Program.unbit(bn), Pg.Program.unword(q, w)) ==
   W1.b(q, Ub.u(B, Bk.Term.Lab{bn}), Bk.Term.Tup{Bk.Quan.Q1{}, w, Bk.Term.Lab{u2}}) : Maybe<&2, Word(1n+q)>}:
  match B:
    case True{}:
      LW.M(Pg.Program.unbit(bn), q, w, u2)
    case False{}:
      {==}

def LW.A(A: Bool, +q: Nat, +bn: List<&2, Word(8n)>, +u1: List<&2, Word(8n)>, +w: Bk.Term, +u2: List<&2, Word(8n)>) ->
  {Pg.Program.unword.con(q, Bool.and(Bool.and(A, Sd.Name.is_eq(u1, Pg.Program.name.unit())), Sd.Name.is_eq(u2, Pg.Program.name.unit())),
     Pg.Program.unbit(bn), Pg.Program.unword(q, w)) ==
   W1.k(q, A, Bk.Term.Tup{Bk.Quan.Q1{}, Bk.Term.Tup{Bk.Quan.Q1{}, Bk.Term.Lab{bn}, Bk.Term.Lab{u1}}, Bk.Term.Tup{Bk.Quan.Q1{}, w, Bk.Term.Lab{u2}}}) : Maybe<&2, Word(1n+q)>}:
  match A:
    case True{}:
      LW.B(Sd.Name.is_eq(u1, Pg.Program.name.unit()), q, bn, w, u2)
    case False{}:
      {==}

def WE0(+t: Bk.Term) -> {Pg.Program.unword(0n, t) == Wd(0n, t) : Maybe<&2, Word(0n)>}:
  match t:
    case Bk.Term.Var{_}:
      {==}
    case Bk.Term.Ref{_}:
      {==}
    case Bk.Term.Ann{_, _}:
      {==}
    case Bk.Term.Let{_, _, _}:
      {==}
    case Bk.Term.Typ{_}:
      {==}
    case Bk.Term.Min{_, _}:
      {==}
    case Bk.Term.All{_, _, _}:
      {==}
    case Bk.Term.Lam{_, _}:
      {==}
    case Bk.Term.App{_, _, _}:
      {==}
    case Bk.Term.Sig{_, _, _}:
      {==}
    case Bk.Term.Tup{+q, +a, +b}:
      match q:
        case Bk.Quan.Q0{}:
          {==}
        case Bk.Quan.Q1{}:
          match a:
            case Bk.Term.Var{_}:
              {==}
            case Bk.Term.Ref{_}:
              {==}
            case Bk.Term.Ann{_, _}:
              {==}
            case Bk.Term.Let{_, _, _}:
              {==}
            case Bk.Term.Typ{_}:
              {==}
            case Bk.Term.Min{_, _}:
              {==}
            case Bk.Term.All{_, _, _}:
              {==}
            case Bk.Term.Lam{_, _}:
              {==}
            case Bk.Term.App{_, _, _}:
              {==}
            case Bk.Term.Sig{_, _, _}:
              {==}
            case Bk.Term.Tup{_, _, _}:
              {==}
            case Bk.Term.Prj{_}:
              {==}
            case Bk.Term.Enu{_}:
              {==}
            case Bk.Term.Lab{+k}:
              match b:
                case Bk.Term.Var{_}:
                  W0K_none(Sd.Name.is_eq(k, Pg.Program.name.wnil()), b, {==})
                case Bk.Term.Ref{_}:
                  W0K_none(Sd.Name.is_eq(k, Pg.Program.name.wnil()), b, {==})
                case Bk.Term.Ann{_, _}:
                  W0K_none(Sd.Name.is_eq(k, Pg.Program.name.wnil()), b, {==})
                case Bk.Term.Let{_, _, _}:
                  W0K_none(Sd.Name.is_eq(k, Pg.Program.name.wnil()), b, {==})
                case Bk.Term.Typ{_}:
                  W0K_none(Sd.Name.is_eq(k, Pg.Program.name.wnil()), b, {==})
                case Bk.Term.Min{_, _}:
                  W0K_none(Sd.Name.is_eq(k, Pg.Program.name.wnil()), b, {==})
                case Bk.Term.All{_, _, _}:
                  W0K_none(Sd.Name.is_eq(k, Pg.Program.name.wnil()), b, {==})
                case Bk.Term.Lam{_, _}:
                  W0K_none(Sd.Name.is_eq(k, Pg.Program.name.wnil()), b, {==})
                case Bk.Term.App{_, _, _}:
                  W0K_none(Sd.Name.is_eq(k, Pg.Program.name.wnil()), b, {==})
                case Bk.Term.Sig{_, _, _}:
                  W0K_none(Sd.Name.is_eq(k, Pg.Program.name.wnil()), b, {==})
                case Bk.Term.Tup{_, _, _}:
                  W0K_none(Sd.Name.is_eq(k, Pg.Program.name.wnil()), b, {==})
                case Bk.Term.Prj{_}:
                  W0K_none(Sd.Name.is_eq(k, Pg.Program.name.wnil()), b, {==})
                case Bk.Term.Enu{_}:
                  W0K_none(Sd.Name.is_eq(k, Pg.Program.name.wnil()), b, {==})
                case Bk.Term.Lab{+u}:
                  W0N(Sd.Name.is_eq(k, Pg.Program.name.wnil()), u)
                case Bk.Term.Mat{_, _, _}:
                  W0K_none(Sd.Name.is_eq(k, Pg.Program.name.wnil()), b, {==})
                case Bk.Term.Efq{}:
                  W0K_none(Sd.Name.is_eq(k, Pg.Program.name.wnil()), b, {==})
                case Bk.Term.Eql{_, _, _}:
                  W0K_none(Sd.Name.is_eq(k, Pg.Program.name.wnil()), b, {==})
                case Bk.Term.Rfl{}:
                  W0K_none(Sd.Name.is_eq(k, Pg.Program.name.wnil()), b, {==})
                case Bk.Term.Rwt{_, _, _}:
                  W0K_none(Sd.Name.is_eq(k, Pg.Program.name.wnil()), b, {==})
            case Bk.Term.Mat{_, _, _}:
              {==}
            case Bk.Term.Efq{}:
              {==}
            case Bk.Term.Eql{_, _, _}:
              {==}
            case Bk.Term.Rfl{}:
              {==}
            case Bk.Term.Rwt{_, _, _}:
              {==}
        case Bk.Quan.Q2{}:
          {==}
    case Bk.Term.Prj{_}:
      {==}
    case Bk.Term.Enu{_}:
      {==}
    case Bk.Term.Lab{_}:
      {==}
    case Bk.Term.Mat{_, _, _}:
      {==}
    case Bk.Term.Efq{}:
      {==}
    case Bk.Term.Eql{_, _, _}:
      {==}
    case Bk.Term.Rfl{}:
      {==}
    case Bk.Term.Rwt{_, _, _}:
      {==}

def WE1(+q: Nat, +t: Bk.Term) -> {Pg.Program.unword(1n+q, t) == Wd(1n+q, t) : Maybe<&2, Word(1n+q)>}:
  match t:
    case Bk.Term.Var{_}:
      {==}
    case Bk.Term.Ref{_}:
      {==}
    case Bk.Term.Ann{_, _}:
      {==}
    case Bk.Term.Let{_, _, _}:
      {==}
    case Bk.Term.Typ{_}:
      {==}
    case Bk.Term.Min{_, _}:
      {==}
    case Bk.Term.All{_, _, _}:
      {==}
    case Bk.Term.Lam{_, _}:
      {==}
    case Bk.Term.App{_, _, _}:
      {==}
    case Bk.Term.Sig{_, _, _}:
      {==}
    case Bk.Term.Tup{+qq, +a, +f}:
      match qq:
        case Bk.Quan.Q0{}:
          {==}
        case Bk.Quan.Q1{}:
          match a:
            case Bk.Term.Var{_}:
              {==}
            case Bk.Term.Ref{_}:
              {==}
            case Bk.Term.Ann{_, _}:
              {==}
            case Bk.Term.Let{_, _, _}:
              {==}
            case Bk.Term.Typ{_}:
              {==}
            case Bk.Term.Min{_, _}:
              {==}
            case Bk.Term.All{_, _, _}:
              {==}
            case Bk.Term.Lam{_, _}:
              {==}
            case Bk.Term.App{_, _, _}:
              {==}
            case Bk.Term.Sig{_, _, _}:
              {==}
            case Bk.Term.Tup{_, _, _}:
              {==}
            case Bk.Term.Prj{_}:
              {==}
            case Bk.Term.Enu{_}:
              {==}
            case Bk.Term.Lab{+k}:
              match f:
                case Bk.Term.Var{_}:
                  W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
                case Bk.Term.Ref{_}:
                  W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
                case Bk.Term.Ann{_, _}:
                  W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
                case Bk.Term.Let{_, _, _}:
                  W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
                case Bk.Term.Typ{_}:
                  W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
                case Bk.Term.Min{_, _}:
                  W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
                case Bk.Term.All{_, _, _}:
                  W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
                case Bk.Term.Lam{_, _}:
                  W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
                case Bk.Term.App{_, _, _}:
                  W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
                case Bk.Term.Sig{_, _, _}:
                  W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
                case Bk.Term.Tup{+q2, +bt, +r}:
                  match q2:
                    case Bk.Quan.Q0{}:
                      W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
                    case Bk.Quan.Q1{}:
                      match bt:
                        case Bk.Term.Var{_}:
                          W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
                        case Bk.Term.Ref{_}:
                          W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
                        case Bk.Term.Ann{_, _}:
                          W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
                        case Bk.Term.Let{_, _, _}:
                          W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
                        case Bk.Term.Typ{_}:
                          W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
                        case Bk.Term.Min{_, _}:
                          W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
                        case Bk.Term.All{_, _, _}:
                          W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
                        case Bk.Term.Lam{_, _}:
                          W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
                        case Bk.Term.App{_, _, _}:
                          W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
                        case Bk.Term.Sig{_, _, _}:
                          W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
                        case Bk.Term.Tup{+q3, +x, +y}:
                          match q3:
                            case Bk.Quan.Q0{}:
                              W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
                            case Bk.Quan.Q1{}:
                              match x:
                                case Bk.Term.Var{_}:
                                  W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, W1BY_none(q, VL(y), x, r, u => W1BU_none(q, Sd.Name.is_eq(u, Pg.Program.name.unit()), x, r, {==})))
                                case Bk.Term.Ref{_}:
                                  W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, W1BY_none(q, VL(y), x, r, u => W1BU_none(q, Sd.Name.is_eq(u, Pg.Program.name.unit()), x, r, {==})))
                                case Bk.Term.Ann{_, _}:
                                  W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, W1BY_none(q, VL(y), x, r, u => W1BU_none(q, Sd.Name.is_eq(u, Pg.Program.name.unit()), x, r, {==})))
                                case Bk.Term.Let{_, _, _}:
                                  W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, W1BY_none(q, VL(y), x, r, u => W1BU_none(q, Sd.Name.is_eq(u, Pg.Program.name.unit()), x, r, {==})))
                                case Bk.Term.Typ{_}:
                                  W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, W1BY_none(q, VL(y), x, r, u => W1BU_none(q, Sd.Name.is_eq(u, Pg.Program.name.unit()), x, r, {==})))
                                case Bk.Term.Min{_, _}:
                                  W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, W1BY_none(q, VL(y), x, r, u => W1BU_none(q, Sd.Name.is_eq(u, Pg.Program.name.unit()), x, r, {==})))
                                case Bk.Term.All{_, _, _}:
                                  W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, W1BY_none(q, VL(y), x, r, u => W1BU_none(q, Sd.Name.is_eq(u, Pg.Program.name.unit()), x, r, {==})))
                                case Bk.Term.Lam{_, _}:
                                  W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, W1BY_none(q, VL(y), x, r, u => W1BU_none(q, Sd.Name.is_eq(u, Pg.Program.name.unit()), x, r, {==})))
                                case Bk.Term.App{_, _, _}:
                                  W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, W1BY_none(q, VL(y), x, r, u => W1BU_none(q, Sd.Name.is_eq(u, Pg.Program.name.unit()), x, r, {==})))
                                case Bk.Term.Sig{_, _, _}:
                                  W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, W1BY_none(q, VL(y), x, r, u => W1BU_none(q, Sd.Name.is_eq(u, Pg.Program.name.unit()), x, r, {==})))
                                case Bk.Term.Tup{_, _, _}:
                                  W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, W1BY_none(q, VL(y), x, r, u => W1BU_none(q, Sd.Name.is_eq(u, Pg.Program.name.unit()), x, r, {==})))
                                case Bk.Term.Prj{_}:
                                  W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, W1BY_none(q, VL(y), x, r, u => W1BU_none(q, Sd.Name.is_eq(u, Pg.Program.name.unit()), x, r, {==})))
                                case Bk.Term.Enu{_}:
                                  W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, W1BY_none(q, VL(y), x, r, u => W1BU_none(q, Sd.Name.is_eq(u, Pg.Program.name.unit()), x, r, {==})))
                                case Bk.Term.Lab{+bn}:
                                  match y:
                                    case Bk.Term.Var{_}:
                                      W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
                                    case Bk.Term.Ref{_}:
                                      W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
                                    case Bk.Term.Ann{_, _}:
                                      W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
                                    case Bk.Term.Let{_, _, _}:
                                      W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
                                    case Bk.Term.Typ{_}:
                                      W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
                                    case Bk.Term.Min{_, _}:
                                      W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
                                    case Bk.Term.All{_, _, _}:
                                      W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
                                    case Bk.Term.Lam{_, _}:
                                      W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
                                    case Bk.Term.App{_, _, _}:
                                      W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
                                    case Bk.Term.Sig{_, _, _}:
                                      W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
                                    case Bk.Term.Tup{_, _, _}:
                                      W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
                                    case Bk.Term.Prj{_}:
                                      W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
                                    case Bk.Term.Enu{_}:
                                      W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
                                    case Bk.Term.Lab{+u1}:
                                      match r:
                                        case Bk.Term.Var{_}:
                                          W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                        case Bk.Term.Ref{_}:
                                          W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                        case Bk.Term.Ann{_, _}:
                                          W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                        case Bk.Term.Let{_, _, _}:
                                          W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                        case Bk.Term.Typ{_}:
                                          W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                        case Bk.Term.Min{_, _}:
                                          W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                        case Bk.Term.All{_, _, _}:
                                          W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                        case Bk.Term.Lam{_, _}:
                                          W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                        case Bk.Term.App{_, _, _}:
                                          W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                        case Bk.Term.Sig{_, _, _}:
                                          W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                        case Bk.Term.Tup{+q4, +w, +z}:
                                          match q4:
                                            case Bk.Quan.Q0{}:
                                              W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                            case Bk.Quan.Q1{}:
                                              match z:
                                                case Bk.Term.Var{_}:
                                                  W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                                case Bk.Term.Ref{_}:
                                                  W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                                case Bk.Term.Ann{_, _}:
                                                  W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                                case Bk.Term.Let{_, _, _}:
                                                  W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                                case Bk.Term.Typ{_}:
                                                  W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                                case Bk.Term.Min{_, _}:
                                                  W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                                case Bk.Term.All{_, _, _}:
                                                  W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                                case Bk.Term.Lam{_, _}:
                                                  W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                                case Bk.Term.App{_, _, _}:
                                                  W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                                case Bk.Term.Sig{_, _, _}:
                                                  W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                                case Bk.Term.Tup{_, _, _}:
                                                  W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                                case Bk.Term.Prj{_}:
                                                  W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                                case Bk.Term.Enu{_}:
                                                  W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                                case Bk.Term.Lab{+u2}:
                                                  LW.A(Sd.Name.is_eq(k, Pg.Program.name.wcon()), q, bn, u1, w, u2)
                                                case Bk.Term.Mat{_, _, _}:
                                                  W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                                case Bk.Term.Efq{}:
                                                  W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                                case Bk.Term.Eql{_, _, _}:
                                                  W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                                case Bk.Term.Rfl{}:
                                                  W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                                case Bk.Term.Rwt{_, _, _}:
                                                  W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                            case Bk.Quan.Q2{}:
                                              W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                        case Bk.Term.Prj{_}:
                                          W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                        case Bk.Term.Enu{_}:
                                          W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                        case Bk.Term.Lab{_}:
                                          W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                        case Bk.Term.Mat{_, _, _}:
                                          W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                        case Bk.Term.Efq{}:
                                          W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                        case Bk.Term.Eql{_, _, _}:
                                          W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                        case Bk.Term.Rfl{}:
                                          W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                        case Bk.Term.Rwt{_, _, _}:
                                          W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                    case Bk.Term.Mat{_, _, _}:
                                      W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
                                    case Bk.Term.Efq{}:
                                      W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
                                    case Bk.Term.Eql{_, _, _}:
                                      W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
                                    case Bk.Term.Rfl{}:
                                      W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
                                    case Bk.Term.Rwt{_, _, _}:
                                      W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
                                case Bk.Term.Mat{_, _, _}:
                                  W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, W1BY_none(q, VL(y), x, r, u => W1BU_none(q, Sd.Name.is_eq(u, Pg.Program.name.unit()), x, r, {==})))
                                case Bk.Term.Efq{}:
                                  W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, W1BY_none(q, VL(y), x, r, u => W1BU_none(q, Sd.Name.is_eq(u, Pg.Program.name.unit()), x, r, {==})))
                                case Bk.Term.Eql{_, _, _}:
                                  W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, W1BY_none(q, VL(y), x, r, u => W1BU_none(q, Sd.Name.is_eq(u, Pg.Program.name.unit()), x, r, {==})))
                                case Bk.Term.Rfl{}:
                                  W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, W1BY_none(q, VL(y), x, r, u => W1BU_none(q, Sd.Name.is_eq(u, Pg.Program.name.unit()), x, r, {==})))
                                case Bk.Term.Rwt{_, _, _}:
                                  W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, W1BY_none(q, VL(y), x, r, u => W1BU_none(q, Sd.Name.is_eq(u, Pg.Program.name.unit()), x, r, {==})))
                            case Bk.Quan.Q2{}:
                              W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
                        case Bk.Term.Prj{_}:
                          W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
                        case Bk.Term.Enu{_}:
                          W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
                        case Bk.Term.Lab{_}:
                          W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
                        case Bk.Term.Mat{_, _, _}:
                          W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
                        case Bk.Term.Efq{}:
                          W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
                        case Bk.Term.Eql{_, _, _}:
                          W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
                        case Bk.Term.Rfl{}:
                          W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
                        case Bk.Term.Rwt{_, _, _}:
                          W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
                    case Bk.Quan.Q2{}:
                      W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
                case Bk.Term.Prj{_}:
                  W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
                case Bk.Term.Enu{_}:
                  W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
                case Bk.Term.Lab{_}:
                  W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
                case Bk.Term.Mat{_, _, _}:
                  W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
                case Bk.Term.Efq{}:
                  W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
                case Bk.Term.Eql{_, _, _}:
                  W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
                case Bk.Term.Rfl{}:
                  W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
                case Bk.Term.Rwt{_, _, _}:
                  W1K_none(q, Sd.Name.is_eq(k, Pg.Program.name.wcon()), f, {==})
            case Bk.Term.Mat{_, _, _}:
              {==}
            case Bk.Term.Efq{}:
              {==}
            case Bk.Term.Eql{_, _, _}:
              {==}
            case Bk.Term.Rfl{}:
              {==}
            case Bk.Term.Rwt{_, _, _}:
              {==}
        case Bk.Quan.Q2{}:
          {==}
    case Bk.Term.Prj{_}:
      {==}
    case Bk.Term.Enu{_}:
      {==}
    case Bk.Term.Lab{_}:
      {==}
    case Bk.Term.Mat{_, _, _}:
      {==}
    case Bk.Term.Efq{}:
      {==}
    case Bk.Term.Eql{_, _, _}:
      {==}
    case Bk.Term.Rfl{}:
      {==}
    case Bk.Term.Rwt{_, _, _}:
      {==}

def WE(+p: Nat, +t: Bk.Term) -> {Pg.Program.unword(p, t) == Wd(p, t) : Maybe<&2, Word(p)>}:
  match p:
    case 0n:
      WE0(t)
    case 1n+q:
      WE1(q, t)


# The term of a word is the word that CW reads
# ---------------------------------------------

def W0z_eq(x: Bool) -> {Pg.Program.unword.nil(x) == CW0.z(x) : Maybe<&2, Word(0n)>}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

def WB0.u2(+k: List<&2, Word(8n)>, +g: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32,
  +hok3: {ok(1n+g, m, ks, img, Fd(3n, m, c), im, fs, nx) == True{} : Bool}, +eL: {Lm(m, Fd(3n, m, c)) == True{} : Bool},
  +ek: {T.tm.name(ks, Fd(2n, m, Fd(3n, m, c))) == Some{k} : Maybe<&2, List<&2, Word(8n)>>}) ->
  {W0.z(Some{k}) == CW0.z(U32.is_eq(Fd(2n, m, Fd(3n, m, c)), 0)) : Maybe<&2, Word(0n)>}:
  %Equal.sym(Bool, Sd.Name.is_eq(k, Pg.Program.name.unit()), U32.is_eq(Fd(2n, m, Fd(3n, m, c)), 0), kn0(Fd(2n, m, Fd(3n, m, c)), k, LK(g, m, ks, img, Fd(3n, m, c), im, fs, nx, hok3, eL, k, ek))) :
    {Pg.Program.unword.nil(_) == CW0.z(U32.is_eq(Fd(2n, m, Fd(3n, m, c)), 0)) : Maybe<&2, Word(0n)>}
  W0z_eq(U32.is_eq(Fd(2n, m, Fd(3n, m, c)), 0))

def WB0.u(bu: Bool, +g: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32,
  +hok3: {ok(1n+g, m, ks, img, Fd(3n, m, c), im, fs, nx) == True{} : Bool}, +e: {Lm(m, Fd(3n, m, c)) == bu : Bool}) ->
  SpecM(T.tm.of(1n+g, m, ks, img, Fd(3n, m, c)), z => {W0.z(VL(z)) == CW0.z(Bool.and(bu, U32.is_eq(Fd(2n, m, Fd(3n, m, c)), 0))) : Maybe<&2, Word(0n)>}):
  match bu:
    case False{}:
      cellNotL(g, m, ks, img, Fd(3n, m, c), im, fs, nx, z => {W0.z(VL(z)) == CW0.z(Bool.and(False{}, U32.is_eq(Fd(2n, m, Fd(3n, m, c)), 0))) : Maybe<&2, Word(0n)>}, e, hok3,
        v => ev => Equal.cong(Maybe<&2, List<&2, Word(8n)>>, Maybe<&2, Word(0n)>, mm => W0.z(mm), VL(v), None{}, ev))
    case True{}:
      cellLab(g, m, ks, img, Fd(3n, m, c), z => {W0.z(VL(z)) == CW0.z(Bool.and(True{}, U32.is_eq(Fd(2n, m, Fd(3n, m, c)), 0))) : Maybe<&2, Word(0n)>}, e,
        k => ek => WB0.u2(k, g, m, ks, img, c, im, fs, nx, hok3, e, ek))

def WB0.k(bk: Bool, +g: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32,
  +hok3: {ok(1n+g, m, ks, img, Fd(3n, m, c), im, fs, nx) == True{} : Bool}) ->
  SpecM(T.tm.of(1n+g, m, ks, img, Fd(3n, m, c)), z => {W0.k(bk, z) == CW0.l(bk, m, c) : Maybe<&2, Word(0n)>}):
  match bk:
    case False{}:
      SpecM.all(T.tm.of(1n+g, m, ks, img, Fd(3n, m, c)), z => {W0.k(False{}, z) == CW0.l(False{}, m, c) : Maybe<&2, Word(0n)>}, z => {==})
    case True{}:
      WB0.u(Lm(m, Fd(3n, m, c)), g, m, ks, img, c, im, fs, nx, hok3, {==})

def WB0.k0(+k: List<&2, Word(8n)>, +g: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32,
  +hok2: {ok(1n+g, m, ks, img, Fd(2n, m, c), im, fs, nx) == True{} : Bool}, +hok3: {ok(1n+g, m, ks, img, Fd(3n, m, c), im, fs, nx) == True{} : Bool},
  +eL: {Lm(m, Fd(2n, m, c)) == True{} : Bool}, +ek: {T.tm.name(ks, Fd(2n, m, Fd(2n, m, c))) == Some{k} : Maybe<&2, List<&2, Word(8n)>>}) ->
  SpecM(T.tm.of(1n+g, m, ks, img, Fd(3n, m, c)), z => {W0.a(Some{k}, z) == CW0.l(Bool.and(True{}, U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 3)), m, c) : Maybe<&2, Word(0n)>}):
  %Equal.sym(Bool, Sd.Name.is_eq(k, Pg.Program.name.wnil()), U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 3), kn3(Fd(2n, m, Fd(2n, m, c)), k, LK(g, m, ks, img, Fd(2n, m, c), im, fs, nx, hok2, eL, k, ek))) :
    SpecM(T.tm.of(1n+g, m, ks, img, Fd(3n, m, c)), z => {W0.k(_, z) == CW0.l(U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 3), m, c) : Maybe<&2, Word(0n)>})
  WB0.k(U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 3), g, m, ks, img, c, im, fs, nx, hok3)

def WB0.l(bl: Bool, +g: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32,
  +hok2: {ok(1n+g, m, ks, img, Fd(2n, m, c), im, fs, nx) == True{} : Bool}, +hok3: {ok(1n+g, m, ks, img, Fd(3n, m, c), im, fs, nx) == True{} : Bool},
  +e: {Lm(m, Fd(2n, m, c)) == bl : Bool}) ->
  SpecM(T.tm.of(1n+g, m, ks, img, Fd(2n, m, c)), a => SpecM(T.tm.of(1n+g, m, ks, img, Fd(3n, m, c)),
    z => {W0.a(VL(a), z) == CW0.l(Bool.and(bl, U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 3)), m, c) : Maybe<&2, Word(0n)>})):
  match bl:
    case False{}:
      cellNotL(g, m, ks, img, Fd(2n, m, c), im, fs, nx, a => SpecM(T.tm.of(1n+g, m, ks, img, Fd(3n, m, c)),
        z => {W0.a(VL(a), z) == CW0.l(Bool.and(False{}, U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 3)), m, c) : Maybe<&2, Word(0n)>}), e, hok2,
        v => ev => SpecM.all(T.tm.of(1n+g, m, ks, img, Fd(3n, m, c)),
          z => {W0.a(VL(v), z) == CW0.l(Bool.and(False{}, U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 3)), m, c) : Maybe<&2, Word(0n)>},
          z => Equal.cong(Maybe<&2, List<&2, Word(8n)>>, Maybe<&2, Word(0n)>, mm => W0.a(mm, z), VL(v), None{}, ev)))
    case True{}:
      cellLab(g, m, ks, img, Fd(2n, m, c), a => SpecM(T.tm.of(1n+g, m, ks, img, Fd(3n, m, c)),
        z => {W0.a(VL(a), z) == CW0.l(Bool.and(True{}, U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 3)), m, c) : Maybe<&2, Word(0n)>}), e,
        k => ek => WB0.k0(k, g, m, ks, img, c, im, fs, nx, hok2, hok3, e, ek))

def WB0.p(b: Bool, +f: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32,
  +hok: {ok(1n+f, m, ks, img, c, im, fs, nx) == True{} : Bool}, +eb: {Pm(m, c) == b : Bool}) ->
  SpecM(T.tm.of(1n+f, m, ks, img, c), t => {W0.r(V1(t)) == CW0.p(b, m, c) : Maybe<&2, Word(0n)>}):
  match b:
    case False{}:
      cellNotT1(f, m, ks, img, c, im, fs, nx, t => {W0.r(V1(t)) == CW0.p(False{}, m, c) : Maybe<&2, Word(0n)>}, eb, hok,
        v => ev => Equal.cong(Maybe<&2, TP>, Maybe<&2, Word(0n)>, mm => W0.r(mm), V1(v), None{}, ev))
    case True{}:
      match f:
        case 0n:
          cellT1(0n, m, ks, img, c, t => {W0.r(V1(t)) == CW0.p(True{}, m, c) : Maybe<&2, Word(0n)>}, eb, Unit{})
        case 1n+g:
          cellT1(1n+g, m, ks, img, c, t => {W0.r(V1(t)) == CW0.p(True{}, m, c) : Maybe<&2, Word(0n)>}, eb,
            WB0.l(Lm(m, Fd(2n, m, c)), g, m, ks, img, c, im, fs, nx, ok.l(1n+g, m, ks, img, c, im, fs, nx, hok, eb),
              ok.r(1n+g, m, ks, img, c, im, fs, nx, hok, eb), {==}))

# the term of the cell c, a word of no bits, is what CW reads
def WB0(+fw: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32,
  +hok: {ok(fw, m, ks, img, c, im, fs, nx) == True{} : Bool}) ->
  SpecM(T.tm.of(fw, m, ks, img, c), t => {Wd(0n, t) == CW(0n, m, c) : Maybe<&2, Word(0n)>}):
  match fw:
    case 0n:
      Empty.absurd(SpecM(T.tm.of(0n, m, ks, img, c), t => {Wd(0n, t) == CW(0n, m, c) : Maybe<&2, Word(0n)>}), ok.zero(m, ks, img, c, im, fs, nx, hok))
    case 1n+f:
      WB0.p(Pm(m, c), f, m, ks, img, c, im, fs, nx, hok, {==})

# the claim of WB for the word of q bits after a bit
def WB.IH(+q: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +im: U32, +fs: U32, +nx: U32) -> Type:
  @fw2: Nat -> @c2: U32 -> {ok(fw2, m, ks, img, c2, im, fs, nx) == True{} : Bool} ->
    SpecM(T.tm.of(fw2, m, ks, img, c2), w => {Pg.Program.unword(q, w) == CW(q, m, c2) : Maybe<&2, Word(q)>})

def WB1.u(bu: Bool, +q: Nat, +x: Bool, +i: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32, +hokn: {ok(1n+i, m, ks, img, CW.next(m, c), im, fs, nx) == True{} : Bool}, ih: WB.IH(q, m, ks, img, im, fs, nx)) ->
  SpecM(T.tm.of(1n+i, m, ks, img, CW.next(m, c)), w => {W1.u(q, x, bu, w) == W1.g(q, GB.z(x, bu), CW(q, m, CW.next(m, c))) : Maybe<&2, Word(1n+q)>}):
  match bu:
    case False{}:
      SpecM.all(T.tm.of(1n+i, m, ks, img, CW.next(m, c)), w => {W1.u(q, x, False{}, w) == W1.g(q, GB.z(x, False{}), CW(q, m, CW.next(m, c))) : Maybe<&2, Word(1n+q)>}, w => {==})
    case True{}:
      SpecM.map(T.tm.of(1n+i, m, ks, img, CW.next(m, c)), w => {Pg.Program.unword(q, w) == CW(q, m, CW.next(m, c)) : Maybe<&2, Word(q)>},
        w => {W1.u(q, x, True{}, w) == W1.g(q, GB.z(x, True{}), CW(q, m, CW.next(m, c))) : Maybe<&2, Word(1n+q)>}, ih(1n+i, CW.next(m, c), hokn),
        w => e => Equal.cong(Maybe<&2, Word(q)>, Maybe<&2, Word(1n+q)>, mw => W1.w(q, x, mw), Pg.Program.unword(q, w), CW(q, m, CW.next(m, c)), e))

def WB1.u0(+k: List<&2, Word(8n)>, +q: Nat, +x: Bool, +i: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32, +hokz: {ok(1n+i, m, ks, img, Fd(3n, m, Fd(3n, m, Fd(3n, m, c))), im, fs, nx) == True{} : Bool}, +hokn: {ok(1n+i, m, ks, img, CW.next(m, c), im, fs, nx) == True{} : Bool},
  +eL: {Lm(m, Fd(3n, m, Fd(3n, m, Fd(3n, m, c)))) == True{} : Bool}, +ek: {T.tm.name(ks, Fd(2n, m, Fd(3n, m, Fd(3n, m, Fd(3n, m, c))))) == Some{k} : Maybe<&2, List<&2, Word(8n)>>}, ih: WB.IH(q, m, ks, img, im, fs, nx)) ->
  SpecM(T.tm.of(1n+i, m, ks, img, CW.next(m, c)), w => {W1.z(q, x, w, Some{k}) == W1.g(q, GB.z(x, Bool.and(True{}, U32.is_eq(Fd(2n, m, Fd(3n, m, Fd(3n, m, Fd(3n, m, c)))), 0))), CW(q, m, CW.next(m, c))) : Maybe<&2, Word(1n+q)>}):
  %Equal.sym(Bool, Sd.Name.is_eq(k, Pg.Program.name.unit()), U32.is_eq(Fd(2n, m, Fd(3n, m, Fd(3n, m, Fd(3n, m, c)))), 0), kn0(Fd(2n, m, Fd(3n, m, Fd(3n, m, Fd(3n, m, c)))), k, LK(i, m, ks, img, Fd(3n, m, Fd(3n, m, Fd(3n, m, c))), im, fs, nx, hokz, eL, k, ek))) :
    SpecM(T.tm.of(1n+i, m, ks, img, CW.next(m, c)), w => {W1.u(q, x, _, w) == W1.g(q, GB.z(x, U32.is_eq(Fd(2n, m, Fd(3n, m, Fd(3n, m, Fd(3n, m, c)))), 0)), CW(q, m, CW.next(m, c))) : Maybe<&2, Word(1n+q)>})
  WB1.u(U32.is_eq(Fd(2n, m, Fd(3n, m, Fd(3n, m, Fd(3n, m, c)))), 0), q, x, i, m, ks, img, c, im, fs, nx, hokn, ih)

def WB1.z(bz: Bool, +q: Nat, +x: Bool, +i: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32, +hokz: {ok(1n+i, m, ks, img, Fd(3n, m, Fd(3n, m, Fd(3n, m, c))), im, fs, nx) == True{} : Bool}, +hokn: {ok(1n+i, m, ks, img, CW.next(m, c), im, fs, nx) == True{} : Bool},
  +e: {Lm(m, Fd(3n, m, Fd(3n, m, Fd(3n, m, c)))) == bz : Bool}, ih: WB.IH(q, m, ks, img, im, fs, nx)) ->
  SpecM(T.tm.of(1n+i, m, ks, img, Fd(3n, m, Fd(3n, m, Fd(3n, m, c)))), z => SpecM(T.tm.of(1n+i, m, ks, img, CW.next(m, c)), w => {W1.z(q, x, w, VL(z)) == W1.g(q, GB.z(x, Bool.and(bz, U32.is_eq(Fd(2n, m, Fd(3n, m, Fd(3n, m, Fd(3n, m, c)))), 0))), CW(q, m, CW.next(m, c))) : Maybe<&2, Word(1n+q)>})):
  match bz:
    case False{}:
      cellNotL(i, m, ks, img, Fd(3n, m, Fd(3n, m, Fd(3n, m, c))), im, fs, nx, z => SpecM(T.tm.of(1n+i, m, ks, img, CW.next(m, c)), w => {W1.z(q, x, w, VL(z)) == W1.g(q, GB.z(x, Bool.and(False{}, U32.is_eq(Fd(2n, m, Fd(3n, m, Fd(3n, m, Fd(3n, m, c)))), 0))), CW(q, m, CW.next(m, c))) : Maybe<&2, Word(1n+q)>}),
        e, hokz, v => ev => SpecM.all(T.tm.of(1n+i, m, ks, img, CW.next(m, c)), w => {W1.z(q, x, w, VL(v)) == W1.g(q, GB.z(x, Bool.and(False{}, U32.is_eq(Fd(2n, m, Fd(3n, m, Fd(3n, m, Fd(3n, m, c)))), 0))), CW(q, m, CW.next(m, c))) : Maybe<&2, Word(1n+q)>},
          w => Equal.cong(Maybe<&2, List<&2, Word(8n)>>, Maybe<&2, Word(1n+q)>, mm => W1.z(q, x, w, mm), VL(v), None{}, ev)))
    case True{}:
      cellLab(i, m, ks, img, Fd(3n, m, Fd(3n, m, Fd(3n, m, c))), z => SpecM(T.tm.of(1n+i, m, ks, img, CW.next(m, c)), w => {W1.z(q, x, w, VL(z)) == W1.g(q, GB.z(x, Bool.and(True{}, U32.is_eq(Fd(2n, m, Fd(3n, m, Fd(3n, m, Fd(3n, m, c)))), 0))), CW(q, m, CW.next(m, c))) : Maybe<&2, Word(1n+q)>}),
        e, k => ek => WB1.u0(k, q, x, i, m, ks, img, c, im, fs, nx, hokz, hokn, e, ek, ih))

def WB1.r(br: Bool, +q: Nat, +x: Bool, +h: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32, +hokr: {ok(1n+h, m, ks, img, Fd(3n, m, Fd(3n, m, c)), im, fs, nx) == True{} : Bool}, +e: {Pm(m, Fd(3n, m, Fd(3n, m, c))) == br : Bool}, ih: WB.IH(q, m, ks, img, im, fs, nx)) ->
  SpecM(T.tm.of(1n+h, m, ks, img, Fd(3n, m, Fd(3n, m, c))), r => {W1.r2(q, x, V1(r)) == W1.g(q, GB.r(x, br, m, Fd(3n, m, Fd(3n, m, c))), CW(q, m, CW.next(m, c))) : Maybe<&2, Word(1n+q)>}):
  match br:
    case False{}:
      cellNotT1(h, m, ks, img, Fd(3n, m, Fd(3n, m, c)), im, fs, nx, r => {W1.r2(q, x, V1(r)) == W1.g(q, GB.r(x, False{}, m, Fd(3n, m, Fd(3n, m, c))), CW(q, m, CW.next(m, c))) : Maybe<&2, Word(1n+q)>}, e, hokr,
        v => ev => Equal.cong(Maybe<&2, TP>, Maybe<&2, Word(1n+q)>, mm => W1.r2(q, x, mm), V1(v), None{}, ev))
    case True{}:
      match h:
        case 0n:
          cellT1(0n, m, ks, img, Fd(3n, m, Fd(3n, m, c)), r => {W1.r2(q, x, V1(r)) == W1.g(q, GB.r(x, True{}, m, Fd(3n, m, Fd(3n, m, c))), CW(q, m, CW.next(m, c))) : Maybe<&2, Word(1n+q)>}, e, Unit{})
        case 1n+i:
          cellT1(1n+i, m, ks, img, Fd(3n, m, Fd(3n, m, c)), r => {W1.r2(q, x, V1(r)) == W1.g(q, GB.r(x, True{}, m, Fd(3n, m, Fd(3n, m, c))), CW(q, m, CW.next(m, c))) : Maybe<&2, Word(1n+q)>}, e,
            SpecM.swap(T.tm.of(1n+i, m, ks, img, CW.next(m, c)), T.tm.of(1n+i, m, ks, img, Fd(3n, m, Fd(3n, m, Fd(3n, m, c)))), w => z => {W1.r2(q, x, V1(Bk.Term.Tup{Bk.Quan.Q1{}, w, z})) == W1.g(q, GB.r(x, True{}, m, Fd(3n, m, Fd(3n, m, c))), CW(q, m, CW.next(m, c))) : Maybe<&2, Word(1n+q)>},
              WB1.z(Lm(m, Fd(3n, m, Fd(3n, m, Fd(3n, m, c)))), q, x, i, m, ks, img, c, im, fs, nx, ok.r(1n+i, m, ks, img, Fd(3n, m, Fd(3n, m, c)), im, fs, nx, hokr, e), ok.l(1n+i, m, ks, img, Fd(3n, m, Fd(3n, m, c)), im, fs, nx, hokr, e), {==}, ih)))

def WB1.b(mb: Maybe<&2, Bool>, +q: Nat, +h: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32, +hokr: {ok(1n+h, m, ks, img, Fd(3n, m, Fd(3n, m, c)), im, fs, nx) == True{} : Bool}, ih: WB.IH(q, m, ks, img, im, fs, nx)) ->
  SpecM(T.tm.of(1n+h, m, ks, img, Fd(3n, m, Fd(3n, m, c))), r => {W1.b(q, mb, r) == W1.g(q, GB.b(mb, m, Fd(3n, m, Fd(3n, m, c))), CW(q, m, CW.next(m, c))) : Maybe<&2, Word(1n+q)>}):
  match mb:
    case None{}:
      SpecM.all(T.tm.of(1n+h, m, ks, img, Fd(3n, m, Fd(3n, m, c))), r => {W1.b(q, None{}, r) == W1.g(q, GB.b(None{}, m, Fd(3n, m, Fd(3n, m, c))), CW(q, m, CW.next(m, c))) : Maybe<&2, Word(1n+q)>}, r => {==})
    case Some{x}:
      WB1.r(Pm(m, Fd(3n, m, Fd(3n, m, c))), q, x, h, m, ks, img, c, im, fs, nx, hokr, {==}, ih)

def WB1.bt(+q: Nat, -bt: Bk.Term, +h: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32, +eub: {Ub(bt) == CB(m, Fd(2n, m, Fd(3n, m, c))) : Maybe<&2, Bool>},
  x: SpecM(T.tm.of(1n+h, m, ks, img, Fd(3n, m, Fd(3n, m, c))), r => {W1.b(q, CB(m, Fd(2n, m, Fd(3n, m, c))), r) == W1.g(q, GB.b(CB(m, Fd(2n, m, Fd(3n, m, c))), m, Fd(3n, m, Fd(3n, m, c))), CW(q, m, CW.next(m, c))) : Maybe<&2, Word(1n+q)>})) ->
  SpecM(T.tm.of(1n+h, m, ks, img, Fd(3n, m, Fd(3n, m, c))), r => {W1.b(q, Ub(bt), r) == W1.g(q, GB.b(CB(m, Fd(2n, m, Fd(3n, m, c))), m, Fd(3n, m, Fd(3n, m, c))), CW(q, m, CW.next(m, c))) : Maybe<&2, Word(1n+q)>}):
  %Equal.sym(Maybe<&2, Bool>, Ub(bt), CB(m, Fd(2n, m, Fd(3n, m, c))), eub) :
    SpecM(T.tm.of(1n+h, m, ks, img, Fd(3n, m, Fd(3n, m, c))), r => {W1.b(q, _, r) == W1.g(q, GB.b(CB(m, Fd(2n, m, Fd(3n, m, c))), m, Fd(3n, m, Fd(3n, m, c))), CW(q, m, CW.next(m, c))) : Maybe<&2, Word(1n+q)>})
  x

def WB1.f(bf: Bool, +q: Nat, +g: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32, +hokf: {ok(1n+g, m, ks, img, Fd(3n, m, c), im, fs, nx) == True{} : Bool}, +e: {Pm(m, Fd(3n, m, c)) == bf : Bool}, ih: WB.IH(q, m, ks, img, im, fs, nx)) ->
  SpecM(T.tm.of(1n+g, m, ks, img, Fd(3n, m, c)), fv => {W1.f(q, V1(fv)) == W1.g(q, GB.f(bf, m, Fd(3n, m, c)), CW(q, m, CW.next(m, c))) : Maybe<&2, Word(1n+q)>}):
  match bf:
    case False{}:
      cellNotT1(g, m, ks, img, Fd(3n, m, c), im, fs, nx, fv => {W1.f(q, V1(fv)) == W1.g(q, GB.f(False{}, m, Fd(3n, m, c)), CW(q, m, CW.next(m, c))) : Maybe<&2, Word(1n+q)>}, e, hokf,
        v => ev => Equal.cong(Maybe<&2, TP>, Maybe<&2, Word(1n+q)>, mm => W1.f(q, mm), V1(v), None{}, ev))
    case True{}:
      match g:
        case 0n:
          cellT1(0n, m, ks, img, Fd(3n, m, c), fv => {W1.f(q, V1(fv)) == W1.g(q, GB.f(True{}, m, Fd(3n, m, c)), CW(q, m, CW.next(m, c))) : Maybe<&2, Word(1n+q)>}, e, Unit{})
        case 1n+h:
          cellT1(1n+h, m, ks, img, Fd(3n, m, c), fv => {W1.f(q, V1(fv)) == W1.g(q, GB.f(True{}, m, Fd(3n, m, c)), CW(q, m, CW.next(m, c))) : Maybe<&2, Word(1n+q)>}, e,
            SpecM.map(T.tm.of(1n+h, m, ks, img, Fd(2n, m, Fd(3n, m, c))), bt => {Ub(bt) == CB(m, Fd(2n, m, Fd(3n, m, c))) : Maybe<&2, Bool>},
              bt => SpecM(T.tm.of(1n+h, m, ks, img, Fd(3n, m, Fd(3n, m, c))), r => {W1.b(q, Ub(bt), r) == W1.g(q, GB.b(CB(m, Fd(2n, m, Fd(3n, m, c))), m, Fd(3n, m, Fd(3n, m, c))), CW(q, m, CW.next(m, c))) : Maybe<&2, Word(1n+q)>}),
              BB(1n+h, m, ks, img, Fd(2n, m, Fd(3n, m, c)), im, fs, nx, ok.l(1n+h, m, ks, img, Fd(3n, m, c), im, fs, nx, hokf, e)),
              bt => eub => WB1.bt(q, bt, h, m, ks, img, c, im, fs, nx, eub, WB1.b(CB(m, Fd(2n, m, Fd(3n, m, c))), q, h, m, ks, img, c, im, fs, nx, ok.r(1n+h, m, ks, img, Fd(3n, m, c), im, fs, nx, hokf, e), ih))))

def WB1.k(bk: Bool, +q: Nat, +g: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32, +hokf: {ok(1n+g, m, ks, img, Fd(3n, m, c), im, fs, nx) == True{} : Bool}, ih: WB.IH(q, m, ks, img, im, fs, nx)) ->
  SpecM(T.tm.of(1n+g, m, ks, img, Fd(3n, m, c)), fv => {W1.k(q, bk, fv) == W1.g(q, GB.l(bk, m, Fd(3n, m, c)), CW(q, m, CW.next(m, c))) : Maybe<&2, Word(1n+q)>}):
  match bk:
    case False{}:
      SpecM.all(T.tm.of(1n+g, m, ks, img, Fd(3n, m, c)), fv => {W1.k(q, False{}, fv) == W1.g(q, GB.l(False{}, m, Fd(3n, m, c)), CW(q, m, CW.next(m, c))) : Maybe<&2, Word(1n+q)>}, fv => {==})
    case True{}:
      WB1.f(Pm(m, Fd(3n, m, c)), q, g, m, ks, img, c, im, fs, nx, hokf, {==}, ih)

def WB1.k0(+k: List<&2, Word(8n)>, +q: Nat, +g: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32, +hok2: {ok(1n+g, m, ks, img, Fd(2n, m, c), im, fs, nx) == True{} : Bool}, +hokf: {ok(1n+g, m, ks, img, Fd(3n, m, c), im, fs, nx) == True{} : Bool},
  +eL: {Lm(m, Fd(2n, m, c)) == True{} : Bool}, +ek: {T.tm.name(ks, Fd(2n, m, Fd(2n, m, c))) == Some{k} : Maybe<&2, List<&2, Word(8n)>>}, ih: WB.IH(q, m, ks, img, im, fs, nx)) ->
  SpecM(T.tm.of(1n+g, m, ks, img, Fd(3n, m, c)), fv => {W1.a(q, Some{k}, fv) == W1.g(q, GB.l(Bool.and(True{}, U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 4)), m, Fd(3n, m, c)), CW(q, m, CW.next(m, c))) : Maybe<&2, Word(1n+q)>}):
  %Equal.sym(Bool, Sd.Name.is_eq(k, Pg.Program.name.wcon()), U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 4), kn4(Fd(2n, m, Fd(2n, m, c)), k, LK(g, m, ks, img, Fd(2n, m, c), im, fs, nx, hok2, eL, k, ek))) :
    SpecM(T.tm.of(1n+g, m, ks, img, Fd(3n, m, c)), fv => {W1.k(q, _, fv) == W1.g(q, GB.l(U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 4), m, Fd(3n, m, c)), CW(q, m, CW.next(m, c))) : Maybe<&2, Word(1n+q)>})
  WB1.k(U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 4), q, g, m, ks, img, c, im, fs, nx, hokf, ih)

def WB1.l(bl: Bool, +q: Nat, +g: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32, +hok2: {ok(1n+g, m, ks, img, Fd(2n, m, c), im, fs, nx) == True{} : Bool}, +hokf: {ok(1n+g, m, ks, img, Fd(3n, m, c), im, fs, nx) == True{} : Bool}, +e: {Lm(m, Fd(2n, m, c)) == bl : Bool}, ih: WB.IH(q, m, ks, img, im, fs, nx)) ->
  SpecM(T.tm.of(1n+g, m, ks, img, Fd(2n, m, c)), a => SpecM(T.tm.of(1n+g, m, ks, img, Fd(3n, m, c)), fv => {W1.a(q, VL(a), fv) == W1.g(q, GB.l(Bool.and(bl, U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 4)), m, Fd(3n, m, c)), CW(q, m, CW.next(m, c))) : Maybe<&2, Word(1n+q)>})):
  match bl:
    case False{}:
      cellNotL(g, m, ks, img, Fd(2n, m, c), im, fs, nx, a => SpecM(T.tm.of(1n+g, m, ks, img, Fd(3n, m, c)), fv => {W1.a(q, VL(a), fv) == W1.g(q, GB.l(Bool.and(False{}, U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 4)), m, Fd(3n, m, c)), CW(q, m, CW.next(m, c))) : Maybe<&2, Word(1n+q)>}),
        e, hok2, v => ev => SpecM.all(T.tm.of(1n+g, m, ks, img, Fd(3n, m, c)), fv => {W1.a(q, VL(v), fv) == W1.g(q, GB.l(Bool.and(False{}, U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 4)), m, Fd(3n, m, c)), CW(q, m, CW.next(m, c))) : Maybe<&2, Word(1n+q)>},
          fv => Equal.cong(Maybe<&2, List<&2, Word(8n)>>, Maybe<&2, Word(1n+q)>, mm => W1.a(q, mm, fv), VL(v), None{}, ev)))
    case True{}:
      cellLab(g, m, ks, img, Fd(2n, m, c), a => SpecM(T.tm.of(1n+g, m, ks, img, Fd(3n, m, c)), fv => {W1.a(q, VL(a), fv) == W1.g(q, GB.l(Bool.and(True{}, U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 4)), m, Fd(3n, m, c)), CW(q, m, CW.next(m, c))) : Maybe<&2, Word(1n+q)>}),
        e, k => ek => WB1.k0(k, q, g, m, ks, img, c, im, fs, nx, hok2, hokf, e, ek, ih))

def WB1.p(b: Bool, +q: Nat, +f: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32, +hok: {ok(1n+f, m, ks, img, c, im, fs, nx) == True{} : Bool}, +eb: {Pm(m, c) == b : Bool}, ih: WB.IH(q, m, ks, img, im, fs, nx)) ->
  SpecM(T.tm.of(1n+f, m, ks, img, c), t => {W1.r(q, V1(t)) == W1.g(q, GB.p(b, m, c), CW(q, m, CW.next(m, c))) : Maybe<&2, Word(1n+q)>}):
  match b:
    case False{}:
      cellNotT1(f, m, ks, img, c, im, fs, nx, t => {W1.r(q, V1(t)) == W1.g(q, GB.p(False{}, m, c), CW(q, m, CW.next(m, c))) : Maybe<&2, Word(1n+q)>}, eb, hok,
        v => ev => Equal.cong(Maybe<&2, TP>, Maybe<&2, Word(1n+q)>, mm => W1.r(q, mm), V1(v), None{}, ev))
    case True{}:
      match f:
        case 0n:
          cellT1(0n, m, ks, img, c, t => {W1.r(q, V1(t)) == W1.g(q, GB.p(True{}, m, c), CW(q, m, CW.next(m, c))) : Maybe<&2, Word(1n+q)>}, eb, Unit{})
        case 1n+g:
          cellT1(1n+g, m, ks, img, c, t => {W1.r(q, V1(t)) == W1.g(q, GB.p(True{}, m, c), CW(q, m, CW.next(m, c))) : Maybe<&2, Word(1n+q)>}, eb,
            WB1.l(Lm(m, Fd(2n, m, c)), q, g, m, ks, img, c, im, fs, nx, ok.l(1n+g, m, ks, img, c, im, fs, nx, hok, eb), ok.r(1n+g, m, ks, img, c, im, fs, nx, hok, eb), {==}, ih))

def WB1(+q: Nat, +fw: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32, +hok: {ok(fw, m, ks, img, c, im, fs, nx) == True{} : Bool}, ih: WB.IH(q, m, ks, img, im, fs, nx)) ->
  SpecM(T.tm.of(fw, m, ks, img, c), t => {Wd(1n+q, t) == CW(1n+q, m, c) : Maybe<&2, Word(1n+q)>}):
  match fw:
    case 0n:
      Empty.absurd(SpecM(T.tm.of(0n, m, ks, img, c), t => {Wd(1n+q, t) == CW(1n+q, m, c) : Maybe<&2, Word(1n+q)>}), ok.zero(m, ks, img, c, im, fs, nx, hok))
    case 1n+f:
      WB1.p(Pm(m, c), q, f, m, ks, img, c, im, fs, nx, hok, {==}, ih)

# the term of the cell c, a word of p bits, is the word that CW reads
def WB(+p: Nat, +fw: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32, +hok: {ok(fw, m, ks, img, c, im, fs, nx) == True{} : Bool}) ->
  SpecM(T.tm.of(fw, m, ks, img, c), t => {Pg.Program.unword(p, t) == CW(p, m, c) : Maybe<&2, Word(p)>}):
  match p:
    case 0n:
      SpecM.map(T.tm.of(fw, m, ks, img, c), t => {Wd(0n, t) == CW(0n, m, c) : Maybe<&2, Word(0n)>}, t => {Pg.Program.unword(0n, t) == CW(0n, m, c) : Maybe<&2, Word(0n)>},
        WB0(fw, m, ks, img, c, im, fs, nx, hok), t => e => Equal.trans(Maybe<&2, Word(0n)>, Pg.Program.unword(0n, t), Wd(0n, t), CW(0n, m, c), WE0(t), e))
    case 1n+q:
      SpecM.map(T.tm.of(fw, m, ks, img, c), t => {Wd(1n+q, t) == CW(1n+q, m, c) : Maybe<&2, Word(1n+q)>}, t => {Pg.Program.unword(1n+q, t) == CW(1n+q, m, c) : Maybe<&2, Word(1n+q)>},
        WB1(q, fw, m, ks, img, c, im, fs, nx, hok, fw2 => c2 => h2 => WB(q, fw2, m, ks, img, c2, im, fs, nx, h2)),
        t => e => Equal.trans(Maybe<&2, Word(1n+q)>, Pg.Program.unword(1n+q, t), Wd(1n+q, t), CW(1n+q, m, c), WE1(q, t), e))

# The term of a list is the list that CU reads
# --------------------------------------------

# the claim of LB for the rest of a list
def LB.IH(+k: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +im: U32, +fs: U32, +nx: U32) -> Type:
  @rc2: U32 -> {ok(k, m, ks, img, rc2, im, fs, nx) == True{} : Bool} ->
    SpecM(T.tm.of(k, m, ks, img, rc2), t => {Pg.Program.unbytes(t) == CU(k, m, Step(m, rc2)) : Maybe<&2, List<&2, Word(8n)>>})

def LB.c4(mw: Maybe<&2, Word(8n)>, +a3: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32, +hokr: {ok(1n+a3, m, ks, img, Fd(2n, m, Fd(3n, m, Fd(3n, m, c))), im, fs, nx) == True{} : Bool}, ih: LB.IH(1n+a3, m, ks, img, im, fs, nx)) ->
  SpecM(T.tm.of(1n+a3, m, ks, img, Fd(2n, m, Fd(3n, m, Fd(3n, m, c)))), rest => {U.c4(mw, rest) == CU(4n+a3, m, S.c3(mw, Fd(2n, m, Fd(3n, m, Fd(3n, m, c))))) : Maybe<&2, List<&2, Word(8n)>>}):
  match mw:
    case None{}:
      SpecM.all(T.tm.of(1n+a3, m, ks, img, Fd(2n, m, Fd(3n, m, Fd(3n, m, c)))), rest => {U.c4(None{}, rest) == CU(4n+a3, m, S.c3(None{}, Fd(2n, m, Fd(3n, m, Fd(3n, m, c))))) : Maybe<&2, List<&2, Word(8n)>>}, rest => Equal.sym(Maybe<&2, List<&2, Word(8n)>>, CU(1n+3n+a3, m, SR.done{None{}}), None{}, CUd(3n+a3, m, None{})))
    case Some{x}:
      SpecM.map(T.tm.of(1n+a3, m, ks, img, Fd(2n, m, Fd(3n, m, Fd(3n, m, c)))), rest => {Pg.Program.unbytes(rest) == CU(1n+a3, m, Step(m, Fd(2n, m, Fd(3n, m, Fd(3n, m, c))))) : Maybe<&2, List<&2, Word(8n)>>},
        rest => {U.c4(Some{x}, rest) == CU(4n+a3, m, S.c3(Some{x}, Fd(2n, m, Fd(3n, m, Fd(3n, m, c))))) : Maybe<&2, List<&2, Word(8n)>>}, ih(Fd(2n, m, Fd(3n, m, Fd(3n, m, c))), hokr),
        rest => e => Equal.cong(Maybe<&2, List<&2, Word(8n)>>, Maybe<&2, List<&2, Word(8n)>>, mr => U.c5(x, mr), Pg.Program.unbytes(rest), CU(1n+a3, m, Step(m, Fd(2n, m, Fd(3n, m, Fd(3n, m, c))))), e))

def LB.c3w(-w: Bk.Term, +a3: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32, +ew: {Pg.Program.unword(8n, w) == CW(8n, m, Fd(2n, m, Fd(3n, m, c))) : Maybe<&2, Word(8n)>},
  x: SpecM(T.tm.of(1n+a3, m, ks, img, Fd(2n, m, Fd(3n, m, Fd(3n, m, c)))), rest => {U.c4(CW(8n, m, Fd(2n, m, Fd(3n, m, c))), rest) == CU(4n+a3, m, S.c3(CW(8n, m, Fd(2n, m, Fd(3n, m, c))), Fd(2n, m, Fd(3n, m, Fd(3n, m, c))))) : Maybe<&2, List<&2, Word(8n)>>})) ->
  SpecM(T.tm.of(1n+a3, m, ks, img, Fd(2n, m, Fd(3n, m, Fd(3n, m, c)))), rest => {U.c4(Pg.Program.unword(8n, w), rest) == CU(4n+a3, m, S.c3(CW(8n, m, Fd(2n, m, Fd(3n, m, c))), Fd(2n, m, Fd(3n, m, Fd(3n, m, c))))) : Maybe<&2, List<&2, Word(8n)>>}):
  %Equal.sym(Maybe<&2, Word(8n)>, Pg.Program.unword(8n, w), CW(8n, m, Fd(2n, m, Fd(3n, m, c))), ew) :
    SpecM(T.tm.of(1n+a3, m, ks, img, Fd(2n, m, Fd(3n, m, Fd(3n, m, c)))), rest => {U.c4(_, rest) == CU(4n+a3, m, S.c3(CW(8n, m, Fd(2n, m, Fd(3n, m, c))), Fd(2n, m, Fd(3n, m, Fd(3n, m, c))))) : Maybe<&2, List<&2, Word(8n)>>})
  x

def LB.c3(bu: Bool, +a3: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32, +hokx: {ok(2n+a3, m, ks, img, Fd(2n, m, Fd(3n, m, c)), im, fs, nx) == True{} : Bool}, +hokr: {ok(1n+a3, m, ks, img, Fd(2n, m, Fd(3n, m, Fd(3n, m, c))), im, fs, nx) == True{} : Bool}, ih: LB.IH(1n+a3, m, ks, img, im, fs, nx)) ->
  SpecM(T.tm.of(1n+a3, m, ks, img, Fd(2n, m, Fd(3n, m, Fd(3n, m, c)))), rest => SpecM(T.tm.of(2n+a3, m, ks, img, Fd(2n, m, Fd(3n, m, c))), x => {U.c3(bu, x, rest) == CU(4n+a3, m, S.c2(bu, m, Fd(2n, m, Fd(3n, m, c)), Fd(2n, m, Fd(3n, m, Fd(3n, m, c))))) : Maybe<&2, List<&2, Word(8n)>>})):
  match bu:
    case False{}:
      SpecM.all(T.tm.of(1n+a3, m, ks, img, Fd(2n, m, Fd(3n, m, Fd(3n, m, c)))), rest => SpecM(T.tm.of(2n+a3, m, ks, img, Fd(2n, m, Fd(3n, m, c))), x => {U.c3(False{}, x, rest) == CU(4n+a3, m, S.c2(False{}, m, Fd(2n, m, Fd(3n, m, c)), Fd(2n, m, Fd(3n, m, Fd(3n, m, c))))) : Maybe<&2, List<&2, Word(8n)>>}),
        rest => SpecM.all(T.tm.of(2n+a3, m, ks, img, Fd(2n, m, Fd(3n, m, c))), x => {U.c3(False{}, x, rest) == CU(4n+a3, m, S.c2(False{}, m, Fd(2n, m, Fd(3n, m, c)), Fd(2n, m, Fd(3n, m, Fd(3n, m, c))))) : Maybe<&2, List<&2, Word(8n)>>}, x => Equal.sym(Maybe<&2, List<&2, Word(8n)>>, CU(1n+3n+a3, m, SR.done{None{}}), None{}, CUd(3n+a3, m, None{}))))
    case True{}:
      SpecM.swap(T.tm.of(1n+a3, m, ks, img, Fd(2n, m, Fd(3n, m, Fd(3n, m, c)))), T.tm.of(2n+a3, m, ks, img, Fd(2n, m, Fd(3n, m, c))), rest => x => {U.c3(True{}, x, rest) == CU(4n+a3, m, S.c2(True{}, m, Fd(2n, m, Fd(3n, m, c)), Fd(2n, m, Fd(3n, m, Fd(3n, m, c))))) : Maybe<&2, List<&2, Word(8n)>>},
        SpecM.map(T.tm.of(2n+a3, m, ks, img, Fd(2n, m, Fd(3n, m, c))), x => {Pg.Program.unword(8n, x) == CW(8n, m, Fd(2n, m, Fd(3n, m, c))) : Maybe<&2, Word(8n)>},
          x => SpecM(T.tm.of(1n+a3, m, ks, img, Fd(2n, m, Fd(3n, m, Fd(3n, m, c)))), rest => {U.c3(True{}, x, rest) == CU(4n+a3, m, S.c2(True{}, m, Fd(2n, m, Fd(3n, m, c)), Fd(2n, m, Fd(3n, m, Fd(3n, m, c))))) : Maybe<&2, List<&2, Word(8n)>>}),
          WB(8n, 2n+a3, m, ks, img, Fd(2n, m, Fd(3n, m, c)), im, fs, nx, hokx),
          x => ex => LB.c3w(x, a3, m, ks, img, c, im, fs, nx, ex, LB.c4(CW(8n, m, Fd(2n, m, Fd(3n, m, c))), a3, m, ks, img, c, im, fs, nx, hokr, ih))))

def LB.c2k(+k: List<&2, Word(8n)>, +a3: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32, +hokx: {ok(2n+a3, m, ks, img, Fd(2n, m, Fd(3n, m, c)), im, fs, nx) == True{} : Bool}, +hokr: {ok(1n+a3, m, ks, img, Fd(2n, m, Fd(3n, m, Fd(3n, m, c))), im, fs, nx) == True{} : Bool}, +hokz: {ok(1n+a3, m, ks, img, Fd(3n, m, Fd(3n, m, Fd(3n, m, c))), im, fs, nx) == True{} : Bool},
  +eL: {Lm(m, Fd(3n, m, Fd(3n, m, Fd(3n, m, c)))) == True{} : Bool}, +ek: {T.tm.name(ks, Fd(2n, m, Fd(3n, m, Fd(3n, m, Fd(3n, m, c))))) == Some{k} : Maybe<&2, List<&2, Word(8n)>>}, ih: LB.IH(1n+a3, m, ks, img, im, fs, nx)) ->
  SpecM(T.tm.of(1n+a3, m, ks, img, Fd(2n, m, Fd(3n, m, Fd(3n, m, c)))), rest => SpecM(T.tm.of(2n+a3, m, ks, img, Fd(2n, m, Fd(3n, m, c))), x => {U.c2(x, rest, Some{k}) == CU(4n+a3, m, S.c2(Bool.and(True{}, U32.is_eq(Fd(2n, m, Fd(3n, m, Fd(3n, m, Fd(3n, m, c)))), 0)), m, Fd(2n, m, Fd(3n, m, c)), Fd(2n, m, Fd(3n, m, Fd(3n, m, c))))) : Maybe<&2, List<&2, Word(8n)>>})):
  %Equal.sym(Bool, Sd.Name.is_eq(k, Pg.Program.name.unit()), U32.is_eq(Fd(2n, m, Fd(3n, m, Fd(3n, m, Fd(3n, m, c)))), 0), kn0(Fd(2n, m, Fd(3n, m, Fd(3n, m, Fd(3n, m, c)))), k, LK(a3, m, ks, img, Fd(3n, m, Fd(3n, m, Fd(3n, m, c))), im, fs, nx, hokz, eL, k, ek))) :
    SpecM(T.tm.of(1n+a3, m, ks, img, Fd(2n, m, Fd(3n, m, Fd(3n, m, c)))), rest => SpecM(T.tm.of(2n+a3, m, ks, img, Fd(2n, m, Fd(3n, m, c))), x => {U.c3(_, x, rest) == CU(4n+a3, m, S.c2(U32.is_eq(Fd(2n, m, Fd(3n, m, Fd(3n, m, Fd(3n, m, c)))), 0), m, Fd(2n, m, Fd(3n, m, c)), Fd(2n, m, Fd(3n, m, Fd(3n, m, c))))) : Maybe<&2, List<&2, Word(8n)>>}))
  LB.c3(U32.is_eq(Fd(2n, m, Fd(3n, m, Fd(3n, m, Fd(3n, m, c)))), 0), a3, m, ks, img, c, im, fs, nx, hokx, hokr, ih)

def LB.c2(bz: Bool, +a3: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32, +hokx: {ok(2n+a3, m, ks, img, Fd(2n, m, Fd(3n, m, c)), im, fs, nx) == True{} : Bool}, +hokr: {ok(1n+a3, m, ks, img, Fd(2n, m, Fd(3n, m, Fd(3n, m, c))), im, fs, nx) == True{} : Bool}, +hokz: {ok(1n+a3, m, ks, img, Fd(3n, m, Fd(3n, m, Fd(3n, m, c))), im, fs, nx) == True{} : Bool},
  +e: {Lm(m, Fd(3n, m, Fd(3n, m, Fd(3n, m, c)))) == bz : Bool}, ih: LB.IH(1n+a3, m, ks, img, im, fs, nx)) ->
  SpecM(T.tm.of(1n+a3, m, ks, img, Fd(3n, m, Fd(3n, m, Fd(3n, m, c)))), z => SpecM(T.tm.of(1n+a3, m, ks, img, Fd(2n, m, Fd(3n, m, Fd(3n, m, c)))), rest => SpecM(T.tm.of(2n+a3, m, ks, img, Fd(2n, m, Fd(3n, m, c))), x =>
    {U.c2(x, rest, VL(z)) == CU(4n+a3, m, S.c2(Bool.and(bz, U32.is_eq(Fd(2n, m, Fd(3n, m, Fd(3n, m, Fd(3n, m, c)))), 0)), m, Fd(2n, m, Fd(3n, m, c)), Fd(2n, m, Fd(3n, m, Fd(3n, m, c))))) : Maybe<&2, List<&2, Word(8n)>>}))):
  match bz:
    case False{}:
      cellNotL(a3, m, ks, img, Fd(3n, m, Fd(3n, m, Fd(3n, m, c))), im, fs, nx, z => SpecM(T.tm.of(1n+a3, m, ks, img, Fd(2n, m, Fd(3n, m, Fd(3n, m, c)))), rest => SpecM(T.tm.of(2n+a3, m, ks, img, Fd(2n, m, Fd(3n, m, c))), x =>
          {U.c2(x, rest, VL(z)) == CU(4n+a3, m, S.c2(Bool.and(False{}, U32.is_eq(Fd(2n, m, Fd(3n, m, Fd(3n, m, Fd(3n, m, c)))), 0)), m, Fd(2n, m, Fd(3n, m, c)), Fd(2n, m, Fd(3n, m, Fd(3n, m, c))))) : Maybe<&2, List<&2, Word(8n)>>})), e, hokz,
        v => ev => SpecM.all(T.tm.of(1n+a3, m, ks, img, Fd(2n, m, Fd(3n, m, Fd(3n, m, c)))), rest => SpecM(T.tm.of(2n+a3, m, ks, img, Fd(2n, m, Fd(3n, m, c))), x =>
            {U.c2(x, rest, VL(v)) == CU(4n+a3, m, S.c2(Bool.and(False{}, U32.is_eq(Fd(2n, m, Fd(3n, m, Fd(3n, m, Fd(3n, m, c)))), 0)), m, Fd(2n, m, Fd(3n, m, c)), Fd(2n, m, Fd(3n, m, Fd(3n, m, c))))) : Maybe<&2, List<&2, Word(8n)>>}),
          rest => SpecM.all(T.tm.of(2n+a3, m, ks, img, Fd(2n, m, Fd(3n, m, c))), x => {U.c2(x, rest, VL(v)) == CU(4n+a3, m, S.c2(Bool.and(False{}, U32.is_eq(Fd(2n, m, Fd(3n, m, Fd(3n, m, Fd(3n, m, c)))), 0)), m, Fd(2n, m, Fd(3n, m, c)), Fd(2n, m, Fd(3n, m, Fd(3n, m, c))))) : Maybe<&2, List<&2, Word(8n)>>},
            x => Equal.trans(Maybe<&2, List<&2, Word(8n)>>, U.c2(x, rest, VL(v)), None{}, CU(4n+a3, m, SR.done{None{}}), Equal.cong(Maybe<&2, List<&2, Word(8n)>>, Maybe<&2, List<&2, Word(8n)>>, mm => U.c2(x, rest, mm), VL(v), None{}, ev), Equal.sym(Maybe<&2, List<&2, Word(8n)>>, CU(1n+3n+a3, m, SR.done{None{}}), None{}, CUd(3n+a3, m, None{}))))))
    case True{}:
      cellLab(a3, m, ks, img, Fd(3n, m, Fd(3n, m, Fd(3n, m, c))), z => SpecM(T.tm.of(1n+a3, m, ks, img, Fd(2n, m, Fd(3n, m, Fd(3n, m, c)))), rest => SpecM(T.tm.of(2n+a3, m, ks, img, Fd(2n, m, Fd(3n, m, c))), x =>
          {U.c2(x, rest, VL(z)) == CU(4n+a3, m, S.c2(Bool.and(True{}, U32.is_eq(Fd(2n, m, Fd(3n, m, Fd(3n, m, Fd(3n, m, c)))), 0)), m, Fd(2n, m, Fd(3n, m, c)), Fd(2n, m, Fd(3n, m, Fd(3n, m, c))))) : Maybe<&2, List<&2, Word(8n)>>})), e,
        k => ek => LB.c2k(k, a3, m, ks, img, c, im, fs, nx, hokx, hokr, hokz, e, ek, ih))

def LB.c1(by: Bool, +a2: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32, +hokx: {ok(1n+a2, m, ks, img, Fd(2n, m, Fd(3n, m, c)), im, fs, nx) == True{} : Bool}, +hoky: {ok(1n+a2, m, ks, img, Fd(3n, m, Fd(3n, m, c)), im, fs, nx) == True{} : Bool}, +e: {Pm(m, Fd(3n, m, Fd(3n, m, c))) == by : Bool}, ih: LB.IH(a2, m, ks, img, im, fs, nx)) ->
  SpecM(T.tm.of(1n+a2, m, ks, img, Fd(3n, m, Fd(3n, m, c))), yy => SpecM(T.tm.of(1n+a2, m, ks, img, Fd(2n, m, Fd(3n, m, c))), x => {U.c1(x, V1(yy)) == CU(3n+a2, m, S.c1(by, m, Fd(2n, m, Fd(3n, m, c)), Fd(3n, m, Fd(3n, m, c)))) : Maybe<&2, List<&2, Word(8n)>>})):
  match by:
    case False{}:
      cellNotT1(a2, m, ks, img, Fd(3n, m, Fd(3n, m, c)), im, fs, nx, yy => SpecM(T.tm.of(1n+a2, m, ks, img, Fd(2n, m, Fd(3n, m, c))), x => {U.c1(x, V1(yy)) == CU(3n+a2, m, S.c1(False{}, m, Fd(2n, m, Fd(3n, m, c)), Fd(3n, m, Fd(3n, m, c)))) : Maybe<&2, List<&2, Word(8n)>>}), e, hoky,
        v => ev => SpecM.all(T.tm.of(1n+a2, m, ks, img, Fd(2n, m, Fd(3n, m, c))), x => {U.c1(x, V1(v)) == CU(3n+a2, m, S.c1(False{}, m, Fd(2n, m, Fd(3n, m, c)), Fd(3n, m, Fd(3n, m, c)))) : Maybe<&2, List<&2, Word(8n)>>},
          x => Equal.trans(Maybe<&2, List<&2, Word(8n)>>, U.c1(x, V1(v)), None{}, CU(3n+a2, m, SR.done{None{}}), Equal.cong(Maybe<&2, TP>, Maybe<&2, List<&2, Word(8n)>>, mm => U.c1(x, mm), V1(v), None{}, ev), Equal.sym(Maybe<&2, List<&2, Word(8n)>>, CU(1n+2n+a2, m, SR.done{None{}}), None{}, CUd(2n+a2, m, None{})))))
    case True{}:
      match a2:
        case 0n:
          cellT1(0n, m, ks, img, Fd(3n, m, Fd(3n, m, c)), yy => SpecM(T.tm.of(1n+0n, m, ks, img, Fd(2n, m, Fd(3n, m, c))), x => {U.c1(x, V1(yy)) == CU(3n, m, S.c1(True{}, m, Fd(2n, m, Fd(3n, m, c)), Fd(3n, m, Fd(3n, m, c)))) : Maybe<&2, List<&2, Word(8n)>>}), e, Unit{})
        case 1n+a3:
          cellT1(1n+a3, m, ks, img, Fd(3n, m, Fd(3n, m, c)), yy => SpecM(T.tm.of(2n+a3, m, ks, img, Fd(2n, m, Fd(3n, m, c))), x => {U.c1(x, V1(yy)) == CU(4n+a3, m, S.c1(True{}, m, Fd(2n, m, Fd(3n, m, c)), Fd(3n, m, Fd(3n, m, c)))) : Maybe<&2, List<&2, Word(8n)>>}), e,
            SpecM.swap(T.tm.of(1n+a3, m, ks, img, Fd(2n, m, Fd(3n, m, Fd(3n, m, c)))), T.tm.of(1n+a3, m, ks, img, Fd(3n, m, Fd(3n, m, Fd(3n, m, c)))),
              rest => z => SpecM(T.tm.of(2n+a3, m, ks, img, Fd(2n, m, Fd(3n, m, c))), x => {U.c1(x, V1(Bk.Term.Tup{Bk.Quan.Q1{}, rest, z})) == CU(4n+a3, m, S.c1(True{}, m, Fd(2n, m, Fd(3n, m, c)), Fd(3n, m, Fd(3n, m, c)))) : Maybe<&2, List<&2, Word(8n)>>}),
              LB.c2(Lm(m, Fd(3n, m, Fd(3n, m, Fd(3n, m, c)))), a3, m, ks, img, c, im, fs, nx, hokx, ok.l(1n+a3, m, ks, img, Fd(3n, m, Fd(3n, m, c)), im, fs, nx, hoky, e), ok.r(1n+a3, m, ks, img, Fd(3n, m, Fd(3n, m, c)), im, fs, nx, hoky, e), {==}, ih)))

def LB.c0(b0: Bool, +a1: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32, +hokb: {ok(1n+a1, m, ks, img, Fd(3n, m, c), im, fs, nx) == True{} : Bool}, +e: {Pm(m, Fd(3n, m, c)) == b0 : Bool}, ih: LB.IH(Pr(a1), m, ks, img, im, fs, nx)) ->
  SpecM(T.tm.of(1n+a1, m, ks, img, Fd(3n, m, c)), y => {U.con(V1(y)) == CU(2n+a1, m, S.c0(b0, m, Fd(3n, m, c))) : Maybe<&2, List<&2, Word(8n)>>}):
  match b0:
    case False{}:
      cellNotT1(a1, m, ks, img, Fd(3n, m, c), im, fs, nx, y => {U.con(V1(y)) == CU(2n+a1, m, S.c0(False{}, m, Fd(3n, m, c))) : Maybe<&2, List<&2, Word(8n)>>}, e, hokb,
        v => ev => Equal.trans(Maybe<&2, List<&2, Word(8n)>>, U.con(V1(v)), None{}, CU(2n+a1, m, SR.done{None{}}), Equal.cong(Maybe<&2, TP>, Maybe<&2, List<&2, Word(8n)>>, mm => U.con(mm), V1(v), None{}, ev), Equal.sym(Maybe<&2, List<&2, Word(8n)>>, CU(1n+1n+a1, m, SR.done{None{}}), None{}, CUd(1n+a1, m, None{}))))
    case True{}:
      match a1:
        case 0n:
          cellT1(0n, m, ks, img, Fd(3n, m, c), y => {U.con(V1(y)) == CU(2n, m, S.c0(True{}, m, Fd(3n, m, c))) : Maybe<&2, List<&2, Word(8n)>>}, e, Unit{})
        case 1n+a2:
          cellT1(1n+a2, m, ks, img, Fd(3n, m, c), y => {U.con(V1(y)) == CU(3n+a2, m, S.c0(True{}, m, Fd(3n, m, c))) : Maybe<&2, List<&2, Word(8n)>>}, e,
            SpecM.swap(T.tm.of(1n+a2, m, ks, img, Fd(2n, m, Fd(3n, m, c))), T.tm.of(1n+a2, m, ks, img, Fd(3n, m, Fd(3n, m, c))), x => yy => {U.con(V1(Bk.Term.Tup{Bk.Quan.Q1{}, x, yy})) == CU(3n+a2, m, S.c0(True{}, m, Fd(3n, m, c))) : Maybe<&2, List<&2, Word(8n)>>},
              LB.c1(Pm(m, Fd(3n, m, Fd(3n, m, c))), a2, m, ks, img, c, im, fs, nx, ok.l(1n+a2, m, ks, img, Fd(3n, m, c), im, fs, nx, hokb, e), ok.r(1n+a2, m, ks, img, Fd(3n, m, c), im, fs, nx, hokb, e), {==}, ih)))

def LB.nilv(x: Bool, +a: Nat, +m: Cr.Cir.Cells) -> {Pg.Program.unbytes.nil(x) == CU(1n+a, m, S.nil(x)) : Maybe<&2, List<&2, Word(8n)>>}:
  match x:
    case True{}:
      Equal.sym(Maybe<&2, List<&2, Word(8n)>>, CU(1n+a, m, SR.done{Some{Nil{}}}), Some{Nil{}}, CUd(a, m, Some{Nil{}}))
    case False{}:
      Equal.sym(Maybe<&2, List<&2, Word(8n)>>, CU(1n+a, m, SR.done{None{}}), None{}, CUd(a, m, None{}))

def LB.nilk(+k: List<&2, Word(8n)>, +a1: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32, +hok3: {ok(1n+a1, m, ks, img, Fd(3n, m, c), im, fs, nx) == True{} : Bool}, +eL: {Lm(m, Fd(3n, m, c)) == True{} : Bool},
  +ek: {T.tm.name(ks, Fd(2n, m, Fd(3n, m, c))) == Some{k} : Maybe<&2, List<&2, Word(8n)>>}) ->
  {U.nil(Some{k}) == CU(2n+a1, m, S.nil(Bool.and(True{}, U32.is_eq(Fd(2n, m, Fd(3n, m, c)), 0)))) : Maybe<&2, List<&2, Word(8n)>>}:
  %Equal.sym(Bool, Sd.Name.is_eq(k, Pg.Program.name.unit()), U32.is_eq(Fd(2n, m, Fd(3n, m, c)), 0), kn0(Fd(2n, m, Fd(3n, m, c)), k, LK(a1, m, ks, img, Fd(3n, m, c), im, fs, nx, hok3, eL, k, ek))) :
    {Pg.Program.unbytes.nil(_) == CU(2n+a1, m, S.nil(U32.is_eq(Fd(2n, m, Fd(3n, m, c)), 0))) : Maybe<&2, List<&2, Word(8n)>>}
  LB.nilv(U32.is_eq(Fd(2n, m, Fd(3n, m, c)), 0), 1n+a1, m)

def LB.nil(bu: Bool, +a1: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32, +hok3: {ok(1n+a1, m, ks, img, Fd(3n, m, c), im, fs, nx) == True{} : Bool}, +e: {Lm(m, Fd(3n, m, c)) == bu : Bool}) ->
  SpecM(T.tm.of(1n+a1, m, ks, img, Fd(3n, m, c)), y => {U.nil(VL(y)) == CU(2n+a1, m, S.nil(Bool.and(bu, U32.is_eq(Fd(2n, m, Fd(3n, m, c)), 0)))) : Maybe<&2, List<&2, Word(8n)>>}):
  match bu:
    case False{}:
      cellNotL(a1, m, ks, img, Fd(3n, m, c), im, fs, nx, y => {U.nil(VL(y)) == CU(2n+a1, m, S.nil(Bool.and(False{}, U32.is_eq(Fd(2n, m, Fd(3n, m, c)), 0)))) : Maybe<&2, List<&2, Word(8n)>>}, e, hok3,
        v => ev => Equal.trans(Maybe<&2, List<&2, Word(8n)>>, U.nil(VL(v)), None{}, CU(2n+a1, m, SR.done{None{}}), Equal.cong(Maybe<&2, List<&2, Word(8n)>>, Maybe<&2, List<&2, Word(8n)>>, mm => U.nil(mm), VL(v), None{}, ev), Equal.sym(Maybe<&2, List<&2, Word(8n)>>, CU(1n+1n+a1, m, SR.done{None{}}), None{}, CUd(1n+a1, m, None{}))))
    case True{}:
      cellLab(a1, m, ks, img, Fd(3n, m, c), y => {U.nil(VL(y)) == CU(2n+a1, m, S.nil(Bool.and(True{}, U32.is_eq(Fd(2n, m, Fd(3n, m, c)), 0)))) : Maybe<&2, List<&2, Word(8n)>>}, e,
        k => ek => LB.nilk(k, a1, m, ks, img, c, im, fs, nx, hok3, e, ek))

def LB.w(isnil: Bool, iscon: Bool, +a1: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32, +hok3: {ok(1n+a1, m, ks, img, Fd(3n, m, c), im, fs, nx) == True{} : Bool}, ih: LB.IH(Pr(a1), m, ks, img, im, fs, nx)) ->
  SpecM(T.tm.of(1n+a1, m, ks, img, Fd(3n, m, c)), y => {U.k(isnil, iscon, y) == CU(2n+a1, m, S.w(isnil, iscon, m, c)) : Maybe<&2, List<&2, Word(8n)>>}):
  match isnil:
    case True{}:
      LB.nil(Lm(m, Fd(3n, m, c)), a1, m, ks, img, c, im, fs, nx, hok3, {==})
    case False{}:
      match iscon:
        case False{}:
          SpecM.all(T.tm.of(1n+a1, m, ks, img, Fd(3n, m, c)), y => {U.k(False{}, False{}, y) == CU(2n+a1, m, S.w(False{}, False{}, m, c)) : Maybe<&2, List<&2, Word(8n)>>}, y => Equal.sym(Maybe<&2, List<&2, Word(8n)>>, CU(1n+1n+a1, m, SR.done{None{}}), None{}, CUd(1n+a1, m, None{})))
        case True{}:
          LB.c0(Pm(m, Fd(3n, m, c)), a1, m, ks, img, c, im, fs, nx, hok3, {==}, ih)

def LB.k0(+k: List<&2, Word(8n)>, +a1: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32, +hok2: {ok(1n+a1, m, ks, img, Fd(2n, m, c), im, fs, nx) == True{} : Bool}, +hok3: {ok(1n+a1, m, ks, img, Fd(3n, m, c), im, fs, nx) == True{} : Bool}, +eL: {Lm(m, Fd(2n, m, c)) == True{} : Bool},
  +ek: {T.tm.name(ks, Fd(2n, m, Fd(2n, m, c))) == Some{k} : Maybe<&2, List<&2, Word(8n)>>}, ih: LB.IH(Pr(a1), m, ks, img, im, fs, nx)) ->
  SpecM(T.tm.of(1n+a1, m, ks, img, Fd(3n, m, c)), y => {U.a(Some{k}, y) == CU(2n+a1, m, S.l(True{}, m, c)) : Maybe<&2, List<&2, Word(8n)>>}):
  +h = LK(a1, m, ks, img, Fd(2n, m, c), im, fs, nx, hok2, eL, k, ek)
  %Equal.sym(Bool, Sd.Name.is_eq(k, Pg.Program.name.nil()), U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 1), kn1(Fd(2n, m, Fd(2n, m, c)), k, h)) :
    SpecM(T.tm.of(1n+a1, m, ks, img, Fd(3n, m, c)), y => {U.k(_, Sd.Name.is_eq(k, Pg.Program.name.con()), y) == CU(2n+a1, m, S.w(U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 1), U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 2), m, c)) : Maybe<&2, List<&2, Word(8n)>>})
  %Equal.sym(Bool, Sd.Name.is_eq(k, Pg.Program.name.con()), U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 2), kn2(Fd(2n, m, Fd(2n, m, c)), k, h)) :
    SpecM(T.tm.of(1n+a1, m, ks, img, Fd(3n, m, c)), y => {U.k(U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 1), _, y) == CU(2n+a1, m, S.w(U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 1), U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 2), m, c)) : Maybe<&2, List<&2, Word(8n)>>})
  LB.w(U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 1), U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 2), a1, m, ks, img, c, im, fs, nx, hok3, ih)

def LB.l(bl: Bool, +a1: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32, +hok2: {ok(1n+a1, m, ks, img, Fd(2n, m, c), im, fs, nx) == True{} : Bool}, +hok3: {ok(1n+a1, m, ks, img, Fd(3n, m, c), im, fs, nx) == True{} : Bool}, +e: {Lm(m, Fd(2n, m, c)) == bl : Bool}, ih: LB.IH(Pr(a1), m, ks, img, im, fs, nx)) ->
  SpecM(T.tm.of(1n+a1, m, ks, img, Fd(2n, m, c)), x => SpecM(T.tm.of(1n+a1, m, ks, img, Fd(3n, m, c)), y => {U.a(VL(x), y) == CU(2n+a1, m, S.l(bl, m, c)) : Maybe<&2, List<&2, Word(8n)>>})):
  match bl:
    case False{}:
      cellNotL(a1, m, ks, img, Fd(2n, m, c), im, fs, nx, x => SpecM(T.tm.of(1n+a1, m, ks, img, Fd(3n, m, c)), y => {U.a(VL(x), y) == CU(2n+a1, m, S.l(False{}, m, c)) : Maybe<&2, List<&2, Word(8n)>>}), e, hok2,
        v => ev => SpecM.all(T.tm.of(1n+a1, m, ks, img, Fd(3n, m, c)), y => {U.a(VL(v), y) == CU(2n+a1, m, S.l(False{}, m, c)) : Maybe<&2, List<&2, Word(8n)>>},
          y => Equal.trans(Maybe<&2, List<&2, Word(8n)>>, U.a(VL(v), y), None{}, CU(2n+a1, m, SR.done{None{}}), Equal.cong(Maybe<&2, List<&2, Word(8n)>>, Maybe<&2, List<&2, Word(8n)>>, mm => U.a(mm, y), VL(v), None{}, ev), Equal.sym(Maybe<&2, List<&2, Word(8n)>>, CU(1n+1n+a1, m, SR.done{None{}}), None{}, CUd(1n+a1, m, None{})))))
    case True{}:
      cellLab(a1, m, ks, img, Fd(2n, m, c), x => SpecM(T.tm.of(1n+a1, m, ks, img, Fd(3n, m, c)), y => {U.a(VL(x), y) == CU(2n+a1, m, S.l(True{}, m, c)) : Maybe<&2, List<&2, Word(8n)>>}), e,
        k => ek => LB.k0(k, a1, m, ks, img, c, im, fs, nx, hok2, hok3, e, ek, ih))

def LB.p(b: Bool, +a: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32, +hok: {ok(1n+a, m, ks, img, c, im, fs, nx) == True{} : Bool}, +eb: {Pm(m, c) == b : Bool}, ih: LB.IH(Pr(Pr(a)), m, ks, img, im, fs, nx)) ->
  SpecM(T.tm.of(1n+a, m, ks, img, c), t => {U.r(V1(t)) == CU(1n+a, m, S.p(b, m, c)) : Maybe<&2, List<&2, Word(8n)>>}):
  match b:
    case False{}:
      cellNotT1(a, m, ks, img, c, im, fs, nx, t => {U.r(V1(t)) == CU(1n+a, m, S.p(False{}, m, c)) : Maybe<&2, List<&2, Word(8n)>>}, eb, hok,
        v => ev => Equal.trans(Maybe<&2, List<&2, Word(8n)>>, U.r(V1(v)), None{}, CU(1n+a, m, SR.done{None{}}), Equal.cong(Maybe<&2, TP>, Maybe<&2, List<&2, Word(8n)>>, mm => U.r(mm), V1(v), None{}, ev), Equal.sym(Maybe<&2, List<&2, Word(8n)>>, CU(1n+a, m, SR.done{None{}}), None{}, CUd(a, m, None{}))))
    case True{}:
      match a:
        case 0n:
          cellT1(0n, m, ks, img, c, t => {U.r(V1(t)) == CU(1n, m, S.p(True{}, m, c)) : Maybe<&2, List<&2, Word(8n)>>}, eb, Unit{})
        case 1n+a1:
          cellT1(1n+a1, m, ks, img, c, t => {U.r(V1(t)) == CU(2n+a1, m, S.p(True{}, m, c)) : Maybe<&2, List<&2, Word(8n)>>}, eb,
            LB.l(Lm(m, Fd(2n, m, c)), a1, m, ks, img, c, im, fs, nx, ok.l(1n+a1, m, ks, img, c, im, fs, nx, hok, eb), ok.r(1n+a1, m, ks, img, c, im, fs, nx, hok, eb), {==}, ih))

# the term of the list cell c is the list that CU reads
def LB(+n: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32, +hok: {ok(n, m, ks, img, c, im, fs, nx) == True{} : Bool}) ->
  SpecM(T.tm.of(n, m, ks, img, c), t => {Pg.Program.unbytes(t) == CU(n, m, Step(m, c)) : Maybe<&2, List<&2, Word(8n)>>}):
  match n:
    case 0n:
      Unit{}
    case 1n+a:
      match a:
        case 0n:
          SpecM.map(T.tm.of(1n, m, ks, img, c), t => {U(t) == CU(1n, m, Step(m, c)) : Maybe<&2, List<&2, Word(8n)>>}, t => {Pg.Program.unbytes(t) == CU(1n, m, Step(m, c)) : Maybe<&2, List<&2, Word(8n)>>},
            LB.p(Pm(m, c), 0n, m, ks, img, c, im, fs, nx, hok, {==}, rc2 => h => Unit{}),
            t => e => Equal.trans(Maybe<&2, List<&2, Word(8n)>>, Pg.Program.unbytes(t), U(t), CU(1n, m, Step(m, c)), UE(t), e))
        case 1n+a1:
          match a1:
            case 0n:
              SpecM.map(T.tm.of(2n, m, ks, img, c), t => {U(t) == CU(2n, m, Step(m, c)) : Maybe<&2, List<&2, Word(8n)>>}, t => {Pg.Program.unbytes(t) == CU(2n, m, Step(m, c)) : Maybe<&2, List<&2, Word(8n)>>},
                LB.p(Pm(m, c), 1n, m, ks, img, c, im, fs, nx, hok, {==}, rc2 => h => Unit{}),
                t => e => Equal.trans(Maybe<&2, List<&2, Word(8n)>>, Pg.Program.unbytes(t), U(t), CU(2n, m, Step(m, c)), UE(t), e))
            case 1n+a2:
              SpecM.map(T.tm.of(3n+a2, m, ks, img, c), t => {U(t) == CU(3n+a2, m, Step(m, c)) : Maybe<&2, List<&2, Word(8n)>>}, t => {Pg.Program.unbytes(t) == CU(3n+a2, m, Step(m, c)) : Maybe<&2, List<&2, Word(8n)>>},
                LB.p(Pm(m, c), 2n+a2, m, ks, img, c, im, fs, nx, hok, {==}, rc2 => h => LB(a2, m, ks, img, rc2, im, fs, nx, h)),
                t => e => Equal.trans(Maybe<&2, List<&2, Word(8n)>>, Pg.Program.unbytes(t), U(t), CU(3n+a2, m, Step(m, c)), UE(t), e))

# M.out gives the bytes of the focus' term
# ----------------------------------------

# xs reversed onto acc is xs reversed, then acc
def rev_go(xs: List<&2, Word(8n)>, +ys: List<&2, Word(8n)>, +acc: List<&2, Word(8n)>) ->
  {List.reverse.go(&2, Word(8n), xs, List.append(&2, Word(8n), ys, acc)) == List.append(&2, Word(8n), List.reverse.go(&2, Word(8n), xs, ys), acc) : List<&2, Word(8n)>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      rev_go(t, Con{h, ys}, acc)

def rev_app(+xs: List<&2, Word(8n)>, +acc: List<&2, Word(8n)>) ->
  {List.reverse.go(&2, Word(8n), xs, acc) == List.append(&2, Word(8n), List.reverse(&2, Word(8n), xs), acc) : List<&2, Word(8n)>}:
  rev_go(xs, Nil{}, acc)

# a halt with the status s in the state st, by the bytes r: with 0 and the
# bytes of r out (the output holds them reversed, in front of out0; outn0
# gains one for each), or with 2 when r is none
def Gives.halt(r: Maybe<&2, List<&2, Word(8n)>>, out0: List<&2, Word(8n)>, outn0: U32, s: U32, st: Cr.Cir.State) -> Type:
  match r:
    case Some{bs}:
      {s == 0 : U32} & ({St.out(st) == List.append(&2, Word(8n), List.reverse(&2, Word(8n), bs), out0) : List<&2, Word(8n)>} & {St.outn(st) == Incs(bs, outn0) : U32})
    case None{}:
      {s == 2 : U32}

# the run o halts as Gives.halt says, or runs out of memory
def Gives(o: Cr.Cir.Out, r: Maybe<&2, List<&2, Word(8n)>>, out0: List<&2, Word(8n)>, outn0: U32, O: Type) -> Type:
  match o:
    case Cr.Cir.Out.next{_}:
      Empty
    case Cr.Cir.Out.halt{s, st}:
      Gives.halt(r, out0, outn0, s, st)
    case Cr.Cir.Out.out_of_memory{}:
      O
    case Cr.Cir.Out.trap{}:
      Empty
    case Cr.Cir.Out.not_done{}:
      Empty

def Gives.fin(r: Maybe<&2, List<&2, Word(8n)>>, +out0: List<&2, Word(8n)>, +outn0: U32, +s: U32, +st: Cr.Cir.State, h: Fin(r, out0, outn0, s, st)) ->
  Gives.halt(r, out0, outn0, s, st):
  match r:
    case Some{+bs}:
      (e0, rest) = h
      (eo, en) = rest
      (e0, (Equal.trans(List<&2, Word(8n)>, St.out(st), List.reverse.go(&2, Word(8n), bs, out0), List.append(&2, Word(8n), List.reverse(&2, Word(8n), bs), out0), eo,
        rev_app(bs, out0)), en))
    case None{}:
      h

def Gives.of(o: Cr.Cir.Out, r: Maybe<&2, List<&2, Word(8n)>>, +out0: List<&2, Word(8n)>, +outn0: U32, -O: Type,
  h: Wp(o, st => Empty, s => st => Fin(r, out0, outn0, s, st), O)) -> Gives(o, r, out0, outn0, O):
  match o:
    case Cr.Cir.Out.next{st}:
      match h:
    case Cr.Cir.Out.halt{+s, +st}:
      Gives.fin(r, out0, outn0, s, st, h)
    case Cr.Cir.Out.out_of_memory{}:
      h
    case Cr.Cir.Out.trap{}:
      match h:
    case Cr.Cir.Out.not_done{}:
      match h:

# THE LEMMA, with the fuel 1 + f of n + 34 or more. The focus register of the
# state holds the cell c, whose term (with the fuel n of T.tm.of) is v; the
# state has the machine's 63 registers at least; and ok holds of c: every
# cell that the walk of M.out reads is one that Cir.is_cell accepts, a Ref or
# an Enu has an image's term that is no pair at quantity 1 nor label, and the
# number j of a label is one whose name in ks is the machine's name i (for i
# from 0 to 6: (), Nil, Con, WNil, WCon, True, False) exactly when j is
# i. Then M.out gives Program.unbytes(v) (Gives).
def out.run(+n: Nat, +f: Nat, +hF: PN.Le(Nat.add(n, 34n), 1n+f), +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fs: U32, +im: U32,
  +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +out: List<&2, Word(8n)>, +outn: U32, +c: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +v: Bk.Term,
  +hreg: {List.get(&2, U32, regs, Mc.R.focus()) == Some{c} : Maybe<&2, U32>},
  +hlen: {Nat.is_le(Mc.Mach.regs(), List.length(&2, U32, regs)) == True{} : Bool},
  +htm: {T.tm.of(n, m, ks, img, c) == Some{v} : Maybe<&2, Bk.Term>},
  +hok: {ok(n, m, ks, img, c, im, fs, nx) == True{} : Bool}) ->
  Gives(Cr.Cir.exec(1n+f, Mc.M.out(), Cr.Cir.State{regs, m, nx, fs, im, pg, lim, inp, out, outn}), Pg.Program.unbytes(v), out, outn, OBn(lim, nx, Nat.add(U32.to_nat(outn), n))):
  ev = Tr(Maybe<&2, Bk.Term>, r => SpecM(r, t => {Pg.Program.unbytes(t) == CU(n, m, Step(m, c)) : Maybe<&2, List<&2, Word(8n)>>}),
    T.tm.of(n, m, ks, img, c), Some{v}, htm, LB(n, m, ks, img, c, im, fs, nx, hok))
  Gives.of(Cr.Cir.exec(1n+f, Mc.M.out(), Cr.Cir.State{regs, m, nx, fs, im, pg, lim, inp, out, outn}), Pg.Program.unbytes(v), out, outn, OBn(lim, nx, Nat.add(U32.to_nat(outn), n)),
    Tr(Maybe<&2, List<&2, Word(8n)>>, r => Wp(Cr.Cir.exec(1n+f, Mc.M.out(), Cr.Cir.State{regs, m, nx, fs, im, pg, lim, inp, out, outn}), st => Empty,
        s => st => Fin(r, out, outn, s, st), OB(Cr.Cir.State{regs, m, nx, fs, im, pg, lim, inp, out, outn}, Nat.add(U32.to_nat(outn), n))),
      CU(n, m, Step(m, c)), Pg.Program.unbytes(v), Equal.sym(Maybe<&2, List<&2, Word(8n)>>, Pg.Program.unbytes(v), CU(n, m, Step(m, c)), ev),
      MOUT(n, f, hF, regs, m, nx, fs, im, pg, lim, inp, out, outn, c, ks, img, Nat.add(U32.to_nat(outn), n), hreg, hlen, hok,
        PN.le_refl(Nat.add(U32.to_nat(outn), n)))))

# THE LEMMA, for some fuel F (1 + n + 34)
def out.gives(+n: Nat, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fs: U32, +im: U32,
  +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +out: List<&2, Word(8n)>, +outn: U32, +c: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +v: Bk.Term,
  +hreg: {List.get(&2, U32, regs, Mc.R.focus()) == Some{c} : Maybe<&2, U32>},
  +hlen: {Nat.is_le(Mc.Mach.regs(), List.length(&2, U32, regs)) == True{} : Bool},
  +htm: {T.tm.of(n, m, ks, img, c) == Some{v} : Maybe<&2, Bk.Term>},
  +hok: {ok(n, m, ks, img, c, im, fs, nx) == True{} : Bool}) ->
  &F: Nat -> Gives(Cr.Cir.exec(F, Mc.M.out(), Cr.Cir.State{regs, m, nx, fs, im, pg, lim, inp, out, outn}), Pg.Program.unbytes(v), out, outn, OBn(lim, nx, Nat.add(U32.to_nat(outn), n))):
  (1n+Nat.add(n, 34n), out.run(n, Nat.add(n, 34n), PN.le_succ(Nat.add(n, 34n), Nat.add(n, 34n), PN.le_refl(Nat.add(n, 34n))),
    regs, m, nx, fs, im, pg, lim, inp, out, outn, c, ks, img, v, hreg, hlen, htm, hok))

# Gives, for bytes, as a halt with 0 or out of memory
def Gives.some(o: Cr.Cir.Out, +bs: List<&2, Word(8n)>, +out0: List<&2, Word(8n)>, +outn0: U32, -O: Type, g: Gives(o, Some{bs}, out0, outn0, O)) ->
  Or(&st: Cr.Cir.State -> ({o == Cr.Cir.Out.halt{0, st} : Cr.Cir.Out} & ({St.out(st) == List.append(&2, Word(8n), List.reverse(&2, Word(8n), bs), out0) : List<&2, Word(8n)>} &
      {St.outn(st) == Incs(bs, outn0) : U32})),
    {o == Cr.Cir.Out.out_of_memory{} : Cr.Cir.Out}):
  match o:
    case Cr.Cir.Out.next{st}:
      match g:
    case Cr.Cir.Out.halt{+s, +st}:
      (e0, rest) = g
      Inl{(st, (Equal.cong(U32, Cr.Cir.Out, x => Cr.Cir.Out.halt{x, st}, s, 0, e0), rest))}
    case Cr.Cir.Out.out_of_memory{}:
      Inr{{==}}
    case Cr.Cir.Out.trap{}:
      match g:
    case Cr.Cir.Out.not_done{}:
      match g:

# Gives, for no bytes, as a halt with 2 or out of memory
def Gives.none(o: Cr.Cir.Out, -out0: List<&2, Word(8n)>, -outn0: U32, -O: Type, g: Gives(o, None{}, out0, outn0, O)) ->
  Or(&st: Cr.Cir.State -> {o == Cr.Cir.Out.halt{2, st} : Cr.Cir.Out}, {o == Cr.Cir.Out.out_of_memory{} : Cr.Cir.Out}):
  match o:
    case Cr.Cir.Out.next{st}:
      match g:
    case Cr.Cir.Out.halt{+s, +st}:
      Inl{(st, Equal.cong(U32, Cr.Cir.Out, x => Cr.Cir.Out.halt{x, st}, s, 2, g))}
    case Cr.Cir.Out.out_of_memory{}:
      Inr{{==}}
    case Cr.Cir.Out.trap{}:
      match g:
    case Cr.Cir.Out.not_done{}:
      match g:

# when Program.unbytes(v) is Some{o}: M.out halts with 0 and the output o,
# or runs out of memory
def out.some(+n: Nat, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fs: U32, +im: U32,
  +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +out: List<&2, Word(8n)>, +outn: U32, +c: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +v: Bk.Term, +o: List<&2, Word(8n)>,
  +hreg: {List.get(&2, U32, regs, Mc.R.focus()) == Some{c} : Maybe<&2, U32>},
  +hlen: {Nat.is_le(Mc.Mach.regs(), List.length(&2, U32, regs)) == True{} : Bool},
  +htm: {T.tm.of(n, m, ks, img, c) == Some{v} : Maybe<&2, Bk.Term>},
  +hok: {ok(n, m, ks, img, c, im, fs, nx) == True{} : Bool},
  +eo: {Pg.Program.unbytes(v) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}) ->
  &F: Nat -> Or(&st2: Cr.Cir.State ->
      ({Cr.Cir.exec(F, Mc.M.out(), Cr.Cir.State{regs, m, nx, fs, im, pg, lim, inp, out, outn}) == Cr.Cir.Out.halt{0, st2} : Cr.Cir.Out} &
       ({St.out(st2) == List.append(&2, Word(8n), List.reverse(&2, Word(8n), o), out) : List<&2, Word(8n)>} & {St.outn(st2) == Incs(o, outn) : U32})),
    {Cr.Cir.exec(F, Mc.M.out(), Cr.Cir.State{regs, m, nx, fs, im, pg, lim, inp, out, outn}) == Cr.Cir.Out.out_of_memory{} : Cr.Cir.Out}):
  +F = {1n+Nat.add(n, 34n) : Nat}
  +x = {Cr.Cir.exec(F, Mc.M.out(), Cr.Cir.State{regs, m, nx, fs, im, pg, lim, inp, out, outn}) : Cr.Cir.Out}
  (F, Gives.some(x, o, out, outn, OBn(lim, nx, Nat.add(U32.to_nat(outn), n)),
    Tr(Maybe<&2, List<&2, Word(8n)>>, r => Gives(x, r, out, outn, OBn(lim, nx, Nat.add(U32.to_nat(outn), n))), Pg.Program.unbytes(v), Some{o}, eo,
      out.run(n, Nat.add(n, 34n), PN.le_succ(Nat.add(n, 34n), Nat.add(n, 34n), PN.le_refl(Nat.add(n, 34n))),
        regs, m, nx, fs, im, pg, lim, inp, out, outn, c, ks, img, v, hreg, hlen, htm, hok))))

# when Program.unbytes(v) is none: M.out halts with 2, or runs out of memory
def out.none(+n: Nat, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fs: U32, +im: U32,
  +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +out: List<&2, Word(8n)>, +outn: U32, +c: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +v: Bk.Term,
  +hreg: {List.get(&2, U32, regs, Mc.R.focus()) == Some{c} : Maybe<&2, U32>},
  +hlen: {Nat.is_le(Mc.Mach.regs(), List.length(&2, U32, regs)) == True{} : Bool},
  +htm: {T.tm.of(n, m, ks, img, c) == Some{v} : Maybe<&2, Bk.Term>},
  +hok: {ok(n, m, ks, img, c, im, fs, nx) == True{} : Bool},
  +eo: {Pg.Program.unbytes(v) == None{} : Maybe<&2, List<&2, Word(8n)>>}) ->
  &F: Nat -> Or(&st2: Cr.Cir.State -> {Cr.Cir.exec(F, Mc.M.out(), Cr.Cir.State{regs, m, nx, fs, im, pg, lim, inp, out, outn}) == Cr.Cir.Out.halt{2, st2} : Cr.Cir.Out},
    {Cr.Cir.exec(F, Mc.M.out(), Cr.Cir.State{regs, m, nx, fs, im, pg, lim, inp, out, outn}) == Cr.Cir.Out.out_of_memory{} : Cr.Cir.Out}):
  +F = {1n+Nat.add(n, 34n) : Nat}
  +x = {Cr.Cir.exec(F, Mc.M.out(), Cr.Cir.State{regs, m, nx, fs, im, pg, lim, inp, out, outn}) : Cr.Cir.Out}
  (F, Gives.none(x, out, outn, OBn(lim, nx, Nat.add(U32.to_nat(outn), n)),
    Tr(Maybe<&2, List<&2, Word(8n)>>, r => Gives(x, r, out, outn, OBn(lim, nx, Nat.add(U32.to_nat(outn), n))), Pg.Program.unbytes(v), None{}, eo,
      out.run(n, Nat.add(n, 34n), PN.le_succ(Nat.add(n, 34n), Nat.add(n, 34n), PN.le_refl(Nat.add(n, 34n))),
        regs, m, nx, fs, im, pg, lim, inp, out, outn, c, ks, img, v, hreg, hlen, htm, hok))))

# The names of the labels
# -----------------------
#
# In the image, the names ks are C.Img.known(ks2): the machine's own first,
# and a label holds the number C.Img.id(ks, k, 0) of its name k, the first
# place of k in ks (labid). Such a number compares with the machine's names
# 0 to 6 as its name does (labid.ok), which is what ok asks (labok).

def nat_eq_refl(+b: Nat) -> {Nat.is_eq(b, b) == True{} : Bool}:
  match b:
    case 0n:
      {==}
    case 1n+p:
      nat_eq_refl(p)

def ne_rel(c: Cmp, -X: Nat, +a: Nat, +b: Nat, h: PN.Rel(c, X, b), +ea: {X == a : Nat}, +hne: {Nat.is_eq(a, b) == False{} : Bool}) ->
  {Cmp.is_eq(c) == False{} : Bool}:
  match c:
    case LT{}:
      {==}
    case GT{}:
      {==}
    case EQ{}:
      +eab = Equal.trans(Nat, a, X, b, Equal.sym(Nat, X, a, ea), h)
      Empty.absurd({Cmp.is_eq(EQ{}) == False{} : Bool}, PN.true_ne_false(Equal.trans(Bool, True{}, Nat.is_eq(b, b), False{},
        Equal.sym(Bool, Nat.is_eq(b, b), True{}, nat_eq_refl(b)), Tr(Nat, y => {Nat.is_eq(y, b) == False{} : Bool}, a, b, eab, hne))))

# a U32 of the number a is not n, when a is not the number of n
def ne_num(+x: U32, +n: U32, +a: Nat, +ea: {U32.to_nat(x) == a : Nat}, +hne: {Nat.is_eq(a, U32.to_nat(n)) == False{} : Bool}) ->
  {U32.is_eq(x, n) == False{} : Bool}:
  ne_rel(U32.cmp(x, n), U32.to_nat(x), a, U32.to_nat(n), PN.U32.rel(x, n), ea, hne)

# Byte.is_eq and Name.is_eq do not depend on the order of their arguments
def Fsym(c: Cmp, d: Cmp, a: Bool, b: Bool, +e: {Cmp.is_eq(c) == Cmp.is_eq(d) : Bool}) ->
  {Cmp.is_eq(Word.cmp.fin(a, b, c)) == Cmp.is_eq(Word.cmp.fin(b, a, d)) : Bool}:
  match c d:
    case LT{} LT{}:
      {==}
    case LT{} GT{}:
      {==}
    case GT{} LT{}:
      {==}
    case GT{} GT{}:
      {==}
    case EQ{} EQ{}:
      match a b:
        case True{} True{}:
          {==}
        case True{} False{}:
          {==}
        case False{} True{}:
          {==}
        case False{} False{}:
          {==}
    case LT{} EQ{}:
      Empty.absurd({Cmp.is_eq(Word.cmp.fin(a, b, LT{})) == Cmp.is_eq(Word.cmp.fin(b, a, EQ{})) : Bool}, PN.false_ne_true(e))
    case GT{} EQ{}:
      Empty.absurd({Cmp.is_eq(Word.cmp.fin(a, b, GT{})) == Cmp.is_eq(Word.cmp.fin(b, a, EQ{})) : Bool}, PN.false_ne_true(e))
    case EQ{} LT{}:
      Empty.absurd({Cmp.is_eq(Word.cmp.fin(a, b, EQ{})) == Cmp.is_eq(Word.cmp.fin(b, a, LT{})) : Bool}, PN.true_ne_false(e))
    case EQ{} GT{}:
      Empty.absurd({Cmp.is_eq(Word.cmp.fin(a, b, EQ{})) == Cmp.is_eq(Word.cmp.fin(b, a, GT{})) : Bool}, PN.true_ne_false(e))

def Wsym(+n: Nat, a: Word(n), b: Word(n)) -> {Cmp.is_eq(Word.cmp(n, a, b)) == Cmp.is_eq(Word.cmp(n, b, a)) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match a b:
        case WCon{+x, +at} WCon{+y, +bt}:
          Fsym(Word.cmp(p, at, bt), Word.cmp(p, bt, at), x, y, Wsym(p, at, bt))

def Bsym(x: Word(8n), y: Word(8n)) -> {Sd.Byte.is_eq(x, y) == Sd.Byte.is_eq(y, x) : Bool}:
  Wsym(8n, x, y)

def Nsym(a: List<&2, Word(8n)>, b: List<&2, Word(8n)>) -> {Sd.Name.is_eq(a, b) == Sd.Name.is_eq(b, a) : Bool}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{_, _}:
      {==}
    case Con{_, _} Nil{}:
      {==}
    case Con{+x, +xs} Con{+y, +ys}:
      %Bsym(y, x) : {Bool.and(_, Sd.Name.is_eq(xs, ys)) == Bool.and(Sd.Byte.is_eq(y, x), Sd.Name.is_eq(ys, xs)) : Bool}
      %Equal.sym(Bool, Sd.Name.is_eq(xs, ys), Sd.Name.is_eq(ys, xs), Nsym(xs, ys)) :
        {Bool.and(Sd.Byte.is_eq(y, x), _) == Bool.and(Sd.Byte.is_eq(y, x), Sd.Name.is_eq(ys, xs)) : Bool}
      {==}

# known.ok, once its parts are known
def KO(n0: Bool, n1: Bool, n2: Bool, n3: Bool, n4: Bool, n5: Bool, n6: Bool,
  x0: Bool, x1: Bool, x2: Bool, x3: Bool, x4: Bool, x5: Bool, x6: Bool) -> Bool:
  iff(n0, x0) && iff(n1, x1) && iff(n2, x2) && iff(n3, x3) && iff(n4, x4) && iff(n5, x5) && iff(n6, x6)

def KO.rw(+b: List<&2, Word(8n)>, +j: U32, n0: Bool, n1: Bool, n2: Bool, n3: Bool, n4: Bool, n5: Bool, n6: Bool, x0: Bool, x1: Bool, x2: Bool, x3: Bool, x4: Bool, x5: Bool, x6: Bool,
  +en0: {Sd.Name.is_eq(b, Pg.Program.name.unit()) == n0 : Bool},
  +en1: {Sd.Name.is_eq(b, Pg.Program.name.nil()) == n1 : Bool},
  +en2: {Sd.Name.is_eq(b, Pg.Program.name.con()) == n2 : Bool},
  +en3: {Sd.Name.is_eq(b, Pg.Program.name.wnil()) == n3 : Bool},
  +en4: {Sd.Name.is_eq(b, Pg.Program.name.wcon()) == n4 : Bool},
  +en5: {Sd.Name.is_eq(b, Pg.Program.name.true()) == n5 : Bool},
  +en6: {Sd.Name.is_eq(b, Pg.Program.name.false()) == n6 : Bool},
  +ex0: {U32.is_eq(j, 0) == x0 : Bool},
  +ex1: {U32.is_eq(j, 1) == x1 : Bool},
  +ex2: {U32.is_eq(j, 2) == x2 : Bool},
  +ex3: {U32.is_eq(j, 3) == x3 : Bool},
  +ex4: {U32.is_eq(j, 4) == x4 : Bool},
  +ex5: {U32.is_eq(j, 5) == x5 : Bool},
  +ex6: {U32.is_eq(j, 6) == x6 : Bool},
  +h: {KO(n0, n1, n2, n3, n4, n5, n6, x0, x1, x2, x3, x4, x5, x6) == True{} : Bool}) -> {known.ok(j, b) == True{} : Bool}:
  %Equal.sym(Bool, Sd.Name.is_eq(b, Pg.Program.name.unit()), n0, en0) : {KO(_, Sd.Name.is_eq(b, Pg.Program.name.nil()), Sd.Name.is_eq(b, Pg.Program.name.con()), Sd.Name.is_eq(b, Pg.Program.name.wnil()), Sd.Name.is_eq(b, Pg.Program.name.wcon()), Sd.Name.is_eq(b, Pg.Program.name.true()), Sd.Name.is_eq(b, Pg.Program.name.false()), U32.is_eq(j, 0), U32.is_eq(j, 1), U32.is_eq(j, 2), U32.is_eq(j, 3), U32.is_eq(j, 4), U32.is_eq(j, 5), U32.is_eq(j, 6)) == True{} : Bool}
  %Equal.sym(Bool, Sd.Name.is_eq(b, Pg.Program.name.nil()), n1, en1) : {KO(n0, _, Sd.Name.is_eq(b, Pg.Program.name.con()), Sd.Name.is_eq(b, Pg.Program.name.wnil()), Sd.Name.is_eq(b, Pg.Program.name.wcon()), Sd.Name.is_eq(b, Pg.Program.name.true()), Sd.Name.is_eq(b, Pg.Program.name.false()), U32.is_eq(j, 0), U32.is_eq(j, 1), U32.is_eq(j, 2), U32.is_eq(j, 3), U32.is_eq(j, 4), U32.is_eq(j, 5), U32.is_eq(j, 6)) == True{} : Bool}
  %Equal.sym(Bool, Sd.Name.is_eq(b, Pg.Program.name.con()), n2, en2) : {KO(n0, n1, _, Sd.Name.is_eq(b, Pg.Program.name.wnil()), Sd.Name.is_eq(b, Pg.Program.name.wcon()), Sd.Name.is_eq(b, Pg.Program.name.true()), Sd.Name.is_eq(b, Pg.Program.name.false()), U32.is_eq(j, 0), U32.is_eq(j, 1), U32.is_eq(j, 2), U32.is_eq(j, 3), U32.is_eq(j, 4), U32.is_eq(j, 5), U32.is_eq(j, 6)) == True{} : Bool}
  %Equal.sym(Bool, Sd.Name.is_eq(b, Pg.Program.name.wnil()), n3, en3) : {KO(n0, n1, n2, _, Sd.Name.is_eq(b, Pg.Program.name.wcon()), Sd.Name.is_eq(b, Pg.Program.name.true()), Sd.Name.is_eq(b, Pg.Program.name.false()), U32.is_eq(j, 0), U32.is_eq(j, 1), U32.is_eq(j, 2), U32.is_eq(j, 3), U32.is_eq(j, 4), U32.is_eq(j, 5), U32.is_eq(j, 6)) == True{} : Bool}
  %Equal.sym(Bool, Sd.Name.is_eq(b, Pg.Program.name.wcon()), n4, en4) : {KO(n0, n1, n2, n3, _, Sd.Name.is_eq(b, Pg.Program.name.true()), Sd.Name.is_eq(b, Pg.Program.name.false()), U32.is_eq(j, 0), U32.is_eq(j, 1), U32.is_eq(j, 2), U32.is_eq(j, 3), U32.is_eq(j, 4), U32.is_eq(j, 5), U32.is_eq(j, 6)) == True{} : Bool}
  %Equal.sym(Bool, Sd.Name.is_eq(b, Pg.Program.name.true()), n5, en5) : {KO(n0, n1, n2, n3, n4, _, Sd.Name.is_eq(b, Pg.Program.name.false()), U32.is_eq(j, 0), U32.is_eq(j, 1), U32.is_eq(j, 2), U32.is_eq(j, 3), U32.is_eq(j, 4), U32.is_eq(j, 5), U32.is_eq(j, 6)) == True{} : Bool}
  %Equal.sym(Bool, Sd.Name.is_eq(b, Pg.Program.name.false()), n6, en6) : {KO(n0, n1, n2, n3, n4, n5, _, U32.is_eq(j, 0), U32.is_eq(j, 1), U32.is_eq(j, 2), U32.is_eq(j, 3), U32.is_eq(j, 4), U32.is_eq(j, 5), U32.is_eq(j, 6)) == True{} : Bool}
  %Equal.sym(Bool, U32.is_eq(j, 0), x0, ex0) : {KO(n0, n1, n2, n3, n4, n5, n6, _, U32.is_eq(j, 1), U32.is_eq(j, 2), U32.is_eq(j, 3), U32.is_eq(j, 4), U32.is_eq(j, 5), U32.is_eq(j, 6)) == True{} : Bool}
  %Equal.sym(Bool, U32.is_eq(j, 1), x1, ex1) : {KO(n0, n1, n2, n3, n4, n5, n6, x0, _, U32.is_eq(j, 2), U32.is_eq(j, 3), U32.is_eq(j, 4), U32.is_eq(j, 5), U32.is_eq(j, 6)) == True{} : Bool}
  %Equal.sym(Bool, U32.is_eq(j, 2), x2, ex2) : {KO(n0, n1, n2, n3, n4, n5, n6, x0, x1, _, U32.is_eq(j, 3), U32.is_eq(j, 4), U32.is_eq(j, 5), U32.is_eq(j, 6)) == True{} : Bool}
  %Equal.sym(Bool, U32.is_eq(j, 3), x3, ex3) : {KO(n0, n1, n2, n3, n4, n5, n6, x0, x1, x2, _, U32.is_eq(j, 4), U32.is_eq(j, 5), U32.is_eq(j, 6)) == True{} : Bool}
  %Equal.sym(Bool, U32.is_eq(j, 4), x4, ex4) : {KO(n0, n1, n2, n3, n4, n5, n6, x0, x1, x2, x3, _, U32.is_eq(j, 5), U32.is_eq(j, 6)) == True{} : Bool}
  %Equal.sym(Bool, U32.is_eq(j, 5), x5, ex5) : {KO(n0, n1, n2, n3, n4, n5, n6, x0, x1, x2, x3, x4, _, U32.is_eq(j, 6)) == True{} : Bool}
  %Equal.sym(Bool, U32.is_eq(j, 6), x6, ex6) : {KO(n0, n1, n2, n3, n4, n5, n6, x0, x1, x2, x3, x4, x5, _) == True{} : Bool}
  h

# the list xs past its first n
def KD(n: Nat, xs: List<&2, List<&2, Word(8n)>>) -> List<&2, List<&2, Word(8n)>>:
  match n:
    case 0n:
      xs
    case 1n+p:
      match xs:
        case Nil{}:
          Nil{}
        case Con{_, t}:
          KD(p, t)

def id.at0(+ks2: List<&2, List<&2, Word(8n)>>, +k: List<&2, Word(8n)>, +e0: {Sd.Name.is_eq(Pg.Program.name.unit(), k) == True{} : Bool}) -> {Mc.Img.id(Mc.Img.known(ks2), k, 0) == 0 : U32}:
  %Equal.sym(Bool, Sd.Name.is_eq(Pg.Program.name.unit(), k), True{}, e0) : {Mc.Img.ref.if(_, 0, u => Mc.Img.id(KD(1n, Mc.Img.known(ks2)), k, U32.inc(0))) == 0 : U32}
  {==}

def id.at1(+ks2: List<&2, List<&2, Word(8n)>>, +k: List<&2, Word(8n)>, +e0: {Sd.Name.is_eq(Pg.Program.name.unit(), k) == False{} : Bool}, +e1: {Sd.Name.is_eq(Pg.Program.name.nil(), k) == True{} : Bool}) -> {Mc.Img.id(Mc.Img.known(ks2), k, 0) == 1 : U32}:
  %Equal.sym(Bool, Sd.Name.is_eq(Pg.Program.name.unit(), k), False{}, e0) : {Mc.Img.ref.if(_, 0, u => Mc.Img.id(KD(1n, Mc.Img.known(ks2)), k, U32.inc(0))) == 1 : U32}
  %Equal.sym(Bool, Sd.Name.is_eq(Pg.Program.name.nil(), k), True{}, e1) : {Mc.Img.ref.if(_, 1, u => Mc.Img.id(KD(2n, Mc.Img.known(ks2)), k, U32.inc(1))) == 1 : U32}
  {==}

def id.at2(+ks2: List<&2, List<&2, Word(8n)>>, +k: List<&2, Word(8n)>, +e0: {Sd.Name.is_eq(Pg.Program.name.unit(), k) == False{} : Bool}, +e1: {Sd.Name.is_eq(Pg.Program.name.nil(), k) == False{} : Bool}, +e2: {Sd.Name.is_eq(Pg.Program.name.con(), k) == True{} : Bool}) -> {Mc.Img.id(Mc.Img.known(ks2), k, 0) == 2 : U32}:
  %Equal.sym(Bool, Sd.Name.is_eq(Pg.Program.name.unit(), k), False{}, e0) : {Mc.Img.ref.if(_, 0, u => Mc.Img.id(KD(1n, Mc.Img.known(ks2)), k, U32.inc(0))) == 2 : U32}
  %Equal.sym(Bool, Sd.Name.is_eq(Pg.Program.name.nil(), k), False{}, e1) : {Mc.Img.ref.if(_, 1, u => Mc.Img.id(KD(2n, Mc.Img.known(ks2)), k, U32.inc(1))) == 2 : U32}
  %Equal.sym(Bool, Sd.Name.is_eq(Pg.Program.name.con(), k), True{}, e2) : {Mc.Img.ref.if(_, 2, u => Mc.Img.id(KD(3n, Mc.Img.known(ks2)), k, U32.inc(2))) == 2 : U32}
  {==}

def id.at3(+ks2: List<&2, List<&2, Word(8n)>>, +k: List<&2, Word(8n)>, +e0: {Sd.Name.is_eq(Pg.Program.name.unit(), k) == False{} : Bool}, +e1: {Sd.Name.is_eq(Pg.Program.name.nil(), k) == False{} : Bool}, +e2: {Sd.Name.is_eq(Pg.Program.name.con(), k) == False{} : Bool}, +e3: {Sd.Name.is_eq(Pg.Program.name.wnil(), k) == True{} : Bool}) -> {Mc.Img.id(Mc.Img.known(ks2), k, 0) == 3 : U32}:
  %Equal.sym(Bool, Sd.Name.is_eq(Pg.Program.name.unit(), k), False{}, e0) : {Mc.Img.ref.if(_, 0, u => Mc.Img.id(KD(1n, Mc.Img.known(ks2)), k, U32.inc(0))) == 3 : U32}
  %Equal.sym(Bool, Sd.Name.is_eq(Pg.Program.name.nil(), k), False{}, e1) : {Mc.Img.ref.if(_, 1, u => Mc.Img.id(KD(2n, Mc.Img.known(ks2)), k, U32.inc(1))) == 3 : U32}
  %Equal.sym(Bool, Sd.Name.is_eq(Pg.Program.name.con(), k), False{}, e2) : {Mc.Img.ref.if(_, 2, u => Mc.Img.id(KD(3n, Mc.Img.known(ks2)), k, U32.inc(2))) == 3 : U32}
  %Equal.sym(Bool, Sd.Name.is_eq(Pg.Program.name.wnil(), k), True{}, e3) : {Mc.Img.ref.if(_, 3, u => Mc.Img.id(KD(4n, Mc.Img.known(ks2)), k, U32.inc(3))) == 3 : U32}
  {==}

def id.at4(+ks2: List<&2, List<&2, Word(8n)>>, +k: List<&2, Word(8n)>, +e0: {Sd.Name.is_eq(Pg.Program.name.unit(), k) == False{} : Bool}, +e1: {Sd.Name.is_eq(Pg.Program.name.nil(), k) == False{} : Bool}, +e2: {Sd.Name.is_eq(Pg.Program.name.con(), k) == False{} : Bool}, +e3: {Sd.Name.is_eq(Pg.Program.name.wnil(), k) == False{} : Bool}, +e4: {Sd.Name.is_eq(Pg.Program.name.wcon(), k) == True{} : Bool}) -> {Mc.Img.id(Mc.Img.known(ks2), k, 0) == 4 : U32}:
  %Equal.sym(Bool, Sd.Name.is_eq(Pg.Program.name.unit(), k), False{}, e0) : {Mc.Img.ref.if(_, 0, u => Mc.Img.id(KD(1n, Mc.Img.known(ks2)), k, U32.inc(0))) == 4 : U32}
  %Equal.sym(Bool, Sd.Name.is_eq(Pg.Program.name.nil(), k), False{}, e1) : {Mc.Img.ref.if(_, 1, u => Mc.Img.id(KD(2n, Mc.Img.known(ks2)), k, U32.inc(1))) == 4 : U32}
  %Equal.sym(Bool, Sd.Name.is_eq(Pg.Program.name.con(), k), False{}, e2) : {Mc.Img.ref.if(_, 2, u => Mc.Img.id(KD(3n, Mc.Img.known(ks2)), k, U32.inc(2))) == 4 : U32}
  %Equal.sym(Bool, Sd.Name.is_eq(Pg.Program.name.wnil(), k), False{}, e3) : {Mc.Img.ref.if(_, 3, u => Mc.Img.id(KD(4n, Mc.Img.known(ks2)), k, U32.inc(3))) == 4 : U32}
  %Equal.sym(Bool, Sd.Name.is_eq(Pg.Program.name.wcon(), k), True{}, e4) : {Mc.Img.ref.if(_, 4, u => Mc.Img.id(KD(5n, Mc.Img.known(ks2)), k, U32.inc(4))) == 4 : U32}
  {==}

def id.at5(+ks2: List<&2, List<&2, Word(8n)>>, +k: List<&2, Word(8n)>, +e0: {Sd.Name.is_eq(Pg.Program.name.unit(), k) == False{} : Bool}, +e1: {Sd.Name.is_eq(Pg.Program.name.nil(), k) == False{} : Bool}, +e2: {Sd.Name.is_eq(Pg.Program.name.con(), k) == False{} : Bool}, +e3: {Sd.Name.is_eq(Pg.Program.name.wnil(), k) == False{} : Bool}, +e4: {Sd.Name.is_eq(Pg.Program.name.wcon(), k) == False{} : Bool}, +e5: {Sd.Name.is_eq(Pg.Program.name.true(), k) == True{} : Bool}) -> {Mc.Img.id(Mc.Img.known(ks2), k, 0) == 5 : U32}:
  %Equal.sym(Bool, Sd.Name.is_eq(Pg.Program.name.unit(), k), False{}, e0) : {Mc.Img.ref.if(_, 0, u => Mc.Img.id(KD(1n, Mc.Img.known(ks2)), k, U32.inc(0))) == 5 : U32}
  %Equal.sym(Bool, Sd.Name.is_eq(Pg.Program.name.nil(), k), False{}, e1) : {Mc.Img.ref.if(_, 1, u => Mc.Img.id(KD(2n, Mc.Img.known(ks2)), k, U32.inc(1))) == 5 : U32}
  %Equal.sym(Bool, Sd.Name.is_eq(Pg.Program.name.con(), k), False{}, e2) : {Mc.Img.ref.if(_, 2, u => Mc.Img.id(KD(3n, Mc.Img.known(ks2)), k, U32.inc(2))) == 5 : U32}
  %Equal.sym(Bool, Sd.Name.is_eq(Pg.Program.name.wnil(), k), False{}, e3) : {Mc.Img.ref.if(_, 3, u => Mc.Img.id(KD(4n, Mc.Img.known(ks2)), k, U32.inc(3))) == 5 : U32}
  %Equal.sym(Bool, Sd.Name.is_eq(Pg.Program.name.wcon(), k), False{}, e4) : {Mc.Img.ref.if(_, 4, u => Mc.Img.id(KD(5n, Mc.Img.known(ks2)), k, U32.inc(4))) == 5 : U32}
  %Equal.sym(Bool, Sd.Name.is_eq(Pg.Program.name.true(), k), True{}, e5) : {Mc.Img.ref.if(_, 5, u => Mc.Img.id(KD(6n, Mc.Img.known(ks2)), k, U32.inc(5))) == 5 : U32}
  {==}

def id.at6(+ks2: List<&2, List<&2, Word(8n)>>, +k: List<&2, Word(8n)>, +e0: {Sd.Name.is_eq(Pg.Program.name.unit(), k) == False{} : Bool}, +e1: {Sd.Name.is_eq(Pg.Program.name.nil(), k) == False{} : Bool}, +e2: {Sd.Name.is_eq(Pg.Program.name.con(), k) == False{} : Bool}, +e3: {Sd.Name.is_eq(Pg.Program.name.wnil(), k) == False{} : Bool}, +e4: {Sd.Name.is_eq(Pg.Program.name.wcon(), k) == False{} : Bool}, +e5: {Sd.Name.is_eq(Pg.Program.name.true(), k) == False{} : Bool}, +e6: {Sd.Name.is_eq(Pg.Program.name.false(), k) == True{} : Bool}) -> {Mc.Img.id(Mc.Img.known(ks2), k, 0) == 6 : U32}:
  %Equal.sym(Bool, Sd.Name.is_eq(Pg.Program.name.unit(), k), False{}, e0) : {Mc.Img.ref.if(_, 0, u => Mc.Img.id(KD(1n, Mc.Img.known(ks2)), k, U32.inc(0))) == 6 : U32}
  %Equal.sym(Bool, Sd.Name.is_eq(Pg.Program.name.nil(), k), False{}, e1) : {Mc.Img.ref.if(_, 1, u => Mc.Img.id(KD(2n, Mc.Img.known(ks2)), k, U32.inc(1))) == 6 : U32}
  %Equal.sym(Bool, Sd.Name.is_eq(Pg.Program.name.con(), k), False{}, e2) : {Mc.Img.ref.if(_, 2, u => Mc.Img.id(KD(3n, Mc.Img.known(ks2)), k, U32.inc(2))) == 6 : U32}
  %Equal.sym(Bool, Sd.Name.is_eq(Pg.Program.name.wnil(), k), False{}, e3) : {Mc.Img.ref.if(_, 3, u => Mc.Img.id(KD(4n, Mc.Img.known(ks2)), k, U32.inc(3))) == 6 : U32}
  %Equal.sym(Bool, Sd.Name.is_eq(Pg.Program.name.wcon(), k), False{}, e4) : {Mc.Img.ref.if(_, 4, u => Mc.Img.id(KD(5n, Mc.Img.known(ks2)), k, U32.inc(4))) == 6 : U32}
  %Equal.sym(Bool, Sd.Name.is_eq(Pg.Program.name.true(), k), False{}, e5) : {Mc.Img.ref.if(_, 5, u => Mc.Img.id(KD(6n, Mc.Img.known(ks2)), k, U32.inc(5))) == 6 : U32}
  %Equal.sym(Bool, Sd.Name.is_eq(Pg.Program.name.false(), k), True{}, e6) : {Mc.Img.ref.if(_, 6, u => Mc.Img.id(KD(7n, Mc.Img.known(ks2)), k, U32.inc(6))) == 6 : U32}
  {==}

def lab.at0(+ks2: List<&2, List<&2, Word(8n)>>, +j: U32, +k: List<&2, Word(8n)>, +ek: {T.tm.name(Mc.Img.known(ks2), j) == Some{k} : Maybe<&2, List<&2, Word(8n)>>},
  +ej: {U32.is_eq(j, Mc.Img.id(Mc.Img.known(ks2), k, 0)) == True{} : Bool}, +e0: {Sd.Name.is_eq(Pg.Program.name.unit(), k) == True{} : Bool}) -> {known.ok(j, k) == True{} : Bool}:
  +etn = eq_nat(j, 0, Tr(U32, y => {U32.is_eq(j, y) == True{} : Bool}, Mc.Img.id(Mc.Img.known(ks2), k, 0), 0, id.at0(ks2, k, e0), ej))
  +enk = Equal.cong(Maybe<&2, List<&2, Word(8n)>>, List<&2, Word(8n)>, x => Maybe.default(&2, List<&2, Word(8n)>, x, Nil{}), Some{Pg.Program.name.unit()}, Some{k},
    Tr(Nat, t => {List.get(&2, List<&2, Word(8n)>, Mc.Img.known(ks2), t) == Some{k} : Maybe<&2, List<&2, Word(8n)>>}, U32.to_nat(j), 0n, etn, ek))
  Tr(List<&2, Word(8n)>, b => {known.ok(j, b) == True{} : Bool}, Pg.Program.name.unit(), k, enk,
    KO.rw(Pg.Program.name.unit(), j, True{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, nat_eq(j, 0, etn), ne_num(j, 1, 0n, etn, {==}), ne_num(j, 2, 0n, etn, {==}), ne_num(j, 3, 0n, etn, {==}), ne_num(j, 4, 0n, etn, {==}), ne_num(j, 5, 0n, etn, {==}), ne_num(j, 6, 0n, etn, {==}), {==}))

def lab.at1(+ks2: List<&2, List<&2, Word(8n)>>, +j: U32, +k: List<&2, Word(8n)>, +ek: {T.tm.name(Mc.Img.known(ks2), j) == Some{k} : Maybe<&2, List<&2, Word(8n)>>},
  +ej: {U32.is_eq(j, Mc.Img.id(Mc.Img.known(ks2), k, 0)) == True{} : Bool}, +e0: {Sd.Name.is_eq(Pg.Program.name.unit(), k) == False{} : Bool}, +e1: {Sd.Name.is_eq(Pg.Program.name.nil(), k) == True{} : Bool}) -> {known.ok(j, k) == True{} : Bool}:
  +etn = eq_nat(j, 1, Tr(U32, y => {U32.is_eq(j, y) == True{} : Bool}, Mc.Img.id(Mc.Img.known(ks2), k, 0), 1, id.at1(ks2, k, e0, e1), ej))
  +enk = Equal.cong(Maybe<&2, List<&2, Word(8n)>>, List<&2, Word(8n)>, x => Maybe.default(&2, List<&2, Word(8n)>, x, Nil{}), Some{Pg.Program.name.nil()}, Some{k},
    Tr(Nat, t => {List.get(&2, List<&2, Word(8n)>, Mc.Img.known(ks2), t) == Some{k} : Maybe<&2, List<&2, Word(8n)>>}, U32.to_nat(j), 1n, etn, ek))
  Tr(List<&2, Word(8n)>, b => {known.ok(j, b) == True{} : Bool}, Pg.Program.name.nil(), k, enk,
    KO.rw(Pg.Program.name.nil(), j, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, ne_num(j, 0, 1n, etn, {==}), nat_eq(j, 1, etn), ne_num(j, 2, 1n, etn, {==}), ne_num(j, 3, 1n, etn, {==}), ne_num(j, 4, 1n, etn, {==}), ne_num(j, 5, 1n, etn, {==}), ne_num(j, 6, 1n, etn, {==}), {==}))

def lab.at2(+ks2: List<&2, List<&2, Word(8n)>>, +j: U32, +k: List<&2, Word(8n)>, +ek: {T.tm.name(Mc.Img.known(ks2), j) == Some{k} : Maybe<&2, List<&2, Word(8n)>>},
  +ej: {U32.is_eq(j, Mc.Img.id(Mc.Img.known(ks2), k, 0)) == True{} : Bool}, +e0: {Sd.Name.is_eq(Pg.Program.name.unit(), k) == False{} : Bool}, +e1: {Sd.Name.is_eq(Pg.Program.name.nil(), k) == False{} : Bool}, +e2: {Sd.Name.is_eq(Pg.Program.name.con(), k) == True{} : Bool}) -> {known.ok(j, k) == True{} : Bool}:
  +etn = eq_nat(j, 2, Tr(U32, y => {U32.is_eq(j, y) == True{} : Bool}, Mc.Img.id(Mc.Img.known(ks2), k, 0), 2, id.at2(ks2, k, e0, e1, e2), ej))
  +enk = Equal.cong(Maybe<&2, List<&2, Word(8n)>>, List<&2, Word(8n)>, x => Maybe.default(&2, List<&2, Word(8n)>, x, Nil{}), Some{Pg.Program.name.con()}, Some{k},
    Tr(Nat, t => {List.get(&2, List<&2, Word(8n)>, Mc.Img.known(ks2), t) == Some{k} : Maybe<&2, List<&2, Word(8n)>>}, U32.to_nat(j), 2n, etn, ek))
  Tr(List<&2, Word(8n)>, b => {known.ok(j, b) == True{} : Bool}, Pg.Program.name.con(), k, enk,
    KO.rw(Pg.Program.name.con(), j, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, ne_num(j, 0, 2n, etn, {==}), ne_num(j, 1, 2n, etn, {==}), nat_eq(j, 2, etn), ne_num(j, 3, 2n, etn, {==}), ne_num(j, 4, 2n, etn, {==}), ne_num(j, 5, 2n, etn, {==}), ne_num(j, 6, 2n, etn, {==}), {==}))

def lab.at3(+ks2: List<&2, List<&2, Word(8n)>>, +j: U32, +k: List<&2, Word(8n)>, +ek: {T.tm.name(Mc.Img.known(ks2), j) == Some{k} : Maybe<&2, List<&2, Word(8n)>>},
  +ej: {U32.is_eq(j, Mc.Img.id(Mc.Img.known(ks2), k, 0)) == True{} : Bool}, +e0: {Sd.Name.is_eq(Pg.Program.name.unit(), k) == False{} : Bool}, +e1: {Sd.Name.is_eq(Pg.Program.name.nil(), k) == False{} : Bool}, +e2: {Sd.Name.is_eq(Pg.Program.name.con(), k) == False{} : Bool}, +e3: {Sd.Name.is_eq(Pg.Program.name.wnil(), k) == True{} : Bool}) -> {known.ok(j, k) == True{} : Bool}:
  +etn = eq_nat(j, 3, Tr(U32, y => {U32.is_eq(j, y) == True{} : Bool}, Mc.Img.id(Mc.Img.known(ks2), k, 0), 3, id.at3(ks2, k, e0, e1, e2, e3), ej))
  +enk = Equal.cong(Maybe<&2, List<&2, Word(8n)>>, List<&2, Word(8n)>, x => Maybe.default(&2, List<&2, Word(8n)>, x, Nil{}), Some{Pg.Program.name.wnil()}, Some{k},
    Tr(Nat, t => {List.get(&2, List<&2, Word(8n)>, Mc.Img.known(ks2), t) == Some{k} : Maybe<&2, List<&2, Word(8n)>>}, U32.to_nat(j), 3n, etn, ek))
  Tr(List<&2, Word(8n)>, b => {known.ok(j, b) == True{} : Bool}, Pg.Program.name.wnil(), k, enk,
    KO.rw(Pg.Program.name.wnil(), j, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, ne_num(j, 0, 3n, etn, {==}), ne_num(j, 1, 3n, etn, {==}), ne_num(j, 2, 3n, etn, {==}), nat_eq(j, 3, etn), ne_num(j, 4, 3n, etn, {==}), ne_num(j, 5, 3n, etn, {==}), ne_num(j, 6, 3n, etn, {==}), {==}))

def lab.at4(+ks2: List<&2, List<&2, Word(8n)>>, +j: U32, +k: List<&2, Word(8n)>, +ek: {T.tm.name(Mc.Img.known(ks2), j) == Some{k} : Maybe<&2, List<&2, Word(8n)>>},
  +ej: {U32.is_eq(j, Mc.Img.id(Mc.Img.known(ks2), k, 0)) == True{} : Bool}, +e0: {Sd.Name.is_eq(Pg.Program.name.unit(), k) == False{} : Bool}, +e1: {Sd.Name.is_eq(Pg.Program.name.nil(), k) == False{} : Bool}, +e2: {Sd.Name.is_eq(Pg.Program.name.con(), k) == False{} : Bool}, +e3: {Sd.Name.is_eq(Pg.Program.name.wnil(), k) == False{} : Bool}, +e4: {Sd.Name.is_eq(Pg.Program.name.wcon(), k) == True{} : Bool}) -> {known.ok(j, k) == True{} : Bool}:
  +etn = eq_nat(j, 4, Tr(U32, y => {U32.is_eq(j, y) == True{} : Bool}, Mc.Img.id(Mc.Img.known(ks2), k, 0), 4, id.at4(ks2, k, e0, e1, e2, e3, e4), ej))
  +enk = Equal.cong(Maybe<&2, List<&2, Word(8n)>>, List<&2, Word(8n)>, x => Maybe.default(&2, List<&2, Word(8n)>, x, Nil{}), Some{Pg.Program.name.wcon()}, Some{k},
    Tr(Nat, t => {List.get(&2, List<&2, Word(8n)>, Mc.Img.known(ks2), t) == Some{k} : Maybe<&2, List<&2, Word(8n)>>}, U32.to_nat(j), 4n, etn, ek))
  Tr(List<&2, Word(8n)>, b => {known.ok(j, b) == True{} : Bool}, Pg.Program.name.wcon(), k, enk,
    KO.rw(Pg.Program.name.wcon(), j, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, ne_num(j, 0, 4n, etn, {==}), ne_num(j, 1, 4n, etn, {==}), ne_num(j, 2, 4n, etn, {==}), ne_num(j, 3, 4n, etn, {==}), nat_eq(j, 4, etn), ne_num(j, 5, 4n, etn, {==}), ne_num(j, 6, 4n, etn, {==}), {==}))

def lab.at5(+ks2: List<&2, List<&2, Word(8n)>>, +j: U32, +k: List<&2, Word(8n)>, +ek: {T.tm.name(Mc.Img.known(ks2), j) == Some{k} : Maybe<&2, List<&2, Word(8n)>>},
  +ej: {U32.is_eq(j, Mc.Img.id(Mc.Img.known(ks2), k, 0)) == True{} : Bool}, +e0: {Sd.Name.is_eq(Pg.Program.name.unit(), k) == False{} : Bool}, +e1: {Sd.Name.is_eq(Pg.Program.name.nil(), k) == False{} : Bool}, +e2: {Sd.Name.is_eq(Pg.Program.name.con(), k) == False{} : Bool}, +e3: {Sd.Name.is_eq(Pg.Program.name.wnil(), k) == False{} : Bool}, +e4: {Sd.Name.is_eq(Pg.Program.name.wcon(), k) == False{} : Bool}, +e5: {Sd.Name.is_eq(Pg.Program.name.true(), k) == True{} : Bool}) -> {known.ok(j, k) == True{} : Bool}:
  +etn = eq_nat(j, 5, Tr(U32, y => {U32.is_eq(j, y) == True{} : Bool}, Mc.Img.id(Mc.Img.known(ks2), k, 0), 5, id.at5(ks2, k, e0, e1, e2, e3, e4, e5), ej))
  +enk = Equal.cong(Maybe<&2, List<&2, Word(8n)>>, List<&2, Word(8n)>, x => Maybe.default(&2, List<&2, Word(8n)>, x, Nil{}), Some{Pg.Program.name.true()}, Some{k},
    Tr(Nat, t => {List.get(&2, List<&2, Word(8n)>, Mc.Img.known(ks2), t) == Some{k} : Maybe<&2, List<&2, Word(8n)>>}, U32.to_nat(j), 5n, etn, ek))
  Tr(List<&2, Word(8n)>, b => {known.ok(j, b) == True{} : Bool}, Pg.Program.name.true(), k, enk,
    KO.rw(Pg.Program.name.true(), j, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, ne_num(j, 0, 5n, etn, {==}), ne_num(j, 1, 5n, etn, {==}), ne_num(j, 2, 5n, etn, {==}), ne_num(j, 3, 5n, etn, {==}), ne_num(j, 4, 5n, etn, {==}), nat_eq(j, 5, etn), ne_num(j, 6, 5n, etn, {==}), {==}))

def lab.at6(+ks2: List<&2, List<&2, Word(8n)>>, +j: U32, +k: List<&2, Word(8n)>, +ek: {T.tm.name(Mc.Img.known(ks2), j) == Some{k} : Maybe<&2, List<&2, Word(8n)>>},
  +ej: {U32.is_eq(j, Mc.Img.id(Mc.Img.known(ks2), k, 0)) == True{} : Bool}, +e0: {Sd.Name.is_eq(Pg.Program.name.unit(), k) == False{} : Bool}, +e1: {Sd.Name.is_eq(Pg.Program.name.nil(), k) == False{} : Bool}, +e2: {Sd.Name.is_eq(Pg.Program.name.con(), k) == False{} : Bool}, +e3: {Sd.Name.is_eq(Pg.Program.name.wnil(), k) == False{} : Bool}, +e4: {Sd.Name.is_eq(Pg.Program.name.wcon(), k) == False{} : Bool}, +e5: {Sd.Name.is_eq(Pg.Program.name.true(), k) == False{} : Bool}, +e6: {Sd.Name.is_eq(Pg.Program.name.false(), k) == True{} : Bool}) -> {known.ok(j, k) == True{} : Bool}:
  +etn = eq_nat(j, 6, Tr(U32, y => {U32.is_eq(j, y) == True{} : Bool}, Mc.Img.id(Mc.Img.known(ks2), k, 0), 6, id.at6(ks2, k, e0, e1, e2, e3, e4, e5, e6), ej))
  +enk = Equal.cong(Maybe<&2, List<&2, Word(8n)>>, List<&2, Word(8n)>, x => Maybe.default(&2, List<&2, Word(8n)>, x, Nil{}), Some{Pg.Program.name.false()}, Some{k},
    Tr(Nat, t => {List.get(&2, List<&2, Word(8n)>, Mc.Img.known(ks2), t) == Some{k} : Maybe<&2, List<&2, Word(8n)>>}, U32.to_nat(j), 6n, etn, ek))
  Tr(List<&2, Word(8n)>, b => {known.ok(j, b) == True{} : Bool}, Pg.Program.name.false(), k, enk,
    KO.rw(Pg.Program.name.false(), j, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, ne_num(j, 0, 6n, etn, {==}), ne_num(j, 1, 6n, etn, {==}), ne_num(j, 2, 6n, etn, {==}), ne_num(j, 3, 6n, etn, {==}), ne_num(j, 4, 6n, etn, {==}), ne_num(j, 5, 6n, etn, {==}), nat_eq(j, 6, etn), {==}))

def lab.ne0(b: Bool, +ks2: List<&2, List<&2, Word(8n)>>, +j: U32, +k: List<&2, Word(8n)>, +ek: {T.tm.name(Mc.Img.known(ks2), j) == Some{k} : Maybe<&2, List<&2, Word(8n)>>},
  +en: {Sd.Name.is_eq(Pg.Program.name.unit(), k) == False{} : Bool}, +eb: {U32.is_eq(j, 0) == b : Bool}) -> {U32.is_eq(j, 0) == False{} : Bool}:
  match b:
    case False{}:
      eb
    case True{}:
      +etn = eq_nat(j, 0, eb)
      +enk = Equal.cong(Maybe<&2, List<&2, Word(8n)>>, List<&2, Word(8n)>, x => Maybe.default(&2, List<&2, Word(8n)>, x, Nil{}), Some{Pg.Program.name.unit()}, Some{k},
        Tr(Nat, t => {List.get(&2, List<&2, Word(8n)>, Mc.Img.known(ks2), t) == Some{k} : Maybe<&2, List<&2, Word(8n)>>}, U32.to_nat(j), 0n, etn, ek))
      Empty.absurd({U32.is_eq(j, 0) == False{} : Bool}, PN.true_ne_false(Tr(List<&2, Word(8n)>, y => {Sd.Name.is_eq(Pg.Program.name.unit(), y) == False{} : Bool}, k, Pg.Program.name.unit(),
        Equal.sym(List<&2, Word(8n)>, Pg.Program.name.unit(), k, enk), en)))

def lab.ne1(b: Bool, +ks2: List<&2, List<&2, Word(8n)>>, +j: U32, +k: List<&2, Word(8n)>, +ek: {T.tm.name(Mc.Img.known(ks2), j) == Some{k} : Maybe<&2, List<&2, Word(8n)>>},
  +en: {Sd.Name.is_eq(Pg.Program.name.nil(), k) == False{} : Bool}, +eb: {U32.is_eq(j, 1) == b : Bool}) -> {U32.is_eq(j, 1) == False{} : Bool}:
  match b:
    case False{}:
      eb
    case True{}:
      +etn = eq_nat(j, 1, eb)
      +enk = Equal.cong(Maybe<&2, List<&2, Word(8n)>>, List<&2, Word(8n)>, x => Maybe.default(&2, List<&2, Word(8n)>, x, Nil{}), Some{Pg.Program.name.nil()}, Some{k},
        Tr(Nat, t => {List.get(&2, List<&2, Word(8n)>, Mc.Img.known(ks2), t) == Some{k} : Maybe<&2, List<&2, Word(8n)>>}, U32.to_nat(j), 1n, etn, ek))
      Empty.absurd({U32.is_eq(j, 1) == False{} : Bool}, PN.true_ne_false(Tr(List<&2, Word(8n)>, y => {Sd.Name.is_eq(Pg.Program.name.nil(), y) == False{} : Bool}, k, Pg.Program.name.nil(),
        Equal.sym(List<&2, Word(8n)>, Pg.Program.name.nil(), k, enk), en)))

def lab.ne2(b: Bool, +ks2: List<&2, List<&2, Word(8n)>>, +j: U32, +k: List<&2, Word(8n)>, +ek: {T.tm.name(Mc.Img.known(ks2), j) == Some{k} : Maybe<&2, List<&2, Word(8n)>>},
  +en: {Sd.Name.is_eq(Pg.Program.name.con(), k) == False{} : Bool}, +eb: {U32.is_eq(j, 2) == b : Bool}) -> {U32.is_eq(j, 2) == False{} : Bool}:
  match b:
    case False{}:
      eb
    case True{}:
      +etn = eq_nat(j, 2, eb)
      +enk = Equal.cong(Maybe<&2, List<&2, Word(8n)>>, List<&2, Word(8n)>, x => Maybe.default(&2, List<&2, Word(8n)>, x, Nil{}), Some{Pg.Program.name.con()}, Some{k},
        Tr(Nat, t => {List.get(&2, List<&2, Word(8n)>, Mc.Img.known(ks2), t) == Some{k} : Maybe<&2, List<&2, Word(8n)>>}, U32.to_nat(j), 2n, etn, ek))
      Empty.absurd({U32.is_eq(j, 2) == False{} : Bool}, PN.true_ne_false(Tr(List<&2, Word(8n)>, y => {Sd.Name.is_eq(Pg.Program.name.con(), y) == False{} : Bool}, k, Pg.Program.name.con(),
        Equal.sym(List<&2, Word(8n)>, Pg.Program.name.con(), k, enk), en)))

def lab.ne3(b: Bool, +ks2: List<&2, List<&2, Word(8n)>>, +j: U32, +k: List<&2, Word(8n)>, +ek: {T.tm.name(Mc.Img.known(ks2), j) == Some{k} : Maybe<&2, List<&2, Word(8n)>>},
  +en: {Sd.Name.is_eq(Pg.Program.name.wnil(), k) == False{} : Bool}, +eb: {U32.is_eq(j, 3) == b : Bool}) -> {U32.is_eq(j, 3) == False{} : Bool}:
  match b:
    case False{}:
      eb
    case True{}:
      +etn = eq_nat(j, 3, eb)
      +enk = Equal.cong(Maybe<&2, List<&2, Word(8n)>>, List<&2, Word(8n)>, x => Maybe.default(&2, List<&2, Word(8n)>, x, Nil{}), Some{Pg.Program.name.wnil()}, Some{k},
        Tr(Nat, t => {List.get(&2, List<&2, Word(8n)>, Mc.Img.known(ks2), t) == Some{k} : Maybe<&2, List<&2, Word(8n)>>}, U32.to_nat(j), 3n, etn, ek))
      Empty.absurd({U32.is_eq(j, 3) == False{} : Bool}, PN.true_ne_false(Tr(List<&2, Word(8n)>, y => {Sd.Name.is_eq(Pg.Program.name.wnil(), y) == False{} : Bool}, k, Pg.Program.name.wnil(),
        Equal.sym(List<&2, Word(8n)>, Pg.Program.name.wnil(), k, enk), en)))

def lab.ne4(b: Bool, +ks2: List<&2, List<&2, Word(8n)>>, +j: U32, +k: List<&2, Word(8n)>, +ek: {T.tm.name(Mc.Img.known(ks2), j) == Some{k} : Maybe<&2, List<&2, Word(8n)>>},
  +en: {Sd.Name.is_eq(Pg.Program.name.wcon(), k) == False{} : Bool}, +eb: {U32.is_eq(j, 4) == b : Bool}) -> {U32.is_eq(j, 4) == False{} : Bool}:
  match b:
    case False{}:
      eb
    case True{}:
      +etn = eq_nat(j, 4, eb)
      +enk = Equal.cong(Maybe<&2, List<&2, Word(8n)>>, List<&2, Word(8n)>, x => Maybe.default(&2, List<&2, Word(8n)>, x, Nil{}), Some{Pg.Program.name.wcon()}, Some{k},
        Tr(Nat, t => {List.get(&2, List<&2, Word(8n)>, Mc.Img.known(ks2), t) == Some{k} : Maybe<&2, List<&2, Word(8n)>>}, U32.to_nat(j), 4n, etn, ek))
      Empty.absurd({U32.is_eq(j, 4) == False{} : Bool}, PN.true_ne_false(Tr(List<&2, Word(8n)>, y => {Sd.Name.is_eq(Pg.Program.name.wcon(), y) == False{} : Bool}, k, Pg.Program.name.wcon(),
        Equal.sym(List<&2, Word(8n)>, Pg.Program.name.wcon(), k, enk), en)))

def lab.ne5(b: Bool, +ks2: List<&2, List<&2, Word(8n)>>, +j: U32, +k: List<&2, Word(8n)>, +ek: {T.tm.name(Mc.Img.known(ks2), j) == Some{k} : Maybe<&2, List<&2, Word(8n)>>},
  +en: {Sd.Name.is_eq(Pg.Program.name.true(), k) == False{} : Bool}, +eb: {U32.is_eq(j, 5) == b : Bool}) -> {U32.is_eq(j, 5) == False{} : Bool}:
  match b:
    case False{}:
      eb
    case True{}:
      +etn = eq_nat(j, 5, eb)
      +enk = Equal.cong(Maybe<&2, List<&2, Word(8n)>>, List<&2, Word(8n)>, x => Maybe.default(&2, List<&2, Word(8n)>, x, Nil{}), Some{Pg.Program.name.true()}, Some{k},
        Tr(Nat, t => {List.get(&2, List<&2, Word(8n)>, Mc.Img.known(ks2), t) == Some{k} : Maybe<&2, List<&2, Word(8n)>>}, U32.to_nat(j), 5n, etn, ek))
      Empty.absurd({U32.is_eq(j, 5) == False{} : Bool}, PN.true_ne_false(Tr(List<&2, Word(8n)>, y => {Sd.Name.is_eq(Pg.Program.name.true(), y) == False{} : Bool}, k, Pg.Program.name.true(),
        Equal.sym(List<&2, Word(8n)>, Pg.Program.name.true(), k, enk), en)))

def lab.ne6(b: Bool, +ks2: List<&2, List<&2, Word(8n)>>, +j: U32, +k: List<&2, Word(8n)>, +ek: {T.tm.name(Mc.Img.known(ks2), j) == Some{k} : Maybe<&2, List<&2, Word(8n)>>},
  +en: {Sd.Name.is_eq(Pg.Program.name.false(), k) == False{} : Bool}, +eb: {U32.is_eq(j, 6) == b : Bool}) -> {U32.is_eq(j, 6) == False{} : Bool}:
  match b:
    case False{}:
      eb
    case True{}:
      +etn = eq_nat(j, 6, eb)
      +enk = Equal.cong(Maybe<&2, List<&2, Word(8n)>>, List<&2, Word(8n)>, x => Maybe.default(&2, List<&2, Word(8n)>, x, Nil{}), Some{Pg.Program.name.false()}, Some{k},
        Tr(Nat, t => {List.get(&2, List<&2, Word(8n)>, Mc.Img.known(ks2), t) == Some{k} : Maybe<&2, List<&2, Word(8n)>>}, U32.to_nat(j), 6n, etn, ek))
      Empty.absurd({U32.is_eq(j, 6) == False{} : Bool}, PN.true_ne_false(Tr(List<&2, Word(8n)>, y => {Sd.Name.is_eq(Pg.Program.name.false(), y) == False{} : Bool}, k, Pg.Program.name.false(),
        Equal.sym(List<&2, Word(8n)>, Pg.Program.name.false(), k, enk), en)))

def lab.none(+ks2: List<&2, List<&2, Word(8n)>>, +j: U32, +k: List<&2, Word(8n)>, +ek: {T.tm.name(Mc.Img.known(ks2), j) == Some{k} : Maybe<&2, List<&2, Word(8n)>>},
  +e0: {Sd.Name.is_eq(Pg.Program.name.unit(), k) == False{} : Bool}, +e1: {Sd.Name.is_eq(Pg.Program.name.nil(), k) == False{} : Bool}, +e2: {Sd.Name.is_eq(Pg.Program.name.con(), k) == False{} : Bool}, +e3: {Sd.Name.is_eq(Pg.Program.name.wnil(), k) == False{} : Bool}, +e4: {Sd.Name.is_eq(Pg.Program.name.wcon(), k) == False{} : Bool}, +e5: {Sd.Name.is_eq(Pg.Program.name.true(), k) == False{} : Bool}, +e6: {Sd.Name.is_eq(Pg.Program.name.false(), k) == False{} : Bool}) -> {known.ok(j, k) == True{} : Bool}:
  KO.rw(k, j, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, Equal.trans(Bool, Sd.Name.is_eq(k, Pg.Program.name.unit()), Sd.Name.is_eq(Pg.Program.name.unit(), k), False{}, Nsym(k, Pg.Program.name.unit()), e0), Equal.trans(Bool, Sd.Name.is_eq(k, Pg.Program.name.nil()), Sd.Name.is_eq(Pg.Program.name.nil(), k), False{}, Nsym(k, Pg.Program.name.nil()), e1), Equal.trans(Bool, Sd.Name.is_eq(k, Pg.Program.name.con()), Sd.Name.is_eq(Pg.Program.name.con(), k), False{}, Nsym(k, Pg.Program.name.con()), e2), Equal.trans(Bool, Sd.Name.is_eq(k, Pg.Program.name.wnil()), Sd.Name.is_eq(Pg.Program.name.wnil(), k), False{}, Nsym(k, Pg.Program.name.wnil()), e3), Equal.trans(Bool, Sd.Name.is_eq(k, Pg.Program.name.wcon()), Sd.Name.is_eq(Pg.Program.name.wcon(), k), False{}, Nsym(k, Pg.Program.name.wcon()), e4), Equal.trans(Bool, Sd.Name.is_eq(k, Pg.Program.name.true()), Sd.Name.is_eq(Pg.Program.name.true(), k), False{}, Nsym(k, Pg.Program.name.true()), e5), Equal.trans(Bool, Sd.Name.is_eq(k, Pg.Program.name.false()), Sd.Name.is_eq(Pg.Program.name.false(), k), False{}, Nsym(k, Pg.Program.name.false()), e6), lab.ne0(U32.is_eq(j, 0), ks2, j, k, ek, e0, {==}), lab.ne1(U32.is_eq(j, 1), ks2, j, k, ek, e1, {==}), lab.ne2(U32.is_eq(j, 2), ks2, j, k, ek, e2, {==}), lab.ne3(U32.is_eq(j, 3), ks2, j, k, ek, e3, {==}), lab.ne4(U32.is_eq(j, 4), ks2, j, k, ek, e4, {==}), lab.ne5(U32.is_eq(j, 5), ks2, j, k, ek, e5, {==}), lab.ne6(U32.is_eq(j, 6), ks2, j, k, ek, e6, {==}), {==})

def lab.cases(b0: Bool, b1: Bool, b2: Bool, b3: Bool, b4: Bool, b5: Bool, b6: Bool, +ks2: List<&2, List<&2, Word(8n)>>, +j: U32, +k: List<&2, Word(8n)>, +e0: {Sd.Name.is_eq(Pg.Program.name.unit(), k) == b0 : Bool}, +e1: {Sd.Name.is_eq(Pg.Program.name.nil(), k) == b1 : Bool}, +e2: {Sd.Name.is_eq(Pg.Program.name.con(), k) == b2 : Bool}, +e3: {Sd.Name.is_eq(Pg.Program.name.wnil(), k) == b3 : Bool}, +e4: {Sd.Name.is_eq(Pg.Program.name.wcon(), k) == b4 : Bool}, +e5: {Sd.Name.is_eq(Pg.Program.name.true(), k) == b5 : Bool}, +e6: {Sd.Name.is_eq(Pg.Program.name.false(), k) == b6 : Bool},
  +ek: {T.tm.name(Mc.Img.known(ks2), j) == Some{k} : Maybe<&2, List<&2, Word(8n)>>},
  +ej: {U32.is_eq(j, Mc.Img.id(Mc.Img.known(ks2), k, 0)) == True{} : Bool}) -> {known.ok(j, k) == True{} : Bool}:
  match b0:
    case True{}:
      lab.at0(ks2, j, k, ek, ej, e0)
    case False{}:
      match b1:
        case True{}:
          lab.at1(ks2, j, k, ek, ej, e0, e1)
        case False{}:
          match b2:
            case True{}:
              lab.at2(ks2, j, k, ek, ej, e0, e1, e2)
            case False{}:
              match b3:
                case True{}:
                  lab.at3(ks2, j, k, ek, ej, e0, e1, e2, e3)
                case False{}:
                  match b4:
                    case True{}:
                      lab.at4(ks2, j, k, ek, ej, e0, e1, e2, e3, e4)
                    case False{}:
                      match b5:
                        case True{}:
                          lab.at5(ks2, j, k, ek, ej, e0, e1, e2, e3, e4, e5)
                        case False{}:
                          match b6:
                            case True{}:
                              lab.at6(ks2, j, k, ek, ej, e0, e1, e2, e3, e4, e5, e6)
                            case False{}:
                              lab.none(ks2, j, k, ek, e0, e1, e2, e3, e4, e5, e6)

# the number j of a label is the number of its name
def labid.of(n: Maybe<&2, List<&2, Word(8n)>>, +j: U32, +ks: List<&2, List<&2, Word(8n)>>) -> Bool:
  match n:
    case None{}:
      True{}
    case Some{+k}:
      U32.is_eq(j, Mc.Img.id(ks, k, 0))

def labid(+ks: List<&2, List<&2, Word(8n)>>, +j: U32) -> Bool:
  labid.of(T.tm.name(ks, j), j, ks)

def labid.ok.of(n: Maybe<&2, List<&2, Word(8n)>>, +ks2: List<&2, List<&2, Word(8n)>>, +j: U32,
  +en: {T.tm.name(Mc.Img.known(ks2), j) == n : Maybe<&2, List<&2, Word(8n)>>}, +h: {labid.of(n, j, Mc.Img.known(ks2)) == True{} : Bool}) ->
  {labok.of(n, j) == True{} : Bool}:
  match n:
    case None{}:
      {==}
    case Some{+k}:
      lab.cases(Sd.Name.is_eq(Pg.Program.name.unit(), k), Sd.Name.is_eq(Pg.Program.name.nil(), k), Sd.Name.is_eq(Pg.Program.name.con(), k), Sd.Name.is_eq(Pg.Program.name.wnil(), k), Sd.Name.is_eq(Pg.Program.name.wcon(), k), Sd.Name.is_eq(Pg.Program.name.true(), k), Sd.Name.is_eq(Pg.Program.name.false(), k), ks2, j, k, {==}, {==}, {==}, {==}, {==}, {==}, {==}, en, h)

# a label that holds the number of its name is one that ok accepts
def labid.ok(+ks2: List<&2, List<&2, Word(8n)>>, +j: U32, +h: {labid(Mc.Img.known(ks2), j) == True{} : Bool}) ->
  {labok(Mc.Img.known(ks2), j) == True{} : Bool}:
  labid.ok.of(T.tm.name(Mc.Img.known(ks2), j), ks2, j, {==}, h)

# ok, with labels that hold the number of their name (labid) in place of
# labok
def okn.lab(+t: U32, +ks: List<&2, List<&2, Word(8n)>>, +j: U32) -> Bool:
  Bool.or(Bool.not(U32.is_eq(t, 13)), labid(ks, j))

def okn(+fuel: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32,
  +fs: U32, +nx: U32) -> Bool:
  match fuel:
    case 0n:
      False{}
    case 1n+f:
      +t = Tg(m, c)
      Bool.and(Bool.and(Bool.and(Cr.Cir.is_cell(c, im, fs, nx), ok.img(t, T.tm.image(img, c))), okn.lab(t, ks, Fd(2n, m, c))),
        Bool.or(Bool.not(U32.is_eq(t, 10)),
          Bool.and(okn(f, m, ks, img, Fd(2n, m, c), im, fs, nx), okn(f, m, ks, img, Fd(3n, m, c), im, fs, nx))))

def and_i(a: Bool, -b: Bool, +ea: {a == True{} : Bool}, +eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      Empty.absurd({Bool.and(False{}, b) == True{} : Bool}, PN.false_ne_true(ea))

def or_imp(x: Bool, -y: Bool, -z: Bool, +h: {Bool.or(Bool.not(x), y) == True{} : Bool}, k: {y == True{} : Bool} -> {z == True{} : Bool}) ->
  {Bool.or(Bool.not(x), z) == True{} : Bool}:
  match x:
    case True{}:
      k(h)
    case False{}:
      {==}

# okn gives ok, when the names are the machine's first
def okn.ok(+fuel: Nat, +m: Cr.Cir.Cells, +ks2: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32,
  +h: {okn(fuel, m, Mc.Img.known(ks2), img, c, im, fs, nx) == True{} : Bool}) ->
  {ok(fuel, m, Mc.Img.known(ks2), img, c, im, fs, nx) == True{} : Bool}:
  match fuel:
    case 0n:
      h
    case 1n+f:
      +ks = Mc.Img.known(ks2)
      +t = Tg(m, c)
      +IC = Cr.Cir.is_cell(c, im, fs, nx)
      +IM = ok.img(t, T.tm.image(img, c))
      +L2 = okn.lab(t, ks, Fd(2n, m, c))
      +K2 = Bool.or(Bool.not(U32.is_eq(t, 10)), Bool.and(okn(f, m, ks, img, Fd(2n, m, c), im, fs, nx), okn(f, m, ks, img, Fd(3n, m, c), im, fs, nx)))
      +h1 = and_l(Bool.and(Bool.and(IC, IM), L2), K2, h)
      +h2 = and_l(Bool.and(IC, IM), L2, h1)
      +hl = and_r(Bool.and(IC, IM), L2, h1)
      +hk = and_r(Bool.and(Bool.and(IC, IM), L2), K2, h)
      and_i(Bool.and(Bool.and(IC, IM), ok.lab(t, ks, Fd(2n, m, c))),
        Bool.or(Bool.not(U32.is_eq(t, 10)), Bool.and(ok(f, m, ks, img, Fd(2n, m, c), im, fs, nx), ok(f, m, ks, img, Fd(3n, m, c), im, fs, nx))),
        and_i(Bool.and(IC, IM), ok.lab(t, ks, Fd(2n, m, c)), h2,
          or_imp(U32.is_eq(t, 13), labid(ks, Fd(2n, m, c)), labok(ks, Fd(2n, m, c)), hl, e => labid.ok(ks2, Fd(2n, m, c), e))),
        or_imp(U32.is_eq(t, 10), Bool.and(okn(f, m, ks, img, Fd(2n, m, c), im, fs, nx), okn(f, m, ks, img, Fd(3n, m, c), im, fs, nx)),
          Bool.and(ok(f, m, ks, img, Fd(2n, m, c), im, fs, nx), ok(f, m, ks, img, Fd(3n, m, c), im, fs, nx)), hk,
          +e => and_i(ok(f, m, ks, img, Fd(2n, m, c), im, fs, nx), ok(f, m, ks, img, Fd(3n, m, c), im, fs, nx),
            okn.ok(f, m, ks2, img, Fd(2n, m, c), im, fs, nx, and_l(okn(f, m, ks, img, Fd(2n, m, c), im, fs, nx), okn(f, m, ks, img, Fd(3n, m, c), im, fs, nx), e)),
            okn.ok(f, m, ks2, img, Fd(3n, m, c), im, fs, nx, and_r(okn(f, m, ks, img, Fd(2n, m, c), im, fs, nx), okn(f, m, ks, img, Fd(3n, m, c), im, fs, nx), e)))))

# THE LEMMA, with the image's names: ks is C.Img.known(ks2), and every label
# that the walk reads holds the number of its name (okn)
def out.known(+n: Nat, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fs: U32, +im: U32,
  +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +out: List<&2, Word(8n)>, +outn: U32, +c: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +ks2: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +v: Bk.Term,
  +hreg: {List.get(&2, U32, regs, Mc.R.focus()) == Some{c} : Maybe<&2, U32>},
  +hlen: {Nat.is_le(Mc.Mach.regs(), List.length(&2, U32, regs)) == True{} : Bool},
  +htm: {T.tm.of(n, m, ks, img, c) == Some{v} : Maybe<&2, Bk.Term>},
  +hk: {ks == Mc.Img.known(ks2) : List<&2, List<&2, Word(8n)>>},
  +hok: {okn(n, m, ks, img, c, im, fs, nx) == True{} : Bool}) ->
  &F: Nat -> Gives(Cr.Cir.exec(F, Mc.M.out(), Cr.Cir.State{regs, m, nx, fs, im, pg, lim, inp, out, outn}), Pg.Program.unbytes(v), out, outn, OBn(lim, nx, Nat.add(U32.to_nat(outn), n))):
  out.gives(n, regs, m, nx, fs, im, pg, lim, inp, out, outn, c, ks, img, v, hreg, hlen, htm,
    Tr(List<&2, List<&2, Word(8n)>>, x => {ok(n, m, x, img, c, im, fs, nx) == True{} : Bool}, Mc.Img.known(ks2), ks,
      Equal.sym(List<&2, List<&2, Word(8n)>>, ks, Mc.Img.known(ks2), hk),
      okn.ok(n, m, ks2, img, c, im, fs, nx,
        Tr(List<&2, List<&2, Word(8n)>>, x => {okn(n, m, x, img, c, im, fs, nx) == True{} : Bool}, ks, Mc.Img.known(ks2), hk, hok))))

# More fuel keeps an ended run
# ----------------------------

# a ends, and b is a; or a runs out of fuel
def OMc(a: Cr.Cir.Out, b: Cr.Cir.Out) -> Type:
  match a:
    case Cr.Cir.Out.next{st}:
      {Cr.Cir.Out.next{st} == b : Cr.Cir.Out}
    case Cr.Cir.Out.halt{s, st}:
      {Cr.Cir.Out.halt{s, st} == b : Cr.Cir.Out}
    case Cr.Cir.Out.out_of_memory{}:
      {Cr.Cir.Out.out_of_memory{} == b : Cr.Cir.Out}
    case Cr.Cir.Out.trap{}:
      {Cr.Cir.Out.trap{} == b : Cr.Cir.Out}
    case Cr.Cir.Out.not_done{}:
      Unit

def OMc.refl(x: Cr.Cir.Out) -> OMc(x, x):
  match x:
    case Cr.Cir.Out.next{st}:
      {==}
    case Cr.Cir.Out.halt{s, st}:
      {==}
    case Cr.Cir.Out.out_of_memory{}:
      {==}
    case Cr.Cir.Out.trap{}:
      {==}
    case Cr.Cir.Out.not_done{}:
      Unit{}

def OMc.then(a: Cr.Cir.Out, -b: Cr.Cir.Out, -k1: Cr.Cir.State -> Cr.Cir.Out, -k2: Cr.Cir.State -> Cr.Cir.Out, hab: OMc(a, b),
  hk: @t: Cr.Cir.State -> OMc(k1(t), k2(t))) -> OMc(Cr.Cir.exec.then(a, k1), Cr.Cir.exec.then(b, k2)):
  match a:
    case Cr.Cir.Out.next{st}:
      %hab : OMc(k1(st), Cr.Cir.exec.then(_, k2))
      hk(st)
    case Cr.Cir.Out.halt{s, st}:
      %hab : {Cr.Cir.Out.halt{s, st} == Cr.Cir.exec.then(_, k2) : Cr.Cir.Out}
      {==}
    case Cr.Cir.Out.out_of_memory{}:
      %hab : {Cr.Cir.Out.out_of_memory{} == Cr.Cir.exec.then(_, k2) : Cr.Cir.Out}
      {==}
    case Cr.Cir.Out.trap{}:
      %hab : {Cr.Cir.Out.trap{} == Cr.Cir.exec.then(_, k2) : Cr.Cir.Out}
      {==}
    case Cr.Cir.Out.not_done{}:
      Unit{}

def OMc.ifof(z: Bool, -y1: Unit -> Cr.Cir.Out, -n1: Unit -> Cr.Cir.Out, -y2: Unit -> Cr.Cir.Out, -n2: Unit -> Cr.Cir.Out,
  hy: OMc(y1(Unit{}), y2(Unit{})), hn: OMc(n1(Unit{}), n2(Unit{}))) -> OMc(Cr.Cir.exec.if.of(z, y1, n1), Cr.Cir.exec.if.of(z, y2, n2)):
  match z:
    case False{}:
      hy
    case True{}:
      hn

def OMc.if(v: Maybe<&2, U32>, -y1: Unit -> Cr.Cir.Out, -n1: Unit -> Cr.Cir.Out, -y2: Unit -> Cr.Cir.Out, -n2: Unit -> Cr.Cir.Out,
  hy: OMc(y1(Unit{}), y2(Unit{})), hn: OMc(n1(Unit{}), n2(Unit{}))) -> OMc(Cr.Cir.exec.if(v, y1, n1), Cr.Cir.exec.if(v, y2, n2)):
  match v:
    case Some{+x}:
      OMc.ifof(U32.is_zero(x), y1, n1, y2, n2, hy, hn)
    case None{}:
      {==}

# a run with no fuel, and with some
def EM0(s: Cr.Cir.Stmt, +g: Nat, +st: Cr.Cir.State) -> OMc(Cr.Cir.exec(0n, s, st), Cr.Cir.exec(1n+g, s, st)):
  match s:
    case Cr.Cir.Stmt.nop{}:
      {==}
    case Cr.Cir.Stmt.set{+r, +e}:
      OMc.refl(Cr.Cir.exec(0n, Cr.Cir.Stmt.set{r, e}, st))
    case Cr.Cir.Stmt.store{+k, +a, +v}:
      OMc.refl(Cr.Cir.exec(0n, Cr.Cir.Stmt.store{k, a, v}, st))
    case Cr.Cir.Stmt.alloc{+r}:
      OMc.refl(Cr.Cir.exec(0n, Cr.Cir.Stmt.alloc{r}, st))
    case Cr.Cir.Stmt.emit{+v}:
      OMc.refl(Cr.Cir.exec(0n, Cr.Cir.Stmt.emit{v}, st))
    case Cr.Cir.Stmt.seq{+a, +b}:
      OMc.then(Cr.Cir.exec(0n, a, st), Cr.Cir.exec(1n+g, a, st), u => Cr.Cir.exec(0n, b, u), u => Cr.Cir.exec(1n+g, b, u),
        EM0(a, g, st), u => EM0(b, g, u))
    case Cr.Cir.Stmt.if{+c, +x, +y}:
      OMc.if(Cr.Cir.eval(c, st), u => Cr.Cir.exec(0n, x, st), u => Cr.Cir.exec(0n, y, st), u => Cr.Cir.exec(1n+g, x, st), u => Cr.Cir.exec(1n+g, y, st),
        EM0(x, g, st), EM0(y, g, st))
    case Cr.Cir.Stmt.while{_, _}:
      Unit{}
    case Cr.Cir.Stmt.halt{+h}:
      {==}

# a run that ends with the fuel f ends the same with f + g
def EM(+f: Nat, +g: Nat, s: Cr.Cir.Stmt, +st: Cr.Cir.State) -> OMc(Cr.Cir.exec(f, s, st), Cr.Cir.exec(Nat.add(f, g), s, st)):
  match f:
    case 0n:
      match g:
        case 0n:
          OMc.refl(Cr.Cir.exec(0n, s, st))
        case 1n+h:
          EM0(s, h, st)
    case 1n+p:
      match s:
        case Cr.Cir.Stmt.nop{}:
          {==}
        case Cr.Cir.Stmt.set{+r, +e}:
          OMc.refl(Cr.Cir.exec(1n+p, Cr.Cir.Stmt.set{r, e}, st))
        case Cr.Cir.Stmt.store{+k, +a, +v}:
          OMc.refl(Cr.Cir.exec(1n+p, Cr.Cir.Stmt.store{k, a, v}, st))
        case Cr.Cir.Stmt.alloc{+r}:
          OMc.refl(Cr.Cir.exec(1n+p, Cr.Cir.Stmt.alloc{r}, st))
        case Cr.Cir.Stmt.emit{+v}:
          OMc.refl(Cr.Cir.exec(1n+p, Cr.Cir.Stmt.emit{v}, st))
        case Cr.Cir.Stmt.seq{+a, +b}:
          OMc.then(Cr.Cir.exec(1n+p, a, st), Cr.Cir.exec(1n+Nat.add(p, g), a, st), u => Cr.Cir.exec(1n+p, b, u), u => Cr.Cir.exec(1n+Nat.add(p, g), b, u),
            EM(1n+p, g, a, st), u => EM(1n+p, g, b, u))
        case Cr.Cir.Stmt.if{+c, +x, +y}:
          OMc.if(Cr.Cir.eval(c, st), u => Cr.Cir.exec(1n+p, x, st), u => Cr.Cir.exec(1n+p, y, st), u => Cr.Cir.exec(1n+Nat.add(p, g), x, st),
            u => Cr.Cir.exec(1n+Nat.add(p, g), y, st), EM(1n+p, g, x, st), EM(1n+p, g, y, st))
        case Cr.Cir.Stmt.while{+c, +body}:
          OMc.if(Cr.Cir.eval(c, st), u => Cr.Cir.exec.then(Cr.Cir.exec(p, body, st), t => Cr.Cir.exec(p, Cr.Cir.Stmt.while{c, body}, t)), u => Cr.Cir.Out.next{st},
            u => Cr.Cir.exec.then(Cr.Cir.exec(Nat.add(p, g), body, st), t => Cr.Cir.exec(Nat.add(p, g), Cr.Cir.Stmt.while{c, body}, t)), u => Cr.Cir.Out.next{st},
            OMc.then(Cr.Cir.exec(p, body, st), Cr.Cir.exec(Nat.add(p, g), body, st), t => Cr.Cir.exec(p, Cr.Cir.Stmt.while{c, body}, t),
              t => Cr.Cir.exec(Nat.add(p, g), Cr.Cir.Stmt.while{c, body}, t), EM(p, g, body, st), t => EM(p, g, Cr.Cir.Stmt.while{c, body}, t)),
            {==})
        case Cr.Cir.Stmt.halt{+h}:
          {==}

# Gives, or out of fuel
def GivesF(o: Cr.Cir.Out, r: Maybe<&2, List<&2, Word(8n)>>, out0: List<&2, Word(8n)>, outn0: U32, O: Type) -> Type:
  match o:
    case Cr.Cir.Out.next{_}:
      Empty
    case Cr.Cir.Out.halt{s, st}:
      Gives.halt(r, out0, outn0, s, st)
    case Cr.Cir.Out.out_of_memory{}:
      O
    case Cr.Cir.Out.trap{}:
      Empty
    case Cr.Cir.Out.not_done{}:
      Unit

def GivesF.of(a: Cr.Cir.Out, -b: Cr.Cir.Out, -r: Maybe<&2, List<&2, Word(8n)>>, -out0: List<&2, Word(8n)>, -outn0: U32, -O: Type,
  hab: OMc(a, b), g: Gives(b, r, out0, outn0, O)) -> GivesF(a, r, out0, outn0, O):
  match a:
    case Cr.Cir.Out.next{st}:
      Empty.absurd(GivesF(Cr.Cir.Out.next{st}, r, out0, outn0, O),
        Tr(Cr.Cir.Out, x => Gives(x, r, out0, outn0, O), b, Cr.Cir.Out.next{st}, Equal.sym(Cr.Cir.Out, Cr.Cir.Out.next{st}, b, hab), g))
    case Cr.Cir.Out.halt{s, st}:
      Tr(Cr.Cir.Out, x => Gives(x, r, out0, outn0, O), b, Cr.Cir.Out.halt{s, st}, Equal.sym(Cr.Cir.Out, Cr.Cir.Out.halt{s, st}, b, hab), g)
    case Cr.Cir.Out.out_of_memory{}:
      Tr(Cr.Cir.Out, x => Gives(x, r, out0, outn0, O), b, Cr.Cir.Out.out_of_memory{}, Equal.sym(Cr.Cir.Out, Cr.Cir.Out.out_of_memory{}, b, hab), g)
    case Cr.Cir.Out.trap{}:
      Empty.absurd(GivesF(Cr.Cir.Out.trap{}, r, out0, outn0, O),
        Tr(Cr.Cir.Out, x => Gives(x, r, out0, outn0, O), b, Cr.Cir.Out.trap{}, Equal.sym(Cr.Cir.Out, Cr.Cir.Out.trap{}, b, hab), g))
    case Cr.Cir.Out.not_done{}:
      Unit{}

# THE LEMMA, for any fuel F: M.out gives Program.unbytes(v), or runs out of
# fuel
def out.any(+n: Nat, +F: Nat, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fs: U32, +im: U32,
  +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +out: List<&2, Word(8n)>, +outn: U32, +c: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +v: Bk.Term,
  +hreg: {List.get(&2, U32, regs, Mc.R.focus()) == Some{c} : Maybe<&2, U32>},
  +hlen: {Nat.is_le(Mc.Mach.regs(), List.length(&2, U32, regs)) == True{} : Bool},
  +htm: {T.tm.of(n, m, ks, img, c) == Some{v} : Maybe<&2, Bk.Term>},
  +hok: {ok(n, m, ks, img, c, im, fs, nx) == True{} : Bool}) ->
  GivesF(Cr.Cir.exec(F, Mc.M.out(), Cr.Cir.State{regs, m, nx, fs, im, pg, lim, inp, out, outn}), Pg.Program.unbytes(v), out, outn, OBn(lim, nx, Nat.add(U32.to_nat(outn), n))):
  +X = Nat.add(n, 34n)
  +st = {Cr.Cir.State{regs, m, nx, fs, im, pg, lim, inp, out, outn} : Cr.Cir.State}
  GivesF.of(Cr.Cir.exec(F, Mc.M.out(), st), Cr.Cir.exec(Nat.add(F, 1n+X), Mc.M.out(), st), Pg.Program.unbytes(v), out, outn, OBn(lim, nx, Nat.add(U32.to_nat(outn), n)),
    EM(F, 1n+X, Mc.M.out(), st),
    Tr(Nat, k => Gives(Cr.Cir.exec(k, Mc.M.out(), st), Pg.Program.unbytes(v), out, outn, OBn(lim, nx, Nat.add(U32.to_nat(outn), n))), 1n+Nat.add(F, X), Nat.add(F, 1n+X),
      Equal.sym(Nat, Nat.add(F, 1n+X), 1n+Nat.add(F, X), PN.add_succ_r(F, X)),
      out.run(n, Nat.add(F, X), PN.le_succ(X, Nat.add(F, X), PN.le_add_l(F, X)), regs, m, nx, fs, im, pg, lim, inp, out, outn, c, ks, img, v,
        hreg, hlen, htm, hok)))

# The halts of out.post
# ---------------------

def app_nil(xs: List<&2, Word(8n)>) -> {List.append(&2, Word(8n), xs, Nil{}) == xs : List<&2, Word(8n)>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %Equal.sym(List<&2, Word(8n)>, List.append(&2, Word(8n), t, Nil{}), t, app_nil(t)) : {Con{h, _} == Con{h, t} : List<&2, Word(8n)>}
      {==}

def rev_rev.go(xs: List<&2, Word(8n)>, +ys: List<&2, Word(8n)>) ->
  {List.reverse.go(&2, Word(8n), List.reverse.go(&2, Word(8n), xs, ys), Nil{}) == List.reverse.go(&2, Word(8n), ys, xs) : List<&2, Word(8n)>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      rev_rev.go(t, Con{h, ys})

def rev_rev(+xs: List<&2, Word(8n)>) -> {List.reverse(&2, Word(8n), List.reverse(&2, Word(8n), xs)) == xs : List<&2, Word(8n)>}:
  rev_rev.go(xs, Nil{})

# a halt with the status s in the state st2: with 0 and the bytes of v out (the
# last first), or with 2 when v has none (OutH of moves.bend)
def OutH(+v: Bk.Term, +s: U32, st2: Cr.Cir.State) -> Data:
  Either<&2, &2, PD({s == 0 : U32}, {Pg.Program.unbytes(v) == Some{List.reverse(&2, Word(8n), St.out(st2))} : Maybe<&2, List<&2, Word(8n)>>}),
    PD({s == 2 : U32}, {Pg.Program.unbytes(v) == None{} : Maybe<&2, List<&2, Word(8n)>>})>

def OutH.of(r: Maybe<&2, List<&2, Word(8n)>>, +v: Bk.Term, +s: U32, +st: Cr.Cir.State, +er: {Pg.Program.unbytes(v) == r : Maybe<&2, List<&2, Word(8n)>>},
  h: Gives.halt(r, Nil{}, 0, s, st)) -> OutH(v, s, st):
  match r:
    case Some{+bs}:
      (e0, rest) = h
      (eo, en) = rest
      +e1 = Equal.trans(List<&2, Word(8n)>, List.reverse(&2, Word(8n), St.out(st)), List.reverse(&2, Word(8n), List.append(&2, Word(8n), List.reverse(&2, Word(8n), bs), Nil{})), bs,
        Equal.cong(List<&2, Word(8n)>, List<&2, Word(8n)>, xs => List.reverse(&2, Word(8n), xs), St.out(st), List.append(&2, Word(8n), List.reverse(&2, Word(8n), bs), Nil{}), eo),
        Equal.trans(List<&2, Word(8n)>, List.reverse(&2, Word(8n), List.append(&2, Word(8n), List.reverse(&2, Word(8n), bs), Nil{})), List.reverse(&2, Word(8n), List.reverse(&2, Word(8n), bs)), bs,
          Equal.cong(List<&2, Word(8n)>, List<&2, Word(8n)>, xs => List.reverse(&2, Word(8n), xs), List.append(&2, Word(8n), List.reverse(&2, Word(8n), bs), Nil{}), List.reverse(&2, Word(8n), bs),
            app_nil(List.reverse(&2, Word(8n), bs))),
          rev_rev(bs)))
      Inl{(e0, Equal.trans(Maybe<&2, List<&2, Word(8n)>>, Pg.Program.unbytes(v), Some{bs}, Some{List.reverse(&2, Word(8n), St.out(st))}, er,
        Equal.cong(List<&2, Word(8n)>, Maybe<&2, List<&2, Word(8n)>>, xs => Some{xs}, bs, List.reverse(&2, Word(8n), St.out(st)),
          Equal.sym(List<&2, Word(8n)>, List.reverse(&2, Word(8n), St.out(st)), bs, e1))))}
    case None{}:
      Inr{(h, er)}

# what the outcome o of M.out may be (Post(False, o, st => Empty, s => st2 =>
# OutH(v, s, st2)) of moves.bend): a halt as OutH says, out of memory,
# or out of fuel
def PostO(o: Cr.Cir.Out, +v: Bk.Term) -> Type:
  match o:
    case Cr.Cir.Out.next{st}:
      Empty
    case Cr.Cir.Out.halt{s, st}:
      OutH(v, s, st)
    case Cr.Cir.Out.out_of_memory{}:
      Unit
    case Cr.Cir.Out.trap{}:
      Empty
    case Cr.Cir.Out.not_done{}:
      Unit

def PostO.of(o: Cr.Cir.Out, +v: Bk.Term, -O: Type, g: GivesF(o, Pg.Program.unbytes(v), Nil{}, 0, O)) -> PostO(o, v):
  match o:
    case Cr.Cir.Out.next{st}:
      match g:
    case Cr.Cir.Out.halt{+s, +st}:
      OutH.of(Pg.Program.unbytes(v), v, s, st, {==}, g)
    case Cr.Cir.Out.out_of_memory{}:
      Unit{}
    case Cr.Cir.Out.trap{}:
      match g:
    case Cr.Cir.Out.not_done{}:
      Unit{}

# the run ends: anything but out of fuel (Ends of moves.bend)
def EndsO(o: Cr.Cir.Out) -> Data:
  match o:
    case Cr.Cir.Out.next{_}:
      Unit
    case Cr.Cir.Out.halt{_, _}:
      Unit
    case Cr.Cir.Out.out_of_memory{}:
      Unit
    case Cr.Cir.Out.trap{}:
      Unit
    case Cr.Cir.Out.not_done{}:
      Empty

def EndsO.of(o: Cr.Cir.Out, -r: Maybe<&2, List<&2, Word(8n)>>, -out0: List<&2, Word(8n)>, -outn0: U32, -O: Type, g: Gives(o, r, out0, outn0, O)) -> EndsO(o):
  match o:
    case Cr.Cir.Out.next{st}:
      Unit{}
    case Cr.Cir.Out.halt{s, st}:
      Unit{}
    case Cr.Cir.Out.out_of_memory{}:
      Unit{}
    case Cr.Cir.Out.trap{}:
      Unit{}
    case Cr.Cir.Out.not_done{}:
      match g:

# ok, from okn and the image's names
def ok.known(+n: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +ks2: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32,
  +im: U32, +fs: U32, +nx: U32, +hk: {ks == Mc.Img.known(ks2) : List<&2, List<&2, Word(8n)>>},
  +hok: {okn(n, m, ks, img, c, im, fs, nx) == True{} : Bool}) -> {ok(n, m, ks, img, c, im, fs, nx) == True{} : Bool}:
  Tr(List<&2, List<&2, Word(8n)>>, x => {ok(n, m, x, img, c, im, fs, nx) == True{} : Bool}, Mc.Img.known(ks2), ks,
    Equal.sym(List<&2, List<&2, Word(8n)>>, ks, Mc.Img.known(ks2), hk),
    okn.ok(n, m, ks2, img, c, im, fs, nx,
      Tr(List<&2, List<&2, Word(8n)>>, x => {okn(n, m, x, img, c, im, fs, nx) == True{} : Bool}, ks, Mc.Img.known(ks2), hk, hok)))

# out.post of moves.bend, from a state with no output yet: for any fuel
# F, M.out halts as OutH says, runs out of memory, or runs out of fuel
def out.post.of(+n: Nat, +F: Nat, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fs: U32, +im: U32,
  +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +c: U32, +ks: List<&2, List<&2, Word(8n)>>, +ks2: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +v: Bk.Term,
  +hreg: {List.get(&2, U32, regs, Mc.R.focus()) == Some{c} : Maybe<&2, U32>},
  +hlen: {Nat.is_le(Mc.Mach.regs(), List.length(&2, U32, regs)) == True{} : Bool},
  +htm: {T.tm.of(n, m, ks, img, c) == Some{v} : Maybe<&2, Bk.Term>},
  +hk: {ks == Mc.Img.known(ks2) : List<&2, List<&2, Word(8n)>>},
  +hok: {okn(n, m, ks, img, c, im, fs, nx) == True{} : Bool}) ->
  PostO(Cr.Cir.exec(F, Mc.M.out(), Cr.Cir.State{regs, m, nx, fs, im, pg, lim, inp, Nil{}, 0}), v):
  PostO.of(Cr.Cir.exec(F, Mc.M.out(), Cr.Cir.State{regs, m, nx, fs, im, pg, lim, inp, Nil{}, 0}), v, OBn(lim, nx, Nat.add(U32.to_nat(0), n)),
    out.any(n, F, regs, m, nx, fs, im, pg, lim, inp, Nil{}, 0, c, ks, img, v, hreg, hlen, htm, ok.known(n, m, ks, ks2, img, c, im, fs, nx, hk, hok)))

# PostO, with what an out of memory gives (O)
def PostOB(o: Cr.Cir.Out, +v: Bk.Term, O: Type) -> Type:
  match o:
    case Cr.Cir.Out.next{st}:
      Empty
    case Cr.Cir.Out.halt{s, st}:
      OutH(v, s, st)
    case Cr.Cir.Out.out_of_memory{}:
      O
    case Cr.Cir.Out.trap{}:
      Empty
    case Cr.Cir.Out.not_done{}:
      Unit

def PostOB.of(o: Cr.Cir.Out, +v: Bk.Term, -O: Type, g: GivesF(o, Pg.Program.unbytes(v), Nil{}, 0, O)) -> PostOB(o, v, O):
  match o:
    case Cr.Cir.Out.next{st}:
      match g:
    case Cr.Cir.Out.halt{+s, +st}:
      OutH.of(Pg.Program.unbytes(v), v, s, st, {==}, g)
    case Cr.Cir.Out.out_of_memory{}:
      g
    case Cr.Cir.Out.trap{}:
      match g:
    case Cr.Cir.Out.not_done{}:
      Unit{}

# out.post.of with the budget: M.out runs out of memory only when the limit
# has fewer bytes than 20 next + n
def out.postb.of(+n: Nat, +F: Nat, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fs: U32, +im: U32,
  +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +c: U32, +ks: List<&2, List<&2, Word(8n)>>, +ks2: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +v: Bk.Term,
  +hreg: {List.get(&2, U32, regs, Mc.R.focus()) == Some{c} : Maybe<&2, U32>},
  +hlen: {Nat.is_le(Mc.Mach.regs(), List.length(&2, U32, regs)) == True{} : Bool},
  +htm: {T.tm.of(n, m, ks, img, c) == Some{v} : Maybe<&2, Bk.Term>},
  +hk: {ks == Mc.Img.known(ks2) : List<&2, List<&2, Word(8n)>>},
  +hok: {okn(n, m, ks, img, c, im, fs, nx) == True{} : Bool}) ->
  PostOB(Cr.Cir.exec(F, Mc.M.out(), Cr.Cir.State{regs, m, nx, fs, im, pg, lim, inp, Nil{}, 0}), v, OBn(lim, nx, Nat.add(U32.to_nat(0), n))):
  PostOB.of(Cr.Cir.exec(F, Mc.M.out(), Cr.Cir.State{regs, m, nx, fs, im, pg, lim, inp, Nil{}, 0}), v, OBn(lim, nx, Nat.add(U32.to_nat(0), n)),
    out.any(n, F, regs, m, nx, fs, im, pg, lim, inp, Nil{}, 0, c, ks, img, v, hreg, hlen, htm, ok.known(n, m, ks, ks2, img, c, im, fs, nx, hk, hok)))

# out.done of moves.bend: with some fuel, M.out ends
def out.done.of(+n: Nat, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fs: U32, +im: U32,
  +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +out: List<&2, Word(8n)>, +outn: U32, +c: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +ks2: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +v: Bk.Term,
  +hreg: {List.get(&2, U32, regs, Mc.R.focus()) == Some{c} : Maybe<&2, U32>},
  +hlen: {Nat.is_le(Mc.Mach.regs(), List.length(&2, U32, regs)) == True{} : Bool},
  +htm: {T.tm.of(n, m, ks, img, c) == Some{v} : Maybe<&2, Bk.Term>},
  +hk: {ks == Mc.Img.known(ks2) : List<&2, List<&2, Word(8n)>>},
  +hok: {okn(n, m, ks, img, c, im, fs, nx) == True{} : Bool}) ->
  Sigma<&2, &2, Nat, F => EndsO(Cr.Cir.exec(F, Mc.M.out(), Cr.Cir.State{regs, m, nx, fs, im, pg, lim, inp, out, outn}))>:
  +F = {1n+Nat.add(n, 34n) : Nat}
  (F, EndsO.of(Cr.Cir.exec(F, Mc.M.out(), Cr.Cir.State{regs, m, nx, fs, im, pg, lim, inp, out, outn}), Pg.Program.unbytes(v), out, outn, OBn(lim, nx, Nat.add(U32.to_nat(outn), n)),
    out.run(n, Nat.add(n, 34n), PN.le_succ(Nat.add(n, 34n), Nat.add(n, 34n), PN.le_refl(Nat.add(n, 34n))),
      regs, m, nx, fs, im, pg, lim, inp, out, outn, c, ks, img, v, hreg, hlen, htm, ok.known(n, m, ks, ks2, img, c, im, fs, nx, hk, hok))))

# The terms of the cells, with more fuel
# --------------------------------------
#
# What the bridge from moves's Is needs that does not need Is: a cell's
# term with the fuel f is its term with more fuel (tm.mono), and okn from the
# facts of each node (okn.node and the lemmas after it), with more fuel too.

# r is none, or r2 is r
def MO(r: Maybe<&2, Bk.Term>, r2: Maybe<&2, Bk.Term>) -> Type:
  match r:
    case None{}:
      Unit
    case Some{x}:
      {Some{x} == r2 : Maybe<&2, Bk.Term>}

def MO.refl(r: Maybe<&2, Bk.Term>) -> MO(r, r):
  match r:
    case None{}:
      Unit{}
    case Some{x}:
      {==}

def MO.one(-k: Bk.Term -> Bk.Term, r: Maybe<&2, Bk.Term>, -r2: Maybe<&2, Bk.Term>, h: MO(r, r2)) -> MO(T.tm.one(k, r), T.tm.one(k, r2)):
  match r:
    case None{}:
      Unit{}
    case Some{a}:
      %h : {Some{k(a)} == T.tm.one(k, _) : Maybe<&2, Bk.Term>}
      {==}

def MO.two(-k: Bk.Term -> Bk.Term -> Bk.Term, r: Maybe<&2, Bk.Term>, -r2: Maybe<&2, Bk.Term>, s: Maybe<&2, Bk.Term>, -s2: Maybe<&2, Bk.Term>,
  hr: MO(r, r2), hs: MO(s, s2)) -> MO(T.tm.two(k, r, s), T.tm.two(k, r2, s2)):
  match r s:
    case Some{a} Some{b}:
      %hr : {Some{k(a, b)} == T.tm.two(k, _, s2) : Maybe<&2, Bk.Term>}
      %hs : {Some{k(a, b)} == T.tm.two(k, Some{a}, _) : Maybe<&2, Bk.Term>}
      {==}
    case Some{a} None{}:
      Unit{}
    case None{} _:
      Unit{}

def MO.three(-k: Bk.Term -> Bk.Term -> Bk.Term -> Bk.Term, r: Maybe<&2, Bk.Term>, -r2: Maybe<&2, Bk.Term>, s: Maybe<&2, Bk.Term>, -s2: Maybe<&2, Bk.Term>,
  t: Maybe<&2, Bk.Term>, -t2: Maybe<&2, Bk.Term>, hr: MO(r, r2), hs: MO(s, s2), ht: MO(t, t2)) -> MO(T.tm.three(k, r, s, t), T.tm.three(k, r2, s2, t2)):
  match r s t:
    case Some{a} Some{b} Some{d}:
      %hr : {Some{k(a, b, d)} == T.tm.three(k, _, s2, t2) : Maybe<&2, Bk.Term>}
      %hs : {Some{k(a, b, d)} == T.tm.three(k, Some{a}, _, t2) : Maybe<&2, Bk.Term>}
      %ht : {Some{k(a, b, d)} == T.tm.three(k, Some{a}, Some{b}, _) : Maybe<&2, Bk.Term>}
      {==}
    case Some{a} Some{b} None{}:
      Unit{}
    case Some{a} None{} _:
      Unit{}
    case None{} _ _:
      Unit{}

def MO.mat(n: Maybe<&2, List<&2, Word(8n)>>, r: Maybe<&2, Bk.Term>, -r2: Maybe<&2, Bk.Term>, s: Maybe<&2, Bk.Term>, -s2: Maybe<&2, Bk.Term>,
  hr: MO(r, r2), hs: MO(s, s2)) -> MO(T.tm.mat(n, r, s), T.tm.mat(n, r2, s2)):
  match n r s:
    case Some{+x} Some{a} Some{b}:
      %hr : {Some{Bk.Term.Mat{x, a, b}} == T.tm.mat(Some{x}, _, s2) : Maybe<&2, Bk.Term>}
      %hs : {Some{Bk.Term.Mat{x, a, b}} == T.tm.mat(Some{x}, Some{a}, _) : Maybe<&2, Bk.Term>}
      {==}
    case Some{x} Some{a} None{}:
      Unit{}
    case Some{x} None{} _:
      Unit{}
    case None{} _ _:
      Unit{}

def MO.cell(tag: Nat, +q: Bk.Quan, +c: U32, +f2: U32, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  p2: Unit -> Maybe<&2, Bk.Term>, p3: Unit -> Maybe<&2, Bk.Term>, p4: Unit -> Maybe<&2, Bk.Term>,
  -q2: Unit -> Maybe<&2, Bk.Term>, -q3: Unit -> Maybe<&2, Bk.Term>, -q4: Unit -> Maybe<&2, Bk.Term>,
  h2: MO(p2(Unit{}), q2(Unit{})), h3: MO(p3(Unit{}), q3(Unit{})), h4: MO(p4(Unit{}), q4(Unit{}))) ->
  MO(T.tm.cell(tag, q, c, f2, ks, img, p2, p3, p4), T.tm.cell(tag, q, c, f2, ks, img, q2, q3, q4)):
  match tag:
    case 0n:
      MO.refl(Some{Bk.Term.Var{U32.to_nat(f2)}})
    case 1n+t1:
      match t1:
        case 0n:
          MO.refl(T.tm.image(img, c))
        case 1n+t2:
          match t2:
            case 0n:
              MO.two(a => b => Bk.Term.Ann{a, b}, p2(Unit{}), q2(Unit{}), p3(Unit{}), q3(Unit{}), h2, h3)
            case 1n+t3:
              match t3:
                case 0n:
                  MO.two(a => b => Bk.Term.Let{q, a, b}, p2(Unit{}), q2(Unit{}), p3(Unit{}), q3(Unit{}), h2, h3)
                case 1n+t4:
                  match t4:
                    case 0n:
                      MO.one(a => Bk.Term.Typ{a}, p2(Unit{}), q2(Unit{}), h2)
                    case 1n+t5:
                      match t5:
                        case 0n:
                          MO.two(a => b => Bk.Term.Min{a, b}, p2(Unit{}), q2(Unit{}), p3(Unit{}), q3(Unit{}), h2, h3)
                        case 1n+t6:
                          match t6:
                            case 0n:
                              MO.two(a => b => Bk.Term.All{q, a, b}, p2(Unit{}), q2(Unit{}), p3(Unit{}), q3(Unit{}), h2, h3)
                            case 1n+t7:
                              match t7:
                                case 0n:
                                  MO.one(a => Bk.Term.Lam{q, a}, p2(Unit{}), q2(Unit{}), h2)
                                case 1n+t8:
                                  match t8:
                                    case 0n:
                                      MO.two(a => b => Bk.Term.App{q, a, b}, p2(Unit{}), q2(Unit{}), p3(Unit{}), q3(Unit{}), h2, h3)
                                    case 1n+t9:
                                      match t9:
                                        case 0n:
                                          MO.two(a => b => Bk.Term.Sig{q, a, b}, p2(Unit{}), q2(Unit{}), p3(Unit{}), q3(Unit{}), h2, h3)
                                        case 1n+t10:
                                          match t10:
                                            case 0n:
                                              MO.two(a => b => Bk.Term.Tup{q, a, b}, p2(Unit{}), q2(Unit{}), p3(Unit{}), q3(Unit{}), h2, h3)
                                            case 1n+t11:
                                              match t11:
                                                case 0n:
                                                  MO.one(a => Bk.Term.Prj{a}, p2(Unit{}), q2(Unit{}), h2)
                                                case 1n+t12:
                                                  match t12:
                                                    case 0n:
                                                      MO.refl(T.tm.image(img, c))
                                                    case 1n+t13:
                                                      match t13:
                                                        case 0n:
                                                          MO.refl(T.tm.named(T.tm.name(ks, f2), k => Bk.Term.Lab{k}))
                                                        case 1n+t14:
                                                          match t14:
                                                            case 0n:
                                                              MO.mat(T.tm.name(ks, f2), p3(Unit{}), q3(Unit{}), p4(Unit{}), q4(Unit{}), h3, h4)
                                                            case 1n+t15:
                                                              match t15:
                                                                case 0n:
                                                                  MO.refl(Some{Bk.Term.Efq{}})
                                                                case 1n+t16:
                                                                  match t16:
                                                                    case 0n:
                                                                      MO.three(a => b => d => Bk.Term.Eql{a, b, d}, p2(Unit{}), q2(Unit{}), p3(Unit{}), q3(Unit{}), p4(Unit{}), q4(Unit{}), h2, h3, h4)
                                                                    case 1n+t17:
                                                                      match t17:
                                                                        case 0n:
                                                                          MO.refl(Some{Bk.Term.Rfl{}})
                                                                        case 1n+t18:
                                                                          match t18:
                                                                            case 0n:
                                                                              MO.three(a => b => d => Bk.Term.Rwt{a, b, d}, p2(Unit{}), q2(Unit{}), p3(Unit{}), q3(Unit{}), p4(Unit{}), q4(Unit{}), h2, h3, h4)
                                                                            case 1n+t19:
                                                                              Unit{}

# a cell's term with the fuel f is its term with the fuel f + g
def tm.mono(+f: Nat, +g: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32) ->
  MO(T.tm.of(f, m, ks, img, c), T.tm.of(Nat.add(f, g), m, ks, img, c)):
  match f:
    case 0n:
      Unit{}
    case 1n+p:
      MO.cell(U32.to_nat(U32.and(Fd(0n, m, c), 63)), T.tm.quan(U32.and(U32.shrn(Fd(0n, m, c), 6n), 3)), c, Fd(2n, m, c), ks, img,
        u => T.tm.of(p, m, ks, img, Fd(2n, m, c)), u => T.tm.of(p, m, ks, img, Fd(3n, m, c)), u => T.tm.of(p, m, ks, img, Fd(4n, m, c)),
        u => T.tm.of(Nat.add(p, g), m, ks, img, Fd(2n, m, c)), u => T.tm.of(Nat.add(p, g), m, ks, img, Fd(3n, m, c)),
        u => T.tm.of(Nat.add(p, g), m, ks, img, Fd(4n, m, c)),
        tm.mono(p, g, m, ks, img, Fd(2n, m, c)), tm.mono(p, g, m, ks, img, Fd(3n, m, c)), tm.mono(p, g, m, ks, img, Fd(4n, m, c)))

# Unit for none, Empty for some
def MT.none(x: Maybe<&2, Bk.Term>) -> Type:
  match x:
    case None{}:
      Unit
    case Some{_}:
      Empty

# with more fuel, a term that is there is the same
def MO.use(r: Maybe<&2, Bk.Term>, -r2: Maybe<&2, Bk.Term>, -v: Bk.Term, +e: {r == Some{v} : Maybe<&2, Bk.Term>}, h: MO(r, r2)) ->
  {r2 == Some{v} : Maybe<&2, Bk.Term>}:
  match r:
    case None{}:
      Empty.absurd({r2 == Some{v} : Maybe<&2, Bk.Term>}, Tr(Maybe<&2, Bk.Term>, x => MT.none(x), None{}, Some{v}, e, Unit{}))
    case Some{x}:
      Equal.trans(Maybe<&2, Bk.Term>, r2, Some{x}, Some{v}, Equal.sym(Maybe<&2, Bk.Term>, Some{x}, r2, h), e)

# T.tm.of(f) == Some{v} gives T.tm.of(f + g) == Some{v}
def tm.more(+f: Nat, +g: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, -v: Bk.Term,
  +e: {T.tm.of(f, m, ks, img, c) == Some{v} : Maybe<&2, Bk.Term>}) -> {T.tm.of(Nat.add(f, g), m, ks, img, c) == Some{v} : Maybe<&2, Bk.Term>}:
  MO.use(T.tm.of(f, m, ks, img, c), T.tm.of(Nat.add(f, g), m, ks, img, c), v, e, tm.mono(f, g, m, ks, img, c))

# okn with more fuel
def okn.mono(+f: Nat, +g: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32,
  +h: {okn(f, m, ks, img, c, im, fs, nx) == True{} : Bool}) -> {okn(Nat.add(f, g), m, ks, img, c, im, fs, nx) == True{} : Bool}:
  match f:
    case 0n:
      Empty.absurd({okn(g, m, ks, img, c, im, fs, nx) == True{} : Bool}, PN.false_ne_true(h))
    case 1n+p:
      +t = Tg(m, c)
      +A = Bool.and(Bool.and(Cr.Cir.is_cell(c, im, fs, nx), ok.img(t, T.tm.image(img, c))), okn.lab(t, ks, Fd(2n, m, c)))
      +K2 = Bool.or(Bool.not(U32.is_eq(t, 10)), Bool.and(okn(p, m, ks, img, Fd(2n, m, c), im, fs, nx), okn(p, m, ks, img, Fd(3n, m, c), im, fs, nx)))
      and_i(A, Bool.or(Bool.not(U32.is_eq(t, 10)), Bool.and(okn(Nat.add(p, g), m, ks, img, Fd(2n, m, c), im, fs, nx), okn(Nat.add(p, g), m, ks, img, Fd(3n, m, c), im, fs, nx))),
        and_l(A, K2, h),
        or_imp(U32.is_eq(t, 10), Bool.and(okn(p, m, ks, img, Fd(2n, m, c), im, fs, nx), okn(p, m, ks, img, Fd(3n, m, c), im, fs, nx)),
          Bool.and(okn(Nat.add(p, g), m, ks, img, Fd(2n, m, c), im, fs, nx), okn(Nat.add(p, g), m, ks, img, Fd(3n, m, c), im, fs, nx)), and_r(A, K2, h),
          +e => and_i(okn(Nat.add(p, g), m, ks, img, Fd(2n, m, c), im, fs, nx), okn(Nat.add(p, g), m, ks, img, Fd(3n, m, c), im, fs, nx),
            okn.mono(p, g, m, ks, img, Fd(2n, m, c), im, fs, nx, and_l(okn(p, m, ks, img, Fd(2n, m, c), im, fs, nx), okn(p, m, ks, img, Fd(3n, m, c), im, fs, nx), e)),
            okn.mono(p, g, m, ks, img, Fd(3n, m, c), im, fs, nx, and_r(okn(p, m, ks, img, Fd(2n, m, c), im, fs, nx), okn(p, m, ks, img, Fd(3n, m, c), im, fs, nx), e)))))

# okn at the cell c, from the facts of its node: it is a cell, its image's
# term (for a Ref or an Enu), its label's number, and its parts (for a pair)
def okn.node(+f: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32,
  +hc: {Cr.Cir.is_cell(c, im, fs, nx) == True{} : Bool},
  +hi: {ok.img(Tg(m, c), T.tm.image(img, c)) == True{} : Bool},
  +hl: {okn.lab(Tg(m, c), ks, Fd(2n, m, c)) == True{} : Bool},
  +hp: {Bool.or(Bool.not(U32.is_eq(Tg(m, c), 10)), Bool.and(okn(f, m, ks, img, Fd(2n, m, c), im, fs, nx), okn(f, m, ks, img, Fd(3n, m, c), im, fs, nx))) == True{} : Bool}) ->
  {okn(1n+f, m, ks, img, c, im, fs, nx) == True{} : Bool}:
  +t = Tg(m, c)
  and_i(Bool.and(Bool.and(Cr.Cir.is_cell(c, im, fs, nx), ok.img(t, T.tm.image(img, c))), okn.lab(t, ks, Fd(2n, m, c))),
    Bool.or(Bool.not(U32.is_eq(t, 10)), Bool.and(okn(f, m, ks, img, Fd(2n, m, c), im, fs, nx), okn(f, m, ks, img, Fd(3n, m, c), im, fs, nx))),
    and_i(Bool.and(Cr.Cir.is_cell(c, im, fs, nx), ok.img(t, T.tm.image(img, c))), okn.lab(t, ks, Fd(2n, m, c)),
      and_i(Cr.Cir.is_cell(c, im, fs, nx), ok.img(t, T.tm.image(img, c)), hc, hi), hl), hp)

# the image's term, for a node of the tag tg: none asked unless tg is 1
# (Ref) or 12 (Enu), whose image's term is the node's
def oimg.eq(+t: U32, +tg: U32, +r: Maybe<&2, Bk.Term>, +e: {t == tg : U32}, +h: {ok.img(tg, r) == True{} : Bool}) -> {ok.img(t, r) == True{} : Bool}:
  Tr(U32, x => {ok.img(x, r) == True{} : Bool}, tg, t, Equal.sym(U32, t, tg, e), h)

def oimg.ref(+r: Maybe<&2, Bk.Term>, +k: List<&2, Word(8n)>, +e: {r == Some{Bk.Term.Ref{k}} : Maybe<&2, Bk.Term>}) -> {ok.img(1, r) == True{} : Bool}:
  Tr(Maybe<&2, Bk.Term>, x => {ok.img(1, x) == True{} : Bool}, Some{Bk.Term.Ref{k}}, r, Equal.sym(Maybe<&2, Bk.Term>, r, Some{Bk.Term.Ref{k}}, e), {==})

def oimg.enu(+r: Maybe<&2, Bk.Term>, +ns: List<&2, List<&2, Word(8n)>>, +e: {r == Some{Bk.Term.Enu{ns}} : Maybe<&2, Bk.Term>}) -> {ok.img(12, r) == True{} : Bool}:
  Tr(Maybe<&2, Bk.Term>, x => {ok.img(12, x) == True{} : Bool}, Some{Bk.Term.Enu{ns}}, r, Equal.sym(Maybe<&2, Bk.Term>, r, Some{Bk.Term.Enu{ns}}, e), {==})

# the label's number, for a node of the tag tg: none asked unless tg is 13,
# whose number j is that of its name k (Nm of moves.bend)
def olab.eq(+t: U32, +tg: U32, +ks: List<&2, List<&2, Word(8n)>>, +j: U32, +e: {t == tg : U32}, +h: {okn.lab(tg, ks, j) == True{} : Bool}) ->
  {okn.lab(t, ks, j) == True{} : Bool}:
  Tr(U32, x => {okn.lab(x, ks, j) == True{} : Bool}, tg, t, Equal.sym(U32, t, tg, e), h)

def olab.lab(+ks: List<&2, List<&2, Word(8n)>>, +j: U32, +k: List<&2, Word(8n)>, +en: {T.tm.name(ks, j) == Some{k} : Maybe<&2, List<&2, Word(8n)>>},
  +ej: {j == Mc.Img.id(ks, k, 0) : U32}) -> {okn.lab(13, ks, j) == True{} : Bool}:
  %Equal.sym(Maybe<&2, List<&2, Word(8n)>>, T.tm.name(ks, j), Some{k}, en) : {labid.of(_, j, ks) == True{} : Bool}
  Tr(U32, x => {U32.is_eq(j, x) == True{} : Bool}, j, Mc.Img.id(ks, k, 0), ej, nat_eq(j, j, {==}))

# the parts, for a node of the tag tg: none asked unless tg is 10 (Tup)
def okids.eq(+t: U32, +tg: U32, -X: Bool, +e: {t == tg : U32}, +h: {Bool.or(Bool.not(U32.is_eq(tg, 10)), X) == True{} : Bool}) ->
  {Bool.or(Bool.not(U32.is_eq(t, 10)), X) == True{} : Bool}:
  Tr(U32, x => {Bool.or(Bool.not(U32.is_eq(x, 10)), X) == True{} : Bool}, tg, t, Equal.sym(U32, t, tg, e), h)

def okids.tup(+t: U32, +f: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32,
  +h2: {okn(f, m, ks, img, Fd(2n, m, c), im, fs, nx) == True{} : Bool}, +h3: {okn(f, m, ks, img, Fd(3n, m, c), im, fs, nx) == True{} : Bool}) ->
  {Bool.or(Bool.not(U32.is_eq(t, 10)), Bool.and(okn(f, m, ks, img, Fd(2n, m, c), im, fs, nx), okn(f, m, ks, img, Fd(3n, m, c), im, fs, nx))) == True{} : Bool}:
  or_r_true(Bool.not(U32.is_eq(t, 10)), Bool.and(okn(f, m, ks, img, Fd(2n, m, c), im, fs, nx), okn(f, m, ks, img, Fd(3n, m, c), im, fs, nx)),
    and_i(okn(f, m, ks, img, Fd(2n, m, c), im, fs, nx), okn(f, m, ks, img, Fd(3n, m, c), im, fs, nx), h2, h3))

# the term of a node of the tag tg: T.tm.cell of the tag, with its parts'
# terms one level less deep
def tm.at(+f: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +tg: U32, +e: {Tg(m, c) == tg : U32}) ->
  {T.tm.of(1n+f, m, ks, img, c) == T.tm.cell(U32.to_nat(tg), T.tm.quan(U32.and(U32.shrn(Fd(0n, m, c), 6n), 3)), c, Fd(2n, m, c), ks, img,
    u => T.tm.of(f, m, ks, img, Fd(2n, m, c)), u => T.tm.of(f, m, ks, img, Fd(3n, m, c)), u => T.tm.of(f, m, ks, img, Fd(4n, m, c))) : Maybe<&2, Bk.Term>}:
  Tr(U32, x => {T.tm.of(1n+f, m, ks, img, c) == T.tm.cell(U32.to_nat(x), T.tm.quan(U32.and(U32.shrn(Fd(0n, m, c), 6n), 3)), c, Fd(2n, m, c), ks, img,
      u => T.tm.of(f, m, ks, img, Fd(2n, m, c)), u => T.tm.of(f, m, ks, img, Fd(3n, m, c)), u => T.tm.of(f, m, ks, img, Fd(4n, m, c))) : Maybe<&2, Bk.Term>},
    Tg(m, c), tg, e, {==})
