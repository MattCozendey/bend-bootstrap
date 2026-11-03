# compiler: the first cell of the machine is past the table (layer B)
# ==================================================================
#
# hf.first.k: from Start's equation first = Cir.first(k, 20 (k + 1) + len),
# with k < 2^26, the first cell is past the image's k cells; hf.first: with
# 290 <= k, it is at least 272 (In.input.post's premise hF). Cir.first picks
# k + 1 when 20 (k + 1) >= end; else it is (end - 1) / 20 + 1 with
# end > 20 (k + 1), so the quotient is past k. hf.hF and hf.kF take k and
# first from what Cir.result computed.
#
# The long division (dm and what it needs) is copied from
# Compiler/Cir/simulation_first_cell_division.bend and its imports
# (Compiler/Cir/simulation_* are edited elsewhere): it gives q 20 + r = x
# with r < 20 for U32.div(x, 20) = q. The arithmetic of words (hw.*) is
# copied from Compiler/Cir/halt.bend, which imports the whole compiler.
# Big closed numbers (2^26, 2^32, 214748364) meet only in equations, as
# variables of a lemma (hw.hP, hf.lt.pat): bend2 computes the type of a def
# that has no parameter, and the lowering computes a comparison of two
# closed numbers in a type, 2^26 and 2^32 included.

import Base
import ../../Book/impl.bend as Bk
import ../Cir/impl.bend as Cr
import ./impl.bend as Mc
import ../need_big.bend as N
import ../Cir/module_round_trip.bend as MO
import ../Cir/instrs_round_trip.bend as PI
import ../img_small.bend as PG

# Arithmetic of words (copied)
# -----------------------------
#
# From Compiler/Cir/halt.bend, which imports the whole compiler: every lemma
# is over words of any n bits, so that its proof computes only with
# variables; 2^32 never unfolds.

def hw.bn(b: Bool) -> Nat:
  match b:
    case False{}:
      0n
    case True{}:
      1n

# 2^n
def hw.W(n: Nat) -> Nat:
  N.D(n, hw.bn(True{}))

# the carry of a full adder
def hw.carry(a: Bool, +b: Bool, +c: Bool) -> Bool:
  match a:
    case False{}:
      Bool.and(b, c)
    case True{}:
      Bool.or(b, c)

# the carry out of Word.adc(n, a, b, False, c)
def hw.cout(n: Nat, a: Word(n), b: Word(n), c: Bool) -> Bool:
  match n:
    case 0n:
      c
    case 1n+p:
      match a b:
        case WCon{ab, at} WCon{bb, bt}:
          hw.cout(p, at, bt, hw.carry(ab, bb, c))

# 2x + 2y = 2(x + y)
def hw.dd(+x: Nat, +y: Nat) -> {Nat.add(Nat.double(x), Nat.double(y)) == Nat.double(Nat.add(x, y)) : Nat}:
  Equal.sym(Nat, Nat.double(Nat.add(x, y)), Nat.add(Nat.double(x), Nat.double(y)), N.double_add(x, y))

# x + (b + y) = b + (x + y), for a bit b
def hw.add_bit(+x: Nat, b: Bool, +y: Nat) -> {Nat.add(x, Nat.add(hw.bn(b), y)) == Nat.add(hw.bn(b), Nat.add(x, y)) : Nat}:
  match b:
    case False{}:
      {==}
    case True{}:
      N.add_succ_r(x, y)

def hw.adc.l(+s: Bool, +S: Nat, +Dp: Nat, +k: Bool, +A: Nat, +B: Nat,
  ih: {Nat.add(S, Dp) == Nat.add(hw.bn(k), Nat.add(A, B)) : Nat}) ->
  {Nat.add(hw.bn(s), Nat.add(Nat.double(S), Nat.double(Dp))) == Nat.add(hw.bn(s), Nat.double(Nat.add(hw.bn(k), Nat.add(A, B)))) : Nat}:
  %ih : {Nat.add(hw.bn(s), Nat.add(Nat.double(S), Nat.double(Dp))) == Nat.add(hw.bn(s), Nat.double(_)) : Nat}
  Equal.cong(Nat, Nat, z => Nat.add(hw.bn(s), z), Nat.add(Nat.double(S), Nat.double(Dp)), Nat.double(Nat.add(S, Dp)), hw.dd(S, Dp))

def hw.adc.r(+c: Bool, +ab: Bool, +bb: Bool, +A: Nat, +B: Nat) ->
  {Nat.add(hw.bn(c), Nat.add(hw.bn(ab), Nat.add(Nat.double(A), Nat.add(hw.bn(bb), Nat.double(B))))) ==
    Nat.add(hw.bn(c), Nat.add(hw.bn(ab), Nat.add(hw.bn(bb), Nat.double(Nat.add(A, B))))) : Nat}:
  %hw.dd(A, B) : {Nat.add(hw.bn(c), Nat.add(hw.bn(ab), Nat.add(Nat.double(A), Nat.add(hw.bn(bb), Nat.double(B))))) ==
    Nat.add(hw.bn(c), Nat.add(hw.bn(ab), Nat.add(hw.bn(bb), _))) : Nat}
  Equal.cong(Nat, Nat, z => Nat.add(hw.bn(c), Nat.add(hw.bn(ab), z)),
    Nat.add(Nat.double(A), Nat.add(hw.bn(bb), Nat.double(B))), Nat.add(hw.bn(bb), Nat.add(Nat.double(A), Nat.double(B))),
    hw.add_bit(Nat.double(A), bb, Nat.double(B)))

# one bit of an addition: s + 2k = a + b + c
def hw.adc.fin(+s: Bool, +k: Bool, +c: Bool, +ab: Bool, +bb: Bool, +S: Nat, +Dp: Nat, +A: Nat, +B: Nat,
  ih: {Nat.add(S, Dp) == Nat.add(hw.bn(k), Nat.add(A, B)) : Nat},
  mid: {Nat.add(hw.bn(s), Nat.double(Nat.add(hw.bn(k), Nat.add(A, B)))) ==
    Nat.add(hw.bn(c), Nat.add(hw.bn(ab), Nat.add(hw.bn(bb), Nat.double(Nat.add(A, B))))) : Nat}) ->
  {Nat.add(hw.bn(s), Nat.add(Nat.double(S), Nat.double(Dp))) ==
    Nat.add(hw.bn(c), Nat.add(hw.bn(ab), Nat.add(Nat.double(A), Nat.add(hw.bn(bb), Nat.double(B))))) : Nat}:
  Equal.trans(Nat, Nat.add(hw.bn(s), Nat.add(Nat.double(S), Nat.double(Dp))),
    Nat.add(hw.bn(s), Nat.double(Nat.add(hw.bn(k), Nat.add(A, B)))),
    Nat.add(hw.bn(c), Nat.add(hw.bn(ab), Nat.add(Nat.double(A), Nat.add(hw.bn(bb), Nat.double(B))))),
    hw.adc.l(s, S, Dp, k, A, B, ih),
    Equal.trans(Nat, Nat.add(hw.bn(s), Nat.double(Nat.add(hw.bn(k), Nat.add(A, B)))),
      Nat.add(hw.bn(c), Nat.add(hw.bn(ab), Nat.add(hw.bn(bb), Nat.double(Nat.add(A, B))))),
      Nat.add(hw.bn(c), Nat.add(hw.bn(ab), Nat.add(Nat.double(A), Nat.add(hw.bn(bb), Nat.double(B))))),
      mid, Equal.sym(Nat, Nat.add(hw.bn(c), Nat.add(hw.bn(ab), Nat.add(Nat.double(A), Nat.add(hw.bn(bb), Nat.double(B))))),
        Nat.add(hw.bn(c), Nat.add(hw.bn(ab), Nat.add(hw.bn(bb), Nat.double(Nat.add(A, B))))), hw.adc.r(c, ab, bb, A, B))))

# the value of an addition, with its carry out
def hw.adc(+n: Nat, +a: Word(n), +b: Word(n), +c: Bool) ->
  {Nat.add(Word.to_nat(n, Word.adc(n, a, b, False{}, c)), N.D(n, hw.bn(hw.cout(n, a, b, c)))) ==
    Nat.add(hw.bn(c), Nat.add(Word.to_nat(n, a), Word.to_nat(n, b))) : Nat}:
  match n:
    case 0n:
      match c:
        case False{}:
          {==}
        case True{}:
          {==}
    case 1n+p:
      match a b c:
        case WCon{False{}, +at} WCon{False{}, +bt} False{}:
          hw.adc.fin(False{}, False{}, False{}, False{}, False{}, Word.to_nat(p, Word.adc(p, at, bt, False{}, False{})),
            N.D(p, hw.bn(hw.cout(p, at, bt, False{}))), Word.to_nat(p, at), Word.to_nat(p, bt), hw.adc(p, at, bt, False{}), {==})
        case WCon{False{}, +at} WCon{False{}, +bt} True{}:
          hw.adc.fin(True{}, False{}, True{}, False{}, False{}, Word.to_nat(p, Word.adc(p, at, bt, False{}, False{})),
            N.D(p, hw.bn(hw.cout(p, at, bt, False{}))), Word.to_nat(p, at), Word.to_nat(p, bt), hw.adc(p, at, bt, False{}), {==})
        case WCon{False{}, +at} WCon{True{}, +bt} False{}:
          hw.adc.fin(True{}, False{}, False{}, False{}, True{}, Word.to_nat(p, Word.adc(p, at, bt, False{}, False{})),
            N.D(p, hw.bn(hw.cout(p, at, bt, False{}))), Word.to_nat(p, at), Word.to_nat(p, bt), hw.adc(p, at, bt, False{}), {==})
        case WCon{False{}, +at} WCon{True{}, +bt} True{}:
          hw.adc.fin(False{}, True{}, True{}, False{}, True{}, Word.to_nat(p, Word.adc(p, at, bt, False{}, True{})),
            N.D(p, hw.bn(hw.cout(p, at, bt, True{}))), Word.to_nat(p, at), Word.to_nat(p, bt), hw.adc(p, at, bt, True{}), {==})
        case WCon{True{}, +at} WCon{False{}, +bt} False{}:
          hw.adc.fin(True{}, False{}, False{}, True{}, False{}, Word.to_nat(p, Word.adc(p, at, bt, False{}, False{})),
            N.D(p, hw.bn(hw.cout(p, at, bt, False{}))), Word.to_nat(p, at), Word.to_nat(p, bt), hw.adc(p, at, bt, False{}), {==})
        case WCon{True{}, +at} WCon{False{}, +bt} True{}:
          hw.adc.fin(False{}, True{}, True{}, True{}, False{}, Word.to_nat(p, Word.adc(p, at, bt, False{}, True{})),
            N.D(p, hw.bn(hw.cout(p, at, bt, True{}))), Word.to_nat(p, at), Word.to_nat(p, bt), hw.adc(p, at, bt, True{}), {==})
        case WCon{True{}, +at} WCon{True{}, +bt} False{}:
          hw.adc.fin(False{}, True{}, False{}, True{}, True{}, Word.to_nat(p, Word.adc(p, at, bt, False{}, True{})),
            N.D(p, hw.bn(hw.cout(p, at, bt, True{}))), Word.to_nat(p, at), Word.to_nat(p, bt), hw.adc(p, at, bt, True{}), {==})
        case WCon{True{}, +at} WCon{True{}, +bt} True{}:
          hw.adc.fin(True{}, True{}, True{}, True{}, True{}, Word.to_nat(p, Word.adc(p, at, bt, False{}, True{})),
            N.D(p, hw.bn(hw.cout(p, at, bt, True{}))), Word.to_nat(p, at), Word.to_nat(p, bt), hw.adc(p, at, bt, True{}), {==})

# 2^n × 0 = 0
def hw.D0(n: Nat) -> {N.D(n, 0n) == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %hw.D0(p) : {Nat.double(N.D(p, 0n)) == Nat.double(_) : Nat}
      {==}

def hw.noc.z(+n: Nat, +V: Nat) -> {V == Nat.add(V, N.D(n, 0n)) : Nat}:
  %Equal.sym(Nat, N.D(n, 0n), 0n, hw.D0(n)) : {V == Nat.add(V, _) : Nat}
  Equal.sym(Nat, Nat.add(V, 0n), V, N.add_zero(V))

# a sum below 2^n has no carry out
def hw.noc(o: Bool, +n: Nat, +V: Nat, +X: Nat, e: {Nat.add(V, N.D(n, hw.bn(o))) == X : Nat}, h: N.Le(1n+X, hw.W(n))) ->
  {V == X : Nat}:
  match o:
    case False{}:
      Equal.trans(Nat, V, Nat.add(V, N.D(n, 0n)), X, hw.noc.z(n, V), e)
    case True{}:
      +W = hw.W(n)
      Empty.absurd({V == X : Nat}, N.not_succ_le(W,
        N.le_trans(1n+W, 1n+Nat.add(V, W), W, N.le_add_l(V, W),
          N.le_rw_l(1n+X, 1n+Nat.add(V, W), W, Equal.sym(Nat, 1n+Nat.add(V, W), 1n+X,
            Equal.cong(Nat, Nat, z => 1n+z, Nat.add(V, W), X, e)), h))))

# an addition below 2^n is exact
def hw.add_ex(+n: Nat, +a: Word(n), +b: Word(n), h: N.Le(1n+Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)), hw.W(n))) ->
  {Word.to_nat(n, Word.add(n, a, b)) == Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)) : Nat}:
  hw.noc(hw.cout(n, a, b, False{}), n, Word.to_nat(n, Word.add(n, a, b)), Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)),
    hw.adc(n, a, b, False{}), h)

# the bit that a shift left pushes out of the top
def hw.pout(n: Nat, c: Bool, w: Word(n)) -> Bool:
  match n:
    case 0n:
      c
    case 1n+p:
      match w:
        case WCon{b, t}:
          hw.pout(p, b, t)

def hw.sout(n: Nat, w: Word(n)) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+p:
      match w:
        case WCon{b, t}:
          hw.pout(p, b, t)

def hw.put.fin(+c: Bool, +b: Bool, +Pv: Nat, +Dp: Nat, +T: Nat,
  ih: {Nat.add(Pv, Dp) == Nat.add(hw.bn(b), Nat.double(T)) : Nat}) ->
  {Nat.add(hw.bn(c), Nat.add(Nat.double(Pv), Nat.double(Dp))) == Nat.add(hw.bn(c), Nat.double(Nat.add(hw.bn(b), Nat.double(T)))) : Nat}:
  %ih : {Nat.add(hw.bn(c), Nat.add(Nat.double(Pv), Nat.double(Dp))) == Nat.add(hw.bn(c), Nat.double(_)) : Nat}
  Equal.cong(Nat, Nat, z => Nat.add(hw.bn(c), z), Nat.add(Nat.double(Pv), Nat.double(Dp)), Nat.double(Nat.add(Pv, Dp)), hw.dd(Pv, Dp))

# the value of a shift with c in at the bottom, with the bit out at the top
def hw.put(+n: Nat, +c: Bool, +w: Word(n)) ->
  {Nat.add(Word.to_nat(n, Word.shl.put(n, c, w)), N.D(n, hw.bn(hw.pout(n, c, w)))) == Nat.add(hw.bn(c), Nat.double(Word.to_nat(n, w))) : Nat}:
  match n:
    case 0n:
      match c:
        case False{}:
          {==}
        case True{}:
          {==}
    case 1n+p:
      match c w:
        case False{} WCon{False{}, +t}:
          hw.put.fin(False{}, False{}, Word.to_nat(p, Word.shl.put(p, False{}, t)), N.D(p, hw.bn(hw.pout(p, False{}, t))), Word.to_nat(p, t), hw.put(p, False{}, t))
        case False{} WCon{True{}, +t}:
          hw.put.fin(False{}, True{}, Word.to_nat(p, Word.shl.put(p, True{}, t)), N.D(p, hw.bn(hw.pout(p, True{}, t))), Word.to_nat(p, t), hw.put(p, True{}, t))
        case True{} WCon{False{}, +t}:
          hw.put.fin(True{}, False{}, Word.to_nat(p, Word.shl.put(p, False{}, t)), N.D(p, hw.bn(hw.pout(p, False{}, t))), Word.to_nat(p, t), hw.put(p, False{}, t))
        case True{} WCon{True{}, +t}:
          hw.put.fin(True{}, True{}, Word.to_nat(p, Word.shl.put(p, True{}, t)), N.D(p, hw.bn(hw.pout(p, True{}, t))), Word.to_nat(p, t), hw.put(p, True{}, t))

# the value of a shift left, with the bit out at the top
def hw.shl(+n: Nat, +w: Word(n)) ->
  {Nat.add(Word.to_nat(n, Word.shl(n, w)), N.D(n, hw.bn(hw.sout(n, w)))) == Nat.double(Word.to_nat(n, w)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{False{}, +t}:
          hw.put.fin(False{}, False{}, Word.to_nat(p, Word.shl.put(p, False{}, t)), N.D(p, hw.bn(hw.pout(p, False{}, t))), Word.to_nat(p, t), hw.put(p, False{}, t))
        case WCon{True{}, +t}:
          hw.put.fin(False{}, True{}, Word.to_nat(p, Word.shl.put(p, True{}, t)), N.D(p, hw.bn(hw.pout(p, True{}, t))), Word.to_nat(p, t), hw.put(p, True{}, t))

# a shift left below 2^n is exact
def hw.shl_ex(+n: Nat, +w: Word(n), h: N.Le(1n+Nat.double(Word.to_nat(n, w)), hw.W(n))) ->
  {Word.to_nat(n, Word.shl(n, w)) == Nat.double(Word.to_nat(n, w)) : Nat}:
  hw.noc(hw.sout(n, w), n, Word.to_nat(n, Word.shl(n, w)), Nat.double(Word.to_nat(n, w)), hw.shl(n, w), h)

# 20 × x
def hw.t20(x: Nat) -> Nat:
  match x:
    case 0n:
      0n
    case 1n+p:
      20n+hw.t20(p)

def hw.t20_mono(+x: Nat, +y: Nat, h: N.Le(x, y)) -> N.Le(hw.t20(x), hw.t20(y)):
  match x:
    case 0n:
      N.le_zero(hw.t20(y))
    case 1n+p:
      match y:
        case 0n:
          Empty.absurd(N.Le(hw.t20(1n+p), 0n), h)
        case 1n+q:
          hw.t20_mono(p, q, h)

# 20x < 20y gives x < y
def hw.t20_lt(+x: Nat, +y: Nat, h: N.Le(1n+hw.t20(x), hw.t20(y))) -> N.Le(1n+x, y):
  match x y:
    case _ 0n:
      Empty.absurd(N.Le(1n+x, 0n), h)
    case 0n 1n+q:
      N.le_zero(q)
    case 1n+p 1n+q:
      hw.t20_lt(p, q, h)

def hw.le_t20(+x: Nat) -> N.Le(x, hw.t20(x)):
  match x:
    case 0n:
      Unit{}
    case 1n+p:
      N.le_trans(p, hw.t20(p), 19n+hw.t20(p), hw.le_t20(p), N.le_add_l(19n, hw.t20(p)))

# 20 × 2x = 2 × 20x
def hw.t20_double(+x: Nat) -> {hw.t20(Nat.double(x)) == Nat.double(hw.t20(x)) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      %hw.t20_double(p) : {40n+hw.t20(Nat.double(p)) == 40n+_ : Nat}
      {==}

# a + (k + b) = k + (a + b)
def hw.add_k(+a: Nat, +k: Nat, +b: Nat) -> {Nat.add(a, Nat.add(k, b)) == Nat.add(k, Nat.add(a, b)) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+q:
      %hw.add_k(a, q, b) : {Nat.add(a, 1n+Nat.add(q, b)) == 1n+_ : Nat}
      N.add_succ_r(a, Nat.add(q, b))

# 16x + 4x = 20x
def hw.t20_shifts(+x: Nat) -> {Nat.add(N.D(4n, x), N.D(2n, x)) == hw.t20(x) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(N.D(4n, p), Nat.add(4n, N.D(2n, p))), Nat.add(4n, Nat.add(N.D(4n, p), N.D(2n, p))),
        hw.add_k(N.D(4n, p), 4n, N.D(2n, p))) : {16n+_ == 20n+hw.t20(p) : Nat}
      %Equal.sym(Nat, Nat.add(N.D(4n, p), N.D(2n, p)), hw.t20(p), hw.t20_shifts(p)) : {20n+_ == 20n+hw.t20(p) : Nat}
      {==}

def hw.le_double(+x: Nat) -> N.Le(x, Nat.double(x)):
  match x:
    case 0n:
      Unit{}
    case 1n+p:
      N.le_succ(p, Nat.double(p), hw.le_double(p))

# j shifts left
def hw.shlj(j: Nat, +n: Nat, w: Word(n)) -> Word(n):
  match j:
    case 0n:
      w
    case 1n+q:
      Word.shl(n, hw.shlj(q, n, w))

# j shifts left below 2^n are exact
def hw.shlj_ex(+j: Nat, +n: Nat, +w: Word(n), +h: N.Le(1n+N.D(j, Word.to_nat(n, w)), hw.W(n))) ->
  {Word.to_nat(n, hw.shlj(j, n, w)) == N.D(j, Word.to_nat(n, w)) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+q:
      +X = Word.to_nat(n, w)
      +Y = N.D(q, X)
      +sq = hw.shlj(q, n, w)
      +ih = hw.shlj_ex(q, n, w, N.le_trans(1n+Y, 1n+Nat.double(Y), hw.W(n), hw.le_double(Y), h))
      Equal.trans(Nat, Word.to_nat(n, Word.shl(n, sq)), Nat.double(Word.to_nat(n, sq)), Nat.double(Y),
        hw.shl_ex(n, sq, N.le_rw_l(1n+Nat.double(Y), 1n+Nat.double(Word.to_nat(n, sq)), hw.W(n),
          Equal.cong(Nat, Nat, z => 1n+Nat.double(z), Y, Word.to_nat(n, sq), Equal.sym(Nat, Word.to_nat(n, sq), Y, ih)), h)),
        Equal.cong(Nat, Nat, z => Nat.double(z), Word.to_nat(n, sq), Y, ih))

# 20x below 2^n, for x <= P where 2^4 + 20P = 2^n
def hw.t20_bound(+n: Nat, +X: Nat, +P: Nat, +hP: {Nat.add(hw.W(4n), hw.t20(P)) == hw.W(n) : Nat}, +hx: N.Le(X, P)) ->
  N.Le(1n+hw.t20(X), hw.W(n)):
  N.le_trans(1n+hw.t20(X), 1n+hw.t20(P), hw.W(n), hw.t20_mono(X, P, hx),
    N.le_rw_r(1n+hw.t20(P), Nat.add(hw.W(4n), hw.t20(P)), hw.W(n), hP, N.le_add_l(15n, hw.t20(P))))

# 16x + 4x, the module's 20 × x, is exact for x <= P
def hw.tex_w(+n: Nat, +w: Word(n), +P: Nat, +hP: {Nat.add(hw.W(4n), hw.t20(P)) == hw.W(n) : Nat},
  +hx: N.Le(Word.to_nat(n, w), P)) ->
  {Word.to_nat(n, Word.add(n, hw.shlj(4n, n, w), hw.shlj(2n, n, w))) == hw.t20(Word.to_nat(n, w)) : Nat}:
  +X = Word.to_nat(n, w)
  +b0 = hw.t20_bound(n, X, P, hP, hx)
  +D4 = N.D(4n, X)
  +D2 = N.D(2n, X)
  +ts = hw.t20_shifts(X)
  +s4 = hw.shlj(4n, n, w)
  +s2 = hw.shlj(2n, n, w)
  +bsum = N.le_rw_l(1n+hw.t20(X), 1n+Nat.add(D4, D2), hw.W(n), Equal.cong(Nat, Nat, z => 1n+z, hw.t20(X), Nat.add(D4, D2), Equal.sym(Nat, Nat.add(D4, D2), hw.t20(X), ts)), b0)
  +e4 = hw.shlj_ex(4n, n, w, N.le_trans(1n+D4, 1n+Nat.add(D4, D2), hw.W(n), N.le_add_r(D4, D2), bsum))
  +e2 = hw.shlj_ex(2n, n, w, N.le_trans(1n+D2, 1n+Nat.add(D4, D2), hw.W(n), N.le_add_l(D4, D2), bsum))
  +esum = Equal.trans(Nat, Nat.add(Word.to_nat(n, s4), Word.to_nat(n, s2)), Nat.add(D4, Word.to_nat(n, s2)), Nat.add(D4, D2),
    Equal.cong(Nat, Nat, z => Nat.add(z, Word.to_nat(n, s2)), Word.to_nat(n, s4), D4, e4),
    Equal.cong(Nat, Nat, z => Nat.add(D4, z), Word.to_nat(n, s2), D2, e2))
  +ha = N.le_rw_l(1n+Nat.add(D4, D2), 1n+Nat.add(Word.to_nat(n, s4), Word.to_nat(n, s2)), hw.W(n),
    Equal.cong(Nat, Nat, z => 1n+z, Nat.add(D4, D2), Nat.add(Word.to_nat(n, s4), Word.to_nat(n, s2)),
      Equal.sym(Nat, Nat.add(Word.to_nat(n, s4), Word.to_nat(n, s2)), Nat.add(D4, D2), esum)), bsum)
  Equal.trans(Nat, Word.to_nat(n, Word.add(n, s4, s2)), Nat.add(D4, D2), hw.t20(X),
    Equal.trans(Nat, Word.to_nat(n, Word.add(n, s4, s2)), Nat.add(Word.to_nat(n, s4), Word.to_nat(n, s2)), Nat.add(D4, D2),
      hw.add_ex(n, s4, s2, ha), esum),
    ts)

def hw.rel_nge(c: Cmp, +x: Nat, +y: Nat, h: N.Rel(c, x, y), e: {Cmp.is_ge(c) == False{} : Bool}) -> N.Le(1n+x, y):
  match c:
    case LT{}:
      h
    case EQ{}:
      Empty.absurd(N.Le(1n+x, y), N.true_ne_false(e))
    case GT{}:
      Empty.absurd(N.Le(1n+x, y), N.true_ne_false(e))

# 20 × t20(2^4 x) = 2^4 × 20x
def hw.t20_D4(+x: Nat) -> {hw.t20(N.D(4n, x)) == N.D(4n, hw.t20(x)) : Nat}:
  +x1 = Nat.double(x)
  +x2 = Nat.double(x1)
  +x3 = Nat.double(x2)
  Equal.trans(Nat, hw.t20(Nat.double(x3)), Nat.double(hw.t20(x3)), Nat.double(Nat.double(Nat.double(Nat.double(hw.t20(x))))),
    hw.t20_double(x3),
    Equal.cong(Nat, Nat, z => Nat.double(z), hw.t20(x3), Nat.double(Nat.double(Nat.double(hw.t20(x)))),
      Equal.trans(Nat, hw.t20(x3), Nat.double(hw.t20(x2)), Nat.double(Nat.double(Nat.double(hw.t20(x)))),
        hw.t20_double(x2),
        Equal.cong(Nat, Nat, z => Nat.double(z), hw.t20(x2), Nat.double(Nat.double(hw.t20(x))),
          Equal.trans(Nat, hw.t20(x2), Nat.double(hw.t20(x1)), Nat.double(Nat.double(hw.t20(x))),
            hw.t20_double(x1),
            Equal.cong(Nat, Nat, z => Nat.double(z), hw.t20(x1), Nat.double(hw.t20(x)), hw.t20_double(x)))))))

# 0x0CCC...C, nibble by nibble: 12 + 16 × the rest
def hw.pat(j: Nat) -> Nat:
  match j:
    case 0n:
      0n
    case 1n+q:
      Nat.add(12n, N.D(4n, hw.pat(q)))

def hw.e4(j: Nat) -> Nat:
  match j:
    case 0n:
      4n
    case 1n+q:
      4n+hw.e4(q)

# 2^4 + 20 × pat(j) = 2^(4 + 4j)
def hw.pat_val(+j: Nat) -> {Nat.add(hw.W(4n), hw.t20(hw.pat(j))) == hw.W(hw.e4(j)) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+q:
      %hw.pat_val(q) : {256n+hw.t20(N.D(4n, hw.pat(q))) == N.D(4n, _) : Nat}
      %Equal.sym(Nat, hw.t20(N.D(4n, hw.pat(q))), N.D(4n, hw.t20(hw.pat(q))), hw.t20_D4(hw.pat(q))) :
        {256n+_ == 256n+N.D(4n, hw.t20(hw.pat(q))) : Nat}
      {==}

# 2^4 + 20 × pat(j) = 2^n, for n = 4 + 4j (j = 7: 2^4 + 20 × 214748364 =
# 2^32)
def hw.hP(+j: Nat, -n: Nat, e: {hw.e4(j) == n : Nat}) -> {Nat.add(hw.W(4n), hw.t20(hw.pat(j))) == hw.W(n) : Nat}:
  %e : {Nat.add(hw.W(4n), hw.t20(hw.pat(j))) == hw.W(_) : Nat}
  hw.pat_val(j)


# Kit (copied)
# ------------

def hf.P2(-A: Data, -B: Data) -> Data:
  Sigma<&2, &2, A, _ => B>

def hf.fst(-A: Data, -B: Data, p: hf.P2(A, B)) -> A:
  (a, b) = p
  a

def hf.snd(-A: Data, -B: Data, p: hf.P2(A, B)) -> B:
  (a, b) = p
  b

def hf.sub0(x: Nat) -> {Nat.sub(x, 0n) == x : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

# (1 + x) - f = 1 + (x - f), for f <= x
def hf.sub.succ.l(+x: Nat, +f: Nat, h: N.Le(f, x)) -> {Nat.sub(1n+x, f) == 1n+Nat.sub(x, f) : Nat}:
  match x f:
    case _ 0n:
      Equal.cong(Nat, Nat, z => 1n+z, x, Nat.sub(x, 0n), Equal.sym(Nat, Nat.sub(x, 0n), x, hf.sub0(x)))
    case 0n 1n+q:
      Empty.absurd({Nat.sub(1n, 1n+q) == 1n+Nat.sub(0n, 1n+q) : Nat}, h)
    case 1n+p 1n+q:
      hf.sub.succ.l(p, q, h)

def hf.W.subadd(+n: Nat, +x: Word(n), +p: Word(n), c: Bool) ->
  {Word.adc(n, Word.adc(n, x, p, True{}, c), p, False{}, Bool.not(c)) == x : Word(n)}:
  match n:
    case 0n:
      match x p:
        case WNil{} WNil{}:
          {==}
    case 1n+q:
      match x p c:
        case WCon{False{}, +xt} WCon{False{}, +pt} False{}:
          Equal.cong(Word(q), Word(1n+q), z => WCon{False{}, z}, Word.adc(q, Word.adc(q, xt, pt, True{}, False{}), pt, False{}, True{}), xt, hf.W.subadd(q, xt, pt, False{}))
        case WCon{False{}, +xt} WCon{False{}, +pt} True{}:
          Equal.cong(Word(q), Word(1n+q), z => WCon{False{}, z}, Word.adc(q, Word.adc(q, xt, pt, True{}, True{}), pt, False{}, False{}), xt, hf.W.subadd(q, xt, pt, True{}))
        case WCon{False{}, +xt} WCon{True{}, +pt} False{}:
          Equal.cong(Word(q), Word(1n+q), z => WCon{False{}, z}, Word.adc(q, Word.adc(q, xt, pt, True{}, False{}), pt, False{}, True{}), xt, hf.W.subadd(q, xt, pt, False{}))
        case WCon{False{}, +xt} WCon{True{}, +pt} True{}:
          Equal.cong(Word(q), Word(1n+q), z => WCon{False{}, z}, Word.adc(q, Word.adc(q, xt, pt, True{}, False{}), pt, False{}, True{}), xt, hf.W.subadd(q, xt, pt, False{}))
        case WCon{True{}, +xt} WCon{False{}, +pt} False{}:
          Equal.cong(Word(q), Word(1n+q), z => WCon{True{}, z}, Word.adc(q, Word.adc(q, xt, pt, True{}, True{}), pt, False{}, False{}), xt, hf.W.subadd(q, xt, pt, True{}))
        case WCon{True{}, +xt} WCon{False{}, +pt} True{}:
          Equal.cong(Word(q), Word(1n+q), z => WCon{True{}, z}, Word.adc(q, Word.adc(q, xt, pt, True{}, True{}), pt, False{}, False{}), xt, hf.W.subadd(q, xt, pt, True{}))
        case WCon{True{}, +xt} WCon{True{}, +pt} False{}:
          Equal.cong(Word(q), Word(1n+q), z => WCon{True{}, z}, Word.adc(q, Word.adc(q, xt, pt, True{}, False{}), pt, False{}, True{}), xt, hf.W.subadd(q, xt, pt, False{}))
        case WCon{True{}, +xt} WCon{True{}, +pt} True{}:
          Equal.cong(Word(q), Word(1n+q), z => WCon{True{}, z}, Word.adc(q, Word.adc(q, xt, pt, True{}, True{}), pt, False{}, False{}), xt, hf.W.subadd(q, xt, pt, True{}))

# (x - p) + p = x
def hf.U32.subadd(+x: U32, +p: U32) -> {U32.add(U32.sub(x, p), p) == x : U32}:
  match x p:
    case U32{+xw} U32{+pw}:
      Equal.cong(Word(32n), U32, z => U32{z}, Word.adc(32n, Word.adc(32n, xw, pw, True{}, True{}), pw, False{}, False{}), xw, hf.W.subadd(32n, xw, pw, True{}))

def hf.add.comm(+a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, N.add_zero(b))
    case 1n+p:
      Equal.trans(Nat, 1n+Nat.add(p, b), 1n+Nat.add(b, p), Nat.add(b, 1n+p),
        Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, b), Nat.add(b, p), hf.add.comm(p, b)),
        Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), N.add_succ_r(b, p)))

def hf.add.assoc(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(Nat.add(p, b), c), Nat.add(p, Nat.add(b, c)), hf.add.assoc(p, b, c))

def hf.le.add_r(+a: Nat, +b: Nat, +c: Nat, h: N.Le(a, b)) -> N.Le(Nat.add(a, c), Nat.add(b, c)):
  N.add_mono(a, b, c, c, h, N.le_refl(c))

def hf.sub.add(+x: Nat, +f: Nat, h: N.Le(f, x)) -> {Nat.add(Nat.sub(x, f), f) == x : Nat}:
  match x f:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({Nat.add(Nat.sub(0n, 1n+q), 1n+q) == 0n : Nat}, h)
    case 1n+p 0n:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, 0n), p, N.add_zero(p))
    case 1n+p 1n+q:
      Equal.trans(Nat, Nat.add(Nat.sub(p, q), 1n+q), 1n+Nat.add(Nat.sub(p, q), q), 1n+p, N.add_succ_r(Nat.sub(p, q), q),
        Equal.cong(Nat, Nat, z => 1n+z, Nat.add(Nat.sub(p, q), q), p, hf.sub.add(p, q, h)))

# a word of n bits is below 2^n
def hf.word.lt(+n: Nat, w: Word(n)) -> N.Le(1n+Word.to_nat(n, w), N.D(n, 1n)):
  match n:
    case 0n:
      match w:
        case WNil{}:
          Unit{}
    case 1n+p:
      match w:
        case WCon{False{}, +t}:
          N.lt_dd(Word.to_nat(p, t), N.D(p, 1n), hf.word.lt(p, t))
        case WCon{True{}, +t}:
          N.double_mono(1n+Word.to_nat(p, t), N.D(p, 1n), hf.word.lt(p, t))

# a U32 is below 2^32
def hf.u32.lt(x: U32) -> N.Le(1n+U32.to_nat(x), N.D(32n, 1n)):
  match x:
    case U32{+w}:
      N.le_rw_l(1n+Word.to_nat(32n, w), 1n+U32.to_nat(U32{w}), N.D(32n, 1n),
        Equal.cong(Nat, Nat, v => 1n+v, Word.to_nat(32n, w), U32.to_nat(U32{w}), Equal.sym(Nat, U32.to_nat(U32{w}), Word.to_nat(32n, w), N.u32_to_nat(w))),
        hf.word.lt(32n, w))

# The long division (copied from Compiler/Cir/simulation_first_cell_division.bend)
# -------------------------------------------------

def hf.dq(-p: Nat, x: Word(p) & U32) -> Word(p):
  (q, r) = x
  q

def hf.dr(-p: Nat, x: Word(p) & U32) -> U32:
  (q, r) = x
  r

def hf.out.put(+n: Nat, +c: Bool, +w: Word(n)) -> {Word.shl.out(n, c, w) == (hw.pout(n, c, w), Word.shl.put(n, c, w)) : Bool & Word(n)}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{+b, +t}:
          %Equal.sym(Bool & Word(p), Word.shl.out(p, b, t), (hw.pout(p, b, t), Word.shl.put(p, b, t)), hf.out.put(p, b, t)) : {Word.shl.out.con(p, c, _) == (hw.pout(p, b, t), WCon{c, Word.shl.put(p, b, t)}) : Bool & Word(1n+p)}
          {==}

def hf.wt(+q: Nat, a0: Bool, +hi: Word(q)) -> {Word.to_nat(1n+q, WCon{a0, hi}) == Nat.add(hw.bn(a0), Nat.double(Word.to_nat(q, hi))) : Nat}:
  match a0:
    case False{}:
      {==}
    case True{}:
      {==}

def hf.sub.self(x: Nat) -> {Nat.sub(x, x) == 0n : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      hf.sub.self(p)

def hf.add.sub.r(a: Nat, +b: Nat) -> {Nat.sub(Nat.add(a, b), b) == a : Nat}:
  match a:
    case 0n:
      hf.sub.self(b)
    case 1n+(+p):
      Equal.trans(Nat, Nat.sub(1n+Nat.add(p, b), b), 1n+Nat.sub(Nat.add(p, b), b), 1n+p,
        hf.sub.succ.l(Nat.add(p, b), b, N.le_add_l(p, b)), Equal.cong(Nat, Nat, z => 1n+z, Nat.sub(Nat.add(p, b), b), p, hf.add.sub.r(p, b)))

def hf.sub.nat.go(c: Bool, +X: Nat, +Y0: Nat, +D0: Nat, +T: Nat, eT: {N.D(32n, hw.bn(True{})) == T : Nat}, h: N.Le(Y0, X), hd: N.Le(1n+D0, T),
  e: {Nat.add(X, N.D(32n, hw.bn(c))) == Nat.add(D0, Y0) : Nat}) -> {D0 == Nat.sub(X, Y0) : Nat}:
  match c:
    case False{}:
      +e0 = Equal.trans(Nat, X, Nat.add(X, 0n), Nat.add(D0, Y0), Equal.sym(Nat, Nat.add(X, 0n), X, N.add_zero(X)), e)
      Equal.sym(Nat, Nat.sub(X, Y0), D0, Equal.trans(Nat, Nat.sub(X, Y0), Nat.sub(Nat.add(D0, Y0), Y0), D0,
        Equal.cong(Nat, Nat, z => Nat.sub(z, Y0), X, Nat.add(D0, Y0), e0), hf.add.sub.r(D0, Y0)))
    case True{}:
      +e1 = {(%eT : {Nat.add(X, _) == Nat.add(D0, Y0) : Nat}; e) : {Nat.add(X, T) == Nat.add(D0, Y0) : Nat}}
      +l1 = N.le_rw_l(Nat.add(D0, Y0), Nat.add(X, T), Nat.add(D0, Y0), Equal.sym(Nat, Nat.add(X, T), Nat.add(D0, Y0), e1), N.le_refl(Nat.add(D0, Y0)))
      +l2 = N.add_mono(D0, D0, Y0, X, N.le_refl(D0), h)
      +l3 = N.le_rw_r(1n+Nat.add(D0, X), Nat.add(T, X), Nat.add(X, T), hf.add.comm(T, X), hf.le.add_r(1n+D0, T, X, hd))
      Empty.absurd({D0 == Nat.sub(X, Y0) : Nat}, N.not_succ_le(Nat.add(D0, X),
        N.le_trans(1n+Nat.add(D0, X), Nat.add(X, T), Nat.add(D0, X), l3, N.le_trans(Nat.add(X, T), Nat.add(D0, Y0), Nat.add(D0, X), l1, l2))))

# x - y is exact for y <= x
def hf.sub.nat(+x: U32, +y: U32, h: N.Le(U32.to_nat(y), U32.to_nat(x))) -> {U32.to_nat(U32.sub(x, y)) == Nat.sub(U32.to_nat(x), U32.to_nat(y)) : Nat}:
  match x y:
    case U32{+xw} U32{+yw}:
      +d = Word.sub(32n, xw, yw)
      +X = Word.to_nat(32n, xw)
      +Y0 = Word.to_nat(32n, yw)
      +D0 = Word.to_nat(32n, d)
      +c = hw.cout(32n, d, yw, False{})
      +ea = hw.adc(32n, d, yw, False{})
      +es = Equal.cong(U32, Nat, z => U32.to_nat(z), U32.add(U32.sub(U32{xw}, U32{yw}), U32{yw}), U32{xw}, hf.U32.subadd(U32{xw}, U32{yw}))
      +es2 = {es : {Word.to_nat(32n, Word.adc(32n, d, yw, False{}, False{})) == X : Nat}}
      hf.sub.nat.go(c, X, Y0, D0, N.D(32n, 1n), Equal.cong(Nat, Nat, z => N.D(32n, z), hw.bn(True{}), 1n, {==}), h, hf.word.lt(32n, d),
        Equal.trans(Nat, Nat.add(X, N.D(32n, hw.bn(c))), Nat.add(Word.to_nat(32n, Word.adc(32n, d, yw, False{}, False{})), N.D(32n, hw.bn(c))),
          Nat.add(D0, Y0),
          Equal.cong(Nat, Nat, z => Nat.add(z, N.D(32n, hw.bn(c))), X, Word.to_nat(32n, Word.adc(32n, d, yw, False{}, False{})),
            Equal.sym(Nat, Word.to_nat(32n, Word.adc(32n, d, yw, False{}, False{})), X, es2)), ea))

def hf.DM(-p: Nat, x: Word(p) & U32, +B: Nat, +A0: Nat) -> Data:
  hf.P2({Nat.add(Nat.mul(Word.to_nat(p, hf.dq(p, x)), B), U32.to_nat(hf.dr(p, x))) == A0 : Nat}, N.Le(1n+U32.to_nat(hf.dr(p, x)), B))

def hf.ge.le(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), e: {Cmp.is_ge(c) == True{} : Bool}) -> N.Le(y, x):
  match c:
    case LT{}:
      Empty.absurd(N.Le(y, x), N.false_ne_true(e))
    case EQ{}:
      %r : N.Le(_, x)
      N.le_refl(x)
    case GT{}:
      N.weaken(y, x, r)

def hf.bn.le(a0: Bool, +x: Nat) -> N.Le(Nat.add(hw.bn(a0), x), 1n+x):
  match a0:
    case False{}:
      N.le_succ(x, x, N.le_refl(x))
    case True{}:
      N.le_refl(1n+x)

def hf.pout.f(b: Bool, +a0: Bool, +rw: Word(32n), +T: Nat, +eT: {N.D(32n, hw.bn(True{})) == T : Nat}, +H: Nat, +eH: {Nat.double(H) == T : Nat},
  +hR: N.Le(1n+Word.to_nat(32n, rw), H), +e: {hw.pout(32n, a0, rw) == b : Bool}) -> {hw.pout(32n, a0, rw) == False{} : Bool}:
  match b:
    case False{}:
      e
    case True{}:
      +V0 = Word.to_nat(32n, Word.shl.put(32n, a0, rw))
      +R0 = Word.to_nat(32n, rw)
      +ep = hw.put(32n, a0, rw)
      +ep1 = {(%e : {Nat.add(V0, N.D(32n, hw.bn(_))) == Nat.add(hw.bn(a0), Nat.double(R0)) : Nat}; ep) :
        {Nat.add(V0, N.D(32n, hw.bn(True{}))) == Nat.add(hw.bn(a0), Nat.double(R0)) : Nat}}
      +ep2 = {(%eT : {Nat.add(V0, _) == Nat.add(hw.bn(a0), Nat.double(R0)) : Nat}; ep1) : {Nat.add(V0, T) == Nat.add(hw.bn(a0), Nat.double(R0)) : Nat}}
      +l1 = N.le_rw_r(T, Nat.add(V0, T), Nat.add(hw.bn(a0), Nat.double(R0)), ep2, N.le_add_l(V0, T))
      +l2 = N.le_trans(T, Nat.add(hw.bn(a0), Nat.double(R0)), 1n+Nat.double(R0), l1, hf.bn.le(a0, Nat.double(R0)))
      +l3 = N.le_rw_r(2n+Nat.double(R0), Nat.double(H), T, eH, N.double_mono(1n+R0, H, hR))
      Empty.absurd({hw.pout(32n, a0, rw) == False{} : Bool}, N.not_succ_le(1n+Nat.double(R0), N.le_trans(2n+Nat.double(R0), T, 1n+Nat.double(R0), l3, l2)))

def hf.alg1(+QB: Nat, +a: Nat, +R: Nat) -> {Nat.add(Nat.double(QB), Nat.add(a, Nat.double(R))) == Nat.add(a, Nat.double(Nat.add(QB, R))) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.double(QB), Nat.add(a, Nat.double(R))), Nat.add(a, Nat.add(Nat.double(QB), Nat.double(R))), Nat.add(a, Nat.double(Nat.add(QB, R))),
    hw.add_k(Nat.double(QB), a, Nat.double(R)),
    Equal.cong(Nat, Nat, z => Nat.add(a, z), Nat.add(Nat.double(QB), Nat.double(R)), Nat.double(Nat.add(QB, R)),
      Equal.sym(Nat, Nat.double(Nat.add(QB, R)), Nat.add(Nat.double(QB), Nat.double(R)), N.double_add(QB, R))))

def hf.alg2(+B: Nat, +X: Nat, +S0: Nat, h: N.Le(B, S0)) -> {Nat.add(Nat.add(B, X), Nat.sub(S0, B)) == Nat.add(X, S0) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(B, X), Nat.sub(S0, B)), Nat.add(Nat.add(X, B), Nat.sub(S0, B)), Nat.add(X, S0),
    Equal.cong(Nat, Nat, z => Nat.add(z, Nat.sub(S0, B)), Nat.add(B, X), Nat.add(X, B), hf.add.comm(B, X)),
    Equal.trans(Nat, Nat.add(Nat.add(X, B), Nat.sub(S0, B)), Nat.add(X, Nat.add(B, Nat.sub(S0, B))), Nat.add(X, S0),
      hf.add.assoc(X, B, Nat.sub(S0, B)),
      Equal.cong(Nat, Nat, z => Nat.add(X, z), Nat.add(B, Nat.sub(S0, B)), S0,
        Equal.trans(Nat, Nat.add(B, Nat.sub(S0, B)), Nat.add(Nat.sub(S0, B), B), S0, hf.add.comm(B, Nat.sub(S0, B)), hf.sub.add(S0, B, h)))))

def hf.le.cancel.l(c: Nat, +a: Nat, +b: Nat, h: N.Le(Nat.add(c, a), Nat.add(c, b))) -> N.Le(a, b):
  match c:
    case 0n:
      h
    case 1n+p:
      hf.le.cancel.l(p, a, b, h)

def hf.alg3(+B: Nat, +S0: Nat, h: N.Le(B, S0), h2: N.Le(1n+S0, Nat.add(B, B))) -> N.Le(1n+Nat.sub(S0, B), B):
  +D0 = Nat.sub(S0, B)
  +h3 = N.le_rw_l(1n+S0, Nat.add(B, 1n+D0), Nat.add(B, B),
    Equal.trans(Nat, 1n+S0, 1n+Nat.add(D0, B), Nat.add(B, 1n+D0),
      Equal.cong(Nat, Nat, z => 1n+z, S0, Nat.add(D0, B), Equal.sym(Nat, Nat.add(D0, B), S0, hf.sub.add(S0, B, h))),
      hf.add.comm(1n+D0, B)), h2)
  hf.le.cancel.l(B, 1n+D0, B, h3)

def hf.dbl.add(+x: Nat) -> {Nat.double(x) == Nat.add(x, x) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+(+p):
      Equal.trans(Nat, 2n+Nat.double(p), 2n+Nat.add(p, p), 1n+Nat.add(p, 1n+p),
        Equal.cong(Nat, Nat, z => 2n+z, Nat.double(p), Nat.add(p, p), hf.dbl.add(p)),
        Equal.cong(Nat, Nat, z => 1n+z, 1n+Nat.add(p, p), Nat.add(p, 1n+p), Equal.sym(Nat, Nat.add(p, 1n+p), 1n+Nat.add(p, p), N.add_succ_r(p, p))))

def hf.dm.base(+q: Nat, +q0: Word(q), +S0: Nat, +B: Nat, +a0: Bool, +HI: Nat, +R0: Nat,
  +eih: {Nat.add(Nat.mul(Word.to_nat(q, q0), B), R0) == HI : Nat},
  +eS: {S0 == Nat.add(hw.bn(a0), Nat.double(R0)) : Nat}) ->
  {Nat.add(Nat.mul(Nat.double(Word.to_nat(q, q0)), B), S0) == Nat.add(hw.bn(a0), Nat.double(HI)) : Nat}:
  +Q0 = Word.to_nat(q, q0)
  Equal.trans(Nat, Nat.add(Nat.mul(Nat.double(Q0), B), S0), Nat.add(Nat.double(Nat.mul(Q0, B)), Nat.add(hw.bn(a0), Nat.double(R0))),
    Nat.add(hw.bn(a0), Nat.double(HI)),
    Equal.trans(Nat, Nat.add(Nat.mul(Nat.double(Q0), B), S0), Nat.add(Nat.double(Nat.mul(Q0, B)), S0), Nat.add(Nat.double(Nat.mul(Q0, B)), Nat.add(hw.bn(a0), Nat.double(R0))),
      Equal.cong(Nat, Nat, z => Nat.add(z, S0), Nat.mul(Nat.double(Q0), B), Nat.double(Nat.mul(Q0, B)), N.mul_double(Q0, B)),
      Equal.cong(Nat, Nat, z => Nat.add(Nat.double(Nat.mul(Q0, B)), z), S0, Nat.add(hw.bn(a0), Nat.double(R0)), eS)),
    Equal.trans(Nat, Nat.add(Nat.double(Nat.mul(Q0, B)), Nat.add(hw.bn(a0), Nat.double(R0))), Nat.add(hw.bn(a0), Nat.double(Nat.add(Nat.mul(Q0, B), R0))),
      Nat.add(hw.bn(a0), Nat.double(HI)), hf.alg1(Nat.mul(Q0, B), hw.bn(a0), R0),
      Equal.cong(Nat, Nat, z => Nat.add(hw.bn(a0), Nat.double(z)), Nat.add(Nat.mul(Q0, B), R0), HI, eih)))

def hf.dm.fin(g: Bool, +q: Nat, +q0: Word(q), +sput: Word(32n), +b: U32, +a0: Bool, +HI: Nat, +R0: Nat,
  +eg: {U32.is_ge(U32{sput}, b) == g : Bool},
  +eih: {Nat.add(Nat.mul(Word.to_nat(q, q0), U32.to_nat(b)), R0) == HI : Nat}, +rih: N.Le(1n+R0, U32.to_nat(b)),
  +eS: {Word.to_nat(32n, sput) == Nat.add(hw.bn(a0), Nat.double(R0)) : Nat}) ->
  hf.DM(1n+q, U32.divmod.go.fin(q, q0, U32{sput}, b, g), U32.to_nat(b), Nat.add(hw.bn(a0), Nat.double(HI))):
  match g:
    case False{}:
      +B = U32.to_nat(b)
      +S0 = Word.to_nat(32n, sput)
      (hf.dm.base(q, q0, S0, B, a0, HI, R0, eih, eS), hw.rel_nge(U32.cmp(U32{sput}, b), S0, B, N.U32.rel(U32{sput}, b), eg))
    case True{}:
      +B = U32.to_nat(b)
      +Q0 = Word.to_nat(q, q0)
      +S0 = Word.to_nat(32n, sput)
      +base = hf.dm.base(q, q0, S0, B, a0, HI, R0, eih, eS)
      +hBS = hf.ge.le(U32.cmp(U32{sput}, b), S0, B, N.U32.rel(U32{sput}, b), eg)
      +esub = hf.sub.nat(U32{sput}, b, hBS)
      +eq = Equal.trans(Nat, Nat.add(Nat.add(B, Nat.mul(Nat.double(Q0), B)), U32.to_nat(U32.sub(U32{sput}, b))),
        Nat.add(Nat.add(B, Nat.mul(Nat.double(Q0), B)), Nat.sub(S0, B)), Nat.add(hw.bn(a0), Nat.double(HI)),
        Equal.cong(Nat, Nat, z => Nat.add(Nat.add(B, Nat.mul(Nat.double(Q0), B)), z), U32.to_nat(U32.sub(U32{sput}, b)), Nat.sub(S0, B), esub),
        Equal.trans(Nat, Nat.add(Nat.add(B, Nat.mul(Nat.double(Q0), B)), Nat.sub(S0, B)), Nat.add(Nat.mul(Nat.double(Q0), B), S0),
          Nat.add(hw.bn(a0), Nat.double(HI)), hf.alg2(B, Nat.mul(Nat.double(Q0), B), S0, hBS), base))
      +h2 = N.le_rw_r(1n+S0, Nat.double(B), Nat.add(B, B), hf.dbl.add(B),
        N.le_trans(1n+S0, 2n+Nat.double(R0), Nat.double(B),
          N.le_rw_l(1n+Nat.add(hw.bn(a0), Nat.double(R0)), 1n+S0, 2n+Nat.double(R0),
            Equal.cong(Nat, Nat, z => 1n+z, Nat.add(hw.bn(a0), Nat.double(R0)), S0, Equal.sym(Nat, S0, Nat.add(hw.bn(a0), Nat.double(R0)), eS)),
            hf.bn.le(a0, Nat.double(R0))),
          N.double_mono(1n+R0, B, rih)))
      +lt = N.le_rw_l(1n+Nat.sub(S0, B), 1n+U32.to_nat(U32.sub(U32{sput}, b)), B,
        Equal.cong(Nat, Nat, z => 1n+z, Nat.sub(S0, B), U32.to_nat(U32.sub(U32{sput}, b)), Equal.sym(Nat, U32.to_nat(U32.sub(U32{sput}, b)), Nat.sub(S0, B), esub)),
        hf.alg3(B, S0, hBS, h2))
      (eq, lt)

def hf.dm.rec(+q: Nat, +a0: Bool, +b: U32, x: Word(q) & U32, +HI: Nat, +T: Nat, +eT: {N.D(32n, hw.bn(True{})) == T : Nat},
  +H: Nat, +eH: {Nat.double(H) == T : Nat}, +hb: N.Le(U32.to_nat(b), H), ih: hf.DM(q, x, U32.to_nat(b), HI)) ->
  hf.DM(1n+q, U32.divmod.go.rec(q, a0, b, x), U32.to_nat(b), Nat.add(hw.bn(a0), Nat.double(HI))):
  match x:
    case Tuple{+q0, +r0}:
      match r0:
        case U32{+rw}:
          (+eih, +rih) = ih
          +R0 = Word.to_nat(32n, rw)
          +sput = Word.shl.put(32n, a0, rw)
          +B = U32.to_nat(b)
          +hR = N.le_trans(1n+R0, B, H, rih, hb)
          +pf = hf.pout.f(hw.pout(32n, a0, rw), a0, rw, T, eT, H, eH, hR, {==})
          +ep = hw.put(32n, a0, rw)
          +ep0 = {(%pf :
              {Nat.add(Word.to_nat(32n, sput), N.D(32n, hw.bn(_))) == Nat.add(hw.bn(a0), Nat.double(R0)) : Nat}; ep) :
            {Nat.add(Word.to_nat(32n, sput), N.D(32n, hw.bn(False{}))) == Nat.add(hw.bn(a0), Nat.double(R0)) : Nat}}
          +eS = Equal.trans(Nat, Word.to_nat(32n, sput), Nat.add(Word.to_nat(32n, sput), 0n), Nat.add(hw.bn(a0), Nat.double(R0)),
            Equal.sym(Nat, Nat.add(Word.to_nat(32n, sput), 0n), Word.to_nat(32n, sput), N.add_zero(Word.to_nat(32n, sput))), ep0)
          %Equal.sym(Bool & Word(32n), Word.shl.out(32n, a0, rw), (hw.pout(32n, a0, rw), sput), hf.out.put(32n, a0, rw)) :
            hf.DM(1n+q, U32.divmod.go.shl(q, q0, b, _), B, Nat.add(hw.bn(a0), Nat.double(HI)))
          %Equal.sym(Bool, hw.pout(32n, a0, rw), False{}, pf) :
            hf.DM(1n+q, U32.divmod.go.fin(q, q0, U32{sput}, b, Bool.or(_, U32.is_ge(U32{sput}, b))), B, Nat.add(hw.bn(a0), Nat.double(HI)))
          hf.dm.fin(U32.is_ge(U32{sput}, b), q, q0, sput, b, a0, HI, R0, {==}, eih, rih, eS)

# the long division of a by b, for 1 <= b <= 2^31
def hf.dm(+p: Nat, +a: Word(p), +b: U32, +T: Nat, +eT: {N.D(32n, hw.bn(True{})) == T : Nat},
  +H: Nat, +eH: {Nat.double(H) == T : Nat}, +hb: N.Le(U32.to_nat(b), H), +hb1: N.Le(1n, U32.to_nat(b))) ->
  hf.DM(p, U32.divmod.go(p, a, b), U32.to_nat(b), Word.to_nat(p, a)):
  match p a:
    case 0n WNil{}:
      ({==}, hb1)
    case 1n+q WCon{+a0, +hi}:
      %Equal.sym(Nat, Word.to_nat(1n+q, WCon{a0, hi}), Nat.add(hw.bn(a0), Nat.double(Word.to_nat(q, hi))), hf.wt(q, a0, hi)) :
        hf.DM(1n+q, U32.divmod.go.rec(q, a0, b, U32.divmod.go(q, hi, b)), U32.to_nat(b), _)
      hf.dm.rec(q, a0, b, U32.divmod.go(q, hi, b), Word.to_nat(q, hi), T, eT, H, eH, hb, hf.dm(q, hi, b, T, eT, H, eH, hb, hb1))

def hf.dsucc(+k: Nat, +x: Nat) -> {N.D(1n+k, x) == Nat.double(N.D(k, x)) : Nat}:
  {==}

def hf.mul20(+q: Nat) -> {Nat.mul(q, 20n) == hw.t20(q) : Nat}:
  match q:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 20n+z, Nat.mul(p, 20n), hw.t20(p), hf.mul20(p))

def hf.div.dq(x: Word(32n) & U32) -> {U32.div.fin(x) == U32{hf.dq(32n, x)} : U32}:
  match x:
    case Tuple{q, r}:
      {==}

# x / 20 by its parts: 20 q <= x <= 19 + 20 q
def hf.div.of(+xw: Word(32n), d: hf.DM(32n, U32.divmod.go(32n, xw, 20), U32.to_nat(20), Word.to_nat(32n, xw))) ->
  hf.P2(N.Le(hw.t20(U32.to_nat(U32.div(U32{xw}, 20))), U32.to_nat(U32{xw})),
    N.Le(U32.to_nat(U32{xw}), 19n+hw.t20(U32.to_nat(U32.div(U32{xw}, 20))))):
  (+eq, +lt) = d
  +Q = Word.to_nat(32n, hf.dq(32n, U32.divmod.go(32n, xw, 20)))
  +R = U32.to_nat(hf.dr(32n, U32.divmod.go(32n, xw, 20)))
  +X = Word.to_nat(32n, xw)
  +eQ = Equal.trans(Nat, U32.to_nat(U32.div(U32{xw}, 20)), U32.to_nat(U32{hf.dq(32n, U32.divmod.go(32n, xw, 20))}), Q,
    Equal.cong(U32, Nat, z => U32.to_nat(z), U32.div.fin(U32.divmod.go(32n, xw, 20)), U32{hf.dq(32n, U32.divmod.go(32n, xw, 20))},
      hf.div.dq(U32.divmod.go(32n, xw, 20))),
    N.u32_to_nat(hf.dq(32n, U32.divmod.go(32n, xw, 20))))
  +e2 = Equal.trans(Nat, Nat.add(hw.t20(Q), R), Nat.add(Nat.mul(Q, 20n), R), X,
    Equal.cong(Nat, Nat, z => Nat.add(z, R), hw.t20(Q), Nat.mul(Q, 20n), Equal.sym(Nat, Nat.mul(Q, 20n), hw.t20(Q), hf.mul20(Q))), eq)
  +lo = N.le_rw_r(hw.t20(Q), Nat.add(hw.t20(Q), R), X, e2, N.le_add_r(hw.t20(Q), R))
  +hi0 = N.add_mono(hw.t20(Q), hw.t20(Q), R, 19n, N.le_refl(hw.t20(Q)), lt)
  +hi1 = N.le_rw_r(Nat.add(hw.t20(Q), R), Nat.add(hw.t20(Q), 19n), 19n+hw.t20(Q), hf.add.comm(hw.t20(Q), 19n), hi0)
  +hi = N.le_rw_l(Nat.add(hw.t20(Q), R), X, 19n+hw.t20(Q), e2, hi1)
  %Equal.sym(Nat, U32.to_nat(U32.div(U32{xw}, 20)), Q, eQ) :
    hf.P2(N.Le(hw.t20(_), U32.to_nat(U32{xw})), N.Le(U32.to_nat(U32{xw}), 19n+hw.t20(_)))
  (lo, hi)

def hf.div(+x: U32) -> hf.P2(N.Le(hw.t20(U32.to_nat(U32.div(x, 20))), U32.to_nat(x)),
    N.Le(U32.to_nat(x), 19n+hw.t20(U32.to_nat(U32.div(x, 20))))):
  match x:
    case U32{+xw}:
      hf.div.of(xw, hf.dm(32n, xw, 20, N.D(32n, 1n), Equal.cong(Nat, Nat, z => N.D(32n, z), hw.bn(True{}), 1n, {==}), N.D(31n, 1n),
        Equal.sym(Nat, N.D(32n, 1n), Nat.double(N.D(31n, 1n)), hf.dsucc(31n, 1n)), Unit{}, Unit{}))

# Numbers
# -------

# 20 x <= 32 x
def hf.t20.D5(x: Nat) -> N.Le(hw.t20(x), N.D(5n, x)):
  match x:
    case 0n:
      Unit{}
    case 1n+(+p):
      N.le_trans(hw.t20(p), N.D(5n, p), 12n+N.D(5n, p), hf.t20.D5(p), N.le_add_l(12n, N.D(5n, p)))

# x <= y, or y < x
def hf.cmp(x: Nat, y: Nat, -G: Type, kl: N.Le(x, y) -> G, kg: N.Le(1n+y, x) -> G) -> G:
  match x y:
    case 0n _:
      kl(N.le_zero(y))
    case 1n+a 0n:
      kg(N.le_zero(a))
    case 1n+a 1n+b:
      hf.cmp(a, b, G, kl, kg)

# 4 + t <= t is false
def hf.no4(+t: Nat, h: N.Le(4n+t, t)) -> Empty:
  N.not_succ_le(t, N.le_trans(1n+t, 4n+t, t, N.le_add_l(3n, 1n+t), h))

def hf.big.gt(+X: Nat, +P: Nat, +Y: Nat, eY: {N.D(6n, X) == Y : Nat}, hP: {Nat.add(hw.W(4n), hw.t20(P)) == Y : Nat},
  h: N.Le(1n+P, X)) -> Empty:
  +a = hw.t20_mono(1n+P, X, h)
  +b = N.le_trans(hw.t20(1n+P), hw.t20(X), N.D(6n, X), a,
    N.le_trans(hw.t20(X), N.D(5n, X), N.D(6n, X), hf.t20.D5(X), PG.le_double(N.D(5n, X))))
  +c = N.le_rw_r(hw.t20(1n+P), N.D(6n, X), Nat.add(hw.W(4n), hw.t20(P)),
    Equal.trans(Nat, N.D(6n, X), Y, Nat.add(hw.W(4n), hw.t20(P)), eY, Equal.sym(Nat, Nat.add(hw.W(4n), hw.t20(P)), Y, hP)), b)
  hf.no4(hw.t20(P), c)

# 2^6 X = 2^4 + 20 P gives X <= P
def hf.big(+X: Nat, +P: Nat, +Y: Nat, eY: {N.D(6n, X) == Y : Nat}, hP: {Nat.add(hw.W(4n), hw.t20(P)) == Y : Nat}) -> N.Le(X, P):
  hf.cmp(X, P, N.Le(X, P), h => h, h => Empty.absurd(N.Le(X, P), hf.big.gt(X, P, Y, eY, hP, h)))

def hf.eY(+a: Nat, +b: Nat, +c: Nat, e: {Nat.add(a, b) == c : Nat}) -> {N.D(a, N.D(b, 1n)) == hw.W(c) : Nat}:
  N.D_add(a, b, c, 1n, e)

# x < M gives x < P, for M = X and 2^6 X = 2^4 + 20 P (M = 2^26, P =
# 214748364)
def hf.lt.pat(+x: Nat, +M: U32, +X: Nat, +P: Nat, +Y: Nat, h: N.Le(1n+x, U32.to_nat(M)), eM: {U32.to_nat(M) == X : Nat},
  eY: {N.D(6n, X) == Y : Nat}, hP: {Nat.add(hw.W(4n), hw.t20(P)) == Y : Nat}) -> N.Le(1n+x, P):
  N.le_trans(1n+x, X, P, N.le_rw_r(1n+x, U32.to_nat(M), X, eM, h), hf.big(X, P, Y, eY, hP))

# Cir.at(c) = 20 c, for c <= P
def hf.at.val(+c: U32, +P: Nat, +hP: {Nat.add(hw.W(4n), hw.t20(P)) == hw.W(32n) : Nat}, +hx: N.Le(U32.to_nat(c), P)) ->
  {U32.to_nat(Cr.Cir.at(c)) == hw.t20(U32.to_nat(c)) : Nat}:
  match c:
    case U32{+w}:
      hw.tex_w(32n, w, P, hP, hx)

# k + 1, exact below 2^26
def hf.inc(+k: U32, hkM: N.Le(1n+U32.to_nat(k), U32.to_nat(67108864))) -> {U32.to_nat(U32.inc(k)) == 1n+U32.to_nat(k) : Nat}:
  PI.U32.inc_nat(k, Equal.sym(Bool, U32.is_zero(U32.inc(k)), False{}, MO.nz(k, 67108864, hkM)))

# 1 + t <= e gives t <= e - 1
def hf.le.pred(+t: Nat, +e: Nat, h: N.Le(1n+t, e)) -> N.Le(t, Nat.sub(e, 1n)):
  match e:
    case 0n:
      Empty.absurd(N.Le(t, Nat.sub(0n, 1n)), h)
    case 1n+(+q):
      N.le_rw_r(t, q, Nat.sub(1n+q, 1n), Equal.sym(Nat, Nat.sub(q, 0n), q, hf.sub0(q)), h)

# 1 + q <= 20 q, for 1 <= q
def hf.q.t20(+Q: Nat, hq: N.Le(1n, Q)) -> N.Le(1n+Q, hw.t20(Q)):
  match Q:
    case 0n:
      Empty.absurd(N.Le(1n, hw.t20(0n)), hq)
    case 1n+(+q):
      N.le_trans(q, hw.t20(q), 18n+hw.t20(q), hw.le_t20(q), N.le_add_l(18n, hw.t20(q)))

# 20 q <= x < T = 1 + Mx gives 1 + q <= Mx, for 1 <= q
def hf.qmax(+Q: Nat, +Xn: Nat, +T: Nat, +Mx: Nat, h1: N.Le(hw.t20(Q), Xn), h2: N.Le(1n+Xn, T), e: {1n+Mx == T : Nat},
  hq: N.Le(1n, Q)) -> N.Le(1n+Q, Mx):
  +a = N.le_trans(1n+hw.t20(Q), 1n+Xn, T, h1, h2)
  +b = N.le_rw_r(1n+hw.t20(Q), T, 1n+Mx, Equal.sym(Nat, 1n+Mx, T, e), a)
  N.le_trans(1n+Q, hw.t20(Q), Mx, hf.q.t20(Q, hq), b)

# The first cell
# --------------

def hf.first.t(+k: U32, +first: U32, hkM: N.Le(1n+U32.to_nat(k), U32.to_nat(67108864)),
  ef: {first == U32.inc(k) : U32}) -> N.Le(1n+U32.to_nat(k), U32.to_nat(first)):
  +e = Equal.trans(Nat, 1n+U32.to_nat(k), U32.to_nat(U32.inc(k)), U32.to_nat(first),
    Equal.sym(Nat, U32.to_nat(U32.inc(k)), 1n+U32.to_nat(k), hf.inc(k, hkM)),
    Equal.cong(U32, Nat, z => U32.to_nat(z), U32.inc(k), first, Equal.sym(U32, first, U32.inc(k), ef)))
  N.le_rw_r(1n+U32.to_nat(k), 1n+U32.to_nat(k), U32.to_nat(first), e, N.le_refl(1n+U32.to_nat(k)))

def hf.first.f(+k: U32, +E: U32, +first: U32, +hkM: N.Le(1n+U32.to_nat(k), U32.to_nat(67108864)),
  eb: {U32.is_ge(Cr.Cir.at(U32.inc(k)), E) == False{} : Bool},
  ef: {first == U32.inc(U32.div(U32.sub(E, 1), 20)) : U32}) -> N.Le(1n+U32.to_nat(k), U32.to_nat(first)):
  +n = U32.to_nat(k)
  +A = Cr.Cir.at(U32.inc(k))
  +hlt = hw.rel_nge(U32.cmp(A, E), U32.to_nat(A), U32.to_nat(E), N.U32.rel(A, E), eb)
  +ei = hf.inc(k, hkM)
  +hx = N.le_rw_l(1n+n, U32.to_nat(U32.inc(k)), hw.pat(7n), Equal.sym(Nat, U32.to_nat(U32.inc(k)), 1n+n, ei),
    hf.lt.pat(n, 67108864, N.D(26n, 1n), hw.pat(7n), hw.W(32n), hkM, PG.val_M2(), hf.eY(6n, 26n, 32n, {==}), hw.hP(7n, 32n, {==})))
  +eA = hf.at.val(U32.inc(k), hw.pat(7n), hw.hP(7n, 32n, {==}), hx)
  +eA2 = Equal.trans(Nat, U32.to_nat(A), hw.t20(U32.to_nat(U32.inc(k))), hw.t20(1n+n), eA,
    Equal.cong(Nat, Nat, z => hw.t20(z), U32.to_nat(U32.inc(k)), 1n+n, ei))
  +h1 = N.le_rw_l(1n+U32.to_nat(A), 1n+hw.t20(1n+n), U32.to_nat(E), Equal.cong(Nat, Nat, z => 1n+z, U32.to_nat(A), hw.t20(1n+n), eA2), hlt)
  +X = U32.sub(E, 1)
  +hE1 = N.le_trans(U32.to_nat(1), 1n+hw.t20(1n+n), U32.to_nat(E), N.le_zero(hw.t20(1n+n)), h1)
  +eX = hf.sub.nat(E, 1, hE1)
  +h2 = hf.le.pred(hw.t20(1n+n), U32.to_nat(E), h1)
  +h3 = N.le_rw_r(hw.t20(1n+n), Nat.sub(U32.to_nat(E), 1n), U32.to_nat(X), Equal.sym(Nat, U32.to_nat(X), Nat.sub(U32.to_nat(E), U32.to_nat(1)), eX), h2)
  +D = U32.div(X, 20)
  +Q = U32.to_nat(D)
  +dv = hf.div(X)
  +lo = hf.fst(N.Le(hw.t20(Q), U32.to_nat(X)), N.Le(U32.to_nat(X), 19n+hw.t20(Q)), dv)
  +hi = hf.snd(N.Le(hw.t20(Q), U32.to_nat(X)), N.Le(U32.to_nat(X), 19n+hw.t20(Q)), dv)
  +h4 = N.le_trans(hw.t20(1n+n), U32.to_nat(X), 19n+hw.t20(Q), h3, hi)
  +hQ = hw.t20_lt(1n+n, 1n+Q, h4)
  +hq1 = N.le_trans(1n, 1n+n, Q, N.le_zero(n), hQ)
  +hmax = hf.qmax(Q, U32.to_nat(X), N.D(32n, 1n), U32.to_nat(4294967295), lo, hf.u32.lt(X), MO.val_MAX(), hq1)
  +eD = PI.U32.inc_nat(D, Equal.sym(Bool, U32.is_zero(U32.inc(D)), False{}, MO.nz(D, 4294967295, hmax)))
  +e = Equal.trans(Nat, 1n+Q, U32.to_nat(U32.inc(D)), U32.to_nat(first), Equal.sym(Nat, U32.to_nat(U32.inc(D)), 1n+Q, eD),
    Equal.cong(U32, Nat, z => U32.to_nat(z), U32.inc(D), first, Equal.sym(U32, first, U32.inc(D), ef)))
  N.le_rw_r(1n+n, 1n+Q, U32.to_nat(first), e, N.weaken(n, Q, hQ))

def hf.first.of(b: Bool, +k: U32, +E: U32, +first: U32, hkM: N.Le(1n+U32.to_nat(k), U32.to_nat(67108864)),
  eb: {U32.is_ge(Cr.Cir.at(U32.inc(k)), E) == b : Bool},
  ef: {first == Bool.pick(U32, b, U32.inc(k), U32.inc(U32.div(U32.sub(E, 1), 20))) : U32}) -> N.Le(1n+U32.to_nat(k), U32.to_nat(first)):
  match b:
    case True{}:
      hf.first.t(k, first, hkM, ef)
    case False{}:
      hf.first.f(k, E, first, hkM, eb, ef)

# the first cell, Cir.first(k, 20 (k + 1) + len), is past the image's k
# cells, for k < 2^26
def hf.first.k(+k: U32, +len: U32, +first: U32, hkM: N.Le(1n+U32.to_nat(k), U32.to_nat(67108864)),
  ef: {first == Cr.Cir.first(k, U32.add(Cr.Cir.input.at(k), len)) : U32}) -> N.Le(1n+U32.to_nat(k), U32.to_nat(first)):
  hf.first.of(U32.is_ge(Cr.Cir.at(U32.inc(k)), U32.add(Cr.Cir.input.at(k), len)), k, U32.add(Cr.Cir.input.at(k), len), first, hkM, {==}, ef)

# and so it is at least 272, for 290 <= k
def hf.first(+k: U32, +len: U32, +first: U32, h290: N.Le(290n, U32.to_nat(k)), hkM: N.Le(1n+U32.to_nat(k), U32.to_nat(67108864)),
  ef: {first == Cr.Cir.first(k, U32.add(Cr.Cir.input.at(k), len)) : U32}) -> N.Le(272n, U32.to_nat(first)):
  N.le_trans(272n, 1n+U32.to_nat(k), U32.to_nat(first), N.le_trans(272n, 290n, 1n+U32.to_nat(k), Unit{}, N.le_succ(290n, U32.to_nat(k), h290)),
    hf.first.k(k, len, first, hkM, ef))

# The image's size
# ----------------

def hf.enc_len(xs: List<&2, Cr.Cir.Cell>) -> {U32.from_nat(List.length(&2, Cr.Cir.Cell, xs)) == Cr.Wasm.encode.len(Cr.Cir.Cell, xs) : U32}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, r}:
      Equal.cong(U32, U32, y => U32.inc(y), U32.from_nat(List.length(&2, Cr.Cir.Cell, r)), Cr.Wasm.encode.len(Cr.Cir.Cell, r), hf.enc_len(r))

# the image of a book of fewer than 2^26 bytes has fewer than 2^26 cells
def hf.hsm(+p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  small: {Mc.Img.small(p, 0) == True{} : Bool}) -> N.Le(1n+List.length(&2, Cr.Cir.Cell, Mc.Img.cells(ds)), U32.to_nat(67108864)):
  MO.lt_le(List.length(&2, Cr.Cir.Cell, Mc.Img.cells(ds)), U32.to_nat(67108864), PG.img.small.nat(p, ds, rd, small))

# k, the image's size, as a Nat
def hf.k.nat(+ds: List<&2, Bk.Def>, +k: U32, ek: {k == Cr.Wasm.encode.len(Cr.Cir.Cell, Mc.Img.cells(ds)) : U32},
  hsm: N.Le(1n+List.length(&2, Cr.Cir.Cell, Mc.Img.cells(ds)), U32.to_nat(67108864))) ->
  {U32.to_nat(k) == List.length(&2, Cr.Cir.Cell, Mc.Img.cells(ds)) : Nat}:
  +n = List.length(&2, Cr.Cir.Cell, Mc.Img.cells(ds))
  Equal.trans(Nat, U32.to_nat(k), U32.to_nat(U32.from_nat(n)), n,
    Equal.cong(U32, Nat, z => U32.to_nat(z), k, U32.from_nat(n),
      Equal.trans(U32, k, Cr.Wasm.encode.len(Cr.Cir.Cell, Mc.Img.cells(ds)), U32.from_nat(n), ek,
        Equal.sym(U32, U32.from_nat(n), Cr.Wasm.encode.len(Cr.Cir.Cell, Mc.Img.cells(ds)), hf.enc_len(Mc.Img.cells(ds))))),
    MO.tofrom(n, 67108864, N.weaken(n, U32.to_nat(67108864), hsm)))

# 290 <= k
def hf.k290(+ds: List<&2, Bk.Def>, +k: U32, ek: {k == Cr.Wasm.encode.len(Cr.Cir.Cell, Mc.Img.cells(ds)) : U32},
  hsm: N.Le(1n+List.length(&2, Cr.Cir.Cell, Mc.Img.cells(ds)), U32.to_nat(67108864))) -> N.Le(290n, U32.to_nat(k)):
  N.le_rw_r(290n, Nat.add(290n, PG.Bl(ds, 0n)), U32.to_nat(k),
    Equal.sym(Nat, U32.to_nat(k), Nat.add(290n, PG.Bl(ds, 0n)),
      Equal.trans(Nat, U32.to_nat(k), List.length(&2, Cr.Cir.Cell, Mc.Img.cells(ds)), Nat.add(290n, PG.Bl(ds, 0n)), hf.k.nat(ds, k, ek, hsm), PG.cells_len(ds))),
    N.le_add_r(290n, PG.Bl(ds, 0n)))

# k < 2^26
def hf.kM(+ds: List<&2, Bk.Def>, +k: U32, ek: {k == Cr.Wasm.encode.len(Cr.Cir.Cell, Mc.Img.cells(ds)) : U32},
  +hsm: N.Le(1n+List.length(&2, Cr.Cir.Cell, Mc.Img.cells(ds)), U32.to_nat(67108864))) -> N.Le(1n+U32.to_nat(k), U32.to_nat(67108864)):
  N.le_rw_l(1n+List.length(&2, Cr.Cir.Cell, Mc.Img.cells(ds)), 1n+U32.to_nat(k), U32.to_nat(67108864),
    Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, Cr.Cir.Cell, Mc.Img.cells(ds)), U32.to_nat(k),
      Equal.sym(Nat, U32.to_nat(k), List.length(&2, Cr.Cir.Cell, Mc.Img.cells(ds)), hf.k.nat(ds, k, ek, hsm))), hsm)

# hF: the first cell is past the table, from what Cir.result computed
def hf.hF(+p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +k: U32, +len: U32, +first: U32,
  rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>}, small: {Mc.Img.small(p, 0) == True{} : Bool},
  +ek: {k == Cr.Wasm.encode.len(Cr.Cir.Cell, Mc.Img.cells(ds)) : U32},
  ef: {first == Cr.Cir.first(k, U32.add(Cr.Cir.input.at(k), len)) : U32}) -> N.Le(272n, U32.to_nat(first)):
  +hsm = hf.hsm(p, ds, rd, small)
  hf.first(k, len, first, hf.k290(ds, k, ek, hsm), hf.kM(ds, k, ek, hsm), ef)

# and past the image, from what Cir.result computed
def hf.kF(+p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +k: U32, +len: U32, +first: U32,
  rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>}, small: {Mc.Img.small(p, 0) == True{} : Bool},
  +ek: {k == Cr.Wasm.encode.len(Cr.Cir.Cell, Mc.Img.cells(ds)) : U32},
  ef: {first == Cr.Cir.first(k, U32.add(Cr.Cir.input.at(k), len)) : U32}) -> N.Le(1n+U32.to_nat(k), U32.to_nat(first)):
  hf.first.k(k, len, first, hf.kM(ds, k, ek, hf.hsm(p, ds, rd, small)), ef)
