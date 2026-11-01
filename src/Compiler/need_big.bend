# compiler: the proof of need.big
# ================================
#
# A book of 2^26 bytes or more needs more memory than a module can have:
#
#   need   = 64 × (size + S) + 2^24 >= 64 × |p| + 1 >= 2^32 + 1
#   memory = 65536 × min(m, 65536)  <= 2^16 × 2^16  = 2^32
#
# where size, the program's size, is at least |p| for a book that Book.read
# reads (size.ge).
#
# The big numbers stay symbolic: 2^k is D(k, 1n), and the literals meet it
# only through lemmas about the words of their bits, so the checker never
# counts to them. Every lemma is stated over variables, so its proof only
# computes with variables; the final proof only chains instances of them.

import Base
import ../Book/impl.bend as Bk
import ../Wasm/impl.bend as Wa
import ../Program/impl.bend as Pg
import ./Machine/impl.bend as Mc

# Kit
# ---

# the truth of b as a type
def T(b: Bool) -> Data:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

# a <= b, as a type
def Le(a: Nat, b: Nat) -> Data:
  T(Nat.is_le(a, b))

# True is not False
def true_ne_false(e: {True{} == False{} : Bool}) -> Empty:
  %e : T(_)
  Unit{}

# False is not True
def false_ne_true(e: {False{} == True{} : Bool}) -> Empty:
  %e : T(Bool.not(_))
  Unit{}

# a Bool equal to True is true
def toT(b: Bool, e: {b == True{} : Bool}) -> T(b):
  match b:
    case True{}:
      Unit{}
    case False{}:
      false_ne_true(e)

# Order of Nat
# ------------

# 0 is at most every number
def le_zero(b: Nat) -> Le(0n, b):
  match b:
    case 0n:
      Unit{}
    case 1n+q:
      Unit{}

# a <= a
def le_refl(a: Nat) -> Le(a, a):
  match a:
    case 0n:
      Unit{}
    case 1n+p:
      le_refl(p)

# a <= b gives a <= 1 + b
def le_succ(a: Nat, b: Nat, h: Le(a, b)) -> Le(a, 1n+b):
  match a:
    case 0n:
      Unit{}
    case 1n+p:
      match b:
        case 0n:
          Empty.absurd(Le(1n+p, 1n), h)
        case 1n+q:
          le_succ(p, q, h)

# 1 + a <= b gives a <= b
def weaken(a: Nat, b: Nat, h: Le(1n+a, b)) -> Le(a, b):
  match a:
    case 0n:
      le_zero(b)
    case 1n+p:
      match b:
        case 0n:
          Empty.absurd(Le(1n+p, 0n), h)
        case 1n+q:
          weaken(p, q, h)

# a <= b and b <= c give a <= c
def le_trans(+a: Nat, +b: Nat, +c: Nat, h1: Le(a, b), h2: Le(b, c)) -> Le(a, c):
  match a:
    case 0n:
      le_zero(c)
    case 1n+p:
      match b:
        case 0n:
          Empty.absurd(Le(1n+p, c), h1)
        case 1n+q:
          match c:
            case 0n:
              Empty.absurd(Le(1n+p, 0n), h2)
            case 1n+r:
              le_trans(p, q, r, h1, h2)

# 1 + a <= a is false
def not_succ_le(a: Nat, h: Le(1n+a, a)) -> Empty:
  match a:
    case 0n:
      h
    case 1n+p:
      not_succ_le(p, h)

# a <= b rewritten on the left
def le_rw_l(-a: Nat, -b: Nat, -c: Nat, e: {a == b : Nat}, h: Le(a, c)) -> Le(b, c):
  %e : Le(_, c)
  h

# a <= b rewritten on the right
def le_rw_r(-a: Nat, -b: Nat, -c: Nat, e: {b == c : Nat}, h: Le(a, b)) -> Le(a, c):
  %e : Le(a, _)
  h

# a Bool comparison that holds gives a <= b
def toLe(a: Nat, b: Nat, e: {Nat.is_le(a, b) == True{} : Bool}) -> Le(a, b):
  toT(Nat.is_le(a, b), e)

# Addition and order
# ------------------

# a <= a + b
def le_add_r(a: Nat, b: Nat) -> Le(a, Nat.add(a, b)):
  match a:
    case 0n:
      le_zero(b)
    case 1n+p:
      le_add_r(p, b)

# d <= b + d
def le_add_l(+b: Nat, +d: Nat) -> Le(d, Nat.add(b, d)):
  match b:
    case 0n:
      le_refl(d)
    case 1n+q:
      le_succ(d, Nat.add(q, d), le_add_l(q, d))

# 1 + a <= a + 1
def le_succ_add(a: Nat) -> Le(1n+a, Nat.add(a, 1n)):
  match a:
    case 0n:
      Unit{}
    case 1n+p:
      le_succ_add(p)

# 1 + a <= a + (1 + b)
def lt_add(a: Nat, b: Nat) -> Le(1n+a, Nat.add(a, 1n+b)):
  match a:
    case 0n:
      le_zero(b)
    case 1n+p:
      lt_add(p, b)

# a <= b and c <= d give a + c <= b + d
def add_mono(+a: Nat, +b: Nat, +c: Nat, +d: Nat, h1: Le(a, b), h2: Le(c, d)) -> Le(Nat.add(a, c), Nat.add(b, d)):
  match a:
    case 0n:
      le_trans(c, d, Nat.add(b, d), h2, le_add_l(b, d))
    case 1n+p:
      match b:
        case 0n:
          Empty.absurd(Le(Nat.add(1n+p, c), d), h1)
        case 1n+q:
          add_mono(p, q, c, d, h1, h2)

# a <= b gives 2a <= 2b
def double_mono(+a: Nat, +b: Nat, h: Le(a, b)) -> Le(Nat.double(a), Nat.double(b)):
  match a:
    case 0n:
      le_zero(Nat.double(b))
    case 1n+p:
      match b:
        case 0n:
          Empty.absurd(Le(Nat.double(1n+p), 0n), h)
        case 1n+q:
          double_mono(p, q, h)

# b <= c gives a × b <= a × c
def mul_mono_r(+a: Nat, +b: Nat, +c: Nat, +h: Le(b, c)) -> Le(Nat.mul(a, b), Nat.mul(a, c)):
  match a:
    case 0n:
      Unit{}
    case 1n+p:
      add_mono(b, c, Nat.mul(p, b), Nat.mul(p, c), h, mul_mono_r(p, b, c, h))

# a <= b gives a × c <= b × c
def mul_mono_l(+a: Nat, +b: Nat, +c: Nat, h: Le(a, b)) -> Le(Nat.mul(a, c), Nat.mul(b, c)):
  match a:
    case 0n:
      le_zero(Nat.mul(b, c))
    case 1n+p:
      match b:
        case 0n:
          Empty.absurd(Le(Nat.mul(1n+p, c), 0n), h)
        case 1n+q:
          add_mono(c, c, Nat.mul(p, c), Nat.mul(q, c), le_refl(c), mul_mono_l(p, q, c, h))

# Equations of Nat
# ----------------

# a + 0 = a
def add_zero(a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

# a + (1 + b) = 1 + (a + b)
def add_succ_r(a: Nat, +b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_succ_r(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

# 2(a + b) = 2a + 2b
def double_add(a: Nat, +b: Nat) -> {Nat.double(Nat.add(a, b)) == Nat.add(Nat.double(a), Nat.double(b)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %double_add(p, b) : {2n+Nat.double(Nat.add(p, b)) == 2n+_ : Nat}
      {==}

# b + (b + x) = 2b + x
def add_double(+b: Nat, +x: Nat) -> {Nat.add(b, Nat.add(b, x)) == Nat.add(Nat.double(b), x) : Nat}:
  match b:
    case 0n:
      {==}
    case 1n+q:
      %add_double(q, x) : {1n+Nat.add(q, 1n+Nat.add(q, x)) == 2n+_ : Nat}
      %add_succ_r(q, Nat.add(q, x)) : {1n+Nat.add(q, 1n+Nat.add(q, x)) == 1n+_ : Nat}
      {==}

# 2a × b = 2(a × b)
def mul_double(+a: Nat, +b: Nat) -> {Nat.mul(Nat.double(a), b) == Nat.double(Nat.mul(a, b)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.double(Nat.add(b, Nat.mul(p, b))), Nat.add(Nat.double(b), Nat.double(Nat.mul(p, b))), double_add(b, Nat.mul(p, b))) : {Nat.add(b, Nat.add(b, Nat.mul(Nat.double(p), b))) == _ : Nat}
      %mul_double(p, b) : {Nat.add(b, Nat.add(b, Nat.mul(Nat.double(p), b))) == Nat.add(Nat.double(b), _) : Nat}
      add_double(b, Nat.mul(Nat.double(p), b))

# Powers of two
# -------------

# 2^k × x
def D(k: Nat, x: Nat) -> Nat:
  match k:
    case 0n:
      x
    case 1n+q:
      Nat.double(D(q, x))

# 2^k × b, as a product
def mul_D(+k: Nat, +b: Nat) -> {Nat.mul(D(k, 1n), b) == D(k, b) : Nat}:
  match k:
    case 0n:
      add_zero(b)
    case 1n+q:
      %mul_D(q, b) : {Nat.mul(Nat.double(D(q, 1n)), b) == Nat.double(_) : Nat}
      mul_double(D(q, 1n), b)

# 2^a × 2^b × x = 2^(a + b) × x
def D_add.go(+a: Nat, +b: Nat, +x: Nat) -> {D(a, D(b, x)) == D(Nat.add(a, b), x) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %D_add.go(p, b, x) : {Nat.double(D(p, D(b, x))) == Nat.double(_) : Nat}
      {==}

# 2^a × 2^b × x = 2^c × x, when a + b = c
def D_add(+a: Nat, +b: Nat, -c: Nat, +x: Nat, e: {Nat.add(a, b) == c : Nat}) -> {D(a, D(b, x)) == D(c, x) : Nat}:
  %e : {D(a, D(b, x)) == D(_, x) : Nat}
  D_add.go(a, b, x)

# Words
# -----

# the word of n bits whose k lowest bits are set
def ones(n: Nat, k: Nat) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match k:
        case 0n:
          WCon{False{}, ones(p, 0n)}
        case 1n+q:
          WCon{True{}, ones(p, q)}

# the word of n bits whose k-th bit alone is set
def bit(n: Nat, k: Nat) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match k:
        case 0n:
          WCon{True{}, ones(p, 0n)}
        case 1n+q:
          WCon{False{}, bit(p, q)}

# the word of no set bits is 0
def ones_zero(+n: Nat) -> {Word.to_nat(n, ones(n, 0n)) == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Word.to_nat(p, ones(p, 0n)), 0n, ones_zero(p)) : {Nat.double(_) == 0n : Nat}
      {==}

# k set bits make 2^k - 1
def ones_val(+n: Nat, +k: Nat, h: Le(k, n)) -> {1n+Word.to_nat(n, ones(n, k)) == D(k, 1n) : Nat}:
  match n:
    case 0n:
      match k:
        case 0n:
          {==}
        case 1n+q:
          Empty.absurd({1n+Word.to_nat(0n, ones(0n, 1n+q)) == D(1n+q, 1n) : Nat}, h)
    case 1n+p:
      match k:
        case 0n:
          %Equal.sym(Nat, Word.to_nat(p, ones(p, 0n)), 0n, ones_zero(p)) : {1n+Nat.double(_) == 1n : Nat}
          {==}
        case 1n+q:
          %ones_val(p, q, h) : {2n+Nat.double(Word.to_nat(p, ones(p, q))) == Nat.double(_) : Nat}
          {==}

# the k-th bit makes 2^k
def bit_val(+n: Nat, +k: Nat, h: Le(1n+k, n)) -> {Word.to_nat(n, bit(n, k)) == D(k, 1n) : Nat}:
  match n:
    case 0n:
      Empty.absurd({Word.to_nat(0n, bit(0n, k)) == D(k, 1n) : Nat}, h)
    case 1n+p:
      match k:
        case 0n:
          %Equal.sym(Nat, Word.to_nat(p, ones(p, 0n)), 0n, ones_zero(p)) : {1n+Nat.double(_) == 1n : Nat}
          {==}
        case 1n+q:
          %bit_val(p, q, h) : {Nat.double(Word.to_nat(p, bit(p, q))) == Nat.double(_) : Nat}
          {==}

# the number of a U32 is the number of its word
def u32_to_nat(+w: Word(32n)) -> {U32.to_nat(U32{w}) == Word.to_nat(32n, w) : Nat}:
  {==}

# the increment adds at most 1
def Word.inc_le(+n: Nat, w: Word(n)) -> Le(Word.to_nat(n, Word.inc(n, w)), 1n+Word.to_nat(n, w)):
  match n:
    case 0n:
      Unit{}
    case 1n+p:
      match w:
        case WCon{False{}, +t}:
          le_refl(1n+Nat.double(Word.to_nat(p, t)))
        case WCon{True{}, +t}:
          double_mono(Word.to_nat(p, Word.inc(p, t)), 1n+Word.to_nat(p, t), Word.inc_le(p, t))

def U32.inc_le(a: U32) -> Le(U32.to_nat(U32.inc(a)), 1n+U32.to_nat(a)):
  match a:
    case U32{w}:
      Word.inc_le(32n, w)

# Comparison of words
# -------------------

# what a comparison says of the numbers it compares
def Rel(c: Cmp, x: Nat, y: Nat) -> Type:
  match c:
    case LT{}:
      Le(1n+x, y)
    case EQ{}:
      {x == y : Nat}
    case GT{}:
      Le(1n+y, x)

# 1 + x <= y gives 1 + 2x <= 2y
def lt_dd(+x: Nat, +y: Nat, h: Le(1n+x, y)) -> Le(1n+Nat.double(x), Nat.double(y)):
  weaken(1n+Nat.double(x), Nat.double(y), double_mono(1n+x, y, h))

# x = y gives 2x = 2y
def eq_dd(-x: Nat, -y: Nat, h: {x == y : Nat}) -> {Nat.double(x) == Nat.double(y) : Nat}:
  %h : {Nat.double(x) == Nat.double(_) : Nat}
  {==}

# x = y gives 2x + 1 = 2y + 1
def eq_dd1(-x: Nat, -y: Nat, h: {x == y : Nat}) -> {1n+Nat.double(x) == 1n+Nat.double(y) : Nat}:
  %h : {1n+Nat.double(x) == 1n+Nat.double(_) : Nat}
  {==}

# x = y gives 2x + 1 <= 2y + 1
def eq_le1(+x: Nat, -y: Nat, h: {x == y : Nat}) -> Le(1n+Nat.double(x), 1n+Nat.double(y)):
  %h : Le(1n+Nat.double(x), 1n+Nat.double(_))
  le_refl(1n+Nat.double(x))

# the low bits 0 and 0
def rel.ff(c: Cmp, +x: Nat, +y: Nat, h: Rel(c, x, y)) -> Rel(Word.cmp.fin(False{}, False{}, c), Nat.double(x), Nat.double(y)):
  match c:
    case LT{}:
      lt_dd(x, y, h)
    case EQ{}:
      eq_dd(x, y, h)
    case GT{}:
      lt_dd(y, x, h)

# the low bits 0 and 1
def rel.ft(c: Cmp, +x: Nat, +y: Nat, h: Rel(c, x, y)) -> Rel(Word.cmp.fin(False{}, True{}, c), Nat.double(x), 1n+Nat.double(y)):
  match c:
    case LT{}:
      double_mono(x, y, weaken(x, y, h))
    case EQ{}:
      eq_le1(x, y, h)
    case GT{}:
      double_mono(1n+y, x, h)

# the low bits 1 and 0
def rel.tf(c: Cmp, +x: Nat, +y: Nat, h: Rel(c, x, y)) -> Rel(Word.cmp.fin(True{}, False{}, c), 1n+Nat.double(x), Nat.double(y)):
  match c:
    case LT{}:
      double_mono(1n+x, y, h)
    case EQ{}:
      eq_le1(y, x, Equal.sym(Nat, x, y, h))
    case GT{}:
      double_mono(y, x, weaken(y, x, h))

# the low bits 1 and 1
def rel.tt(c: Cmp, +x: Nat, +y: Nat, h: Rel(c, x, y)) -> Rel(Word.cmp.fin(True{}, True{}, c), 1n+Nat.double(x), 1n+Nat.double(y)):
  match c:
    case LT{}:
      lt_dd(x, y, h)
    case EQ{}:
      eq_dd1(x, y, h)
    case GT{}:
      lt_dd(y, x, h)

# a comparison of words says how their numbers compare
def Word.rel(+n: Nat, a: Word(n), b: Word(n)) -> Rel(Word.cmp(n, a, b), Word.to_nat(n, a), Word.to_nat(n, b)):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{False{}, +at} WCon{False{}, +bt}:
          rel.ff(Word.cmp(p, at, bt), Word.to_nat(p, at), Word.to_nat(p, bt), Word.rel(p, at, bt))
        case WCon{False{}, +at} WCon{True{}, +bt}:
          rel.ft(Word.cmp(p, at, bt), Word.to_nat(p, at), Word.to_nat(p, bt), Word.rel(p, at, bt))
        case WCon{True{}, +at} WCon{False{}, +bt}:
          rel.tf(Word.cmp(p, at, bt), Word.to_nat(p, at), Word.to_nat(p, bt), Word.rel(p, at, bt))
        case WCon{True{}, +at} WCon{True{}, +bt}:
          rel.tt(Word.cmp(p, at, bt), Word.to_nat(p, at), Word.to_nat(p, bt), Word.rel(p, at, bt))

# a comparison of U32s says how their numbers compare
def U32.rel(a: U32, b: U32) -> Rel(U32.cmp(a, b), U32.to_nat(a), U32.to_nat(b)):
  match a b:
    case U32{x} U32{y}:
      Word.rel(32n, x, y)

# a comparison at most EQ gives x <= y
def rel_le(c: Cmp, +x: Nat, +y: Nat, h: Rel(c, x, y), e: T(Cmp.is_le(c))) -> Le(x, y):
  match c:
    case LT{}:
      weaken(x, y, h)
    case EQ{}:
      %h : Le(x, _)
      le_refl(x)
    case GT{}:
      Empty.absurd(Le(x, y), e)

# a comparison EQ gives x = y
def rel_eq(c: Cmp, -x: Nat, -y: Nat, h: Rel(c, x, y), e: T(Cmp.is_eq(c))) -> {x == y : Nat}:
  match c:
    case LT{}:
      Empty.absurd({x == y : Nat}, e)
    case EQ{}:
      h
    case GT{}:
      Empty.absurd({x == y : Nat}, e)

# the minimum of m and k, by the branch of U32.is_le(m, k)
def min.case(b: Bool, +m: U32, +k: U32, e: {U32.is_le(m, k) == b : Bool}) -> Le(U32.to_nat(Wa.Wasm.min.if(b, m, k)), U32.to_nat(k)):
  match b:
    case True{}:
      rel_le(U32.cmp(m, k), U32.to_nat(m), U32.to_nat(k), U32.rel(m, k), toT(U32.is_le(m, k), e))
    case False{}:
      le_refl(U32.to_nat(k))

# Length of a big image
# ---------------------

# 0 + x = x, with the 0 of a U32
def zero_add(+x: Nat) -> {Nat.add(U32.to_nat(0), x) == x : Nat}:
  {==}

# one step of Img.small, for any limit M, by the branch of U32.is_eq(n, M)
def small.step(
  b: Bool, +n: U32, +M: U32, +h: Word(8n), +rest: List<&2, Word(8n)>,
  eb: {U32.is_eq(n, M) == b : Bool},
  e: {Mc.Img.small.if(b, u => Mc.Img.small(rest, U32.inc(n))) == False{} : Bool},
  ih: {Mc.Img.small(rest, U32.inc(n)) == False{} : Bool} ->
    Le(1n+U32.to_nat(M), Nat.add(U32.to_nat(U32.inc(n)), List.length(&2, Word(8n), rest)))
) -> Le(1n+U32.to_nat(M), Nat.add(U32.to_nat(n), List.length(&2, Word(8n), Con{h, rest}))):
  match b:
    case True{}:
      +nm = rel_eq(U32.cmp(n, M), U32.to_nat(n), U32.to_nat(M), U32.rel(n, M), toT(U32.is_eq(n, M), eb))
      %Equal.sym(Nat, U32.to_nat(n), U32.to_nat(M), nm) : Le(1n+U32.to_nat(M), Nat.add(_, 1n+List.length(&2, Word(8n), rest)))
      lt_add(U32.to_nat(M), List.length(&2, Word(8n), rest))
    case False{}:
      %Equal.sym(Nat, Nat.add(U32.to_nat(n), 1n+List.length(&2, Word(8n), rest)), 1n+Nat.add(U32.to_nat(n), List.length(&2, Word(8n), rest)), add_succ_r(U32.to_nat(n), List.length(&2, Word(8n), rest))) : Le(1n+U32.to_nat(M), _)
      le_trans(1n+U32.to_nat(M), Nat.add(U32.to_nat(U32.inc(n)), List.length(&2, Word(8n), rest)), 1n+Nat.add(U32.to_nat(n), List.length(&2, Word(8n), rest)), ih(e),
        add_mono(U32.to_nat(U32.inc(n)), 1n+U32.to_nat(n), List.length(&2, Word(8n), rest), List.length(&2, Word(8n), rest), U32.inc_le(n), le_refl(List.length(&2, Word(8n), rest))))

# Img.small(xs, n) false: n + |xs| > 67108863
def small.len(xs: List<&2, Word(8n)>, +n: U32, e: {Mc.Img.small(xs, n) == False{} : Bool}) ->
  Le(1n+U32.to_nat(67108863), Nat.add(U32.to_nat(n), List.length(&2, Word(8n), xs))):
  match xs:
    case Nil{}:
      Empty.absurd(Le(1n+U32.to_nat(67108863), Nat.add(U32.to_nat(n), List.length(&2, Word(8n), Nil{}))), true_ne_false(e))
    case Con{+h, +rest}:
      small.step(U32.is_eq(n, 67108863), n, 67108863, h, rest, {==}, e, e2 => small.len(rest, U32.inc(n), e2))

# The literals
# ------------

# 67108863 is the word of 26 set bits
def lit_M() -> {67108863 == U32{ones(32n, 26n)} : U32}:
  {==}

# 65536 is the word of bit 16
def lit_65536() -> {65536 == U32{bit(32n, 16n)} : U32}:
  {==}

# 1 + 67108863 = 2^26
def val_M() -> {1n+U32.to_nat(67108863) == D(26n, 1n) : Nat}:
  %Equal.sym(U32, 67108863, U32{ones(32n, 26n)}, lit_M()) : {1n+U32.to_nat(_) == D(26n, 1n) : Nat}
  %Equal.sym(Nat, U32.to_nat(U32{ones(32n, 26n)}), Word.to_nat(32n, ones(32n, 26n)), u32_to_nat(ones(32n, 26n))) : {1n+_ == D(26n, 1n) : Nat}
  ones_val(32n, 26n, Unit{})

# 65536 = 2^16
def val_65536() -> {U32.to_nat(65536) == D(16n, 1n) : Nat}:
  %Equal.sym(U32, 65536, U32{bit(32n, 16n)}, lit_65536()) : {U32.to_nat(_) == D(16n, 1n) : Nat}
  %Equal.sym(Nat, U32.to_nat(U32{bit(32n, 16n)}), Word.to_nat(32n, bit(32n, 16n)), u32_to_nat(bit(32n, 16n))) : {_ == D(16n, 1n) : Nat}
  bit_val(32n, 16n, Unit{})

# 64 = 2^6
def val_64() -> {D(6n, 1n) == 64n : Nat}:
  {==}

# 65536 × 65536 = 2^32
def sq_65536() -> {Nat.mul(U32.to_nat(65536), U32.to_nat(65536)) == D(32n, 1n) : Nat}:
  %Equal.sym(Nat, U32.to_nat(65536), D(16n, 1n), val_65536()) : {Nat.mul(_, _) == D(32n, 1n) : Nat}
  Equal.trans(Nat, Nat.mul(D(16n, 1n), D(16n, 1n)), D(16n, D(16n, 1n)), D(32n, 1n),
    mul_D(16n, D(16n, 1n)), D_add(16n, 16n, 32n, 1n, {==}))

# 64 × 2^26 = 2^32
def mul_64() -> {Nat.mul(64n, D(26n, 1n)) == D(32n, 1n) : Nat}:
  %val_64() : {Nat.mul(_, D(26n, 1n)) == D(32n, 1n) : Nat}
  Equal.trans(Nat, Nat.mul(D(6n, 1n), D(26n, 1n)), D(6n, D(26n, 1n)), D(32n, 1n),
    mul_D(6n, D(26n, 1n)), D_add(6n, 26n, 32n, 1n, {==}))

# the Nat 65536 is at most the number of the U32 65536
def le_65536() -> Le(65536n, U32.to_nat(65536)):
  Unit{}

# 1 <= 2^24
def le_one() -> Le(1n, 16777216n):
  Unit{}

# The memory
# ----------
#
# Program.memory(m) is Nat.mul(65536n, y): a check that unfolds it against
# another spelling of that product walks the 65536 steps of the literal, deeper
# than the checker's stack. So the proof spells the product as the checker
# holds it once it has evaluated it, Nat.add(y, Nat.mul(65535n, y)) with y
# U32.to_nat(C.Wasm.min.if(Cmp.is_le(U32.cmp(m, 65536)), m, 65536)), and
# meets it there: Q opens a goal on a fresh copy x of Program.memory(m); the
# first rewrite compares two spellings of the goal that unfold x, so the
# checker evaluates x in place, and the last step then matches the product with
# x as written, without unfolding the literal.

# the goal of bridge, on a fresh copy of x
def Q(x: Nat, d: Nat) -> Type:
  @e1: {x == x : Nat} -> @e2: {x == x : Nat} -> Le(x, d)

# a proof of the goal on the copy proves it on x
def use(+x: Nat, +d: Nat, k: Q(x, d)) -> Le(x, d):
  k({==}, {==})

# 65536 × y, as the checker holds the evaluated Program.memory(m)
def bridge(+m: U32, +d: Nat,
  h: Le(Nat.add(U32.to_nat(Wa.Wasm.min.if(Cmp.is_le(U32.cmp(m, 65536)), m, 65536)),
    Nat.mul(65535n, U32.to_nat(Wa.Wasm.min.if(Cmp.is_le(U32.cmp(m, 65536)), m, 65536)))), d)
) -> Le(Pg.Program.memory(m), d):
  use(Pg.Program.memory(m), d, e1 => e2 =>
    %e1 : T(Nat.is_le(_, d))
    %e2 : Le(_, d)
    h)

# (1 + k) × y = y + k × y
def mul_succ(+k: Nat, +y: Nat) -> {Nat.mul(1n+k, y) == Nat.add(y, Nat.mul(k, y)) : Nat}:
  {==}

# the memory of m is at most 2^32
def memory_le(+m: U32) -> Le(Pg.Program.memory(m), D(32n, 1n)):
  +y = U32.to_nat(Wa.Wasm.min.if(Cmp.is_le(U32.cmp(m, 65536)), m, 65536))
  +t = U32.to_nat(65536)
  +hy = min.case(Cmp.is_le(U32.cmp(m, 65536)), m, 65536, {==})
  +h = le_trans(Nat.mul(65536n, y), Nat.mul(t, y), D(32n, 1n),
    mul_mono_l(65536n, t, y, le_65536()),
    le_rw_r(Nat.mul(t, y), Nat.mul(t, t), D(32n, 1n), sq_65536(), mul_mono_r(t, y, t, hy)))
  bridge(m, D(32n, 1n), le_rw_l(Nat.mul(65536n, y), Nat.add(y, Nat.mul(65535n, y)), D(32n, 1n), mul_succ(65535n, y), h))

# The program's size
# ------------------
#
# A book that Book.read reads from p has at least |p| nodes in its data form
# (C.Program.size): each token of 2 bytes makes a constructor or a list cell
# of 3 nodes or more, and the reader discards nothing. G counts 2 for each
# token that built a value, plus a: the stack's G grows by 2 a token (the top
# item holds the rest), and a value's G is at most its nodes, plus a.

# (a + b) + c = a + (b + c)
def add_assoc(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_assoc(p, b, c) : {1n+Nat.add(Nat.add(p, b), c) == 1n+_ : Nat}
      {==}

# a + (b + c) = b + (a + c)
def add_swap(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(a, Nat.add(b, c)) == Nat.add(b, Nat.add(a, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(b, 1n+Nat.add(p, c)), 1n+Nat.add(b, Nat.add(p, c)), add_succ_r(b, Nat.add(p, c))) : {1n+Nat.add(p, Nat.add(b, c)) == _ : Nat}
      %add_swap(p, b, c) : {1n+Nat.add(p, Nat.add(b, c)) == 1n+_ : Nat}
      {==}

# b + (c + a) = (c + b) + a
def add_comm3(+b: Nat, +c: Nat, +a: Nat) -> {Nat.add(b, Nat.add(c, a)) == Nat.add(Nat.add(c, b), a) : Nat}:
  Equal.trans(Nat, Nat.add(b, Nat.add(c, a)), Nat.add(c, Nat.add(b, a)), Nat.add(Nat.add(c, b), a),
    add_swap(b, c, a), Equal.sym(Nat, Nat.add(Nat.add(c, b), a), Nat.add(c, Nat.add(b, a)), add_assoc(c, b, a)))

# ((f1 + f2) + f3) + a = (f1 + (f2 + f3)) + a
def assoc_l(+f1: Nat, +f2: Nat, +f3: Nat, +a: Nat) ->
  {Nat.add(Nat.add(Nat.add(f1, f2), f3), a) == Nat.add(Nat.add(f1, Nat.add(f2, f3)), a) : Nat}:
  %add_assoc(f1, f2, f3) : {Nat.add(Nat.add(Nat.add(f1, f2), f3), a) == Nat.add(_, a) : Nat}
  {==}

# 2 + (a + l) = a + (2 + l)
def add_two(+a: Nat, +l: Nat) -> {2n+Nat.add(a, l) == Nat.add(a, 2n+l) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_two(p, l) : {3n+Nat.add(p, l) == 1n+_ : Nat}
      {==}

# x + x = 2x
def add_self(+x: Nat) -> {Nat.add(x, x) == Nat.double(x) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(p, 1n+p), 1n+Nat.add(p, p), add_succ_r(p, p)) : {1n+_ == Nat.double(1n+p) : Nat}
      %add_self(p) : {2n+Nat.add(p, p) == 2n+_ : Nat}
      {==}

# u <= z gives u <= k + z
def le_plus(+k: Nat, +u: Nat, +z: Nat, h: Le(u, z)) -> Le(u, Nat.add(k, z)):
  le_trans(u, z, Nat.add(k, z), h, le_add_l(k, z))

# 2l <= (2 + k) × l
def dbl_mul(+k: Nat, +l: Nat) -> Le(Nat.double(l), Nat.mul(2n+k, l)):
  le_rw_l(Nat.add(l, l), Nat.double(l), Nat.mul(2n+k, l), add_self(l),
    add_mono(l, l, l, Nat.mul(1n+k, l), le_refl(l), le_add_r(l, Nat.mul(k, l))))

# u <= fx + y and y <= fy + a give u <= (fx + fy) + a
def chain2(+u: Nat, +y: Nat, +fx: Nat, +fy: Nat, +a: Nat, hx: Le(u, Nat.add(fx, y)), hy: Le(y, Nat.add(fy, a))) ->
  Le(u, Nat.add(Nat.add(fx, fy), a)):
  le_trans(u, Nat.add(fx, y), Nat.add(Nat.add(fx, fy), a), hx,
    le_rw_r(Nat.add(fx, y), Nat.add(fx, Nat.add(fy, a)), Nat.add(Nat.add(fx, fy), a),
      Equal.sym(Nat, Nat.add(Nat.add(fx, fy), a), Nat.add(fx, Nat.add(fy, a)), add_assoc(fx, fy, a)),
      add_mono(fx, fx, y, Nat.add(fy, a), le_refl(fx), hy)))

# u <= fo + y and y <= fn + a give u <= (fn + fo) + a
def chainr(+u: Nat, +y: Nat, +fo: Nat, +fn: Nat, +a: Nat, hx: Le(u, Nat.add(fo, y)), hy: Le(y, Nat.add(fn, a))) ->
  Le(u, Nat.add(Nat.add(fn, fo), a)):
  le_trans(u, Nat.add(fo, y), Nat.add(Nat.add(fn, fo), a), hx,
    le_rw_r(Nat.add(fo, y), Nat.add(fo, Nat.add(fn, a)), Nat.add(Nat.add(fn, fo), a), add_comm3(fo, fn, a),
      add_mono(fo, fo, y, Nat.add(fn, a), le_refl(fo), hy)))

# chainr with 2 more in the addend of y
def chainq(+u: Nat, +y: Nat, +fo: Nat, +fn: Nat, +a: Nat, hx: Le(u, Nat.add(fo, y)), hy: Le(y, Nat.add(fn, 2n+a))) ->
  Le(u, 2n+Nat.add(Nat.add(fn, fo), a)):
  le_rw_r(u, Nat.add(Nat.add(fn, fo), 2n+a), 2n+Nat.add(Nat.add(fn, fo), a),
    Equal.sym(Nat, 2n+Nat.add(Nat.add(fn, fo), a), Nat.add(Nat.add(fn, fo), 2n+a), add_two(Nat.add(fn, fo), a)),
    chainr(u, y, fo, fn, 2n+a, hx, hy))

# three in a row: u over y over z
def chain3(+u: Nat, +y: Nat, +z: Nat, +f1: Nat, +f2: Nat, +f3: Nat, +a: Nat,
  h3: Le(u, Nat.add(f3, y)), h2: Le(y, Nat.add(f2, z)), h1: Le(z, Nat.add(f1, a))) ->
  Le(u, Nat.add(Nat.add(f1, Nat.add(f2, f3)), a)):
  le_rw_r(u, Nat.add(Nat.add(Nat.add(f1, f2), f3), a), Nat.add(Nat.add(f1, Nat.add(f2, f3)), a), assoc_l(f1, f2, f3, a),
    chainr(u, y, f3, Nat.add(f1, f2), a, h3, chainr(y, z, f2, f1, a, h2, h1)))

# G of a Nat, plus a
def Gn(i: Nat, a: Nat) -> Nat:
  match i:
    case 0n:
      2n+a
    case 1n+q:
      2n+Gn(q, a)

# G of a name, plus a
def Gk(k: List<&2, Word(8n)>, a: Nat) -> Nat:
  match k:
    case Nil{}:
      2n+a
    case Con{_, rest}:
      2n+Gk(rest, a)

# G of names, plus a
def Gks(ks: List<&2, List<&2, Word(8n)>>, a: Nat) -> Nat:
  match ks:
    case Nil{}:
      2n+a
    case Con{k, rest}:
      2n+Gk(k, Gks(rest, a))

# G of a term, plus a: its last field outermost, as the reader pops it
def Gt(t: Bk.Term, a: Nat) -> Nat:
  match t:
    case Bk.Term.Var{x1}:
      2n+Gn(x1, a)
    case Bk.Term.Ref{x1}:
      2n+Gk(x1, a)
    case Bk.Term.Ann{x1, x2}:
      2n+Gt(x2, Gt(x1, a))
    case Bk.Term.Let{_, x1, x2}:
      2n+Gt(x2, Gt(x1, 2n+a))
    case Bk.Term.Typ{x1}:
      2n+Gt(x1, a)
    case Bk.Term.Min{x1, x2}:
      2n+Gt(x2, Gt(x1, a))
    case Bk.Term.All{_, x1, x2}:
      2n+Gt(x2, Gt(x1, 2n+a))
    case Bk.Term.Lam{_, x1}:
      2n+Gt(x1, 2n+a)
    case Bk.Term.App{_, x1, x2}:
      2n+Gt(x2, Gt(x1, 2n+a))
    case Bk.Term.Sig{_, x1, x2}:
      2n+Gt(x2, Gt(x1, 2n+a))
    case Bk.Term.Tup{_, x1, x2}:
      2n+Gt(x2, Gt(x1, 2n+a))
    case Bk.Term.Prj{x1}:
      2n+Gt(x1, a)
    case Bk.Term.Enu{x1}:
      2n+Gks(x1, a)
    case Bk.Term.Lab{x1}:
      2n+Gk(x1, a)
    case Bk.Term.Mat{x1, x2, x3}:
      2n+Gt(x3, Gt(x2, Gk(x1, a)))
    case Bk.Term.Efq{}:
      2n+a
    case Bk.Term.Eql{x1, x2, x3}:
      2n+Gt(x3, Gt(x2, Gt(x1, a)))
    case Bk.Term.Rfl{}:
      2n+a
    case Bk.Term.Rwt{x1, x2, x3}:
      2n+Gt(x3, Gt(x2, Gt(x1, a)))

# G of a def, plus a
def Gdef(d: Bk.Def, a: Nat) -> Nat:
  match d:
    case Bk.Def{k, ty, v, _}:
      4n+Gt(v, Gt(ty, Gk(k, a)))

# G of defs, plus a
def Gd(ds: List<&2, Bk.Def>, a: Nat) -> Nat:
  match ds:
    case Nil{}:
      2n+a
    case Con{d, rest}:
      2n+Gdef(d, Gd(rest, a))

# G of an item, plus a
def Gi(it: Bk.Item, a: Nat) -> Nat:
  match it:
    case Bk.Item.quan{_}:
      2n+a
    case Bk.Item.nat{i}:
      Gn(i, a)
    case Bk.Item.name{k}:
      Gk(k, a)
    case Bk.Item.names{ks}:
      Gks(ks, a)
    case Bk.Item.bool{_}:
      2n+a
    case Bk.Item.term{t}:
      Gt(t, a)
    case Bk.Item.def{d}:
      Gdef(d, a)
    case Bk.Item.defs{ds}:
      Gd(ds, a)

# G of a stack, plus a: the top item outermost
def Gs(st: List<&2, Bk.Item>, a: Nat) -> Nat:
  match st:
    case Nil{}:
      a
    case Con{it, rest}:
      Gi(it, Gs(rest, a))

# G of a reader's state
def Gm(st: Maybe<List<&2, Bk.Item>>) -> Nat:
  match st:
    case None{}:
      0n
    case Some{s}:
      Gs(s, 0n)

# a token's result: none, or a stack of G 2 more than w
def Ge(r: Maybe<List<&2, Bk.Item>>, w: Nat) -> Type:
  match r:
    case None{}:
      Unit
    case Some{s}:
      Le(2n+w, Gs(s, 0n))

# Each token adds 2 to G
# ---------------------

def succ.ge(s0: List<&2, Bk.Item>) -> Ge(Bk.Book.read.succ(s0), Gs(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{Bk.Item.quan{_}, _}:
      Unit{}
    case Con{Bk.Item.nat{+x1}, +rest}:
      le_refl(Gs(Con{Bk.Item.nat{1n+x1}, rest}, 0n))
    case Con{Bk.Item.name{_}, _}:
      Unit{}
    case Con{Bk.Item.names{_}, _}:
      Unit{}
    case Con{Bk.Item.bool{_}, _}:
      Unit{}
    case Con{Bk.Item.term{_}, _}:
      Unit{}
    case Con{Bk.Item.def{_}, _}:
      Unit{}
    case Con{Bk.Item.defs{_}, _}:
      Unit{}

def byte.ge(s0: List<&2, Bk.Item>, b: Word(8n)) -> Ge(Bk.Book.read.byte(s0, b), Gs(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{Bk.Item.quan{_}, _}:
      Unit{}
    case Con{Bk.Item.nat{_}, _}:
      Unit{}
    case Con{Bk.Item.name{+x1}, +rest}:
      le_refl(Gs(Con{Bk.Item.name{Con{b, x1}}, rest}, 0n))
    case Con{Bk.Item.names{_}, _}:
      Unit{}
    case Con{Bk.Item.bool{_}, _}:
      Unit{}
    case Con{Bk.Item.term{_}, _}:
      Unit{}
    case Con{Bk.Item.def{_}, _}:
      Unit{}
    case Con{Bk.Item.defs{_}, _}:
      Unit{}

def names.ge(s0: List<&2, Bk.Item>) -> Ge(Bk.Book.read.names(s0), Gs(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{Bk.Item.quan{_}, _}:
      Unit{}
    case Con{Bk.Item.nat{_}, _}:
      Unit{}
    case Con{Bk.Item.name{+x1}, +s1}:
      match s1:
        case Nil{}:
          Unit{}
        case Con{Bk.Item.quan{_}, _}:
          Unit{}
        case Con{Bk.Item.nat{_}, _}:
          Unit{}
        case Con{Bk.Item.name{_}, _}:
          Unit{}
        case Con{Bk.Item.names{+x2}, +rest}:
          le_refl(Gs(Con{Bk.Item.names{Con{x1, x2}}, rest}, 0n))
        case Con{Bk.Item.bool{_}, _}:
          Unit{}
        case Con{Bk.Item.term{_}, _}:
          Unit{}
        case Con{Bk.Item.def{_}, _}:
          Unit{}
        case Con{Bk.Item.defs{_}, _}:
          Unit{}
    case Con{Bk.Item.names{_}, _}:
      Unit{}
    case Con{Bk.Item.bool{_}, _}:
      Unit{}
    case Con{Bk.Item.term{_}, _}:
      Unit{}
    case Con{Bk.Item.def{_}, _}:
      Unit{}
    case Con{Bk.Item.defs{_}, _}:
      Unit{}

def defs.ge(s0: List<&2, Bk.Item>) -> Ge(Bk.Book.read.defs(s0), Gs(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{Bk.Item.quan{_}, _}:
      Unit{}
    case Con{Bk.Item.nat{_}, _}:
      Unit{}
    case Con{Bk.Item.name{_}, _}:
      Unit{}
    case Con{Bk.Item.names{_}, _}:
      Unit{}
    case Con{Bk.Item.bool{_}, _}:
      Unit{}
    case Con{Bk.Item.term{_}, _}:
      Unit{}
    case Con{Bk.Item.def{+x1}, +s1}:
      match s1:
        case Nil{}:
          Unit{}
        case Con{Bk.Item.quan{_}, _}:
          Unit{}
        case Con{Bk.Item.nat{_}, _}:
          Unit{}
        case Con{Bk.Item.name{_}, _}:
          Unit{}
        case Con{Bk.Item.names{_}, _}:
          Unit{}
        case Con{Bk.Item.bool{_}, _}:
          Unit{}
        case Con{Bk.Item.term{_}, _}:
          Unit{}
        case Con{Bk.Item.def{_}, _}:
          Unit{}
        case Con{Bk.Item.defs{+x2}, +rest}:
          le_refl(Gs(Con{Bk.Item.defs{Con{x1, x2}}, rest}, 0n))
    case Con{Bk.Item.defs{_}, _}:
      Unit{}

def def.ge(s0: List<&2, Bk.Item>) -> Ge(Bk.Book.read.def(s0), Gs(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{Bk.Item.quan{_}, _}:
      Unit{}
    case Con{Bk.Item.nat{_}, _}:
      Unit{}
    case Con{Bk.Item.name{_}, _}:
      Unit{}
    case Con{Bk.Item.names{_}, _}:
      Unit{}
    case Con{Bk.Item.bool{+x1}, +s1}:
      match s1:
        case Nil{}:
          Unit{}
        case Con{Bk.Item.quan{_}, _}:
          Unit{}
        case Con{Bk.Item.nat{_}, _}:
          Unit{}
        case Con{Bk.Item.name{_}, _}:
          Unit{}
        case Con{Bk.Item.names{_}, _}:
          Unit{}
        case Con{Bk.Item.bool{_}, _}:
          Unit{}
        case Con{Bk.Item.term{+x2}, +s2}:
          match s2:
            case Nil{}:
              Unit{}
            case Con{Bk.Item.quan{_}, _}:
              Unit{}
            case Con{Bk.Item.nat{_}, _}:
              Unit{}
            case Con{Bk.Item.name{_}, _}:
              Unit{}
            case Con{Bk.Item.names{_}, _}:
              Unit{}
            case Con{Bk.Item.bool{_}, _}:
              Unit{}
            case Con{Bk.Item.term{+x3}, +s3}:
              match s3:
                case Nil{}:
                  Unit{}
                case Con{Bk.Item.quan{_}, _}:
                  Unit{}
                case Con{Bk.Item.nat{_}, _}:
                  Unit{}
                case Con{Bk.Item.name{+x4}, +rest}:
                  le_refl(Gs(Con{Bk.Item.def{Bk.Def{x4, x3, x2, x1}}, rest}, 0n))
                case Con{Bk.Item.names{_}, _}:
                  Unit{}
                case Con{Bk.Item.bool{_}, _}:
                  Unit{}
                case Con{Bk.Item.term{_}, _}:
                  Unit{}
                case Con{Bk.Item.def{_}, _}:
                  Unit{}
                case Con{Bk.Item.defs{_}, _}:
                  Unit{}
            case Con{Bk.Item.def{_}, _}:
              Unit{}
            case Con{Bk.Item.defs{_}, _}:
              Unit{}
        case Con{Bk.Item.def{_}, _}:
          Unit{}
        case Con{Bk.Item.defs{_}, _}:
          Unit{}
    case Con{Bk.Item.term{_}, _}:
      Unit{}
    case Con{Bk.Item.def{_}, _}:
      Unit{}
    case Con{Bk.Item.defs{_}, _}:
      Unit{}

def var.ge(s0: List<&2, Bk.Item>) -> Ge(Bk.Book.read.var(s0), Gs(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{Bk.Item.quan{_}, _}:
      Unit{}
    case Con{Bk.Item.nat{+x1}, +rest}:
      le_refl(Gs(Con{Bk.Item.term{Bk.Term.Var{x1}}, rest}, 0n))
    case Con{Bk.Item.name{_}, _}:
      Unit{}
    case Con{Bk.Item.names{_}, _}:
      Unit{}
    case Con{Bk.Item.bool{_}, _}:
      Unit{}
    case Con{Bk.Item.term{_}, _}:
      Unit{}
    case Con{Bk.Item.def{_}, _}:
      Unit{}
    case Con{Bk.Item.defs{_}, _}:
      Unit{}

def ref.ge(s0: List<&2, Bk.Item>) -> Ge(Bk.Book.read.ref(s0), Gs(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{Bk.Item.quan{_}, _}:
      Unit{}
    case Con{Bk.Item.nat{_}, _}:
      Unit{}
    case Con{Bk.Item.name{+x1}, +rest}:
      le_refl(Gs(Con{Bk.Item.term{Bk.Term.Ref{x1}}, rest}, 0n))
    case Con{Bk.Item.names{_}, _}:
      Unit{}
    case Con{Bk.Item.bool{_}, _}:
      Unit{}
    case Con{Bk.Item.term{_}, _}:
      Unit{}
    case Con{Bk.Item.def{_}, _}:
      Unit{}
    case Con{Bk.Item.defs{_}, _}:
      Unit{}

def ann.ge(s0: List<&2, Bk.Item>) -> Ge(Bk.Book.read.ann(s0), Gs(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{Bk.Item.quan{_}, _}:
      Unit{}
    case Con{Bk.Item.nat{_}, _}:
      Unit{}
    case Con{Bk.Item.name{_}, _}:
      Unit{}
    case Con{Bk.Item.names{_}, _}:
      Unit{}
    case Con{Bk.Item.bool{_}, _}:
      Unit{}
    case Con{Bk.Item.term{+x1}, +s1}:
      match s1:
        case Nil{}:
          Unit{}
        case Con{Bk.Item.quan{_}, _}:
          Unit{}
        case Con{Bk.Item.nat{_}, _}:
          Unit{}
        case Con{Bk.Item.name{_}, _}:
          Unit{}
        case Con{Bk.Item.names{_}, _}:
          Unit{}
        case Con{Bk.Item.bool{_}, _}:
          Unit{}
        case Con{Bk.Item.term{+x2}, +rest}:
          le_refl(Gs(Con{Bk.Item.term{Bk.Term.Ann{x2, x1}}, rest}, 0n))
        case Con{Bk.Item.def{_}, _}:
          Unit{}
        case Con{Bk.Item.defs{_}, _}:
          Unit{}
    case Con{Bk.Item.def{_}, _}:
      Unit{}
    case Con{Bk.Item.defs{_}, _}:
      Unit{}

def let.ge(s0: List<&2, Bk.Item>) -> Ge(Bk.Book.read.let(s0), Gs(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{Bk.Item.quan{_}, _}:
      Unit{}
    case Con{Bk.Item.nat{_}, _}:
      Unit{}
    case Con{Bk.Item.name{_}, _}:
      Unit{}
    case Con{Bk.Item.names{_}, _}:
      Unit{}
    case Con{Bk.Item.bool{_}, _}:
      Unit{}
    case Con{Bk.Item.term{+x1}, +s1}:
      match s1:
        case Nil{}:
          Unit{}
        case Con{Bk.Item.quan{_}, _}:
          Unit{}
        case Con{Bk.Item.nat{_}, _}:
          Unit{}
        case Con{Bk.Item.name{_}, _}:
          Unit{}
        case Con{Bk.Item.names{_}, _}:
          Unit{}
        case Con{Bk.Item.bool{_}, _}:
          Unit{}
        case Con{Bk.Item.term{+x2}, +s2}:
          match s2:
            case Nil{}:
              Unit{}
            case Con{Bk.Item.quan{+x3}, +rest}:
              le_refl(Gs(Con{Bk.Item.term{Bk.Term.Let{x3, x2, x1}}, rest}, 0n))
            case Con{Bk.Item.nat{_}, _}:
              Unit{}
            case Con{Bk.Item.name{_}, _}:
              Unit{}
            case Con{Bk.Item.names{_}, _}:
              Unit{}
            case Con{Bk.Item.bool{_}, _}:
              Unit{}
            case Con{Bk.Item.term{_}, _}:
              Unit{}
            case Con{Bk.Item.def{_}, _}:
              Unit{}
            case Con{Bk.Item.defs{_}, _}:
              Unit{}
        case Con{Bk.Item.def{_}, _}:
          Unit{}
        case Con{Bk.Item.defs{_}, _}:
          Unit{}
    case Con{Bk.Item.def{_}, _}:
      Unit{}
    case Con{Bk.Item.defs{_}, _}:
      Unit{}

def typ.ge(s0: List<&2, Bk.Item>) -> Ge(Bk.Book.read.typ(s0), Gs(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{Bk.Item.quan{_}, _}:
      Unit{}
    case Con{Bk.Item.nat{_}, _}:
      Unit{}
    case Con{Bk.Item.name{_}, _}:
      Unit{}
    case Con{Bk.Item.names{_}, _}:
      Unit{}
    case Con{Bk.Item.bool{_}, _}:
      Unit{}
    case Con{Bk.Item.term{+x1}, +rest}:
      le_refl(Gs(Con{Bk.Item.term{Bk.Term.Typ{x1}}, rest}, 0n))
    case Con{Bk.Item.def{_}, _}:
      Unit{}
    case Con{Bk.Item.defs{_}, _}:
      Unit{}

def min.ge(s0: List<&2, Bk.Item>) -> Ge(Bk.Book.read.min(s0), Gs(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{Bk.Item.quan{_}, _}:
      Unit{}
    case Con{Bk.Item.nat{_}, _}:
      Unit{}
    case Con{Bk.Item.name{_}, _}:
      Unit{}
    case Con{Bk.Item.names{_}, _}:
      Unit{}
    case Con{Bk.Item.bool{_}, _}:
      Unit{}
    case Con{Bk.Item.term{+x1}, +s1}:
      match s1:
        case Nil{}:
          Unit{}
        case Con{Bk.Item.quan{_}, _}:
          Unit{}
        case Con{Bk.Item.nat{_}, _}:
          Unit{}
        case Con{Bk.Item.name{_}, _}:
          Unit{}
        case Con{Bk.Item.names{_}, _}:
          Unit{}
        case Con{Bk.Item.bool{_}, _}:
          Unit{}
        case Con{Bk.Item.term{+x2}, +rest}:
          le_refl(Gs(Con{Bk.Item.term{Bk.Term.Min{x2, x1}}, rest}, 0n))
        case Con{Bk.Item.def{_}, _}:
          Unit{}
        case Con{Bk.Item.defs{_}, _}:
          Unit{}
    case Con{Bk.Item.def{_}, _}:
      Unit{}
    case Con{Bk.Item.defs{_}, _}:
      Unit{}

def all.ge(s0: List<&2, Bk.Item>) -> Ge(Bk.Book.read.all(s0), Gs(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{Bk.Item.quan{_}, _}:
      Unit{}
    case Con{Bk.Item.nat{_}, _}:
      Unit{}
    case Con{Bk.Item.name{_}, _}:
      Unit{}
    case Con{Bk.Item.names{_}, _}:
      Unit{}
    case Con{Bk.Item.bool{_}, _}:
      Unit{}
    case Con{Bk.Item.term{+x1}, +s1}:
      match s1:
        case Nil{}:
          Unit{}
        case Con{Bk.Item.quan{_}, _}:
          Unit{}
        case Con{Bk.Item.nat{_}, _}:
          Unit{}
        case Con{Bk.Item.name{_}, _}:
          Unit{}
        case Con{Bk.Item.names{_}, _}:
          Unit{}
        case Con{Bk.Item.bool{_}, _}:
          Unit{}
        case Con{Bk.Item.term{+x2}, +s2}:
          match s2:
            case Nil{}:
              Unit{}
            case Con{Bk.Item.quan{+x3}, +rest}:
              le_refl(Gs(Con{Bk.Item.term{Bk.Term.All{x3, x2, x1}}, rest}, 0n))
            case Con{Bk.Item.nat{_}, _}:
              Unit{}
            case Con{Bk.Item.name{_}, _}:
              Unit{}
            case Con{Bk.Item.names{_}, _}:
              Unit{}
            case Con{Bk.Item.bool{_}, _}:
              Unit{}
            case Con{Bk.Item.term{_}, _}:
              Unit{}
            case Con{Bk.Item.def{_}, _}:
              Unit{}
            case Con{Bk.Item.defs{_}, _}:
              Unit{}
        case Con{Bk.Item.def{_}, _}:
          Unit{}
        case Con{Bk.Item.defs{_}, _}:
          Unit{}
    case Con{Bk.Item.def{_}, _}:
      Unit{}
    case Con{Bk.Item.defs{_}, _}:
      Unit{}

def lam.ge(s0: List<&2, Bk.Item>) -> Ge(Bk.Book.read.lam(s0), Gs(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{Bk.Item.quan{_}, _}:
      Unit{}
    case Con{Bk.Item.nat{_}, _}:
      Unit{}
    case Con{Bk.Item.name{_}, _}:
      Unit{}
    case Con{Bk.Item.names{_}, _}:
      Unit{}
    case Con{Bk.Item.bool{_}, _}:
      Unit{}
    case Con{Bk.Item.term{+x1}, +s1}:
      match s1:
        case Nil{}:
          Unit{}
        case Con{Bk.Item.quan{+x2}, +rest}:
          le_refl(Gs(Con{Bk.Item.term{Bk.Term.Lam{x2, x1}}, rest}, 0n))
        case Con{Bk.Item.nat{_}, _}:
          Unit{}
        case Con{Bk.Item.name{_}, _}:
          Unit{}
        case Con{Bk.Item.names{_}, _}:
          Unit{}
        case Con{Bk.Item.bool{_}, _}:
          Unit{}
        case Con{Bk.Item.term{_}, _}:
          Unit{}
        case Con{Bk.Item.def{_}, _}:
          Unit{}
        case Con{Bk.Item.defs{_}, _}:
          Unit{}
    case Con{Bk.Item.def{_}, _}:
      Unit{}
    case Con{Bk.Item.defs{_}, _}:
      Unit{}

def app.ge(s0: List<&2, Bk.Item>) -> Ge(Bk.Book.read.app(s0), Gs(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{Bk.Item.quan{_}, _}:
      Unit{}
    case Con{Bk.Item.nat{_}, _}:
      Unit{}
    case Con{Bk.Item.name{_}, _}:
      Unit{}
    case Con{Bk.Item.names{_}, _}:
      Unit{}
    case Con{Bk.Item.bool{_}, _}:
      Unit{}
    case Con{Bk.Item.term{+x1}, +s1}:
      match s1:
        case Nil{}:
          Unit{}
        case Con{Bk.Item.quan{_}, _}:
          Unit{}
        case Con{Bk.Item.nat{_}, _}:
          Unit{}
        case Con{Bk.Item.name{_}, _}:
          Unit{}
        case Con{Bk.Item.names{_}, _}:
          Unit{}
        case Con{Bk.Item.bool{_}, _}:
          Unit{}
        case Con{Bk.Item.term{+x2}, +s2}:
          match s2:
            case Nil{}:
              Unit{}
            case Con{Bk.Item.quan{+x3}, +rest}:
              le_refl(Gs(Con{Bk.Item.term{Bk.Term.App{x3, x2, x1}}, rest}, 0n))
            case Con{Bk.Item.nat{_}, _}:
              Unit{}
            case Con{Bk.Item.name{_}, _}:
              Unit{}
            case Con{Bk.Item.names{_}, _}:
              Unit{}
            case Con{Bk.Item.bool{_}, _}:
              Unit{}
            case Con{Bk.Item.term{_}, _}:
              Unit{}
            case Con{Bk.Item.def{_}, _}:
              Unit{}
            case Con{Bk.Item.defs{_}, _}:
              Unit{}
        case Con{Bk.Item.def{_}, _}:
          Unit{}
        case Con{Bk.Item.defs{_}, _}:
          Unit{}
    case Con{Bk.Item.def{_}, _}:
      Unit{}
    case Con{Bk.Item.defs{_}, _}:
      Unit{}

def sig.ge(s0: List<&2, Bk.Item>) -> Ge(Bk.Book.read.sig(s0), Gs(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{Bk.Item.quan{_}, _}:
      Unit{}
    case Con{Bk.Item.nat{_}, _}:
      Unit{}
    case Con{Bk.Item.name{_}, _}:
      Unit{}
    case Con{Bk.Item.names{_}, _}:
      Unit{}
    case Con{Bk.Item.bool{_}, _}:
      Unit{}
    case Con{Bk.Item.term{+x1}, +s1}:
      match s1:
        case Nil{}:
          Unit{}
        case Con{Bk.Item.quan{_}, _}:
          Unit{}
        case Con{Bk.Item.nat{_}, _}:
          Unit{}
        case Con{Bk.Item.name{_}, _}:
          Unit{}
        case Con{Bk.Item.names{_}, _}:
          Unit{}
        case Con{Bk.Item.bool{_}, _}:
          Unit{}
        case Con{Bk.Item.term{+x2}, +s2}:
          match s2:
            case Nil{}:
              Unit{}
            case Con{Bk.Item.quan{+x3}, +rest}:
              le_refl(Gs(Con{Bk.Item.term{Bk.Term.Sig{x3, x2, x1}}, rest}, 0n))
            case Con{Bk.Item.nat{_}, _}:
              Unit{}
            case Con{Bk.Item.name{_}, _}:
              Unit{}
            case Con{Bk.Item.names{_}, _}:
              Unit{}
            case Con{Bk.Item.bool{_}, _}:
              Unit{}
            case Con{Bk.Item.term{_}, _}:
              Unit{}
            case Con{Bk.Item.def{_}, _}:
              Unit{}
            case Con{Bk.Item.defs{_}, _}:
              Unit{}
        case Con{Bk.Item.def{_}, _}:
          Unit{}
        case Con{Bk.Item.defs{_}, _}:
          Unit{}
    case Con{Bk.Item.def{_}, _}:
      Unit{}
    case Con{Bk.Item.defs{_}, _}:
      Unit{}

def tup.ge(s0: List<&2, Bk.Item>) -> Ge(Bk.Book.read.tup(s0), Gs(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{Bk.Item.quan{_}, _}:
      Unit{}
    case Con{Bk.Item.nat{_}, _}:
      Unit{}
    case Con{Bk.Item.name{_}, _}:
      Unit{}
    case Con{Bk.Item.names{_}, _}:
      Unit{}
    case Con{Bk.Item.bool{_}, _}:
      Unit{}
    case Con{Bk.Item.term{+x1}, +s1}:
      match s1:
        case Nil{}:
          Unit{}
        case Con{Bk.Item.quan{_}, _}:
          Unit{}
        case Con{Bk.Item.nat{_}, _}:
          Unit{}
        case Con{Bk.Item.name{_}, _}:
          Unit{}
        case Con{Bk.Item.names{_}, _}:
          Unit{}
        case Con{Bk.Item.bool{_}, _}:
          Unit{}
        case Con{Bk.Item.term{+x2}, +s2}:
          match s2:
            case Nil{}:
              Unit{}
            case Con{Bk.Item.quan{+x3}, +rest}:
              le_refl(Gs(Con{Bk.Item.term{Bk.Term.Tup{x3, x2, x1}}, rest}, 0n))
            case Con{Bk.Item.nat{_}, _}:
              Unit{}
            case Con{Bk.Item.name{_}, _}:
              Unit{}
            case Con{Bk.Item.names{_}, _}:
              Unit{}
            case Con{Bk.Item.bool{_}, _}:
              Unit{}
            case Con{Bk.Item.term{_}, _}:
              Unit{}
            case Con{Bk.Item.def{_}, _}:
              Unit{}
            case Con{Bk.Item.defs{_}, _}:
              Unit{}
        case Con{Bk.Item.def{_}, _}:
          Unit{}
        case Con{Bk.Item.defs{_}, _}:
          Unit{}
    case Con{Bk.Item.def{_}, _}:
      Unit{}
    case Con{Bk.Item.defs{_}, _}:
      Unit{}

def prj.ge(s0: List<&2, Bk.Item>) -> Ge(Bk.Book.read.prj(s0), Gs(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{Bk.Item.quan{_}, _}:
      Unit{}
    case Con{Bk.Item.nat{_}, _}:
      Unit{}
    case Con{Bk.Item.name{_}, _}:
      Unit{}
    case Con{Bk.Item.names{_}, _}:
      Unit{}
    case Con{Bk.Item.bool{_}, _}:
      Unit{}
    case Con{Bk.Item.term{+x1}, +rest}:
      le_refl(Gs(Con{Bk.Item.term{Bk.Term.Prj{x1}}, rest}, 0n))
    case Con{Bk.Item.def{_}, _}:
      Unit{}
    case Con{Bk.Item.defs{_}, _}:
      Unit{}

def enu.ge(s0: List<&2, Bk.Item>) -> Ge(Bk.Book.read.enu(s0), Gs(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{Bk.Item.quan{_}, _}:
      Unit{}
    case Con{Bk.Item.nat{_}, _}:
      Unit{}
    case Con{Bk.Item.name{_}, _}:
      Unit{}
    case Con{Bk.Item.names{+x1}, +rest}:
      le_refl(Gs(Con{Bk.Item.term{Bk.Term.Enu{x1}}, rest}, 0n))
    case Con{Bk.Item.bool{_}, _}:
      Unit{}
    case Con{Bk.Item.term{_}, _}:
      Unit{}
    case Con{Bk.Item.def{_}, _}:
      Unit{}
    case Con{Bk.Item.defs{_}, _}:
      Unit{}

def lab.ge(s0: List<&2, Bk.Item>) -> Ge(Bk.Book.read.lab(s0), Gs(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{Bk.Item.quan{_}, _}:
      Unit{}
    case Con{Bk.Item.nat{_}, _}:
      Unit{}
    case Con{Bk.Item.name{+x1}, +rest}:
      le_refl(Gs(Con{Bk.Item.term{Bk.Term.Lab{x1}}, rest}, 0n))
    case Con{Bk.Item.names{_}, _}:
      Unit{}
    case Con{Bk.Item.bool{_}, _}:
      Unit{}
    case Con{Bk.Item.term{_}, _}:
      Unit{}
    case Con{Bk.Item.def{_}, _}:
      Unit{}
    case Con{Bk.Item.defs{_}, _}:
      Unit{}

def mat.ge(s0: List<&2, Bk.Item>) -> Ge(Bk.Book.read.mat(s0), Gs(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{Bk.Item.quan{_}, _}:
      Unit{}
    case Con{Bk.Item.nat{_}, _}:
      Unit{}
    case Con{Bk.Item.name{_}, _}:
      Unit{}
    case Con{Bk.Item.names{_}, _}:
      Unit{}
    case Con{Bk.Item.bool{_}, _}:
      Unit{}
    case Con{Bk.Item.term{+x1}, +s1}:
      match s1:
        case Nil{}:
          Unit{}
        case Con{Bk.Item.quan{_}, _}:
          Unit{}
        case Con{Bk.Item.nat{_}, _}:
          Unit{}
        case Con{Bk.Item.name{_}, _}:
          Unit{}
        case Con{Bk.Item.names{_}, _}:
          Unit{}
        case Con{Bk.Item.bool{_}, _}:
          Unit{}
        case Con{Bk.Item.term{+x2}, +s2}:
          match s2:
            case Nil{}:
              Unit{}
            case Con{Bk.Item.quan{_}, _}:
              Unit{}
            case Con{Bk.Item.nat{_}, _}:
              Unit{}
            case Con{Bk.Item.name{+x3}, +rest}:
              le_refl(Gs(Con{Bk.Item.term{Bk.Term.Mat{x3, x2, x1}}, rest}, 0n))
            case Con{Bk.Item.names{_}, _}:
              Unit{}
            case Con{Bk.Item.bool{_}, _}:
              Unit{}
            case Con{Bk.Item.term{_}, _}:
              Unit{}
            case Con{Bk.Item.def{_}, _}:
              Unit{}
            case Con{Bk.Item.defs{_}, _}:
              Unit{}
        case Con{Bk.Item.def{_}, _}:
          Unit{}
        case Con{Bk.Item.defs{_}, _}:
          Unit{}
    case Con{Bk.Item.def{_}, _}:
      Unit{}
    case Con{Bk.Item.defs{_}, _}:
      Unit{}

def eql.ge(s0: List<&2, Bk.Item>) -> Ge(Bk.Book.read.eql(s0), Gs(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{Bk.Item.quan{_}, _}:
      Unit{}
    case Con{Bk.Item.nat{_}, _}:
      Unit{}
    case Con{Bk.Item.name{_}, _}:
      Unit{}
    case Con{Bk.Item.names{_}, _}:
      Unit{}
    case Con{Bk.Item.bool{_}, _}:
      Unit{}
    case Con{Bk.Item.term{+x1}, +s1}:
      match s1:
        case Nil{}:
          Unit{}
        case Con{Bk.Item.quan{_}, _}:
          Unit{}
        case Con{Bk.Item.nat{_}, _}:
          Unit{}
        case Con{Bk.Item.name{_}, _}:
          Unit{}
        case Con{Bk.Item.names{_}, _}:
          Unit{}
        case Con{Bk.Item.bool{_}, _}:
          Unit{}
        case Con{Bk.Item.term{+x2}, +s2}:
          match s2:
            case Nil{}:
              Unit{}
            case Con{Bk.Item.quan{_}, _}:
              Unit{}
            case Con{Bk.Item.nat{_}, _}:
              Unit{}
            case Con{Bk.Item.name{_}, _}:
              Unit{}
            case Con{Bk.Item.names{_}, _}:
              Unit{}
            case Con{Bk.Item.bool{_}, _}:
              Unit{}
            case Con{Bk.Item.term{+x3}, +rest}:
              le_refl(Gs(Con{Bk.Item.term{Bk.Term.Eql{x3, x2, x1}}, rest}, 0n))
            case Con{Bk.Item.def{_}, _}:
              Unit{}
            case Con{Bk.Item.defs{_}, _}:
              Unit{}
        case Con{Bk.Item.def{_}, _}:
          Unit{}
        case Con{Bk.Item.defs{_}, _}:
          Unit{}
    case Con{Bk.Item.def{_}, _}:
      Unit{}
    case Con{Bk.Item.defs{_}, _}:
      Unit{}

def rwt.ge(s0: List<&2, Bk.Item>) -> Ge(Bk.Book.read.rwt(s0), Gs(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{Bk.Item.quan{_}, _}:
      Unit{}
    case Con{Bk.Item.nat{_}, _}:
      Unit{}
    case Con{Bk.Item.name{_}, _}:
      Unit{}
    case Con{Bk.Item.names{_}, _}:
      Unit{}
    case Con{Bk.Item.bool{_}, _}:
      Unit{}
    case Con{Bk.Item.term{+x1}, +s1}:
      match s1:
        case Nil{}:
          Unit{}
        case Con{Bk.Item.quan{_}, _}:
          Unit{}
        case Con{Bk.Item.nat{_}, _}:
          Unit{}
        case Con{Bk.Item.name{_}, _}:
          Unit{}
        case Con{Bk.Item.names{_}, _}:
          Unit{}
        case Con{Bk.Item.bool{_}, _}:
          Unit{}
        case Con{Bk.Item.term{+x2}, +s2}:
          match s2:
            case Nil{}:
              Unit{}
            case Con{Bk.Item.quan{_}, _}:
              Unit{}
            case Con{Bk.Item.nat{_}, _}:
              Unit{}
            case Con{Bk.Item.name{_}, _}:
              Unit{}
            case Con{Bk.Item.names{_}, _}:
              Unit{}
            case Con{Bk.Item.bool{_}, _}:
              Unit{}
            case Con{Bk.Item.term{+x3}, +rest}:
              le_refl(Gs(Con{Bk.Item.term{Bk.Term.Rwt{x3, x2, x1}}, rest}, 0n))
            case Con{Bk.Item.def{_}, _}:
              Unit{}
            case Con{Bk.Item.defs{_}, _}:
              Unit{}
        case Con{Bk.Item.def{_}, _}:
          Unit{}
        case Con{Bk.Item.defs{_}, _}:
          Unit{}
    case Con{Bk.Item.def{_}, _}:
      Unit{}
    case Con{Bk.Item.defs{_}, _}:
      Unit{}

def token32.ge(n: Nat, +st: List<&2, Bk.Item>) -> Ge(Bk.Book.read.token32(n, st), Gs(st, 0n)):
  match n:
    case 0n:
      rwt.ge(st)
    case 1n+_:
      Unit{}

def token24.ge(n: Nat, +st: List<&2, Bk.Item>) -> Ge(Bk.Book.read.token24(n, st), Gs(st, 0n)):
  match n:
    case 0n:
      tup.ge(st)
    case 1n:
      prj.ge(st)
    case 2n:
      enu.ge(st)
    case 3n:
      lab.ge(st)
    case 4n:
      mat.ge(st)
    case 5n:
      le_refl(2n+Gs(st, 0n))
    case 6n:
      eql.ge(st)
    case 7n:
      le_refl(2n+Gs(st, 0n))
    case 8n+p:
      token32.ge(p, st)

def token16.ge(n: Nat, +st: List<&2, Bk.Item>) -> Ge(Bk.Book.read.token16(n, st), Gs(st, 0n)):
  match n:
    case 0n:
      ann.ge(st)
    case 1n:
      let.ge(st)
    case 2n:
      typ.ge(st)
    case 3n:
      min.ge(st)
    case 4n:
      all.ge(st)
    case 5n:
      lam.ge(st)
    case 6n:
      app.ge(st)
    case 7n:
      sig.ge(st)
    case 8n+p:
      token24.ge(p, st)

def token8.ge(n: Nat, +st: List<&2, Bk.Item>) -> Ge(Bk.Book.read.token8(n, st), Gs(st, 0n)):
  match n:
    case 0n:
      names.ge(st)
    case 1n:
      le_refl(2n+Gs(st, 0n))
    case 2n:
      le_refl(2n+Gs(st, 0n))
    case 3n:
      le_refl(2n+Gs(st, 0n))
    case 4n:
      defs.ge(st)
    case 5n:
      def.ge(st)
    case 6n:
      var.ge(st)
    case 7n:
      ref.ge(st)
    case 8n+p:
      token16.ge(p, st)

def token.ge(n: Nat, +st: List<&2, Bk.Item>, b: Word(8n)) -> Ge(Bk.Book.read.token(n, st, b), Gs(st, 0n)):
  match n:
    case 0n:
      le_refl(2n+Gs(st, 0n))
    case 1n:
      le_refl(2n+Gs(st, 0n))
    case 2n:
      le_refl(2n+Gs(st, 0n))
    case 3n:
      le_refl(2n+Gs(st, 0n))
    case 4n:
      succ.ge(st)
    case 5n:
      le_refl(2n+Gs(st, 0n))
    case 6n:
      byte.ge(st, b)
    case 7n:
      le_refl(2n+Gs(st, 0n))
    case 8n+p:
      token8.ge(p, st)

# Reading a book
# --------------

# None is not Some
def IsNone(m: Maybe<List<&2, Bk.Def>>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{_}:
      Empty

def none_ne_some(-ds: List<&2, Bk.Def>, e: {None{} == Some{ds} : Maybe<List<&2, Bk.Def>>}) -> Empty:
  %e : IsNone(_)
  Unit{}

# a reader that failed reads no book
def go.none(xs: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, e: {Bk.Book.read.go(xs, None{}) == Some{ds} : Maybe<List<&2, Bk.Def>>}) -> Empty:
  match xs:
    case Nil{}:
      none_ne_some(ds, e)
    case Con{_, Nil{}}:
      none_ne_some(ds, e)
    case Con{_, Con{_, +rest}}:
      go.none(rest, ds, e)

# G of a read book
def Vd(m: Maybe<List<&2, Bk.Def>>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{ds}:
      Gd(ds, 0n)

# the end of the reading: the book's G is the stack's
def done.ge(st: Maybe<List<&2, Bk.Item>>, +ds: List<&2, Bk.Def>, e: {Bk.Book.read.done(st) == Some{ds} : Maybe<List<&2, Bk.Def>>}) ->
  Le(Gm(st), Gd(ds, 0n)):
  match st:
    case None{}:
      Empty.absurd(Le(Gm(st), Gd(ds, 0n)), none_ne_some(ds, e))
    case Some{s}:
      match s:
        case Nil{}:
          Empty.absurd(Le(Gm(st), Gd(ds, 0n)), none_ne_some(ds, e))
        case Con{Bk.Item.quan{_}, _}:
          Empty.absurd(Le(Gm(st), Gd(ds, 0n)), none_ne_some(ds, e))
        case Con{Bk.Item.nat{_}, _}:
          Empty.absurd(Le(Gm(st), Gd(ds, 0n)), none_ne_some(ds, e))
        case Con{Bk.Item.name{_}, _}:
          Empty.absurd(Le(Gm(st), Gd(ds, 0n)), none_ne_some(ds, e))
        case Con{Bk.Item.names{_}, _}:
          Empty.absurd(Le(Gm(st), Gd(ds, 0n)), none_ne_some(ds, e))
        case Con{Bk.Item.bool{_}, _}:
          Empty.absurd(Le(Gm(st), Gd(ds, 0n)), none_ne_some(ds, e))
        case Con{Bk.Item.term{_}, _}:
          Empty.absurd(Le(Gm(st), Gd(ds, 0n)), none_ne_some(ds, e))
        case Con{Bk.Item.def{_}, _}:
          Empty.absurd(Le(Gm(st), Gd(ds, 0n)), none_ne_some(ds, e))
        case Con{Bk.Item.defs{+ds0}, t}:
          match t:
            case Nil{}:
              %e : Le(Gd(ds0, 0n), Vd(_))
              le_refl(Gd(ds0, 0n))
            case Con{_, _}:
              Empty.absurd(Le(Gm(st), Gd(ds, 0n)), none_ne_some(ds, e))

# one token of the reading: 2 bytes, and 2 more G
def next.ge(r: Maybe<List<&2, Bk.Item>>, +rest: List<&2, Word(8n)>, +w: Nat, +ds: List<&2, Bk.Def>,
  g: Ge(r, w),
  ih: Le(Nat.add(List.length(&2, Word(8n), rest), Gm(r)), Gd(ds, 0n)),
  e: {Bk.Book.read.go(rest, r) == Some{ds} : Maybe<List<&2, Bk.Def>>}
) -> Le(2n+Nat.add(List.length(&2, Word(8n), rest), w), Gd(ds, 0n)):
  match r:
    case None{}:
      Empty.absurd(Le(2n+Nat.add(List.length(&2, Word(8n), rest), w), Gd(ds, 0n)), go.none(rest, ds, e))
    case Some{+s}:
      +l = List.length(&2, Word(8n), rest)
      +h = le_trans(Nat.add(l, 2n+w), Nat.add(l, Gs(s, 0n)), Gd(ds, 0n), add_mono(l, l, 2n+w, Gs(s, 0n), le_refl(l), g), ih)
      le_rw_l(Nat.add(l, 2n+w), 2n+Nat.add(l, w), Gd(ds, 0n), Equal.sym(Nat, 2n+Nat.add(l, w), Nat.add(l, 2n+w), add_two(l, w)), h)

# the reading: the bytes left plus the stack's G are at most the book's G
def go.ge(xs: List<&2, Word(8n)>, st: Maybe<List<&2, Bk.Item>>, +ds: List<&2, Bk.Def>,
  +e: {Bk.Book.read.go(xs, st) == Some{ds} : Maybe<List<&2, Bk.Def>>}
) -> Le(Nat.add(List.length(&2, Word(8n), xs), Gm(st)), Gd(ds, 0n)):
  match xs:
    case Nil{}:
      done.ge(st, ds, e)
    case Con{_, Nil{}}:
      Empty.absurd(Le(Nat.add(1n, Gm(st)), Gd(ds, 0n)), none_ne_some(ds, e))
    case Con{+tag, Con{+b, +rest}}:
      match st:
        case None{}:
          Empty.absurd(Le(Nat.add(2n+List.length(&2, Word(8n), rest), Gm(st)), Gd(ds, 0n)), go.none(rest, ds, e))
        case Some{+s}:
          next.ge(Bk.Book.read.token(Word.to_nat(8n, tag), s, b), rest, Gs(s, 0n), ds, token.ge(Word.to_nat(8n, tag), s, b),
            go.ge(rest, Bk.Book.read.token(Word.to_nat(8n, tag), s, b), ds, e), e)

# a book read from p has a G of at least |p|
def read.ge(+p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>}) ->
  Le(List.length(&2, Word(8n), p), Gd(ds, 0n)):
  +l = List.length(&2, Word(8n), p)
  le_rw_l(Nat.add(l, 0n), l, Gd(ds, 0n), add_zero(l), go.ge(p, Some{Nil{}}, ds, rd))

# G is at most the nodes
# ----------------------

def gn.dbl(i: Nat, +a: Nat) -> Le(Gn(i, a), 2n+Nat.add(Nat.double(i), a)):
  match i:
    case 0n:
      le_refl(2n+a)
    case 1n+q:
      gn.dbl(q, a)

def gn.le(+i: Nat, +a: Nat) -> Le(Gn(i, a), Nat.add(Pg.Form.size.nat(i), a)):
  le_trans(Gn(i, a), 2n+Nat.add(Nat.double(i), a), Nat.add(Pg.Form.size.nat(i), a), gn.dbl(i, a),
    le_succ(Nat.add(Nat.double(i), a), Nat.add(Nat.mul(4n, i), a),
      add_mono(Nat.double(i), Nat.mul(4n, i), a, a, dbl_mul(2n, i), le_refl(a))))

def gk.dbl(k: List<&2, Word(8n)>, +a: Nat) -> Le(Gk(k, a), 2n+Nat.add(Nat.double(List.length(&2, Word(8n), k)), a)):
  match k:
    case Nil{}:
      le_refl(2n+a)
    case Con{_, +rest}:
      gk.dbl(rest, a)

def gk.le(+k: List<&2, Word(8n)>, +a: Nat) -> Le(Gk(k, a), Nat.add(Pg.Form.size.name(k), a)):
  +l = List.length(&2, Word(8n), k)
  le_trans(Gk(k, a), 2n+Nat.add(Nat.double(l), a), Nat.add(Pg.Form.size.name(k), a), gk.dbl(k, a),
    le_succ(Nat.add(Nat.double(l), a), Nat.add(Nat.mul(72n, l), a),
      add_mono(Nat.double(l), Nat.mul(72n, l), a, a, dbl_mul(70n, l), le_refl(a))))

def gks.le(ks: List<&2, List<&2, Word(8n)>>, +a: Nat) -> Le(Gks(ks, a), Nat.add(Pg.Form.size.names(ks), a)):
  match ks:
    case Nil{}:
      le_succ(a, a, le_refl(a))
    case Con{+k, +rest}:
      le_plus(3n, Gk(k, Gks(rest, a)), Nat.add(Nat.add(Pg.Form.size.name(k), Pg.Form.size.names(rest)), a),
        chain2(Gk(k, Gks(rest, a)), Gks(rest, a), Pg.Form.size.name(k), Pg.Form.size.names(rest), a, gk.le(k, Gks(rest, a)), gks.le(rest, a)))

def gt.le(t: Bk.Term, +a: Nat) -> Le(Gt(t, a), Nat.add(Pg.Form.size.term(t), a)):
  match t:
    case Bk.Term.Var{+x1}:
      le_plus(2n, Gn(x1, a), Nat.add(Pg.Form.size.nat(x1), a), gn.le(x1, a))
    case Bk.Term.Ref{+x1}:
      le_plus(2n, Gk(x1, a), Nat.add(Pg.Form.size.name(x1), a), gk.le(x1, a))
    case Bk.Term.Ann{+x1, +x2}:
      le_plus(3n, Gt(x2, Gt(x1, a)), Nat.add(Nat.add(Pg.Form.size.term(x1), Pg.Form.size.term(x2)), a),
        chainr(Gt(x2, Gt(x1, a)), Gt(x1, a), Pg.Form.size.term(x2), Pg.Form.size.term(x1), a, gt.le(x2, Gt(x1, a)), gt.le(x1, a)))
    case Bk.Term.Let{_, +x1, +x2}:
      le_plus(5n, Gt(x2, Gt(x1, 2n+a)), 2n+Nat.add(Nat.add(Pg.Form.size.term(x1), Pg.Form.size.term(x2)), a),
        chainq(Gt(x2, Gt(x1, 2n+a)), Gt(x1, 2n+a), Pg.Form.size.term(x2), Pg.Form.size.term(x1), a, gt.le(x2, Gt(x1, 2n+a)), gt.le(x1, 2n+a)))
    case Bk.Term.Typ{+x1}:
      le_plus(2n, Gt(x1, a), Nat.add(Pg.Form.size.term(x1), a), gt.le(x1, a))
    case Bk.Term.Min{+x1, +x2}:
      le_plus(3n, Gt(x2, Gt(x1, a)), Nat.add(Nat.add(Pg.Form.size.term(x1), Pg.Form.size.term(x2)), a),
        chainr(Gt(x2, Gt(x1, a)), Gt(x1, a), Pg.Form.size.term(x2), Pg.Form.size.term(x1), a, gt.le(x2, Gt(x1, a)), gt.le(x1, a)))
    case Bk.Term.All{_, +x1, +x2}:
      le_plus(5n, Gt(x2, Gt(x1, 2n+a)), 2n+Nat.add(Nat.add(Pg.Form.size.term(x1), Pg.Form.size.term(x2)), a),
        chainq(Gt(x2, Gt(x1, 2n+a)), Gt(x1, 2n+a), Pg.Form.size.term(x2), Pg.Form.size.term(x1), a, gt.le(x2, Gt(x1, 2n+a)), gt.le(x1, 2n+a)))
    case Bk.Term.Lam{_, +x1}:
      le_plus(4n, Gt(x1, 2n+a), 2n+Nat.add(Pg.Form.size.term(x1), a),
        le_rw_r(Gt(x1, 2n+a), Nat.add(Pg.Form.size.term(x1), 2n+a), 2n+Nat.add(Pg.Form.size.term(x1), a),
          Equal.sym(Nat, 2n+Nat.add(Pg.Form.size.term(x1), a), Nat.add(Pg.Form.size.term(x1), 2n+a), add_two(Pg.Form.size.term(x1), a)),
          gt.le(x1, 2n+a)))
    case Bk.Term.App{_, +x1, +x2}:
      le_plus(5n, Gt(x2, Gt(x1, 2n+a)), 2n+Nat.add(Nat.add(Pg.Form.size.term(x1), Pg.Form.size.term(x2)), a),
        chainq(Gt(x2, Gt(x1, 2n+a)), Gt(x1, 2n+a), Pg.Form.size.term(x2), Pg.Form.size.term(x1), a, gt.le(x2, Gt(x1, 2n+a)), gt.le(x1, 2n+a)))
    case Bk.Term.Sig{_, +x1, +x2}:
      le_plus(5n, Gt(x2, Gt(x1, 2n+a)), 2n+Nat.add(Nat.add(Pg.Form.size.term(x1), Pg.Form.size.term(x2)), a),
        chainq(Gt(x2, Gt(x1, 2n+a)), Gt(x1, 2n+a), Pg.Form.size.term(x2), Pg.Form.size.term(x1), a, gt.le(x2, Gt(x1, 2n+a)), gt.le(x1, 2n+a)))
    case Bk.Term.Tup{_, +x1, +x2}:
      le_plus(5n, Gt(x2, Gt(x1, 2n+a)), 2n+Nat.add(Nat.add(Pg.Form.size.term(x1), Pg.Form.size.term(x2)), a),
        chainq(Gt(x2, Gt(x1, 2n+a)), Gt(x1, 2n+a), Pg.Form.size.term(x2), Pg.Form.size.term(x1), a, gt.le(x2, Gt(x1, 2n+a)), gt.le(x1, 2n+a)))
    case Bk.Term.Prj{+x1}:
      le_plus(2n, Gt(x1, a), Nat.add(Pg.Form.size.term(x1), a), gt.le(x1, a))
    case Bk.Term.Enu{+x1}:
      le_plus(2n, Gks(x1, a), Nat.add(Pg.Form.size.names(x1), a), gks.le(x1, a))
    case Bk.Term.Lab{+x1}:
      le_plus(2n, Gk(x1, a), Nat.add(Pg.Form.size.name(x1), a), gk.le(x1, a))
    case Bk.Term.Mat{+x1, +x2, +x3}:
      le_plus(4n, Gt(x3, Gt(x2, Gk(x1, a))), Nat.add(Nat.add(Pg.Form.size.name(x1), Nat.add(Pg.Form.size.term(x2), Pg.Form.size.term(x3))), a),
        chain3(Gt(x3, Gt(x2, Gk(x1, a))), Gt(x2, Gk(x1, a)), Gk(x1, a), Pg.Form.size.name(x1), Pg.Form.size.term(x2), Pg.Form.size.term(x3), a,
          gt.le(x3, Gt(x2, Gk(x1, a))), gt.le(x2, Gk(x1, a)), gk.le(x1, a)))
    case Bk.Term.Efq{}:
      le_succ(a, a, le_refl(a))
    case Bk.Term.Eql{+x1, +x2, +x3}:
      le_plus(4n, Gt(x3, Gt(x2, Gt(x1, a))), Nat.add(Nat.add(Pg.Form.size.term(x1), Nat.add(Pg.Form.size.term(x2), Pg.Form.size.term(x3))), a),
        chain3(Gt(x3, Gt(x2, Gt(x1, a))), Gt(x2, Gt(x1, a)), Gt(x1, a), Pg.Form.size.term(x1), Pg.Form.size.term(x2), Pg.Form.size.term(x3), a,
          gt.le(x3, Gt(x2, Gt(x1, a))), gt.le(x2, Gt(x1, a)), gt.le(x1, a)))
    case Bk.Term.Rfl{}:
      le_succ(a, a, le_refl(a))
    case Bk.Term.Rwt{+x1, +x2, +x3}:
      le_plus(4n, Gt(x3, Gt(x2, Gt(x1, a))), Nat.add(Nat.add(Pg.Form.size.term(x1), Nat.add(Pg.Form.size.term(x2), Pg.Form.size.term(x3))), a),
        chain3(Gt(x3, Gt(x2, Gt(x1, a))), Gt(x2, Gt(x1, a)), Gt(x1, a), Pg.Form.size.term(x1), Pg.Form.size.term(x2), Pg.Form.size.term(x3), a,
          gt.le(x3, Gt(x2, Gt(x1, a))), gt.le(x2, Gt(x1, a)), gt.le(x1, a)))

def gd.le(ds: List<&2, Bk.Def>, +a: Nat) -> Le(Gd(ds, a), Nat.add(Pg.Form.size.defs(ds), a)):
  match ds:
    case Nil{}:
      le_succ(a, a, le_refl(a))
    case Con{Bk.Def{+k, +ty, +v, _}, +rest}:
      +r = Gd(rest, a)
      +u = Gt(v, Gt(ty, Gk(k, r)))
      +d3 = Nat.add(Pg.Form.size.name(k), Nat.add(Pg.Form.size.term(ty), Pg.Form.size.term(v)))
      +h = chain3(u, Gt(ty, Gk(k, r)), Gk(k, r), Pg.Form.size.name(k), Pg.Form.size.term(ty), Pg.Form.size.term(v), r,
        gt.le(v, Gt(ty, Gk(k, r))), gt.le(ty, Gk(k, r)), gk.le(k, r))
      le_plus(9n, u, Nat.add(Nat.add(d3, Pg.Form.size.defs(rest)), a), chain2(u, r, d3, Pg.Form.size.defs(rest), a, h, gd.le(rest, a)))

# the program's size of a book that Book.read reads
def size.eq(+p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>}) ->
  {Pg.Form.size.defs(ds) == Pg.Program.size(p) : Nat}:
  %Equal.sym(Maybe<List<&2, Bk.Def>>, Bk.Book.read(p), Some{ds}, rd) : {Pg.Form.size.defs(ds) == Pg.Program.size.of(_) : Nat}
  {==}

# the bytes of a book are at most its program's size
def size.ge(+p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>}) ->
  Le(List.length(&2, Word(8n), p), Pg.Program.size(p)):
  +l = List.length(&2, Word(8n), p)
  +f = Pg.Form.size.defs(ds)
  le_rw_r(l, f, Pg.Program.size(p), size.eq(p, ds, rd),
    le_trans(l, Gd(ds, 0n), f, read.ge(p, ds, rd), le_rw_r(Gd(ds, 0n), Nat.add(f, 0n), f, add_zero(f), gd.le(ds, 0n))))

# The need
# --------

# 64 × z + 1 <= 64 × (z + s) + 2^24
def need_ge(+z: Nat, +s: Nat) ->
  Le(1n+Nat.mul(64n, z), Nat.add(Nat.mul(64n, Nat.add(z, s)), 16777216n)):
  +x = Nat.mul(64n, z)
  le_trans(1n+x, Nat.add(x, 1n), Nat.add(Nat.mul(64n, Nat.add(z, s)), 16777216n), le_succ_add(x),
    add_mono(x, Nat.mul(64n, Nat.add(z, s)), 1n, 16777216n, mul_mono_r(64n, z, Nat.add(z, s), le_add_r(z, s)), le_one()))

# a small-failing book: 2^32 <= 64 × |p|
def len_ge(+p: List<&2, Word(8n)>, small: {Mc.Img.small(p, 0) == False{} : Bool}) ->
  Le(D(32n, 1n), Nat.mul(64n, List.length(&2, Word(8n), p))):
  +l = List.length(&2, Word(8n), p)
  +h1 = le_rw_r(1n+U32.to_nat(67108863), Nat.add(U32.to_nat(0), l), l, zero_add(l), small.len(p, 0, small))
  +h2 = le_rw_l(1n+U32.to_nat(67108863), D(26n, 1n), l, val_M(), h1)
  le_rw_l(Nat.mul(64n, D(26n, 1n)), D(32n, 1n), Nat.mul(64n, l), mul_64(), mul_mono_r(64n, D(26n, 1n), l, h2))

# a book of 2^26 bytes or more needs more memory than a module can have
def need.big.proof(
  +p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +n: Nat, +m: U32,
  rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  small: {Mc.Img.small(p, 0) == False{} : Bool},
  big: {Nat.is_le(Pg.Program.need(p, i, n), Pg.Program.memory(m)) == True{} : Bool}
) -> Empty:
  +l = List.length(&2, Word(8n), p)
  +z = Pg.Program.size(p)
  +x = Nat.mul(64n, z)
  +need = Pg.Program.need(p, i, n)
  +mem = Pg.Program.memory(m)
  +hn = {need_ge(z, Pg.Program.largest(p, i, n)) : Le(1n+x, need)}
  +hz = mul_mono_r(64n, l, z, size.ge(p, ds, rd))
  not_succ_le(x,
    le_trans(1n+x, need, x, hn,
      le_trans(need, mem, x, toLe(need, mem, big),
        le_trans(mem, D(32n, 1n), x, memory_le(m),
          le_trans(D(32n, 1n), Nat.mul(64n, l), x, len_ge(p, small), hz)))))
