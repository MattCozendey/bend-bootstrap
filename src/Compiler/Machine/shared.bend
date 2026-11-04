# compiler: layer B0, the kit of the machine's proofs
# ===================================================
#
# What every layer of the machine's proofs shares: Bool facts, membership in
# lists of registers (Nat) and of cells (U32), and List.get after List.set.
# Self-contained: it imports Base only, and proves its own lemmas. A lemma
# whose body is ?TODO is still open.
#
# A fact is a Bool equation {f(..) == True{} : Bool}; facts join with the
# product A & B, a witness with &x:T -> P. A list of registers or cells is a
# List<&2, Nat> or a List<&2, U32>, whose facts close by {==} when the lists
# are concrete.

import Base

# Lists
# -----

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

# no register of xs is in ys
def Disj(xs: List<&2, Nat>, +ys: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, rest}:
      Bool.not(Has(ys, x)) && Disj(rest, ys)

# each register of xs is in ys
def Sub(xs: List<&2, Nat>, +ys: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, rest}:
      Has(ys, x) && Sub(rest, ys)

# Bool
# ----

def bool.T(b: Bool) -> Type:
  match b:
    case True{}:
      Empty
    case False{}:
      Unit

# False is not True
def bool.ff(-G: Type, +e: {False{} == True{} : Bool}) -> G:
  Empty.absurd(G, (%e : bool.T(_); Unit{}))

# True is not False
def bool.tf(-G: Type, +e: {True{} == False{} : Bool}) -> G:
  bool.ff(G, Equal.sym(Bool, True{}, False{}, e))

# a Bool is True or False: from b == True, not b == False
def bool.tf2(-G: Type, -b: Bool, +ht: {b == True{} : Bool}, +hf: {b == False{} : Bool}) -> G:
  bool.ff(G, Equal.trans(Bool, False{}, b, True{}, Equal.sym(Bool, b, False{}, hf), ht))

def bool.or_f(a: Bool, -b: Bool, +ha: {a == False{} : Bool}, +hb: {b == False{} : Bool}) -> {Bool.or(a, b) == False{} : Bool}:
  match a:
    case False{}:
      hb
    case True{}:
      bool.tf({Bool.or(True{}, b) == False{} : Bool}, ha)

def bool.and_l(a: Bool, -b: Bool, +h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def bool.and_r(a: Bool, -b: Bool, +h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      bool.ff({b == True{} : Bool}, h)

def bool.and_i(a: Bool, -b: Bool, +ha: {a == True{} : Bool}, +hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      hb
    case False{}:
      bool.ff({Bool.and(False{}, b) == True{} : Bool}, ha)

def bool.or_l(a: Bool, -b: Bool, +h: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      bool.ff({Bool.or(False{}, b) == True{} : Bool}, h)

def bool.or_r(a: Bool, -b: Bool, +h: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def bool.not_t(a: Bool, +h: {Bool.not(a) == True{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      bool.ff({True{} == False{} : Bool}, h)
    case False{}:
      {==}

def bool.not_f(a: Bool, +h: {a == False{} : Bool}) -> {Bool.not(a) == True{} : Bool}:
  match a:
    case True{}:
      bool.ff({Bool.not(True{}) == True{} : Bool}, Equal.sym(Bool, True{}, False{}, h))
    case False{}:
      {==}

# a split on a Bool b: G from each of b == True and b == False
def bool.case(+b: Bool, -G: Type, t: @+h: {b == True{} : Bool} -> G, f: @+h: {b == False{} : Bool} -> G) -> G:
  match b:
    case True{}:
      t({==})
    case False{}:
      f({==})

# Nat
# ---

def nat.is_eq_ok(+a: Nat, +b: Nat, +e: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      bool.ff({0n == 1n+q : Nat}, e)
    case 1n+p 0n:
      bool.ff({1n+p == 0n : Nat}, e)
    case 1n+p 1n+q:
      %nat.is_eq_ok(p, q, e) : {1n+p == 1n+_ : Nat}
      {==}

def nat.is_eq_refl(a: Nat) -> {Nat.is_eq(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      nat.is_eq_refl(p)

def nat.is_eq_sym(a: Nat, b: Nat) -> {Nat.is_eq(a, b) == Nat.is_eq(b, a) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      nat.is_eq_sym(p, q)

# Has, Disj, Sub
# --------------

# x is not r when ys has r but not x (e is Nat.is_eq(x, r))
def has.ne(e: Bool, +x: Nat, +ys: List<&2, Nat>, +r: Nat, +he: {Nat.is_eq(x, r) == e : Bool},
  +hx: {Has(ys, x) == False{} : Bool}, +h: {Has(ys, r) == True{} : Bool}) -> {e == False{} : Bool}:
  match e:
    case False{}:
      {==}
    case True{}:
      +xr = nat.is_eq_ok(x, r, he)
      bool.tf2({True{} == False{} : Bool}, Has(ys, r), h,
        Equal.trans(Bool, Has(ys, r), Has(ys, x), False{}, Equal.cong(Nat, Bool, z => Has(ys, z), r, x, Equal.sym(Nat, x, r, xr)), hx))

# a register that ys has is not one of xs, when xs and ys are disjoint
def disj.has(+xs: List<&2, Nat>, +ys: List<&2, Nat>, +r: Nat, +d: {Disj(xs, ys) == True{} : Bool},
  +h: {Has(ys, r) == True{} : Bool}) -> {Has(xs, r) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, rest}:
      bool.or_f(Nat.is_eq(x, r), Has(rest, r),
        has.ne(Nat.is_eq(x, r), x, ys, r, {==}, bool.not_t(Has(ys, x), bool.and_l(Bool.not(Has(ys, x)), Disj(rest, ys), d)), h),
        disj.has(rest, ys, r, bool.and_r(Bool.not(Has(ys, x)), Disj(rest, ys), d), h))

# a register that ys does not have is not one of xs, when ys holds each of xs
def sub.has(+xs: List<&2, Nat>, +ys: List<&2, Nat>, +r: Nat, +s: {Sub(xs, ys) == True{} : Bool},
  +h: {Has(ys, r) == False{} : Bool}) -> {Has(xs, r) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, rest}:
      bool.or_f(Nat.is_eq(x, r), Has(rest, r),
        has.ne(Nat.is_eq(x, r), r, ys, x, Equal.trans(Bool, Nat.is_eq(r, x), Nat.is_eq(x, r), Nat.is_eq(x, r), nat.is_eq_sym(r, x), {==}), h,
          bool.and_l(Has(ys, x), Sub(rest, ys), s)),
        sub.has(rest, ys, r, bool.and_r(Has(ys, x), Sub(rest, ys), s), h))

# Sub with one more register in ys
def sub.con(+xs: List<&2, Nat>, +y: Nat, +ys: List<&2, Nat>, +s: {Sub(xs, ys) == True{} : Bool}) ->
  {Sub(xs, Con{y, ys}) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, rest}:
      bool.and_i(Has(Con{y, ys}, x), Sub(rest, Con{y, ys}), bool.or_r(Nat.is_eq(y, x), Has(ys, x), bool.and_l(Has(ys, x), Sub(rest, ys), s)),
        sub.con(rest, y, ys, bool.and_r(Has(ys, x), Sub(rest, ys), s)))

# Lists
# -----

def list.length_set(-A: Data, xs: List<&2, A>, n: Nat, x: A) ->
  {List.length(&2, A, List.set(&2, A, xs, n, x)) == List.length(&2, A, xs) : Nat}:
  match xs n:
    case Nil{} _:
      {==}
    case Con{h, t} 0n:
      {==}
    case Con{h, t} 1n+p:
      %list.length_set(A, t, p, x) : {1n+List.length(&2, A, List.set(&2, A, t, p, x)) == 1n+_ : Nat}
      {==}

# List.get after List.set, at the index set (below the length) or another
def list.get_set(-A: Data, +xs: List<&2, A>, +n: Nat, +x: A, +j: Nat,
  +h: {Nat.is_lt(n, List.length(&2, A, xs)) == True{} : Bool}) ->
  {List.get(&2, A, List.set(&2, A, xs, n, x), j) == Bool.pick(Maybe<&2, A>, Nat.is_eq(n, j), Some{x}, List.get(&2, A, xs, j)) : Maybe<&2, A>}:
  match xs n:
    case Nil{} 0n:
      bool.ff({List.get(&2, A, Nil{}, j) == Bool.pick(Maybe<&2, A>, Nat.is_eq(0n, j), Some{x}, List.get(&2, A, Nil{}, j)) : Maybe<&2, A>}, h)
    case Nil{} 1n+m:
      bool.ff({List.get(&2, A, Nil{}, j) == Bool.pick(Maybe<&2, A>, Nat.is_eq(1n+m, j), Some{x}, List.get(&2, A, Nil{}, j)) : Maybe<&2, A>}, h)
    case Con{y, t} 0n:
      match j:
        case 0n:
          {==}
        case 1n+p:
          {==}
    case Con{y, t} 1n+m:
      match j:
        case 0n:
          {==}
        case 1n+p:
          list.get_set(A, t, m, x, p, h)

def maybe.T(-A: Data, m: Maybe<&2, A>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{_}:
      Empty

# an index below the length finds an item: Some of it (d: what Maybe.default gives for none)
def list.get_lt(-A: Data, +xs: List<&2, A>, +n: Nat, +d: A, +h: {Nat.is_lt(n, List.length(&2, A, xs)) == True{} : Bool}) ->
  {List.get(&2, A, xs, n) == Some{Maybe.default(&2, A, List.get(&2, A, xs, n), d)} : Maybe<&2, A>}:
  match xs n:
    case Nil{} 0n:
      bool.ff({List.get(&2, A, Nil{}, 0n) == Some{Maybe.default(&2, A, List.get(&2, A, Nil{}, 0n), d)} : Maybe<&2, A>}, h)
    case Nil{} 1n+m:
      bool.ff({List.get(&2, A, Nil{}, 1n+m) == Some{Maybe.default(&2, A, List.get(&2, A, Nil{}, 1n+m), d)} : Maybe<&2, A>}, h)
    case Con{y, t} 0n:
      {==}
    case Con{y, t} 1n+m:
      list.get_lt(A, t, m, d, h)

# an index that finds an item is below the length
def list.lt_get(-A: Data, +xs: List<&2, A>, +n: Nat, +c: A, +e: {List.get(&2, A, xs, n) == Some{c} : Maybe<&2, A>}) ->
  {Nat.is_lt(n, List.length(&2, A, xs)) == True{} : Bool}:
  match xs n:
    case Nil{} _:
      Empty.absurd({Nat.is_lt(n, 0n) == True{} : Bool}, (%e : maybe.T(A, _); Unit{}))
    case Con{y, t} 0n:
      {==}
    case Con{y, t} 1n+m:
      list.lt_get(A, t, m, c, e)

# U32
# ---

# the word of n zero bits
def word.zero(n: Nat) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      WCon{False{}, word.zero(p)}

def cmp.fin_ff(c: Cmp) -> {Cmp.is_eq(Word.cmp.fin(False{}, False{}, c)) == Cmp.is_eq(c) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def cmp.fin_tf(c: Cmp) -> {Cmp.is_eq(Word.cmp.fin(True{}, False{}, c)) == False{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

# a word equal to the zero word, by Word.cmp, is it
def word.cmp_zero(+n: Nat, +w: Word(n), +h: {Cmp.is_eq(Word.cmp(n, w, word.zero(n))) == True{} : Bool}) ->
  {w == word.zero(n) : Word(n)}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{+b, +t}:
          match b:
            case False{}:
              +ht = Equal.trans(Bool, Cmp.is_eq(Word.cmp(p, t, word.zero(p))), Cmp.is_eq(Word.cmp.fin(False{}, False{}, Word.cmp(p, t, word.zero(p)))),
                True{}, Equal.sym(Bool, Cmp.is_eq(Word.cmp.fin(False{}, False{}, Word.cmp(p, t, word.zero(p)))), Cmp.is_eq(Word.cmp(p, t, word.zero(p))),
                  cmp.fin_ff(Word.cmp(p, t, word.zero(p)))), h)
              Equal.cong(Word(p), Word(1n+p), z => WCon{False{}, z}, t, word.zero(p), word.cmp_zero(p, t, ht))
            case True{}:
              bool.tf2({WCon{True{}, t} == word.zero(1n+p) : Word(1n+p)}, Cmp.is_eq(Word.cmp.fin(True{}, False{}, Word.cmp(p, t, word.zero(p)))), h,
                cmp.fin_tf(Word.cmp(p, t, word.zero(p))))

# a word that U32.is_zero finds zero is 0
def u32.is_zero_t(+x: U32, +h: {U32.is_zero(x) == True{} : Bool}) -> {x == 0 : U32}:
  match x:
    case U32{+w}:
      Equal.cong(Word(32n), U32, z => U32{z}, w, word.zero(32n), word.cmp_zero(32n, w, h))
