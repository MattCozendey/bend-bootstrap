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
def bool.ff(-G: Type, e: {False{} == True{} : Bool}) -> G:
  Empty.absurd(G, (%e : bool.T(_); Unit{}))

def bool.and_l(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def bool.and_r(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      bool.ff({b == True{} : Bool}, h)

def bool.and_i(a: Bool, -b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      hb
    case False{}:
      bool.ff({Bool.and(False{}, b) == True{} : Bool}, ha)

def bool.or_l(a: Bool, -b: Bool, h: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      bool.ff({Bool.or(False{}, b) == True{} : Bool}, h)

def bool.or_r(a: Bool, -b: Bool, h: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def bool.not_t(a: Bool, h: {Bool.not(a) == True{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      bool.ff({True{} == False{} : Bool}, h)
    case False{}:
      {==}

def bool.not_f(a: Bool, h: {a == False{} : Bool}) -> {Bool.not(a) == True{} : Bool}:
  match a:
    case True{}:
      bool.ff({Bool.not(True{}) == True{} : Bool}, Equal.sym(Bool, True{}, False{}, h))
    case False{}:
      {==}

# Nat
# ---

def nat.is_eq_ok(a: Nat, b: Nat, e: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
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

# a register that ys has is not one of xs, when xs and ys are disjoint
def disj.has(xs: List<&2, Nat>, +ys: List<&2, Nat>, +r: Nat, d: {Disj(xs, ys) == True{} : Bool},
  h: {Has(ys, r) == True{} : Bool}) -> {Has(xs, r) == False{} : Bool}:
  ?TODO

# a register that ys does not have is not one of xs, when ys holds each of xs
def sub.has(xs: List<&2, Nat>, +ys: List<&2, Nat>, +r: Nat, s: {Sub(xs, ys) == True{} : Bool},
  h: {Has(ys, r) == False{} : Bool}) -> {Has(xs, r) == False{} : Bool}:
  ?TODO

# Sub with one more register in ys
def sub.con(xs: List<&2, Nat>, +y: Nat, +ys: List<&2, Nat>, s: {Sub(xs, ys) == True{} : Bool}) ->
  {Sub(xs, Con{y, ys}) == True{} : Bool}:
  ?TODO

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
def list.get_set(-A: Data, xs: List<&2, A>, n: Nat, x: A, +j: Nat,
  h: {Nat.is_lt(n, List.length(&2, A, xs)) == True{} : Bool}) ->
  {List.get(&2, A, List.set(&2, A, xs, n, x), j) == Bool.pick(Maybe<&2, A>, Nat.is_eq(n, j), Some{x}, List.get(&2, A, xs, j)) : Maybe<&2, A>}:
  ?TODO
