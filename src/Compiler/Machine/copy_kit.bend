# compiler: the copy's kit
# ========================
#
# Lemmas of Bool, Nat, U32, the cells and the runs of Cir that the proofs
# of copy_substitution.bend's claims use.

import Base
import ../../Wasm/impl.bend as Wa
import ../Cir/impl.bend as Cr
import ./cell_terms.bend as T
import ../need_big.bend as N
import ./copy_substitution.bend as D

# Bools
# -----

def Bo.ft(-G: Type, h: {True{} == False{} : Bool}) -> G:
  Empty.absurd(G, N.true_ne_false(h))

def Bo.tf(-G: Type, h: {False{} == True{} : Bool}) -> G:
  Empty.absurd(G, N.false_ne_true(h))

def Bo.and_l(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Bo.tf({False{} == True{} : Bool}, h)

def Bo.and_r(a: Bool, b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      Bo.tf({b == True{} : Bool}, h)

def Bo.and_i(-a: Bool, -b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  %Equal.sym(Bool, b, True{}, hb) : {Bool.and(True{}, _) == True{} : Bool}
  {==}

# a or b, and not a, give b
def Bo.or_r(a: Bool, b: Bool, h: {Bool.or(a, b) == True{} : Bool}, na: {a == False{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      Bo.tf({b == True{} : Bool}, Equal.sym(Bool, True{}, False{}, na))
    case False{}:
      h

def Bo.or_il(-a: Bool, b: Bool, h: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, h) : {Bool.or(_, b) == True{} : Bool}
  {==}

def Bo.or_ir(a: Bool, -b: Bool, h: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def Bo.not_t(a: Bool, h: {Bool.not(a) == True{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      Bo.tf({True{} == False{} : Bool}, h)
    case False{}:
      {==}

def Bo.not_f(a: Bool, h: {Bool.not(a) == False{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Bo.ft({False{} == True{} : Bool}, h)

def Bo.not_i(-a: Bool, h: {a == False{} : Bool}) -> {Bool.not(a) == True{} : Bool}:
  %Equal.sym(Bool, a, False{}, h) : {Bool.not(_) == True{} : Bool}
  {==}

# Words and U32
# -------------

def W.cmp_eq.same(c: Cmp, b: Bool, -p: Nat, -at: Word(p), -bt: Word(p), ih: {c == EQ{} : Cmp} -> {at == bt : Word(p)},
  h: {Word.cmp.fin(b, b, c) == EQ{} : Cmp}) -> {WCon{b, at} == WCon{b, bt} : Word.Con<p>}:
  match c:
    case LT{}:
      Empty.absurd({WCon{b, at} == WCon{b, bt} : Word.Con<p>}, N.true_ne_false(Equal.cong(Cmp, Bool, x => Cmp.is_lt(x), LT{}, EQ{}, h)))
    case GT{}:
      Empty.absurd({WCon{b, at} == WCon{b, bt} : Word.Con<p>}, N.true_ne_false(Equal.cong(Cmp, Bool, x => Cmp.is_gt(x), GT{}, EQ{}, h)))
    case EQ{}:
      %ih({==}) : {WCon{b, at} == WCon{b, _} : Word.Con<p>}
      {==}

def W.cmp_eq.diff(c: Cmp, -G: Type, h: {Word.cmp.fin(False{}, True{}, c) == EQ{} : Cmp}) -> G:
  match c:
    case LT{}:
      Empty.absurd(G, N.true_ne_false(Equal.cong(Cmp, Bool, x => Cmp.is_lt(x), LT{}, EQ{}, h)))
    case GT{}:
      Empty.absurd(G, N.true_ne_false(Equal.cong(Cmp, Bool, x => Cmp.is_gt(x), GT{}, EQ{}, h)))
    case EQ{}:
      Empty.absurd(G, N.true_ne_false(Equal.cong(Cmp, Bool, x => Cmp.is_lt(x), LT{}, EQ{}, h)))

def W.cmp_eq.diff2(c: Cmp, -G: Type, h: {Word.cmp.fin(True{}, False{}, c) == EQ{} : Cmp}) -> G:
  match c:
    case LT{}:
      Empty.absurd(G, N.true_ne_false(Equal.cong(Cmp, Bool, x => Cmp.is_lt(x), LT{}, EQ{}, h)))
    case GT{}:
      Empty.absurd(G, N.true_ne_false(Equal.cong(Cmp, Bool, x => Cmp.is_gt(x), GT{}, EQ{}, h)))
    case EQ{}:
      Empty.absurd(G, N.true_ne_false(Equal.cong(Cmp, Bool, x => Cmp.is_gt(x), GT{}, EQ{}, h)))

def W.cmp_eq.fin(ab: Bool, bb: Bool, c: Cmp, -p: Nat, -at: Word(p), -bt: Word(p), ih: {c == EQ{} : Cmp} -> {at == bt : Word(p)},
  h: {Word.cmp.fin(ab, bb, c) == EQ{} : Cmp}) -> {WCon{ab, at} == WCon{bb, bt} : Word.Con<p>}:
  match ab bb:
    case False{} False{}:
      W.cmp_eq.same(c, False{}, p, at, bt, ih, h)
    case True{} True{}:
      W.cmp_eq.same(c, True{}, p, at, bt, ih, h)
    case False{} True{}:
      W.cmp_eq.diff(c, {WCon{False{}, at} == WCon{True{}, bt} : Word.Con<p>}, h)
    case True{} False{}:
      W.cmp_eq.diff2(c, {WCon{True{}, at} == WCon{False{}, bt} : Word.Con<p>}, h)

# words that compare equal are equal
def W.cmp_eq(n: Nat, a: Word(n), b: Word(n), h: {Word.cmp(n, a, b) == EQ{} : Cmp}) -> {a == b : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+(+p):
      match a b:
        case WCon{ab, +at} WCon{bb, +bt}:
          W.cmp_eq.fin(ab, bb, Word.cmp(p, at, bt), p, at, bt, e => W.cmp_eq(p, at, bt, e), h)

def W.cmp_refl(n: Nat, a: Word(n)) -> {Word.cmp(n, a, a) == EQ{} : Cmp}:
  match n:
    case 0n:
      match a:
        case WNil{}:
          {==}
    case 1n+(+p):
      match a:
        case WCon{False{}, +at}:
          %Equal.sym(Cmp, Word.cmp(p, at, at), EQ{}, W.cmp_refl(p, at)) : {Word.cmp.fin(False{}, False{}, _) == EQ{} : Cmp}
          {==}
        case WCon{True{}, +at}:
          %Equal.sym(Cmp, Word.cmp(p, at, at), EQ{}, W.cmp_refl(p, at)) : {Word.cmp.fin(True{}, True{}, _) == EQ{} : Cmp}
          {==}

def U.cmp_eq(a: U32, b: U32, h: {U32.cmp(a, b) == EQ{} : Cmp}) -> {a == b : U32}:
  match a b:
    case U32{x} U32{y}:
      Equal.cong(Word(32n), U32, w => U32{w}, x, y, W.cmp_eq(32n, x, y, h))

def U.eq.if(c: Cmp, h: {Cmp.is_eq(c) == True{} : Bool}) -> {c == EQ{} : Cmp}:
  match c:
    case LT{}:
      Bo.tf({LT{} == EQ{} : Cmp}, h)
    case EQ{}:
      {==}
    case GT{}:
      Bo.tf({GT{} == EQ{} : Cmp}, h)

# U32.is_eq says equality
def U.eq(+a: U32, +b: U32, h: {U32.is_eq(a, b) == True{} : Bool}) -> {a == b : U32}:
  U.cmp_eq(a, b, U.eq.if(U32.cmp(a, b), h))

def U.eq_refl(a: U32) -> {U32.is_eq(a, a) == True{} : Bool}:
  match a:
    case U32{+x}:
      %Equal.sym(Cmp, Word.cmp(32n, x, x), EQ{}, W.cmp_refl(32n, x)) : {Cmp.is_eq(_) == True{} : Bool}
      {==}

# equal cells are equal, so a cell that is not another is not equal to it
def U.ne(+a: U32, +b: U32, h: {U32.is_eq(a, b) == False{} : Bool}, e: {a == b : U32}) -> Empty:
  N.true_ne_false(Equal.trans(Bool, True{}, U32.is_eq(a, a), False{}, Equal.sym(Bool, U32.is_eq(a, a), True{}, U.eq_refl(a)),
    Equal.trans(Bool, U32.is_eq(a, a), U32.is_eq(a, b), False{}, Equal.cong(U32, Bool, x => U32.is_eq(a, x), a, b, e), h)))

# the relation of U32 numbers
def U.rel(a: U32, b: U32) -> N.Rel(U32.cmp(a, b), U32.to_nat(a), U32.to_nat(b)):
  match a b:
    case U32{x} U32{y}:
      N.Word.rel(32n, x, y)

# Cells
# -----

# a cell set at w is there
def Cl.get_set.at(n: Nat, +w: Word(n), +m: Cr.Cir.Cells, +c: Cr.Cir.Cell) ->
  {Cr.Cir.Cells.get.at(n, w, Cr.Cir.Cells.set.at(n, w, m, c)) == c : Cr.Cir.Cell}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{False{}, +t}:
          match m:
            case Cr.Cir.Cells.node{+lo, +hi}:
              Cl.get_set.at(p, t, lo, c)
            case Cr.Cir.Cells.none{}:
              Cl.get_set.at(p, t, Cr.Cir.Cells.none{}, c)
            case Cr.Cir.Cells.one{+d}:
              Cl.get_set.at(p, t, Cr.Cir.Cells.none{}, c)
        case WCon{True{}, +t}:
          match m:
            case Cr.Cir.Cells.node{+lo, +hi}:
              Cl.get_set.at(p, t, hi, c)
            case Cr.Cir.Cells.none{}:
              Cl.get_set.at(p, t, Cr.Cir.Cells.none{}, c)
            case Cr.Cir.Cells.one{+d}:
              Cl.get_set.at(p, t, Cr.Cir.Cells.none{}, c)

def Cl.get_set(+m: Cr.Cir.Cells, +i: U32, +c: Cr.Cir.Cell) -> {Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, i, c), i) == c : Cr.Cir.Cell}:
  match i:
    case U32{+w}:
      Cl.get_set.at(32n, w, m, c)

# no cell is all zeros
def Cl.get_none(n: Nat, +v: Word(n)) -> {Cr.Cir.Cell.zero() == Cr.Cir.Cells.get.at(n, v, Cr.Cir.Cells.none{}) : Cr.Cir.Cell}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match v:
        case WCon{False{}, +s}:
          {==}
        case WCon{True{}, +s}:
          {==}

# a set at w keeps the cell at another address v
def Cl.get_other.at(n: Nat, +v: Word(n), +w: Word(n), +m: Cr.Cir.Cells, +c: Cr.Cir.Cell, ne: {v == w : Word(n)} -> Empty) ->
  {Cr.Cir.Cells.get.at(n, v, m) == Cr.Cir.Cells.get.at(n, v, Cr.Cir.Cells.set.at(n, w, m, c)) : Cr.Cir.Cell}:
  match n:
    case 0n:
      match v w:
        case WNil{} WNil{}:
          Empty.absurd({Cr.Cir.Cells.get.at(0n, WNil{}, m) == Cr.Cir.Cells.get.at(0n, WNil{}, Cr.Cir.Cells.set.at(0n, WNil{}, m, c)) : Cr.Cir.Cell}, ne({==}))
    case 1n+(+p):
      match v w:
        case WCon{False{}, +s} WCon{False{}, +t}:
          match m:
            case Cr.Cir.Cells.node{+lo, +hi}:
              Cl.get_other.at(p, s, t, lo, c, e => ne(Equal.cong(Word(p), Word(1n+p), x => WCon{False{}, x}, s, t, e)))
            case Cr.Cir.Cells.none{}:
              Equal.trans(Cr.Cir.Cell, Cr.Cir.Cell.zero(), Cr.Cir.Cells.get.at(p, s, Cr.Cir.Cells.none{}), Cr.Cir.Cells.get.at(p, s, Cr.Cir.Cells.set.at(p, t, Cr.Cir.Cells.none{}, c)),
                Cl.get_none(p, s), Cl.get_other.at(p, s, t, Cr.Cir.Cells.none{}, c, e => ne(Equal.cong(Word(p), Word(1n+p), x => WCon{False{}, x}, s, t, e))))
            case Cr.Cir.Cells.one{+d}:
              Equal.trans(Cr.Cir.Cell, Cr.Cir.Cell.zero(), Cr.Cir.Cells.get.at(p, s, Cr.Cir.Cells.none{}), Cr.Cir.Cells.get.at(p, s, Cr.Cir.Cells.set.at(p, t, Cr.Cir.Cells.none{}, c)),
                Cl.get_none(p, s), Cl.get_other.at(p, s, t, Cr.Cir.Cells.none{}, c, e => ne(Equal.cong(Word(p), Word(1n+p), x => WCon{False{}, x}, s, t, e))))
        case WCon{True{}, +s} WCon{True{}, +t}:
          match m:
            case Cr.Cir.Cells.node{+lo, +hi}:
              Cl.get_other.at(p, s, t, hi, c, e => ne(Equal.cong(Word(p), Word(1n+p), x => WCon{True{}, x}, s, t, e)))
            case Cr.Cir.Cells.none{}:
              Equal.trans(Cr.Cir.Cell, Cr.Cir.Cell.zero(), Cr.Cir.Cells.get.at(p, s, Cr.Cir.Cells.none{}), Cr.Cir.Cells.get.at(p, s, Cr.Cir.Cells.set.at(p, t, Cr.Cir.Cells.none{}, c)),
                Cl.get_none(p, s), Cl.get_other.at(p, s, t, Cr.Cir.Cells.none{}, c, e => ne(Equal.cong(Word(p), Word(1n+p), x => WCon{True{}, x}, s, t, e))))
            case Cr.Cir.Cells.one{+d}:
              Equal.trans(Cr.Cir.Cell, Cr.Cir.Cell.zero(), Cr.Cir.Cells.get.at(p, s, Cr.Cir.Cells.none{}), Cr.Cir.Cells.get.at(p, s, Cr.Cir.Cells.set.at(p, t, Cr.Cir.Cells.none{}, c)),
                Cl.get_none(p, s), Cl.get_other.at(p, s, t, Cr.Cir.Cells.none{}, c, e => ne(Equal.cong(Word(p), Word(1n+p), x => WCon{True{}, x}, s, t, e))))
        case WCon{False{}, +s} WCon{True{}, +t}:
          match m:
            case Cr.Cir.Cells.node{+lo, +hi}:
              {==}
            case Cr.Cir.Cells.none{}:
              Cl.get_none(p, s)
            case Cr.Cir.Cells.one{+d}:
              Cl.get_none(p, s)
        case WCon{True{}, +s} WCon{False{}, +t}:
          match m:
            case Cr.Cir.Cells.node{+lo, +hi}:
              {==}
            case Cr.Cir.Cells.none{}:
              Cl.get_none(p, s)
            case Cr.Cir.Cells.one{+d}:
              Cl.get_none(p, s)

def Cl.get_other(+m: Cr.Cir.Cells, +j: U32, +i: U32, +c: Cr.Cir.Cell, ne: {j == i : U32} -> Empty) ->
  {Cr.Cir.Cells.get(m, j) == Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, i, c), j) : Cr.Cir.Cell}:
  match j i:
    case U32{+v} U32{+w}:
      Cl.get_other.at(32n, v, w, m, c, e => ne(Equal.cong(Word(32n), U32, x => U32{x}, v, w, e)))

# a set at i keeps the cell j, when U32.is_eq says they differ
def Cl.get_ne(+m: Cr.Cir.Cells, +j: U32, +i: U32, +c: Cr.Cir.Cell, h: {U32.is_eq(j, i) == False{} : Bool}) ->
  {Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, i, c), j) == Cr.Cir.Cells.get(m, j) : Cr.Cir.Cell}:
  Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(m, j), Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, i, c), j), Cl.get_other(m, j, i, c, e => U.ne(j, i, h, e)))

# Runs
# ----

# a write of r with the value v of e
def X.set(+f: Nat, +r: Nat, +e: Cr.Cir.Expr, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +F: U32, +K: U32, +pg: U32,
  +L: U32, +I: List<&2, Word(8n)>, +v: U32, ev: {Some{v} == Cr.Cir.eval(e, D.S(regs, m, nx, F, K, pg, L, I)) : Maybe<&2, U32>},
  hl: {True{} == Nat.is_lt(r, List.length(&2, U32, regs)) : Bool}) ->
  {Cr.Cir.exec(1n+f, Cr.Cir.Stmt.set{r, e}, D.S(regs, m, nx, F, K, pg, L, I)) ==
    Cr.Cir.Out.next{D.S(List.set(&2, U32, regs, r, v), m, nx, F, K, pg, L, I)} : Cr.Cir.Out}:
  %ev : {Cr.Cir.exec.set(r, _, D.S(regs, m, nx, F, K, pg, L, I)) == Cr.Cir.Out.next{D.S(List.set(&2, U32, regs, r, v), m, nx, F, K, pg, L, I)} : Cr.Cir.Out}
  %hl : {Cr.Cir.exec.set.of(Cr.Cir.regs.set.if(_, regs, r, v), D.S(regs, m, nx, F, K, pg, L, I)) ==
    Cr.Cir.Out.next{D.S(List.set(&2, U32, regs, r, v), m, nx, F, K, pg, L, I)} : Cr.Cir.Out}
  {==}

# a store of the value x of v in field k of the cell i, the value of c
def X.st(+f: Nat, +k: Nat, +c: Cr.Cir.Expr, +v: Cr.Cir.Expr, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +F: U32, +K: U32,
  +pg: U32, +L: U32, +I: List<&2, Word(8n)>, +i: U32, +x: U32,
  ec: {Some{i} == Cr.Cir.eval(c, D.S(regs, m, nx, F, K, pg, L, I)) : Maybe<&2, U32>},
  ev: {Some{x} == Cr.Cir.eval(v, D.S(regs, m, nx, F, K, pg, L, I)) : Maybe<&2, U32>},
  hc: {True{} == Cr.Cir.is_cell(i, K, F, nx) : Bool}) ->
  {Cr.Cir.exec(1n+f, Cr.Cir.Stmt.store{k, c, v}, D.S(regs, m, nx, F, K, pg, L, I)) ==
    Cr.Cir.Out.next{D.S(regs, Cr.Cir.Cells.set(m, i, Cr.Cir.Cell.set(k, Cr.Cir.Cells.get(m, i), x)), nx, F, K, pg, L, I)} : Cr.Cir.Out}:
  +st = D.S(regs, m, nx, F, K, pg, L, I)
  +out = {Cr.Cir.Out.next{D.S(regs, Cr.Cir.Cells.set(m, i, Cr.Cir.Cell.set(k, Cr.Cir.Cells.get(m, i), x)), nx, F, K, pg, L, I)} : Cr.Cir.Out}
  %ec : {Cr.Cir.exec.store(k, _, Cr.Cir.eval(v, st), st) == out : Cr.Cir.Out}
  %ev : {Cr.Cir.exec.store(k, Some{i}, _, st) == out : Cr.Cir.Out}
  %hc : {Cr.Cir.exec.store.if(_, k, i, x, st) == out : Cr.Cir.Out}
  {==}

# an if whose condition is x, not 0: its then
def X.if1(+f: Nat, +c: Cr.Cir.Expr, +t: Cr.Cir.Stmt, +e: Cr.Cir.Stmt, +st: Cr.Cir.State, +x: U32,
  ev: {Some{x} == Cr.Cir.eval(c, st) : Maybe<&2, U32>}, nz: {False{} == U32.is_zero(x) : Bool}) ->
  {Cr.Cir.exec(1n+f, Cr.Cir.Stmt.if{c, t, e}, st) == Cr.Cir.exec(1n+f, t, st) : Cr.Cir.Out}:
  %ev : {Cr.Cir.exec.if(_, u => Cr.Cir.exec(1n+f, t, st), u => Cr.Cir.exec(1n+f, e, st)) == Cr.Cir.exec(1n+f, t, st) : Cr.Cir.Out}
  %nz : {Cr.Cir.exec.if.of(_, u => Cr.Cir.exec(1n+f, t, st), u => Cr.Cir.exec(1n+f, e, st)) == Cr.Cir.exec(1n+f, t, st) : Cr.Cir.Out}
  {==}

# an if whose condition is 0: its else
def X.if0(+f: Nat, +c: Cr.Cir.Expr, +t: Cr.Cir.Stmt, +e: Cr.Cir.Stmt, +st: Cr.Cir.State,
  ev: {Some{0} == Cr.Cir.eval(c, st) : Maybe<&2, U32>}) ->
  {Cr.Cir.exec(1n+f, Cr.Cir.Stmt.if{c, t, e}, st) == Cr.Cir.exec(1n+f, e, st) : Cr.Cir.Out}:
  %ev : {Cr.Cir.exec.if(_, u => Cr.Cir.exec(1n+f, t, st), u => Cr.Cir.exec(1n+f, e, st)) == Cr.Cir.exec(1n+f, e, st) : Cr.Cir.Out}
  {==}

# a then b, once a ends in st1
def X.seq(+f: Nat, a: Cr.Cir.Stmt, +b: Cr.Cir.Stmt, +st: Cr.Cir.State, +st1: Cr.Cir.State,
  h: {Cr.Cir.Out.next{st1} == Cr.Cir.exec(1n+f, a, st) : Cr.Cir.Out}) ->
  {Cr.Cir.exec(1n+f, Cr.Cir.Stmt.seq{a, b}, st) == Cr.Cir.exec(1n+f, b, st1) : Cr.Cir.Out}:
  %h : {Cr.Cir.exec.then(_, t => Cr.Cir.exec(1n+f, b, t)) == Cr.Cir.exec(1n+f, b, st1) : Cr.Cir.Out}
  {==}

# a round of a while whose condition is x, not 0
def X.wh1(+f: Nat, +c: Cr.Cir.Expr, +body: Cr.Cir.Stmt, +st: Cr.Cir.State, +x: U32,
  ev: {Some{x} == Cr.Cir.eval(c, st) : Maybe<&2, U32>}, nz: {False{} == U32.is_zero(x) : Bool}) ->
  {Cr.Cir.exec(1n+f, Cr.Cir.Stmt.while{c, body}, st) ==
    Cr.Cir.exec.then(Cr.Cir.exec(f, body, st), t => Cr.Cir.exec(f, Cr.Cir.Stmt.while{c, body}, t)) : Cr.Cir.Out}:
  +rhs = {Cr.Cir.exec.then(Cr.Cir.exec(f, body, st), t => Cr.Cir.exec(f, Cr.Cir.Stmt.while{c, body}, t)) : Cr.Cir.Out}
  %ev : {Cr.Cir.exec.if(_, u => rhs, u => Cr.Cir.Out.next{st}) == rhs : Cr.Cir.Out}
  %nz : {Cr.Cir.exec.if.of(_, u => rhs, u => Cr.Cir.Out.next{st}) == rhs : Cr.Cir.Out}
  {==}

# the end of a while whose condition is 0
def X.wh0(+f: Nat, +c: Cr.Cir.Expr, +body: Cr.Cir.Stmt, +st: Cr.Cir.State,
  ev: {Some{0} == Cr.Cir.eval(c, st) : Maybe<&2, U32>}) ->
  {Cr.Cir.exec(1n+f, Cr.Cir.Stmt.while{c, body}, st) == Cr.Cir.Out.next{st} : Cr.Cir.Out}:
  +rhs = {Cr.Cir.exec.then(Cr.Cir.exec(f, body, st), t => Cr.Cir.exec(f, Cr.Cir.Stmt.while{c, body}, t)) : Cr.Cir.Out}
  %ev : {Cr.Cir.exec.if(_, u => rhs, u => Cr.Cir.Out.next{st}) == Cr.Cir.Out.next{st} : Cr.Cir.Out}
  {==}

# Outcomes
# --------

# an outcome equal to one of which Ok holds
def Ok.eq(-o1: Cr.Cir.Out, -o2: Cr.Cir.Out, -F: U32, -K: U32, -L: U32, -I: List<&2, Word(8n)>, -B: Nat,
  -Q: List<&2, U32> -> Cr.Cir.Cells -> U32 -> U32 -> Type, e: {o2 == o1 : Cr.Cir.Out}, h: D.Ok(o2, F, K, L, I, B, Q)) ->
  D.Ok(o1, F, K, L, I, B, Q):
  %e : D.Ok(_, F, K, L, I, B, Q)
  h

# a state of which Q holds
def Ok.next(+rg: List<&2, U32>, +ms: Cr.Cir.Cells, +nx: U32, +F: U32, +K: U32, +pg: U32, +L: U32, +I: List<&2, Word(8n)>,
  -B: Nat, -Q: List<&2, U32> -> Cr.Cir.Cells -> U32 -> U32 -> Type, q: Q(rg, ms, nx, pg)) ->
  D.Ok(Cr.Cir.Out.next{D.S(rg, ms, nx, F, K, pg, L, I)}, F, K, L, I, B, Q):
  ({==}, q)

# a state of which At holds, by its parts
def Ok.at(st: Cr.Cir.State, +F: U32, +K: U32, +L: U32, +I: List<&2, Word(8n)>, -B: Nat, -Q: List<&2, U32> -> Cr.Cir.Cells -> U32 -> U32 -> Type,
  -R: List<&2, U32> -> Cr.Cir.Cells -> U32 -> U32 -> Type, -k: Cr.Cir.State -> Cr.Cir.Out, h: D.At(st, F, K, L, I, Q),
  g: @rg: List<&2, U32> -> @ms: Cr.Cir.Cells -> @nx: U32 -> @pg: U32 -> Q(rg, ms, nx, pg) -> D.Ok(k(D.S(rg, ms, nx, F, K, pg, L, I)), F, K, L, I, B, R)) ->
  D.Ok(k(st), F, K, L, I, B, R):
  match st:
    case Cr.Cir.State{+rg, +ms, +nx, fi, im, +pg, li, inp, out, outn}:
      (eq, q) = h
      %eq : D.Ok(k(_), F, K, L, I, B, R)
      g(rg, ms, nx, pg, q)

# a statement, then more
def Ok.then(o: Cr.Cir.Out, +F: U32, +K: U32, +L: U32, +I: List<&2, Word(8n)>, -B: Nat, -k: Cr.Cir.State -> Cr.Cir.Out,
  -Q: List<&2, U32> -> Cr.Cir.Cells -> U32 -> U32 -> Type, -R: List<&2, U32> -> Cr.Cir.Cells -> U32 -> U32 -> Type,
  h: D.Ok(o, F, K, L, I, B, Q),
  g: @rg: List<&2, U32> -> @ms: Cr.Cir.Cells -> @nx: U32 -> @pg: U32 -> Q(rg, ms, nx, pg) -> D.Ok(k(D.S(rg, ms, nx, F, K, pg, L, I)), F, K, L, I, B, R)) ->
  D.Ok(Cr.Cir.exec.then(o, k), F, K, L, I, B, R):
  match o:
    case Cr.Cir.Out.next{st}:
      Ok.at(st, F, K, L, I, B, Q, R, k, h, g)
    case Cr.Cir.Out.halt{s, st}:
      match h:
    case Cr.Cir.Out.out_of_memory{}:
      h
    case Cr.Cir.Out.trap{}:
      match h:
    case Cr.Cir.Out.not_done{}:
      match h:

# a then b
def Ok.seq(+f: Nat, a: Cr.Cir.Stmt, +b: Cr.Cir.Stmt, st: Cr.Cir.State, +F: U32, +K: U32, +L: U32, +I: List<&2, Word(8n)>, -B: Nat,
  -Q: List<&2, U32> -> Cr.Cir.Cells -> U32 -> U32 -> Type, -R: List<&2, U32> -> Cr.Cir.Cells -> U32 -> U32 -> Type,
  h: D.Ok(Cr.Cir.exec(1n+f, a, st), F, K, L, I, B, Q),
  g: @rg: List<&2, U32> -> @ms: Cr.Cir.Cells -> @nx: U32 -> @pg: U32 -> Q(rg, ms, nx, pg) ->
    D.Ok(Cr.Cir.exec(1n+f, b, D.S(rg, ms, nx, F, K, pg, L, I)), F, K, L, I, B, R)) ->
  D.Ok(Cr.Cir.exec(1n+f, Cr.Cir.Stmt.seq{a, b}, st), F, K, L, I, B, R):
  Ok.then(Cr.Cir.exec(1n+f, a, st), F, K, L, I, B, t => Cr.Cir.exec(1n+f, b, t), Q, R, h, g)

# a round of a while, then the while again
def Ok.loop(+f: Nat, +c: Cr.Cir.Expr, +body: Cr.Cir.Stmt, +st: Cr.Cir.State, +x: U32, +F: U32, +K: U32, +L: U32, +I: List<&2, Word(8n)>,
  -B: Nat, -Q: List<&2, U32> -> Cr.Cir.Cells -> U32 -> U32 -> Type, -R: List<&2, U32> -> Cr.Cir.Cells -> U32 -> U32 -> Type,
  ev: {Some{x} == Cr.Cir.eval(c, st) : Maybe<&2, U32>}, nz: {False{} == U32.is_zero(x) : Bool},
  h: D.Ok(Cr.Cir.exec(1n+f, body, st), F, K, L, I, B, Q),
  g: @rg: List<&2, U32> -> @ms: Cr.Cir.Cells -> @nx: U32 -> @pg: U32 -> Q(rg, ms, nx, pg) ->
    D.Ok(Cr.Cir.exec(1n+f, Cr.Cir.Stmt.while{c, body}, D.S(rg, ms, nx, F, K, pg, L, I)), F, K, L, I, B, R)) ->
  D.Ok(Cr.Cir.exec(2n+f, Cr.Cir.Stmt.while{c, body}, st), F, K, L, I, B, R):
  Ok.eq(Cr.Cir.exec(2n+f, Cr.Cir.Stmt.while{c, body}, st), Cr.Cir.exec.then(Cr.Cir.exec(1n+f, body, st), t => Cr.Cir.exec(1n+f, Cr.Cir.Stmt.while{c, body}, t)),
    F, K, L, I, B, R, Equal.sym(Cr.Cir.Out, Cr.Cir.exec(2n+f, Cr.Cir.Stmt.while{c, body}, st),
      Cr.Cir.exec.then(Cr.Cir.exec(1n+f, body, st), t => Cr.Cir.exec(1n+f, Cr.Cir.Stmt.while{c, body}, t)), X.wh1(1n+f, c, body, st, x, ev, nz)),
    Ok.then(Cr.Cir.exec(1n+f, body, st), F, K, L, I, B, t => Cr.Cir.exec(1n+f, Cr.Cir.Stmt.while{c, body}, t), Q, R, h, g))

# Order
# -----

def U.le.of(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), h: {Cmp.is_le(c) == True{} : Bool}) -> N.Le(x, y):
  match c:
    case LT{}:
      N.weaken(x, y, r)
    case EQ{}:
      %r : N.Le(x, _)
      N.le_refl(x)
    case GT{}:
      Bo.tf(N.Le(x, y), h)

# U32.is_le as Nat
def U.le(+a: U32, +b: U32, h: {U32.is_le(a, b) == True{} : Bool}) -> N.Le(U32.to_nat(a), U32.to_nat(b)):
  U.le.of(U32.cmp(a, b), U32.to_nat(a), U32.to_nat(b), U.rel(a, b), h)

def U.lt.of(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), h: {Cmp.is_lt(c) == True{} : Bool}) -> N.Le(1n+x, y):
  match c:
    case LT{}:
      r
    case EQ{}:
      Bo.tf(N.Le(1n+x, y), h)
    case GT{}:
      Bo.tf(N.Le(1n+x, y), h)

# U32.is_lt as Nat
def U.lt(+a: U32, +b: U32, h: {U32.is_lt(a, b) == True{} : Bool}) -> N.Le(1n+U32.to_nat(a), U32.to_nat(b)):
  U.lt.of(U32.cmp(a, b), U32.to_nat(a), U32.to_nat(b), U.rel(a, b), h)

def U.nz.of(c: Cmp, +x: Nat, r: N.Rel(c, x, 0n), h: N.Le(1n, x)) -> {Cmp.is_eq(c) == False{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({True{} == False{} : Bool}, N.le_rw_r(1n, x, 0n, r, h))
    case GT{}:
      {==}

# a cell from F on, past the image K, is not 0
def U.nz(+n: U32, +K: U32, +F: U32, hkf: {U32.is_lt(K, F) == True{} : Bool}, hfn: {U32.is_le(F, n) == True{} : Bool}) ->
  {U32.is_zero(n) == False{} : Bool}:
  U.nz.of(U32.cmp(n, 0), U32.to_nat(n), U.rel(n, 0),
    N.le_trans(1n, 1n+U32.to_nat(K), U32.to_nat(n), N.le_zero(U32.to_nat(K)),
      N.le_trans(1n+U32.to_nat(K), U32.to_nat(F), U32.to_nat(n), U.lt(K, F, hkf), U.le(F, n, hfn))))

# 0 <= g
def Na.le0(g: Nat) -> {Nat.is_le(0n, g) == True{} : Bool}:
  match g:
    case 0n:
      {==}
    case 1n+p:
      {==}

# p < q <= 0 is false
def Na.lt0(q: Nat, p: Nat, -G: Type, h2: {Nat.is_le(q, 0n) == True{} : Bool}, h1: {Nat.is_lt(p, q) == True{} : Bool}) -> G:
  match q:
    case 0n:
      match p:
        case 0n:
          Bo.tf(G, h1)
        case 1n+r:
          Bo.tf(G, h1)
    case 1n+r:
      Bo.tf(G, h2)

# a < b <= 1 + g gives a <= g
def Na.lt_le(b: Nat, a: Nat, +g: Nat, h1: {Nat.is_lt(a, b) == True{} : Bool}, h2: {Nat.is_le(b, 1n+g) == True{} : Bool}) ->
  {Nat.is_le(a, g) == True{} : Bool}:
  match b:
    case 0n:
      match a:
        case 0n:
          Bo.tf({Nat.is_le(0n, g) == True{} : Bool}, h1)
        case 1n+p:
          Bo.tf({Nat.is_le(1n+p, g) == True{} : Bool}, h1)
    case 1n+q:
      match a g:
        case 0n _:
          Na.le0(g)
        case 1n+p 0n:
          Na.lt0(q, p, {Nat.is_le(1n+p, 0n) == True{} : Bool}, h2, h1)
        case 1n+p 1n+(+r):
          Na.lt_le(q, p, r, h1, h2)

def Na.le_refl(a: Nat) -> {Nat.is_le(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Na.le_refl(p)

# a <= b gives a <= 1 + b
def Na.le_up(a: Nat, b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, 1n+b) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      match b:
        case 0n:
          Bo.tf({Nat.is_le(1n+p, 1n) == True{} : Bool}, h)
        case 1n+q:
          Na.le_up(p, q, h)

# q + c <= g gives c <= g
def Na.le_add_l(q: Nat, +c: Nat, g: Nat, h: {Nat.is_le(Nat.add(q, c), g) == True{} : Bool}) -> {Nat.is_le(c, g) == True{} : Bool}:
  match q:
    case 0n:
      h
    case 1n+r:
      match g:
        case 0n:
          Bo.tf({Nat.is_le(c, 0n) == True{} : Bool}, h)
        case 1n+(+gp):
          Na.le_up(c, gp, Na.le_add_l(r, c, gp, h))

# q + c <= 0 and p < q are false
def Na.c0(q: Nat, p: Nat, +c: Nat, -G: Type, h2: {Nat.is_le(Nat.add(q, c), 0n) == True{} : Bool},
  h1: {Nat.is_lt(p, q) == True{} : Bool}) -> G:
  match q:
    case 0n:
      match p:
        case 0n:
          Bo.tf(G, h1)
        case 1n+r:
          Bo.tf(G, h1)
    case 1n+r:
      Bo.tf(G, h2)

# a < b, b + c <= 1 + g give a + c <= g
def Na.lt_le_add(b: Nat, a: Nat, +c: Nat, g: Nat, h1: {Nat.is_lt(a, b) == True{} : Bool},
  h2: {Nat.is_le(Nat.add(b, c), 1n+g) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, c), g) == True{} : Bool}:
  match b:
    case 0n:
      match a:
        case 0n:
          Bo.tf({Nat.is_le(c, g) == True{} : Bool}, h1)
        case 1n+p:
          Bo.tf({Nat.is_le(1n+Nat.add(p, c), g) == True{} : Bool}, h1)
    case 1n+q:
      match a:
        case 0n:
          Na.le_add_l(q, c, g, h2)
        case 1n+p:
          match g:
            case 0n:
              Na.c0(q, p, c, {Nat.is_le(1n+Nat.add(p, c), 0n) == True{} : Bool}, h2, h1)
            case 1n+gp:
              Na.lt_le_add(q, p, c, gp, h1, h2)

# Nat order as U32 order
def U.le_t.of(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), h: N.Le(x, y)) -> {Cmp.is_le(c) == True{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({False{} == True{} : Bool}, N.not_succ_le(y, N.le_trans(1n+y, x, y, r, h)))

def U.le_t(+a: U32, +b: U32, h: N.Le(U32.to_nat(a), U32.to_nat(b))) -> {U32.is_le(a, b) == True{} : Bool}:
  U.le_t.of(U32.cmp(a, b), U32.to_nat(a), U32.to_nat(b), U.rel(a, b), h)

def U.lt_t.of(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), h: N.Le(1n+x, y)) -> {Cmp.is_lt(c) == True{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({False{} == True{} : Bool}, N.not_succ_le(y, N.le_rw_l(1n+x, 1n+y, y, Equal.cong(Nat, Nat, z => 1n+z, x, y, r), h)))
    case GT{}:
      Empty.absurd({False{} == True{} : Bool}, N.not_succ_le(y, N.le_trans(1n+y, x, y, r, N.weaken(x, y, h))))

def U.lt_t(+a: U32, +b: U32, h: N.Le(1n+U32.to_nat(a), U32.to_nat(b))) -> {U32.is_lt(a, b) == True{} : Bool}:
  U.lt_t.of(U32.cmp(a, b), U32.to_nat(a), U32.to_nat(b), U.rel(a, b), h)

# a < b <= c gives a < c
def U.lt_le(+a: U32, +b: U32, +c: U32, h1: {U32.is_lt(a, b) == True{} : Bool}, h2: {U32.is_le(b, c) == True{} : Bool}) ->
  {U32.is_lt(a, c) == True{} : Bool}:
  U.lt_t(a, c, N.le_trans(1n+U32.to_nat(a), U32.to_nat(b), U32.to_nat(c), U.lt(a, b, h1), U.le(b, c, h2)))

# a <= b < c gives a < c
def U.le_lt(+a: U32, +b: U32, +c: U32, h1: {U32.is_le(a, b) == True{} : Bool}, h2: {U32.is_lt(b, c) == True{} : Bool}) ->
  {U32.is_lt(a, c) == True{} : Bool}:
  U.lt_t(a, c, N.le_trans(1n+U32.to_nat(a), 1n+U32.to_nat(b), U32.to_nat(c), U.le(a, b, h1), U.lt(b, c, h2)))

# a < b and b <= a are false
def U.lt_ge(+a: U32, +b: U32, -G: Type, h1: {U32.is_lt(a, b) == True{} : Bool}, h2: {U32.is_le(b, a) == True{} : Bool}) -> G:
  Empty.absurd(G, N.not_succ_le(U32.to_nat(a), N.le_trans(1n+U32.to_nat(a), U32.to_nat(b), U32.to_nat(a), U.lt(a, b, h1), U.le(b, a, h2))))

# Budgets
# -------
#
# A Cir alloc at next nx runs out of memory only when the limit L has fewer
# than 20 (nx + 1) bytes (D.Lim.bytes): either nx is 214748364 or more, and
# 20 (nx + 1) is past 2^32, the most bytes of a limit; or the pages of the
# cell's last byte, ((20 nx + 19) >> 16) + 1, are more than L. The big
# numbers stay symbolic, as in need_big.bend: 2^k is N.D(k, 1n), 214748364
# is Pat(7), of nibbles 12, and the code's arithmetic is bounded above only (a
# wrap makes a value smaller).

# 20 × x
def T20(x: Nat) -> Nat:
  match x:
    case 0n:
      0n
    case 1n+p:
      20n+T20(p)

# 20 × x grows with x
def t20.mono(+x: Nat, +y: Nat, h: N.Le(x, y)) -> N.Le(T20(x), T20(y)):
  match x:
    case 0n:
      N.le_zero(T20(y))
    case 1n+p:
      match y:
        case 0n:
          Empty.absurd(N.Le(T20(1n+p), 0n), h)
        case 1n+q:
          t20.mono(p, q, h)

# 20 × 2x = 2 × 20x
def t20.double(+x: Nat) -> {T20(Nat.double(x)) == Nat.double(T20(x)) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      %t20.double(p) : {40n+T20(Nat.double(p)) == 40n+_ : Nat}
      {==}

# 20 × 16x = 16 × 20x
def t20.D4(+x: Nat) -> {T20(N.D(4n, x)) == N.D(4n, T20(x)) : Nat}:
  +x1 = Nat.double(x)
  +x2 = Nat.double(x1)
  +x3 = Nat.double(x2)
  Equal.trans(Nat, T20(Nat.double(x3)), Nat.double(T20(x3)), Nat.double(Nat.double(Nat.double(Nat.double(T20(x))))),
    t20.double(x3),
    Equal.cong(Nat, Nat, z => Nat.double(z), T20(x3), Nat.double(Nat.double(Nat.double(T20(x)))),
      Equal.trans(Nat, T20(x3), Nat.double(T20(x2)), Nat.double(Nat.double(Nat.double(T20(x)))),
        t20.double(x2),
        Equal.cong(Nat, Nat, z => Nat.double(z), T20(x2), Nat.double(Nat.double(T20(x))),
          Equal.trans(Nat, T20(x2), Nat.double(T20(x1)), Nat.double(Nat.double(T20(x))),
            t20.double(x1),
            Equal.cong(Nat, Nat, z => Nat.double(z), T20(x1), Nat.double(T20(x)), t20.double(x)))))))

# 0x0CCC...C, nibble by nibble: 12 + 16 × the rest
def Pat(j: Nat) -> Nat:
  match j:
    case 0n:
      0n
    case 1n+q:
      Nat.add(12n, N.D(4n, Pat(q)))

def E4(j: Nat) -> Nat:
  match j:
    case 0n:
      4n
    case 1n+q:
      4n+E4(q)

# 16 + 20 × Pat(j) = 2^(4 + 4j)
def pat.val(+j: Nat) -> {Nat.add(16n, T20(Pat(j))) == N.D(E4(j), 1n) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+q:
      %pat.val(q) : {256n+T20(N.D(4n, Pat(q))) == N.D(4n, _) : Nat}
      %Equal.sym(Nat, T20(N.D(4n, Pat(q))), N.D(4n, T20(Pat(q))), t20.D4(Pat(q))) :
        {256n+_ == 256n+N.D(4n, T20(Pat(q))) : Nat}
      {==}

# 16 + 20 × 214748364 = 2^32
def hP() -> {Nat.add(16n, T20(Pat(7n))) == N.D(32n, 1n) : Nat}:
  %{{==} : {E4(7n) == 32n : Nat}} : {Nat.add(16n, T20(Pat(7n))) == N.D(_, 1n) : Nat}
  pat.val(7n)

def q4(j: Nat) -> Nat:
  match j:
    case 0n:
      0n
    case 1n+q:
      4n+q4(q)

# n bits of 0x0CCC...C with j nibbles of 12 at the bottom, its lowest bit
# first; the index is n itself, so that the word of 32 bits is a Word(32n)
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

def wb.val(j: Nat, +n: Nat, e: {n == 4n+q4(j) : Nat}) -> {Word.to_nat(n, wb(n, j)) == Pat(j) : Nat}:
  match j:
    case 0n:
      %Equal.sym(Nat, n, 4n, e) : {Word.to_nat(_, wb(_, 0n)) == Pat(0n) : Nat}
      {==}
    case 1n+(+q):
      %Equal.sym(Nat, n, 4n+q4(1n+q), e) : {Word.to_nat(_, wb(_, 1n+q)) == Pat(1n+q) : Nat}
      %Equal.sym(Nat, Word.to_nat(q4(1n+q), wb(q4(1n+q), q)), Pat(q), wb.val(q, q4(1n+q), {==})) :
        {Nat.double(Nat.double(1n+Nat.double(1n+Nat.double(_)))) == Nat.add(12n, N.D(4n, Pat(q))) : Nat}
      {==}

def lit.wb() -> {214748364 == U32{wb(32n, 7n)} : U32}:
  {==}

# 214748364 is Pat(7)
def lit.pat() -> {U32.to_nat(214748364) == Pat(7n) : Nat}:
  %Equal.sym(U32, 214748364, U32{wb(32n, 7n)}, lit.wb()) : {U32.to_nat(_) == Pat(7n) : Nat}
  Equal.trans(Nat, U32.to_nat(U32{wb(32n, 7n)}), Word.to_nat(32n, wb(32n, 7n)), Pat(7n), N.u32_to_nat(wb(32n, 7n)),
    wb.val(7n, 32n, {==}))

# 2^k x grows with x
def Dk.mono(+k: Nat, +x: Nat, +y: Nat, h: N.Le(x, y)) -> N.Le(N.D(k, x), N.D(k, y)):
  match k:
    case 0n:
      h
    case 1n+q:
      N.double_mono(N.D(q, x), N.D(q, y), Dk.mono(q, x, y, h))

def adc.h0(+X: Nat, +A: Nat, +B: Nat, ih: N.Le(X, Nat.add(A, B))) -> N.Le(Nat.double(X), Nat.add(Nat.double(A), Nat.double(B))):
  N.le_rw_r(Nat.double(X), Nat.double(Nat.add(A, B)), Nat.add(Nat.double(A), Nat.double(B)), N.double_add(A, B),
    N.double_mono(X, Nat.add(A, B), ih))

def adc.h1(+X: Nat, +A: Nat, +B: Nat, ih: N.Le(X, 1n+Nat.add(A, B))) -> N.Le(Nat.double(X), 2n+Nat.add(Nat.double(A), Nat.double(B))):
  N.le_rw_r(Nat.double(X), 2n+Nat.double(Nat.add(A, B)), 2n+Nat.add(Nat.double(A), Nat.double(B)),
    Equal.cong(Nat, Nat, z => 2n+z, Nat.double(Nat.add(A, B)), Nat.add(Nat.double(A), Nat.double(B)), N.double_add(A, B)),
    N.double_mono(X, 1n+Nat.add(A, B), ih))

# 1 + (a + b) = a + (1 + b), on the right of a bound
def adc.r1(+Y: Nat, +a: Nat, +b: Nat, h: N.Le(Y, 1n+Nat.add(a, b))) -> N.Le(Y, Nat.add(a, 1n+b)):
  N.le_rw_r(Y, 1n+Nat.add(a, b), Nat.add(a, 1n+b), Equal.sym(Nat, Nat.add(a, 1n+b), 1n+Nat.add(a, b), N.add_succ_r(a, b)), h)

# the number of a sum of words, with the carry c in, is at most the sum
def adc.le(+n: Nat, +a: Word(n), +b: Word(n), +c: Bool) ->
  N.Le(Word.to_nat(n, Word.adc(n, a, b, False{}, c)), Nat.add(D.Nat.of(c), Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)))):
  match n:
    case 0n:
      N.le_zero(Nat.add(D.Nat.of(c), Nat.add(Word.to_nat(0n, a), Word.to_nat(0n, b))))
    case 1n+p:
      match a b c:
        case WCon{False{}, +at} WCon{False{}, +bt} False{}:
          adc.h0(Word.to_nat(p, Word.adc(p, at, bt, False{}, False{})), Word.to_nat(p, at), Word.to_nat(p, bt), adc.le(p, at, bt, False{}))
        case WCon{False{}, +at} WCon{False{}, +bt} True{}:
          adc.h0(Word.to_nat(p, Word.adc(p, at, bt, False{}, False{})), Word.to_nat(p, at), Word.to_nat(p, bt), adc.le(p, at, bt, False{}))
        case WCon{False{}, +at} WCon{True{}, +bt} False{}:
          +A = Word.to_nat(p, at)
          +B = Word.to_nat(p, bt)
          adc.r1(1n+Nat.double(Word.to_nat(p, Word.adc(p, at, bt, False{}, False{}))), Nat.double(A), Nat.double(B),
            adc.h0(Word.to_nat(p, Word.adc(p, at, bt, False{}, False{})), A, B, adc.le(p, at, bt, False{})))
        case WCon{False{}, +at} WCon{True{}, +bt} True{}:
          +A = Word.to_nat(p, at)
          +B = Word.to_nat(p, bt)
          +X = Nat.double(Word.to_nat(p, Word.adc(p, at, bt, False{}, True{})))
          N.le_rw_r(X, 2n+Nat.add(Nat.double(A), Nat.double(B)), 1n+Nat.add(Nat.double(A), 1n+Nat.double(B)),
            Equal.cong(Nat, Nat, z => 1n+z, 1n+Nat.add(Nat.double(A), Nat.double(B)), Nat.add(Nat.double(A), 1n+Nat.double(B)),
              Equal.sym(Nat, Nat.add(Nat.double(A), 1n+Nat.double(B)), 1n+Nat.add(Nat.double(A), Nat.double(B)), N.add_succ_r(Nat.double(A), Nat.double(B)))),
            adc.h1(Word.to_nat(p, Word.adc(p, at, bt, False{}, True{})), A, B, adc.le(p, at, bt, True{})))
        case WCon{True{}, +at} WCon{False{}, +bt} False{}:
          adc.h0(Word.to_nat(p, Word.adc(p, at, bt, False{}, False{})), Word.to_nat(p, at), Word.to_nat(p, bt), adc.le(p, at, bt, False{}))
        case WCon{True{}, +at} WCon{False{}, +bt} True{}:
          adc.h1(Word.to_nat(p, Word.adc(p, at, bt, False{}, True{})), Word.to_nat(p, at), Word.to_nat(p, bt), adc.le(p, at, bt, True{}))
        case WCon{True{}, +at} WCon{True{}, +bt} False{}:
          +A = Word.to_nat(p, at)
          +B = Word.to_nat(p, bt)
          +X = Nat.double(Word.to_nat(p, Word.adc(p, at, bt, False{}, True{})))
          N.le_rw_r(X, 2n+Nat.add(Nat.double(A), Nat.double(B)), 1n+Nat.add(Nat.double(A), 1n+Nat.double(B)),
            Equal.cong(Nat, Nat, z => 1n+z, 1n+Nat.add(Nat.double(A), Nat.double(B)), Nat.add(Nat.double(A), 1n+Nat.double(B)),
              Equal.sym(Nat, Nat.add(Nat.double(A), 1n+Nat.double(B)), 1n+Nat.add(Nat.double(A), Nat.double(B)), N.add_succ_r(Nat.double(A), Nat.double(B)))),
            adc.h1(Word.to_nat(p, Word.adc(p, at, bt, False{}, True{})), A, B, adc.le(p, at, bt, True{})))
        case WCon{True{}, +at} WCon{True{}, +bt} True{}:
          +A = Word.to_nat(p, at)
          +B = Word.to_nat(p, bt)
          +X = Nat.double(Word.to_nat(p, Word.adc(p, at, bt, False{}, True{})))
          N.le_rw_r(X, 2n+Nat.add(Nat.double(A), Nat.double(B)), 1n+Nat.add(Nat.double(A), 1n+Nat.double(B)),
            Equal.cong(Nat, Nat, z => 1n+z, 1n+Nat.add(Nat.double(A), Nat.double(B)), Nat.add(Nat.double(A), 1n+Nat.double(B)),
              Equal.sym(Nat, Nat.add(Nat.double(A), 1n+Nat.double(B)), 1n+Nat.add(Nat.double(A), Nat.double(B)), N.add_succ_r(Nat.double(A), Nat.double(B)))),
            adc.h1(Word.to_nat(p, Word.adc(p, at, bt, False{}, True{})), A, B, adc.le(p, at, bt, True{})))

# a sum of U32s is at most the sum of their numbers
def add.le(+x: U32, +y: U32) -> N.Le(U32.to_nat(U32.add(x, y)), Nat.add(U32.to_nat(x), U32.to_nat(y))):
  match x y:
    case U32{+a} U32{+b}:
      adc.le(32n, a, b, False{})

# the bit c under the word w less its top bit: at most c + 2w
def shl.put.le(+n: Nat, c: Bool, w: Word(n)) ->
  N.Le(Word.to_nat(n, Word.shl.put(n, c, w)), Nat.add(D.Nat.of(c), Nat.double(Word.to_nat(n, w)))):
  match n:
    case 0n:
      N.le_zero(Nat.add(D.Nat.of(c), Nat.double(Word.to_nat(0n, w))))
    case 1n+p:
      match c w:
        case False{} WCon{False{}, +t}:
          N.double_mono(Word.to_nat(p, Word.shl.put(p, False{}, t)), Nat.double(Word.to_nat(p, t)), shl.put.le(p, False{}, t))
        case True{} WCon{False{}, +t}:
          N.double_mono(Word.to_nat(p, Word.shl.put(p, False{}, t)), Nat.double(Word.to_nat(p, t)), shl.put.le(p, False{}, t))
        case False{} WCon{True{}, +t}:
          N.double_mono(Word.to_nat(p, Word.shl.put(p, True{}, t)), 1n+Nat.double(Word.to_nat(p, t)), shl.put.le(p, True{}, t))
        case True{} WCon{True{}, +t}:
          N.double_mono(Word.to_nat(p, Word.shl.put(p, True{}, t)), 1n+Nat.double(Word.to_nat(p, t)), shl.put.le(p, True{}, t))

# a shift left at most doubles a word
def shl.le(+n: Nat, w: Word(n)) -> N.Le(Word.to_nat(n, Word.shl(n, w)), Nat.double(Word.to_nat(n, w))):
  match n:
    case 0n:
      N.le_zero(Nat.double(Word.to_nat(0n, w)))
    case 1n+p:
      match w:
        case WCon{False{}, +t}:
          N.double_mono(Word.to_nat(p, Word.shl.put(p, False{}, t)), Nat.double(Word.to_nat(p, t)), shl.put.le(p, False{}, t))
        case WCon{True{}, +t}:
          N.double_mono(Word.to_nat(p, Word.shl.put(p, True{}, t)), 1n+Nat.double(Word.to_nat(p, t)), shl.put.le(p, True{}, t))

def ushl.le(+y: U32) -> N.Le(U32.to_nat(U32.shl(y)), Nat.double(U32.to_nat(y))):
  match y:
    case U32{+w}:
      shl.le(32n, w)

# k shifts left multiply by at most 2^k
def shln.le(+x: U32, +k: Nat) -> N.Le(U32.to_nat(U32.shln(x, k)), N.D(k, U32.to_nat(x))):
  match k:
    case 0n:
      N.le_refl(U32.to_nat(x))
    case 1n+q:
      +y = U32.shln(x, q)
      N.le_trans(U32.to_nat(U32.shl(y)), Nat.double(U32.to_nat(y)), N.D(1n+q, U32.to_nat(x)),
        ushl.le(y), N.double_mono(U32.to_nat(y), N.D(q, U32.to_nat(x)), shln.le(x, q)))

# a word shifted right with a 0 on top keeps its number
def pad.val(+p: Nat, t: Word(p)) -> {Word.to_nat(1n+p, Word.shr.pad(p, t)) == Word.to_nat(p, t) : Nat}:
  match p:
    case 0n:
      match t:
        case WNil{}:
          {==}
    case 1n+q:
      match t:
        case WCon{False{}, +r}:
          Equal.cong(Nat, Nat, v => Nat.double(v), Word.to_nat(1n+q, Word.shr.pad(q, r)), Word.to_nat(q, r), pad.val(q, r))
        case WCon{True{}, +r}:
          Equal.cong(Nat, Nat, v => 1n+Nat.double(v), Word.to_nat(1n+q, Word.shr.pad(q, r)), Word.to_nat(q, r), pad.val(q, r))

# 2 (x >> 1) <= x
def shr.le(x: U32) -> N.Le(Nat.double(U32.to_nat(U32.shr(x))), U32.to_nat(x)):
  match x:
    case U32{w}:
      match w:
        case WCon{False{}, +t}:
          +a = Nat.double(Word.to_nat(31n, t))
          N.le_rw_l(a, Nat.double(Word.to_nat(32n, Word.shr.pad(31n, t))), a,
            Equal.cong(Nat, Nat, v => Nat.double(v), Word.to_nat(31n, t), Word.to_nat(32n, Word.shr.pad(31n, t)),
              Equal.sym(Nat, Word.to_nat(32n, Word.shr.pad(31n, t)), Word.to_nat(31n, t), pad.val(31n, t))),
            N.le_refl(a))
        case WCon{True{}, +t}:
          +a = Nat.double(Word.to_nat(31n, t))
          N.le_rw_l(a, Nat.double(Word.to_nat(32n, Word.shr.pad(31n, t))), 1n+a,
            Equal.cong(Nat, Nat, v => Nat.double(v), Word.to_nat(31n, t), Word.to_nat(32n, Word.shr.pad(31n, t)),
              Equal.sym(Nat, Word.to_nat(32n, Word.shr.pad(31n, t)), Word.to_nat(31n, t), pad.val(31n, t))),
            N.le_succ(a, a, N.le_refl(a)))

# x >> (1 + q) = (x >> 1) >> q
def shrn.succ(+x: U32, q: Nat) -> {U32.shrn(x, 1n+q) == U32.shrn(U32.shr(x), q) : U32}:
  match q:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(U32, U32, y => U32.shr(y), U32.shrn(x, 1n+p), U32.shrn(U32.shr(x), p), shrn.succ(x, p))

# 2^k (x >> k) <= x
def shrn.le(+k: Nat, +x: U32) -> N.Le(N.D(k, U32.to_nat(U32.shrn(x, k))), U32.to_nat(x)):
  match k:
    case 0n:
      N.le_refl(U32.to_nat(x))
    case 1n+q:
      +y = U32.shr(x)
      +a = Nat.double(N.D(q, U32.to_nat(U32.shrn(y, q))))
      +h = N.le_trans(a, Nat.double(U32.to_nat(y)), U32.to_nat(x),
        N.double_mono(N.D(q, U32.to_nat(U32.shrn(y, q))), U32.to_nat(y), shrn.le(q, y)), shr.le(x))
      N.le_rw_l(a, Nat.double(N.D(q, U32.to_nat(U32.shrn(x, 1n+q)))), U32.to_nat(x),
        Equal.cong(U32, Nat, z => Nat.double(N.D(q, U32.to_nat(z))), U32.shrn(y, q), U32.shrn(x, 1n+q),
          Equal.sym(U32, U32.shrn(x, 1n+q), U32.shrn(y, q), shrn.succ(x, q))), h)
# a comparison that is not at most EQ: y < x
def nle.of(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), h: {Cmp.is_le(c) == False{} : Bool}) -> N.Le(1n+y, x):
  match c:
    case LT{}:
      Bo.ft(N.Le(1n+y, x), h)
    case EQ{}:
      Bo.ft(N.Le(1n+y, x), h)
    case GT{}:
      r
# a comparison that is not LT: y <= x
def nlt.of(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), h: {Cmp.is_lt(c) == False{} : Bool}) -> N.Le(y, x):
  match c:
    case LT{}:
      Bo.ft(N.Le(y, x), h)
    case EQ{}:
      %Equal.sym(Nat, x, y, r) : N.Le(y, _)
      N.le_refl(y)
    case GT{}:
      N.weaken(y, x, r)
# min(m, k) is at most m
def min.le.l(b0: Bool, +m: U32, +k: U32, e: {U32.is_le(m, k) == b0 : Bool}) -> N.Le(U32.to_nat(Wa.Wasm.min.if(b0, m, k)), U32.to_nat(m)):
  match b0:
    case True{}:
      N.le_refl(U32.to_nat(m))
    case False{}:
      N.weaken(U32.to_nat(k), U32.to_nat(m), nle.of(U32.cmp(m, k), U32.to_nat(m), U32.to_nat(k), U.rel(m, k), e))
# the minimum of the limit and 65536, as min.case gives it
def lim.min(+L: U32) -> {Wa.Wasm.min.if(U32.is_le(L, 65536), L, 65536) == Wa.Wasm.min(L, 65536) : U32}:
  {==}
# the bytes of a limit, as min.case gives its pages
def lim.eq(+L: U32) -> {N.D(16n, U32.to_nat(Wa.Wasm.min.if(U32.is_le(L, 65536), L, 65536))) == D.Lim.bytes(L) : Nat}:
  {==}
# a limit's bytes are at most 2^32
def lim.le(+L: U32) -> N.Le(D.Lim.bytes(L), N.D(32n, 1n)):
  +y = U32.to_nat(Wa.Wasm.min.if(U32.is_le(L, 65536), L, 65536))
  +h2 = N.le_rw_r(y, U32.to_nat(65536), N.D(16n, 1n), N.val_65536(), N.min.case(U32.is_le(L, 65536), L, 65536, {==}))
  N.le_rw_l(N.D(16n, y), D.Lim.bytes(L), N.D(32n, 1n), lim.eq(L),
    N.le_rw_r(N.D(16n, y), N.D(16n, N.D(16n, 1n)), N.D(32n, 1n), N.D_add(16n, 16n, 32n, 1n, {==}), Dk.mono(16n, y, N.D(16n, 1n), h2)))
# a limit's bytes are at most those of its pages
def lim.le.pages(+L: U32) -> N.Le(D.Lim.bytes(L), N.D(16n, U32.to_nat(L))):
  +y = U32.to_nat(Wa.Wasm.min.if(U32.is_le(L, 65536), L, 65536))
  N.le_rw_l(N.D(16n, y), D.Lim.bytes(L), N.D(16n, U32.to_nat(L)), lim.eq(L),
    Dk.mono(16n, y, U32.to_nat(L), min.le.l(U32.is_le(L, 65536), L, 65536, {==})))
# a + (k + b) = k + (a + b)
def add.k(+a: Nat, +k: Nat, +b: Nat) -> {Nat.add(a, Nat.add(k, b)) == Nat.add(k, Nat.add(a, b)) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+q:
      %add.k(a, q, b) : {Nat.add(a, 1n+Nat.add(q, b)) == 1n+_ : Nat}
      N.add_succ_r(a, Nat.add(q, b))
# 16x + 4x = 20x
def t20.shifts(+x: Nat) -> {Nat.add(N.D(4n, x), N.D(2n, x)) == T20(x) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(N.D(4n, p), Nat.add(4n, N.D(2n, p))), Nat.add(4n, Nat.add(N.D(4n, p), N.D(2n, p))),
        add.k(N.D(4n, p), 4n, N.D(2n, p))) : {16n+_ == 20n+T20(p) : Nat}
      %Equal.sym(Nat, Nat.add(N.D(4n, p), N.D(2n, p)), T20(p), t20.shifts(p)) : {20n+_ == 20n+T20(p) : Nat}
      {==}
# k × (1 + y) = k + k × y
def mul.k(+k: Nat, +y: Nat) -> {Nat.mul(k, 1n+y) == Nat.add(k, Nat.mul(k, y)) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+q:
      %Equal.sym(Nat, Nat.mul(q, 1n+y), Nat.add(q, Nat.mul(q, y)), mul.k(q, y)) :
        {1n+Nat.add(y, _) == 1n+Nat.add(q, Nat.add(y, Nat.mul(q, y))) : Nat}
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(y, Nat.add(q, Nat.mul(q, y))), Nat.add(q, Nat.add(y, Nat.mul(q, y))),
        N.add_swap(y, q, Nat.mul(q, y)))
# 20 × y, as T20
def mul20(+y: Nat) -> {Nat.mul(20n, y) == T20(y) : Nat}:
  match y:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.mul(20n, 1n+p), Nat.add(20n, Nat.mul(20n, p)), mul.k(20n, p)) : {_ == 20n+T20(p) : Nat}
      %Equal.sym(Nat, Nat.mul(20n, p), T20(p), mul20(p)) : {Nat.add(20n, _) == 20n+T20(p) : Nat}
      {==}
# the cell's place, 20 nx, as the code computes it: at most 20 nx
def at.le(+nx: U32) -> N.Le(U32.to_nat(Cr.Cir.at(nx)), T20(U32.to_nat(nx))):
  +x = U32.to_nat(nx)
  N.le_rw_r(U32.to_nat(Cr.Cir.at(nx)), Nat.add(N.D(4n, x), N.D(2n, x)), T20(x), t20.shifts(x),
    N.le_trans(U32.to_nat(Cr.Cir.at(nx)), Nat.add(U32.to_nat(U32.shln(nx, 4n)), U32.to_nat(U32.shln(nx, 2n))), Nat.add(N.D(4n, x), N.D(2n, x)),
      add.le(U32.shln(nx, 4n), U32.shln(nx, 2n)),
      N.add_mono(U32.to_nat(U32.shln(nx, 4n)), N.D(4n, x), U32.to_nat(U32.shln(nx, 2n)), N.D(2n, x), shln.le(nx, 4n), shln.le(nx, 2n))))

def M.T(x: Maybe<&2, U32>) -> Data:
  match x:
    case Some{_}:
      Unit
    case None{}:
      Empty

def ms.ne(-x: U32, h: {Some{x} == None{} : Maybe<&2, U32>}) -> Empty:
  %h : M.T(_)
  Unit{}
# no room: the pages needed are more than the limit allows
def room.none(i: Bool, c: Bool, +p: U32, +nd: U32, h: {Cr.Cir.room.if(i, c, p, nd) == None{} : Maybe<&2, U32>}) -> {c == False{} : Bool}:
  match i c:
    case True{} _:
      Empty.absurd({c == False{} : Bool}, ms.ne(p, h))
    case False{} True{}:
      Empty.absurd({True{} == False{} : Bool}, ms.ne(nd, h))
    case False{} False{}:
      {==}
# out of memory at a new cell, for want of room: the limit's bytes are
# fewer than 20 (nx + 1)
def oom.room(+L: U32, +pg: U32, +nx: U32, h: {Cr.Cir.room(U32.add(Cr.Cir.at(nx), 19), pg, L) == None{} : Maybe<&2, U32>}) ->
  N.Le(1n+D.Lim.bytes(L), Nat.mul(20n, 1n+U32.to_nat(nx))):
  +b = U32.add(Cr.Cir.at(nx), 19)
  +sh = U32.shrn(b, 16n)
  +nd = U32.inc(sh)
  +L1 = U32.to_nat(L)
  +S1 = U32.to_nat(sh)
  +A = U32.to_nat(Cr.Cir.at(nx))
  +X = U32.to_nat(nx)
  +hc = room.none(U32.is_le(nd, pg), U32.is_le(nd, L), pg, nd, h)
  +h1 = nle.of(U32.cmp(nd, L), U32.to_nat(nd), L1, U.rel(nd, L), hc)
  +h2 = N.le_trans(1n+L1, U32.to_nat(nd), 1n+S1, h1, N.U32.inc_le(sh))
  +h3 = N.le_trans(N.D(16n, L1), N.D(16n, S1), U32.to_nat(b), Dk.mono(16n, L1, S1, h2), shrn.le(16n, b))
  +hb = N.le_rw_l(U32.to_nat(U32.add(19, Cr.Cir.at(nx))), U32.to_nat(b), 19n+A,
    Equal.cong(U32, Nat, z => U32.to_nat(z), U32.add(19, Cr.Cir.at(nx)), b, U32.add_comm(19, Cr.Cir.at(nx))), add.le(19, Cr.Cir.at(nx)))
  +h4 = N.le_trans(N.D(16n, L1), U32.to_nat(b), 19n+T20(X), h3, N.le_trans(U32.to_nat(b), 19n+A, 19n+T20(X), hb, at.le(nx)))
  N.le_rw_r(1n+D.Lim.bytes(L), T20(1n+X), Nat.mul(20n, 1n+X), Equal.sym(Nat, Nat.mul(20n, 1n+X), T20(1n+X), mul20(1n+X)),
    N.le_trans(D.Lim.bytes(L), N.D(16n, L1), 19n+T20(X), lim.le.pages(L), h4))

# 1 + B <= 20 (1 + X) when B <= 16 + 20 P and P <= X (over variables)
def big.le(+B: Nat, +D: Nat, +P: Nat, +X: Nat, hb: N.Le(B, D), hp: {Nat.add(16n, T20(P)) == D : Nat}, hx: N.Le(P, X)) ->
  N.Le(1n+B, Nat.mul(20n, 1n+X)):
  +hw = N.le_rw_r(B, D, Nat.add(16n, T20(P)), Equal.sym(Nat, Nat.add(16n, T20(P)), D, hp), hb)
  N.le_rw_r(1n+B, T20(1n+X), Nat.mul(20n, 1n+X), Equal.sym(Nat, Nat.mul(20n, 1n+X), T20(1n+X), mul20(1n+X)),
    N.le_trans(1n+B, 17n+T20(P), 20n+T20(X), hw,
      N.le_trans(17n+T20(P), 20n+T20(P), 20n+T20(X), N.le_add_l(3n, T20(P)), t20.mono(P, X, hx))))

# out of memory at a new cell, next being 214748364 or more: 20 (nx + 1) is
# past 2^32
def oom.big(+L: U32, +nx: U32, h: {U32.is_lt(nx, 214748364) == False{} : Bool}) ->
  N.Le(1n+D.Lim.bytes(L), Nat.mul(20n, 1n+U32.to_nat(nx))):
  +X = U32.to_nat(nx)
  +hx = N.le_rw_l(U32.to_nat(214748364), Pat(7n), X, lit.pat(), nlt.of(U32.cmp(nx, 214748364), X, U32.to_nat(214748364), U.rel(nx, 214748364), h))
  big.le(D.Lim.bytes(L), N.D(32n, 1n), Pat(7n), X, lim.le(L), hP(), hx)

# The allocation
# --------------
#
# M.alloc takes the cell nx (Cir's alloc, all zeros) when the pend list is
# empty, else the first of the pend list, whose parts then lose a pointer.
# The lemmas below follow the n cells from o (Inc: the k-th of them), and
# what AL, Kept and the pointers say before and after a store.

# 2a <= 2b gives a <= b
def Ar.dle(a: Nat, b: Nat, h: N.Le(Nat.double(a), Nat.double(b))) -> N.Le(a, b):
  match a:
    case 0n:
      N.le_zero(b)
    case 1n+p:
      match b:
        case 0n:
          Empty.absurd(N.Le(1n+p, 0n), h)
        case 1n+q:
          Ar.dle(p, q, h)

# 2 + 2a <= 1 + 2b gives 1 + a <= b
def Ar.dle1(a: Nat, b: Nat, h: N.Le(2n+Nat.double(a), 1n+Nat.double(b))) -> N.Le(1n+a, b):
  match a:
    case 0n:
      match b:
        case 0n:
          Empty.absurd(N.Le(1n, 0n), h)
        case 1n+q:
          N.le_zero(q)
    case 1n+p:
      match b:
        case 0n:
          Empty.absurd(N.Le(2n+p, 0n), h)
        case 1n+q:
          Ar.dle1(p, q, h)

# a word below another one adds 1 when it grows
def Ar.w.inc(+n: Nat, w: Word(n), w2: Word(n), h: N.Le(1n+Word.to_nat(n, w), Word.to_nat(n, w2))) ->
  {Word.to_nat(n, Word.inc(n, w)) == 1n+Word.to_nat(n, w) : Nat}:
  match n:
    case 0n:
      match w w2:
        case WNil{} WNil{}:
          Empty.absurd({0n == 1n : Nat}, h)
    case 1n+p:
      match w w2:
        case WCon{False{}, t} _:
          {==}
        case WCon{True{}, +t} WCon{False{}, +t2}:
          %Equal.sym(Nat, Word.to_nat(p, Word.inc(p, t)), 1n+Word.to_nat(p, t), Ar.w.inc(p, t, t2, Ar.dle(1n+Word.to_nat(p, t), Word.to_nat(p, t2), h))) :
            {Nat.double(_) == 2n+Nat.double(Word.to_nat(p, t)) : Nat}
          {==}
        case WCon{True{}, +t} WCon{True{}, +t2}:
          %Equal.sym(Nat, Word.to_nat(p, Word.inc(p, t)), 1n+Word.to_nat(p, t), Ar.w.inc(p, t, t2, Ar.dle1(Word.to_nat(p, t), Word.to_nat(p, t2), h))) :
            {Nat.double(_) == 2n+Nat.double(Word.to_nat(p, t)) : Nat}
          {==}

# a U32 below another one adds 1 when it grows
def Ar.u.inc(+a: U32, +b: U32, h: N.Le(1n+U32.to_nat(a), U32.to_nat(b))) -> {U32.to_nat(U32.inc(a)) == 1n+U32.to_nat(a) : Nat}:
  match a b:
    case U32{x} U32{y}:
      Ar.w.inc(32n, x, y, h)

# a + (b - a) = b, when a <= b
def Ar.sub.add(+a: Nat, +b: Nat, h: N.Le(a, b)) -> {Nat.add(a, Nat.sub(b, a)) == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.add(1n+p, Nat.sub(0n, 1n+p)) == 0n : Nat}, h)
    case 1n+(+p) 1n+(+q):
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(p, Nat.sub(q, p)), q, Ar.sub.add(p, q, h))

# (1 + a) - b = 1 + (a - b), when b <= a
def Ar.sub.succ(+a: Nat, +b: Nat, h: N.Le(b, a)) -> {Nat.sub(1n+a, b) == 1n+Nat.sub(a, b) : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 1n+p 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({Nat.sub(1n, 1n+q) == 1n+Nat.sub(0n, 1n+q) : Nat}, h)
    case 1n+(+p) 1n+(+q):
      Ar.sub.succ(p, q, h)

# U32s of the same number are equal
def Ar.inj.of(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), e: {x == y : Nat}) -> {c == EQ{} : Cmp}:
  match c:
    case LT{}:
      Empty.absurd({LT{} == EQ{} : Cmp}, N.not_succ_le(y, (%e : N.Le(1n+_, y); r)))
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({GT{} == EQ{} : Cmp}, N.not_succ_le(y, (%e : N.Le(1n+y, _); r)))

def Ar.inj(+a: U32, +b: U32, e: {U32.to_nat(a) == U32.to_nat(b) : Nat}) -> {a == b : U32}:
  U.cmp_eq(a, b, Ar.inj.of(U32.cmp(a, b), U32.to_nat(a), U32.to_nat(b), U.rel(a, b), e))

# a cell below another is not it
def Ar.ne.of(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), h: N.Le(1n+x, y)) -> {Cmp.is_eq(c) == False{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({Cmp.is_eq(EQ{}) == False{} : Bool}, N.not_succ_le(y, (%r : N.Le(1n+_, y); h)))
    case GT{}:
      {==}

def Ar.ne(+a: U32, +b: U32, h: N.Le(1n+U32.to_nat(a), U32.to_nat(b))) -> {U32.is_eq(a, b) == False{} : Bool}:
  Ar.ne.of(U32.cmp(a, b), U32.to_nat(a), U32.to_nat(b), U.rel(a, b), h)

# the cell k cells after o
def Inc(k: Nat, +o: U32) -> U32:
  match k:
    case 0n:
      o
    case 1n+p:
      Inc(p, U32.inc(o))

# the k-th cell from o, below z, is o + k
def Ar.inc.nat(k: Nat, +o: U32, +z: U32, h: N.Le(Nat.add(U32.to_nat(o), k), U32.to_nat(z))) ->
  {U32.to_nat(Inc(k, o)) == Nat.add(U32.to_nat(o), k) : Nat}:
  match k:
    case 0n:
      Equal.sym(Nat, Nat.add(U32.to_nat(o), 0n), U32.to_nat(o), N.add_zero(U32.to_nat(o)))
    case 1n+(+p):
      +x = U32.to_nat(o)
      +h1 = N.le_rw_l(Nat.add(x, 1n+p), 1n+Nat.add(x, p), U32.to_nat(z), N.add_succ_r(x, p), h)
      +ei = Ar.u.inc(o, z, N.le_trans(1n+x, 1n+Nat.add(x, p), U32.to_nat(z), N.le_add_r(1n+x, p), h1))
      +ec = Equal.cong(Nat, Nat, y => Nat.add(y, p), U32.to_nat(U32.inc(o)), 1n+x, ei)
      +h2 = N.le_rw_l(1n+Nat.add(x, p), Nat.add(U32.to_nat(U32.inc(o)), p), U32.to_nat(z),
        Equal.sym(Nat, Nat.add(U32.to_nat(U32.inc(o)), p), 1n+Nat.add(x, p), ec), h1)
      Equal.trans(Nat, U32.to_nat(Inc(p, U32.inc(o))), Nat.add(U32.to_nat(U32.inc(o)), p), Nat.add(x, 1n+p),
        Ar.inc.nat(p, U32.inc(o), z, h2),
        Equal.trans(Nat, Nat.add(U32.to_nat(U32.inc(o)), p), 1n+Nat.add(x, p), Nat.add(x, 1n+p), ec,
          Equal.sym(Nat, Nat.add(x, 1n+p), 1n+Nat.add(x, p), N.add_succ_r(x, p))))

# the cell nx - F cells after F is nx
def Ar.inc.end(+F: U32, +nx: U32, h: {U32.is_le(F, nx) == True{} : Bool}) ->
  {Inc(Nat.sub(U32.to_nat(nx), U32.to_nat(F)), F) == nx : U32}:
  +n = Nat.sub(U32.to_nat(nx), U32.to_nat(F))
  +e = Ar.sub.add(U32.to_nat(F), U32.to_nat(nx), U.le(F, nx, h))
  Ar.inj(Inc(n, F), nx, Equal.trans(Nat, U32.to_nat(Inc(n, F)), Nat.add(U32.to_nat(F), n), U32.to_nat(nx),
    Ar.inc.nat(n, F, nx, N.le_rw_l(U32.to_nat(nx), Nat.add(U32.to_nat(F), n), U32.to_nat(nx),
      Equal.sym(Nat, Nat.add(U32.to_nat(F), n), U32.to_nat(nx), e), N.le_refl(U32.to_nat(nx)))), e))

# the cells from F to inc(nx): one more
def Ar.cnt.new(+F: U32, +nx: U32, hfn: {U32.is_le(F, nx) == True{} : Bool}, hb: N.Le(1n+U32.to_nat(nx), U32.to_nat(214748364))) ->
  {Nat.sub(U32.to_nat(U32.inc(nx)), U32.to_nat(F)) == 1n+Nat.sub(U32.to_nat(nx), U32.to_nat(F)) : Nat}:
  %Equal.sym(Nat, U32.to_nat(U32.inc(nx)), 1n+U32.to_nat(nx), Ar.u.inc(nx, 214748364, hb)) :
    {Nat.sub(_, U32.to_nat(F)) == 1n+Nat.sub(U32.to_nat(nx), U32.to_nat(F)) : Nat}
  Ar.sub.succ(U32.to_nat(nx), U32.to_nat(F), U.le(F, nx, hfn))

# each of the n cells from o is not z
def Ne(n: Nat, +o: U32, +z: U32) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(Bool.not(U32.is_eq(o, z)), Ne(p, U32.inc(o), z))

def Ar.ne.all(n: Nat, +o: U32, +z: U32, h: N.Le(Nat.add(U32.to_nat(o), n), U32.to_nat(z))) -> {Ne(n, o, z) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      +x = U32.to_nat(o)
      +h1 = N.le_rw_l(Nat.add(x, 1n+p), 1n+Nat.add(x, p), U32.to_nat(z), N.add_succ_r(x, p), h)
      +lt = N.le_trans(1n+x, 1n+Nat.add(x, p), U32.to_nat(z), N.le_add_r(1n+x, p), h1)
      +ei = Ar.u.inc(o, z, lt)
      +h2 = N.le_rw_l(1n+Nat.add(x, p), Nat.add(U32.to_nat(U32.inc(o)), p), U32.to_nat(z),
        Equal.sym(Nat, Nat.add(U32.to_nat(U32.inc(o)), p), 1n+Nat.add(x, p),
          Equal.cong(Nat, Nat, y => Nat.add(y, p), U32.to_nat(U32.inc(o)), 1n+x, ei)), h1)
      Bo.and_i(Bool.not(U32.is_eq(o, z)), Ne(p, U32.inc(o), z), Bo.not_i(U32.is_eq(o, z), Ar.ne(o, z, lt)),
        Ar.ne.all(p, U32.inc(o), z, h2))

# the n cells from F, below nx, are not nx
def Ar.ne.own(+F: U32, +nx: U32, hfn: {U32.is_le(F, nx) == True{} : Bool}) ->
  {Ne(Nat.sub(U32.to_nat(nx), U32.to_nat(F)), F, nx) == True{} : Bool}:
  +e = Ar.sub.add(U32.to_nat(F), U32.to_nat(nx), U.le(F, nx, hfn))
  Ar.ne.all(Nat.sub(U32.to_nat(nx), U32.to_nat(F)), F, nx,
    N.le_rw_l(U32.to_nat(nx), Nat.add(U32.to_nat(F), Nat.sub(U32.to_nat(nx), U32.to_nat(F))), U32.to_nat(nx),
      Equal.sym(Nat, Nat.add(U32.to_nat(F), Nat.sub(U32.to_nat(nx), U32.to_nat(F))), U32.to_nat(nx), e), N.le_refl(U32.to_nat(nx))))

# Bools
def Bo.and_true(a: Bool) -> {Bool.and(a, True{}) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def Bo.and_assoc(a: Bool, -b: Bool, -c: Bool) -> {Bool.and(a, Bool.and(b, c)) == Bool.and(Bool.and(a, b), c) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# a or b or (c and d), with c giving c2 and d giving d2
def Bo.or3(a: Bool, b: Bool, c: Bool, -d: Bool, -c2: Bool, -d2: Bool, h: {Bool.or(a, Bool.or(b, Bool.and(c, d))) == True{} : Bool},
  hc: {c == True{} : Bool} -> {c2 == True{} : Bool}, hd: {c == True{} : Bool} -> {d == True{} : Bool} -> {d2 == True{} : Bool}) ->
  {Bool.or(a, Bool.or(b, Bool.and(c2, d2))) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      match b:
        case True{}:
          {==}
        case False{}:
          match c:
            case True{}:
              Bo.and_i(c2, d2, hc({==}), hd({==}, h))
            case False{}:
              Bo.tf({Bool.or(False{}, Bool.or(False{}, Bool.and(c2, d2))) == True{} : Bool}, h)

# Nat.is_eq of a number and itself
def Na.eq_refl(a: Nat) -> {Nat.is_eq(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Na.eq_refl(p)

# The cells past the table
# ------------------------

# the table's cell of a term's tag, 272 + tg, is below 291
def Ar.tbl.lt(+tg: U32, e: {U32.is_lt(tg, 19) == True{} : Bool}) -> N.Le(1n+U32.to_nat(U32.add(272, tg)), 291n):
  N.le_trans(1n+U32.to_nat(U32.add(272, tg)), Nat.add(272n, 1n+U32.to_nat(tg)), 291n, add.le(272, tg),
    N.add_mono(272n, 272n, 1n+U32.to_nat(tg), U32.to_nat(19), N.le_refl(272n), U.lt(tg, 19, e)))

def Ar.tbl.ne(+tg: U32, +z: U32, e: {U32.is_lt(tg, 19) == True{} : Bool}, hz: N.Le(291n, U32.to_nat(z))) ->
  {U32.is_eq(U32.add(272, tg), z) == False{} : Bool}:
  Ar.ne(U32.add(272, tg), z, N.le_trans(1n+U32.to_nat(U32.add(272, tg)), 291n, U32.to_nat(z), Ar.tbl.lt(tg, e), hz))

# a tag below 32 of a garbage cell (18 or less, or 32 or more) is below 19
def Ar.t19.of(b: Bool, +t: U32, -hq: Bool, eb: {U32.is_le(t, 18) == b : Bool}, h32: {U32.is_lt(t, 32) == True{} : Bool},
  ht: {Bool.or(b, Bool.and(U32.is_le(32, t), hq)) == True{} : Bool}) -> {U32.is_lt(t, 19) == True{} : Bool}:
  match b:
    case True{}:
      U.lt_t(t, 19, U.le(t, 18, eb))
    case False{}:
      U.lt_ge(t, 32, {U32.is_lt(t, 19) == True{} : Bool}, h32, Bo.and_l(U32.is_le(32, t), hq, ht))

def Ar.t19(+t: U32, -hq: Bool, h32: {U32.is_lt(t, 32) == True{} : Bool},
  ht: {Bool.or(U32.is_le(t, 18), Bool.and(U32.is_le(32, t), hq)) == True{} : Bool}) -> {U32.is_lt(t, 19) == True{} : Bool}:
  Ar.t19.of(U32.is_le(t, 18), t, hq, {==}, h32, ht)

# The pointers after a store
# --------------------------

# Ps of the cell y at o, with the test b of a term's tag and the mask a
def PsK(b: Bool, +a: U32, +y: Cr.Cir.Cell, +Q: List<&2, U32>, +o: U32) -> List<&2, U32>:
  +f0 = Cr.Cir.Cell.get(0n, y)
  +tg = U32.and(f0, 63)
  Bool.pick(List<&2, U32>, b, D.Ps.term(a, Cr.Cir.Cell.get(2n, y), Cr.Cir.Cell.get(3n, y), Cr.Cir.Cell.get(4n, y)),
    Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_le(32, tg), U32.is_le(tg, 40)), Bool.not(D.Has(Q, o))),
      Con{Cr.Cir.Cell.get(2n, y), D.Ps.opt(U32.is_eq(tg, 38), Cr.Cir.Cell.get(3n, y), Nil{})},
      Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_eq(tg, 41), U32.is_ne(U32.and(f0, 4096), 0)), Bool.not(D.Has(Q, o))),
        [Cr.Cir.Cell.get(2n, y)], Nil{})))

def PsK.b(b: Bool, +a1: U32, +a2: U32, +y: Cr.Cir.Cell, +Q: List<&2, U32>, +o: U32, e: {b == True{} : Bool} -> {a1 == a2 : U32}) ->
  {PsK(b, a1, y, Q, o) == PsK(b, a2, y, Q, o) : List<&2, U32>}:
  match b:
    case True{}:
      %e({==}) : {PsK(True{}, a1, y, Q, o) == PsK(True{}, _, y, Q, o) : List<&2, U32>}
      {==}
    case False{}:
      {==}

# a store to z, past the table, keeps Ps of another cell o
def ps.set(+m: Cr.Cir.Cells, +z: U32, +x: Cr.Cir.Cell, +Q: List<&2, U32>, +o: U32, ne: {U32.is_eq(o, z) == False{} : Bool},
  +hz: N.Le(291n, U32.to_nat(z))) -> {D.Ps(Cr.Cir.Cells.set(m, z, x), Q, o) == D.Ps(m, Q, o) : List<&2, U32>}:
  +M2 = Cr.Cir.Cells.set(m, z, x)
  +y = Cr.Cir.Cells.get(m, o)
  +tg = U32.and(Cr.Cir.Cell.get(0n, y), 63)
  %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, o), y, Cl.get_ne(m, o, z, x, ne)) :
    {PsK(U32.is_lt(U32.and(Cr.Cir.Cell.get(0n, _), 63), 19), Cr.Cir.Cell.get(2n, Cr.Cir.Cells.get(M2, U32.add(272, U32.and(Cr.Cir.Cell.get(0n, _), 63)))),
      _, Q, o) == D.Ps(m, Q, o) : List<&2, U32>}
  PsK.b(U32.is_lt(tg, 19), D.Fd(2n, M2, U32.add(272, tg)), D.Fd(2n, m, U32.add(272, tg)), y, Q, o,
    e => Equal.cong(Cr.Cir.Cell, U32, w => Cr.Cir.Cell.get(2n, w), Cr.Cir.Cells.get(M2, U32.add(272, tg)), Cr.Cir.Cells.get(m, U32.add(272, tg)),
      Cl.get_ne(m, U32.add(272, tg), z, x, Ar.tbl.ne(tg, z, e, hz))))

# a cell set to zeros, past the table, holds no pointer
def ps.zero(+m: Cr.Cir.Cells, +z: U32, +Q: List<&2, U32>, t0: {Cr.Cir.Cells.get(m, 272) == Cr.Cir.Cell{0, 0, 0, 0, 0} : Cr.Cir.Cell},
  hz: N.Le(291n, U32.to_nat(z))) -> {D.Ps(Cr.Cir.Cells.set(m, z, Cr.Cir.Cell.zero()), Q, z) == Nil{} : List<&2, U32>}:
  +M2 = Cr.Cir.Cells.set(m, z, Cr.Cir.Cell.zero())
  %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, z), Cr.Cir.Cell.zero(), Cl.get_set(m, z, Cr.Cir.Cell.zero())) :
    {PsK(U32.is_lt(U32.and(Cr.Cir.Cell.get(0n, _), 63), 19), Cr.Cir.Cell.get(2n, Cr.Cir.Cells.get(M2, U32.add(272, U32.and(Cr.Cir.Cell.get(0n, _), 63)))),
      _, Q, z) == Nil{} : List<&2, U32>}
  %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, 272), Cr.Cir.Cells.get(m, 272),
    Cl.get_ne(m, 272, z, Cr.Cir.Cell.zero(), Ar.ne(272, z, N.le_trans(1n+U32.to_nat(272), 291n, U32.to_nat(z), Unit{}, hz)))) :
    {D.Ps.term(Cr.Cir.Cell.get(2n, _), 0, 0, 0) == Nil{} : List<&2, U32>}
  %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(m, 272), Cr.Cir.Cell{0, 0, 0, 0, 0}, t0) :
    {D.Ps.term(Cr.Cir.Cell.get(2n, _), 0, 0, 0) == Nil{} : List<&2, U32>}
  {==}

# a store to z, past the table, keeps the pointers of the n cells from o,
# none of them z
def pc.set(n: Nat, +m: Cr.Cir.Cells, +z: U32, +x: Cr.Cir.Cell, +Q: List<&2, U32>, +o: U32, +c: U32,
  +hn: {Ne(n, o, z) == True{} : Bool}, +hz: N.Le(291n, U32.to_nat(z))) ->
  {D.Pc(n, Cr.Cir.Cells.set(m, z, x), Q, o, c) == D.Pc(n, m, Q, o, c) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      +M2 = Cr.Cir.Cells.set(m, z, x)
      +ne = Bo.not_t(U32.is_eq(o, z), Bo.and_l(Bool.not(U32.is_eq(o, z)), Ne(p, U32.inc(o), z), hn))
      %Equal.sym(List<&2, U32>, D.Ps(M2, Q, o), D.Ps(m, Q, o), ps.set(m, z, x, Q, o, ne, hz)) :
        {Nat.add(D.Occ(_, c), D.Pc(p, M2, Q, U32.inc(o), c)) == Nat.add(D.Occ(D.Ps(m, Q, o), c), D.Pc(p, m, Q, U32.inc(o), c)) : Nat}
      %Equal.sym(Nat, D.Pc(p, M2, Q, U32.inc(o), c), D.Pc(p, m, Q, U32.inc(o), c),
        pc.set(p, m, z, x, Q, U32.inc(o), c, Bo.and_r(Bool.not(U32.is_eq(o, z)), Ne(p, U32.inc(o), z), hn), hz)) :
        {Nat.add(D.Occ(D.Ps(m, Q, o), c), _) == Nat.add(D.Occ(D.Ps(m, Q, o), c), D.Pc(p, m, Q, U32.inc(o), c)) : Nat}
      {==}

# the pointers of n + 1 cells: of the n first, and of the last
def pc.snoc(n: Nat, +m: Cr.Cir.Cells, +Q: List<&2, U32>, +o: U32, +c: U32) ->
  {D.Pc(1n+n, m, Q, o, c) == Nat.add(D.Pc(n, m, Q, o, c), D.Occ(D.Ps(m, Q, Inc(n, o)), c)) : Nat}:
  match n:
    case 0n:
      N.add_zero(D.Occ(D.Ps(m, Q, o), c))
    case 1n+(+p):
      +A = D.Occ(D.Ps(m, Q, o), c)
      +B = D.Pc(p, m, Q, U32.inc(o), c)
      +C = D.Occ(D.Ps(m, Q, Inc(p, U32.inc(o))), c)
      %Equal.sym(Nat, D.Pc(1n+p, m, Q, U32.inc(o), c), Nat.add(B, C), pc.snoc(p, m, Q, U32.inc(o), c)) :
        {Nat.add(A, _) == Nat.add(Nat.add(A, B), C) : Nat}
      Equal.sym(Nat, Nat.add(Nat.add(A, B), C), Nat.add(A, Nat.add(B, C)), N.add_assoc(A, B, C))

# the pointers of the cells from F to nx, and of the new cell nx, set to
# zeros: the same
def pc.new(+m: Cr.Cir.Cells, +F: U32, +nx: U32, +Q: List<&2, U32>, +c: U32,
  +t0: {Cr.Cir.Cells.get(m, 272) == Cr.Cir.Cell{0, 0, 0, 0, 0} : Cr.Cir.Cell}, +hz: N.Le(291n, U32.to_nat(nx)),
  +hfn: {U32.is_le(F, nx) == True{} : Bool}) ->
  {D.Pc(1n+Nat.sub(U32.to_nat(nx), U32.to_nat(F)), Cr.Cir.Cells.set(m, nx, Cr.Cir.Cell.zero()), Q, F, c) ==
    D.Pc(Nat.sub(U32.to_nat(nx), U32.to_nat(F)), m, Q, F, c) : Nat}:
  +n = Nat.sub(U32.to_nat(nx), U32.to_nat(F))
  +M2 = Cr.Cir.Cells.set(m, nx, Cr.Cir.Cell.zero())
  %Equal.sym(Nat, D.Pc(1n+n, M2, Q, F, c), Nat.add(D.Pc(n, M2, Q, F, c), D.Occ(D.Ps(M2, Q, Inc(n, F)), c)), pc.snoc(n, M2, Q, F, c)) :
    {_ == D.Pc(n, m, Q, F, c) : Nat}
  %Equal.sym(U32, Inc(n, F), nx, Ar.inc.end(F, nx, hfn)) :
    {Nat.add(D.Pc(n, M2, Q, F, c), D.Occ(D.Ps(M2, Q, _), c)) == D.Pc(n, m, Q, F, c) : Nat}
  %Equal.sym(List<&2, U32>, D.Ps(M2, Q, nx), Nil{}, ps.zero(m, nx, Q, t0, hz)) :
    {Nat.add(D.Pc(n, M2, Q, F, c), D.Occ(_, c)) == D.Pc(n, m, Q, F, c) : Nat}
  %Equal.sym(Nat, D.Pc(n, M2, Q, F, c), D.Pc(n, m, Q, F, c), pc.set(n, m, nx, Cr.Cir.Cell.zero(), Q, F, c, Ar.ne.own(F, nx, hfn), hz)) :
    {Nat.add(_, 0n) == D.Pc(n, m, Q, F, c) : Nat}
  N.add_zero(D.Pc(n, m, Q, F, c))

# Ow of the cell y, with the test b of a tag below 32 and the mask a
def OwK(b: Bool, +a: U32, +y: Cr.Cir.Cell, +c: U32) -> Nat:
  +am = Bool.pick(U32, b, a, 0)
  Nat.add(D.Nat.of(Bool.and(U32.is_ne(U32.and(am, 1), 0), U32.is_eq(Cr.Cir.Cell.get(2n, y), c))),
    Nat.add(D.Nat.of(Bool.and(U32.is_ne(U32.and(am, 2), 0), U32.is_eq(Cr.Cir.Cell.get(3n, y), c))),
      D.Nat.of(Bool.and(U32.is_ne(U32.and(am, 4), 0), U32.is_eq(Cr.Cir.Cell.get(4n, y), c)))))

def OwK.b(b: Bool, +a1: U32, +a2: U32, +y: Cr.Cir.Cell, +c: U32, e: {b == True{} : Bool} -> {a1 == a2 : U32}) ->
  {OwK(b, a1, y, c) == OwK(b, a2, y, c) : Nat}:
  match b:
    case True{}:
      %e({==}) : {OwK(True{}, a1, y, c) == OwK(True{}, _, y, c) : Nat}
      {==}
    case False{}:
      {==}

# a store to z, past the table, keeps Ow of another cell o of a garbage
# cell's tag
def ow.set(+m: Cr.Cir.Cells, +z: U32, +x: Cr.Cir.Cell, +o: U32, +c: U32, -hq: Bool, ne: {U32.is_eq(o, z) == False{} : Bool},
  ht: {Bool.or(U32.is_le(U32.and(D.Fd(0n, m, o), 63), 18), Bool.and(U32.is_le(32, U32.and(D.Fd(0n, m, o), 63)), hq)) == True{} : Bool},
  +hz: N.Le(291n, U32.to_nat(z))) -> {D.Ow(Cr.Cir.Cells.set(m, z, x), o, c) == D.Ow(m, o, c) : Nat}:
  +M2 = Cr.Cir.Cells.set(m, z, x)
  +y = Cr.Cir.Cells.get(m, o)
  +t = U32.and(Cr.Cir.Cell.get(0n, y), 63)
  %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, o), y, Cl.get_ne(m, o, z, x, ne)) :
    {OwK(U32.is_lt(U32.and(Cr.Cir.Cell.get(0n, _), 63), 32), Cr.Cir.Cell.get(2n, Cr.Cir.Cells.get(M2, U32.add(272, U32.and(Cr.Cir.Cell.get(0n, _), 63)))),
      _, c) == D.Ow(m, o, c) : Nat}
  OwK.b(U32.is_lt(t, 32), D.Fd(2n, M2, U32.add(272, t)), D.Fd(2n, m, U32.add(272, t)), y, c,
    e => Equal.cong(Cr.Cir.Cell, U32, w => Cr.Cir.Cell.get(2n, w), Cr.Cir.Cells.get(M2, U32.add(272, t)), Cr.Cir.Cells.get(m, U32.add(272, t)),
      Cl.get_ne(m, U32.add(272, t), z, x, Ar.tbl.ne(t, z, Ar.t19(t, hq, e, ht), hz))))

# The parts of AL
# ---------------

# a garbage cell's own facts, parts and counts, as AL.cells has them
def AL.hd(+m: Cr.Cir.Cells, +Q: List<&2, U32>, +o: U32, +F: U32, +N: U32) -> Bool:
  +tg = U32.and(D.Fd(0n, m, o), 63)
  Bool.and(Bool.and(Bool.and(U32.is_le(F, o), U32.is_lt(o, N)), Bool.not(D.Stc(m, o))),
    Bool.or(U32.is_le(tg, 18), Bool.and(U32.is_le(32, tg), D.Has(Q, o))))

def AL.pt(+m: Cr.Cir.Cells, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +o: U32, +K: U32, +F: U32, +N: U32) -> Bool:
  +am = D.Am(m, o)
  +z = D.Zz(zs, o)
  Bool.and(D.AL.part(m, P, zs, z, am, 1, D.Fd(2n, m, o), K, F, N),
    Bool.and(D.AL.part(m, P, zs, z, am, 2, D.Fd(3n, m, o), K, F, N), D.AL.part(m, P, zs, z, am, 4, D.Fd(4n, m, o), K, F, N)))

def AL.ct(+m: Cr.Cir.Cells, +P: List<&2, U32>, +Q: List<&2, U32>, +o: U32, +F: U32, +N: U32) -> Bool:
  +pp = D.Pp(P, m, o)
  Bool.and(Nat.is_eq(D.Pc(Nat.sub(U32.to_nat(N), U32.to_nat(F)), m, Q, F, o), pp),
    Bool.pick(Bool, D.Has(Q, o), Nat.is_eq(pp, 0n), Bool.and(Nat.is_eq(pp, U32.to_nat(D.Fd(1n, m, o))), Nat.is_lt(0n, pp))))

# AL.cells of a cell and the rest, by its parts
def al.hd(+o: U32, -rest: List<&2, U32>, +m: Cr.Cir.Cells, +P: List<&2, U32>, +Q: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32,
  +N: U32, h: {D.AL.cells(Con{o, rest}, m, P, Q, zs, K, F, N) == True{} : Bool}) -> {AL.hd(m, Q, o, F, N) == True{} : Bool}:
  Bo.and_l(AL.hd(m, Q, o, F, N), Bool.and(AL.pt(m, P, zs, o, K, F, N), Bool.and(AL.ct(m, P, Q, o, F, N), D.AL.cells(rest, m, P, Q, zs, K, F, N))), h)

def al.pt(+o: U32, +rest: List<&2, U32>, +m: Cr.Cir.Cells, +P: List<&2, U32>, +Q: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32,
  +N: U32, h: {D.AL.cells(Con{o, rest}, m, P, Q, zs, K, F, N) == True{} : Bool}) -> {AL.pt(m, P, zs, o, K, F, N) == True{} : Bool}:
  Bo.and_l(AL.pt(m, P, zs, o, K, F, N), Bool.and(AL.ct(m, P, Q, o, F, N), D.AL.cells(rest, m, P, Q, zs, K, F, N)),
    Bo.and_r(AL.hd(m, Q, o, F, N), Bool.and(AL.pt(m, P, zs, o, K, F, N), Bool.and(AL.ct(m, P, Q, o, F, N), D.AL.cells(rest, m, P, Q, zs, K, F, N))), h))

def al.ct(+o: U32, +rest: List<&2, U32>, +m: Cr.Cir.Cells, +P: List<&2, U32>, +Q: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32,
  +N: U32, h: {D.AL.cells(Con{o, rest}, m, P, Q, zs, K, F, N) == True{} : Bool}) -> {AL.ct(m, P, Q, o, F, N) == True{} : Bool}:
  Bo.and_l(AL.ct(m, P, Q, o, F, N), D.AL.cells(rest, m, P, Q, zs, K, F, N),
    Bo.and_r(AL.pt(m, P, zs, o, K, F, N), Bool.and(AL.ct(m, P, Q, o, F, N), D.AL.cells(rest, m, P, Q, zs, K, F, N)),
      Bo.and_r(AL.hd(m, Q, o, F, N), Bool.and(AL.pt(m, P, zs, o, K, F, N), Bool.and(AL.ct(m, P, Q, o, F, N), D.AL.cells(rest, m, P, Q, zs, K, F, N))), h)))

def al.rest(+o: U32, +rest: List<&2, U32>, +m: Cr.Cir.Cells, +P: List<&2, U32>, +Q: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32,
  +N: U32, h: {D.AL.cells(Con{o, rest}, m, P, Q, zs, K, F, N) == True{} : Bool}) -> {D.AL.cells(rest, m, P, Q, zs, K, F, N) == True{} : Bool}:
  Bo.and_r(AL.ct(m, P, Q, o, F, N), D.AL.cells(rest, m, P, Q, zs, K, F, N),
    Bo.and_r(AL.pt(m, P, zs, o, K, F, N), Bool.and(AL.ct(m, P, Q, o, F, N), D.AL.cells(rest, m, P, Q, zs, K, F, N)),
      Bo.and_r(AL.hd(m, Q, o, F, N), Bool.and(AL.pt(m, P, zs, o, K, F, N), Bool.and(AL.ct(m, P, Q, o, F, N), D.AL.cells(rest, m, P, Q, zs, K, F, N))), h)))

def al.cons(+o: U32, rest: List<&2, U32>, +m: Cr.Cir.Cells, +P: List<&2, U32>, +Q: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32,
  +N: U32, h1: {AL.hd(m, Q, o, F, N) == True{} : Bool}, h2: {AL.pt(m, P, zs, o, K, F, N) == True{} : Bool},
  h3: {AL.ct(m, P, Q, o, F, N) == True{} : Bool}, h4: {D.AL.cells(rest, m, P, Q, zs, K, F, N) == True{} : Bool}) ->
  {D.AL.cells(Con{o, rest}, m, P, Q, zs, K, F, N) == True{} : Bool}:
  Bo.and_i(AL.hd(m, Q, o, F, N), Bool.and(AL.pt(m, P, zs, o, K, F, N), Bool.and(AL.ct(m, P, Q, o, F, N), D.AL.cells(rest, m, P, Q, zs, K, F, N))), h1,
    Bo.and_i(AL.pt(m, P, zs, o, K, F, N), Bool.and(AL.ct(m, P, Q, o, F, N), D.AL.cells(rest, m, P, Q, zs, K, F, N)), h2,
      Bo.and_i(AL.ct(m, P, Q, o, F, N), D.AL.cells(rest, m, P, Q, zs, K, F, N), h3, h4)))

# the parts of AL.hd
def al.hd.lt(+m: Cr.Cir.Cells, +Q: List<&2, U32>, +o: U32, +F: U32, +N: U32, h: {AL.hd(m, Q, o, F, N) == True{} : Bool}) ->
  {U32.is_lt(o, N) == True{} : Bool}:
  +tg = U32.and(D.Fd(0n, m, o), 63)
  Bo.and_r(U32.is_le(F, o), U32.is_lt(o, N), Bo.and_l(Bool.and(U32.is_le(F, o), U32.is_lt(o, N)), Bool.not(D.Stc(m, o)),
    Bo.and_l(Bool.and(Bool.and(U32.is_le(F, o), U32.is_lt(o, N)), Bool.not(D.Stc(m, o))), Bool.or(U32.is_le(tg, 18), Bool.and(U32.is_le(32, tg), D.Has(Q, o))), h)))

def al.hd.tg(+m: Cr.Cir.Cells, +Q: List<&2, U32>, +o: U32, +F: U32, +N: U32, h: {AL.hd(m, Q, o, F, N) == True{} : Bool}) ->
  {Bool.or(U32.is_le(U32.and(D.Fd(0n, m, o), 63), 18), Bool.and(U32.is_le(32, U32.and(D.Fd(0n, m, o), 63)), D.Has(Q, o))) == True{} : Bool}:
  +tg = U32.and(D.Fd(0n, m, o), 63)
  Bo.and_r(Bool.and(Bool.and(U32.is_le(F, o), U32.is_lt(o, N)), Bool.not(D.Stc(m, o))), Bool.or(U32.is_le(tg, 18), Bool.and(U32.is_le(32, tg), D.Has(Q, o))), h)

# a store to z, past the table and next N, keeps the garbage's pointers Pp
def pp.set(os: List<&2, U32>, +m: Cr.Cir.Cells, +P: List<&2, U32>, +Q: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32,
  +N: U32, +z: U32, +x: Cr.Cir.Cell, +c: U32, h: {D.AL.cells(os, m, P, Q, zs, K, F, N) == True{} : Bool},
  +hzn: N.Le(U32.to_nat(N), U32.to_nat(z)), +hz: N.Le(291n, U32.to_nat(z))) ->
  {D.Pp(os, Cr.Cir.Cells.set(m, z, x), c) == D.Pp(os, m, c) : Nat}:
  match os:
    case Nil{}:
      {==}
    case Con{+o, +rest}:
      +M2 = Cr.Cir.Cells.set(m, z, x)
      +h2 = h
      +hd = al.hd(o, rest, m, P, Q, zs, K, F, N, h2)
      +ne = Ar.ne(o, z, N.le_trans(1n+U32.to_nat(o), U32.to_nat(N), U32.to_nat(z), U.lt(o, N, al.hd.lt(m, Q, o, F, N, hd)), hzn))
      %Equal.sym(Nat, D.Ow(M2, o, c), D.Ow(m, o, c), ow.set(m, z, x, o, c, D.Has(Q, o), ne, al.hd.tg(m, Q, o, F, N, hd), hz)) :
        {Nat.add(_, D.Pp(rest, M2, c)) == Nat.add(D.Ow(m, o, c), D.Pp(rest, m, c)) : Nat}
      %Equal.sym(Nat, D.Pp(rest, M2, c), D.Pp(rest, m, c), pp.set(rest, m, P, Q, zs, K, F, N, z, x, c, al.rest(o, rest, m, P, Q, zs, K, F, N, h2), hzn, hz)) :
        {Nat.add(D.Ow(m, o, c), _) == Nat.add(D.Ow(m, o, c), D.Pp(rest, m, c)) : Nat}
      {==}

# a and b and c and d, with b giving b2
def Bo.and4.b(a: Bool, b: Bool, -c: Bool, -d: Bool, -b2: Bool, h: {Bool.and(Bool.and(Bool.and(a, b), c), d) == True{} : Bool},
  g: {b == True{} : Bool} -> {b2 == True{} : Bool}) -> {Bool.and(Bool.and(Bool.and(a, b2), c), d) == True{} : Bool}:
  match a:
    case True{}:
      match b:
        case True{}:
          %Equal.sym(Bool, b2, True{}, g({==})) : {Bool.and(Bool.and(Bool.and(True{}, _), c), d) == True{} : Bool}
          h
        case False{}:
          Bo.tf({Bool.and(Bool.and(Bool.and(True{}, b2), c), d) == True{} : Bool}, h)
    case False{}:
      Bo.tf({Bool.and(Bool.and(Bool.and(False{}, b2), c), d) == True{} : Bool}, h)

# o < N <= M gives o < M
def Ar.lt.up(+o: U32, +N: U32, +M: U32, h: {U32.is_lt(o, N) == True{} : Bool}, hm: N.Le(U32.to_nat(N), U32.to_nat(M))) ->
  {U32.is_lt(o, M) == True{} : Bool}:
  U.lt_t(o, M, N.le_trans(1n+U32.to_nat(o), U32.to_nat(N), U32.to_nat(M), U.lt(o, N, h), hm))

# next grows by one, below 214748364
def Ar.nx.up(+nx: U32, hb: N.Le(1n+U32.to_nat(nx), U32.to_nat(214748364))) -> N.Le(U32.to_nat(nx), U32.to_nat(U32.inc(nx))):
  N.le_rw_r(U32.to_nat(nx), 1n+U32.to_nat(nx), U32.to_nat(U32.inc(nx)),
    Equal.sym(Nat, U32.to_nat(U32.inc(nx)), 1n+U32.to_nat(nx), Ar.u.inc(nx, 214748364, hb)), N.le_succ(U32.to_nat(nx), U32.to_nat(nx), N.le_refl(U32.to_nat(nx))))

# a cell below N is one below M >= N
def cell.up.of(b: Bool, +p: U32, +F: U32, +N: U32, +M: U32, hm: N.Le(U32.to_nat(N), U32.to_nat(M)),
  h: {Bool.or(b, Bool.and(U32.is_le(F, p), U32.is_lt(p, N))) == True{} : Bool}) ->
  {Bool.or(b, Bool.and(U32.is_le(F, p), U32.is_lt(p, M))) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      +h2 = h
      Bo.and_i(U32.is_le(F, p), U32.is_lt(p, M), Bo.and_l(U32.is_le(F, p), U32.is_lt(p, N), h2),
        Ar.lt.up(p, N, M, Bo.and_r(U32.is_le(F, p), U32.is_lt(p, N), h2), hm))

def cell.up(+p: U32, +K: U32, +F: U32, +N: U32, +M: U32, hm: N.Le(U32.to_nat(N), U32.to_nat(M)),
  h: {Cr.Cir.is_cell(p, K, F, N) == True{} : Bool}) -> {Cr.Cir.is_cell(p, K, F, M) == True{} : Bool}:
  cell.up.of(Bool.and(Bool.not(U32.is_zero(p)), U32.is_le(p, K)), p, F, N, M, hm, h)

# a cell is not N, past the image K
def cell.ne.of(b: Bool, +p: U32, +K: U32, +F: U32, +N: U32, eb: {Bool.and(Bool.not(U32.is_zero(p)), U32.is_le(p, K)) == b : Bool},
  hk: N.Le(1n+U32.to_nat(K), U32.to_nat(N)), h: {Bool.or(b, Bool.and(U32.is_le(F, p), U32.is_lt(p, N))) == True{} : Bool}) ->
  {U32.is_eq(p, N) == False{} : Bool}:
  match b:
    case True{}:
      Ar.ne(p, N, N.le_trans(1n+U32.to_nat(p), 1n+U32.to_nat(K), U32.to_nat(N),
        U.le(p, K, Bo.and_r(Bool.not(U32.is_zero(p)), U32.is_le(p, K), eb)), hk))
    case False{}:
      Ar.ne(p, N, U.lt(p, N, Bo.and_r(U32.is_le(F, p), U32.is_lt(p, N), h)))

def cell.ne(+p: U32, +K: U32, +F: U32, +N: U32, hk: N.Le(1n+U32.to_nat(K), U32.to_nat(N)),
  h: {Cr.Cir.is_cell(p, K, F, N) == True{} : Bool}) -> {U32.is_eq(p, N) == False{} : Bool}:
  cell.ne.of(Bool.and(Bool.not(U32.is_zero(p)), U32.is_le(p, K)), p, K, F, N, {==}, hk, h)

# The pointers below next
# -----------------------

# each of ys is below N, so below M >= N
def all.lt.up(ys: List<&2, U32>, +N: U32, +M: U32, +hm: N.Le(U32.to_nat(N), U32.to_nat(M)), h: {D.All.lt(ys, N) == True{} : Bool}) ->
  {D.All.lt(ys, M) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      +h2 = h
      Bo.and_i(U32.is_lt(y, M), D.All.lt(rest, M), Ar.lt.up(y, N, M, Bo.and_l(U32.is_lt(y, N), D.All.lt(rest, N), h2), hm),
        all.lt.up(rest, N, M, hm, Bo.and_r(U32.is_lt(y, N), D.All.lt(rest, N), h2)))

# no pointer below N is N
def occ.lt0(ys: List<&2, U32>, +N: U32, h: {D.All.lt(ys, N) == True{} : Bool}) -> {D.Occ(ys, N) == 0n : Nat}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      +h2 = h
      %Equal.sym(Bool, U32.is_eq(y, N), False{}, Ar.ne(y, N, U.lt(y, N, Bo.and_l(U32.is_lt(y, N), D.All.lt(rest, N), h2)))) :
        {Nat.add(D.Nat.of(_), D.Occ(rest, N)) == 0n : Nat}
      occ.lt0(rest, N, Bo.and_r(U32.is_lt(y, N), D.All.lt(rest, N), h2))

# the cells whose pointers are below N do not point to N
def lt.pc0(k: Nat, +m: Cr.Cir.Cells, +Q: List<&2, U32>, +o: U32, +N: U32, h: {D.Lt(k, m, Q, o, N) == True{} : Bool}) ->
  {D.Pc(k, m, Q, o, N) == 0n : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+(+p):
      +h2 = h
      %Equal.sym(Nat, D.Occ(D.Ps(m, Q, o), N), 0n, occ.lt0(D.Ps(m, Q, o), N, Bo.and_l(D.All.lt(D.Ps(m, Q, o), N), D.Lt(p, m, Q, U32.inc(o), N), h2))) :
        {Nat.add(_, D.Pc(p, m, Q, U32.inc(o), N)) == 0n : Nat}
      lt.pc0(p, m, Q, U32.inc(o), N, Bo.and_r(D.All.lt(D.Ps(m, Q, o), N), D.Lt(p, m, Q, U32.inc(o), N), h2))

# a store to z, past the table, keeps Lt of the n cells from o, none of
# them z, with next M >= N
def lt.set(n: Nat, +m: Cr.Cir.Cells, +z: U32, +x: Cr.Cir.Cell, +Q: List<&2, U32>, +o: U32, +N: U32, +M: U32,
  +hn: {Ne(n, o, z) == True{} : Bool}, +hz: N.Le(291n, U32.to_nat(z)), +hm: N.Le(U32.to_nat(N), U32.to_nat(M)),
  h: {D.Lt(n, m, Q, o, N) == True{} : Bool}) -> {D.Lt(n, Cr.Cir.Cells.set(m, z, x), Q, o, M) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      +M2 = Cr.Cir.Cells.set(m, z, x)
      +h2 = h
      +ne = Bo.not_t(U32.is_eq(o, z), Bo.and_l(Bool.not(U32.is_eq(o, z)), Ne(p, U32.inc(o), z), hn))
      %Equal.sym(List<&2, U32>, D.Ps(M2, Q, o), D.Ps(m, Q, o), ps.set(m, z, x, Q, o, ne, hz)) :
        {Bool.and(D.All.lt(_, M), D.Lt(p, M2, Q, U32.inc(o), M)) == True{} : Bool}
      Bo.and_i(D.All.lt(D.Ps(m, Q, o), M), D.Lt(p, M2, Q, U32.inc(o), M),
        all.lt.up(D.Ps(m, Q, o), N, M, hm, Bo.and_l(D.All.lt(D.Ps(m, Q, o), N), D.Lt(p, m, Q, U32.inc(o), N), h2)),
        lt.set(p, m, z, x, Q, U32.inc(o), N, M, Bo.and_r(Bool.not(U32.is_eq(o, z)), Ne(p, U32.inc(o), z), hn), hz, hm,
          Bo.and_r(D.All.lt(D.Ps(m, Q, o), N), D.Lt(p, m, Q, U32.inc(o), N), h2)))

# Lt of n + 1 cells: of the n first, and of the last
def lt.snoc(n: Nat, +m: Cr.Cir.Cells, +Q: List<&2, U32>, +o: U32, +N: U32) ->
  {D.Lt(1n+n, m, Q, o, N) == Bool.and(D.Lt(n, m, Q, o, N), D.All.lt(D.Ps(m, Q, Inc(n, o)), N)) : Bool}:
  match n:
    case 0n:
      Bo.and_true(D.All.lt(D.Ps(m, Q, o), N))
    case 1n+(+p):
      +A = D.All.lt(D.Ps(m, Q, o), N)
      +B = D.Lt(p, m, Q, U32.inc(o), N)
      +C = D.All.lt(D.Ps(m, Q, Inc(p, U32.inc(o))), N)
      %Equal.sym(Bool, D.Lt(1n+p, m, Q, U32.inc(o), N), Bool.and(B, C), lt.snoc(p, m, Q, U32.inc(o), N)) :
        {Bool.and(A, _) == Bool.and(Bool.and(A, B), C) : Bool}
      Bo.and_assoc(A, B, C)

# the pointers of the cells from F to nx are below nx, and the new cell nx,
# set to zeros, has none: all are below nx + 1
def lt.new(+m: Cr.Cir.Cells, +F: U32, +nx: U32, +Q: List<&2, U32>,
  +t0: {Cr.Cir.Cells.get(m, 272) == Cr.Cir.Cell{0, 0, 0, 0, 0} : Cr.Cir.Cell}, +hz: N.Le(291n, U32.to_nat(nx)),
  +hfn: {U32.is_le(F, nx) == True{} : Bool}, +hb: N.Le(1n+U32.to_nat(nx), U32.to_nat(214748364)),
  h: {D.Lt(Nat.sub(U32.to_nat(nx), U32.to_nat(F)), m, Q, F, nx) == True{} : Bool}) ->
  {D.Lt(1n+Nat.sub(U32.to_nat(nx), U32.to_nat(F)), Cr.Cir.Cells.set(m, nx, Cr.Cir.Cell.zero()), Q, F, U32.inc(nx)) == True{} : Bool}:
  +n = Nat.sub(U32.to_nat(nx), U32.to_nat(F))
  +M2 = Cr.Cir.Cells.set(m, nx, Cr.Cir.Cell.zero())
  +N2 = U32.inc(nx)
  %Equal.sym(Bool, D.Lt(1n+n, M2, Q, F, N2), Bool.and(D.Lt(n, M2, Q, F, N2), D.All.lt(D.Ps(M2, Q, Inc(n, F)), N2)), lt.snoc(n, M2, Q, F, N2)) :
    {_ == True{} : Bool}
  %Equal.sym(U32, Inc(n, F), nx, Ar.inc.end(F, nx, hfn)) :
    {Bool.and(D.Lt(n, M2, Q, F, N2), D.All.lt(D.Ps(M2, Q, _), N2)) == True{} : Bool}
  %Equal.sym(List<&2, U32>, D.Ps(M2, Q, nx), Nil{}, ps.zero(m, nx, Q, t0, hz)) :
    {Bool.and(D.Lt(n, M2, Q, F, N2), D.All.lt(_, N2)) == True{} : Bool}
  Bo.and_i(D.Lt(n, M2, Q, F, N2), True{},
    lt.set(n, m, nx, Cr.Cir.Cell.zero(), Q, F, nx, N2, Ar.ne.own(F, nx, hfn), hz, Ar.nx.up(nx, hb), h), {==})

# AL across a new cell
# --------------------

# a pick of a or 0, with a giving a2 when b holds
def Pk.b(b: Bool, +a1: U32, +a2: U32, e: {b == True{} : Bool} -> {a1 == a2 : U32}) ->
  {Bool.pick(U32, b, a1, 0) == Bool.pick(U32, b, a2, 0) : U32}:
  match b:
    case True{}:
      e({==})
    case False{}:
      {==}

# a store to z, past the table, keeps the mask Am of another cell o of a
# garbage cell's tag
def am.set(+m: Cr.Cir.Cells, +z: U32, +x: Cr.Cir.Cell, +o: U32, -hq: Bool, ne: {U32.is_eq(o, z) == False{} : Bool},
  ht: {Bool.or(U32.is_le(U32.and(D.Fd(0n, m, o), 63), 18), Bool.and(U32.is_le(32, U32.and(D.Fd(0n, m, o), 63)), hq)) == True{} : Bool},
  +hz: N.Le(291n, U32.to_nat(z))) -> {D.Am(Cr.Cir.Cells.set(m, z, x), o) == D.Am(m, o) : U32}:
  +M2 = Cr.Cir.Cells.set(m, z, x)
  +y = Cr.Cir.Cells.get(m, o)
  +t = U32.and(Cr.Cir.Cell.get(0n, y), 63)
  %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, o), y, Cl.get_ne(m, o, z, x, ne)) :
    {Bool.pick(U32, U32.is_lt(U32.and(Cr.Cir.Cell.get(0n, _), 63), 32), Cr.Cir.Cell.get(2n, Cr.Cir.Cells.get(M2, U32.add(272, U32.and(Cr.Cir.Cell.get(0n, _), 63)))), 0) ==
      D.Am(m, o) : U32}
  Pk.b(U32.is_lt(t, 32), D.Fd(2n, M2, U32.add(272, t)), D.Fd(2n, m, U32.add(272, t)),
    e => Equal.cong(Cr.Cir.Cell, U32, w => Cr.Cir.Cell.get(2n, w), Cr.Cir.Cells.get(M2, U32.add(272, t)), Cr.Cir.Cells.get(m, U32.add(272, t)),
      Cl.get_ne(m, U32.add(272, t), z, x, Ar.tbl.ne(t, z, Ar.t19(t, hq, e, ht), hz))))

# a part of a garbage cell across the new cell nx, set to zeros
def part.fresh(+m: Cr.Cir.Cells, +P: List<&2, U32>, +Q: List<&2, U32>, +zs: List<&2, D.Zs>, +z: Nat, +am: U32, +bit: U32, +p: U32,
  +K: U32, +F: U32, +nx: U32, +hP: {D.AL.cells(P, m, P, Q, zs, K, F, nx) == True{} : Bool},
  +hk: N.Le(1n+U32.to_nat(K), U32.to_nat(nx)), +hm: N.Le(U32.to_nat(nx), U32.to_nat(U32.inc(nx))), +hz: N.Le(291n, U32.to_nat(nx)),
  h: {D.AL.part(m, P, zs, z, am, bit, p, K, F, nx) == True{} : Bool}) ->
  {D.AL.part(Cr.Cir.Cells.set(m, nx, Cr.Cir.Cell.zero()), P, zs, z, am, bit, p, K, F, U32.inc(nx)) == True{} : Bool}:
  +M2 = Cr.Cir.Cells.set(m, nx, Cr.Cir.Cell.zero())
  Bo.or3(U32.is_zero(U32.and(am, bit)), U32.is_zero(p), Cr.Cir.is_cell(p, K, F, nx),
    Bool.or(D.Stc(m, p), Bool.or(Bool.and(D.Has(P, p), Nat.is_lt(D.Zz(zs, p), z)), Nat.is_lt(D.Pp(P, m, p), U32.to_nat(D.Fd(1n, m, p))))),
    Cr.Cir.is_cell(p, K, F, U32.inc(nx)),
    Bool.or(D.Stc(M2, p), Bool.or(Bool.and(D.Has(P, p), Nat.is_lt(D.Zz(zs, p), z)), Nat.is_lt(D.Pp(P, M2, p), U32.to_nat(D.Fd(1n, M2, p))))),
    h, ec => cell.up(p, K, F, nx, U32.inc(nx), hm, ec),
    ec => ed =>
      (%Equal.sym(Nat, D.Pp(P, M2, p), D.Pp(P, m, p), pp.set(P, m, P, Q, zs, K, F, nx, nx, Cr.Cir.Cell.zero(), p, hP, N.le_refl(U32.to_nat(nx)), hz)) :
        {Bool.or(D.Stc(M2, p), Bool.or(Bool.and(D.Has(P, p), Nat.is_lt(D.Zz(zs, p), z)), Nat.is_lt(_, U32.to_nat(D.Fd(1n, M2, p))))) == True{} : Bool};
      (%Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, p), Cr.Cir.Cells.get(m, p), Cl.get_ne(m, p, nx, Cr.Cir.Cell.zero(), cell.ne(p, K, F, nx, hk, ec))) :
        {Bool.or(U32.is_ne(U32.and(Cr.Cir.Cell.get(0n, _), 1024), 0), Bool.or(Bool.and(D.Has(P, p), Nat.is_lt(D.Zz(zs, p), z)),
          Nat.is_lt(D.Pp(P, m, p), U32.to_nat(Cr.Cir.Cell.get(1n, _))))) == True{} : Bool};
      ed)))

# a garbage cell's own facts across the new cell nx
def hd.fresh(+m: Cr.Cir.Cells, +Q: List<&2, U32>, +o: U32, +F: U32, +nx: U32, +hm: N.Le(U32.to_nat(nx), U32.to_nat(U32.inc(nx))),
  h: {AL.hd(m, Q, o, F, nx) == True{} : Bool}) -> {AL.hd(Cr.Cir.Cells.set(m, nx, Cr.Cir.Cell.zero()), Q, o, F, U32.inc(nx)) == True{} : Bool}:
  +M2 = Cr.Cir.Cells.set(m, nx, Cr.Cir.Cell.zero())
  +h2 = h
  +ne = Ar.ne(o, nx, U.lt(o, nx, al.hd.lt(m, Q, o, F, nx, h2)))
  %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, o), Cr.Cir.Cells.get(m, o), Cl.get_ne(m, o, nx, Cr.Cir.Cell.zero(), ne)) :
    {Bool.and(Bool.and(Bool.and(U32.is_le(F, o), U32.is_lt(o, U32.inc(nx))), Bool.not(U32.is_ne(U32.and(Cr.Cir.Cell.get(0n, _), 1024), 0))),
      Bool.or(U32.is_le(U32.and(Cr.Cir.Cell.get(0n, _), 63), 18), Bool.and(U32.is_le(32, U32.and(Cr.Cir.Cell.get(0n, _), 63)), D.Has(Q, o)))) == True{} : Bool}
  Bo.and4.b(U32.is_le(F, o), U32.is_lt(o, nx), Bool.not(D.Stc(m, o)),
    Bool.or(U32.is_le(U32.and(D.Fd(0n, m, o), 63), 18), Bool.and(U32.is_le(32, U32.and(D.Fd(0n, m, o), 63)), D.Has(Q, o))),
    U32.is_lt(o, U32.inc(nx)), h2, e => Ar.lt.up(o, nx, U32.inc(nx), e, hm))

# a garbage cell's parts across the new cell nx
def pt.fresh(+m: Cr.Cir.Cells, +P: List<&2, U32>, +Q: List<&2, U32>, +zs: List<&2, D.Zs>, +o: U32, +K: U32, +F: U32, +nx: U32,
  +hP: {D.AL.cells(P, m, P, Q, zs, K, F, nx) == True{} : Bool}, +hk: N.Le(1n+U32.to_nat(K), U32.to_nat(nx)),
  +hm: N.Le(U32.to_nat(nx), U32.to_nat(U32.inc(nx))), +hz: N.Le(291n, U32.to_nat(nx)),
  hd: {AL.hd(m, Q, o, F, nx) == True{} : Bool}, h: {AL.pt(m, P, zs, o, K, F, nx) == True{} : Bool}) ->
  {AL.pt(Cr.Cir.Cells.set(m, nx, Cr.Cir.Cell.zero()), P, zs, o, K, F, U32.inc(nx)) == True{} : Bool}:
  +M2 = Cr.Cir.Cells.set(m, nx, Cr.Cir.Cell.zero())
  +N2 = U32.inc(nx)
  +hd2 = hd
  +ne = Ar.ne(o, nx, U.lt(o, nx, al.hd.lt(m, Q, o, F, nx, hd2)))
  +am = D.Am(m, o)
  +zz = D.Zz(zs, o)
  +q1 = D.AL.part(m, P, zs, zz, am, 1, D.Fd(2n, m, o), K, F, nx)
  +q2 = D.AL.part(m, P, zs, zz, am, 2, D.Fd(3n, m, o), K, F, nx)
  +q4 = D.AL.part(m, P, zs, zz, am, 4, D.Fd(4n, m, o), K, F, nx)
  +h2 = h
  +r1 = Bo.and_r(q1, Bool.and(q2, q4), h2)
  %Equal.sym(U32, D.Am(M2, o), am, am.set(m, nx, Cr.Cir.Cell.zero(), o, D.Has(Q, o), ne, al.hd.tg(m, Q, o, F, nx, hd2), hz)) :
    {Bool.and(D.AL.part(M2, P, zs, zz, _, 1, D.Fd(2n, M2, o), K, F, N2), Bool.and(D.AL.part(M2, P, zs, zz, _, 2, D.Fd(3n, M2, o), K, F, N2),
      D.AL.part(M2, P, zs, zz, _, 4, D.Fd(4n, M2, o), K, F, N2))) == True{} : Bool}
  %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, o), Cr.Cir.Cells.get(m, o), Cl.get_ne(m, o, nx, Cr.Cir.Cell.zero(), ne)) :
    {Bool.and(D.AL.part(M2, P, zs, zz, am, 1, Cr.Cir.Cell.get(2n, _), K, F, N2), Bool.and(D.AL.part(M2, P, zs, zz, am, 2, Cr.Cir.Cell.get(3n, _), K, F, N2),
      D.AL.part(M2, P, zs, zz, am, 4, Cr.Cir.Cell.get(4n, _), K, F, N2))) == True{} : Bool}
  Bo.and_i(D.AL.part(M2, P, zs, zz, am, 1, D.Fd(2n, m, o), K, F, N2),
    Bool.and(D.AL.part(M2, P, zs, zz, am, 2, D.Fd(3n, m, o), K, F, N2), D.AL.part(M2, P, zs, zz, am, 4, D.Fd(4n, m, o), K, F, N2)),
    part.fresh(m, P, Q, zs, zz, am, 1, D.Fd(2n, m, o), K, F, nx, hP, hk, hm, hz, Bo.and_l(q1, Bool.and(q2, q4), h2)),
    Bo.and_i(D.AL.part(M2, P, zs, zz, am, 2, D.Fd(3n, m, o), K, F, N2), D.AL.part(M2, P, zs, zz, am, 4, D.Fd(4n, m, o), K, F, N2),
      part.fresh(m, P, Q, zs, zz, am, 2, D.Fd(3n, m, o), K, F, nx, hP, hk, hm, hz, Bo.and_l(q2, q4, r1)),
      part.fresh(m, P, Q, zs, zz, am, 4, D.Fd(4n, m, o), K, F, nx, hP, hk, hm, hz, Bo.and_r(q2, q4, r1))))

# a garbage cell's counts across the new cell nx
def ct.fresh(+m: Cr.Cir.Cells, +P: List<&2, U32>, +Q: List<&2, U32>, +zs: List<&2, D.Zs>, +o: U32, +K: U32, +F: U32, +nx: U32,
  +hP: {D.AL.cells(P, m, P, Q, zs, K, F, nx) == True{} : Bool}, +t0: {Cr.Cir.Cells.get(m, 272) == Cr.Cir.Cell{0, 0, 0, 0, 0} : Cr.Cir.Cell},
  +hz: N.Le(291n, U32.to_nat(nx)), +hfn: {U32.is_le(F, nx) == True{} : Bool}, +hb: N.Le(1n+U32.to_nat(nx), U32.to_nat(214748364)),
  ne: {U32.is_eq(o, nx) == False{} : Bool}, h: {AL.ct(m, P, Q, o, F, nx) == True{} : Bool}) ->
  {AL.ct(Cr.Cir.Cells.set(m, nx, Cr.Cir.Cell.zero()), P, Q, o, F, U32.inc(nx)) == True{} : Bool}:
  +n = Nat.sub(U32.to_nat(nx), U32.to_nat(F))
  +M2 = Cr.Cir.Cells.set(m, nx, Cr.Cir.Cell.zero())
  +pp2 = D.Pp(P, M2, o)
  +pp = D.Pp(P, m, o)
  %Equal.sym(Nat, Nat.sub(U32.to_nat(U32.inc(nx)), U32.to_nat(F)), 1n+n, Ar.cnt.new(F, nx, hfn, hb)) :
    {Bool.and(Nat.is_eq(D.Pc(_, M2, Q, F, o), pp2), Bool.pick(Bool, D.Has(Q, o), Nat.is_eq(pp2, 0n),
      Bool.and(Nat.is_eq(pp2, U32.to_nat(D.Fd(1n, M2, o))), Nat.is_lt(0n, pp2)))) == True{} : Bool}
  %Equal.sym(Nat, D.Pc(1n+n, M2, Q, F, o), D.Pc(n, m, Q, F, o), pc.new(m, F, nx, Q, o, t0, hz, hfn)) :
    {Bool.and(Nat.is_eq(_, pp2), Bool.pick(Bool, D.Has(Q, o), Nat.is_eq(pp2, 0n),
      Bool.and(Nat.is_eq(pp2, U32.to_nat(D.Fd(1n, M2, o))), Nat.is_lt(0n, pp2)))) == True{} : Bool}
  %Equal.sym(Nat, pp2, pp, pp.set(P, m, P, Q, zs, K, F, nx, nx, Cr.Cir.Cell.zero(), o, hP, N.le_refl(U32.to_nat(nx)), hz)) :
    {Bool.and(Nat.is_eq(D.Pc(n, m, Q, F, o), _), Bool.pick(Bool, D.Has(Q, o), Nat.is_eq(_, 0n),
      Bool.and(Nat.is_eq(_, U32.to_nat(D.Fd(1n, M2, o))), Nat.is_lt(0n, _)))) == True{} : Bool}
  %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, o), Cr.Cir.Cells.get(m, o), Cl.get_ne(m, o, nx, Cr.Cir.Cell.zero(), ne)) :
    {Bool.and(Nat.is_eq(D.Pc(n, m, Q, F, o), pp), Bool.pick(Bool, D.Has(Q, o), Nat.is_eq(pp, 0n),
      Bool.and(Nat.is_eq(pp, U32.to_nat(Cr.Cir.Cell.get(1n, _))), Nat.is_lt(0n, pp)))) == True{} : Bool}
  h

# the garbage cells os across the new cell nx
def al.cells.fresh(os: List<&2, U32>, +m: Cr.Cir.Cells, +P: List<&2, U32>, +Q: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32,
  +nx: U32, +hP: {D.AL.cells(P, m, P, Q, zs, K, F, nx) == True{} : Bool},
  +t0: {Cr.Cir.Cells.get(m, 272) == Cr.Cir.Cell{0, 0, 0, 0, 0} : Cr.Cir.Cell}, +hz: N.Le(291n, U32.to_nat(nx)),
  +hfn: {U32.is_le(F, nx) == True{} : Bool}, +hb: N.Le(1n+U32.to_nat(nx), U32.to_nat(214748364)),
  +hk: N.Le(1n+U32.to_nat(K), U32.to_nat(nx)), +hm: N.Le(U32.to_nat(nx), U32.to_nat(U32.inc(nx))),
  h: {D.AL.cells(os, m, P, Q, zs, K, F, nx) == True{} : Bool}) ->
  {D.AL.cells(os, Cr.Cir.Cells.set(m, nx, Cr.Cir.Cell.zero()), P, Q, zs, K, F, U32.inc(nx)) == True{} : Bool}:
  match os:
    case Nil{}:
      {==}
    case Con{+o, +rest}:
      +M2 = Cr.Cir.Cells.set(m, nx, Cr.Cir.Cell.zero())
      +h2 = h
      +hd = al.hd(o, rest, m, P, Q, zs, K, F, nx, h2)
      +ne = Ar.ne(o, nx, U.lt(o, nx, al.hd.lt(m, Q, o, F, nx, hd)))
      al.cons(o, rest, M2, P, Q, zs, K, F, U32.inc(nx), hd.fresh(m, Q, o, F, nx, hm, hd),
        pt.fresh(m, P, Q, zs, o, K, F, nx, hP, hk, hm, hz, hd, al.pt(o, rest, m, P, Q, zs, K, F, nx, h2)),
        ct.fresh(m, P, Q, zs, o, K, F, nx, hP, t0, hz, hfn, hb, ne, al.ct(o, rest, m, P, Q, zs, K, F, nx, h2)),
        al.cells.fresh(rest, m, P, Q, zs, K, F, nx, hP, t0, hz, hfn, hb, hk, hm, al.rest(o, rest, m, P, Q, zs, K, F, nx, h2)))

# AL with an empty pend list across the new cell nx, set to zeros
def al.fresh(+m: Cr.Cir.Cells, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +nx: U32,
  hal: {D.AL(m, 0, P, Nil{}, zs, K, F, nx) == True{} : Bool},
  +t0: {Cr.Cir.Cells.get(m, 272) == Cr.Cir.Cell{0, 0, 0, 0, 0} : Cr.Cir.Cell}, +hz: N.Le(291n, U32.to_nat(nx)),
  +hfn: {U32.is_le(F, nx) == True{} : Bool}, +hb: N.Le(1n+U32.to_nat(nx), U32.to_nat(214748364)),
  +hk: N.Le(1n+U32.to_nat(K), U32.to_nat(nx))) ->
  {D.AL(Cr.Cir.Cells.set(m, nx, Cr.Cir.Cell.zero()), 0, P, Nil{}, zs, K, F, U32.inc(nx)) == True{} : Bool}:
  +n = Nat.sub(U32.to_nat(nx), U32.to_nat(F))
  +M2 = Cr.Cir.Cells.set(m, nx, Cr.Cir.Cell.zero())
  +N2 = U32.inc(nx)
  +hm = Ar.nx.up(nx, hb)
  +C1 = D.AL.cells(P, m, P, Nil{}, zs, K, F, nx)
  +L1 = D.Lt(n, m, Nil{}, F, nx)
  +ha = {hal : {Bool.and(D.Nodup(P), Bool.and(C1, L1)) == True{} : Bool}}
  +hr = Bo.and_r(D.Nodup(P), Bool.and(C1, L1), ha)
  +hc = Bo.and_l(C1, L1, hr)
  %Equal.sym(Nat, Nat.sub(U32.to_nat(N2), U32.to_nat(F)), 1n+n, Ar.cnt.new(F, nx, hfn, hb)) :
    {Bool.and(D.Nodup(P), Bool.and(D.AL.cells(P, M2, P, Nil{}, zs, K, F, N2), D.Lt(_, M2, Nil{}, F, N2))) == True{} : Bool}
  Bo.and_i(D.Nodup(P), Bool.and(D.AL.cells(P, M2, P, Nil{}, zs, K, F, N2), D.Lt(1n+n, M2, Nil{}, F, N2)),
    Bo.and_l(D.Nodup(P), Bool.and(C1, L1), ha),
    Bo.and_i(D.AL.cells(P, M2, P, Nil{}, zs, K, F, N2), D.Lt(1n+n, M2, Nil{}, F, N2),
      al.cells.fresh(P, m, P, Nil{}, zs, K, F, nx, hc, t0, hz, hfn, hb, hk, hm, hc),
      lt.new(m, F, nx, Nil{}, t0, hz, hfn, hb, Bo.and_r(C1, L1, hr))))
