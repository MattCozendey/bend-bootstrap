# compiler: the copy's kit
# ========================
#
# Lemmas of Bool, Nat, U32, the cells and the runs of Cir that the proofs
# of copy_substitution.bend's claims use.

import Base
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
