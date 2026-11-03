# compiler: the memory bound of a run (layer B, U16)
# ==================================================
#
# The arithmetic of F (AGENTS.md 3.9.1.4, Program.need) that mach.memory
# (moves.bend) needs: the budget of every round of the run, M.input's budget,
# and the bytes that Cir.result takes before the program are at most
#
#   F = 64 × (size + S) + 2^24,   S = Program.largest(p, i, n).
#
# With C the cache's STATIC cells (at most 6144), W the nodes of the def
# bodies, k the image's cells and fi the first cell:
#
#   every term of the run, and its step, has at most S nodes (largest.*);
#   the start term has 72 |i| + 5 (start.size);
#   k <= 290 + W, Defs.big <= W, 3 W <= size (k.le, big.le, w.le);
#   fi <= 1 + k + |i| (first.le);
#   Budget <= Room = 20 (fi + Peak) + S, Peak = C + 16 + 2 S + 3 Defs.big
#     (budget.room);
#   Room <= 20 (307 + C) + 80 W + 61 S <= F (room.need).
#
# The loop of mach.memory carries only budget.lim's premises, which name no
# closed big number; room.lim (with C <= 6144 and the memory F) is proven
# once, before it. The big numbers stay as need_big.bend keeps them: 2^k is
# D(k, 1n), every lemma is over variables, and the one comparison of two
# closed numbers (2^18 <= 2^24) is a def of its own.

import Base
import ../../Shared/shared.bend as Sd
import ../../Book/impl.bend as Bk
import ../../Eval/impl.bend as El
import ../../Wasm/impl.bend as Wa
import ../../Program/impl.bend as Pg
import ../Cir/impl.bend as Cr
import ./impl.bend as Mc
import ../need_big.bend as N
import ../img_small.bend as PG
import ./definitions.bend as D
import ./eval_facts.bend as EV
import ./first_cell_past_table.bend as FC

# Kit
# ---

# a <= max(a, b)
def max_l(+a: Nat, +b: Nat) -> N.Le(a, Nat.max(a, b)):
  match a b:
    case 0n _:
      N.le_zero(b)
    case 1n+p 0n:
      N.le_refl(1n+p)
    case 1n+p 1n+q:
      max_l(p, q)

# b <= max(a, b)
def max_r(+a: Nat, +b: Nat) -> N.Le(b, Nat.max(a, b)):
  match a b:
    case 0n _:
      N.le_refl(b)
    case 1n+p 0n:
      N.le_zero(1n+p)
    case 1n+p 1n+q:
      max_r(p, q)

# the larger of a and b is at most c when both are
def max.le(+a: Nat, +b: Nat, +c: Nat, ha: N.Le(a, c), hb: N.Le(b, c)) -> N.Le(Nat.max(a, b), c):
  match a b c:
    case 0n _ _:
      hb
    case 1n+p 0n _:
      ha
    case 1n+p 1n+q 0n:
      Empty.absurd(N.Le(Nat.max(1n+p, 1n+q), 0n), ha)
    case 1n+p 1n+q 1n+r:
      max.le(p, q, r, ha, hb)

# x <= y + (x - y)
def sub_le(+x: Nat, +y: Nat) -> N.Le(x, Nat.add(y, Nat.sub(x, y))):
  match x y:
    case 0n _:
      N.le_zero(Nat.add(y, Nat.sub(0n, y)))
    case 1n+p 0n:
      N.le_refl(1n+p)
    case 1n+p 1n+q:
      sub_le(p, q)

# j + (n - j) = n, for j <= n
def sub_add(+n: Nat, +j: Nat, h: N.Le(j, n)) -> {Nat.add(j, Nat.sub(n, j)) == n : Nat}:
  match n j:
    case 0n 0n:
      {==}
    case 1n+q 0n:
      {==}
    case 0n 1n+p:
      Empty.absurd({Nat.add(1n+p, Nat.sub(0n, 1n+p)) == 0n : Nat}, h)
    case 1n+q 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(p, Nat.sub(q, p)), q, sub_add(q, p, h))

# the term in a Some
def tget(m: Maybe<Bk.Term>, d: Bk.Term) -> Bk.Term:
  match m:
    case Some{x}:
      x
    case None{}:
      d

# Some is one to one
def tsome.inj(-a: Bk.Term, -b: Bk.Term, e: {Some{a} == Some{b} : Maybe<Bk.Term>}) -> {a == b : Bk.Term}:
  Equal.cong(Maybe<Bk.Term>, Bk.Term, x => tget(x, a), Some{a}, Some{b}, e)

# None is no Some
def IsNone(m: Maybe<Bk.Term>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{_}:
      Empty

def tsome.ne(-u: Bk.Term, e: {None{} == Some{u} : Maybe<Bk.Term>}) -> Empty:
  %e : IsNone(_)
  Unit{}

def OIsNone(m: Maybe<&2, List<&2, Word(8n)>>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{_}:
      Empty

def osome.ne(-o: List<&2, Word(8n)>, e: {None{} == Some{o} : Maybe<&2, List<&2, Word(8n)>>}) -> Empty:
  %e : OIsNone(_)
  Unit{}

# x + 1 = 1 + x
def add_one(+x: Nat) -> {Nat.add(x, 1n) == 1n+x : Nat}:
  Equal.trans(Nat, Nat.add(x, 1n), 1n+Nat.add(x, 0n), 1n+x, N.add_succ_r(x, 0n),
    Equal.cong(Nat, Nat, y => 1n+y, Nat.add(x, 0n), x, N.add_zero(x)))

# a × (1 + b) = a + a × b
def mul_succ_r(+a: Nat, +b: Nat) -> {Nat.mul(a, 1n+b) == Nat.add(a, Nat.mul(a, b)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(b, Nat.mul(p, 1n+b)), Nat.add(p, Nat.add(b, Nat.mul(p, b))),
        Equal.trans(Nat, Nat.add(b, Nat.mul(p, 1n+b)), Nat.add(b, Nat.add(p, Nat.mul(p, b))), Nat.add(p, Nat.add(b, Nat.mul(p, b))),
          Equal.cong(Nat, Nat, x => Nat.add(b, x), Nat.mul(p, 1n+b), Nat.add(p, Nat.mul(p, b)), mul_succ_r(p, b)),
          N.add_swap(b, p, Nat.mul(p, b))))

# 3 × x, one 3 a unit
def Tri(x: Nat) -> Nat:
  match x:
    case 0n:
      0n
    case 1n+p:
      3n+Tri(p)

# 3 (a + b) = 3 a + 3 b
def tri_add(+a: Nat, +b: Nat) -> {Tri(Nat.add(a, b)) == Nat.add(Tri(a), Tri(b)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 3n+x, Tri(Nat.add(p, b)), Nat.add(Tri(p), Tri(b)), tri_add(p, b))

# a × (x + y) = a × x + a × y
def mul_add(+a: Nat, +x: Nat, +y: Nat) -> {Nat.mul(a, Nat.add(x, y)) == Nat.add(Nat.mul(a, x), Nat.mul(a, y)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      +px = Nat.mul(p, x)
      +py = Nat.mul(p, y)
      Equal.trans(Nat, Nat.add(Nat.add(x, y), Nat.mul(p, Nat.add(x, y))), Nat.add(Nat.add(x, y), Nat.add(px, py)), Nat.add(Nat.add(x, px), Nat.add(y, py)),
        Equal.cong(Nat, Nat, z => Nat.add(Nat.add(x, y), z), Nat.mul(p, Nat.add(x, y)), Nat.add(px, py), mul_add(p, x, y)),
        Equal.trans(Nat, Nat.add(Nat.add(x, y), Nat.add(px, py)), Nat.add(x, Nat.add(px, Nat.add(y, py))), Nat.add(Nat.add(x, px), Nat.add(y, py)),
          Equal.trans(Nat, Nat.add(Nat.add(x, y), Nat.add(px, py)), Nat.add(x, Nat.add(y, Nat.add(px, py))), Nat.add(x, Nat.add(px, Nat.add(y, py))),
            N.add_assoc(x, y, Nat.add(px, py)),
            Equal.cong(Nat, Nat, z => Nat.add(x, z), Nat.add(y, Nat.add(px, py)), Nat.add(px, Nat.add(y, py)), N.add_swap(y, px, py))),
          Equal.sym(Nat, Nat.add(Nat.add(x, px), Nat.add(y, py)), Nat.add(x, Nat.add(px, Nat.add(y, py))), N.add_assoc(x, px, Nat.add(y, py)))))

# (x + y) × c = x × c + y × c
def mul_add_l(x: Nat, +y: Nat, +c: Nat) -> {Nat.mul(Nat.add(x, y), c) == Nat.add(Nat.mul(x, c), Nat.mul(y, c)) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+(+q):
      Equal.trans(Nat, Nat.add(c, Nat.mul(Nat.add(q, y), c)), Nat.add(c, Nat.add(Nat.mul(q, c), Nat.mul(y, c))), Nat.add(Nat.add(c, Nat.mul(q, c)), Nat.mul(y, c)),
        Equal.cong(Nat, Nat, z => Nat.add(c, z), Nat.mul(Nat.add(q, y), c), Nat.add(Nat.mul(q, c), Nat.mul(y, c)), mul_add_l(q, y, c)),
        Equal.sym(Nat, Nat.add(Nat.add(c, Nat.mul(q, c)), Nat.mul(y, c)), Nat.add(c, Nat.add(Nat.mul(q, c), Nat.mul(y, c))), N.add_assoc(c, Nat.mul(q, c), Nat.mul(y, c))))

# (a × b) × c = a × (b × c)
def mul_assoc(a: Nat, +b: Nat, +c: Nat) -> {Nat.mul(Nat.mul(a, b), c) == Nat.mul(a, Nat.mul(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+(+p):
      Equal.trans(Nat, Nat.mul(Nat.add(b, Nat.mul(p, b)), c), Nat.add(Nat.mul(b, c), Nat.mul(Nat.mul(p, b), c)), Nat.add(Nat.mul(b, c), Nat.mul(p, Nat.mul(b, c))),
        mul_add_l(b, Nat.mul(p, b), c),
        Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(b, c), z), Nat.mul(Nat.mul(p, b), c), Nat.mul(p, Nat.mul(b, c)), mul_assoc(p, b, c)))

# 2^k a + 2^k b = 2^k (a + b)
def D_plus(k: Nat, +a: Nat, +b: Nat) -> {Nat.add(N.D(k, a), N.D(k, b)) == N.D(k, Nat.add(a, b)) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+(+q):
      Equal.trans(Nat, Nat.add(Nat.double(N.D(q, a)), Nat.double(N.D(q, b))), Nat.double(Nat.add(N.D(q, a), N.D(q, b))), Nat.double(N.D(q, Nat.add(a, b))),
        FC.hw.dd(N.D(q, a), N.D(q, b)),
        Equal.cong(Nat, Nat, z => Nat.double(z), Nat.add(N.D(q, a), N.D(q, b)), N.D(q, Nat.add(a, b)), D_plus(q, a, b)))

# 3 × x is Tri(x)
def mul3(+x: Nat) -> {Nat.mul(3n, x) == Tri(x) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      Equal.trans(Nat, Nat.mul(3n, 1n+p), Nat.add(3n, Nat.mul(3n, p)), 3n+Tri(p), mul_succ_r(3n, p),
        Equal.cong(Nat, Nat, y => Nat.add(3n, y), Nat.mul(3n, p), Tri(p), mul3(p)))

# The bounds
# ----------

# the most own cells that a round of the run needs (Need, with C for the
# STATIC cells and S for the nodes of the term and of its step)
def Peak(+ds: List<&2, Bk.Def>, +C: Nat, +S: Nat) -> Nat:
  Nat.add(C, Nat.add(16n, Nat.add(Nat.mul(2n, S), Nat.mul(3n, D.Defs.big(ds)))))

# the most bytes that a round of the run needs (Budget), when its first cell
# is at most X
def Room(+ds: List<&2, Bk.Def>, +X: Nat, +C: Nat, +S: Nat) -> Nat:
  Nat.add(Nat.mul(20n, Nat.add(X, Peak(ds, C, S))), S)

# The terms of the run
# --------------------

# the run from t reaches t, so its largest term has at least t's nodes
def largest.self(+n: Nat, +ds: List<&2, Bk.Def>, +t: Bk.Term) ->
  N.Le(Pg.Term.size(t), Pg.Program.largest.go(n, ds, t)):
  match n:
    case 0n:
      N.le_refl(Pg.Term.size(t))
    case 1n+m:
      max_l(Pg.Term.size(t), Pg.Program.largest.next(El.Eval.step(ds, t), u => Pg.Program.largest.go(m, ds, u)))

# after a step from t to u, the largest term of the rest of the run is at most
# that of the run from t
def largest.next(+j: Nat, +ds: List<&2, Bk.Def>, +t: Bk.Term, +u: Bk.Term,
  es: {El.Eval.step(ds, t) == Some{u} : Maybe<Bk.Term>}) ->
  N.Le(Pg.Program.largest.go(j, ds, u), Pg.Program.largest.go(1n+j, ds, t)):
  %Equal.sym(Maybe<Bk.Term>, El.Eval.step(ds, t), Some{u}, es) :
    N.Le(Pg.Program.largest.go(j, ds, u), Nat.max(Pg.Term.size(t), Pg.Program.largest.next(_, x => Pg.Program.largest.go(j, ds, x))))
  max_r(Pg.Term.size(t), Pg.Program.largest.go(j, ds, u))

# the step of t, by what it is, after which the run has j more steps
def step.le(r: Maybe<Bk.Term>, +j: Nat, +ds: List<&2, Bk.Def>, +t: Bk.Term, +er: {El.Eval.step(ds, t) == r : Maybe<Bk.Term>}) ->
  N.Le(D.StepSize(ds, t), Pg.Program.largest.go(1n+j, ds, t)):
  match r:
    case None{}:
      %Equal.sym(Maybe<Bk.Term>, El.Eval.step(ds, t), None{}, er) : N.Le(D.StepSize.of(_), Pg.Program.largest.go(1n+j, ds, t))
      N.le_zero(Pg.Program.largest.go(1n+j, ds, t))
    case Some{+u}:
      %Equal.sym(Maybe<Bk.Term>, El.Eval.step(ds, t), Some{u}, er) : N.Le(D.StepSize.of(_), Pg.Program.largest.go(1n+j, ds, t))
      N.le_trans(Pg.Term.size(u), Pg.Program.largest.go(j, ds, u), Pg.Program.largest.go(1n+j, ds, t), largest.self(j, ds, u),
        largest.next(j, ds, t, u, er))

# a term from which the run gives a result at once is a value: no step
def val.le(b: Bool, +ds: List<&2, Bk.Def>, +t: Bk.Term, -o: List<&2, Word(8n)>, eb: {El.Eval.vals(ds, t, False{}) == b : Bool},
  e: {Pg.Program.result.if(b, t) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}) -> N.Le(D.StepSize(ds, t), Pg.Term.size(t)):
  match b:
    case True{}:
      %Equal.sym(Maybe<Bk.Term>, El.Eval.step(ds, t), None{}, EV.ev.stops(ds, t, eb)) : N.Le(D.StepSize.of(_), Pg.Term.size(t))
      N.le_zero(Pg.Term.size(t))
    case False{}:
      Empty.absurd(N.Le(D.StepSize(ds, t), Pg.Term.size(t)), osome.ne(o, e))

# when Eval reaches a list of bytes from t within n steps, the step of t has
# at most as many nodes as the largest term of that run (a value has no step)
def largest.step(+n: Nat, +ds: List<&2, Bk.Def>, +t: Bk.Term, +o: List<&2, Word(8n)>,
  e: {Pg.Program.result(ds, El.Eval.steps(n, ds, t)) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}) ->
  N.Le(D.StepSize(ds, t), Pg.Program.largest.go(n, ds, t)):
  match n:
    case 0n:
      val.le(El.Eval.vals(ds, t, False{}), ds, t, o, {==}, e)
    case 1n+m:
      step.le(El.Eval.step(ds, t), m, ds, t, {==})

# a run from no term reaches none
def run.none(j: Nat, +ds: List<&2, Bk.Def>) -> {El.Eval.run(j, ds, None{}) == None{} : Maybe<Bk.Term>}:
  match j:
    case 0n:
      {==}
    case 1n+q:
      {==}

# the rest of the run after 1 + j steps, by the step of t
def rest.of(s: Maybe<Bk.Term>, +j: Nat, +r: Nat, +ds: List<&2, Bk.Def>, +t: Bk.Term, +u: Bk.Term,
  +es: {El.Eval.step(ds, t) == s : Maybe<Bk.Term>},
  e: {El.Eval.run(j, ds, s) == Some{u} : Maybe<Bk.Term>},
  ih: @t1: Bk.Term -> {El.Eval.steps(j, ds, t1) == Some{u} : Maybe<Bk.Term>} ->
    N.Le(Pg.Program.largest.go(r, ds, u), Pg.Program.largest.go(Nat.add(j, r), ds, t1))) ->
  N.Le(Pg.Program.largest.go(r, ds, u), Pg.Program.largest.go(1n+Nat.add(j, r), ds, t)):
  match s:
    case None{}:
      Empty.absurd(N.Le(Pg.Program.largest.go(r, ds, u), Pg.Program.largest.go(1n+Nat.add(j, r), ds, t)),
        tsome.ne(u, Equal.trans(Maybe<Bk.Term>, None{}, El.Eval.run(j, ds, None{}), Some{u},
          Equal.sym(Maybe<Bk.Term>, El.Eval.run(j, ds, None{}), None{}, run.none(j, ds)), e)))
    case Some{+t1}:
      N.le_trans(Pg.Program.largest.go(r, ds, u), Pg.Program.largest.go(Nat.add(j, r), ds, t1), Pg.Program.largest.go(1n+Nat.add(j, r), ds, t),
        ih(t1, e), largest.next(Nat.add(j, r), ds, t, t1, es))

# the rest of the run after j steps, from u, is within the run from t
def largest.rest(j: Nat, +r: Nat, +ds: List<&2, Bk.Def>, +t: Bk.Term, +u: Bk.Term,
  e: {El.Eval.steps(j, ds, t) == Some{u} : Maybe<Bk.Term>}) ->
  N.Le(Pg.Program.largest.go(r, ds, u), Pg.Program.largest.go(Nat.add(j, r), ds, t)):
  match j:
    case 0n:
      %tsome.inj(t, u, e) : N.Le(Pg.Program.largest.go(r, ds, _), Pg.Program.largest.go(Nat.add(0n, r), ds, t))
      N.le_refl(Pg.Program.largest.go(r, ds, t))
    case 1n+(+q):
      rest.of(El.Eval.step(ds, t), q, r, ds, t, u, {==}, e, t1 => e1 => largest.rest(q, r, ds, t1, u, e1))

# S, the largest term of the run of the program p on the input i within n
# steps, is that of the run from the start term in the book that p reads
def largest.eq(+p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +n: Nat,
  rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>}) ->
  {Pg.Program.largest(p, i, n) == Pg.Program.largest.go(n, ds, Pg.Program.start(i)) : Nat}:
  %Equal.sym(Maybe<List<&2, Bk.Def>>, Bk.Book.read(p), Some{ds}, rd) :
    {Pg.Program.largest.of(_, i, n) == Pg.Program.largest.go(n, ds, Pg.Program.start(i)) : Nat}
  {==}

# every term that the run of p on i reaches within n steps has at most S
# nodes
def largest.ge(+p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +j: Nat, +n: Nat, +u: Bk.Term,
  rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  hj: N.Le(j, n),
  e: {El.Eval.steps(j, ds, Pg.Program.start(i)) == Some{u} : Maybe<Bk.Term>}) ->
  N.Le(Pg.Term.size(u), Pg.Program.largest(p, i, n)):
  +t = Pg.Program.start(i)
  +r = Nat.sub(n, j)
  +h1 = N.le_trans(Pg.Term.size(u), Pg.Program.largest.go(r, ds, u), Pg.Program.largest.go(Nat.add(j, r), ds, t),
    largest.self(r, ds, u), largest.rest(j, r, ds, t, u, e))
  +h2 = N.le_rw_r(Pg.Term.size(u), Pg.Program.largest.go(Nat.add(j, r), ds, t), Pg.Program.largest.go(n, ds, t),
    Equal.cong(Nat, Nat, x => Pg.Program.largest.go(x, ds, t), Nat.add(j, r), n, sub_add(n, j, hj)), h1)
  N.le_rw_r(Pg.Term.size(u), Pg.Program.largest.go(n, ds, t), Pg.Program.largest(p, i, n),
    Equal.sym(Nat, Pg.Program.largest(p, i, n), Pg.Program.largest.go(n, ds, t), largest.eq(p, ds, i, n, rd)), h2)

# the run of 1 + j + r steps, by the step of t
def split.of(s: Maybe<Bk.Term>, +j: Nat, +r: Nat, +ds: List<&2, Bk.Def>, +u: Bk.Term,
  e: {El.Eval.run(j, ds, s) == Some{u} : Maybe<Bk.Term>},
  ih: @t1: Bk.Term -> {El.Eval.steps(j, ds, t1) == Some{u} : Maybe<Bk.Term>} ->
    {El.Eval.steps(Nat.add(j, r), ds, t1) == El.Eval.steps(r, ds, u) : Maybe<Bk.Term>}) ->
  {El.Eval.run(Nat.add(j, r), ds, s) == El.Eval.steps(r, ds, u) : Maybe<Bk.Term>}:
  match s:
    case None{}:
      Empty.absurd({El.Eval.run(Nat.add(j, r), ds, None{}) == El.Eval.steps(r, ds, u) : Maybe<Bk.Term>},
        tsome.ne(u, Equal.trans(Maybe<Bk.Term>, None{}, El.Eval.run(j, ds, None{}), Some{u},
          Equal.sym(Maybe<Bk.Term>, El.Eval.run(j, ds, None{}), None{}, run.none(j, ds)), e)))
    case Some{+t1}:
      ih(t1, e)

# the run of j + r steps from t is the run of r steps from where j steps lead
def steps.split(j: Nat, +r: Nat, +ds: List<&2, Bk.Def>, +t: Bk.Term, +u: Bk.Term,
  e: {El.Eval.steps(j, ds, t) == Some{u} : Maybe<Bk.Term>}) ->
  {El.Eval.steps(Nat.add(j, r), ds, t) == El.Eval.steps(r, ds, u) : Maybe<Bk.Term>}:
  match j:
    case 0n:
      %tsome.inj(t, u, e) : {El.Eval.steps(Nat.add(0n, r), ds, t) == El.Eval.steps(r, ds, _) : Maybe<Bk.Term>}
      {==}
    case 1n+(+q):
      split.of(El.Eval.step(ds, t), q, r, ds, u, e, t1 => e1 => steps.split(q, r, ds, t1, u, e1))

# and so has its step, when the run reaches the list of bytes o at n
def largest.ge.step(+p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +j: Nat, +n: Nat, +u: Bk.Term,
  +o: List<&2, Word(8n)>,
  rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  hj: N.Le(j, n),
  +e: {El.Eval.steps(j, ds, Pg.Program.start(i)) == Some{u} : Maybe<Bk.Term>},
  er: {Pg.Program.result(ds, El.Eval.steps(n, ds, Pg.Program.start(i))) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}) ->
  N.Le(D.StepSize(ds, u), Pg.Program.largest(p, i, n)):
  +t = Pg.Program.start(i)
  +r = Nat.sub(n, j)
  +en = sub_add(n, j, hj)
  +er1 = {(%Equal.sym(Nat, Nat.add(j, r), n, en) : {Pg.Program.result(ds, El.Eval.steps(_, ds, t)) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}; er) :
    {Pg.Program.result(ds, El.Eval.steps(Nat.add(j, r), ds, t)) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}}
  +er2 = {(%steps.split(j, r, ds, t, u, e) : {Pg.Program.result(ds, _) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}; er1) :
    {Pg.Program.result(ds, El.Eval.steps(r, ds, u)) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}}
  +h1 = N.le_trans(D.StepSize(ds, u), Pg.Program.largest.go(r, ds, u), Pg.Program.largest.go(Nat.add(j, r), ds, t),
    largest.step(r, ds, u, o, er2), largest.rest(j, r, ds, t, u, e))
  +h2 = N.le_rw_r(D.StepSize(ds, u), Pg.Program.largest.go(Nat.add(j, r), ds, t), Pg.Program.largest.go(n, ds, t),
    Equal.cong(Nat, Nat, x => Pg.Program.largest.go(x, ds, t), Nat.add(j, r), n, en), h1)
  N.le_rw_r(D.StepSize(ds, u), Pg.Program.largest.go(n, ds, t), Pg.Program.largest(p, i, n),
    Equal.sym(Nat, Pg.Program.largest(p, i, n), Pg.Program.largest.go(n, ds, t), largest.eq(p, ds, i, n, rd)), h2)

# The input and the output
# ------------------------

# the start term, main applied to the input's bytes, has 72 nodes a byte and
# 5 more
def bit.size(b: Bool) -> {Pg.Term.size(Pg.Program.bit(b)) == 3n : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# a word of n bits has 8 nodes a bit and 3 more
def word.size(n: Nat, w: Word(n)) -> {Pg.Term.size(Pg.Program.word(n, w)) == 3n+Nat.mul(8n, n) : Nat}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+(+p):
      match w:
        case WCon{+b, +t}:
          +W = Pg.Term.size(Pg.Program.word(p, t))
          %Equal.sym(Nat, Pg.Term.size(Pg.Program.bit(b)), 3n, bit.size(b)) :
            {3n+Nat.add(_, 1n+Nat.add(W, 1n)) == 3n+Nat.mul(8n, 1n+p) : Nat}
          Equal.trans(Nat, 7n+Nat.add(W, 1n), 8n+W, 3n+Nat.mul(8n, 1n+p),
            Equal.cong(Nat, Nat, x => 7n+x, Nat.add(W, 1n), 1n+W, add_one(W)),
            Equal.trans(Nat, 8n+W, 11n+Nat.mul(8n, p), 3n+Nat.mul(8n, 1n+p),
              Equal.cong(Nat, Nat, x => 8n+x, W, 3n+Nat.mul(8n, p), word.size(p, t)),
              Equal.sym(Nat, 3n+Nat.mul(8n, 1n+p), 11n+Nat.mul(8n, p),
                Equal.cong(Nat, Nat, x => 3n+x, Nat.mul(8n, 1n+p), Nat.add(8n, Nat.mul(8n, p)), mul_succ_r(8n, p)))))

# the bytes of a list: 72 nodes a byte and 3 more
def bytes.size(i: List<&2, Word(8n)>) -> {Pg.Term.size(Pg.Program.bytes(i)) == 3n+Nat.mul(72n, List.length(&2, Word(8n), i)) : Nat}:
  match i:
    case Nil{}:
      {==}
    case Con{+b, +rest}:
      +B = Pg.Term.size(Pg.Program.bytes(rest))
      +l = List.length(&2, Word(8n), rest)
      %Equal.sym(Nat, Pg.Term.size(Pg.Program.word(8n, b)), 3n+Nat.mul(8n, 8n), word.size(8n, b)) :
        {3n+Nat.add(_, 1n+Nat.add(B, 1n)) == 3n+Nat.mul(72n, 1n+l) : Nat}
      Equal.trans(Nat, 71n+Nat.add(B, 1n), 72n+B, 3n+Nat.mul(72n, 1n+l),
        Equal.cong(Nat, Nat, x => 71n+x, Nat.add(B, 1n), 1n+B, add_one(B)),
        Equal.trans(Nat, 72n+B, 75n+Nat.mul(72n, l), 3n+Nat.mul(72n, 1n+l),
          Equal.cong(Nat, Nat, x => 72n+x, B, 3n+Nat.mul(72n, l), bytes.size(rest)),
          Equal.sym(Nat, 3n+Nat.mul(72n, 1n+l), 75n+Nat.mul(72n, l),
            Equal.cong(Nat, Nat, x => 3n+x, Nat.mul(72n, 1n+l), Nat.add(72n, Nat.mul(72n, l)), mul_succ_r(72n, l)))))

def start.size(+i: List<&2, Word(8n)>) ->
  {Pg.Term.size(Pg.Program.start(i)) == 5n+Nat.mul(72n, List.length(&2, Word(8n), i)) : Nat}:
  Equal.cong(Nat, Nat, x => 2n+x, Pg.Term.size(Pg.Program.bytes(i)), 3n+Nat.mul(72n, List.length(&2, Word(8n), i)), bytes.size(i))

# so the input has at most S / 72 bytes
def start.le(+p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +n: Nat,
  rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>}) ->
  N.Le(5n+Nat.mul(72n, List.length(&2, Word(8n), i)), Pg.Program.largest(p, i, n)):
  +t = Pg.Program.start(i)
  +h = N.le_rw_l(Pg.Term.size(t), 5n+Nat.mul(72n, List.length(&2, Word(8n), i)), Pg.Program.largest.go(n, ds, t), start.size(i),
    largest.self(n, ds, t))
  N.le_rw_r(5n+Nat.mul(72n, List.length(&2, Word(8n), i)), Pg.Program.largest.go(n, ds, t), Pg.Program.largest(p, i, n),
    Equal.sym(Nat, Pg.Program.largest(p, i, n), Pg.Program.largest.go(n, ds, t), largest.eq(p, ds, i, n, rd)), h)

# Program.unword and Program.unbytes read a term by one nested pattern, whose
# other terms give None: the proofs below take each constructor at each level
# of it, since a default case does not say which constructor the term has

def WIsNone(-n: Nat, m: Maybe<&2, Word(n)>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{_}:
      Empty

def wsome.ne(-n: Nat, -x: Word(n), e: {None{} == Some{x} : Maybe<&2, Word(n)>}) -> Empty:
  %e : WIsNone(n, _)
  Unit{}

def word.no(+n: Nat, +t: Bk.Term, -w: Word(n), e: {None{} == Some{w} : Maybe<&2, Word(n)>}) ->
  {Pg.Term.size(t) == 3n+Nat.mul(8n, n) : Nat}:
  Empty.absurd({Pg.Term.size(t) == 3n+Nat.mul(8n, n) : Nat}, wsome.ne(n, w, e))

# a word's term, by what unword.con gives: 3 nodes for the bit and 5 more
def wcon.size(ok: Bool, mb: Maybe<&2, Bool>, +p: Nat, mw: Maybe<&2, Word(p)>, -w: Word(1n+p), +sw: Nat,
  e: {Pg.Program.unword.con(p, ok, mb, mw) == Some{w} : Maybe<&2, Word(1n+p)>},
  hw: @y: Word(p) -> {mw == Some{y} : Maybe<&2, Word(p)>} -> {sw == 3n+Nat.mul(8n, p) : Nat}) ->
  {7n+Nat.add(sw, 1n) == 3n+Nat.mul(8n, 1n+p) : Nat}:
  match ok mb mw:
    case True{} Some{_} Some{+y}:
      +M = Nat.mul(8n, p)
      %Equal.sym(Nat, sw, 3n+M, hw(y, {==})) : {7n+Nat.add(_, 1n) == 3n+Nat.mul(8n, 1n+p) : Nat}
      Equal.trans(Nat, 7n+Nat.add(3n+M, 1n), 11n+M, 3n+Nat.mul(8n, 1n+p),
        Equal.cong(Nat, Nat, x => 10n+x, Nat.add(M, 1n), 1n+M, add_one(M)),
        Equal.sym(Nat, 3n+Nat.mul(8n, 1n+p), 11n+M,
          Equal.cong(Nat, Nat, x => 3n+x, Nat.mul(8n, 1n+p), Nat.add(8n, M), mul_succ_r(8n, p))))
    case True{} Some{_} None{}:
      Empty.absurd({7n+Nat.add(sw, 1n) == 3n+Nat.mul(8n, 1n+p) : Nat}, wsome.ne(1n+p, w, e))
    case True{} None{} _:
      Empty.absurd({7n+Nat.add(sw, 1n) == 3n+Nat.mul(8n, 1n+p) : Nat}, wsome.ne(1n+p, w, e))
    case False{} _ _:
      Empty.absurd({7n+Nat.add(sw, 1n) == 3n+Nat.mul(8n, 1n+p) : Nat}, wsome.ne(1n+p, w, e))

# a term that Program.unword reads as a word of n bits has 8 nodes a bit and
# 3 more
def unword.size(n: Nat, +t: Bk.Term, -w: Word(n), e: {Pg.Program.unword(n, t) == Some{w} : Maybe<&2, Word(n)>}) ->
  {Pg.Term.size(t) == 3n+Nat.mul(8n, n) : Nat}:
  match n:
    case 0n:
      match t:
        case Bk.Term.Var{_}: word.no(0n, t, w, e)
        case Bk.Term.Ref{_}: word.no(0n, t, w, e)
        case Bk.Term.Ann{_, _}: word.no(0n, t, w, e)
        case Bk.Term.Let{_, _, _}: word.no(0n, t, w, e)
        case Bk.Term.Typ{_}: word.no(0n, t, w, e)
        case Bk.Term.Min{_, _}: word.no(0n, t, w, e)
        case Bk.Term.All{_, _, _}: word.no(0n, t, w, e)
        case Bk.Term.Lam{_, _}: word.no(0n, t, w, e)
        case Bk.Term.App{_, _, _}: word.no(0n, t, w, e)
        case Bk.Term.Sig{_, _, _}: word.no(0n, t, w, e)
        case Bk.Term.Tup{+q, +a, +b}:
          match q:
            case Bk.Quan.Q0{}: word.no(0n, t, w, e)
            case Bk.Quan.Q1{}:
              match a:
                case Bk.Term.Var{_}: word.no(0n, t, w, e)
                case Bk.Term.Ref{_}: word.no(0n, t, w, e)
                case Bk.Term.Ann{_, _}: word.no(0n, t, w, e)
                case Bk.Term.Let{_, _, _}: word.no(0n, t, w, e)
                case Bk.Term.Typ{_}: word.no(0n, t, w, e)
                case Bk.Term.Min{_, _}: word.no(0n, t, w, e)
                case Bk.Term.All{_, _, _}: word.no(0n, t, w, e)
                case Bk.Term.Lam{_, _}: word.no(0n, t, w, e)
                case Bk.Term.App{_, _, _}: word.no(0n, t, w, e)
                case Bk.Term.Sig{_, _, _}: word.no(0n, t, w, e)
                case Bk.Term.Tup{_, _, _}: word.no(0n, t, w, e)
                case Bk.Term.Prj{_}: word.no(0n, t, w, e)
                case Bk.Term.Enu{_}: word.no(0n, t, w, e)
                case Bk.Term.Lab{+k}:
                  match b:
                    case Bk.Term.Var{_}: word.no(0n, t, w, e)
                    case Bk.Term.Ref{_}: word.no(0n, t, w, e)
                    case Bk.Term.Ann{_, _}: word.no(0n, t, w, e)
                    case Bk.Term.Let{_, _, _}: word.no(0n, t, w, e)
                    case Bk.Term.Typ{_}: word.no(0n, t, w, e)
                    case Bk.Term.Min{_, _}: word.no(0n, t, w, e)
                    case Bk.Term.All{_, _, _}: word.no(0n, t, w, e)
                    case Bk.Term.Lam{_, _}: word.no(0n, t, w, e)
                    case Bk.Term.App{_, _, _}: word.no(0n, t, w, e)
                    case Bk.Term.Sig{_, _, _}: word.no(0n, t, w, e)
                    case Bk.Term.Tup{_, _, _}: word.no(0n, t, w, e)
                    case Bk.Term.Prj{_}: word.no(0n, t, w, e)
                    case Bk.Term.Enu{_}: word.no(0n, t, w, e)
                    case Bk.Term.Lab{+u}:
                      {==}
                    case Bk.Term.Mat{_, _, _}: word.no(0n, t, w, e)
                    case Bk.Term.Efq{}: word.no(0n, t, w, e)
                    case Bk.Term.Eql{_, _, _}: word.no(0n, t, w, e)
                    case Bk.Term.Rfl{}: word.no(0n, t, w, e)
                    case Bk.Term.Rwt{_, _, _}: word.no(0n, t, w, e)
                case Bk.Term.Mat{_, _, _}: word.no(0n, t, w, e)
                case Bk.Term.Efq{}: word.no(0n, t, w, e)
                case Bk.Term.Eql{_, _, _}: word.no(0n, t, w, e)
                case Bk.Term.Rfl{}: word.no(0n, t, w, e)
                case Bk.Term.Rwt{_, _, _}: word.no(0n, t, w, e)
            case Bk.Quan.Q2{}: word.no(0n, t, w, e)
        case Bk.Term.Prj{_}: word.no(0n, t, w, e)
        case Bk.Term.Enu{_}: word.no(0n, t, w, e)
        case Bk.Term.Lab{_}: word.no(0n, t, w, e)
        case Bk.Term.Mat{_, _, _}: word.no(0n, t, w, e)
        case Bk.Term.Efq{}: word.no(0n, t, w, e)
        case Bk.Term.Eql{_, _, _}: word.no(0n, t, w, e)
        case Bk.Term.Rfl{}: word.no(0n, t, w, e)
        case Bk.Term.Rwt{_, _, _}: word.no(0n, t, w, e)
    case 1n+(+p):
      match t:
        case Bk.Term.Var{_}: word.no(1n+p, t, w, e)
        case Bk.Term.Ref{_}: word.no(1n+p, t, w, e)
        case Bk.Term.Ann{_, _}: word.no(1n+p, t, w, e)
        case Bk.Term.Let{_, _, _}: word.no(1n+p, t, w, e)
        case Bk.Term.Typ{_}: word.no(1n+p, t, w, e)
        case Bk.Term.Min{_, _}: word.no(1n+p, t, w, e)
        case Bk.Term.All{_, _, _}: word.no(1n+p, t, w, e)
        case Bk.Term.Lam{_, _}: word.no(1n+p, t, w, e)
        case Bk.Term.App{_, _, _}: word.no(1n+p, t, w, e)
        case Bk.Term.Sig{_, _, _}: word.no(1n+p, t, w, e)
        case Bk.Term.Tup{+q, +a, +b}:
          match q:
            case Bk.Quan.Q0{}: word.no(1n+p, t, w, e)
            case Bk.Quan.Q1{}:
              match a:
                case Bk.Term.Var{_}: word.no(1n+p, t, w, e)
                case Bk.Term.Ref{_}: word.no(1n+p, t, w, e)
                case Bk.Term.Ann{_, _}: word.no(1n+p, t, w, e)
                case Bk.Term.Let{_, _, _}: word.no(1n+p, t, w, e)
                case Bk.Term.Typ{_}: word.no(1n+p, t, w, e)
                case Bk.Term.Min{_, _}: word.no(1n+p, t, w, e)
                case Bk.Term.All{_, _, _}: word.no(1n+p, t, w, e)
                case Bk.Term.Lam{_, _}: word.no(1n+p, t, w, e)
                case Bk.Term.App{_, _, _}: word.no(1n+p, t, w, e)
                case Bk.Term.Sig{_, _, _}: word.no(1n+p, t, w, e)
                case Bk.Term.Tup{_, _, _}: word.no(1n+p, t, w, e)
                case Bk.Term.Prj{_}: word.no(1n+p, t, w, e)
                case Bk.Term.Enu{_}: word.no(1n+p, t, w, e)
                case Bk.Term.Lab{+k}:
                  match b:
                    case Bk.Term.Var{_}: word.no(1n+p, t, w, e)
                    case Bk.Term.Ref{_}: word.no(1n+p, t, w, e)
                    case Bk.Term.Ann{_, _}: word.no(1n+p, t, w, e)
                    case Bk.Term.Let{_, _, _}: word.no(1n+p, t, w, e)
                    case Bk.Term.Typ{_}: word.no(1n+p, t, w, e)
                    case Bk.Term.Min{_, _}: word.no(1n+p, t, w, e)
                    case Bk.Term.All{_, _, _}: word.no(1n+p, t, w, e)
                    case Bk.Term.Lam{_, _}: word.no(1n+p, t, w, e)
                    case Bk.Term.App{_, _, _}: word.no(1n+p, t, w, e)
                    case Bk.Term.Sig{_, _, _}: word.no(1n+p, t, w, e)
                    case Bk.Term.Tup{+q1, +b1, +b2}:
                      match q1:
                        case Bk.Quan.Q0{}: word.no(1n+p, t, w, e)
                        case Bk.Quan.Q1{}:
                          match b1:
                            case Bk.Term.Var{_}: word.no(1n+p, t, w, e)
                            case Bk.Term.Ref{_}: word.no(1n+p, t, w, e)
                            case Bk.Term.Ann{_, _}: word.no(1n+p, t, w, e)
                            case Bk.Term.Let{_, _, _}: word.no(1n+p, t, w, e)
                            case Bk.Term.Typ{_}: word.no(1n+p, t, w, e)
                            case Bk.Term.Min{_, _}: word.no(1n+p, t, w, e)
                            case Bk.Term.All{_, _, _}: word.no(1n+p, t, w, e)
                            case Bk.Term.Lam{_, _}: word.no(1n+p, t, w, e)
                            case Bk.Term.App{_, _, _}: word.no(1n+p, t, w, e)
                            case Bk.Term.Sig{_, _, _}: word.no(1n+p, t, w, e)
                            case Bk.Term.Tup{+q2, +x1, +x2}:
                              match q2:
                                case Bk.Quan.Q0{}: word.no(1n+p, t, w, e)
                                case Bk.Quan.Q1{}:
                                  match x1:
                                    case Bk.Term.Var{_}: word.no(1n+p, t, w, e)
                                    case Bk.Term.Ref{_}: word.no(1n+p, t, w, e)
                                    case Bk.Term.Ann{_, _}: word.no(1n+p, t, w, e)
                                    case Bk.Term.Let{_, _, _}: word.no(1n+p, t, w, e)
                                    case Bk.Term.Typ{_}: word.no(1n+p, t, w, e)
                                    case Bk.Term.Min{_, _}: word.no(1n+p, t, w, e)
                                    case Bk.Term.All{_, _, _}: word.no(1n+p, t, w, e)
                                    case Bk.Term.Lam{_, _}: word.no(1n+p, t, w, e)
                                    case Bk.Term.App{_, _, _}: word.no(1n+p, t, w, e)
                                    case Bk.Term.Sig{_, _, _}: word.no(1n+p, t, w, e)
                                    case Bk.Term.Tup{_, _, _}: word.no(1n+p, t, w, e)
                                    case Bk.Term.Prj{_}: word.no(1n+p, t, w, e)
                                    case Bk.Term.Enu{_}: word.no(1n+p, t, w, e)
                                    case Bk.Term.Lab{+bb}:
                                      match x2:
                                        case Bk.Term.Var{_}: word.no(1n+p, t, w, e)
                                        case Bk.Term.Ref{_}: word.no(1n+p, t, w, e)
                                        case Bk.Term.Ann{_, _}: word.no(1n+p, t, w, e)
                                        case Bk.Term.Let{_, _, _}: word.no(1n+p, t, w, e)
                                        case Bk.Term.Typ{_}: word.no(1n+p, t, w, e)
                                        case Bk.Term.Min{_, _}: word.no(1n+p, t, w, e)
                                        case Bk.Term.All{_, _, _}: word.no(1n+p, t, w, e)
                                        case Bk.Term.Lam{_, _}: word.no(1n+p, t, w, e)
                                        case Bk.Term.App{_, _, _}: word.no(1n+p, t, w, e)
                                        case Bk.Term.Sig{_, _, _}: word.no(1n+p, t, w, e)
                                        case Bk.Term.Tup{_, _, _}: word.no(1n+p, t, w, e)
                                        case Bk.Term.Prj{_}: word.no(1n+p, t, w, e)
                                        case Bk.Term.Enu{_}: word.no(1n+p, t, w, e)
                                        case Bk.Term.Lab{+u1}:
                                          match b2:
                                            case Bk.Term.Var{_}: word.no(1n+p, t, w, e)
                                            case Bk.Term.Ref{_}: word.no(1n+p, t, w, e)
                                            case Bk.Term.Ann{_, _}: word.no(1n+p, t, w, e)
                                            case Bk.Term.Let{_, _, _}: word.no(1n+p, t, w, e)
                                            case Bk.Term.Typ{_}: word.no(1n+p, t, w, e)
                                            case Bk.Term.Min{_, _}: word.no(1n+p, t, w, e)
                                            case Bk.Term.All{_, _, _}: word.no(1n+p, t, w, e)
                                            case Bk.Term.Lam{_, _}: word.no(1n+p, t, w, e)
                                            case Bk.Term.App{_, _, _}: word.no(1n+p, t, w, e)
                                            case Bk.Term.Sig{_, _, _}: word.no(1n+p, t, w, e)
                                            case Bk.Term.Tup{+q3, +x, +y}:
                                              match q3:
                                                case Bk.Quan.Q0{}: word.no(1n+p, t, w, e)
                                                case Bk.Quan.Q1{}:
                                                  match y:
                                                    case Bk.Term.Var{_}: word.no(1n+p, t, w, e)
                                                    case Bk.Term.Ref{_}: word.no(1n+p, t, w, e)
                                                    case Bk.Term.Ann{_, _}: word.no(1n+p, t, w, e)
                                                    case Bk.Term.Let{_, _, _}: word.no(1n+p, t, w, e)
                                                    case Bk.Term.Typ{_}: word.no(1n+p, t, w, e)
                                                    case Bk.Term.Min{_, _}: word.no(1n+p, t, w, e)
                                                    case Bk.Term.All{_, _, _}: word.no(1n+p, t, w, e)
                                                    case Bk.Term.Lam{_, _}: word.no(1n+p, t, w, e)
                                                    case Bk.Term.App{_, _, _}: word.no(1n+p, t, w, e)
                                                    case Bk.Term.Sig{_, _, _}: word.no(1n+p, t, w, e)
                                                    case Bk.Term.Tup{_, _, _}: word.no(1n+p, t, w, e)
                                                    case Bk.Term.Prj{_}: word.no(1n+p, t, w, e)
                                                    case Bk.Term.Enu{_}: word.no(1n+p, t, w, e)
                                                    case Bk.Term.Lab{+u2}:
                                                      wcon.size(Sd.Name.is_eq(k, Pg.Program.name.wcon()) && Sd.Name.is_eq(u1, Pg.Program.name.unit()) && Sd.Name.is_eq(u2, Pg.Program.name.unit()),
                                                        Pg.Program.unbit(bb), p, Pg.Program.unword(p, x), w, Pg.Term.size(x), e, y => ey => unword.size(p, x, y, ey))
                                                    case Bk.Term.Mat{_, _, _}: word.no(1n+p, t, w, e)
                                                    case Bk.Term.Efq{}: word.no(1n+p, t, w, e)
                                                    case Bk.Term.Eql{_, _, _}: word.no(1n+p, t, w, e)
                                                    case Bk.Term.Rfl{}: word.no(1n+p, t, w, e)
                                                    case Bk.Term.Rwt{_, _, _}: word.no(1n+p, t, w, e)
                                                case Bk.Quan.Q2{}: word.no(1n+p, t, w, e)
                                            case Bk.Term.Prj{_}: word.no(1n+p, t, w, e)
                                            case Bk.Term.Enu{_}: word.no(1n+p, t, w, e)
                                            case Bk.Term.Lab{_}: word.no(1n+p, t, w, e)
                                            case Bk.Term.Mat{_, _, _}: word.no(1n+p, t, w, e)
                                            case Bk.Term.Efq{}: word.no(1n+p, t, w, e)
                                            case Bk.Term.Eql{_, _, _}: word.no(1n+p, t, w, e)
                                            case Bk.Term.Rfl{}: word.no(1n+p, t, w, e)
                                            case Bk.Term.Rwt{_, _, _}: word.no(1n+p, t, w, e)
                                        case Bk.Term.Mat{_, _, _}: word.no(1n+p, t, w, e)
                                        case Bk.Term.Efq{}: word.no(1n+p, t, w, e)
                                        case Bk.Term.Eql{_, _, _}: word.no(1n+p, t, w, e)
                                        case Bk.Term.Rfl{}: word.no(1n+p, t, w, e)
                                        case Bk.Term.Rwt{_, _, _}: word.no(1n+p, t, w, e)
                                    case Bk.Term.Mat{_, _, _}: word.no(1n+p, t, w, e)
                                    case Bk.Term.Efq{}: word.no(1n+p, t, w, e)
                                    case Bk.Term.Eql{_, _, _}: word.no(1n+p, t, w, e)
                                    case Bk.Term.Rfl{}: word.no(1n+p, t, w, e)
                                    case Bk.Term.Rwt{_, _, _}: word.no(1n+p, t, w, e)
                                case Bk.Quan.Q2{}: word.no(1n+p, t, w, e)
                            case Bk.Term.Prj{_}: word.no(1n+p, t, w, e)
                            case Bk.Term.Enu{_}: word.no(1n+p, t, w, e)
                            case Bk.Term.Lab{_}: word.no(1n+p, t, w, e)
                            case Bk.Term.Mat{_, _, _}: word.no(1n+p, t, w, e)
                            case Bk.Term.Efq{}: word.no(1n+p, t, w, e)
                            case Bk.Term.Eql{_, _, _}: word.no(1n+p, t, w, e)
                            case Bk.Term.Rfl{}: word.no(1n+p, t, w, e)
                            case Bk.Term.Rwt{_, _, _}: word.no(1n+p, t, w, e)
                        case Bk.Quan.Q2{}: word.no(1n+p, t, w, e)
                    case Bk.Term.Prj{_}: word.no(1n+p, t, w, e)
                    case Bk.Term.Enu{_}: word.no(1n+p, t, w, e)
                    case Bk.Term.Lab{_}: word.no(1n+p, t, w, e)
                    case Bk.Term.Mat{_, _, _}: word.no(1n+p, t, w, e)
                    case Bk.Term.Efq{}: word.no(1n+p, t, w, e)
                    case Bk.Term.Eql{_, _, _}: word.no(1n+p, t, w, e)
                    case Bk.Term.Rfl{}: word.no(1n+p, t, w, e)
                    case Bk.Term.Rwt{_, _, _}: word.no(1n+p, t, w, e)
                case Bk.Term.Mat{_, _, _}: word.no(1n+p, t, w, e)
                case Bk.Term.Efq{}: word.no(1n+p, t, w, e)
                case Bk.Term.Eql{_, _, _}: word.no(1n+p, t, w, e)
                case Bk.Term.Rfl{}: word.no(1n+p, t, w, e)
                case Bk.Term.Rwt{_, _, _}: word.no(1n+p, t, w, e)
            case Bk.Quan.Q2{}: word.no(1n+p, t, w, e)
        case Bk.Term.Prj{_}: word.no(1n+p, t, w, e)
        case Bk.Term.Enu{_}: word.no(1n+p, t, w, e)
        case Bk.Term.Lab{_}: word.no(1n+p, t, w, e)
        case Bk.Term.Mat{_, _, _}: word.no(1n+p, t, w, e)
        case Bk.Term.Efq{}: word.no(1n+p, t, w, e)
        case Bk.Term.Eql{_, _, _}: word.no(1n+p, t, w, e)
        case Bk.Term.Rfl{}: word.no(1n+p, t, w, e)
        case Bk.Term.Rwt{_, _, _}: word.no(1n+p, t, w, e)

# the empty list's term, by what unbytes.nil gives
def unil.size(ok: Bool, +o: List<&2, Word(8n)>, e: {Pg.Program.unbytes.nil(ok) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}) ->
  {3n == 3n+Nat.mul(72n, List.length(&2, Word(8n), o)) : Nat}:
  match ok:
    case True{}:
      %D.mb.inj(Nil{}, o, e) : {3n == 3n+Nat.mul(72n, List.length(&2, Word(8n), _)) : Nat}
      {==}
    case False{}:
      Empty.absurd({3n == 3n+Nat.mul(72n, List.length(&2, Word(8n), o)) : Nat}, osome.ne(o, e))

# a list's term, by what unbytes.con gives: the byte's 67 nodes and 5 more
def ucon.size(ok: Bool, mw: Maybe<&2, Word(8n)>, bs: Maybe<&2, List<&2, Word(8n)>>, +o: List<&2, Word(8n)>, +sw: Nat, +sr: Nat,
  e: {Pg.Program.unbytes.con(ok, mw, bs) == Some{o} : Maybe<&2, List<&2, Word(8n)>>},
  hw: @x: Word(8n) -> {mw == Some{x} : Maybe<&2, Word(8n)>} -> {sw == 3n+Nat.mul(8n, 8n) : Nat},
  hr: @r: List<&2, Word(8n)> -> {bs == Some{r} : Maybe<&2, List<&2, Word(8n)>>} ->
    {sr == 3n+Nat.mul(72n, List.length(&2, Word(8n), r)) : Nat}) ->
  {3n+Nat.add(sw, 1n+Nat.add(sr, 1n)) == 3n+Nat.mul(72n, List.length(&2, Word(8n), o)) : Nat}:
  match ok mw bs:
    case True{} Some{+x} Some{+r}:
      +l = List.length(&2, Word(8n), r)
      +M = Nat.mul(72n, l)
      +W = {3n+Nat.mul(8n, 8n) : Nat}
      %D.mb.inj(Con{x, r}, o, e) : {3n+Nat.add(sw, 1n+Nat.add(sr, 1n)) == 3n+Nat.mul(72n, List.length(&2, Word(8n), _)) : Nat}
      %Equal.sym(Nat, sw, W, hw(x, {==})) : {3n+Nat.add(_, 1n+Nat.add(sr, 1n)) == 3n+Nat.mul(72n, List.length(&2, Word(8n), Con{x, r})) : Nat}
      %Equal.sym(Nat, sr, 3n+M, hr(r, {==})) : {3n+Nat.add(W, 1n+Nat.add(_, 1n)) == 3n+Nat.mul(72n, List.length(&2, Word(8n), Con{x, r})) : Nat}
      Equal.trans(Nat, 3n+Nat.add(W, 1n+Nat.add(3n+M, 1n)), 75n+M, 3n+Nat.mul(72n, 1n+l),
        Equal.cong(Nat, Nat, y => 74n+y, Nat.add(M, 1n), 1n+M, add_one(M)),
        Equal.sym(Nat, 3n+Nat.mul(72n, 1n+l), 75n+M,
          Equal.cong(Nat, Nat, y => 3n+y, Nat.mul(72n, 1n+l), Nat.add(72n, M), mul_succ_r(72n, l))))
    case True{} Some{_} None{}:
      Empty.absurd({3n+Nat.add(sw, 1n+Nat.add(sr, 1n)) == 3n+Nat.mul(72n, List.length(&2, Word(8n), o)) : Nat}, osome.ne(o, e))
    case True{} None{} _:
      Empty.absurd({3n+Nat.add(sw, 1n+Nat.add(sr, 1n)) == 3n+Nat.mul(72n, List.length(&2, Word(8n), o)) : Nat}, osome.ne(o, e))
    case False{} _ _:
      Empty.absurd({3n+Nat.add(sw, 1n+Nat.add(sr, 1n)) == 3n+Nat.mul(72n, List.length(&2, Word(8n), o)) : Nat}, osome.ne(o, e))

def out.no(+v: Bk.Term, +o: List<&2, Word(8n)>, e: {None{} == Some{o} : Maybe<&2, List<&2, Word(8n)>>}) ->
  {Pg.Term.size(v) == 3n+Nat.mul(72n, List.length(&2, Word(8n), o)) : Nat}:
  Empty.absurd({Pg.Term.size(v) == 3n+Nat.mul(72n, List.length(&2, Word(8n), o)) : Nat}, osome.ne(o, e))

# a term that Program.unbytes reads as the bytes o has 72 nodes a byte and 3
# more
def out.size(+v: Bk.Term, +o: List<&2, Word(8n)>,
  e: {Pg.Program.unbytes(v) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}) ->
  {Pg.Term.size(v) == 3n+Nat.mul(72n, List.length(&2, Word(8n), o)) : Nat}:
  match v:
    case Bk.Term.Var{_}: out.no(v, o, e)
    case Bk.Term.Ref{_}: out.no(v, o, e)
    case Bk.Term.Ann{_, _}: out.no(v, o, e)
    case Bk.Term.Let{_, _, _}: out.no(v, o, e)
    case Bk.Term.Typ{_}: out.no(v, o, e)
    case Bk.Term.Min{_, _}: out.no(v, o, e)
    case Bk.Term.All{_, _, _}: out.no(v, o, e)
    case Bk.Term.Lam{_, _}: out.no(v, o, e)
    case Bk.Term.App{_, _, _}: out.no(v, o, e)
    case Bk.Term.Sig{_, _, _}: out.no(v, o, e)
    case Bk.Term.Tup{+q, +a, +b}:
      match q:
        case Bk.Quan.Q0{}: out.no(v, o, e)
        case Bk.Quan.Q1{}:
          match a:
            case Bk.Term.Var{_}: out.no(v, o, e)
            case Bk.Term.Ref{_}: out.no(v, o, e)
            case Bk.Term.Ann{_, _}: out.no(v, o, e)
            case Bk.Term.Let{_, _, _}: out.no(v, o, e)
            case Bk.Term.Typ{_}: out.no(v, o, e)
            case Bk.Term.Min{_, _}: out.no(v, o, e)
            case Bk.Term.All{_, _, _}: out.no(v, o, e)
            case Bk.Term.Lam{_, _}: out.no(v, o, e)
            case Bk.Term.App{_, _, _}: out.no(v, o, e)
            case Bk.Term.Sig{_, _, _}: out.no(v, o, e)
            case Bk.Term.Tup{_, _, _}: out.no(v, o, e)
            case Bk.Term.Prj{_}: out.no(v, o, e)
            case Bk.Term.Enu{_}: out.no(v, o, e)
            case Bk.Term.Lab{+k}:
              match b:
                case Bk.Term.Var{_}: out.no(v, o, e)
                case Bk.Term.Ref{_}: out.no(v, o, e)
                case Bk.Term.Ann{_, _}: out.no(v, o, e)
                case Bk.Term.Let{_, _, _}: out.no(v, o, e)
                case Bk.Term.Typ{_}: out.no(v, o, e)
                case Bk.Term.Min{_, _}: out.no(v, o, e)
                case Bk.Term.All{_, _, _}: out.no(v, o, e)
                case Bk.Term.Lam{_, _}: out.no(v, o, e)
                case Bk.Term.App{_, _, _}: out.no(v, o, e)
                case Bk.Term.Sig{_, _, _}: out.no(v, o, e)
                case Bk.Term.Tup{+q2, +w, +b2}:
                  match q2:
                    case Bk.Quan.Q0{}: out.no(v, o, e)
                    case Bk.Quan.Q1{}:
                      match b2:
                        case Bk.Term.Var{_}: out.no(v, o, e)
                        case Bk.Term.Ref{_}: out.no(v, o, e)
                        case Bk.Term.Ann{_, _}: out.no(v, o, e)
                        case Bk.Term.Let{_, _, _}: out.no(v, o, e)
                        case Bk.Term.Typ{_}: out.no(v, o, e)
                        case Bk.Term.Min{_, _}: out.no(v, o, e)
                        case Bk.Term.All{_, _, _}: out.no(v, o, e)
                        case Bk.Term.Lam{_, _}: out.no(v, o, e)
                        case Bk.Term.App{_, _, _}: out.no(v, o, e)
                        case Bk.Term.Sig{_, _, _}: out.no(v, o, e)
                        case Bk.Term.Tup{+q3, +rest, +z}:
                          match q3:
                            case Bk.Quan.Q0{}: out.no(v, o, e)
                            case Bk.Quan.Q1{}:
                              match z:
                                case Bk.Term.Var{_}: out.no(v, o, e)
                                case Bk.Term.Ref{_}: out.no(v, o, e)
                                case Bk.Term.Ann{_, _}: out.no(v, o, e)
                                case Bk.Term.Let{_, _, _}: out.no(v, o, e)
                                case Bk.Term.Typ{_}: out.no(v, o, e)
                                case Bk.Term.Min{_, _}: out.no(v, o, e)
                                case Bk.Term.All{_, _, _}: out.no(v, o, e)
                                case Bk.Term.Lam{_, _}: out.no(v, o, e)
                                case Bk.Term.App{_, _, _}: out.no(v, o, e)
                                case Bk.Term.Sig{_, _, _}: out.no(v, o, e)
                                case Bk.Term.Tup{_, _, _}: out.no(v, o, e)
                                case Bk.Term.Prj{_}: out.no(v, o, e)
                                case Bk.Term.Enu{_}: out.no(v, o, e)
                                case Bk.Term.Lab{+u}:
                                  ucon.size(Sd.Name.is_eq(k, Pg.Program.name.con()) && Sd.Name.is_eq(u, Pg.Program.name.unit()),
                                    Pg.Program.unword(8n, w), Pg.Program.unbytes(rest), o, Pg.Term.size(w), Pg.Term.size(rest), e,
                                    x => ex => unword.size(8n, w, x, ex), r => er => out.size(rest, r, er))
                                case Bk.Term.Mat{_, _, _}: out.no(v, o, e)
                                case Bk.Term.Efq{}: out.no(v, o, e)
                                case Bk.Term.Eql{_, _, _}: out.no(v, o, e)
                                case Bk.Term.Rfl{}: out.no(v, o, e)
                                case Bk.Term.Rwt{_, _, _}: out.no(v, o, e)
                            case Bk.Quan.Q2{}: out.no(v, o, e)
                        case Bk.Term.Prj{_}: out.no(v, o, e)
                        case Bk.Term.Enu{_}: out.no(v, o, e)
                        case Bk.Term.Lab{_}: out.no(v, o, e)
                        case Bk.Term.Mat{_, _, _}: out.no(v, o, e)
                        case Bk.Term.Efq{}: out.no(v, o, e)
                        case Bk.Term.Eql{_, _, _}: out.no(v, o, e)
                        case Bk.Term.Rfl{}: out.no(v, o, e)
                        case Bk.Term.Rwt{_, _, _}: out.no(v, o, e)
                    case Bk.Quan.Q2{}: out.no(v, o, e)
                case Bk.Term.Prj{_}: out.no(v, o, e)
                case Bk.Term.Enu{_}: out.no(v, o, e)
                case Bk.Term.Lab{+u}:
                  unil.size(Sd.Name.is_eq(k, Pg.Program.name.nil()) && Sd.Name.is_eq(u, Pg.Program.name.unit()), o, e)
                case Bk.Term.Mat{_, _, _}: out.no(v, o, e)
                case Bk.Term.Efq{}: out.no(v, o, e)
                case Bk.Term.Eql{_, _, _}: out.no(v, o, e)
                case Bk.Term.Rfl{}: out.no(v, o, e)
                case Bk.Term.Rwt{_, _, _}: out.no(v, o, e)
            case Bk.Term.Mat{_, _, _}: out.no(v, o, e)
            case Bk.Term.Efq{}: out.no(v, o, e)
            case Bk.Term.Eql{_, _, _}: out.no(v, o, e)
            case Bk.Term.Rfl{}: out.no(v, o, e)
            case Bk.Term.Rwt{_, _, _}: out.no(v, o, e)
        case Bk.Quan.Q2{}: out.no(v, o, e)
    case Bk.Term.Prj{_}: out.no(v, o, e)
    case Bk.Term.Enu{_}: out.no(v, o, e)
    case Bk.Term.Lab{_}: out.no(v, o, e)
    case Bk.Term.Mat{_, _, _}: out.no(v, o, e)
    case Bk.Term.Efq{}: out.no(v, o, e)
    case Bk.Term.Eql{_, _, _}: out.no(v, o, e)
    case Bk.Term.Rfl{}: out.no(v, o, e)
    case Bk.Term.Rwt{_, _, _}: out.no(v, o, e)

# a value that the run gives as a list of bytes is a list of bytes
def out.val(b: Bool, +v: Bk.Term, +o: List<&2, Word(8n)>, e: {Pg.Program.result.if(b, v) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}) ->
  {Pg.Program.unbytes(v) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}:
  match b:
    case True{}:
      e
    case False{}:
      Empty.absurd({Pg.Program.unbytes(v) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}, osome.ne(o, e))

# the result o of the run, by the end r that it reaches in n steps
def out.of(r: Maybe<Bk.Term>, +p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +n: Nat, +o: List<&2, Word(8n)>,
  rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  er: {El.Eval.steps(n, ds, Pg.Program.start(i)) == r : Maybe<Bk.Term>},
  e: {Pg.Program.result(ds, r) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}) ->
  N.Le(3n+Nat.mul(72n, List.length(&2, Word(8n), o)), Pg.Program.largest(p, i, n)):
  match r:
    case None{}:
      Empty.absurd(N.Le(3n+Nat.mul(72n, List.length(&2, Word(8n), o)), Pg.Program.largest(p, i, n)), osome.ne(o, e))
    case Some{+v}:
      N.le_rw_l(Pg.Term.size(v), 3n+Nat.mul(72n, List.length(&2, Word(8n), o)), Pg.Program.largest(p, i, n),
        out.size(v, o, out.val(El.Eval.vals(ds, v, False{}), v, o, e)), largest.ge(p, ds, i, n, n, v, rd, N.le_refl(n), er))

# so the result o of the run has at most S / 72 bytes
def out.le(+p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +n: Nat, +o: List<&2, Word(8n)>,
  rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  e: {Pg.Program.result(ds, El.Eval.steps(n, ds, Pg.Program.start(i))) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}) ->
  N.Le(3n+Nat.mul(72n, List.length(&2, Word(8n), o)), Pg.Program.largest(p, i, n)):
  out.of(El.Eval.steps(n, ds, Pg.Program.start(i)), p, ds, i, n, o, rd, {==}, e)

# The book
# --------

# a node above two parts: Nsz is the nodes plus the addend
def nsz.two(+A: Nat, +B: Nat, +X: Nat, +Y: Nat, +n: Nat, ex: {X == Nat.add(A, Y) : Nat}, ey: {Y == Nat.add(B, n) : Nat}) ->
  {1n+X == 1n+Nat.add(Nat.add(A, B), n) : Nat}:
  Equal.cong(Nat, Nat, x => 1n+x, X, Nat.add(Nat.add(A, B), n),
    Equal.trans(Nat, X, Nat.add(A, Y), Nat.add(Nat.add(A, B), n), ex,
      Equal.trans(Nat, Nat.add(A, Y), Nat.add(A, Nat.add(B, n)), Nat.add(Nat.add(A, B), n),
        Equal.cong(Nat, Nat, x => Nat.add(A, x), Y, Nat.add(B, n), ey),
        Equal.sym(Nat, Nat.add(Nat.add(A, B), n), Nat.add(A, Nat.add(B, n)), N.add_assoc(A, B, n)))))

# a node above three parts
def nsz.three(+A: Nat, +B: Nat, +E: Nat, +X: Nat, +Y: Nat, +Z: Nat, +n: Nat, ex: {X == Nat.add(A, Y) : Nat},
  ey: {Y == Nat.add(B, Z) : Nat}, ez: {Z == Nat.add(E, n) : Nat}) ->
  {1n+X == 1n+Nat.add(Nat.add(A, Nat.add(B, E)), n) : Nat}:
  Equal.cong(Nat, Nat, x => 1n+x, X, Nat.add(Nat.add(A, Nat.add(B, E)), n),
    Equal.trans(Nat, X, Nat.add(A, Y), Nat.add(Nat.add(A, Nat.add(B, E)), n), ex,
      Equal.trans(Nat, Nat.add(A, Y), Nat.add(A, Nat.add(Nat.add(B, E), n)), Nat.add(Nat.add(A, Nat.add(B, E)), n),
        Equal.cong(Nat, Nat, x => Nat.add(A, x), Y, Nat.add(Nat.add(B, E), n),
          Equal.trans(Nat, Y, Nat.add(B, Z), Nat.add(Nat.add(B, E), n), ey,
            Equal.trans(Nat, Nat.add(B, Z), Nat.add(B, Nat.add(E, n)), Nat.add(Nat.add(B, E), n),
              Equal.cong(Nat, Nat, x => Nat.add(B, x), Z, Nat.add(E, n), ez),
              Equal.sym(Nat, Nat.add(Nat.add(B, E), n), Nat.add(B, Nat.add(E, n)), N.add_assoc(B, E, n))))),
        Equal.sym(Nat, Nat.add(Nat.add(A, Nat.add(B, E)), n), Nat.add(A, Nat.add(Nat.add(B, E), n)), N.add_assoc(A, Nat.add(B, E), n)))))

# img_small's Nsz(t, n) is t's nodes plus n
def size.nsz(t: Bk.Term, +n: Nat) -> {PG.Nsz(t, n) == Nat.add(Pg.Term.size(t), n) : Nat}:
  match t:
    case Bk.Term.Var{_}:
      {==}
    case Bk.Term.Ref{_}:
      {==}
    case Bk.Term.Ann{+x, +T}:
      nsz.two(Pg.Term.size(x), Pg.Term.size(T), PG.Nsz(x, PG.Nsz(T, n)), PG.Nsz(T, n), n, size.nsz(x, PG.Nsz(T, n)), size.nsz(T, n))
    case Bk.Term.Let{_, +v, +f}:
      nsz.two(Pg.Term.size(v), Pg.Term.size(f), PG.Nsz(v, PG.Nsz(f, n)), PG.Nsz(f, n), n, size.nsz(v, PG.Nsz(f, n)), size.nsz(f, n))
    case Bk.Term.Typ{+q}:
      Equal.cong(Nat, Nat, x => 1n+x, PG.Nsz(q, n), Nat.add(Pg.Term.size(q), n), size.nsz(q, n))
    case Bk.Term.Min{+a, +b}:
      nsz.two(Pg.Term.size(a), Pg.Term.size(b), PG.Nsz(a, PG.Nsz(b, n)), PG.Nsz(b, n), n, size.nsz(a, PG.Nsz(b, n)), size.nsz(b, n))
    case Bk.Term.All{_, +A, +B}:
      nsz.two(Pg.Term.size(A), Pg.Term.size(B), PG.Nsz(A, PG.Nsz(B, n)), PG.Nsz(B, n), n, size.nsz(A, PG.Nsz(B, n)), size.nsz(B, n))
    case Bk.Term.Lam{_, +f}:
      Equal.cong(Nat, Nat, x => 1n+x, PG.Nsz(f, n), Nat.add(Pg.Term.size(f), n), size.nsz(f, n))
    case Bk.Term.App{_, +f, +x}:
      nsz.two(Pg.Term.size(f), Pg.Term.size(x), PG.Nsz(f, PG.Nsz(x, n)), PG.Nsz(x, n), n, size.nsz(f, PG.Nsz(x, n)), size.nsz(x, n))
    case Bk.Term.Sig{_, +A, +B}:
      nsz.two(Pg.Term.size(A), Pg.Term.size(B), PG.Nsz(A, PG.Nsz(B, n)), PG.Nsz(B, n), n, size.nsz(A, PG.Nsz(B, n)), size.nsz(B, n))
    case Bk.Term.Tup{_, +a, +b}:
      nsz.two(Pg.Term.size(a), Pg.Term.size(b), PG.Nsz(a, PG.Nsz(b, n)), PG.Nsz(b, n), n, size.nsz(a, PG.Nsz(b, n)), size.nsz(b, n))
    case Bk.Term.Prj{+h}:
      Equal.cong(Nat, Nat, x => 1n+x, PG.Nsz(h, n), Nat.add(Pg.Term.size(h), n), size.nsz(h, n))
    case Bk.Term.Enu{_}:
      {==}
    case Bk.Term.Lab{_}:
      {==}
    case Bk.Term.Mat{_, +h, +m}:
      nsz.two(Pg.Term.size(h), Pg.Term.size(m), PG.Nsz(h, PG.Nsz(m, n)), PG.Nsz(m, n), n, size.nsz(h, PG.Nsz(m, n)), size.nsz(m, n))
    case Bk.Term.Efq{}:
      {==}
    case Bk.Term.Eql{+a, +b, +T}:
      nsz.three(Pg.Term.size(a), Pg.Term.size(b), Pg.Term.size(T), PG.Nsz(a, PG.Nsz(b, PG.Nsz(T, n))), PG.Nsz(b, PG.Nsz(T, n)),
        PG.Nsz(T, n), n, size.nsz(a, PG.Nsz(b, PG.Nsz(T, n))), size.nsz(b, PG.Nsz(T, n)), size.nsz(T, n))
    case Bk.Term.Rfl{}:
      {==}
    case Bk.Term.Rwt{+e, +P, +f}:
      nsz.three(Pg.Term.size(e), Pg.Term.size(P), Pg.Term.size(f), PG.Nsz(e, PG.Nsz(P, PG.Nsz(f, n))), PG.Nsz(P, PG.Nsz(f, n)),
        PG.Nsz(f, n), n, size.nsz(e, PG.Nsz(P, PG.Nsz(f, n))), size.nsz(P, PG.Nsz(f, n)), size.nsz(f, n))

# a constructor of k fields, of form X, has 3 nodes more than 3 A when X
# has A's
def ft.k(+A: Nat, +X: Nat, +k: Nat, h: N.Le(A, X)) -> N.Le(3n+A, Pg.Form.size.ctor(k, X)):
  N.le_trans(A, X, Nat.add(k, X), h, N.le_add_l(k, X))

# two parts of a term, a field between them (a name, or a quantity's 3)
def ft.two(+A: Nat, +B: Nat, +X: Nat, +Y: Nat, +E: Nat, ha: N.Le(A, X), hb: N.Le(B, Y)) ->
  N.Le(Nat.add(A, B), Nat.add(E, Nat.add(X, Y))):
  N.le_trans(Nat.add(A, B), Nat.add(X, Y), Nat.add(E, Nat.add(X, Y)), N.add_mono(A, X, B, Y, ha, hb), N.le_add_l(E, Nat.add(X, Y)))

# each node of a term is 3 nodes or more of its data form
def ft.ge(t: Bk.Term) -> N.Le(Tri(Pg.Term.size(t)), Pg.Form.size.term(t)):
  match t:
    case Bk.Term.Var{_}:
      Unit{}
    case Bk.Term.Ref{_}:
      Unit{}
    case Bk.Term.Ann{+x, +T}:
      %Equal.sym(Nat, Tri(Nat.add(Pg.Term.size(x), Pg.Term.size(T))), Nat.add(Tri(Pg.Term.size(x)), Tri(Pg.Term.size(T))), tri_add(Pg.Term.size(x), Pg.Term.size(T))) :
        N.Le(3n+_, Pg.Form.size.ctor(2n, Nat.add(Pg.Form.size.term(x), Pg.Form.size.term(T))))
      ft.k(Nat.add(Tri(Pg.Term.size(x)), Tri(Pg.Term.size(T))), Nat.add(Pg.Form.size.term(x), Pg.Form.size.term(T)), 2n,
        N.add_mono(Tri(Pg.Term.size(x)), Pg.Form.size.term(x), Tri(Pg.Term.size(T)), Pg.Form.size.term(T), ft.ge(x), ft.ge(T)))
    case Bk.Term.Let{_, +v, +f}:
      %Equal.sym(Nat, Tri(Nat.add(Pg.Term.size(v), Pg.Term.size(f))), Nat.add(Tri(Pg.Term.size(v)), Tri(Pg.Term.size(f))), tri_add(Pg.Term.size(v), Pg.Term.size(f))) :
        N.Le(3n+_, Pg.Form.size.ctor(3n, 3n+Nat.add(Pg.Form.size.term(v), Pg.Form.size.term(f))))
      ft.k(Nat.add(Tri(Pg.Term.size(v)), Tri(Pg.Term.size(f))), 3n+Nat.add(Pg.Form.size.term(v), Pg.Form.size.term(f)), 3n,
        ft.two(Tri(Pg.Term.size(v)), Tri(Pg.Term.size(f)), Pg.Form.size.term(v), Pg.Form.size.term(f), 3n, ft.ge(v), ft.ge(f)))
    case Bk.Term.Typ{+q}:
      ft.k(Tri(Pg.Term.size(q)), Pg.Form.size.term(q), 1n, ft.ge(q))
    case Bk.Term.Min{+a, +b}:
      %Equal.sym(Nat, Tri(Nat.add(Pg.Term.size(a), Pg.Term.size(b))), Nat.add(Tri(Pg.Term.size(a)), Tri(Pg.Term.size(b))), tri_add(Pg.Term.size(a), Pg.Term.size(b))) :
        N.Le(3n+_, Pg.Form.size.ctor(2n, Nat.add(Pg.Form.size.term(a), Pg.Form.size.term(b))))
      ft.k(Nat.add(Tri(Pg.Term.size(a)), Tri(Pg.Term.size(b))), Nat.add(Pg.Form.size.term(a), Pg.Form.size.term(b)), 2n,
        N.add_mono(Tri(Pg.Term.size(a)), Pg.Form.size.term(a), Tri(Pg.Term.size(b)), Pg.Form.size.term(b), ft.ge(a), ft.ge(b)))
    case Bk.Term.All{_, +A, +B}:
      %Equal.sym(Nat, Tri(Nat.add(Pg.Term.size(A), Pg.Term.size(B))), Nat.add(Tri(Pg.Term.size(A)), Tri(Pg.Term.size(B))), tri_add(Pg.Term.size(A), Pg.Term.size(B))) :
        N.Le(3n+_, Pg.Form.size.ctor(3n, 3n+Nat.add(Pg.Form.size.term(A), Pg.Form.size.term(B))))
      ft.k(Nat.add(Tri(Pg.Term.size(A)), Tri(Pg.Term.size(B))), 3n+Nat.add(Pg.Form.size.term(A), Pg.Form.size.term(B)), 3n,
        ft.two(Tri(Pg.Term.size(A)), Tri(Pg.Term.size(B)), Pg.Form.size.term(A), Pg.Form.size.term(B), 3n, ft.ge(A), ft.ge(B)))
    case Bk.Term.Lam{_, +f}:
      ft.k(Tri(Pg.Term.size(f)), 3n+Pg.Form.size.term(f), 2n,
        N.le_trans(Tri(Pg.Term.size(f)), Pg.Form.size.term(f), 3n+Pg.Form.size.term(f), ft.ge(f), N.le_add_l(3n, Pg.Form.size.term(f))))
    case Bk.Term.App{_, +f, +x}:
      %Equal.sym(Nat, Tri(Nat.add(Pg.Term.size(f), Pg.Term.size(x))), Nat.add(Tri(Pg.Term.size(f)), Tri(Pg.Term.size(x))), tri_add(Pg.Term.size(f), Pg.Term.size(x))) :
        N.Le(3n+_, Pg.Form.size.ctor(3n, 3n+Nat.add(Pg.Form.size.term(f), Pg.Form.size.term(x))))
      ft.k(Nat.add(Tri(Pg.Term.size(f)), Tri(Pg.Term.size(x))), 3n+Nat.add(Pg.Form.size.term(f), Pg.Form.size.term(x)), 3n,
        ft.two(Tri(Pg.Term.size(f)), Tri(Pg.Term.size(x)), Pg.Form.size.term(f), Pg.Form.size.term(x), 3n, ft.ge(f), ft.ge(x)))
    case Bk.Term.Sig{_, +A, +B}:
      %Equal.sym(Nat, Tri(Nat.add(Pg.Term.size(A), Pg.Term.size(B))), Nat.add(Tri(Pg.Term.size(A)), Tri(Pg.Term.size(B))), tri_add(Pg.Term.size(A), Pg.Term.size(B))) :
        N.Le(3n+_, Pg.Form.size.ctor(3n, 3n+Nat.add(Pg.Form.size.term(A), Pg.Form.size.term(B))))
      ft.k(Nat.add(Tri(Pg.Term.size(A)), Tri(Pg.Term.size(B))), 3n+Nat.add(Pg.Form.size.term(A), Pg.Form.size.term(B)), 3n,
        ft.two(Tri(Pg.Term.size(A)), Tri(Pg.Term.size(B)), Pg.Form.size.term(A), Pg.Form.size.term(B), 3n, ft.ge(A), ft.ge(B)))
    case Bk.Term.Tup{_, +a, +b}:
      %Equal.sym(Nat, Tri(Nat.add(Pg.Term.size(a), Pg.Term.size(b))), Nat.add(Tri(Pg.Term.size(a)), Tri(Pg.Term.size(b))), tri_add(Pg.Term.size(a), Pg.Term.size(b))) :
        N.Le(3n+_, Pg.Form.size.ctor(3n, 3n+Nat.add(Pg.Form.size.term(a), Pg.Form.size.term(b))))
      ft.k(Nat.add(Tri(Pg.Term.size(a)), Tri(Pg.Term.size(b))), 3n+Nat.add(Pg.Form.size.term(a), Pg.Form.size.term(b)), 3n,
        ft.two(Tri(Pg.Term.size(a)), Tri(Pg.Term.size(b)), Pg.Form.size.term(a), Pg.Form.size.term(b), 3n, ft.ge(a), ft.ge(b)))
    case Bk.Term.Prj{+h}:
      ft.k(Tri(Pg.Term.size(h)), Pg.Form.size.term(h), 1n, ft.ge(h))
    case Bk.Term.Enu{_}:
      Unit{}
    case Bk.Term.Lab{_}:
      Unit{}
    case Bk.Term.Mat{+k, +h, +m}:
      %Equal.sym(Nat, Tri(Nat.add(Pg.Term.size(h), Pg.Term.size(m))), Nat.add(Tri(Pg.Term.size(h)), Tri(Pg.Term.size(m))), tri_add(Pg.Term.size(h), Pg.Term.size(m))) :
        N.Le(3n+_, Pg.Form.size.ctor(3n, Nat.add(Pg.Form.size.name(k), Nat.add(Pg.Form.size.term(h), Pg.Form.size.term(m)))))
      ft.k(Nat.add(Tri(Pg.Term.size(h)), Tri(Pg.Term.size(m))), Nat.add(Pg.Form.size.name(k), Nat.add(Pg.Form.size.term(h), Pg.Form.size.term(m))), 3n,
        ft.two(Tri(Pg.Term.size(h)), Tri(Pg.Term.size(m)), Pg.Form.size.term(h), Pg.Form.size.term(m), Pg.Form.size.name(k), ft.ge(h), ft.ge(m)))
    case Bk.Term.Efq{}:
      Unit{}
    case Bk.Term.Eql{+a, +b, +T}:
      +sa = Pg.Term.size(a)
      +sb = Pg.Term.size(b)
      +sT = Pg.Term.size(T)
      %Equal.sym(Nat, Tri(Nat.add(sa, Nat.add(sb, sT))), Nat.add(Tri(sa), Tri(Nat.add(sb, sT))), tri_add(sa, Nat.add(sb, sT))) :
        N.Le(3n+_, Pg.Form.size.ctor(3n, Nat.add(Pg.Form.size.term(a), Nat.add(Pg.Form.size.term(b), Pg.Form.size.term(T)))))
      %Equal.sym(Nat, Tri(Nat.add(sb, sT)), Nat.add(Tri(sb), Tri(sT)), tri_add(sb, sT)) :
        N.Le(3n+Nat.add(Tri(sa), _), Pg.Form.size.ctor(3n, Nat.add(Pg.Form.size.term(a), Nat.add(Pg.Form.size.term(b), Pg.Form.size.term(T)))))
      ft.k(Nat.add(Tri(sa), Nat.add(Tri(sb), Tri(sT))), Nat.add(Pg.Form.size.term(a), Nat.add(Pg.Form.size.term(b), Pg.Form.size.term(T))), 3n,
        N.add_mono(Tri(sa), Pg.Form.size.term(a), Nat.add(Tri(sb), Tri(sT)), Nat.add(Pg.Form.size.term(b), Pg.Form.size.term(T)), ft.ge(a),
          N.add_mono(Tri(sb), Pg.Form.size.term(b), Tri(sT), Pg.Form.size.term(T), ft.ge(b), ft.ge(T))))
    case Bk.Term.Rfl{}:
      Unit{}
    case Bk.Term.Rwt{+e, +P, +f}:
      +se = Pg.Term.size(e)
      +sP = Pg.Term.size(P)
      +sf = Pg.Term.size(f)
      %Equal.sym(Nat, Tri(Nat.add(se, Nat.add(sP, sf))), Nat.add(Tri(se), Tri(Nat.add(sP, sf))), tri_add(se, Nat.add(sP, sf))) :
        N.Le(3n+_, Pg.Form.size.ctor(3n, Nat.add(Pg.Form.size.term(e), Nat.add(Pg.Form.size.term(P), Pg.Form.size.term(f)))))
      %Equal.sym(Nat, Tri(Nat.add(sP, sf)), Nat.add(Tri(sP), Tri(sf)), tri_add(sP, sf)) :
        N.Le(3n+Nat.add(Tri(se), _), Pg.Form.size.ctor(3n, Nat.add(Pg.Form.size.term(e), Nat.add(Pg.Form.size.term(P), Pg.Form.size.term(f)))))
      ft.k(Nat.add(Tri(se), Nat.add(Tri(sP), Tri(sf))), Nat.add(Pg.Form.size.term(e), Nat.add(Pg.Form.size.term(P), Pg.Form.size.term(f))), 3n,
        N.add_mono(Tri(se), Pg.Form.size.term(e), Nat.add(Tri(sP), Tri(sf)), Nat.add(Pg.Form.size.term(P), Pg.Form.size.term(f)), ft.ge(e),
          N.add_mono(Tri(sP), Pg.Form.size.term(P), Tri(sf), Pg.Form.size.term(f), ft.ge(P), ft.ge(f))))

# the image's k cells: 290, then one a node of the def bodies (W)
def k.le(+ds: List<&2, Bk.Def>, +k: U32,
  ek: {k == Cr.Wasm.encode.len(Cr.Cir.Cell, Mc.Img.cells(ds)) : U32}) ->
  N.Le(U32.to_nat(k), Nat.add(290n, PG.Bl(ds, 0n))):
  +cells = Mc.Img.cells(ds)
  %Equal.sym(U32, k, Cr.Wasm.encode.len(Cr.Cir.Cell, cells), ek) : N.Le(U32.to_nat(_), Nat.add(290n, PG.Bl(ds, 0n)))
  N.le_rw_r(U32.to_nat(Cr.Wasm.encode.len(Cr.Cir.Cell, cells)), List.length(&2, Cr.Cir.Cell, cells), Nat.add(290n, PG.Bl(ds, 0n)),
    PG.cells_len(ds), PG.enc_len_le(cells))

# the largest def body has at most W nodes
def big.go(ds: List<&2, Bk.Def>, +a: Nat) -> N.Le(D.Defs.big(ds), PG.Bl(ds, a)):
  match ds:
    case Nil{}:
      N.le_zero(a)
    case Con{Bk.Def{_, _, +v, _}, +rest}:
      +sv = Pg.Term.size(v)
      +b = PG.Bl(rest, a)
      N.le_rw_r(Nat.max(sv, D.Defs.big(rest)), Nat.add(sv, b), PG.Nsz(v, b), Equal.sym(Nat, PG.Nsz(v, b), Nat.add(sv, b), size.nsz(v, b)),
        max.le(sv, D.Defs.big(rest), Nat.add(sv, b), N.le_add_r(sv, b),
          N.le_trans(D.Defs.big(rest), b, Nat.add(sv, b), big.go(rest, a), N.le_add_l(sv, b))))

def big.le(+ds: List<&2, Bk.Def>) -> N.Le(D.Defs.big(ds), PG.Bl(ds, 0n)):
  big.go(ds, 0n)

# with the addend a: 3 Bl(ds, a) <= the data form's nodes + 3 a
def w.go(ds: List<&2, Bk.Def>, +a: Nat) -> N.Le(Tri(PG.Bl(ds, a)), Nat.add(Pg.Form.size.defs(ds), Tri(a))):
  match ds:
    case Nil{}:
      N.le_add_l(3n, Tri(a))
    case Con{Bk.Def{+k, +T, +v, _}, +rest}:
      +b = PG.Bl(rest, a)
      +fv = Pg.Form.size.term(v)
      +fr = Pg.Form.size.defs(rest)
      +X = Pg.Form.size.ctor(4n, 3n+Nat.add(Pg.Form.size.name(k), Nat.add(Pg.Form.size.term(T), fv)))
      +hX = N.le_trans(fv, Nat.add(Pg.Form.size.name(k), Nat.add(Pg.Form.size.term(T), fv)), X,
        N.le_trans(fv, Nat.add(Pg.Form.size.term(T), fv), Nat.add(Pg.Form.size.name(k), Nat.add(Pg.Form.size.term(T), fv)),
          N.le_add_l(Pg.Form.size.term(T), fv), N.le_add_l(Pg.Form.size.name(k), Nat.add(Pg.Form.size.term(T), fv))),
        N.le_add_l(10n, Nat.add(Pg.Form.size.name(k), Nat.add(Pg.Form.size.term(T), fv))))
      +e1 = Equal.trans(Nat, Tri(PG.Nsz(v, b)), Tri(Nat.add(Pg.Term.size(v), b)), Nat.add(Tri(Pg.Term.size(v)), Tri(b)),
        Equal.cong(Nat, Nat, x => Tri(x), PG.Nsz(v, b), Nat.add(Pg.Term.size(v), b), size.nsz(v, b)), tri_add(Pg.Term.size(v), b))
      +h1 = N.add_mono(Tri(Pg.Term.size(v)), X, Tri(b), Nat.add(fr, Tri(a)), N.le_trans(Tri(Pg.Term.size(v)), fv, X, ft.ge(v), hX), w.go(rest, a))
      +h2 = N.le_rw_r(Nat.add(Tri(Pg.Term.size(v)), Tri(b)), Nat.add(X, Nat.add(fr, Tri(a))), Nat.add(Nat.add(X, fr), Tri(a)),
        Equal.sym(Nat, Nat.add(Nat.add(X, fr), Tri(a)), Nat.add(X, Nat.add(fr, Tri(a))), N.add_assoc(X, fr, Tri(a))), h1)
      N.le_rw_l(Nat.add(Tri(Pg.Term.size(v)), Tri(b)), Tri(PG.Nsz(v, b)), Nat.add(5n+Nat.add(X, fr), Tri(a)),
        Equal.sym(Nat, Tri(PG.Nsz(v, b)), Nat.add(Tri(Pg.Term.size(v)), Tri(b)), e1),
        N.le_trans(Nat.add(Tri(Pg.Term.size(v)), Tri(b)), Nat.add(Nat.add(X, fr), Tri(a)), Nat.add(5n+Nat.add(X, fr), Tri(a)), h2,
          N.le_add_l(5n, Nat.add(Nat.add(X, fr), Tri(a)))))

# each node of a def body is 3 nodes or more of the book's data form: 3 W is
# at most the program's size
def w.le(+p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>,
  rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>}) ->
  N.Le(Nat.mul(3n, PG.Bl(ds, 0n)), Pg.Program.size(p)):
  +b = PG.Bl(ds, 0n)
  +f = Pg.Form.size.defs(ds)
  +h = N.le_rw_r(Tri(b), Nat.add(f, Tri(0n)), f, N.add_zero(f), w.go(ds, 0n))
  N.le_rw_r(Nat.mul(3n, b), f, Pg.Program.size(p), N.size.eq(p, ds, rd),
    N.le_rw_l(Tri(b), Nat.mul(3n, b), f, Equal.sym(Nat, Nat.mul(3n, b), Tri(b), mul3(b)), h))

# The first cell
# --------------

def UIsNone(m: Maybe<&2, U32>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{_}:
      Empty

def usome.ne(-x: U32, e: {None{} == Some{x} : Maybe<&2, U32>}) -> Empty:
  %e : UIsNone(_)
  Unit{}

# one byte more of the count, by whether the count is full
def len.con(b: Bool, +rest: List<&2, Word(8n)>, +n: U32, +len: U32,
  e: {Wa.Wasm.length32.if(b, u => Wa.Wasm.length32.go(rest, U32.inc(n))) == Some{len} : Maybe<&2, U32>},
  ih: {Wa.Wasm.length32.go(rest, U32.inc(n)) == Some{len} : Maybe<&2, U32>} ->
    N.Le(U32.to_nat(len), Nat.add(U32.to_nat(U32.inc(n)), List.length(&2, Word(8n), rest)))) ->
  N.Le(U32.to_nat(len), Nat.add(U32.to_nat(n), 1n+List.length(&2, Word(8n), rest))):
  match b:
    case True{}:
      Empty.absurd(N.Le(U32.to_nat(len), Nat.add(U32.to_nat(n), 1n+List.length(&2, Word(8n), rest))), usome.ne(len, e))
    case False{}:
      +l = List.length(&2, Word(8n), rest)
      %Equal.sym(Nat, Nat.add(U32.to_nat(n), 1n+l), 1n+Nat.add(U32.to_nat(n), l), N.add_succ_r(U32.to_nat(n), l)) : N.Le(U32.to_nat(len), _)
      N.le_trans(U32.to_nat(len), Nat.add(U32.to_nat(U32.inc(n)), l), 1n+Nat.add(U32.to_nat(n), l), ih(e),
        N.add_mono(U32.to_nat(U32.inc(n)), 1n+U32.to_nat(n), l, l, N.U32.inc_le(n), N.le_refl(l)))

# the count from n: n and the bytes
def len.go(xs: List<&2, Word(8n)>, +n: U32, +len: U32, e: {Wa.Wasm.length32.go(xs, n) == Some{len} : Maybe<&2, U32>}) ->
  N.Le(U32.to_nat(len), Nat.add(U32.to_nat(n), List.length(&2, Word(8n), xs))):
  match xs:
    case Nil{}:
      +enl = {Equal.cong(Maybe<&2, U32>, U32, x => Maybe.default(&2, U32, x, n), Some{n}, Some{len}, e) : {n == len : U32}}
      %enl : N.Le(U32.to_nat(_), Nat.add(U32.to_nat(n), 0n))
      N.le_add_r(U32.to_nat(n), 0n)
    case Con{_, +rest}:
      len.con(U32.is_eq(n, 4294967295), rest, n, len, e, e2 => len.go(rest, U32.inc(n), len, e2))

# the length that Wasm.length32 gives is the list's
def len.le(+i: List<&2, Word(8n)>, +len: U32,
  el: {Wa.Wasm.length32(i) == Some{len} : Maybe<&2, U32>}) ->
  N.Le(U32.to_nat(len), List.length(&2, Word(8n), i)):
  +l = List.length(&2, Word(8n), i)
  N.le_rw_r(U32.to_nat(len), Nat.add(U32.to_nat(0), l), l, N.zero_add(l), len.go(i, 0, len, el))

# a sum of words is at most the sum of their numbers (it may wrap)
def wadd.le(+n: Nat, +a: Word(n), +b: Word(n)) ->
  N.Le(Word.to_nat(n, Word.add(n, a, b)), Nat.add(Word.to_nat(n, a), Word.to_nat(n, b))):
  +X = Word.to_nat(n, Word.adc(n, a, b, False{}, False{}))
  +Dc = N.D(n, FC.hw.bn(FC.hw.cout(n, a, b, False{})))
  N.le_rw_r(X, Nat.add(X, Dc), Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)), FC.hw.adc(n, a, b, False{}), N.le_add_r(X, Dc))

def add.le(+a: U32, +b: U32) -> N.Le(U32.to_nat(U32.add(a, b)), Nat.add(U32.to_nat(a), U32.to_nat(b))):
  match a b:
    case U32{+x} U32{+y}:
      wadd.le(32n, x, y)

# a shift left at most doubles
def shl.le(+n: Nat, +w: Word(n)) -> N.Le(Word.to_nat(n, Word.shl(n, w)), Nat.double(Word.to_nat(n, w))):
  +X = Word.to_nat(n, Word.shl(n, w))
  +Dc = N.D(n, FC.hw.bn(FC.hw.sout(n, w)))
  N.le_rw_r(X, Nat.add(X, Dc), Nat.double(Word.to_nat(n, w)), FC.hw.shl(n, w), N.le_add_r(X, Dc))

def shlj.le(j: Nat, +n: Nat, +w: Word(n)) -> N.Le(Word.to_nat(n, FC.hw.shlj(j, n, w)), N.D(j, Word.to_nat(n, w))):
  match j:
    case 0n:
      N.le_refl(Word.to_nat(n, w))
    case 1n+(+q):
      +s = FC.hw.shlj(q, n, w)
      N.le_trans(Word.to_nat(n, Word.shl(n, s)), Nat.double(Word.to_nat(n, s)), Nat.double(N.D(q, Word.to_nat(n, w))), shl.le(n, s),
        N.double_mono(Word.to_nat(n, s), N.D(q, Word.to_nat(n, w)), shlj.le(q, n, w)))

# the first byte of the cell c is at most 20 c
def at.le(+c: U32) -> N.Le(U32.to_nat(Cr.Cir.at(c)), FC.hw.t20(U32.to_nat(c))):
  match c:
    case U32{+w}:
      +X = Word.to_nat(32n, w)
      +s4 = FC.hw.shlj(4n, 32n, w)
      +s2 = FC.hw.shlj(2n, 32n, w)
      N.le_rw_r(Word.to_nat(32n, Word.add(32n, s4, s2)), Nat.add(N.D(4n, X), N.D(2n, X)), FC.hw.t20(X), FC.hw.t20_shifts(X),
        N.le_trans(Word.to_nat(32n, Word.add(32n, s4, s2)), Nat.add(Word.to_nat(32n, s4), Word.to_nat(32n, s2)), Nat.add(N.D(4n, X), N.D(2n, X)),
          wadd.le(32n, s4, s2),
          N.add_mono(Word.to_nat(32n, s4), N.D(4n, X), Word.to_nat(32n, s2), N.D(2n, X), shlj.le(4n, 32n, w), shlj.le(2n, 32n, w))))

# 20 (a + b) = 20 a + 20 b
def t20_add(+a: Nat, +b: Nat) -> {FC.hw.t20(Nat.add(a, b)) == Nat.add(FC.hw.t20(a), FC.hw.t20(b)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 20n+x, FC.hw.t20(Nat.add(p, b)), Nat.add(FC.hw.t20(p), FC.hw.t20(b)), t20_add(p, b))

# 1 + (e - 1) = e, for 1 <= e
def sub1.le(+e: Nat, h: N.Le(1n, e)) -> N.Le(1n+Nat.sub(e, 1n), e):
  match e:
    case 0n:
      Empty.absurd(N.Le(1n+Nat.sub(0n, 1n), 0n), h)
    case 1n+(+q):
      %Equal.sym(Nat, Nat.sub(q, 0n), q, FC.hf.sub0(q)) : N.Le(_, q)
      N.le_refl(q)

# Cir.first's k + 1
def first.le.t(+k: U32, +first: U32, +L: Nat, ef: {first == U32.inc(k) : U32}) ->
  N.Le(U32.to_nat(first), 1n+Nat.add(U32.to_nat(k), L)):
  %Equal.sym(U32, first, U32.inc(k), ef) : N.Le(U32.to_nat(_), 1n+Nat.add(U32.to_nat(k), L))
  N.le_trans(U32.to_nat(U32.inc(k)), 1n+U32.to_nat(k), 1n+Nat.add(U32.to_nat(k), L), N.U32.inc_le(k), N.le_add_r(U32.to_nat(k), L))

# Cir.first's (E - 1) / 20 + 1, for E above 20 (k + 1), E <= 20 (k + 1) + L
def first.le.f(+k: U32, +E: U32, +first: U32, +L: Nat,
  hE: N.Le(U32.to_nat(E), Nat.add(FC.hw.t20(1n+U32.to_nat(k)), L)),
  eb: {U32.is_ge(Cr.Cir.at(U32.inc(k)), E) == False{} : Bool},
  ef: {first == U32.inc(U32.div(U32.sub(E, 1), 20)) : U32}) -> N.Le(U32.to_nat(first), 1n+Nat.add(U32.to_nat(k), L)):
  +K = U32.to_nat(k)
  +A = Cr.Cir.at(U32.inc(k))
  +En = U32.to_nat(E)
  +hlt = FC.hw.rel_nge(U32.cmp(A, E), U32.to_nat(A), En, N.U32.rel(A, E), eb)
  +hE1 = N.le_trans(U32.to_nat(1), 1n+U32.to_nat(A), En, N.le_zero(U32.to_nat(A)), hlt)
  +hE2 = N.le_trans(1n, 1n+U32.to_nat(A), En, N.le_zero(U32.to_nat(A)), hlt)
  +X = U32.sub(E, 1)
  +eX = FC.hf.sub.nat(E, 1, hE1)
  +D0 = U32.div(X, 20)
  +Q = U32.to_nat(D0)
  +lo = FC.hf.fst(N.Le(FC.hw.t20(Q), U32.to_nat(X)), N.Le(U32.to_nat(X), 19n+FC.hw.t20(Q)), FC.hf.div(X))
  +h1 = N.le_rw_r(FC.hw.t20(Q), U32.to_nat(X), Nat.sub(En, 1n), eX, lo)
  +h3 = N.le_trans(1n+FC.hw.t20(Q), 1n+Nat.sub(En, 1n), En, h1, sub1.le(En, hE2))
  +M = Nat.add(1n+K, L)
  +h5 = N.le_rw_r(Nat.add(FC.hw.t20(1n+K), L), Nat.add(FC.hw.t20(1n+K), FC.hw.t20(L)), FC.hw.t20(M),
    Equal.sym(Nat, FC.hw.t20(M), Nat.add(FC.hw.t20(1n+K), FC.hw.t20(L)), t20_add(1n+K, L)),
    N.add_mono(FC.hw.t20(1n+K), FC.hw.t20(1n+K), L, FC.hw.t20(L), N.le_refl(FC.hw.t20(1n+K)), FC.hw.le_t20(L)))
  +hQ = FC.hw.t20_lt(Q, M, N.le_trans(1n+FC.hw.t20(Q), En, FC.hw.t20(M), h3, N.le_trans(En, Nat.add(FC.hw.t20(1n+K), L), FC.hw.t20(M), hE, h5)))
  %Equal.sym(U32, first, U32.inc(D0), ef) : N.Le(U32.to_nat(_), 1n+Nat.add(K, L))
  N.le_trans(U32.to_nat(U32.inc(D0)), 1n+Q, 1n+Nat.add(K, L), N.U32.inc_le(D0), hQ)

def first.of(b: Bool, +k: U32, +E: U32, +first: U32, +L: Nat,
  hE: N.Le(U32.to_nat(E), Nat.add(FC.hw.t20(1n+U32.to_nat(k)), L)),
  eb: {U32.is_ge(Cr.Cir.at(U32.inc(k)), E) == b : Bool},
  ef: {first == Bool.pick(U32, b, U32.inc(k), U32.inc(U32.div(U32.sub(E, 1), 20))) : U32}) ->
  N.Le(U32.to_nat(first), 1n+Nat.add(U32.to_nat(k), L)):
  match b:
    case True{}:
      first.le.t(k, first, L, ef)
    case False{}:
      first.le.f(k, E, first, L, hE, eb, ef)

# the first cell after the image's k cells and the input's bytes, as
# Cir.result computes it, is at most 1 + k + |i|
def first.le(+i: List<&2, Word(8n)>, +k: U32, +len: U32, +first: U32,
  el: {Wa.Wasm.length32(i) == Some{len} : Maybe<&2, U32>},
  ef: {first == Cr.Cir.first(k, U32.add(Cr.Cir.input.at(k), len)) : U32}) ->
  N.Le(U32.to_nat(first), 1n+Nat.add(U32.to_nat(k), List.length(&2, Word(8n), i))):
  +K = U32.to_nat(k)
  +L = List.length(&2, Word(8n), i)
  +E = U32.add(Cr.Cir.input.at(k), len)
  +ha = N.le_trans(U32.to_nat(Cr.Cir.at(U32.inc(k))), FC.hw.t20(U32.to_nat(U32.inc(k))), FC.hw.t20(1n+K), at.le(U32.inc(k)),
    FC.hw.t20_mono(U32.to_nat(U32.inc(k)), 1n+K, N.U32.inc_le(k)))
  +hE = N.le_trans(U32.to_nat(E), Nat.add(U32.to_nat(Cr.Cir.input.at(k)), U32.to_nat(len)), Nat.add(FC.hw.t20(1n+K), L),
    add.le(Cr.Cir.input.at(k), len),
    N.add_mono(U32.to_nat(Cr.Cir.at(U32.inc(k))), FC.hw.t20(1n+K), U32.to_nat(len), L, ha, len.le(i, len, el)))
  first.of(U32.is_ge(Cr.Cir.at(U32.inc(k)), E), k, E, first, L, hE, {==}, ef)

# A round
# -------

# Peak holds the STATIC own cells and the nodes of one term (the state after
# M.input: the cache and the start term)
def peak.ge(+ds: List<&2, Bk.Def>, +C: Nat, +S: Nat, +a: Nat, h: N.Le(a, Nat.add(C, S))) -> N.Le(a, Peak(ds, C, S)):
  +L3 = Nat.mul(3n, D.Defs.big(ds))
  +S2 = Nat.mul(2n, S)
  +hs = N.le_trans(S, S2, Nat.add(16n, Nat.add(S2, L3)), N.le_add_r(S, Nat.mul(1n, S)),
    N.le_trans(S2, Nat.add(S2, L3), Nat.add(16n, Nat.add(S2, L3)), N.le_add_r(S2, L3), N.le_add_l(16n, Nat.add(S2, L3))))
  N.le_trans(a, Nat.add(C, S), Peak(ds, C, S), h, N.add_mono(C, C, S, Nat.add(16n, Nat.add(S2, L3)), N.le_refl(C), hs))

# a round from the state st, of the term t, needs at most Peak own cells,
# when st has at most C STATIC own cells and t and its step at most S nodes
def need.peak(+ds: List<&2, Bk.Def>, +st: Cr.Cir.State, +t: Bk.Term, +C: Nat, +S: Nat,
  hst: N.Le(D.Stat(D.Mem.cells(st), D.St.cells(st), D.St.first(st)), C),
  ht: N.Le(Pg.Term.size(t), S),
  hu: N.Le(D.StepSize(ds, t), S)) ->
  N.Le(D.Need(ds, st, t), Peak(ds, C, S)):
  +M = Nat.max(Pg.Term.size(t), D.StepSize(ds, t))
  +L3 = Nat.mul(3n, D.Defs.big(ds))
  N.add_mono(D.Stat(D.Mem.cells(st), D.St.cells(st), D.St.first(st)), C, Nat.add(16n, Nat.add(Nat.mul(2n, M), L3)),
    Nat.add(16n, Nat.add(Nat.mul(2n, S), L3)), hst,
    N.add_mono(16n, 16n, Nat.add(Nat.mul(2n, M), L3), Nat.add(Nat.mul(2n, S), L3), N.le_refl(16n),
      N.add_mono(Nat.mul(2n, M), Nat.mul(2n, S), L3, L3, N.mul_mono_r(2n, M, S, max.le(Pg.Term.size(t), D.StepSize(ds, t), S, ht, hu)),
        N.le_refl(L3))))

# the bytes of Need are within Budget
def need.bytes.le(+ds: List<&2, Bk.Def>, +st: Cr.Cir.State, +t: Bk.Term) ->
  N.Le(D.Need.bytes(ds, st, t), D.Budget(ds, st, t)):
  max_l(D.Need.bytes(ds, st, t), Nat.add(Nat.mul(20n, U32.to_nat(D.St.next(st))), Pg.Term.size(t)))

# and its budget is at most Room, when st has at most Peak own cells and its
# first cell is at most X
def budget.room(+ds: List<&2, Bk.Def>, +st: Cr.Cir.State, +t: Bk.Term, +X: Nat, +C: Nat, +S: Nat,
  +hfi: N.Le(U32.to_nat(D.St.first(st)), X),
  hst: N.Le(D.Stat(D.Mem.cells(st), D.St.cells(st), D.St.first(st)), C),
  +ht: N.Le(Pg.Term.size(t), S),
  hu: N.Le(D.StepSize(ds, t), S),
  hm: N.Le(D.Mem.cells(st), Peak(ds, C, S))) ->
  N.Le(D.Budget(ds, st, t), Room(ds, X, C, S)):
  +FI = U32.to_nat(D.St.first(st))
  +NX = U32.to_nat(D.St.next(st))
  +P = Peak(ds, C, S)
  +T = Pg.Term.size(t)
  +Q = Nat.add(X, P)
  +h1 = N.add_mono(Nat.mul(20n, Nat.add(FI, D.Need(ds, st, t))), Nat.mul(20n, Q), T, S,
    N.mul_mono_r(20n, Nat.add(FI, D.Need(ds, st, t)), Q, N.add_mono(FI, X, D.Need(ds, st, t), P, hfi, need.peak(ds, st, t, C, S, hst, ht, hu))),
    ht)
  +hn = N.le_trans(NX, Nat.add(FI, D.Mem.cells(st)), Q, sub_le(NX, FI), N.add_mono(FI, X, D.Mem.cells(st), P, hfi, hm))
  +h2 = N.add_mono(Nat.mul(20n, NX), Nat.mul(20n, Q), T, S, N.mul_mono_r(20n, NX, Q, hn), ht)
  max.le(D.Need.bytes(ds, st, t), Nat.add(Nat.mul(20n, NX), T), Room(ds, X, C, S), h1, h2)

# so its limit has room for its budget (round.room's room) when the limit lim
# has room for Room (room.lim): the loop's form, with no closed big number
def budget.lim(+ds: List<&2, Bk.Def>, +st: Cr.Cir.State, +t: Bk.Term, +X: Nat, +C: Nat, +S: Nat, +lim: U32,
  hfi: N.Le(U32.to_nat(D.St.first(st)), X),
  hlim: {D.St.lim(st) == lim : U32},
  hst: N.Le(D.Stat(D.Mem.cells(st), D.St.cells(st), D.St.first(st)), C),
  ht: N.Le(Pg.Term.size(t), S),
  hu: N.Le(D.StepSize(ds, t), S),
  hm: N.Le(D.Mem.cells(st), Peak(ds, C, S)),
  hroom: N.Le(Room(ds, X, C, S), D.Lim.bytes(lim))) ->
  N.Le(D.Budget(ds, st, t), D.Lim.bytes(D.St.lim(st))):
  %Equal.sym(U32, D.St.lim(st), lim, hlim) : N.Le(D.Budget(ds, st, t), D.Lim.bytes(_))
  N.le_trans(D.Budget(ds, st, t), Room(ds, X, C, S), D.Lim.bytes(lim), budget.room(ds, st, t, X, C, S, hfi, hst, ht, hu, hm), hroom)

# The run's memory
# ----------------

# 2^18 <= 2^24: the one comparison of two closed numbers
def pow.le() -> N.Le(N.D(18n, 1n), 16777216n):
  Unit{}

# Peak, with W for Defs.big
def peak.le(+ds: List<&2, Bk.Def>, +C: Nat, +S: Nat, +W: Nat, h: N.Le(D.Defs.big(ds), W)) ->
  N.Le(Peak(ds, C, S), Nat.add(C, Nat.add(16n, Nat.add(Nat.mul(2n, S), Nat.mul(3n, W))))):
  +S2 = Nat.mul(2n, S)
  +L3 = Nat.mul(3n, D.Defs.big(ds))
  +W3 = Nat.mul(3n, W)
  N.add_mono(C, C, Nat.add(16n, Nat.add(S2, L3)), Nat.add(16n, Nat.add(S2, W3)), N.le_refl(C),
    N.add_mono(16n, 16n, Nat.add(S2, L3), Nat.add(S2, W3), N.le_refl(16n),
      N.add_mono(S2, S2, L3, W3, N.le_refl(S2), N.mul_mono_r(3n, D.Defs.big(ds), W, h))))

# the first cell and Peak, with k <= 290 + W, |i| <= S and Defs.big <= W, are
# at most 307 + C + 4 W + 3 S
def room.top(+K: Nat, +I: Nat, +W: Nat, +ds: List<&2, Bk.Def>, +C: Nat, +S: Nat,
  hK: N.Le(K, Nat.add(290n, W)), hI: N.Le(I, S), hL: N.Le(D.Defs.big(ds), W)) ->
  N.Le(Nat.add(1n+Nat.add(K, I), Peak(ds, C, S)), Nat.add(Nat.add(307n, C), Nat.add(Nat.mul(4n, W), Nat.mul(3n, S)))):
  +S2 = Nat.mul(2n, S)
  +S3 = Nat.mul(3n, S)
  +W3 = Nat.mul(3n, W)
  +W4 = Nat.mul(4n, W)
  +WS = Nat.add(W, S)
  +R = Nat.add(S2, W3)
  +X1 = {1n+Nat.add(Nat.add(290n, W), S) : Nat}
  +P1 = Nat.add(C, Nat.add(16n, R))
  +hX = N.add_mono(K, Nat.add(290n, W), I, S, hK, hI)
  +h1 = N.add_mono(1n+Nat.add(K, I), X1, Peak(ds, C, S), P1, hX, peak.le(ds, C, S, W, hL))
  +eSR = {Equal.sym(Nat, Nat.add(Nat.add(S, S2), W3), Nat.add(S, R), N.add_assoc(S, S2, W3)) : {Nat.add(S, R) == Nat.add(S3, W3) : Nat}}
  +e4 = Equal.trans(Nat, Nat.add(WS, R), Nat.add(W, Nat.add(S, R)), Nat.add(W4, S3), N.add_assoc(W, S, R),
    Equal.trans(Nat, Nat.add(W, Nat.add(S, R)), Nat.add(W, Nat.add(S3, W3)), Nat.add(W4, S3),
      Equal.cong(Nat, Nat, x => Nat.add(W, x), Nat.add(S, R), Nat.add(S3, W3), eSR),
      Equal.trans(Nat, Nat.add(W, Nat.add(S3, W3)), Nat.add(S3, W4), Nat.add(W4, S3), N.add_swap(W, S3, W3), FC.hf.add.comm(S3, W4))))
  +eq = Equal.trans(Nat, Nat.add(WS, P1), Nat.add(C, Nat.add(WS, Nat.add(16n, R))), Nat.add(16n, Nat.add(C, Nat.add(W4, S3))),
    N.add_swap(WS, C, Nat.add(16n, R)),
    Equal.trans(Nat, Nat.add(C, Nat.add(WS, Nat.add(16n, R))), Nat.add(C, Nat.add(16n, Nat.add(WS, R))), Nat.add(16n, Nat.add(C, Nat.add(W4, S3))),
      Equal.cong(Nat, Nat, x => Nat.add(C, x), Nat.add(WS, Nat.add(16n, R)), Nat.add(16n, Nat.add(WS, R)), FC.hw.add_k(WS, 16n, R)),
      Equal.trans(Nat, Nat.add(C, Nat.add(16n, Nat.add(WS, R))), Nat.add(16n, Nat.add(C, Nat.add(WS, R))), Nat.add(16n, Nat.add(C, Nat.add(W4, S3))),
        FC.hw.add_k(C, 16n, Nat.add(WS, R)),
        Equal.cong(Nat, Nat, x => Nat.add(16n, Nat.add(C, x)), Nat.add(WS, R), Nat.add(W4, S3), e4))))
  +eT = {Equal.cong(Nat, Nat, x => 291n+x, Nat.add(WS, P1), Nat.add(16n, Nat.add(C, Nat.add(W4, S3))), eq) :
    {Nat.add(X1, P1) == Nat.add(Nat.add(307n, C), Nat.add(W4, S3)) : Nat}}
  N.le_rw_r(Nat.add(1n+Nat.add(K, I), Peak(ds, C, S)), Nat.add(X1, P1), Nat.add(Nat.add(307n, C), Nat.add(W4, S3)), eT, h1)

# 20 (307 + C + 4 W + 3 S) + S <= 64 (z + S) + G, for C <= 6144, 3 W <= z and
# 2^18 <= G (G is F's 2^24, a variable here)
def top.need(+C: Nat, +W: Nat, +S: Nat, +z: Nat, +G: Nat, hC: N.Le(C, N.D(11n, 3n)), hW: N.Le(Nat.mul(3n, W), z),
  hG: N.Le(N.D(18n, 1n), G)) ->
  N.Le(Nat.add(Nat.mul(20n, Nat.add(Nat.add(307n, C), Nat.add(Nat.mul(4n, W), Nat.mul(3n, S)))), S), Nat.add(Nat.mul(64n, Nat.add(z, S)), G)):
  +A0 = Nat.add(307n, C)
  +W4 = Nat.mul(4n, W)
  +S3 = Nat.mul(3n, S)
  +Aa = Nat.mul(20n, A0)
  +Bw = Nat.mul(20n, W4)
  +Cs = Nat.mul(20n, S3)
  +Z64 = Nat.mul(64n, z)
  +S64 = Nat.mul(64n, S)
  +hc0 = N.add_mono(307n, N.D(11n, 1n), C, N.D(11n, 3n), Unit{}, hC)
  +e13 = Equal.trans(Nat, Nat.add(N.D(11n, 1n), N.D(11n, 3n)), N.D(11n, Nat.add(1n, 3n)), N.D(13n, 1n), D_plus(11n, 1n, 3n),
    Equal.trans(Nat, N.D(11n, Nat.add(1n, 3n)), N.D(11n, N.D(2n, 1n)), N.D(13n, 1n),
      Equal.cong(Nat, Nat, x => N.D(11n, x), Nat.add(1n, 3n), N.D(2n, 1n), {==}), N.D_add(11n, 2n, 13n, 1n, {==})))
  +hc1 = N.le_rw_r(A0, Nat.add(N.D(11n, 1n), N.D(11n, 3n)), N.D(13n, 1n), e13, hc0)
  +hc2 = N.le_trans(Aa, Nat.mul(20n, N.D(13n, 1n)), Nat.mul(N.D(5n, 1n), N.D(13n, 1n)), N.mul_mono_r(20n, A0, N.D(13n, 1n), hc1),
    N.mul_mono_l(20n, N.D(5n, 1n), N.D(13n, 1n), Unit{}))
  +e18 = Equal.trans(Nat, Nat.mul(N.D(5n, 1n), N.D(13n, 1n)), N.D(5n, N.D(13n, 1n)), N.D(18n, 1n), N.mul_D(5n, N.D(13n, 1n)),
    N.D_add(5n, 13n, 18n, 1n, {==}))
  +hA = N.le_trans(Aa, N.D(18n, 1n), G, N.le_rw_r(Aa, Nat.mul(N.D(5n, 1n), N.D(13n, 1n)), N.D(18n, 1n), e18, hc2), hG)
  +hB = N.le_trans(Bw, Nat.mul(64n, Nat.mul(3n, W)), Z64,
    N.le_rw_l(Nat.mul(Nat.mul(20n, 4n), W), Bw, Nat.mul(64n, Nat.mul(3n, W)), mul_assoc(20n, 4n, W),
      N.le_rw_r(Nat.mul(Nat.mul(20n, 4n), W), Nat.mul(Nat.mul(64n, 3n), W), Nat.mul(64n, Nat.mul(3n, W)), mul_assoc(64n, 3n, W),
        N.mul_mono_l(Nat.mul(20n, 4n), Nat.mul(64n, 3n), W, Unit{}))),
    N.mul_mono_r(64n, Nat.mul(3n, W), z, hW))
  +M60 = Nat.mul(Nat.mul(20n, 3n), S)
  +hS = N.le_rw_l(Nat.add(S, M60), Nat.add(Cs, S), S64,
    Equal.trans(Nat, Nat.add(S, M60), Nat.add(M60, S), Nat.add(Cs, S), FC.hf.add.comm(S, M60),
      Equal.cong(Nat, Nat, x => Nat.add(x, S), M60, Cs, mul_assoc(20n, 3n, S))),
    N.mul_mono_l(1n+Nat.mul(20n, 3n), 64n, S, Unit{}))
  +e1 = Equal.trans(Nat, Nat.mul(20n, Nat.add(A0, Nat.add(W4, S3))), Nat.add(Aa, Nat.mul(20n, Nat.add(W4, S3))), Nat.add(Aa, Nat.add(Bw, Cs)),
    mul_add(20n, A0, Nat.add(W4, S3)),
    Equal.cong(Nat, Nat, x => Nat.add(Aa, x), Nat.mul(20n, Nat.add(W4, S3)), Nat.add(Bw, Cs), mul_add(20n, W4, S3)))
  +e2 = Equal.trans(Nat, Nat.add(Nat.add(Aa, Nat.add(Bw, Cs)), S), Nat.add(Aa, Nat.add(Nat.add(Bw, Cs), S)), Nat.add(Aa, Nat.add(Bw, Nat.add(Cs, S))),
    N.add_assoc(Aa, Nat.add(Bw, Cs), S),
    Equal.cong(Nat, Nat, x => Nat.add(Aa, x), Nat.add(Nat.add(Bw, Cs), S), Nat.add(Bw, Nat.add(Cs, S)), N.add_assoc(Bw, Cs, S)))
  +e3 = Equal.trans(Nat, Nat.add(Nat.mul(20n, Nat.add(A0, Nat.add(W4, S3))), S), Nat.add(Nat.add(Aa, Nat.add(Bw, Cs)), S), Nat.add(Aa, Nat.add(Bw, Nat.add(Cs, S))),
    Equal.cong(Nat, Nat, x => Nat.add(x, S), Nat.mul(20n, Nat.add(A0, Nat.add(W4, S3))), Nat.add(Aa, Nat.add(Bw, Cs)), e1), e2)
  +eF = Equal.trans(Nat, Nat.add(G, Nat.add(Z64, S64)), Nat.add(G, Nat.mul(64n, Nat.add(z, S))), Nat.add(Nat.mul(64n, Nat.add(z, S)), G),
    Equal.cong(Nat, Nat, x => Nat.add(G, x), Nat.add(Z64, S64), Nat.mul(64n, Nat.add(z, S)),
      Equal.sym(Nat, Nat.mul(64n, Nat.add(z, S)), Nat.add(Z64, S64), mul_add(64n, z, S))),
    FC.hf.add.comm(G, Nat.mul(64n, Nat.add(z, S))))
  +h = N.add_mono(Aa, G, Nat.add(Bw, Nat.add(Cs, S)), Nat.add(Z64, S64), hA, N.add_mono(Bw, Z64, Nat.add(Cs, S), S64, hB, hS))
  N.le_rw_l(Nat.add(Aa, Nat.add(Bw, Nat.add(Cs, S))), Nat.add(Nat.mul(20n, Nat.add(A0, Nat.add(W4, S3))), S), Nat.add(Nat.mul(64n, Nat.add(z, S)), G),
    Equal.sym(Nat, Nat.add(Nat.mul(20n, Nat.add(A0, Nat.add(W4, S3))), S), Nat.add(Aa, Nat.add(Bw, Nat.add(Cs, S))), e3),
    N.le_rw_r(Nat.add(Aa, Nat.add(Bw, Nat.add(Cs, S))), Nat.add(G, Nat.add(Z64, S64)), Nat.add(Nat.mul(64n, Nat.add(z, S)), G), eF, h))

# Room is at most 20 T + S, when the first cell and Peak are at most T
def room.le(+ds: List<&2, Bk.Def>, +X: Nat, +C: Nat, +S: Nat, +T: Nat, h: N.Le(Nat.add(X, Peak(ds, C, S)), T)) ->
  N.Le(Room(ds, X, C, S), Nat.add(Nat.mul(20n, T), S)):
  N.add_mono(Nat.mul(20n, Nat.add(X, Peak(ds, C, S))), Nat.mul(20n, T), S, S, N.mul_mono_r(20n, Nat.add(X, Peak(ds, C, S)), T, h),
    N.le_refl(S))

# 20 a + b is at most Room, when a is at most the first cell and Peak, and b
# at most S
def room.ge(+ds: List<&2, Bk.Def>, +X: Nat, +C: Nat, +S: Nat, +a: Nat, +b: Nat, ha: N.Le(a, Nat.add(X, Peak(ds, C, S))), hb: N.Le(b, S)) ->
  N.Le(Nat.add(Nat.mul(20n, a), b), Room(ds, X, C, S)):
  N.add_mono(Nat.mul(20n, a), Nat.mul(20n, Nat.add(X, Peak(ds, C, S))), b, S, N.mul_mono_r(20n, a, Nat.add(X, Peak(ds, C, S)), ha), hb)

# the bytes of the cells up to fi + y are at most Room, when fi + y is at
# most the first cell and Peak
def cells.room(+ds: List<&2, Bk.Def>, +X: Nat, +C: Nat, +S: Nat, +fi: U32, +y: Nat,
  h: N.Le(Nat.add(U32.to_nat(fi), y), Nat.add(X, Peak(ds, C, S)))) ->
  N.Le(D.Cells.bytes(fi, y), Room(ds, X, C, S)):
  +A = Nat.mul(20n, Nat.add(X, Peak(ds, C, S)))
  N.le_trans(D.Cells.bytes(fi, y), A, Room(ds, X, C, S), N.mul_mono_r(20n, Nat.add(U32.to_nat(fi), y), Nat.add(X, Peak(ds, C, S)), h),
    N.le_add_r(A, S))

# F, as Program.need spells it
def need.eq(+p: List<&2, Word(8n)>, +i: List<&2, Word(8n)>, +n: Nat) ->
  {Nat.add(Nat.mul(64n, Nat.add(Pg.Program.size(p), Pg.Program.largest(p, i, n))), 16777216n) == Pg.Program.need(p, i, n) : Nat}:
  {==}

# |i| <= S
def input.le(+p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +n: Nat,
  rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>}) ->
  N.Le(List.length(&2, Word(8n), i), Pg.Program.largest(p, i, n)):
  +I = List.length(&2, Word(8n), i)
  N.le_trans(I, 5n+Nat.mul(72n, I), Pg.Program.largest(p, i, n),
    N.le_trans(I, Nat.mul(72n, I), 5n+Nat.mul(72n, I), N.le_add_r(I, Nat.mul(71n, I)), N.le_add_l(5n, Nat.mul(72n, I))),
    start.le(p, ds, i, n, rd))

# Room, for the first cell of the run (first.le), C <= 6144 STATIC own cells
# and the run's largest term S, is at most F
def room.need(+p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +n: Nat, +k: U32, +C: Nat,
  +rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  ek: {k == Cr.Wasm.encode.len(Cr.Cir.Cell, Mc.Img.cells(ds)) : U32},
  hC: N.Le(C, N.D(11n, 3n))) ->
  N.Le(Room(ds, 1n+Nat.add(U32.to_nat(k), List.length(&2, Word(8n), i)), C, Pg.Program.largest(p, i, n)), Pg.Program.need(p, i, n)):
  +K = U32.to_nat(k)
  +I = List.length(&2, Word(8n), i)
  +W = PG.Bl(ds, 0n)
  +S = Pg.Program.largest(p, i, n)
  +T0 = Nat.add(Nat.add(307n, C), Nat.add(Nat.mul(4n, W), Nat.mul(3n, S)))
  +B = Nat.add(Nat.mul(64n, Nat.add(Pg.Program.size(p), S)), 16777216n)
  +ht = room.top(K, I, W, ds, C, S, k.le(ds, k, ek), input.le(p, ds, i, n, rd), big.le(ds))
  N.le_trans(Room(ds, 1n+Nat.add(K, I), C, S), Nat.add(Nat.mul(20n, T0), S), Pg.Program.need(p, i, n),
    room.le(ds, 1n+Nat.add(K, I), C, S, T0, ht),
    N.le_rw_r(Nat.add(Nat.mul(20n, T0), S), B, Pg.Program.need(p, i, n), need.eq(p, i, n),
      top.need(C, W, S, Pg.Program.size(p), 16777216n, hC, w.le(p, ds, rd), pow.le())))

# 2^k a <= 2^k b, for a <= b
def D_mono(k: Nat, +a: Nat, +b: Nat, h: N.Le(a, b)) -> N.Le(N.D(k, a), N.D(k, b)):
  match k:
    case 0n:
      h
    case 1n+(+q):
      N.double_mono(N.D(q, a), N.D(q, b), D_mono(q, a, b, h))

# the pages of min(m, 65536) are the limit's
def lim.y(+m: U32, +lim: U32, elim: {lim == Wa.Wasm.min(m, 65536) : U32}) ->
  N.Le(U32.to_nat(Wa.Wasm.min.if(Cmp.is_le(U32.cmp(m, 65536)), m, 65536)), U32.to_nat(lim)):
  %Equal.sym(U32, lim, Wa.Wasm.min(m, 65536), elim) :
    N.Le(U32.to_nat(Wa.Wasm.min.if(Cmp.is_le(U32.cmp(m, 65536)), m, 65536)), U32.to_nat(_))
  N.le_refl(U32.to_nat(Wa.Wasm.min(m, 65536)))

# so they are at most the pages min(lim, 65536) that Lim.bytes counts, by the
# branch of U32.is_le(lim, 65536)
def lim.pages(b: Bool, +lim: U32, +y: Nat, hy: N.Le(y, U32.to_nat(65536)), hl: N.Le(y, U32.to_nat(lim))) ->
  N.Le(y, U32.to_nat(Wa.Wasm.min.if(b, lim, 65536))):
  match b:
    case True{}:
      hl
    case False{}:
      %{{==} : {65536 == Wa.Wasm.min.if(False{}, lim, 65536) : U32}} : N.Le(y, U32.to_nat(_))
      hy

# the bytes of m pages are within the limit lim = min(m, 65536) (Program.memory
# as need_big.bend's memory_le meets it)
def memory.le(+m: U32, +lim: U32, elim: {lim == Wa.Wasm.min(m, 65536) : U32}) ->
  N.Le(Pg.Program.memory(m), D.Lim.bytes(lim)):
  +y = U32.to_nat(Wa.Wasm.min.if(Cmp.is_le(U32.cmp(m, 65536)), m, 65536))
  +t = U32.to_nat(65536)
  +z = U32.to_nat(Wa.Wasm.min(lim, 65536))
  +hy = N.min.case(Cmp.is_le(U32.cmp(m, 65536)), m, 65536, {==})
  +hz = lim.pages(U32.is_le(lim, 65536), lim, y, hy, lim.y(m, lim, elim))
  +e2 = Equal.trans(Nat, Nat.mul(t, y), Nat.mul(N.D(16n, 1n), y), N.D(16n, y),
    Equal.cong(Nat, Nat, x => Nat.mul(x, y), t, N.D(16n, 1n), N.val_65536()), N.mul_D(16n, y))
  +h2 = N.le_rw_r(Nat.mul(65536n, y), Nat.mul(t, y), N.D(16n, y), e2, N.mul_mono_l(65536n, t, y, N.le_65536()))
  +h3 = N.le_trans(Nat.mul(65536n, y), N.D(16n, y), D.Lim.bytes(lim), h2, D_mono(16n, y, z, hz))
  N.bridge(m, D.Lim.bytes(lim), N.le_rw_l(Nat.mul(65536n, y), Nat.add(y, Nat.mul(65535n, y)), D.Lim.bytes(lim), N.mul_succ(65535n, y), h3))

# F is at most the bytes of the limit lim = min(m, 65536) of Cir.result, when
# the memory of m pages holds F
def need.lim(+p: List<&2, Word(8n)>, +i: List<&2, Word(8n)>, +n: Nat, +m: U32, +lim: U32,
  elim: {lim == Wa.Wasm.min(m, 65536) : U32},
  big: {Nat.is_le(Pg.Program.need(p, i, n), Pg.Program.memory(m)) == True{} : Bool}) ->
  N.Le(Pg.Program.need(p, i, n), D.Lim.bytes(lim)):
  N.le_trans(Pg.Program.need(p, i, n), Pg.Program.memory(m), D.Lim.bytes(lim), N.toLe(Pg.Program.need(p, i, n), Pg.Program.memory(m), big),
    memory.le(m, lim, elim))

# so, with the memory F, the limit of Cir.result's start has room for Room
# (the loop carries this and budget.lim's premises)
def room.lim(+p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +n: Nat, +m: U32, +k: U32,
  +len: U32, +pg: U32, +lim: U32, +first: U32, +C: Nat,
  rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  s: D.Start(Mc.Img.cells(ds), i, m, k, len, pg, lim, first),
  hC: N.Le(C, N.D(11n, 3n)),
  big: {Nat.is_le(Pg.Program.need(p, i, n), Pg.Program.memory(m)) == True{} : Bool}) ->
  N.Le(Room(ds, 1n+Nat.add(U32.to_nat(k), List.length(&2, Word(8n), i)), C, Pg.Program.largest(p, i, n)), D.Lim.bytes(lim)):
  (ek, r1) = s
  (em, r2) = r1
  (elim, r3) = r2
  N.le_trans(Room(ds, 1n+Nat.add(U32.to_nat(k), List.length(&2, Word(8n), i)), C, Pg.Program.largest(p, i, n)), Pg.Program.need(p, i, n),
    D.Lim.bytes(lim), room.need(p, ds, i, n, k, C, rd, ek, hC), need.lim(p, i, n, m, lim, elim, big))

# the first cell of a state of the run is Cir.result's, at most 1 + k + |i|
def fi.le(+st: Cr.Cir.State, +i: List<&2, Word(8n)>, +k: U32, +len: U32, +first: U32,
  hfi: {D.St.first(st) == first : U32},
  el: {Wa.Wasm.length32(i) == Some{len} : Maybe<&2, U32>},
  ef: {first == Cr.Cir.first(k, U32.add(Cr.Cir.input.at(k), len)) : U32}) ->
  N.Le(U32.to_nat(D.St.first(st)), 1n+Nat.add(U32.to_nat(k), List.length(&2, Word(8n), i))):
  %Equal.sym(U32, D.St.first(st), first, hfi) : N.Le(U32.to_nat(_), 1n+Nat.add(U32.to_nat(k), List.length(&2, Word(8n), i)))
  first.le(i, k, len, first, el, ef)

# the budget of a round of the run is at most F: from a state of the run
# (its first cell is Cir.result's, it has at most C <= 6144 STATIC own cells
# and at most Peak own cells), of a term of the run (it and its step have at
# most S nodes)
def budget.need(+p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +n: Nat, +m: U32, +k: U32,
  +len: U32, +pg: U32, +lim: U32, +first: U32, +st: Cr.Cir.State, +t: Bk.Term, +C: Nat,
  rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  s: D.Start(Mc.Img.cells(ds), i, m, k, len, pg, lim, first),
  hfi: {D.St.first(st) == first : U32},
  hC: N.Le(C, N.D(11n, 3n)),
  hst: N.Le(D.Stat(D.Mem.cells(st), D.St.cells(st), D.St.first(st)), C),
  ht: N.Le(Pg.Term.size(t), Pg.Program.largest(p, i, n)),
  hu: N.Le(D.StepSize(ds, t), Pg.Program.largest(p, i, n)),
  hm: N.Le(D.Mem.cells(st), Peak(ds, C, Pg.Program.largest(p, i, n)))) ->
  N.Le(D.Budget(ds, st, t), Pg.Program.need(p, i, n)):
  (ek, r1) = s
  (em, r2) = r1
  (elim, r3) = r2
  (el, r4) = r3
  (ea, ef) = r4
  +X = {1n+Nat.add(U32.to_nat(k), List.length(&2, Word(8n), i)) : Nat}
  +S = Pg.Program.largest(p, i, n)
  N.le_trans(D.Budget(ds, st, t), Room(ds, X, C, S), Pg.Program.need(p, i, n),
    budget.room(ds, st, t, X, C, S, fi.le(st, i, k, len, first, hfi, el, ef), hst, ht, hu, hm),
    room.need(p, ds, i, n, k, C, rd, ek, hC))

# M.input's budget, from what Cir.result computed for the start
def input.need.of(+p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +n: Nat, +k: U32, +len: U32, +first: U32,
  +rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  ek: {k == Cr.Wasm.encode.len(Cr.Cir.Cell, Mc.Img.cells(ds)) : U32},
  el: {Wa.Wasm.length32(i) == Some{len} : Maybe<&2, U32>},
  ef: {first == Cr.Cir.first(k, U32.add(Cr.Cir.input.at(k), len)) : U32}) ->
  N.Le(D.Cells.bytes(first, 1n+Nat.mul(27n, List.length(&2, Word(8n), i))), Pg.Program.need(p, i, n)):
  +I = List.length(&2, Word(8n), i)
  +X = {1n+Nat.add(U32.to_nat(k), I) : Nat}
  +S = Pg.Program.largest(p, i, n)
  +Y = {1n+Nat.mul(27n, I) : Nat}
  +hY = N.le_trans(Y, 5n+Nat.mul(72n, I), S, N.add_mono(1n, 5n, Nat.mul(27n, I), Nat.mul(72n, I), Unit{}, N.mul_mono_l(27n, 72n, I, Unit{})),
    start.le(p, ds, i, n, rd))
  +h = N.add_mono(U32.to_nat(first), X, Y, Peak(ds, 0n, S), first.le(i, k, len, first, el, ef), peak.ge(ds, 0n, S, Y, hY))
  N.le_trans(D.Cells.bytes(first, Y), Room(ds, X, 0n, S), Pg.Program.need(p, i, n), cells.room(ds, X, 0n, S, first, Y, h),
    room.need(p, ds, i, n, k, 0n, rd, ek, N.le_zero(N.D(11n, 3n))))

# M.input's budget (InputPost: 27 cells a byte of the input, and the focus)
# is at most F
def input.need(+p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +n: Nat, +m: U32, +k: U32,
  +len: U32, +pg: U32, +lim: U32, +first: U32,
  rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  s: D.Start(Mc.Img.cells(ds), i, m, k, len, pg, lim, first)) ->
  N.Le(D.Cells.bytes(first, 1n+Nat.mul(27n, List.length(&2, Word(8n), i))), Pg.Program.need(p, i, n)):
  (ek, r1) = s
  (em, r2) = r1
  (elim, r3) = r2
  (el, r4) = r3
  (ea, ef) = r4
  input.need.of(p, ds, i, n, k, len, first, rd, ek, el, ef)

# so, with the memory F, M.input has room for its budget in the limit
def input.lim(+p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +n: Nat, +m: U32, +k: U32,
  +len: U32, +pg: U32, +lim: U32, +first: U32,
  rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  s: D.Start(Mc.Img.cells(ds), i, m, k, len, pg, lim, first),
  big: {Nat.is_le(Pg.Program.need(p, i, n), Pg.Program.memory(m)) == True{} : Bool}) ->
  N.Le(D.Cells.bytes(first, 1n+Nat.mul(27n, List.length(&2, Word(8n), i))), D.Lim.bytes(lim)):
  (ek, r1) = s
  (em, r2) = r1
  (elim, r3) = r2
  (el, r4) = r3
  (ea, ef) = r4
  N.le_trans(D.Cells.bytes(first, 1n+Nat.mul(27n, List.length(&2, Word(8n), i))), Pg.Program.need(p, i, n), D.Lim.bytes(lim),
    input.need.of(p, ds, i, n, k, len, first, rd, ek, el, ef), need.lim(p, i, n, m, lim, elim, big))

# the bytes up to the cell after the image's k cells and the input, which
# Cir.result needs before the program, are at most F
def start.need(+p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +n: Nat, +k: U32,
  +rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  ek: {k == Cr.Wasm.encode.len(Cr.Cir.Cell, Mc.Img.cells(ds)) : U32}) ->
  N.Le(Nat.add(Nat.mul(20n, 2n+U32.to_nat(k)), List.length(&2, Word(8n), i)), Pg.Program.need(p, i, n)):
  +K = U32.to_nat(k)
  +I = List.length(&2, Word(8n), i)
  +S = Pg.Program.largest(p, i, n)
  +P = Peak(ds, 0n, S)
  +Z = Nat.add(Nat.add(K, I), P)
  +h1 = N.le_rw_l(Nat.add(K, 1n), 1n+K, Z, add_one(K), N.add_mono(K, Nat.add(K, I), 1n, P, N.le_add_r(K, I), Unit{}))
  N.le_trans(Nat.add(Nat.mul(20n, 2n+K), I), Room(ds, 1n+Nat.add(K, I), 0n, S), Pg.Program.need(p, i, n),
    room.ge(ds, 1n+Nat.add(K, I), 0n, S, 2n+K, I, h1, input.le(p, ds, i, n, rd)),
    room.need(p, ds, i, n, k, 0n, rd, ek, N.le_zero(N.D(11n, 3n))))
