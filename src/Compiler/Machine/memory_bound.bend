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

# a term that Program.unbytes reads as the bytes o has 72 nodes a byte and 3
# more
def out.size(+v: Bk.Term, +o: List<&2, Word(8n)>,
  e: {Pg.Program.unbytes(v) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}) ->
  {Pg.Term.size(v) == 3n+Nat.mul(72n, List.length(&2, Word(8n), o)) : Nat}:
  ?TODO

# so the result o of the run has at most S / 72 bytes
def out.le(+p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +n: Nat, +o: List<&2, Word(8n)>,
  rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  e: {Pg.Program.result(ds, El.Eval.steps(n, ds, Pg.Program.start(i))) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}) ->
  N.Le(3n+Nat.mul(72n, List.length(&2, Word(8n), o)), Pg.Program.largest(p, i, n)):
  ?TODO

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

# the length that Wasm.length32 gives is the list's
def len.le(+i: List<&2, Word(8n)>, +len: U32,
  el: {Wa.Wasm.length32(i) == Some{len} : Maybe<&2, U32>}) ->
  N.Le(U32.to_nat(len), List.length(&2, Word(8n), i)):
  ?TODO

# the first cell after the image's k cells and the input's bytes, as
# Cir.result computes it, is at most 1 + k + |i|
def first.le(+i: List<&2, Word(8n)>, +k: U32, +len: U32, +first: U32,
  el: {Wa.Wasm.length32(i) == Some{len} : Maybe<&2, U32>},
  ef: {first == Cr.Cir.first(k, U32.add(Cr.Cir.input.at(k), len)) : U32}) ->
  N.Le(U32.to_nat(first), 1n+Nat.add(U32.to_nat(k), List.length(&2, Word(8n), i))):
  ?TODO

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

# Room, for the first cell of the run (first.le), C <= 6144 STATIC own cells
# and the run's largest term S, is at most F
def room.need(+p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +n: Nat, +k: U32, +C: Nat,
  rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  ek: {k == Cr.Wasm.encode.len(Cr.Cir.Cell, Mc.Img.cells(ds)) : U32},
  hC: N.Le(C, N.D(11n, 3n))) ->
  N.Le(Room(ds, 1n+Nat.add(U32.to_nat(k), List.length(&2, Word(8n), i)), C, Pg.Program.largest(p, i, n)), Pg.Program.need(p, i, n)):
  ?TODO

# F is at most the bytes of the limit lim = min(m, 65536) of Cir.result, when
# the memory of m pages holds F
def need.lim(+p: List<&2, Word(8n)>, +i: List<&2, Word(8n)>, +n: Nat, +m: U32, +lim: U32,
  elim: {lim == Wa.Wasm.min(m, 65536) : U32},
  big: {Nat.is_le(Pg.Program.need(p, i, n), Pg.Program.memory(m)) == True{} : Bool}) ->
  N.Le(Pg.Program.need(p, i, n), D.Lim.bytes(lim)):
  ?TODO

# so, with the memory F, the limit of Cir.result's start has room for Room
# (the loop carries this and budget.lim's premises)
def room.lim(+p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +n: Nat, +m: U32, +k: U32,
  +len: U32, +pg: U32, +lim: U32, +first: U32, +C: Nat,
  rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  s: D.Start(Mc.Img.cells(ds), i, m, k, len, pg, lim, first),
  hC: N.Le(C, N.D(11n, 3n)),
  big: {Nat.is_le(Pg.Program.need(p, i, n), Pg.Program.memory(m)) == True{} : Bool}) ->
  N.Le(Room(ds, 1n+Nat.add(U32.to_nat(k), List.length(&2, Word(8n), i)), C, Pg.Program.largest(p, i, n)), D.Lim.bytes(lim)):
  ?TODO

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
  ?TODO

# M.input's budget (InputPost: 27 cells a byte of the input, and the focus)
# is at most F
def input.need(+p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +n: Nat, +m: U32, +k: U32,
  +len: U32, +pg: U32, +lim: U32, +first: U32,
  rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  s: D.Start(Mc.Img.cells(ds), i, m, k, len, pg, lim, first)) ->
  N.Le(D.Cells.bytes(first, 1n+Nat.mul(27n, List.length(&2, Word(8n), i))), Pg.Program.need(p, i, n)):
  ?TODO

# so, with the memory F, M.input has room for its budget in the limit
def input.lim(+p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +n: Nat, +m: U32, +k: U32,
  +len: U32, +pg: U32, +lim: U32, +first: U32,
  rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  s: D.Start(Mc.Img.cells(ds), i, m, k, len, pg, lim, first),
  big: {Nat.is_le(Pg.Program.need(p, i, n), Pg.Program.memory(m)) == True{} : Bool}) ->
  N.Le(D.Cells.bytes(first, 1n+Nat.mul(27n, List.length(&2, Word(8n), i))), D.Lim.bytes(lim)):
  ?TODO

# the bytes up to the cell after the image's k cells and the input, which
# Cir.result needs before the program, are at most F
def start.need(+p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +n: Nat, +k: U32,
  rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  ek: {k == Cr.Wasm.encode.len(Cr.Cir.Cell, Mc.Img.cells(ds)) : U32}) ->
  N.Le(Nat.add(Nat.mul(20n, 2n+U32.to_nat(k)), List.length(&2, Word(8n), i)), Pg.Program.need(p, i, n)):
  ?TODO
