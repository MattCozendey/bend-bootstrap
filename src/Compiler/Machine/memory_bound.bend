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
def start.size(+i: List<&2, Word(8n)>) ->
  {Pg.Term.size(Pg.Program.start(i)) == 5n+Nat.mul(72n, List.length(&2, Word(8n), i)) : Nat}:
  ?TODO

# so the input has at most S / 72 bytes
def start.le(+p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +n: Nat,
  rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>}) ->
  N.Le(5n+Nat.mul(72n, List.length(&2, Word(8n), i)), Pg.Program.largest(p, i, n)):
  ?TODO

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

# the image's k cells: 290, then one a node of the def bodies (W)
def k.le(+ds: List<&2, Bk.Def>, +k: U32,
  ek: {k == Cr.Wasm.encode.len(Cr.Cir.Cell, Mc.Img.cells(ds)) : U32}) ->
  N.Le(U32.to_nat(k), Nat.add(290n, PG.Bl(ds, 0n))):
  ?TODO

# the largest def body has at most W nodes
def big.le(+ds: List<&2, Bk.Def>) -> N.Le(D.Defs.big(ds), PG.Bl(ds, 0n)):
  ?TODO

# each node of a def body is 3 nodes or more of the book's data form: 3 W is
# at most the program's size
def w.le(+p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>,
  rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>}) ->
  N.Le(Nat.mul(3n, PG.Bl(ds, 0n)), Pg.Program.size(p)):
  ?TODO

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

# the larger of a and b is at most c when both are
def max.le(+a: Nat, +b: Nat, +c: Nat, ha: N.Le(a, c), hb: N.Le(b, c)) -> N.Le(Nat.max(a, b), c):
  ?TODO

# Peak holds the STATIC own cells and the nodes of one term (the state after
# M.input: the cache and the start term)
def peak.ge(+ds: List<&2, Bk.Def>, +C: Nat, +S: Nat, +a: Nat, h: N.Le(a, Nat.add(C, S))) -> N.Le(a, Peak(ds, C, S)):
  ?TODO

# a round from the state st, of the term t, needs at most Peak own cells,
# when st has at most C STATIC own cells and t and its step at most S nodes
def need.peak(+ds: List<&2, Bk.Def>, +st: Cr.Cir.State, +t: Bk.Term, +C: Nat, +S: Nat,
  hst: N.Le(D.Stat(D.Mem.cells(st), D.St.cells(st), D.St.first(st)), C),
  ht: N.Le(Pg.Term.size(t), S),
  hu: N.Le(D.StepSize(ds, t), S)) ->
  N.Le(D.Need(ds, st, t), Peak(ds, C, S)):
  ?TODO

# the bytes of Need are within Budget
def need.bytes.le(+ds: List<&2, Bk.Def>, +st: Cr.Cir.State, +t: Bk.Term) ->
  N.Le(D.Need.bytes(ds, st, t), D.Budget(ds, st, t)):
  ?TODO

# and its budget is at most Room, when st has at most Peak own cells and its
# first cell is at most X
def budget.room(+ds: List<&2, Bk.Def>, +st: Cr.Cir.State, +t: Bk.Term, +X: Nat, +C: Nat, +S: Nat,
  hfi: N.Le(U32.to_nat(D.St.first(st)), X),
  hst: N.Le(D.Stat(D.Mem.cells(st), D.St.cells(st), D.St.first(st)), C),
  ht: N.Le(Pg.Term.size(t), S),
  hu: N.Le(D.StepSize(ds, t), S),
  hm: N.Le(D.Mem.cells(st), Peak(ds, C, S))) ->
  N.Le(D.Budget(ds, st, t), Room(ds, X, C, S)):
  ?TODO

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
  ?TODO

# The run's memory
# ----------------

# 2^18 <= 2^24: the one comparison of two closed numbers
def pow.le() -> N.Le(N.D(18n, 1n), 16777216n):
  ?TODO

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
