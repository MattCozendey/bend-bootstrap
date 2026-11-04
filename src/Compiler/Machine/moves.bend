# compiler: layer B8, the assembly of the machine's proofs
# ========================================================
#
# mach.safe, mach.sound, mach.complete and mach.memory of runs_as_eval.bend,
# with exactly their types (mach.*.proof, at the end), proven from the laws of
# the layers below: input.spec (routines/spec.bend) starts the run in a state
# that Inv finds for the start term; round.sim (moves/spec.bend) moves each
# round as AM.move does; am.ok (am/spec.bend) says that each move is an admin
# move (the same term, a smaller measure AS.w), a canonical step (CStep), or a
# halt as the term asks; canon.steps and canon.result (canon/spec.bend) turn
# canonical steps from the start term into Eval's; code.fits, round.mem and
# the bounds of memory/spec.bend give the output's room and the memory.
#
# The loop (Asm.loop, Mach.code's while): asm.post, by induction on the fuel,
# halts only as Eval says (HE); asm.done, by induction on Eval's steps and,
# between two steps, on the measure, finds a fuel that gives Eval's result or
# runs out of memory; asm.mem does so with no out of memory, from the memory
# F: it carries the run's position (j steps done), the limit, the cache's
# cells (at most C) and next - first (at most Peak). Each round's facts are
# Asm.J: Inv and AS.ok0 (what am.ok asks, with inv.vb).
#
# Only laws are used (proven or not): no ?TODO is in this file.

import Base
import ../../Shared/shared.bend as Sd
import ../../Book/impl.bend as Bk
import ../../Eval/impl.bend as El
import ../../Wasm/impl.bend as Wa
import ../../Program/impl.bend as Pg
import ../Cir/impl.bend as Cr
import ./impl.bend as Mc
import ../need_big.bend as N
import ../Cir/simulation_memory_bytes.bend as SB
import ./shared.bend as K
import ./logic/spec.bend as Lg
import ./canon/spec.bend as C
import ./am/spec.bend as A
import ./heap/spec.bend as Hp
import ./image/spec.bend as I
import ./routines/spec.bend as R
import ./memory/spec.bend as Me
import ./moves/spec.bend as Mv
import ./logic/impl.bend as LgP
import ./header/impl.bend as HsP
import ./canon/impl.bend as CP
import ./am/impl.bend as AP
import ./heap/view.bend as HpV
import ./heap/count.bend as HpC
import ./image/impl.bend as IP
import ./routines/prims.bend as RP
import ./routines/nth.bend as RN
import ./routines/dec.bend as RD
import ./routines/copy.bend as RC
import ./routines/walk.bend as RW
import ./routines/out.bend as RO
import ./routines/input.bend as RI
import ./memory/impl.bend as MeP
import ./moves/round.bend as MvP

# Kit
# ---

def Asm.mb.T(x: Maybe<&2, List<&2, Word(8n)>>) -> Type:
  match x:
    case None{}:
      Unit
    case Some{_}:
      Empty

# None is not Some (bytes)
def asm.mb.ne(-o: List<&2, Word(8n)>, e: {None{} == Some{o} : Maybe<&2, List<&2, Word(8n)>>}) -> Empty:
  %e : Asm.mb.T(_)
  Unit{}

def asm.mb.get(x: Maybe<&2, List<&2, Word(8n)>>, d: List<&2, Word(8n)>) -> List<&2, Word(8n)>:
  match x:
    case None{}:
      d
    case Some{y}:
      y

# Some is one to one (bytes)
def asm.mb.inj(+a: List<&2, Word(8n)>, -b: List<&2, Word(8n)>, e: {Some{a} == Some{b} : Maybe<&2, List<&2, Word(8n)>>}) ->
  {a == b : List<&2, Word(8n)>}:
  Equal.cong(Maybe<&2, List<&2, Word(8n)>>, List<&2, Word(8n)>, x => asm.mb.get(x, a), Some{a}, Some{b}, e)

def Asm.tm.T(x: Maybe<Bk.Term>) -> Type:
  match x:
    case None{}:
      Unit
    case Some{_}:
      Empty

# None is not Some (terms)
def asm.tm.ne(-u: Bk.Term, e: {None{} == Some{u} : Maybe<Bk.Term>}) -> Empty:
  %e : Asm.tm.T(_)
  Unit{}

def asm.tm.get(x: Maybe<Bk.Term>, d: Bk.Term) -> Bk.Term:
  match x:
    case None{}:
      d
    case Some{y}:
      y

# Some is one to one (terms)
def asm.tm.inj(+a: Bk.Term, -b: Bk.Term, e: {Some{a} == Some{b} : Maybe<Bk.Term>}) -> {a == b : Bk.Term}:
  Equal.cong(Maybe<Bk.Term>, Bk.Term, x => asm.tm.get(x, a), Some{a}, Some{b}, e)

# Tm.is says the term
def asm.tm.is(r: Maybe<Bk.Term>, +t: Bk.Term, +h: {C.Tm.is(r, t) == True{} : Bool}) -> {r == Some{t} : Maybe<Bk.Term>}:
  match r:
    case Some{+u}:
      Equal.cong(Bk.Term, Maybe<Bk.Term>, z => Some{z}, u, t, C.term.is_eq_ok(u, t, h))
    case None{}:
      K.bool.ff({None{} == Some{t} : Maybe<Bk.Term>}, h)

# Tm.none says none
def asm.tm.none(r: Maybe<Bk.Term>, +h: {C.Tm.none(r) == True{} : Bool}) -> {r == None{} : Maybe<Bk.Term>}:
  match r:
    case Some{_}:
      K.bool.ff({r == None{} : Maybe<Bk.Term>}, h)
    case None{}:
      {==}

# Name.is_eq says True only of equal names
def asm.name.ok(a: List<&2, Word(8n)>, +b: List<&2, Word(8n)>, +e: {Sd.Name.is_eq(a, b) == True{} : Bool}) ->
  {a == b : List<&2, Word(8n)>}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Con{+x, +xs} Con{+y, +ys}:
      +ex = SB.W.eq(8n, x, y, K.bool.and_l(Sd.Byte.is_eq(x, y), Sd.Name.is_eq(xs, ys), e))
      +er = asm.name.ok(xs, ys, K.bool.and_r(Sd.Byte.is_eq(x, y), Sd.Name.is_eq(xs, ys), e))
      %ex : {Con{x, xs} == Con{_, ys} : List<&2, Word(8n)>}
      %er : {Con{x, xs} == Con{x, _} : List<&2, Word(8n)>}
      {==}
    case Nil{} Con{_, _}:
      K.bool.ff({a == b : List<&2, Word(8n)>}, e)
    case Con{_, _} Nil{}:
      K.bool.ff({a == b : List<&2, Word(8n)>}, e)

# a || b gives one of them
def asm.or(a: Bool, -b: Bool, +h: {Bool.or(a, b) == True{} : Bool}) -> Or({a == True{} : Bool}, {b == True{} : Bool}):
  match a:
    case True{}:
      Inl{{==}}
    case False{}:
      Inr{h}

# a Bool that is true, from its truth as a type
def asm.fromT(b: Bool, t: N.T(b)) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, t)

def asm.le.trans(+a: Nat, +b: Nat, +c: Nat, +h1: {Nat.is_le(a, b) == True{} : Bool}, +h2: {Nat.is_le(b, c) == True{} : Bool}) ->
  {Nat.is_le(a, c) == True{} : Bool}:
  asm.fromT(Nat.is_le(a, c), N.le_trans(a, b, c, N.toLe(a, b, h1), N.toLe(b, c, h2)))

# a < b and b <= a: none
def asm.lt.abs(a: Nat, b: Nat, +h1: {Nat.is_lt(a, b) == True{} : Bool}, +h2: {Nat.is_le(b, a) == True{} : Bool}) -> Empty:
  match a b:
    case 0n 0n:
      K.bool.ff(Empty, h1)
    case 0n 1n+q:
      K.bool.ff(Empty, h2)
    case 1n+p 0n:
      K.bool.ff(Empty, h1)
    case 1n+p 1n+q:
      asm.lt.abs(p, q, h1, h2)

# the measure is below 0: none
def asm.lt0(a: Nat, +h: {Nat.is_lt(a, 0n) == True{} : Bool}) -> Empty:
  match a:
    case 0n:
      K.bool.ff(Empty, h)
    case 1n+p:
      K.bool.ff(Empty, h)

# a < b and b < 1 + c give a < c
def asm.lt.step(a: Nat, b: Nat, c: Nat, +h1: {Nat.is_lt(a, b) == True{} : Bool}, +h2: {Nat.is_lt(b, 1n+c) == True{} : Bool}) ->
  {Nat.is_lt(a, c) == True{} : Bool}:
  match a b c:
    case 0n 0n _:
      K.bool.ff({Nat.is_lt(0n, c) == True{} : Bool}, h1)
    case 1n+p 0n _:
      K.bool.ff({Nat.is_lt(1n+p, c) == True{} : Bool}, h1)
    case 0n 1n+q 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, asm.lt0(q, h2))
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 1n+q 0n:
      Empty.absurd({Nat.is_lt(1n+p, 0n) == True{} : Bool}, asm.lt0(q, h2))
    case 1n+p 1n+q 1n+r:
      asm.lt.step(p, q, r, h1, h2)

# n < 1 + n
def asm.lt.succ(n: Nat) -> {Nat.is_lt(n, 1n+n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      asm.lt.succ(p)

# a <= a + b
def asm.le.add(+a: Nat, +b: Nat) -> {Nat.is_le(a, Nat.add(a, b)) == True{} : Bool}:
  asm.fromT(Nat.is_le(a, Nat.add(a, b)), N.le_add_r(a, b))

# the larger of a and b is at most c when both are
def asm.max.le(a: Nat, b: Nat, c: Nat, +ha: {Nat.is_le(a, c) == True{} : Bool}, +hb: {Nat.is_le(b, c) == True{} : Bool}) ->
  {Nat.is_le(Nat.max(a, b), c) == True{} : Bool}:
  match a b c:
    case 0n _ _:
      hb
    case 1n+p 0n _:
      ha
    case 1n+p 1n+q 0n:
      K.bool.ff({Nat.is_le(Nat.max(1n+p, 1n+q), 0n) == True{} : Bool}, ha)
    case 1n+p 1n+q 1n+r:
      asm.max.le(p, q, r, ha, hb)

# no canonical steps from no term
def asm.cs.none(n: Nat, +ds: List<&2, Bk.Def>) -> {C.CSteps(n, ds, None{}) == None{} : Maybe<Bk.Term>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

# one more canonical step, at the end
def asm.cs.snoc(j: Nat, +ds: List<&2, Bk.Def>, r: Maybe<Bk.Term>, +t: Bk.Term, +u: Bk.Term,
  +h: {C.CSteps(j, ds, r) == Some{t} : Maybe<Bk.Term>}, +es: {C.CStep(ds, t) == Some{u} : Maybe<Bk.Term>}) ->
  {C.CSteps(1n+j, ds, r) == Some{u} : Maybe<Bk.Term>}:
  match j r:
    case 0n None{}:
      Empty.absurd({C.CSteps(1n, ds, None{}) == Some{u} : Maybe<Bk.Term>}, asm.tm.ne(t, h))
    case 0n Some{+w}:
      %Equal.sym(Bk.Term, w, t, asm.tm.inj(w, t, h)) : {C.CSteps(0n, ds, C.CStep(ds, _)) == Some{u} : Maybe<Bk.Term>}
      es
    case 1n+p None{}:
      Empty.absurd({C.CSteps(2n+p, ds, None{}) == Some{u} : Maybe<Bk.Term>}, asm.tm.ne(t, h))
    case 1n+p Some{+w}:
      asm.cs.snoc(p, ds, C.CStep(ds, w), t, u, h, es)

# the canonical steps from the start term give Eval's result
def asm.cs.eval(+ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +n: Nat) ->
  {Pg.Program.result(ds, C.CSteps(n, ds, Some{Pg.Program.start(i)})) == Pg.Program.result(ds, El.Eval.steps(n, ds, Pg.Program.start(i))) :
    Maybe<&2, List<&2, Word(8n)>>}:
  +t = Pg.Program.start(i)
  +ec = C.term.is_eq_ok(C.Canon.term(t, 0n), t, C.canon.start(i))
  %ec : {Pg.Program.result(ds, C.CSteps(n, ds, Some{_})) == Pg.Program.result(ds, El.Eval.steps(n, ds, t)) : Maybe<&2, List<&2, Word(8n)>>}
  %Equal.sym(Maybe<Bk.Term>, C.CSteps(n, ds, Some{C.Canon.term(t, 0n)}), C.Canon.opt(El.Eval.steps(n, ds, t)), C.canon.steps(n, ds, t)) :
    {Pg.Program.result(ds, _) == Pg.Program.result(ds, El.Eval.steps(n, ds, t)) : Maybe<&2, List<&2, Word(8n)>>}
  C.canon.result(ds, El.Eval.steps(n, ds, t))

# a value has no canonical step
def asm.vals(b: Bool, +ds: List<&2, Bk.Def>, +t: Bk.Term, -o: List<&2, Word(8n)>, +eb: {El.Eval.vals(ds, t, False{}) == b : Bool},
  e: {Pg.Program.result.if(b, t) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}) -> {C.CStep(ds, t) == None{} : Maybe<Bk.Term>}:
  match b:
    case True{}:
      %Equal.sym(Maybe<Bk.Term>, El.Eval.step(ds, t), None{}, Me.eval.stops(ds, t, eb)) : {C.Canon.opt(_) == None{} : Maybe<Bk.Term>}
      {==}
    case False{}:
      Empty.absurd({C.CStep(ds, t) == None{} : Maybe<Bk.Term>}, asm.mb.ne(o, e))

# The outcomes of a round and of the loop
# ---------------------------------------

# the loop: Mach.code's while
def Asm.loop() -> Cr.Cir.Stmt:
  Mc.M.while(Mc.M.c(1), Mc.Mach.round())

# what a round needs of its state: Inv and what am.ok asks but the focus' flag
def Asm.J(+x: Hp.Cx, +st: Cr.Cir.State, +s: A.AS) -> Bool:
  R.Inv(x, st, s) && A.AS.ok0(Hp.Cx.ds(x), s)

# a pair of facts, as Data (Base's & is a Type)
def Asm.P2(-A: Data, -B: Data) -> Data:
  Sigma<&2, &2, A, _ => B>

# a round went on to u by an admin move from the term t of measure w
def Asm.Adm(+x: Hp.Cx, +t: Bk.Term, +w: Nat, +u: Cr.Cir.State) -> Type:
  Sigma<&2, &2, A.AS, s2 => Asm.P2({Asm.J(x, u, s2) == True{} : Bool},
    Asm.P2({A.AS.term(s2) == t : Bk.Term}, {Nat.is_lt(A.AS.w(s2), w) == True{} : Bool}))>

# or by a canonical step of t
def Asm.Stp(+x: Hp.Cx, +t: Bk.Term, +u: Cr.Cir.State) -> Type:
  Sigma<&2, &2, A.AS, s2 => Asm.P2({Asm.J(x, u, s2) == True{} : Bool}, {C.CStep(Hp.Cx.ds(x), t) == Some{A.AS.term(s2)} : Maybe<Bk.Term>})>

def Asm.Rnd(+x: Hp.Cx, +t: Bk.Term, +w: Nat, +u: Cr.Cir.State) -> Type:
  Or(Asm.Adm(x, t, w, u), Asm.Stp(x, t, u))

# a round from the term t halted with k: with 0, t has no step and its
# result is the output's bytes; with 2, it has no step and no result
def Asm.HR(+ds: List<&2, Bk.Def>, +t: Bk.Term, +k: U32, +st2: Cr.Cir.State) -> Type:
  Or(Asm.P2({k == 0 : U32}, Asm.P2({C.CStep(ds, t) == None{} : Maybe<Bk.Term>},
      {Pg.Program.result(ds, Some{t}) == Some{List.reverse(&2, Word(8n), Lg.St.out(st2))} : Maybe<&2, List<&2, Word(8n)>>})),
    Asm.P2({k == 2 : U32}, Asm.P2({C.CStep(ds, t) == None{} : Maybe<Bk.Term>},
      {Pg.Program.result(ds, Some{t}) == None{} : Maybe<&2, List<&2, Word(8n)>>})))

# the loop from the term t halted with k: with 0, some canonical steps from t
# reach the output's bytes; else k is 2
def Asm.HE(+ds: List<&2, Bk.Def>, +t: Bk.Term, +k: U32, +st2: Cr.Cir.State) -> Type:
  Or(Asm.P2({k == 0 : U32}, Sigma<&2, &2, Nat, n => {Pg.Program.result(ds, C.CSteps(n, ds, Some{t})) ==
    Some{List.reverse(&2, Word(8n), Lg.St.out(st2))} : Maybe<&2, List<&2, Word(8n)>>}>), {k == 2 : U32})

# what a run of the loop gives at any fuel: never next, a halt with H, out of
# memory or of fuel; never a trap
def Asm.Ps(o: Cr.Cir.Out, H: U32 -> Cr.Cir.State -> Type) -> Type:
  match o:
    case Cr.Cir.Out.next{_}:
      Empty
    case Cr.Cir.Out.halt{s, st}:
      H(s, st)
    case Cr.Cir.Out.out_of_memory{}:
      Unit
    case Cr.Cir.Out.trap{}:
      Empty
    case Cr.Cir.Out.not_done{}:
      Unit

def Asm.Oom(m: Bool) -> Data:
  match m:
    case True{}:
      Empty
    case False{}:
      Unit

# the end of a run that gives the bytes o, or (when m is False) runs out of
# memory
def Asm.Good(+m: Bool, +o: List<&2, Word(8n)>, r: Cr.Cir.Out) -> Data:
  match r:
    case Cr.Cir.Out.next{_}:
      Empty
    case Cr.Cir.Out.halt{s, st}:
      Asm.P2({s == 0 : U32}, {List.reverse(&2, Word(8n), Lg.St.out(st)) == o : List<&2, Word(8n)>})
    case Cr.Cir.Out.out_of_memory{}:
      Asm.Oom(m)
    case Cr.Cir.Out.trap{}:
      Empty
    case Cr.Cir.Out.not_done{}:
      Empty

def Asm.Nd(o: Cr.Cir.Out) -> Type:
  match o:
    case Cr.Cir.Out.not_done{}:
      Empty
    case _:
      Unit

# an outcome that ended is not out of fuel
def asm.nd(-o: Cr.Cir.Out, e: {o == Cr.Cir.Out.not_done{} : Cr.Cir.Out}, u: Asm.Nd(o)) -> Empty:
  %e : Asm.Nd(_)
  u

def asm.ps.wk(o: Cr.Cir.Out, -H1: U32 -> Cr.Cir.State -> Type, -H2: U32 -> Cr.Cir.State -> Type, h: Asm.Ps(o, H1),
  hh: @s: U32 -> @st: Cr.Cir.State -> H1(s, st) -> H2(s, st)) -> Asm.Ps(o, H2):
  match o:
    case Cr.Cir.Out.next{_}:
      h
    case Cr.Cir.Out.halt{s, st}:
      hh(s, st, h)
    case Cr.Cir.Out.out_of_memory{}:
      Unit{}
    case Cr.Cir.Out.trap{}:
      h
    case Cr.Cir.Out.not_done{}:
      Unit{}

# what the loop gives, then more: the same, as the loop never goes on
def asm.ps.then(o: Cr.Cir.Out, -k: Cr.Cir.State -> Cr.Cir.Out, -H: U32 -> Cr.Cir.State -> Type, h: Asm.Ps(o, H)) ->
  Asm.Ps(Cr.Cir.exec.then(o, k), H):
  match o:
    case Cr.Cir.Out.next{st}:
      Empty.absurd(Asm.Ps(k(st), H), h)
    case Cr.Cir.Out.halt{s, st}:
      h
    case Cr.Cir.Out.out_of_memory{}:
      Unit{}
    case Cr.Cir.Out.trap{}:
      h
    case Cr.Cir.Out.not_done{}:
      Unit{}

def asm.good.then(+m: Bool, -o: List<&2, Word(8n)>, r: Cr.Cir.Out, -k: Cr.Cir.State -> Cr.Cir.Out, g: Asm.Good(m, o, r)) ->
  Asm.Good(m, o, Cr.Cir.exec.then(r, k)):
  match r:
    case Cr.Cir.Out.next{st}:
      Empty.absurd(Asm.Good(m, o, k(st)), g)
    case Cr.Cir.Out.halt{s, st}:
      g
    case Cr.Cir.Out.out_of_memory{}:
      g
    case Cr.Cir.Out.trap{}:
      g
    case Cr.Cir.Out.not_done{}:
      g

# a good end ended
def asm.good.done(+m: Bool, -o: List<&2, Word(8n)>, r: Cr.Cir.Out, g: Asm.Good(m, o, r)) -> {Lg.Out.done(r) == True{} : Bool}:
  match r:
    case Cr.Cir.Out.next{_}:
      {==}
    case Cr.Cir.Out.halt{_, _}:
      {==}
    case Cr.Cir.Out.out_of_memory{}:
      {==}
    case Cr.Cir.Out.trap{}:
      {==}
    case Cr.Cir.Out.not_done{}:
      Empty.absurd({Lg.Out.done(Cr.Cir.Out.not_done{}) == True{} : Bool}, g)

# The round
# ---------

# a round's halt, by its result r: HR
def asm.hr.res(r: Maybe<&2, List<&2, Word(8n)>>, +ds: List<&2, Bk.Def>, +t: Bk.Term, +k: U32, +j: U32, +out: List<&2, Word(8n)>,
  +st2: Cr.Cir.State, +er: {Pg.Program.result(ds, Some{t}) == r : Maybe<&2, List<&2, Word(8n)>>}, +ek: {k == j : U32},
  +cn: {C.CStep(ds, t) == None{} : Maybe<Bk.Term>}, +ar: {A.AO.res(j, r, out) == True{} : Bool},
  +hr: {Bool.or(Bool.not(U32.is_eq(j, 0)), Sd.Name.is_eq(List.reverse(&2, Word(8n), Lg.St.out(st2)), out)) == True{} : Bool}) ->
  Asm.HR(ds, t, k, st2):
  match r:
    case Some{+bs}:
      +e0 = SB.U32.eq(j, 0, K.bool.and_l(U32.is_eq(j, 0), Sd.Name.is_eq(bs, out), ar))
      +eb = asm.name.ok(bs, out, K.bool.and_r(U32.is_eq(j, 0), Sd.Name.is_eq(bs, out), ar))
      +hn = {(%e0 : {Bool.or(Bool.not(U32.is_eq(_, 0)), Sd.Name.is_eq(List.reverse(&2, Word(8n), Lg.St.out(st2)), out)) == True{} : Bool}; hr) :
        {Sd.Name.is_eq(List.reverse(&2, Word(8n), Lg.St.out(st2)), out) == True{} : Bool}}
      +eo = asm.name.ok(List.reverse(&2, Word(8n), Lg.St.out(st2)), out, hn)
      +ex = Equal.trans(List<&2, Word(8n)>, bs, out, List.reverse(&2, Word(8n), Lg.St.out(st2)), eb,
        Equal.sym(List<&2, Word(8n)>, List.reverse(&2, Word(8n), Lg.St.out(st2)), out, eo))
      Inl{(Equal.trans(U32, k, j, 0, ek, e0), (cn, Equal.trans(Maybe<&2, List<&2, Word(8n)>>, Pg.Program.result(ds, Some{t}), Some{bs},
        Some{List.reverse(&2, Word(8n), Lg.St.out(st2))}, er,
        Equal.cong(List<&2, Word(8n)>, Maybe<&2, List<&2, Word(8n)>>, z => Some{z}, bs, List.reverse(&2, Word(8n), Lg.St.out(st2)), ex))))}
    case None{}:
      Inr{(Equal.trans(U32, k, j, 2, ek, SB.U32.eq(j, 2, ar)), (cn, er))}

# an admin move or a step, by am.ok's choice
def asm.rnd.pick(+x: Hp.Cx, +s: A.AS, +s2: A.AS, +u: Cr.Cir.State, +j2: {Asm.J(x, u, s2) == True{} : Bool},
  c: Or({A.AO.adm(s, s2) == True{} : Bool}, {C.Tm.is(C.CStep(Hp.Cx.ds(x), A.AS.term(s)), A.AS.term(s2)) == True{} : Bool})) ->
  Asm.Rnd(x, A.AS.term(s), A.AS.w(s), u):
  match c:
    case Inl{+ha}:
      +eq = C.term.is_eq_ok(A.AS.term(s2), A.AS.term(s),
        K.bool.and_l(C.Term.is_eq(A.AS.term(s2), A.AS.term(s)), Nat.is_lt(A.AS.w(s2), A.AS.w(s)), ha))
      Inl{(s2, (j2, (eq, K.bool.and_r(C.Term.is_eq(A.AS.term(s2), A.AS.term(s)), Nat.is_lt(A.AS.w(s2), A.AS.w(s)), ha))))}
    case Inr{+hb}:
      Inr{(s2, (j2, asm.tm.is(C.CStep(Hp.Cx.ds(x), A.AS.term(s)), A.AS.term(s2), hb)))}

# a round that goes on: by am.ok, an admin move or a step
def asm.rnd.next(+x: Hp.Cx, +s: A.AS, o: A.AO, +u: Cr.Cir.State, +ok: {A.AO.ok(Hp.Cx.ds(x), s, o) == True{} : Bool},
  +h: {Mv.Next.is(x, o, u) == True{} : Bool}) -> Asm.Rnd(x, A.AS.term(s), A.AS.w(s), u):
  match o:
    case A.AO.next{+s2}:
      +ds = Hp.Cx.ds(x)
      +rel = Bool.or(A.AO.adm(s, s2), C.Tm.is(C.CStep(ds, A.AS.term(s)), A.AS.term(s2)))
      +j2 = K.bool.and_i(R.Inv(x, u, s2), A.AS.ok0(ds, s2), h, K.bool.and_l(A.AS.ok0(ds, s2), rel, ok))
      +hr = K.bool.and_r(A.AS.ok0(ds, s2), rel, ok)
      asm.rnd.pick(x, s, s2, u, j2, asm.or(A.AO.adm(s, s2), C.Tm.is(C.CStep(ds, A.AS.term(s)), A.AS.term(s2)), hr))
    case A.AO.halt{_, _}:
      K.bool.ff(Asm.Rnd(x, A.AS.term(s), A.AS.w(s), u), h)

# a round that halts: by am.ok, as the term asks
def asm.rnd.halt(+ds: List<&2, Bk.Def>, +s: A.AS, o: A.AO, +k: U32, +st2: Cr.Cir.State, +ok: {A.AO.ok(ds, s, o) == True{} : Bool},
  +h: {Mv.Halt.is(o, k, st2) == True{} : Bool}) -> Asm.HR(ds, A.AS.term(s), k, st2):
  match o:
    case A.AO.next{_}:
      K.bool.ff(Asm.HR(ds, A.AS.term(s), k, st2), h)
    case A.AO.halt{+j, +out}:
      +t = A.AS.term(s)
      +ho = Bool.or(Bool.not(U32.is_eq(j, 0)), Sd.Name.is_eq(List.reverse(&2, Word(8n), Lg.St.out(st2)), out))
      +rs = A.AO.res(j, Pg.Program.result(ds, Some{t}), out)
      asm.hr.res(Pg.Program.result(ds, Some{t}), ds, t, k, j, out, st2, {==}, SB.U32.eq(k, j, K.bool.and_l(U32.is_eq(k, j), ho, h)),
        asm.tm.none(C.CStep(ds, t), K.bool.and_l(C.Tm.none(C.CStep(ds, t)), rs, ok)), K.bool.and_r(C.Tm.none(C.CStep(ds, t)), rs, ok),
        K.bool.and_r(U32.is_eq(k, j), ho, h))

# a round from a state of J: an admin move, a step, or a halt as HR says;
# out of memory only below its Budget
def asm.rnd(+x: Hp.Cx, +st: Cr.Cir.State, +s: A.AS, +j: {Asm.J(x, st, s) == True{} : Bool}) ->
  Lg.Tot(Mc.Mach.round(), st, Me.Budget(x, st, s), u => Asm.Rnd(x, A.AS.term(s), A.AS.w(s), u),
    k => st2 => Asm.HR(Hp.Cx.ds(x), A.AS.term(s), k, st2)):
  +ds = Hp.Cx.ds(x)
  +o = A.AM.move(ds, Mv.Vb(st), s)
  +iv = K.bool.and_l(R.Inv(x, st, s), A.AS.ok0(ds, s), j)
  +ok0 = K.bool.and_r(R.Inv(x, st, s), A.AS.ok0(ds, s), j)
  +ok = A.am.ok(ds, Mv.Vb(st), s, K.bool.and_i(A.AS.ok0(ds, s), Bool.or(Bool.not(Mv.Vb(st)), El.Eval.vals(ds, A.AS.focus(s), False{})), ok0,
    Mv.inv.vb(x, st, s, iv)))
  Lg.tot.wk(Mc.Mach.round(), st, Me.Budget(x, st, s), Me.Budget(x, st, s), Mv.Next(x, o), u => Asm.Rnd(x, A.AS.term(s), A.AS.w(s), u),
    Mv.Halt(o), k => st2 => Asm.HR(ds, A.AS.term(s), k, st2), LgP.lg.le_refl(Me.Budget(x, st, s)),
    u => h => asm.rnd.next(x, s, o, u, ok, h), k => st2 => h => asm.rnd.halt(ds, s, o, k, st2, ok, h), Mv.round.sim(x, st, s, iv))

# The loop gives what Eval gives
# ------------------------------

# HR gives HE
def asm.he.of(+ds: List<&2, Bk.Def>, +t: Bk.Term, -k: U32, -st2: Cr.Cir.State, h: Asm.HR(ds, t, k, st2)) -> Asm.HE(ds, t, k, st2):
  match h:
    case Inl{y}:
      (e0, r) = y
      (_, er) = r
      Inl{(e0, (0n, er))}
    case Inr{y}:
      (e2, _) = y
      Inr{e2}

# HE after a step gives HE before it
def asm.he.step(+ds: List<&2, Bk.Def>, +t: Bk.Term, +t2: Bk.Term, +es: {C.CStep(ds, t) == Some{t2} : Maybe<Bk.Term>}, -k: U32,
  -st2: Cr.Cir.State, h: Asm.HE(ds, t2, k, st2)) -> Asm.HE(ds, t, k, st2):
  match h:
    case Inl{y}:
      (e0, r) = y
      (+n, en) = r
      Inl{(e0, (1n+n, (%Equal.sym(Maybe<Bk.Term>, C.CStep(ds, t), Some{t2}, es) :
        {Pg.Program.result(ds, C.CSteps(n, ds, _)) == Some{List.reverse(&2, Word(8n), Lg.St.out(st2))} : Maybe<&2, List<&2, Word(8n)>>}; en)))}
    case Inr{e2}:
      Inr{e2}

# after a round that goes on, the loop from there, by ih
def asm.post.next(+p: Nat, +x: Hp.Cx, +s: A.AS, +u: Cr.Cir.State, rn: Asm.Rnd(x, A.AS.term(s), A.AS.w(s), u),
  ih: @s2: A.AS -> {Asm.J(x, u, s2) == True{} : Bool} ->
    Asm.Ps(Cr.Cir.exec(p, Asm.loop(), u), k => st2 => Asm.HE(Hp.Cx.ds(x), A.AS.term(s2), k, st2))) ->
  Asm.Ps(Cr.Cir.exec(p, Asm.loop(), u), k => st2 => Asm.HE(Hp.Cx.ds(x), A.AS.term(s), k, st2)):
  match rn:
    case Inl{ad}:
      (+s2, r1) = ad
      (+j2, r2) = r1
      (+eq, _) = r2
      %eq : Asm.Ps(Cr.Cir.exec(p, Asm.loop(), u), k => st2 => Asm.HE(Hp.Cx.ds(x), _, k, st2))
      ih(s2, j2)
    case Inr{sp}:
      (+s2, r1) = sp
      (+j2, +es) = r1
      asm.ps.wk(Cr.Cir.exec(p, Asm.loop(), u), k => st2 => Asm.HE(Hp.Cx.ds(x), A.AS.term(s2), k, st2),
        k => st2 => Asm.HE(Hp.Cx.ds(x), A.AS.term(s), k, st2), ih(s2, j2),
        k => st2 => h => asm.he.step(Hp.Cx.ds(x), A.AS.term(s), A.AS.term(s2), es, k, st2, h))

# the loop after a round with the outcome r
def asm.post.go(r: Cr.Cir.Out, +p: Nat, +x: Hp.Cx, +st: Cr.Cir.State, +s: A.AS,
  a: Or({r == Cr.Cir.Out.not_done{} : Cr.Cir.Out}, Lg.Ok(r, Lg.Lim(st), Me.Budget(x, st, s), u => Asm.Rnd(x, A.AS.term(s), A.AS.w(s), u),
    k => st2 => Asm.HR(Hp.Cx.ds(x), A.AS.term(s), k, st2))),
  ih: @u: Cr.Cir.State -> @s2: A.AS -> {Asm.J(x, u, s2) == True{} : Bool} ->
    Asm.Ps(Cr.Cir.exec(p, Asm.loop(), u), k => st2 => Asm.HE(Hp.Cx.ds(x), A.AS.term(s2), k, st2))) ->
  Asm.Ps(Cr.Cir.exec.then(r, t => Cr.Cir.exec(p, Asm.loop(), t)), k => st2 => Asm.HE(Hp.Cx.ds(x), A.AS.term(s), k, st2)):
  match r:
    case Cr.Cir.Out.next{+u}:
      match a:
        case Inl{e}:
          Empty.absurd(Asm.Ps(Cr.Cir.exec(p, Asm.loop(), u), k => st2 => Asm.HE(Hp.Cx.ds(x), A.AS.term(s), k, st2)),
            asm.nd(Cr.Cir.Out.next{u}, e, Unit{}))
        case Inr{rn}:
          asm.post.next(p, x, s, u, rn, s2 => j2 => ih(u, s2, j2))
    case Cr.Cir.Out.halt{+k, +st2}:
      match a:
        case Inl{e}:
          Empty.absurd(Asm.HE(Hp.Cx.ds(x), A.AS.term(s), k, st2), asm.nd(Cr.Cir.Out.halt{k, st2}, e, Unit{}))
        case Inr{hr}:
          asm.he.of(Hp.Cx.ds(x), A.AS.term(s), k, st2, hr)
    case Cr.Cir.Out.out_of_memory{}:
      Unit{}
    case Cr.Cir.Out.trap{}:
      match a:
        case Inl{e}:
          asm.nd(Cr.Cir.Out.trap{}, e, Unit{})
        case Inr{z}:
          z
    case Cr.Cir.Out.not_done{}:
      Unit{}

# the loop, from a state of J, halts only as HE says, at any fuel: by
# induction on the fuel
def asm.post(+f: Nat, +x: Hp.Cx, +st: Cr.Cir.State, +s: A.AS, +j: {Asm.J(x, st, s) == True{} : Bool}) ->
  Asm.Ps(Cr.Cir.exec(f, Asm.loop(), st), k => st2 => Asm.HE(Hp.Cx.ds(x), A.AS.term(s), k, st2)):
  match f:
    case 0n:
      Unit{}
    case 1n+p:
      asm.post.go(Cr.Cir.exec(p, Mc.Mach.round(), st), p, x, st, s,
        Lg.tot.any(Mc.Mach.round(), st, Me.Budget(x, st, s), u => Asm.Rnd(x, A.AS.term(s), A.AS.w(s), u),
          k => st2 => Asm.HR(Hp.Cx.ds(x), A.AS.term(s), k, st2), asm.rnd(x, st, s, j), p),
        u => s2 => j2 => asm.post(p, x, u, s2, j2))

# The loop reaches what Eval reaches
# ----------------------------------

# a round that goes on with the fuel f0, then the loop with n1, are the loop
# with 1 + f0 + n1
def asm.next.fin(+m: Bool, +o: List<&2, Word(8n)>, +f0: Nat, +n1: Nat, +st: Cr.Cir.State, +u: Cr.Cir.State,
  +er: {Cr.Cir.exec(f0, Mc.Mach.round(), st) == Cr.Cir.Out.next{u} : Cr.Cir.Out},
  +g1: Asm.Good(m, o, Cr.Cir.exec(n1, Asm.loop(), u))) -> Asm.Good(m, o, Cr.Cir.exec(1n+Nat.add(f0, n1), Asm.loop(), st)):
  +n = Nat.add(f0, n1)
  +d0 = Equal.cong(Cr.Cir.Out, Bool, x => Lg.Out.done(x), Cr.Cir.exec(f0, Mc.Mach.round(), st), Cr.Cir.Out.next{u}, er)
  +e1 = Equal.trans(Cr.Cir.Out, Cr.Cir.exec(n, Mc.Mach.round(), st), Cr.Cir.exec(f0, Mc.Mach.round(), st), Cr.Cir.Out.next{u},
    Lg.exec.more(f0, n1, Mc.Mach.round(), st, d0), er)
  +e2 = Equal.trans(Cr.Cir.Out, Cr.Cir.exec(n, Asm.loop(), u), Cr.Cir.exec(Nat.add(n1, f0), Asm.loop(), u), Cr.Cir.exec(n1, Asm.loop(), u),
    Equal.cong(Nat, Cr.Cir.Out, g => Cr.Cir.exec(g, Asm.loop(), u), n, Nat.add(n1, f0), LgP.lg.add_comm(f0, n1)),
    Lg.exec.more(n1, f0, Asm.loop(), u, asm.good.done(m, o, Cr.Cir.exec(n1, Asm.loop(), u), g1)))
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(n, Mc.Mach.round(), st), Cr.Cir.Out.next{u}, e1) :
    Asm.Good(m, o, Cr.Cir.exec.then(_, t => Cr.Cir.exec(n, Asm.loop(), t)))
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(n, Asm.loop(), u), Cr.Cir.exec(n1, Asm.loop(), u), e2) : Asm.Good(m, o, _)
  g1

# a round that halts or runs out of memory with the fuel f0 ends the loop the
# same with 1 + f0
def asm.out.fin(+m: Bool, -o: List<&2, Word(8n)>, +f0: Nat, -st: Cr.Cir.State, r: Cr.Cir.Out,
  er: {Cr.Cir.exec(f0, Mc.Mach.round(), st) == r : Cr.Cir.Out}, g: Asm.Good(m, o, r)) ->
  Asm.Good(m, o, Cr.Cir.exec(1n+f0, Asm.loop(), st)):
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f0, Mc.Mach.round(), st), r, er) :
    Asm.Good(m, o, Cr.Cir.exec.then(_, t => Cr.Cir.exec(f0, Asm.loop(), t)))
  asm.good.then(m, o, r, t => Cr.Cir.exec(f0, Asm.loop(), t), g)

# a round's halt: the term has no step
def asm.halt.cn(+ds: List<&2, Bk.Def>, +t: Bk.Term, -k: U32, -st2: Cr.Cir.State, h: Asm.HR(ds, t, k, st2)) ->
  {C.CStep(ds, t) == None{} : Maybe<Bk.Term>}:
  match h:
    case Inl{y}:
      (_, r) = y
      (cn, _) = r
      cn
    case Inr{y}:
      (_, r) = y
      (cn, _) = r
      cn

# a round that halts, from a term from which canonical steps reach the bytes
# o: the loop gives them
def asm.halt.good(kk: Nat, +m: Bool, +ds: List<&2, Bk.Def>, +t: Bk.Term, -k: U32, +st2: Cr.Cir.State, +o: List<&2, Word(8n)>,
  +e: {Pg.Program.result(ds, C.CSteps(kk, ds, Some{t})) == Some{o} : Maybe<&2, List<&2, Word(8n)>>},
  h: Asm.HR(ds, t, k, st2)) -> Asm.Good(m, o, Cr.Cir.Out.halt{k, st2}):
  match kk:
    case 0n:
      match h:
        case Inl{y}:
          (e0, r) = y
          (_, er) = r
          (e0, asm.mb.inj(List.reverse(&2, Word(8n), Lg.St.out(st2)), o,
            Equal.trans(Maybe<&2, List<&2, Word(8n)>>, Some{List.reverse(&2, Word(8n), Lg.St.out(st2))}, Pg.Program.result(ds, Some{t}), Some{o},
              Equal.sym(Maybe<&2, List<&2, Word(8n)>>, Pg.Program.result(ds, Some{t}), Some{List.reverse(&2, Word(8n), Lg.St.out(st2))}, er), e)))
        case Inr{y}:
          (_, r) = y
          (_, er) = r
          Empty.absurd(Asm.Good(m, o, Cr.Cir.Out.halt{k, st2}), asm.mb.ne(o,
            Equal.trans(Maybe<&2, List<&2, Word(8n)>>, None{}, Pg.Program.result(ds, Some{t}), Some{o},
              Equal.sym(Maybe<&2, List<&2, Word(8n)>>, Pg.Program.result(ds, Some{t}), None{}, er), e)))
    case 1n+(+n):
      +cn = asm.halt.cn(ds, t, k, st2, h)
      +e1 = {(%cn : {Pg.Program.result(ds, C.CSteps(n, ds, _)) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}; e) :
        {Pg.Program.result(ds, C.CSteps(n, ds, None{})) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}}
      +e2 = {(%asm.cs.none(n, ds) : {Pg.Program.result(ds, _) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}; e1) :
        {None{} == Some{o} : Maybe<&2, List<&2, Word(8n)>>}}
      Empty.absurd(Asm.Good(m, o, Cr.Cir.Out.halt{k, st2}), asm.mb.ne(o, e2))

# a step from a term from which canonical steps reach the bytes o at once:
# none, a value has no step
def asm.step0(+ds: List<&2, Bk.Def>, +t: Bk.Term, +u: Bk.Term, -o: List<&2, Word(8n)>,
  e: {Pg.Program.result(ds, Some{t}) == Some{o} : Maybe<&2, List<&2, Word(8n)>>},
  es: {C.CStep(ds, t) == Some{u} : Maybe<Bk.Term>}) -> Empty:
  +cn = asm.vals(El.Eval.vals(ds, t, False{}), ds, t, o, {==}, e)
  asm.tm.ne(u, Equal.trans(Maybe<Bk.Term>, None{}, C.CStep(ds, t), Some{u}, Equal.sym(Maybe<Bk.Term>, C.CStep(ds, t), None{}, cn), es))

# a fuel for the loop after a round that goes on gives one before it
def asm.fin.ex(+m: Bool, +o: List<&2, Word(8n)>, +f0: Nat, +st: Cr.Cir.State, +u: Cr.Cir.State,
  +er: {Cr.Cir.exec(f0, Mc.Mach.round(), st) == Cr.Cir.Out.next{u} : Cr.Cir.Out},
  g: &n:Nat -> Asm.Good(m, o, Cr.Cir.exec(n, Asm.loop(), u))) -> &n:Nat -> Asm.Good(m, o, Cr.Cir.exec(n, Asm.loop(), st)):
  match g:
    case Tuple{+n1, g1}:
      (1n+Nat.add(f0, n1), asm.next.fin(m, o, f0, n1, st, u, er, g1))

# the fuel of a Tot, and its outcome
def asm.tot.f(-s: Cr.Cir.Stmt, -st: Cr.Cir.State, -b: Nat, -Q: Cr.Cir.State -> Type, -H: U32 -> Cr.Cir.State -> Type,
  t: Lg.Tot(s, st, b, Q, H)) -> Nat:
  match t:
    case Tuple{f, _}:
      f

def asm.tot.ok(-s: Cr.Cir.Stmt, -st: Cr.Cir.State, -b: Nat, -Q: Cr.Cir.State -> Type, -H: U32 -> Cr.Cir.State -> Type,
  t: Lg.Tot(s, st, b, Q, H)) -> Lg.Ok(Cr.Cir.exec(asm.tot.f(s, st, b, Q, H, t), s, st), Lg.Lim(st), b, Q, H):
  match t:
    case Tuple{_, ok}:
      ok

# the loop after a round with the fuel f0 and the outcome r: ia after an
# admin move, ist after a step
def asm.done.r(r: Cr.Cir.Out, +m: Bool, +f0: Nat, +x: Hp.Cx, +st: Cr.Cir.State, +s: A.AS, +kk: Nat, +o: List<&2, Word(8n)>,
  +er: {Cr.Cir.exec(f0, Mc.Mach.round(), st) == r : Cr.Cir.Out},
  ok: Lg.Ok(r, Lg.Lim(st), Me.Budget(x, st, s), u => Asm.Rnd(x, A.AS.term(s), A.AS.w(s), u),
    k => st2 => Asm.HR(Hp.Cx.ds(x), A.AS.term(s), k, st2)),
  +e: {Pg.Program.result(Hp.Cx.ds(x), C.CSteps(kk, Hp.Cx.ds(x), Some{A.AS.term(s)})) == Some{o} : Maybe<&2, List<&2, Word(8n)>>},
  oom: {Nat.is_lt(Lg.Lim(st), Me.Budget(x, st, s)) == True{} : Bool} -> Asm.Oom(m),
  ia: @u: Cr.Cir.State -> @s2: A.AS -> {Cr.Cir.exec(f0, Mc.Mach.round(), st) == Cr.Cir.Out.next{u} : Cr.Cir.Out} ->
    {Asm.J(x, u, s2) == True{} : Bool} -> {A.AS.term(s2) == A.AS.term(s) : Bk.Term} -> {Nat.is_lt(A.AS.w(s2), A.AS.w(s)) == True{} : Bool} ->
    &n:Nat -> Asm.Good(m, o, Cr.Cir.exec(n, Asm.loop(), u)),
  ist: @u: Cr.Cir.State -> @s2: A.AS -> {Cr.Cir.exec(f0, Mc.Mach.round(), st) == Cr.Cir.Out.next{u} : Cr.Cir.Out} ->
    {Asm.J(x, u, s2) == True{} : Bool} -> {C.CStep(Hp.Cx.ds(x), A.AS.term(s)) == Some{A.AS.term(s2)} : Maybe<Bk.Term>} ->
    &n:Nat -> Asm.Good(m, o, Cr.Cir.exec(n, Asm.loop(), u))) ->
  &n:Nat -> Asm.Good(m, o, Cr.Cir.exec(n, Asm.loop(), st)):
  match r:
    case Cr.Cir.Out.next{+u}:
      match ok:
        case Inl{ad}:
          (+s2, r1) = ad
          (+j2, r2) = r1
          (+eq, lt) = r2
          asm.fin.ex(m, o, f0, st, u, er, ia(u, s2, er, j2, eq, lt))
        case Inr{sp}:
          (+s2, r1) = sp
          (+j2, es) = r1
          asm.fin.ex(m, o, f0, st, u, er, ist(u, s2, er, j2, es))
    case Cr.Cir.Out.halt{+k, +st2}:
      (1n+f0, asm.out.fin(m, o, f0, st, Cr.Cir.Out.halt{k, st2}, er,
        asm.halt.good(kk, m, Hp.Cx.ds(x), A.AS.term(s), k, st2, o, e, ok)))
    case Cr.Cir.Out.out_of_memory{}:
      (1n+f0, asm.out.fin(m, o, f0, st, Cr.Cir.Out.out_of_memory{}, er, oom(ok)))
    case Cr.Cir.Out.trap{}:
      Empty.absurd(&n:Nat -> Asm.Good(m, o, Cr.Cir.exec(n, Asm.loop(), st)), ok)
    case Cr.Cir.Out.not_done{}:
      Empty.absurd(&n:Nat -> Asm.Good(m, o, Cr.Cir.exec(n, Asm.loop(), st)), ok)

# when canonical steps reach the bytes o from the term of s within kk steps,
# the loop gives them or runs out of memory, with some fuel: by induction on
# kk, and on b, above the measure of the admin moves
def asm.done(kk: Nat, b: Nat, +x: Hp.Cx, +st: Cr.Cir.State, +s: A.AS, +o: List<&2, Word(8n)>,
  +hw: {Nat.is_lt(A.AS.w(s), b) == True{} : Bool},
  +e: {Pg.Program.result(Hp.Cx.ds(x), C.CSteps(kk, Hp.Cx.ds(x), Some{A.AS.term(s)})) == Some{o} : Maybe<&2, List<&2, Word(8n)>>},
  +j: {Asm.J(x, st, s) == True{} : Bool}) -> &n:Nat -> Asm.Good(False{}, o, Cr.Cir.exec(n, Asm.loop(), st)):
  match kk:
    case 0n:
      match b:
        case 0n:
          Empty.absurd(&n:Nat -> Asm.Good(False{}, o, Cr.Cir.exec(n, Asm.loop(), st)), asm.lt0(A.AS.w(s), hw))
        case 1n+(+c):
          +ds = Hp.Cx.ds(x)
          +B = Me.Budget(x, st, s)
          +f0 = asm.tot.f(Mc.Mach.round(), st, B, u => Asm.Rnd(x, A.AS.term(s), A.AS.w(s), u), k => st2 => Asm.HR(ds, A.AS.term(s), k, st2), asm.rnd(x, st, s, j))
          ok0 = asm.tot.ok(Mc.Mach.round(), st, B, u => Asm.Rnd(x, A.AS.term(s), A.AS.w(s), u), k => st2 => Asm.HR(ds, A.AS.term(s), k, st2), asm.rnd(x, st, s, j))
          asm.done.r(Cr.Cir.exec(f0, Mc.Mach.round(), st), False{}, f0, x, st, s, 0n, o, {==}, ok0, e, z => Unit{},
            +u => +s2 => er => +j2 => +eq => lt => asm.done(0n, c, x, u, s2, o, asm.lt.step(A.AS.w(s2), A.AS.w(s), c, lt, hw),
              (%Equal.sym(Bk.Term, A.AS.term(s2), A.AS.term(s), eq) :
                {Pg.Program.result(ds, C.CSteps(0n, ds, Some{_})) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}; e), j2),
            +u => +s2 => er => +j2 => +es => Empty.absurd(&n:Nat -> Asm.Good(False{}, o, Cr.Cir.exec(n, Asm.loop(), u)),
              asm.step0(ds, A.AS.term(s), A.AS.term(s2), o, e, es)))
    case 1n+(+q):
      match b:
        case 0n:
          Empty.absurd(&n:Nat -> Asm.Good(False{}, o, Cr.Cir.exec(n, Asm.loop(), st)), asm.lt0(A.AS.w(s), hw))
        case 1n+(+c):
          +ds = Hp.Cx.ds(x)
          +B = Me.Budget(x, st, s)
          +f0 = asm.tot.f(Mc.Mach.round(), st, B, u => Asm.Rnd(x, A.AS.term(s), A.AS.w(s), u), k => st2 => Asm.HR(ds, A.AS.term(s), k, st2), asm.rnd(x, st, s, j))
          ok0 = asm.tot.ok(Mc.Mach.round(), st, B, u => Asm.Rnd(x, A.AS.term(s), A.AS.w(s), u), k => st2 => Asm.HR(ds, A.AS.term(s), k, st2), asm.rnd(x, st, s, j))
          asm.done.r(Cr.Cir.exec(f0, Mc.Mach.round(), st), False{}, f0, x, st, s, 1n+q, o, {==}, ok0, e, z => Unit{},
            +u => +s2 => er => +j2 => +eq => lt => asm.done(1n+q, c, x, u, s2, o, asm.lt.step(A.AS.w(s2), A.AS.w(s), c, lt, hw),
              (%Equal.sym(Bk.Term, A.AS.term(s2), A.AS.term(s), eq) :
                {Pg.Program.result(ds, C.CSteps(1n+q, ds, Some{_})) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}; e), j2),
            +u => +s2 => er => +j2 => +es => asm.done(q, 1n+A.AS.w(s2), x, u, s2, o, asm.lt.succ(A.AS.w(s2)),
              (%es : {Pg.Program.result(ds, C.CSteps(q, ds, _)) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}; e), j2))
