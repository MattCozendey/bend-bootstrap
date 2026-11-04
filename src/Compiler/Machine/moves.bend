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

# The loop within the memory F
# ----------------------------

# the run's context: Cir.result's start of a book that Book.read reads
def Asm.x0(+ds: List<&2, Bk.Def>, +k: U32, +first: U32) -> Hp.Cx:
  I.Cx.of(ds, k, first)

def Asm.St0(+ds: List<&2, Bk.Def>, +first: U32, +k: U32, +pg: U32, +lim: U32, +i: List<&2, Word(8n)>) -> Cr.Cir.State:
  I.St0(Mc.Mach.regs(), Mc.Img.cells(ds), first, k, pg, lim, i)

# the facts of the run that the memory loop carries: Start, at most 6144
# cache cells (c), and the start's limit has F bytes
def Asm.Mf(+p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +m: U32, +k: U32, +len: U32, +pg: U32, +lim: U32,
  +first: U32, +n: Nat, +c: Nat) -> Bool:
  I.Start(Mc.Img.cells(ds), i, m, k, len, pg, lim, first) && Nat.is_le(c, 6144n) &&
    Nat.is_le(Pg.Program.need(p, i, n), Lg.Lim(Asm.St0(ds, first, k, pg, lim, i)))

# what the memory loop knows of the state st of s after jj of the run's n
# steps: its term is the jj-th; its limit is the start's; at most c cache
# cells; next - first at most Peak
def Asm.Ms(+p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +k: U32, +pg: U32, +lim: U32, +first: U32,
  +n: Nat, +c: Nat, +jj: Nat, +st: Cr.Cir.State, +s: A.AS) -> Bool:
  C.Tm.is(C.CSteps(jj, ds, Some{Pg.Program.start(i)}), A.AS.term(s)) && Nat.is_eq(Lg.Lim(st), Lg.Lim(Asm.St0(ds, first, k, pg, lim, i))) &&
    Nat.is_le(Me.Stat(st), c) && Nat.is_le(Me.Mem.cells(st), Me.Peak(ds, c, Pg.Program.largest(p, i, n)))

# a round of the memory loop does not run out of memory: its Budget is at most
# F, which the limit has
def asm.mem.oom(+p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +m: U32, +k: U32, +len: U32, +pg: U32,
  +lim: U32, +first: U32, +n: Nat, +o: List<&2, Word(8n)>, +c: Nat, +jj: Nat, +kk: Nat, +st: Cr.Cir.State, +s: A.AS,
  +rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  +he: {Pg.Program.result(ds, El.Eval.steps(n, ds, Pg.Program.start(i))) == Some{o} : Maybe<&2, List<&2, Word(8n)>>},
  +hf: {Asm.Mf(p, ds, i, m, k, len, pg, lim, first, n, c) == True{} : Bool},
  +hjk: {Nat.add(jj, kk) == n : Nat},
  +hs: {Asm.Ms(p, ds, i, k, pg, lim, first, n, c, jj, st, s) == True{} : Bool},
  +iv: {R.Inv(Asm.x0(ds, k, first), st, s) == True{} : Bool},
  +z: {Nat.is_lt(Lg.Lim(st), Me.Budget(Asm.x0(ds, k, first), st, s)) == True{} : Bool}) -> Empty:
  +S = Pg.Program.largest(p, i, n)
  +L0 = Lg.Lim(Asm.St0(ds, first, k, pg, lim, i))
  +sa = I.Start(Mc.Img.cells(ds), i, m, k, len, pg, lim, first)
  +nd = Pg.Program.need(p, i, n)
  +ht = C.Tm.is(C.CSteps(jj, ds, Some{Pg.Program.start(i)}), A.AS.term(s))
  +hf1 = K.bool.and_l(Bool.and(sa, Nat.is_le(c, 6144n)), Nat.is_le(nd, L0), hf)
  +hs1 = K.bool.and_l(Bool.and(Bool.and(ht, Nat.is_eq(Lg.Lim(st), L0)), Nat.is_le(Me.Stat(st), c)),
    Nat.is_le(Me.Mem.cells(st), Me.Peak(ds, c, S)), hs)
  +hs2 = K.bool.and_l(Bool.and(ht, Nat.is_eq(Lg.Lim(st), L0)), Nat.is_le(Me.Stat(st), c), hs1)
  +hj = {(%hjk : {Nat.is_le(jj, _) == True{} : Bool}; asm.le.add(jj, kk)) : {Nat.is_le(jj, n) == True{} : Bool}}
  +hb = Me.budget.need(p, ds, i, m, k, len, pg, lim, first, n, jj, o, c, st, s, rd, K.bool.and_l(sa, Nat.is_le(c, 6144n), hf1), he, hj,
    K.bool.and_l(ht, Nat.is_eq(Lg.Lim(st), L0), hs2), iv, K.bool.and_r(sa, Nat.is_le(c, 6144n), hf1),
    K.bool.and_r(Bool.and(ht, Nat.is_eq(Lg.Lim(st), L0)), Nat.is_le(Me.Stat(st), c), hs1),
    K.bool.and_r(Bool.and(Bool.and(ht, Nat.is_eq(Lg.Lim(st), L0)), Nat.is_le(Me.Stat(st), c)),
      Nat.is_le(Me.Mem.cells(st), Me.Peak(ds, c, S)), hs))
  +el = K.nat.is_eq_ok(Lg.Lim(st), L0, K.bool.and_r(ht, Nat.is_eq(Lg.Lim(st), L0), hs2))
  +hl = {(%Equal.sym(Nat, Lg.Lim(st), L0, el) : {Nat.is_le(nd, _) == True{} : Bool};
    K.bool.and_r(Bool.and(sa, Nat.is_le(c, 6144n)), Nat.is_le(nd, L0), hf)) : {Nat.is_le(nd, Lg.Lim(st)) == True{} : Bool}}
  asm.lt.abs(Lg.Lim(st), Me.Budget(Asm.x0(ds, k, first), st, s), z,
    asm.le.trans(Me.Budget(Asm.x0(ds, k, first), st, s), nd, Lg.Lim(st), hb, hl))

# the memory facts after a round that goes on from st to u: the limit is the
# same (frame.fixed), no new cache cell and next - first within Peak
# (round.mem, need.peak)
def asm.mem.next(+p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +k: U32, +pg: U32, +lim: U32, +first: U32,
  +n: Nat, +o: List<&2, Word(8n)>, +c: Nat, +jj: Nat, +kk: Nat, +f0: Nat, +st: Cr.Cir.State, +s: A.AS, +u: Cr.Cir.State,
  +jn: Nat, +s2: A.AS,
  +rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  +he: {Pg.Program.result(ds, El.Eval.steps(n, ds, Pg.Program.start(i))) == Some{o} : Maybe<&2, List<&2, Word(8n)>>},
  +hjk: {Nat.add(jj, kk) == n : Nat},
  +hs: {Asm.Ms(p, ds, i, k, pg, lim, first, n, c, jj, st, s) == True{} : Bool},
  +iv: {R.Inv(Asm.x0(ds, k, first), st, s) == True{} : Bool},
  +er: {Cr.Cir.exec(f0, Mc.Mach.round(), st) == Cr.Cir.Out.next{u} : Cr.Cir.Out},
  +ht2: {C.Tm.is(C.CSteps(jn, ds, Some{Pg.Program.start(i)}), A.AS.term(s2)) == True{} : Bool}) ->
  {Asm.Ms(p, ds, i, k, pg, lim, first, n, c, jn, u, s2) == True{} : Bool}:
  +S = Pg.Program.largest(p, i, n)
  +L0 = Lg.Lim(Asm.St0(ds, first, k, pg, lim, i))
  +ht = C.Tm.is(C.CSteps(jj, ds, Some{Pg.Program.start(i)}), A.AS.term(s))
  +hs1 = K.bool.and_l(Bool.and(Bool.and(ht, Nat.is_eq(Lg.Lim(st), L0)), Nat.is_le(Me.Stat(st), c)),
    Nat.is_le(Me.Mem.cells(st), Me.Peak(ds, c, S)), hs)
  +hs2 = K.bool.and_l(Bool.and(ht, Nat.is_eq(Lg.Lim(st), L0)), Nat.is_le(Me.Stat(st), c), hs1)
  +hst = K.bool.and_r(Bool.and(ht, Nat.is_eq(Lg.Lim(st), L0)), Nat.is_le(Me.Stat(st), c), hs1)
  +hm = K.bool.and_r(Bool.and(Bool.and(ht, Nat.is_eq(Lg.Lim(st), L0)), Nat.is_le(Me.Stat(st), c)),
    Nat.is_le(Me.Mem.cells(st), Me.Peak(ds, c, S)), hs)
  +hj = {(%hjk : {Nat.is_le(jj, _) == True{} : Bool}; asm.le.add(jj, kk)) : {Nat.is_le(jj, n) == True{} : Bool}}
  +rm = Me.round.mem(Asm.x0(ds, k, first), st, s, iv, f0, u, er)
  +nm = Nat.max(Me.Mem.cells(st), Me.Need(ds, st, s))
  +np = Me.need.peak(p, ds, i, n, jj, o, c, st, s, rd, he, hj, K.bool.and_l(ht, Nat.is_eq(Lg.Lim(st), L0), hs2), hst)
  +el = K.nat.is_eq_ok(Lg.Lim(st), L0, K.bool.and_r(ht, Nat.is_eq(Lg.Lim(st), L0), hs2))
  +el2 = Equal.trans(Nat, Lg.Lim(u), Lg.Lim(st), L0, LgP.lg.lim.eq(u, st, Lg.frame.fixed(f0, Mc.Mach.round(), st, u, er)), el)
  K.bool.and_i(Bool.and(Bool.and(C.Tm.is(C.CSteps(jn, ds, Some{Pg.Program.start(i)}), A.AS.term(s2)), Nat.is_eq(Lg.Lim(u), L0)),
    Nat.is_le(Me.Stat(u), c)), Nat.is_le(Me.Mem.cells(u), Me.Peak(ds, c, S)),
    K.bool.and_i(Bool.and(C.Tm.is(C.CSteps(jn, ds, Some{Pg.Program.start(i)}), A.AS.term(s2)), Nat.is_eq(Lg.Lim(u), L0)),
      Nat.is_le(Me.Stat(u), c),
      K.bool.and_i(C.Tm.is(C.CSteps(jn, ds, Some{Pg.Program.start(i)}), A.AS.term(s2)), Nat.is_eq(Lg.Lim(u), L0), ht2,
        (%el2 : {Nat.is_eq(Lg.Lim(u), _) == True{} : Bool}; K.nat.is_eq_refl(Lg.Lim(u)))),
      asm.le.trans(Me.Stat(u), Me.Stat(st), c, K.bool.and_l(Nat.is_le(Me.Stat(u), Me.Stat(st)), Nat.is_le(Me.Mem.cells(u), nm), rm), hst)),
    asm.le.trans(Me.Mem.cells(u), nm, Me.Peak(ds, c, S), K.bool.and_r(Nat.is_le(Me.Stat(u), Me.Stat(st)), Nat.is_le(Me.Mem.cells(u), nm), rm),
      asm.max.le(Me.Mem.cells(st), Me.Need(ds, st, s), Me.Peak(ds, c, S), hm, np)))

# the term of the memory loop's state: the jj-th
def asm.ms.ht(+p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +k: U32, +pg: U32, +lim: U32, +first: U32,
  +n: Nat, +c: Nat, +jj: Nat, +st: Cr.Cir.State, +s: A.AS,
  +hs: {Asm.Ms(p, ds, i, k, pg, lim, first, n, c, jj, st, s) == True{} : Bool}) ->
  {C.Tm.is(C.CSteps(jj, ds, Some{Pg.Program.start(i)}), A.AS.term(s)) == True{} : Bool}:
  +S = Pg.Program.largest(p, i, n)
  +L0 = Lg.Lim(Asm.St0(ds, first, k, pg, lim, i))
  +ht = C.Tm.is(C.CSteps(jj, ds, Some{Pg.Program.start(i)}), A.AS.term(s))
  +hs1 = K.bool.and_l(Bool.and(Bool.and(ht, Nat.is_eq(Lg.Lim(st), L0)), Nat.is_le(Me.Stat(st), c)),
    Nat.is_le(Me.Mem.cells(st), Me.Peak(ds, c, S)), hs)
  +hs2 = K.bool.and_l(Bool.and(ht, Nat.is_eq(Lg.Lim(st), L0)), Nat.is_le(Me.Stat(st), c), hs1)
  K.bool.and_l(ht, Nat.is_eq(Lg.Lim(st), L0), hs2)

# after an admin move, the same term
def asm.mem.adm(+ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +jj: Nat, +s: A.AS, +s2: A.AS,
  +eq: {A.AS.term(s2) == A.AS.term(s) : Bk.Term},
  +ht: {C.Tm.is(C.CSteps(jj, ds, Some{Pg.Program.start(i)}), A.AS.term(s)) == True{} : Bool}) ->
  {C.Tm.is(C.CSteps(jj, ds, Some{Pg.Program.start(i)}), A.AS.term(s2)) == True{} : Bool}:
  (%Equal.sym(Bk.Term, A.AS.term(s2), A.AS.term(s), eq) : {C.Tm.is(C.CSteps(jj, ds, Some{Pg.Program.start(i)}), _) == True{} : Bool}; ht)

# after a step, the next term of the run
def asm.mem.stp(+ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +jj: Nat, +s: A.AS, +s2: A.AS,
  +es: {C.CStep(ds, A.AS.term(s)) == Some{A.AS.term(s2)} : Maybe<Bk.Term>},
  +ht: {C.Tm.is(C.CSteps(jj, ds, Some{Pg.Program.start(i)}), A.AS.term(s)) == True{} : Bool}) ->
  {C.Tm.is(C.CSteps(1n+jj, ds, Some{Pg.Program.start(i)}), A.AS.term(s2)) == True{} : Bool}:
  +en = asm.cs.snoc(jj, ds, Some{Pg.Program.start(i)}, A.AS.term(s), A.AS.term(s2),
    asm.tm.is(C.CSteps(jj, ds, Some{Pg.Program.start(i)}), A.AS.term(s), ht), es)
  (%Equal.sym(Maybe<Bk.Term>, C.CSteps(1n+jj, ds, Some{Pg.Program.start(i)}), Some{A.AS.term(s2)}, en) :
    {C.Tm.is(_, A.AS.term(s2)) == True{} : Bool}; C.term.is_eq_refl(A.AS.term(s2)))

# the loop within the memory F gives the bytes o: as asm.done, with no out of
# memory
def asm.mem(kk: Nat, b: Nat, +p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +m: U32, +k: U32, +len: U32,
  +pg: U32, +lim: U32, +first: U32, +n: Nat, +o: List<&2, Word(8n)>, +c: Nat, +jj: Nat, +st: Cr.Cir.State, +s: A.AS,
  +rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  +he: {Pg.Program.result(ds, El.Eval.steps(n, ds, Pg.Program.start(i))) == Some{o} : Maybe<&2, List<&2, Word(8n)>>},
  +hf: {Asm.Mf(p, ds, i, m, k, len, pg, lim, first, n, c) == True{} : Bool},
  +hw: {Nat.is_lt(A.AS.w(s), b) == True{} : Bool},
  +e: {Pg.Program.result(ds, C.CSteps(kk, ds, Some{A.AS.term(s)})) == Some{o} : Maybe<&2, List<&2, Word(8n)>>},
  +hjk: {Nat.add(jj, kk) == n : Nat},
  +hs: {Asm.Ms(p, ds, i, k, pg, lim, first, n, c, jj, st, s) == True{} : Bool},
  +j: {Asm.J(Asm.x0(ds, k, first), st, s) == True{} : Bool}) -> &r:Nat -> Asm.Good(True{}, o, Cr.Cir.exec(r, Asm.loop(), st)):
  match kk:
    case 0n:
      match b:
        case 0n:
          Empty.absurd(&r:Nat -> Asm.Good(True{}, o, Cr.Cir.exec(r, Asm.loop(), st)), asm.lt0(A.AS.w(s), hw))
        case 1n+(+c2):
          +x = Asm.x0(ds, k, first)
          +B = Me.Budget(x, st, s)
          +iv = K.bool.and_l(R.Inv(x, st, s), A.AS.ok0(ds, s), j)
          +ht = asm.ms.ht(p, ds, i, k, pg, lim, first, n, c, jj, st, s, hs)
          +f0 = asm.tot.f(Mc.Mach.round(), st, B, u => Asm.Rnd(x, A.AS.term(s), A.AS.w(s), u),
            q => st2 => Asm.HR(ds, A.AS.term(s), q, st2), asm.rnd(x, st, s, j))
          ok0 = asm.tot.ok(Mc.Mach.round(), st, B, u => Asm.Rnd(x, A.AS.term(s), A.AS.w(s), u),
            q => st2 => Asm.HR(ds, A.AS.term(s), q, st2), asm.rnd(x, st, s, j))
          asm.done.r(Cr.Cir.exec(f0, Mc.Mach.round(), st), True{}, f0, x, st, s, 0n, o, {==}, ok0, e,
            z => asm.mem.oom(p, ds, i, m, k, len, pg, lim, first, n, o, c, jj, 0n, st, s, rd, he, hf, hjk, hs, iv, z),
            +u => +s2 => +er => +j2 => +eq => lt =>
              asm.mem(0n, c2, p, ds, i, m, k, len, pg, lim, first, n, o, c, jj, u, s2, rd, he, hf,
                asm.lt.step(A.AS.w(s2), A.AS.w(s), c2, lt, hw),
                (%Equal.sym(Bk.Term, A.AS.term(s2), A.AS.term(s), eq) :
                  {Pg.Program.result(ds, C.CSteps(0n, ds, Some{_})) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}; e), hjk,
                asm.mem.next(p, ds, i, k, pg, lim, first, n, o, c, jj, 0n, f0, st, s, u, jj, s2, rd, he, hjk, hs, iv, er,
                  asm.mem.adm(ds, i, jj, s, s2, eq, ht)), j2),
            +u => +s2 => er => +j2 => +es => Empty.absurd(&r:Nat -> Asm.Good(True{}, o, Cr.Cir.exec(r, Asm.loop(), u)),
              asm.step0(ds, A.AS.term(s), A.AS.term(s2), o, e, es)))
    case 1n+(+q):
      match b:
        case 0n:
          Empty.absurd(&r:Nat -> Asm.Good(True{}, o, Cr.Cir.exec(r, Asm.loop(), st)), asm.lt0(A.AS.w(s), hw))
        case 1n+(+c2):
          +x = Asm.x0(ds, k, first)
          +B = Me.Budget(x, st, s)
          +iv = K.bool.and_l(R.Inv(x, st, s), A.AS.ok0(ds, s), j)
          +ht = asm.ms.ht(p, ds, i, k, pg, lim, first, n, c, jj, st, s, hs)
          +f0 = asm.tot.f(Mc.Mach.round(), st, B, u => Asm.Rnd(x, A.AS.term(s), A.AS.w(s), u),
            q2 => st2 => Asm.HR(ds, A.AS.term(s), q2, st2), asm.rnd(x, st, s, j))
          ok0 = asm.tot.ok(Mc.Mach.round(), st, B, u => Asm.Rnd(x, A.AS.term(s), A.AS.w(s), u),
            q2 => st2 => Asm.HR(ds, A.AS.term(s), q2, st2), asm.rnd(x, st, s, j))
          +hjk2 = Equal.trans(Nat, 1n+Nat.add(jj, q), Nat.add(jj, 1n+q), n, Equal.sym(Nat, Nat.add(jj, 1n+q), 1n+Nat.add(jj, q),
            N.add_succ_r(jj, q)), hjk)
          asm.done.r(Cr.Cir.exec(f0, Mc.Mach.round(), st), True{}, f0, x, st, s, 1n+q, o, {==}, ok0, e,
            z => asm.mem.oom(p, ds, i, m, k, len, pg, lim, first, n, o, c, jj, 1n+q, st, s, rd, he, hf, hjk, hs, iv, z),
            +u => +s2 => +er => +j2 => +eq => lt =>
              asm.mem(1n+q, c2, p, ds, i, m, k, len, pg, lim, first, n, o, c, jj, u, s2, rd, he, hf,
                asm.lt.step(A.AS.w(s2), A.AS.w(s), c2, lt, hw),
                (%Equal.sym(Bk.Term, A.AS.term(s2), A.AS.term(s), eq) :
                  {Pg.Program.result(ds, C.CSteps(1n+q, ds, Some{_})) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}; e), hjk,
                asm.mem.next(p, ds, i, k, pg, lim, first, n, o, c, jj, 1n+q, f0, st, s, u, jj, s2, rd, he, hjk, hs, iv, er,
                  asm.mem.adm(ds, i, jj, s, s2, eq, ht)), j2),
            +u => +s2 => +er => +j2 => +es =>
              asm.mem(q, 1n+A.AS.w(s2), p, ds, i, m, k, len, pg, lim, first, n, o, c, 1n+jj, u, s2, rd, he, hf, asm.lt.succ(A.AS.w(s2)),
                (%es : {Pg.Program.result(ds, C.CSteps(q, ds, _)) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}; e), hjk2,
                asm.mem.next(p, ds, i, k, pg, lim, first, n, o, c, jj, 1n+q, f0, st, s, u, 1n+jj, s2, rd, he, hjk, hs, iv, er,
                  asm.mem.stp(ds, i, jj, s, s2, es, ht)), j2))

# Cir.result's start
# ------------------

# Cir.result's values make Start hold
def asm.start(+cells: List<&2, Cr.Cir.Cell>, +i: List<&2, Word(8n)>, +m: U32, +k: U32, +len: U32, +p: U32, +lim: U32,
  +ek: {k == Cr.Wasm.encode.len(Cr.Cir.Cell, cells) : U32},
  +em: {U32.is_le(Cr.Cir.pages(Cr.Cir.input.at(k)), m) == True{} : Bool},
  +elim: {lim == Wa.Wasm.min(m, 65536) : U32},
  +el: {Wa.Wasm.length32(i) == Some{len} : Maybe<&2, U32>},
  +er: {Cr.Cir.alloc.pages(k, len, Cr.Cir.pages(Cr.Cir.input.at(k)), lim) == Some{p} : Maybe<&2, U32>}) ->
  {I.Start(cells, i, m, k, len, p, lim, Cr.Cir.first(k, U32.add(Cr.Cir.input.at(k), len))) == True{} : Bool}:
  +c1 = U32.is_eq(k, Cr.Wasm.encode.len(Cr.Cir.Cell, cells))
  +c2 = U32.is_le(Cr.Cir.pages(Cr.Cir.input.at(k)), m)
  +c3 = U32.is_eq(lim, Wa.Wasm.min(m, 65536))
  +c4 = I.Mb.is(Wa.Wasm.length32(i), len)
  +c5 = I.Mb.is(Cr.Cir.alloc.pages(k, len, Cr.Cir.pages(Cr.Cir.input.at(k)), lim), p)
  +h1 = {(%ek : {U32.is_eq(k, _) == True{} : Bool}; SB.U32.is_eq.refl(k)) : {c1 == True{} : Bool}}
  +h3 = {(%elim : {U32.is_eq(lim, _) == True{} : Bool}; SB.U32.is_eq.refl(lim)) : {c3 == True{} : Bool}}
  +h4 = {(%Equal.sym(Maybe<&2, U32>, Wa.Wasm.length32(i), Some{len}, el) : {I.Mb.is(_, len) == True{} : Bool}; SB.U32.is_eq.refl(len)) : {c4 == True{} : Bool}}
  +h5 = {(%Equal.sym(Maybe<&2, U32>, Cr.Cir.alloc.pages(k, len, Cr.Cir.pages(Cr.Cir.input.at(k)), lim), Some{p}, er) :
    {I.Mb.is(_, p) == True{} : Bool}; SB.U32.is_eq.refl(p)) : {c5 == True{} : Bool}}
  K.bool.and_i(Bool.and(Bool.and(Bool.and(Bool.and(c1, c2), c3), c4), c5),
    U32.is_eq(Cr.Cir.first(k, U32.add(Cr.Cir.input.at(k), len)), Cr.Cir.first(k, U32.add(Cr.Cir.input.at(k), len))),
    K.bool.and_i(Bool.and(Bool.and(Bool.and(c1, c2), c3), c4), c5,
      K.bool.and_i(Bool.and(Bool.and(c1, c2), c3), c4, K.bool.and_i(Bool.and(c1, c2), c3, K.bool.and_i(c1, c2, h1, em), h3), h4), h5),
    SB.U32.is_eq.refl(Cr.Cir.first(k, U32.add(Cr.Cir.input.at(k), len))))

def asm.res.alloced(r: Maybe<&2, U32>, fuel: Nat, prog: Cr.Cir.Stmt, +regs: Nat, +cells: List<&2, Cr.Cir.Cell>, +k: U32,
  +len: U32, +lim: U32, +i: List<&2, Word(8n)>, +m: U32, -P: Wa.Wasm.Outcome -> Type, po: P(Wa.Wasm.Outcome.out_of_memory{}),
  ek: {k == Cr.Wasm.encode.len(Cr.Cir.Cell, cells) : U32},
  em: {U32.is_le(Cr.Cir.pages(Cr.Cir.input.at(k)), m) == True{} : Bool},
  elim: {lim == Wa.Wasm.min(m, 65536) : U32},
  el: {Wa.Wasm.length32(i) == Some{len} : Maybe<&2, U32>},
  er: {Cr.Cir.alloc.pages(k, len, Cr.Cir.pages(Cr.Cir.input.at(k)), lim) == r : Maybe<&2, U32>},
  g: @k2: U32 -> @len2: U32 -> @p2: U32 -> @lim2: U32 -> @first2: U32 -> {I.Start(cells, i, m, k2, len2, p2, lim2, first2) == True{} : Bool} ->
    P(Cr.Cir.ended(Cr.Cir.exec(fuel, prog, I.St0(regs, cells, first2, k2, p2, lim2, i))))) ->
  P(Cr.Cir.result.alloced(r, fuel, prog, regs, cells, k, U32.add(Cr.Cir.input.at(k), len), lim, i)):
  match r:
    case None{}:
      po
    case Some{+p}:
      g(k, len, p, lim, Cr.Cir.first(k, U32.add(Cr.Cir.input.at(k), len)), asm.start(cells, i, m, k, len, p, lim, ek, em, elim, el, er))

def asm.res.sized(nl: Maybe<&2, U32>, fuel: Nat, prog: Cr.Cir.Stmt, +regs: Nat, +cells: List<&2, Cr.Cir.Cell>, +k: U32,
  +lim: U32, +i: List<&2, Word(8n)>, +m: U32, -P: Wa.Wasm.Outcome -> Type, po: P(Wa.Wasm.Outcome.out_of_memory{}),
  ek: {k == Cr.Wasm.encode.len(Cr.Cir.Cell, cells) : U32},
  em: {U32.is_le(Cr.Cir.pages(Cr.Cir.input.at(k)), m) == True{} : Bool},
  elim: {lim == Wa.Wasm.min(m, 65536) : U32},
  el: {Wa.Wasm.length32(i) == nl : Maybe<&2, U32>},
  g: @k2: U32 -> @len2: U32 -> @p2: U32 -> @lim2: U32 -> @first2: U32 -> {I.Start(cells, i, m, k2, len2, p2, lim2, first2) == True{} : Bool} ->
    P(Cr.Cir.ended(Cr.Cir.exec(fuel, prog, I.St0(regs, cells, first2, k2, p2, lim2, i))))) ->
  P(Cr.Cir.result.sized(nl, fuel, prog, regs, cells, k, Cr.Cir.pages(Cr.Cir.input.at(k)), lim, i)):
  match nl:
    case None{}:
      po
    case Some{+len}:
      asm.res.alloced(Cr.Cir.alloc.pages(k, len, Cr.Cir.pages(Cr.Cir.input.at(k)), lim), fuel, prog, regs, cells, k, len, lim, i, m,
        P, po, ek, em, elim, el, {==}, g)

def asm.res.memory(ok: Bool, fuel: Nat, prog: Cr.Cir.Stmt, +regs: Nat, +cells: List<&2, Cr.Cir.Cell>, +k: U32,
  +lim: U32, +i: List<&2, Word(8n)>, +m: U32, -P: Wa.Wasm.Outcome -> Type, po: P(Wa.Wasm.Outcome.out_of_memory{}),
  ek: {k == Cr.Wasm.encode.len(Cr.Cir.Cell, cells) : U32},
  em: {U32.is_le(Cr.Cir.pages(Cr.Cir.input.at(k)), m) == ok : Bool},
  elim: {lim == Wa.Wasm.min(m, 65536) : U32},
  g: @k2: U32 -> @len2: U32 -> @p2: U32 -> @lim2: U32 -> @first2: U32 -> {I.Start(cells, i, m, k2, len2, p2, lim2, first2) == True{} : Bool} ->
    P(Cr.Cir.ended(Cr.Cir.exec(fuel, prog, I.St0(regs, cells, first2, k2, p2, lim2, i))))) ->
  P(Cr.Cir.result.memory(ok, fuel, prog, regs, cells, k, Cr.Cir.pages(Cr.Cir.input.at(k)), lim, i)):
  match ok:
    case False{}:
      po
    case True{}:
      asm.res.sized(Wa.Wasm.length32(i), fuel, prog, regs, cells, k, lim, i, m, P, po, ek, em, elim, {==}, g)

# what holds of every run from the start, and of out of memory, holds of
# Cir.result
def asm.res.on(fuel: Nat, prog: Cr.Cir.Stmt, +regs: Nat, +cells: List<&2, Cr.Cir.Cell>, +i: List<&2, Word(8n)>, +m: U32,
  -P: Wa.Wasm.Outcome -> Type, po: P(Wa.Wasm.Outcome.out_of_memory{}),
  g: @k2: U32 -> @len2: U32 -> @p2: U32 -> @lim2: U32 -> @first2: U32 -> {I.Start(cells, i, m, k2, len2, p2, lim2, first2) == True{} : Bool} ->
    P(Cr.Cir.ended(Cr.Cir.exec(fuel, prog, I.St0(regs, cells, first2, k2, p2, lim2, i))))) ->
  P(Cr.Cir.result(fuel, prog, regs, cells, i, m)):
  asm.res.memory(U32.is_le(Cr.Cir.pages(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), m), fuel, prog, regs, cells,
    Cr.Wasm.encode.len(Cr.Cir.Cell, cells), Wa.Wasm.min(m, 65536), i, m, P, po, {==}, {==}, {==}, g)

def asm.rex.alloced(r: Maybe<&2, U32>, prog: Cr.Cir.Stmt, +regs: Nat, +cells: List<&2, Cr.Cir.Cell>, +k: U32,
  +len: U32, +lim: U32, +i: List<&2, Word(8n)>, +m: U32, -P: Wa.Wasm.Outcome -> Type, po: P(Wa.Wasm.Outcome.out_of_memory{}),
  ek: {k == Cr.Wasm.encode.len(Cr.Cir.Cell, cells) : U32},
  em: {U32.is_le(Cr.Cir.pages(Cr.Cir.input.at(k)), m) == True{} : Bool},
  elim: {lim == Wa.Wasm.min(m, 65536) : U32},
  el: {Wa.Wasm.length32(i) == Some{len} : Maybe<&2, U32>},
  er: {Cr.Cir.alloc.pages(k, len, Cr.Cir.pages(Cr.Cir.input.at(k)), lim) == r : Maybe<&2, U32>},
  g: @k2: U32 -> @len2: U32 -> @p2: U32 -> @lim2: U32 -> @first2: U32 -> {I.Start(cells, i, m, k2, len2, p2, lim2, first2) == True{} : Bool} ->
    &n: Nat -> P(Cr.Cir.ended(Cr.Cir.exec(n, prog, I.St0(regs, cells, first2, k2, p2, lim2, i))))) ->
  &n: Nat -> P(Cr.Cir.result.alloced(r, n, prog, regs, cells, k, U32.add(Cr.Cir.input.at(k), len), lim, i)):
  match r:
    case None{}:
      (0n, po)
    case Some{+p}:
      g(k, len, p, lim, Cr.Cir.first(k, U32.add(Cr.Cir.input.at(k), len)), asm.start(cells, i, m, k, len, p, lim, ek, em, elim, el, er))

def asm.rex.sized(nl: Maybe<&2, U32>, prog: Cr.Cir.Stmt, +regs: Nat, +cells: List<&2, Cr.Cir.Cell>, +k: U32,
  +lim: U32, +i: List<&2, Word(8n)>, +m: U32, -P: Wa.Wasm.Outcome -> Type, po: P(Wa.Wasm.Outcome.out_of_memory{}),
  ek: {k == Cr.Wasm.encode.len(Cr.Cir.Cell, cells) : U32},
  em: {U32.is_le(Cr.Cir.pages(Cr.Cir.input.at(k)), m) == True{} : Bool},
  elim: {lim == Wa.Wasm.min(m, 65536) : U32},
  el: {Wa.Wasm.length32(i) == nl : Maybe<&2, U32>},
  g: @k2: U32 -> @len2: U32 -> @p2: U32 -> @lim2: U32 -> @first2: U32 -> {I.Start(cells, i, m, k2, len2, p2, lim2, first2) == True{} : Bool} ->
    &n: Nat -> P(Cr.Cir.ended(Cr.Cir.exec(n, prog, I.St0(regs, cells, first2, k2, p2, lim2, i))))) ->
  &n: Nat -> P(Cr.Cir.result.sized(nl, n, prog, regs, cells, k, Cr.Cir.pages(Cr.Cir.input.at(k)), lim, i)):
  match nl:
    case None{}:
      (0n, po)
    case Some{+len}:
      asm.rex.alloced(Cr.Cir.alloc.pages(k, len, Cr.Cir.pages(Cr.Cir.input.at(k)), lim), prog, regs, cells, k, len, lim, i, m,
        P, po, ek, em, elim, el, {==}, g)

def asm.rex.memory(ok: Bool, prog: Cr.Cir.Stmt, +regs: Nat, +cells: List<&2, Cr.Cir.Cell>, +k: U32,
  +lim: U32, +i: List<&2, Word(8n)>, +m: U32, -P: Wa.Wasm.Outcome -> Type, po: P(Wa.Wasm.Outcome.out_of_memory{}),
  ek: {k == Cr.Wasm.encode.len(Cr.Cir.Cell, cells) : U32},
  em: {U32.is_le(Cr.Cir.pages(Cr.Cir.input.at(k)), m) == ok : Bool},
  elim: {lim == Wa.Wasm.min(m, 65536) : U32},
  g: @k2: U32 -> @len2: U32 -> @p2: U32 -> @lim2: U32 -> @first2: U32 -> {I.Start(cells, i, m, k2, len2, p2, lim2, first2) == True{} : Bool} ->
    &n: Nat -> P(Cr.Cir.ended(Cr.Cir.exec(n, prog, I.St0(regs, cells, first2, k2, p2, lim2, i))))) ->
  &n: Nat -> P(Cr.Cir.result.memory(ok, n, prog, regs, cells, k, Cr.Cir.pages(Cr.Cir.input.at(k)), lim, i)):
  match ok:
    case False{}:
      (0n, po)
    case True{}:
      asm.rex.sized(Wa.Wasm.length32(i), prog, regs, cells, k, lim, i, m, P, po, ek, em, elim, {==}, g)

# a fuel for each run from the start gives one for Cir.result, which runs out
# of memory or runs from the same start with any fuel
def asm.res.ex(prog: Cr.Cir.Stmt, +regs: Nat, +cells: List<&2, Cr.Cir.Cell>, +i: List<&2, Word(8n)>, +m: U32,
  -P: Wa.Wasm.Outcome -> Type, po: P(Wa.Wasm.Outcome.out_of_memory{}),
  g: @k2: U32 -> @len2: U32 -> @p2: U32 -> @lim2: U32 -> @first2: U32 -> {I.Start(cells, i, m, k2, len2, p2, lim2, first2) == True{} : Bool} ->
    &n: Nat -> P(Cr.Cir.ended(Cr.Cir.exec(n, prog, I.St0(regs, cells, first2, k2, p2, lim2, i))))) ->
  &n: Nat -> P(Cr.Cir.result(n, prog, regs, cells, i, m)):
  asm.rex.memory(U32.is_le(Cr.Cir.pages(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), m), prog, regs, cells,
    Cr.Wasm.encode.len(Cr.Cir.Cell, cells), Wa.Wasm.min(m, 65536), i, m, P, po, {==}, {==}, {==}, g)


# what Cir.result does when it finds room for the image and the input (memory
# F): it runs the program from the start
def asm.rok.alloced(r: Maybe<&2, U32>, prog: Cr.Cir.Stmt, +regs: Nat, +cells: List<&2, Cr.Cir.Cell>, +k: U32,
  +len: U32, +lim: U32, +i: List<&2, Word(8n)>, +m: U32, -P: Wa.Wasm.Outcome -> Type,
  +ek: {k == Cr.Wasm.encode.len(Cr.Cir.Cell, cells) : U32},
  +em: {U32.is_le(Cr.Cir.pages(Cr.Cir.input.at(k)), m) == True{} : Bool},
  +elim: {lim == Wa.Wasm.min(m, 65536) : U32},
  +el: {Wa.Wasm.length32(i) == Some{len} : Maybe<&2, U32>},
  +er: {Cr.Cir.alloc.pages(k, len, Cr.Cir.pages(Cr.Cir.input.at(k)), lim) == r : Maybe<&2, U32>},
  +hr: {Me.Start.pg(r) == True{} : Bool},
  g: @k2: U32 -> @len2: U32 -> @p2: U32 -> @lim2: U32 -> @first2: U32 -> {I.Start(cells, i, m, k2, len2, p2, lim2, first2) == True{} : Bool} ->
    &n: Nat -> P(Cr.Cir.ended(Cr.Cir.exec(n, prog, I.St0(regs, cells, first2, k2, p2, lim2, i))))) ->
  &n: Nat -> P(Cr.Cir.result.alloced(r, n, prog, regs, cells, k, U32.add(Cr.Cir.input.at(k), len), lim, i)):
  match r:
    case None{}:
      K.bool.ff(&n: Nat -> P(Cr.Cir.result.alloced(None{}, n, prog, regs, cells, k, U32.add(Cr.Cir.input.at(k), len), lim, i)), hr)
    case Some{+p}:
      g(k, len, p, lim, Cr.Cir.first(k, U32.add(Cr.Cir.input.at(k), len)), asm.start(cells, i, m, k, len, p, lim, ek, em, elim, el, er))

def asm.rok.sized(nl: Maybe<&2, U32>, prog: Cr.Cir.Stmt, +regs: Nat, +cells: List<&2, Cr.Cir.Cell>, +k: U32,
  +lim: U32, +i: List<&2, Word(8n)>, +m: U32, -P: Wa.Wasm.Outcome -> Type,
  +ek: {k == Cr.Wasm.encode.len(Cr.Cir.Cell, cells) : U32},
  +em: {U32.is_le(Cr.Cir.pages(Cr.Cir.input.at(k)), m) == True{} : Bool},
  +elim: {lim == Wa.Wasm.min(m, 65536) : U32},
  +el: {Wa.Wasm.length32(i) == nl : Maybe<&2, U32>},
  +hl: {Me.Start.len(nl, k, Cr.Cir.pages(Cr.Cir.input.at(k)), lim) == True{} : Bool},
  g: @k2: U32 -> @len2: U32 -> @p2: U32 -> @lim2: U32 -> @first2: U32 -> {I.Start(cells, i, m, k2, len2, p2, lim2, first2) == True{} : Bool} ->
    &n: Nat -> P(Cr.Cir.ended(Cr.Cir.exec(n, prog, I.St0(regs, cells, first2, k2, p2, lim2, i))))) ->
  &n: Nat -> P(Cr.Cir.result.sized(nl, n, prog, regs, cells, k, Cr.Cir.pages(Cr.Cir.input.at(k)), lim, i)):
  match nl:
    case None{}:
      K.bool.ff(&n: Nat -> P(Cr.Cir.result.sized(None{}, n, prog, regs, cells, k, Cr.Cir.pages(Cr.Cir.input.at(k)), lim, i)), hl)
    case Some{+len}:
      asm.rok.alloced(Cr.Cir.alloc.pages(k, len, Cr.Cir.pages(Cr.Cir.input.at(k)), lim), prog, regs, cells, k, len, lim, i, m,
        P, ek, em, elim, el, {==}, hl, g)

def asm.rok.memory(ok: Bool, prog: Cr.Cir.Stmt, +regs: Nat, +cells: List<&2, Cr.Cir.Cell>, +k: U32,
  +lim: U32, +i: List<&2, Word(8n)>, +m: U32, -P: Wa.Wasm.Outcome -> Type,
  +ek: {k == Cr.Wasm.encode.len(Cr.Cir.Cell, cells) : U32},
  +em: {U32.is_le(Cr.Cir.pages(Cr.Cir.input.at(k)), m) == ok : Bool},
  +elim: {lim == Wa.Wasm.min(m, 65536) : U32},
  +hs: {Bool.and(ok, Me.Start.len(Wa.Wasm.length32(i), k, Cr.Cir.pages(Cr.Cir.input.at(k)), lim)) == True{} : Bool},
  g: @k2: U32 -> @len2: U32 -> @p2: U32 -> @lim2: U32 -> @first2: U32 -> {I.Start(cells, i, m, k2, len2, p2, lim2, first2) == True{} : Bool} ->
    &n: Nat -> P(Cr.Cir.ended(Cr.Cir.exec(n, prog, I.St0(regs, cells, first2, k2, p2, lim2, i))))) ->
  &n: Nat -> P(Cr.Cir.result.memory(ok, n, prog, regs, cells, k, Cr.Cir.pages(Cr.Cir.input.at(k)), lim, i)):
  match ok:
    case False{}:
      K.bool.ff(&n: Nat -> P(Cr.Cir.result.memory(False{}, n, prog, regs, cells, k, Cr.Cir.pages(Cr.Cir.input.at(k)), lim, i)), hs)
    case True{}:
      asm.rok.sized(Wa.Wasm.length32(i), prog, regs, cells, k, lim, i, m, P, ek, em, elim, {==}, hs, g)

def asm.rok.ex(prog: Cr.Cir.Stmt, +regs: Nat, +cells: List<&2, Cr.Cir.Cell>, +i: List<&2, Word(8n)>, +m: U32,
  -P: Wa.Wasm.Outcome -> Type, +hs: {Me.Start.ok(cells, i, m) == True{} : Bool},
  g: @k2: U32 -> @len2: U32 -> @p2: U32 -> @lim2: U32 -> @first2: U32 -> {I.Start(cells, i, m, k2, len2, p2, lim2, first2) == True{} : Bool} ->
    &n: Nat -> P(Cr.Cir.ended(Cr.Cir.exec(n, prog, I.St0(regs, cells, first2, k2, p2, lim2, i))))) ->
  &n: Nat -> P(Cr.Cir.result(n, prog, regs, cells, i, m)):
  asm.rok.memory(U32.is_le(Cr.Cir.pages(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), m), prog, regs, cells,
    Cr.Wasm.encode.len(Cr.Cir.Cell, cells), Wa.Wasm.min(m, 65536), i, m, P, {==}, {==}, {==}, hs, g)

# The run
# -------

# Mach.code after M.input: the mode's set, then the loop
def Asm.rest() -> Cr.Cir.Stmt:
  Mc.M.do([Mc.M.set(Mc.R.mode(), Mc.M.c(0)), Asm.loop()])

def Asm.tail() -> Cr.Cir.Stmt:
  Mc.M.do([Asm.loop()])

# the start's abstract state
def Asm.s0(+i: List<&2, Word(8n)>) -> A.AS:
  A.AS{False{}, Pg.Program.start(i), []}

# M.input's post: Inv of the start term once the mode is 0
def Asm.In(+ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +k: U32, +first: U32, +st: Cr.Cir.State) -> Bool:
  R.Inv(Asm.x0(ds, k, first), R.Mode0(st), Asm.s0(i))

# J at the loop's start: Inv, and the start term is canonical
def asm.j0(+ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +k: U32, +first: U32, +st: Cr.Cir.State,
  +iv: {Asm.In(ds, i, k, first, st) == True{} : Bool}) -> {Asm.J(Asm.x0(ds, k, first), R.Mode0(st), Asm.s0(i)) == True{} : Bool}:
  K.bool.and_i(R.Inv(Asm.x0(ds, k, first), R.Mode0(st), Asm.s0(i)), A.AS.ok0(ds, Asm.s0(i)), iv, C.canon.start(i))

# the mode is a register of the state after M.input
def asm.hr0(+ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +k: U32, +first: U32, +st: Cr.Cir.State,
  +iv: {Asm.In(ds, i, k, first, st) == True{} : Bool}) -> {Nat.is_lt(Mc.R.mode(), Lg.St.nregs(st)) == True{} : Bool}:
  +x = Asm.x0(ds, k, first)
  +st1 = R.Mode0(st)
  +em = MvP.rd.mb(Lg.Reg(st1, Mc.R.mode()), 0, K.bool.and_l(R.Inv.mode(st1, False{}),
    Hp.H(x, st1, Hp.V.Live(st1), [Hp.Rt{Lg.St.reg(st1, Mc.R.focus()), 0n, Pg.Program.start(i)}], [], []), iv))
  (%Lg.nregs.set(st, Mc.R.mode(), 0) : {Nat.is_lt(Mc.R.mode(), _) == True{} : Bool}; Lg.reg.lt(st1, Mc.R.mode(), 0, em))

# the rest of Mach.code after M.input, at any fuel: the loop's HE
def asm.run.rest(+n: Nat, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +k: U32, +first: U32, +st: Cr.Cir.State,
  +iv: {Asm.In(ds, i, k, first, st) == True{} : Bool}) ->
  Asm.Ps(Cr.Cir.exec(n, Asm.rest(), st), q => st2 => Asm.HE(ds, Pg.Program.start(i), q, st2)):
  +set = Mc.M.set(Mc.R.mode(), Mc.M.c(0))
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(n, Asm.rest(), st), Cr.Cir.exec.then(Cr.Cir.exec(n, set, st), t => Cr.Cir.exec(n, Asm.tail(), t)),
    LgP.lg.exec.seq(n, set, Asm.tail(), st)) : Asm.Ps(_, q => st2 => Asm.HE(ds, Pg.Program.start(i), q, st2))
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(n, set, st), Cr.Cir.Out.next{Lg.St.set(st, Mc.R.mode(), 0)},
    Lg.exec.set(n, Mc.R.mode(), Mc.M.c(0), st, 0, {==}, asm.hr0(ds, i, k, first, st, iv))) :
    Asm.Ps(Cr.Cir.exec.then(_, t => Cr.Cir.exec(n, Asm.tail(), t)), q => st2 => Asm.HE(ds, Pg.Program.start(i), q, st2))
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(n, Asm.tail(), R.Mode0(st)),
    Cr.Cir.exec.then(Cr.Cir.exec(n, Asm.loop(), R.Mode0(st)), t => Cr.Cir.exec(n, Cr.Cir.Stmt.nop{}, t)),
    LgP.lg.exec.seq(n, Asm.loop(), Cr.Cir.Stmt.nop{}, R.Mode0(st))) : Asm.Ps(_, q => st2 => Asm.HE(ds, Pg.Program.start(i), q, st2))
  asm.ps.then(Cr.Cir.exec(n, Asm.loop(), R.Mode0(st)), t => Cr.Cir.exec(n, Cr.Cir.Stmt.nop{}, t),
    q => st2 => Asm.HE(ds, Pg.Program.start(i), q, st2),
    asm.post(n, Asm.x0(ds, k, first), R.Mode0(st), Asm.s0(i), asm.j0(ds, i, k, first, st, iv)))

# Mach.code after M.input's outcome r, at any fuel
def asm.run.go(r: Cr.Cir.Out, +n: Nat, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +k: U32, +pg: U32, +lim: U32,
  +first: U32,
  a: Or({r == Cr.Cir.Out.not_done{} : Cr.Cir.Out}, Lg.Ok(r, Lg.Lim(Asm.St0(ds, first, k, pg, lim, i)), R.Input.budget(first, i),
    st => {Asm.In(ds, i, k, first, st) == True{} : Bool}, Lg.No))) ->
  Asm.Ps(Cr.Cir.exec.then(r, t => Cr.Cir.exec(n, Asm.rest(), t)), q => st2 => Asm.HE(ds, Pg.Program.start(i), q, st2)):
  match r:
    case Cr.Cir.Out.next{+st}:
      match a:
        case Inl{e}:
          Empty.absurd(Asm.Ps(Cr.Cir.exec(n, Asm.rest(), st), q => st2 => Asm.HE(ds, Pg.Program.start(i), q, st2)),
            asm.nd(Cr.Cir.Out.next{st}, e, Unit{}))
        case Inr{iv}:
          asm.run.rest(n, ds, i, k, first, st, iv)
    case Cr.Cir.Out.halt{+q, +st2}:
      match a:
        case Inl{e}:
          Empty.absurd(Asm.HE(ds, Pg.Program.start(i), q, st2), asm.nd(Cr.Cir.Out.halt{q, st2}, e, Unit{}))
        case Inr{z}:
          Empty.absurd(Asm.HE(ds, Pg.Program.start(i), q, st2), z)
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

# a run of Mach.code from the start halts only as HE says, from the start
# term, at any fuel
def asm.run.post(+n: Nat, +p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +m: U32, +k: U32, +len: U32,
  +pg: U32, +lim: U32, +first: U32,
  +rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  +small: {Mc.Img.small(p, 0) == True{} : Bool},
  +s: {I.Start(Mc.Img.cells(ds), i, m, k, len, pg, lim, first) == True{} : Bool}) ->
  Asm.Ps(Cr.Cir.exec(n, Mc.Mach.code(), Asm.St0(ds, first, k, pg, lim, i)), q => st2 => Asm.HE(ds, Pg.Program.start(i), q, st2)):
  +St0 = Asm.St0(ds, first, k, pg, lim, i)
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(n, Mc.Mach.code(), St0),
    Cr.Cir.exec.then(Cr.Cir.exec(n, Mc.M.input(), St0), t => Cr.Cir.exec(n, Asm.rest(), t)),
    LgP.lg.exec.seq(n, Mc.M.input(), Asm.rest(), St0)) : Asm.Ps(_, q => st2 => Asm.HE(ds, Pg.Program.start(i), q, st2))
  asm.run.go(Cr.Cir.exec(n, Mc.M.input(), St0), n, ds, i, k, pg, lim, first,
    Lg.tot.any(Mc.M.input(), St0, R.Input.budget(first, i), st => {Asm.In(ds, i, k, first, st) == True{} : Bool}, Lg.No,
      R.input.spec(p, ds, i, m, k, len, pg, lim, first, rd, small, s), n))

# M.input with the fuel f1, then the loop with n2, are Mach.code with f1 + n2
def asm.run.fin(+mm: Bool, +o: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +k: U32, +pg: U32, +lim: U32,
  +first: U32, +f1: Nat, +n2: Nat, +st: Cr.Cir.State,
  +er1: {Cr.Cir.exec(f1, Mc.M.input(), Asm.St0(ds, first, k, pg, lim, i)) == Cr.Cir.Out.next{st} : Cr.Cir.Out},
  +hr: {Nat.is_lt(Mc.R.mode(), Lg.St.nregs(st)) == True{} : Bool},
  +g2: Asm.Good(mm, o, Cr.Cir.exec(n2, Asm.loop(), R.Mode0(st)))) ->
  Asm.Good(mm, o, Cr.Cir.exec(Nat.add(f1, n2), Mc.Mach.code(), Asm.St0(ds, first, k, pg, lim, i))):
  +St0 = Asm.St0(ds, first, k, pg, lim, i)
  +n = Nat.add(f1, n2)
  +set = Mc.M.set(Mc.R.mode(), Mc.M.c(0))
  +d1 = Equal.cong(Cr.Cir.Out, Bool, x => Lg.Out.done(x), Cr.Cir.exec(f1, Mc.M.input(), St0), Cr.Cir.Out.next{st}, er1)
  +e1 = Equal.trans(Cr.Cir.Out, Cr.Cir.exec(n, Mc.M.input(), St0), Cr.Cir.exec(f1, Mc.M.input(), St0), Cr.Cir.Out.next{st},
    Lg.exec.more(f1, n2, Mc.M.input(), St0, d1), er1)
  +e5 = Equal.trans(Cr.Cir.Out, Cr.Cir.exec(n, Asm.loop(), R.Mode0(st)), Cr.Cir.exec(Nat.add(n2, f1), Asm.loop(), R.Mode0(st)),
    Cr.Cir.exec(n2, Asm.loop(), R.Mode0(st)),
    Equal.cong(Nat, Cr.Cir.Out, g => Cr.Cir.exec(g, Asm.loop(), R.Mode0(st)), n, Nat.add(n2, f1), LgP.lg.add_comm(f1, n2)),
    Lg.exec.more(n2, f1, Asm.loop(), R.Mode0(st), asm.good.done(mm, o, Cr.Cir.exec(n2, Asm.loop(), R.Mode0(st)), g2)))
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(n, Mc.Mach.code(), St0),
    Cr.Cir.exec.then(Cr.Cir.exec(n, Mc.M.input(), St0), t => Cr.Cir.exec(n, Asm.rest(), t)),
    LgP.lg.exec.seq(n, Mc.M.input(), Asm.rest(), St0)) : Asm.Good(mm, o, _)
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(n, Mc.M.input(), St0), Cr.Cir.Out.next{st}, e1) :
    Asm.Good(mm, o, Cr.Cir.exec.then(_, t => Cr.Cir.exec(n, Asm.rest(), t)))
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(n, Asm.rest(), st), Cr.Cir.exec.then(Cr.Cir.exec(n, set, st), t => Cr.Cir.exec(n, Asm.tail(), t)),
    LgP.lg.exec.seq(n, set, Asm.tail(), st)) : Asm.Good(mm, o, _)
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(n, set, st), Cr.Cir.Out.next{Lg.St.set(st, Mc.R.mode(), 0)},
    Lg.exec.set(n, Mc.R.mode(), Mc.M.c(0), st, 0, {==}, hr)) : Asm.Good(mm, o, Cr.Cir.exec.then(_, t => Cr.Cir.exec(n, Asm.tail(), t)))
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(n, Asm.tail(), R.Mode0(st)),
    Cr.Cir.exec.then(Cr.Cir.exec(n, Asm.loop(), R.Mode0(st)), t => Cr.Cir.exec(n, Cr.Cir.Stmt.nop{}, t)),
    LgP.lg.exec.seq(n, Asm.loop(), Cr.Cir.Stmt.nop{}, R.Mode0(st))) : Asm.Good(mm, o, _)
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(n, Asm.loop(), R.Mode0(st)), Cr.Cir.exec(n2, Asm.loop(), R.Mode0(st)), e5) :
    Asm.Good(mm, o, Cr.Cir.exec.then(_, t => Cr.Cir.exec(n, Cr.Cir.Stmt.nop{}, t)))
  asm.good.then(mm, o, Cr.Cir.exec(n2, Asm.loop(), R.Mode0(st)), t => Cr.Cir.exec(n, Cr.Cir.Stmt.nop{}, t), g2)

# a fuel for the loop after M.input gives one for Mach.code
def asm.run.ex(+mm: Bool, +o: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +k: U32, +pg: U32, +lim: U32,
  +first: U32, +f1: Nat, +st: Cr.Cir.State,
  +er1: {Cr.Cir.exec(f1, Mc.M.input(), Asm.St0(ds, first, k, pg, lim, i)) == Cr.Cir.Out.next{st} : Cr.Cir.Out},
  +hr: {Nat.is_lt(Mc.R.mode(), Lg.St.nregs(st)) == True{} : Bool},
  g: &r:Nat -> Asm.Good(mm, o, Cr.Cir.exec(r, Asm.loop(), R.Mode0(st)))) ->
  &r:Nat -> Asm.Good(mm, o, Cr.Cir.exec(r, Mc.Mach.code(), Asm.St0(ds, first, k, pg, lim, i))):
  match g:
    case Tuple{+n2, g2}:
      (Nat.add(f1, n2), asm.run.fin(mm, o, ds, i, k, pg, lim, first, f1, n2, st, er1, hr, g2))

# M.input that runs out of memory with the fuel f1 ends Mach.code so
def asm.run.oom(+o: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +k: U32, +pg: U32, +lim: U32, +first: U32,
  +f1: Nat, +er1: {Cr.Cir.exec(f1, Mc.M.input(), Asm.St0(ds, first, k, pg, lim, i)) == Cr.Cir.Out.out_of_memory{} : Cr.Cir.Out}) ->
  Asm.Good(False{}, o, Cr.Cir.exec(f1, Mc.Mach.code(), Asm.St0(ds, first, k, pg, lim, i))):
  +St0 = Asm.St0(ds, first, k, pg, lim, i)
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f1, Mc.Mach.code(), St0),
    Cr.Cir.exec.then(Cr.Cir.exec(f1, Mc.M.input(), St0), t => Cr.Cir.exec(f1, Asm.rest(), t)),
    LgP.lg.exec.seq(f1, Mc.M.input(), Asm.rest(), St0)) : Asm.Good(False{}, o, _)
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f1, Mc.M.input(), St0), Cr.Cir.Out.out_of_memory{}, er1) :
    Asm.Good(False{}, o, Cr.Cir.exec.then(_, t => Cr.Cir.exec(f1, Asm.rest(), t)))
  Unit{}

# when Eval reaches the bytes o, Mach.code gives them or runs out of memory,
# by M.input's outcome r with the fuel f1
def asm.run.done.r(r: Cr.Cir.Out, +kk: Nat, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +k: U32, +pg: U32, +lim: U32,
  +first: U32, +o: List<&2, Word(8n)>, +f1: Nat,
  +er1: {Cr.Cir.exec(f1, Mc.M.input(), Asm.St0(ds, first, k, pg, lim, i)) == r : Cr.Cir.Out},
  ok1: Lg.Ok(r, Lg.Lim(Asm.St0(ds, first, k, pg, lim, i)), R.Input.budget(first, i),
    st => {Asm.In(ds, i, k, first, st) == True{} : Bool}, Lg.No),
  +e: {Pg.Program.result(ds, El.Eval.steps(kk, ds, Pg.Program.start(i))) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}) ->
  &r:Nat -> Asm.Good(False{}, o, Cr.Cir.exec(r, Mc.Mach.code(), Asm.St0(ds, first, k, pg, lim, i))):
  match r:
    case Cr.Cir.Out.next{+st}:
      +iv = {ok1 : {Asm.In(ds, i, k, first, st) == True{} : Bool}}
      asm.run.ex(False{}, o, ds, i, k, pg, lim, first, f1, st, er1, asm.hr0(ds, i, k, first, st, iv),
        asm.done(kk, 1n+A.AS.w(Asm.s0(i)), Asm.x0(ds, k, first), R.Mode0(st), Asm.s0(i), o, asm.lt.succ(A.AS.w(Asm.s0(i))),
          Equal.trans(Maybe<&2, List<&2, Word(8n)>>, Pg.Program.result(ds, C.CSteps(kk, ds, Some{Pg.Program.start(i)})),
            Pg.Program.result(ds, El.Eval.steps(kk, ds, Pg.Program.start(i))), Some{o}, asm.cs.eval(ds, i, kk), e),
          asm.j0(ds, i, k, first, st, iv)))
    case Cr.Cir.Out.halt{_, _}:
      Empty.absurd(&r:Nat -> Asm.Good(False{}, o, Cr.Cir.exec(r, Mc.Mach.code(), Asm.St0(ds, first, k, pg, lim, i))), ok1)
    case Cr.Cir.Out.out_of_memory{}:
      (f1, asm.run.oom(o, ds, i, k, pg, lim, first, f1, er1))
    case Cr.Cir.Out.trap{}:
      Empty.absurd(&r:Nat -> Asm.Good(False{}, o, Cr.Cir.exec(r, Mc.Mach.code(), Asm.St0(ds, first, k, pg, lim, i))), ok1)
    case Cr.Cir.Out.not_done{}:
      Empty.absurd(&r:Nat -> Asm.Good(False{}, o, Cr.Cir.exec(r, Mc.Mach.code(), Asm.St0(ds, first, k, pg, lim, i))), ok1)

def asm.run.done(+kk: Nat, +p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +m: U32, +o: List<&2, Word(8n)>,
  +k: U32, +len: U32, +pg: U32, +lim: U32, +first: U32,
  +rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  +small: {Mc.Img.small(p, 0) == True{} : Bool},
  +s: {I.Start(Mc.Img.cells(ds), i, m, k, len, pg, lim, first) == True{} : Bool},
  +e: {Pg.Program.result(ds, El.Eval.steps(kk, ds, Pg.Program.start(i))) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}) ->
  &r:Nat -> Asm.Good(False{}, o, Cr.Cir.exec(r, Mc.Mach.code(), Asm.St0(ds, first, k, pg, lim, i))):
  +St0 = Asm.St0(ds, first, k, pg, lim, i)
  +f1 = asm.tot.f(Mc.M.input(), St0, R.Input.budget(first, i), st => {Asm.In(ds, i, k, first, st) == True{} : Bool}, Lg.No,
    R.input.spec(p, ds, i, m, k, len, pg, lim, first, rd, small, s))
  ok1 = asm.tot.ok(Mc.M.input(), St0, R.Input.budget(first, i), st => {Asm.In(ds, i, k, first, st) == True{} : Bool}, Lg.No,
    R.input.spec(p, ds, i, m, k, len, pg, lim, first, rd, small, s))
  asm.run.done.r(Cr.Cir.exec(f1, Mc.M.input(), St0), kk, ds, i, k, pg, lim, first, o, f1, {==}, ok1, e)

# within the memory F, Mach.code gives the bytes o, by M.input's outcome r
def asm.run.mem.r(r: Cr.Cir.Out, +kk: Nat, +p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +m: U32,
  +k: U32, +len: U32, +pg: U32, +lim: U32, +first: U32, +o: List<&2, Word(8n)>, +f1: Nat,
  +rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  +small: {Mc.Img.small(p, 0) == True{} : Bool},
  +s: {I.Start(Mc.Img.cells(ds), i, m, k, len, pg, lim, first) == True{} : Bool},
  +e: {Pg.Program.result(ds, El.Eval.steps(kk, ds, Pg.Program.start(i))) == Some{o} : Maybe<&2, List<&2, Word(8n)>>},
  +big: {Nat.is_le(Pg.Program.need(p, i, kk), Pg.Program.memory(m)) == True{} : Bool},
  +er1: {Cr.Cir.exec(f1, Mc.M.input(), Asm.St0(ds, first, k, pg, lim, i)) == r : Cr.Cir.Out},
  ok1: Lg.Ok(r, Lg.Lim(Asm.St0(ds, first, k, pg, lim, i)), R.Input.budget(first, i),
    st => {Asm.In(ds, i, k, first, st) == True{} : Bool}, Lg.No)) ->
  &r:Nat -> Asm.Good(True{}, o, Cr.Cir.exec(r, Mc.Mach.code(), Asm.St0(ds, first, k, pg, lim, i))):
  match r:
    case Cr.Cir.Out.next{+st}:
      +iv = {ok1 : {Asm.In(ds, i, k, first, st) == True{} : Bool}}
      +St0 = Asm.St0(ds, first, k, pg, lim, i)
      +L0 = Lg.Lim(St0)
      +S = Pg.Program.largest(p, i, kk)
      +st1 = R.Mode0(st)
      +c = Me.Stat(st1)
      +im = Me.input.mem(p, ds, i, m, k, len, pg, lim, first, kk, rd, small, s, f1, st, er1)
      +hc = K.bool.and_l(Nat.is_le(c, 6144n), Nat.is_le(Me.Mem.cells(st1), Me.Peak(ds, c, S)), im)
      +hm = K.bool.and_r(Nat.is_le(c, 6144n), Nat.is_le(Me.Mem.cells(st1), Me.Peak(ds, c, S)), im)
      +hf = K.bool.and_i(Bool.and(I.Start(Mc.Img.cells(ds), i, m, k, len, pg, lim, first), Nat.is_le(c, 6144n)),
        Nat.is_le(Pg.Program.need(p, i, kk), L0),
        K.bool.and_i(I.Start(Mc.Img.cells(ds), i, m, k, len, pg, lim, first), Nat.is_le(c, 6144n), s, hc),
        Me.need.lim(p, ds, i, m, k, len, pg, lim, first, kk, s, big))
      +el = Equal.trans(Nat, Lg.Lim(st1), Lg.Lim(st), L0, Lg.lim.set(st, Mc.R.mode(), 0),
        LgP.lg.lim.eq(st, St0, Lg.frame.fixed(f1, Mc.M.input(), St0, st, er1)))
      +ht0 = C.Tm.is(C.CSteps(0n, ds, Some{Pg.Program.start(i)}), A.AS.term(Asm.s0(i)))
      +hs = K.bool.and_i(Bool.and(Bool.and(ht0, Nat.is_eq(Lg.Lim(st1), L0)), Nat.is_le(c, c)), Nat.is_le(Me.Mem.cells(st1), Me.Peak(ds, c, S)),
        K.bool.and_i(Bool.and(ht0, Nat.is_eq(Lg.Lim(st1), L0)), Nat.is_le(c, c),
          K.bool.and_i(ht0, Nat.is_eq(Lg.Lim(st1), L0), C.term.is_eq_refl(Pg.Program.start(i)),
            (%el : {Nat.is_eq(Lg.Lim(st1), _) == True{} : Bool}; K.nat.is_eq_refl(Lg.Lim(st1)))),
          LgP.lg.le_refl(c)), hm)
      asm.run.ex(True{}, o, ds, i, k, pg, lim, first, f1, st, er1, asm.hr0(ds, i, k, first, st, iv),
        asm.mem(kk, 1n+A.AS.w(Asm.s0(i)), p, ds, i, m, k, len, pg, lim, first, kk, o, c, 0n, st1, Asm.s0(i), rd, e, hf,
          asm.lt.succ(A.AS.w(Asm.s0(i))),
          Equal.trans(Maybe<&2, List<&2, Word(8n)>>, Pg.Program.result(ds, C.CSteps(kk, ds, Some{Pg.Program.start(i)})),
            Pg.Program.result(ds, El.Eval.steps(kk, ds, Pg.Program.start(i))), Some{o}, asm.cs.eval(ds, i, kk), e),
          {==}, hs, asm.j0(ds, i, k, first, st, iv)))
    case Cr.Cir.Out.halt{_, _}:
      Empty.absurd(&r:Nat -> Asm.Good(True{}, o, Cr.Cir.exec(r, Mc.Mach.code(), Asm.St0(ds, first, k, pg, lim, i))), ok1)
    case Cr.Cir.Out.out_of_memory{}:
      +St0 = Asm.St0(ds, first, k, pg, lim, i)
      +nd = Pg.Program.need(p, i, kk)
      Empty.absurd(&r:Nat -> Asm.Good(True{}, o, Cr.Cir.exec(r, Mc.Mach.code(), St0)),
        asm.lt.abs(Lg.Lim(St0), R.Input.budget(first, i), ok1,
          asm.le.trans(R.Input.budget(first, i), nd, Lg.Lim(St0), Me.input.need(p, ds, i, m, k, len, pg, lim, first, kk, rd, s),
            Me.need.lim(p, ds, i, m, k, len, pg, lim, first, kk, s, big))))
    case Cr.Cir.Out.trap{}:
      Empty.absurd(&r:Nat -> Asm.Good(True{}, o, Cr.Cir.exec(r, Mc.Mach.code(), Asm.St0(ds, first, k, pg, lim, i))), ok1)
    case Cr.Cir.Out.not_done{}:
      Empty.absurd(&r:Nat -> Asm.Good(True{}, o, Cr.Cir.exec(r, Mc.Mach.code(), Asm.St0(ds, first, k, pg, lim, i))), ok1)

def asm.run.mem(+kk: Nat, +p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +m: U32, +o: List<&2, Word(8n)>,
  +k: U32, +len: U32, +pg: U32, +lim: U32, +first: U32,
  +rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  +small: {Mc.Img.small(p, 0) == True{} : Bool},
  +s: {I.Start(Mc.Img.cells(ds), i, m, k, len, pg, lim, first) == True{} : Bool},
  +e: {Pg.Program.result(ds, El.Eval.steps(kk, ds, Pg.Program.start(i))) == Some{o} : Maybe<&2, List<&2, Word(8n)>>},
  +big: {Nat.is_le(Pg.Program.need(p, i, kk), Pg.Program.memory(m)) == True{} : Bool}) ->
  &r:Nat -> Asm.Good(True{}, o, Cr.Cir.exec(r, Mc.Mach.code(), Asm.St0(ds, first, k, pg, lim, i))):
  +St0 = Asm.St0(ds, first, k, pg, lim, i)
  +f1 = asm.tot.f(Mc.M.input(), St0, R.Input.budget(first, i), st => {Asm.In(ds, i, k, first, st) == True{} : Bool}, Lg.No,
    R.input.spec(p, ds, i, m, k, len, pg, lim, first, rd, small, s))
  ok1 = asm.tot.ok(Mc.M.input(), St0, R.Input.budget(first, i), st => {Asm.In(ds, i, k, first, st) == True{} : Bool}, Lg.No,
    R.input.spec(p, ds, i, m, k, len, pg, lim, first, rd, small, s))
  asm.run.mem.r(Cr.Cir.exec(f1, Mc.M.input(), St0), kk, p, ds, i, m, k, len, pg, lim, first, o, f1, rd, small, s, e, big, {==}, ok1)

# How a run ends
# --------------

# the outcomes that are no trap
def Asm.nt(x: Wa.Wasm.Outcome) -> Type:
  match x:
    case Wa.Wasm.Outcome.result{_}:
      Unit
    case Wa.Wasm.Outcome.out_of_memory{}:
      Unit
    case Wa.Wasm.Outcome.no_result{}:
      Unit
    case Wa.Wasm.Outcome.unsupported{}:
      Unit
    case Wa.Wasm.Outcome.trap{}:
      Empty
    case Wa.Wasm.Outcome.not_done{}:
      Unit

# the outcomes that are no result
def Asm.nr(x: Wa.Wasm.Outcome) -> Type:
  match x:
    case Wa.Wasm.Outcome.result{_}:
      Empty
    case Wa.Wasm.Outcome.out_of_memory{}:
      Unit
    case Wa.Wasm.Outcome.no_result{}:
      Unit
    case Wa.Wasm.Outcome.unsupported{}:
      Unit
    case Wa.Wasm.Outcome.trap{}:
      Unit
    case Wa.Wasm.Outcome.not_done{}:
      Unit

def asm.oc.get(x: Wa.Wasm.Outcome, d: List<&2, Word(8n)>) -> List<&2, Word(8n)>:
  match x:
    case Wa.Wasm.Outcome.result{y}:
      y
    case _:
      d

# result is one to one
def asm.oc.inj(+a: List<&2, Word(8n)>, -b: List<&2, Word(8n)>, e: {Wa.Wasm.Outcome.result{a} == Wa.Wasm.Outcome.result{b} : Wa.Wasm.Outcome}) ->
  {a == b : List<&2, Word(8n)>}:
  Equal.cong(Wa.Wasm.Outcome, List<&2, Word(8n)>, x => asm.oc.get(x, a), Wa.Wasm.Outcome.result{a}, Wa.Wasm.Outcome.result{b}, e)

# a run that halts with 0 gives its output as the host reads it
def asm.ended0(-s: U32, -fits: Bool, +out: List<&2, Word(8n)>, e0: {s == 0 : U32}) ->
  {Cr.Cir.ended.halt(U32.is_eq(s, 0), U32.is_eq(s, 1), U32.is_eq(s, 2), fits, out) == Cr.Cir.ended.output(fits, out) : Wa.Wasm.Outcome}:
  %Equal.sym(U32, s, 0, e0) : {Cr.Cir.ended.halt(U32.is_eq(_, 0), U32.is_eq(_, 1), U32.is_eq(_, 2), fits, out) == Cr.Cir.ended.output(fits, out) : Wa.Wasm.Outcome}
  {==}

# a run that halts with 2 gives no result
def asm.ended2(-s: U32, -fits: Bool, +out: List<&2, Word(8n)>, e2: {s == 2 : U32}) ->
  {Cr.Cir.ended.halt(U32.is_eq(s, 0), U32.is_eq(s, 1), U32.is_eq(s, 2), fits, out) == Wa.Wasm.Outcome.no_result{} : Wa.Wasm.Outcome}:
  %Equal.sym(U32, s, 2, e2) : {Cr.Cir.ended.halt(U32.is_eq(_, 0), U32.is_eq(_, 1), U32.is_eq(_, 2), fits, out) == Wa.Wasm.Outcome.no_result{} : Wa.Wasm.Outcome}
  {==}

# an output that the host reads as the result x is its bytes
def asm.output.inj(fits: Bool, +out: List<&2, Word(8n)>, -x: List<&2, Word(8n)>,
  e: {Cr.Cir.ended.output(fits, out) == Wa.Wasm.Outcome.result{x} : Wa.Wasm.Outcome}) ->
  {List.reverse(&2, Word(8n), out) == x : List<&2, Word(8n)>}:
  match fits:
    case True{}:
      asm.oc.inj(List.reverse(&2, Word(8n), out), x, e)
    case False{}:
      Empty.absurd({List.reverse(&2, Word(8n), out) == x : List<&2, Word(8n)>}, (%e : Asm.nr(_); Unit{}))

# at a halt 0, Fits.halt says the host's check
def asm.fits0(-s: U32, +F: Bool, e0: {s == 0 : U32}, hf: {Bool.or(Bool.not(U32.is_eq(s, 0)), F) == True{} : Bool}) -> {F == True{} : Bool}:
  (%e0 : {Bool.or(Bool.not(U32.is_eq(_, 0)), F) == True{} : Bool}; hf)

# a run that halts only as HE says, with its output in the memory at halt 0,
# never traps
def asm.safe.end(o: Cr.Cir.Out, -ds: List<&2, Bk.Def>, -t: Bk.Term,
  h: Asm.Ps(o, q => st2 => Asm.HE(ds, t, q, st2)), hf: {Me.Fits.halt(o) == True{} : Bool}) ->
  {Cr.Cir.ended(o) != Wa.Wasm.Outcome.trap{} : Wa.Wasm.Outcome}:
  match o:
    case Cr.Cir.Out.next{st}:
      e => (%e : Asm.nt(_); Unit{})
    case Cr.Cir.Out.halt{+s, Cr.Cir.State{regs, m, +nx, fi, im, +pg, lim, inp, +out, +outn}}:
      match h:
        case Inl{y}:
          (+e0, _) = y
          +fits = Wa.Wasm.fits(pg, Cr.Cir.at(nx), outn)
          %Equal.sym(Wa.Wasm.Outcome, Cr.Cir.ended.halt(U32.is_eq(s, 0), U32.is_eq(s, 1), U32.is_eq(s, 2), fits, out),
            Cr.Cir.ended.output(fits, out), asm.ended0(s, fits, out, e0)) : {_ != Wa.Wasm.Outcome.trap{} : Wa.Wasm.Outcome}
          %Equal.sym(Bool, fits, True{}, asm.fits0(s, fits, e0, hf)) : {Cr.Cir.ended.output(_, out) != Wa.Wasm.Outcome.trap{} : Wa.Wasm.Outcome}
          e => (%e : Asm.nt(_); Unit{})
        case Inr{e2}:
          +fits = Wa.Wasm.fits(pg, Cr.Cir.at(nx), outn)
          %Equal.sym(Wa.Wasm.Outcome, Cr.Cir.ended.halt(U32.is_eq(s, 0), U32.is_eq(s, 1), U32.is_eq(s, 2), fits, out),
            Wa.Wasm.Outcome.no_result{}, asm.ended2(s, fits, out, e2)) : {_ != Wa.Wasm.Outcome.trap{} : Wa.Wasm.Outcome}
          e => (%e : Asm.nt(_); Unit{})
    case Cr.Cir.Out.out_of_memory{}:
      e => (%e : Asm.nt(_); Unit{})
    case Cr.Cir.Out.trap{}:
      Empty.absurd({Wa.Wasm.Outcome.trap{} != Wa.Wasm.Outcome.trap{} : Wa.Wasm.Outcome}, h)
    case Cr.Cir.Out.not_done{}:
      e => (%e : Asm.nt(_); Unit{})

# a halt 0 of the start term whose canonical steps reach its output gives
# Eval's result
def asm.sound.go(+ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +x: List<&2, Word(8n)>, -s: U32, +out: List<&2, Word(8n)>,
  r: Sigma<&2, &2, Nat, n => {Pg.Program.result(ds, C.CSteps(n, ds, Some{Pg.Program.start(i)})) ==
  Some{List.reverse(&2, Word(8n), out)} : Maybe<&2, List<&2, Word(8n)>>}>, +fits: Bool, e0: {s == 0 : U32},
  e: {Cr.Cir.ended.halt(U32.is_eq(s, 0), U32.is_eq(s, 1), U32.is_eq(s, 2), fits, out) == Wa.Wasm.Outcome.result{x} : Wa.Wasm.Outcome}) ->
  &k: Nat -> {Pg.Program.result(ds, El.Eval.steps(k, ds, Pg.Program.start(i))) == Some{x} : Maybe<&2, List<&2, Word(8n)>>}:
  match r:
    case Tuple{+n, en}:
      +rx = asm.output.inj(fits, out, x, Equal.trans(Wa.Wasm.Outcome, Cr.Cir.ended.output(fits, out),
        Cr.Cir.ended.halt(U32.is_eq(s, 0), U32.is_eq(s, 1), U32.is_eq(s, 2), fits, out), Wa.Wasm.Outcome.result{x},
        Equal.sym(Wa.Wasm.Outcome, Cr.Cir.ended.halt(U32.is_eq(s, 0), U32.is_eq(s, 1), U32.is_eq(s, 2), fits, out),
          Cr.Cir.ended.output(fits, out), asm.ended0(s, fits, out, e0)), e))
      (n, Equal.trans(Maybe<&2, List<&2, Word(8n)>>, Pg.Program.result(ds, El.Eval.steps(n, ds, Pg.Program.start(i))),
        Pg.Program.result(ds, C.CSteps(n, ds, Some{Pg.Program.start(i)})), Some{x},
        Equal.sym(Maybe<&2, List<&2, Word(8n)>>, Pg.Program.result(ds, C.CSteps(n, ds, Some{Pg.Program.start(i)})),
          Pg.Program.result(ds, El.Eval.steps(n, ds, Pg.Program.start(i))), asm.cs.eval(ds, i, n)),
        (%rx : {Pg.Program.result(ds, C.CSteps(n, ds, Some{Pg.Program.start(i)})) == Some{_} : Maybe<&2, List<&2, Word(8n)>>}; en)))

# a result of a run of the start term that halts only as HE says is one that
# Eval reaches
def asm.sound.end(o: Cr.Cir.Out, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +x: List<&2, Word(8n)>,
  h: Asm.Ps(o, q => st2 => Asm.HE(ds, Pg.Program.start(i), q, st2)),
  e: {Cr.Cir.ended(o) == Wa.Wasm.Outcome.result{x} : Wa.Wasm.Outcome}) ->
  &k: Nat -> {Pg.Program.result(ds, El.Eval.steps(k, ds, Pg.Program.start(i))) == Some{x} : Maybe<&2, List<&2, Word(8n)>>}:
  match o:
    case Cr.Cir.Out.next{st}:
      Empty.absurd(&k: Nat -> {Pg.Program.result(ds, El.Eval.steps(k, ds, Pg.Program.start(i))) == Some{x} : Maybe<&2, List<&2, Word(8n)>>},
        (%e : Asm.nr(_); Unit{}))
    case Cr.Cir.Out.halt{+s, Cr.Cir.State{regs, m, +nx, fi, im, +pg, lim, inp, +out, +outn}}:
      match h:
        case Inl{y}:
          (+e0, r) = y
          asm.sound.go(ds, i, x, s, out, r, Wa.Wasm.fits(pg, Cr.Cir.at(nx), outn), e0, e)
        case Inr{e2}:
          +fits = Wa.Wasm.fits(pg, Cr.Cir.at(nx), outn)
          Empty.absurd(&k: Nat -> {Pg.Program.result(ds, El.Eval.steps(k, ds, Pg.Program.start(i))) == Some{x} : Maybe<&2, List<&2, Word(8n)>>},
            (%Equal.trans(Wa.Wasm.Outcome, Wa.Wasm.Outcome.no_result{},
              Cr.Cir.ended.halt(U32.is_eq(s, 0), U32.is_eq(s, 1), U32.is_eq(s, 2), fits, out), Wa.Wasm.Outcome.result{x},
              Equal.sym(Wa.Wasm.Outcome, Cr.Cir.ended.halt(U32.is_eq(s, 0), U32.is_eq(s, 1), U32.is_eq(s, 2), fits, out),
                Wa.Wasm.Outcome.no_result{}, asm.ended2(s, fits, out, e2)), e) : Asm.nr(_); Unit{}))
    case Cr.Cir.Out.out_of_memory{}:
      Empty.absurd(&k: Nat -> {Pg.Program.result(ds, El.Eval.steps(k, ds, Pg.Program.start(i))) == Some{x} : Maybe<&2, List<&2, Word(8n)>>},
        (%e : Asm.nr(_); Unit{}))
    case Cr.Cir.Out.trap{}:
      Empty.absurd(&k: Nat -> {Pg.Program.result(ds, El.Eval.steps(k, ds, Pg.Program.start(i))) == Some{x} : Maybe<&2, List<&2, Word(8n)>>}, h)
    case Cr.Cir.Out.not_done{}:
      Empty.absurd(&k: Nat -> {Pg.Program.result(ds, El.Eval.steps(k, ds, Pg.Program.start(i))) == Some{x} : Maybe<&2, List<&2, Word(8n)>>},
        (%e : Asm.nr(_); Unit{}))

# a halt 0 with the output o in the memory gives the result o
def asm.halt.res(+s: U32, +nx: U32, +pg: U32, +outn: U32, +out: List<&2, Word(8n)>, +o: List<&2, Word(8n)>, +e0: {s == 0 : U32},
  eo: {List.reverse(&2, Word(8n), out) == o : List<&2, Word(8n)>},
  hf: {Bool.or(Bool.not(U32.is_eq(s, 0)), Wa.Wasm.fits(pg, Cr.Cir.at(nx), outn)) == True{} : Bool}) ->
  {Cr.Cir.ended.halt(U32.is_eq(s, 0), U32.is_eq(s, 1), U32.is_eq(s, 2), Wa.Wasm.fits(pg, Cr.Cir.at(nx), outn), out) ==
    Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome}:
  +fits = Wa.Wasm.fits(pg, Cr.Cir.at(nx), outn)
  Equal.trans(Wa.Wasm.Outcome, Cr.Cir.ended.halt(U32.is_eq(s, 0), U32.is_eq(s, 1), U32.is_eq(s, 2), fits, out),
    Cr.Cir.ended.output(fits, out), Wa.Wasm.Outcome.result{o}, asm.ended0(s, fits, out, e0),
    (%Equal.sym(Bool, fits, True{}, asm.fits0(s, fits, e0, hf)) : {Cr.Cir.ended.output(_, out) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome};
      Equal.cong(List<&2, Word(8n)>, Wa.Wasm.Outcome, y => Wa.Wasm.Outcome.result{y}, List.reverse(&2, Word(8n), out), o, eo)))

# a run that gives the bytes o, or runs out of memory, ends so, when its
# output is in the memory at halt 0
def asm.good.end(+o: List<&2, Word(8n)>, r: Cr.Cir.Out, g: Asm.Good(False{}, o, r), hf: {Me.Fits.halt(r) == True{} : Bool}) ->
  Or({Cr.Cir.ended(r) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome}, {Cr.Cir.ended(r) == Wa.Wasm.Outcome.out_of_memory{} : Wa.Wasm.Outcome}):
  match r:
    case Cr.Cir.Out.next{st}:
      Empty.absurd(Or({Wa.Wasm.Outcome.no_result{} == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome},
        {Wa.Wasm.Outcome.no_result{} == Wa.Wasm.Outcome.out_of_memory{} : Wa.Wasm.Outcome}), g)
    case Cr.Cir.Out.halt{+s, Cr.Cir.State{regs, m, +nx, fi, im, +pg, lim, inp, +out, +outn}}:
      match g:
        case Tuple{+e0, eo}:
          Inl{asm.halt.res(s, nx, pg, outn, out, o, e0, eo, hf)}
    case Cr.Cir.Out.out_of_memory{}:
      Inr{{==}}
    case Cr.Cir.Out.trap{}:
      Empty.absurd(Or({Wa.Wasm.Outcome.trap{} == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome},
        {Wa.Wasm.Outcome.trap{} == Wa.Wasm.Outcome.out_of_memory{} : Wa.Wasm.Outcome}), g)
    case Cr.Cir.Out.not_done{}:
      Empty.absurd(Or({Wa.Wasm.Outcome.not_done{} == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome},
        {Wa.Wasm.Outcome.not_done{} == Wa.Wasm.Outcome.out_of_memory{} : Wa.Wasm.Outcome}), g)

# a run that gives the bytes o ends so, when its output is in the memory
def asm.good.res(+o: List<&2, Word(8n)>, r: Cr.Cir.Out, g: Asm.Good(True{}, o, r), hf: {Me.Fits.halt(r) == True{} : Bool}) ->
  {Cr.Cir.ended(r) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome}:
  match r:
    case Cr.Cir.Out.next{st}:
      Empty.absurd({Wa.Wasm.Outcome.no_result{} == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome}, g)
    case Cr.Cir.Out.halt{+s, Cr.Cir.State{regs, m, +nx, fi, im, +pg, lim, inp, +out, +outn}}:
      match g:
        case Tuple{+e0, eo}:
          asm.halt.res(s, nx, pg, outn, out, o, e0, eo, hf)
    case Cr.Cir.Out.out_of_memory{}:
      Empty.absurd({Wa.Wasm.Outcome.out_of_memory{} == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome}, g)
    case Cr.Cir.Out.trap{}:
      Empty.absurd({Wa.Wasm.Outcome.trap{} == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome}, g)
    case Cr.Cir.Out.not_done{}:
      Empty.absurd({Wa.Wasm.Outcome.not_done{} == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome}, g)

# a fuel that gives o (or out of memory) for the run from the start ends it so
def asm.comp.go(+o: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +k: U32, +pg: U32, +lim: U32, +first: U32,
  g: &r:Nat -> Asm.Good(False{}, o, Cr.Cir.exec(r, Mc.Mach.code(), Asm.St0(ds, first, k, pg, lim, i)))) ->
  &n:Nat -> Or({Cr.Cir.ended(Cr.Cir.exec(n, Mc.Mach.code(), I.St0(Mc.Mach.regs(), Mc.Img.cells(ds), first, k, pg, lim, i))) ==
    Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome},
    {Cr.Cir.ended(Cr.Cir.exec(n, Mc.Mach.code(), I.St0(Mc.Mach.regs(), Mc.Img.cells(ds), first, k, pg, lim, i))) ==
      Wa.Wasm.Outcome.out_of_memory{} : Wa.Wasm.Outcome}):
  match g:
    case Tuple{+n, g1}:
      (n, asm.good.end(o, Cr.Cir.exec(n, Mc.Mach.code(), Asm.St0(ds, first, k, pg, lim, i)), g1,
        Me.code.fits(n, Mc.Img.cells(ds), first, k, pg, lim, i)))

def asm.memo.go(+o: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +k: U32, +pg: U32, +lim: U32, +first: U32,
  g: &r:Nat -> Asm.Good(True{}, o, Cr.Cir.exec(r, Mc.Mach.code(), Asm.St0(ds, first, k, pg, lim, i)))) ->
  &n:Nat -> {Cr.Cir.ended(Cr.Cir.exec(n, Mc.Mach.code(), I.St0(Mc.Mach.regs(), Mc.Img.cells(ds), first, k, pg, lim, i))) ==
    Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome}:
  match g:
    case Tuple{+n, g1}:
      (n, asm.good.res(o, Cr.Cir.exec(n, Mc.Mach.code(), Asm.St0(ds, first, k, pg, lim, i)), g1,
        Me.code.fits(n, Mc.Img.cells(ds), first, k, pg, lim, i)))

# Layer B
# -------
#
# The lemmas of runs_as_eval.bend, with exactly their types.

def asm.safe(+p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +m: U32, +n: Nat,
  +rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  +small: {Mc.Img.small(p, 0) == True{} : Bool}) ->
  {Cr.Cir.result(n, Mc.Mach.code(), Mc.Mach.regs(), Mc.Img.cells(ds), i, m) != Wa.Wasm.Outcome.trap{} : Wa.Wasm.Outcome}:
  asm.res.on(n, Mc.Mach.code(), Mc.Mach.regs(), Mc.Img.cells(ds), i, m, x => {x != Wa.Wasm.Outcome.trap{} : Wa.Wasm.Outcome},
    e => (%e : Asm.nt(_); Unit{}),
    +k => +len => +pg => +lim => +first => +s =>
      asm.safe.end(Cr.Cir.exec(n, Mc.Mach.code(), Asm.St0(ds, first, k, pg, lim, i)), ds, Pg.Program.start(i),
        asm.run.post(n, p, ds, i, m, k, len, pg, lim, first, rd, small, s), Me.code.fits(n, Mc.Img.cells(ds), first, k, pg, lim, i)))

def asm.sound(+p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +m: U32, +n: Nat, +o: List<&2, Word(8n)>,
  +rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  +small: {Mc.Img.small(p, 0) == True{} : Bool},
  e: {Cr.Cir.result(n, Mc.Mach.code(), Mc.Mach.regs(), Mc.Img.cells(ds), i, m) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome}) ->
  &k:Nat -> {Pg.Program.result(ds, El.Eval.steps(k, ds, Pg.Program.start(i))) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}:
  asm.res.on(n, Mc.Mach.code(), Mc.Mach.regs(), Mc.Img.cells(ds), i, m,
    x => {x == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome} ->
      &k:Nat -> {Pg.Program.result(ds, El.Eval.steps(k, ds, Pg.Program.start(i))) == Some{o} : Maybe<&2, List<&2, Word(8n)>>},
    e2 => Empty.absurd(&k:Nat -> {Pg.Program.result(ds, El.Eval.steps(k, ds, Pg.Program.start(i))) == Some{o} : Maybe<&2, List<&2, Word(8n)>>},
      (%e2 : Asm.nr(_); Unit{})),
    +k => +len => +pg => +lim => +first => +s => e2 =>
      asm.sound.end(Cr.Cir.exec(n, Mc.Mach.code(), Asm.St0(ds, first, k, pg, lim, i)), ds, i, o,
        asm.run.post(n, p, ds, i, m, k, len, pg, lim, first, rd, small, s), e2), e)

def asm.complete(+p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +m: U32, +kk: Nat, +o: List<&2, Word(8n)>,
  +rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  +small: {Mc.Img.small(p, 0) == True{} : Bool},
  +e: {Pg.Program.result(ds, El.Eval.steps(kk, ds, Pg.Program.start(i))) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}) ->
  &n:Nat -> Or({Cr.Cir.result(n, Mc.Mach.code(), Mc.Mach.regs(), Mc.Img.cells(ds), i, m) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome},
    {Cr.Cir.result(n, Mc.Mach.code(), Mc.Mach.regs(), Mc.Img.cells(ds), i, m) == Wa.Wasm.Outcome.out_of_memory{} : Wa.Wasm.Outcome}):
  asm.res.ex(Mc.Mach.code(), Mc.Mach.regs(), Mc.Img.cells(ds), i, m,
    x => Or({x == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome}, {x == Wa.Wasm.Outcome.out_of_memory{} : Wa.Wasm.Outcome}),
    Inr{{==}},
    +k => +len => +pg => +lim => +first => +s =>
      asm.comp.go(o, ds, i, k, pg, lim, first, asm.run.done(kk, p, ds, i, m, o, k, len, pg, lim, first, rd, small, s, e)))

def asm.memory(+p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +m: U32, +kk: Nat, +o: List<&2, Word(8n)>,
  +rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  +small: {Mc.Img.small(p, 0) == True{} : Bool},
  +e: {Pg.Program.result(ds, El.Eval.steps(kk, ds, Pg.Program.start(i))) == Some{o} : Maybe<&2, List<&2, Word(8n)>>},
  +big: {Nat.is_le(Pg.Program.need(p, i, kk), Pg.Program.memory(m)) == True{} : Bool}) ->
  &n:Nat -> {Cr.Cir.result(n, Mc.Mach.code(), Mc.Mach.regs(), Mc.Img.cells(ds), i, m) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome}:
  asm.rok.ex(Mc.Mach.code(), Mc.Mach.regs(), Mc.Img.cells(ds), i, m, x => {x == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome},
    Me.start.ok(p, ds, i, m, kk, rd, big),
    +k => +len => +pg => +lim => +first => +s =>
      asm.memo.go(o, ds, i, k, pg, lim, first, asm.run.mem(kk, p, ds, i, m, o, k, len, pg, lim, first, rd, small, s, e, big)))

# B: the machine never makes an access that its module could not make the
# same way
def mach.safe.proof(
  +p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +m: U32, +n: Nat,
  rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  small: {Mc.Img.small(p, 0) == True{} : Bool}
) -> {Cr.Cir.result(n, Mc.Mach.code(), Mc.Mach.regs(), Mc.Img.cells(ds), i, m) != Wa.Wasm.Outcome.trap{} : Wa.Wasm.Outcome}:
  asm.safe(p, ds, i, m, n, rd, small)

# B: a result of the machine is the list of bytes of a value that Eval reaches
def mach.sound.proof(
  +p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +m: U32, +n: Nat, +o: List<&2, Word(8n)>,
  rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  small: {Mc.Img.small(p, 0) == True{} : Bool},
  e: {Cr.Cir.result(n, Mc.Mach.code(), Mc.Mach.regs(), Mc.Img.cells(ds), i, m) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome}
) -> &k:Nat -> {Pg.Program.result(ds, El.Eval.steps(k, ds, Pg.Program.start(i))) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}:
  asm.sound(p, ds, i, m, n, o, rd, small, e)

# B: when Eval reaches a list of bytes, the machine gives it, or runs out of
# memory
def mach.complete.proof(
  +p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +m: U32, +k: Nat, +o: List<&2, Word(8n)>,
  rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  small: {Mc.Img.small(p, 0) == True{} : Bool},
  e: {Pg.Program.result(ds, El.Eval.steps(k, ds, Pg.Program.start(i))) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}
) -> &n:Nat -> Or({Cr.Cir.result(n, Mc.Mach.code(), Mc.Mach.regs(), Mc.Img.cells(ds), i, m) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome},
  {Cr.Cir.result(n, Mc.Mach.code(), Mc.Mach.regs(), Mc.Img.cells(ds), i, m) == Wa.Wasm.Outcome.out_of_memory{} : Wa.Wasm.Outcome}):
  asm.complete(p, ds, i, m, k, o, rd, small, e)

# B: with the memory of AGENTS.md 3.9.1.4, the machine gives the list of bytes
def mach.memory.proof(
  +p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +m: U32, +k: Nat, +o: List<&2, Word(8n)>,
  rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  small: {Mc.Img.small(p, 0) == True{} : Bool},
  e: {Pg.Program.result(ds, El.Eval.steps(k, ds, Pg.Program.start(i))) == Some{o} : Maybe<&2, List<&2, Word(8n)>>},
  big: {Nat.is_le(Pg.Program.need(p, i, k), Pg.Program.memory(m)) == True{} : Bool}
) -> &n:Nat -> {Cr.Cir.result(n, Mc.Mach.code(), Mc.Mach.regs(), Mc.Img.cells(ds), i, m) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome}:
  asm.memory(p, ds, i, m, k, o, rd, small, e, big)
