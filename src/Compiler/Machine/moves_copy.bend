# compiler: layer B, the moves that copy (U12)
# ============================================
#
# mv.ev.unlet, mv.ret.let, mv.ret.app.lam and mv.ret.fun.lam of move_kit.bend: M.data when the
# quantity is 2, M.one, M.copy, then the step.
# Filled by U12; U0 left each as ?TODO.

import Base
import ../../Book/impl.bend as Bk
import ../../Eval/impl.bend as El
import ../../Wasm/impl.bend as Wa
import ../../Program/impl.bend as Pg
import ../Cir/impl.bend as Cr
import ./impl.bend as Mc
import ../need_big.bend as N
import ./definitions.bend as D
import ./statement_runs.bend as X
import ./accounting.bend as A
import ./move_kit.bend as K
import ./heap_ops.bend as U2
import ./copy_bridge.bend as U5
import ./data_check.bend as U6
import ./moves_match.bend as U13
import ./moves_push.bend as U10
import ./swap_moves.bend as U11

# The run of a round's statements
# -------------------------------
#
# Rn: from the state st, the statement s ends, with one fuel F, as MV says of the round from st0 (of
# the term t and the measure w): PostB with no fuel left over (dn is True). rn.step takes the first
# statement of a seq by what its law gives (PostB for any fuel, with its budget, and a fuel that ends
# it) and the rest by Rn; rn.mv gives MV (any fuel, and a fuel that ends) from the run of the round's
# body.

def Rn(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st0: Cr.Cir.State, +t: Bk.Term, +w: Nat,
  s: Cr.Cir.Stmt, st: Cr.Cir.State) -> Type:
  Sigma<&1, &1, Nat, F => D.PostB(True{}, Cr.Cir.exec(F, s, st), s2 => K.MV.next(ds, ks, img, st0, t, w, s2), s2 => st2 => D.HR(ds, t, s2, st2),
    D.Budget(ds, st0, t), D.St.lim(st0))>

# a seq's run, unfolded
def seq.unfold(+f: Nat, +a: Cr.Cir.Stmt, +b: Cr.Cir.Stmt, +st: Cr.Cir.State) ->
  {Cr.Cir.exec(f, Cr.Cir.Stmt.seq{a, b}, st) == Cr.Cir.exec.then(Cr.Cir.exec(f, a, st), t => Cr.Cir.exec(f, b, t)) : Cr.Cir.Out}:
  match f:
    case 0n:
      {==}
    case 1n+p:
      {==}

# PostB with no fuel left over: the run ends, and the same PostB
def postb.end2(o: Cr.Cir.Out, -Q: Cr.Cir.State -> Type, -H: U32 -> Cr.Cir.State -> Type, -B: Nat, -lim: U32,
  h: D.PostB(True{}, o, Q, H, B, lim)) -> Sigma<&1, &1, D.Ends(o), _ => D.PostB(True{}, o, Q, H, B, lim)>:
  match o:
    case Cr.Cir.Out.next{st}:
      (Unit{}, h)
    case Cr.Cir.Out.halt{s, st}:
      (Unit{}, h)
    case Cr.Cir.Out.out_of_memory{}:
      (Unit{}, h)
    case Cr.Cir.Out.trap{}:
      (Unit{}, h)
    case Cr.Cir.Out.not_done{}:
      Empty.absurd(Sigma<&1, &1, D.Ends(Cr.Cir.Out.not_done{}), _ => D.PostB(True{}, Cr.Cir.Out.not_done{}, Q, H, B, lim)>, h)

# a then b, from the run of b with F2 that ends it after the first statement a ended with F1 into st1
def rn.seq.go(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st0: Cr.Cir.State, +t: Bk.Term, +w: Nat,
  +F1: Nat, +F2: Nat, +a: Cr.Cir.Stmt, +b: Cr.Cir.Stmt, +st: Cr.Cir.State, +st1: Cr.Cir.State,
  +eo: {Cr.Cir.exec(F1, a, st) == Cr.Cir.Out.next{st1} : Cr.Cir.Out},
  pr: Sigma<&1, &1, D.Ends(Cr.Cir.exec(F2, b, st1)), _ => D.PostB(True{}, Cr.Cir.exec(F2, b, st1), s2 => K.MV.next(ds, ks, img, st0, t, w, s2),
    s2 => st2 => D.HR(ds, t, s2, st2), D.Budget(ds, st0, t), D.St.lim(st0))>) ->
  Rn(ds, ks, img, st0, t, w, Cr.Cir.Stmt.seq{a, b}, st):
  match pr:
    case Tuple{+d2, p2}:
      +F = Nat.add(F1, F2)
      +e1 = D.mono(F1, F, a, st, N.le_add_r(F1, F2), (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec(F1, a, st), Cr.Cir.Out.next{st1}, eo) : D.Ends(_); Unit{}))
      +e2 = D.mono(F2, F, b, st1, N.le_add_l(F1, F2), d2)
      (F, (%X.rw.seq(F, a, b, st, st1, Equal.trans(Cr.Cir.Out, Cr.Cir.exec(F, a, st), Cr.Cir.exec(F1, a, st), Cr.Cir.Out.next{st1},
        Equal.sym(Cr.Cir.Out, Cr.Cir.exec(F1, a, st), Cr.Cir.exec(F, a, st), e1), eo)) :
          D.PostB(True{}, _, s2 => K.MV.next(ds, ks, img, st0, t, w, s2), s2 => st2 => D.HR(ds, t, s2, st2), D.Budget(ds, st0, t), D.St.lim(st0));
        (%e2 : D.PostB(True{}, _, s2 => K.MV.next(ds, ks, img, st0, t, w, s2), s2 => st2 => D.HR(ds, t, s2, st2), D.Budget(ds, st0, t), D.St.lim(st0)); p2)))

def rn.seq.next(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st0: Cr.Cir.State, +t: Bk.Term, +w: Nat,
  +F1: Nat, +a: Cr.Cir.Stmt, +b: Cr.Cir.Stmt, +st: Cr.Cir.State, +st1: Cr.Cir.State,
  +eo: {Cr.Cir.exec(F1, a, st) == Cr.Cir.Out.next{st1} : Cr.Cir.Out}, gx: Rn(ds, ks, img, st0, t, w, b, st1)) ->
  Rn(ds, ks, img, st0, t, w, Cr.Cir.Stmt.seq{a, b}, st):
  match gx:
    case Tuple{+F2, p2}:
      rn.seq.go(ds, ks, img, st0, t, w, F1, F2, a, b, st, st1, eo,
        postb.end2(Cr.Cir.exec(F2, b, st1), s2 => K.MV.next(ds, ks, img, st0, t, w, s2), s2 => st2 => D.HR(ds, t, s2, st2),
          D.Budget(ds, st0, t), D.St.lim(st0), p2))

# a then b, by the outcome o of a with the fuel F1 (the law's PostB, with no fuel left over)
def rn.seq.o(o: Cr.Cir.Out, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st0: Cr.Cir.State,
  +t: Bk.Term, +w: Nat, +F1: Nat, +a: Cr.Cir.Stmt, +b: Cr.Cir.Stmt, +st: Cr.Cir.State, -Q: Cr.Cir.State -> Type, +Ba: Nat,
  +eo: {Cr.Cir.exec(F1, a, st) == o : Cr.Cir.Out}, p1: D.PostB(True{}, o, Q, s => st2 => Empty, Ba, D.St.lim(st0)),
  hb: N.Le(Ba, D.Budget(ds, st0, t)), k: @st1: Cr.Cir.State -> Q(st1) -> Rn(ds, ks, img, st0, t, w, b, st1)) ->
  Rn(ds, ks, img, st0, t, w, Cr.Cir.Stmt.seq{a, b}, st):
  match o:
    case Cr.Cir.Out.next{+st1}:
      rn.seq.next(ds, ks, img, st0, t, w, F1, a, b, st, st1, eo, k(st1, p1))
    case Cr.Cir.Out.halt{s, st1}:
      Empty.absurd(Rn(ds, ks, img, st0, t, w, Cr.Cir.Stmt.seq{a, b}, st), p1)
    case Cr.Cir.Out.out_of_memory{}:
      (F1, (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec(F1, Cr.Cir.Stmt.seq{a, b}, st), Cr.Cir.exec.then(Cr.Cir.exec(F1, a, st), t2 => Cr.Cir.exec(F1, b, t2)),
          seq.unfold(F1, a, b, st)) :
            D.PostB(True{}, _, s2 => K.MV.next(ds, ks, img, st0, t, w, s2), s2 => st2 => D.HR(ds, t, s2, st2), D.Budget(ds, st0, t), D.St.lim(st0));
        (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec(F1, a, st), Cr.Cir.Out.out_of_memory{}, eo) :
            D.PostB(True{}, Cr.Cir.exec.then(_, t2 => Cr.Cir.exec(F1, b, t2)), s2 => K.MV.next(ds, ks, img, st0, t, w, s2),
              s2 => st2 => D.HR(ds, t, s2, st2), D.Budget(ds, st0, t), D.St.lim(st0));
          N.le_trans(1n+D.Lim.bytes(D.St.lim(st0)), Ba, D.Budget(ds, st0, t), p1, hb))))
    case Cr.Cir.Out.trap{}:
      Empty.absurd(Rn(ds, ks, img, st0, t, w, Cr.Cir.Stmt.seq{a, b}, st), p1)
    case Cr.Cir.Out.not_done{}:
      Empty.absurd(Rn(ds, ks, img, st0, t, w, Cr.Cir.Stmt.seq{a, b}, st), p1)

# the first statement of a seq, by its law (PostB for any fuel, with the budget Ba, and a fuel that ends it),
# then the rest
def rn.step(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st0: Cr.Cir.State, +t: Bk.Term, +w: Nat,
  +a: Cr.Cir.Stmt, +b: Cr.Cir.Stmt, +st: Cr.Cir.State, -Q: Cr.Cir.State -> Type, +Ba: Nat,
  hp: @f: Nat -> D.PostB(False{}, Cr.Cir.exec(f, a, st), Q, s => st2 => Empty, Ba, D.St.lim(st0)), hb: N.Le(Ba, D.Budget(ds, st0, t)),
  +hd: D.Ex(Nat, f1 => D.Ends(Cr.Cir.exec(f1, a, st))),
  k: @st1: Cr.Cir.State -> Q(st1) -> Rn(ds, ks, img, st0, t, w, b, st1)) ->
  Rn(ds, ks, img, st0, t, w, Cr.Cir.Stmt.seq{a, b}, st):
  +f1 = D.Ex.fst(Nat, f => D.Ends(Cr.Cir.exec(f, a, st)), hd)
  rn.seq.o(Cr.Cir.exec(f1, a, st), ds, ks, img, st0, t, w, f1, a, b, st, Q, Ba, {==},
    D.postb.ends(Cr.Cir.exec(f1, a, st), Q, s => st2 => Empty, Ba, D.St.lim(st0), hp(f1), D.Ex.snd(Nat, f => D.Ends(Cr.Cir.exec(f, a, st)), hd)), hb, k)

# a set of the register r to the value v of e
def rn.set(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st0: Cr.Cir.State, +t: Bk.Term, +w: Nat,
  +r: Nat, +e: Cr.Cir.Expr, +rest: Cr.Cir.Stmt, +st: Cr.Cir.State, +v: U32,
  ev: {Cr.Cir.eval(e, st) == Some{v} : Maybe<&2, U32>}, hl: {List.length(&2, U32, X.X.regs(st)) == 63n : Nat},
  hr: {Nat.is_lt(r, 63n) == True{} : Bool}, h: Rn(ds, ks, img, st0, t, w, rest, X.X.setst(st, r, v))) ->
  Rn(ds, ks, img, st0, t, w, Cr.Cir.Stmt.seq{Cr.Cir.Stmt.set{r, e}, rest}, st):
  match h:
    case Tuple{+F, p}:
      (F, (%X.rw.seq(F, Cr.Cir.Stmt.set{r, e}, rest, st, X.X.setst(st, r, v), X.run.set(F, r, e, st, v, ev, hl, hr)) :
        D.PostB(True{}, _, s2 => K.MV.next(ds, ks, img, st0, t, w, s2), s2 => st2 => D.HR(ds, t, s2, st2), D.Budget(ds, st0, t), D.St.lim(st0)); p))

# the end of the statements: the state is the round's next state
def rn.nop(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st0: Cr.Cir.State, +t: Bk.Term, +w: Nat,
  +st: Cr.Cir.State, h: K.MV.next(ds, ks, img, st0, t, w, st)) -> Rn(ds, ks, img, st0, t, w, Cr.Cir.Stmt.nop{}, st):
  (0n, (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec(0n, Cr.Cir.Stmt.nop{}, st), Cr.Cir.Out.next{st}, X.run.nop(0n, st)) :
    D.PostB(True{}, _, s2 => K.MV.next(ds, ks, img, st0, t, w, s2), s2 => st2 => D.HR(ds, t, s2, st2), D.Budget(ds, st0, t), D.St.lim(st0)); h))

# a halt: the round halts as HR says
def rn.halt(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st0: Cr.Cir.State, +t: Bk.Term, +w: Nat,
  +x: U32, +st: Cr.Cir.State, h: D.HR(ds, t, x, st)) -> Rn(ds, ks, img, st0, t, w, Cr.Cir.Stmt.halt{x}, st):
  (0n, (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec(0n, Cr.Cir.Stmt.halt{x}, st), Cr.Cir.Out.halt{x, st}, K.eq.halt(0n, x, st)) :
    D.PostB(True{}, _, s2 => K.MV.next(ds, ks, img, st0, t, w, s2), s2 => st2 => D.HR(ds, t, s2, st2), D.Budget(ds, st0, t), D.St.lim(st0)); h))

# an if whose condition is not 0: its first branch; whose condition is 0: its second
def rn.if.t(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st0: Cr.Cir.State, +t: Bk.Term, +w: Nat,
  +c: Cr.Cir.Expr, +y: Cr.Cir.Stmt, +n: Cr.Cir.Stmt, +st: Cr.Cir.State, -v: U32,
  ev: {Cr.Cir.eval(c, st) == Some{v} : Maybe<&2, U32>}, nz: {U32.is_zero(v) == False{} : Bool}, h: Rn(ds, ks, img, st0, t, w, y, st)) ->
  Rn(ds, ks, img, st0, t, w, Cr.Cir.Stmt.if{c, y, n}, st):
  match h:
    case Tuple{+F, p}:
      (F, (%X.rw.if.t(F, c, y, n, st, v, ev, nz) :
        D.PostB(True{}, _, s2 => K.MV.next(ds, ks, img, st0, t, w, s2), s2 => st2 => D.HR(ds, t, s2, st2), D.Budget(ds, st0, t), D.St.lim(st0)); p))

def rn.if.e(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st0: Cr.Cir.State, +t: Bk.Term, +w: Nat,
  +c: Cr.Cir.Expr, +y: Cr.Cir.Stmt, +n: Cr.Cir.Stmt, +st: Cr.Cir.State,
  ev: {Cr.Cir.eval(c, st) == Some{0} : Maybe<&2, U32>}, h: Rn(ds, ks, img, st0, t, w, n, st)) ->
  Rn(ds, ks, img, st0, t, w, Cr.Cir.Stmt.if{c, y, n}, st):
  match h:
    case Tuple{+F, p}:
      (F, (%X.rw.if.e(F, c, y, n, st, ev) :
        D.PostB(True{}, _, s2 => K.MV.next(ds, ks, img, st0, t, w, s2), s2 => st2 => D.HR(ds, t, s2, st2), D.Budget(ds, st0, t), D.St.lim(st0)); p))

# From one fuel to any fuel
# -------------------------

# PostB with no fuel left over gives PostB with some left over
def postb.dn(o: Cr.Cir.Out, -Q: Cr.Cir.State -> Type, -H: U32 -> Cr.Cir.State -> Type, -B: Nat, -lim: U32,
  h: D.PostB(True{}, o, Q, H, B, lim)) -> D.PostB(False{}, o, Q, H, B, lim):
  match o:
    case Cr.Cir.Out.next{st}:
      h
    case Cr.Cir.Out.halt{s, st}:
      h
    case Cr.Cir.Out.out_of_memory{}:
      h
    case Cr.Cir.Out.trap{}:
      h
    case Cr.Cir.Out.not_done{}:
      Empty.absurd(D.PostB(False{}, Cr.Cir.Out.not_done{}, Q, H, B, lim), h)

# the run with the fuel f <= F that ends in the outcome o gives the PostB of the run with F
def post.all.end(o: Cr.Cir.Out, +f: Nat, +F: Nat, +s: Cr.Cir.Stmt, +st: Cr.Cir.State, -Q: Cr.Cir.State -> Type,
  -H: U32 -> Cr.Cir.State -> Type, -B: Nat, -lim: U32, +le: N.Le(f, F), +eo: {Cr.Cir.exec(f, s, st) == o : Cr.Cir.Out}, d: D.Ends(o),
  p: D.PostB(True{}, Cr.Cir.exec(F, s, st), Q, H, B, lim)) -> D.PostB(False{}, o, Q, H, B, lim):
  +e = D.mono(f, F, s, st, le, (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, s, st), o, eo) : D.Ends(_); d))
  postb.dn(o, Q, H, B, lim, (%Equal.trans(Cr.Cir.Out, Cr.Cir.exec(F, s, st), Cr.Cir.exec(f, s, st), o, Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, s, st), Cr.Cir.exec(F, s, st), e), eo) :
    D.PostB(True{}, _, Q, H, B, lim); p))

# a fuel f <= F: the run is not done, or ends as that of F does
def post.all.low(o: Cr.Cir.Out, +f: Nat, +F: Nat, +s: Cr.Cir.Stmt, +st: Cr.Cir.State, -Q: Cr.Cir.State -> Type,
  -H: U32 -> Cr.Cir.State -> Type, -B: Nat, -lim: U32, +le: N.Le(f, F), +eo: {Cr.Cir.exec(f, s, st) == o : Cr.Cir.Out},
  p: D.PostB(True{}, Cr.Cir.exec(F, s, st), Q, H, B, lim)) -> D.PostB(False{}, o, Q, H, B, lim):
  match o:
    case Cr.Cir.Out.next{st2}:
      post.all.end(Cr.Cir.Out.next{st2}, f, F, s, st, Q, H, B, lim, le, eo, Unit{}, p)
    case Cr.Cir.Out.halt{x, st2}:
      post.all.end(Cr.Cir.Out.halt{x, st2}, f, F, s, st, Q, H, B, lim, le, eo, Unit{}, p)
    case Cr.Cir.Out.out_of_memory{}:
      post.all.end(Cr.Cir.Out.out_of_memory{}, f, F, s, st, Q, H, B, lim, le, eo, Unit{}, p)
    case Cr.Cir.Out.trap{}:
      post.all.end(Cr.Cir.Out.trap{}, f, F, s, st, Q, H, B, lim, le, eo, Unit{}, p)
    case Cr.Cir.Out.not_done{}:
      Unit{}

# any fuel f: its run ends as that of F does (f >= F), or is not done, or ends as that of F does
def post.all.cmp(c: Bool, +f: Nat, +F: Nat, +s: Cr.Cir.Stmt, +st: Cr.Cir.State, -Q: Cr.Cir.State -> Type,
  -H: U32 -> Cr.Cir.State -> Type, -B: Nat, -lim: U32, eb: {Nat.is_le(F, f) == c : Bool}, +d: D.Ends(Cr.Cir.exec(F, s, st)),
  p: D.PostB(True{}, Cr.Cir.exec(F, s, st), Q, H, B, lim)) -> D.PostB(False{}, Cr.Cir.exec(f, s, st), Q, H, B, lim):
  match c:
    case True{}:
      +e = D.mono(F, f, s, st, N.toLe(F, f, eb), d)
      (%e : D.PostB(False{}, _, Q, H, B, lim); postb.dn(Cr.Cir.exec(F, s, st), Q, H, B, lim, p))
    case False{}:
      post.all.low(Cr.Cir.exec(f, s, st), f, F, s, st, Q, H, B, lim, U5.le.not(F, f, eb), {==}, p)

# a run that ends with the fuel F as MV says gives MV
def rn.mv.go(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st0: Cr.Cir.State, +t: Bk.Term, +w: Nat,
  +F: Nat, pr: Sigma<&1, &1, D.Ends(Cr.Cir.exec(F, D.B.body(), st0)), _ => D.PostB(True{}, Cr.Cir.exec(F, D.B.body(), st0),
    s2 => K.MV.next(ds, ks, img, st0, t, w, s2), s2 => st2 => D.HR(ds, t, s2, st2), D.Budget(ds, st0, t), D.St.lim(st0))>) ->
  K.MV(ds, ks, img, st0, t, w):
  match pr:
    case Tuple{+d, p}:
      (+f => post.all.cmp(Nat.is_le(F, f), f, F, D.B.body(), st0, s2 => K.MV.next(ds, ks, img, st0, t, w, s2),
          s2 => st2 => D.HR(ds, t, s2, st2), D.Budget(ds, st0, t), D.St.lim(st0), {==}, d, p),
        (F, d))

def rn.mv(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st0: Cr.Cir.State, +t: Bk.Term, +w: Nat,
  h: Rn(ds, ks, img, st0, t, w, D.B.body(), st0)) -> K.MV(ds, ks, img, st0, t, w):
  match h:
    case Tuple{+F, p}:
      rn.mv.go(ds, ks, img, st0, t, w, F, postb.end2(Cr.Cir.exec(F, D.B.body(), st0), s2 => K.MV.next(ds, ks, img, st0, t, w, s2),
        s2 => st2 => D.HR(ds, t, s2, st2), D.Budget(ds, st0, t), D.St.lim(st0), p))

def K.mv.ev.unlet(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, v, b, iv, hv, hq, hfv):
  ?TODO

def K.mv.ret.app.lam(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, r, h, kind, q, k, a, b, iv, hk, hs, hfv):
  ?TODO

def K.mv.ret.fun.lam(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, r, h, focus, q, k, b, iv, hfv):
  ?TODO

def K.mv.ret.let(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, focus, q, k, a, b, iv, hfv):
  ?TODO

# generated by tools/gen/gen.ts rn Mc.M.ev.let() --br e
def gen.unlet.s1(+ds: List<&2, Bk.Def>,
  +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>,
  +st0: Cr.Cir.State,
  +t: Bk.Term,
  +w: Nat,
  +foc: U32,
  +sp: U32,
  +pend: U32,
  +r4: U32,
  +r5: U32,
  +r6: U32,
  +r7: U32,
  +r8: U32,
  +r9: U32,
  +r10: U32,
  +r11: U32,
  +r12: U32,
  +r13: U32,
  +r14: U32,
  +r15: U32,
  +r16: U32,
  +r17: U32,
  +r18: U32,
  +r19: U32,
  +r20: U32,
  +r21: U32,
  +r22: U32,
  +r23: U32,
  +r24: U32,
  +r25: U32,
  +r26: U32,
  +r27: U32,
  +r28: U32,
  +r29: U32,
  +r30: U32,
  +r31: U32,
  +r32: U32,
  +r33: U32,
  +r34: U32,
  +r35: U32,
  +r36: U32,
  +r37: U32,
  +r38: U32,
  +r39: U32,
  +r40: U32,
  +r41: U32,
  +r42: U32,
  +r43: U32,
  +r44: U32,
  +r45: U32,
  +r46: U32,
  +r47: U32,
  +r48: U32,
  +r49: U32,
  +r50: U32,
  +r51: U32,
  +r52: U32,
  +r53: U32,
  +r54: U32,
  +r55: U32,
  +r56: U32,
  +r57: U32,
  +r58: U32,
  +r59: U32,
  +r60: U32,
  +r61: U32,
  +r62: U32,
  +m: Cr.Cir.Cells,
  +nx: U32,
  +fi: U32,
  +im: U32,
  +pg: U32,
  +lim: U32,
  +inp: List<&2, Word(8n)>,
  +hc0: {Cr.Cir.is_cell(foc, im, fi, nx) == True{} : Bool},
  +hz1: {Wa.Wasm.op(Wa.Wasm.Op.ne{}, Wa.Wasm.op(Wa.Wasm.Op.and{}, Wa.Wasm.op(Wa.Wasm.Op.shr_u{}, Cr.Cir.Cell.get(0n, Cr.Cir.Cells.get(m, foc)), 6), 3), 0) == 0 : U32},
  k: Rn(ds, ks, img, st0, t, w, X.sel.b(X.sel.e(Mc.M.ev.let())), X.X.setst(X.X.st([foc, 0, sp, pend, r4, r5, r6, r7, foc, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62], m, nx, fi, im, pg, lim, inp), 12n, Cr.Cir.Cell.get(2n, Cr.Cir.Cells.get(m, foc))))) ->
  Rn(ds, ks, img, st0, t, w, Mc.M.ev.let(), X.X.st([foc, 0, sp, pend, r4, r5, r6, r7, foc, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62], m, nx, fi, im, pg, lim, inp)):
  +s0 = X.X.st([foc, 0, sp, pend, r4, r5, r6, r7, foc, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62], m, nx, fi, im, pg, lim, inp)
  +s1 = X.X.setst(s0, 12n, Cr.Cir.Cell.get(2n, Cr.Cir.Cells.get(m, foc)))
  rn.if.e(ds, ks, img, st0, t, w, X.sel.c(Mc.M.ev.let()), X.sel.t(Mc.M.ev.let()), X.sel.e(Mc.M.ev.let()), s0, (%hz1 : {Cr.Cir.eval(X.sel.c(Mc.M.ev.let()), s0) == Some{_} : Maybe<&2, U32>}; X.ev.op(Wa.Wasm.Op.ne{}, Mc.M.q(Mc.M.g(Mc.R.c())), Mc.M.c(0), s0, Wa.Wasm.op(Wa.Wasm.Op.and{}, Wa.Wasm.op(Wa.Wasm.Op.shr_u{}, Cr.Cir.Cell.get(0n, Cr.Cir.Cells.get(m, foc)), 6), 3), 0, X.ev.op(Wa.Wasm.Op.and{}, Mc.M.shr(Mc.M.f(0n, Mc.M.g(Mc.R.c())), Mc.M.c(6)), Mc.M.c(3), s0, Wa.Wasm.op(Wa.Wasm.Op.shr_u{}, Cr.Cir.Cell.get(0n, Cr.Cir.Cells.get(m, foc)), 6), 3, X.ev.op(Wa.Wasm.Op.shr_u{}, Mc.M.f(0n, Mc.M.g(Mc.R.c())), Mc.M.c(6), s0, Cr.Cir.Cell.get(0n, Cr.Cir.Cells.get(m, foc)), 6, X.ev.fld(0n, Mc.M.g(Mc.R.c()), s0, foc, {==}, hc0), {==}), {==}), {==})),
   rn.set(ds, ks, img, st0, t, w, 12n, Mc.M.f(2n, Mc.M.g(Mc.R.c())), X.sel.b(X.sel.e(Mc.M.ev.let())), s0, Cr.Cir.Cell.get(2n, Cr.Cir.Cells.get(m, foc)), X.ev.fld(2n, Mc.M.g(Mc.R.c()), s0, foc, {==}, hc0), {==}, {==},
    k))

# Rn of a statement that runs as another, for any fuel
def rn.eq(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st0: Cr.Cir.State, +t: Bk.Term, +w: Nat,
  +s: Cr.Cir.Stmt, +st: Cr.Cir.State, +s2: Cr.Cir.Stmt, +st2: Cr.Cir.State,
  e: @f: Nat -> {Cr.Cir.exec(f, s, st) == Cr.Cir.exec(f, s2, st2) : Cr.Cir.Out}, h: Rn(ds, ks, img, st0, t, w, s2, st2)) ->
  Rn(ds, ks, img, st0, t, w, s, st):
  match h:
    case Tuple{+F, p}:
      (F, (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec(F, s, st), Cr.Cir.exec(F, s2, st2), e(F)) :
        D.PostB(True{}, _, s3 => K.MV.next(ds, ks, img, st0, t, w, s3), s3 => st3 => D.HR(ds, t, s3, st3), D.Budget(ds, st0, t), D.St.lim(st0)); p))

# mv.ev.unlet: M.ev's tests reach M.ev.let, whose test of q (dead) takes the else branch; y gets the value's cell
def unlet.disp(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32, +r4: U32, +r5: U32, +r6: U32, +r7: U32, +r8: U32, +r9: U32, +r10: U32, +r11: U32, +r12: U32, +r13: U32, +r14: U32, +r15: U32, +r16: U32, +r17: U32, +r18: U32, +r19: U32, +r20: U32, +r21: U32, +r22: U32, +r23: U32, +r24: U32, +r25: U32, +r26: U32, +r27: U32, +r28: U32, +r29: U32, +r30: U32, +r31: U32, +r32: U32, +r33: U32, +r34: U32, +r35: U32, +r36: U32, +r37: U32, +r38: U32, +r39: U32, +r40: U32, +r41: U32, +r42: U32, +r43: U32, +r44: U32, +r45: U32, +r46: U32, +r47: U32, +r48: U32, +r49: U32, +r50: U32, +r51: U32, +r52: U32, +r53: U32, +r54: U32, +r55: U32, +r56: U32, +r57: U32, +r58: U32, +r59: U32, +r60: U32, +r61: U32, +r62: U32,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat, +q: Bk.Quan, +v: Bk.Term, +b: Bk.Term,
  +nd: D.Nd(ds, im, fi, nx, foc, Cr.Cir.Cells.get(m, foc), Bk.Term.Let{q, v, b}, D.A.tag(Bk.Term.Let{q, v, b})), +tb: D.Tbl(m, im, fi, nx),
  +hv: {D.Fl(m, foc, 256) == False{} : Bool}, +hqs: {D.QnW(D.Fd(0n, m, foc)) == 0 : U32},
  k: Rn(ds, ks, img, D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), t, w, X.sel.b(X.sel.e(Mc.M.ev.let())),
    X.X.setst(X.X.st([foc, 0, sp, pend, r4, r5, r6, r7, foc, r9, D.TgW(D.Fd(0n, m, foc)), r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62], m, nx, fi, im, pg, lim, inp), 12n, Cr.Cir.Cell.get(2n, Cr.Cir.Cells.get(m, foc))))) ->
  Rn(ds, ks, img, D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), t, w, D.B.body(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)):
  +F = {Bk.Term.Let{q, v, b} : Bk.Term}
  +ST0 = {D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp) : Cr.Cir.State}
  +st2 = {K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp) : Cr.Cir.State}
  +hc = U10.nd.cell(ds, im, fi, nx, foc, Cr.Cir.Cells.get(m, foc), F, D.A.tag(F), nd)
  rn.eq(ds, ks, img, ST0, t, w, D.B.body(), ST0, Mc.M.ev.let(), st2,
    +f => Equal.trans(Cr.Cir.Out, Cr.Cir.exec(f, D.B.body(), ST0), Cr.Cir.exec(f, K.B.else(), st2), Cr.Cir.exec(f, Mc.M.ev.let(), st2),
      U10.ev.pre.E(f, ds, ks, img, foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp, F, nd, tb, hv, {==}),
      U10.br.let(f, st2, D.Fd(0n, m, foc), U10.nd.tag(ds, im, fi, nx, foc, Cr.Cir.Cells.get(m, foc), F, D.A.tag(F), nd), {==})),
    gen.unlet.s1(ds, ks, img, ST0, t, w, foc, sp, pend, r4, r5, r6, r7, r8, r9, D.TgW(D.Fd(0n, m, foc)), r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp, hc,
      (%Equal.sym(U32, D.QnW(D.Fd(0n, m, foc)), 0, hqs) : {Wa.Wasm.op(Wa.Wasm.Op.ne{}, _, 0) == 0 : U32}; {==}), k))

# M.one(y): M.make of a K.arg cell z for the value's cell yv
# ---------------------------------------------------------
#
# M.alloc(wa) gives the cell z, of zeros (alloc.post, keeping the registers
# focus, mode, sp, c and y); M.make's five stores make it {41, 1, yv, 0, 0}.

# what alloc.post gives for M.alloc(wa)
def AlQ1(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>,
  +sp: U32, +ps: List<&2, U32>, st2: Cr.Cir.State) -> Type:
  D.P2(D.Same(regs, fi, im, lim, inp, [0n, 1n, 2n, 8n, 12n], st2),
    D.Ex(U32, z => D.Ex(U32, pend2 => D.Ex(List<&2, U32>, ps2 =>
      D.P2(D.Reg(st2, 22n, z), D.P2(D.Reg(st2, 3n, pend2),
      D.P2({Cr.Cir.Cells.get(D.St.cells(st2), z) == Cr.Cir.Cell.zero() : Cr.Cir.Cell},
      D.P2({D.Own(fi, D.St.next(st2), z) == True{} : Bool}, D.P2({D.Mem(ps2, z) == False{} : Bool},
      D.P2({Bool.or(D.Mem(ps, z), U32.is_eq(z, nx)) == True{} : Bool},
      D.P2({Bool.or(Bool.and(D.Mem(ps, z), U32.is_eq(D.St.next(st2), nx)),
           Bool.and(D.Pend.none(ps), Bool.and(U32.is_eq(z, nx), U32.is_eq(D.St.next(st2), U32.inc(nx))))) == True{} : Bool},
      D.P2(D.Ex(List<&2, D.W1>, ws => D.P2({D.St.cells(st2) == Cr.Cir.Cells.set(D.Put1(ws, m), z, Cr.Cir.Cell.zero()) : Cr.Cir.Cells},
        {D.Took(ws, ps, m) == True{} : Bool})),
      D.P2({D.PsSub(ps2, ps, m) == True{} : Bool},
      D.P2({D.Ptr(Nat.sub(U32.to_nat(D.St.next(st2)), U32.to_nat(fi)), D.St.cells(st2), fi, ps2, D.Rt.cells(os), z) == 0n : Nat},
      D.P2(D.HSK(True{}, ds, ks, img, D.St.cells(st2), D.St.next(st2), fi, im, os, bs, fs, sp, pend2, ps2),
        D.Ex(List<&2, D.Rt>, zs2 => D.AccK(True{}, ds, ks, img, D.St.cells(st2), D.St.next(st2), fi, im, os, Con{D.TmpE{z, Nil{}}, Nil{}}, sp, fs, ps2, zs2))))))))))))))))) & D.AlFr(m, ps, nx, st2)

# the state after M.make's stores: the cell z is {41, 1, yv, 0, 0}
def MkQ(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>,
  +sp: U32, +ps: List<&2, U32>, +yv: U32, st: Cr.Cir.State) -> Data:
  D.Ex(List<&2, U32>, regs1 => D.Ex(Cr.Cir.Cells, m1 => D.Ex(U32, nx1 => D.Ex(U32, pg1 => D.Ex(U32, z => D.Ex(U32, pend2 =>
  D.Ex(List<&2, U32>, ps2 => D.Ex(List<&2, D.Rt>, zs2 =>
    D.P2({st == Cr.Cir.State{regs1, Cr.Cir.Cells.set(m1, z, Cr.Cir.Cell{41, 1, yv, 0, 0}), nx1, fi, im, pg1, lim, inp, Nil{}, 0} : Cr.Cir.State},
    D.P2({List.length(&2, U32, regs1) == 63n : Nat},
    D.P2(D.Kept(regs, regs1, [0n, 1n, 2n, 8n, 12n]),
    D.P2({List.get(&2, U32, regs1, 22n) == Some{z} : Maybe<&2, U32>},
    D.P2({List.get(&2, U32, regs1, 3n) == Some{pend2} : Maybe<&2, U32>},
    D.P2({Cr.Cir.Cells.get(m1, z) == Cr.Cir.Cell.zero() : Cr.Cir.Cell},
    D.P2({D.Own(fi, nx1, z) == True{} : Bool},
    D.P2({D.Mem(ps2, z) == False{} : Bool},
    D.P2({Bool.or(Bool.and(D.Mem(ps, z), U32.is_eq(nx1, nx)), Bool.and(D.Pend.none(ps), Bool.and(U32.is_eq(z, nx), U32.is_eq(nx1, U32.inc(nx))))) == True{} : Bool},
    D.P2(D.Ex(List<&2, D.W1>, ws => D.P2({m1 == Cr.Cir.Cells.set(D.Put1(ws, m), z, Cr.Cir.Cell.zero()) : Cr.Cir.Cells}, {D.Took(ws, ps, m) == True{} : Bool})),
    D.P2({D.Ptr(Nat.sub(U32.to_nat(nx1), U32.to_nat(fi)), m1, fi, ps2, D.Rt.cells(os), z) == 0n : Nat},
    D.P2(D.HSK(True{}, ds, ks, img, m1, nx1, fi, im, os, bs, fs, sp, pend2, ps2),
      D.AccK(True{}, ds, ks, img, m1, nx1, fi, im, os, Con{D.TmpE{z, Nil{}}, Nil{}}, sp, fs, ps2, zs2)))))))))))))))))))))

# M.alloc(wa) with a cell in the pend list takes no new cell
def na.alloc22() -> {U10.NA(K.stmt.then(Mc.M.alloc(22n))) == True{} : Bool}:
  {==}

def noom.alloc22(+f: Nat, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32,
  +inp: List<&2, Word(8n)>, +pend: U32, h3: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>},
  hne: {U32.is_eq(pend, 0) == False{} : Bool}) ->
  D.NoOom(Cr.Cir.exec(f, Mc.M.alloc(22n), Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0})):
  +st = {Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0} : Cr.Cir.State}
  +ec = X.ev.op(Wa.Wasm.Op.ne{}, Mc.M.g(3n), Mc.M.c(0), st, pend, 0, h3, {==})
  +nz = {(%Equal.sym(Bool, U32.is_eq(pend, 0), False{}, hne) : {U32.is_zero(Bool.to_u32(Bool.not(_))) == False{} : Bool}; {==}) :
    {U32.is_zero(Wa.Wasm.op(Wa.Wasm.Op.ne{}, pend, 0)) == False{} : Bool}}
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, Mc.M.alloc(22n), st), Cr.Cir.exec(f, K.stmt.then(Mc.M.alloc(22n)), st),
    D.eq.if.t(f, K.stmt.cond(Mc.M.alloc(22n)), K.stmt.then(Mc.M.alloc(22n)), K.stmt.else(Mc.M.alloc(22n)), st, Wa.Wasm.op(Wa.Wasm.Op.ne{}, pend, 0), ec, nz)) :
    D.NoOom(_)
  U10.noom.na(f, K.stmt.then(Mc.M.alloc(22n)), st, na.alloc22())

# M.alloc(wa), within the budget B: a new cell only when the pend list is empty
def alloc22.run(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>,
  +sp: U32, +pend: U32, +ps: List<&2, U32>, +zs: List<&2, D.Rt>, +B: Nat,
  hroom: Or(N.Le(Nat.mul(20n, Nat.add(U32.to_nat(nx), 1n)), B), {U32.is_eq(pend, 0) == False{} : Bool}),
  +hs: D.HSK(True{}, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps),
  +hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, os, Nil{}, sp, fs, ps, zs),
  +hl: {List.length(&2, U32, regs) == 63n : Nat}, +h3: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>}) ->
  D.PostB(False{}, Cr.Cir.exec(f, Mc.M.alloc(22n), Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0}),
    st2 => AlQ1(ds, ks, img, regs, m, nx, fi, im, lim, inp, os, bs, fs, sp, ps, st2), s => st2 => Empty, B, lim):
  match hroom:
    case Inl{hle}:
      D.postb.wk(False{}, Cr.Cir.exec(f, Mc.M.alloc(22n), Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0}),
        st2 => AlQ1(ds, ks, img, regs, m, nx, fi, im, lim, inp, os, bs, fs, sp, ps, st2), s => st2 => Empty, Nat.mul(20n, Nat.add(U32.to_nat(nx), 1n)), B, lim,
        D.alloc.post(f, True{}, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, 22n, [0n, 1n, 2n, 8n, 12n], os, bs, fs, sp, pend, ps, Nil{}, zs,
          hs, hac, hl, h3, {==}, {==}), hle)
    case Inr{hne}:
      U10.postb.noom(False{}, Cr.Cir.exec(f, Mc.M.alloc(22n), Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0}),
        st2 => AlQ1(ds, ks, img, regs, m, nx, fi, im, lim, inp, os, bs, fs, sp, ps, st2), s => st2 => Empty, Nat.mul(20n, Nat.add(U32.to_nat(nx), 1n)), B, lim,
        D.alloc.post(f, True{}, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, 22n, [0n, 1n, 2n, 8n, 12n], os, bs, fs, sp, pend, ps, Nil{}, zs,
          hs, hac, hl, h3, {==}, {==}), noom.alloc22(f, regs, m, nx, fi, im, pg, lim, inp, pend, h3, hne))

# M.make's five stores at the cell z of zeros: the cell {41, 1, yv, 0, 0}
def one.cells(+m: Cr.Cir.Cells, +z: U32, +yv: U32, hz: {Cr.Cir.Cells.get(m, z) == Cr.Cir.Cell.zero() : Cr.Cir.Cell}) ->
  {X.X.put(X.X.put(X.X.put(X.X.put(X.X.put(m, 0n, z, 41), 1n, z, 1), 2n, z, yv), 3n, z, 0), 4n, z, 0) ==
    Cr.Cir.Cells.set(m, z, Cr.Cir.Cell{41, 1, yv, 0, 0}) : Cr.Cir.Cells}:
  +P4 = X.X.put(X.X.put(X.X.put(X.X.put(m, 0n, z, 41), 1n, z, 1), 2n, z, yv), 3n, z, 0)
  +C = {Cr.Cir.Cell{41, 1, yv, 0, 0} : Cr.Cir.Cell}
  Equal.trans(Cr.Cir.Cells, X.X.put(P4, 4n, z, 0), X.X.put(Cr.Cir.Cells.set(m, z, C), 4n, z, 0), Cr.Cir.Cells.set(m, z, C),
    Equal.cong(Cr.Cir.Cells, Cr.Cir.Cells, y => X.X.put(y, 4n, z, 0), P4, Cr.Cir.Cells.set(m, z, C), U10.push.cells(m, z, 41, 1, yv, 0, hz)),
    Equal.sym(Cr.Cir.Cells, Cr.Cir.Cells.set(m, z, C), X.X.put(Cr.Cir.Cells.set(m, z, C), 4n, z, 0), X.Ce.put_set(m, z, C, 4n, 0)))

# the register y of the registers that M.alloc(wa) keeps
def kept5.y(-regs: List<&2, U32>, -regs1: List<&2, U32>, h: D.Kept(regs, regs1, [0n, 1n, 2n, 8n, 12n])) ->
  {List.get(&2, U32, regs1, 12n) == List.get(&2, U32, regs, 12n) : Maybe<&2, U32>}:
  match h:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}:
      e

# the stores of M.make, from alloc.post's facts
def one.k2(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>,
  +sp: U32, +ps: List<&2, U32>, +yv: U32, +B: Nat, +h12: {List.get(&2, U32, regs, 12n) == Some{yv} : Maybe<&2, U32>},
  +st1: Cr.Cir.State, hparts: D.P2({List.length(&2, U32, D.St.regs(st1)) == 63n : Nat}, D.Kept(regs, D.St.regs(st1), [0n, 1n, 2n, 8n, 12n])),
  +hsame: D.Same(regs, fi, im, lim, inp, [0n, 1n, 2n, 8n, 12n], st1), +z: U32, +pend2: U32, +ps2: List<&2, U32>,
  +h22: D.Reg(st1, 22n, z), +h3b: D.Reg(st1, 3n, pend2), +hzero: {Cr.Cir.Cells.get(D.St.cells(st1), z) == Cr.Cir.Cell.zero() : Cr.Cir.Cell},
  +hown: {D.Own(fi, D.St.next(st1), z) == True{} : Bool}, +hmz: {D.Mem(ps2, z) == False{} : Bool},
  +hnx: {Bool.or(Bool.and(D.Mem(ps, z), U32.is_eq(D.St.next(st1), nx)),
    Bool.and(D.Pend.none(ps), Bool.and(U32.is_eq(z, nx), U32.is_eq(D.St.next(st1), U32.inc(nx))))) == True{} : Bool},
  +hws: D.Ex(List<&2, D.W1>, ws => D.P2({D.St.cells(st1) == Cr.Cir.Cells.set(D.Put1(ws, m), z, Cr.Cir.Cell.zero()) : Cr.Cir.Cells}, {D.Took(ws, ps, m) == True{} : Bool})),
  +hptr: {D.Ptr(Nat.sub(U32.to_nat(D.St.next(st1)), U32.to_nat(fi)), D.St.cells(st1), fi, ps2, D.Rt.cells(os), z) == 0n : Nat},
  +hsk: D.HSK(True{}, ds, ks, img, D.St.cells(st1), D.St.next(st1), fi, im, os, bs, fs, sp, pend2, ps2), +zs2: List<&2, D.Rt>,
  +hac2: D.AccK(True{}, ds, ks, img, D.St.cells(st1), D.St.next(st1), fi, im, os, Con{D.TmpE{z, Nil{}}, Nil{}}, sp, fs, ps2, zs2)) ->
  D.PostB(False{}, Cr.Cir.exec(f, X.sel.b(Mc.M.make(22n, Mc.M.c(41), Mc.M.g(12n), Mc.M.c(0), Mc.M.c(0))), st1),
    st => MkQ(ds, ks, img, regs, m, nx, fi, im, lim, inp, os, bs, fs, sp, ps, yv, st), s => st2 => Empty, B, lim):
  match hparts:
    case Tuple{+hl1, +hkept}:
      +regs1 = D.St.regs(st1)
      +m1 = D.St.cells(st1)
      +nx1 = D.St.next(st1)
      +pg1 = U10.St.pg(st1)
      +t0 = {Cr.Cir.State{regs1, m1, nx1, fi, im, pg1, lim, inp, Nil{}, 0} : Cr.Cir.State}
      +hc = U10.own.cell(fi, nx1, im, z, hown)
      +ey = Equal.trans(Maybe<&2, U32>, List.get(&2, U32, regs1, 12n), List.get(&2, U32, regs, 12n), Some{yv}, kept5.y(regs, regs1, hkept), h12)
      +t1 = X.X.store(t0, 0n, z, 41)
      +t2 = X.X.store(t1, 1n, z, 1)
      +t3 = X.X.store(t2, 2n, z, yv)
      +t4 = X.X.store(t3, 3n, z, 0)
      +t5 = X.X.store(t4, 4n, z, 0)
      +q1 = X.sel.b(Mc.M.make(22n, Mc.M.c(41), Mc.M.g(12n), Mc.M.c(0), Mc.M.c(0)))
      +q2 = X.sel.b(q1)
      +q3 = X.sel.b(q2)
      +q4 = X.sel.b(q3)
      +q5 = X.sel.b(q4)
      +e1 = X.run.store(f, 0n, Mc.M.g(22n), Mc.M.c(41), t0, z, 41, h22, {==}, hc)
      +e2 = X.run.store(f, 1n, Mc.M.g(22n), Mc.M.c(1), t1, z, 1, h22, {==}, hc)
      +e3 = X.run.store(f, 2n, Mc.M.g(22n), Mc.M.g(12n), t2, z, yv, h22, ey, hc)
      +e4 = X.run.store(f, 3n, Mc.M.g(22n), Mc.M.c(0), t3, z, 0, h22, {==}, hc)
      +e5 = X.run.store(f, 4n, Mc.M.g(22n), Mc.M.c(0), t4, z, 0, h22, {==}, hc)
      +eq = {(%X.rw.seq(f, X.sel.a(q1), q2, t0, t1, e1) : {_ == Cr.Cir.Out.next{t5} : Cr.Cir.Out};
        %X.rw.seq(f, X.sel.a(q2), q3, t1, t2, e2) : {_ == Cr.Cir.Out.next{t5} : Cr.Cir.Out};
        %X.rw.seq(f, X.sel.a(q3), q4, t2, t3, e3) : {_ == Cr.Cir.Out.next{t5} : Cr.Cir.Out};
        %X.rw.seq(f, X.sel.a(q4), q5, t3, t4, e4) : {_ == Cr.Cir.Out.next{t5} : Cr.Cir.Out};
        %X.rw.seq(f, X.sel.a(q5), X.sel.b(q5), t4, t5, e5) : {_ == Cr.Cir.Out.next{t5} : Cr.Cir.Out};
        X.run.nop(f, t5)) : {Cr.Cir.exec(f, q1, t0) == Cr.Cir.Out.next{t5} : Cr.Cir.Out}}
      +est = Equal.cong(Cr.Cir.Cells, Cr.Cir.State, y => Cr.Cir.State{regs1, y, nx1, fi, im, pg1, lim, inp, Nil{}, 0},
        X.X.put(X.X.put(X.X.put(X.X.put(X.X.put(m1, 0n, z, 41), 1n, z, 1), 2n, z, yv), 3n, z, 0), 4n, z, 0),
        Cr.Cir.Cells.set(m1, z, Cr.Cir.Cell{41, 1, yv, 0, 0}), one.cells(m1, z, yv, hzero))
      %Equal.sym(Cr.Cir.State, st1, t0, U10.same.st(regs, fi, im, lim, inp, [0n, 1n, 2n, 8n, 12n], st1, hsame)) :
        D.PostB(False{}, Cr.Cir.exec(f, q1, _), st => MkQ(ds, ks, img, regs, m, nx, fi, im, lim, inp, os, bs, fs, sp, ps, yv, st), s => st2 => Empty, B, lim)
      %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, q1, t0), Cr.Cir.Out.next{t5}, eq) :
        D.PostB(False{}, _, st => MkQ(ds, ks, img, regs, m, nx, fi, im, lim, inp, os, bs, fs, sp, ps, yv, st), s => st2 => Empty, B, lim)
      (regs1, (m1, (nx1, (pg1, (z, (pend2, (ps2, (zs2, (est, (hl1, (hkept, (h22, (h3b, (hzero, (hown, (hmz, (hnx, (hws, (hptr, (hsk, hac2))))))))))))))))))))

def one.k(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>,
  +sp: U32, +ps: List<&2, U32>, +yv: U32, +B: Nat, +h12: {List.get(&2, U32, regs, 12n) == Some{yv} : Maybe<&2, U32>},
  +st1: Cr.Cir.State, qa: AlQ1(ds, ks, img, regs, m, nx, fi, im, lim, inp, os, bs, fs, sp, ps, st1)) ->
  D.PostB(False{}, Cr.Cir.exec(f, X.sel.b(Mc.M.make(22n, Mc.M.c(41), Mc.M.g(12n), Mc.M.c(0), Mc.M.c(0))), st1),
    st => MkQ(ds, ks, img, regs, m, nx, fi, im, lim, inp, os, bs, fs, sp, ps, yv, st), s => st2 => Empty, B, lim):
  match qa:
    case Tuple{Tuple{+hsame, Tuple{+z, Tuple{+pend2, Tuple{+ps2, Tuple{+h22, Tuple{+h3b, Tuple{+hzero, Tuple{+hown, Tuple{+hmz, Tuple{_, Tuple{+hnx, Tuple{+hws, Tuple{_, Tuple{+hptr, Tuple{+hsk, Tuple{+zs2, hac2}}}}}}}}}}}}}}}}, _}:
      one.k2(f, ds, ks, img, regs, m, nx, fi, im, lim, inp, os, bs, fs, sp, ps, yv, B, h12, st1, U10.same.parts(regs, fi, im, lim, inp, [0n, 1n, 2n, 8n, 12n], st1, hsame), hsame,
        z, pend2, ps2, h22, h3b, hzero, hown, hmz, hnx, hws, hptr, hsk, zs2, hac2)

# M.make of M.one's cell: M.alloc(wa), then the stores
def one.make(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>,
  +sp: U32, +pend: U32, +ps: List<&2, U32>, +zs: List<&2, D.Rt>, +yv: U32, +B: Nat,
  hroom: Or(N.Le(Nat.mul(20n, Nat.add(U32.to_nat(nx), 1n)), B), {U32.is_eq(pend, 0) == False{} : Bool}),
  +hs: D.HSK(True{}, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps),
  +hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, os, Nil{}, sp, fs, ps, zs),
  +hl: {List.length(&2, U32, regs) == 63n : Nat}, +h3: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>},
  +h12: {List.get(&2, U32, regs, 12n) == Some{yv} : Maybe<&2, U32>}) ->
  D.PostB(False{}, Cr.Cir.exec(f, Mc.M.make(22n, Mc.M.c(41), Mc.M.g(12n), Mc.M.c(0), Mc.M.c(0)), Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0}),
    st => MkQ(ds, ks, img, regs, m, nx, fi, im, lim, inp, os, bs, fs, sp, ps, yv, st), s => st2 => Empty, B, lim):
  D.postb.seq(f, False{}, Mc.M.alloc(22n), X.sel.b(Mc.M.make(22n, Mc.M.c(41), Mc.M.g(12n), Mc.M.c(0), Mc.M.c(0))), Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0},
    st2 => AlQ1(ds, ks, img, regs, m, nx, fi, im, lim, inp, os, bs, fs, sp, ps, st2), st => MkQ(ds, ks, img, regs, m, nx, fi, im, lim, inp, os, bs, fs, sp, ps, yv, st),
    s => st2 => Empty, s => st2 => Empty, B, lim,
    alloc22.run(f, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, os, bs, fs, sp, pend, ps, zs, B, hroom, hs, hac, hl, h3), s => st2 => e => e,
    +st1 => qa => one.k(f, ds, ks, img, regs, m, nx, fi, im, lim, inp, os, bs, fs, sp, ps, yv, B, h12, st1, qa))

# M.one's cell, after its store of field 1: {41, 0, yv, 0, 0} (a K.arg of Q0, the end of its chain); cenv
# gets it, clen 1. HSK and AccK hold with z the one temporary
def OneQ(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>,
  +sp: U32, +ps: List<&2, U32>, +yv: U32, st: Cr.Cir.State) -> Data:
  D.Ex(List<&2, U32>, regs1 => D.Ex(Cr.Cir.Cells, m1 => D.Ex(U32, nx1 => D.Ex(U32, pg1 => D.Ex(U32, z => D.Ex(U32, pend2 =>
  D.Ex(List<&2, U32>, ps2 => D.Ex(List<&2, D.Rt>, zs2 =>
    D.P2({st == Cr.Cir.State{List.set(&2, U32, List.set(&2, U32, regs1, 36n, z), 37n, 1), Cr.Cir.Cells.set(m1, z, Cr.Cir.Cell{41, 0, yv, 0, 0}), nx1, fi, im, pg1, lim, inp, Nil{}, 0} : Cr.Cir.State},
    D.P2({List.length(&2, U32, regs1) == 63n : Nat},
    D.P2(D.Kept(regs, regs1, [0n, 1n, 2n, 8n, 12n]),
    D.P2({List.get(&2, U32, regs1, 22n) == Some{z} : Maybe<&2, U32>},
    D.P2({List.get(&2, U32, regs1, 3n) == Some{pend2} : Maybe<&2, U32>},
    D.P2({D.Own(fi, nx1, z) == True{} : Bool},
    D.P2({D.Mem(ps2, z) == False{} : Bool},
    D.P2({Bool.or(U32.is_eq(nx1, nx), Bool.and(D.Pend.none(ps), U32.is_eq(nx1, U32.inc(nx)))) == True{} : Bool},
    D.P2(N.Le(D.Stat(Nat.sub(U32.to_nat(nx1), U32.to_nat(fi)), Cr.Cir.Cells.set(m1, z, Cr.Cir.Cell{41, 0, yv, 0, 0}), fi), D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi)),
    D.P2(D.HSK(True{}, ds, ks, img, Cr.Cir.Cells.set(m1, z, Cr.Cir.Cell{41, 0, yv, 0, 0}), nx1, fi, im, os, bs, fs, sp, pend2, ps2),
      D.AccK(True{}, ds, ks, img, Cr.Cir.Cells.set(m1, z, Cr.Cir.Cell{41, 0, yv, 0, 0}), nx1, fi, im, os, Con{D.TmpE{z, Nil{}}, Nil{}}, sp, fs, ps2, zs2)))))))))))))))))))

# a K.arg cell with no flag OWNED holds no pointer
def fs.arg(+m1: Cr.Cir.Cells, +ps: List<&2, U32>, +z: U32, +yv: U32) ->
  {D.Fs(Cr.Cir.Cells.set(m1, z, Cr.Cir.Cell{41, 0, yv, 0, 0}), ps, z) == Nil{} : List<&2, U32>}:
  %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m1, z, Cr.Cir.Cell{41, 0, yv, 0, 0}), z), Cr.Cir.Cell{41, 0, yv, 0, 0},
      X.Ce.get_set(m1, z, Cr.Cir.Cell{41, 0, yv, 0, 0})) :
    {Bool.pick(List<&2, U32>, U32.is_lt(U32.and(Cr.Cir.Cell.get(0n, _), 63), 19),
            D.Fs.term(D.Fd(2n, Cr.Cir.Cells.set(m1, z, Cr.Cir.Cell{41, 0, yv, 0, 0}), U32.add(272, U32.and(Cr.Cir.Cell.get(0n, _), 63))), Cr.Cir.Cell.get(2n, _), Cr.Cir.Cell.get(3n, _), Cr.Cir.Cell.get(4n, _)),
            Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_le(32, U32.and(Cr.Cir.Cell.get(0n, _), 63)), U32.is_le(U32.and(Cr.Cir.Cell.get(0n, _), 63), 40)), Bool.not(D.Mem(ps, z))),
              Con{Cr.Cir.Cell.get(2n, _), D.Fs.opt(U32.is_eq(U32.and(Cr.Cir.Cell.get(0n, _), 63), 38), Cr.Cir.Cell.get(3n, _), Nil{})},
              Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_eq(U32.and(Cr.Cir.Cell.get(0n, _), 63), 41), D.FlW(Cr.Cir.Cell.get(0n, _), 4096)), Bool.not(D.Mem(ps, z))),
                [Cr.Cir.Cell.get(2n, _)], Nil{}))) == Nil{} : List<&2, U32>}
  {==}

# HSK's parts: the borrowed terms are held, and the image
def hsk.held(-dk: Bool, -ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -m: Cr.Cir.Cells, -nx: U32,
  -fi: U32, -im: U32, -os: List<&2, D.Rt>, -bs: List<&2, D.Rt>, -fs: List<&2, D.AF>, -sp: U32, -pend: U32, -ps: List<&2, U32>,
  h: D.HSK(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps)) -> D.Held(m, os, bs):
  match h:
    case Tuple{_, Tuple{_, Tuple{e, _}}}:
      e

def hsk.io(-dk: Bool, -ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -m: Cr.Cir.Cells, -nx: U32,
  -fi: U32, -im: U32, -os: List<&2, D.Rt>, -bs: List<&2, D.Rt>, -fs: List<&2, D.AF>, -sp: U32, -pend: U32, -ps: List<&2, U32>,
  h: D.HSK(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps)) -> D.ImgOKK(dk, ds, ks, img, m, im, fi, nx):
  match h:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, e}}}}}:
      e

# the rest of M.one after M.make: the store of field 1, cenv and clen
def one.fin(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>,
  +sp: U32, +ps: List<&2, U32>, +yv: U32, +B: Nat, +hfn: {U32.is_le(fi, nx) == True{} : Bool},
  +st5: Cr.Cir.State, qm: MkQ(ds, ks, img, regs, m, nx, fi, im, lim, inp, os, bs, fs, sp, ps, yv, st5)) ->
  D.PostB(False{}, Cr.Cir.exec(f, X.sel.b(Mc.M.one(Mc.R.y())), st5),
    st => OneQ(ds, ks, img, regs, m, nx, fi, im, lim, inp, os, bs, fs, sp, ps, yv, st), s => st2 => Empty, B, lim):
  match qm:
    case Tuple{+regs1, Tuple{+m1, Tuple{+nx1, Tuple{+pg1, Tuple{+z, Tuple{+pend2, Tuple{+ps2, Tuple{+zs2, Tuple{+est, Tuple{+hl1,
      Tuple{+hkept, Tuple{+h22, Tuple{+h3b, Tuple{+hzero, Tuple{+hown, Tuple{+hmz, Tuple{+hnx, Tuple{+hws, Tuple{+hptr, Tuple{+hsk, hac2}}}}}}}}}}}}}}}}}}}}:
      +C1 = {Cr.Cir.Cell{41, 1, yv, 0, 0} : Cr.Cir.Cell}
      +XC = {Cr.Cir.Cell{41, 0, yv, 0, 0} : Cr.Cir.Cell}
      +S5 = {Cr.Cir.State{regs1, Cr.Cir.Cells.set(m1, z, C1), nx1, fi, im, pg1, lim, inp, Nil{}, 0} : Cr.Cir.State}
      +hc = U10.own.cell(fi, nx1, im, z, hown)
      +T1 = X.X.store(S5, 1n, z, 0)
      +T2 = X.X.setst(T1, 36n, z)
      +T3 = X.X.setst(T2, 37n, 1)
      +q1 = X.sel.b(Mc.M.one(Mc.R.y()))
      +q2 = X.sel.b(q1)
      +q3 = X.sel.b(q2)
      +e1 = X.run.store(f, 1n, Mc.M.g(22n), Mc.M.c(0), S5, z, 0, h22, {==}, hc)
      +e2 = X.run.set(f, 36n, Mc.M.g(22n), T1, z, h22, hl1, {==})
      +e3 = X.run.set(f, 37n, Mc.M.c(1), T2, 1, {==}, X.L.len(regs1, 36n, z, 63n, hl1), {==})
      +eq = {(%X.rw.seq(f, X.sel.a(q1), q2, S5, T1, e1) : {_ == Cr.Cir.Out.next{T3} : Cr.Cir.Out};
        %X.rw.seq(f, X.sel.a(q2), q3, T1, T2, e2) : {_ == Cr.Cir.Out.next{T3} : Cr.Cir.Out};
        %X.rw.seq(f, X.sel.a(q3), X.sel.b(q3), T2, T3, e3) : {_ == Cr.Cir.Out.next{T3} : Cr.Cir.Out};
        X.run.nop(f, T3)) : {Cr.Cir.exec(f, q1, S5) == Cr.Cir.Out.next{T3} : Cr.Cir.Out}}
      +est3 = Equal.cong(Cr.Cir.Cells, Cr.Cir.State, y => Cr.Cir.State{List.set(&2, U32, List.set(&2, U32, regs1, 36n, z), 37n, 1), y, nx1, fi, im, pg1, lim, inp, Nil{}, 0},
        X.X.put(Cr.Cir.Cells.set(m1, z, C1), 1n, z, 0), Cr.Cir.Cells.set(m1, z, XC),
        Equal.sym(Cr.Cir.Cells, Cr.Cir.Cells.set(m1, z, XC), X.X.put(Cr.Cir.Cells.set(m1, z, C1), 1n, z, 0), X.Ce.put_set(m1, z, C1, 1n, 0)))
      +hn2 = U10.next.of(D.Mem(ps, z), U32.is_eq(nx1, nx), D.Pend.none(ps), U32.is_eq(z, nx), U32.is_eq(nx1, U32.inc(nx)), hnx)
      +hsm = K.stat.make(m, nx, fi, ps, z, nx1, m1, XC, {==}, hfn, hws, hnx, hown)
      +io = hsk.io(True{}, ds, ks, img, m1, nx1, fi, im, os, bs, fs, sp, pend2, ps2, hsk)
      +hst = D.store.post(True{}, ds, ks, img, m1, nx1, fi, im, Nil{}, os, bs, fs, sp, pend2, ps2, z, XC, [D.TmpE{z, Nil{}}], zs2,
        hsk, hac2, {==}, hsk.held(True{}, ds, ks, img, m1, nx1, fi, im, os, bs, fs, sp, pend2, ps2, hsk), hown, hmz, U10.zero.st(m1, z, hzero),
        U10.zero.tg(m1, z, hzero), hptr, U10.fs.zero(m1, ps2, z, hzero, U10.tbl.z(m1, im, fi, nx1, D.img.tbl(True{}, ds, ks, img, m1, im, fi, nx1, io))),
        {==}, {==}, fs.arg(m1, ps2, z, yv))
      %Equal.sym(Cr.Cir.State, st5, S5, est) :
        D.PostB(False{}, Cr.Cir.exec(f, q1, _), st => OneQ(ds, ks, img, regs, m, nx, fi, im, lim, inp, os, bs, fs, sp, ps, yv, st), s => st2 => Empty, B, lim)
      %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, q1, S5), Cr.Cir.Out.next{T3}, eq) :
        D.PostB(False{}, _, st => OneQ(ds, ks, img, regs, m, nx, fi, im, lim, inp, os, bs, fs, sp, ps, yv, st), s => st2 => Empty, B, lim)
      (regs1, (m1, (nx1, (pg1, (z, (pend2, (ps2, (zs2, (est3, (hl1, (hkept, (h22, (h3b, (hown, (hmz, (hn2, (hsm, hst)))))))))))))))))

# M.one(y), with the value's cell yv in y
def one.post(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>,
  +sp: U32, +pend: U32, +ps: List<&2, U32>, +zs: List<&2, D.Rt>, +yv: U32, +B: Nat,
  hroom: Or(N.Le(Nat.mul(20n, Nat.add(U32.to_nat(nx), 1n)), B), {U32.is_eq(pend, 0) == False{} : Bool}),
  +hs: D.HSK(True{}, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps),
  +hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, os, Nil{}, sp, fs, ps, zs),
  +hl: {List.length(&2, U32, regs) == 63n : Nat}, +h3: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>},
  +h12: {List.get(&2, U32, regs, 12n) == Some{yv} : Maybe<&2, U32>}) ->
  D.PostB(False{}, Cr.Cir.exec(f, Mc.M.one(Mc.R.y()), Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0}),
    st => OneQ(ds, ks, img, regs, m, nx, fi, im, lim, inp, os, bs, fs, sp, ps, yv, st), s => st2 => Empty, B, lim):
  D.postb.seq(f, False{}, Mc.M.make(22n, Mc.M.c(41), Mc.M.g(12n), Mc.M.c(0), Mc.M.c(0)), X.sel.b(Mc.M.one(Mc.R.y())), Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0},
    st => MkQ(ds, ks, img, regs, m, nx, fi, im, lim, inp, os, bs, fs, sp, ps, yv, st), st => OneQ(ds, ks, img, regs, m, nx, fi, im, lim, inp, os, bs, fs, sp, ps, yv, st),
    s => st2 => Empty, s => st2 => Empty, B, lim,
    one.make(f, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, os, bs, fs, sp, pend, ps, zs, yv, B, hroom, hs, hac, hl, h3, h12), s => st2 => e => e,
    +st5 => qm => one.fin(f, ds, ks, img, regs, m, nx, fi, im, lim, inp, os, bs, fs, sp, ps, yv, B,
      K.hsk.fin(True{}, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps, hs), st5, qm))

# M.one's cell is the chain of one K.arg (Ag)
# -------------------------------------------
#
# The value's cell yv, borrowed during M.one (a node of an owned root's term),
# stands for v in the cell's field 2: the locals' chain for M.copy.

# a field of a cell set to the value X
def ga.fd(+M: Cr.Cir.Cells, +z: U32, +X: Cr.Cir.Cell, +k: Nat, e: {Cr.Cir.Cells.get(M, z) == X : Cr.Cir.Cell}) ->
  {D.Fd(k, M, z) == Cr.Cir.Cell.get(k, X) : U32}:
  Equal.cong(Cr.Cir.Cell, U32, c => Cr.Cir.Cell.get(k, c), Cr.Cir.Cells.get(M, z), X, e)

# a or b, then c or d false: a or (b or (False or False))
def or.ab0(a: Bool, b: Bool, h: {Bool.or(a, b) == True{} : Bool}) -> {Bool.or(a, Bool.or(b, Bool.or(False{}, False{}))) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      match b:
        case True{}:
          {==}
        case False{}:
          h

# HSK's parts
def hsk.bs1(-dk: Bool, -ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -m: Cr.Cir.Cells, -nx: U32,
  -fi: U32, -im: U32, -os: List<&2, D.Rt>, -c: U32, -u: Bk.Term, -bs: List<&2, D.Rt>, -fs: List<&2, D.AF>, -sp: U32, -pend: U32, -ps: List<&2, U32>,
  h: D.HSK(dk, ds, ks, img, m, nx, fi, im, os, Con{D.Rt{c, u}, bs}, fs, sp, pend, ps)) -> D.IsK(dk, ds, m, im, fi, nx, ks, img, c, u):
  match h:
    case Tuple{_, Tuple{Tuple{e, _}, _}}:
      e

def hsk.heap(-dk: Bool, -ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -m: Cr.Cir.Cells, -nx: U32,
  -fi: U32, -im: U32, -os: List<&2, D.Rt>, -bs: List<&2, D.Rt>, -fs: List<&2, D.AF>, -sp: U32, -pend: U32, -ps: List<&2, U32>,
  h: D.HSK(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps)) -> D.Heap(m, nx, fi, im, D.Rt.cells(os), pend, ps):
  match h:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}:
      e

def held1(-m: Cr.Cir.Cells, -os: List<&2, D.Rt>, -c: U32, -u: Bk.Term, -bs: List<&2, D.Rt>, h: D.Held(m, os, Con{D.Rt{c, u}, bs})) ->
  {Bool.or(D.Fl(m, c, 1024), D.Nodes(os, m, c)) == True{} : Bool}:
  match h:
    case Tuple{e, _}:
      e

# a held cell is STATIC or out of the pend list
def held.np(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>, +c: U32,
  +hs: D.HSK(True{}, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps), hn: {Bool.or(D.Fl(m, c, 1024), D.Nodes(os, m, c)) == True{} : Bool}) ->
  {Bool.or(D.Fl(m, c, 1024), Bool.not(D.Mem(ps, c))) == True{} : Bool}:
  +P = D.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, D.Rt.cells(os), c)
  D.or.cases(D.Fl(m, c, 1024), Nat.is_lt(0n, P), {Bool.or(D.Fl(m, c, 1024), Bool.not(D.Mem(ps, c))) == True{} : Bool},
    D.held.ptr(True{}, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps, c, hs, hn),
    e => D.or.l(D.Fl(m, c, 1024), Bool.not(D.Mem(ps, c)), e),
    e => D.or.r(D.Fl(m, c, 1024), Bool.not(D.Mem(ps, c)),
      (%Equal.sym(Bool, D.Mem(ps, c), False{}, U2.notin.ps(D.Mem(ps, c), ps, m, fi, nx, D.Rt.cells(os), c, {==},
          D.heap.pend(m, nx, fi, im, D.Rt.cells(os), pend, ps, hsk.heap(True{}, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps, hs)), e)) :
        {Bool.not(_) == True{} : Bool}; {==})))

# M.one's cell z, {41, 0, yv, 0, 0}, with yv borrowed for v: the chain of one argument v of Q0
def one.ag(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m1: Cr.Cir.Cells, +nx1: U32, +fi: U32, +im: U32,
  +os: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +pend2: U32, +ps2: List<&2, U32>, +z: U32, +yv: U32, +v: Bk.Term,
  +hsk: D.HSK(True{}, ds, ks, img, Cr.Cir.Cells.set(m1, z, Cr.Cir.Cell{41, 0, yv, 0, 0}), nx1, fi, im, os, [D.Rt{yv, v}], fs, sp, pend2, ps2),
  +hown: {D.Own(fi, nx1, z) == True{} : Bool}, +hmz: {D.Mem(ps2, z) == False{} : Bool}) ->
  D.Ag(ds, Cr.Cir.Cells.set(m1, z, Cr.Cir.Cell{41, 0, yv, 0, 0}), im, fi, nx1, ks, img, ps2, os, Nil{}, z, [El.Arg{Bk.Quan.Q0{}, v}]):
  +XC = {Cr.Cir.Cell{41, 0, yv, 0, 0} : Cr.Cir.Cell}
  +M3 = Cr.Cir.Cells.set(m1, z, XC)
  +gs = X.Ce.get_set(m1, z, XC)
  +e0 = Equal.sym(U32, D.Fd(0n, M3, z), 41, ga.fd(M3, z, XC, 0n, gs))
  +e1 = Equal.sym(U32, D.Fd(1n, M3, z), 0, ga.fd(M3, z, XC, 1n, gs))
  +e2 = Equal.sym(U32, D.Fd(2n, M3, z), yv, ga.fd(M3, z, XC, 2n, gs))
  +io = hsk.io(True{}, ds, ks, img, M3, nx1, fi, im, os, [D.Rt{yv, v}], fs, sp, pend2, ps2, hsk)
  +lo = U10.img.lo(True{}, ds, ks, img, M3, im, fi, nx1, io)
  +hh = held1(M3, os, yv, v, Nil{}, hsk.held(True{}, ds, ks, img, M3, nx1, fi, im, os, [D.Rt{yv, v}], fs, sp, pend2, ps2, hsk))
  +c1 = U10.own.nz(fi, nx1, im, z, U10.p2.fst.b(U32.is_le(290, im), U32.is_lt(im, fi), lo), U10.p2.snd.b(U32.is_le(290, im), U32.is_lt(im, fi), lo), hown)
  +c2 = U10.own.cell(fi, nx1, im, z, hown)
  +c4 = {(%e0 : {U32.is_ne(U32.and(_, 1024), 0) == False{} : Bool}; {==}) : {D.Fl(M3, z, 1024) == False{} : Bool}}
  +c6 = {(%e0 : {U32.and(_, 63) == 41 : U32}; {==}) : {D.Tg(M3, z) == 41 : U32}}
  +c7 = {(%e0 : {D.QnW(_) == Mc.Img.quan(Bk.Quan.Q0{}) : U32}; {==}) : D.Qs(Cr.Cir.Cells.get(M3, z), Bk.Quan.Q0{})}
  +c8 = {(%e0 : {Bool.or(Bool.not(U32.is_ne(U32.and(_, 2048), 0)), El.Eval.vals(ds, v, False{})) == True{} : Bool}; {==}) :
    {Bool.or(Bool.not(D.Fl(M3, z, 2048)), El.Eval.vals(ds, v, False{})) == True{} : Bool}}
  +c9 = {(%e0 : {Bool.or(Bool.not(U32.is_ne(U32.and(_, 4096), 0)), D.Term.is_var(v)) == True{} : Bool}; {==}) :
    {Bool.or(Bool.not(D.Fl(M3, z, 4096)), D.Term.is_var(v)) == True{} : Bool}}
  +c10 = {(%e2 : D.Is(ds, M3, im, fi, nx1, ks, img, _, v); hsk.bs1(True{}, ds, ks, img, M3, nx1, fi, im, os, yv, v, Nil{}, fs, sp, pend2, ps2, hsk)) :
    D.Is(ds, M3, im, fi, nx1, ks, img, D.Fd(2n, M3, z), v)}
  +c11 = {(%e0 : {Bool.or(U32.is_ne(U32.and(_, 4096), 0), Bool.or(D.Fl(M3, D.Fd(2n, M3, z), 1024), Bool.or(D.Nodes(os, M3, D.Fd(2n, M3, z)),
        Bool.or(D.Mem(Nil{}, D.Fd(2n, M3, z)), D.Mem(D.Ag.vars(Nil{}, M3, D.Fd(1n, M3, z)), D.Fd(2n, M3, z)))))) == True{} : Bool};
      %e2 : {Bool.or(D.Fl(M3, _, 1024), Bool.or(D.Nodes(os, M3, _), Bool.or(D.Mem(Nil{}, _), D.Mem(D.Ag.vars(Nil{}, M3, D.Fd(1n, M3, z)), _)))) == True{} : Bool};
      or.ab0(D.Fl(M3, yv, 1024), D.Nodes(os, M3, yv), hh)) :
    {Bool.or(D.Fl(M3, z, 4096), Bool.or(D.Fl(M3, D.Fd(2n, M3, z), 1024), Bool.or(D.Nodes(os, M3, D.Fd(2n, M3, z)),
        Bool.or(D.Mem(Nil{}, D.Fd(2n, M3, z)), D.Mem(D.Ag.vars(Nil{}, M3, D.Fd(1n, M3, z)), D.Fd(2n, M3, z)))))) == True{} : Bool}}
  +c12 = {(%e2 : {Bool.or(D.Fl(M3, _, 1024), Bool.not(D.Mem(ps2, _))) == True{} : Bool};
      held.np(ds, ks, img, M3, nx1, fi, im, os, [D.Rt{yv, v}], fs, sp, pend2, ps2, yv, hsk, hh)) :
    {Bool.or(D.Fl(M3, D.Fd(2n, M3, z), 1024), Bool.not(D.Mem(ps2, D.Fd(2n, M3, z)))) == True{} : Bool}}
  +c13 = {(%e1 : {_ == 0 : U32}; {==}) : {D.Fd(1n, M3, z) == 0 : U32}}
  (c1, (c2, (hown, (c4, (hmz, (c6, (c7, (c8, (c9, (c10, (c11, (c12, c13))))))))))))

# no frame binds a variable over its hole: the hole's term is below n when the
# whole is
def below.plug(fr: D.AF, +t: Bk.Term, +n: Nat, h: {D.Term.below(D.A.plug(fr, t), n) == True{} : Bool}) ->
  {D.Term.below(t, n) == True{} : Bool}:
  match fr:
    case D.AF{D.FK.arg{}, q, _, a, _}:
      D.and.l(D.Term.below(t, n), D.Term.below(a, n), h)
    case D.AF{D.FK.val{}, q, _, a, _}:
      D.and.l(D.Term.below(t, n), D.Term.below(a, n), h)
    case D.AF{D.FK.fun{}, q, _, a, _}:
      D.and.r(D.Term.below(a, n), D.Term.below(t, n), h)
    case D.AF{D.FK.let{}, q, _, a, _}:
      D.and.l(D.Term.below(t, n), D.Term.below(a, 1n+n), h)
    case D.AF{D.FK.tupb{}, q, _, a, _}:
      D.and.l(D.Term.below(t, n), D.Term.below(a, n), h)
    case D.AF{D.FK.tupa{}, q, _, a, _}:
      D.and.r(D.Term.below(a, n), D.Term.below(t, n), h)
    case D.AF{D.FK.rwt{}, _, _, a, b}:
      D.and.l(D.Term.below(t, n), Bool.and(D.Term.below(a, 2n+n), D.Term.below(b, n)), h)
    case D.AF{D.FK.minb{}, _, _, a, _}:
      D.and.l(D.Term.below(t, n), D.Term.below(a, n), h)
    case D.AF{D.FK.mina{}, _, _, a, _}:
      D.and.r(D.Term.below(a, n), D.Term.below(t, n), h)

def below.plugs(fs: List<&2, D.AF>, +t: Bk.Term, +n: Nat, h: {D.Term.below(D.A.plugs(fs, t), n) == True{} : Bool}) ->
  {D.Term.below(t, n) == True{} : Bool}:
  match fs:
    case Nil{}:
      h
    case Con{+fr, rest}:
      below.plug(fr, t, n, below.plugs(rest, D.A.plug(fr, t), n, h))
