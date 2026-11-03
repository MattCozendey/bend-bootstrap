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
