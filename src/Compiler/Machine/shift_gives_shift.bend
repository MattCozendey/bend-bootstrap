# compiler: M.shift gives Term.shift
# ==================================
#
# The proof of copy_substitution.bend's Sh.ok: M.shift's walk (copy_walk.bend)
# with the shift's registers (sroot, ss, scut, snew, sk, ssrc, sdep) and part.
# Sh.start makes the root and the first frame; Sh.loop, by induction on the
# fuel, runs the rounds, each of which (Sh.body) makes the measure smaller;
# Sh.end reads the copy from the root and releases the root. The walk keeps
# its start's facts (W.Sc) and its accounting (W.Acc), so that it runs out of
# memory only below the budget Sh.B.

import Base
import ../../Book/impl.bend as Bk
import ../../Eval/impl.bend as El
import ../../Program/impl.bend as Pg
import ../Cir/impl.bend as Cr
import ./impl.bend as Mc
import ./cell_terms.bend as T
import ../need_big.bend as N
import ./copy_substitution.bend as D
import ./copy_kit.bend as K
import ./copy_walk.bend as W
import ./copy_end.bend as En

# The code
# --------

# a round of M.copy.walk's loop
def Wk.body(+stack: Nat, +depth: Nat, +top: Nat, +k: Nat, +at: Nat, +under: Nat, part: Cr.Cir.Stmt) -> Cr.Cir.Stmt:
  Mc.M.do([
    Mc.M.set(top, Mc.M.g(stack)),
    Mc.M.if(Mc.M.eq(Mc.M.todo(Mc.M.g(top)), Mc.M.c(0)), Mc.M.do([
      Mc.M.set(stack, Mc.M.f(1n, Mc.M.g(top))),
      Mc.M.finish(top),
      Mc.M.when(Mc.M.ne(Mc.M.g(stack), Mc.M.c(0)),
        Mc.M.set(depth, Mc.M.sub(Mc.M.g(depth), Mc.M.bump(Mc.M.g(stack), Mc.M.todo.last(Mc.M.g(stack))))))]),
    Mc.M.do([
      Mc.M.set(k, Mc.M.todo.first(Mc.M.g(top))),
      Mc.M.st(0n, Mc.M.g(top), Mc.M.sub(Mc.M.f(0n, Mc.M.g(top)), Mc.M.todo.bit(Mc.M.g(k)))),
      Mc.M.set(at, Mc.M.get(Mc.M.g(top), Mc.M.g(k))),
      Mc.M.set(under, Mc.M.add(Mc.M.g(depth), Mc.M.bump(Mc.M.g(top), Mc.M.g(k)))),
      part]))])

# M.shift's part
def Sh.part() -> Cr.Cir.Stmt:
  Mc.M.if(Mc.M.and(Mc.M.lt(Mc.M.fv(Mc.M.g(Mc.R.ssrc())), Mc.M.c(Mc.F.fv_max())), Mc.M.le(Mc.M.fv(Mc.M.g(Mc.R.ssrc())), Mc.M.g(Mc.R.sdep()))),
    Mc.M.inc(Mc.R.ssrc()),
    Mc.M.if(Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.ssrc())), Mc.M.c(Mc.T.var())),
      Mc.M.if(Mc.M.lt(Mc.M.f(2n, Mc.M.g(Mc.R.ssrc())), Mc.M.g(Mc.R.sdep())),
        Mc.M.inc(Mc.R.ssrc()),
        Mc.M.do([
          Mc.M.var(Mc.R.t1(), Mc.M.add(Mc.M.f(2n, Mc.M.g(Mc.R.ssrc())), Mc.M.g(Mc.R.samt()))),
          Mc.M.put(Mc.R.snew(), Mc.R.sk(), Mc.M.g(Mc.R.t1()))])),
      Mc.M.do([
        Mc.M.copy.push(Mc.R.t1(), Mc.R.ssrc(), Mc.R.snew(), Mc.R.sk(), Mc.R.ss()),
        Mc.M.set(Mc.R.scut(), Mc.M.g(Mc.R.sdep()))])))

def Sh.body() -> Cr.Cir.Stmt:
  Wk.body(Mc.R.ss(), Mc.R.scut(), Mc.R.snew(), Mc.R.sk(), Mc.R.ssrc(), Mc.R.sdep(), Sh.part())

def Sh.loop.stmt() -> Cr.Cir.Stmt:
  Mc.M.while(Mc.M.ne(Mc.M.g(Mc.R.ss()), Mc.M.c(0)), Sh.body())

# The registers
# -------------

# the registers at a round of M.shift's loop: regs0's, with pend, the stack,
# the depth and the root, and any values j for the others that it writes
def Sh.R(+regs0: List<&2, U32>, +pend: U32, +stack: U32, +depth: U32, +root: U32, +j: List<&2, U32>) -> List<&2, U32>:
  D.Ups([D.Up{3n, pend}, D.Up{4n, T.tm.reg(j, 0n)}, D.Up{5n, T.tm.reg(j, 1n)}, D.Up{6n, T.tm.reg(j, 2n)},
    D.Up{7n, T.tm.reg(j, 3n)}, D.Up{33n, T.tm.reg(j, 4n)}, D.Up{41n, T.tm.reg(j, 5n)}, D.Up{54n, stack},
    D.Up{55n, T.tm.reg(j, 6n)}, D.Up{56n, depth}, D.Up{57n, root}, D.Up{58n, T.tm.reg(j, 7n)},
    D.Up{59n, T.tm.reg(j, 8n)}, D.Up{61n, T.tm.reg(j, 9n)}, D.Up{62n, T.tm.reg(j, 10n)}], D.Rg.ex(63n, regs0, 0n))

# The invariant
# -------------

# the walk's state at a round: the frames, the garbage and its pend list, the
# registers pend, stack, depth and root, the cells taken so far (T) and the
# old cells that the new ones copy (cs), and the values j of the other
# registers that it writes
type Wk is Data:
  Wk{frs: List<&2, W.Fr>, P: List<&2, U32>, Q: List<&2, U32>, pend: U32, stack: U32, depth: U32,
    root: U32, T: List<&2, U32>, cs: List<&2, D.Pr>, j: List<&2, U32>}

# the shift's budget: the cells up to F + B0, the result's nodes and the root
def Sh.B(sc: W.Sc, +F: U32, +a: U32, +t: Bk.Term) -> Nat:
  match sc:
    case W.Sc{_, _, _, _, _, _, _, _, +B0, _, _, _}:
      D.Cells.bytes(F, Nat.add(B0, 1n+Pg.Term.size(El.Term.shift(t, U32.to_nat(a), 0n))))

# the invariant of M.shift's walk, of the amount a, the image's names ks and
# terms img, the image K, first F, the start's facts sc, the source's cell x
# and term t, and the start's measure Wm0
def Sh.WI(+a: U32, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +K: U32, +F: U32, sc: W.Sc, +x: U32,
  +t: Bk.Term, +Wm0: Nat, +m: Cr.Cir.Cells, +nx: U32, +frs: List<&2, W.Fr>, +P: List<&2, U32>, +Q: List<&2, U32>,
  +pend: U32, +stack: U32, +depth: U32, +root: U32, +T: List<&2, U32>, +cs: List<&2, D.Pr>) -> Data:
  match sc:
    case W.Sc{+m0, +P0, +Q0, +N0, +E, +rs, +ts, +kc, +B0, +zs, +S, +hx}:
      +mo = {D.Mo.shift{U32.to_nat(a)} : D.Mo}
      +X = {List.append(&2, U32, P, Con{root, List.append(&2, U32, W.Ns(frs), E)}) : List<&2, U32>}
      D.P2({U32.is_le(290, K) == True{} : Bool},
      D.P2({U32.is_lt(K, F) == True{} : Bool},
      D.P2({U32.is_le(F, nx) == True{} : Bool},
      D.P2({Cr.Cir.is_cell(root, K, F, nx) == True{} : Bool},
      D.P2({U32.is_le(F, root) == True{} : Bool},
      D.P2({W.Dj(Con{root, W.Ns(frs)}, List.append(&2, U32, P, E)) == True{} : Bool},
      D.P2(W.Frs(mo, m, ks, img, K, F, X, nx, frs, stack, True{}, 0, Bk.Term.Efq{}, 0n),
      D.P2(W.Root(mo, m, ks, img, K, F, X, nx, hx, frs, root, x, t),
      D.P2(W.Dp(frs, depth),
      D.P2({W.DB(frs, Wm0) == True{} : Bool},
      D.P2({D.AL(m, pend, P, Q, zs, K, F, nx) == True{} : Bool},
      D.P2({D.Incl(P0, N0, X, nx) == True{} : Bool},
      D.P2(D.Tb(m),
      D.P2(D.Rts(m, ks, img, K, F, List.append(&2, U32, P0, E), N0, List.append(&2, D.Rt, rs, D.Tmp.held(ts))),
      D.P2(D.Kcs(m, K, F, List.append(&2, U32, P0, E), N0, E, kc),
      D.P2({D.Ex.ok(E, P, F, nx) == True{} : Bool},
      D.P2({Nat.is_le(W.Wm(frs), Wm0) == True{} : Bool},
      D.P2({W.Pz(Con{root, W.Ns(frs)}, P, m) == True{} : Bool},
        W.Acc(mo, m0, K, F, P0, Q0, N0, E, rs, ts, B0, 0n, t, hx, S, cs, ks, img, m, nx, frs, P, Q, root, T)))))))))))))))))))

# the invariant of a state, by its witness w, with the registers rg
def Sh.WI.of(+regs0: List<&2, U32>, +a: U32, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +K: U32, +F: U32,
  +sc: W.Sc, +x: U32, +t: Bk.Term, +Wm0: Nat, w: Wk, +rg: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32) -> Data:
  match w:
    case Wk{+frs, +P, +Q, +pend, +stack, +depth, +root, +T, +cs, +j}:
      D.P2({rg == Sh.R(regs0, pend, stack, depth, root, j) : List<&2, U32>},
        Sh.WI(a, ks, img, K, F, sc, x, t, Wm0, m, nx, frs, P, Q, pend, stack, depth, root, T, cs))

# the measure of a witness
def Wk.m(w: Wk) -> Nat:
  match w:
    case Wk{frs, _, _, _, _, _, _, _, _, _}:
      W.Wm(frs)

# The rounds
# ----------

# a round of the loop: the invariant again, with a smaller measure, or out of
# memory within the budget
def Sh.body.ok(+f: Nat, +regs0: List<&2, U32>, +a: U32, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +K: U32,
  +F: U32, +L: U32, +I: List<&2, Word(8n)>, +sc: W.Sc, +x: U32, +t: Bk.Term, +Wm0: Nat, +m: Cr.Cir.Cells, +nx: U32, +pg: U32,
  +fr: W.Fr, +frs: List<&2, W.Fr>, +P: List<&2, U32>, +Q: List<&2, U32>, +pend: U32, +stack: U32, +depth: U32,
  +root: U32, +T: List<&2, U32>, +cs: List<&2, D.Pr>, +j: List<&2, U32>, ha: {T.tm.reg(regs0, 60n) == a : U32},
  wi: Sh.WI(a, ks, img, K, F, sc, x, t, Wm0, m, nx, Con{fr, frs}, P, Q, pend, stack, depth, root, T, cs)) ->
  D.Ok(Cr.Cir.exec(1n+f, Sh.body(), D.S(Sh.R(regs0, pend, stack, depth, root, j), m, nx, F, K, pg, L, I)), F, K, L, I,
    Sh.B(sc, F, a, t),
    rg => ms => nx2 => pg2 => D.Ex(Wk, w => D.P2(Sh.WI.of(regs0, a, ks, img, K, F, sc, x, t, Wm0, w, rg, ms, nx2),
      {Nat.is_lt(Wk.m(w), W.Wm(Con{fr, frs})) == True{} : Bool}))):
  ?TODO

# the loop's end: the frames are gone and the root's field 2 holds the copy
def Sh.fin(+regs0: List<&2, U32>, +a: U32, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +K: U32, +F: U32,
  +sc: W.Sc, +x: U32, +t: Bk.Term, +Wm0: Nat, +rg: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32) -> Data:
  D.Ex(Wk, w => D.P2(Sh.WI.of(regs0, a, ks, img, K, F, sc, x, t, Wm0, w, rg, m, nx),
    {Wk.m(w) == 0n : Nat}))

# The loop
# --------

# the stack register holds the top frame's cell, which is not 0
def Sh.nz(+a: U32, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +K: U32, +F: U32, sc: W.Sc, +x: U32,
  +t: Bk.Term, +Wm0: Nat, +m: Cr.Cir.Cells, +nx: U32, fr: W.Fr, +frs: List<&2, W.Fr>, +P: List<&2, U32>, +Q: List<&2, U32>,
  +pend: U32, +stack: U32, +depth: U32, +root: U32, +T: List<&2, U32>, +cs: List<&2, D.Pr>,
  wi: Sh.WI(a, ks, img, K, F, sc, x, t, Wm0, m, nx, Con{fr, frs}, P, Q, pend, stack, depth, root, T, cs)) ->
  {U32.is_zero(stack) == False{} : Bool}:
  match sc fr:
    case W.Sc{+m0, +P0, +Q0, +N0, +E, +rs, +ts, +kc, +B0, +zs, +S0, +hx} W.Fr{+n, +h, +x2, +T0, +y2, +y3, +y4, +t2, +t3, +t4, +s2, +s3, +s4, +d}:
      (_, w1) = wi
      (hkf, w2) = w1
      (_, w3) = w2
      (_, w4) = w3
      (_, w5) = w4
      (_, w6) = w5
      (hf, _) = w6
      (hs, h2) = hf
      (fo, _) = h2
      (_, f1) = fo
      (_, f2) = f1
      (_, f3) = f2
      (_, f4) = f3
      (_, f5) = f4
      (_, f6) = f5
      (_, f7) = f6
      (_, f8) = f7
      (_, f9) = f8
      (_, f10) = f9
      (hle, _) = f10
      %Equal.sym(U32, stack, n, hs) : {U32.is_zero(_) == False{} : Bool}
      K.U.nz(n, K, F, hkf, hle)

# Sh.loop's claim
def Sh.loop.goal(+f: Nat, +regs0: List<&2, U32>, +a: U32, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +K: U32,
  +F: U32, +L: U32, +I: List<&2, Word(8n)>, +sc: W.Sc, +x: U32, +t: Bk.Term, +Wm0: Nat, +m: Cr.Cir.Cells, +nx: U32, +pg: U32,
  +pend: U32, +stack: U32, +depth: U32, +root: U32, +j: List<&2, U32>) -> Type:
  D.Ok(Cr.Cir.exec(1n+f, Sh.loop.stmt(), D.S(Sh.R(regs0, pend, stack, depth, root, j), m, nx, F, K, pg, L, I)), F, K, L, I,
    Sh.B(sc, F, a, t), rg => ms => nx2 => pg2 => Sh.fin(regs0, a, ks, img, K, F, sc, x, t, Wm0, rg, ms, nx2))

# the loop's end, once the frames are gone
def Sh.loop.nil(+f: Nat, +regs0: List<&2, U32>, +a: U32, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +K: U32,
  +F: U32, +L: U32, +I: List<&2, Word(8n)>, sc: W.Sc, +x: U32, +t: Bk.Term, +Wm0: Nat, +m: Cr.Cir.Cells, +nx: U32, +pg: U32,
  +P: List<&2, U32>, +Q: List<&2, U32>, +pend: U32, +stack: U32, +depth: U32, +root: U32, +T: List<&2, U32>,
  +cs: List<&2, D.Pr>, +j: List<&2, U32>, +wi: Sh.WI(a, ks, img, K, F, sc, x, t, Wm0, m, nx, [], P, Q, pend, stack, depth, root, T, cs)) ->
  Sh.loop.goal(f, regs0, a, ks, img, K, F, L, I, sc, x, t, Wm0, m, nx, pg, pend, stack, depth, root, j):
  match sc:
    case W.Sc{+m0, +P0, +Q0, +N0, +E, +rs, +ts, +kc, +B0, +zs, +S0, +hx}:
      (_, w1) = wi
      (_, w2) = w1
      (_, w3) = w2
      (_, w4) = w3
      (_, w5) = w4
      (_, w6) = w5
      (hs, _) = w6
      +sc0 = {W.Sc{m0, P0, Q0, N0, E, rs, ts, kc, B0, zs, S0, hx} : W.Sc}
      +st = D.S(Sh.R(regs0, pend, stack, depth, root, j), m, nx, F, K, pg, L, I)
      +cnd = Mc.M.ne(Mc.M.g(Mc.R.ss()), Mc.M.c(0))
      +ev = {%Equal.sym(U32, stack, 0, hs) : {Some{0} == Some{Bool.to_u32(U32.is_ne(_, 0))} : Maybe<&2, U32>}; {==} : {Some{0} == Cr.Cir.eval(cnd, st) : Maybe<&2, U32>}}
      K.Ok.eq(Cr.Cir.exec(1n+f, Sh.loop.stmt(), st), Cr.Cir.Out.next{st}, F, K, L, I, Sh.B(sc0, F, a, t),
        rg => ms => nx2 => pg2 => Sh.fin(regs0, a, ks, img, K, F, sc0, x, t, Wm0, rg, ms, nx2),
        Equal.sym(Cr.Cir.Out, Cr.Cir.exec(1n+f, Sh.loop.stmt(), st), Cr.Cir.Out.next{st}, K.X.wh0(f, cnd, Sh.body(), st, ev)),
        K.Ok.next(Sh.R(regs0, pend, stack, depth, root, j), m, nx, F, K, pg, L, I, Sh.B(sc0, F, a, t),
          rg => ms => nx2 => pg2 => Sh.fin(regs0, a, ks, img, K, F, sc0, x, t, Wm0, rg, ms, nx2),
          (Wk{[], P, Q, pend, stack, depth, root, T, cs, j}, (({==}, wi), {==}))))

# a round's outcome: the invariant again, with a smaller measure, so that the
# fuel left bounds it; k continues the loop from there
def Sh.loop.next(+g: Nat, +regs0: List<&2, U32>, +a: U32, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +K: U32,
  +F: U32, +L: U32, +I: List<&2, Word(8n)>, +sc: W.Sc, +x: U32, +t: Bk.Term, +Wm0: Nat, +rg: List<&2, U32>, +ms: Cr.Cir.Cells,
  +nx2: U32, +pg2: U32, +Wold: Nat, hf: {Nat.is_le(Wold, 1n+g) == True{} : Bool},
  q: D.Ex(Wk, w => D.P2(Sh.WI.of(regs0, a, ks, img, K, F, sc, x, t, Wm0, w, rg, ms, nx2),
    {Nat.is_lt(Wk.m(w), Wold) == True{} : Bool})),
  k: @frs: List<&2, W.Fr> -> @P: List<&2, U32> -> @Q: List<&2, U32> -> @pend: U32 -> @stack: U32 ->
    @depth: U32 -> @root: U32 -> @T: List<&2, U32> -> @cs: List<&2, D.Pr> -> @j: List<&2, U32> ->
    {Nat.is_le(W.Wm(frs), g) == True{} : Bool} ->
    Sh.WI(a, ks, img, K, F, sc, x, t, Wm0, ms, nx2, frs, P, Q, pend, stack, depth, root, T, cs) ->
    Sh.loop.goal(g, regs0, a, ks, img, K, F, L, I, sc, x, t, Wm0, ms, nx2, pg2, pend, stack, depth, root, j)) ->
  D.Ok(Cr.Cir.exec(1n+g, Sh.loop.stmt(), D.S(rg, ms, nx2, F, K, pg2, L, I)), F, K, L, I, Sh.B(sc, F, a, t),
    rg => ms => nx2 => pg2 => Sh.fin(regs0, a, ks, img, K, F, sc, x, t, Wm0, rg, ms, nx2)):
  (w, r2) = q
  match w:
    case Wk{+frs, +P, +Q, +pend, +stack, +depth, +root, +T, +cs, +j}:
      (wio, hlt) = r2
      (heq, wi) = wio
      %Equal.sym(List<&2, U32>, rg, Sh.R(regs0, pend, stack, depth, root, j), heq) :
        D.Ok(Cr.Cir.exec(1n+g, Sh.loop.stmt(), D.S(_, ms, nx2, F, K, pg2, L, I)), F, K, L, I, Sh.B(sc, F, a, t),
        rg => ms => nx2 => pg2 => Sh.fin(regs0, a, ks, img, K, F, sc, x, t, Wm0, rg, ms, nx2))
      k(frs, P, Q, pend, stack, depth, root, T, cs, j, K.Na.lt_le(Wold, W.Wm(frs), g, hlt, hf), wi)

# the loop, from a state of the invariant whose measure is at most the fuel
def Sh.loop(f: Nat, +regs0: List<&2, U32>, +a: U32, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +K: U32,
  +F: U32, +L: U32, +I: List<&2, Word(8n)>, +sc: W.Sc, +x: U32, +t: Bk.Term, +Wm0: Nat, +m: Cr.Cir.Cells, +nx: U32, +pg: U32,
  frs: List<&2, W.Fr>, +P: List<&2, U32>, +Q: List<&2, U32>, +pend: U32, +stack: U32, +depth: U32, +root: U32,
  +T: List<&2, U32>, +cs: List<&2, D.Pr>, +j: List<&2, U32>, +ha: {T.tm.reg(regs0, 60n) == a : U32},
  hf: {Nat.is_le(W.Wm(frs), f) == True{} : Bool},
  +wi: Sh.WI(a, ks, img, K, F, sc, x, t, Wm0, m, nx, frs, P, Q, pend, stack, depth, root, T, cs)) ->
  Sh.loop.goal(f, regs0, a, ks, img, K, F, L, I, sc, x, t, Wm0, m, nx, pg, pend, stack, depth, root, j):
  match f frs:
    case _ Nil{}:
      Sh.loop.nil(f, regs0, a, ks, img, K, F, L, I, sc, x, t, Wm0, m, nx, pg, P, Q, pend, stack, depth, root, T, cs, j, wi)
    case 0n Con{W.Fr{+n, +h, +x2, +T0, +y2, +y3, +y4, +t2, +t3, +t4, +s2, +s3, +s4, +d}, +rest}:
      K.Bo.tf(Sh.loop.goal(0n, regs0, a, ks, img, K, F, L, I, sc, x, t, Wm0, m, nx, pg, pend, stack, depth, root, j), hf)
    case 1n+(+g) Con{+fr, +rest}:
      +st = D.S(Sh.R(regs0, pend, stack, depth, root, j), m, nx, F, K, pg, L, I)
      +cnd = Mc.M.ne(Mc.M.g(Mc.R.ss()), Mc.M.c(0))
      +nz = Sh.nz(a, ks, img, K, F, sc, x, t, Wm0, m, nx, fr, rest, P, Q, pend, stack, depth, root, T, cs, wi)
      +ev = {%Equal.sym(Bool, U32.is_zero(stack), False{}, nz) : {Some{1} == Some{Bool.to_u32(Bool.not(_))} : Maybe<&2, U32>}; {==} :
        {Some{1} == Cr.Cir.eval(cnd, st) : Maybe<&2, U32>}}
      K.Ok.loop(g, cnd, Sh.body(), st, 1, F, K, L, I, Sh.B(sc, F, a, t),
        rg => ms => nx2 => pg2 => D.Ex(Wk, w => D.P2(Sh.WI.of(regs0, a, ks, img, K, F, sc, x, t, Wm0, w, rg, ms, nx2),
          {Nat.is_lt(Wk.m(w), W.Wm(Con{fr, rest})) == True{} : Bool})),
        rg => ms => nx2 => pg2 => Sh.fin(regs0, a, ks, img, K, F, sc, x, t, Wm0, rg, ms, nx2),
        ev, {==},
        Sh.body.ok(g, regs0, a, ks, img, K, F, L, I, sc, x, t, Wm0, m, nx, pg, fr, rest, P, Q, pend, stack, depth, root, T, cs,
          j, ha, wi),
        +rg => +ms => +nx2 => +pg2 => q => Sh.loop.next(g, regs0, a, ks, img, K, F, L, I, sc, x, t, Wm0, rg, ms, nx2, pg2,
          W.Wm(Con{fr, rest}), hf, q, frs2 => P2 => Q2 => pend2 => stack2 => depth2 => root2 => T2 => cs2 => j2 => hf2 => wi2 =>
            Sh.loop(g, regs0, a, ks, img, K, F, L, I, sc, x, t, Wm0, ms, nx2, pg2, frs2, P2, Q2, pend2, stack2, depth2, root2,
              T2, cs2, j2, ha, hf2, wi2)))

# The start and the end
# ---------------------

# the root cell n0: a Prj (11) whose part, in field 2, the source's cell x of
# the term t, is pending
def Sh.fr0(+n0: U32, +x: U32, +t: Bk.Term) -> W.Fr:
  W.Fr{n0, 11, x, Bk.Term.Prj{t}, x, 0, 0, t, Bk.Term.Efq{}, Bk.Term.Efq{}, W.St.pe{}, W.St.un{}, W.St.un{}, 0n}

# the start's facts of M.shift from the law's
def Sh.sc(+m: Cr.Cir.Cells, +P: List<&2, U32>, +Q: List<&2, U32>, +nx: U32, +E: List<&2, U32>, +rs: List<&2, D.Rt>,
  +ts: List<&2, D.Tmp>, +kc: List<&2, D.Kc>, +B0: Nat, +zs: List<&2, D.Zs>, +g: Nat, +x: U32, +t: Bk.Term, +hx: Bool) -> W.Sc:
  W.Sc{m, P, Q, nx, E, rs, ts, kc, B0, zs, [D.Rt{g, x, t}], hx}

# M.copy.root, then the stack and the depth: the invariant holds of the root
# frame, with the measure 1 + 2 × Sz(t), and the root taken
def Sh.start(+f: Nat, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +F: U32, +K: U32, +pg: U32, +L: U32,
  +I: List<&2, Word(8n)>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +P: List<&2, U32>, +Q: List<&2, U32>,
  +zs: List<&2, D.Zs>, +E: List<&2, U32>, +rs: List<&2, D.Rt>, +ts: List<&2, D.Tmp>, +kc: List<&2, D.Kc>, +B0: Nat, +hx: Bool,
  +t: Bk.Term, +g: Nat, +a: U32, +B: Cr.Cir.Stmt, -R: List<&2, U32> -> Cr.Cir.Cells -> U32 -> U32 -> Type,
  pre: D.Pre(regs, m, nx, F, K, ks, img, P, Q, zs, E, rs, ts, kc, B0),
  ht: {D.Tm(g, m, ks, img, K, F, List.append(&2, U32, P, E), nx, T.tm.reg(regs, 62n)) == Some{t} : Maybe<&2, Bk.Term>},
  hd: N.Le(U32.to_nat(a), Nat.double(U32.to_nat(nx))),
  hv: D.Hx(hx, N.Le(D.Fv(t), N.D(31n, 1n))),
  k: @ms: Cr.Cir.Cells -> @nx2: U32 -> @pg2: U32 -> @P2: List<&2, U32> -> @Q2: List<&2, U32> -> @pend: U32 -> @n0: U32 ->
    @j: List<&2, U32> ->
    Sh.WI(a, ks, img, K, F, Sh.sc(m, P, Q, nx, E, rs, ts, kc, B0, zs, g, T.tm.reg(regs, 62n), t, hx), T.tm.reg(regs, 62n), t,
      1n+Nat.double(D.Sz(t)), ms, nx2, [Sh.fr0(n0, T.tm.reg(regs, 62n), t)], P2, Q2, pend, n0, 0, n0, [n0], Nil{}) ->
    D.Ok(Cr.Cir.exec(1n+f, B, D.S(Sh.R(regs, pend, n0, 0, n0, j), ms, nx2, F, K, pg2, L, I)), F, K, L, I,
      Sh.B(Sh.sc(m, P, Q, nx, E, rs, ts, kc, B0, zs, g, T.tm.reg(regs, 62n), t, hx), F, a, t), R)) ->
  D.Ok(Cr.Cir.exec(1n+f, Cr.Cir.Stmt.seq{Mc.M.copy.root(Mc.R.sroot(), Mc.R.t2()), Cr.Cir.Stmt.seq{Mc.M.set(Mc.R.ss(), Mc.M.g(Mc.R.sroot())),
    Cr.Cir.Stmt.seq{Mc.M.set(Mc.R.scut(), Mc.M.c(0)), B}}}, D.S(regs, m, nx, F, K, pg, L, I)), F, K, L, I,
    Sh.B(Sh.sc(m, P, Q, nx, E, rs, ts, kc, B0, zs, g, T.tm.reg(regs, 62n), t, hx), F, a, t), R):
  ?TODO

# the walk's end, at no frames (Wm 0): M.copy.end from the shift's registers
def Sh.end.at(+f: Nat, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +F: U32, +K: U32, +L: U32, +I: List<&2, Word(8n)>,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +P: List<&2, U32>, +Q: List<&2, U32>, +zs: List<&2, D.Zs>,
  +E: List<&2, U32>, +rs: List<&2, D.Rt>, +ts: List<&2, D.Tmp>, +kc: List<&2, D.Kc>, +B0: Nat, +hx: Bool, +t: Bk.Term, +g: Nat,
  +a: U32, +Wm0: Nat, +ms: Cr.Cir.Cells, +nx2: U32, +pg2: U32, frs: List<&2, W.Fr>, +P2: List<&2, U32>, +Q2: List<&2, U32>,
  +pend: U32, +stack: U32, +depth: U32, +root: U32, +Tn: List<&2, U32>, +cs: List<&2, D.Pr>, +j: List<&2, U32>,
  wi: Sh.WI(a, ks, img, K, F, Sh.sc(m, P, Q, nx, E, rs, ts, kc, B0, zs, g, T.tm.reg(regs, 62n), t, hx), T.tm.reg(regs, 62n), t, Wm0,
    ms, nx2, frs, P2, Q2, pend, stack, depth, root, Tn, cs),
  hm0: {W.Wm(frs) == 0n : Nat}) ->
  D.Ok(Cr.Cir.exec(1n+f, Cr.Cir.Stmt.seq{Mc.M.copy.end(Mc.R.sres(), Mc.R.sroot()), Cr.Cir.Stmt.nop{}},
    D.S(Sh.R(regs, pend, stack, depth, root, j), ms, nx2, F, K, pg2, L, I)),
    F, K, L, I, Sh.B(Sh.sc(m, P, Q, nx, E, rs, ts, kc, B0, zs, g, T.tm.reg(regs, 62n), t, hx), F, a, t),
    rg => ms => nx3 => pg3 => D.Ex(D.Wt, w => D.Post(hx, D.Mo.shift{U32.to_nat(a)}, t, regs, D.Sh.scratch(), Mc.R.sres(),
      ks, img, K, F, m, P, Q, E, nx, Nat.add(B0, 1n+Pg.Term.size(El.Term.shift(t, U32.to_nat(a), 0n))), rs, ts, kc,
      [D.Rt{g, T.tm.reg(regs, 62n), t}], w, rg, ms, nx3))):
  match frs:
    case Nil{}:
      (hk, w1) = wi
      (hkf, w2) = w1
      (hfn, w3) = w2
      (hrc, w4) = w3
      (hfr, w5) = w4
      (hdj, w6) = w5
      (_, w7) = w6
      (hroot, w8) = w7
      (_, w9) = w8
      (_, w10) = w9
      (hal, w11) = w10
      (hincl, w12) = w11
      (htb, w13) = w12
      (hrts, w14) = w13
      (hkcs, w15) = w14
      (_, w16) = w15
      (_, w17) = w16
      (hpz, hacc) = w17
      +x = T.tm.reg(regs, 62n)
      +r = D.Fd(2n, ms, root)
      +ups = {[D.Up{3n, pend}, D.Up{4n, T.tm.reg(j, 0n)}, D.Up{5n, T.tm.reg(j, 1n)}, D.Up{6n, T.tm.reg(j, 2n)},
        D.Up{7n, T.tm.reg(j, 3n)}, D.Up{33n, T.tm.reg(j, 4n)}, D.Up{41n, T.tm.reg(j, 5n)}, D.Up{54n, stack},
        D.Up{55n, T.tm.reg(j, 6n)}, D.Up{56n, depth}, D.Up{57n, root}, D.Up{58n, T.tm.reg(j, 7n)},
        D.Up{59n, T.tm.reg(j, 8n)}, D.Up{61n, T.tm.reg(j, 9n)}, D.Up{62n, T.tm.reg(j, 10n)}, D.Up{40n, r}, D.Up{3n, root}] : List<&2, D.Up>}
      En.end.post(f, hx, D.Mo.shift{U32.to_nat(a)}, t, regs, D.Sh.scratch(), Mc.R.sres(), Mc.R.sroot(), ks, img, K, F, pg2, L, I,
        m, P, Q, E, nx, Nat.add(B0, 1n+Pg.Term.size(El.Term.shift(t, U32.to_nat(a), 0n))), rs, ts, kc, [D.Rt{g, x, t}], B0, 0n, zs, cs, x,
        Sh.B(Sh.sc(m, P, Q, nx, E, rs, ts, kc, B0, zs, g, x, t, hx), F, a, t), Sh.R(regs, pend, stack, depth, root, j), ms, nx2, P2, Q2,
        pend, root, Tn, ups, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==},
        hk, hkf, hfn, hrc, hfr, hdj, hroot, hal, hincl, htb, hrts, hkcs, hpz, hacc)
    case Con{W.Fr{+n, +h, +x2, +T0, +y2, +y3, +y4, +t2, +t3, +t4, +s2, +s3, +s4, +d}, +rest}:
      Empty.absurd(D.Ok(Cr.Cir.exec(1n+f, Cr.Cir.Stmt.seq{Mc.M.copy.end(Mc.R.sres(), Mc.R.sroot()), Cr.Cir.Stmt.nop{}},
        D.S(Sh.R(regs, pend, stack, depth, root, j), ms, nx2, F, K, pg2, L, I)),
        F, K, L, I, Sh.B(Sh.sc(m, P, Q, nx, E, rs, ts, kc, B0, zs, g, T.tm.reg(regs, 62n), t, hx), F, a, t),
        rg => ms => nx3 => pg3 => D.Ex(D.Wt, w => D.Post(hx, D.Mo.shift{U32.to_nat(a)}, t, regs, D.Sh.scratch(), Mc.R.sres(),
          ks, img, K, F, m, P, Q, E, nx, Nat.add(B0, 1n+Pg.Term.size(El.Term.shift(t, U32.to_nat(a), 0n))), rs, ts, kc,
          [D.Rt{g, T.tm.reg(regs, 62n), t}], w, rg, ms, nx3))),
        (%hm0 : N.Le(1n, _); N.le_zero(Nat.add(W.Wp(s2, t2), Nat.add(W.Wp(s3, t3), Nat.add(W.Wp(s4, t4), W.Wm(rest)))))))

# M.copy.end: sres gets the copy from the root, whose cell goes to the pend list
def Sh.end(+f: Nat, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +F: U32, +K: U32, +pg: U32, +L: U32,
  +I: List<&2, Word(8n)>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +P: List<&2, U32>, +Q: List<&2, U32>,
  +zs: List<&2, D.Zs>, +E: List<&2, U32>, +rs: List<&2, D.Rt>, +ts: List<&2, D.Tmp>, +kc: List<&2, D.Kc>, +B0: Nat, +hx: Bool,
  +t: Bk.Term, +g: Nat, +a: U32, +Wm0: Nat, +rg: List<&2, U32>, +ms: Cr.Cir.Cells, +nx2: U32, +pg2: U32,
  fin: Sh.fin(regs, a, ks, img, K, F, Sh.sc(m, P, Q, nx, E, rs, ts, kc, B0, zs, g, T.tm.reg(regs, 62n), t, hx), T.tm.reg(regs, 62n),
    t, Wm0, rg, ms, nx2)) ->
  D.Ok(Cr.Cir.exec(1n+f, Cr.Cir.Stmt.seq{Mc.M.copy.end(Mc.R.sres(), Mc.R.sroot()), Cr.Cir.Stmt.nop{}}, D.S(rg, ms, nx2, F, K, pg2, L, I)),
    F, K, L, I, Sh.B(Sh.sc(m, P, Q, nx, E, rs, ts, kc, B0, zs, g, T.tm.reg(regs, 62n), t, hx), F, a, t),
    rg => ms => nx3 => pg3 => D.Ex(D.Wt, w => D.Post(hx, D.Mo.shift{U32.to_nat(a)}, t, regs, D.Sh.scratch(), Mc.R.sres(),
      ks, img, K, F, m, P, Q, E, nx, Nat.add(B0, 1n+Pg.Term.size(El.Term.shift(t, U32.to_nat(a), 0n))), rs, ts, kc,
      [D.Rt{g, T.tm.reg(regs, 62n), t}], w, rg, ms, nx3))):
  (w, r2) = fin
  match w:
    case Wk{+frs, +P2, +Q2, +pend, +stack, +depth, +root, +Tn, +cs, +j}:
      (wio, hm0) = r2
      (heq, wi) = wio
      %Equal.sym(List<&2, U32>, rg, Sh.R(regs, pend, stack, depth, root, j), heq) :
        D.Ok(Cr.Cir.exec(1n+f, Cr.Cir.Stmt.seq{Mc.M.copy.end(Mc.R.sres(), Mc.R.sroot()), Cr.Cir.Stmt.nop{}}, D.S(_, ms, nx2, F, K, pg2, L, I)),
          F, K, L, I, Sh.B(Sh.sc(m, P, Q, nx, E, rs, ts, kc, B0, zs, g, T.tm.reg(regs, 62n), t, hx), F, a, t),
          rg => ms => nx3 => pg3 => D.Ex(D.Wt, w => D.Post(hx, D.Mo.shift{U32.to_nat(a)}, t, regs, D.Sh.scratch(), Mc.R.sres(),
            ks, img, K, F, m, P, Q, E, nx, Nat.add(B0, 1n+Pg.Term.size(El.Term.shift(t, U32.to_nat(a), 0n))), rs, ts, kc,
            [D.Rt{g, T.tm.reg(regs, 62n), t}], w, rg, ms, nx3)))
      Sh.end.at(f, regs, m, nx, F, K, L, I, ks, img, P, Q, zs, E, rs, ts, kc, B0, hx, t, g, a, Wm0, ms, nx2, pg2, frs, P2, Q2, pend,
        stack, depth, root, Tn, cs, j, wi, hm0)

# The claim
# ---------

# the root frame's measure
def Sh.w0(+n0: U32, +x: U32, +t: Bk.Term) -> {Nat.is_le(W.Wm([Sh.fr0(n0, x, t)]), 1n+Nat.double(D.Sz(t))) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(Nat.double(D.Sz(t)), 0n), Nat.double(D.Sz(t)), N.add_zero(Nat.double(D.Sz(t)))) :
    {Nat.is_le(1n+_, 1n+Nat.double(D.Sz(t))) == True{} : Bool}
  K.Na.le_refl(Nat.double(D.Sz(t)))

def D.Sh.ok(regs, m, nx, F, K, pg, L, I, ks, img, P, Q, zs, E, rs, ts, kc, B0, hx, t, g, a, pre, ht, ha, hd, hv):
  +W0 = {1n+Nat.double(D.Sz(t)) : Nat}
  +x = {T.tm.reg(regs, 62n) : U32}
  +mo = {D.Mo.shift{U32.to_nat(a)} : D.Mo}
  +sc = {Sh.sc(m, P, Q, nx, E, rs, ts, kc, B0, zs, g, x, t, hx) : W.Sc}
  +S0 = {[D.Rt{g, x, t}] : List<&2, D.Rt>}
  +bud = {Sh.B(sc, F, a, t) : Nat}
  +Bc = {Nat.add(B0, 1n+Pg.Term.size(El.Term.shift(t, U32.to_nat(a), 0n))) : Nat}
  +fin = {Cr.Cir.Stmt.seq{Mc.M.copy.end(Mc.R.sres(), Mc.R.sroot()), Cr.Cir.Stmt.nop{}} : Cr.Cir.Stmt}
  (1n+W0, Sh.start(W0, regs, m, nx, F, K, pg, L, I, ks, img, P, Q, zs, E, rs, ts, kc, B0, hx, t, g, a,
    Cr.Cir.Stmt.seq{Sh.loop.stmt(), fin},
    rg => ms => nx2 => pg2 => D.Ex(D.Wt, w => D.Post(hx, mo, t, regs, D.Sh.scratch(), Mc.R.sres(), ks, img, K, F, m, P, Q, E, nx,
      Bc, rs, ts, kc, S0, w, rg, ms, nx2)),
    pre, ht, hd, hv,
    +ms => +nx2 => +pg2 => +P2 => +Q2 => +pend => +n0 => +j => wi =>
      K.Ok.seq(W0, Sh.loop.stmt(), fin, D.S(Sh.R(regs, pend, n0, 0, n0, j), ms, nx2, F, K, pg2, L, I), F, K, L, I, bud,
        rg => ms3 => nx3 => pg3 => Sh.fin(regs, a, ks, img, K, F, sc, x, t, W0, rg, ms3, nx3),
        rg => ms3 => nx3 => pg3 => D.Ex(D.Wt, w => D.Post(hx, mo, t, regs, D.Sh.scratch(), Mc.R.sres(), ks, img, K, F, m, P, Q, E, nx,
          Bc, rs, ts, kc, S0, w, rg, ms3, nx3)),
        Sh.loop(W0, regs, a, ks, img, K, F, L, I, sc, x, t, W0, ms, nx2, pg2, [Sh.fr0(n0, x, t)], P2, Q2,
          pend, n0, 0, n0, [n0], Nil{}, j, ha, Sh.w0(n0, x, t), wi),
        +rg => +ms3 => +nx3 => +pg3 => fq => Sh.end(W0, regs, m, nx, F, K, pg, L, I, ks, img, P, Q, zs, E, rs, ts, kc, B0, hx, t, g, a,
          W0, rg, ms3, nx3, pg3, fq))))
