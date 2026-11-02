# compiler: layer B, the redexes of λ-matches (U13)
# =================================================
#
# mv.ret.app.prj, mv.ret.fun.prj, mv.ret.app.mat and mv.ret.fun.mat of move_kit.bend.
# Filled by U13; U0 left each as ?TODO.

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
import ./move_kit.bend as K

# Straight runs
# -------------
#
# A statement with no while, no alloc and no emit (Flat) ends with any fuel,
# and never runs out of memory (Safe), whatever it runs from.

# no while, no alloc, no emit
def Flat(s: Cr.Cir.Stmt) -> Bool:
  match s:
    case Cr.Cir.Stmt.nop{}:
      True{}
    case Cr.Cir.Stmt.set{_, _}:
      True{}
    case Cr.Cir.Stmt.store{_, _, _}:
      True{}
    case Cr.Cir.Stmt.alloc{_}:
      False{}
    case Cr.Cir.Stmt.emit{_}:
      False{}
    case Cr.Cir.Stmt.seq{+a, +b}:
      Bool.and(Flat(a), Flat(b))
    case Cr.Cir.Stmt.if{_, a, b}:
      Bool.and(Flat(a), Flat(b))
    case Cr.Cir.Stmt.while{_, _}:
      False{}
    case Cr.Cir.Stmt.halt{_}:
      True{}

# an outcome that ends, and not out of memory
def Safe(o: Cr.Cir.Out) -> Data:
  match o:
    case Cr.Cir.Out.next{_}:
      Unit
    case Cr.Cir.Out.halt{_, _}:
      Unit
    case Cr.Cir.Out.out_of_memory{}:
      Empty
    case Cr.Cir.Out.trap{}:
      Unit
    case Cr.Cir.Out.not_done{}:
      Empty

def safe.set.of(rs: Maybe<&2, List<&2, U32>>, st: Cr.Cir.State) -> Safe(Cr.Cir.exec.set.of(rs, st)):
  match rs st:
    case Some{_} Cr.Cir.State{_, _, _, _, _, _, _, _, _, _}:
      Unit{}
    case None{} _:
      Unit{}

def safe.set(r: Nat, v: Maybe<&2, U32>, st: Cr.Cir.State) -> Safe(Cr.Cir.exec.set(r, v, st)):
  match v st:
    case Some{x} Cr.Cir.State{+regs, m, nx, fi, im, pg, lim, inp, out, outn}:
      safe.set.of(Cr.Cir.regs.set(regs, r, x), Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, out, outn})
    case None{} _:
      Unit{}

def safe.store.if(ok: Bool, k: Nat, i: U32, v: U32, st: Cr.Cir.State) -> Safe(Cr.Cir.exec.store.if(ok, k, i, v, st)):
  match ok st:
    case True{} Cr.Cir.State{_, _, _, _, _, _, _, _, _, _}:
      Unit{}
    case False{} _:
      Unit{}

def safe.store(k: Nat, c: Maybe<&2, U32>, v: Maybe<&2, U32>, st: Cr.Cir.State) -> Safe(Cr.Cir.exec.store(k, c, v, st)):
  match c v st:
    case Some{+i} Some{x} Cr.Cir.State{regs, m, +nx, +fi, +im, pg, lim, inp, out, outn}:
      safe.store.if(Cr.Cir.is_cell(i, im, fi, nx), k, i, x, Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, out, outn})
    case Some{_} None{} _:
      Unit{}
    case None{} _ _:
      Unit{}

def safe.then(o: Cr.Cir.Out, -k: Cr.Cir.State -> Cr.Cir.Out, h: Safe(o), g: @st: Cr.Cir.State -> Safe(k(st))) ->
  Safe(Cr.Cir.exec.then(o, k)):
  match o:
    case Cr.Cir.Out.next{st}:
      g(st)
    case Cr.Cir.Out.halt{s, st}:
      Unit{}
    case Cr.Cir.Out.out_of_memory{}:
      h
    case Cr.Cir.Out.trap{}:
      Unit{}
    case Cr.Cir.Out.not_done{}:
      h

def safe.if.of(z: Bool, -yes: Unit -> Cr.Cir.Out, -no: Unit -> Cr.Cir.Out, hy: Safe(yes(Unit{})), hn: Safe(no(Unit{}))) ->
  Safe(Cr.Cir.exec.if.of(z, yes, no)):
  match z:
    case False{}:
      hy
    case True{}:
      hn

def safe.if(c: Maybe<&2, U32>, -yes: Unit -> Cr.Cir.Out, -no: Unit -> Cr.Cir.Out, hy: Safe(yes(Unit{})), hn: Safe(no(Unit{}))) ->
  Safe(Cr.Cir.exec.if(c, yes, no)):
  match c:
    case Some{x}:
      safe.if.of(U32.is_zero(x), yes, no, hy, hn)
    case None{}:
      Unit{}

def and.l(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def and.r(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      D.bool.ft({b == True{} : Bool}, h)

# a Flat statement runs safely, with any fuel
def flat.safe(f: Nat, s: Cr.Cir.Stmt, +st: Cr.Cir.State, +h: {Flat(s) == True{} : Bool}) -> Safe(Cr.Cir.exec(f, s, st)):
  match f:
    case 0n:
      match s:
        case Cr.Cir.Stmt.nop{}:
          Unit{}
        case Cr.Cir.Stmt.set{+r, +e}:
          safe.set(r, Cr.Cir.eval(e, st), st)
        case Cr.Cir.Stmt.store{+k, +c, +v}:
          safe.store(k, Cr.Cir.eval(c, st), Cr.Cir.eval(v, st), st)
        case Cr.Cir.Stmt.alloc{r}:
          D.bool.ft(Safe(Cr.Cir.exec(0n, Cr.Cir.Stmt.alloc{r}, st)), h)
        case Cr.Cir.Stmt.emit{v}:
          D.bool.ft(Safe(Cr.Cir.exec(0n, Cr.Cir.Stmt.emit{v}, st)), h)
        case Cr.Cir.Stmt.seq{+a, +b}:
          safe.then(Cr.Cir.exec(0n, a, st), u => Cr.Cir.exec(0n, b, u), flat.safe(0n, a, st, and.l(Flat(a), Flat(b), h)),
            u => flat.safe(0n, b, u, and.r(Flat(a), Flat(b), h)))
        case Cr.Cir.Stmt.if{+c, +a, +b}:
          safe.if(Cr.Cir.eval(c, st), u => Cr.Cir.exec(0n, a, st), u => Cr.Cir.exec(0n, b, st),
            flat.safe(0n, a, st, and.l(Flat(a), Flat(b), h)), flat.safe(0n, b, st, and.r(Flat(a), Flat(b), h)))
        case Cr.Cir.Stmt.while{c, b}:
          D.bool.ft(Safe(Cr.Cir.exec(0n, Cr.Cir.Stmt.while{c, b}, st)), h)
        case Cr.Cir.Stmt.halt{x}:
          Unit{}
    case 1n+(+g):
      match s:
        case Cr.Cir.Stmt.nop{}:
          Unit{}
        case Cr.Cir.Stmt.set{+r, +e}:
          safe.set(r, Cr.Cir.eval(e, st), st)
        case Cr.Cir.Stmt.store{+k, +c, +v}:
          safe.store(k, Cr.Cir.eval(c, st), Cr.Cir.eval(v, st), st)
        case Cr.Cir.Stmt.alloc{r}:
          D.bool.ft(Safe(Cr.Cir.exec(1n+g, Cr.Cir.Stmt.alloc{r}, st)), h)
        case Cr.Cir.Stmt.emit{v}:
          D.bool.ft(Safe(Cr.Cir.exec(1n+g, Cr.Cir.Stmt.emit{v}, st)), h)
        case Cr.Cir.Stmt.seq{+a, +b}:
          safe.then(Cr.Cir.exec(1n+g, a, st), u => Cr.Cir.exec(1n+g, b, u), flat.safe(1n+g, a, st, and.l(Flat(a), Flat(b), h)),
            u => flat.safe(1n+g, b, u, and.r(Flat(a), Flat(b), h)))
        case Cr.Cir.Stmt.if{+c, +a, +b}:
          safe.if(Cr.Cir.eval(c, st), u => Cr.Cir.exec(1n+g, a, st), u => Cr.Cir.exec(1n+g, b, st),
            flat.safe(1n+g, a, st, and.l(Flat(a), Flat(b), h)), flat.safe(1n+g, b, st, and.r(Flat(a), Flat(b), h)))
        case Cr.Cir.Stmt.while{c, b}:
          D.bool.ft(Safe(Cr.Cir.exec(1n+g, Cr.Cir.Stmt.while{c, b}, st)), h)
        case Cr.Cir.Stmt.halt{x}:
          Unit{}

# a safe outcome ends
def safe.ends(o: Cr.Cir.Out, h: Safe(o)) -> D.Ends(o):
  match o:
    case Cr.Cir.Out.next{_}:
      Unit{}
    case Cr.Cir.Out.halt{_, _}:
      Unit{}
    case Cr.Cir.Out.out_of_memory{}:
      Unit{}
    case Cr.Cir.Out.trap{}:
      Unit{}
    case Cr.Cir.Out.not_done{}:
      Empty.absurd(D.Ends(Cr.Cir.Out.not_done{}), h)

# a safe outcome holds PostB with any budget
def safe.postb(dn: Bool, o: Cr.Cir.Out, -Q: Cr.Cir.State -> Type, -H: U32 -> Cr.Cir.State -> Type, -B: Nat, -B2: Nat, -lim: U32,
  h: D.PostB(dn, o, Q, H, B, lim), s: Safe(o)) -> D.PostB(dn, o, Q, H, B2, lim):
  match o:
    case Cr.Cir.Out.next{st}:
      h
    case Cr.Cir.Out.halt{x, st}:
      h
    case Cr.Cir.Out.out_of_memory{}:
      Empty.absurd(D.PostB(dn, Cr.Cir.Out.out_of_memory{}, Q, H, B2, lim), s)
    case Cr.Cir.Out.trap{}:
      h
    case Cr.Cir.Out.not_done{}:
      h

# The moves of move_kit.bend that this file proves
# ------------------------------------------------

def K.mv.ret.app.prj(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, h, kind, q, k, a, b, iv, hk, hs):
  ?TODO

def K.mv.ret.fun.prj(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, h, focus, q, k, b, iv):
  ?TODO

def K.mv.ret.app.mat(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, j, h, n, kind, q, k, a, b, iv, hk, hs):
  ?TODO

def K.mv.ret.fun.mat(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, j, h, n, focus, q, k, b, iv):
  ?TODO
