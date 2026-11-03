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
import ../../Shared/shared.bend as Sd
import ../Cir/impl.bend as Cr
import ./impl.bend as Mc
import ./cell_terms.bend as T
import ../need_big.bend as N
import ./definitions.bend as D
import ./statement_runs.bend as X
import ./move_kit.bend as K
import ./heap_ops.bend as U2
import ./accounting.bend as A1

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
# Runs with no while
# -------------------
#
# After U10 (moves_push.bend): a statement with no while (NW) ends with any
# fuel (ends.nw), out of memory or not.

def NW(s: Cr.Cir.Stmt) -> Bool:
  match s:
    case Cr.Cir.Stmt.nop{}:
      True{}
    case Cr.Cir.Stmt.set{_, _}:
      True{}
    case Cr.Cir.Stmt.store{_, _, _}:
      True{}
    case Cr.Cir.Stmt.alloc{_}:
      True{}
    case Cr.Cir.Stmt.emit{_}:
      False{}
    case Cr.Cir.Stmt.seq{a, b}:
      Bool.and(NW(a), NW(b))
    case Cr.Cir.Stmt.if{_, a, b}:
      Bool.and(NW(a), NW(b))
    case Cr.Cir.Stmt.while{_, _}:
      False{}
    case Cr.Cir.Stmt.halt{_}:
      True{}

def Calm(o: Cr.Cir.Out) -> Data:
  D.P2(D.Ends(o), D.NoOom(o))

def calm.set.of(regs: Maybe<&2, List<&2, U32>>, st: Cr.Cir.State) -> Calm(Cr.Cir.exec.set.of(regs, st)):
  match regs st:
    case Some{_} Cr.Cir.State{_, _, _, _, _, _, _, _, _, _}:
      (Unit{}, Unit{})
    case None{} _:
      (Unit{}, Unit{})

def calm.set(r: Nat, v: Maybe<&2, U32>, +st: Cr.Cir.State) -> Calm(Cr.Cir.exec.set(r, v, st)):
  match v st:
    case Some{+x} Cr.Cir.State{+regs, +m, +nx, +fi, +im, +pg, +lim, +inp, +out, +outn}:
      calm.set.of(Cr.Cir.regs.set(regs, r, x), Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, out, outn})
    case None{} _:
      (Unit{}, Unit{})

def calm.store.if(ok: Bool, k: Nat, +i: U32, v: U32, st: Cr.Cir.State) -> Calm(Cr.Cir.exec.store.if(ok, k, i, v, st)):
  match ok st:
    case True{} Cr.Cir.State{_, _, _, _, _, _, _, _, _, _}:
      (Unit{}, Unit{})
    case False{} _:
      (Unit{}, Unit{})

def calm.store(k: Nat, c: Maybe<&2, U32>, v: Maybe<&2, U32>, +st: Cr.Cir.State) -> Calm(Cr.Cir.exec.store(k, c, v, st)):
  match c v st:
    case Some{+i} Some{+x} Cr.Cir.State{+regs, +m, +nx, +fi, +im, +pg, +lim, +inp, +out, +outn}:
      calm.store.if(Cr.Cir.is_cell(i, im, fi, nx), k, i, x, Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, out, outn})
    case Some{_} None{} _:
      (Unit{}, Unit{})
    case None{} _ _:
      (Unit{}, Unit{})

def ends.then(o: Cr.Cir.Out, -k: Cr.Cir.State -> Cr.Cir.Out, d: D.Ends(o), g: @st: Cr.Cir.State -> D.Ends(k(st))) ->
  D.Ends(Cr.Cir.exec.then(o, k)):
  match o:
    case Cr.Cir.Out.next{st}:
      g(st)
    case Cr.Cir.Out.halt{_, _}:
      Unit{}
    case Cr.Cir.Out.out_of_memory{}:
      Unit{}
    case Cr.Cir.Out.trap{}:
      Unit{}
    case Cr.Cir.Out.not_done{}:
      d

def ends.if.of(zero: Bool, -yes: Unit -> Cr.Cir.Out, -no: Unit -> Cr.Cir.Out, dy: D.Ends(yes(Unit{})), dn: D.Ends(no(Unit{}))) ->
  D.Ends(Cr.Cir.exec.if.of(zero, yes, no)):
  match zero:
    case False{}:
      dy
    case True{}:
      dn

def ends.if(c: Maybe<&2, U32>, -yes: Unit -> Cr.Cir.Out, -no: Unit -> Cr.Cir.Out, dy: D.Ends(yes(Unit{})), dn: D.Ends(no(Unit{}))) ->
  D.Ends(Cr.Cir.exec.if(c, yes, no)):
  match c:
    case Some{x}:
      ends.if.of(U32.is_zero(x), yes, no, dy, dn)
    case None{}:
      Unit{}

def ends.took(r: Nat, +i: U32, st: Cr.Cir.State, next: U32, pages: U32) -> D.Ends(Cr.Cir.exec.took(r, i, st, next, pages)):
  match st:
    case Cr.Cir.State{+regs, +m, _, +fi, +im, _, +lim, +inp, +out, +outn}:
      D.Ex.fst(D.Ends(Cr.Cir.exec.set(r, Some{i}, Cr.Cir.State{regs, Cr.Cir.Cells.set(m, i, Cr.Cir.Cell.zero()), next, fi, im, pages, lim, inp, out, outn})),
        _ => D.NoOom(Cr.Cir.exec.set(r, Some{i}, Cr.Cir.State{regs, Cr.Cir.Cells.set(m, i, Cr.Cir.Cell.zero()), next, fi, im, pages, lim, inp, out, outn})),
        calm.set(r, Some{i}, Cr.Cir.State{regs, Cr.Cir.Cells.set(m, i, Cr.Cir.Cell.zero()), next, fi, im, pages, lim, inp, out, outn}))

def ends.bump.of(r: Nat, +next: U32, st: Cr.Cir.State, pages: Maybe<&2, U32>) -> D.Ends(Cr.Cir.exec.bump.of(r, next, st, pages)):
  match pages:
    case Some{p}:
      ends.took(r, next, st, U32.inc(next), p)
    case None{}:
      Unit{}

def ends.bump.if(fits: Bool, r: Nat, +next: U32, +pages: U32, lim: U32, st: Cr.Cir.State) -> D.Ends(Cr.Cir.exec.bump.if(fits, r, next, pages, lim, st)):
  match fits:
    case True{}:
      ends.bump.of(r, next, st, Cr.Cir.room(U32.add(Cr.Cir.at(next), 19), pages, lim))
    case False{}:
      Unit{}

def ends.alloc.if(no_out: Bool, r: Nat, +st: Cr.Cir.State) -> D.Ends(Cr.Cir.exec.alloc.if(no_out, r, st)):
  match no_out st:
    case True{} Cr.Cir.State{+regs, +m, +nx, +fi, +im, +pg, +lim, +inp, +out, +outn}:
      ends.bump.if(U32.is_lt(nx, 214748364), r, nx, pg, lim, Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, out, outn})
    case False{} _:
      Unit{}

def ends.alloc(r: Nat, +st: Cr.Cir.State) -> D.Ends(Cr.Cir.exec.alloc(r, st)):
  match st:
    case Cr.Cir.State{+regs, +m, +nx, +fi, +im, +pg, +lim, +inp, +out, +outn}:
      ends.alloc.if(U32.is_zero(outn), r, Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, out, outn})

def ends.nw(+f: Nat, s: Cr.Cir.Stmt, +st: Cr.Cir.State, +h: {NW(s) == True{} : Bool}) -> D.Ends(Cr.Cir.exec(f, s, st)):
  match f:
    case 0n:
      match s:
        case Cr.Cir.Stmt.nop{}:
          Unit{}
        case Cr.Cir.Stmt.set{+r, +e}:
          D.Ex.fst(D.Ends(Cr.Cir.exec.set(r, Cr.Cir.eval(e, st), st)), _ => D.NoOom(Cr.Cir.exec.set(r, Cr.Cir.eval(e, st), st)),
            calm.set(r, Cr.Cir.eval(e, st), st))
        case Cr.Cir.Stmt.store{+k, +c, +v}:
          D.Ex.fst(D.Ends(Cr.Cir.exec.store(k, Cr.Cir.eval(c, st), Cr.Cir.eval(v, st), st)),
            _ => D.NoOom(Cr.Cir.exec.store(k, Cr.Cir.eval(c, st), Cr.Cir.eval(v, st), st)),
            calm.store(k, Cr.Cir.eval(c, st), Cr.Cir.eval(v, st), st))
        case Cr.Cir.Stmt.alloc{r}:
          ends.alloc(r, st)
        case Cr.Cir.Stmt.emit{v}:
          D.bool.ft(D.Ends(Cr.Cir.exec(0n, Cr.Cir.Stmt.emit{v}, st)), h)
        case Cr.Cir.Stmt.seq{+a, +b}:
          +ha = D.and.l(NW(a), NW(b), h)
          +hb = D.and.r(NW(a), NW(b), h)
          ends.then(Cr.Cir.exec(0n, a, st), t => Cr.Cir.exec(0n, b, t), ends.nw(0n, a, st, ha), t => ends.nw(0n, b, t, hb))
        case Cr.Cir.Stmt.if{+c, +a, +b}:
          +ha = D.and.l(NW(a), NW(b), h)
          +hb = D.and.r(NW(a), NW(b), h)
          ends.if(Cr.Cir.eval(c, st), u => Cr.Cir.exec(0n, a, st), u => Cr.Cir.exec(0n, b, st), ends.nw(0n, a, st, ha), ends.nw(0n, b, st, hb))
        case Cr.Cir.Stmt.while{c, b}:
          D.bool.ft(D.Ends(Cr.Cir.exec(0n, Cr.Cir.Stmt.while{c, b}, st)), h)
        case Cr.Cir.Stmt.halt{_}:
          Unit{}
    case 1n+g:
      match s:
        case Cr.Cir.Stmt.nop{}:
          Unit{}
        case Cr.Cir.Stmt.set{+r, +e}:
          D.Ex.fst(D.Ends(Cr.Cir.exec.set(r, Cr.Cir.eval(e, st), st)), _ => D.NoOom(Cr.Cir.exec.set(r, Cr.Cir.eval(e, st), st)),
            calm.set(r, Cr.Cir.eval(e, st), st))
        case Cr.Cir.Stmt.store{+k, +c, +v}:
          D.Ex.fst(D.Ends(Cr.Cir.exec.store(k, Cr.Cir.eval(c, st), Cr.Cir.eval(v, st), st)),
            _ => D.NoOom(Cr.Cir.exec.store(k, Cr.Cir.eval(c, st), Cr.Cir.eval(v, st), st)),
            calm.store(k, Cr.Cir.eval(c, st), Cr.Cir.eval(v, st), st))
        case Cr.Cir.Stmt.alloc{r}:
          ends.alloc(r, st)
        case Cr.Cir.Stmt.emit{v}:
          D.bool.ft(D.Ends(Cr.Cir.exec(1n+g, Cr.Cir.Stmt.emit{v}, st)), h)
        case Cr.Cir.Stmt.seq{+a, +b}:
          +ha = D.and.l(NW(a), NW(b), h)
          +hb = D.and.r(NW(a), NW(b), h)
          ends.then(Cr.Cir.exec(1n+g, a, st), t => Cr.Cir.exec(1n+g, b, t), ends.nw(1n+g, a, st, ha), t => ends.nw(1n+g, b, t, hb))
        case Cr.Cir.Stmt.if{+c, +a, +b}:
          +ha = D.and.l(NW(a), NW(b), h)
          +hb = D.and.r(NW(a), NW(b), h)
          ends.if(Cr.Cir.eval(c, st), u => Cr.Cir.exec(1n+g, a, st), u => Cr.Cir.exec(1n+g, b, st), ends.nw(1n+g, a, st, ha),
            ends.nw(1n+g, b, st, hb))
        case Cr.Cir.Stmt.while{c, b}:
          D.bool.ft(D.Ends(Cr.Cir.exec(1n+g, Cr.Cir.Stmt.while{c, b}, st)), h)
        case Cr.Cir.Stmt.halt{_}:
          Unit{}

# Eval in the frames
# ------------------
#
# A focus with a step makes its frames' term step there (step.plugs), when
# the frames are as AF.ok says: a frame's other part that goes first is a
# value, with no step.

# the step of App q a u, a a value with no step and q live, from u's
def app.sx(+q: Bk.Quan, +a: Bk.Term, +u: Bk.Term, -u2: Bk.Term, sf: Maybe<Bk.Term>, vf: Bool, live: Bool, sx: Maybe<Bk.Term>, vx: Bool,
  r: Maybe<Bk.Term>, e1: {sf == None{} : Maybe<Bk.Term>}, e2: {vf == True{} : Bool}, e3: {live == True{} : Bool},
  e4: {sx == Some{u2} : Maybe<Bk.Term>}) ->
  {El.Eval.step.app(q, a, u, sf, vf, live, sx, vx, r) == Some{Bk.Term.App{q, a, u2}} : Maybe<Bk.Term>}:
  %Equal.sym(Maybe<Bk.Term>, sf, None{}, e1) : {El.Eval.step.app(q, a, u, _, vf, live, sx, vx, r) == Some{Bk.Term.App{q, a, u2}} : Maybe<Bk.Term>}
  %Equal.sym(Bool, vf, True{}, e2) : {El.Eval.step.app(q, a, u, None{}, _, live, sx, vx, r) == Some{Bk.Term.App{q, a, u2}} : Maybe<Bk.Term>}
  %Equal.sym(Bool, live, True{}, e3) : {El.Eval.step.app(q, a, u, None{}, True{}, _, sx, vx, r) == Some{Bk.Term.App{q, a, u2}} : Maybe<Bk.Term>}
  %Equal.sym(Maybe<Bk.Term>, sx, Some{u2}, e4) : {El.Eval.step.app(q, a, u, None{}, True{}, True{}, _, vx, r) == Some{Bk.Term.App{q, a, u2}} : Maybe<Bk.Term>}
  {==}

# the step of Tup q a u, from u's, a a value with no step when q is live
def tupa.s(+q: Bk.Quan, +a: Bk.Term, +u: Bk.Term, -u2: Bk.Term, live: Bool, sa: Maybe<Bk.Term>, va: Bool, sb: Maybe<Bk.Term>,
  +ok: {Bool.or(Bool.not(live), va) == True{} : Bool}, hsa: {va == True{} : Bool} -> {sa == None{} : Maybe<Bk.Term>},
  e: {sb == Some{u2} : Maybe<Bk.Term>}) -> {El.Eval.step.tup(q, a, u, live, sa, va, sb) == Some{Bk.Term.Tup{q, a, u2}} : Maybe<Bk.Term>}:
  match live:
    case False{}:
      %Equal.sym(Maybe<Bk.Term>, sb, Some{u2}, e) : {El.Eval.step.tup(q, a, u, False{}, sa, va, _) == Some{Bk.Term.Tup{q, a, u2}} : Maybe<Bk.Term>}
      {==}
    case True{}:
      %Equal.sym(Maybe<Bk.Term>, sb, Some{u2}, e) : {El.Eval.step.tup(q, a, u, True{}, sa, va, _) == Some{Bk.Term.Tup{q, a, u2}} : Maybe<Bk.Term>}
      %Equal.sym(Bool, va, True{}, ok) : {El.Eval.step.tup(q, a, u, True{}, sa, _, Some{u2}) == Some{Bk.Term.Tup{q, a, u2}} : Maybe<Bk.Term>}
      %Equal.sym(Maybe<Bk.Term>, sa, None{}, hsa(ok)) : {El.Eval.step.tup(q, a, u, True{}, _, True{}, Some{u2}) == Some{Bk.Term.Tup{q, a, u2}} : Maybe<Bk.Term>}
      {==}

# the step of Min a u, a a value with no step, from u's
def mina.s(+a: Bk.Term, +u: Bk.Term, -u2: Bk.Term, sa: Maybe<Bk.Term>, va: Bool, sb: Maybe<Bk.Term>, vb: Bool, mt: Maybe<Bk.Term>,
  e1: {sa == None{} : Maybe<Bk.Term>}, e2: {va == True{} : Bool}, e3: {sb == Some{u2} : Maybe<Bk.Term>}) ->
  {El.Eval.step.min(a, u, sa, va, sb, vb, mt) == Some{Bk.Term.Min{a, u2}} : Maybe<Bk.Term>}:
  %Equal.sym(Maybe<Bk.Term>, sa, None{}, e1) : {El.Eval.step.min(a, u, _, va, sb, vb, mt) == Some{Bk.Term.Min{a, u2}} : Maybe<Bk.Term>}
  %Equal.sym(Bool, va, True{}, e2) : {El.Eval.step.min(a, u, None{}, _, sb, vb, mt) == Some{Bk.Term.Min{a, u2}} : Maybe<Bk.Term>}
  %Equal.sym(Maybe<Bk.Term>, sb, Some{u2}, e3) : {El.Eval.step.min(a, u, None{}, True{}, _, vb, mt) == Some{Bk.Term.Min{a, u2}} : Maybe<Bk.Term>}
  {==}

# one frame around a focus u that steps to u2
def step1(+ds: List<&2, Bk.Def>, fr: D.AF, +u: Bk.Term, -u2: Bk.Term, +ok: D.AF.ok(ds, fr),
  +hs: {El.Eval.step(ds, u) == Some{u2} : Maybe<Bk.Term>}) ->
  {El.Eval.step(ds, D.A.plug(fr, u)) == Some{D.A.plug(fr, u2)} : Maybe<Bk.Term>}:
  match fr:
    case D.AF{+kind, +q, +k, +a, +b}:
      match kind:
        case D.FK.arg{}:
          %Equal.sym(Maybe<Bk.Term>, El.Eval.step(ds, u), Some{u2}, hs) : {El.Eval.step.app(q, u, a, _, El.Eval.vals(ds, u, False{}), El.Quan.live(q), El.Eval.step(ds, a), El.Eval.vals(ds, a, False{}),
            El.Eval.redex(ds, q, u, a)) == Some{Bk.Term.App{q, u2, a}} : Maybe<Bk.Term>}
          {==}
        case D.FK.val{}:
          %Equal.sym(Maybe<Bk.Term>, El.Eval.step(ds, u), Some{u2}, hs) : {El.Eval.step.app(q, u, a, _, El.Eval.vals(ds, u, False{}), El.Quan.live(q), El.Eval.step(ds, a), El.Eval.vals(ds, a, False{}),
            El.Eval.redex(ds, q, u, a)) == Some{Bk.Term.App{q, u2, a}} : Maybe<Bk.Term>}
          {==}
        case D.FK.fun{}:
          +el = and.l(El.Quan.live(q), El.Eval.vals(ds, a, False{}), ok)
          +ea = and.r(El.Quan.live(q), El.Eval.vals(ds, a, False{}), ok)
          app.sx(q, a, u, u2, El.Eval.step(ds, a), El.Eval.vals(ds, a, False{}), El.Quan.live(q), El.Eval.step(ds, u), El.Eval.vals(ds, u, False{}),
            El.Eval.redex(ds, q, a, u), K.ev.stops(ds, a, ea), ea, el, hs)
        case D.FK.let{}:
          %Equal.sym(Bool, El.Quan.live(q), True{}, ok) :
            {El.Eval.step.let(q, u, a, _, El.Eval.step(ds, u), El.Eval.vals(ds, u, False{}), El.Quan.fits(q, u)) == Some{Bk.Term.Let{q, u2, a}} : Maybe<Bk.Term>}
          %Equal.sym(Maybe<Bk.Term>, El.Eval.step(ds, u), Some{u2}, hs) : {El.Eval.step.let(q, u, a, True{}, _, El.Eval.vals(ds, u, False{}), El.Quan.fits(q, u)) == Some{Bk.Term.Let{q, u2, a}} : Maybe<Bk.Term>}
          {==}
        case D.FK.tupb{}:
          %Equal.sym(Bool, El.Quan.live(q), True{}, ok) :
            {El.Eval.step.tup(q, u, a, _, El.Eval.step(ds, u), El.Eval.vals(ds, u, False{}), El.Eval.step(ds, a)) == Some{Bk.Term.Tup{q, u2, a}} : Maybe<Bk.Term>}
          %Equal.sym(Maybe<Bk.Term>, El.Eval.step(ds, u), Some{u2}, hs) : {El.Eval.step.tup(q, u, a, True{}, _, El.Eval.vals(ds, u, False{}), El.Eval.step(ds, a)) == Some{Bk.Term.Tup{q, u2, a}} : Maybe<Bk.Term>}
          {==}
        case D.FK.tupa{}:
          tupa.s(q, a, u, u2, El.Quan.live(q), El.Eval.step(ds, a), El.Eval.vals(ds, a, False{}), El.Eval.step(ds, u), ok,
            e => K.ev.stops(ds, a, e), hs)
        case D.FK.rwt{}:
          %Equal.sym(Maybe<Bk.Term>, El.Eval.step(ds, u), Some{u2}, hs) : {El.Eval.step.rwt(u, a, b, _, El.Eval.vals(ds, u, False{})) == Some{Bk.Term.Rwt{u2, a, b}} : Maybe<Bk.Term>}
          {==}
        case D.FK.minb{}:
          %Equal.sym(Maybe<Bk.Term>, El.Eval.step(ds, u), Some{u2}, hs) : {El.Eval.step.min(u, a, _, El.Eval.vals(ds, u, False{}), El.Eval.step(ds, a), El.Eval.vals(ds, a, False{}), El.Eval.meet(u, a)) ==
            Some{Bk.Term.Min{u2, a}} : Maybe<Bk.Term>}
          {==}
        case D.FK.mina{}:
          mina.s(a, u, u2, El.Eval.step(ds, a), El.Eval.vals(ds, a, False{}), El.Eval.step(ds, u), El.Eval.vals(ds, u, False{}), El.Eval.meet(a, u),
            K.ev.stops(ds, a, ok), ok, hs)

# a focus u that steps to u2 makes its frames' term step to the frames around u2
def step.plugs(+ds: List<&2, Bk.Def>, fs: List<&2, D.AF>, +u: Bk.Term, -u2: Bk.Term, hfs: D.AFs.ok(ds, fs),
  hs: {El.Eval.step(ds, u) == Some{u2} : Maybe<Bk.Term>}) ->
  {El.Eval.step(ds, D.A.plugs(fs, u)) == Some{D.A.plugs(fs, u2)} : Maybe<Bk.Term>}:
  match fs:
    case Nil{}:
      hs
    case Con{+fr, +rest}:
      (ok, oks) = hfs
      step.plugs(ds, rest, D.A.plug(fr, u), D.A.plug(fr, u2), oks, step1(ds, fr, u, u2, ok, hs))

# Registers
# ---------
#
# A list of 63 registers is RG of its first four and R59.of the rest (rg.of).

# xs has exactly n items
def Has(n: Nat, xs: List<&2, U32>) -> Data:
  match n xs:
    case 0n Nil{}:
      Unit
    case 1n+k Con{_, rest}:
      Has(k, rest)
    case _ _:
      Empty

def nat.pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+k:
      k

def has.len(xs: List<&2, U32>, n: Nat, h: {List.length(&2, U32, xs) == n : Nat}) -> Has(n, xs):
  match xs n:
    case Nil{} 0n:
      Unit{}
    case Nil{} 1n+k:
      D.bool.ft(Has(1n+k, Nil{}), Equal.cong(Nat, Bool, x => Nat.is_eq(x, 0n), 1n+k, 0n, Equal.sym(Nat, 0n, 1n+k, h)))
    case Con{x, rest} 0n:
      D.bool.ft(Has(0n, Con{x, rest}), Equal.cong(Nat, Bool, y => Nat.is_eq(y, 0n), 1n+List.length(&2, U32, rest), 0n, h))
    case Con{_, rest} 1n+k:
      has.len(rest, k, Equal.cong(Nat, Nat, y => nat.pred(y), 1n+List.length(&2, U32, rest), 1n+k, h))

# the registers of RG, as rg.of reads them from a list
def Rg.of(+xs: List<&2, U32>) -> List<&2, U32>:
  D.RG(Maybe.default(&2, U32, List.get(&2, U32, xs, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 1n), 0),
    Maybe.default(&2, U32, List.get(&2, U32, xs, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 3n), 0),
    D.R59.list(D.R59.of(xs)))

def rg.go(xs: List<&2, U32>, hh: Has(63n, xs)) -> {xs == Rg.of(xs) : List<&2, U32>}:
  match xs:
    case Nil{}:
      match hh:
    case Con{x0, r0}:
      match r0:
        case Nil{}:
          match hh:
        case Con{x1, r1}:
          match r1:
            case Nil{}:
              match hh:
            case Con{x2, r2}:
              match r2:
                case Nil{}:
                  match hh:
                case Con{x3, r3}:
                  match r3:
                    case Nil{}:
                      match hh:
                    case Con{x4, r4}:
                      match r4:
                        case Nil{}:
                          match hh:
                        case Con{x5, r5}:
                          match r5:
                            case Nil{}:
                              match hh:
                            case Con{x6, r6}:
                              match r6:
                                case Nil{}:
                                  match hh:
                                case Con{x7, r7}:
                                  match r7:
                                    case Nil{}:
                                      match hh:
                                    case Con{x8, r8}:
                                      match r8:
                                        case Nil{}:
                                          match hh:
                                        case Con{x9, r9}:
                                          match r9:
                                            case Nil{}:
                                              match hh:
                                            case Con{x10, r10}:
                                              match r10:
                                                case Nil{}:
                                                  match hh:
                                                case Con{x11, r11}:
                                                  match r11:
                                                    case Nil{}:
                                                      match hh:
                                                    case Con{x12, r12}:
                                                      match r12:
                                                        case Nil{}:
                                                          match hh:
                                                        case Con{x13, r13}:
                                                          match r13:
                                                            case Nil{}:
                                                              match hh:
                                                            case Con{x14, r14}:
                                                              match r14:
                                                                case Nil{}:
                                                                  match hh:
                                                                case Con{x15, r15}:
                                                                  match r15:
                                                                    case Nil{}:
                                                                      match hh:
                                                                    case Con{x16, r16}:
                                                                      match r16:
                                                                        case Nil{}:
                                                                          match hh:
                                                                        case Con{x17, r17}:
                                                                          match r17:
                                                                            case Nil{}:
                                                                              match hh:
                                                                            case Con{x18, r18}:
                                                                              match r18:
                                                                                case Nil{}:
                                                                                  match hh:
                                                                                case Con{x19, r19}:
                                                                                  match r19:
                                                                                    case Nil{}:
                                                                                      match hh:
                                                                                    case Con{x20, r20}:
                                                                                      match r20:
                                                                                        case Nil{}:
                                                                                          match hh:
                                                                                        case Con{x21, r21}:
                                                                                          match r21:
                                                                                            case Nil{}:
                                                                                              match hh:
                                                                                            case Con{x22, r22}:
                                                                                              match r22:
                                                                                                case Nil{}:
                                                                                                  match hh:
                                                                                                case Con{x23, r23}:
                                                                                                  match r23:
                                                                                                    case Nil{}:
                                                                                                      match hh:
                                                                                                    case Con{x24, r24}:
                                                                                                      match r24:
                                                                                                        case Nil{}:
                                                                                                          match hh:
                                                                                                        case Con{x25, r25}:
                                                                                                          match r25:
                                                                                                            case Nil{}:
                                                                                                              match hh:
                                                                                                            case Con{x26, r26}:
                                                                                                              match r26:
                                                                                                                case Nil{}:
                                                                                                                  match hh:
                                                                                                                case Con{x27, r27}:
                                                                                                                  match r27:
                                                                                                                    case Nil{}:
                                                                                                                      match hh:
                                                                                                                    case Con{x28, r28}:
                                                                                                                      match r28:
                                                                                                                        case Nil{}:
                                                                                                                          match hh:
                                                                                                                        case Con{x29, r29}:
                                                                                                                          match r29:
                                                                                                                            case Nil{}:
                                                                                                                              match hh:
                                                                                                                            case Con{x30, r30}:
                                                                                                                              match r30:
                                                                                                                                case Nil{}:
                                                                                                                                  match hh:
                                                                                                                                case Con{x31, r31}:
                                                                                                                                  match r31:
                                                                                                                                    case Nil{}:
                                                                                                                                      match hh:
                                                                                                                                    case Con{x32, r32}:
                                                                                                                                      match r32:
                                                                                                                                        case Nil{}:
                                                                                                                                          match hh:
                                                                                                                                        case Con{x33, r33}:
                                                                                                                                          match r33:
                                                                                                                                            case Nil{}:
                                                                                                                                              match hh:
                                                                                                                                            case Con{x34, r34}:
                                                                                                                                              match r34:
                                                                                                                                                case Nil{}:
                                                                                                                                                  match hh:
                                                                                                                                                case Con{x35, r35}:
                                                                                                                                                  match r35:
                                                                                                                                                    case Nil{}:
                                                                                                                                                      match hh:
                                                                                                                                                    case Con{x36, r36}:
                                                                                                                                                      match r36:
                                                                                                                                                        case Nil{}:
                                                                                                                                                          match hh:
                                                                                                                                                        case Con{x37, r37}:
                                                                                                                                                          match r37:
                                                                                                                                                            case Nil{}:
                                                                                                                                                              match hh:
                                                                                                                                                            case Con{x38, r38}:
                                                                                                                                                              match r38:
                                                                                                                                                                case Nil{}:
                                                                                                                                                                  match hh:
                                                                                                                                                                case Con{x39, r39}:
                                                                                                                                                                  match r39:
                                                                                                                                                                    case Nil{}:
                                                                                                                                                                      match hh:
                                                                                                                                                                    case Con{x40, r40}:
                                                                                                                                                                      match r40:
                                                                                                                                                                        case Nil{}:
                                                                                                                                                                          match hh:
                                                                                                                                                                        case Con{x41, r41}:
                                                                                                                                                                          match r41:
                                                                                                                                                                            case Nil{}:
                                                                                                                                                                              match hh:
                                                                                                                                                                            case Con{x42, r42}:
                                                                                                                                                                              match r42:
                                                                                                                                                                                case Nil{}:
                                                                                                                                                                                  match hh:
                                                                                                                                                                                case Con{x43, r43}:
                                                                                                                                                                                  match r43:
                                                                                                                                                                                    case Nil{}:
                                                                                                                                                                                      match hh:
                                                                                                                                                                                    case Con{x44, r44}:
                                                                                                                                                                                      match r44:
                                                                                                                                                                                        case Nil{}:
                                                                                                                                                                                          match hh:
                                                                                                                                                                                        case Con{x45, r45}:
                                                                                                                                                                                          match r45:
                                                                                                                                                                                            case Nil{}:
                                                                                                                                                                                              match hh:
                                                                                                                                                                                            case Con{x46, r46}:
                                                                                                                                                                                              match r46:
                                                                                                                                                                                                case Nil{}:
                                                                                                                                                                                                  match hh:
                                                                                                                                                                                                case Con{x47, r47}:
                                                                                                                                                                                                  match r47:
                                                                                                                                                                                                    case Nil{}:
                                                                                                                                                                                                      match hh:
                                                                                                                                                                                                    case Con{x48, r48}:
                                                                                                                                                                                                      match r48:
                                                                                                                                                                                                        case Nil{}:
                                                                                                                                                                                                          match hh:
                                                                                                                                                                                                        case Con{x49, r49}:
                                                                                                                                                                                                          match r49:
                                                                                                                                                                                                            case Nil{}:
                                                                                                                                                                                                              match hh:
                                                                                                                                                                                                            case Con{x50, r50}:
                                                                                                                                                                                                              match r50:
                                                                                                                                                                                                                case Nil{}:
                                                                                                                                                                                                                  match hh:
                                                                                                                                                                                                                case Con{x51, r51}:
                                                                                                                                                                                                                  match r51:
                                                                                                                                                                                                                    case Nil{}:
                                                                                                                                                                                                                      match hh:
                                                                                                                                                                                                                    case Con{x52, r52}:
                                                                                                                                                                                                                      match r52:
                                                                                                                                                                                                                        case Nil{}:
                                                                                                                                                                                                                          match hh:
                                                                                                                                                                                                                        case Con{x53, r53}:
                                                                                                                                                                                                                          match r53:
                                                                                                                                                                                                                            case Nil{}:
                                                                                                                                                                                                                              match hh:
                                                                                                                                                                                                                            case Con{x54, r54}:
                                                                                                                                                                                                                              match r54:
                                                                                                                                                                                                                                case Nil{}:
                                                                                                                                                                                                                                  match hh:
                                                                                                                                                                                                                                case Con{x55, r55}:
                                                                                                                                                                                                                                  match r55:
                                                                                                                                                                                                                                    case Nil{}:
                                                                                                                                                                                                                                      match hh:
                                                                                                                                                                                                                                    case Con{x56, r56}:
                                                                                                                                                                                                                                      match r56:
                                                                                                                                                                                                                                        case Nil{}:
                                                                                                                                                                                                                                          match hh:
                                                                                                                                                                                                                                        case Con{x57, r57}:
                                                                                                                                                                                                                                          match r57:
                                                                                                                                                                                                                                            case Nil{}:
                                                                                                                                                                                                                                              match hh:
                                                                                                                                                                                                                                            case Con{x58, r58}:
                                                                                                                                                                                                                                              match r58:
                                                                                                                                                                                                                                                case Nil{}:
                                                                                                                                                                                                                                                  match hh:
                                                                                                                                                                                                                                                case Con{x59, r59}:
                                                                                                                                                                                                                                                  match r59:
                                                                                                                                                                                                                                                    case Nil{}:
                                                                                                                                                                                                                                                      match hh:
                                                                                                                                                                                                                                                    case Con{x60, r60}:
                                                                                                                                                                                                                                                      match r60:
                                                                                                                                                                                                                                                        case Nil{}:
                                                                                                                                                                                                                                                          match hh:
                                                                                                                                                                                                                                                        case Con{x61, r61}:
                                                                                                                                                                                                                                                          match r61:
                                                                                                                                                                                                                                                            case Nil{}:
                                                                                                                                                                                                                                                              match hh:
                                                                                                                                                                                                                                                            case Con{x62, r62}:
                                                                                                                                                                                                                                                              match r62:
                                                                                                                                                                                                                                                                case Nil{}:
                                                                                                                                                                                                                                                                  {==}
                                                                                                                                                                                                                                                                case Con{_, _}:
                                                                                                                                                                                                                                                                  match hh:

def rg.of(+xs: List<&2, U32>, hl: {List.length(&2, U32, xs) == 63n : Nat}) -> {xs == Rg.of(xs) : List<&2, U32>}:
  rg.go(xs, has.len(xs, 63n, hl))


# The round to M.redex
# --------------------
#
# From mode 1 with the top frame sp: M.ret's tests take the frame's branch
# (App q □ a with q dead or a known, or App q g □), registers x and y get
# the function and the argument, M.pop moves sp to the pend list, and the
# round goes on with M.redex (pre.app, pre.fun).

# the registers when M.redex starts: h, tag, q, x, y, fr set, sp the next
# frame, pend the old top frame
def R.pre(+regs: List<&2, U32>, +m: Cr.Cir.Cells, +sp: U32, +T: U32, +vx: U32, +vy: U32) -> List<&2, U32>:
  X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(regs, 9n, sp), 10n, T), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)),
    11n, vx), 12n, vy), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp)

# the state when M.redex starts
def S.pre(+regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>,
  +sp: U32, +pend: U32, +T: U32, +vx: U32, +vy: U32) -> Cr.Cir.State:
  X.X.st(R.pre(regs, m, sp, T, vx, vy), X.X.put(m, 1n, sp, pend), nx, fi, im, pg, lim, inp)

# x and y set, M.pop, then M.redex
def pre.tail(+f: Nat, +ex: Cr.Cir.Expr, +ey: Cr.Cir.Expr, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32,
  +lim: U32, +inp: List<&2, Word(8n)>, +sp: U32, +pend: U32, +T: U32, +vx: U32, +vy: U32,
  hl: {List.length(&2, U32, regs) == 63n : Nat},
  h2: {List.get(&2, U32, regs, 2n) == Some{sp} : Maybe<&2, U32>}, h3: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>},
  hc: {Cr.Cir.is_cell(sp, im, fi, nx) == True{} : Bool},
  ehx: {Cr.Cir.eval(ex, X.X.st(X.X.set(X.X.set(X.X.set(regs, 9n, sp), 10n, T), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), m, nx, fi, im, pg, lim, inp)) == Some{vx} : Maybe<&2, U32>},
  ehy: {Cr.Cir.eval(ey, X.X.st(X.X.set(X.X.set(X.X.set(X.X.set(regs, 9n, sp), 10n, T), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, vx), m, nx, fi, im, pg, lim, inp)) == Some{vy} : Maybe<&2, U32>}) ->
  {Cr.Cir.exec(f, Mc.M.redex(), S.pre(regs, m, nx, fi, im, pg, lim, inp, sp, pend, T, vx, vy)) ==
    Cr.Cir.exec(f, Mc.M.do([Mc.M.set(11n, ex), Mc.M.set(12n, ey), Mc.M.pop(), Mc.M.redex()]),
      X.X.st(X.X.set(X.X.set(X.X.set(regs, 9n, sp), 10n, T), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), m, nx, fi, im, pg, lim, inp)) : Cr.Cir.Out}:
  +Q = U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)
  +r1 = X.X.set(regs, 9n, sp)
  +r2 = X.X.set(r1, 10n, T)
  +r3 = X.X.set(r2, 14n, Q)
  +r4 = X.X.set(r3, 11n, vx)
  +r5 = X.X.set(r4, 12n, vy)
  +l3 = X.L.len(r2, 14n, Q, 63n, X.L.len(r1, 10n, T, 63n, X.L.len(regs, 9n, sp, 63n, hl)))
  +l4 = X.L.len(r3, 11n, vx, 63n, l3)
  +l5 = X.L.len(r4, 12n, vy, 63n, l4)
  +s3 = X.X.st(r3, m, nx, fi, im, pg, lim, inp)
  +s4 = X.X.st(r4, m, nx, fi, im, pg, lim, inp)
  +s5 = X.X.st(r5, m, nx, fi, im, pg, lim, inp)
  +g2 = X.L.go(r4, 12n, 2n, vy, sp, {==}, X.L.go(r3, 11n, 2n, vx, sp, {==}, X.L.go(r2, 14n, 2n, Q, sp, {==},
    X.L.go(r1, 10n, 2n, T, sp, {==}, X.L.go(regs, 9n, 2n, sp, sp, {==}, h2)))))
  +g3 = X.L.go(r4, 12n, 3n, vy, pend, {==}, X.L.go(r3, 11n, 3n, vx, pend, {==}, X.L.go(r2, 14n, 3n, Q, pend, {==},
    X.L.go(r1, 10n, 3n, T, pend, {==}, X.L.go(regs, 9n, 3n, sp, pend, {==}, h3)))))
  +lhs = {Cr.Cir.exec(f, Mc.M.redex(), S.pre(regs, m, nx, fi, im, pg, lim, inp, sp, pend, T, vx, vy)) : Cr.Cir.Out}
  +b1 = Mc.M.do([Mc.M.set(12n, ey), Mc.M.pop(), Mc.M.redex()])
  +b2 = Mc.M.do([Mc.M.pop(), Mc.M.redex()])
  +b3 = Mc.M.do([Mc.M.redex()])
  %X.rw.seq(f, Mc.M.set(11n, ex), b1, s3, s4, X.run.set(f, 11n, ex, s3, vx, ehx, l3, {==})) : {lhs == _ : Cr.Cir.Out}
  %X.rw.seq(f, Mc.M.set(12n, ey), b2, s4, s5, X.run.set(f, 12n, ey, s4, vy, ehy, l4, {==})) : {lhs == _ : Cr.Cir.Out}
  %X.rw.seq(f, Mc.M.pop(), b3, s5, S.pre(regs, m, nx, fi, im, pg, lim, inp, sp, pend, T, vx, vy),
    X.pop.eq(f, r5, m, nx, fi, im, pg, lim, inp, sp, pend, l5, g2, g3, hc)) : {lhs == _ : Cr.Cir.Out}
  X.rw.seq_nop(f, Mc.M.redex(), S.pre(regs, m, nx, fi, im, pg, lim, inp, sp, pend, T, vx, vy))

# 63 registers
def rg.len(rest: D.R59, +foc: U32, +md: U32, +sp: U32, +pend: U32) -> {List.length(&2, U32, D.RG(foc, md, sp, pend, D.R59.list(rest))) == 63n : Nat}:
  match rest:
    case D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}:
      {==}

# the test of App q □ a, when q is dead or a known: 0
def cond0(q: Bk.Quan, k: Bool, hs: {Bool.and(El.Quan.live(q), Bool.not(k)) == False{} : Bool}) ->
  {Wa.Wasm.op(Wa.Wasm.Op.and{}, Wa.Wasm.op(Wa.Wasm.Op.ne{}, Mc.Img.quan(q), 0), Bool.to_u32(U32.is_zero(Bool.to_u32(k)))) == 0 : U32}:
  match q k:
    case Bk.Quan.Q0{} True{}:
      {==}
    case Bk.Quan.Q0{} False{}:
      {==}
    case Bk.Quan.Q1{} True{}:
      {==}
    case Bk.Quan.Q1{} False{}:
      D.bool.ft({Wa.Wasm.op(Wa.Wasm.Op.and{}, Wa.Wasm.op(Wa.Wasm.Op.ne{}, 1, 0), Bool.to_u32(U32.is_zero(Bool.to_u32(False{})))) == 0 : U32}, Equal.sym(Bool, True{}, False{}, hs))
    case Bk.Quan.Q2{} True{}:
      {==}
    case Bk.Quan.Q2{} False{}:
      D.bool.ft({Wa.Wasm.op(Wa.Wasm.Op.and{}, Wa.Wasm.op(Wa.Wasm.Op.ne{}, 2, 0), Bool.to_u32(U32.is_zero(Bool.to_u32(False{})))) == 0 : U32}, Equal.sym(Bool, True{}, False{}, hs))

# M.ret's tests, to an App q □ a frame: its branch
def disp.app(+f: Nat, kind: D.FK, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32,
  +inp: List<&2, Word(8n)>, +sp: U32, hk: {K.FK.isapp(kind) == True{} : Bool}, hl: {List.length(&2, U32, regs) == 63n : Nat},
  h1: {List.get(&2, U32, regs, 1n) == Some{1} : Maybe<&2, U32>}, h2: {List.get(&2, U32, regs, 2n) == Some{sp} : Maybe<&2, U32>},
  hz: {U32.is_eq(sp, 0) == False{} : Bool}, hc: {Cr.Cir.is_cell(sp, im, fi, nx) == True{} : Bool},
  ht: {D.Tg(m, sp) == D.FK.tag(kind) : U32}) ->
  {Cr.Cir.exec(f, X.sel.t(X.X.chain(0n)), X.ret.st(regs, m, nx, fi, im, pg, lim, inp, sp, D.FK.tag(kind))) ==
    Cr.Cir.exec(f, X.X.body(), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) : Cr.Cir.Out}:
  match kind:
    case D.FK.arg{}:
      Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, X.X.body(), X.X.st(regs, m, nx, fi, im, pg, lim, inp)),
        Cr.Cir.exec(f, X.sel.t(X.X.chain(0n)), X.ret.st(regs, m, nx, fi, im, pg, lim, inp, sp, 32)),
        X.ret.disp.app(f, regs, m, nx, fi, im, pg, lim, inp, sp, hl, h1, h2, hz, hc, ht))
    case D.FK.val{}:
      Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, X.X.body(), X.X.st(regs, m, nx, fi, im, pg, lim, inp)),
        Cr.Cir.exec(f, X.sel.t(X.X.chain(0n)), X.ret.st(regs, m, nx, fi, im, pg, lim, inp, sp, 33)),
        X.ret.disp.val(f, regs, m, nx, fi, im, pg, lim, inp, sp, hl, h1, h2, hz, hc, ht))
    case D.FK.fun{}:
      D.bool.ft({Cr.Cir.exec(f, X.sel.t(X.X.chain(0n)), X.ret.st(regs, m, nx, fi, im, pg, lim, inp, sp, 34)) ==
        Cr.Cir.exec(f, X.X.body(), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) : Cr.Cir.Out}, hk)
    case D.FK.let{}:
      D.bool.ft({Cr.Cir.exec(f, X.sel.t(X.X.chain(0n)), X.ret.st(regs, m, nx, fi, im, pg, lim, inp, sp, 35)) ==
        Cr.Cir.exec(f, X.X.body(), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) : Cr.Cir.Out}, hk)
    case D.FK.tupb{}:
      D.bool.ft({Cr.Cir.exec(f, X.sel.t(X.X.chain(0n)), X.ret.st(regs, m, nx, fi, im, pg, lim, inp, sp, 36)) ==
        Cr.Cir.exec(f, X.X.body(), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) : Cr.Cir.Out}, hk)
    case D.FK.tupa{}:
      D.bool.ft({Cr.Cir.exec(f, X.sel.t(X.X.chain(0n)), X.ret.st(regs, m, nx, fi, im, pg, lim, inp, sp, 37)) ==
        Cr.Cir.exec(f, X.X.body(), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) : Cr.Cir.Out}, hk)
    case D.FK.rwt{}:
      D.bool.ft({Cr.Cir.exec(f, X.sel.t(X.X.chain(0n)), X.ret.st(regs, m, nx, fi, im, pg, lim, inp, sp, 38)) ==
        Cr.Cir.exec(f, X.X.body(), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) : Cr.Cir.Out}, hk)
    case D.FK.minb{}:
      D.bool.ft({Cr.Cir.exec(f, X.sel.t(X.X.chain(0n)), X.ret.st(regs, m, nx, fi, im, pg, lim, inp, sp, 39)) ==
        Cr.Cir.exec(f, X.X.body(), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) : Cr.Cir.Out}, hk)
    case D.FK.mina{}:
      D.bool.ft({Cr.Cir.exec(f, X.sel.t(X.X.chain(0n)), X.ret.st(regs, m, nx, fi, im, pg, lim, inp, sp, 40)) ==
        Cr.Cir.exec(f, X.X.body(), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) : Cr.Cir.Out}, hk)

# a round from mode 1 with App q □ a on top, q dead or a known: M.redex of
# the focus and a
def pre.app(+f: Nat, +kind: D.FK, +rest: D.R59, +foc: U32, +sp: U32, +pend: U32, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +q: Bk.Quan, +k: Bool, hk: {K.FK.isapp(kind) == True{} : Bool},
  hs: {Bool.and(El.Quan.live(q), Bool.not(k)) == False{} : Bool}, hz: {U32.is_eq(sp, 0) == False{} : Bool},
  +hc: {Cr.Cir.is_cell(sp, im, fi, nx) == True{} : Bool}, ht: {D.Tg(m, sp) == D.FK.tag(kind) : U32},
  hq: D.Qs(Cr.Cir.Cells.get(m, sp), q), hkn: {D.Fl(m, sp, 2048) == k : Bool}) ->
  {Cr.Cir.exec(f, Mc.M.redex(), S.pre(D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, nx, fi, im, pg, lim, inp, sp, pend, D.FK.tag(kind), foc, D.Fd(2n, m, sp))) ==
    Cr.Cir.exec(f, D.B.body(), D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)) : Cr.Cir.Out}:
  +regs = D.RG(foc, 1, sp, pend, D.R59.list(rest))
  +hl = rg.len(rest, foc, 1, sp, pend)
  +T = D.FK.tag(kind)
  +Q = U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)
  +r1 = X.X.set(regs, 9n, sp)
  +r2 = X.X.set(r1, 10n, T)
  +r3 = X.X.set(r2, 14n, Q)
  +l2 = X.L.len(r1, 10n, T, 63n, X.L.len(regs, 9n, sp, 63n, hl))
  +s3 = X.X.st(r3, m, nx, fi, im, pg, lim, inp)
  +T0 = X.sel.t(X.X.chain(0n))
  +g9 = X.L.go(r2, 14n, 9n, Q, sp, {==}, X.L.go(r1, 10n, 9n, T, sp, {==}, X.L.gs(regs, 9n, sp, X.L.lt(regs, 9n, hl, {==}))))
  +g14 = X.L.gs(r2, 14n, Q, X.L.lt(r2, 14n, l2, {==}))
  +ev = X.ev.op(Wa.Wasm.Op.and{}, Mc.M.ne(Mc.M.g(14n), Mc.M.c(0)), Mc.M.not(Mc.M.flag(Mc.M.g(9n), 2048)), s3,
    Wa.Wasm.op(Wa.Wasm.Op.ne{}, Q, 0), Bool.to_u32(U32.is_zero(Bool.to_u32(k))),
    X.ev.op(Wa.Wasm.Op.ne{}, Mc.M.g(14n), Mc.M.c(0), s3, Q, 0, g14, {==}),
    X.ev.notflag(9n, s3, sp, 2048, k, g9, hc, hkn))
  +ev0 = {(%cond0(q, k, hs) : {Cr.Cir.eval(X.sel.c(T0), s3) == Some{_} : Maybe<&2, U32>};
    %hq : {Cr.Cir.eval(X.sel.c(T0), s3) == Some{Wa.Wasm.op(Wa.Wasm.Op.and{}, Wa.Wasm.op(Wa.Wasm.Op.ne{}, _, 0), Bool.to_u32(U32.is_zero(Bool.to_u32(k))))} : Maybe<&2, U32>};
    ev) : {Cr.Cir.eval(X.sel.c(T0), s3) == Some{0} : Maybe<&2, U32>}}
  +g9b = X.L.go(r3, 11n, 9n, foc, sp, {==}, g9)
  +e1 = disp.app(f, kind, regs, m, nx, fi, im, pg, lim, inp, sp, hk, hl, {==}, {==}, hz, hc, ht)
  +e2 = X.rw.if.e(f, X.sel.c(T0), X.sel.t(T0), X.sel.e(T0), s3, ev0)
  +e3 = pre.tail(f, Mc.M.g(0n), Mc.M.f(2n, Mc.M.g(9n)), regs, m, nx, fi, im, pg, lim, inp, sp, pend, T, foc, D.Fd(2n, m, sp), hl, {==}, {==}, hc,
    {==}, X.ev.fld(2n, Mc.M.g(9n), X.X.st(X.X.set(r3, 11n, foc), m, nx, fi, im, pg, lim, inp), sp, g9b, hc))
  Equal.trans(Cr.Cir.Out, Cr.Cir.exec(f, Mc.M.redex(), S.pre(regs, m, nx, fi, im, pg, lim, inp, sp, pend, T, foc, D.Fd(2n, m, sp))),
    Cr.Cir.exec(f, X.sel.e(T0), s3), Cr.Cir.exec(f, D.B.body(), D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)), e3,
    Equal.trans(Cr.Cir.Out, Cr.Cir.exec(f, X.sel.e(T0), s3), Cr.Cir.exec(f, T0, s3),
      Cr.Cir.exec(f, D.B.body(), D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)), e2, e1))

# a round from mode 1 with App q g □ on top: M.redex of g and the focus
def pre.fun(+f: Nat, +rest: D.R59, +foc: U32, +sp: U32, +pend: U32, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, hz: {U32.is_eq(sp, 0) == False{} : Bool},
  +hc: {Cr.Cir.is_cell(sp, im, fi, nx) == True{} : Bool}, ht: {D.Tg(m, sp) == 34 : U32}) ->
  {Cr.Cir.exec(f, Mc.M.redex(), S.pre(D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, nx, fi, im, pg, lim, inp, sp, pend, 34, D.Fd(2n, m, sp), foc)) ==
    Cr.Cir.exec(f, D.B.body(), D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)) : Cr.Cir.Out}:
  +regs = D.RG(foc, 1, sp, pend, D.R59.list(rest))
  +hl = rg.len(rest, foc, 1, sp, pend)
  +Q = U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)
  +r1 = X.X.set(regs, 9n, sp)
  +r2 = X.X.set(r1, 10n, 34)
  +r3 = X.X.set(r2, 14n, Q)
  +s3 = X.X.st(r3, m, nx, fi, im, pg, lim, inp)
  +g9 = X.L.go(r2, 14n, 9n, Q, sp, {==}, X.L.go(r1, 10n, 9n, 34, sp, {==}, X.L.gs(regs, 9n, sp, X.L.lt(regs, 9n, hl, {==}))))
  +e1 = Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, X.X.body(), X.X.st(regs, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(f, X.sel.t(X.X.chain(1n)), s3),
    X.ret.disp.fun(f, regs, m, nx, fi, im, pg, lim, inp, sp, hl, {==}, {==}, hz, hc, ht))
  +e3 = pre.tail(f, Mc.M.f(2n, Mc.M.g(9n)), Mc.M.g(0n), regs, m, nx, fi, im, pg, lim, inp, sp, pend, 34, D.Fd(2n, m, sp), foc, hl, {==}, {==}, hc,
    X.ev.fld(2n, Mc.M.g(9n), s3, sp, g9, hc), {==})
  Equal.trans(Cr.Cir.Out, Cr.Cir.exec(f, Mc.M.redex(), S.pre(regs, m, nx, fi, im, pg, lim, inp, sp, pend, 34, D.Fd(2n, m, sp), foc)),
    Cr.Cir.exec(f, X.sel.t(X.X.chain(1n)), s3), Cr.Cir.exec(f, D.B.body(), D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)), e3, e1)

# The pop
# -------
#
# M.pop stores pend in field 1 of the top frame sp (m1: sp's cell x1) and puts
# sp in the pend list: the frame's pointer to its term y leaves the cells for
# the roots, so every count Ptr stays (ptr.pop, by induction on the cells
# from fi, with sp among them once, as swap_moves.bend's Pc.mv), and so does
# the heap (heap.pop). The frames past sp are not sp (their chain is shorter,
# Hops, copied from swap_moves.bend), and keep their facts (frs.pop).

# Nat algebra (swap_moves.bend's, copied)
def add.comm(+a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, N.add_zero(b))
    case 1n+p:
      Equal.trans(Nat, 1n+Nat.add(p, b), 1n+Nat.add(b, p), Nat.add(b, 1n+p),
        Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, b), Nat.add(b, p), add.comm(p, b)),
        Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), N.add_succ_r(b, p)))

def add.assoc(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(Nat.add(p, b), c), Nat.add(p, Nat.add(b, c)), add.assoc(p, b, c))

# (a + b) + c = (c + b) + a
def add.swap3(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(Nat.add(c, b), a) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(a, b), c), Nat.add(c, Nat.add(a, b)), Nat.add(Nat.add(c, b), a),
    add.comm(Nat.add(a, b), c),
    Equal.trans(Nat, Nat.add(c, Nat.add(a, b)), Nat.add(c, Nat.add(b, a)), Nat.add(Nat.add(c, b), a),
      Equal.cong(Nat, Nat, y => Nat.add(c, y), Nat.add(a, b), Nat.add(b, a), add.comm(a, b)),
      Equal.sym(Nat, Nat.add(Nat.add(c, b), a), Nat.add(c, Nat.add(b, a)), add.assoc(c, b, a))))

# a cell past z is not z (swap_moves.bend's, copied)
def ne.lt.b(b: Bool, +o: U32, +z: U32, eb: {U32.is_eq(o, z) == b : Bool}, h: N.Le(1n+U32.to_nat(z), U32.to_nat(o))) ->
  {U32.is_eq(o, z) == False{} : Bool}:
  match b:
    case False{}:
      eb
    case True{}:
      +e = D.u32.eq(o, z, eb)
      Empty.absurd({U32.is_eq(o, z) == False{} : Bool},
        N.not_succ_le(U32.to_nat(z), (%e : N.Le(1n+U32.to_nat(z), U32.to_nat(_)); h)))

def ne.lt(+o: U32, +z: U32, h: N.Le(1n+U32.to_nat(z), U32.to_nat(o))) -> {U32.is_eq(o, z) == False{} : Bool}:
  ne.lt.b(U32.is_eq(o, z), o, z, {==}, h)

# a cell of a tag below 19 is not z, whose tag is 19 or more (swap_moves.bend's, copied)
def tg.ne.b(b: Bool, +m: Cr.Cir.Cells, +y: U32, +z: U32, eb: {U32.is_eq(y, z) == b : Bool},
  hy: {U32.is_lt(D.Tg(m, y), 19) == True{} : Bool}, hz: {U32.is_lt(D.Tg(m, z), 19) == False{} : Bool}) ->
  {U32.is_eq(y, z) == False{} : Bool}:
  match b:
    case False{}:
      eb
    case True{}:
      +e = D.u32.eq(y, z, eb)
      +hz2 = {(%Equal.sym(U32, y, z, e) : {U32.is_lt(D.Tg(m, _), 19) == False{} : Bool}; hz) : {U32.is_lt(D.Tg(m, y), 19) == False{} : Bool}}
      D.bool.ft({U32.is_eq(y, z) == False{} : Bool},
        Equal.trans(Bool, False{}, U32.is_lt(D.Tg(m, y), 19), True{}, Equal.sym(Bool, U32.is_lt(D.Tg(m, y), 19), False{}, hz2), hy))

def tg.ne(+m: Cr.Cir.Cells, +y: U32, +z: U32, hy: {U32.is_lt(D.Tg(m, y), 19) == True{} : Bool},
  hz: {U32.is_lt(D.Tg(m, z), 19) == False{} : Bool}) -> {U32.is_eq(y, z) == False{} : Bool}:
  tg.ne.b(U32.is_eq(y, z), m, y, z, {==}, hy, hz)

# the tag of a pointer, as LtC says it (swap_moves.bend's, copied)
def ltc.tg(+y: U32, +c: Cr.Cir.Cell, +im: U32, +fi: U32, +nx: U32, h: {D.LtC(y, c, im, fi, nx) == True{} : Bool}) ->
  {U32.is_lt(D.TgW(Cr.Cir.Cell.get(0n, c)), 19) == True{} : Bool}:
  +f0 = Cr.Cir.Cell.get(0n, c)
  D.and.r(U32.is_lt(y, nx), U32.is_lt(D.TgW(f0), 19),
    D.and.l(Bool.and(U32.is_lt(y, nx), U32.is_lt(D.TgW(f0), 19)),
      Bool.and(Cr.Cir.is_cell(y, im, fi, nx), Bool.or(D.Own(fi, nx, y), D.FlW(f0, 1024))), h))

# no pointer of xs, to a term cell, is z, whose tag is 19 or more (swap_moves.bend's, copied)
def rcl.none(xs: List<&2, U32>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +z: U32,
  +hz: {U32.is_lt(D.Tg(m, z), 19) == False{} : Bool},
  h: {D.Lt.all(xs, m, im, fi, nx) == True{} : Bool}) -> {D.RcL(xs, z) == 0n : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      +h2 = h
      +hy = D.and.l(D.LtC(y, Cr.Cir.Cells.get(m, y), im, fi, nx), D.Lt.all(rest, m, im, fi, nx), h2)
      +ne = tg.ne(m, y, z, ltc.tg(y, Cr.Cir.Cells.get(m, y), im, fi, nx, hy), hz)
      %Equal.sym(Bool, U32.is_eq(y, z), False{}, ne) : {Nat.add(D.Nat.of(_), D.RcL(rest, z)) == 0n : Nat}
      rcl.none(rest, m, im, fi, nx, z, hz, D.and.r(D.LtC(y, Cr.Cir.Cells.get(m, y), im, fi, nx), D.Lt.all(rest, m, im, fi, nx), h2))

# no cell points to z, whose tag is 19 or more (swap_moves.bend's, copied)
def pc.none(k: Nat, +m: Cr.Cir.Cells, +ps: List<&2, U32>, +o: U32, +im: U32, +fi: U32, +nx: U32, +z: U32,
  +hz: {U32.is_lt(D.Tg(m, z), 19) == False{} : Bool}, h: {D.Pts(k, m, ps, o, im, fi, nx) == True{} : Bool}) ->
  {D.Pc(k, m, ps, o, z) == 0n : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+(+j):
      +h2 = h
      %Equal.sym(Nat, D.RcL(D.Fs(m, ps, o), z), 0n,
        rcl.none(D.Fs(m, ps, o), m, im, fi, nx, z, hz,
          D.and.l(D.Lt.all(D.Fs(m, ps, o), m, im, fi, nx), D.Pts(j, m, ps, U32.inc(o), im, fi, nx), h2))) :
        {Nat.add(_, D.Pc(j, m, ps, U32.inc(o), z)) == 0n : Nat}
      pc.none(j, m, ps, U32.inc(o), im, fi, nx, z, hz, D.and.r(D.Lt.all(D.Fs(m, ps, o), m, im, fi, nx), D.Pts(j, m, ps, U32.inc(o), im, fi, nx), h2))

# the pointers xs, to term cells, after a store to z, whose tag is 19 or more (swap_moves.bend's, copied)
def lt.tg(xs: List<&2, U32>, +m: Cr.Cir.Cells, +z: U32, +x: Cr.Cir.Cell, +im: U32, +fi: U32, +nx: U32,
  +hz: {U32.is_lt(D.Tg(m, z), 19) == False{} : Bool},
  h: {D.Lt.all(xs, m, im, fi, nx) == True{} : Bool}) -> {D.Lt.all(xs, Cr.Cir.Cells.set(m, z, x), im, fi, nx) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      +M2 = Cr.Cir.Cells.set(m, z, x)
      +h2 = h
      +hy = D.and.l(D.LtC(y, Cr.Cir.Cells.get(m, y), im, fi, nx), D.Lt.all(rest, m, im, fi, nx), h2)
      +ne = tg.ne(m, y, z, ltc.tg(y, Cr.Cir.Cells.get(m, y), im, fi, nx, hy), hz)
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, y), Cr.Cir.Cells.get(m, y), D.cl.go(m, y, z, x, ne)) :
        {Bool.and(D.LtC(y, _, im, fi, nx), D.Lt.all(rest, M2, im, fi, nx)) == True{} : Bool}
      D.and.i(D.LtC(y, Cr.Cir.Cells.get(m, y), im, fi, nx), D.Lt.all(rest, M2, im, fi, nx), hy,
        lt.tg(rest, m, z, x, im, fi, nx, hz, D.and.r(D.LtC(y, Cr.Cir.Cells.get(m, y), im, fi, nx), D.Lt.all(rest, m, im, fi, nx), h2)))

# The pend list with one more cell
# --------------------------------

# a cell other than z is in Con{z, ps} as in ps
def mem.out(+z: U32, +ps: List<&2, U32>, +o: U32, ne: {U32.is_eq(z, o) == False{} : Bool}) ->
  {D.Mem(Con{z, ps}, o) == D.Mem(ps, o) : Bool}:
  %Equal.sym(Bool, U32.is_eq(z, o), False{}, ne) : {Bool.or(_, D.Mem(ps, o)) == D.Mem(ps, o) : Bool}
  {==}

# Fs's body, by its tag and its membership in the pend list
def FsT(+tg: U32, +mem: Bool, +a: U32, +y: Cr.Cir.Cell) -> List<&2, U32>:
  Bool.pick(List<&2, U32>, U32.is_lt(tg, 19), D.Fs.term(a, Cr.Cir.Cell.get(2n, y), Cr.Cir.Cell.get(3n, y), Cr.Cir.Cell.get(4n, y)),
    Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_le(32, tg), U32.is_le(tg, 40)), Bool.not(mem)),
      Con{Cr.Cir.Cell.get(2n, y), D.Fs.opt(U32.is_eq(tg, 38), Cr.Cir.Cell.get(3n, y), Nil{})},
      Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_eq(tg, 41), D.FlW(Cr.Cir.Cell.get(0n, y), 4096)), Bool.not(mem)),
        [Cr.Cir.Cell.get(2n, y)], Nil{})))

# a cell other than z holds the same pointers with z in the pend list
def fs.ps(+m: Cr.Cir.Cells, +z: U32, +ps: List<&2, U32>, +o: U32, ne: {U32.is_eq(z, o) == False{} : Bool}) ->
  {D.Fs(m, Con{z, ps}, o) == D.Fs(m, ps, o) : List<&2, U32>}:
  +tg = D.TgW(D.Fd(0n, m, o))
  %Equal.sym(Bool, D.Mem(Con{z, ps}, o), D.Mem(ps, o), mem.out(z, ps, o, ne)) :
    {FsT(tg, _, D.Fd(2n, m, U32.add(272, tg)), Cr.Cir.Cells.get(m, o)) == D.Fs(m, ps, o) : List<&2, U32>}
  {==}

# the table's cell of a term cell is no own cell past 290
def tblat(+m: Cr.Cir.Cells, +o: U32, +z: U32, hz: N.Le(1n+U32.to_nat(290), U32.to_nat(z))) -> {D.TblAt(m, o, z) == True{} : Bool}:
  D.and.l(D.TblAt(m, o, z), D.TblR(0n, m, U32.inc(o), z), D.TblR.of(1n, m, o, z, hz))

# the cell sp after M.pop's store: field 1 holds pend
def X1(+m: Cr.Cir.Cells, +sp: U32, +pend: U32) -> Cr.Cir.Cell:
  Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, sp), pend)

def M1(+m: Cr.Cir.Cells, +sp: U32, +pend: U32) -> Cr.Cir.Cells:
  Cr.Cir.Cells.set(m, sp, X1(m, sp, pend))

def g0.s1(y: Cr.Cir.Cell, -v: U32) -> {Cr.Cir.Cell.get(0n, Cr.Cir.Cell.set(1n, y, v)) == Cr.Cir.Cell.get(0n, y) : U32}:
  match y:
    case Cr.Cir.Cell{a, b, c, d, e}:
      {==}

def g1.s1(y: Cr.Cir.Cell, -v: U32) -> {Cr.Cir.Cell.get(1n, Cr.Cir.Cell.set(1n, y, v)) == v : U32}:
  match y:
    case Cr.Cir.Cell{a, b, c, d, e}:
      {==}

def g2.s1(y: Cr.Cir.Cell, -v: U32) -> {Cr.Cir.Cell.get(2n, Cr.Cir.Cell.set(1n, y, v)) == Cr.Cir.Cell.get(2n, y) : U32}:
  match y:
    case Cr.Cir.Cell{a, b, c, d, e}:
      {==}

def g3.s1(y: Cr.Cir.Cell, -v: U32) -> {Cr.Cir.Cell.get(3n, Cr.Cir.Cell.set(1n, y, v)) == Cr.Cir.Cell.get(3n, y) : U32}:
  match y:
    case Cr.Cir.Cell{a, b, c, d, e}:
      {==}

# field 0 of the cell sp after M.pop's store
def pop.f0(+m: Cr.Cir.Cells, +sp: U32, +pend: U32) -> {D.Fd(0n, M1(m, sp, pend), sp) == D.Fd(0n, m, sp) : U32}:
  Equal.trans(U32, D.Fd(0n, M1(m, sp, pend), sp), Cr.Cir.Cell.get(0n, X1(m, sp, pend)), D.Fd(0n, m, sp),
    Equal.cong(Cr.Cir.Cell, U32, y => Cr.Cir.Cell.get(0n, y), Cr.Cir.Cells.get(M1(m, sp, pend), sp), X1(m, sp, pend), D.cl.gs(m, sp, X1(m, sp, pend))),
    g0.s1(Cr.Cir.Cells.get(m, sp), pend))

# every cell but sp holds the same pointers after M.pop
def he.pop(+m: Cr.Cir.Cells, +sp: U32, +pend: U32, +ps: List<&2, U32>, +hz: N.Le(1n+U32.to_nat(290), U32.to_nat(sp)),
  +o: U32, +ne: {U32.is_eq(o, sp) == False{} : Bool}) ->
  {D.Fs(M1(m, sp, pend), Con{sp, ps}, o) == D.Fs(m, ps, o) : List<&2, U32>}:
  Equal.trans(List<&2, U32>, D.Fs(M1(m, sp, pend), Con{sp, ps}, o), D.Fs(M1(m, sp, pend), ps, o), D.Fs(m, ps, o),
    fs.ps(M1(m, sp, pend), sp, ps, o, D.ne.sym(o, sp, ne)), D.fs.eq(m, sp, X1(m, sp, pend), ps, o, ne, tblat(m, o, sp, hz)))

# a frame's pointers, by its kind: its field 2 (but Rwt)
def fst.ok(kind: D.FK, +a: U32, +y: Cr.Cir.Cell, h38: {U32.is_eq(D.FK.tag(kind), 38) == False{} : Bool}) ->
  {FsT(D.FK.tag(kind), False{}, a, y) == [Cr.Cir.Cell.get(2n, y)] : List<&2, U32>}:
  match kind:
    case D.FK.arg{}:
      {==}
    case D.FK.val{}:
      {==}
    case D.FK.fun{}:
      {==}
    case D.FK.let{}:
      {==}
    case D.FK.tupb{}:
      {==}
    case D.FK.tupa{}:
      {==}
    case D.FK.rwt{}:
      D.bool.ft({FsT(38, False{}, a, y) == [Cr.Cir.Cell.get(2n, y)] : List<&2, U32>}, Equal.sym(Bool, True{}, False{}, h38))
    case D.FK.minb{}:
      {==}
    case D.FK.mina{}:
      {==}

# a frame in the pend list holds no pointer
def fst1.ok(kind: D.FK, +a: U32, +y: Cr.Cir.Cell) -> {FsT(D.FK.tag(kind), True{}, a, y) == Nil{} : List<&2, U32>}:
  match kind:
    case D.FK.arg{}:
      {==}
    case D.FK.val{}:
      {==}
    case D.FK.fun{}:
      {==}
    case D.FK.let{}:
      {==}
    case D.FK.tupb{}:
      {==}
    case D.FK.tupa{}:
      {==}
    case D.FK.rwt{}:
      {==}
    case D.FK.minb{}:
      {==}
    case D.FK.mina{}:
      {==}

# the top frame's pointers: its term's cell
def fs.top(kind: D.FK, +m: Cr.Cir.Cells, +ps: List<&2, U32>, +sp: U32, h38: {U32.is_eq(D.FK.tag(kind), 38) == False{} : Bool},
  ht: {D.Tg(m, sp) == D.FK.tag(kind) : U32}, hm: {D.Mem(ps, sp) == False{} : Bool}) -> {D.Fs(m, ps, sp) == [D.Fd(2n, m, sp)] : List<&2, U32>}:
  +y = Cr.Cir.Cells.get(m, sp)
  +a = D.Fd(2n, m, U32.add(272, D.Tg(m, sp)))
  %Equal.sym(Bool, D.Mem(ps, sp), False{}, hm) : {FsT(D.Tg(m, sp), _, a, y) == [D.Fd(2n, m, sp)] : List<&2, U32>}
  %Equal.sym(U32, D.Tg(m, sp), D.FK.tag(kind), ht) : {FsT(_, False{}, a, y) == [D.Fd(2n, m, sp)] : List<&2, U32>}
  fst.ok(kind, a, y, h38)

# a frame's tag
def fk.tag(kind: D.FK) -> {Bool.and(Bool.and(U32.is_le(32, D.FK.tag(kind)), U32.is_le(D.FK.tag(kind), 40)), Bool.not(U32.is_lt(D.FK.tag(kind), 19))) == True{} : Bool}:
  match kind:
    case D.FK.arg{}:
      {==}
    case D.FK.val{}:
      {==}
    case D.FK.fun{}:
      {==}
    case D.FK.let{}:
      {==}
    case D.FK.tupb{}:
      {==}
    case D.FK.tupa{}:
      {==}
    case D.FK.rwt{}:
      {==}
    case D.FK.minb{}:
      {==}
    case D.FK.mina{}:
      {==}

def fk.lt19(kind: D.FK) -> {U32.is_lt(D.FK.tag(kind), 19) == False{} : Bool}:
  match kind:
    case D.FK.arg{}:
      {==}
    case D.FK.val{}:
      {==}
    case D.FK.fun{}:
      {==}
    case D.FK.let{}:
      {==}
    case D.FK.tupb{}:
      {==}
    case D.FK.tupa{}:
      {==}
    case D.FK.rwt{}:
      {==}
    case D.FK.minb{}:
      {==}
    case D.FK.mina{}:
      {==}

# the old top frame holds no pointer once in the pend list
def fs.top1(kind: D.FK, +m: Cr.Cir.Cells, +ps: List<&2, U32>, +sp: U32, +pend: U32, ht: {D.Tg(m, sp) == D.FK.tag(kind) : U32}) ->
  {D.Fs(M1(m, sp, pend), Con{sp, ps}, sp) == Nil{} : List<&2, U32>}:
  +y = Cr.Cir.Cells.get(M1(m, sp, pend), sp)
  +a = D.Fd(2n, M1(m, sp, pend), U32.add(272, D.Tg(M1(m, sp, pend), sp)))
  %Equal.sym(Bool, U32.is_eq(sp, sp), True{}, D.u32.refl(sp)) : {FsT(D.Tg(M1(m, sp, pend), sp), Bool.or(_, D.Mem(ps, sp)), a, y) == Nil{} : List<&2, U32>}
  %Equal.sym(U32, D.Tg(M1(m, sp, pend), sp), D.FK.tag(kind),
    Equal.trans(U32, D.Tg(M1(m, sp, pend), sp), D.Tg(m, sp), D.FK.tag(kind),
      Equal.cong(U32, U32, w => U32.and(w, 63), D.Fd(0n, M1(m, sp, pend), sp), D.Fd(0n, m, sp), pop.f0(m, sp, pend)), ht)) :
    {FsT(_, True{}, a, y) == Nil{} : List<&2, U32>}
  fst1.ok(kind, a, y)

# The counts after M.pop at z: Pc of the cells M1 and the pend list z :: ps,
# which hold the pointers of m and ps at every cell but z (he), against m's
# and ps' (swap_moves.bend's Pc.out and Pc.mv, for any such change)

# the k cells from o, all past z and below nx, hold the same pointers
def pcx.out(k: Nat, +m: Cr.Cir.Cells, +ps: List<&2, U32>, +z: U32, +pend: U32, +h290: N.Le(1n+U32.to_nat(290), U32.to_nat(z)), +o: U32, +c: U32, +nx: U32,
  hz: N.Le(1n+U32.to_nat(z), U32.to_nat(o)), hb: N.Le(Nat.add(U32.to_nat(o), k), U32.to_nat(nx))) ->
  {D.Pc(k, M1(m, z, pend), Con{z, ps}, o, c) == D.Pc(k, m, ps, o, c) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+(+j):
      +hz2 = hz
      +hb2 = hb
      +lt1 = N.le_trans(1n+U32.to_nat(o), Nat.add(U32.to_nat(o), 1n+j), U32.to_nat(nx), N.lt_add(U32.to_nat(o), j), hb2)
      +ei = D.u.inc(o, nx, lt1)
      +hzi = N.le_rw_r(1n+U32.to_nat(z), 1n+U32.to_nat(o), U32.to_nat(U32.inc(o)),
        Equal.sym(Nat, U32.to_nat(U32.inc(o)), 1n+U32.to_nat(o), ei), N.le_succ(1n+U32.to_nat(z), U32.to_nat(o), hz2))
      +hbi = N.le_rw_l(Nat.add(U32.to_nat(o), 1n+j), Nat.add(U32.to_nat(U32.inc(o)), j), U32.to_nat(nx),
        Equal.trans(Nat, Nat.add(U32.to_nat(o), 1n+j), 1n+Nat.add(U32.to_nat(o), j), Nat.add(U32.to_nat(U32.inc(o)), j),
          N.add_succ_r(U32.to_nat(o), j),
          Equal.sym(Nat, Nat.add(U32.to_nat(U32.inc(o)), j), 1n+Nat.add(U32.to_nat(o), j),
            Equal.cong(Nat, Nat, y => Nat.add(y, j), U32.to_nat(U32.inc(o)), 1n+U32.to_nat(o), ei))), hb2)
      +e1 = he.pop(m, z, pend, ps, h290, o, ne.lt(o, z, hz2))
      +e2 = pcx.out(j, m, ps, z, pend, h290, U32.inc(o), c, nx, hzi, hbi)
      %Equal.sym(List<&2, U32>, D.Fs(M1(m, z, pend), Con{z, ps}, o), D.Fs(m, ps, o), e1) :
        {Nat.add(D.RcL(_, c), D.Pc(j, M1(m, z, pend), Con{z, ps}, U32.inc(o), c)) == Nat.add(D.RcL(D.Fs(m, ps, o), c), D.Pc(j, m, ps, U32.inc(o), c)) : Nat}
      %Equal.sym(Nat, D.Pc(j, M1(m, z, pend), Con{z, ps}, U32.inc(o), c), D.Pc(j, m, ps, U32.inc(o), c), e2) :
        {Nat.add(D.RcL(D.Fs(m, ps, o), c), _) == Nat.add(D.RcL(D.Fs(m, ps, o), c), D.Pc(j, m, ps, U32.inc(o), c)) : Nat}
      {==}

# the step of pcx.mv: o is z, or z is past o
def pcx.mv.b(bb: Bool, +j: Nat, +m: Cr.Cir.Cells, +ps: List<&2, U32>, +z: U32, +pend: U32, +h290: N.Le(1n+U32.to_nat(290), U32.to_nat(z)), +o: U32, +c: U32,
  +nx: U32,
  +eb: {U32.is_eq(o, z) == bb : Bool}, +h1: N.Le(U32.to_nat(o), U32.to_nat(z)),
  +h2: N.Le(1n+U32.to_nat(z), Nat.add(U32.to_nat(o), 1n+j)), +hb: N.Le(Nat.add(U32.to_nat(o), 1n+j), U32.to_nat(nx)),
  ih: N.Le(U32.to_nat(U32.inc(o)), U32.to_nat(z)) -> N.Le(1n+U32.to_nat(z), Nat.add(U32.to_nat(U32.inc(o)), j)) ->
    N.Le(Nat.add(U32.to_nat(U32.inc(o)), j), U32.to_nat(nx)) ->
    {Nat.add(D.Pc(j, M1(m, z, pend), Con{z, ps}, U32.inc(o), c), D.RcL(D.Fs(m, ps, z), c)) ==
      Nat.add(D.Pc(j, m, ps, U32.inc(o), c), D.RcL(D.Fs(M1(m, z, pend), Con{z, ps}, z), c)) : Nat}) ->
  {Nat.add(D.Pc(1n+j, M1(m, z, pend), Con{z, ps}, o, c), D.RcL(D.Fs(m, ps, z), c)) ==
    Nat.add(D.Pc(1n+j, m, ps, o, c), D.RcL(D.Fs(M1(m, z, pend), Con{z, ps}, z), c)) : Nat}:
  match bb:
    case True{}:
      +R0 = D.RcL(D.Fs(m, ps, z), c)
      +R1 = D.RcL(D.Fs(M1(m, z, pend), Con{z, ps}, z), c)
      +eadd = Equal.trans(Nat, Nat.add(U32.to_nat(o), 1n+j), 1n+Nat.add(U32.to_nat(o), j), Nat.add(1n+U32.to_nat(o), j),
        N.add_succ_r(U32.to_nat(o), j), {==})
      +eo = D.u32.eq(o, z, eb)
      +lt1 = N.le_trans(1n+U32.to_nat(o), Nat.add(U32.to_nat(o), 1n+j), U32.to_nat(nx), N.lt_add(U32.to_nat(o), j), hb)
      +ei = D.u.inc(o, nx, lt1)
      +hzo = {(%eo : N.Le(1n+U32.to_nat(_), U32.to_nat(U32.inc(o)));
        N.le_rw_r(1n+U32.to_nat(o), 1n+U32.to_nat(o), U32.to_nat(U32.inc(o)), Equal.sym(Nat, U32.to_nat(U32.inc(o)), 1n+U32.to_nat(o), ei),
          N.le_refl(1n+U32.to_nat(o)))) : N.Le(1n+U32.to_nat(z), U32.to_nat(U32.inc(o)))}
      +hbi = N.le_rw_l(Nat.add(U32.to_nat(o), 1n+j), Nat.add(U32.to_nat(U32.inc(o)), j), U32.to_nat(nx),
        Equal.trans(Nat, Nat.add(U32.to_nat(o), 1n+j), Nat.add(1n+U32.to_nat(o), j), Nat.add(U32.to_nat(U32.inc(o)), j), eadd,
          Equal.sym(Nat, Nat.add(U32.to_nat(U32.inc(o)), j), Nat.add(1n+U32.to_nat(o), j),
            Equal.cong(Nat, Nat, y => Nat.add(y, j), U32.to_nat(U32.inc(o)), 1n+U32.to_nat(o), ei))), hb)
      +e2 = pcx.out(j, m, ps, z, pend, h290, U32.inc(o), c, nx, hzo, hbi)
      %Equal.sym(U32, o, z, eo) :
        {Nat.add(Nat.add(D.RcL(D.Fs(M1(m, z, pend), Con{z, ps}, _), c), D.Pc(j, M1(m, z, pend), Con{z, ps}, U32.inc(o), c)), R0) ==
          Nat.add(Nat.add(D.RcL(D.Fs(m, ps, _), c), D.Pc(j, m, ps, U32.inc(o), c)), R1) : Nat}
      %Equal.sym(Nat, D.Pc(j, M1(m, z, pend), Con{z, ps}, U32.inc(o), c), D.Pc(j, m, ps, U32.inc(o), c), e2) :
        {Nat.add(Nat.add(R1, _), R0) == Nat.add(Nat.add(R0, D.Pc(j, m, ps, U32.inc(o), c)), R1) : Nat}
      add.swap3(R1, D.Pc(j, m, ps, U32.inc(o), c), R0)
    case False{}:
      +R0 = D.RcL(D.Fs(m, ps, z), c)
      +R1 = D.RcL(D.Fs(M1(m, z, pend), Con{z, ps}, z), c)
      +eadd = Equal.trans(Nat, Nat.add(U32.to_nat(o), 1n+j), 1n+Nat.add(U32.to_nat(o), j), Nat.add(1n+U32.to_nat(o), j),
        N.add_succ_r(U32.to_nat(o), j), {==})
      +lt = D.lt.ne(U32.cmp(o, z), U32.to_nat(o), U32.to_nat(z), N.U32.rel(o, z), eb, h1)
      +ei = D.u.inc(o, z, lt)
      +ej = Equal.trans(Nat, Nat.add(U32.to_nat(o), 1n+j), Nat.add(1n+U32.to_nat(o), j), Nat.add(U32.to_nat(U32.inc(o)), j), eadd,
        Equal.sym(Nat, Nat.add(U32.to_nat(U32.inc(o)), j), Nat.add(1n+U32.to_nat(o), j),
          Equal.cong(Nat, Nat, y => Nat.add(y, j), U32.to_nat(U32.inc(o)), 1n+U32.to_nat(o), ei)))
      +h1b = N.le_rw_l(1n+U32.to_nat(o), U32.to_nat(U32.inc(o)), U32.to_nat(z), Equal.sym(Nat, U32.to_nat(U32.inc(o)), 1n+U32.to_nat(o), ei), lt)
      +h2b = N.le_rw_r(1n+U32.to_nat(z), Nat.add(U32.to_nat(o), 1n+j), Nat.add(U32.to_nat(U32.inc(o)), j), ej, h2)
      +hbb = N.le_rw_l(Nat.add(U32.to_nat(o), 1n+j), Nat.add(U32.to_nat(U32.inc(o)), j), U32.to_nat(nx), ej, hb)
      +e1 = he.pop(m, z, pend, ps, h290, o, eb)
      +e2 = ih(h1b, h2b, hbb)
      +A = D.RcL(D.Fs(m, ps, o), c)
      +P1 = D.Pc(j, M1(m, z, pend), Con{z, ps}, U32.inc(o), c)
      +P0 = D.Pc(j, m, ps, U32.inc(o), c)
      %Equal.sym(List<&2, U32>, D.Fs(M1(m, z, pend), Con{z, ps}, o), D.Fs(m, ps, o), e1) :
        {Nat.add(Nat.add(D.RcL(_, c), P1), R0) == Nat.add(Nat.add(A, P0), R1) : Nat}
      Equal.trans(Nat, Nat.add(Nat.add(A, P1), R0), Nat.add(A, Nat.add(P1, R0)), Nat.add(Nat.add(A, P0), R1),
        add.assoc(A, P1, R0),
        Equal.trans(Nat, Nat.add(A, Nat.add(P1, R0)), Nat.add(A, Nat.add(P0, R1)), Nat.add(Nat.add(A, P0), R1),
          Equal.cong(Nat, Nat, y => Nat.add(A, y), Nat.add(P1, R0), Nat.add(P0, R1), e2),
          Equal.sym(Nat, Nat.add(Nat.add(A, P0), R1), Nat.add(A, Nat.add(P0, R1)), add.assoc(A, P0, R1))))

# z, one of the k cells from o (below nx), trades its pointers in Pc
def pcx.mv(k: Nat, +m: Cr.Cir.Cells, +ps: List<&2, U32>, +z: U32, +pend: U32, +h290: N.Le(1n+U32.to_nat(290), U32.to_nat(z)), +o: U32, +c: U32, +nx: U32,
  h1: N.Le(U32.to_nat(o), U32.to_nat(z)), h2: N.Le(1n+U32.to_nat(z), Nat.add(U32.to_nat(o), k)),
  hb: N.Le(Nat.add(U32.to_nat(o), k), U32.to_nat(nx))) ->
  {Nat.add(D.Pc(k, M1(m, z, pend), Con{z, ps}, o, c), D.RcL(D.Fs(m, ps, z), c)) == Nat.add(D.Pc(k, m, ps, o, c), D.RcL(D.Fs(M1(m, z, pend), Con{z, ps}, z), c)) : Nat}:
  match k:
    case 0n:
      Empty.absurd({Nat.add(0n, D.RcL(D.Fs(m, ps, z), c)) == Nat.add(0n, D.RcL(D.Fs(M1(m, z, pend), Con{z, ps}, z), c)) : Nat},
        N.not_succ_le(U32.to_nat(z), N.le_trans(1n+U32.to_nat(z), U32.to_nat(o), U32.to_nat(z),
          N.le_rw_r(1n+U32.to_nat(z), Nat.add(U32.to_nat(o), 0n), U32.to_nat(o), N.add_zero(U32.to_nat(o)), h2), h1)))
    case 1n+(+j):
      pcx.mv.b(U32.is_eq(o, z), j, m, ps, z, pend, h290, o, c, nx, {==}, h1, h2, hb,
        a => b => d => pcx.mv(j, m, ps, z, pend, h290, U32.inc(o), c, nx, a, b, d))

# the own cells' bounds for z, one of them
def own.lo(+fi: U32, +nx: U32, +z: U32, ho: {D.Own(fi, nx, z) == True{} : Bool}) -> N.Le(U32.to_nat(fi), U32.to_nat(z)):
  D.u.le(fi, z, D.and.l(U32.is_le(fi, z), U32.is_lt(z, nx), ho))

def own.end(+fi: U32, +nx: U32, +z: U32, ho: {D.Own(fi, nx, z) == True{} : Bool}) ->
  {Nat.add(U32.to_nat(fi), Nat.sub(U32.to_nat(nx), U32.to_nat(fi))) == U32.to_nat(nx) : Nat}:
  +ho2 = ho
  +h1 = D.u.le(fi, z, D.and.l(U32.is_le(fi, z), U32.is_lt(z, nx), ho2))
  +hl = D.u.lt(z, nx, D.and.r(U32.is_le(fi, z), U32.is_lt(z, nx), ho2))
  D.add.sub(U32.to_nat(fi), U32.to_nat(nx), N.le_trans(U32.to_nat(fi), U32.to_nat(z), U32.to_nat(nx), h1, N.weaken(U32.to_nat(z), U32.to_nat(nx), hl)))

def own.hi(+fi: U32, +nx: U32, +z: U32, ho: {D.Own(fi, nx, z) == True{} : Bool}) ->
  N.Le(1n+U32.to_nat(z), Nat.add(U32.to_nat(fi), Nat.sub(U32.to_nat(nx), U32.to_nat(fi)))):
  +ho2 = ho
  N.le_rw_r(1n+U32.to_nat(z), U32.to_nat(nx), Nat.add(U32.to_nat(fi), Nat.sub(U32.to_nat(nx), U32.to_nat(fi))),
    Equal.sym(Nat, Nat.add(U32.to_nat(fi), Nat.sub(U32.to_nat(nx), U32.to_nat(fi))), U32.to_nat(nx), own.end(fi, nx, z, ho2)),
    D.u.lt(z, nx, D.and.r(U32.is_le(fi, z), U32.is_lt(z, nx), ho2)))

def own.bd(+fi: U32, +nx: U32, +z: U32, ho: {D.Own(fi, nx, z) == True{} : Bool}) ->
  N.Le(Nat.add(U32.to_nat(fi), Nat.sub(U32.to_nat(nx), U32.to_nat(fi))), U32.to_nat(nx)):
  N.le_rw_l(U32.to_nat(nx), Nat.add(U32.to_nat(fi), Nat.sub(U32.to_nat(nx), U32.to_nat(fi))), U32.to_nat(nx),
    Equal.sym(Nat, Nat.add(U32.to_nat(fi), Nat.sub(U32.to_nat(nx), U32.to_nat(fi))), U32.to_nat(nx), own.end(fi, nx, z, ho)),
    N.le_refl(U32.to_nat(nx)))

# the counts after M.pop: the top frame's pointer to y is a root now
def ptr.pop(+m: Cr.Cir.Cells, +nx: U32, +fi: U32, +ps: List<&2, U32>, +sp: U32, +pend: U32, +y: U32, +rs: List<&2, U32>, +c: U32,
  +hz: N.Le(1n+U32.to_nat(290), U32.to_nat(sp)), ho: {D.Own(fi, nx, sp) == True{} : Bool},
  hf0: {D.Fs(m, ps, sp) == [y] : List<&2, U32>}, hf1: {D.Fs(M1(m, sp, pend), Con{sp, ps}, sp) == Nil{} : List<&2, U32>}) ->
  {D.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), M1(m, sp, pend), fi, Con{sp, ps}, Con{y, rs}, c) ==
    D.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, rs, c) : Nat}:
  +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
  +m1 = M1(m, sp, pend)
  +ps1 = {Con{sp, ps} : List<&2, U32>}
  +P1 = D.Pc(n, m1, ps1, fi, c)
  +P0 = D.Pc(n, m, ps, fi, c)
  +A = D.Nat.of(U32.is_eq(y, c))
  +B = D.RcL(rs, c)
  +ho2 = ho
  +e = {(%hf1 : {Nat.add(P1, D.RcL([y], c)) == Nat.add(P0, D.RcL(_, c)) : Nat};
    %hf0 : {Nat.add(P1, D.RcL(_, c)) == Nat.add(P0, D.RcL(D.Fs(m1, ps1, sp), c)) : Nat};
    pcx.mv(n, m, ps, sp, pend, hz, fi, c, nx, own.lo(fi, nx, sp, ho2),
      own.hi(fi, nx, sp, ho2), own.bd(fi, nx, sp, ho2))) :
    {Nat.add(P1, Nat.add(A, 0n)) == Nat.add(P0, 0n) : Nat}}
  +e2 = Equal.trans(Nat, Nat.add(P1, A), Nat.add(P1, Nat.add(A, 0n)), P0,
    Equal.cong(Nat, Nat, w => Nat.add(P1, w), A, Nat.add(A, 0n), Equal.sym(Nat, Nat.add(A, 0n), A, N.add_zero(A))),
    Equal.trans(Nat, Nat.add(P1, Nat.add(A, 0n)), Nat.add(P0, 0n), P0, e, N.add_zero(P0)))
  Equal.trans(Nat, Nat.add(P1, Nat.add(A, B)), Nat.add(Nat.add(P1, A), B), Nat.add(P0, B),
    Equal.sym(Nat, Nat.add(Nat.add(P1, A), B), Nat.add(P1, Nat.add(A, B)), add.assoc(P1, A, B)),
    Equal.cong(Nat, Nat, w => Nat.add(w, B), Nat.add(P1, A), P0, e2))

# a frame's kind keeps it out of the term cells, and may be in the pend list
def fk.pend(kind: D.FK) -> {Bool.or(U32.is_lt(D.FK.tag(kind), 19), U32.is_le(32, D.FK.tag(kind))) == True{} : Bool}:
  match kind:
    case D.FK.arg{}:
      {==}
    case D.FK.val{}:
      {==}
    case D.FK.fun{}:
      {==}
    case D.FK.let{}:
      {==}
    case D.FK.tupb{}:
      {==}
    case D.FK.tupa{}:
      {==}
    case D.FK.rwt{}:
      {==}
    case D.FK.minb{}:
      {==}
    case D.FK.mina{}:
      {==}

# the top frame's tag, after M.pop's store
def pop.tg(kind: D.FK, +m: Cr.Cir.Cells, +sp: U32, +pend: U32, ht: {D.Tg(m, sp) == D.FK.tag(kind) : U32}) ->
  {D.Tg(M1(m, sp, pend), sp) == D.FK.tag(kind) : U32}:
  Equal.trans(U32, D.Tg(M1(m, sp, pend), sp), D.Tg(m, sp), D.FK.tag(kind),
    Equal.cong(U32, U32, w => U32.and(w, 63), D.Fd(0n, M1(m, sp, pend), sp), D.Fd(0n, m, sp), pop.f0(m, sp, pend)), ht)

# no term cell
def tg.big(kind: D.FK, +m: Cr.Cir.Cells, +sp: U32, ht: {D.Tg(m, sp) == D.FK.tag(kind) : U32}) -> {U32.is_lt(D.Tg(m, sp), 19) == False{} : Bool}:
  %Equal.sym(U32, D.Tg(m, sp), D.FK.tag(kind), ht) : {U32.is_lt(_, 19) == False{} : Bool}
  fk.lt19(kind)

# CntC's body, by the cell's membership in the pend list
def CntB(+y: Cr.Cir.Cell, +P: Nat, +mem: Bool) -> Bool:
  Bool.or(Bool.not(U32.is_lt(D.TgW(Cr.Cir.Cell.get(0n, y)), 19)), Bool.or(D.FlW(Cr.Cir.Cell.get(0n, y), 1024), Bool.or(mem,
    Nat.is_eq(U32.to_nat(Cr.Cir.Cell.get(1n, y)), P))))

# Cnt at the cell o, after M.pop
def cnt.pop.at(b: Bool, +kind: D.FK, +m: Cr.Cir.Cells, +sp: U32, +pend: U32, +o: U32, +n: Nat, +fi: U32, +ps: List<&2, U32>,
  +rs1: List<&2, U32>, +rs0: List<&2, U32>, +eb: {U32.is_eq(o, sp) == b : Bool}, ht: {D.Tg(m, sp) == D.FK.tag(kind) : U32},
  hP: {D.Ptr(n, M1(m, sp, pend), fi, Con{sp, ps}, rs1, o) == D.Ptr(n, m, fi, ps, rs0, o) : Nat},
  h: {D.CntC(Cr.Cir.Cells.get(m, o), D.Ptr(n, m, fi, ps, rs0, o), ps, o) == True{} : Bool}) ->
  {D.CntC(Cr.Cir.Cells.get(M1(m, sp, pend), o), D.Ptr(n, M1(m, sp, pend), fi, Con{sp, ps}, rs1, o), Con{sp, ps}, o) == True{} : Bool}:
  match b:
    case True{}:
      +m1 = M1(m, sp, pend)
      +eo = D.u32.eq(o, sp, eb)
      +ht1 = pop.tg(kind, m, sp, pend, ht)
      %Equal.sym(U32, o, sp, eo) :
        {D.CntC(Cr.Cir.Cells.get(m1, _), D.Ptr(n, m1, fi, Con{sp, ps}, rs1, _), Con{sp, ps}, _) == True{} : Bool}
      D.or.l(Bool.not(U32.is_lt(D.Tg(m1, sp), 19)), Bool.or(D.Fl(m1, sp, 1024), Bool.or(D.Mem(Con{sp, ps}, sp),
        Nat.is_eq(U32.to_nat(D.Fd(1n, m1, sp)), D.Ptr(n, m1, fi, Con{sp, ps}, rs1, sp)))),
        (%Equal.sym(Bool, U32.is_lt(D.Tg(m1, sp), 19), False{}, tg.big(kind, m1, sp, ht1)) : {Bool.not(_) == True{} : Bool}; {==}))
    case False{}:
      +m1 = M1(m, sp, pend)
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(m1, o), Cr.Cir.Cells.get(m, o), D.cl.go(m, o, sp, X1(m, sp, pend), eb)) :
        {CntB(_, D.Ptr(n, m1, fi, Con{sp, ps}, rs1, o), D.Mem(Con{sp, ps}, o)) == True{} : Bool}
      %Equal.sym(Bool, D.Mem(Con{sp, ps}, o), D.Mem(ps, o), mem.out(sp, ps, o, D.ne.sym(o, sp, eb))) :
        {CntB(Cr.Cir.Cells.get(m, o), D.Ptr(n, m1, fi, Con{sp, ps}, rs1, o), _) == True{} : Bool}
      %Equal.sym(Nat, D.Ptr(n, m1, fi, Con{sp, ps}, rs1, o), D.Ptr(n, m, fi, ps, rs0, o), hP) :
        {CntB(Cr.Cir.Cells.get(m, o), _, D.Mem(ps, o)) == True{} : Bool}
      h

# the counts of k cells from o, after M.pop
def cnt.pop(k: Nat, +kind: D.FK, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +ps: List<&2, U32>, +sp: U32, +pend: U32, +y: U32,
  +rs: List<&2, U32>, +o: U32, +hz: N.Le(1n+U32.to_nat(290), U32.to_nat(sp)), +ho: {D.Own(fi, nx, sp) == True{} : Bool},
  +ht: {D.Tg(m, sp) == D.FK.tag(kind) : U32}, +hf0: {D.Fs(m, ps, sp) == [y] : List<&2, U32>},
  +hf1: {D.Fs(M1(m, sp, pend), Con{sp, ps}, sp) == Nil{} : List<&2, U32>},
  h: {D.Cnt(k, m, o, Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), fi, ps, rs) == True{} : Bool}) ->
  {D.Cnt(k, M1(m, sp, pend), o, Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), fi, Con{sp, ps}, Con{y, rs}) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+(+j):
      +m1 = M1(m, sp, pend)
      +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
      +h2 = h
      D.and.i(D.CntC(Cr.Cir.Cells.get(m1, o), D.Ptr(n, m1, fi, Con{sp, ps}, Con{y, rs}, o), Con{sp, ps}, o),
        D.Cnt(j, m1, U32.inc(o), n, fi, Con{sp, ps}, Con{y, rs}),
        cnt.pop.at(U32.is_eq(o, sp), kind, m, sp, pend, o, n, fi, ps, Con{y, rs}, rs, {==}, ht,
          ptr.pop(m, nx, fi, ps, sp, pend, y, rs, o, hz, ho, hf0, hf1),
          D.and.l(D.CntC(Cr.Cir.Cells.get(m, o), D.Ptr(n, m, fi, ps, rs, o), ps, o), D.Cnt(j, m, U32.inc(o), n, fi, ps, rs), h2)),
        cnt.pop(j, kind, m, nx, fi, ps, sp, pend, y, rs, U32.inc(o), hz, ho, ht, hf0, hf1,
          D.and.r(D.CntC(Cr.Cir.Cells.get(m, o), D.Ptr(n, m, fi, ps, rs, o), ps, o), D.Cnt(j, m, U32.inc(o), n, fi, ps, rs), h2)))

# the pend list's old cells, none of them sp, after M.pop
def pendok.pop(qs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +ps: List<&2, U32>, +sp: U32, +pend: U32, +y: U32,
  +rs: List<&2, U32>, +hz: N.Le(1n+U32.to_nat(290), U32.to_nat(sp)), +ho: {D.Own(fi, nx, sp) == True{} : Bool},
  +hf0: {D.Fs(m, ps, sp) == [y] : List<&2, U32>}, +hf1: {D.Fs(M1(m, sp, pend), Con{sp, ps}, sp) == Nil{} : List<&2, U32>},
  hq: {D.Mem(qs, sp) == False{} : Bool}, h: D.PendOK(qs, ps, m, fi, nx, rs)) -> D.PendOK(qs, Con{sp, ps}, M1(m, sp, pend), fi, nx, Con{y, rs}):
  match qs:
    case Nil{}:
      Unit{}
    case Con{+p, +rest}:
      (hown, r1) = h
      (hs, r2) = r1
      (htg, r3) = r2
      (hp0, r4) = r3
      +m1 = M1(m, sp, pend)
      +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
      +hq2 = hq
      +ne = D.or.f.l(U32.is_eq(p, sp), D.Mem(rest, sp), hq2)
      +ec = D.cl.go(m, p, sp, X1(m, sp, pend), ne)
      (hown, ((%Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(m1, p), Cr.Cir.Cells.get(m, p), ec) :
          {U32.is_ne(U32.and(Cr.Cir.Cell.get(0n, _), 1024), 0) == False{} : Bool}; hs),
        ((%Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(m1, p), Cr.Cir.Cells.get(m, p), ec) :
          {Bool.or(U32.is_lt(U32.and(Cr.Cir.Cell.get(0n, _), 63), 19), U32.is_le(32, U32.and(Cr.Cir.Cell.get(0n, _), 63))) == True{} : Bool}; htg),
        ((%Equal.sym(Nat, D.Ptr(n, m1, fi, Con{sp, ps}, Con{y, rs}, p), D.Ptr(n, m, fi, ps, rs, p), ptr.pop(m, nx, fi, ps, sp, pend, y, rs, p, hz, ho, hf0, hf1)) :
            {_ == 0n : Nat}; hp0),
          pendok.pop(rest, m, nx, fi, ps, sp, pend, y, rs, hz, ho, hf0, hf1, D.or.f.r(U32.is_eq(p, sp), D.Mem(rest, sp), hq2), r4)))))

# the pointers of the cell o after M.pop
def pts.pop.at(b: Bool, +m: Cr.Cir.Cells, +sp: U32, +pend: U32, +ps: List<&2, U32>, +o: U32, +im: U32, +fi: U32, +nx: U32,
  +hz: N.Le(1n+U32.to_nat(290), U32.to_nat(sp)), eb: {U32.is_eq(o, sp) == b : Bool},
  hf1: {D.Fs(M1(m, sp, pend), Con{sp, ps}, sp) == Nil{} : List<&2, U32>}, hzt: {U32.is_lt(D.Tg(m, sp), 19) == False{} : Bool},
  h: {D.Lt.all(D.Fs(m, ps, o), m, im, fi, nx) == True{} : Bool}) ->
  {D.Lt.all(D.Fs(M1(m, sp, pend), Con{sp, ps}, o), M1(m, sp, pend), im, fi, nx) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(U32, o, sp, D.u32.eq(o, sp, eb)) :
        {D.Lt.all(D.Fs(M1(m, sp, pend), Con{sp, ps}, _), M1(m, sp, pend), im, fi, nx) == True{} : Bool}
      %Equal.sym(List<&2, U32>, D.Fs(M1(m, sp, pend), Con{sp, ps}, sp), Nil{}, hf1) :
        {D.Lt.all(_, M1(m, sp, pend), im, fi, nx) == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(List<&2, U32>, D.Fs(M1(m, sp, pend), Con{sp, ps}, o), D.Fs(m, ps, o), he.pop(m, sp, pend, ps, hz, o, eb)) :
        {D.Lt.all(_, M1(m, sp, pend), im, fi, nx) == True{} : Bool}
      lt.tg(D.Fs(m, ps, o), m, sp, X1(m, sp, pend), im, fi, nx, hzt, h)

# every pointer points to a term cell, after M.pop
def pts.pop(k: Nat, +m: Cr.Cir.Cells, +sp: U32, +pend: U32, +ps: List<&2, U32>, +o: U32, +im: U32, +fi: U32, +nx: U32,
  +hz: N.Le(1n+U32.to_nat(290), U32.to_nat(sp)), +hf1: {D.Fs(M1(m, sp, pend), Con{sp, ps}, sp) == Nil{} : List<&2, U32>},
  +hzt: {U32.is_lt(D.Tg(m, sp), 19) == False{} : Bool},
  h: {D.Pts(k, m, ps, o, im, fi, nx) == True{} : Bool}) -> {D.Pts(k, M1(m, sp, pend), Con{sp, ps}, o, im, fi, nx) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+(+j):
      +m1 = M1(m, sp, pend)
      +h2 = h
      D.and.i(D.Lt.all(D.Fs(m1, Con{sp, ps}, o), m1, im, fi, nx), D.Pts(j, m1, Con{sp, ps}, U32.inc(o), im, fi, nx),
        pts.pop.at(U32.is_eq(o, sp), m, sp, pend, ps, o, im, fi, nx, hz, {==}, hf1, hzt,
          D.and.l(D.Lt.all(D.Fs(m, ps, o), m, im, fi, nx), D.Pts(j, m, ps, U32.inc(o), im, fi, nx), h2)),
        pts.pop(j, m, sp, pend, ps, U32.inc(o), im, fi, nx, hz, hf1, hzt,
          D.and.r(D.Lt.all(D.Fs(m, ps, o), m, im, fi, nx), D.Pts(j, m, ps, U32.inc(o), im, fi, nx), h2)))

# field 1 of the top frame after M.pop's store: pend
def pop.f1(+m: Cr.Cir.Cells, +sp: U32, +pend: U32) -> {D.Fd(1n, M1(m, sp, pend), sp) == pend : U32}:
  Equal.trans(U32, D.Fd(1n, M1(m, sp, pend), sp), Cr.Cir.Cell.get(1n, X1(m, sp, pend)), pend,
    Equal.cong(Cr.Cir.Cell, U32, w => Cr.Cir.Cell.get(1n, w), Cr.Cir.Cells.get(M1(m, sp, pend), sp), X1(m, sp, pend), D.cl.gs(m, sp, X1(m, sp, pend))),
    g1.s1(Cr.Cir.Cells.get(m, sp), pend))

# the heap after M.pop: the top frame sp is the pend list's first, and its
# term's cell y a root
def heap.pop(+kind: D.FK, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +ps: List<&2, U32>, +sp: U32, +pend: U32, +y: U32,
  +rs: List<&2, U32>, +hz: N.Le(1n+U32.to_nat(290), U32.to_nat(sp)), +ho: {D.Own(fi, nx, sp) == True{} : Bool},
  +hz0: {U32.is_eq(sp, 0) == False{} : Bool}, +hs: {D.Fl(m, sp, 1024) == False{} : Bool}, +hm: {D.Mem(ps, sp) == False{} : Bool},
  +ht: {D.Tg(m, sp) == D.FK.tag(kind) : U32}, +h38: {U32.is_eq(D.FK.tag(kind), 38) == False{} : Bool},
  +hr0: {D.RcL(rs, sp) == 0n : Nat}, +hy: {D.Fd(2n, m, sp) == y : U32},
  h: D.Heap(m, nx, fi, im, rs, pend, ps)) -> D.Heap(M1(m, sp, pend), nx, fi, im, Con{y, rs}, sp, Con{sp, ps}):
  (hc, r1) = h
  (hp, r2) = r1
  (hcn, r3) = r2
  (+hpt, hr) = r3
  +m1 = M1(m, sp, pend)
  +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
  +hf0 = {(%hy : {D.Fs(m, ps, sp) == [_] : List<&2, U32>};
    fs.top(kind, m, ps, sp, h38, ht, hm)) : {D.Fs(m, ps, sp) == [y] : List<&2, U32>}}
  +hf1 = fs.top1(kind, m, ps, sp, pend, ht)
  +hzt = tg.big(kind, m, sp, ht)
  +p0 = {(%Equal.sym(Nat, D.Pc(n, m, ps, fi, sp), 0n, pc.none(n, m, ps, fi, im, fi, nx, sp, hzt, hpt)) : {Nat.add(_, D.RcL(rs, sp)) == 0n : Nat};
    hr0) : {D.Ptr(n, m, fi, ps, rs, sp) == 0n : Nat}}
  +p1 = Equal.trans(Nat, D.Ptr(n, m1, fi, Con{sp, ps}, Con{y, rs}, sp), D.Ptr(n, m, fi, ps, rs, sp), 0n,
    ptr.pop(m, nx, fi, ps, sp, pend, y, rs, sp, hz, ho, hf0, hf1), p0)
  +ch = {(%Equal.sym(U32, D.Fd(1n, m1, sp), pend, pop.f1(m, sp, pend)) : D.Chain(ps, m1, _);
    D.Chain.fz(ps, m, sp, X1(m, sp, pend), pend, hm, hc)) : D.Chain(ps, m1, D.Fd(1n, m1, sp))}
  +hs1 = {(%Equal.sym(U32, D.Fd(0n, m1, sp), D.Fd(0n, m, sp), pop.f0(m, sp, pend)) : {U32.is_ne(U32.and(_, 1024), 0) == False{} : Bool}; hs) :
    {D.Fl(m1, sp, 1024) == False{} : Bool}}
  +htg1 = {(%Equal.sym(U32, D.Tg(m1, sp), D.FK.tag(kind), pop.tg(kind, m, sp, pend, ht)) : {Bool.or(U32.is_lt(_, 19), U32.is_le(32, _)) == True{} : Bool};
    fk.pend(kind)) : {Bool.or(U32.is_lt(D.Tg(m1, sp), 19), U32.is_le(32, D.Tg(m1, sp))) == True{} : Bool}}
  (({==}, (hz0, ch)),
   ((ho, (hs1, (htg1, (p1, pendok.pop(ps, m, nx, fi, ps, sp, pend, y, rs, hz, ho, hf0, hf1, hm, hp))))),
    (cnt.pop(n, kind, m, nx, fi, ps, sp, pend, y, rs, fi, hz, ho, ht, hf0, hf1, hcn),
     (pts.pop(n, m, sp, pend, ps, fi, im, fi, nx, hz, hf1, hzt, hpt), hr))))

# The frames after M.pop (swap_moves.bend's Hops kit, copied)
# ------------------------------------------------------------

# from fr, n cells that are not 0, linked by field 1, then 0
def Hops(n: Nat, +m: Cr.Cir.Cells, +fr: U32) -> Bool:
  match n:
    case 0n:
      U32.is_eq(fr, 0)
    case 1n+p:
      Bool.and(Bool.not(U32.is_eq(fr, 0)), Hops(p, m, D.Fd(1n, m, fr)))

# the frames from fr are as many as its chain's cells
def frs.hops(fs: List<&2, D.AF>, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +fr: U32, h: D.Frs(ds, m, im, fi, nx, ks, img, ps, fr, fs)) ->
  {Hops(List.length(&2, D.AF, fs), m, fr) == True{} : Bool}:
  match fs:
    case Nil{}:
      %Equal.sym(U32, fr, 0, h) : {Hops(0n, m, _) == True{} : Bool}
      {==}
    case Con{D.AF{+kind, +q, +k, +a, +b}, +rest}:
      match h:
        case Tuple{e0, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, ir}}}}}}}}}}:
          D.and.i(Bool.not(U32.is_eq(fr, 0)), Hops(List.length(&2, D.AF, rest), m, D.Fd(1n, m, fr)),
            (%Equal.sym(Bool, U32.is_eq(fr, 0), False{}, e0) : {Bool.not(_) == True{} : Bool}; {==}),
            frs.hops(rest, ds, m, im, fi, nx, ks, img, ps, D.Fd(1n, m, fr), ir))

# a chain ends after one number of cells only
def hops.lt(a: Nat, b: Nat, +m: Cr.Cir.Cells, +x: U32, ha: {Hops(a, m, x) == True{} : Bool}, hb: {Hops(b, m, x) == True{} : Bool},
  hlt: N.Le(1n+a, b)) -> Empty:
  match a b:
    case 0n 0n:
      hlt
    case 0n 1n+q:
      D.bool.ft(Empty, (%ha : {Bool.not(_) == True{} : Bool};
        D.and.l(Bool.not(U32.is_eq(x, 0)), Hops(q, m, D.Fd(1n, m, x)), hb)))
    case 1n+p 0n:
      hlt
    case 1n+p 1n+q:
      hops.lt(p, q, m, D.Fd(1n, m, x), D.and.r(Bool.not(U32.is_eq(x, 0)), Hops(p, m, D.Fd(1n, m, x)), ha),
        D.and.r(Bool.not(U32.is_eq(x, 0)), Hops(q, m, D.Fd(1n, m, x)), hb), hlt)

def hops.ne.b(bb: Bool, a: Nat, b: Nat, +m: Cr.Cir.Cells, +x: U32, +y: U32, eb: {U32.is_eq(x, y) == bb : Bool},
  hx: {Hops(a, m, x) == True{} : Bool}, hy: {Hops(b, m, y) == True{} : Bool}, hlt: N.Le(1n+a, b)) -> {U32.is_eq(x, y) == False{} : Bool}:
  match bb:
    case False{}:
      eb
    case True{}:
      +e = D.u32.eq(x, y, eb)
      Empty.absurd({U32.is_eq(x, y) == False{} : Bool}, hops.lt(a, b, m, y, (%e : {Hops(a, m, _) == True{} : Bool}; hx), hy, hlt))

# a cell whose chain is shorter than y's is not y
def hops.ne(a: Nat, b: Nat, +m: Cr.Cir.Cells, +x: U32, +y: U32, hx: {Hops(a, m, x) == True{} : Bool},
  hy: {Hops(b, m, y) == True{} : Bool}, hlt: N.Le(1n+a, b)) -> {U32.is_eq(x, y) == False{} : Bool}:
  hops.ne.b(U32.is_eq(x, y), a, b, m, x, y, {==}, hx, hy, hlt)

# the second of a pair
def p2.snd(-A: Data, -B: Data, p: D.P2(A, B)) -> B:
  match p:
    case Tuple{_, b}:
      b

# a store to sx, of a tag of 32 or more, keeps the term of the cell c
def is.keep(t: Bk.Term, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +sx: U32, +sv: Cr.Cir.Cell, +c: U32, +ht: {U32.is_lt(D.TgW(D.Fd(0n, m, sx)), 32) == False{} : Bool},
  h: D.Is(ds, m, im, fi, nx, ks, img, c, t)) -> D.Is(ds, Cr.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, c, t):
  p2.snd({Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, sx, sv), c) == Cr.Cir.Cells.get(m, c) : Cr.Cir.Cell},
    D.Is(ds, Cr.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, c, t), D.is.st(t, ds, m, im, fi, nx, ks, img, sx, sv, c, ht, h))

def frsb.st(kind: D.FK, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +sx: U32, +sv: Cr.Cir.Cell, +c: U32, +b: Bk.Term, +ht: {U32.is_lt(D.TgW(D.Fd(0n, m, sx)), 32) == False{} : Bool},
  h: D.Frs.b(ds, m, im, fi, nx, ks, img, c, kind, b)) -> D.Frs.b(ds, Cr.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, c, kind, b):
  match kind:
    case D.FK.rwt{}:
      is.keep(b, ds, m, im, fi, nx, ks, img, sx, sv, c, ht, h)
    case D.FK.arg{}:
      Unit{}
    case D.FK.val{}:
      Unit{}
    case D.FK.fun{}:
      Unit{}
    case D.FK.let{}:
      Unit{}
    case D.FK.tupb{}:
      Unit{}
    case D.FK.tupa{}:
      Unit{}
    case D.FK.minb{}:
      Unit{}
    case D.FK.mina{}:
      Unit{}

# M.pop keeps the frames from fr, past the top frame sp (a longer chain than
# fr's), with sp in the pend list
def frs.pop.c(fs: List<&2, D.AF>, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +sp: U32, +pend: U32, +fr: U32, +n: Nat,
  +ht: {U32.is_lt(D.TgW(D.Fd(0n, m, sp)), 32) == False{} : Bool}, +hn: {Hops(n, m, sp) == True{} : Bool},
  +hf: {Hops(List.length(&2, D.AF, fs), m, fr) == True{} : Bool},
  hl: N.Le(1n+List.length(&2, D.AF, fs), n), h: D.Frs(ds, m, im, fi, nx, ks, img, ps, fr, fs)) ->
  D.Frs(ds, M1(m, sp, pend), im, fi, nx, ks, img, Con{sp, ps}, fr, fs):
  match fs:
    case Nil{}:
      h
    case Con{D.AF{+kind, +q, +k, +a, +b}, +rest}:
      match h:
        case Tuple{e0, Tuple{ev, Tuple{eo, Tuple{es, Tuple{em, Tuple{etg, Tuple{eq, Tuple{ek, Tuple{ia, Tuple{ib, ir}}}}}}}}}}:
          +m1 = M1(m, sp, pend)
          +sv = X1(m, sp, pend)
          +hl2 = hl
          +ne = hops.ne(1n+List.length(&2, D.AF, rest), n, m, fr, sp, hf, hn, hl2)
          +ec = D.cl.go(m, fr, sp, sv, ne)
          +em1 = Equal.trans(Bool, D.Mem(Con{sp, ps}, fr), D.Mem(ps, fr), False{}, mem.out(sp, ps, fr, D.ne.sym(fr, sp, ne)), em)
          D.frs.uc(ds, m1, im, fi, nx, ks, img, Con{sp, ps}, fr, Con{D.AF{kind, q, k, a, b}, rest},
            D.frsc.at(ds, m1, im, fi, nx, ks, img, Con{sp, ps}, fr, Cr.Cir.Cells.get(m1, fr), Cr.Cir.Cells.get(m, fr), Con{D.AF{kind, q, k, a, b}, rest}, ec,
              (e0, (ev, (eo, (es, (em1, (etg, (eq, (ek,
                (is.keep(a, ds, m, im, fi, nx, ks, img, sp, sv, D.Fd(2n, m, fr), ht, ia),
                (frsb.st(kind, ds, m, im, fi, nx, ks, img, sp, sv, D.Fd(3n, m, fr), b, ht, ib),
                 frs.pop.c(rest, ds, m, im, fi, nx, ks, img, ps, sp, pend, D.Fd(1n, m, fr), n, ht, hn,
                   D.and.r(Bool.not(U32.is_eq(fr, 0)), Hops(List.length(&2, D.AF, rest), m, D.Fd(1n, m, fr)), hf),
                   N.weaken(1n+List.length(&2, D.AF, rest), n, hl2), ir)))))))))))))

# no pointer to z, of a tag of 19 or more, from the cells or the roots rs, of
# term cells (swap_moves.bend's ptr.none)
def ptr.none(+m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +ps: List<&2, U32>, +pend: U32, +rs: List<&2, U32>, +z: U32,
  +hz: {U32.is_lt(D.Tg(m, z), 19) == False{} : Bool}, hr0: {D.RcL(rs, z) == 0n : Nat},
  h: D.Heap(m, nx, fi, im, rs, pend, ps)) -> {D.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, rs, z) == 0n : Nat}:
  (hc, r1) = h
  (hp, r2) = r1
  (hcn, r3) = r2
  (hpt, hr) = r3
  +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
  %Equal.sym(Nat, D.Pc(n, m, ps, fi, z), 0n, pc.none(n, m, ps, fi, im, fi, nx, z, hz, hpt)) : {Nat.add(_, D.RcL(rs, z)) == 0n : Nat}
  hr0

# a term's tag is below 19 (swap_moves.bend's, copied)
def atag.lt(t: Bk.Term) -> {U32.is_lt(D.A.tag(t), 19) == True{} : Bool}:
  match t:
    case Bk.Term.Var{_}:
      {==}
    case Bk.Term.Ref{_}:
      {==}
    case Bk.Term.Ann{_, _}:
      {==}
    case Bk.Term.Let{_, _, _}:
      {==}
    case Bk.Term.Typ{_}:
      {==}
    case Bk.Term.Min{_, _}:
      {==}
    case Bk.Term.All{_, _, _}:
      {==}
    case Bk.Term.Lam{_, _}:
      {==}
    case Bk.Term.App{_, _, _}:
      {==}
    case Bk.Term.Sig{_, _, _}:
      {==}
    case Bk.Term.Tup{_, _, _}:
      {==}
    case Bk.Term.Prj{_}:
      {==}
    case Bk.Term.Enu{_}:
      {==}
    case Bk.Term.Lab{_}:
      {==}
    case Bk.Term.Mat{_, _, _}:
      {==}
    case Bk.Term.Efq{}:
      {==}
    case Bk.Term.Eql{_, _, _}:
      {==}
    case Bk.Term.Rfl{}:
      {==}
    case Bk.Term.Rwt{_, _, _}:
      {==}

# the tag of a node's cell is below 19 (swap_moves.bend's, copied)
def nd.tglt(+dk: Bool, -ds: List<&2, Bk.Def>, -im: U32, -fi: U32, -nx: U32, -c: U32, +x: Cr.Cir.Cell, +t: Bk.Term,
  nd: D.NdK(dk, ds, im, fi, nx, c, x, t, D.A.tag(t))) -> {U32.is_lt(D.TgW(Cr.Cir.Cell.get(0n, x)), 19) == True{} : Bool}:
  match nd:
    case Tuple{_, Tuple{_, Tuple{etag, _}}}:
      %Equal.sym(U32, D.TgW(Cr.Cir.Cell.get(0n, x)), D.A.tag(t), etag) : {U32.is_lt(_, 19) == True{} : Bool}
      atag.lt(t)


# the focus' cell is a term cell
def is.tglt(+ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +c: U32, +t: Bk.Term, h: D.Is(ds, m, im, fi, nx, ks, img, c, t)) -> {U32.is_lt(D.Tg(m, c), 19) == True{} : Bool}:
  nd.tglt(True{}, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), t, D.is.nd(ds, m, im, fi, nx, ks, img, c, t, h))


def fk.lt32(kind: D.FK) -> {U32.is_lt(D.FK.tag(kind), 32) == False{} : Bool}:
  match kind:
    case D.FK.arg{}:
      {==}
    case D.FK.val{}:
      {==}
    case D.FK.fun{}:
      {==}
    case D.FK.let{}:
      {==}
    case D.FK.tupb{}:
      {==}
    case D.FK.tupa{}:
      {==}
    case D.FK.rwt{}:
      {==}
    case D.FK.minb{}:
      {==}
    case D.FK.mina{}:
      {==}

# HS after M.pop: the roots are the top frame's term a (its field 2) and the
# focus; the frames are the rest; sp is the pend list's first
def hsk.pop(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32,
  +im: U32, +focus: Bk.Term, +fs: List<&2, D.AF>, +foc: U32, +sp: U32, +pend: U32, +ps: List<&2, U32>, +kind: D.FK, +q: Bk.Quan,
  +k: Bool, +a: Bk.Term, +b: Bk.Term, +h38: {U32.is_eq(D.FK.tag(kind), 38) == False{} : Bool},
  +isf: D.Is(ds, m, im, fi, nx, ks, img, foc, focus), +hp: D.Heap(m, nx, fi, im, [foc], pend, ps),
  +io: D.ImgOK(ds, ks, img, m, im, fi, nx),
  +frs: D.Frs(ds, m, im, fi, nx, ks, img, ps, sp, Con{D.AF{kind, q, k, a, b}, fs})) ->
  D.HS(ds, ks, img, M1(m, sp, pend), nx, fi, im, [D.Rt{D.Fd(2n, m, sp), a}, D.Rt{foc, focus}], Nil{}, fs, D.Fd(1n, m, sp), sp, Con{sp, ps}):
  match frs:
    case Tuple{e0, Tuple{ev, Tuple{eo, Tuple{es, Tuple{em, Tuple{etg, Tuple{_, Tuple{_, Tuple{ia, Tuple{_, ir}}}}}}}}}}:
      +sv = X1(m, sp, pend)
      +eo2 = eo
      +es2 = es
      +em2 = em
      +etg2 = etg
      +ht = {(%Equal.sym(U32, D.Tg(m, sp), D.FK.tag(kind), etg2) : {U32.is_lt(_, 32) == False{} : Bool}; fk.lt32(kind)) :
        {U32.is_lt(D.TgW(D.Fd(0n, m, sp)), 32) == False{} : Bool}}
      +hzt = tg.big(kind, m, sp, etg2)
      +hsp = frs.hops(Con{D.AF{kind, q, k, a, b}, fs}, ds, m, im, fi, nx, ks, img, ps, sp, frs)
      +hfoc = is.tglt(ds, m, im, fi, nx, ks, img, foc, focus, isf)
      +nef = tg.ne(m, foc, sp, hfoc, hzt)
      +hr0 = {(%Equal.sym(Bool, U32.is_eq(foc, sp), False{}, nef) : {Nat.add(D.Nat.of(_), 0n) == 0n : Nat}; {==}) : {D.RcL([foc], sp) == 0n : Nat}}
      +hz290 = D.img.hz(True{}, ds, ks, img, m, im, fi, nx, sp, io, eo2)
      +hz0 = ptr.none(m, nx, fi, im, ps, pend, [foc], sp, hzt, hr0, hp)
      ((is.keep(a, ds, m, im, fi, nx, ks, img, sp, sv, D.Fd(2n, m, sp), ht, ia), (is.keep(focus, ds, m, im, fi, nx, ks, img, sp, sv, foc, ht, isf), Unit{})),
      (Unit{}, (Unit{},
      (frs.pop.c(fs, ds, m, im, fi, nx, ks, img, ps, sp, pend, D.Fd(1n, m, sp), 1n+List.length(&2, D.AF, fs), ht, hsp,
         D.and.r(Bool.not(U32.is_eq(sp, 0)), Hops(List.length(&2, D.AF, fs), m, D.Fd(1n, m, sp)), hsp),
         N.le_refl(1n+List.length(&2, D.AF, fs)), ir),
      (heap.pop(kind, m, nx, fi, im, ps, sp, pend, D.Fd(2n, m, sp), [foc], hz290, eo2, e0, es2, em2, etg2, h38, hr0, {==}, hp),
        D.ImgOK.fz(True{}, ds, ks, img, m, im, fi, nx, ps, [foc], sp, sv, hz0, es2, eo2, io))))))

# A move's round, statement by statement
# --------------------------------------
#
# PB: what a move's round says of an outcome (MV's PostB, with the move's
# start st0, term t, measure w and limit lim). Each of the statements that
# the redexes run (a set, M.inc, M.dec, M.push) takes PB of the statements
# after it to PB of itself and them (pb.*), with what its law gives.

def PB(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st0: Cr.Cir.State, +t: Bk.Term, +w: Nat,
  +lim: U32, o: Cr.Cir.Out) -> Type:
  D.PostB(False{}, o, s => K.MV.next(ds, ks, img, st0, t, w, s), s => st2 => D.HR(ds, t, s, st2), D.Budget(ds, st0, t), lim)

# a set of the register r to the value v of e
def pb.set(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st0: Cr.Cir.State, +t: Bk.Term,
  +w: Nat, +lim: U32, +r: Nat, +e: Cr.Cir.Expr, +rest: Cr.Cir.Stmt, +st: Cr.Cir.State, +v: U32,
  ev: {Cr.Cir.eval(e, st) == Some{v} : Maybe<&2, U32>}, hl: {List.length(&2, U32, X.X.regs(st)) == 63n : Nat},
  hr: {Nat.is_lt(r, 63n) == True{} : Bool}, h: PB(ds, ks, img, st0, t, w, lim, Cr.Cir.exec(f, rest, X.X.setst(st, r, v)))) ->
  PB(ds, ks, img, st0, t, w, lim, Cr.Cir.exec(f, Cr.Cir.Stmt.seq{Cr.Cir.Stmt.set{r, e}, rest}, st)):
  %X.rw.seq(f, Cr.Cir.Stmt.set{r, e}, rest, st, X.X.setst(st, r, v), X.run.set(f, r, e, st, v, ev, hl, hr)) :
    PB(ds, ks, img, st0, t, w, lim, _)
  h

# the inc's next state
def pb.inc.k(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st0: Cr.Cir.State, +t: Bk.Term,
  +w: Nat, +lim: U32, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +inp: List<&2, Word(8n)>,
  +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>, +c: U32, +u: Bk.Term,
  +xs: List<&2, D.TmpE>, +zs: List<&2, D.Rt>, +rest: Cr.Cir.Stmt,
  st2: Cr.Cir.State,
  q: D.Ex(Cr.Cir.Cells, m2 => D.P2({st2 == Cr.Cir.State{regs, m2, nx, fi, im, pg, lim, inp, Nil{}, 0} : Cr.Cir.State},
      D.P2({D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m2, fi) == D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi) : Nat},
      D.P2(D.HSK(True{}, ds, ks, img, m2, nx, fi, im, Con{D.Rt{c, u}, os}, Con{D.Rt{c, u}, bs}, fs, sp, pend, ps),
        D.AccK(True{}, ds, ks, img, m2, nx, fi, im, Con{D.Rt{c, u}, os}, xs, sp, fs, ps, zs))))),
  k: @m2: Cr.Cir.Cells -> {D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m2, fi) == D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi) : Nat} ->
    D.HSK(True{}, ds, ks, img, m2, nx, fi, im, Con{D.Rt{c, u}, os}, Con{D.Rt{c, u}, bs}, fs, sp, pend, ps) ->
    D.AccK(True{}, ds, ks, img, m2, nx, fi, im, Con{D.Rt{c, u}, os}, xs, sp, fs, ps, zs) ->
    PB(ds, ks, img, st0, t, w, lim, Cr.Cir.exec(f, rest, Cr.Cir.State{regs, m2, nx, fi, im, pg, lim, inp, Nil{}, 0}))) ->
  PB(ds, ks, img, st0, t, w, lim, Cr.Cir.exec(f, rest, st2)):
  match q:
    case Tuple{m2, Tuple{e, Tuple{hst, Tuple{hs2, hac2}}}}:
      %Equal.sym(Cr.Cir.State, st2, Cr.Cir.State{regs, m2, nx, fi, im, pg, lim, inp, Nil{}, 0}, e) :
        PB(ds, ks, img, st0, t, w, lim, Cr.Cir.exec(f, rest, _))
      k(m2, hst, hs2, hac2)

# M.inc of the held cell c of u in register r: c is an owned root too
def pb.inc(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st0: Cr.Cir.State, +t: Bk.Term,
  +w: Nat, +lim: U32, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +inp: List<&2, Word(8n)>,
  +r: Nat, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>, +c: U32, +u: Bk.Term,
  +xs: List<&2, D.TmpE>, +zs: List<&2, D.Rt>, +rest: Cr.Cir.Stmt,
  hs: D.HSK(True{}, ds, ks, img, m, nx, fi, im, os, Con{D.Rt{c, u}, bs}, fs, sp, pend, ps),
  hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, os, xs, sp, fs, ps, zs),
  hn: N.Le(List.length(&2, D.Rt, os), 64n), hc: {List.get(&2, U32, regs, r) == Some{c} : Maybe<&2, U32>},
  k: @m2: Cr.Cir.Cells -> {D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m2, fi) == D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi) : Nat} ->
    D.HSK(True{}, ds, ks, img, m2, nx, fi, im, Con{D.Rt{c, u}, os}, Con{D.Rt{c, u}, bs}, fs, sp, pend, ps) ->
    D.AccK(True{}, ds, ks, img, m2, nx, fi, im, Con{D.Rt{c, u}, os}, xs, sp, fs, ps, zs) ->
    PB(ds, ks, img, st0, t, w, lim, Cr.Cir.exec(f, rest, Cr.Cir.State{regs, m2, nx, fi, im, pg, lim, inp, Nil{}, 0}))) ->
  PB(ds, ks, img, st0, t, w, lim, Cr.Cir.exec(f, Cr.Cir.Stmt.seq{Mc.M.inc(r), rest}, Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0})):
  +st = {Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0} : Cr.Cir.State}
  +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
  D.postb.seq(f, False{}, Mc.M.inc(r), rest, st,
    st2 => D.Ex(Cr.Cir.Cells, m2 => D.P2({st2 == Cr.Cir.State{regs, m2, nx, fi, im, pg, lim, inp, Nil{}, 0} : Cr.Cir.State},
      D.P2({D.Stat(n, m2, fi) == D.Stat(n, m, fi) : Nat},
      D.P2(D.HSK(True{}, ds, ks, img, m2, nx, fi, im, Con{D.Rt{c, u}, os}, Con{D.Rt{c, u}, bs}, fs, sp, pend, ps),
        D.AccK(True{}, ds, ks, img, m2, nx, fi, im, Con{D.Rt{c, u}, os}, xs, sp, fs, ps, zs))))),
    s => K.MV.next(ds, ks, img, st0, t, w, s), s => st2 => Empty, s => st2 => D.HR(ds, t, s, st2), D.Budget(ds, st0, t), lim,
    D.postb.wk(False{}, Cr.Cir.exec(f, Mc.M.inc(r), st),
      st2 => D.Ex(Cr.Cir.Cells, m2 => D.P2({st2 == Cr.Cir.State{regs, m2, nx, fi, im, pg, lim, inp, Nil{}, 0} : Cr.Cir.State},
        D.P2({D.Stat(n, m2, fi) == D.Stat(n, m, fi) : Nat},
        D.P2(D.HSK(True{}, ds, ks, img, m2, nx, fi, im, Con{D.Rt{c, u}, os}, Con{D.Rt{c, u}, bs}, fs, sp, pend, ps),
          D.AccK(True{}, ds, ks, img, m2, nx, fi, im, Con{D.Rt{c, u}, os}, xs, sp, fs, ps, zs))))),
      s => st2 => Empty, 0n, D.Budget(ds, st0, t), lim,
      D.inc.post(f, True{}, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, r, os, bs, fs, sp, pend, ps, c, u, xs, zs, hs, hac, hn, hc),
      N.le_zero(D.Budget(ds, st0, t))),
    s => st2 => e => Empty.absurd(D.HR(ds, t, s, st2), e),
    st2 => q => pb.inc.k(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, os, bs, fs, sp, pend, ps, c, u, xs, zs, rest, st2, q, k))

# the dec's next state
def pb.dec.k(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st0: Cr.Cir.State, +t: Bk.Term,
  +w: Nat, +lim: U32, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +inp: List<&2, Word(8n)>,
  +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +xs: List<&2, D.TmpE>, +rest: Cr.Cir.Stmt,
  st2: Cr.Cir.State,
  q: D.Ex(Cr.Cir.Cells, m2 => D.Ex(U32, d => D.Ex(U32, pend2 => D.Ex(List<&2, U32>, ps2 =>
      D.P2({st2 == Cr.Cir.State{List.set(&2, U32, List.set(&2, U32, regs, 5n, d), 3n, pend2), m2, nx, fi, im, pg, lim, inp, Nil{}, 0} : Cr.Cir.State},
      D.P2({D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m2, fi) == D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi) : Nat},
      D.P2(D.HSK(True{}, ds, ks, img, m2, nx, fi, im, os, bs, fs, sp, pend2, ps2),
        D.Ex(List<&2, D.Rt>, zs2 => D.AccK(True{}, ds, ks, img, m2, nx, fi, im, os, xs, sp, fs, ps2, zs2))))))))),
  k: @m2: Cr.Cir.Cells -> @d: U32 -> @pend2: U32 -> @ps2: List<&2, U32> ->
    {D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m2, fi) == D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi) : Nat} ->
    D.HSK(True{}, ds, ks, img, m2, nx, fi, im, os, bs, fs, sp, pend2, ps2) ->
    D.Ex(List<&2, D.Rt>, zs2 => D.AccK(True{}, ds, ks, img, m2, nx, fi, im, os, xs, sp, fs, ps2, zs2)) ->
    PB(ds, ks, img, st0, t, w, lim, Cr.Cir.exec(f, rest, Cr.Cir.State{List.set(&2, U32, List.set(&2, U32, regs, 5n, d), 3n, pend2), m2, nx, fi, im, pg, lim, inp, Nil{}, 0}))) ->
  PB(ds, ks, img, st0, t, w, lim, Cr.Cir.exec(f, rest, st2)):
  match q:
    case Tuple{m2, Tuple{d, Tuple{pend2, Tuple{ps2, Tuple{e, Tuple{hst, Tuple{hs2, hac2}}}}}}}:
      %Equal.sym(Cr.Cir.State, st2, Cr.Cir.State{List.set(&2, U32, List.set(&2, U32, regs, 5n, d), 3n, pend2), m2, nx, fi, im, pg, lim, inp, Nil{}, 0}, e) :
        PB(ds, ks, img, st0, t, w, lim, Cr.Cir.exec(f, rest, _))
      k(m2, d, pend2, ps2, hst, hs2, hac2)

# M.dec of the owned root c of u in register r, the first root, when the
# borrowed terms bs are held without it
def pb.dec(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st0: Cr.Cir.State, +t: Bk.Term,
  +w: Nat, +lim: U32, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +inp: List<&2, Word(8n)>,
  +r: Nat, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>, +c: U32, +u: Bk.Term,
  +xs: List<&2, D.TmpE>, +zs: List<&2, D.Rt>, +rest: Cr.Cir.Stmt,
  hs: D.HSK(True{}, ds, ks, img, m, nx, fi, im, Con{D.Rt{c, u}, os}, bs, fs, sp, pend, ps),
  hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, Con{D.Rt{c, u}, os}, xs, sp, fs, ps, zs),
  hb: D.Held(m, os, bs), hl: {List.length(&2, U32, regs) == 63n : Nat}, hc: {List.get(&2, U32, regs, r) == Some{c} : Maybe<&2, U32>},
  hp: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>}, h5: {Nat.is_eq(5n, r) == False{} : Bool},
  k: @m2: Cr.Cir.Cells -> @d: U32 -> @pend2: U32 -> @ps2: List<&2, U32> ->
    {D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m2, fi) == D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi) : Nat} ->
    D.HSK(True{}, ds, ks, img, m2, nx, fi, im, os, bs, fs, sp, pend2, ps2) ->
    D.Ex(List<&2, D.Rt>, zs2 => D.AccK(True{}, ds, ks, img, m2, nx, fi, im, os, xs, sp, fs, ps2, zs2)) ->
    PB(ds, ks, img, st0, t, w, lim, Cr.Cir.exec(f, rest, Cr.Cir.State{List.set(&2, U32, List.set(&2, U32, regs, 5n, d), 3n, pend2), m2, nx, fi, im, pg, lim, inp, Nil{}, 0}))) ->
  PB(ds, ks, img, st0, t, w, lim, Cr.Cir.exec(f, Cr.Cir.Stmt.seq{Mc.M.dec(r), rest}, Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0})):
  +st = {Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0} : Cr.Cir.State}
  +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
  D.postb.seq(f, False{}, Mc.M.dec(r), rest, st,
    st2 => D.Ex(Cr.Cir.Cells, m2 => D.Ex(U32, d => D.Ex(U32, pend2 => D.Ex(List<&2, U32>, ps2 =>
      D.P2({st2 == Cr.Cir.State{List.set(&2, U32, List.set(&2, U32, regs, 5n, d), 3n, pend2), m2, nx, fi, im, pg, lim, inp, Nil{}, 0} : Cr.Cir.State},
      D.P2({D.Stat(n, m2, fi) == D.Stat(n, m, fi) : Nat},
      D.P2(D.HSK(True{}, ds, ks, img, m2, nx, fi, im, os, bs, fs, sp, pend2, ps2),
        D.Ex(List<&2, D.Rt>, zs2 => D.AccK(True{}, ds, ks, img, m2, nx, fi, im, os, xs, sp, fs, ps2, zs2))))))))),
    s => K.MV.next(ds, ks, img, st0, t, w, s), s => st2 => Empty, s => st2 => D.HR(ds, t, s, st2), D.Budget(ds, st0, t), lim,
    D.postb.wk(False{}, Cr.Cir.exec(f, Mc.M.dec(r), st),
      st2 => D.Ex(Cr.Cir.Cells, m2 => D.Ex(U32, d => D.Ex(U32, pend2 => D.Ex(List<&2, U32>, ps2 =>
        D.P2({st2 == Cr.Cir.State{List.set(&2, U32, List.set(&2, U32, regs, 5n, d), 3n, pend2), m2, nx, fi, im, pg, lim, inp, Nil{}, 0} : Cr.Cir.State},
        D.P2({D.Stat(n, m2, fi) == D.Stat(n, m, fi) : Nat},
        D.P2(D.HSK(True{}, ds, ks, img, m2, nx, fi, im, os, bs, fs, sp, pend2, ps2),
          D.Ex(List<&2, D.Rt>, zs2 => D.AccK(True{}, ds, ks, img, m2, nx, fi, im, os, xs, sp, fs, ps2, zs2))))))))),
      s => st2 => Empty, 0n, D.Budget(ds, st0, t), lim,
      D.dec.post(f, True{}, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, r, os, bs, fs, sp, pend, ps, c, u, xs, zs, hs, hac, hb, hl, hc, hp, h5),
      N.le_zero(D.Budget(ds, st0, t))),
    s => st2 => e => Empty.absurd(D.HR(ds, t, s, st2), e),
    st2 => q => pb.dec.k(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, os, bs, fs, sp, xs, rest, st2, q, k))

# M.push
# ------
#
# M.push's M.alloc gives a cell z, all zeros (alloc.post); its four stores
# make it the cell {hv, sp, av, bv, 0} (put4), the top frame of the kind of
# hv over the frames from sp (stores.eq); store.post moves the root of its
# term to the temporary z, which the new frame then is (frame.hsk,
# frame.acc).

# four stores to a cell that is all zeros
def put4(+m: Cr.Cir.Cells, +z: U32, +hv: U32, +s1: U32, +av: U32, +bv: U32,
  e0: {Cr.Cir.Cells.get(m, z) == Cr.Cir.Cell.zero() : Cr.Cir.Cell}) ->
  {X.X.put(X.X.put(X.X.put(X.X.put(m, 0n, z, hv), 1n, z, s1), 2n, z, av), 3n, z, bv) == Cr.Cir.Cells.set(m, z, Cr.Cir.Cell{hv, s1, av, bv, 0}) : Cr.Cir.Cells}:
  +c1 = {Cr.Cir.Cell{hv, 0, 0, 0, 0} : Cr.Cir.Cell}
  +c2 = {Cr.Cir.Cell{hv, s1, 0, 0, 0} : Cr.Cir.Cell}
  +c3 = {Cr.Cir.Cell{hv, s1, av, 0, 0} : Cr.Cir.Cell}
  +rhs = Cr.Cir.Cells.set(m, z, Cr.Cir.Cell{hv, s1, av, bv, 0})
  %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(m, z), Cr.Cir.Cell.zero(), e0) :
    {X.X.put(X.X.put(X.X.put(Cr.Cir.Cells.set(m, z, Cr.Cir.Cell.set(0n, _, hv)), 1n, z, s1), 2n, z, av), 3n, z, bv) == rhs : Cr.Cir.Cells}
  %X.Ce.put_set(m, z, c1, 1n, s1) : {X.X.put(X.X.put(_, 2n, z, av), 3n, z, bv) == rhs : Cr.Cir.Cells}
  %X.Ce.put_set(m, z, c2, 2n, av) : {X.X.put(_, 3n, z, bv) == rhs : Cr.Cir.Cells}
  %X.Ce.put_set(m, z, c3, 3n, bv) : {_ == rhs : Cr.Cir.Cells}
  {==}

# M.push past its M.alloc, which gave the cell z in fr: its stores and the
# set of sp
def stores.eq(+f: Nat, +h: Cr.Cir.Expr, +a: Cr.Cir.Expr, +b: Cr.Cir.Expr, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32,
  +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +z: U32, +sp: U32, +hv: U32, +av: U32, +bv: U32,
  ez: {List.get(&2, U32, regs, 16n) == Some{z} : Maybe<&2, U32>}, esp: {List.get(&2, U32, regs, 2n) == Some{sp} : Maybe<&2, U32>},
  hc: {Cr.Cir.is_cell(z, im, fi, nx) == True{} : Bool}, hl: {List.length(&2, U32, regs) == 63n : Nat},
  e0: {Cr.Cir.Cells.get(m, z) == Cr.Cir.Cell.zero() : Cr.Cir.Cell},
  eh: {Cr.Cir.eval(h, X.X.st(regs, m, nx, fi, im, pg, lim, inp)) == Some{hv} : Maybe<&2, U32>},
  ea: {Cr.Cir.eval(a, X.X.st(regs, X.X.put(X.X.put(m, 0n, z, hv), 1n, z, sp), nx, fi, im, pg, lim, inp)) == Some{av} : Maybe<&2, U32>},
  eb: {Cr.Cir.eval(b, X.X.st(regs, X.X.put(X.X.put(X.X.put(m, 0n, z, hv), 1n, z, sp), 2n, z, av), nx, fi, im, pg, lim, inp)) == Some{bv} : Maybe<&2, U32>}) ->
  {Cr.Cir.exec(f, X.sel.b(Mc.M.push(h, a, b)), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) ==
    Cr.Cir.Out.next{X.X.st(X.X.set(regs, 2n, z), Cr.Cir.Cells.set(m, z, Cr.Cir.Cell{hv, sp, av, bv, 0}), nx, fi, im, pg, lim, inp)} : Cr.Cir.Out}:
  +g = ez
  +cc = hc
  +t0 = X.X.st(regs, m, nx, fi, im, pg, lim, inp)
  +t1 = X.X.store(t0, 0n, z, hv)
  +t2 = X.X.store(t1, 1n, z, sp)
  +t3 = X.X.store(t2, 2n, z, av)
  +t4 = X.X.store(t3, 3n, z, bv)
  +t5 = X.X.setst(t4, 2n, z)
  +q1 = X.sel.b(Mc.M.push(h, a, b))
  +q2 = X.sel.b(q1)
  +q3 = X.sel.b(q2)
  +q4 = X.sel.b(q3)
  +q5 = X.sel.b(q4)
  +rhs = {Cr.Cir.Out.next{X.X.st(X.X.set(regs, 2n, z), Cr.Cir.Cells.set(m, z, Cr.Cir.Cell{hv, sp, av, bv, 0}), nx, fi, im, pg, lim, inp)} : Cr.Cir.Out}
  %put4(m, z, hv, sp, av, bv, e0) : {Cr.Cir.exec(f, q1, t0) == Cr.Cir.Out.next{X.X.st(X.X.set(regs, 2n, z), _, nx, fi, im, pg, lim, inp)} : Cr.Cir.Out}
  %X.rw.seq(f, X.sel.a(q1), q2, t0, t1, X.run.store(f, 0n, Mc.M.g(16n), h, t0, z, hv, g, eh, cc)) : {_ == Cr.Cir.Out.next{t5} : Cr.Cir.Out}
  %X.rw.seq(f, X.sel.a(q2), q3, t1, t2, X.run.store(f, 1n, Mc.M.g(16n), Mc.M.g(2n), t1, z, sp, g, esp, cc)) : {_ == Cr.Cir.Out.next{t5} : Cr.Cir.Out}
  %X.rw.seq(f, X.sel.a(q3), q4, t2, t3, X.run.store(f, 2n, Mc.M.g(16n), a, t2, z, av, g, ea, cc)) : {_ == Cr.Cir.Out.next{t5} : Cr.Cir.Out}
  %X.rw.seq(f, X.sel.a(q4), q5, t3, t4, X.run.store(f, 3n, Mc.M.g(16n), b, t3, z, bv, g, eb, cc)) : {_ == Cr.Cir.Out.next{t5} : Cr.Cir.Out}
  %X.rw.seq(f, X.sel.a(q5), X.sel.b(q5), t4, t5, X.run.set(f, 2n, Mc.M.g(16n), t4, z, g, hl, {==})) : {_ == Cr.Cir.Out.next{t5} : Cr.Cir.Out}
  X.run.nop(f, t5)

# a or (b or c) = b or (a or c)
def or.swap(a: Bool, b: Bool, +c: Bool) -> {Bool.or(a, Bool.or(b, c)) == Bool.or(b, Bool.or(a, c)) : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# z in the middle of a list, or first
def mem.mid(A: List<&2, U32>, +z: U32, +B: List<&2, U32>, +c: U32) ->
  {D.Mem(List.append(&2, U32, A, Con{z, B}), c) == D.Mem(Con{z, List.append(&2, U32, A, B)}, c) : Bool}:
  match A:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Equal.trans(Bool, Bool.or(U32.is_eq(x, c), D.Mem(List.append(&2, U32, rest, Con{z, B}), c)),
        Bool.or(U32.is_eq(x, c), Bool.or(U32.is_eq(z, c), D.Mem(List.append(&2, U32, rest, B), c))),
        Bool.or(U32.is_eq(z, c), Bool.or(U32.is_eq(x, c), D.Mem(List.append(&2, U32, rest, B), c))),
        Equal.cong(Bool, Bool, y => Bool.or(U32.is_eq(x, c), y), D.Mem(List.append(&2, U32, rest, Con{z, B}), c),
          D.Mem(Con{z, List.append(&2, U32, rest, B)}, c), mem.mid(rest, z, B, c)),
        or.swap(U32.is_eq(x, c), U32.is_eq(z, c), D.Mem(List.append(&2, U32, rest, B), c)))

# Cov with z moved to the front of the other cells
def cov.mid(n: Nat, +m: Cr.Cir.Cells, +c: U32, +rs: List<&2, D.Rt>, +A: List<&2, U32>, +z: U32, +B: List<&2, U32>,
  h: {D.Cov(n, m, c, rs, List.append(&2, U32, A, Con{z, B})) == True{} : Bool}) ->
  {D.Cov(n, m, c, rs, Con{z, List.append(&2, U32, A, B)}) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      +h2 = h
      +X1 = Bool.or(D.Fl(m, c, 1024), Bool.or(D.Nodes(rs, m, c), D.Mem(List.append(&2, U32, A, Con{z, B}), c)))
      +R1 = D.Cov(p, m, U32.inc(c), rs, List.append(&2, U32, A, Con{z, B}))
      D.and.i(Bool.or(D.Fl(m, c, 1024), Bool.or(D.Nodes(rs, m, c), D.Mem(Con{z, List.append(&2, U32, A, B)}, c))),
        D.Cov(p, m, U32.inc(c), rs, Con{z, List.append(&2, U32, A, B)}),
        (%mem.mid(A, z, B, c) : {Bool.or(D.Fl(m, c, 1024), Bool.or(D.Nodes(rs, m, c), _)) == True{} : Bool};
          D.and.l(X1, R1, h2)),
        cov.mid(p, m, U32.inc(c), rs, A, z, B, D.and.r(X1, R1, h2)))

# Clo with no temporary
def clo.drop(n: Nat, +m: Cr.Cir.Cells, +c: U32, +ps: List<&2, U32>, +cs: List<&2, U32>, +hc: List<&2, U32>,
  h: {D.Clo(n, m, c, ps, cs, hc) == True{} : Bool}) -> {D.Clo(n, m, c, ps, Nil{}, Nil{}) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      +h2 = h
      +S = Bool.or(Bool.not(D.Fl(m, c, 1024)), D.All.static(D.Fs(m, ps, c), m))
      +T1 = Bool.or(Bool.not(D.Mem(cs, c)), D.All.held(D.Fs(m, ps, c), m, cs, hc))
      +hat = D.and.l(D.Clo.at(m, c, ps, cs, hc), D.Clo(p, m, U32.inc(c), ps, cs, hc), h2)
      D.and.i(D.Clo.at(m, c, ps, Nil{}, Nil{}), D.Clo(p, m, U32.inc(c), ps, Nil{}, Nil{}),
        D.and.i(S, Bool.or(Bool.not(False{}), D.All.held(D.Fs(m, ps, c), m, Nil{}, Nil{})), D.and.l(S, T1, hat), {==}),
        clo.drop(p, m, U32.inc(c), ps, cs, hc, D.and.r(D.Clo.at(m, c, ps, cs, hc), D.Clo(p, m, U32.inc(c), ps, cs, hc), h2)))

# the new top frame's terms and cells, from its cell x
def fr.rts.top(+m: Cr.Cir.Cells, +z: U32, +q: Bk.Quan, +k: Bool, +b: Bk.Term, +b2: Bk.Term, +fs: List<&2, D.AF>, +hv: U32, +sp: U32,
  +kv: U32, +bv: U32, e: {Cr.Cir.Cells.get(m, z) == Cr.Cir.Cell{hv, sp, kv, bv, 0} : Cr.Cir.Cell}) ->
  {D.Fr.rts(Con{D.AF{D.FK.val{}, q, k, b, b2}, fs}, m, z) == Con{D.Rt{kv, b}, D.Fr.rts(fs, m, sp)} : List<&2, D.Rt>}:
  %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(m, z), Cr.Cir.Cell{hv, sp, kv, bv, 0}, e) :
    {Con{D.Rt{Cr.Cir.Cell.get(2n, _), b}, D.Fr.rts(fs, m, Cr.Cir.Cell.get(1n, _))} == Con{D.Rt{kv, b}, D.Fr.rts(fs, m, sp)} : List<&2, D.Rt>}
  {==}

def fr.cells.top(+m: Cr.Cir.Cells, +z: U32, +q: Bk.Quan, +k: Bool, +b: Bk.Term, +b2: Bk.Term, +fs: List<&2, D.AF>, +hv: U32, +sp: U32,
  +kv: U32, +bv: U32, e: {Cr.Cir.Cells.get(m, z) == Cr.Cir.Cell{hv, sp, kv, bv, 0} : Cr.Cir.Cell}) ->
  {D.Fr.cells(Con{D.AF{D.FK.val{}, q, k, b, b2}, fs}, m, z) == Con{z, D.Fr.cells(fs, m, sp)} : List<&2, U32>}:
  %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(m, z), Cr.Cir.Cell{hv, sp, kv, bv, 0}, e) :
    {Con{z, D.Fr.cells(fs, m, Cr.Cir.Cell.get(1n, _))} == Con{z, D.Fr.cells(fs, m, sp)} : List<&2, U32>}
  {==}

# the temporary z, the cell {hv, sp, kv, bv, 0} that holds b, is the top
# frame App q □ b over the frames from sp: Acc
def frame.acc(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32,
  +im: U32, +os: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +zs: List<&2, D.Rt>, +z: U32, +q: Bk.Quan, +k: Bool,
  +b: Bk.Term, +b2: Bk.Term, +hv: U32, +kv: U32, +bv: U32,
  +e: {Cr.Cir.Cells.get(m, z) == Cr.Cir.Cell{hv, sp, kv, bv, 0} : Cr.Cir.Cell},
  h: D.AccK(True{}, ds, ks, img, m, nx, fi, im, os, [D.TmpE{z, [D.Rt{kv, b}]}], sp, fs, ps, zs)) ->
  D.AccK(True{}, ds, ks, img, m, nx, fi, im, os, Nil{}, z, Con{D.AF{D.FK.val{}, q, k, b, b2}, fs}, ps, zs):
  (hz, r1) = h
  (_, r2) = r1
  (hpz, r3) = r2
  (hcov, r4) = r3
  (hclo, _) = r4
  +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
  +frt = D.Fr.rts(fs, m, sp)
  +frc = D.Fr.cells(fs, m, sp)
  +RS = List.append(&2, D.Rt, os, Con{D.Rt{kv, b}, List.append(&2, D.Rt, frt, zs)})
  +cov2 = cov.mid(n, m, fi, RS, frc, z, ps, hcov)
  (hz, (Unit{}, (hpz,
    ((%Equal.sym(List<&2, D.Rt>, D.Fr.rts(Con{D.AF{D.FK.val{}, q, k, b, b2}, fs}, m, z), Con{D.Rt{kv, b}, frt},
        fr.rts.top(m, z, q, k, b, b2, fs, hv, sp, kv, bv, e)) :
        {D.Cov(n, m, fi, List.append(&2, D.Rt, os, List.append(&2, D.Rt, Nil{}, List.append(&2, D.Rt, _, zs))),
          List.append(&2, U32, D.Fr.cells(Con{D.AF{D.FK.val{}, q, k, b, b2}, fs}, m, z), List.append(&2, U32, Nil{}, ps))) == True{} : Bool};
      %Equal.sym(List<&2, U32>, D.Fr.cells(Con{D.AF{D.FK.val{}, q, k, b, b2}, fs}, m, z), Con{z, frc},
        fr.cells.top(m, z, q, k, b, b2, fs, hv, sp, kv, bv, e)) :
        {D.Cov(n, m, fi, RS, List.append(&2, U32, _, ps)) == True{} : Bool};
      cov2),
    (clo.drop(n, m, fi, ps, [z], [kv], hclo), {==})))))

# the same: HS
def frame.hsk(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32,
  +im: U32, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>, +z: U32, +q: Bk.Quan,
  +k: Bool, +b: Bk.Term, +b2: Bk.Term, +hv: U32, +kv: U32, +bv: U32,
  +e: {Cr.Cir.Cells.get(m, z) == Cr.Cir.Cell{hv, sp, kv, bv, 0} : Cr.Cir.Cell},
  hz0: {U32.is_eq(z, 0) == False{} : Bool}, hc: {Cr.Cir.is_cell(z, im, fi, nx) == True{} : Bool}, ho: {D.Own(fi, nx, z) == True{} : Bool},
  hm: {D.Mem(ps, z) == False{} : Bool}, htg: {D.TgW(hv) == 33 : U32}, hq: {D.QnW(hv) == Mc.Img.quan(q) : U32},
  hst: {D.FlW(hv, 1024) == False{} : Bool}, hk: {D.FlW(hv, 2048) == k : Bool},
  hb: D.IsK(True{}, ds, m, im, fi, nx, ks, img, kv, b),
  h: D.HSK(True{}, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps)) ->
  D.HSK(True{}, ds, ks, img, m, nx, fi, im, os, bs, Con{D.AF{D.FK.val{}, q, k, b, b2}, fs}, z, pend, ps):
  (hos, r1) = h
  (hbs, r2) = r1
  (hh, r3) = r2
  (hfr, r4) = r3
  (hp, hio) = r4
  +fc = {(hz0, (hc, (ho, (hst, (hm, (htg, (hq, (hk, (hb, (Unit{}, hfr)))))))))) :
    D.FrsCK(True{}, ds, m, im, fi, nx, ks, img, ps, z, Cr.Cir.Cell{hv, sp, kv, bv, 0}, Con{D.AF{D.FK.val{}, q, k, b, b2}, fs})}
  +fr2 = D.frs.uck(True{}, ds, m, im, fi, nx, ks, img, ps, z, Con{D.AF{D.FK.val{}, q, k, b, b2}, fs},
    D.frsc.atk(True{}, ds, m, im, fi, nx, ks, img, ps, z, Cr.Cir.Cells.get(m, z), Cr.Cir.Cell{hv, sp, kv, bv, 0},
      Con{D.AF{D.FK.val{}, q, k, b, b2}, fs}, e, fc))
  (hos, (hbs, (hh, (fr2, (hp, hio)))))

# a then b, then c
def then.assoc(o: Cr.Cir.Out, -g: Cr.Cir.State -> Cr.Cir.Out, -h: Cr.Cir.State -> Cr.Cir.Out) ->
  {Cr.Cir.exec.then(o, u => Cr.Cir.exec.then(g(u), h)) == Cr.Cir.exec.then(Cr.Cir.exec.then(o, g), h) : Cr.Cir.Out}:
  match o:
    case Cr.Cir.Out.next{st}:
      {==}
    case Cr.Cir.Out.halt{s, st}:
      {==}
    case Cr.Cir.Out.out_of_memory{}:
      {==}
    case Cr.Cir.Out.trap{}:
      {==}
    case Cr.Cir.Out.not_done{}:
      {==}

def seq.assoc(+f: Nat, +a: Cr.Cir.Stmt, +b: Cr.Cir.Stmt, +c: Cr.Cir.Stmt, +st: Cr.Cir.State) ->
  {Cr.Cir.exec(f, Cr.Cir.Stmt.seq{a, Cr.Cir.Stmt.seq{b, c}}, st) == Cr.Cir.exec(f, Cr.Cir.Stmt.seq{Cr.Cir.Stmt.seq{a, b}, c}, st) : Cr.Cir.Out}:
  match f:
    case 0n:
      then.assoc(Cr.Cir.exec(0n, a, st), u => Cr.Cir.exec(0n, b, u), u => Cr.Cir.exec(0n, c, u))
    case 1n+g:
      then.assoc(Cr.Cir.exec(1n+g, a, st), u => Cr.Cir.exec(1n+g, b, u), u => Cr.Cir.exec(1n+g, c, u))

# the registers that M.push keeps for the redexes
def KEEP() -> List<&2, Nat>:
  [0n, 1n, 2n, 9n, 10n, 11n, 12n, 13n, 14n, 15n, 17n, 18n]

# what M.push's M.alloc gives (alloc.post's next state, for fr, KEEP, no
# borrowed term and no temporary)
def EXA(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +os: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, st2: Cr.Cir.State) -> Data:
  D.Ex(U32, z => D.Ex(U32, pend2 => D.Ex(List<&2, U32>, ps2 =>
    D.P2(D.Reg(st2, 16n, z), D.P2(D.Reg(st2, 3n, pend2),
    D.P2({Cr.Cir.Cells.get(D.St.cells(st2), z) == Cr.Cir.Cell.zero() : Cr.Cir.Cell},
    D.P2({D.Own(fi, D.St.next(st2), z) == True{} : Bool}, D.P2({D.Mem(ps2, z) == False{} : Bool},
    D.P2({Bool.or(D.Mem(ps, z), U32.is_eq(z, nx)) == True{} : Bool},
    D.P2({Bool.or(Bool.and(D.Mem(ps, z), U32.is_eq(D.St.next(st2), nx)),
         Bool.and(D.Pend.none(ps), Bool.and(U32.is_eq(z, nx), U32.is_eq(D.St.next(st2), U32.inc(nx))))) == True{} : Bool},
    D.P2(D.Ex(List<&2, D.W1>, ws => D.P2({D.St.cells(st2) == Cr.Cir.Cells.set(D.Put1(ws, m), z, Cr.Cir.Cell.zero()) : Cr.Cir.Cells},
      {D.Took(ws, ps, m) == True{} : Bool})),
    D.P2({D.PsSub(ps2, ps, m) == True{} : Bool},
    D.P2({D.Ptr(Nat.sub(U32.to_nat(D.St.next(st2)), U32.to_nat(fi)), D.St.cells(st2), fi, ps2, D.Rt.cells(os), z) == 0n : Nat},
    D.P2(D.HSK(True{}, ds, ks, img, D.St.cells(st2), D.St.next(st2), fi, im, os, Nil{}, fs, sp, pend2, ps2),
      D.Ex(List<&2, D.Rt>, zs2 => D.AccK(True{}, ds, ks, img, D.St.cells(st2), D.St.next(st2), fi, im, os, [D.TmpE{z, Nil{}}], sp, fs, ps2, zs2))))))))))))))))

def QA(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +os: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32,
  +ps: List<&2, U32>, st2: Cr.Cir.State) -> Type:
  D.P2(D.Same(regs, fi, im, lim, inp, KEEP(), st2), EXA(ds, ks, img, m, nx, fi, im, os, fs, sp, ps, st2)) & D.AlFr(m, ps, nx, st2)

# M.alloc with a pend list's first cell runs safely
def alloc.safe(+f: Nat, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>,
  +r: Nat, +pend: U32, hp: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>}, hz: {U32.is_eq(pend, 0) == False{} : Bool}) ->
  Safe(Cr.Cir.exec(f, Mc.M.alloc(r), X.X.st(regs, m, nx, fi, im, pg, lim, inp))):
  +st = X.X.st(regs, m, nx, fi, im, pg, lim, inp)
  +A = Mc.M.alloc(r)
  %X.rw.if.t(f, X.sel.c(A), X.sel.t(A), X.sel.e(A), st, 1, X.ev.ne0(3n, st, pend, hp, hz), {==}) : Safe(_)
  flat.safe(f, X.sel.t(A), st, {==})

# M.alloc, within the round's budget: room for a new cell when the pend list
# is empty (hroom); else it takes the list's first cell, and runs safely
def alloc.pb(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st0: Cr.Cir.State, +t: Bk.Term,
  +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>,
  +os: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32, ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  +hs: D.HSK(True{}, ds, ks, img, m, nx, fi, im, os, Nil{}, fs, sp, pend, ps),
  hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, os, Nil{}, sp, fs, ps, zs),
  hl: {List.length(&2, U32, regs) == 63n : Nat}, +hp: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>},
  hroom: {D.Pend.none(ps) == True{} : Bool} -> N.Le(Nat.mul(20n, Nat.add(U32.to_nat(nx), 1n)), D.Budget(ds, st0, t))) ->
  D.PostB(False{}, Cr.Cir.exec(f, Mc.M.alloc(16n), X.X.st(regs, m, nx, fi, im, pg, lim, inp)),
    st2 => QA(ds, ks, img, regs, m, nx, fi, im, lim, inp, os, fs, sp, ps, st2), s => st2 => Empty, D.Budget(ds, st0, t), lim):
  match ps:
    case Nil{}:
      +o = Cr.Cir.exec(f, Mc.M.alloc(16n), X.X.st(regs, m, nx, fi, im, pg, lim, inp))
      D.postb.wk(False{}, o, st2 => QA(ds, ks, img, regs, m, nx, fi, im, lim, inp, os, fs, sp, Nil{}, st2), s => st2 => Empty,
        Nat.mul(20n, Nat.add(U32.to_nat(nx), 1n)), D.Budget(ds, st0, t), lim,
        D.alloc.post(f, True{}, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, 16n, KEEP(), os, Nil{}, fs, sp, pend, Nil{}, Nil{}, zs,
          hs, hac, hl, hp, {==}, {==}),
        hroom({==}))
    case Con{+p, +rest}:
      (_, r1) = hs
      (_, r2) = r1
      (_, r3) = r2
      (_, r4) = r3
      (hheap, _) = r4
      (hch, _) = hheap
      (+ep, r5) = hch
      (+ep0, _) = r5
      +hz = {(%Equal.sym(U32, pend, p, ep) : {U32.is_eq(_, 0) == False{} : Bool}; ep0) : {U32.is_eq(pend, 0) == False{} : Bool}}
      +o = Cr.Cir.exec(f, Mc.M.alloc(16n), X.X.st(regs, m, nx, fi, im, pg, lim, inp))
      safe.postb(False{}, o, st2 => QA(ds, ks, img, regs, m, nx, fi, im, lim, inp, os, fs, sp, Con{p, rest}, st2), s => st2 => Empty,
        Nat.mul(20n, Nat.add(U32.to_nat(nx), 1n)), D.Budget(ds, st0, t), lim,
        D.alloc.post(f, True{}, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, 16n, KEEP(), os, Nil{}, fs, sp, pend, Con{p, rest}, Nil{}, zs,
          hs, hac, hl, hp, {==}, {==}),
        alloc.safe(f, regs, m, nx, fi, im, pg, lim, inp, 16n, pend, hp, hz))

# a cell that M.alloc reused from the pend list, then stored: no more STATIC
# cells
def stat.reuse(+n: Nat, +m: Cr.Cir.Cells, +fi: U32, +ws: List<&2, D.W1>, +z: U32, +x: Cr.Cir.Cell,
  hx: {D.FlW(Cr.Cir.Cell.get(0n, x), 1024) == False{} : Bool}) ->
  N.Le(D.Stat(n, Cr.Cir.Cells.set(Cr.Cir.Cells.set(D.Put1(ws, m), z, Cr.Cir.Cell.zero()), z, x), fi), D.Stat(n, m, fi)):
  +m1 = Cr.Cir.Cells.set(D.Put1(ws, m), z, Cr.Cir.Cell.zero())
  N.le_trans(D.Stat(n, Cr.Cir.Cells.set(m1, z, x), fi), D.Stat(n, m1, fi), D.Stat(n, m, fi), A1.stat.set(n, m1, fi, z, x, hx),
    N.le_trans(D.Stat(n, m1, fi), D.Stat(n, D.Put1(ws, m), fi), D.Stat(n, m, fi), A1.stat.set(n, D.Put1(ws, m), fi, z, Cr.Cir.Cell.zero(), {==}),
      N.le_rw_l(D.Stat(n, m, fi), D.Stat(n, D.Put1(ws, m), fi), D.Stat(n, m, fi),
        Equal.sym(Nat, D.Stat(n, D.Put1(ws, m), fi), D.Stat(n, m, fi), A1.stat.put1(n, ws, m, fi)), N.le_refl(D.Stat(n, m, fi)))))

# a new cell nx, then stored: no more STATIC cells
def stat.new(+m: Cr.Cir.Cells, +nx: U32, +fi: U32, +ws: List<&2, D.W1>, +x: Cr.Cir.Cell,
  hx: {D.FlW(Cr.Cir.Cell.get(0n, x), 1024) == False{} : Bool}, hfn: {U32.is_le(fi, nx) == True{} : Bool},
  +e: U32, hl: {U32.is_lt(nx, e) == True{} : Bool}) ->
  N.Le(D.Stat(Nat.sub(U32.to_nat(U32.inc(nx)), U32.to_nat(fi)), Cr.Cir.Cells.set(Cr.Cir.Cells.set(D.Put1(ws, m), nx, Cr.Cir.Cell.zero()), nx, x), fi),
    D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi)):
  +n1 = Nat.sub(U32.to_nat(U32.inc(nx)), U32.to_nat(fi))
  +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
  +m1 = Cr.Cir.Cells.set(D.Put1(ws, m), nx, Cr.Cir.Cell.zero())
  N.le_trans(D.Stat(n1, Cr.Cir.Cells.set(m1, nx, x), fi), D.Stat(n1, m1, fi), D.Stat(n, m, fi), A1.stat.set(n1, m1, fi, nx, x, hx),
    N.le_rw_l(D.Stat(n, m, fi), D.Stat(n1, m1, fi), D.Stat(n, m, fi),
      Equal.sym(Nat, D.Stat(n1, m1, fi), D.Stat(n, m, fi),
        Equal.trans(Nat, D.Stat(n1, m1, fi), D.Stat(n, D.Put1(ws, m), fi), D.Stat(n, m, fi),
          A1.stat.fresh(D.Put1(ws, m), nx, fi, e, hfn, hl), A1.stat.put1(n, ws, m, fi))),
      N.le_refl(D.Stat(n, m, fi))))


# a cell that is all zeros holds no pointer (the table's mask of Var is 0)
def fs.zero(+m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ps: List<&2, U32>, +z: U32, tb: D.Tbl(m, im, fi, nx),
  e0: {Cr.Cir.Cells.get(m, z) == Cr.Cir.Cell.zero() : Cr.Cir.Cell}) -> {D.Fs(m, ps, z) == Nil{} : List<&2, U32>}:
  %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(m, z), Cr.Cir.Cell.zero(), e0) :
    {FsT(D.TgW(Cr.Cir.Cell.get(0n, _)), D.Mem(ps, z), D.Fd(2n, m, U32.add(272, D.TgW(Cr.Cir.Cell.get(0n, _)))), _) == Nil{} : List<&2, U32>}
  %Equal.sym(U32, D.Fd(2n, m, U32.add(272, D.A.tag(Bk.Term.Var{0n}))), D.Mask(Bk.Term.Var{0n}), D.tbl.mask(m, im, fi, nx, Bk.Term.Var{0n}, tb)) :
    {D.Fs.term(_, 0, 0, 0) == Nil{} : List<&2, U32>}
  {==}

# a cell past 290 is not 0
def ne0.of(+z: U32, h: N.Le(1n+U32.to_nat(290), U32.to_nat(z))) -> {U32.is_eq(z, 0) == False{} : Bool}:
  ne.lt(z, 0, N.le_trans(1n+U32.to_nat(0), 1n+U32.to_nat(290), U32.to_nat(z), N.toLe(1n+U32.to_nat(0), 1n+U32.to_nat(290), {==}), h))

# the first of a pair
def p2.fst(-A: Data, -B: Data, p: D.P2(A, B)) -> A:
  match p:
    case Tuple{a, _}:
      a

# register 2 is one that M.push's M.alloc keeps
def kept.get2(+regs: List<&2, U32>, +regs1: List<&2, U32>, kept: D.Kept(regs, regs1, KEEP())) ->
  {List.get(&2, U32, regs1, 2n) == List.get(&2, U32, regs, 2n) : Maybe<&2, U32>}:
  match kept:
    case Tuple{_, Tuple{_, Tuple{e2, _}}}:
      e2

# the term that the one temporary holds
def acc.held(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32,
  +im: U32, +os: List<&2, D.Rt>, +z: U32, +kv: U32, +b: Bk.Term, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, os, [D.TmpE{z, [D.Rt{kv, b}]}], sp, fs, ps, zs)) -> D.IsK(True{}, ds, m, im, fi, nx, ks, img, kv, b):
  match hac:
    case Tuple{_, Tuple{Tuple{i, _}, _}}:
      i

# the STATIC cells after a new cell
def push.statnew(+m: Cr.Cir.Cells, +nx: U32, +fi: U32, +ps: List<&2, U32>, +z: U32, +nx1: U32, +ws: List<&2, D.W1>, +x: Cr.Cir.Cell,
  hx: {D.FlW(Cr.Cir.Cell.get(0n, x), 1024) == False{} : Bool}, hfn: {U32.is_le(fi, nx) == True{} : Bool},
  e: {Bool.and(D.Pend.none(ps), Bool.and(U32.is_eq(z, nx), U32.is_eq(nx1, U32.inc(nx)))) == True{} : Bool},
  hown: {D.Own(fi, nx1, z) == True{} : Bool}) ->
  N.Le(D.Stat(Nat.sub(U32.to_nat(nx1), U32.to_nat(fi)), Cr.Cir.Cells.set(Cr.Cir.Cells.set(D.Put1(ws, m), z, Cr.Cir.Cell.zero()), z, x), fi),
    D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi)):
  +e2 = D.and.r(D.Pend.none(ps), Bool.and(U32.is_eq(z, nx), U32.is_eq(nx1, U32.inc(nx))), e)
  +ez = D.u32.eq(z, nx, D.and.l(U32.is_eq(z, nx), U32.is_eq(nx1, U32.inc(nx)), e2))
  +en = D.u32.eq(nx1, U32.inc(nx), D.and.r(U32.is_eq(z, nx), U32.is_eq(nx1, U32.inc(nx)), e2))
  +hl = {(%ez : {U32.is_lt(_, nx1) == True{} : Bool}; D.and.r(U32.is_le(fi, z), U32.is_lt(z, nx1), hown)) :
    {U32.is_lt(nx, nx1) == True{} : Bool}}
  %Equal.sym(U32, z, nx, ez) :
    N.Le(D.Stat(Nat.sub(U32.to_nat(nx1), U32.to_nat(fi)), Cr.Cir.Cells.set(Cr.Cir.Cells.set(D.Put1(ws, m), _, Cr.Cir.Cell.zero()), _, x), fi),
      D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi))
  %Equal.sym(U32, nx1, U32.inc(nx), en) :
    N.Le(D.Stat(Nat.sub(U32.to_nat(_), U32.to_nat(fi)), Cr.Cir.Cells.set(Cr.Cir.Cells.set(D.Put1(ws, m), nx, Cr.Cir.Cell.zero()), nx, x), fi),
      D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi))
  stat.new(m, nx, fi, ws, x, hx, hfn, nx1, hl)

# the STATIC cells after M.push's M.alloc and store: no more
def push.statle(+m: Cr.Cir.Cells, +nx: U32, +fi: U32, +ps: List<&2, U32>, +z: U32, +nx1: U32, +m1: Cr.Cir.Cells, +x: Cr.Cir.Cell,
  +hx: {D.FlW(Cr.Cir.Cell.get(0n, x), 1024) == False{} : Bool}, +hfn: {U32.is_le(fi, nx) == True{} : Bool},
  hws: D.Ex(List<&2, D.W1>, ws => D.P2({m1 == Cr.Cir.Cells.set(D.Put1(ws, m), z, Cr.Cir.Cell.zero()) : Cr.Cir.Cells}, {D.Took(ws, ps, m) == True{} : Bool})),
  hor: {Bool.or(Bool.and(D.Mem(ps, z), U32.is_eq(nx1, nx)), Bool.and(D.Pend.none(ps), Bool.and(U32.is_eq(z, nx), U32.is_eq(nx1, U32.inc(nx))))) == True{} : Bool},
  hown: {D.Own(fi, nx1, z) == True{} : Bool}) ->
  N.Le(D.Stat(Nat.sub(U32.to_nat(nx1), U32.to_nat(fi)), Cr.Cir.Cells.set(m1, z, x), fi), D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi)):
  match hws:
    case Tuple{+ws, Tuple{em1, _}}:
      +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
      %Equal.sym(Cr.Cir.Cells, m1, Cr.Cir.Cells.set(D.Put1(ws, m), z, Cr.Cir.Cell.zero()), em1) :
        N.Le(D.Stat(Nat.sub(U32.to_nat(nx1), U32.to_nat(fi)), Cr.Cir.Cells.set(_, z, x), fi), D.Stat(n, m, fi))
      D.or.cases(Bool.and(D.Mem(ps, z), U32.is_eq(nx1, nx)), Bool.and(D.Pend.none(ps), Bool.and(U32.is_eq(z, nx), U32.is_eq(nx1, U32.inc(nx)))),
        N.Le(D.Stat(Nat.sub(U32.to_nat(nx1), U32.to_nat(fi)), Cr.Cir.Cells.set(Cr.Cir.Cells.set(D.Put1(ws, m), z, Cr.Cir.Cell.zero()), z, x), fi), D.Stat(n, m, fi)),
        hor,
        e => (%Equal.sym(U32, nx1, nx, D.u32.eq(nx1, nx, D.and.r(D.Mem(ps, z), U32.is_eq(nx1, nx), e))) :
            N.Le(D.Stat(Nat.sub(U32.to_nat(_), U32.to_nat(fi)), Cr.Cir.Cells.set(Cr.Cir.Cells.set(D.Put1(ws, m), z, Cr.Cir.Cell.zero()), z, x), fi), D.Stat(n, m, fi));
          stat.reuse(n, m, fi, ws, z, x, hx)),
        e => push.statnew(m, nx, fi, ps, z, nx1, ws, x, hx, hfn, e, hown))

# the length and the kept registers that Same says, of a state
def same.lk(+regs: List<&2, U32>, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +regs1: List<&2, U32>, +m1: Cr.Cir.Cells,
  +nx1: U32, +pg1: U32, h: D.Same(regs, fi, im, lim, inp, KEEP(), X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp))) ->
  D.P2({List.length(&2, U32, regs1) == 63n : Nat}, D.Kept(regs, regs1, KEEP())):
  match h:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, r}}}}}}:
      r

# the push past its M.alloc, from the state that it gives (with fi, im, lim,
# inp and no output, as Same says)
def push.go2(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st0: Cr.Cir.State, +t: Bk.Term,
  +w: Nat, +lim: U32, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +inp: List<&2, Word(8n)>,
  +os: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +q: Bk.Quan, +kf: Bool, +b: Bk.Term, +b2: Bk.Term,
  +h: Cr.Cir.Expr, +a: Cr.Cir.Expr, +bx: Cr.Cir.Expr, +hv: U32, +kv: U32, +bv: U32, +rest: Cr.Cir.Stmt,
  +regs1: List<&2, U32>, +m1: Cr.Cir.Cells, +nx1: U32, +pg1: U32,
  +htg: {D.TgW(hv) == 33 : U32}, +hq: {D.QnW(hv) == Mc.Img.quan(q) : U32}, +hst: {D.FlW(hv, 1024) == False{} : Bool},
  +hk: {D.FlW(hv, 2048) == kf : Bool}, +hsp: {List.get(&2, U32, regs, 2n) == Some{sp} : Maybe<&2, U32>},
  hfn: {U32.is_le(fi, nx) == True{} : Bool},
  eh: @rr: List<&2, U32> -> D.Kept(regs, rr, KEEP()) -> @mz: Cr.Cir.Cells -> @nz: U32 -> @pz: U32 -> {Cr.Cir.eval(h, X.X.st(rr, mz, nz, fi, im, pz, lim, inp)) == Some{hv} : Maybe<&2, U32>},
  ea: @rr: List<&2, U32> -> D.Kept(regs, rr, KEEP()) -> @mz: Cr.Cir.Cells -> @nz: U32 -> @pz: U32 -> {Cr.Cir.eval(a, X.X.st(rr, mz, nz, fi, im, pz, lim, inp)) == Some{kv} : Maybe<&2, U32>},
  eb: @rr: List<&2, U32> -> D.Kept(regs, rr, KEEP()) -> @mz: Cr.Cir.Cells -> @nz: U32 -> @pz: U32 -> {Cr.Cir.eval(bx, X.X.st(rr, mz, nz, fi, im, pz, lim, inp)) == Some{bv} : Maybe<&2, U32>},
  +same: D.Same(regs, fi, im, lim, inp, KEEP(), X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp)),
  ex: EXA(ds, ks, img, m, nx, fi, im, Con{D.Rt{kv, b}, os}, fs, sp, ps, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp)),
  k: @z: U32 -> @pend2: U32 -> @ps2: List<&2, U32> -> @zs2: List<&2, D.Rt> ->
    {List.length(&2, U32, regs1) == 63n : Nat} -> D.Kept(regs, regs1, KEEP()) -> {List.get(&2, U32, regs1, 3n) == Some{pend2} : Maybe<&2, U32>} ->
    N.Le(D.Stat(Nat.sub(U32.to_nat(nx1), U32.to_nat(fi)), Cr.Cir.Cells.set(m1, z, Cr.Cir.Cell{hv, sp, kv, bv, 0}), fi), D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi)) ->
    {Bool.or(Bool.and(D.Mem(ps, z), U32.is_eq(nx1, nx)), Bool.and(D.Pend.none(ps), Bool.and(U32.is_eq(z, nx), U32.is_eq(nx1, U32.inc(nx))))) == True{} : Bool} ->
    D.HSK(True{}, ds, ks, img, Cr.Cir.Cells.set(m1, z, Cr.Cir.Cell{hv, sp, kv, bv, 0}), nx1, fi, im, os, Nil{}, Con{D.AF{D.FK.val{}, q, kf, b, b2}, fs}, z, pend2, ps2) ->
    D.AccK(True{}, ds, ks, img, Cr.Cir.Cells.set(m1, z, Cr.Cir.Cell{hv, sp, kv, bv, 0}), nx1, fi, im, os, Nil{}, z, Con{D.AF{D.FK.val{}, q, kf, b, b2}, fs}, ps2, zs2) ->
    PB(ds, ks, img, st0, t, w, lim, Cr.Cir.exec(f, rest, X.X.st(X.X.set(regs1, 2n, z), Cr.Cir.Cells.set(m1, z, Cr.Cir.Cell{hv, sp, kv, bv, 0}), nx1, fi, im, pg1, lim, inp)))) ->
  PB(ds, ks, img, st0, t, w, lim, Cr.Cir.exec(f, Cr.Cir.Stmt.seq{X.sel.b(Mc.M.push(h, a, bx)), rest}, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp))):
  match ex:
        case Tuple{+z, Tuple{+pend2, Tuple{+ps2, Tuple{hz16, Tuple{hz3, Tuple{+ez0, Tuple{+hown, Tuple{+hmem, Tuple{_, Tuple{+hor2, Tuple{hws, Tuple{_, Tuple{hptr, Tuple{+hs1, Tuple{+zs2, hac1}}}}}}}}}}}}}}}:
          +lk = same.lk(regs, fi, im, lim, inp, regs1, m1, nx1, pg1, same)
          +elen = p2.fst({List.length(&2, U32, regs1) == 63n : Nat}, D.Kept(regs, regs1, KEEP()), lk)
          +kept = p2.snd({List.length(&2, U32, regs1) == 63n : Nat}, D.Kept(regs, regs1, KEEP()), lk)
          +x = {Cr.Cir.Cell{hv, sp, kv, bv, 0} : Cr.Cir.Cell}
          +m2 = Cr.Cir.Cells.set(m1, z, x)
          +st1 = X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp)
          +st2 = X.X.st(X.X.set(regs1, 2n, z), m2, nx1, fi, im, pg1, lim, inp)
          +hio1 = p2.snd(D.Heap(m1, nx1, fi, im, D.Rt.cells(Con{D.Rt{kv, b}, os}), pend2, ps2), D.ImgOKK(True{}, ds, ks, img, m1, im, fi, nx1),
            p2.snd(D.FrsK(True{}, ds, m1, im, fi, nx1, ks, img, ps2, sp, fs), D.P2(D.Heap(m1, nx1, fi, im, D.Rt.cells(Con{D.Rt{kv, b}, os}), pend2, ps2), D.ImgOKK(True{}, ds, ks, img, m1, im, fi, nx1)),
            p2.snd(D.Held(m1, Con{D.Rt{kv, b}, os}, Nil{}), D.P2(D.FrsK(True{}, ds, m1, im, fi, nx1, ks, img, ps2, sp, fs), D.P2(D.Heap(m1, nx1, fi, im, D.Rt.cells(Con{D.Rt{kv, b}, os}), pend2, ps2), D.ImgOKK(True{}, ds, ks, img, m1, im, fi, nx1))),
            p2.snd(D.RtsK(True{}, ds, m1, im, fi, nx1, ks, img, Nil{}), D.P2(D.Held(m1, Con{D.Rt{kv, b}, os}, Nil{}), D.P2(D.FrsK(True{}, ds, m1, im, fi, nx1, ks, img, ps2, sp, fs), D.P2(D.Heap(m1, nx1, fi, im, D.Rt.cells(Con{D.Rt{kv, b}, os}), pend2, ps2), D.ImgOKK(True{}, ds, ks, img, m1, im, fi, nx1)))),
            p2.snd(D.RtsK(True{}, ds, m1, im, fi, nx1, ks, img, Con{D.Rt{kv, b}, os}), D.P2(D.RtsK(True{}, ds, m1, im, fi, nx1, ks, img, Nil{}), D.P2(D.Held(m1, Con{D.Rt{kv, b}, os}, Nil{}), D.P2(D.FrsK(True{}, ds, m1, im, fi, nx1, ks, img, ps2, sp, fs), D.P2(D.Heap(m1, nx1, fi, im, D.Rt.cells(Con{D.Rt{kv, b}, os}), pend2, ps2), D.ImgOKK(True{}, ds, ks, img, m1, im, fi, nx1))))), hs1)))))
          +h290 = D.img.hz(True{}, ds, ks, img, m1, im, fi, nx1, z, hio1, hown)
          +esp1 = Equal.trans(Maybe<&2, U32>, List.get(&2, U32, regs1, 2n), List.get(&2, U32, regs, 2n), Some{sp},
            kept.get2(regs, regs1, kept), hsp)
          +hcz = D.or.r(Bool.and(Bool.not(U32.is_zero(z)), U32.is_le(z, im)), D.Own(fi, nx1, z), hown)
          +eqs = stores.eq(f, h, a, bx, regs1, m1, nx1, fi, im, pg1, lim, inp, z, sp, hv, kv, bv, hz16, esp1, hcz, elen, ez0,
            eh(regs1, kept, m1, nx1, pg1), ea(regs1, kept, X.X.put(X.X.put(m1, 0n, z, hv), 1n, z, sp), nx1, pg1),
            eb(regs1, kept, X.X.put(X.X.put(X.X.put(m1, 0n, z, hv), 1n, z, sp), 2n, z, kv), nx1, pg1))
          +hzs = {(%Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(m1, z), Cr.Cir.Cell.zero(), ez0) :
              {U32.is_ne(U32.and(Cr.Cir.Cell.get(0n, _), 1024), 0) == False{} : Bool}; {==}) : {D.Fl(m1, z, 1024) == False{} : Bool}}
          +hzt = {(%Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(m1, z), Cr.Cir.Cell.zero(), ez0) :
              {Bool.or(U32.is_lt(U32.and(Cr.Cir.Cell.get(0n, _), 63), 32), U32.is_le(41, U32.and(Cr.Cir.Cell.get(0n, _), 63))) == True{} : Bool}; {==}) :
            {Bool.or(U32.is_lt(D.Tg(m1, z), 32), U32.is_le(41, D.Tg(m1, z))) == True{} : Bool}}
          +hzf = fs.zero(m1, im, fi, nx1, ps2, z, D.img.tbl(True{}, ds, ks, img, m1, im, fi, nx1, hio1), ez0)
          +ht = {(%Equal.sym(U32, D.TgW(hv), 33, htg) : {U32.is_le(32, _) == True{} : Bool}; {==}) : {U32.is_le(32, D.TgW(hv)) == True{} : Bool}}
          +egs = D.cl.gs(m1, z, x)
          +hf = {(%Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(m2, z), x, egs) :
              {FsT(D.TgW(Cr.Cir.Cell.get(0n, _)), D.Mem(ps2, z), D.Fd(2n, m2, U32.add(272, D.TgW(Cr.Cir.Cell.get(0n, _)))), _) == [kv] : List<&2, U32>};
            %Equal.sym(U32, D.TgW(hv), 33, htg) : {FsT(_, D.Mem(ps2, z), D.Fd(2n, m2, U32.add(272, _)), x) == [kv] : List<&2, U32>};
            %Equal.sym(Bool, D.Mem(ps2, z), False{}, hmem) : {FsT(33, _, D.Fd(2n, m2, U32.add(272, 33)), x) == [kv] : List<&2, U32>};
            fst.ok(D.FK.val{}, D.Fd(2n, m2, U32.add(272, 33)), x, {==})) : {D.Fs(m2, ps2, z) == [kv] : List<&2, U32>}}
          +sp2 = D.store.post(True{}, ds, ks, img, m1, nx1, fi, im, [D.Rt{kv, b}], os, Nil{}, fs, sp, pend2, ps2, z, x, [D.TmpE{z, Nil{}}], zs2,
            hs1, hac1, {==}, Unit{}, hown, hmem, hzs, hzt, hptr, hzf, ht, hst, hf)
          +hs2 = p2.fst(D.HSK(True{}, ds, ks, img, m2, nx1, fi, im, os, Nil{}, fs, sp, pend2, ps2),
            D.AccK(True{}, ds, ks, img, m2, nx1, fi, im, os, [D.TmpE{z, [D.Rt{kv, b}]}], sp, fs, ps2, zs2), sp2)
          +hac2 = p2.snd(D.HSK(True{}, ds, ks, img, m2, nx1, fi, im, os, Nil{}, fs, sp, pend2, ps2),
            D.AccK(True{}, ds, ks, img, m2, nx1, fi, im, os, [D.TmpE{z, [D.Rt{kv, b}]}], sp, fs, ps2, zs2), sp2)
          +hib = acc.held(ds, ks, img, m2, nx1, fi, im, os, z, kv, b, fs, sp, ps2, zs2, hac2)
          +hs3 = frame.hsk(ds, ks, img, m2, nx1, fi, im, os, Nil{}, fs, sp, pend2, ps2, z, q, kf, b, b2, hv, kv, bv, egs,
            ne0.of(z, h290), hcz, hown, hmem, htg, hq, hst, hk, hib, hs2)
          +hac3 = frame.acc(ds, ks, img, m2, nx1, fi, im, os, fs, sp, ps2, zs2, z, q, kf, b, b2, hv, kv, bv, egs, hac2)
          %X.rw.seq(f, X.sel.b(Mc.M.push(h, a, bx)), rest, st1, st2, eqs) : PB(ds, ks, img, st0, t, w, lim, _)
          k(z, pend2, ps2, zs2, elen, kept, hz3, push.statle(m, nx, fi, ps, z, nx1, m1, x, hst, hfn, hws, hor2, hown), hor2, hs3, hac3)

def St.pages(st: Cr.Cir.State) -> U32:
  match st:
    case Cr.Cir.State{_, _, _, _, _, pg, _, _, _, _}:
      pg

# a state of which Same holds has fi, im, lim, inp and no output
def same.st(st: Cr.Cir.State, +regs: List<&2, U32>, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +keep: List<&2, Nat>,
  h: D.Same(regs, fi, im, lim, inp, keep, st)) ->
  {X.X.st(D.St.regs(st), D.St.cells(st), D.St.next(st), fi, im, St.pages(st), lim, inp) == st : Cr.Cir.State}:
  match st:
    case Cr.Cir.State{+regs1, +m1, +nx1, +fi1, +im1, +pg1, +lim1, +inp1, +out1, +outn1}:
      match h:
        case Tuple{efi, Tuple{eim, Tuple{elim, Tuple{einp, Tuple{eout, Tuple{eoutn, _}}}}}}:
          %efi : {X.X.st(regs1, m1, nx1, _, im, pg1, lim, inp) == Cr.Cir.State{regs1, m1, nx1, fi1, im1, pg1, lim1, inp1, out1, outn1} : Cr.Cir.State}
          %eim : {X.X.st(regs1, m1, nx1, fi1, _, pg1, lim, inp) == Cr.Cir.State{regs1, m1, nx1, fi1, im1, pg1, lim1, inp1, out1, outn1} : Cr.Cir.State}
          %elim : {X.X.st(regs1, m1, nx1, fi1, im1, pg1, _, inp) == Cr.Cir.State{regs1, m1, nx1, fi1, im1, pg1, lim1, inp1, out1, outn1} : Cr.Cir.State}
          %einp : {X.X.st(regs1, m1, nx1, fi1, im1, pg1, lim1, _) == Cr.Cir.State{regs1, m1, nx1, fi1, im1, pg1, lim1, inp1, out1, outn1} : Cr.Cir.State}
          %Equal.sym(List<&2, Word(8n)>, out1, Nil{}, eout) : {Cr.Cir.State{regs1, m1, nx1, fi1, im1, pg1, lim1, inp1, Nil{}, 0} == Cr.Cir.State{regs1, m1, nx1, fi1, im1, pg1, lim1, inp1, _, outn1} : Cr.Cir.State}
          %Equal.sym(U32, outn1, 0, eoutn) : {Cr.Cir.State{regs1, m1, nx1, fi1, im1, pg1, lim1, inp1, Nil{}, 0} == Cr.Cir.State{regs1, m1, nx1, fi1, im1, pg1, lim1, inp1, Nil{}, _} : Cr.Cir.State}
          {==}

# the own cells are from fi to nx
def hsk.fn(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32,
  +im: U32, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>,
  hs: D.HSK(True{}, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps)) -> {U32.is_le(fi, nx) == True{} : Bool}:
  match hs:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, e}}}}}, _}}}}}:
      e

# the push past its M.alloc, from the state st1 that it gives
def push.go(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st0: Cr.Cir.State, +t: Bk.Term,
  +w: Nat, +lim: U32, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +inp: List<&2, Word(8n)>,
  +os: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +q: Bk.Quan, +kf: Bool, +b: Bk.Term, +b2: Bk.Term,
  +h: Cr.Cir.Expr, +a: Cr.Cir.Expr, +bx: Cr.Cir.Expr, +hv: U32, +kv: U32, +bv: U32, +rest: Cr.Cir.Stmt,
  +htg: {D.TgW(hv) == 33 : U32}, +hq: {D.QnW(hv) == Mc.Img.quan(q) : U32}, +hst: {D.FlW(hv, 1024) == False{} : Bool},
  +hk: {D.FlW(hv, 2048) == kf : Bool}, +hsp: {List.get(&2, U32, regs, 2n) == Some{sp} : Maybe<&2, U32>},
  +hfn: {U32.is_le(fi, nx) == True{} : Bool},
  eh: @rr: List<&2, U32> -> D.Kept(regs, rr, KEEP()) -> @mz: Cr.Cir.Cells -> @nz: U32 -> @pz: U32 -> {Cr.Cir.eval(h, X.X.st(rr, mz, nz, fi, im, pz, lim, inp)) == Some{hv} : Maybe<&2, U32>},
  ea: @rr: List<&2, U32> -> D.Kept(regs, rr, KEEP()) -> @mz: Cr.Cir.Cells -> @nz: U32 -> @pz: U32 -> {Cr.Cir.eval(a, X.X.st(rr, mz, nz, fi, im, pz, lim, inp)) == Some{kv} : Maybe<&2, U32>},
  eb: @rr: List<&2, U32> -> D.Kept(regs, rr, KEEP()) -> @mz: Cr.Cir.Cells -> @nz: U32 -> @pz: U32 -> {Cr.Cir.eval(bx, X.X.st(rr, mz, nz, fi, im, pz, lim, inp)) == Some{bv} : Maybe<&2, U32>},
  +st1: Cr.Cir.State,
  qa: QA(ds, ks, img, regs, m, nx, fi, im, lim, inp, Con{D.Rt{kv, b}, os}, fs, sp, ps, st1),
  k: @regs1: List<&2, U32> -> @m1: Cr.Cir.Cells -> @nx1: U32 -> @pg1: U32 -> @z: U32 -> @pend2: U32 -> @ps2: List<&2, U32> -> @zs2: List<&2, D.Rt> ->
    {List.length(&2, U32, regs1) == 63n : Nat} -> D.Kept(regs, regs1, KEEP()) -> {List.get(&2, U32, regs1, 3n) == Some{pend2} : Maybe<&2, U32>} ->
    N.Le(D.Stat(Nat.sub(U32.to_nat(nx1), U32.to_nat(fi)), Cr.Cir.Cells.set(m1, z, Cr.Cir.Cell{hv, sp, kv, bv, 0}), fi), D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi)) ->
    {Bool.or(Bool.and(D.Mem(ps, z), U32.is_eq(nx1, nx)), Bool.and(D.Pend.none(ps), Bool.and(U32.is_eq(z, nx), U32.is_eq(nx1, U32.inc(nx))))) == True{} : Bool} ->
    D.HSK(True{}, ds, ks, img, Cr.Cir.Cells.set(m1, z, Cr.Cir.Cell{hv, sp, kv, bv, 0}), nx1, fi, im, os, Nil{}, Con{D.AF{D.FK.val{}, q, kf, b, b2}, fs}, z, pend2, ps2) ->
    D.AccK(True{}, ds, ks, img, Cr.Cir.Cells.set(m1, z, Cr.Cir.Cell{hv, sp, kv, bv, 0}), nx1, fi, im, os, Nil{}, z, Con{D.AF{D.FK.val{}, q, kf, b, b2}, fs}, ps2, zs2) ->
    PB(ds, ks, img, st0, t, w, lim, Cr.Cir.exec(f, rest, X.X.st(X.X.set(regs1, 2n, z), Cr.Cir.Cells.set(m1, z, Cr.Cir.Cell{hv, sp, kv, bv, 0}), nx1, fi, im, pg1, lim, inp)))) ->
  PB(ds, ks, img, st0, t, w, lim, Cr.Cir.exec(f, Cr.Cir.Stmt.seq{X.sel.b(Mc.M.push(h, a, bx)), rest}, st1)):
  match qa:
    case Tuple{Tuple{+same, ex}, _}:
      +P = {Cr.Cir.Stmt.seq{X.sel.b(Mc.M.push(h, a, bx)), rest} : Cr.Cir.Stmt}
      +OS = {Con{D.Rt{kv, b}, os} : List<&2, D.Rt>}
      +e = same.st(st1, regs, fi, im, lim, inp, KEEP(), same)
      g = {(%e : (@sm: D.Same(regs, fi, im, lim, inp, KEEP(), _) -> @ex2: EXA(ds, ks, img, m, nx, fi, im, OS, fs, sp, ps, _) ->
            PB(ds, ks, img, st0, t, w, lim, Cr.Cir.exec(f, P, _)));
          sm => ex2 => push.go2(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, inp, os, fs, sp, ps, q, kf, b, b2, h, a, bx, hv, kv, bv, rest,
            D.St.regs(st1), D.St.cells(st1), D.St.next(st1), St.pages(st1), htg, hq, hst, hk, hsp, hfn, eh, ea, eb, sm, ex2,
            k(D.St.regs(st1), D.St.cells(st1), D.St.next(st1), St.pages(st1)))) :
        @sm: D.Same(regs, fi, im, lim, inp, KEEP(), st1) -> @ex2: EXA(ds, ks, img, m, nx, fi, im, OS, fs, sp, ps, st1) ->
          PB(ds, ks, img, st0, t, w, lim, Cr.Cir.exec(f, P, st1))}
      g(same, ex)

# M.push(h, a, bx) of the frame App q □ b (app_val, the header hv, the field
# 2 kv of b's root, the first root), with room for a new cell when the pend
# list is empty: the frame is pushed, and the root of b is its term
def pb.push(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st0: Cr.Cir.State, +t: Bk.Term,
  +w: Nat, +lim: U32, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +inp: List<&2, Word(8n)>,
  +os: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>, +zs: List<&2, D.Rt>, +q: Bk.Quan, +kf: Bool,
  +b: Bk.Term, +b2: Bk.Term, +h: Cr.Cir.Expr, +a: Cr.Cir.Expr, +bx: Cr.Cir.Expr, +hv: U32, +kv: U32, +bv: U32, +rest: Cr.Cir.Stmt,
  +hs: D.HSK(True{}, ds, ks, img, m, nx, fi, im, Con{D.Rt{kv, b}, os}, Nil{}, fs, sp, pend, ps),
  hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, Con{D.Rt{kv, b}, os}, Nil{}, sp, fs, ps, zs),
  +hl: {List.length(&2, U32, regs) == 63n : Nat}, +hp: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>},
  +hsp: {List.get(&2, U32, regs, 2n) == Some{sp} : Maybe<&2, U32>},
  +htg: {D.TgW(hv) == 33 : U32}, +hq: {D.QnW(hv) == Mc.Img.quan(q) : U32}, +hst: {D.FlW(hv, 1024) == False{} : Bool},
  +hk: {D.FlW(hv, 2048) == kf : Bool},
  eh: @rr: List<&2, U32> -> D.Kept(regs, rr, KEEP()) -> @mz: Cr.Cir.Cells -> @nz: U32 -> @pz: U32 -> {Cr.Cir.eval(h, X.X.st(rr, mz, nz, fi, im, pz, lim, inp)) == Some{hv} : Maybe<&2, U32>},
  ea: @rr: List<&2, U32> -> D.Kept(regs, rr, KEEP()) -> @mz: Cr.Cir.Cells -> @nz: U32 -> @pz: U32 -> {Cr.Cir.eval(a, X.X.st(rr, mz, nz, fi, im, pz, lim, inp)) == Some{kv} : Maybe<&2, U32>},
  eb: @rr: List<&2, U32> -> D.Kept(regs, rr, KEEP()) -> @mz: Cr.Cir.Cells -> @nz: U32 -> @pz: U32 -> {Cr.Cir.eval(bx, X.X.st(rr, mz, nz, fi, im, pz, lim, inp)) == Some{bv} : Maybe<&2, U32>},
  hroom: {D.Pend.none(ps) == True{} : Bool} -> N.Le(Nat.mul(20n, Nat.add(U32.to_nat(nx), 1n)), D.Budget(ds, st0, t)),
  k: @regs1: List<&2, U32> -> @m1: Cr.Cir.Cells -> @nx1: U32 -> @pg1: U32 -> @z: U32 -> @pend2: U32 -> @ps2: List<&2, U32> -> @zs2: List<&2, D.Rt> ->
    {List.length(&2, U32, regs1) == 63n : Nat} -> D.Kept(regs, regs1, KEEP()) -> {List.get(&2, U32, regs1, 3n) == Some{pend2} : Maybe<&2, U32>} ->
    N.Le(D.Stat(Nat.sub(U32.to_nat(nx1), U32.to_nat(fi)), Cr.Cir.Cells.set(m1, z, Cr.Cir.Cell{hv, sp, kv, bv, 0}), fi), D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi)) ->
    {Bool.or(Bool.and(D.Mem(ps, z), U32.is_eq(nx1, nx)), Bool.and(D.Pend.none(ps), Bool.and(U32.is_eq(z, nx), U32.is_eq(nx1, U32.inc(nx))))) == True{} : Bool} ->
    D.HSK(True{}, ds, ks, img, Cr.Cir.Cells.set(m1, z, Cr.Cir.Cell{hv, sp, kv, bv, 0}), nx1, fi, im, os, Nil{}, Con{D.AF{D.FK.val{}, q, kf, b, b2}, fs}, z, pend2, ps2) ->
    D.AccK(True{}, ds, ks, img, Cr.Cir.Cells.set(m1, z, Cr.Cir.Cell{hv, sp, kv, bv, 0}), nx1, fi, im, os, Nil{}, z, Con{D.AF{D.FK.val{}, q, kf, b, b2}, fs}, ps2, zs2) ->
    PB(ds, ks, img, st0, t, w, lim, Cr.Cir.exec(f, rest, X.X.st(X.X.set(regs1, 2n, z), Cr.Cir.Cells.set(m1, z, Cr.Cir.Cell{hv, sp, kv, bv, 0}), nx1, fi, im, pg1, lim, inp)))) ->
  PB(ds, ks, img, st0, t, w, lim, Cr.Cir.exec(f, Cr.Cir.Stmt.seq{Mc.M.push(h, a, bx), rest}, X.X.st(regs, m, nx, fi, im, pg, lim, inp))):
  +st = X.X.st(regs, m, nx, fi, im, pg, lim, inp)
  +OS = {Con{D.Rt{kv, b}, os} : List<&2, D.Rt>}
  +P = X.sel.b(Mc.M.push(h, a, bx))
  +hfn = hsk.fn(ds, ks, img, m, nx, fi, im, OS, Nil{}, fs, sp, pend, ps, hs)
  %seq.assoc(f, Mc.M.alloc(16n), P, rest, st) : PB(ds, ks, img, st0, t, w, lim, _)
  D.postb.seq(f, False{}, Mc.M.alloc(16n), Cr.Cir.Stmt.seq{P, rest}, st,
    st2 => QA(ds, ks, img, regs, m, nx, fi, im, lim, inp, OS, fs, sp, ps, st2),
    s => K.MV.next(ds, ks, img, st0, t, w, s), s => st2 => Empty, s => st2 => D.HR(ds, t, s, st2), D.Budget(ds, st0, t), lim,
    alloc.pb(f, ds, ks, img, st0, t, regs, m, nx, fi, im, pg, lim, inp, OS, fs, sp, pend, ps, zs, hs, hac, hl, hp, hroom),
    s => st2 => e => Empty.absurd(D.HR(ds, t, s, st2), e),
    st1 => qa => push.go(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, inp, os, fs, sp, ps, q, kf, b, b2, h, a, bx, hv, kv, bv, rest,
      htg, hq, hst, hk, hsp, hfn, eh, ea, eb, st1, qa, k))

# The end of a step
# -----------------
#
# A state whose registers are RG of the focus n, mode 0, sp and pend, of
# which HS holds with the one root n of h and Acc with no temporary, stands
# for the frames' term around h: if Eval steps t to that term, the round is a
# step (fin.stp).

# 63 registers, as RG names them, from their first four
def rg.eq(+regs: List<&2, U32>, +a0: U32, +a1: U32, +a2: U32, +a3: U32, hl: {List.length(&2, U32, regs) == 63n : Nat},
  h0: {List.get(&2, U32, regs, 0n) == Some{a0} : Maybe<&2, U32>}, h1: {List.get(&2, U32, regs, 1n) == Some{a1} : Maybe<&2, U32>},
  h2: {List.get(&2, U32, regs, 2n) == Some{a2} : Maybe<&2, U32>}, h3: {List.get(&2, U32, regs, 3n) == Some{a3} : Maybe<&2, U32>}) ->
  {regs == D.RG(a0, a1, a2, a3, D.R59.list(D.R59.of(regs))) : List<&2, U32>}:
  +g1 = Maybe.default(&2, U32, List.get(&2, U32, regs, 1n), 0)
  +g2 = Maybe.default(&2, U32, List.get(&2, U32, regs, 2n), 0)
  +g3 = Maybe.default(&2, U32, List.get(&2, U32, regs, 3n), 0)
  +R = D.R59.list(D.R59.of(regs))
  %h0 : {regs == D.RG(Maybe.default(&2, U32, _, 0), a1, a2, a3, R) : List<&2, U32>}
  %h1 : {regs == D.RG(Maybe.default(&2, U32, List.get(&2, U32, regs, 0n), 0), Maybe.default(&2, U32, _, 0), a2, a3, R) : List<&2, U32>}
  %h2 : {regs == D.RG(Maybe.default(&2, U32, List.get(&2, U32, regs, 0n), 0), g1, Maybe.default(&2, U32, _, 0), a3, R) : List<&2, U32>}
  %h3 : {regs == D.RG(Maybe.default(&2, U32, List.get(&2, U32, regs, 0n), 0), g1, g2, Maybe.default(&2, U32, _, 0), R) : List<&2, U32>}
  rg.of(regs, hl)

# a step: the round ends in a state of the term u that t steps to
def fin.stp(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st0: Cr.Cir.State, +t: Bk.Term, +w: Nat,
  +u: Bk.Term, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>,
  +n: U32, +h: Bk.Term, +fs: List<&2, D.AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  hs: D.HS(ds, ks, img, m, nx, fi, im, [D.Rt{n, h}], Nil{}, fs, sp, pend, ps),
  hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{n, h}], Nil{}, sp, fs, ps, zs),
  hl: {List.length(&2, U32, regs) == 63n : Nat}, h0: {List.get(&2, U32, regs, 0n) == Some{n} : Maybe<&2, U32>},
  h1: {List.get(&2, U32, regs, 1n) == Some{0} : Maybe<&2, U32>}, h2: {List.get(&2, U32, regs, 2n) == Some{sp} : Maybe<&2, U32>},
  h3: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>},
  et: {D.A.plugs(fs, h) == u : Bk.Term}, es: {El.Eval.step(ds, t) == Some{u} : Maybe<Bk.Term>}, afs: D.AFs.ok(ds, fs),
  hmem: N.Le(D.Mem.cells(X.X.st(regs, m, nx, fi, im, pg, lim, inp)), Nat.max(D.Mem.cells(st0), D.Need(ds, st0, t)))) ->
  K.MV.next(ds, ks, img, st0, t, w, X.X.st(regs, m, nx, fi, im, pg, lim, inp)):
  match hs:
    case Tuple{Tuple{isn, _}, Tuple{_, Tuple{_, Tuple{frs, Tuple{hp, io}}}}}:
      +rest = D.R59.of(regs)
      +x = {D.Wit{False{}, h, fs, n, sp, pend, ps, rest} : D.Wit}
      +w2 = D.A.w(False{}, h, fs)
      +er = rg.eq(regs, n, 0, sp, pend, hl, h0, h1, h2, h3)
      (Inr{(u, (es, (w2, (x, ((et, ({==}, ({==}, (afs, (er, (isn, (frs, (hp, (io, ({==}, {==})))))))))), (zs, hac))))))}, hmem)

# the nodes of the first two roots, in either order
def nodes.swap1(r1: D.Rt, r2: D.Rt, +rs: List<&2, D.Rt>, +m: Cr.Cir.Cells, +c: U32) ->
  {D.Nodes(Con{r1, Con{r2, rs}}, m, c) == D.Nodes(Con{r2, Con{r1, rs}}, m, c) : Bool}:
  match r1 r2:
    case D.Rt{+a, +u} D.Rt{+b, +v}:
      or.swap(D.Node(u, m, a, c), D.Node(v, m, b, c), D.Nodes(rs, m, c))

# Roots and borrowed terms
# ------------------------
#
# The roots' order does not matter to HS and Acc (hsk.swap, acc.swap: the
# first two trade places); a node of an owned root's term may be borrowed
# (hsk.borrow), and a borrowed term dropped (hsk.drop).

# a cell is a node of the term at that cell
def node.self(t: Bk.Term, +m: Cr.Cir.Cells, +r: U32, +c: U32, e: {U32.is_eq(r, c) == True{} : Bool}) -> {D.Node(t, m, r, c) == True{} : Bool}:
  match t:
    case Bk.Term.Var{+i}:
      e
    case Bk.Term.Ref{+k}:
      e
    case Bk.Term.Ann{+y, +z}:
      D.or.l(U32.is_eq(r, c), Bool.or(D.Node(y, m, D.Fd(2n, m, r), c), D.Node(z, m, D.Fd(3n, m, r), c)), e)
    case Bk.Term.Let{+q, +v, +f}:
      D.or.l(U32.is_eq(r, c), Bool.or(D.Node(v, m, D.Fd(2n, m, r), c), D.Node(f, m, D.Fd(3n, m, r), c)), e)
    case Bk.Term.Typ{+y}:
      D.or.l(U32.is_eq(r, c), D.Node(y, m, D.Fd(2n, m, r), c), e)
    case Bk.Term.Min{+a, +b}:
      D.or.l(U32.is_eq(r, c), Bool.or(D.Node(a, m, D.Fd(2n, m, r), c), D.Node(b, m, D.Fd(3n, m, r), c)), e)
    case Bk.Term.All{+q, +a, +b}:
      D.or.l(U32.is_eq(r, c), Bool.or(D.Node(a, m, D.Fd(2n, m, r), c), D.Node(b, m, D.Fd(3n, m, r), c)), e)
    case Bk.Term.Lam{+q, +f}:
      D.or.l(U32.is_eq(r, c), D.Node(f, m, D.Fd(2n, m, r), c), e)
    case Bk.Term.App{+q, +f, +y}:
      D.or.l(U32.is_eq(r, c), Bool.or(D.Node(f, m, D.Fd(2n, m, r), c), D.Node(y, m, D.Fd(3n, m, r), c)), e)
    case Bk.Term.Sig{+q, +a, +b}:
      D.or.l(U32.is_eq(r, c), Bool.or(D.Node(a, m, D.Fd(2n, m, r), c), D.Node(b, m, D.Fd(3n, m, r), c)), e)
    case Bk.Term.Tup{+q, +a, +b}:
      D.or.l(U32.is_eq(r, c), Bool.or(D.Node(a, m, D.Fd(2n, m, r), c), D.Node(b, m, D.Fd(3n, m, r), c)), e)
    case Bk.Term.Prj{+h}:
      D.or.l(U32.is_eq(r, c), D.Node(h, m, D.Fd(2n, m, r), c), e)
    case Bk.Term.Enu{+en}:
      e
    case Bk.Term.Lab{+k}:
      e
    case Bk.Term.Mat{+k, +h, +n}:
      D.or.l(U32.is_eq(r, c), Bool.or(D.Node(h, m, D.Fd(3n, m, r), c), D.Node(n, m, D.Fd(4n, m, r), c)), e)
    case Bk.Term.Efq{}:
      e
    case Bk.Term.Eql{+a, +b, +y}:
      D.or.l(U32.is_eq(r, c), Bool.or(D.Node(a, m, D.Fd(2n, m, r), c), Bool.or(D.Node(b, m, D.Fd(3n, m, r), c), D.Node(y, m, D.Fd(4n, m, r), c))), e)
    case Bk.Term.Rfl{}:
      e
    case Bk.Term.Rwt{+ee, +y, +f}:
      D.or.l(U32.is_eq(r, c), Bool.or(D.Node(ee, m, D.Fd(2n, m, r), c), Bool.or(D.Node(y, m, D.Fd(3n, m, r), c), D.Node(f, m, D.Fd(4n, m, r), c))), e)

# the roots c1, c2 count the same in either order
def rcl.swap(+c1: U32, +c2: U32, +rs: List<&2, U32>, +c: U32) -> {D.RcL(Con{c2, Con{c1, rs}}, c) == D.RcL(Con{c1, Con{c2, rs}}, c) : Nat}:
  +A = D.Nat.of(U32.is_eq(c1, c))
  +B = D.Nat.of(U32.is_eq(c2, c))
  +R = D.RcL(rs, c)
  Equal.trans(Nat, Nat.add(B, Nat.add(A, R)), Nat.add(Nat.add(B, A), R), Nat.add(A, Nat.add(B, R)),
    Equal.sym(Nat, Nat.add(Nat.add(B, A), R), Nat.add(B, Nat.add(A, R)), add.assoc(B, A, R)),
    Equal.trans(Nat, Nat.add(Nat.add(B, A), R), Nat.add(Nat.add(A, B), R), Nat.add(A, Nat.add(B, R)),
      Equal.cong(Nat, Nat, x => Nat.add(x, R), Nat.add(B, A), Nat.add(A, B), add.comm(B, A)), add.assoc(A, B, R)))

def ptr.swap(+n: Nat, +m: Cr.Cir.Cells, +fi: U32, +ps: List<&2, U32>, +c1: U32, +c2: U32, +rs: List<&2, U32>, +c: U32) ->
  {D.Ptr(n, m, fi, ps, Con{c2, Con{c1, rs}}, c) == D.Ptr(n, m, fi, ps, Con{c1, Con{c2, rs}}, c) : Nat}:
  Equal.cong(Nat, Nat, x => Nat.add(D.Pc(n, m, ps, fi, c), x), D.RcL(Con{c2, Con{c1, rs}}, c), D.RcL(Con{c1, Con{c2, rs}}, c), rcl.swap(c1, c2, rs, c))

def cnt.swap(k: Nat, +m: Cr.Cir.Cells, +o: U32, +N0: Nat, +fi: U32, +ps: List<&2, U32>, +c1: U32, +c2: U32, +rs: List<&2, U32>,
  h: {D.Cnt(k, m, o, N0, fi, ps, Con{c1, Con{c2, rs}}) == True{} : Bool}) -> {D.Cnt(k, m, o, N0, fi, ps, Con{c2, Con{c1, rs}}) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+(+j):
      +h2 = h
      +R1 = {Con{c1, Con{c2, rs}} : List<&2, U32>}
      +R2 = {Con{c2, Con{c1, rs}} : List<&2, U32>}
      D.and.i(D.CntC(Cr.Cir.Cells.get(m, o), D.Ptr(N0, m, fi, ps, R2, o), ps, o), D.Cnt(j, m, U32.inc(o), N0, fi, ps, R2),
        (%Equal.sym(Nat, D.Ptr(N0, m, fi, ps, R2, o), D.Ptr(N0, m, fi, ps, R1, o), ptr.swap(N0, m, fi, ps, c1, c2, rs, o)) : {D.CntC(Cr.Cir.Cells.get(m, o), _, ps, o) == True{} : Bool};
          D.and.l(D.CntC(Cr.Cir.Cells.get(m, o), D.Ptr(N0, m, fi, ps, R1, o), ps, o), D.Cnt(j, m, U32.inc(o), N0, fi, ps, R1), h2)),
        cnt.swap(j, m, U32.inc(o), N0, fi, ps, c1, c2, rs,
          D.and.r(D.CntC(Cr.Cir.Cells.get(m, o), D.Ptr(N0, m, fi, ps, R1, o), ps, o), D.Cnt(j, m, U32.inc(o), N0, fi, ps, R1), h2)))

def pendok.swap(qs: List<&2, U32>, +ps: List<&2, U32>, +m: Cr.Cir.Cells, +fi: U32, +nx: U32, +c1: U32, +c2: U32, +rs: List<&2, U32>,
  h: D.PendOK(qs, ps, m, fi, nx, Con{c1, Con{c2, rs}})) -> D.PendOK(qs, ps, m, fi, nx, Con{c2, Con{c1, rs}}):
  match qs:
    case Nil{}:
      Unit{}
    case Con{+p, +rest}:
      (ho, r1) = h
      (hs, r2) = r1
      (htg, r3) = r2
      (hp0, r4) = r3
      +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
      (ho, (hs, (htg, ((%Equal.sym(Nat, D.Ptr(n, m, fi, ps, Con{c2, Con{c1, rs}}, p), D.Ptr(n, m, fi, ps, Con{c1, Con{c2, rs}}, p), ptr.swap(n, m, fi, ps, c1, c2, rs, p)) : {_ == 0n : Nat}; hp0),
        pendok.swap(rest, ps, m, fi, nx, c1, c2, rs, r4)))))

def heap.swap(+m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +c1: U32, +c2: U32, +rs: List<&2, U32>, +pend: U32, +ps: List<&2, U32>,
  h: D.Heap(m, nx, fi, im, Con{c1, Con{c2, rs}}, pend, ps)) -> D.Heap(m, nx, fi, im, Con{c2, Con{c1, rs}}, pend, ps):
  (hc, r1) = h
  (hp, r2) = r1
  (hcn, r3) = r2
  +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
  (hc, (pendok.swap(ps, ps, m, fi, nx, c1, c2, rs, hp), (cnt.swap(n, m, fi, n, fi, ps, c1, c2, rs, hcn), r3)))

# HS with the first two roots traded
def hsk.swap(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32,
  +im: U32, +c1: U32, +u1: Bk.Term, +c2: U32, +u2: Bk.Term, +os: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>,
  h: D.HSK(True{}, ds, ks, img, m, nx, fi, im, Con{D.Rt{c1, u1}, Con{D.Rt{c2, u2}, os}}, Nil{}, fs, sp, pend, ps)) ->
  D.HSK(True{}, ds, ks, img, m, nx, fi, im, Con{D.Rt{c2, u2}, Con{D.Rt{c1, u1}, os}}, Nil{}, fs, sp, pend, ps):
  match h:
    case Tuple{Tuple{i1, Tuple{i2, ir}}, Tuple{hb, Tuple{_, Tuple{hfr, Tuple{hp, hio}}}}}:
      ((i2, (i1, ir)), (hb, (Unit{}, (hfr, (heap.swap(m, nx, fi, im, c1, c2, D.Rt.cells(os), pend, ps, hp), hio)))))

# Cov with the first two roots traded
def cov.swap(n: Nat, +m: Cr.Cir.Cells, +c: U32, +r1: D.Rt, +r2: D.Rt, +rs: List<&2, D.Rt>, +xs: List<&2, U32>,
  h: {D.Cov(n, m, c, Con{r1, Con{r2, rs}}, xs) == True{} : Bool}) -> {D.Cov(n, m, c, Con{r2, Con{r1, rs}}, xs) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      +h2 = h
      +N1 = D.Nodes([r1], m, c)
      +N2 = D.Nodes([r2], m, c)
      +X1 = Bool.or(D.Fl(m, c, 1024), Bool.or(D.Nodes(Con{r1, Con{r2, rs}}, m, c), D.Mem(xs, c)))
      +C1 = D.Cov(p, m, U32.inc(c), Con{r1, Con{r2, rs}}, xs)
      D.and.i(Bool.or(D.Fl(m, c, 1024), Bool.or(D.Nodes(Con{r2, Con{r1, rs}}, m, c), D.Mem(xs, c))), D.Cov(p, m, U32.inc(c), Con{r2, Con{r1, rs}}, xs),
        (%nodes.swap1(r1, r2, rs, m, c) : {Bool.or(D.Fl(m, c, 1024), Bool.or(_, D.Mem(xs, c))) == True{} : Bool}; D.and.l(X1, C1, h2)),
        cov.swap(p, m, U32.inc(c), r1, r2, rs, xs, D.and.r(X1, C1, h2)))

# Acc with the first two roots traded (no temporary)
def acc.swap(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32,
  +im: U32, +r1: D.Rt, +r2: D.Rt, +os: List<&2, D.Rt>, +sp: U32, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  h: D.AccK(True{}, ds, ks, img, m, nx, fi, im, Con{r1, Con{r2, os}}, Nil{}, sp, fs, ps, zs)) ->
  D.AccK(True{}, ds, ks, img, m, nx, fi, im, Con{r2, Con{r1, os}}, Nil{}, sp, fs, ps, zs):
  match h:
    case Tuple{hz, Tuple{hh, Tuple{hpz, Tuple{hcov, Tuple{hclo, _}}}}}:
      +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
      +R = List.append(&2, D.Rt, os, List.append(&2, D.Rt, Nil{}, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)))
      (hz, (hh, (hpz, (cov.swap(n, m, fi, r1, r2, R, List.append(&2, U32, D.Fr.cells(fs, m, sp), List.append(&2, U32, Nil{}, ps)), hcov),
        (hclo, {==})))))

# a node of an owned root's term, borrowed
def hsk.borrow(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32,
  +im: U32, +os: List<&2, D.Rt>, +c: U32, +u: Bk.Term, +fs: List<&2, D.AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>,
  hi: D.IsK(True{}, ds, m, im, fi, nx, ks, img, c, u), hn: {D.Nodes(os, m, c) == True{} : Bool},
  h: D.HSK(True{}, ds, ks, img, m, nx, fi, im, os, Nil{}, fs, sp, pend, ps)) ->
  D.HSK(True{}, ds, ks, img, m, nx, fi, im, os, [D.Rt{c, u}], fs, sp, pend, ps):
  match h:
    case Tuple{hos, Tuple{_, Tuple{_, r}}}:
      (hos, ((hi, Unit{}), ((D.or.r(D.Fl(m, c, 1024), D.Nodes(os, m, c), hn), Unit{}), r)))

# a borrowed term dropped
def hsk.drop(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32,
  +im: U32, +os: List<&2, D.Rt>, +b: D.Rt, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>,
  h: D.HSK(True{}, ds, ks, img, m, nx, fi, im, os, Con{b, bs}, fs, sp, pend, ps)) ->
  D.HSK(True{}, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps):
  match b:
    case D.Rt{+c, +u}:
      match h:
        case Tuple{hos, Tuple{Tuple{_, hbs}, Tuple{Tuple{_, hh}, r}}}:
          (hos, (hbs, (hh, r)))
# Acc after the pop
# -----------------
#
# The pop's AccK half, after U11's pop.post (swap_moves.bend): the frame sp
# heads the pend list, its term a becomes a root after the focus'.

def fs.pend.ne(+m: Cr.Cir.Cells, +ps: List<&2, U32>, +z: U32, +o: U32, eb: {U32.is_eq(z, o) == False{} : Bool}) ->
  {D.Fs(m, Con{z, ps}, o) == D.Fs(m, ps, o) : List<&2, U32>}:
  %Equal.sym(Bool, U32.is_eq(z, o), False{}, eb) :
    {A1.FsM(U32.is_lt(D.TgW(D.Fd(0n, m, o)), 19), Bool.or(_, D.Mem(ps, o)), m, o, D.TgW(D.Fd(0n, m, o))) == D.Fs(m, ps, o) : List<&2, U32>}
  {==}

def mem.frc(fs: List<&2, D.AF>, +m: Cr.Cir.Cells, +sx: U32, +fr: U32, +n: Nat, +hn: {Hops(n, m, sx) == True{} : Bool},
  hf: {Hops(List.length(&2, D.AF, fs), m, fr) == True{} : Bool}, hl: N.Le(1n+List.length(&2, D.AF, fs), n)) ->
  {D.Mem(D.Fr.cells(fs, m, fr), sx) == False{} : Bool}:
  match fs:
    case Nil{}:
      {==}
    case Con{_, +rest}:
      +hf2 = hf
      +hl2 = hl
      %Equal.sym(Bool, U32.is_eq(fr, sx), False{}, hops.ne(1n+List.length(&2, D.AF, rest), n, m, fr, sx, hf2, hn, hl2)) :
        {Bool.or(_, D.Mem(D.Fr.cells(rest, m, D.Fd(1n, m, fr)), sx)) == False{} : Bool}
      mem.frc(rest, m, sx, D.Fd(1n, m, fr), n, hn, D.and.r(Bool.not(U32.is_eq(fr, 0)), Hops(List.length(&2, D.AF, rest), m, D.Fd(1n, m, fr)), hf2),
        N.weaken(1n+List.length(&2, D.AF, rest), n, hl2))

def clo.pop.at(bb: Bool, +m: Cr.Cir.Cells, +c: U32, +ps: List<&2, U32>, +z: U32, +eb: {U32.is_eq(c, z) == bb : Bool},
  +hz: {D.Fl(m, z, 1024) == False{} : Bool}, h: {D.Clo.at(m, c, ps, Nil{}, Nil{}) == True{} : Bool}) ->
  {D.Clo.at(m, c, Con{z, ps}, Nil{}, Nil{}) == True{} : Bool}:
  match bb:
    case True{}:
      %Equal.sym(U32, c, z, D.u32.eq(c, z, eb)) :
        {Bool.and(Bool.or(Bool.not(D.Fl(m, _, 1024)), D.All.static(D.Fs(m, Con{z, ps}, _), m)), True{}) == True{} : Bool}
      %Equal.sym(Bool, D.Fl(m, z, 1024), False{}, hz) :
        {Bool.and(Bool.or(Bool.not(_), D.All.static(D.Fs(m, Con{z, ps}, z), m)), True{}) == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(List<&2, U32>, D.Fs(m, Con{z, ps}, c), D.Fs(m, ps, c), fs.pend.ne(m, ps, z, c, D.ne.sym(c, z, eb))) :
        {Bool.and(Bool.or(Bool.not(D.Fl(m, c, 1024)), D.All.static(_, m)), True{}) == True{} : Bool}
      h

def clo.pop(k: Nat, +m: Cr.Cir.Cells, +c: U32, +ps: List<&2, U32>, +z: U32, +hz: {D.Fl(m, z, 1024) == False{} : Bool},
  h: {D.Clo(k, m, c, ps, Nil{}, Nil{}) == True{} : Bool}) -> {D.Clo(k, m, c, Con{z, ps}, Nil{}, Nil{}) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+(+j):
      +h2 = h
      D.and.i(D.Clo.at(m, c, Con{z, ps}, Nil{}, Nil{}), D.Clo(j, m, U32.inc(c), Con{z, ps}, Nil{}, Nil{}),
        clo.pop.at(U32.is_eq(c, z), m, c, ps, z, {==}, hz, D.and.l(D.Clo.at(m, c, ps, Nil{}, Nil{}), D.Clo(j, m, U32.inc(c), ps, Nil{}, Nil{}), h2)),
        clo.pop(j, m, U32.inc(c), ps, z, hz, D.and.r(D.Clo.at(m, c, ps, Nil{}, Nil{}), D.Clo(j, m, U32.inc(c), ps, Nil{}, Nil{}), h2)))

def frb.cells(kind: D.FK, +m: Cr.Cir.Cells, +fr: U32, +b: Bk.Term) ->
  {D.Rt.cells(D.Fr.rts.b(m, fr, kind, b)) == D.Fs.opt(U32.is_eq(D.FK.tag(kind), 38), D.Fd(3n, m, fr), Nil{}) : List<&2, U32>}:
  match kind:
    case D.FK.arg{}:
      {==}
    case D.FK.val{}:
      {==}
    case D.FK.fun{}:
      {==}
    case D.FK.let{}:
      {==}
    case D.FK.tupb{}:
      {==}
    case D.FK.tupa{}:
      {==}
    case D.FK.rwt{}:
      {==}
    case D.FK.minb{}:
      {==}
    case D.FK.mina{}:
      {==}

# the AccK of the pop, with the frame's roots after the focus' (as pop.post)
def acc.pop.u(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32,
  +im: U32, +focus: Bk.Term, +fs: List<&2, D.AF>, +foc: U32, +sp: U32, +pend: U32, +ps: List<&2, U32>, +kind: D.FK, +q: Bk.Quan,
  +k: Bool, +a: Bk.Term, +b: Bk.Term, +zs: List<&2, D.Rt>,
  +frs: D.Frs(ds, m, im, fi, nx, ks, img, ps, sp, Con{D.AF{kind, q, k, a, b}, fs}),
  hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{foc, focus}], Nil{}, sp, Con{D.AF{kind, q, k, a, b}, fs}, ps, zs)) ->
  D.AccK(True{}, ds, ks, img, D.Put1([D.W1{sp, pend}], m), nx, fi, im, Con{D.Rt{foc, focus}, Con{D.Rt{D.Fd(2n, m, sp), a}, D.Fr.rts.b(m, sp, kind, b)}},
    Nil{}, D.Fd(1n, m, sp), fs, Con{sp, ps}, zs):
  match frs:
    case Tuple{+e0, Tuple{_, Tuple{_, Tuple{+es, Tuple{_, Tuple{+etg, Tuple{_, Tuple{_, Tuple{_, Tuple{_, _}}}}}}}}}}:
      (hzr, r1) = hac
      (_, r2) = r1
      (hzc, r3) = r2
      (hcov, r4) = r3
      (hclo, _) = r4
      +ws = {[D.W1{sp, pend}] : List<&2, D.W1>}
      +M1 = D.Put1(ws, m)
      +N = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
      +f1 = D.Fd(1n, m, sp)
      +n = D.Fd(2n, m, sp)
      +Frb = D.Fr.rts.b(m, sp, kind, b)
      +OS = {Con{D.Rt{foc, focus}, Con{D.Rt{n, a}, Frb}} : List<&2, D.Rt>}
      +FR = D.Fr.rts(fs, m, f1)
      +FC = D.Fr.cells(fs, m, f1)
      +L = List.length(&2, D.AF, fs)
      +T = D.FK.tag(kind)
      +etg2 = etg
      +hnt = {(%Equal.sym(U32, D.Tg(m, sp), T, etg2) : {U32.is_lt(_, 19) == False{} : Bool}; D.fk.lt(kind)) : {U32.is_lt(D.Tg(m, sp), 19) == False{} : Bool}}
      +hsp = frs.hops(Con{D.AF{kind, q, k, a, b}, fs}, ds, m, im, fi, nx, ks, img, ps, sp, frs)
      +hf1 = D.and.r(Bool.not(U32.is_eq(sp, 0)), Hops(L, m, f1), hsp)
      +e0m = D.put1.f0(ws, m, sp)
      +hst1 = {(%Equal.sym(U32, D.Fd(0n, M1, sp), D.Fd(0n, m, sp), e0m) : {U32.is_ne(U32.and(_, 1024), 0) == False{} : Bool}; es) :
        {D.Fl(M1, sp, 1024) == False{} : Bool}}
      +PT1 = D.Pend.terms(ps, M1)
      +ept = {(%Equal.sym(U32, D.Fd(0n, M1, sp), D.Fd(0n, m, sp), e0m) :
            {Bool.pick(List<&2, U32>, U32.is_lt(U32.and(_, 63), 19), Con{sp, PT1}, PT1) == D.Pend.terms(ps, m) : List<&2, U32>};
          %Equal.sym(Bool, U32.is_lt(D.Tg(m, sp), 19), False{}, hnt) :
            {Bool.pick(List<&2, U32>, _, Con{sp, PT1}, PT1) == D.Pend.terms(ps, m) : List<&2, U32>};
          A1.pend.terms.put1(ps, ws, m)) : {D.Pend.terms(Con{sp, ps}, M1) == D.Pend.terms(ps, m) : List<&2, U32>}}
      +RSo = {Con{D.Rt{foc, focus}, Con{D.Rt{n, a}, List.append(&2, D.Rt, List.append(&2, D.Rt, Frb, FR), zs)}} : List<&2, D.Rt>}
      +RS2 = {Con{D.Rt{foc, focus}, Con{D.Rt{n, a}, List.append(&2, D.Rt, Frb, List.append(&2, D.Rt, FR, zs))}} : List<&2, D.Rt>}
      +XSo = {Con{sp, List.append(&2, U32, FC, ps)} : List<&2, U32>}
      +c1 = Equal.trans(Bool, D.Cov(N, M1, fi, RSo, XSo), D.Cov(N, m, fi, RSo, XSo), True{}, A1.cov.put1(N, ws, m, fi, RSo, XSo), hcov)
      +c2 = {(%A1.app.assoc(Frb, FR, zs) : {D.Cov(N, M1, fi, Con{D.Rt{foc, focus}, Con{D.Rt{n, a}, _}}, XSo) == True{} : Bool}; c1) :
        {D.Cov(N, M1, fi, RS2, XSo) == True{} : Bool}}
      +c3 = A1.cov.mv(D.Cov(N, M1, fi, RS2, XSo), D.Cov(N, M1, fi, RS2, List.append(&2, U32, FC, Con{sp, ps})),
        A1.cov.perm.x(N, M1, fi, RS2, Nil{}, [sp], FC, ps), c2)
      +frp = A1.fr.put1(fs, ws, m, f1, A1.outs.one(FC, sp, mem.frc(fs, m, sp, f1, 1n+L, hsp, hf1, N.le_refl(1n+L))))
      +frc = D.Ex.fst({D.Fr.cells(fs, M1, f1) == FC : List<&2, U32>}, _ => {D.Fr.rts(fs, M1, f1) == FR : List<&2, D.Rt>}, frp)
      +frr = D.Ex.snd({D.Fr.cells(fs, M1, f1) == FC : List<&2, U32>}, _ => {D.Fr.rts(fs, M1, f1) == FR : List<&2, D.Rt>}, frp)
      +c4 = {(%Equal.sym(List<&2, D.Rt>, D.Fr.rts(fs, M1, f1), FR, frr) :
            {D.Cov(N, M1, fi, Con{D.Rt{foc, focus}, Con{D.Rt{n, a}, List.append(&2, D.Rt, Frb, List.append(&2, D.Rt, _, zs))}},
              List.append(&2, U32, D.Fr.cells(fs, M1, f1), Con{sp, ps})) == True{} : Bool};
          %Equal.sym(List<&2, U32>, D.Fr.cells(fs, M1, f1), FC, frc) :
            {D.Cov(N, M1, fi, RS2, List.append(&2, U32, _, Con{sp, ps})) == True{} : Bool};
          c3) :
        {D.Cov(N, M1, fi, List.append(&2, D.Rt, OS, List.append(&2, D.Rt, Nil{}, List.append(&2, D.Rt, D.Fr.rts(fs, M1, f1), zs))),
          List.append(&2, U32, D.Fr.cells(fs, M1, f1), List.append(&2, U32, Nil{}, Con{sp, ps}))) == True{} : Bool}}
      +clo1 = clo.pop(N, M1, fi, ps, sp, hst1,
        Equal.trans(Bool, D.Clo(N, M1, fi, ps, Nil{}, Nil{}), D.Clo(N, m, fi, ps, Nil{}, Nil{}), True{}, A1.clo.put1(N, ws, m, fi, ps, Nil{}, Nil{}), hclo))
      (A1.rts.put1(True{}, zs, ds, ws, m, im, fi, nx, ks, img, hzr), (Unit{},
        (Equal.trans(List<&2, U32>, D.Rt.cells(zs), D.Pend.terms(ps, m), D.Pend.terms(Con{sp, ps}, M1), hzc,
          Equal.sym(List<&2, U32>, D.Pend.terms(Con{sp, ps}, M1), D.Pend.terms(ps, m), ept)),
        (c4, (clo1, {==})))))

# a frame's b is no root, but for Rwt
def frb.nil(kind: D.FK, +m: Cr.Cir.Cells, +fr: U32, +b: Bk.Term, h38: {U32.is_eq(D.FK.tag(kind), 38) == False{} : Bool}) ->
  {D.Fr.rts.b(m, fr, kind, b) == Nil{} : List<&2, D.Rt>}:
  match kind:
    case D.FK.rwt{}:
      D.bool.ft({[D.Rt{D.Fd(3n, m, fr), b}] == Nil{} : List<&2, D.Rt>}, Equal.sym(Bool, True{}, False{}, h38))
    case D.FK.arg{}:
      {==}
    case D.FK.val{}:
      {==}
    case D.FK.fun{}:
      {==}
    case D.FK.let{}:
      {==}
    case D.FK.tupb{}:
      {==}
    case D.FK.tupa{}:
      {==}
    case D.FK.minb{}:
      {==}
    case D.FK.mina{}:
      {==}

# the AccK of the pop, in the roots' order of hsk.pop: the frame's term, then the focus
def acc.pop(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32,
  +im: U32, +focus: Bk.Term, +fs: List<&2, D.AF>, +foc: U32, +sp: U32, +pend: U32, +ps: List<&2, U32>, +kind: D.FK, +q: Bk.Quan,
  +k: Bool, +a: Bk.Term, +b: Bk.Term, +zs: List<&2, D.Rt>, +h38: {U32.is_eq(D.FK.tag(kind), 38) == False{} : Bool},
  +frs: D.Frs(ds, m, im, fi, nx, ks, img, ps, sp, Con{D.AF{kind, q, k, a, b}, fs}),
  hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{foc, focus}], Nil{}, sp, Con{D.AF{kind, q, k, a, b}, fs}, ps, zs)) ->
  D.AccK(True{}, ds, ks, img, M1(m, sp, pend), nx, fi, im, [D.Rt{D.Fd(2n, m, sp), a}, D.Rt{foc, focus}], Nil{}, D.Fd(1n, m, sp), fs, Con{sp, ps}, zs):
  acc.swap(ds, ks, img, M1(m, sp, pend), nx, fi, im, D.Rt{foc, focus}, D.Rt{D.Fd(2n, m, sp), a}, Nil{}, D.Fd(1n, m, sp), fs, Con{sp, ps}, zs,
    (%frb.nil(kind, m, sp, b, h38) :
       D.AccK(True{}, ds, ks, img, M1(m, sp, pend), nx, fi, im, Con{D.Rt{foc, focus}, Con{D.Rt{D.Fd(2n, m, sp), a}, _}}, Nil{}, D.Fd(1n, m, sp), fs, Con{sp, ps}, zs);
     acc.pop.u(ds, ks, img, m, nx, fi, im, focus, fs, foc, sp, pend, ps, kind, q, k, a, b, zs, frs, hac)))

# Names
# -----
#
# A label and a λ-match name the same name exactly when the image gives them
# the same number (Nm): M.redex's test of the case.

def byte.refl(+x: Word(8n)) -> {Sd.Byte.is_eq(x, x) == True{} : Bool}:
  Equal.trans(Bool, Cmp.is_eq(Word.cmp(8n, x, x)), D.Weq(8n, x, x), True{}, D.weq.cmp(8n, x, x), D.weq.refl(8n, x))

def byte.eq(+x: Word(8n), +y: Word(8n), h: {Sd.Byte.is_eq(x, y) == True{} : Bool}) -> {x == y : Word(8n)}:
  D.weq.eq(8n, x, y, Equal.trans(Bool, D.Weq(8n, x, y), Cmp.is_eq(Word.cmp(8n, x, y)), True{},
    Equal.sym(Bool, Cmp.is_eq(Word.cmp(8n, x, y)), D.Weq(8n, x, y), D.weq.cmp(8n, x, y)), h))

def name.refl(a: List<&2, Word(8n)>) -> {Sd.Name.is_eq(a, a) == True{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +xs}:
      D.and.i(Sd.Byte.is_eq(x, x), Sd.Name.is_eq(xs, xs), byte.refl(x), name.refl(xs))

def name.eq(a: List<&2, Word(8n)>, b: List<&2, Word(8n)>, h: {Sd.Name.is_eq(a, b) == True{} : Bool}) -> {a == b : List<&2, Word(8n)>}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{+y, +ys}:
      D.bool.ft({Nil{} == Con{y, ys} : List<&2, Word(8n)>}, h)
    case Con{+x, +xs} Nil{}:
      D.bool.ft({Con{x, xs} == Nil{} : List<&2, Word(8n)>}, h)
    case Con{+x, +xs} Con{+y, +ys}:
      +h2 = h
      +ex = byte.eq(x, y, D.and.l(Sd.Byte.is_eq(x, y), Sd.Name.is_eq(xs, ys), h2))
      +es = name.eq(xs, ys, D.and.r(Sd.Byte.is_eq(x, y), Sd.Name.is_eq(xs, ys), h2))
      %ex : {Con{x, xs} == Con{_, ys} : List<&2, Word(8n)>}
      %es : {Con{x, xs} == Con{x, _} : List<&2, Word(8n)>}
      {==}

def some.inj(-a: List<&2, Word(8n)>, -b: List<&2, Word(8n)>, h: {Some{a} == Some{b} : Maybe<&2, List<&2, Word(8n)>>}) -> {a == b : List<&2, Word(8n)>}:
  Equal.cong(Maybe<&2, List<&2, Word(8n)>>, List<&2, Word(8n)>, x => Maybe.default(&2, List<&2, Word(8n)>, x, a), Some{a}, Some{b}, h)

# the numbers of two names, equal: the names are
def nm.same(+ks: List<&2, List<&2, Word(8n)>>, +y: Cr.Cir.Cell, +x: Cr.Cir.Cell, +l: List<&2, Word(8n)>, +j: List<&2, Word(8n)>,
  hy: D.Nm(ks, y, l), hx: D.Nm(ks, x, j), e: {Cr.Cir.Cell.get(2n, y) == Cr.Cir.Cell.get(2n, x) : U32}) -> {Sd.Name.is_eq(l, j) == True{} : Bool}:
  match hy hx:
    case Tuple{ny, _} Tuple{nx, _}:
      +ny2 = Equal.trans(Maybe<&2, List<&2, Word(8n)>>, T.tm.name(ks, Cr.Cir.Cell.get(2n, x)), T.tm.name(ks, Cr.Cir.Cell.get(2n, y)), Some{l},
        Equal.cong(U32, Maybe<&2, List<&2, Word(8n)>>, i => T.tm.name(ks, i), Cr.Cir.Cell.get(2n, x), Cr.Cir.Cell.get(2n, y),
          Equal.sym(U32, Cr.Cir.Cell.get(2n, y), Cr.Cir.Cell.get(2n, x), e)), ny)
      +elj = some.inj(l, j, Equal.trans(Maybe<&2, List<&2, Word(8n)>>, Some{l}, T.tm.name(ks, Cr.Cir.Cell.get(2n, x)), Some{j},
        Equal.sym(Maybe<&2, List<&2, Word(8n)>>, T.tm.name(ks, Cr.Cir.Cell.get(2n, x)), Some{l}, ny2), nx))
      %elj : {Sd.Name.is_eq(l, _) == True{} : Bool}
      name.refl(l)

def nm.diff.b(c: Bool, +ks: List<&2, List<&2, Word(8n)>>, +y: Cr.Cir.Cell, +x: Cr.Cir.Cell, +l: List<&2, Word(8n)>, +j: List<&2, Word(8n)>,
  ec: {Sd.Name.is_eq(l, j) == c : Bool}, hy: D.Nm(ks, y, l), hx: D.Nm(ks, x, j),
  e: {U32.is_eq(Cr.Cir.Cell.get(2n, y), Cr.Cir.Cell.get(2n, x)) == False{} : Bool}) -> {Sd.Name.is_eq(l, j) == False{} : Bool}:
  match c:
    case False{}:
      ec
    case True{}:
      match hy hx:
        case Tuple{_, iy} Tuple{_, ix}:
          +elj = name.eq(l, j, ec)
          +exy = {(%elj : {Mc.Img.id(ks, l, 0) == Mc.Img.id(ks, _, 0) : U32}; {==}) : {Mc.Img.id(ks, l, 0) == Mc.Img.id(ks, j, 0) : U32}}
          +eyx = Equal.trans(U32, Cr.Cir.Cell.get(2n, y), Mc.Img.id(ks, j, 0), Cr.Cir.Cell.get(2n, x),
            Equal.trans(U32, Cr.Cir.Cell.get(2n, y), Mc.Img.id(ks, l, 0), Mc.Img.id(ks, j, 0), iy, exy),
            Equal.sym(U32, Cr.Cir.Cell.get(2n, x), Mc.Img.id(ks, j, 0), ix))
          Empty.absurd({Sd.Name.is_eq(l, j) == False{} : Bool}, D.u32.ne(Cr.Cir.Cell.get(2n, y), Cr.Cir.Cell.get(2n, x), e, eyx))

# the numbers of two names, not equal: nor are the names
def nm.diff(+ks: List<&2, List<&2, Word(8n)>>, +y: Cr.Cir.Cell, +x: Cr.Cir.Cell, +l: List<&2, Word(8n)>, +j: List<&2, Word(8n)>,
  hy: D.Nm(ks, y, l), hx: D.Nm(ks, x, j), e: {U32.is_eq(Cr.Cir.Cell.get(2n, y), Cr.Cir.Cell.get(2n, x)) == False{} : Bool}) ->
  {Sd.Name.is_eq(l, j) == False{} : Bool}:
  nm.diff.b(Sd.Name.is_eq(l, j), ks, y, x, l, j, {==}, hy, hx, e)

# Eval of the λ-matches' redexes
# -------------------------------

def is.lab(t: Bk.Term) -> Bool:
  match t:
    case Bk.Term.Lab{_}:
      True{}
    case _:
      False{}

def is.tup(t: Bk.Term) -> Bool:
  match t:
    case Bk.Term.Tup{_, _, _}:
      True{}
    case _:
      False{}

def and.true(a: Bool) -> {Bool.and(a, True{}) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# M.redex's test of a λ-match's argument: the quantity is live, and the
# argument's tag is the one of a label (13) or of a pair (10)
def and.b2u(p: Bool, r: Bool) -> {Wa.Wasm.op(Wa.Wasm.Op.and{}, Bool.to_u32(p), Bool.to_u32(r)) == Bool.to_u32(Bool.and(p, r)) : U32}:
  match p r:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def q.live(q: Bk.Quan) -> {Wa.Wasm.op(Wa.Wasm.Op.ne{}, Mc.Img.quan(q), 0) == Bool.to_u32(El.Quan.live(q)) : U32}:
  match q:
    case Bk.Quan.Q0{}:
      {==}
    case Bk.Quan.Q1{}:
      {==}
    case Bk.Quan.Q2{}:
      {==}

def tag.lab(a: Bk.Term) -> {Wa.Wasm.op(Wa.Wasm.Op.eq{}, D.A.tag(a), 13) == Bool.to_u32(is.lab(a)) : U32}:
  match a:
    case Bk.Term.Var{+i}:
      {==}
    case Bk.Term.Ref{+k}:
      {==}
    case Bk.Term.Ann{+x, +y}:
      {==}
    case Bk.Term.Let{+q2, +v, +g}:
      {==}
    case Bk.Term.Typ{+x}:
      {==}
    case Bk.Term.Min{+x, +y}:
      {==}
    case Bk.Term.All{+q2, +x, +y}:
      {==}
    case Bk.Term.Lam{+q2, +g}:
      {==}
    case Bk.Term.App{+q2, +g, +x}:
      {==}
    case Bk.Term.Sig{+q2, +x, +y}:
      {==}
    case Bk.Term.Tup{+r, +x, +y}:
      {==}
    case Bk.Term.Prj{+g}:
      {==}
    case Bk.Term.Enu{+e}:
      {==}
    case Bk.Term.Lab{+l}:
      {==}
    case Bk.Term.Mat{+k, +g, +n2}:
      {==}
    case Bk.Term.Efq{}:
      {==}
    case Bk.Term.Eql{+x, +y, +z}:
      {==}
    case Bk.Term.Rfl{}:
      {==}
    case Bk.Term.Rwt{+x, +y, +z}:
      {==}

def tag.tup(a: Bk.Term) -> {Wa.Wasm.op(Wa.Wasm.Op.eq{}, D.A.tag(a), 10) == Bool.to_u32(is.tup(a)) : U32}:
  match a:
    case Bk.Term.Var{+i}:
      {==}
    case Bk.Term.Ref{+k}:
      {==}
    case Bk.Term.Ann{+x, +y}:
      {==}
    case Bk.Term.Let{+q2, +v, +g}:
      {==}
    case Bk.Term.Typ{+x}:
      {==}
    case Bk.Term.Min{+x, +y}:
      {==}
    case Bk.Term.All{+q2, +x, +y}:
      {==}
    case Bk.Term.Lam{+q2, +g}:
      {==}
    case Bk.Term.App{+q2, +g, +x}:
      {==}
    case Bk.Term.Sig{+q2, +x, +y}:
      {==}
    case Bk.Term.Tup{+r, +x, +y}:
      {==}
    case Bk.Term.Prj{+g}:
      {==}
    case Bk.Term.Enu{+e}:
      {==}
    case Bk.Term.Lab{+l}:
      {==}
    case Bk.Term.Mat{+k, +g, +n2}:
      {==}
    case Bk.Term.Efq{}:
      {==}
    case Bk.Term.Eql{+x, +y, +z}:
      {==}
    case Bk.Term.Rfl{}:
      {==}
    case Bk.Term.Rwt{+x, +y, +z}:
      {==}

# no redex of a λ-match of labels, unless its argument is a label and its
# quantity live
def mat.redex.none(+ds: List<&2, Bk.Def>, +q: Bk.Quan, +j: List<&2, Word(8n)>, +h: Bk.Term, +n: Bk.Term, a: Bk.Term,
  hg: {Bool.and(El.Quan.live(q), is.lab(a)) == False{} : Bool}) -> {El.Eval.redex(ds, q, Bk.Term.Mat{j, h, n}, a) == None{} : Maybe<Bk.Term>}:
  match a:
    case Bk.Term.Var{+i}:
      {==}
    case Bk.Term.Ref{+k}:
      {==}
    case Bk.Term.Ann{+x, +y}:
      {==}
    case Bk.Term.Let{+q2, +v, +g}:
      {==}
    case Bk.Term.Typ{+x}:
      {==}
    case Bk.Term.Min{+x, +y}:
      {==}
    case Bk.Term.All{+q2, +x, +y}:
      {==}
    case Bk.Term.Lam{+q2, +g}:
      {==}
    case Bk.Term.App{+q2, +g, +x}:
      {==}
    case Bk.Term.Sig{+q2, +x, +y}:
      {==}
    case Bk.Term.Tup{+r, +x, +y}:
      {==}
    case Bk.Term.Prj{+g}:
      {==}
    case Bk.Term.Enu{+e}:
      {==}
    case Bk.Term.Lab{+l}:
      %Equal.sym(Bool, El.Quan.live(q), False{}, Equal.trans(Bool, El.Quan.live(q), Bool.and(El.Quan.live(q), True{}), False{},
        Equal.sym(Bool, Bool.and(El.Quan.live(q), True{}), El.Quan.live(q), and.true(El.Quan.live(q))), hg)) :
        {El.Eval.redex.if(_, El.Eval.redex.pick(Sd.Name.is_eq(l, j), h, Bk.Term.App{q, n, Bk.Term.Lab{l}})) == None{} : Maybe<Bk.Term>}
      {==}
    case Bk.Term.Mat{+k, +g, +n2}:
      {==}
    case Bk.Term.Efq{}:
      {==}
    case Bk.Term.Eql{+x, +y, +z}:
      {==}
    case Bk.Term.Rfl{}:
      {==}
    case Bk.Term.Rwt{+x, +y, +z}:
      {==}

# no redex of a λ-match of pairs, unless its argument is a pair and its
# quantity live
def prj.redex.none(+ds: List<&2, Bk.Def>, +q: Bk.Quan, +h: Bk.Term, a: Bk.Term,
  hg: {Bool.and(El.Quan.live(q), is.tup(a)) == False{} : Bool}) -> {El.Eval.redex(ds, q, Bk.Term.Prj{h}, a) == None{} : Maybe<Bk.Term>}:
  match a:
    case Bk.Term.Var{+i}:
      {==}
    case Bk.Term.Ref{+k}:
      {==}
    case Bk.Term.Ann{+x, +y}:
      {==}
    case Bk.Term.Let{+q2, +v, +g}:
      {==}
    case Bk.Term.Typ{+x}:
      {==}
    case Bk.Term.Min{+x, +y}:
      {==}
    case Bk.Term.All{+q2, +x, +y}:
      {==}
    case Bk.Term.Lam{+q2, +g}:
      {==}
    case Bk.Term.App{+q2, +g, +x}:
      {==}
    case Bk.Term.Sig{+q2, +x, +y}:
      {==}
    case Bk.Term.Tup{+r, +x, +y}:
      %Equal.sym(Bool, El.Quan.live(q), False{}, Equal.trans(Bool, El.Quan.live(q), Bool.and(El.Quan.live(q), True{}), False{},
        Equal.sym(Bool, Bool.and(El.Quan.live(q), True{}), El.Quan.live(q), and.true(El.Quan.live(q))), hg)) :
        {El.Eval.redex.if(_, Bk.Term.App{q, Bk.Term.App{El.Quan.fld(r, q), h, x}, y}) == None{} : Maybe<Bk.Term>}
      {==}
    case Bk.Term.Prj{+g}:
      {==}
    case Bk.Term.Enu{+e}:
      {==}
    case Bk.Term.Lab{+l}:
      {==}
    case Bk.Term.Mat{+k, +g, +n2}:
      {==}
    case Bk.Term.Efq{}:
      {==}
    case Bk.Term.Eql{+x, +y, +z}:
      {==}
    case Bk.Term.Rfl{}:
      {==}
    case Bk.Term.Rwt{+x, +y, +z}:
      {==}


# the redexes' steps: a λ-match of labels on its label, a hit or a miss
def mat.step.hit(+ds: List<&2, Bk.Def>, +q: Bk.Quan, +j: List<&2, Word(8n)>, +h: Bk.Term, +n: Bk.Term, +l: List<&2, Word(8n)>,
  hlv: {El.Quan.live(q) == True{} : Bool}, he: {Sd.Name.is_eq(l, j) == True{} : Bool}) ->
  {El.Eval.step(ds, Bk.Term.App{q, Bk.Term.Mat{j, h, n}, Bk.Term.Lab{l}}) == Some{h} : Maybe<Bk.Term>}:
  +M = {Bk.Term.Mat{j, h, n} : Bk.Term}
  +L = {Bk.Term.Lab{l} : Bk.Term}
  %Equal.sym(Bool, El.Quan.live(q), True{}, hlv) :
    {El.Eval.step.app(q, M, L, None{}, True{}, _, None{}, True{}, El.Eval.redex.if(_, El.Eval.redex.pick(Sd.Name.is_eq(l, j), h, Bk.Term.App{q, n, L}))) == Some{h} : Maybe<Bk.Term>}
  %Equal.sym(Bool, Sd.Name.is_eq(l, j), True{}, he) :
    {El.Eval.step.app(q, M, L, None{}, True{}, True{}, None{}, True{}, El.Eval.redex.if(True{}, El.Eval.redex.pick(_, h, Bk.Term.App{q, n, L}))) == Some{h} : Maybe<Bk.Term>}
  {==}

def mat.step.miss(+ds: List<&2, Bk.Def>, +q: Bk.Quan, +j: List<&2, Word(8n)>, +h: Bk.Term, +n: Bk.Term, +l: List<&2, Word(8n)>,
  hlv: {El.Quan.live(q) == True{} : Bool}, he: {Sd.Name.is_eq(l, j) == False{} : Bool}) ->
  {El.Eval.step(ds, Bk.Term.App{q, Bk.Term.Mat{j, h, n}, Bk.Term.Lab{l}}) == Some{Bk.Term.App{q, n, Bk.Term.Lab{l}}} : Maybe<Bk.Term>}:
  +M = {Bk.Term.Mat{j, h, n} : Bk.Term}
  +L = {Bk.Term.Lab{l} : Bk.Term}
  %Equal.sym(Bool, El.Quan.live(q), True{}, hlv) :
    {El.Eval.step.app(q, M, L, None{}, True{}, _, None{}, True{}, El.Eval.redex.if(_, El.Eval.redex.pick(Sd.Name.is_eq(l, j), h, Bk.Term.App{q, n, L}))) == Some{Bk.Term.App{q, n, L}} : Maybe<Bk.Term>}
  %Equal.sym(Bool, Sd.Name.is_eq(l, j), False{}, he) :
    {El.Eval.step.app(q, M, L, None{}, True{}, True{}, None{}, True{}, El.Eval.redex.if(True{}, El.Eval.redex.pick(_, h, Bk.Term.App{q, n, L}))) == Some{Bk.Term.App{q, n, L}} : Maybe<Bk.Term>}
  {==}

# a λ-match of pairs on a pair that is a value: its case on the fields
def prj.step(+ds: List<&2, Bk.Def>, +q: Bk.Quan, +h: Bk.Term, +r: Bk.Quan, +a: Bk.Term, +b: Bk.Term,
  hlv: {El.Quan.live(q) == True{} : Bool}, +hv: {El.Eval.vals(ds, Bk.Term.Tup{r, a, b}, False{}) == True{} : Bool}) ->
  {El.Eval.step(ds, Bk.Term.App{q, Bk.Term.Prj{h}, Bk.Term.Tup{r, a, b}}) == Some{Bk.Term.App{q, Bk.Term.App{El.Quan.fld(r, q), h, a}, b}} : Maybe<Bk.Term>}:
  +P = {Bk.Term.Prj{h} : Bk.Term}
  +T0 = {Bk.Term.Tup{r, a, b} : Bk.Term}
  %Equal.sym(Bool, El.Quan.live(q), True{}, hlv) :
    {El.Eval.step.app(q, P, T0, None{}, True{}, _, El.Eval.step(ds, T0), El.Eval.vals(ds, T0, False{}),
      El.Eval.redex.if(_, Bk.Term.App{q, Bk.Term.App{El.Quan.fld(r, q), h, a}, b})) == Some{Bk.Term.App{q, Bk.Term.App{El.Quan.fld(r, q), h, a}, b}} : Maybe<Bk.Term>}
  %Equal.sym(Maybe<Bk.Term>, El.Eval.step(ds, T0), None{}, K.ev.stops(ds, T0, hv)) :
    {El.Eval.step.app(q, P, T0, None{}, True{}, True{}, _, El.Eval.vals(ds, T0, False{}),
      El.Eval.redex.if(True{}, Bk.Term.App{q, Bk.Term.App{El.Quan.fld(r, q), h, a}, b})) == Some{Bk.Term.App{q, Bk.Term.App{El.Quan.fld(r, q), h, a}, b}} : Maybe<Bk.Term>}
  %Equal.sym(Bool, El.Eval.vals(ds, T0, False{}), True{}, hv) :
    {El.Eval.step.app(q, P, T0, None{}, True{}, True{}, None{}, _,
      El.Eval.redex.if(True{}, Bk.Term.App{q, Bk.Term.App{El.Quan.fld(r, q), h, a}, b})) == Some{Bk.Term.App{q, Bk.Term.App{El.Quan.fld(r, q), h, a}, b}} : Maybe<Bk.Term>}
  {==}

# a λ-match on an argument with no redex (as M.redex's test says), the
# argument a value when the quantity is live: no step, and no value
def mat.stuck(+ds: List<&2, Bk.Def>, q: Bk.Quan, +j: List<&2, Word(8n)>, +h: Bk.Term, +n: Bk.Term, +a: Bk.Term,
  hg: {Bool.and(El.Quan.live(q), is.lab(a)) == False{} : Bool}, +hva: {Bool.or(Bool.not(El.Quan.live(q)), El.Eval.vals(ds, a, False{})) == True{} : Bool}) ->
  D.P2({El.Eval.step(ds, Bk.Term.App{q, Bk.Term.Mat{j, h, n}, a}) == None{} : Maybe<Bk.Term>},
    {El.Eval.vals(ds, Bk.Term.App{q, Bk.Term.Mat{j, h, n}, a}, False{}) == False{} : Bool}):
  match q:
    case Bk.Quan.Q0{}:
      (mat.redex.none(ds, Bk.Quan.Q0{}, j, h, n, a, hg), {==})
    case Bk.Quan.Q1{}:
      +M = {Bk.Term.Mat{j, h, n} : Bk.Term}
      ((%Equal.sym(Maybe<Bk.Term>, El.Eval.step(ds, a), None{}, K.ev.stops(ds, a, hva)) :
          {El.Eval.step.app(Bk.Quan.Q1{}, M, a, None{}, True{}, True{}, _, El.Eval.vals(ds, a, False{}), El.Eval.redex(ds, Bk.Quan.Q1{}, M, a)) == None{} : Maybe<Bk.Term>};
        %Equal.sym(Bool, El.Eval.vals(ds, a, False{}), True{}, hva) :
          {El.Eval.step.app(Bk.Quan.Q1{}, M, a, None{}, True{}, True{}, None{}, _, El.Eval.redex(ds, Bk.Quan.Q1{}, M, a)) == None{} : Maybe<Bk.Term>};
        mat.redex.none(ds, Bk.Quan.Q1{}, j, h, n, a, hg)), {==})
    case Bk.Quan.Q2{}:
      +M = {Bk.Term.Mat{j, h, n} : Bk.Term}
      ((%Equal.sym(Maybe<Bk.Term>, El.Eval.step(ds, a), None{}, K.ev.stops(ds, a, hva)) :
          {El.Eval.step.app(Bk.Quan.Q2{}, M, a, None{}, True{}, True{}, _, El.Eval.vals(ds, a, False{}), El.Eval.redex(ds, Bk.Quan.Q2{}, M, a)) == None{} : Maybe<Bk.Term>};
        %Equal.sym(Bool, El.Eval.vals(ds, a, False{}), True{}, hva) :
          {El.Eval.step.app(Bk.Quan.Q2{}, M, a, None{}, True{}, True{}, None{}, _, El.Eval.redex(ds, Bk.Quan.Q2{}, M, a)) == None{} : Maybe<Bk.Term>};
        mat.redex.none(ds, Bk.Quan.Q2{}, j, h, n, a, hg)), {==})

def prj.stuck(+ds: List<&2, Bk.Def>, q: Bk.Quan, +h: Bk.Term, +a: Bk.Term,
  hg: {Bool.and(El.Quan.live(q), is.tup(a)) == False{} : Bool}, +hva: {Bool.or(Bool.not(El.Quan.live(q)), El.Eval.vals(ds, a, False{})) == True{} : Bool}) ->
  D.P2({El.Eval.step(ds, Bk.Term.App{q, Bk.Term.Prj{h}, a}) == None{} : Maybe<Bk.Term>},
    {El.Eval.vals(ds, Bk.Term.App{q, Bk.Term.Prj{h}, a}, False{}) == False{} : Bool}):
  match q:
    case Bk.Quan.Q0{}:
      (prj.redex.none(ds, Bk.Quan.Q0{}, h, a, hg), {==})
    case Bk.Quan.Q1{}:
      +P = {Bk.Term.Prj{h} : Bk.Term}
      ((%Equal.sym(Maybe<Bk.Term>, El.Eval.step(ds, a), None{}, K.ev.stops(ds, a, hva)) :
          {El.Eval.step.app(Bk.Quan.Q1{}, P, a, None{}, True{}, True{}, _, El.Eval.vals(ds, a, False{}), El.Eval.redex(ds, Bk.Quan.Q1{}, P, a)) == None{} : Maybe<Bk.Term>};
        %Equal.sym(Bool, El.Eval.vals(ds, a, False{}), True{}, hva) :
          {El.Eval.step.app(Bk.Quan.Q1{}, P, a, None{}, True{}, True{}, None{}, _, El.Eval.redex(ds, Bk.Quan.Q1{}, P, a)) == None{} : Maybe<Bk.Term>};
        prj.redex.none(ds, Bk.Quan.Q1{}, h, a, hg)), {==})
    case Bk.Quan.Q2{}:
      +P = {Bk.Term.Prj{h} : Bk.Term}
      ((%Equal.sym(Maybe<Bk.Term>, El.Eval.step(ds, a), None{}, K.ev.stops(ds, a, hva)) :
          {El.Eval.step.app(Bk.Quan.Q2{}, P, a, None{}, True{}, True{}, _, El.Eval.vals(ds, a, False{}), El.Eval.redex(ds, Bk.Quan.Q2{}, P, a)) == None{} : Maybe<Bk.Term>};
        %Equal.sym(Bool, El.Eval.vals(ds, a, False{}), True{}, hva) :
          {El.Eval.step.app(Bk.Quan.Q2{}, P, a, None{}, True{}, True{}, None{}, _, El.Eval.redex(ds, Bk.Quan.Q2{}, P, a)) == None{} : Maybe<Bk.Term>};
        prj.redex.none(ds, Bk.Quan.Q2{}, h, a, hg)), {==})

# What a term's cell says
# -----------------------

def isk.cell(+ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +c: U32, +t: Bk.Term, h: D.Is(ds, m, im, fi, nx, ks, img, c, t)) -> {Cr.Cir.is_cell(c, im, fi, nx) == True{} : Bool}:
  p2.fst({Cr.Cir.is_cell(c, im, fi, nx) == True{} : Bool}, D.P2({Bool.or(D.Own(fi, nx, c), D.FlW(D.Fd(0n, m, c), 1024)) == True{} : Bool},
    D.P2({D.TgW(D.Fd(0n, m, c)) == D.A.tag(t) : U32},
    D.P2({Bool.or(Bool.not(D.FlW(D.Fd(0n, m, c), 256)), El.Eval.vals(ds, t, False{})) == True{} : Bool},
    D.P2(D.DataK(True{}, D.Fd(0n, m, c), t),
      {Bool.or(U32.is_eq(D.FvW(D.Fd(0n, m, c)), 524287), D.Term.below(t, U32.to_nat(D.FvW(D.Fd(0n, m, c))))) == True{} : Bool})))),
    D.is.nd(ds, m, im, fi, nx, ks, img, c, t, h))

def nd.tag(-ds: List<&2, Bk.Def>, -im: U32, -fi: U32, -nx: U32, -c: U32, -x: Cr.Cir.Cell, -t: Bk.Term,
  nd: D.Nd(ds, im, fi, nx, c, x, t, D.A.tag(t))) -> {D.TgW(Cr.Cir.Cell.get(0n, x)) == D.A.tag(t) : U32}:
  match nd:
    case Tuple{_, Tuple{_, Tuple{e, _}}}:
      e

def isk.tag(+ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +c: U32, +t: Bk.Term, h: D.Is(ds, m, im, fi, nx, ks, img, c, t)) -> {D.Tg(m, c) == D.A.tag(t) : U32}:
  nd.tag(ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), t, D.is.nd(ds, m, im, fi, nx, ks, img, c, t, h))

# the two roots' terms, of HS with two roots
def hs.r1(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32,
  +im: U32, +c1: U32, +u1: Bk.Term, +c2: U32, +u2: Bk.Term, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>,
  h: D.HS(ds, ks, img, m, nx, fi, im, [D.Rt{c1, u1}, D.Rt{c2, u2}], bs, fs, sp, pend, ps)) -> D.Is(ds, m, im, fi, nx, ks, img, c1, u1):
  match h:
    case Tuple{Tuple{i, _}, _}:
      i

def hs.r2(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32,
  +im: U32, +c1: U32, +u1: Bk.Term, +c2: U32, +u2: Bk.Term, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>,
  h: D.HS(ds, ks, img, m, nx, fi, im, [D.Rt{c1, u1}, D.Rt{c2, u2}], bs, fs, sp, pend, ps)) -> D.Is(ds, m, im, fi, nx, ks, img, c2, u2):
  match h:
    case Tuple{Tuple{_, Tuple{i, _}}, _}:
      i

# the parts of a λ-match of labels' cell: its cases h (field 3) and n (field 4)
def mat.h(+ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +x: U32, +j: List<&2, Word(8n)>, +h: Bk.Term, +n: Bk.Term,
  hi: D.Is(ds, m, im, fi, nx, ks, img, x, Bk.Term.Mat{j, h, n})) -> D.Is(ds, m, im, fi, nx, ks, img, D.Fd(3n, m, x), h):
  match hi:
    case Tuple{_, Tuple{_, Tuple{Tuple{_, i}, _}}}:
      i

def mat.n(+ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +x: U32, +j: List<&2, Word(8n)>, +h: Bk.Term, +n: Bk.Term,
  hi: D.Is(ds, m, im, fi, nx, ks, img, x, Bk.Term.Mat{j, h, n})) -> D.Is(ds, m, im, fi, nx, ks, img, D.Fd(4n, m, x), n):
  match hi:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{_, i}}}}:
      i

def mat.nm(+ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +x: U32, +j: List<&2, Word(8n)>, +h: Bk.Term, +n: Bk.Term,
  hi: D.Is(ds, m, im, fi, nx, ks, img, x, Bk.Term.Mat{j, h, n})) -> D.Nm(ks, Cr.Cir.Cells.get(m, x), j):
  match hi:
    case Tuple{_, Tuple{e, _}}:
      e

def lab.nm(+ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +y: U32, +l: List<&2, Word(8n)>,
  hi: D.Is(ds, m, im, fi, nx, ks, img, y, Bk.Term.Lab{l})) -> D.Nm(ks, Cr.Cir.Cells.get(m, y), l):
  match hi:
    case Tuple{_, e}:
      e

# the cases of a λ-match of labels at x are nodes of its term
def node.mat3(+m: Cr.Cir.Cells, +x: U32, +j: List<&2, Word(8n)>, +h: Bk.Term, +n: Bk.Term) ->
  {D.Node(Bk.Term.Mat{j, h, n}, m, x, D.Fd(3n, m, x)) == True{} : Bool}:
  +c = D.Fd(3n, m, x)
  D.or.r(U32.is_eq(x, c), Bool.or(D.Node(h, m, c, c), D.Node(n, m, D.Fd(4n, m, x), c)),
    D.or.l(D.Node(h, m, c, c), D.Node(n, m, D.Fd(4n, m, x), c), node.self(h, m, c, c, D.u32.refl(c))))

def node.mat4(+m: Cr.Cir.Cells, +x: U32, +j: List<&2, Word(8n)>, +h: Bk.Term, +n: Bk.Term) ->
  {D.Node(Bk.Term.Mat{j, h, n}, m, x, D.Fd(4n, m, x)) == True{} : Bool}:
  +c = D.Fd(4n, m, x)
  D.or.r(U32.is_eq(x, c), Bool.or(D.Node(h, m, D.Fd(3n, m, x), c), D.Node(n, m, c, c)),
    D.or.r(D.Node(h, m, D.Fd(3n, m, x), c), D.Node(n, m, c, c), node.self(n, m, c, c, D.u32.refl(c))))

# a node of the second of two roots is a node of the roots
def nodes.snd(+r1: D.Rt, +c2: U32, +u2: Bk.Term, +m: Cr.Cir.Cells, +c: U32, h: {D.Node(u2, m, c2, c) == True{} : Bool}) ->
  {D.Nodes([r1, D.Rt{c2, u2}], m, c) == True{} : Bool}:
  match r1:
    case D.Rt{+c1, +u1}:
      D.or.r(D.Node(u1, m, c1, c), Bool.or(D.Node(u2, m, c2, c), False{}), D.or.l(D.Node(u2, m, c2, c), False{}, h))

def nodes.fst(+c1: U32, +u1: Bk.Term, +rs: List<&2, D.Rt>, +m: Cr.Cir.Cells, +c: U32, h: {D.Node(u1, m, c1, c) == True{} : Bool}) ->
  {D.Nodes(Con{D.Rt{c1, u1}, rs}, m, c) == True{} : Bool}:
  D.or.l(D.Node(u1, m, c1, c), D.Nodes(rs, m, c), h)

# a is at most max(a, b)
def le.max.l(a: Nat, b: Nat) -> N.Le(a, Nat.max(a, b)):
  match a b:
    case 0n _:
      N.le_zero(b)
    case 1n+ap 0n:
      N.le_refl(1n+ap)
    case 1n+ap 1n+bp:
      le.max.l(ap, bp)

# The hit of a λ-match of labels
# -------------------------------
#
# M.redex's hit: n gets the case h (field 3 of x), M.inc n, M.dec y (the
# label) and x (the λ-match), and h is the focus, to evaluate: a step.

# the focus and the mode set: the step ends
def mat.end(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st0: Cr.Cir.State, +t: Bk.Term, +w: Nat, +lim: U32, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +inp: List<&2, Word(8n)>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>,
  +nv: U32, +h: Bk.Term, +u: Bk.Term, et: {D.A.plugs(fs, h) == u : Bk.Term}, es: {El.Eval.step(ds, t) == Some{u} : Maybe<Bk.Term>}, afs: D.AFs.ok(ds, fs),
  hmem: N.Le(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), Nat.max(D.Mem.cells(st0), D.Need(ds, st0, t))),
  hex: D.Ex(List<&2, D.Rt>, zs => D.AccK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{nv, h}], Nil{}, sp, fs, ps, zs)),
  hs: D.HS(ds, ks, img, m, nx, fi, im, [D.Rt{nv, h}], Nil{}, fs, sp, pend, ps),
  +hl: {List.length(&2, U32, regs) == 63n : Nat}, h15: {List.get(&2, U32, regs, 15n) == Some{nv} : Maybe<&2, U32>},
  +h2: {List.get(&2, U32, regs, 2n) == Some{sp} : Maybe<&2, U32>}, +h3: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>}) ->
  PB(ds, ks, img, st0, t, w, lim, Cr.Cir.exec(f, Mc.M.do([Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())), Mc.M.set(Mc.R.mode(), Mc.M.c(0))]), X.X.st(regs, m, nx, fi, im, pg, lim, inp))):
  match hex:
    case Tuple{+zs, hac}:
      +r0 = X.X.set(regs, 0n, nv)
      +r1 = X.X.set(r0, 1n, 0)
      +l0 = X.L.len(regs, 0n, nv, 63n, hl)
      +l1 = X.L.len(r0, 1n, 0, 63n, l0)
      +g0 = X.L.go(r0, 1n, 0n, 0, nv, {==}, X.L.gs(regs, 0n, nv, X.L.lt(regs, 0n, hl, {==})))
      +g1 = X.L.gs(r0, 1n, 0, X.L.lt(r0, 1n, l0, {==}))
      +g2 = X.L.go(r0, 1n, 2n, 0, sp, {==}, X.L.go(regs, 0n, 2n, nv, sp, {==}, h2))
      +g3 = X.L.go(r0, 1n, 3n, 0, pend, {==}, X.L.go(regs, 0n, 3n, nv, pend, {==}, h3))
      pb.set(f, ds, ks, img, st0, t, w, lim, 0n, Mc.M.g(15n), Mc.M.do([Mc.M.set(Mc.R.mode(), Mc.M.c(0))]), X.X.st(regs, m, nx, fi, im, pg, lim, inp), nv, h15, hl, {==},
        pb.set(f, ds, ks, img, st0, t, w, lim, 1n, Mc.M.c(0), Mc.M.do([]), X.X.st(r0, m, nx, fi, im, pg, lim, inp), 0, {==}, l0, {==},
          (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, Cr.Cir.Stmt.nop{}, X.X.st(r1, m, nx, fi, im, pg, lim, inp)), Cr.Cir.Out.next{X.X.st(r1, m, nx, fi, im, pg, lim, inp)}, X.run.nop(f, X.X.st(r1, m, nx, fi, im, pg, lim, inp))) :
              PB(ds, ks, img, st0, t, w, lim, _);
            fin.stp(ds, ks, img, st0, t, w, u, r1, m, nx, fi, im, pg, lim, inp, nv, h, fs, sp, pend, ps, zs, hs, hac, l1, g0, g1, g2, g3,
              et, es, afs, hmem))))

# M.dec x, the λ-match, a dead root (the first root, after a trade)
def dec.x(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st0: Cr.Cir.State, +t: Bk.Term, +w: Nat, +lim: U32, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +inp: List<&2, Word(8n)>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>,
  +nv: U32, +h: Bk.Term, +x: U32, +dx: Bk.Term, +u: Bk.Term, et: {D.A.plugs(fs, h) == u : Bk.Term}, es: {El.Eval.step(ds, t) == Some{u} : Maybe<Bk.Term>}, afs: D.AFs.ok(ds, fs),
  hmem: N.Le(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), Nat.max(D.Mem.cells(st0), D.Need(ds, st0, t))),
  hex: D.Ex(List<&2, D.Rt>, zs => D.AccK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{nv, h}, D.Rt{x, dx}], Nil{}, sp, fs, ps, zs)),
  hs: D.HS(ds, ks, img, m, nx, fi, im, [D.Rt{nv, h}, D.Rt{x, dx}], Nil{}, fs, sp, pend, ps),
  +hl: {List.length(&2, U32, regs) == 63n : Nat}, +h15: {List.get(&2, U32, regs, 15n) == Some{nv} : Maybe<&2, U32>},
  +h11: {List.get(&2, U32, regs, 11n) == Some{x} : Maybe<&2, U32>},
  +h2: {List.get(&2, U32, regs, 2n) == Some{sp} : Maybe<&2, U32>}, +h3: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>}) ->
  PB(ds, ks, img, st0, t, w, lim, Cr.Cir.exec(f, Mc.M.do([Mc.M.dec(Mc.R.x()), Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())), Mc.M.set(Mc.R.mode(), Mc.M.c(0))]), X.X.st(regs, m, nx, fi, im, pg, lim, inp))):
  match hex:
    case Tuple{+zs, hac}:
      pb.dec(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, 11n, [D.Rt{nv, h}], Nil{}, fs, sp, pend, ps, x, dx, Nil{}, zs, Mc.M.do([Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())), Mc.M.set(Mc.R.mode(), Mc.M.c(0))]),
        hsk.swap(ds, ks, img, m, nx, fi, im, nv, h, x, dx, Nil{}, fs, sp, pend, ps, hs),
        acc.swap(ds, ks, img, m, nx, fi, im, D.Rt{nv, h}, D.Rt{x, dx}, Nil{}, sp, fs, ps, zs, hac),
        Unit{}, hl, h11, h3, {==},
        +m2 => +d => +pend2 => +ps2 => hst => hs2 => hac2 =>
          mat.end(f, ds, ks, img, st0, t, w, lim, X.X.set(X.X.set(regs, 5n, d), 3n, pend2), m2, nx, fi, im, pg, inp, fs, sp, pend2, ps2, nv, h, u, et, es, afs, hmem, hac2, hs2,
            X.L.len(X.X.set(regs, 5n, d), 3n, pend2, 63n, X.L.len(regs, 5n, d, 63n, hl)),
            X.L.go(X.X.set(regs, 5n, d), 3n, 15n, pend2, nv, {==}, X.L.go(regs, 5n, 15n, d, nv, {==}, h15)),
            X.L.go(X.X.set(regs, 5n, d), 3n, 2n, pend2, sp, {==}, X.L.go(regs, 5n, 2n, d, sp, {==}, h2)),
            X.L.gs(X.X.set(regs, 5n, d), 3n, pend2, X.L.lt(X.X.set(regs, 5n, d), 3n, X.L.len(regs, 5n, d, 63n, hl), {==}))))

# tx.dec y, a dead root (the first root, after a trade), then tx.dec x
def dec.yx(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st0: Cr.Cir.State, +t: Bk.Term, +w: Nat, +lim: U32, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +inp: List<&2, Word(8n)>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  +nv: U32, +h: Bk.Term, +y: U32, +ty: Bk.Term, +x: U32, +tx: Bk.Term, +u: Bk.Term, et: {D.A.plugs(fs, h) == u : Bk.Term}, es: {El.Eval.step(ds, t) == Some{u} : Maybe<Bk.Term>}, afs: D.AFs.ok(ds, fs),
  hmem: N.Le(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), Nat.max(D.Mem.cells(st0), D.Need(ds, st0, t))),
  hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{nv, h}, D.Rt{y, ty}, D.Rt{x, tx}], Nil{}, sp, fs, ps, zs),
  hs: D.HSK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{nv, h}, D.Rt{y, ty}, D.Rt{x, tx}], [D.Rt{nv, h}], fs, sp, pend, ps),
  +hl: {List.length(&2, U32, regs) == 63n : Nat}, +h15: {List.get(&2, U32, regs, 15n) == Some{nv} : Maybe<&2, U32>},
  +h11: {List.get(&2, U32, regs, 11n) == Some{x} : Maybe<&2, U32>}, +h12: {List.get(&2, U32, regs, 12n) == Some{y} : Maybe<&2, U32>},
  +h2: {List.get(&2, U32, regs, 2n) == Some{sp} : Maybe<&2, U32>}, +h3: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>}) ->
  PB(ds, ks, img, st0, t, w, lim, Cr.Cir.exec(f, Mc.M.do([Mc.M.dec(Mc.R.y()), Mc.M.dec(Mc.R.x()), Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())), Mc.M.set(Mc.R.mode(), Mc.M.c(0))]), X.X.st(regs, m, nx, fi, im, pg, lim, inp))):
  pb.dec(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, 12n, [D.Rt{nv, h}, D.Rt{x, tx}], Nil{}, fs, sp, pend, ps, y, ty, Nil{}, zs,
    Mc.M.do([Mc.M.dec(Mc.R.x()), Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())), Mc.M.set(Mc.R.mode(), Mc.M.c(0))]),
    hsk.swap(ds, ks, img, m, nx, fi, im, nv, h, y, ty, [D.Rt{x, tx}], fs, sp, pend, ps,
      hsk.drop(ds, ks, img, m, nx, fi, im, [D.Rt{nv, h}, D.Rt{y, ty}, D.Rt{x, tx}], D.Rt{nv, h}, Nil{}, fs, sp, pend, ps, hs)),
    acc.swap(ds, ks, img, m, nx, fi, im, D.Rt{nv, h}, D.Rt{y, ty}, [D.Rt{x, tx}], sp, fs, ps, zs, hac),
    Unit{}, hl, h12, h3, {==},
    +m2 => +d => +pend2 => +ps2 => hst => hs2 => hac2 =>
      dec.x(f, ds, ks, img, st0, t, w, lim, X.X.set(X.X.set(regs, 5n, d), 3n, pend2), m2, nx, fi, im, pg, inp, fs, sp, pend2, ps2, nv, h, x, tx, u, et, es, afs, hmem, hac2, hs2,
        X.L.len(X.X.set(regs, 5n, d), 3n, pend2, 63n, X.L.len(regs, 5n, d, 63n, hl)),
        X.L.go(X.X.set(regs, 5n, d), 3n, 15n, pend2, nv, {==}, X.L.go(regs, 5n, 15n, d, nv, {==}, h15)),
        X.L.go(X.X.set(regs, 5n, d), 3n, 11n, pend2, x, {==}, X.L.go(regs, 5n, 11n, d, x, {==}, h11)),
        X.L.go(X.X.set(regs, 5n, d), 3n, 2n, pend2, sp, {==}, X.L.go(regs, 5n, 2n, d, sp, {==}, h2)),
        X.L.gs(X.X.set(regs, 5n, d), 3n, pend2, X.L.lt(X.X.set(regs, 5n, d), 3n, X.L.len(regs, 5n, d, 63n, hl), {==}))))

# the hit: from HS with the label y of l and the λ-match x as roots
def mat.hit(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st0: Cr.Cir.State, +t: Bk.Term, +w: Nat, +lim: U32, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +inp: List<&2, Word(8n)>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  +x: U32, +j: List<&2, Word(8n)>, +h: Bk.Term, +n: Bk.Term, +y: U32, +l: List<&2, Word(8n)>, +u: Bk.Term, et: {D.A.plugs(fs, h) == u : Bk.Term}, es: {El.Eval.step(ds, t) == Some{u} : Maybe<Bk.Term>}, afs: D.AFs.ok(ds, fs),
  hmem: N.Le(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), Nat.max(D.Mem.cells(st0), D.Need(ds, st0, t))),
  +hs: D.HS(ds, ks, img, m, nx, fi, im, [D.Rt{y, Bk.Term.Lab{l}}, D.Rt{x, Bk.Term.Mat{j, h, n}}], Nil{}, fs, sp, pend, ps),
  hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{y, Bk.Term.Lab{l}}, D.Rt{x, Bk.Term.Mat{j, h, n}}], Nil{}, sp, fs, ps, zs),
  +hl: {List.length(&2, U32, regs) == 63n : Nat},
  +h11: {List.get(&2, U32, regs, 11n) == Some{x} : Maybe<&2, U32>}, +h12: {List.get(&2, U32, regs, 12n) == Some{y} : Maybe<&2, U32>},
  +h2: {List.get(&2, U32, regs, 2n) == Some{sp} : Maybe<&2, U32>}, +h3: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>}) ->
  PB(ds, ks, img, st0, t, w, lim, Cr.Cir.exec(f, Mc.M.do([Mc.M.set(Mc.R.n(), Mc.M.f(3n, Mc.M.g(Mc.R.x()))), Mc.M.inc(Mc.R.n()), Mc.M.dec(Mc.R.y()), Mc.M.dec(Mc.R.x()), Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())), Mc.M.set(Mc.R.mode(), Mc.M.c(0))]), X.X.st(regs, m, nx, fi, im, pg, lim, inp))):
  +M = {Bk.Term.Mat{j, h, n} : Bk.Term}
  +L = {Bk.Term.Lab{l} : Bk.Term}
  +nv = D.Fd(3n, m, x)
  +r1 = X.X.set(regs, 15n, nv)
  +isx = hs.r2(ds, ks, img, m, nx, fi, im, y, L, x, M, Nil{}, fs, sp, pend, ps, hs)
  +ev = X.ev.fld(3n, Mc.M.g(11n), X.X.st(regs, m, nx, fi, im, pg, lim, inp), x, h11, isk.cell(ds, m, im, fi, nx, ks, img, x, M, isx))
  pb.set(f, ds, ks, img, st0, t, w, lim, 15n, Mc.M.f(3n, Mc.M.g(11n)), Mc.M.do([Mc.M.inc(Mc.R.n()), Mc.M.dec(Mc.R.y()), Mc.M.dec(Mc.R.x()), Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())), Mc.M.set(Mc.R.mode(), Mc.M.c(0))]), X.X.st(regs, m, nx, fi, im, pg, lim, inp), nv, ev, hl, {==},
    pb.inc(f, ds, ks, img, st0, t, w, lim, r1, m, nx, fi, im, pg, inp, 15n, [D.Rt{y, L}, D.Rt{x, M}], Nil{}, fs, sp, pend, ps, nv, h, Nil{}, zs,
      Mc.M.do([Mc.M.dec(Mc.R.y()), Mc.M.dec(Mc.R.x()), Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())), Mc.M.set(Mc.R.mode(), Mc.M.c(0))]),
      hsk.borrow(ds, ks, img, m, nx, fi, im, [D.Rt{y, L}, D.Rt{x, M}], nv, h, fs, sp, pend, ps,
        mat.h(ds, m, im, fi, nx, ks, img, x, j, h, n, isx), nodes.snd(D.Rt{y, L}, x, M, m, nv, node.mat3(m, x, j, h, n)), hs),
      hac, N.toLe(2n, 64n, {==}), X.L.gs(regs, 15n, nv, X.L.lt(regs, 15n, hl, {==})),
      m2 => hst => hs2 => hac2 =>
        dec.yx(f, ds, ks, img, st0, t, w, lim, r1, m2, nx, fi, im, pg, inp, fs, sp, pend, ps, zs, nv, h, y, L, x, M, u, et, es, afs, hmem, hac2, hs2, X.L.len(regs, 15n, nv, 63n, hl),
          X.L.gs(regs, 15n, nv, X.L.lt(regs, 15n, hl, {==})), X.L.go(regs, 15n, 11n, nv, x, {==}, h11), X.L.go(regs, 15n, 12n, nv, y, {==}, h12),
          X.L.go(regs, 15n, 2n, nv, sp, {==}, h2), X.L.go(regs, 15n, 3n, nv, pend, {==}, h3))))

# The miss of a λ-match of labels, and M.redex's λ-match branch
# -------------------------------------------------------------
#
# M.redex's miss: n gets the default n (field 4 of x), M.inc n, M.push of
# App q □ y (the label, known) in the old frame's cell, M.dec x, and n is
# the focus, to evaluate: a step (App q (Mat j h n) l steps to App q n l).

# registers that M.push keeps (KEEP)
def kept.r11(-regs: List<&2, U32>, -regs1: List<&2, U32>, kept: D.Kept(regs, regs1, KEEP())) ->
  {List.get(&2, U32, regs1, 11n) == List.get(&2, U32, regs, 11n) : Maybe<&2, U32>}:
  match kept:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}:
      e

def kept.r12(-regs: List<&2, U32>, -regs1: List<&2, U32>, kept: D.Kept(regs, regs1, KEEP())) ->
  {List.get(&2, U32, regs1, 12n) == List.get(&2, U32, regs, 12n) : Maybe<&2, U32>}:
  match kept:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}:
      e

def kept.r14(-regs: List<&2, U32>, -regs1: List<&2, U32>, kept: D.Kept(regs, regs1, KEEP())) ->
  {List.get(&2, U32, regs1, 14n) == List.get(&2, U32, regs, 14n) : Maybe<&2, U32>}:
  match kept:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}:
      e

def kept.r15(-regs: List<&2, U32>, -regs1: List<&2, U32>, kept: D.Kept(regs, regs1, KEEP())) ->
  {List.get(&2, U32, regs1, 15n) == List.get(&2, U32, regs, 15n) : Maybe<&2, U32>}:
  match kept:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}:
      e

# b or False is b
def or.f.l(b: Bool, h: {Bool.or(b, False{}) == True{} : Bool}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      h

# the header of App q □ a, a known: M.header(app_val, q, known)
def HV(q: Bk.Quan) -> U32:
  Wa.Wasm.op(Wa.Wasm.Op.or{}, Wa.Wasm.op(Wa.Wasm.Op.or{}, 33, Wa.Wasm.op(Wa.Wasm.Op.shl{}, Mc.Img.quan(q), 6)), 2048)

def hv.tg(q: Bk.Quan) -> {D.TgW(HV(q)) == 33 : U32}:
  match q:
    case Bk.Quan.Q0{}:
      {==}
    case Bk.Quan.Q1{}:
      {==}
    case Bk.Quan.Q2{}:
      {==}

def hv.qn(q: Bk.Quan) -> {D.QnW(HV(q)) == Mc.Img.quan(q) : U32}:
  match q:
    case Bk.Quan.Q0{}:
      {==}
    case Bk.Quan.Q1{}:
      {==}
    case Bk.Quan.Q2{}:
      {==}

def hv.st(q: Bk.Quan) -> {D.FlW(HV(q), 1024) == False{} : Bool}:
  match q:
    case Bk.Quan.Q0{}:
      {==}
    case Bk.Quan.Q1{}:
      {==}
    case Bk.Quan.Q2{}:
      {==}

def hv.kn(q: Bk.Quan) -> {D.FlW(HV(q), 2048) == True{} : Bool}:
  match q:
    case Bk.Quan.Q0{}:
      {==}
    case Bk.Quan.Q1{}:
      {==}
    case Bk.Quan.Q2{}:
      {==}

# the header's value, in any state that keeps the register q
def ev.hdr(+regs: List<&2, U32>, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +q: Bk.Quan,
  h14: {List.get(&2, U32, regs, 14n) == Some{Mc.Img.quan(q)} : Maybe<&2, U32>},
  +rr: List<&2, U32>, kp: D.Kept(regs, rr, KEEP()), +mz: Cr.Cir.Cells, +nz: U32, +pz: U32) ->
  {Cr.Cir.eval(Mc.M.header(Mc.K.app_val(), Mc.M.g(Mc.R.q()), Mc.M.c(Mc.F.known())), X.X.st(rr, mz, nz, fi, im, pz, lim, inp)) == Some{HV(q)} : Maybe<&2, U32>}:
  +s = X.X.st(rr, mz, nz, fi, im, pz, lim, inp)
  +Q = Mc.Img.quan(q)
  X.ev.op(Wa.Wasm.Op.or{}, Mc.M.or(Mc.M.c(33), Mc.M.shl(Mc.M.g(14n), Mc.M.c(6))), Mc.M.c(2048), s,
    Wa.Wasm.op(Wa.Wasm.Op.or{}, 33, Wa.Wasm.op(Wa.Wasm.Op.shl{}, Q, 6)), 2048,
    X.ev.op(Wa.Wasm.Op.or{}, Mc.M.c(33), Mc.M.shl(Mc.M.g(14n), Mc.M.c(6)), s, 33, Wa.Wasm.op(Wa.Wasm.Op.shl{}, Q, 6), {==},
      X.ev.op(Wa.Wasm.Op.shl{}, Mc.M.g(14n), Mc.M.c(6), s, Q, 6,
        Equal.trans(Maybe<&2, U32>, List.get(&2, U32, rr, 14n), List.get(&2, U32, regs, 14n), Some{Q}, kept.r14(regs, rr, kp), h14), {==})),
    {==})

# a kept register's value, in any state
def ev.kept12(+regs: List<&2, U32>, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +y: U32,
  h12: {List.get(&2, U32, regs, 12n) == Some{y} : Maybe<&2, U32>},
  +rr: List<&2, U32>, kp: D.Kept(regs, rr, KEEP()), +mz: Cr.Cir.Cells, +nz: U32, +pz: U32) ->
  {Cr.Cir.eval(Mc.M.g(12n), X.X.st(rr, mz, nz, fi, im, pz, lim, inp)) == Some{y} : Maybe<&2, U32>}:
  Equal.trans(Maybe<&2, U32>, List.get(&2, U32, rr, 12n), List.get(&2, U32, regs, 12n), Some{y}, kept.r12(regs, rr, kp), h12)

# after M.push: M.dec x and the end, in the new frame App q □ y
def mat.miss.k(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st0: Cr.Cir.State, +t: Bk.Term, +w: Nat, +lim: U32, +regs: List<&2, U32>, +regs1: List<&2, U32>, +m1: Cr.Cir.Cells, +nx: U32, +nx1: U32, +fi: U32, +im: U32,
  +pg1: U32, +inp: List<&2, Word(8n)>, +fs: List<&2, D.AF>, +sp: U32, +z: U32, +pend2: U32, +ps2: List<&2, U32>, +zs2: List<&2, D.Rt>,
  +p0: U32, +ps0: List<&2, U32>, +x: U32, +j: List<&2, Word(8n)>, +h: Bk.Term, +n: Bk.Term, +y: U32, +l: List<&2, Word(8n)>, +q: Bk.Quan, +nv: U32,
  es: {El.Eval.step(ds, t) == Some{D.A.plugs(fs, Bk.Term.App{q, n, Bk.Term.Lab{l}})} : Maybe<Bk.Term>}, afs: D.AFs.ok(ds, fs),
  hmem: N.Le(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), Nat.max(D.Mem.cells(st0), D.Need(ds, st0, t))),
  +hl1: {List.length(&2, U32, regs1) == 63n : Nat}, +kp: D.Kept(regs, regs1, KEEP()),
  +hp2: {List.get(&2, U32, regs1, 3n) == Some{pend2} : Maybe<&2, U32>},
  hor: {Bool.or(Bool.and(D.Mem(Con{p0, ps0}, z), U32.is_eq(nx1, nx)), Bool.and(D.Pend.none(Con{p0, ps0}), Bool.and(U32.is_eq(z, nx), U32.is_eq(nx1, U32.inc(nx))))) == True{} : Bool},
  hs3: D.HSK(True{}, ds, ks, img, Cr.Cir.Cells.set(m1, z, Cr.Cir.Cell{HV(q), sp, y, 0, 0}), nx1, fi, im, [D.Rt{nv, n}, D.Rt{x, Bk.Term.Mat{j, h, n}}], Nil{}, Con{D.AF{D.FK.val{}, q, True{}, Bk.Term.Lab{l}, Bk.Term.Lab{l}}, fs}, z, pend2, ps2),
  hac3: D.AccK(True{}, ds, ks, img, Cr.Cir.Cells.set(m1, z, Cr.Cir.Cell{HV(q), sp, y, 0, 0}), nx1, fi, im, [D.Rt{nv, n}, D.Rt{x, Bk.Term.Mat{j, h, n}}], Nil{}, z, Con{D.AF{D.FK.val{}, q, True{}, Bk.Term.Lab{l}, Bk.Term.Lab{l}}, fs}, ps2, zs2),
  +h11: {List.get(&2, U32, regs, 11n) == Some{x} : Maybe<&2, U32>}, +h15: {List.get(&2, U32, regs, 15n) == Some{nv} : Maybe<&2, U32>}) ->
  PB(ds, ks, img, st0, t, w, lim, Cr.Cir.exec(f, Mc.M.do([Mc.M.dec(Mc.R.x()), Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())), Mc.M.set(Mc.R.mode(), Mc.M.c(0))]), X.X.st(X.X.set(regs1, 2n, z), Cr.Cir.Cells.set(m1, z, Cr.Cir.Cell{HV(q), sp, y, 0, 0}), nx1, fi, im, pg1, lim, inp))):
  +L = {Bk.Term.Lab{l} : Bk.Term}
  +FS2 = {Con{D.AF{D.FK.val{}, q, True{}, L, L}, fs} : List<&2, D.AF>}
  +r2 = X.X.set(regs1, 2n, z)
  +enx = D.u32.eq(nx1, nx, D.and.r(D.Mem(Con{p0, ps0}, z), U32.is_eq(nx1, nx), or.f.l(Bool.and(D.Mem(Con{p0, ps0}, z), U32.is_eq(nx1, nx)), hor)))
  dec.x(f, ds, ks, img, st0, t, w, lim, r2, Cr.Cir.Cells.set(m1, z, Cr.Cir.Cell{HV(q), sp, y, 0, 0}), nx1, fi, im, pg1, inp, FS2, z, pend2, ps2, nv, n, x, Bk.Term.Mat{j, h, n},
    D.A.plugs(FS2, n), {==}, es, ({==}, afs),
    (%Equal.sym(U32, nx1, nx, enx) : N.Le(Nat.sub(U32.to_nat(_), U32.to_nat(fi)), Nat.max(D.Mem.cells(st0), D.Need(ds, st0, t))); hmem),
    (zs2, hac3), hs3, X.L.len(regs1, 2n, z, 63n, hl1),
    X.L.go(regs1, 2n, 15n, z, nv, {==}, Equal.trans(Maybe<&2, U32>, List.get(&2, U32, regs1, 15n), List.get(&2, U32, regs, 15n), Some{nv}, kept.r15(regs, regs1, kp), h15)),
    X.L.go(regs1, 2n, 11n, z, x, {==}, Equal.trans(Maybe<&2, U32>, List.get(&2, U32, regs1, 11n), List.get(&2, U32, regs, 11n), Some{x}, kept.r11(regs, regs1, kp), h11)),
    X.L.gs(regs1, 2n, z, X.L.lt(regs1, 2n, hl1, {==})), X.L.go(regs1, 2n, 3n, z, pend2, {==}, hp2))

# the miss: from HS with the label y of l and the λ-match x as roots
def mat.miss(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st0: Cr.Cir.State, +t: Bk.Term, +w: Nat, +lim: U32, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +inp: List<&2, Word(8n)>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32, +p0: U32, +ps0: List<&2, U32>, +zs: List<&2, D.Rt>,
  +x: U32, +j: List<&2, Word(8n)>, +h: Bk.Term, +n: Bk.Term, +y: U32, +l: List<&2, Word(8n)>, +q: Bk.Quan,
  es: {El.Eval.step(ds, t) == Some{D.A.plugs(fs, Bk.Term.App{q, n, Bk.Term.Lab{l}})} : Maybe<Bk.Term>}, afs: D.AFs.ok(ds, fs),
  hmem: N.Le(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), Nat.max(D.Mem.cells(st0), D.Need(ds, st0, t))),
  +hs: D.HS(ds, ks, img, m, nx, fi, im, [D.Rt{y, Bk.Term.Lab{l}}, D.Rt{x, Bk.Term.Mat{j, h, n}}], Nil{}, fs, sp, pend, Con{p0, ps0}),
  hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{y, Bk.Term.Lab{l}}, D.Rt{x, Bk.Term.Mat{j, h, n}}], Nil{}, sp, fs, Con{p0, ps0}, zs),
  +hl: {List.length(&2, U32, regs) == 63n : Nat},
  +h11: {List.get(&2, U32, regs, 11n) == Some{x} : Maybe<&2, U32>}, +h12: {List.get(&2, U32, regs, 12n) == Some{y} : Maybe<&2, U32>},
  +h14: {List.get(&2, U32, regs, 14n) == Some{Mc.Img.quan(q)} : Maybe<&2, U32>},
  +h2: {List.get(&2, U32, regs, 2n) == Some{sp} : Maybe<&2, U32>}, +h3: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>}) ->
  PB(ds, ks, img, st0, t, w, lim, Cr.Cir.exec(f, Mc.M.do([Mc.M.set(Mc.R.n(), Mc.M.f(4n, Mc.M.g(Mc.R.x()))), Mc.M.inc(Mc.R.n()), Mc.M.push(Mc.M.header(Mc.K.app_val(), Mc.M.g(Mc.R.q()), Mc.M.c(Mc.F.known())), Mc.M.g(Mc.R.y()), Mc.M.c(0)), Mc.M.dec(Mc.R.x()), Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())), Mc.M.set(Mc.R.mode(), Mc.M.c(0))]), X.X.st(regs, m, nx, fi, im, pg, lim, inp))):
  +M = {Bk.Term.Mat{j, h, n} : Bk.Term}
  +L = {Bk.Term.Lab{l} : Bk.Term}
  +PS = {Con{p0, ps0} : List<&2, U32>}
  +nv = D.Fd(4n, m, x)
  +r1 = X.X.set(regs, 15n, nv)
  +isx = hs.r2(ds, ks, img, m, nx, fi, im, y, L, x, M, Nil{}, fs, sp, pend, PS, hs)
  +ev = X.ev.fld(4n, Mc.M.g(11n), X.X.st(regs, m, nx, fi, im, pg, lim, inp), x, h11, isk.cell(ds, m, im, fi, nx, ks, img, x, M, isx))
  +hl1 = X.L.len(regs, 15n, nv, 63n, hl)
  +g11 = X.L.go(regs, 15n, 11n, nv, x, {==}, h11)
  +g12 = X.L.go(regs, 15n, 12n, nv, y, {==}, h12)
  +g14 = X.L.go(regs, 15n, 14n, nv, Mc.Img.quan(q), {==}, h14)
  +g15 = X.L.gs(regs, 15n, nv, X.L.lt(regs, 15n, hl, {==}))
  pb.set(f, ds, ks, img, st0, t, w, lim, 15n, Mc.M.f(4n, Mc.M.g(11n)), Mc.M.do([Mc.M.inc(Mc.R.n()), Mc.M.push(Mc.M.header(Mc.K.app_val(), Mc.M.g(Mc.R.q()), Mc.M.c(Mc.F.known())), Mc.M.g(Mc.R.y()), Mc.M.c(0)), Mc.M.dec(Mc.R.x()), Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())), Mc.M.set(Mc.R.mode(), Mc.M.c(0))]), X.X.st(regs, m, nx, fi, im, pg, lim, inp), nv, ev, hl, {==},
    pb.inc(f, ds, ks, img, st0, t, w, lim, r1, m, nx, fi, im, pg, inp, 15n, [D.Rt{y, L}, D.Rt{x, M}], Nil{}, fs, sp, pend, PS, nv, n, Nil{}, zs,
      Mc.M.do([Mc.M.push(Mc.M.header(Mc.K.app_val(), Mc.M.g(Mc.R.q()), Mc.M.c(Mc.F.known())), Mc.M.g(Mc.R.y()), Mc.M.c(0)), Mc.M.dec(Mc.R.x()), Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())), Mc.M.set(Mc.R.mode(), Mc.M.c(0))]),
      hsk.borrow(ds, ks, img, m, nx, fi, im, [D.Rt{y, L}, D.Rt{x, M}], nv, n, fs, sp, pend, PS,
        mat.n(ds, m, im, fi, nx, ks, img, x, j, h, n, isx), nodes.snd(D.Rt{y, L}, x, M, m, nv, node.mat4(m, x, j, h, n)), hs),
      hac, N.toLe(2n, 64n, {==}), g15,
      +m2 => hst => hs2 => hac2 =>
        pb.push(f, ds, ks, img, st0, t, w, lim, r1, m2, nx, fi, im, pg, inp, [D.Rt{nv, n}, D.Rt{x, M}], fs, sp, pend, PS, zs, q, True{}, L, L,
          Mc.M.header(Mc.K.app_val(), Mc.M.g(Mc.R.q()), Mc.M.c(Mc.F.known())), Mc.M.g(12n), Mc.M.c(0), HV(q), y, 0, Mc.M.do([Mc.M.dec(Mc.R.x()), Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())), Mc.M.set(Mc.R.mode(), Mc.M.c(0))]),
          hsk.swap(ds, ks, img, m2, nx, fi, im, nv, n, y, L, [D.Rt{x, M}], fs, sp, pend, PS,
            hsk.drop(ds, ks, img, m2, nx, fi, im, [D.Rt{nv, n}, D.Rt{y, L}, D.Rt{x, M}], D.Rt{nv, n}, Nil{}, fs, sp, pend, PS, hs2)),
          acc.swap(ds, ks, img, m2, nx, fi, im, D.Rt{nv, n}, D.Rt{y, L}, [D.Rt{x, M}], sp, fs, PS, zs, hac2),
          hl1, X.L.go(regs, 15n, 3n, nv, pend, {==}, h3), X.L.go(regs, 15n, 2n, nv, sp, {==}, h2),
          hv.tg(q), hv.qn(q), hv.st(q), hv.kn(q),
          +rr => kp => +mz => +nz => +pz => ev.hdr(r1, fi, im, lim, inp, q, g14, rr, kp, mz, nz, pz),
          +rr => kp => +mz => +nz => +pz => ev.kept12(r1, fi, im, lim, inp, y, g12, rr, kp, mz, nz, pz),
          rr => kp => mz => nz => pz => {==},
          e => D.bool.ft(N.Le(Nat.mul(20n, Nat.add(U32.to_nat(nx), 1n)), D.Budget(ds, st0, t)), e),
          +regs1 => +m1 => +nx1 => +pg1 => +z => +pend2 => +ps2 => +zs2 => +hl2 => +kp => +hp2 => _ => hor => hs3 => hac3 =>
            mat.miss.k(f, ds, ks, img, st0, t, w, lim, r1, regs1, m1, nx, nx1, fi, im, pg1, inp, fs, sp, z, pend2, ps2, zs2, p0, ps0, x, j, h, n, y, l, q, nv,
              es, afs, hmem, hl2, kp, hp2, hor, hs3, hac3, g11, g15))))

# M.redex's λ-match branch
# ------------------------
#
# From the pop's roots: y the argument a, x the λ-match. M.redex's tests of
# x's tag take the branch of mat (mat.sel); M.need halts with 2 unless q is
# live and a a label (mat.hlt), then the names of the label and the λ-match
# pick the hit or the miss (mat.nm).

# a tag test of the cell in register r
def ev.tagr(+r: Nat, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>,
  +c: U32, +k: U32, hr: {List.get(&2, U32, regs, r) == Some{c} : Maybe<&2, U32>}, hc: {Cr.Cir.is_cell(c, im, fi, nx) == True{} : Bool}) ->
  {Cr.Cir.eval(Mc.M.eq(Mc.M.tag(Mc.M.g(r)), Mc.M.c(k)), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) == Some{Wa.Wasm.op(Wa.Wasm.Op.eq{}, D.Tg(m, c), k)} : Maybe<&2, U32>}:
  X.ev.op(Wa.Wasm.Op.eq{}, Mc.M.tag(Mc.M.g(r)), Mc.M.c(k), X.X.st(regs, m, nx, fi, im, pg, lim, inp), D.Tg(m, c), k,
    X.ev.op(Wa.Wasm.Op.and{}, Mc.M.f(0n, Mc.M.g(r)), Mc.M.c(63), X.X.st(regs, m, nx, fi, im, pg, lim, inp), D.Fd(0n, m, c), 63, X.ev.fld(0n, Mc.M.g(r), X.X.st(regs, m, nx, fi, im, pg, lim, inp), c, hr, hc), {==}),
    {==})

# M.need's test: q live and a a label
def ev.cnd(+regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>,
  +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +y: U32, +a: Bk.Term, +q: Bk.Quan,
  h12: {List.get(&2, U32, regs, 12n) == Some{y} : Maybe<&2, U32>}, h14: {List.get(&2, U32, regs, 14n) == Some{Mc.Img.quan(q)} : Maybe<&2, U32>},
  +isy: D.Is(ds, m, im, fi, nx, ks, img, y, a)) ->
  {Cr.Cir.eval(Mc.M.and(Mc.M.ne(Mc.M.g(Mc.R.q()), Mc.M.c(0)), Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.y())), Mc.M.c(Mc.T.lab()))), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) == Some{Bool.to_u32(Bool.and(El.Quan.live(q), is.lab(a)))} : Maybe<&2, U32>}:
  %and.b2u(El.Quan.live(q), is.lab(a)) : {Cr.Cir.eval(Mc.M.and(Mc.M.ne(Mc.M.g(Mc.R.q()), Mc.M.c(0)), Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.y())), Mc.M.c(Mc.T.lab()))), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) == Some{_} : Maybe<&2, U32>}
  X.ev.op(Wa.Wasm.Op.and{}, Mc.M.ne(Mc.M.g(Mc.R.q()), Mc.M.c(0)), Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.y())), Mc.M.c(Mc.T.lab())), X.X.st(regs, m, nx, fi, im, pg, lim, inp),
    Bool.to_u32(El.Quan.live(q)), Bool.to_u32(is.lab(a)),
    (%q.live(q) : {Cr.Cir.eval(Mc.M.ne(Mc.M.g(Mc.R.q()), Mc.M.c(0)), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) == Some{_} : Maybe<&2, U32>};
      X.ev.op(Wa.Wasm.Op.ne{}, Mc.M.g(Mc.R.q()), Mc.M.c(0), X.X.st(regs, m, nx, fi, im, pg, lim, inp), Mc.Img.quan(q), 0, h14, {==})),
    (%tag.lab(a) : {Cr.Cir.eval(Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.y())), Mc.M.c(Mc.T.lab())), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) == Some{_} : Maybe<&2, U32>};
      %isk.tag(ds, m, im, fi, nx, ks, img, y, a, isy) : {Cr.Cir.eval(Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.y())), Mc.M.c(Mc.T.lab())), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) == Some{Wa.Wasm.op(Wa.Wasm.Op.eq{}, _, 13)} : Maybe<&2, U32>};
      ev.tagr(12n, regs, m, nx, fi, im, pg, lim, inp, y, 13, h12, isk.cell(ds, m, im, fi, nx, ks, img, y, a, isy))))

# M.redex's tests of x's tag, when x is a λ-match: its branch
def mat.sel(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st0: Cr.Cir.State, +t: Bk.Term, +w: Nat, +lim: U32, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +inp: List<&2, Word(8n)>,
  +x: U32, +j: List<&2, Word(8n)>, +h: Bk.Term, +n: Bk.Term, +h11: {List.get(&2, U32, regs, 11n) == Some{x} : Maybe<&2, U32>},
  +isx: D.Is(ds, m, im, fi, nx, ks, img, x, Bk.Term.Mat{j, h, n})) ->
  {Cr.Cir.exec(f, X.sel.t(X.sel.e(X.sel.e(Mc.M.redex()))), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) == Cr.Cir.exec(f, Mc.M.redex(), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) : Cr.Cir.Out}:
  +RX = Mc.M.redex()
  +E1 = X.sel.e(RX)
  +E2 = X.sel.e(E1)
  +hc = isk.cell(ds, m, im, fi, nx, ks, img, x, Bk.Term.Mat{j, h, n}, isx)
  +et = isk.tag(ds, m, im, fi, nx, ks, img, x, Bk.Term.Mat{j, h, n}, isx)
  +et2 = et
  +et3 = et
  Equal.trans(Cr.Cir.Out, Cr.Cir.exec(f, X.sel.t(E2), X.X.st(regs, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(f, E1, X.X.st(regs, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(f, RX, X.X.st(regs, m, nx, fi, im, pg, lim, inp)),
    Equal.trans(Cr.Cir.Out, Cr.Cir.exec(f, X.sel.t(E2), X.X.st(regs, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(f, E2, X.X.st(regs, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(f, E1, X.X.st(regs, m, nx, fi, im, pg, lim, inp)),
      X.rw.if.t(f, X.sel.c(E2), X.sel.t(E2), X.sel.e(E2), X.X.st(regs, m, nx, fi, im, pg, lim, inp), 1,
        (%et3 : {Cr.Cir.eval(X.sel.c(E2), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) == Some{Wa.Wasm.op(Wa.Wasm.Op.eq{}, _, 14)} : Maybe<&2, U32>};
          ev.tagr(11n, regs, m, nx, fi, im, pg, lim, inp, x, 14, h11, hc)), {==}),
      X.rw.if.e(f, X.sel.c(E1), X.sel.t(E1), E2, X.X.st(regs, m, nx, fi, im, pg, lim, inp),
        (%et2 : {Cr.Cir.eval(X.sel.c(E1), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) == Some{Wa.Wasm.op(Wa.Wasm.Op.eq{}, _, 11)} : Maybe<&2, U32>};
          ev.tagr(11n, regs, m, nx, fi, im, pg, lim, inp, x, 11, h11, hc)))),
    X.rw.if.e(f, X.sel.c(RX), X.sel.t(RX), E1, X.X.st(regs, m, nx, fi, im, pg, lim, inp),
      (%et : {Cr.Cir.eval(X.sel.c(RX), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) == Some{Wa.Wasm.op(Wa.Wasm.Op.eq{}, _, 7)} : Maybe<&2, U32>};
        ev.tagr(11n, regs, m, nx, fi, im, pg, lim, inp, x, 7, h11, hc))))

# a stuck term in the frames: stuck
def stuck.plugs(+ds: List<&2, Bk.Def>, fs: List<&2, D.AF>, +u: Bk.Term, hfs: D.AFs.ok(ds, fs),
  h: D.P2({El.Eval.step(ds, u) == None{} : Maybe<Bk.Term>}, {El.Eval.vals(ds, u, False{}) == False{} : Bool})) ->
  D.P2({El.Eval.step(ds, D.A.plugs(fs, u)) == None{} : Maybe<Bk.Term>}, {El.Eval.vals(ds, D.A.plugs(fs, u), False{}) == False{} : Bool}):
  match h:
    case Tuple{hs, hv}:
      K.ev.stuck(ds, fs, u, hfs, hs, hv)

def and.false(b: Bool) -> {Bool.and(b, False{}) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# M.need halts with 2, when q is dead or a no label: t is stuck
def mat.hlt(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st0: Cr.Cir.State, +t: Bk.Term, +w: Nat, +lim: U32, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +inp: List<&2, Word(8n)>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32, +p0: U32, +ps0: List<&2, U32>, +zs: List<&2, D.Rt>,
  +x: U32, +j: List<&2, Word(8n)>, +h: Bk.Term, +n: Bk.Term, +y: U32, +q: Bk.Quan, +a: Bk.Term,
  +hg: {Bool.and(El.Quan.live(q), is.lab(a)) == False{} : Bool},
  +hva: {Bool.or(Bool.not(El.Quan.live(q)), El.Eval.vals(ds, a, False{})) == True{} : Bool},
  +et0: {D.A.plugs(fs, Bk.Term.App{q, Bk.Term.Mat{j, h, n}, a}) == t : Bk.Term}, +afs: D.AFs.ok(ds, fs),
  +hmem: N.Le(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), Nat.max(D.Mem.cells(st0), D.Need(ds, st0, t))),
  +hs: D.HS(ds, ks, img, m, nx, fi, im, [D.Rt{y, a}, D.Rt{x, Bk.Term.Mat{j, h, n}}], Nil{}, fs, sp, pend, Con{p0, ps0}),
  hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{y, a}, D.Rt{x, Bk.Term.Mat{j, h, n}}], Nil{}, sp, fs, Con{p0, ps0}, zs),
  +hl: {List.length(&2, U32, regs) == 63n : Nat},
  +h11: {List.get(&2, U32, regs, 11n) == Some{x} : Maybe<&2, U32>}, +h12: {List.get(&2, U32, regs, 12n) == Some{y} : Maybe<&2, U32>},
  +h14: {List.get(&2, U32, regs, 14n) == Some{Mc.Img.quan(q)} : Maybe<&2, U32>},
  +h2: {List.get(&2, U32, regs, 2n) == Some{sp} : Maybe<&2, U32>}, +h3: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>}) ->
  PB(ds, ks, img, st0, t, w, lim, Cr.Cir.exec(f, Mc.M.need(Mc.M.and(Mc.M.ne(Mc.M.g(Mc.R.q()), Mc.M.c(0)), Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.y())), Mc.M.c(Mc.T.lab()))), Mc.M.if(Mc.M.eq(Mc.M.f(2n, Mc.M.g(Mc.R.y())), Mc.M.f(2n, Mc.M.g(Mc.R.x()))), Mc.M.do([Mc.M.set(Mc.R.n(), Mc.M.f(3n, Mc.M.g(Mc.R.x()))), Mc.M.inc(Mc.R.n()), Mc.M.dec(Mc.R.y()), Mc.M.dec(Mc.R.x()), Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())), Mc.M.set(Mc.R.mode(), Mc.M.c(0))]), Mc.M.do([Mc.M.set(Mc.R.n(), Mc.M.f(4n, Mc.M.g(Mc.R.x()))), Mc.M.inc(Mc.R.n()), Mc.M.push(Mc.M.header(Mc.K.app_val(), Mc.M.g(Mc.R.q()), Mc.M.c(Mc.F.known())), Mc.M.g(Mc.R.y()), Mc.M.c(0)), Mc.M.dec(Mc.R.x()), Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())), Mc.M.set(Mc.R.mode(), Mc.M.c(0))]))), X.X.st(regs, m, nx, fi, im, pg, lim, inp))):
  +isy = hs.r1(ds, ks, img, m, nx, fi, im, y, a, x, Bk.Term.Mat{j, h, n}, Nil{}, fs, sp, pend, Con{p0, ps0}, hs)
  +ev0 = {(%hg : {Cr.Cir.eval(Mc.M.and(Mc.M.ne(Mc.M.g(Mc.R.q()), Mc.M.c(0)), Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.y())), Mc.M.c(Mc.T.lab()))), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) == Some{Bool.to_u32(_)} : Maybe<&2, U32>};
      ev.cnd(regs, m, nx, fi, im, pg, lim, inp, ds, ks, img, y, a, q, h12, h14, isy)) : {Cr.Cir.eval(Mc.M.and(Mc.M.ne(Mc.M.g(Mc.R.q()), Mc.M.c(0)), Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.y())), Mc.M.c(Mc.T.lab()))), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) == Some{0} : Maybe<&2, U32>}}
  +e = Equal.trans(Cr.Cir.Out, Cr.Cir.exec(f, Mc.M.need(Mc.M.and(Mc.M.ne(Mc.M.g(Mc.R.q()), Mc.M.c(0)), Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.y())), Mc.M.c(Mc.T.lab()))), Mc.M.if(Mc.M.eq(Mc.M.f(2n, Mc.M.g(Mc.R.y())), Mc.M.f(2n, Mc.M.g(Mc.R.x()))), Mc.M.do([Mc.M.set(Mc.R.n(), Mc.M.f(3n, Mc.M.g(Mc.R.x()))), Mc.M.inc(Mc.R.n()), Mc.M.dec(Mc.R.y()), Mc.M.dec(Mc.R.x()), Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())), Mc.M.set(Mc.R.mode(), Mc.M.c(0))]), Mc.M.do([Mc.M.set(Mc.R.n(), Mc.M.f(4n, Mc.M.g(Mc.R.x()))), Mc.M.inc(Mc.R.n()), Mc.M.push(Mc.M.header(Mc.K.app_val(), Mc.M.g(Mc.R.q()), Mc.M.c(Mc.F.known())), Mc.M.g(Mc.R.y()), Mc.M.c(0)), Mc.M.dec(Mc.R.x()), Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())), Mc.M.set(Mc.R.mode(), Mc.M.c(0))]))), X.X.st(regs, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(f, Mc.M.halt(2), X.X.st(regs, m, nx, fi, im, pg, lim, inp)), Cr.Cir.Out.halt{2, X.X.st(regs, m, nx, fi, im, pg, lim, inp)},
    Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, Mc.M.halt(2), X.X.st(regs, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(f, Mc.M.need(Mc.M.and(Mc.M.ne(Mc.M.g(Mc.R.q()), Mc.M.c(0)), Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.y())), Mc.M.c(Mc.T.lab()))), Mc.M.if(Mc.M.eq(Mc.M.f(2n, Mc.M.g(Mc.R.y())), Mc.M.f(2n, Mc.M.g(Mc.R.x()))), Mc.M.do([Mc.M.set(Mc.R.n(), Mc.M.f(3n, Mc.M.g(Mc.R.x()))), Mc.M.inc(Mc.R.n()), Mc.M.dec(Mc.R.y()), Mc.M.dec(Mc.R.x()), Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())), Mc.M.set(Mc.R.mode(), Mc.M.c(0))]), Mc.M.do([Mc.M.set(Mc.R.n(), Mc.M.f(4n, Mc.M.g(Mc.R.x()))), Mc.M.inc(Mc.R.n()), Mc.M.push(Mc.M.header(Mc.K.app_val(), Mc.M.g(Mc.R.q()), Mc.M.c(Mc.F.known())), Mc.M.g(Mc.R.y()), Mc.M.c(0)), Mc.M.dec(Mc.R.x()), Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())), Mc.M.set(Mc.R.mode(), Mc.M.c(0))]))), X.X.st(regs, m, nx, fi, im, pg, lim, inp)), X.rw.if.e(f, Mc.M.and(Mc.M.ne(Mc.M.g(Mc.R.q()), Mc.M.c(0)), Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.y())), Mc.M.c(Mc.T.lab()))), Mc.M.if(Mc.M.eq(Mc.M.f(2n, Mc.M.g(Mc.R.y())), Mc.M.f(2n, Mc.M.g(Mc.R.x()))), Mc.M.do([Mc.M.set(Mc.R.n(), Mc.M.f(3n, Mc.M.g(Mc.R.x()))), Mc.M.inc(Mc.R.n()), Mc.M.dec(Mc.R.y()), Mc.M.dec(Mc.R.x()), Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())), Mc.M.set(Mc.R.mode(), Mc.M.c(0))]), Mc.M.do([Mc.M.set(Mc.R.n(), Mc.M.f(4n, Mc.M.g(Mc.R.x()))), Mc.M.inc(Mc.R.n()), Mc.M.push(Mc.M.header(Mc.K.app_val(), Mc.M.g(Mc.R.q()), Mc.M.c(Mc.F.known())), Mc.M.g(Mc.R.y()), Mc.M.c(0)), Mc.M.dec(Mc.R.x()), Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())), Mc.M.set(Mc.R.mode(), Mc.M.c(0))])), Mc.M.halt(2), X.X.st(regs, m, nx, fi, im, pg, lim, inp), ev0)),
    K.eq.halt(f, 2, X.X.st(regs, m, nx, fi, im, pg, lim, inp)))
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, Mc.M.need(Mc.M.and(Mc.M.ne(Mc.M.g(Mc.R.q()), Mc.M.c(0)), Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.y())), Mc.M.c(Mc.T.lab()))), Mc.M.if(Mc.M.eq(Mc.M.f(2n, Mc.M.g(Mc.R.y())), Mc.M.f(2n, Mc.M.g(Mc.R.x()))), Mc.M.do([Mc.M.set(Mc.R.n(), Mc.M.f(3n, Mc.M.g(Mc.R.x()))), Mc.M.inc(Mc.R.n()), Mc.M.dec(Mc.R.y()), Mc.M.dec(Mc.R.x()), Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())), Mc.M.set(Mc.R.mode(), Mc.M.c(0))]), Mc.M.do([Mc.M.set(Mc.R.n(), Mc.M.f(4n, Mc.M.g(Mc.R.x()))), Mc.M.inc(Mc.R.n()), Mc.M.push(Mc.M.header(Mc.K.app_val(), Mc.M.g(Mc.R.q()), Mc.M.c(Mc.F.known())), Mc.M.g(Mc.R.y()), Mc.M.c(0)), Mc.M.dec(Mc.R.x()), Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())), Mc.M.set(Mc.R.mode(), Mc.M.c(0))]))), X.X.st(regs, m, nx, fi, im, pg, lim, inp)), Cr.Cir.Out.halt{2, X.X.st(regs, m, nx, fi, im, pg, lim, inp)}, e) : PB(ds, ks, img, st0, t, w, lim, _)
  K.hr.stuck(ds, t, X.X.st(regs, m, nx, fi, im, pg, lim, inp),
    (%et0 : D.P2({El.Eval.step(ds, _) == None{} : Maybe<Bk.Term>}, {El.Eval.vals(ds, _, False{}) == False{} : Bool});
      stuck.plugs(ds, fs, Bk.Term.App{q, Bk.Term.Mat{j, h, n}, a}, afs, mat.stuck(ds, q, j, h, n, a, hg, hva))))

# the names of the label and the λ-match, equal or not: the hit or the miss
def mat.names(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st0: Cr.Cir.State, +t: Bk.Term, +w: Nat, +lim: U32, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +inp: List<&2, Word(8n)>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32, +p0: U32, +ps0: List<&2, U32>, +zs: List<&2, D.Rt>,
  +x: U32, +j: List<&2, Word(8n)>, +h: Bk.Term, +n: Bk.Term, +y: U32, +q: Bk.Quan, +l: List<&2, Word(8n)>, b: Bool,
  +eb: {U32.is_eq(D.Fd(2n, m, y), D.Fd(2n, m, x)) == b : Bool}, +hlv: {El.Quan.live(q) == True{} : Bool},
  +et0: {D.A.plugs(fs, Bk.Term.App{q, Bk.Term.Mat{j, h, n}, Bk.Term.Lab{l}}) == t : Bk.Term}, +afs: D.AFs.ok(ds, fs),
  +hmem: N.Le(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), Nat.max(D.Mem.cells(st0), D.Need(ds, st0, t))),
  +hs: D.HS(ds, ks, img, m, nx, fi, im, [D.Rt{y, Bk.Term.Lab{l}}, D.Rt{x, Bk.Term.Mat{j, h, n}}], Nil{}, fs, sp, pend, Con{p0, ps0}),
  hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{y, Bk.Term.Lab{l}}, D.Rt{x, Bk.Term.Mat{j, h, n}}], Nil{}, sp, fs, Con{p0, ps0}, zs),
  +hl: {List.length(&2, U32, regs) == 63n : Nat},
  +h11: {List.get(&2, U32, regs, 11n) == Some{x} : Maybe<&2, U32>}, +h12: {List.get(&2, U32, regs, 12n) == Some{y} : Maybe<&2, U32>},
  +h14: {List.get(&2, U32, regs, 14n) == Some{Mc.Img.quan(q)} : Maybe<&2, U32>},
  +h2: {List.get(&2, U32, regs, 2n) == Some{sp} : Maybe<&2, U32>}, +h3: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>}) ->
  PB(ds, ks, img, st0, t, w, lim, Cr.Cir.exec(f, Mc.M.if(Mc.M.eq(Mc.M.f(2n, Mc.M.g(Mc.R.y())), Mc.M.f(2n, Mc.M.g(Mc.R.x()))), Mc.M.do([Mc.M.set(Mc.R.n(), Mc.M.f(3n, Mc.M.g(Mc.R.x()))), Mc.M.inc(Mc.R.n()), Mc.M.dec(Mc.R.y()), Mc.M.dec(Mc.R.x()), Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())), Mc.M.set(Mc.R.mode(), Mc.M.c(0))]), Mc.M.do([Mc.M.set(Mc.R.n(), Mc.M.f(4n, Mc.M.g(Mc.R.x()))), Mc.M.inc(Mc.R.n()), Mc.M.push(Mc.M.header(Mc.K.app_val(), Mc.M.g(Mc.R.q()), Mc.M.c(Mc.F.known())), Mc.M.g(Mc.R.y()), Mc.M.c(0)), Mc.M.dec(Mc.R.x()), Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())), Mc.M.set(Mc.R.mode(), Mc.M.c(0))])), X.X.st(regs, m, nx, fi, im, pg, lim, inp))):
  match b:
    case True{}:
      +L = {Bk.Term.Lab{l} : Bk.Term}
      +isy = hs.r1(ds, ks, img, m, nx, fi, im, y, L, x, Bk.Term.Mat{j, h, n}, Nil{}, fs, sp, pend, Con{p0, ps0}, hs)
      +isx = hs.r2(ds, ks, img, m, nx, fi, im, y, L, x, Bk.Term.Mat{j, h, n}, Nil{}, fs, sp, pend, Con{p0, ps0}, hs)
      +ev = {(%eb : {Cr.Cir.eval(Mc.M.eq(Mc.M.f(2n, Mc.M.g(Mc.R.y())), Mc.M.f(2n, Mc.M.g(Mc.R.x()))), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) == Some{Bool.to_u32(_)} : Maybe<&2, U32>};
          X.ev.op(Wa.Wasm.Op.eq{}, Mc.M.f(2n, Mc.M.g(Mc.R.y())), Mc.M.f(2n, Mc.M.g(Mc.R.x())), X.X.st(regs, m, nx, fi, im, pg, lim, inp), D.Fd(2n, m, y), D.Fd(2n, m, x),
            X.ev.fld(2n, Mc.M.g(12n), X.X.st(regs, m, nx, fi, im, pg, lim, inp), y, h12, isk.cell(ds, m, im, fi, nx, ks, img, y, L, isy)),
            X.ev.fld(2n, Mc.M.g(11n), X.X.st(regs, m, nx, fi, im, pg, lim, inp), x, h11, isk.cell(ds, m, im, fi, nx, ks, img, x, Bk.Term.Mat{j, h, n}, isx)))) :
        {Cr.Cir.eval(Mc.M.eq(Mc.M.f(2n, Mc.M.g(Mc.R.y())), Mc.M.f(2n, Mc.M.g(Mc.R.x()))), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) == Some{1} : Maybe<&2, U32>}}
      +he = nm.same(ks, Cr.Cir.Cells.get(m, y), Cr.Cir.Cells.get(m, x), l, j, lab.nm(ds, m, im, fi, nx, ks, img, y, l, isy),
        mat.nm(ds, m, im, fi, nx, ks, img, x, j, h, n, isx), D.u32.eq(D.Fd(2n, m, y), D.Fd(2n, m, x), eb))
      +es = {(%et0 : {El.Eval.step(ds, _) == Some{D.A.plugs(fs, h)} : Maybe<Bk.Term>};
          step.plugs(ds, fs, Bk.Term.App{q, Bk.Term.Mat{j, h, n}, L}, h, afs, mat.step.hit(ds, q, j, h, n, l, hlv, he))) :
        {El.Eval.step(ds, t) == Some{D.A.plugs(fs, h)} : Maybe<Bk.Term>}}
      %X.rw.if.t(f, Mc.M.eq(Mc.M.f(2n, Mc.M.g(Mc.R.y())), Mc.M.f(2n, Mc.M.g(Mc.R.x()))), Mc.M.do([Mc.M.set(Mc.R.n(), Mc.M.f(3n, Mc.M.g(Mc.R.x()))), Mc.M.inc(Mc.R.n()), Mc.M.dec(Mc.R.y()), Mc.M.dec(Mc.R.x()), Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())), Mc.M.set(Mc.R.mode(), Mc.M.c(0))]), Mc.M.do([Mc.M.set(Mc.R.n(), Mc.M.f(4n, Mc.M.g(Mc.R.x()))), Mc.M.inc(Mc.R.n()), Mc.M.push(Mc.M.header(Mc.K.app_val(), Mc.M.g(Mc.R.q()), Mc.M.c(Mc.F.known())), Mc.M.g(Mc.R.y()), Mc.M.c(0)), Mc.M.dec(Mc.R.x()), Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())), Mc.M.set(Mc.R.mode(), Mc.M.c(0))]), X.X.st(regs, m, nx, fi, im, pg, lim, inp), 1, ev, {==}) : PB(ds, ks, img, st0, t, w, lim, _)
      mat.hit(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, Con{p0, ps0}, zs, x, j, h, n, y, l, D.A.plugs(fs, h), {==}, es, afs, hmem, hs, hac, hl, h11, h12, h2, h3)
    case False{}:
      +L = {Bk.Term.Lab{l} : Bk.Term}
      +isy = hs.r1(ds, ks, img, m, nx, fi, im, y, L, x, Bk.Term.Mat{j, h, n}, Nil{}, fs, sp, pend, Con{p0, ps0}, hs)
      +isx = hs.r2(ds, ks, img, m, nx, fi, im, y, L, x, Bk.Term.Mat{j, h, n}, Nil{}, fs, sp, pend, Con{p0, ps0}, hs)
      +ev = {(%eb : {Cr.Cir.eval(Mc.M.eq(Mc.M.f(2n, Mc.M.g(Mc.R.y())), Mc.M.f(2n, Mc.M.g(Mc.R.x()))), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) == Some{Bool.to_u32(_)} : Maybe<&2, U32>};
          X.ev.op(Wa.Wasm.Op.eq{}, Mc.M.f(2n, Mc.M.g(Mc.R.y())), Mc.M.f(2n, Mc.M.g(Mc.R.x())), X.X.st(regs, m, nx, fi, im, pg, lim, inp), D.Fd(2n, m, y), D.Fd(2n, m, x),
            X.ev.fld(2n, Mc.M.g(12n), X.X.st(regs, m, nx, fi, im, pg, lim, inp), y, h12, isk.cell(ds, m, im, fi, nx, ks, img, y, L, isy)),
            X.ev.fld(2n, Mc.M.g(11n), X.X.st(regs, m, nx, fi, im, pg, lim, inp), x, h11, isk.cell(ds, m, im, fi, nx, ks, img, x, Bk.Term.Mat{j, h, n}, isx)))) :
        {Cr.Cir.eval(Mc.M.eq(Mc.M.f(2n, Mc.M.g(Mc.R.y())), Mc.M.f(2n, Mc.M.g(Mc.R.x()))), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) == Some{0} : Maybe<&2, U32>}}
      +he = nm.diff(ks, Cr.Cir.Cells.get(m, y), Cr.Cir.Cells.get(m, x), l, j, lab.nm(ds, m, im, fi, nx, ks, img, y, l, isy),
        mat.nm(ds, m, im, fi, nx, ks, img, x, j, h, n, isx), eb)
      +es = {(%et0 : {El.Eval.step(ds, _) == Some{D.A.plugs(fs, Bk.Term.App{q, n, L})} : Maybe<Bk.Term>};
          step.plugs(ds, fs, Bk.Term.App{q, Bk.Term.Mat{j, h, n}, L}, Bk.Term.App{q, n, L}, afs, mat.step.miss(ds, q, j, h, n, l, hlv, he))) :
        {El.Eval.step(ds, t) == Some{D.A.plugs(fs, Bk.Term.App{q, n, L})} : Maybe<Bk.Term>}}
      %X.rw.if.e(f, Mc.M.eq(Mc.M.f(2n, Mc.M.g(Mc.R.y())), Mc.M.f(2n, Mc.M.g(Mc.R.x()))), Mc.M.do([Mc.M.set(Mc.R.n(), Mc.M.f(3n, Mc.M.g(Mc.R.x()))), Mc.M.inc(Mc.R.n()), Mc.M.dec(Mc.R.y()), Mc.M.dec(Mc.R.x()), Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())), Mc.M.set(Mc.R.mode(), Mc.M.c(0))]), Mc.M.do([Mc.M.set(Mc.R.n(), Mc.M.f(4n, Mc.M.g(Mc.R.x()))), Mc.M.inc(Mc.R.n()), Mc.M.push(Mc.M.header(Mc.K.app_val(), Mc.M.g(Mc.R.q()), Mc.M.c(Mc.F.known())), Mc.M.g(Mc.R.y()), Mc.M.c(0)), Mc.M.dec(Mc.R.x()), Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())), Mc.M.set(Mc.R.mode(), Mc.M.c(0))]), X.X.st(regs, m, nx, fi, im, pg, lim, inp), ev) : PB(ds, ks, img, st0, t, w, lim, _)
      mat.miss(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, j, h, n, y, l, q, es, afs, hmem, hs, hac, hl, h11, h12, h14, h2, h3)

# M.need passes: q live and a label
def mat.lv(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st0: Cr.Cir.State, +t: Bk.Term, +w: Nat, +lim: U32, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +inp: List<&2, Word(8n)>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32, +p0: U32, +ps0: List<&2, U32>, +zs: List<&2, D.Rt>,
  +x: U32, +j: List<&2, Word(8n)>, +h: Bk.Term, +n: Bk.Term, +y: U32, +q: Bk.Quan, +l: List<&2, Word(8n)>, +hlv: {El.Quan.live(q) == True{} : Bool},
  +et0: {D.A.plugs(fs, Bk.Term.App{q, Bk.Term.Mat{j, h, n}, Bk.Term.Lab{l}}) == t : Bk.Term}, +afs: D.AFs.ok(ds, fs),
  +hmem: N.Le(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), Nat.max(D.Mem.cells(st0), D.Need(ds, st0, t))),
  +hs: D.HS(ds, ks, img, m, nx, fi, im, [D.Rt{y, Bk.Term.Lab{l}}, D.Rt{x, Bk.Term.Mat{j, h, n}}], Nil{}, fs, sp, pend, Con{p0, ps0}),
  hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{y, Bk.Term.Lab{l}}, D.Rt{x, Bk.Term.Mat{j, h, n}}], Nil{}, sp, fs, Con{p0, ps0}, zs),
  +hl: {List.length(&2, U32, regs) == 63n : Nat},
  +h11: {List.get(&2, U32, regs, 11n) == Some{x} : Maybe<&2, U32>}, +h12: {List.get(&2, U32, regs, 12n) == Some{y} : Maybe<&2, U32>},
  +h14: {List.get(&2, U32, regs, 14n) == Some{Mc.Img.quan(q)} : Maybe<&2, U32>},
  +h2: {List.get(&2, U32, regs, 2n) == Some{sp} : Maybe<&2, U32>}, +h3: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>}) ->
  PB(ds, ks, img, st0, t, w, lim, Cr.Cir.exec(f, Mc.M.need(Mc.M.and(Mc.M.ne(Mc.M.g(Mc.R.q()), Mc.M.c(0)), Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.y())), Mc.M.c(Mc.T.lab()))), Mc.M.if(Mc.M.eq(Mc.M.f(2n, Mc.M.g(Mc.R.y())), Mc.M.f(2n, Mc.M.g(Mc.R.x()))), Mc.M.do([Mc.M.set(Mc.R.n(), Mc.M.f(3n, Mc.M.g(Mc.R.x()))), Mc.M.inc(Mc.R.n()), Mc.M.dec(Mc.R.y()), Mc.M.dec(Mc.R.x()), Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())), Mc.M.set(Mc.R.mode(), Mc.M.c(0))]), Mc.M.do([Mc.M.set(Mc.R.n(), Mc.M.f(4n, Mc.M.g(Mc.R.x()))), Mc.M.inc(Mc.R.n()), Mc.M.push(Mc.M.header(Mc.K.app_val(), Mc.M.g(Mc.R.q()), Mc.M.c(Mc.F.known())), Mc.M.g(Mc.R.y()), Mc.M.c(0)), Mc.M.dec(Mc.R.x()), Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())), Mc.M.set(Mc.R.mode(), Mc.M.c(0))]))), X.X.st(regs, m, nx, fi, im, pg, lim, inp))):
  +L = {Bk.Term.Lab{l} : Bk.Term}
  +isy = hs.r1(ds, ks, img, m, nx, fi, im, y, L, x, Bk.Term.Mat{j, h, n}, Nil{}, fs, sp, pend, Con{p0, ps0}, hs)
  +ev1 = {(%hlv : {Cr.Cir.eval(Mc.M.and(Mc.M.ne(Mc.M.g(Mc.R.q()), Mc.M.c(0)), Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.y())), Mc.M.c(Mc.T.lab()))), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) == Some{Bool.to_u32(Bool.and(_, True{}))} : Maybe<&2, U32>};
      ev.cnd(regs, m, nx, fi, im, pg, lim, inp, ds, ks, img, y, L, q, h12, h14, isy)) : {Cr.Cir.eval(Mc.M.and(Mc.M.ne(Mc.M.g(Mc.R.q()), Mc.M.c(0)), Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.y())), Mc.M.c(Mc.T.lab()))), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) == Some{1} : Maybe<&2, U32>}}
  %X.rw.if.t(f, Mc.M.and(Mc.M.ne(Mc.M.g(Mc.R.q()), Mc.M.c(0)), Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.y())), Mc.M.c(Mc.T.lab()))), Mc.M.if(Mc.M.eq(Mc.M.f(2n, Mc.M.g(Mc.R.y())), Mc.M.f(2n, Mc.M.g(Mc.R.x()))), Mc.M.do([Mc.M.set(Mc.R.n(), Mc.M.f(3n, Mc.M.g(Mc.R.x()))), Mc.M.inc(Mc.R.n()), Mc.M.dec(Mc.R.y()), Mc.M.dec(Mc.R.x()), Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())), Mc.M.set(Mc.R.mode(), Mc.M.c(0))]), Mc.M.do([Mc.M.set(Mc.R.n(), Mc.M.f(4n, Mc.M.g(Mc.R.x()))), Mc.M.inc(Mc.R.n()), Mc.M.push(Mc.M.header(Mc.K.app_val(), Mc.M.g(Mc.R.q()), Mc.M.c(Mc.F.known())), Mc.M.g(Mc.R.y()), Mc.M.c(0)), Mc.M.dec(Mc.R.x()), Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())), Mc.M.set(Mc.R.mode(), Mc.M.c(0))])), Mc.M.halt(2), X.X.st(regs, m, nx, fi, im, pg, lim, inp), 1, ev1, {==}) : PB(ds, ks, img, st0, t, w, lim, _)
  mat.names(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, j, h, n, y, q, l, U32.is_eq(D.Fd(2n, m, y), D.Fd(2n, m, x)), {==}, hlv, et0, afs, hmem, hs, hac, hl, h11, h12, h14, h2, h3)

# M.need and its branches, by the argument's form and q
def mat.go(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st0: Cr.Cir.State, +t: Bk.Term, +w: Nat, +lim: U32, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +inp: List<&2, Word(8n)>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32, +p0: U32, +ps0: List<&2, U32>, +zs: List<&2, D.Rt>,
  +x: U32, +j: List<&2, Word(8n)>, +h: Bk.Term, +n: Bk.Term, +y: U32, +q: Bk.Quan, +a: Bk.Term,
  +hva: {Bool.or(Bool.not(El.Quan.live(q)), El.Eval.vals(ds, a, False{})) == True{} : Bool},
  +et0: {D.A.plugs(fs, Bk.Term.App{q, Bk.Term.Mat{j, h, n}, a}) == t : Bk.Term}, +afs: D.AFs.ok(ds, fs),
  +hmem: N.Le(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), Nat.max(D.Mem.cells(st0), D.Need(ds, st0, t))),
  +hs: D.HS(ds, ks, img, m, nx, fi, im, [D.Rt{y, a}, D.Rt{x, Bk.Term.Mat{j, h, n}}], Nil{}, fs, sp, pend, Con{p0, ps0}),
  hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{y, a}, D.Rt{x, Bk.Term.Mat{j, h, n}}], Nil{}, sp, fs, Con{p0, ps0}, zs),
  +hl: {List.length(&2, U32, regs) == 63n : Nat},
  +h11: {List.get(&2, U32, regs, 11n) == Some{x} : Maybe<&2, U32>}, +h12: {List.get(&2, U32, regs, 12n) == Some{y} : Maybe<&2, U32>},
  +h14: {List.get(&2, U32, regs, 14n) == Some{Mc.Img.quan(q)} : Maybe<&2, U32>},
  +h2: {List.get(&2, U32, regs, 2n) == Some{sp} : Maybe<&2, U32>}, +h3: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>}) ->
  PB(ds, ks, img, st0, t, w, lim, Cr.Cir.exec(f, Mc.M.need(Mc.M.and(Mc.M.ne(Mc.M.g(Mc.R.q()), Mc.M.c(0)), Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.y())), Mc.M.c(Mc.T.lab()))), Mc.M.if(Mc.M.eq(Mc.M.f(2n, Mc.M.g(Mc.R.y())), Mc.M.f(2n, Mc.M.g(Mc.R.x()))), Mc.M.do([Mc.M.set(Mc.R.n(), Mc.M.f(3n, Mc.M.g(Mc.R.x()))), Mc.M.inc(Mc.R.n()), Mc.M.dec(Mc.R.y()), Mc.M.dec(Mc.R.x()), Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())), Mc.M.set(Mc.R.mode(), Mc.M.c(0))]), Mc.M.do([Mc.M.set(Mc.R.n(), Mc.M.f(4n, Mc.M.g(Mc.R.x()))), Mc.M.inc(Mc.R.n()), Mc.M.push(Mc.M.header(Mc.K.app_val(), Mc.M.g(Mc.R.q()), Mc.M.c(Mc.F.known())), Mc.M.g(Mc.R.y()), Mc.M.c(0)), Mc.M.dec(Mc.R.x()), Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())), Mc.M.set(Mc.R.mode(), Mc.M.c(0))]))), X.X.st(regs, m, nx, fi, im, pg, lim, inp))):
  match q:
    case Bk.Quan.Q0{}:
      mat.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, j, h, n, y, Bk.Quan.Q0{}, a, {==}, hva, et0, afs, hmem, hs, hac, hl, h11, h12, h14, h2, h3)
    case Bk.Quan.Q1{}:
      match a:
        case Bk.Term.Var{+i}:
          mat.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, j, h, n, y, Bk.Quan.Q1{}, Bk.Term.Var{i}, {==}, hva, et0, afs, hmem, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Ref{+i}:
          mat.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, j, h, n, y, Bk.Quan.Q1{}, Bk.Term.Ref{i}, {==}, hva, et0, afs, hmem, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Ann{+i0, +i1}:
          mat.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, j, h, n, y, Bk.Quan.Q1{}, Bk.Term.Ann{i0, i1}, {==}, hva, et0, afs, hmem, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Let{+i0, +i1, +i2}:
          mat.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, j, h, n, y, Bk.Quan.Q1{}, Bk.Term.Let{i0, i1, i2}, {==}, hva, et0, afs, hmem, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Typ{+i}:
          mat.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, j, h, n, y, Bk.Quan.Q1{}, Bk.Term.Typ{i}, {==}, hva, et0, afs, hmem, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Min{+i0, +i1}:
          mat.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, j, h, n, y, Bk.Quan.Q1{}, Bk.Term.Min{i0, i1}, {==}, hva, et0, afs, hmem, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.All{+i0, +i1, +i2}:
          mat.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, j, h, n, y, Bk.Quan.Q1{}, Bk.Term.All{i0, i1, i2}, {==}, hva, et0, afs, hmem, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Lam{+i0, +i1}:
          mat.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, j, h, n, y, Bk.Quan.Q1{}, Bk.Term.Lam{i0, i1}, {==}, hva, et0, afs, hmem, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.App{+i0, +i1, +i2}:
          mat.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, j, h, n, y, Bk.Quan.Q1{}, Bk.Term.App{i0, i1, i2}, {==}, hva, et0, afs, hmem, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Sig{+i0, +i1, +i2}:
          mat.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, j, h, n, y, Bk.Quan.Q1{}, Bk.Term.Sig{i0, i1, i2}, {==}, hva, et0, afs, hmem, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Tup{+i0, +i1, +i2}:
          mat.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, j, h, n, y, Bk.Quan.Q1{}, Bk.Term.Tup{i0, i1, i2}, {==}, hva, et0, afs, hmem, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Prj{+i}:
          mat.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, j, h, n, y, Bk.Quan.Q1{}, Bk.Term.Prj{i}, {==}, hva, et0, afs, hmem, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Enu{+i}:
          mat.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, j, h, n, y, Bk.Quan.Q1{}, Bk.Term.Enu{i}, {==}, hva, et0, afs, hmem, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Lab{+l}:
          mat.lv(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, j, h, n, y, Bk.Quan.Q1{}, l, {==}, et0, afs, hmem, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Mat{+i0, +i1, +i2}:
          mat.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, j, h, n, y, Bk.Quan.Q1{}, Bk.Term.Mat{i0, i1, i2}, {==}, hva, et0, afs, hmem, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Efq{}:
          mat.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, j, h, n, y, Bk.Quan.Q1{}, Bk.Term.Efq{}, {==}, hva, et0, afs, hmem, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Eql{+i0, +i1, +i2}:
          mat.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, j, h, n, y, Bk.Quan.Q1{}, Bk.Term.Eql{i0, i1, i2}, {==}, hva, et0, afs, hmem, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Rfl{}:
          mat.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, j, h, n, y, Bk.Quan.Q1{}, Bk.Term.Rfl{}, {==}, hva, et0, afs, hmem, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Rwt{+i0, +i1, +i2}:
          mat.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, j, h, n, y, Bk.Quan.Q1{}, Bk.Term.Rwt{i0, i1, i2}, {==}, hva, et0, afs, hmem, hs, hac, hl, h11, h12, h14, h2, h3)
    case Bk.Quan.Q2{}:
      match a:
        case Bk.Term.Var{+i}:
          mat.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, j, h, n, y, Bk.Quan.Q2{}, Bk.Term.Var{i}, {==}, hva, et0, afs, hmem, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Ref{+i}:
          mat.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, j, h, n, y, Bk.Quan.Q2{}, Bk.Term.Ref{i}, {==}, hva, et0, afs, hmem, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Ann{+i0, +i1}:
          mat.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, j, h, n, y, Bk.Quan.Q2{}, Bk.Term.Ann{i0, i1}, {==}, hva, et0, afs, hmem, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Let{+i0, +i1, +i2}:
          mat.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, j, h, n, y, Bk.Quan.Q2{}, Bk.Term.Let{i0, i1, i2}, {==}, hva, et0, afs, hmem, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Typ{+i}:
          mat.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, j, h, n, y, Bk.Quan.Q2{}, Bk.Term.Typ{i}, {==}, hva, et0, afs, hmem, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Min{+i0, +i1}:
          mat.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, j, h, n, y, Bk.Quan.Q2{}, Bk.Term.Min{i0, i1}, {==}, hva, et0, afs, hmem, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.All{+i0, +i1, +i2}:
          mat.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, j, h, n, y, Bk.Quan.Q2{}, Bk.Term.All{i0, i1, i2}, {==}, hva, et0, afs, hmem, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Lam{+i0, +i1}:
          mat.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, j, h, n, y, Bk.Quan.Q2{}, Bk.Term.Lam{i0, i1}, {==}, hva, et0, afs, hmem, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.App{+i0, +i1, +i2}:
          mat.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, j, h, n, y, Bk.Quan.Q2{}, Bk.Term.App{i0, i1, i2}, {==}, hva, et0, afs, hmem, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Sig{+i0, +i1, +i2}:
          mat.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, j, h, n, y, Bk.Quan.Q2{}, Bk.Term.Sig{i0, i1, i2}, {==}, hva, et0, afs, hmem, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Tup{+i0, +i1, +i2}:
          mat.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, j, h, n, y, Bk.Quan.Q2{}, Bk.Term.Tup{i0, i1, i2}, {==}, hva, et0, afs, hmem, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Prj{+i}:
          mat.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, j, h, n, y, Bk.Quan.Q2{}, Bk.Term.Prj{i}, {==}, hva, et0, afs, hmem, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Enu{+i}:
          mat.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, j, h, n, y, Bk.Quan.Q2{}, Bk.Term.Enu{i}, {==}, hva, et0, afs, hmem, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Lab{+l}:
          mat.lv(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, j, h, n, y, Bk.Quan.Q2{}, l, {==}, et0, afs, hmem, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Mat{+i0, +i1, +i2}:
          mat.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, j, h, n, y, Bk.Quan.Q2{}, Bk.Term.Mat{i0, i1, i2}, {==}, hva, et0, afs, hmem, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Efq{}:
          mat.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, j, h, n, y, Bk.Quan.Q2{}, Bk.Term.Efq{}, {==}, hva, et0, afs, hmem, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Eql{+i0, +i1, +i2}:
          mat.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, j, h, n, y, Bk.Quan.Q2{}, Bk.Term.Eql{i0, i1, i2}, {==}, hva, et0, afs, hmem, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Rfl{}:
          mat.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, j, h, n, y, Bk.Quan.Q2{}, Bk.Term.Rfl{}, {==}, hva, et0, afs, hmem, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Rwt{+i0, +i1, +i2}:
          mat.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, j, h, n, y, Bk.Quan.Q2{}, Bk.Term.Rwt{i0, i1, i2}, {==}, hva, et0, afs, hmem, hs, hac, hl, h11, h12, h14, h2, h3)

# M.redex, on a λ-match of labels
def mat.redex(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st0: Cr.Cir.State, +t: Bk.Term, +w: Nat, +lim: U32, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +inp: List<&2, Word(8n)>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32, +p0: U32, +ps0: List<&2, U32>, +zs: List<&2, D.Rt>,
  +x: U32, +j: List<&2, Word(8n)>, +h: Bk.Term, +n: Bk.Term, +y: U32, +q: Bk.Quan, +a: Bk.Term,
  +hva: {Bool.or(Bool.not(El.Quan.live(q)), El.Eval.vals(ds, a, False{})) == True{} : Bool},
  +et0: {D.A.plugs(fs, Bk.Term.App{q, Bk.Term.Mat{j, h, n}, a}) == t : Bk.Term}, +afs: D.AFs.ok(ds, fs),
  +hmem: N.Le(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), Nat.max(D.Mem.cells(st0), D.Need(ds, st0, t))),
  +hs: D.HS(ds, ks, img, m, nx, fi, im, [D.Rt{y, a}, D.Rt{x, Bk.Term.Mat{j, h, n}}], Nil{}, fs, sp, pend, Con{p0, ps0}),
  hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{y, a}, D.Rt{x, Bk.Term.Mat{j, h, n}}], Nil{}, sp, fs, Con{p0, ps0}, zs),
  +hl: {List.length(&2, U32, regs) == 63n : Nat},
  +h11: {List.get(&2, U32, regs, 11n) == Some{x} : Maybe<&2, U32>}, +h12: {List.get(&2, U32, regs, 12n) == Some{y} : Maybe<&2, U32>},
  +h14: {List.get(&2, U32, regs, 14n) == Some{Mc.Img.quan(q)} : Maybe<&2, U32>},
  +h2: {List.get(&2, U32, regs, 2n) == Some{sp} : Maybe<&2, U32>}, +h3: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>}) ->
  PB(ds, ks, img, st0, t, w, lim, Cr.Cir.exec(f, Mc.M.redex(), X.X.st(regs, m, nx, fi, im, pg, lim, inp))):
  +isx = hs.r2(ds, ks, img, m, nx, fi, im, y, a, x, Bk.Term.Mat{j, h, n}, Nil{}, fs, sp, pend, Con{p0, ps0}, hs)
  %mat.sel(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, x, j, h, n, h11, isx) : PB(ds, ks, img, st0, t, w, lim, _)
  mat.go(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, j, h, n, y, q, a, hva, et0, afs, hmem, hs, hac, hl, h11, h12, h14, h2, h3)

# The moves
# ---------
#
# mv.ret.app.mat and mv.ret.fun.mat: M.ret takes the frame's branch, M.pop
# moves it to the pend list (hsk.pop, acc.pop), and M.redex runs on the
# λ-match x and the argument y (mat.redex); the round from mode 1 ends
# with fuel 0, as M.redex's λ-match branch has no while (ends.nw).

# the top frame's facts (Frs)
def fr.z(-ds: List<&2, Bk.Def>, -m: Cr.Cir.Cells, -im: U32, -fi: U32, -nx: U32, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -ps: List<&2, U32>, -sp: U32, -kind: D.FK, -q: Bk.Quan, -k: Bool, -a: Bk.Term, -b: Bk.Term, -fs: List<&2, D.AF>,
  frs: D.Frs(ds, m, im, fi, nx, ks, img, ps, sp, Con{D.AF{kind, q, k, a, b}, fs})) ->
  {U32.is_eq(sp, 0) == False{} : Bool}:
  match frs:
    case Tuple{e, _}:
      e
def fr.c(-ds: List<&2, Bk.Def>, -m: Cr.Cir.Cells, -im: U32, -fi: U32, -nx: U32, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -ps: List<&2, U32>, -sp: U32, -kind: D.FK, -q: Bk.Quan, -k: Bool, -a: Bk.Term, -b: Bk.Term, -fs: List<&2, D.AF>,
  frs: D.Frs(ds, m, im, fi, nx, ks, img, ps, sp, Con{D.AF{kind, q, k, a, b}, fs})) ->
  {Cr.Cir.is_cell(sp, im, fi, nx) == True{} : Bool}:
  match frs:
    case Tuple{_, Tuple{e, _}}:
      e
def fr.t(-ds: List<&2, Bk.Def>, -m: Cr.Cir.Cells, -im: U32, -fi: U32, -nx: U32, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -ps: List<&2, U32>, -sp: U32, -kind: D.FK, -q: Bk.Quan, -k: Bool, -a: Bk.Term, -b: Bk.Term, -fs: List<&2, D.AF>,
  frs: D.Frs(ds, m, im, fi, nx, ks, img, ps, sp, Con{D.AF{kind, q, k, a, b}, fs})) ->
  {D.Tg(m, sp) == D.FK.tag(kind) : U32}:
  match frs:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}:
      e
def fr.q(-ds: List<&2, Bk.Def>, -m: Cr.Cir.Cells, -im: U32, -fi: U32, -nx: U32, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -ps: List<&2, U32>, -sp: U32, -kind: D.FK, -q: Bk.Quan, -k: Bool, -a: Bk.Term, -b: Bk.Term, -fs: List<&2, D.AF>,
  frs: D.Frs(ds, m, im, fi, nx, ks, img, ps, sp, Con{D.AF{kind, q, k, a, b}, fs})) ->
  D.Qs(Cr.Cir.Cells.get(m, sp), q):
  match frs:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}:
      e
def fr.k(-ds: List<&2, Bk.Def>, -m: Cr.Cir.Cells, -im: U32, -fi: U32, -nx: U32, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -ps: List<&2, U32>, -sp: U32, -kind: D.FK, -q: Bk.Quan, -k: Bool, -a: Bk.Term, -b: Bk.Term, -fs: List<&2, D.AF>,
  frs: D.Frs(ds, m, im, fi, nx, ks, img, ps, sp, Con{D.AF{kind, q, k, a, b}, fs})) ->
  {D.Fl(m, sp, 2048) == k : Bool}:
  match frs:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}:
      e

# the registers when M.redex starts
def pre.l(+regs: List<&2, U32>, +m: Cr.Cir.Cells, +sp: U32, +T: U32, +vx: U32, +vy: U32, +hl: {List.length(&2, U32, regs) == 63n : Nat}) -> {List.length(&2, U32, R.pre(regs, m, sp, T, vx, vy)) == 63n : Nat}:
  X.L.len(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(regs, 9n, sp), 10n, T), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, vx), 12n, vy), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp, 63n, X.L.len(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(regs, 9n, sp), 10n, T), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, vx), 12n, vy), 16n, sp), 2n, D.Fd(1n, m, sp), 63n, X.L.len(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(regs, 9n, sp), 10n, T), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, vx), 12n, vy), 16n, sp, 63n, X.L.len(X.X.set(X.X.set(X.X.set(X.X.set(regs, 9n, sp), 10n, T), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, vx), 12n, vy, 63n, X.L.len(X.X.set(X.X.set(X.X.set(regs, 9n, sp), 10n, T), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, vx, 63n, X.L.len(X.X.set(X.X.set(regs, 9n, sp), 10n, T), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3), 63n, X.L.len(X.X.set(regs, 9n, sp), 10n, T, 63n, X.L.len(regs, 9n, sp, 63n, hl))))))))

def pre.r11(+regs: List<&2, U32>, +m: Cr.Cir.Cells, +sp: U32, +T: U32, +vx: U32, +vy: U32, +hl: {List.length(&2, U32, regs) == 63n : Nat}) -> {List.get(&2, U32, R.pre(regs, m, sp, T, vx, vy), 11n) == Some{vx} : Maybe<&2, U32>}:
  X.L.go(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(regs, 9n, sp), 10n, T), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, vx), 12n, vy), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, 11n, sp, vx, {==}, X.L.go(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(regs, 9n, sp), 10n, T), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, vx), 12n, vy), 16n, sp), 2n, 11n, D.Fd(1n, m, sp), vx, {==}, X.L.go(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(regs, 9n, sp), 10n, T), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, vx), 12n, vy), 16n, 11n, sp, vx, {==}, X.L.go(X.X.set(X.X.set(X.X.set(X.X.set(regs, 9n, sp), 10n, T), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, vx), 12n, 11n, vy, vx, {==}, X.L.gs(X.X.set(X.X.set(X.X.set(regs, 9n, sp), 10n, T), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, vx, X.L.lt(X.X.set(X.X.set(X.X.set(regs, 9n, sp), 10n, T), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, X.L.len(X.X.set(X.X.set(regs, 9n, sp), 10n, T), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3), 63n, X.L.len(X.X.set(regs, 9n, sp), 10n, T, 63n, X.L.len(regs, 9n, sp, 63n, hl))), {==}))))))

def pre.r12(+regs: List<&2, U32>, +m: Cr.Cir.Cells, +sp: U32, +T: U32, +vx: U32, +vy: U32, +hl: {List.length(&2, U32, regs) == 63n : Nat}) -> {List.get(&2, U32, R.pre(regs, m, sp, T, vx, vy), 12n) == Some{vy} : Maybe<&2, U32>}:
  X.L.go(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(regs, 9n, sp), 10n, T), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, vx), 12n, vy), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, 12n, sp, vy, {==}, X.L.go(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(regs, 9n, sp), 10n, T), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, vx), 12n, vy), 16n, sp), 2n, 12n, D.Fd(1n, m, sp), vy, {==}, X.L.go(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(regs, 9n, sp), 10n, T), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, vx), 12n, vy), 16n, 12n, sp, vy, {==}, X.L.gs(X.X.set(X.X.set(X.X.set(X.X.set(regs, 9n, sp), 10n, T), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, vx), 12n, vy, X.L.lt(X.X.set(X.X.set(X.X.set(X.X.set(regs, 9n, sp), 10n, T), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, vx), 12n, X.L.len(X.X.set(X.X.set(X.X.set(regs, 9n, sp), 10n, T), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, vx, 63n, X.L.len(X.X.set(X.X.set(regs, 9n, sp), 10n, T), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3), 63n, X.L.len(X.X.set(regs, 9n, sp), 10n, T, 63n, X.L.len(regs, 9n, sp, 63n, hl)))), {==})))))

def pre.r14(+regs: List<&2, U32>, +m: Cr.Cir.Cells, +sp: U32, +T: U32, +vx: U32, +vy: U32, +hl: {List.length(&2, U32, regs) == 63n : Nat}) -> {List.get(&2, U32, R.pre(regs, m, sp, T, vx, vy), 14n) == Some{U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)} : Maybe<&2, U32>}:
  X.L.go(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(regs, 9n, sp), 10n, T), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, vx), 12n, vy), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, 14n, sp, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3), {==}, X.L.go(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(regs, 9n, sp), 10n, T), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, vx), 12n, vy), 16n, sp), 2n, 14n, D.Fd(1n, m, sp), U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3), {==}, X.L.go(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(regs, 9n, sp), 10n, T), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, vx), 12n, vy), 16n, 14n, sp, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3), {==}, X.L.go(X.X.set(X.X.set(X.X.set(X.X.set(regs, 9n, sp), 10n, T), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, vx), 12n, 14n, vy, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3), {==}, X.L.go(X.X.set(X.X.set(X.X.set(regs, 9n, sp), 10n, T), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, 14n, vx, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3), {==}, X.L.gs(X.X.set(X.X.set(regs, 9n, sp), 10n, T), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3), X.L.lt(X.X.set(X.X.set(regs, 9n, sp), 10n, T), 14n, X.L.len(X.X.set(regs, 9n, sp), 10n, T, 63n, X.L.len(regs, 9n, sp, 63n, hl)), {==})))))))

def pre.r2(+regs: List<&2, U32>, +m: Cr.Cir.Cells, +sp: U32, +T: U32, +vx: U32, +vy: U32, +hl: {List.length(&2, U32, regs) == 63n : Nat}) -> {List.get(&2, U32, R.pre(regs, m, sp, T, vx, vy), 2n) == Some{D.Fd(1n, m, sp)} : Maybe<&2, U32>}:
  X.L.go(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(regs, 9n, sp), 10n, T), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, vx), 12n, vy), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, 2n, sp, D.Fd(1n, m, sp), {==}, X.L.gs(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(regs, 9n, sp), 10n, T), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, vx), 12n, vy), 16n, sp), 2n, D.Fd(1n, m, sp), X.L.lt(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(regs, 9n, sp), 10n, T), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, vx), 12n, vy), 16n, sp), 2n, X.L.len(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(regs, 9n, sp), 10n, T), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, vx), 12n, vy), 16n, sp, 63n, X.L.len(X.X.set(X.X.set(X.X.set(X.X.set(regs, 9n, sp), 10n, T), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, vx), 12n, vy, 63n, X.L.len(X.X.set(X.X.set(X.X.set(regs, 9n, sp), 10n, T), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, vx, 63n, X.L.len(X.X.set(X.X.set(regs, 9n, sp), 10n, T), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3), 63n, X.L.len(X.X.set(regs, 9n, sp), 10n, T, 63n, X.L.len(regs, 9n, sp, 63n, hl)))))), {==})))

def pre.r3(+regs: List<&2, U32>, +m: Cr.Cir.Cells, +sp: U32, +T: U32, +vx: U32, +vy: U32, +hl: {List.length(&2, U32, regs) == 63n : Nat}) -> {List.get(&2, U32, R.pre(regs, m, sp, T, vx, vy), 3n) == Some{sp} : Maybe<&2, U32>}:
  X.L.gs(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(regs, 9n, sp), 10n, T), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, vx), 12n, vy), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp, X.L.lt(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(regs, 9n, sp), 10n, T), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, vx), 12n, vy), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, X.L.len(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(regs, 9n, sp), 10n, T), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, vx), 12n, vy), 16n, sp), 2n, D.Fd(1n, m, sp), 63n, X.L.len(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(regs, 9n, sp), 10n, T), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, vx), 12n, vy), 16n, sp, 63n, X.L.len(X.X.set(X.X.set(X.X.set(X.X.set(regs, 9n, sp), 10n, T), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, vx), 12n, vy, 63n, X.L.len(X.X.set(X.X.set(X.X.set(regs, 9n, sp), 10n, T), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, vx, 63n, X.L.len(X.X.set(X.X.set(regs, 9n, sp), 10n, T), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3), 63n, X.L.len(X.X.set(regs, 9n, sp), 10n, T, 63n, X.L.len(regs, 9n, sp, 63n, hl))))))), {==}))

# q's register, from the frame's quantity
def pre.q(+regs: List<&2, U32>, +m: Cr.Cir.Cells, +sp: U32, +T: U32, +vx: U32, +vy: U32, +hl: {List.length(&2, U32, regs) == 63n : Nat}, +q: Bk.Quan, hq: D.Qs(Cr.Cir.Cells.get(m, sp), q)) ->
  {List.get(&2, U32, R.pre(regs, m, sp, T, vx, vy), 14n) == Some{Mc.Img.quan(q)} : Maybe<&2, U32>}:
  %hq : {List.get(&2, U32, R.pre(regs, m, sp, T, vx, vy), 14n) == Some{_} : Maybe<&2, U32>}
  pre.r14(regs, m, sp, T, vx, vy, hl)

# App q □ a with q dead or a known: a is a value when q is live
def hva.of(lq: Bool, k: Bool, va: Bool, hs: {Bool.and(lq, Bool.not(k)) == False{} : Bool},
  ho: {Bool.or(Bool.not(k), va) == True{} : Bool}) -> {Bool.or(Bool.not(lq), va) == True{} : Bool}:
  match lq k:
    case True{} True{}:
      ho
    case True{} False{}:
      D.bool.ft({Bool.or(Bool.not(True{}), va) == True{} : Bool}, Equal.sym(Bool, True{}, False{}, hs))
    case False{} _:
      {==}

def mat.app.mv(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +j: List<&2, Word(8n)>, +h: Bk.Term, +n: Bk.Term, +kind: D.FK, +q: Bk.Quan, +k: Bool, +a: Bk.Term, +b: Bk.Term, +zs: List<&2, D.Rt>,
  +et0: {D.A.plugs(fs, Bk.Term.App{q, Bk.Term.Mat{j, h, n}, a}) == t : Bk.Term},
  +hok: {Bool.or(Bool.not(k), El.Eval.vals(ds, a, False{})) == True{} : Bool},
  +h38: {U32.is_eq(D.FK.tag(kind), 38) == False{} : Bool}, +hk: {K.FK.isapp(kind) == True{} : Bool},
  +hsq: {Bool.and(El.Quan.live(q), Bool.not(k)) == False{} : Bool}, +afs: D.AFs.ok(ds, fs),
  +isf: D.Is(ds, m, im, fi, nx, ks, img, foc, Bk.Term.Mat{j, h, n}), +frs: D.Frs(ds, m, im, fi, nx, ks, img, ps, sp, Con{D.AF{kind, q, k, a, b}, fs}),
  +hp: D.Heap(m, nx, fi, im, [foc], pend, ps), +io2: D.ImgOK(ds, ks, img, m, im, fi, nx),
  +hac0: D.AccK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{foc, Bk.Term.Mat{j, h, n}}], Nil{}, sp, Con{D.AF{kind, q, k, a, b}, fs}, ps, zs)) ->
  K.MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  (+f => (%pre.app(f, kind, rest, foc, sp, pend, m, nx, fi, im, pg, lim, inp, q, k, hk, hsq, fr.z(ds, m, im, fi, nx, ks, img, ps, sp, kind, q, k, a, b, fs, frs), fr.c(ds, m, im, fi, nx, ks, img, ps, sp, kind, q, k, a, b, fs, frs), fr.t(ds, m, im, fi, nx, ks, img, ps, sp, kind, q, k, a, b, fs, frs), fr.q(ds, m, im, fi, nx, ks, img, ps, sp, kind, q, k, a, b, fs, frs), fr.k(ds, m, im, fi, nx, ks, img, ps, sp, kind, q, k, a, b, fs, frs)) : PB(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, lim, _);
      mat.redex(f, ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, lim, R.pre(D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, sp, D.FK.tag(kind), foc, D.Fd(2n, m, sp)), M1(m, sp, pend), nx, fi, im, pg, inp, fs, D.Fd(1n, m, sp), sp, sp, ps, zs,
        foc, j, h, n, D.Fd(2n, m, sp), q, a, hva.of(El.Quan.live(q), k, El.Eval.vals(ds, a, False{}), hsq, hok), et0, afs, le.max.l(D.Mem.cells(D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)), D.Need(ds, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t)), hsk.pop(ds, ks, img, m, nx, fi, im, Bk.Term.Mat{j, h, n}, fs, foc, sp, pend, ps, kind, q, k, a, b, h38, isf, hp, io2, frs), acc.pop(ds, ks, img, m, nx, fi, im, Bk.Term.Mat{j, h, n}, fs, foc, sp, pend, ps, kind, q, k, a, b, zs, h38, frs, hac0),
        pre.l(D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, sp, D.FK.tag(kind), foc, D.Fd(2n, m, sp), rg.len(rest, foc, 1, sp, pend)), pre.r11(D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, sp, D.FK.tag(kind), foc, D.Fd(2n, m, sp), rg.len(rest, foc, 1, sp, pend)), pre.r12(D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, sp, D.FK.tag(kind), foc, D.Fd(2n, m, sp), rg.len(rest, foc, 1, sp, pend)), pre.q(D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, sp, D.FK.tag(kind), foc, D.Fd(2n, m, sp), rg.len(rest, foc, 1, sp, pend), q, fr.q(ds, m, im, fi, nx, ks, img, ps, sp, kind, q, k, a, b, fs, frs)), pre.r2(D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, sp, D.FK.tag(kind), foc, D.Fd(2n, m, sp), rg.len(rest, foc, 1, sp, pend)), pre.r3(D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, sp, D.FK.tag(kind), foc, D.Fd(2n, m, sp), rg.len(rest, foc, 1, sp, pend)))),
    (0n, (%pre.app(0n, kind, rest, foc, sp, pend, m, nx, fi, im, pg, lim, inp, q, k, hk, hsq, fr.z(ds, m, im, fi, nx, ks, img, ps, sp, kind, q, k, a, b, fs, frs), fr.c(ds, m, im, fi, nx, ks, img, ps, sp, kind, q, k, a, b, fs, frs), fr.t(ds, m, im, fi, nx, ks, img, ps, sp, kind, q, k, a, b, fs, frs), fr.q(ds, m, im, fi, nx, ks, img, ps, sp, kind, q, k, a, b, fs, frs), fr.k(ds, m, im, fi, nx, ks, img, ps, sp, kind, q, k, a, b, fs, frs)) : D.Ends(_);
      %mat.sel(0n, ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, lim, R.pre(D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, sp, D.FK.tag(kind), foc, D.Fd(2n, m, sp)), M1(m, sp, pend), nx, fi, im, pg, inp, foc, j, h, n, pre.r11(D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, sp, D.FK.tag(kind), foc, D.Fd(2n, m, sp), rg.len(rest, foc, 1, sp, pend)), hs.r2(ds, ks, img, M1(m, sp, pend), nx, fi, im, D.Fd(2n, m, sp), a, foc, Bk.Term.Mat{j, h, n}, Nil{}, fs, D.Fd(1n, m, sp), sp, Con{sp, ps}, hsk.pop(ds, ks, img, m, nx, fi, im, Bk.Term.Mat{j, h, n}, fs, foc, sp, pend, ps, kind, q, k, a, b, h38, isf, hp, io2, frs))) : D.Ends(_);
      ends.nw(0n, X.sel.t(X.sel.e(X.sel.e(Mc.M.redex()))), X.X.st(R.pre(D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, sp, D.FK.tag(kind), foc, D.Fd(2n, m, sp)), M1(m, sp, pend), nx, fi, im, pg, lim, inp), {==}))))

def mat.fun.mv(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +j: List<&2, Word(8n)>, +h: Bk.Term, +n: Bk.Term, +q: Bk.Quan, +k: Bool, +v: Bk.Term, +b: Bk.Term, +zs: List<&2, D.Rt>,
  +et0: {D.A.plugs(fs, Bk.Term.App{q, Bk.Term.Mat{j, h, n}, v}) == t : Bk.Term},
  +evv: {El.Eval.vals(ds, v, False{}) == True{} : Bool}, +afs: D.AFs.ok(ds, fs),
  +isf: D.Is(ds, m, im, fi, nx, ks, img, foc, v), +frs: D.Frs(ds, m, im, fi, nx, ks, img, ps, sp, Con{D.AF{D.FK.fun{}, q, k, Bk.Term.Mat{j, h, n}, b}, fs}),
  +hp: D.Heap(m, nx, fi, im, [foc], pend, ps), +io2: D.ImgOK(ds, ks, img, m, im, fi, nx),
  +hac0: D.AccK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{foc, v}], Nil{}, sp, Con{D.AF{D.FK.fun{}, q, k, Bk.Term.Mat{j, h, n}, b}, fs}, ps, zs)) ->
  K.MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  (+f => (%pre.fun(f, rest, foc, sp, pend, m, nx, fi, im, pg, lim, inp, fr.z(ds, m, im, fi, nx, ks, img, ps, sp, D.FK.fun{}, q, k, Bk.Term.Mat{j, h, n}, b, fs, frs), fr.c(ds, m, im, fi, nx, ks, img, ps, sp, D.FK.fun{}, q, k, Bk.Term.Mat{j, h, n}, b, fs, frs), fr.t(ds, m, im, fi, nx, ks, img, ps, sp, D.FK.fun{}, q, k, Bk.Term.Mat{j, h, n}, b, fs, frs)) : PB(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, lim, _);
      mat.redex(f, ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, lim, R.pre(D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, sp, 34, D.Fd(2n, m, sp), foc), M1(m, sp, pend), nx, fi, im, pg, inp, fs, D.Fd(1n, m, sp), sp, sp, ps, zs,
        D.Fd(2n, m, sp), j, h, n, foc, q, v, D.or.r(Bool.not(El.Quan.live(q)), El.Eval.vals(ds, v, False{}), evv), et0, afs, le.max.l(D.Mem.cells(D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)), D.Need(ds, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t)), hsk.swap(ds, ks, img, M1(m, sp, pend), nx, fi, im, D.Fd(2n, m, sp), Bk.Term.Mat{j, h, n}, foc, v, Nil{}, fs, D.Fd(1n, m, sp), sp, Con{sp, ps}, hsk.pop(ds, ks, img, m, nx, fi, im, v, fs, foc, sp, pend, ps, D.FK.fun{}, q, k, Bk.Term.Mat{j, h, n}, b, {==}, isf, hp, io2, frs)), acc.swap(ds, ks, img, M1(m, sp, pend), nx, fi, im, D.Rt{D.Fd(2n, m, sp), Bk.Term.Mat{j, h, n}}, D.Rt{foc, v}, Nil{}, D.Fd(1n, m, sp), fs, Con{sp, ps}, zs, acc.pop(ds, ks, img, m, nx, fi, im, v, fs, foc, sp, pend, ps, D.FK.fun{}, q, k, Bk.Term.Mat{j, h, n}, b, zs, {==}, frs, hac0)),
        pre.l(D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, sp, 34, D.Fd(2n, m, sp), foc, rg.len(rest, foc, 1, sp, pend)), pre.r11(D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, sp, 34, D.Fd(2n, m, sp), foc, rg.len(rest, foc, 1, sp, pend)), pre.r12(D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, sp, 34, D.Fd(2n, m, sp), foc, rg.len(rest, foc, 1, sp, pend)), pre.q(D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, sp, 34, D.Fd(2n, m, sp), foc, rg.len(rest, foc, 1, sp, pend), q, fr.q(ds, m, im, fi, nx, ks, img, ps, sp, D.FK.fun{}, q, k, Bk.Term.Mat{j, h, n}, b, fs, frs)), pre.r2(D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, sp, 34, D.Fd(2n, m, sp), foc, rg.len(rest, foc, 1, sp, pend)), pre.r3(D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, sp, 34, D.Fd(2n, m, sp), foc, rg.len(rest, foc, 1, sp, pend)))),
    (0n, (%pre.fun(0n, rest, foc, sp, pend, m, nx, fi, im, pg, lim, inp, fr.z(ds, m, im, fi, nx, ks, img, ps, sp, D.FK.fun{}, q, k, Bk.Term.Mat{j, h, n}, b, fs, frs), fr.c(ds, m, im, fi, nx, ks, img, ps, sp, D.FK.fun{}, q, k, Bk.Term.Mat{j, h, n}, b, fs, frs), fr.t(ds, m, im, fi, nx, ks, img, ps, sp, D.FK.fun{}, q, k, Bk.Term.Mat{j, h, n}, b, fs, frs)) : D.Ends(_);
      %mat.sel(0n, ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, lim, R.pre(D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, sp, 34, D.Fd(2n, m, sp), foc), M1(m, sp, pend), nx, fi, im, pg, inp, D.Fd(2n, m, sp), j, h, n, pre.r11(D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, sp, 34, D.Fd(2n, m, sp), foc, rg.len(rest, foc, 1, sp, pend)), hs.r2(ds, ks, img, M1(m, sp, pend), nx, fi, im, foc, v, D.Fd(2n, m, sp), Bk.Term.Mat{j, h, n}, Nil{}, fs, D.Fd(1n, m, sp), sp, Con{sp, ps}, hsk.swap(ds, ks, img, M1(m, sp, pend), nx, fi, im, D.Fd(2n, m, sp), Bk.Term.Mat{j, h, n}, foc, v, Nil{}, fs, D.Fd(1n, m, sp), sp, Con{sp, ps}, hsk.pop(ds, ks, img, m, nx, fi, im, v, fs, foc, sp, pend, ps, D.FK.fun{}, q, k, Bk.Term.Mat{j, h, n}, b, {==}, isf, hp, io2, frs)))) : D.Ends(_);
      ends.nw(0n, X.sel.t(X.sel.e(X.sel.e(Mc.M.redex()))), X.X.st(R.pre(D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, sp, 34, D.Fd(2n, m, sp), foc), M1(m, sp, pend), nx, fi, im, pg, lim, inp), {==}))))
# The room of a round
# -------------------
#
# After U10 (moves_push.bend): a new cell fits in Budget when it fits in
# Need (budget.of), and the own cells after the pushes stay within the
# round's peak (peak.fin).

def le.max(a: Nat, +b: Nat) -> N.Le(a, Nat.max(a, b)):
  match a:
    case 0n:
      N.le_zero(b)
    case 1n+p:
      match b:
        case 0n:
          N.le_refl(1n+p)
        case 1n+q:
          le.max(p, q)

def le.max.r(a: Nat, +b: Nat) -> N.Le(b, Nat.max(a, b)):
  match a:
    case 0n:
      N.le_refl(b)
    case 1n+p:
      match b:
        case 0n:
          N.le_zero(1n+p)
        case 1n+q:
          le.max.r(p, q)

def sub.mono(c: Nat, a: Nat, b: Nat, h: N.Le(a, b)) -> N.Le(Nat.sub(a, c), Nat.sub(b, c)):
  match c:
    case 0n:
      match a:
        case 0n:
          N.le_zero(Nat.sub(b, 0n))
        case 1n+ap:
          match b:
            case 0n:
              Empty.absurd(N.Le(1n+ap, 0n), h)
            case 1n+bp:
              h
    case 1n+cp:
      match a:
        case 0n:
          N.le_zero(Nat.sub(b, 1n+cp))
        case 1n+ap:
          match b:
            case 0n:
              Empty.absurd(N.Le(Nat.sub(1n+ap, 1n+cp), Nat.sub(0n, 1n+cp)), h)
            case 1n+bp:
              sub.mono(cp, ap, bp, h)

def sub.succ(c: Nat, n: Nat) -> N.Le(Nat.sub(1n+n, c), 1n+Nat.sub(n, c)):
  match c:
    case 0n:
      match n:
        case 0n:
          Unit{}
        case 1n+p:
          N.le_refl(1n+p)
    case 1n+cp:
      match n:
        case 0n:
          N.le_zero(1n+Nat.sub(0n, 1n+cp))
        case 1n+p:
          sub.succ(cp, p)

def peak.fin(+ds: List<&2, Bk.Def>, +st0: Cr.Cir.State, +t: Bk.Term, +nx: U32, +nx3: U32, +fi: U32, +ps: List<&2, U32>,
  hmc: {D.Mem.cells(st0) == Nat.sub(U32.to_nat(nx), U32.to_nat(fi)) : Nat},
  hnd: {D.Pend.none(ps) == True{} : Bool} -> N.Le(1n+Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), D.Need(ds, st0, t)),
  hn: {Bool.or(U32.is_eq(nx3, nx), Bool.and(D.Pend.none(ps), U32.is_eq(nx3, U32.inc(nx)))) == True{} : Bool}) ->
  N.Le(Nat.sub(U32.to_nat(nx3), U32.to_nat(fi)), Nat.max(D.Mem.cells(st0), D.Need(ds, st0, t))):
  +MX = Nat.max(D.Mem.cells(st0), D.Need(ds, st0, t))
  D.or.cases(U32.is_eq(nx3, nx), Bool.and(D.Pend.none(ps), U32.is_eq(nx3, U32.inc(nx))),
    N.Le(Nat.sub(U32.to_nat(nx3), U32.to_nat(fi)), MX), hn,
    e => (%Equal.sym(U32, nx3, nx, D.u32.eq(nx3, nx, e)) : N.Le(Nat.sub(U32.to_nat(_), U32.to_nat(fi)), MX);
      %hmc : N.Le(_, MX);
      le.max(D.Mem.cells(st0), D.Need(ds, st0, t))),
    +e => (%Equal.sym(U32, nx3, U32.inc(nx), D.u32.eq(nx3, U32.inc(nx), D.and.r(D.Pend.none(ps), U32.is_eq(nx3, U32.inc(nx)), e))) :
        N.Le(Nat.sub(U32.to_nat(_), U32.to_nat(fi)), MX);
      N.le_trans(Nat.sub(U32.to_nat(U32.inc(nx)), U32.to_nat(fi)), 1n+Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), MX,
        N.le_trans(Nat.sub(U32.to_nat(U32.inc(nx)), U32.to_nat(fi)), Nat.sub(1n+U32.to_nat(nx), U32.to_nat(fi)),
          1n+Nat.sub(U32.to_nat(nx), U32.to_nat(fi)),
          sub.mono(U32.to_nat(fi), U32.to_nat(U32.inc(nx)), 1n+U32.to_nat(nx), N.U32.inc_le(nx)), sub.succ(U32.to_nat(fi), U32.to_nat(nx))),
        N.le_trans(1n+Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), D.Need(ds, st0, t), MX,
          hnd(D.and.l(D.Pend.none(ps), U32.is_eq(nx3, U32.inc(nx)), e)), le.max.r(D.Mem.cells(st0), D.Need(ds, st0, t))))))

def budget.of(+nx: U32, +fi: U32, +Nd: Nat, +T: Nat, +Y: Nat, hn: N.Le(1n+Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), Nd),
  hf: N.Le(U32.to_nat(fi), U32.to_nat(nx))) ->
  N.Le(Nat.mul(20n, Nat.add(U32.to_nat(nx), 1n)), Nat.max(Nat.add(Nat.mul(20n, Nat.add(U32.to_nat(fi), Nd)), T), Y)):
  +F = U32.to_nat(fi)
  +X = U32.to_nat(nx)
  +n = Nat.sub(X, F)
  +e1 = Equal.trans(Nat, Nat.add(n, 1n), 1n+Nat.add(n, 0n), 1n+n, N.add_succ_r(n, 0n), Equal.cong(Nat, Nat, z => 1n+z, Nat.add(n, 0n), n, N.add_zero(n)))
  +e2 = Equal.trans(Nat, Nat.add(F, 1n+n), Nat.add(F, Nat.add(n, 1n)), Nat.add(X, 1n),
    Equal.cong(Nat, Nat, z => Nat.add(F, z), 1n+n, Nat.add(n, 1n), Equal.sym(Nat, Nat.add(n, 1n), 1n+n, e1)),
    Equal.trans(Nat, Nat.add(F, Nat.add(n, 1n)), Nat.add(Nat.add(F, n), 1n), Nat.add(X, 1n),
      Equal.sym(Nat, Nat.add(Nat.add(F, n), 1n), Nat.add(F, Nat.add(n, 1n)), add.assoc(F, n, 1n)),
      Equal.cong(Nat, Nat, z => Nat.add(z, 1n), Nat.add(F, n), X, D.add.sub(F, X, hf))))
  +h1 = N.le_rw_l(Nat.add(F, 1n+n), Nat.add(X, 1n), Nat.add(F, Nd), e2, N.add_mono(F, F, 1n+n, Nd, N.le_refl(F), hn))
  N.le_trans(Nat.mul(20n, Nat.add(X, 1n)), Nat.add(Nat.mul(20n, Nat.add(F, Nd)), T), Nat.max(Nat.add(Nat.mul(20n, Nat.add(F, Nd)), T), Y),
    N.le_trans(Nat.mul(20n, Nat.add(X, 1n)), Nat.mul(20n, Nat.add(F, Nd)), Nat.add(Nat.mul(20n, Nat.add(F, Nd)), T),
      N.mul_mono_r(20n, Nat.add(X, 1n), Nat.add(F, Nd), h1), N.le_add_r(Nat.mul(20n, Nat.add(F, Nd)), T)),
    le.max(Nat.add(Nat.mul(20n, Nat.add(F, Nd)), T), Y))

def heap.finx(-m: Cr.Cir.Cells, -nx: U32, -fi: U32, -im: U32, -rs: List<&2, U32>, -pend: U32, -ps: List<&2, U32>,
  h: D.Heap(m, nx, fi, im, rs, pend, ps)) -> {U32.is_le(fi, nx) == True{} : Bool}:
  match h:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, e}}}}}:
      e

# The room of the second push of a λ-match of pairs
# ------------------------------------------------
#
# After the first push, with no pending cell, the own cells are at most
# STATIC ones and the nodes of the roots and the frames (acc.count): those
# of t, and the pair's fields once more (a1 + a2 < A <= t). So a new cell
# fits in Need, which counts the larger of t and its step twice (arith.prj).

# the roots' and frames' nodes after the first push: the pair's fields, and
# the core C of t (the pair A, the λ-match P, the frames' terms and cells)
def arith.w(+a1: Nat, +a2: Nat, +P: Nat, +R2: Nat, +R: Nat, +L2: Nat, +L: Nat, eR: {R2 == R : Nat}, eL: {L2 == L : Nat}) ->
  {Nat.add(Nat.add(a1, Nat.add(1n+Nat.add(a1, a2), Nat.add(P, 0n))), Nat.add(0n, Nat.add(Nat.add(a2, R2), Nat.add(1n+L2, 0n)))) ==
    Nat.add(Nat.add(a1, a2), Nat.add(1n+Nat.add(a1, a2), Nat.add(P, Nat.add(R, 1n+L)))) : Nat}:
  +A = {1n+Nat.add(a1, a2) : Nat}
  +Z = Nat.add(R, 1n+L)
  +C = Nat.add(A, Nat.add(P, Z))
  +TG = Nat.add(Nat.add(a1, a2), C)
  %Equal.sym(Nat, Nat.add(P, 0n), P, N.add_zero(P)) :
    {Nat.add(Nat.add(a1, Nat.add(A, _)), Nat.add(0n, Nat.add(Nat.add(a2, R2), Nat.add(1n+L2, 0n)))) == TG : Nat}
  %Equal.sym(Nat, Nat.add(1n+L2, 0n), 1n+L2, N.add_zero(1n+L2)) :
    {Nat.add(Nat.add(a1, Nat.add(A, P)), Nat.add(Nat.add(a2, R2), _)) == TG : Nat}
  %Equal.sym(Nat, R2, R, eR) : {Nat.add(Nat.add(a1, Nat.add(A, P)), Nat.add(Nat.add(a2, _), 1n+L2)) == TG : Nat}
  %Equal.sym(Nat, L2, L, eL) : {Nat.add(Nat.add(a1, Nat.add(A, P)), Nat.add(Nat.add(a2, R), 1n+_)) == TG : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(a1, Nat.add(A, P)), Nat.add(Nat.add(a2, R), 1n+L)), Nat.add(a1, Nat.add(Nat.add(A, P), Nat.add(Nat.add(a2, R), 1n+L))),
      N.add_assoc(a1, Nat.add(A, P), Nat.add(Nat.add(a2, R), 1n+L))) : {_ == TG : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(A, P), Nat.add(Nat.add(a2, R), 1n+L)), Nat.add(A, Nat.add(P, Nat.add(Nat.add(a2, R), 1n+L))),
      N.add_assoc(A, P, Nat.add(Nat.add(a2, R), 1n+L))) : {Nat.add(a1, _) == TG : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(a2, R), 1n+L), Nat.add(a2, Z), N.add_assoc(a2, R, 1n+L)) : {Nat.add(a1, Nat.add(A, Nat.add(P, _))) == TG : Nat}
  %Equal.sym(Nat, Nat.add(P, Nat.add(a2, Z)), Nat.add(a2, Nat.add(P, Z)), N.add_swap(P, a2, Z)) : {Nat.add(a1, Nat.add(A, _)) == TG : Nat}
  %Equal.sym(Nat, Nat.add(A, Nat.add(a2, Nat.add(P, Z))), Nat.add(a2, C), N.add_swap(A, a2, Nat.add(P, Z))) : {Nat.add(a1, _) == TG : Nat}
  Equal.sym(Nat, Nat.add(Nat.add(a1, a2), C), Nat.add(a1, Nat.add(a2, C)), N.add_assoc(a1, a2, C))
  
# Need's bound, from acc.count's after the first push
def arith.prj(+n: Nat, +S2: Nat, +S0: Nat, +a1: Nat, +a2: Nat, +P: Nat, +R2: Nat, +R: Nat, +L2: Nat, +L: Nat, +T: Nat, +SS: Nat, +DB: Nat,
  h1: N.Le(n, Nat.add(S2, Nat.add(Nat.add(a1, Nat.add(1n+Nat.add(a1, a2), Nat.add(P, 0n))), Nat.add(0n, Nat.add(Nat.add(a2, R2), Nat.add(1n+L2, 0n)))))),
  hS: N.Le(S2, S0), eR: {R2 == R : Nat}, eL: {L2 == L : Nat},
  +hC: N.Le(Nat.add(1n+Nat.add(a1, a2), Nat.add(P, Nat.add(R, 1n+L))), T)) ->
  N.Le(1n+n, Nat.add(S0, Nat.add(16n, Nat.add(Nat.mul(2n, Nat.max(T, SS)), Nat.mul(3n, DB))))):
  +A = {1n+Nat.add(a1, a2) : Nat}
  +C = Nat.add(A, Nat.add(P, Nat.add(R, 1n+L)))
  +M = Nat.max(T, SS)
  +hTm = le.max.l(T, SS)
  +h1w = {(%arith.w(a1, a2, P, R2, R, L2, L, eR, eL) : N.Le(n, Nat.add(S2, _)); h1) :
    N.Le(n, Nat.add(S2, Nat.add(Nat.add(a1, a2), C)))}
  +h2 = N.le_rw_r(1n+n, 1n+Nat.add(S2, Nat.add(Nat.add(a1, a2), C)), Nat.add(S2, Nat.add(A, C)),
    Equal.sym(Nat, Nat.add(S2, 1n+Nat.add(Nat.add(a1, a2), C)), 1n+Nat.add(S2, Nat.add(Nat.add(a1, a2), C)), N.add_succ_r(S2, Nat.add(Nat.add(a1, a2), C))), h1w)
  +hA = N.le_trans(A, C, T, N.le_add_r(A, Nat.add(P, Nat.add(R, 1n+L))), hC)
  +h3 = N.add_mono(S2, S0, Nat.add(A, C), Nat.add(T, T), hS, N.add_mono(A, T, C, T, hA, hC))
  +hTT = N.add_mono(T, M, T, Nat.add(M, 0n), hTm, N.le_rw_r(T, M, Nat.add(M, 0n), Equal.sym(Nat, Nat.add(M, 0n), M, N.add_zero(M)), hTm))
  +h4 = N.le_trans(Nat.add(T, T), Nat.mul(2n, M), Nat.add(16n, Nat.add(Nat.mul(2n, M), Nat.mul(3n, DB))), hTT,
    N.le_trans(Nat.mul(2n, M), Nat.add(Nat.mul(2n, M), Nat.mul(3n, DB)), Nat.add(16n, Nat.add(Nat.mul(2n, M), Nat.mul(3n, DB))),
      N.le_add_r(Nat.mul(2n, M), Nat.mul(3n, DB)), N.le_add_l(16n, Nat.add(Nat.mul(2n, M), Nat.mul(3n, DB)))))
  N.le_trans(1n+n, Nat.add(S2, Nat.add(A, C)), Nat.add(S0, Nat.add(16n, Nat.add(Nat.mul(2n, M), Nat.mul(3n, DB)))), h2,
    N.le_trans(Nat.add(S2, Nat.add(A, C)), Nat.add(S0, Nat.add(T, T)), Nat.add(S0, Nat.add(16n, Nat.add(Nat.mul(2n, M), Nat.mul(3n, DB)))), h3,
      N.add_mono(S0, S0, Nat.add(T, T), Nat.add(16n, Nat.add(Nat.mul(2n, M), Nat.mul(3n, DB))), N.le_refl(S0), h4)))

# The λ-match of pairs
# --------------------
#
# M.redex's branch of prj, on the pair y = (r, a1, a2) and x = Prj h: p, z
# and k get r, a1's and a2's cells, M.inc z and k (borrowed from y), M.push
# of App q □ a2 (known) and of App (r·q) □ a1 (known when r is live), n gets
# h, M.inc n, M.dec y and x, and h is the focus: App q (Prj h) (r, a1, a2)
# steps to App q (App (r·q) h a1) a2. The first push takes the old frame's
# cell, from the pend list; the second may need a new one (need.prj).

# the parts of a pair's and a λ-match of pairs' cells
def tup.a(+ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +y: U32, +r: Bk.Quan, +a1: Bk.Term, +a2: Bk.Term,
  hi: D.Is(ds, m, im, fi, nx, ks, img, y, Bk.Term.Tup{r, a1, a2})) -> D.Is(ds, m, im, fi, nx, ks, img, D.Fd(2n, m, y), a1):
  match hi:
    case Tuple{_, Tuple{_, Tuple{Tuple{_, i}, _}}}:
      i

def tup.b(+ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +y: U32, +r: Bk.Quan, +a1: Bk.Term, +a2: Bk.Term,
  hi: D.Is(ds, m, im, fi, nx, ks, img, y, Bk.Term.Tup{r, a1, a2})) -> D.Is(ds, m, im, fi, nx, ks, img, D.Fd(3n, m, y), a2):
  match hi:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{_, i}}}}:
      i

def tup.q(+ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +y: U32, +r: Bk.Quan, +a1: Bk.Term, +a2: Bk.Term,
  hi: D.Is(ds, m, im, fi, nx, ks, img, y, Bk.Term.Tup{r, a1, a2})) -> D.Qs(Cr.Cir.Cells.get(m, y), r):
  match hi:
    case Tuple{_, Tuple{e, _}}:
      e

def prj.h(+ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +x: U32, +h: Bk.Term,
  hi: D.Is(ds, m, im, fi, nx, ks, img, x, Bk.Term.Prj{h})) -> D.Is(ds, m, im, fi, nx, ks, img, D.Fd(2n, m, x), h):
  match hi:
    case Tuple{_, Tuple{_, i}}:
      i

def node.tup2(+m: Cr.Cir.Cells, +y: U32, +r: Bk.Quan, +a1: Bk.Term, +a2: Bk.Term) -> {D.Node(Bk.Term.Tup{r, a1, a2}, m, y, D.Fd(2n, m, y)) == True{} : Bool}:
  +c = D.Fd(2n, m, y)
  D.or.r(U32.is_eq(y, c), Bool.or(D.Node(a1, m, c, c), D.Node(a2, m, D.Fd(3n, m, y), c)),
    D.or.l(D.Node(a1, m, c, c), D.Node(a2, m, D.Fd(3n, m, y), c), node.self(a1, m, c, c, D.u32.refl(c))))

def node.tup3(+m: Cr.Cir.Cells, +y: U32, +r: Bk.Quan, +a1: Bk.Term, +a2: Bk.Term) -> {D.Node(Bk.Term.Tup{r, a1, a2}, m, y, D.Fd(3n, m, y)) == True{} : Bool}:
  +c = D.Fd(3n, m, y)
  D.or.r(U32.is_eq(y, c), Bool.or(D.Node(a1, m, D.Fd(2n, m, y), c), D.Node(a2, m, c, c)),
    D.or.r(D.Node(a1, m, D.Fd(2n, m, y), c), D.Node(a2, m, c, c), node.self(a2, m, c, c, D.u32.refl(c))))

def node.prj2(+m: Cr.Cir.Cells, +x: U32, +h: Bk.Term) -> {D.Node(Bk.Term.Prj{h}, m, x, D.Fd(2n, m, x)) == True{} : Bool}:
  +c = D.Fd(2n, m, x)
  D.or.r(U32.is_eq(x, c), D.Node(h, m, c, c), node.self(h, m, c, c, D.u32.refl(c)))

# two cells borrowed at once
def hsk.borrow2(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32,
  +im: U32, +os: List<&2, D.Rt>, +c1: U32, +u1: Bk.Term, +c2: U32, +u2: Bk.Term, +fs: List<&2, D.AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>,
  hi1: D.IsK(True{}, ds, m, im, fi, nx, ks, img, c1, u1), hn1: {D.Nodes(os, m, c1) == True{} : Bool},
  hi2: D.IsK(True{}, ds, m, im, fi, nx, ks, img, c2, u2), hn2: {D.Nodes(os, m, c2) == True{} : Bool},
  h: D.HSK(True{}, ds, ks, img, m, nx, fi, im, os, Nil{}, fs, sp, pend, ps)) ->
  D.HSK(True{}, ds, ks, img, m, nx, fi, im, os, [D.Rt{c1, u1}, D.Rt{c2, u2}], fs, sp, pend, ps):
  match h:
    case Tuple{hos, Tuple{_, Tuple{_, r}}}:
      (hos, ((hi1, (hi2, Unit{})), ((D.or.r(D.Fl(m, c1, 1024), D.Nodes(os, m, c1), hn1), ((D.or.r(D.Fl(m, c2, 1024), D.Nodes(os, m, c2), hn2), Unit{}))), r)))

# registers that M.push keeps (KEEP)
def kept.r13(-regs: List<&2, U32>, -regs1: List<&2, U32>, kept: D.Kept(regs, regs1, KEEP())) ->
  {List.get(&2, U32, regs1, 13n) == List.get(&2, U32, regs, 13n) : Maybe<&2, U32>}:
  match kept:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}:
      e

def kept.r17(-regs: List<&2, U32>, -regs1: List<&2, U32>, kept: D.Kept(regs, regs1, KEEP())) ->
  {List.get(&2, U32, regs1, 17n) == List.get(&2, U32, regs, 17n) : Maybe<&2, U32>}:
  match kept:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}:
      e

def kept.r18(-regs: List<&2, U32>, -regs1: List<&2, U32>, kept: D.Kept(regs, regs1, KEEP())) ->
  {List.get(&2, U32, regs1, 18n) == List.get(&2, U32, regs, 18n) : Maybe<&2, U32>}:
  match kept:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}:
      e

def ev.kept13(+regs: List<&2, U32>, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +v: U32,
  h: {List.get(&2, U32, regs, 13n) == Some{v} : Maybe<&2, U32>}, +rr: List<&2, U32>, kp: D.Kept(regs, rr, KEEP()), +mz: Cr.Cir.Cells, +nz: U32, +pz: U32) ->
  {Cr.Cir.eval(Mc.M.g(13n), X.X.st(rr, mz, nz, fi, im, pz, lim, inp)) == Some{v} : Maybe<&2, U32>}:
  Equal.trans(Maybe<&2, U32>, List.get(&2, U32, rr, 13n), List.get(&2, U32, regs, 13n), Some{v}, kept.r13(regs, rr, kp), h)

def ev.kept17(+regs: List<&2, U32>, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +v: U32,
  h: {List.get(&2, U32, regs, 17n) == Some{v} : Maybe<&2, U32>}, +rr: List<&2, U32>, kp: D.Kept(regs, rr, KEEP()), +mz: Cr.Cir.Cells, +nz: U32, +pz: U32) ->
  {Cr.Cir.eval(Mc.M.g(17n), X.X.st(rr, mz, nz, fi, im, pz, lim, inp)) == Some{v} : Maybe<&2, U32>}:
  Equal.trans(Maybe<&2, U32>, List.get(&2, U32, rr, 17n), List.get(&2, U32, regs, 17n), Some{v}, kept.r17(regs, rr, kp), h)

# the header of App (r·q) □ a1, known when r is live
def HV2(+r: Bk.Quan, +q: Bk.Quan) -> U32:
  Wa.Wasm.op(Wa.Wasm.Op.or{}, Wa.Wasm.op(Wa.Wasm.Op.or{}, 33, Wa.Wasm.op(Wa.Wasm.Op.shl{}, Wa.Wasm.op(Wa.Wasm.Op.or{}, Wa.Wasm.op(Wa.Wasm.Op.and{}, Mc.Img.quan(q), Wa.Wasm.op(Wa.Wasm.Op.sub{}, 0, Wa.Wasm.op(Wa.Wasm.Op.eq{}, Mc.Img.quan(r), 1))), Wa.Wasm.op(Wa.Wasm.Op.and{}, Mc.Img.quan(r), Wa.Wasm.op(Wa.Wasm.Op.sub{}, Wa.Wasm.op(Wa.Wasm.Op.eq{}, Mc.Img.quan(r), 1), 1))), 6)), Wa.Wasm.op(Wa.Wasm.Op.and{}, 2048, Wa.Wasm.op(Wa.Wasm.Op.sub{}, 0, Wa.Wasm.op(Wa.Wasm.Op.ne{}, Mc.Img.quan(r), 0))))

def hv2.tg(r: Bk.Quan, q: Bk.Quan) -> {D.TgW(HV2(r, q)) == 33 : U32}:
  match r q:
    case Bk.Quan.Q0{} Bk.Quan.Q0{}:
      {==}
    case Bk.Quan.Q0{} Bk.Quan.Q1{}:
      {==}
    case Bk.Quan.Q0{} Bk.Quan.Q2{}:
      {==}
    case Bk.Quan.Q1{} Bk.Quan.Q0{}:
      {==}
    case Bk.Quan.Q1{} Bk.Quan.Q1{}:
      {==}
    case Bk.Quan.Q1{} Bk.Quan.Q2{}:
      {==}
    case Bk.Quan.Q2{} Bk.Quan.Q0{}:
      {==}
    case Bk.Quan.Q2{} Bk.Quan.Q1{}:
      {==}
    case Bk.Quan.Q2{} Bk.Quan.Q2{}:
      {==}
def hv2.qn(r: Bk.Quan, q: Bk.Quan) -> {D.QnW(HV2(r, q)) == Mc.Img.quan(El.Quan.fld(r, q)) : U32}:
  match r q:
    case Bk.Quan.Q0{} Bk.Quan.Q0{}:
      {==}
    case Bk.Quan.Q0{} Bk.Quan.Q1{}:
      {==}
    case Bk.Quan.Q0{} Bk.Quan.Q2{}:
      {==}
    case Bk.Quan.Q1{} Bk.Quan.Q0{}:
      {==}
    case Bk.Quan.Q1{} Bk.Quan.Q1{}:
      {==}
    case Bk.Quan.Q1{} Bk.Quan.Q2{}:
      {==}
    case Bk.Quan.Q2{} Bk.Quan.Q0{}:
      {==}
    case Bk.Quan.Q2{} Bk.Quan.Q1{}:
      {==}
    case Bk.Quan.Q2{} Bk.Quan.Q2{}:
      {==}
def hv2.st(r: Bk.Quan, q: Bk.Quan) -> {D.FlW(HV2(r, q), 1024) == False{} : Bool}:
  match r q:
    case Bk.Quan.Q0{} Bk.Quan.Q0{}:
      {==}
    case Bk.Quan.Q0{} Bk.Quan.Q1{}:
      {==}
    case Bk.Quan.Q0{} Bk.Quan.Q2{}:
      {==}
    case Bk.Quan.Q1{} Bk.Quan.Q0{}:
      {==}
    case Bk.Quan.Q1{} Bk.Quan.Q1{}:
      {==}
    case Bk.Quan.Q1{} Bk.Quan.Q2{}:
      {==}
    case Bk.Quan.Q2{} Bk.Quan.Q0{}:
      {==}
    case Bk.Quan.Q2{} Bk.Quan.Q1{}:
      {==}
    case Bk.Quan.Q2{} Bk.Quan.Q2{}:
      {==}
def hv2.kn(r: Bk.Quan, q: Bk.Quan) -> {D.FlW(HV2(r, q), 2048) == El.Quan.live(r) : Bool}:
  match r q:
    case Bk.Quan.Q0{} Bk.Quan.Q0{}:
      {==}
    case Bk.Quan.Q0{} Bk.Quan.Q1{}:
      {==}
    case Bk.Quan.Q0{} Bk.Quan.Q2{}:
      {==}
    case Bk.Quan.Q1{} Bk.Quan.Q0{}:
      {==}
    case Bk.Quan.Q1{} Bk.Quan.Q1{}:
      {==}
    case Bk.Quan.Q1{} Bk.Quan.Q2{}:
      {==}
    case Bk.Quan.Q2{} Bk.Quan.Q0{}:
      {==}
    case Bk.Quan.Q2{} Bk.Quan.Q1{}:
      {==}
    case Bk.Quan.Q2{} Bk.Quan.Q2{}:
      {==}

# the second header's value, in any state that keeps p and q
def ev.hdr2(+regs: List<&2, U32>, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +r: Bk.Quan, +q: Bk.Quan,
  +h14: {List.get(&2, U32, regs, 14n) == Some{Mc.Img.quan(q)} : Maybe<&2, U32>}, +h18: {List.get(&2, U32, regs, 18n) == Some{Mc.Img.quan(r)} : Maybe<&2, U32>},
  +rr: List<&2, U32>, +kp: D.Kept(regs, rr, KEEP()), +mz: Cr.Cir.Cells, +nz: U32, +pz: U32) ->
  {Cr.Cir.eval(Mc.M.header(Mc.K.app_val(), Mc.M.fld(Mc.M.g(Mc.R.p()), Mc.M.g(Mc.R.q())), Mc.M.and(Mc.M.c(Mc.F.known()), Mc.M.sub(Mc.M.c(0), Mc.M.ne(Mc.M.g(Mc.R.p()), Mc.M.c(0))))), X.X.st(rr, mz, nz, fi, im, pz, lim, inp)) == Some{HV2(r, q)} : Maybe<&2, U32>}:
  +e18a = Equal.trans(Maybe<&2, U32>, List.get(&2, U32, rr, 18n), List.get(&2, U32, regs, 18n), Some{Mc.Img.quan(r)}, kept.r18(regs, rr, kp), h18)
  +e18b = Equal.trans(Maybe<&2, U32>, List.get(&2, U32, rr, 18n), List.get(&2, U32, regs, 18n), Some{Mc.Img.quan(r)}, kept.r18(regs, rr, kp), h18)
  +e18c = Equal.trans(Maybe<&2, U32>, List.get(&2, U32, rr, 18n), List.get(&2, U32, regs, 18n), Some{Mc.Img.quan(r)}, kept.r18(regs, rr, kp), h18)
  +e18d = Equal.trans(Maybe<&2, U32>, List.get(&2, U32, rr, 18n), List.get(&2, U32, regs, 18n), Some{Mc.Img.quan(r)}, kept.r18(regs, rr, kp), h18)
  +e14 = Equal.trans(Maybe<&2, U32>, List.get(&2, U32, rr, 14n), List.get(&2, U32, regs, 14n), Some{Mc.Img.quan(q)}, kept.r14(regs, rr, kp), h14)
  X.ev.op(Wa.Wasm.Op.or{}, Mc.M.or(Mc.M.c(Mc.K.app_val()), Mc.M.shl(Mc.M.fld(Mc.M.g(18n), Mc.M.g(14n)), Mc.M.c(6))), Mc.M.and(Mc.M.c(Mc.F.known()), Mc.M.sub(Mc.M.c(0), Mc.M.ne(Mc.M.g(18n), Mc.M.c(0)))), X.X.st(rr, mz, nz, fi, im, pz, lim, inp), Wa.Wasm.op(Wa.Wasm.Op.or{}, 33, Wa.Wasm.op(Wa.Wasm.Op.shl{}, Wa.Wasm.op(Wa.Wasm.Op.or{}, Wa.Wasm.op(Wa.Wasm.Op.and{}, Mc.Img.quan(q), Wa.Wasm.op(Wa.Wasm.Op.sub{}, 0, Wa.Wasm.op(Wa.Wasm.Op.eq{}, Mc.Img.quan(r), 1))), Wa.Wasm.op(Wa.Wasm.Op.and{}, Mc.Img.quan(r), Wa.Wasm.op(Wa.Wasm.Op.sub{}, Wa.Wasm.op(Wa.Wasm.Op.eq{}, Mc.Img.quan(r), 1), 1))), 6)), Wa.Wasm.op(Wa.Wasm.Op.and{}, 2048, Wa.Wasm.op(Wa.Wasm.Op.sub{}, 0, Wa.Wasm.op(Wa.Wasm.Op.ne{}, Mc.Img.quan(r), 0))), X.ev.op(Wa.Wasm.Op.or{}, Mc.M.c(Mc.K.app_val()), Mc.M.shl(Mc.M.fld(Mc.M.g(18n), Mc.M.g(14n)), Mc.M.c(6)), X.X.st(rr, mz, nz, fi, im, pz, lim, inp), 33, Wa.Wasm.op(Wa.Wasm.Op.shl{}, Wa.Wasm.op(Wa.Wasm.Op.or{}, Wa.Wasm.op(Wa.Wasm.Op.and{}, Mc.Img.quan(q), Wa.Wasm.op(Wa.Wasm.Op.sub{}, 0, Wa.Wasm.op(Wa.Wasm.Op.eq{}, Mc.Img.quan(r), 1))), Wa.Wasm.op(Wa.Wasm.Op.and{}, Mc.Img.quan(r), Wa.Wasm.op(Wa.Wasm.Op.sub{}, Wa.Wasm.op(Wa.Wasm.Op.eq{}, Mc.Img.quan(r), 1), 1))), 6), {==}, X.ev.op(Wa.Wasm.Op.shl{}, Mc.M.fld(Mc.M.g(18n), Mc.M.g(14n)), Mc.M.c(6), X.X.st(rr, mz, nz, fi, im, pz, lim, inp), Wa.Wasm.op(Wa.Wasm.Op.or{}, Wa.Wasm.op(Wa.Wasm.Op.and{}, Mc.Img.quan(q), Wa.Wasm.op(Wa.Wasm.Op.sub{}, 0, Wa.Wasm.op(Wa.Wasm.Op.eq{}, Mc.Img.quan(r), 1))), Wa.Wasm.op(Wa.Wasm.Op.and{}, Mc.Img.quan(r), Wa.Wasm.op(Wa.Wasm.Op.sub{}, Wa.Wasm.op(Wa.Wasm.Op.eq{}, Mc.Img.quan(r), 1), 1))), 6, X.ev.op(Wa.Wasm.Op.or{}, Mc.M.and(Mc.M.g(14n), Mc.M.sub(Mc.M.c(0), Mc.M.eq(Mc.M.g(18n), Mc.M.c(1)))), Mc.M.and(Mc.M.g(18n), Mc.M.sub(Mc.M.eq(Mc.M.g(18n), Mc.M.c(1)), Mc.M.c(1))), X.X.st(rr, mz, nz, fi, im, pz, lim, inp), Wa.Wasm.op(Wa.Wasm.Op.and{}, Mc.Img.quan(q), Wa.Wasm.op(Wa.Wasm.Op.sub{}, 0, Wa.Wasm.op(Wa.Wasm.Op.eq{}, Mc.Img.quan(r), 1))), Wa.Wasm.op(Wa.Wasm.Op.and{}, Mc.Img.quan(r), Wa.Wasm.op(Wa.Wasm.Op.sub{}, Wa.Wasm.op(Wa.Wasm.Op.eq{}, Mc.Img.quan(r), 1), 1)), X.ev.op(Wa.Wasm.Op.and{}, Mc.M.g(14n), Mc.M.sub(Mc.M.c(0), Mc.M.eq(Mc.M.g(18n), Mc.M.c(1))), X.X.st(rr, mz, nz, fi, im, pz, lim, inp), Mc.Img.quan(q), Wa.Wasm.op(Wa.Wasm.Op.sub{}, 0, Wa.Wasm.op(Wa.Wasm.Op.eq{}, Mc.Img.quan(r), 1)), e14, X.ev.op(Wa.Wasm.Op.sub{}, Mc.M.c(0), Mc.M.eq(Mc.M.g(18n), Mc.M.c(1)), X.X.st(rr, mz, nz, fi, im, pz, lim, inp), 0, Wa.Wasm.op(Wa.Wasm.Op.eq{}, Mc.Img.quan(r), 1), {==}, X.ev.op(Wa.Wasm.Op.eq{}, Mc.M.g(18n), Mc.M.c(1), X.X.st(rr, mz, nz, fi, im, pz, lim, inp), Mc.Img.quan(r), 1, e18a, {==}))), X.ev.op(Wa.Wasm.Op.and{}, Mc.M.g(18n), Mc.M.sub(Mc.M.eq(Mc.M.g(18n), Mc.M.c(1)), Mc.M.c(1)), X.X.st(rr, mz, nz, fi, im, pz, lim, inp), Mc.Img.quan(r), Wa.Wasm.op(Wa.Wasm.Op.sub{}, Wa.Wasm.op(Wa.Wasm.Op.eq{}, Mc.Img.quan(r), 1), 1), e18b, X.ev.op(Wa.Wasm.Op.sub{}, Mc.M.eq(Mc.M.g(18n), Mc.M.c(1)), Mc.M.c(1), X.X.st(rr, mz, nz, fi, im, pz, lim, inp), Wa.Wasm.op(Wa.Wasm.Op.eq{}, Mc.Img.quan(r), 1), 1, X.ev.op(Wa.Wasm.Op.eq{}, Mc.M.g(18n), Mc.M.c(1), X.X.st(rr, mz, nz, fi, im, pz, lim, inp), Mc.Img.quan(r), 1, e18c, {==}), {==}))), {==})), X.ev.op(Wa.Wasm.Op.and{}, Mc.M.c(Mc.F.known()), Mc.M.sub(Mc.M.c(0), Mc.M.ne(Mc.M.g(18n), Mc.M.c(0))), X.X.st(rr, mz, nz, fi, im, pz, lim, inp), 2048, Wa.Wasm.op(Wa.Wasm.Op.sub{}, 0, Wa.Wasm.op(Wa.Wasm.Op.ne{}, Mc.Img.quan(r), 0)), {==}, X.ev.op(Wa.Wasm.Op.sub{}, Mc.M.c(0), Mc.M.ne(Mc.M.g(18n), Mc.M.c(0)), X.X.st(rr, mz, nz, fi, im, pz, lim, inp), 0, Wa.Wasm.op(Wa.Wasm.Op.ne{}, Mc.Img.quan(r), 0), {==}, X.ev.op(Wa.Wasm.Op.ne{}, Mc.M.g(18n), Mc.M.c(0), X.X.st(rr, mz, nz, fi, im, pz, lim, inp), Mc.Img.quan(r), 0, e18d, {==}))))

# the nodes of the frames' terms, and their cells, whatever the cells
def fb.sz(kind: D.FK, b: Bk.Term) -> Nat:
  match kind:
    case D.FK.rwt{}:
      Nat.add(Pg.Term.size(b), 0n)
    case _:
      0n

def frs.sz(fs: List<&2, D.AF>) -> Nat:
  match fs:
    case Nil{}:
      0n
    case Con{D.AF{kind, _, _, a, b}, rest}:
      Nat.add(Pg.Term.size(a), Nat.add(fb.sz(kind, b), frs.sz(rest)))

def fb.size(kind: D.FK, +m: Cr.Cir.Cells, +fr: U32, +b: Bk.Term) -> {D.Rts.size(D.Fr.rts.b(m, fr, kind, b)) == fb.sz(kind, b) : Nat}:
  match kind:
    case D.FK.rwt{}:
      {==}
    case D.FK.arg{}:
      {==}
    case D.FK.val{}:
      {==}
    case D.FK.fun{}:
      {==}
    case D.FK.let{}:
      {==}
    case D.FK.tupb{}:
      {==}
    case D.FK.tupa{}:
      {==}
    case D.FK.minb{}:
      {==}
    case D.FK.mina{}:
      {==}

def rts.sz(fs: List<&2, D.AF>, +m: Cr.Cir.Cells, +fr: U32) -> {D.Rts.size(D.Fr.rts(fs, m, fr)) == frs.sz(fs) : Nat}:
  match fs:
    case Nil{}:
      {==}
    case Con{D.AF{+kind, +q, +k, +a, +b}, +rest}:
      +f1 = D.Fd(1n, m, fr)
      +Fb = D.Fr.rts.b(m, fr, kind, b)
      %Equal.sym(Nat, D.Rts.size(List.append(&2, D.Rt, Fb, D.Fr.rts(rest, m, f1))), Nat.add(D.Rts.size(Fb), D.Rts.size(D.Fr.rts(rest, m, f1))), A1.rts.size.app(Fb, D.Fr.rts(rest, m, f1))) : {Nat.add(Pg.Term.size(a), _) == frs.sz(Con{D.AF{kind, q, k, a, b}, rest}) : Nat}
      %Equal.sym(Nat, D.Rts.size(Fb), fb.sz(kind, b), fb.size(kind, m, fr, b)) : {Nat.add(Pg.Term.size(a), Nat.add(_, D.Rts.size(D.Fr.rts(rest, m, f1)))) == frs.sz(Con{D.AF{kind, q, k, a, b}, rest}) : Nat}
      %Equal.sym(Nat, D.Rts.size(D.Fr.rts(rest, m, f1)), frs.sz(rest), rts.sz(rest, m, f1)) : {Nat.add(Pg.Term.size(a), Nat.add(fb.sz(kind, b), _)) == frs.sz(Con{D.AF{kind, q, k, a, b}, rest}) : Nat}
      {==}

def cells.len(fs: List<&2, D.AF>, +m: Cr.Cir.Cells, +fr: U32) -> {List.length(&2, U32, D.Fr.cells(fs, m, fr)) == List.length(&2, D.AF, fs) : Nat}:
  match fs:
    case Nil{}:
      {==}
    case Con{_, +rest}:
      %Equal.sym(Nat, List.length(&2, U32, D.Fr.cells(rest, m, D.Fd(1n, m, fr))), List.length(&2, D.AF, rest), cells.len(rest, m, D.Fd(1n, m, fr))) : {1n+_ == 1n+List.length(&2, D.AF, rest) : Nat}
      {==}

# after the first push, with no pending cell: a new cell fits in Need
def need.prj(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st0: Cr.Cir.State, +t: Bk.Term,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, ps: List<&2, U32>, +zs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +q: Bk.Quan,
  +zc: U32, +y: U32, +x: U32, +r: Bk.Quan, +a1: Bk.Term, +a2: Bk.Term, +h: Bk.Term,
  hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{zc, a1}, D.Rt{y, Bk.Term.Tup{r, a1, a2}}, D.Rt{x, Bk.Term.Prj{h}}], Nil{}, sp, Con{D.AF{D.FK.val{}, q, True{}, a2, a2}, fs}, ps, zs),
  hS: N.Le(D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi), D.Stat(D.Mem.cells(st0), D.St.cells(st0), D.St.first(st0))),
  +hC: N.Le(Nat.add(Pg.Term.size(Bk.Term.Tup{r, a1, a2}), Nat.add(Pg.Term.size(Bk.Term.Prj{h}), Nat.add(frs.sz(fs), 1n+List.length(&2, D.AF, fs)))), Pg.Term.size(t)),
  e: {D.Pend.none(ps) == True{} : Bool}) -> N.Le(1n+Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), D.Need(ds, st0, t)):
  match ps:
    case Nil{}:
      +f1 = D.Fd(1n, m, sp)
      arith.prj(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi), D.Stat(D.Mem.cells(st0), D.St.cells(st0), D.St.first(st0)),
        Pg.Term.size(a1), Pg.Term.size(a2), Pg.Term.size(Bk.Term.Prj{h}), D.Rts.size(D.Fr.rts(fs, m, f1)), frs.sz(fs),
        List.length(&2, U32, D.Fr.cells(fs, m, f1)), List.length(&2, D.AF, fs), Pg.Term.size(t), D.StepSize(ds, t), D.Defs.big(ds),
        A1.acc.count(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{zc, a1}, D.Rt{y, Bk.Term.Tup{r, a1, a2}}, D.Rt{x, Bk.Term.Prj{h}}], Nil{}, sp,
          Con{D.AF{D.FK.val{}, q, True{}, a2, a2}, fs}, zs, hac),
        hS, rts.sz(fs, m, f1), cells.len(fs, m, f1), hC)
    case Con{_, _}:
      D.bool.ft(N.Le(1n+Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), D.Need(ds, st0, t)), e)

# a new cell's 20 bytes fit in Budget, when it fits in Need
def room.of2(+ds: List<&2, Bk.Def>, +st0: Cr.Cir.State, +t: Bk.Term, +nx: U32, +fi: U32, efi: {D.St.first(st0) == fi : U32},
  hn: N.Le(1n+Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), D.Need(ds, st0, t)), hf: {U32.is_le(fi, nx) == True{} : Bool}) ->
  N.Le(Nat.mul(20n, Nat.add(U32.to_nat(nx), 1n)), D.Budget(ds, st0, t)):
  +Y = Nat.add(Nat.mul(20n, U32.to_nat(D.St.next(st0))), Pg.Term.size(t))
  %Equal.sym(U32, D.St.first(st0), fi, efi) :
    N.Le(Nat.mul(20n, Nat.add(U32.to_nat(nx), 1n)), Nat.max(Nat.add(Nat.mul(20n, Nat.add(U32.to_nat(_), D.Need(ds, st0, t))), Pg.Term.size(t)), Y))
  budget.of(nx, fi, D.Need(ds, st0, t), Pg.Term.size(t), Y, hn, D.u.le(fi, nx, hf))

# the push's outcome: no new cell, or a new one with no pending cell
def hor.f(c: Bool, d: Bool, e: Bool, h: {Bool.and(c, Bool.and(d, e)) == True{} : Bool}) -> {Bool.and(c, e) == True{} : Bool}:
  match c d:
    case True{} True{}:
      h
    case True{} False{}:
      D.bool.ft({Bool.and(True{}, e) == True{} : Bool}, h)
    case False{} _:
      D.bool.ft({Bool.and(False{}, e) == True{} : Bool}, h)

def hor.of(a: Bool, b: Bool, c: Bool, d: Bool, e: Bool, h: {Bool.or(Bool.and(a, b), Bool.and(c, Bool.and(d, e))) == True{} : Bool}) ->
  {Bool.or(b, Bool.and(c, e)) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      hor.f(c, d, e, (%and.false(a) : {Bool.or(_, Bool.and(c, Bool.and(d, e))) == True{} : Bool}; h))

# n gets h, M.inc n, then M.dec y and x
def prj.n(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st0: Cr.Cir.State, +t: Bk.Term, +w: Nat, +lim: U32, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +inp: List<&2, Word(8n)>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  +x: U32, +y: U32, +r: Bk.Quan, +a1: Bk.Term, +a2: Bk.Term, +h: Bk.Term,
  es: {El.Eval.step(ds, t) == Some{D.A.plugs(fs, h)} : Maybe<Bk.Term>}, afs: D.AFs.ok(ds, fs), hmem: N.Le(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), Nat.max(D.Mem.cells(st0), D.Need(ds, st0, t))),
  +hs: D.HSK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{y, Bk.Term.Tup{r, a1, a2}}, D.Rt{x, Bk.Term.Prj{h}}], Nil{}, fs, sp, pend, ps),
  hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{y, Bk.Term.Tup{r, a1, a2}}, D.Rt{x, Bk.Term.Prj{h}}], Nil{}, sp, fs, ps, zs),
  +hl: {List.length(&2, U32, regs) == 63n : Nat}, +h11: {List.get(&2, U32, regs, 11n) == Some{x} : Maybe<&2, U32>}, +h12: {List.get(&2, U32, regs, 12n) == Some{y} : Maybe<&2, U32>}, +h2: {List.get(&2, U32, regs, 2n) == Some{sp} : Maybe<&2, U32>}, +h3: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>}) ->
  PB(ds, ks, img, st0, t, w, lim, Cr.Cir.exec(f, Mc.M.do([Mc.M.set(Mc.R.n(), Mc.M.f(2n, Mc.M.g(Mc.R.x()))), Mc.M.inc(Mc.R.n()), Mc.M.dec(Mc.R.y()), Mc.M.dec(Mc.R.x()), Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())), Mc.M.set(Mc.R.mode(), Mc.M.c(0))]), X.X.st(regs, m, nx, fi, im, pg, lim, inp))):
  +A = {Bk.Term.Tup{r, a1, a2} : Bk.Term}
  +P = {Bk.Term.Prj{h} : Bk.Term}
  +nv = D.Fd(2n, m, x)
  +r1 = X.X.set(regs, 15n, nv)
  +isx = hs.r2(ds, ks, img, m, nx, fi, im, y, A, x, P, Nil{}, fs, sp, pend, ps, hs)
  +ev = X.ev.fld(2n, Mc.M.g(11n), X.X.st(regs, m, nx, fi, im, pg, lim, inp), x, h11, isk.cell(ds, m, im, fi, nx, ks, img, x, P, isx))
  pb.set(f, ds, ks, img, st0, t, w, lim, 15n, Mc.M.f(2n, Mc.M.g(Mc.R.x())), Mc.M.do([Mc.M.inc(Mc.R.n()), Mc.M.dec(Mc.R.y()), Mc.M.dec(Mc.R.x()), Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())), Mc.M.set(Mc.R.mode(), Mc.M.c(0))]), X.X.st(regs, m, nx, fi, im, pg, lim, inp), nv, ev, hl, {==},
    pb.inc(f, ds, ks, img, st0, t, w, lim, r1, m, nx, fi, im, pg, inp, 15n, [D.Rt{y, A}, D.Rt{x, P}], Nil{}, fs, sp, pend, ps, nv, h, Nil{}, zs, Mc.M.do([Mc.M.dec(Mc.R.y()), Mc.M.dec(Mc.R.x()), Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())), Mc.M.set(Mc.R.mode(), Mc.M.c(0))]),
      hsk.borrow(ds, ks, img, m, nx, fi, im, [D.Rt{y, A}, D.Rt{x, P}], nv, h, fs, sp, pend, ps,
        prj.h(ds, m, im, fi, nx, ks, img, x, h, isx), nodes.snd(D.Rt{y, A}, x, P, m, nv, node.prj2(m, x, h)), hs),
      hac, N.toLe(2n, 64n, {==}), X.L.gs(regs, 15n, nv, X.L.lt(regs, 15n, hl, {==})),
      m2 => hst => hs2 => hac2 =>
        dec.yx(f, ds, ks, img, st0, t, w, lim, r1, m2, nx, fi, im, pg, inp, fs, sp, pend, ps, zs, nv, h, y, A, x, P, D.A.plugs(fs, h), {==}, es, afs, hmem, hac2, hs2, X.L.len(regs, 15n, nv, 63n, hl),
          X.L.gs(regs, 15n, nv, X.L.lt(regs, 15n, hl, {==})), X.L.go(regs, 15n, 11n, nv, x, {==}, h11), X.L.go(regs, 15n, 12n, nv, y, {==}, h12),
          X.L.go(regs, 15n, 2n, nv, sp, {==}, h2), X.L.go(regs, 15n, 3n, nv, pend, {==}, h3))))

# the second push, App (r·q) □ a1: a new cell only with no pending cell,
# which fits (hnd)
def prj.p2(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st0: Cr.Cir.State, +t: Bk.Term, +w: Nat, +lim: U32, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +inp: List<&2, Word(8n)>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  +x: U32, +y: U32, +zc: U32, +r: Bk.Quan, +q: Bk.Quan, +a1: Bk.Term, +a2: Bk.Term, +h: Bk.Term,
  +es: {El.Eval.step(ds, t) == Some{D.A.plugs(fs, Bk.Term.App{El.Quan.fld(r, q), h, a1})} : Maybe<Bk.Term>}, +afs: D.AFs.ok(ds, fs),
  +hva1: {Bool.or(Bool.not(El.Quan.live(r)), El.Eval.vals(ds, a1, False{})) == True{} : Bool},
  hnd: {D.Pend.none(ps) == True{} : Bool} -> N.Le(1n+Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), D.Need(ds, st0, t)),
  hnd2: {D.Pend.none(ps) == True{} : Bool} -> N.Le(1n+Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), D.Need(ds, st0, t)),
  +hmc: {D.Mem.cells(st0) == Nat.sub(U32.to_nat(nx), U32.to_nat(fi)) : Nat}, +efi: {D.St.first(st0) == fi : U32},
  +hs: D.HSK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{zc, a1}, D.Rt{y, Bk.Term.Tup{r, a1, a2}}, D.Rt{x, Bk.Term.Prj{h}}], Nil{}, fs, sp, pend, ps),
  hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{zc, a1}, D.Rt{y, Bk.Term.Tup{r, a1, a2}}, D.Rt{x, Bk.Term.Prj{h}}], Nil{}, sp, fs, ps, zs),
  +hl: {List.length(&2, U32, regs) == 63n : Nat}, +h11: {List.get(&2, U32, regs, 11n) == Some{x} : Maybe<&2, U32>}, +h12: {List.get(&2, U32, regs, 12n) == Some{y} : Maybe<&2, U32>}, +h13: {List.get(&2, U32, regs, 13n) == Some{zc} : Maybe<&2, U32>}, +h14: {List.get(&2, U32, regs, 14n) == Some{Mc.Img.quan(q)} : Maybe<&2, U32>},
  +h18: {List.get(&2, U32, regs, 18n) == Some{Mc.Img.quan(r)} : Maybe<&2, U32>}, +h2: {List.get(&2, U32, regs, 2n) == Some{sp} : Maybe<&2, U32>}, +h3: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>}) ->
  PB(ds, ks, img, st0, t, w, lim, Cr.Cir.exec(f, Mc.M.do([Mc.M.push(Mc.M.header(Mc.K.app_val(), Mc.M.fld(Mc.M.g(Mc.R.p()), Mc.M.g(Mc.R.q())), Mc.M.and(Mc.M.c(Mc.F.known()), Mc.M.sub(Mc.M.c(0), Mc.M.ne(Mc.M.g(Mc.R.p()), Mc.M.c(0))))), Mc.M.g(Mc.R.z()), Mc.M.c(0)), Mc.M.set(Mc.R.n(), Mc.M.f(2n, Mc.M.g(Mc.R.x()))), Mc.M.inc(Mc.R.n()), Mc.M.dec(Mc.R.y()), Mc.M.dec(Mc.R.x()), Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())), Mc.M.set(Mc.R.mode(), Mc.M.c(0))]), X.X.st(regs, m, nx, fi, im, pg, lim, inp))):
  +A = {Bk.Term.Tup{r, a1, a2} : Bk.Term}
  +P = {Bk.Term.Prj{h} : Bk.Term}
  pb.push(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, [D.Rt{y, A}, D.Rt{x, P}], fs, sp, pend, ps, zs, El.Quan.fld(r, q), El.Quan.live(r), a1, a1,
    Mc.M.header(Mc.K.app_val(), Mc.M.fld(Mc.M.g(Mc.R.p()), Mc.M.g(Mc.R.q())), Mc.M.and(Mc.M.c(Mc.F.known()), Mc.M.sub(Mc.M.c(0), Mc.M.ne(Mc.M.g(Mc.R.p()), Mc.M.c(0))))), Mc.M.g(13n), Mc.M.c(0), HV2(r, q), zc, 0, Mc.M.do([Mc.M.set(Mc.R.n(), Mc.M.f(2n, Mc.M.g(Mc.R.x()))), Mc.M.inc(Mc.R.n()), Mc.M.dec(Mc.R.y()), Mc.M.dec(Mc.R.x()), Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())), Mc.M.set(Mc.R.mode(), Mc.M.c(0))]), hs, hac, hl, h3, h2,
    hv2.tg(r, q), hv2.qn(r, q), hv2.st(r, q), hv2.kn(r, q),
    +rr => +kp => +mz => +nz => +pz => ev.hdr2(regs, fi, im, lim, inp, r, q, h14, h18, rr, kp, mz, nz, pz),
    +rr => kp => +mz => +nz => +pz => ev.kept13(regs, fi, im, lim, inp, zc, h13, rr, kp, mz, nz, pz),
    rr => kp => mz => nz => pz => {==},
    e => room.of2(ds, st0, t, nx, fi, efi, hnd(e), hsk.fn(ds, ks, img, m, nx, fi, im, [D.Rt{zc, a1}, D.Rt{y, Bk.Term.Tup{r, a1, a2}}, D.Rt{x, Bk.Term.Prj{h}}], Nil{}, fs, sp, pend, ps, hs)),
    +regs1 => +m1 => +nx1 => +pg1 => +z => +pend2 => +ps2 => +zs2 => +hl2 => +kp => +hp2 => _ => hor => hs3 => hac3 =>
      prj.n(f, ds, ks, img, st0, t, w, lim, X.X.set(regs1, 2n, z), Cr.Cir.Cells.set(m1, z, Cr.Cir.Cell{HV2(r, q), sp, zc, 0, 0}), nx1, fi, im, pg1, inp, Con{D.AF{D.FK.val{}, El.Quan.fld(r, q), El.Quan.live(r), a1, a1}, fs}, z, pend2, ps2, zs2, x, y, r, a1, a2, h,
        es, (hva1, afs),
        peak.fin(ds, st0, t, nx, nx1, fi, ps, hmc, hnd2, hor.of(D.Mem(ps, z), U32.is_eq(nx1, nx), D.Pend.none(ps), U32.is_eq(z, nx), U32.is_eq(nx1, U32.inc(nx)), hor)),
        hs3, hac3, X.L.len(regs1, 2n, z, 63n, hl2),
        X.L.go(regs1, 2n, 11n, z, x, {==}, Equal.trans(Maybe<&2, U32>, List.get(&2, U32, regs1, 11n), List.get(&2, U32, regs, 11n), Some{x}, kept.r11(regs, regs1, kp), h11)), X.L.go(regs1, 2n, 12n, z, y, {==}, Equal.trans(Maybe<&2, U32>, List.get(&2, U32, regs1, 12n), List.get(&2, U32, regs, 12n), Some{y}, kept.r12(regs, regs1, kp), h12)),
        X.L.gs(regs1, 2n, z, X.L.lt(regs1, 2n, hl2, {==})), X.L.go(regs1, 2n, 3n, z, pend2, {==}, hp2)))

# after the first push: the second, with its room from acc.count (need.prj)
def prj.p1k(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st0: Cr.Cir.State, +t: Bk.Term, +w: Nat, +lim: U32, +regs: List<&2, U32>, +regs1: List<&2, U32>, +m: Cr.Cir.Cells, +m1: Cr.Cir.Cells, +nx: U32, +nx1: U32, +fi: U32, +im: U32,
  +pg1: U32, +inp: List<&2, Word(8n)>, +fs: List<&2, D.AF>, +sp: U32, +z: U32, +pend2: U32, +p0: U32, +ps0: List<&2, U32>, +ps2: List<&2, U32>,
  +zs2: List<&2, D.Rt>, +x: U32, +y: U32, +zc: U32, +kc: U32, +r: Bk.Quan, +q: Bk.Quan, +a1: Bk.Term, +a2: Bk.Term, +h: Bk.Term,
  +es: {El.Eval.step(ds, t) == Some{D.A.plugs(fs, Bk.Term.App{q, Bk.Term.App{El.Quan.fld(r, q), h, a1}, a2})} : Maybe<Bk.Term>}, +afs: D.AFs.ok(ds, fs), +hvl: {El.Eval.vals(ds, Bk.Term.Tup{r, a1, a2}, False{}) == True{} : Bool},
  +hmc: {D.Mem.cells(st0) == Nat.sub(U32.to_nat(nx), U32.to_nat(fi)) : Nat}, +hS: N.Le(D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi), D.Stat(D.Mem.cells(st0), D.St.cells(st0), D.St.first(st0))), +hC: N.Le(Nat.add(Pg.Term.size(Bk.Term.Tup{r, a1, a2}), Nat.add(Pg.Term.size(Bk.Term.Prj{h}), Nat.add(frs.sz(fs), 1n+List.length(&2, D.AF, fs)))), Pg.Term.size(t)), +efi: {D.St.first(st0) == fi : U32},
  +hl2: {List.length(&2, U32, regs1) == 63n : Nat}, +kp: D.Kept(regs, regs1, KEEP()), +hp2: {List.get(&2, U32, regs1, 3n) == Some{pend2} : Maybe<&2, U32>},
  +hstat: N.Le(D.Stat(Nat.sub(U32.to_nat(nx1), U32.to_nat(fi)), Cr.Cir.Cells.set(m1, z, Cr.Cir.Cell{HV(q), sp, kc, 0, 0}), fi), D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi)),
  +hor: {Bool.or(Bool.and(D.Mem(Con{p0, ps0}, z), U32.is_eq(nx1, nx)), Bool.and(D.Pend.none(Con{p0, ps0}), Bool.and(U32.is_eq(z, nx), U32.is_eq(nx1, U32.inc(nx))))) == True{} : Bool},
  +hs3: D.HSK(True{}, ds, ks, img, Cr.Cir.Cells.set(m1, z, Cr.Cir.Cell{HV(q), sp, kc, 0, 0}), nx1, fi, im, [D.Rt{zc, a1}, D.Rt{y, Bk.Term.Tup{r, a1, a2}}, D.Rt{x, Bk.Term.Prj{h}}], Nil{}, Con{D.AF{D.FK.val{}, q, True{}, a2, a2}, fs}, z, pend2, ps2),
  +hac3: D.AccK(True{}, ds, ks, img, Cr.Cir.Cells.set(m1, z, Cr.Cir.Cell{HV(q), sp, kc, 0, 0}), nx1, fi, im, [D.Rt{zc, a1}, D.Rt{y, Bk.Term.Tup{r, a1, a2}}, D.Rt{x, Bk.Term.Prj{h}}], Nil{}, z, Con{D.AF{D.FK.val{}, q, True{}, a2, a2}, fs}, ps2, zs2),
  +h11: {List.get(&2, U32, regs, 11n) == Some{x} : Maybe<&2, U32>}, +h12: {List.get(&2, U32, regs, 12n) == Some{y} : Maybe<&2, U32>}, +h13: {List.get(&2, U32, regs, 13n) == Some{zc} : Maybe<&2, U32>}, +h14: {List.get(&2, U32, regs, 14n) == Some{Mc.Img.quan(q)} : Maybe<&2, U32>}, +h18: {List.get(&2, U32, regs, 18n) == Some{Mc.Img.quan(r)} : Maybe<&2, U32>}) ->
  PB(ds, ks, img, st0, t, w, lim, Cr.Cir.exec(f, Mc.M.do([Mc.M.push(Mc.M.header(Mc.K.app_val(), Mc.M.fld(Mc.M.g(Mc.R.p()), Mc.M.g(Mc.R.q())), Mc.M.and(Mc.M.c(Mc.F.known()), Mc.M.sub(Mc.M.c(0), Mc.M.ne(Mc.M.g(Mc.R.p()), Mc.M.c(0))))), Mc.M.g(Mc.R.z()), Mc.M.c(0)), Mc.M.set(Mc.R.n(), Mc.M.f(2n, Mc.M.g(Mc.R.x()))), Mc.M.inc(Mc.R.n()), Mc.M.dec(Mc.R.y()), Mc.M.dec(Mc.R.x()), Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())), Mc.M.set(Mc.R.mode(), Mc.M.c(0))]), X.X.st(X.X.set(regs1, 2n, z), Cr.Cir.Cells.set(m1, z, Cr.Cir.Cell{HV(q), sp, kc, 0, 0}), nx1, fi, im, pg1, lim, inp))):
  +enx = D.u32.eq(nx1, nx, D.and.r(D.Mem(Con{p0, ps0}, z), U32.is_eq(nx1, nx), or.f.l(Bool.and(D.Mem(Con{p0, ps0}, z), U32.is_eq(nx1, nx)), hor)))
  +hmc1 = {(%Equal.sym(U32, nx1, nx, enx) : {D.Mem.cells(st0) == Nat.sub(U32.to_nat(_), U32.to_nat(fi)) : Nat}; hmc) :
    {D.Mem.cells(st0) == Nat.sub(U32.to_nat(nx1), U32.to_nat(fi)) : Nat}}
  +hS1 = N.le_trans(D.Stat(Nat.sub(U32.to_nat(nx1), U32.to_nat(fi)), Cr.Cir.Cells.set(m1, z, Cr.Cir.Cell{HV(q), sp, kc, 0, 0}), fi), D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi), D.Stat(D.Mem.cells(st0), D.St.cells(st0), D.St.first(st0)), hstat, hS)
  +VA = Bool.or(Bool.not(El.Quan.live(r)), El.Eval.vals(ds, a1, False{}))
  prj.p2(f, ds, ks, img, st0, t, w, lim, X.X.set(regs1, 2n, z), Cr.Cir.Cells.set(m1, z, Cr.Cir.Cell{HV(q), sp, kc, 0, 0}), nx1, fi, im, pg1, inp, Con{D.AF{D.FK.val{}, q, True{}, a2, a2}, fs}, z, pend2, ps2, zs2, x, y, zc, r, q, a1, a2, h,
    es, (D.and.r(VA, El.Eval.vals(ds, a2, False{}), hvl), afs), D.and.l(VA, El.Eval.vals(ds, a2, False{}), hvl),
    e => need.prj(ds, ks, img, st0, t, Cr.Cir.Cells.set(m1, z, Cr.Cir.Cell{HV(q), sp, kc, 0, 0}), nx1, fi, im, ps2, zs2, fs, z, q, zc, y, x, r, a1, a2, h, hac3, hS1, hC, e),
    e => need.prj(ds, ks, img, st0, t, Cr.Cir.Cells.set(m1, z, Cr.Cir.Cell{HV(q), sp, kc, 0, 0}), nx1, fi, im, ps2, zs2, fs, z, q, zc, y, x, r, a1, a2, h, hac3, hS1, hC, e),
    hmc1, efi, hs3, hac3, X.L.len(regs1, 2n, z, 63n, hl2),
    X.L.go(regs1, 2n, 11n, z, x, {==}, Equal.trans(Maybe<&2, U32>, List.get(&2, U32, regs1, 11n), List.get(&2, U32, regs, 11n), Some{x}, kept.r11(regs, regs1, kp), h11)), X.L.go(regs1, 2n, 12n, z, y, {==}, Equal.trans(Maybe<&2, U32>, List.get(&2, U32, regs1, 12n), List.get(&2, U32, regs, 12n), Some{y}, kept.r12(regs, regs1, kp), h12)),
    X.L.go(regs1, 2n, 13n, z, zc, {==}, Equal.trans(Maybe<&2, U32>, List.get(&2, U32, regs1, 13n), List.get(&2, U32, regs, 13n), Some{zc}, kept.r13(regs, regs1, kp), h13)), X.L.go(regs1, 2n, 14n, z, Mc.Img.quan(q), {==}, Equal.trans(Maybe<&2, U32>, List.get(&2, U32, regs1, 14n), List.get(&2, U32, regs, 14n), Some{Mc.Img.quan(q)}, kept.r14(regs, regs1, kp), h14)),
    X.L.go(regs1, 2n, 18n, z, Mc.Img.quan(r), {==}, Equal.trans(Maybe<&2, U32>, List.get(&2, U32, regs1, 18n), List.get(&2, U32, regs, 18n), Some{Mc.Img.quan(r)}, kept.r18(regs, regs1, kp), h18)), X.L.gs(regs1, 2n, z, X.L.lt(regs1, 2n, hl2, {==})), X.L.go(regs1, 2n, 3n, z, pend2, {==}, hp2))

# the first push, App q □ a2: the old frame's cell, from the pend list
def prj.p1(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st0: Cr.Cir.State, +t: Bk.Term, +w: Nat, +lim: U32, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +inp: List<&2, Word(8n)>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32, +p0: U32, +ps0: List<&2, U32>, +zs: List<&2, D.Rt>,
  +x: U32, +y: U32, +zc: U32, +kc: U32, +r: Bk.Quan, +q: Bk.Quan, +a1: Bk.Term, +a2: Bk.Term, +h: Bk.Term,
  +es: {El.Eval.step(ds, t) == Some{D.A.plugs(fs, Bk.Term.App{q, Bk.Term.App{El.Quan.fld(r, q), h, a1}, a2})} : Maybe<Bk.Term>}, +afs: D.AFs.ok(ds, fs), +hvl: {El.Eval.vals(ds, Bk.Term.Tup{r, a1, a2}, False{}) == True{} : Bool},
  +hmc: {D.Mem.cells(st0) == Nat.sub(U32.to_nat(nx), U32.to_nat(fi)) : Nat}, +hS: N.Le(D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi), D.Stat(D.Mem.cells(st0), D.St.cells(st0), D.St.first(st0))), +hC: N.Le(Nat.add(Pg.Term.size(Bk.Term.Tup{r, a1, a2}), Nat.add(Pg.Term.size(Bk.Term.Prj{h}), Nat.add(frs.sz(fs), 1n+List.length(&2, D.AF, fs)))), Pg.Term.size(t)), +efi: {D.St.first(st0) == fi : U32},
  +hs: D.HSK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{kc, a2}, D.Rt{zc, a1}, D.Rt{y, Bk.Term.Tup{r, a1, a2}}, D.Rt{x, Bk.Term.Prj{h}}], Nil{}, fs, sp, pend, Con{p0, ps0}),
  hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{kc, a2}, D.Rt{zc, a1}, D.Rt{y, Bk.Term.Tup{r, a1, a2}}, D.Rt{x, Bk.Term.Prj{h}}], Nil{}, sp, fs, Con{p0, ps0}, zs),
  +hl: {List.length(&2, U32, regs) == 63n : Nat}, +h11: {List.get(&2, U32, regs, 11n) == Some{x} : Maybe<&2, U32>}, +h12: {List.get(&2, U32, regs, 12n) == Some{y} : Maybe<&2, U32>}, +h13: {List.get(&2, U32, regs, 13n) == Some{zc} : Maybe<&2, U32>}, +h14: {List.get(&2, U32, regs, 14n) == Some{Mc.Img.quan(q)} : Maybe<&2, U32>},
  +h17: {List.get(&2, U32, regs, 17n) == Some{kc} : Maybe<&2, U32>}, +h18: {List.get(&2, U32, regs, 18n) == Some{Mc.Img.quan(r)} : Maybe<&2, U32>}, +h2: {List.get(&2, U32, regs, 2n) == Some{sp} : Maybe<&2, U32>}, +h3: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>}) ->
  PB(ds, ks, img, st0, t, w, lim, Cr.Cir.exec(f, Mc.M.do([Mc.M.push(Mc.M.header(Mc.K.app_val(), Mc.M.g(Mc.R.q()), Mc.M.c(Mc.F.known())), Mc.M.g(Mc.R.k()), Mc.M.c(0)), Mc.M.push(Mc.M.header(Mc.K.app_val(), Mc.M.fld(Mc.M.g(Mc.R.p()), Mc.M.g(Mc.R.q())), Mc.M.and(Mc.M.c(Mc.F.known()), Mc.M.sub(Mc.M.c(0), Mc.M.ne(Mc.M.g(Mc.R.p()), Mc.M.c(0))))), Mc.M.g(Mc.R.z()), Mc.M.c(0)), Mc.M.set(Mc.R.n(), Mc.M.f(2n, Mc.M.g(Mc.R.x()))), Mc.M.inc(Mc.R.n()), Mc.M.dec(Mc.R.y()), Mc.M.dec(Mc.R.x()), Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())), Mc.M.set(Mc.R.mode(), Mc.M.c(0))]), X.X.st(regs, m, nx, fi, im, pg, lim, inp))):
  pb.push(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, [D.Rt{zc, a1}, D.Rt{y, Bk.Term.Tup{r, a1, a2}}, D.Rt{x, Bk.Term.Prj{h}}], fs, sp, pend, Con{p0, ps0}, zs, q, True{}, a2, a2,
    Mc.M.header(Mc.K.app_val(), Mc.M.g(Mc.R.q()), Mc.M.c(Mc.F.known())), Mc.M.g(17n), Mc.M.c(0), HV(q), kc, 0, Mc.M.do([Mc.M.push(Mc.M.header(Mc.K.app_val(), Mc.M.fld(Mc.M.g(Mc.R.p()), Mc.M.g(Mc.R.q())), Mc.M.and(Mc.M.c(Mc.F.known()), Mc.M.sub(Mc.M.c(0), Mc.M.ne(Mc.M.g(Mc.R.p()), Mc.M.c(0))))), Mc.M.g(Mc.R.z()), Mc.M.c(0)), Mc.M.set(Mc.R.n(), Mc.M.f(2n, Mc.M.g(Mc.R.x()))), Mc.M.inc(Mc.R.n()), Mc.M.dec(Mc.R.y()), Mc.M.dec(Mc.R.x()), Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())), Mc.M.set(Mc.R.mode(), Mc.M.c(0))]), hs, hac, hl, h3, h2, hv.tg(q), hv.qn(q), hv.st(q), hv.kn(q),
    +rr => kp => +mz => +nz => +pz => ev.hdr(regs, fi, im, lim, inp, q, h14, rr, kp, mz, nz, pz),
    +rr => kp => +mz => +nz => +pz => ev.kept17(regs, fi, im, lim, inp, kc, h17, rr, kp, mz, nz, pz),
    rr => kp => mz => nz => pz => {==},
    e => D.bool.ft(N.Le(Nat.mul(20n, Nat.add(U32.to_nat(nx), 1n)), D.Budget(ds, st0, t)), e),
    +regs1 => +m1 => +nx1 => +pg1 => +z => +pend2 => +ps2 => +zs2 => +hl2 => +kp => +hp2 => +hstat => hor => hs3 => hac3 =>
      prj.p1k(f, ds, ks, img, st0, t, w, lim, regs, regs1, m, m1, nx, nx1, fi, im, pg1, inp, fs, sp, z, pend2, p0, ps0, ps2, zs2, x, y, zc, kc, r, q, a1, a2, h,
        es, afs, hvl, hmc, hS, hC, efi, hl2, kp, hp2, hstat, hor, hs3, hac3, h11, h12, h13, h14, h18))

# p, z and k set, then M.inc z and k, both borrowed from y
def prj.inc(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st0: Cr.Cir.State, +t: Bk.Term, +w: Nat, +lim: U32, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +inp: List<&2, Word(8n)>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32, +p0: U32, +ps0: List<&2, U32>, +zs: List<&2, D.Rt>,
  +x: U32, +y: U32, +r: Bk.Quan, +q: Bk.Quan, +a1: Bk.Term, +a2: Bk.Term, +h: Bk.Term,
  +es: {El.Eval.step(ds, t) == Some{D.A.plugs(fs, Bk.Term.App{q, Bk.Term.App{El.Quan.fld(r, q), h, a1}, a2})} : Maybe<Bk.Term>}, +afs: D.AFs.ok(ds, fs), +hvl: {El.Eval.vals(ds, Bk.Term.Tup{r, a1, a2}, False{}) == True{} : Bool},
  +hmc: {D.Mem.cells(st0) == Nat.sub(U32.to_nat(nx), U32.to_nat(fi)) : Nat}, +hS: N.Le(D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi), D.Stat(D.Mem.cells(st0), D.St.cells(st0), D.St.first(st0))), +hC: N.Le(Nat.add(Pg.Term.size(Bk.Term.Tup{r, a1, a2}), Nat.add(Pg.Term.size(Bk.Term.Prj{h}), Nat.add(frs.sz(fs), 1n+List.length(&2, D.AF, fs)))), Pg.Term.size(t)), +efi: {D.St.first(st0) == fi : U32},
  +hs: D.HS(ds, ks, img, m, nx, fi, im, [D.Rt{y, Bk.Term.Tup{r, a1, a2}}, D.Rt{x, Bk.Term.Prj{h}}], Nil{}, fs, sp, pend, Con{p0, ps0}),
  hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{y, Bk.Term.Tup{r, a1, a2}}, D.Rt{x, Bk.Term.Prj{h}}], Nil{}, sp, fs, Con{p0, ps0}, zs),
  +hl: {List.length(&2, U32, regs) == 63n : Nat}, +h11: {List.get(&2, U32, regs, 11n) == Some{x} : Maybe<&2, U32>}, +h12: {List.get(&2, U32, regs, 12n) == Some{y} : Maybe<&2, U32>}, +h14: {List.get(&2, U32, regs, 14n) == Some{Mc.Img.quan(q)} : Maybe<&2, U32>},
  +h2: {List.get(&2, U32, regs, 2n) == Some{sp} : Maybe<&2, U32>}, +h3: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>}) ->
  PB(ds, ks, img, st0, t, w, lim, Cr.Cir.exec(f, Mc.M.do([Mc.M.set(Mc.R.p(), Mc.M.q(Mc.M.g(Mc.R.y()))), Mc.M.set(Mc.R.z(), Mc.M.f(2n, Mc.M.g(Mc.R.y()))), Mc.M.set(Mc.R.k(), Mc.M.f(3n, Mc.M.g(Mc.R.y()))), Mc.M.inc(Mc.R.z()), Mc.M.inc(Mc.R.k()), Mc.M.push(Mc.M.header(Mc.K.app_val(), Mc.M.g(Mc.R.q()), Mc.M.c(Mc.F.known())), Mc.M.g(Mc.R.k()), Mc.M.c(0)), Mc.M.push(Mc.M.header(Mc.K.app_val(), Mc.M.fld(Mc.M.g(Mc.R.p()), Mc.M.g(Mc.R.q())), Mc.M.and(Mc.M.c(Mc.F.known()), Mc.M.sub(Mc.M.c(0), Mc.M.ne(Mc.M.g(Mc.R.p()), Mc.M.c(0))))), Mc.M.g(Mc.R.z()), Mc.M.c(0)), Mc.M.set(Mc.R.n(), Mc.M.f(2n, Mc.M.g(Mc.R.x()))), Mc.M.inc(Mc.R.n()), Mc.M.dec(Mc.R.y()), Mc.M.dec(Mc.R.x()), Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())), Mc.M.set(Mc.R.mode(), Mc.M.c(0))]), X.X.st(regs, m, nx, fi, im, pg, lim, inp))):
  +A = {Bk.Term.Tup{r, a1, a2} : Bk.Term}
  +P = {Bk.Term.Prj{h} : Bk.Term}
  +PS = {Con{p0, ps0} : List<&2, U32>}
  +isy = hs.r1(ds, ks, img, m, nx, fi, im, y, A, x, P, Nil{}, fs, sp, pend, PS, hs)
  +cy = isk.cell(ds, m, im, fi, nx, ks, img, y, A, isy)
  +zc = D.Fd(2n, m, y)
  +kc = D.Fd(3n, m, y)
  +ev1 = {(%tup.q(ds, m, im, fi, nx, ks, img, y, r, a1, a2, isy) : {Cr.Cir.eval(Mc.M.q(Mc.M.g(Mc.R.y())), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) == Some{_} : Maybe<&2, U32>};
      X.ev.op(Wa.Wasm.Op.and{}, Mc.M.shr(Mc.M.f(0n, Mc.M.g(12n)), Mc.M.c(6)), Mc.M.c(3), X.X.st(regs, m, nx, fi, im, pg, lim, inp), U32.shrn(D.Fd(0n, m, y), 6n), 3,
        X.ev.op(Wa.Wasm.Op.shr_u{}, Mc.M.f(0n, Mc.M.g(12n)), Mc.M.c(6), X.X.st(regs, m, nx, fi, im, pg, lim, inp), D.Fd(0n, m, y), 6, X.ev.fld(0n, Mc.M.g(12n), X.X.st(regs, m, nx, fi, im, pg, lim, inp), y, h12, cy), {==}), {==})) :
    {Cr.Cir.eval(Mc.M.q(Mc.M.g(Mc.R.y())), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) == Some{Mc.Img.quan(r)} : Maybe<&2, U32>}}
  pb.set(f, ds, ks, img, st0, t, w, lim, 18n, Mc.M.q(Mc.M.g(Mc.R.y())), Mc.M.do([Mc.M.set(Mc.R.z(), Mc.M.f(2n, Mc.M.g(Mc.R.y()))), Mc.M.set(Mc.R.k(), Mc.M.f(3n, Mc.M.g(Mc.R.y()))), Mc.M.inc(Mc.R.z()), Mc.M.inc(Mc.R.k()), Mc.M.push(Mc.M.header(Mc.K.app_val(), Mc.M.g(Mc.R.q()), Mc.M.c(Mc.F.known())), Mc.M.g(Mc.R.k()), Mc.M.c(0)), Mc.M.push(Mc.M.header(Mc.K.app_val(), Mc.M.fld(Mc.M.g(Mc.R.p()), Mc.M.g(Mc.R.q())), Mc.M.and(Mc.M.c(Mc.F.known()), Mc.M.sub(Mc.M.c(0), Mc.M.ne(Mc.M.g(Mc.R.p()), Mc.M.c(0))))), Mc.M.g(Mc.R.z()), Mc.M.c(0)), Mc.M.set(Mc.R.n(), Mc.M.f(2n, Mc.M.g(Mc.R.x()))), Mc.M.inc(Mc.R.n()), Mc.M.dec(Mc.R.y()), Mc.M.dec(Mc.R.x()), Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())), Mc.M.set(Mc.R.mode(), Mc.M.c(0))]), X.X.st(regs, m, nx, fi, im, pg, lim, inp), Mc.Img.quan(r), ev1, hl, {==},
    pb.set(f, ds, ks, img, st0, t, w, lim, 13n, Mc.M.f(2n, Mc.M.g(Mc.R.y())), Mc.M.do([Mc.M.set(Mc.R.k(), Mc.M.f(3n, Mc.M.g(Mc.R.y()))), Mc.M.inc(Mc.R.z()), Mc.M.inc(Mc.R.k()), Mc.M.push(Mc.M.header(Mc.K.app_val(), Mc.M.g(Mc.R.q()), Mc.M.c(Mc.F.known())), Mc.M.g(Mc.R.k()), Mc.M.c(0)), Mc.M.push(Mc.M.header(Mc.K.app_val(), Mc.M.fld(Mc.M.g(Mc.R.p()), Mc.M.g(Mc.R.q())), Mc.M.and(Mc.M.c(Mc.F.known()), Mc.M.sub(Mc.M.c(0), Mc.M.ne(Mc.M.g(Mc.R.p()), Mc.M.c(0))))), Mc.M.g(Mc.R.z()), Mc.M.c(0)), Mc.M.set(Mc.R.n(), Mc.M.f(2n, Mc.M.g(Mc.R.x()))), Mc.M.inc(Mc.R.n()), Mc.M.dec(Mc.R.y()), Mc.M.dec(Mc.R.x()), Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())), Mc.M.set(Mc.R.mode(), Mc.M.c(0))]), X.X.st(X.X.set(regs, 18n, Mc.Img.quan(r)), m, nx, fi, im, pg, lim, inp), zc, X.ev.fld(2n, Mc.M.g(12n), X.X.st(X.X.set(regs, 18n, Mc.Img.quan(r)), m, nx, fi, im, pg, lim, inp), y, X.L.go(regs, 18n, 12n, Mc.Img.quan(r), y, {==}, h12), cy), X.L.len(regs, 18n, Mc.Img.quan(r), 63n, hl), {==},
      pb.set(f, ds, ks, img, st0, t, w, lim, 17n, Mc.M.f(3n, Mc.M.g(Mc.R.y())), Mc.M.do([Mc.M.inc(Mc.R.z()), Mc.M.inc(Mc.R.k()), Mc.M.push(Mc.M.header(Mc.K.app_val(), Mc.M.g(Mc.R.q()), Mc.M.c(Mc.F.known())), Mc.M.g(Mc.R.k()), Mc.M.c(0)), Mc.M.push(Mc.M.header(Mc.K.app_val(), Mc.M.fld(Mc.M.g(Mc.R.p()), Mc.M.g(Mc.R.q())), Mc.M.and(Mc.M.c(Mc.F.known()), Mc.M.sub(Mc.M.c(0), Mc.M.ne(Mc.M.g(Mc.R.p()), Mc.M.c(0))))), Mc.M.g(Mc.R.z()), Mc.M.c(0)), Mc.M.set(Mc.R.n(), Mc.M.f(2n, Mc.M.g(Mc.R.x()))), Mc.M.inc(Mc.R.n()), Mc.M.dec(Mc.R.y()), Mc.M.dec(Mc.R.x()), Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())), Mc.M.set(Mc.R.mode(), Mc.M.c(0))]), X.X.st(X.X.set(X.X.set(regs, 18n, Mc.Img.quan(r)), 13n, zc), m, nx, fi, im, pg, lim, inp), kc, X.ev.fld(3n, Mc.M.g(12n), X.X.st(X.X.set(X.X.set(regs, 18n, Mc.Img.quan(r)), 13n, zc), m, nx, fi, im, pg, lim, inp), y, X.L.go(X.X.set(regs, 18n, Mc.Img.quan(r)), 13n, 12n, zc, y, {==}, X.L.go(regs, 18n, 12n, Mc.Img.quan(r), y, {==}, h12)), cy), X.L.len(X.X.set(regs, 18n, Mc.Img.quan(r)), 13n, zc, 63n, X.L.len(regs, 18n, Mc.Img.quan(r), 63n, hl)), {==},
        pb.inc(f, ds, ks, img, st0, t, w, lim, X.X.set(X.X.set(X.X.set(regs, 18n, Mc.Img.quan(r)), 13n, zc), 17n, kc), m, nx, fi, im, pg, inp, 13n, [D.Rt{y, A}, D.Rt{x, P}], [D.Rt{kc, a2}], fs, sp, pend, PS, zc, a1, Nil{}, zs, Mc.M.do([Mc.M.inc(Mc.R.k()), Mc.M.push(Mc.M.header(Mc.K.app_val(), Mc.M.g(Mc.R.q()), Mc.M.c(Mc.F.known())), Mc.M.g(Mc.R.k()), Mc.M.c(0)), Mc.M.push(Mc.M.header(Mc.K.app_val(), Mc.M.fld(Mc.M.g(Mc.R.p()), Mc.M.g(Mc.R.q())), Mc.M.and(Mc.M.c(Mc.F.known()), Mc.M.sub(Mc.M.c(0), Mc.M.ne(Mc.M.g(Mc.R.p()), Mc.M.c(0))))), Mc.M.g(Mc.R.z()), Mc.M.c(0)), Mc.M.set(Mc.R.n(), Mc.M.f(2n, Mc.M.g(Mc.R.x()))), Mc.M.inc(Mc.R.n()), Mc.M.dec(Mc.R.y()), Mc.M.dec(Mc.R.x()), Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())), Mc.M.set(Mc.R.mode(), Mc.M.c(0))]),
          hsk.borrow2(ds, ks, img, m, nx, fi, im, [D.Rt{y, A}, D.Rt{x, P}], zc, a1, kc, a2, fs, sp, pend, PS,
            tup.a(ds, m, im, fi, nx, ks, img, y, r, a1, a2, isy), nodes.fst(y, A, [D.Rt{x, P}], m, zc, node.tup2(m, y, r, a1, a2)),
            tup.b(ds, m, im, fi, nx, ks, img, y, r, a1, a2, isy), nodes.fst(y, A, [D.Rt{x, P}], m, kc, node.tup3(m, y, r, a1, a2)), hs),
          hac, N.toLe(2n, 64n, {==}), X.L.go(X.X.set(X.X.set(regs, 18n, Mc.Img.quan(r)), 13n, zc), 17n, 13n, kc, zc, {==}, X.L.gs(X.X.set(regs, 18n, Mc.Img.quan(r)), 13n, zc, X.L.lt(X.X.set(regs, 18n, Mc.Img.quan(r)), 13n, X.L.len(regs, 18n, Mc.Img.quan(r), 63n, hl), {==}))),
          +m2 => +est2 => hs2 => hac2 =>
            pb.inc(f, ds, ks, img, st0, t, w, lim, X.X.set(X.X.set(X.X.set(regs, 18n, Mc.Img.quan(r)), 13n, zc), 17n, kc), m2, nx, fi, im, pg, inp, 17n, [D.Rt{zc, a1}, D.Rt{y, A}, D.Rt{x, P}], Nil{}, fs, sp, pend, PS, kc, a2, Nil{}, zs, Mc.M.do([Mc.M.push(Mc.M.header(Mc.K.app_val(), Mc.M.g(Mc.R.q()), Mc.M.c(Mc.F.known())), Mc.M.g(Mc.R.k()), Mc.M.c(0)), Mc.M.push(Mc.M.header(Mc.K.app_val(), Mc.M.fld(Mc.M.g(Mc.R.p()), Mc.M.g(Mc.R.q())), Mc.M.and(Mc.M.c(Mc.F.known()), Mc.M.sub(Mc.M.c(0), Mc.M.ne(Mc.M.g(Mc.R.p()), Mc.M.c(0))))), Mc.M.g(Mc.R.z()), Mc.M.c(0)), Mc.M.set(Mc.R.n(), Mc.M.f(2n, Mc.M.g(Mc.R.x()))), Mc.M.inc(Mc.R.n()), Mc.M.dec(Mc.R.y()), Mc.M.dec(Mc.R.x()), Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())), Mc.M.set(Mc.R.mode(), Mc.M.c(0))]),
              hsk.drop(ds, ks, img, m2, nx, fi, im, [D.Rt{zc, a1}, D.Rt{y, A}, D.Rt{x, P}], D.Rt{zc, a1}, [D.Rt{kc, a2}], fs, sp, pend, PS, hs2),
              hac2, N.toLe(3n, 64n, {==}), X.L.gs(X.X.set(X.X.set(regs, 18n, Mc.Img.quan(r)), 13n, zc), 17n, kc, X.L.lt(X.X.set(X.X.set(regs, 18n, Mc.Img.quan(r)), 13n, zc), 17n, X.L.len(X.X.set(regs, 18n, Mc.Img.quan(r)), 13n, zc, 63n, X.L.len(regs, 18n, Mc.Img.quan(r), 63n, hl)), {==})),
              +m3 => +est3 => hs3 => hac3 =>
                prj.p1(f, ds, ks, img, st0, t, w, lim, X.X.set(X.X.set(X.X.set(regs, 18n, Mc.Img.quan(r)), 13n, zc), 17n, kc), m3, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, y, zc, kc, r, q, a1, a2, h, es, afs, hvl, hmc,
                  N.le_rw_l(D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m2, fi), D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m3, fi), D.Stat(D.Mem.cells(st0), D.St.cells(st0), D.St.first(st0)),
                    Equal.sym(Nat, D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m3, fi), D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m2, fi), est3),
                    N.le_rw_l(D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi), D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m2, fi), D.Stat(D.Mem.cells(st0), D.St.cells(st0), D.St.first(st0)),
                      Equal.sym(Nat, D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m2, fi), D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi), est2), hS)),
                  hC, efi,
                  hsk.drop(ds, ks, img, m3, nx, fi, im, [D.Rt{kc, a2}, D.Rt{zc, a1}, D.Rt{y, A}, D.Rt{x, P}], D.Rt{kc, a2}, Nil{}, fs, sp, pend, PS, hs3), hac3,
                  X.L.len(X.X.set(X.X.set(regs, 18n, Mc.Img.quan(r)), 13n, zc), 17n, kc, 63n, X.L.len(X.X.set(regs, 18n, Mc.Img.quan(r)), 13n, zc, 63n, X.L.len(regs, 18n, Mc.Img.quan(r), 63n, hl))), X.L.go(X.X.set(X.X.set(regs, 18n, Mc.Img.quan(r)), 13n, zc), 17n, 11n, kc, x, {==}, X.L.go(X.X.set(regs, 18n, Mc.Img.quan(r)), 13n, 11n, zc, x, {==}, X.L.go(regs, 18n, 11n, Mc.Img.quan(r), x, {==}, h11))), X.L.go(X.X.set(X.X.set(regs, 18n, Mc.Img.quan(r)), 13n, zc), 17n, 12n, kc, y, {==}, X.L.go(X.X.set(regs, 18n, Mc.Img.quan(r)), 13n, 12n, zc, y, {==}, X.L.go(regs, 18n, 12n, Mc.Img.quan(r), y, {==}, h12))), X.L.go(X.X.set(X.X.set(regs, 18n, Mc.Img.quan(r)), 13n, zc), 17n, 13n, kc, zc, {==}, X.L.gs(X.X.set(regs, 18n, Mc.Img.quan(r)), 13n, zc, X.L.lt(X.X.set(regs, 18n, Mc.Img.quan(r)), 13n, X.L.len(regs, 18n, Mc.Img.quan(r), 63n, hl), {==}))), X.L.go(X.X.set(X.X.set(regs, 18n, Mc.Img.quan(r)), 13n, zc), 17n, 14n, kc, Mc.Img.quan(q), {==}, X.L.go(X.X.set(regs, 18n, Mc.Img.quan(r)), 13n, 14n, zc, Mc.Img.quan(q), {==}, X.L.go(regs, 18n, 14n, Mc.Img.quan(r), Mc.Img.quan(q), {==}, h14))), X.L.gs(X.X.set(X.X.set(regs, 18n, Mc.Img.quan(r)), 13n, zc), 17n, kc, X.L.lt(X.X.set(X.X.set(regs, 18n, Mc.Img.quan(r)), 13n, zc), 17n, X.L.len(X.X.set(regs, 18n, Mc.Img.quan(r)), 13n, zc, 63n, X.L.len(regs, 18n, Mc.Img.quan(r), 63n, hl)), {==})), X.L.go(X.X.set(X.X.set(regs, 18n, Mc.Img.quan(r)), 13n, zc), 17n, 18n, kc, Mc.Img.quan(r), {==}, X.L.go(X.X.set(regs, 18n, Mc.Img.quan(r)), 13n, 18n, zc, Mc.Img.quan(r), {==}, X.L.gs(regs, 18n, Mc.Img.quan(r), X.L.lt(regs, 18n, hl, {==})))),
                  X.L.go(X.X.set(X.X.set(regs, 18n, Mc.Img.quan(r)), 13n, zc), 17n, 2n, kc, sp, {==}, X.L.go(X.X.set(regs, 18n, Mc.Img.quan(r)), 13n, 2n, zc, sp, {==}, X.L.go(regs, 18n, 2n, Mc.Img.quan(r), sp, {==}, h2))), X.L.go(X.X.set(X.X.set(regs, 18n, Mc.Img.quan(r)), 13n, zc), 17n, 3n, kc, pend, {==}, X.L.go(X.X.set(regs, 18n, Mc.Img.quan(r)), 13n, 3n, zc, pend, {==}, X.L.go(regs, 18n, 3n, Mc.Img.quan(r), pend, {==}, h3)))))))))

# M.redex's branch of λ-matches of pairs
# ---------------------------------------

# M.need's test: q live and a a pair
def ev.cndp(+regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>,
  +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +y: U32, +a: Bk.Term, +q: Bk.Quan,
  h12: {List.get(&2, U32, regs, 12n) == Some{y} : Maybe<&2, U32>}, h14: {List.get(&2, U32, regs, 14n) == Some{Mc.Img.quan(q)} : Maybe<&2, U32>},
  +isy: D.Is(ds, m, im, fi, nx, ks, img, y, a)) ->
  {Cr.Cir.eval(Mc.M.and(Mc.M.ne(Mc.M.g(Mc.R.q()), Mc.M.c(0)), Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.y())), Mc.M.c(Mc.T.tup()))), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) == Some{Bool.to_u32(Bool.and(El.Quan.live(q), is.tup(a)))} : Maybe<&2, U32>}:
  %and.b2u(El.Quan.live(q), is.tup(a)) : {Cr.Cir.eval(Mc.M.and(Mc.M.ne(Mc.M.g(Mc.R.q()), Mc.M.c(0)), Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.y())), Mc.M.c(Mc.T.tup()))), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) == Some{_} : Maybe<&2, U32>}
  X.ev.op(Wa.Wasm.Op.and{}, Mc.M.ne(Mc.M.g(Mc.R.q()), Mc.M.c(0)), Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.y())), Mc.M.c(Mc.T.tup())), X.X.st(regs, m, nx, fi, im, pg, lim, inp),
    Bool.to_u32(El.Quan.live(q)), Bool.to_u32(is.tup(a)),
    (%q.live(q) : {Cr.Cir.eval(Mc.M.ne(Mc.M.g(Mc.R.q()), Mc.M.c(0)), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) == Some{_} : Maybe<&2, U32>};
      X.ev.op(Wa.Wasm.Op.ne{}, Mc.M.g(Mc.R.q()), Mc.M.c(0), X.X.st(regs, m, nx, fi, im, pg, lim, inp), Mc.Img.quan(q), 0, h14, {==})),
    (%tag.tup(a) : {Cr.Cir.eval(Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.y())), Mc.M.c(Mc.T.tup())), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) == Some{_} : Maybe<&2, U32>};
      %isk.tag(ds, m, im, fi, nx, ks, img, y, a, isy) : {Cr.Cir.eval(Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.y())), Mc.M.c(Mc.T.tup())), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) == Some{Wa.Wasm.op(Wa.Wasm.Op.eq{}, _, 10)} : Maybe<&2, U32>};
      ev.tagr(12n, regs, m, nx, fi, im, pg, lim, inp, y, 10, h12, isk.cell(ds, m, im, fi, nx, ks, img, y, a, isy))))

# M.redex's tests of x's tag, when x is a λ-match of pairs: its branch
def prj.sel(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st0: Cr.Cir.State, +t: Bk.Term, +w: Nat, +lim: U32, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +inp: List<&2, Word(8n)>,
  +x: U32, +h: Bk.Term, +h11: {List.get(&2, U32, regs, 11n) == Some{x} : Maybe<&2, U32>},
  +isx: D.Is(ds, m, im, fi, nx, ks, img, x, Bk.Term.Prj{h})) ->
  {Cr.Cir.exec(f, X.sel.t(X.sel.e(Mc.M.redex())), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) == Cr.Cir.exec(f, Mc.M.redex(), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) : Cr.Cir.Out}:
  +RX = Mc.M.redex()
  +E1 = X.sel.e(RX)
  +hc = isk.cell(ds, m, im, fi, nx, ks, img, x, Bk.Term.Prj{h}, isx)
  +et = isk.tag(ds, m, im, fi, nx, ks, img, x, Bk.Term.Prj{h}, isx)
  +et2 = et
  Equal.trans(Cr.Cir.Out, Cr.Cir.exec(f, X.sel.t(E1), X.X.st(regs, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(f, E1, X.X.st(regs, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(f, RX, X.X.st(regs, m, nx, fi, im, pg, lim, inp)),
    X.rw.if.t(f, X.sel.c(E1), X.sel.t(E1), X.sel.e(E1), X.X.st(regs, m, nx, fi, im, pg, lim, inp), 1,
      (%et2 : {Cr.Cir.eval(X.sel.c(E1), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) == Some{Wa.Wasm.op(Wa.Wasm.Op.eq{}, _, 11)} : Maybe<&2, U32>};
        ev.tagr(11n, regs, m, nx, fi, im, pg, lim, inp, x, 11, h11, hc)), {==}),
    X.rw.if.e(f, X.sel.c(RX), X.sel.t(RX), E1, X.X.st(regs, m, nx, fi, im, pg, lim, inp),
      (%et : {Cr.Cir.eval(X.sel.c(RX), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) == Some{Wa.Wasm.op(Wa.Wasm.Op.eq{}, _, 7)} : Maybe<&2, U32>};
        ev.tagr(11n, regs, m, nx, fi, im, pg, lim, inp, x, 7, h11, hc))))

# M.need halts with 2, when q is dead or a no pair: t is stuck
def prj.hlt(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st0: Cr.Cir.State, +t: Bk.Term, +w: Nat, +lim: U32, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +inp: List<&2, Word(8n)>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32, +p0: U32, +ps0: List<&2, U32>, +zs: List<&2, D.Rt>,
  +x: U32, +h: Bk.Term, +y: U32, +q: Bk.Quan, +a: Bk.Term,
  +hg: {Bool.and(El.Quan.live(q), is.tup(a)) == False{} : Bool},
  +hva: {Bool.or(Bool.not(El.Quan.live(q)), El.Eval.vals(ds, a, False{})) == True{} : Bool},
  +et0: {D.A.plugs(fs, Bk.Term.App{q, Bk.Term.Prj{h}, a}) == t : Bk.Term}, +afs: D.AFs.ok(ds, fs),
  +hmem: N.Le(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), Nat.max(D.Mem.cells(st0), D.Need(ds, st0, t))),
  +hmc: {D.Mem.cells(st0) == Nat.sub(U32.to_nat(nx), U32.to_nat(fi)) : Nat},
  +hS: N.Le(D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi), D.Stat(D.Mem.cells(st0), D.St.cells(st0), D.St.first(st0))),
  +hC: N.Le(Nat.add(Pg.Term.size(a), Nat.add(Pg.Term.size(Bk.Term.Prj{h}), Nat.add(frs.sz(fs), 1n+List.length(&2, D.AF, fs)))), Pg.Term.size(t)),
  +efi: {D.St.first(st0) == fi : U32},
  +hs: D.HS(ds, ks, img, m, nx, fi, im, [D.Rt{y, a}, D.Rt{x, Bk.Term.Prj{h}}], Nil{}, fs, sp, pend, Con{p0, ps0}),
  hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{y, a}, D.Rt{x, Bk.Term.Prj{h}}], Nil{}, sp, fs, Con{p0, ps0}, zs),
  +hl: {List.length(&2, U32, regs) == 63n : Nat},
  +h11: {List.get(&2, U32, regs, 11n) == Some{x} : Maybe<&2, U32>}, +h12: {List.get(&2, U32, regs, 12n) == Some{y} : Maybe<&2, U32>},
  +h14: {List.get(&2, U32, regs, 14n) == Some{Mc.Img.quan(q)} : Maybe<&2, U32>},
  +h2: {List.get(&2, U32, regs, 2n) == Some{sp} : Maybe<&2, U32>}, +h3: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>}) ->
  PB(ds, ks, img, st0, t, w, lim, Cr.Cir.exec(f, Mc.M.need(Mc.M.and(Mc.M.ne(Mc.M.g(Mc.R.q()), Mc.M.c(0)), Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.y())), Mc.M.c(Mc.T.tup()))), Mc.M.do([Mc.M.set(Mc.R.p(), Mc.M.q(Mc.M.g(Mc.R.y()))), Mc.M.set(Mc.R.z(), Mc.M.f(2n, Mc.M.g(Mc.R.y()))), Mc.M.set(Mc.R.k(), Mc.M.f(3n, Mc.M.g(Mc.R.y()))), Mc.M.inc(Mc.R.z()), Mc.M.inc(Mc.R.k()), Mc.M.push(Mc.M.header(Mc.K.app_val(), Mc.M.g(Mc.R.q()), Mc.M.c(Mc.F.known())), Mc.M.g(Mc.R.k()), Mc.M.c(0)), Mc.M.push(Mc.M.header(Mc.K.app_val(), Mc.M.fld(Mc.M.g(Mc.R.p()), Mc.M.g(Mc.R.q())), Mc.M.and(Mc.M.c(Mc.F.known()), Mc.M.sub(Mc.M.c(0), Mc.M.ne(Mc.M.g(Mc.R.p()), Mc.M.c(0))))), Mc.M.g(Mc.R.z()), Mc.M.c(0)), Mc.M.set(Mc.R.n(), Mc.M.f(2n, Mc.M.g(Mc.R.x()))), Mc.M.inc(Mc.R.n()), Mc.M.dec(Mc.R.y()), Mc.M.dec(Mc.R.x()), Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())), Mc.M.set(Mc.R.mode(), Mc.M.c(0))])), X.X.st(regs, m, nx, fi, im, pg, lim, inp))):
  +isy = hs.r1(ds, ks, img, m, nx, fi, im, y, a, x, Bk.Term.Prj{h}, Nil{}, fs, sp, pend, Con{p0, ps0}, hs)
  +ev0 = {(%hg : {Cr.Cir.eval(Mc.M.and(Mc.M.ne(Mc.M.g(Mc.R.q()), Mc.M.c(0)), Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.y())), Mc.M.c(Mc.T.tup()))), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) == Some{Bool.to_u32(_)} : Maybe<&2, U32>};
      ev.cndp(regs, m, nx, fi, im, pg, lim, inp, ds, ks, img, y, a, q, h12, h14, isy)) : {Cr.Cir.eval(Mc.M.and(Mc.M.ne(Mc.M.g(Mc.R.q()), Mc.M.c(0)), Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.y())), Mc.M.c(Mc.T.tup()))), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) == Some{0} : Maybe<&2, U32>}}
  +e = Equal.trans(Cr.Cir.Out, Cr.Cir.exec(f, Mc.M.need(Mc.M.and(Mc.M.ne(Mc.M.g(Mc.R.q()), Mc.M.c(0)), Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.y())), Mc.M.c(Mc.T.tup()))), Mc.M.do([Mc.M.set(Mc.R.p(), Mc.M.q(Mc.M.g(Mc.R.y()))), Mc.M.set(Mc.R.z(), Mc.M.f(2n, Mc.M.g(Mc.R.y()))), Mc.M.set(Mc.R.k(), Mc.M.f(3n, Mc.M.g(Mc.R.y()))), Mc.M.inc(Mc.R.z()), Mc.M.inc(Mc.R.k()), Mc.M.push(Mc.M.header(Mc.K.app_val(), Mc.M.g(Mc.R.q()), Mc.M.c(Mc.F.known())), Mc.M.g(Mc.R.k()), Mc.M.c(0)), Mc.M.push(Mc.M.header(Mc.K.app_val(), Mc.M.fld(Mc.M.g(Mc.R.p()), Mc.M.g(Mc.R.q())), Mc.M.and(Mc.M.c(Mc.F.known()), Mc.M.sub(Mc.M.c(0), Mc.M.ne(Mc.M.g(Mc.R.p()), Mc.M.c(0))))), Mc.M.g(Mc.R.z()), Mc.M.c(0)), Mc.M.set(Mc.R.n(), Mc.M.f(2n, Mc.M.g(Mc.R.x()))), Mc.M.inc(Mc.R.n()), Mc.M.dec(Mc.R.y()), Mc.M.dec(Mc.R.x()), Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())), Mc.M.set(Mc.R.mode(), Mc.M.c(0))])), X.X.st(regs, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(f, Mc.M.halt(2), X.X.st(regs, m, nx, fi, im, pg, lim, inp)), Cr.Cir.Out.halt{2, X.X.st(regs, m, nx, fi, im, pg, lim, inp)},
    Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, Mc.M.halt(2), X.X.st(regs, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(f, Mc.M.need(Mc.M.and(Mc.M.ne(Mc.M.g(Mc.R.q()), Mc.M.c(0)), Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.y())), Mc.M.c(Mc.T.tup()))), Mc.M.do([Mc.M.set(Mc.R.p(), Mc.M.q(Mc.M.g(Mc.R.y()))), Mc.M.set(Mc.R.z(), Mc.M.f(2n, Mc.M.g(Mc.R.y()))), Mc.M.set(Mc.R.k(), Mc.M.f(3n, Mc.M.g(Mc.R.y()))), Mc.M.inc(Mc.R.z()), Mc.M.inc(Mc.R.k()), Mc.M.push(Mc.M.header(Mc.K.app_val(), Mc.M.g(Mc.R.q()), Mc.M.c(Mc.F.known())), Mc.M.g(Mc.R.k()), Mc.M.c(0)), Mc.M.push(Mc.M.header(Mc.K.app_val(), Mc.M.fld(Mc.M.g(Mc.R.p()), Mc.M.g(Mc.R.q())), Mc.M.and(Mc.M.c(Mc.F.known()), Mc.M.sub(Mc.M.c(0), Mc.M.ne(Mc.M.g(Mc.R.p()), Mc.M.c(0))))), Mc.M.g(Mc.R.z()), Mc.M.c(0)), Mc.M.set(Mc.R.n(), Mc.M.f(2n, Mc.M.g(Mc.R.x()))), Mc.M.inc(Mc.R.n()), Mc.M.dec(Mc.R.y()), Mc.M.dec(Mc.R.x()), Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())), Mc.M.set(Mc.R.mode(), Mc.M.c(0))])), X.X.st(regs, m, nx, fi, im, pg, lim, inp)), X.rw.if.e(f, Mc.M.and(Mc.M.ne(Mc.M.g(Mc.R.q()), Mc.M.c(0)), Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.y())), Mc.M.c(Mc.T.tup()))), Mc.M.do([Mc.M.set(Mc.R.p(), Mc.M.q(Mc.M.g(Mc.R.y()))), Mc.M.set(Mc.R.z(), Mc.M.f(2n, Mc.M.g(Mc.R.y()))), Mc.M.set(Mc.R.k(), Mc.M.f(3n, Mc.M.g(Mc.R.y()))), Mc.M.inc(Mc.R.z()), Mc.M.inc(Mc.R.k()), Mc.M.push(Mc.M.header(Mc.K.app_val(), Mc.M.g(Mc.R.q()), Mc.M.c(Mc.F.known())), Mc.M.g(Mc.R.k()), Mc.M.c(0)), Mc.M.push(Mc.M.header(Mc.K.app_val(), Mc.M.fld(Mc.M.g(Mc.R.p()), Mc.M.g(Mc.R.q())), Mc.M.and(Mc.M.c(Mc.F.known()), Mc.M.sub(Mc.M.c(0), Mc.M.ne(Mc.M.g(Mc.R.p()), Mc.M.c(0))))), Mc.M.g(Mc.R.z()), Mc.M.c(0)), Mc.M.set(Mc.R.n(), Mc.M.f(2n, Mc.M.g(Mc.R.x()))), Mc.M.inc(Mc.R.n()), Mc.M.dec(Mc.R.y()), Mc.M.dec(Mc.R.x()), Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())), Mc.M.set(Mc.R.mode(), Mc.M.c(0))]), Mc.M.halt(2), X.X.st(regs, m, nx, fi, im, pg, lim, inp), ev0)),
    K.eq.halt(f, 2, X.X.st(regs, m, nx, fi, im, pg, lim, inp)))
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, Mc.M.need(Mc.M.and(Mc.M.ne(Mc.M.g(Mc.R.q()), Mc.M.c(0)), Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.y())), Mc.M.c(Mc.T.tup()))), Mc.M.do([Mc.M.set(Mc.R.p(), Mc.M.q(Mc.M.g(Mc.R.y()))), Mc.M.set(Mc.R.z(), Mc.M.f(2n, Mc.M.g(Mc.R.y()))), Mc.M.set(Mc.R.k(), Mc.M.f(3n, Mc.M.g(Mc.R.y()))), Mc.M.inc(Mc.R.z()), Mc.M.inc(Mc.R.k()), Mc.M.push(Mc.M.header(Mc.K.app_val(), Mc.M.g(Mc.R.q()), Mc.M.c(Mc.F.known())), Mc.M.g(Mc.R.k()), Mc.M.c(0)), Mc.M.push(Mc.M.header(Mc.K.app_val(), Mc.M.fld(Mc.M.g(Mc.R.p()), Mc.M.g(Mc.R.q())), Mc.M.and(Mc.M.c(Mc.F.known()), Mc.M.sub(Mc.M.c(0), Mc.M.ne(Mc.M.g(Mc.R.p()), Mc.M.c(0))))), Mc.M.g(Mc.R.z()), Mc.M.c(0)), Mc.M.set(Mc.R.n(), Mc.M.f(2n, Mc.M.g(Mc.R.x()))), Mc.M.inc(Mc.R.n()), Mc.M.dec(Mc.R.y()), Mc.M.dec(Mc.R.x()), Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())), Mc.M.set(Mc.R.mode(), Mc.M.c(0))])), X.X.st(regs, m, nx, fi, im, pg, lim, inp)), Cr.Cir.Out.halt{2, X.X.st(regs, m, nx, fi, im, pg, lim, inp)}, e) : PB(ds, ks, img, st0, t, w, lim, _)
  K.hr.stuck(ds, t, X.X.st(regs, m, nx, fi, im, pg, lim, inp),
    (%et0 : D.P2({El.Eval.step(ds, _) == None{} : Maybe<Bk.Term>}, {El.Eval.vals(ds, _, False{}) == False{} : Bool});
      stuck.plugs(ds, fs, Bk.Term.App{q, Bk.Term.Prj{h}, a}, afs, prj.stuck(ds, q, h, a, hg, hva))))

# M.need passes: q live and a pair
def prj.lv(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st0: Cr.Cir.State, +t: Bk.Term, +w: Nat, +lim: U32, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +inp: List<&2, Word(8n)>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32, +p0: U32, +ps0: List<&2, U32>, +zs: List<&2, D.Rt>,
  +x: U32, +h: Bk.Term, +y: U32, +q: Bk.Quan, +r: Bk.Quan, +a1: Bk.Term, +a2: Bk.Term, +hlv: {El.Quan.live(q) == True{} : Bool},
  +hvl: {El.Eval.vals(ds, Bk.Term.Tup{r, a1, a2}, False{}) == True{} : Bool},
  +et0: {D.A.plugs(fs, Bk.Term.App{q, Bk.Term.Prj{h}, Bk.Term.Tup{r, a1, a2}}) == t : Bk.Term}, +afs: D.AFs.ok(ds, fs),
  +hmem: N.Le(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), Nat.max(D.Mem.cells(st0), D.Need(ds, st0, t))),
  +hmc: {D.Mem.cells(st0) == Nat.sub(U32.to_nat(nx), U32.to_nat(fi)) : Nat},
  +hS: N.Le(D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi), D.Stat(D.Mem.cells(st0), D.St.cells(st0), D.St.first(st0))),
  +hC: N.Le(Nat.add(Pg.Term.size(Bk.Term.Tup{r, a1, a2}), Nat.add(Pg.Term.size(Bk.Term.Prj{h}), Nat.add(frs.sz(fs), 1n+List.length(&2, D.AF, fs)))), Pg.Term.size(t)),
  +efi: {D.St.first(st0) == fi : U32},
  +hs: D.HS(ds, ks, img, m, nx, fi, im, [D.Rt{y, Bk.Term.Tup{r, a1, a2}}, D.Rt{x, Bk.Term.Prj{h}}], Nil{}, fs, sp, pend, Con{p0, ps0}),
  hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{y, Bk.Term.Tup{r, a1, a2}}, D.Rt{x, Bk.Term.Prj{h}}], Nil{}, sp, fs, Con{p0, ps0}, zs),
  +hl: {List.length(&2, U32, regs) == 63n : Nat},
  +h11: {List.get(&2, U32, regs, 11n) == Some{x} : Maybe<&2, U32>}, +h12: {List.get(&2, U32, regs, 12n) == Some{y} : Maybe<&2, U32>},
  +h14: {List.get(&2, U32, regs, 14n) == Some{Mc.Img.quan(q)} : Maybe<&2, U32>},
  +h2: {List.get(&2, U32, regs, 2n) == Some{sp} : Maybe<&2, U32>}, +h3: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>}) ->
  PB(ds, ks, img, st0, t, w, lim, Cr.Cir.exec(f, Mc.M.need(Mc.M.and(Mc.M.ne(Mc.M.g(Mc.R.q()), Mc.M.c(0)), Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.y())), Mc.M.c(Mc.T.tup()))), Mc.M.do([Mc.M.set(Mc.R.p(), Mc.M.q(Mc.M.g(Mc.R.y()))), Mc.M.set(Mc.R.z(), Mc.M.f(2n, Mc.M.g(Mc.R.y()))), Mc.M.set(Mc.R.k(), Mc.M.f(3n, Mc.M.g(Mc.R.y()))), Mc.M.inc(Mc.R.z()), Mc.M.inc(Mc.R.k()), Mc.M.push(Mc.M.header(Mc.K.app_val(), Mc.M.g(Mc.R.q()), Mc.M.c(Mc.F.known())), Mc.M.g(Mc.R.k()), Mc.M.c(0)), Mc.M.push(Mc.M.header(Mc.K.app_val(), Mc.M.fld(Mc.M.g(Mc.R.p()), Mc.M.g(Mc.R.q())), Mc.M.and(Mc.M.c(Mc.F.known()), Mc.M.sub(Mc.M.c(0), Mc.M.ne(Mc.M.g(Mc.R.p()), Mc.M.c(0))))), Mc.M.g(Mc.R.z()), Mc.M.c(0)), Mc.M.set(Mc.R.n(), Mc.M.f(2n, Mc.M.g(Mc.R.x()))), Mc.M.inc(Mc.R.n()), Mc.M.dec(Mc.R.y()), Mc.M.dec(Mc.R.x()), Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())), Mc.M.set(Mc.R.mode(), Mc.M.c(0))])), X.X.st(regs, m, nx, fi, im, pg, lim, inp))):
  +A = {Bk.Term.Tup{r, a1, a2} : Bk.Term}
  +isy = hs.r1(ds, ks, img, m, nx, fi, im, y, A, x, Bk.Term.Prj{h}, Nil{}, fs, sp, pend, Con{p0, ps0}, hs)
  +ev1 = {(%hlv : {Cr.Cir.eval(Mc.M.and(Mc.M.ne(Mc.M.g(Mc.R.q()), Mc.M.c(0)), Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.y())), Mc.M.c(Mc.T.tup()))), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) == Some{Bool.to_u32(Bool.and(_, True{}))} : Maybe<&2, U32>};
      ev.cndp(regs, m, nx, fi, im, pg, lim, inp, ds, ks, img, y, A, q, h12, h14, isy)) : {Cr.Cir.eval(Mc.M.and(Mc.M.ne(Mc.M.g(Mc.R.q()), Mc.M.c(0)), Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.y())), Mc.M.c(Mc.T.tup()))), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) == Some{1} : Maybe<&2, U32>}}
  +es = {(%et0 : {El.Eval.step(ds, _) == Some{D.A.plugs(fs, Bk.Term.App{q, Bk.Term.App{El.Quan.fld(r, q), h, a1}, a2})} : Maybe<Bk.Term>};
      step.plugs(ds, fs, Bk.Term.App{q, Bk.Term.Prj{h}, A}, Bk.Term.App{q, Bk.Term.App{El.Quan.fld(r, q), h, a1}, a2}, afs, prj.step(ds, q, h, r, a1, a2, hlv, hvl))) :
    {El.Eval.step(ds, t) == Some{D.A.plugs(fs, Bk.Term.App{q, Bk.Term.App{El.Quan.fld(r, q), h, a1}, a2})} : Maybe<Bk.Term>}}
  %X.rw.if.t(f, Mc.M.and(Mc.M.ne(Mc.M.g(Mc.R.q()), Mc.M.c(0)), Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.y())), Mc.M.c(Mc.T.tup()))), Mc.M.do([Mc.M.set(Mc.R.p(), Mc.M.q(Mc.M.g(Mc.R.y()))), Mc.M.set(Mc.R.z(), Mc.M.f(2n, Mc.M.g(Mc.R.y()))), Mc.M.set(Mc.R.k(), Mc.M.f(3n, Mc.M.g(Mc.R.y()))), Mc.M.inc(Mc.R.z()), Mc.M.inc(Mc.R.k()), Mc.M.push(Mc.M.header(Mc.K.app_val(), Mc.M.g(Mc.R.q()), Mc.M.c(Mc.F.known())), Mc.M.g(Mc.R.k()), Mc.M.c(0)), Mc.M.push(Mc.M.header(Mc.K.app_val(), Mc.M.fld(Mc.M.g(Mc.R.p()), Mc.M.g(Mc.R.q())), Mc.M.and(Mc.M.c(Mc.F.known()), Mc.M.sub(Mc.M.c(0), Mc.M.ne(Mc.M.g(Mc.R.p()), Mc.M.c(0))))), Mc.M.g(Mc.R.z()), Mc.M.c(0)), Mc.M.set(Mc.R.n(), Mc.M.f(2n, Mc.M.g(Mc.R.x()))), Mc.M.inc(Mc.R.n()), Mc.M.dec(Mc.R.y()), Mc.M.dec(Mc.R.x()), Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())), Mc.M.set(Mc.R.mode(), Mc.M.c(0))]), Mc.M.halt(2), X.X.st(regs, m, nx, fi, im, pg, lim, inp), 1, ev1, {==}) : PB(ds, ks, img, st0, t, w, lim, _)
  prj.inc(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, y, r, q, a1, a2, h, es, afs, hvl, hmc, hS, hC, efi, hs, hac, hl, h11, h12, h14, h2, h3)

# M.need and its branches, by the argument's form and q
def prj.go(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st0: Cr.Cir.State, +t: Bk.Term, +w: Nat, +lim: U32, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +inp: List<&2, Word(8n)>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32, +p0: U32, +ps0: List<&2, U32>, +zs: List<&2, D.Rt>,
  +x: U32, +h: Bk.Term, +y: U32, +q: Bk.Quan, +a: Bk.Term,
  +hva: {Bool.or(Bool.not(El.Quan.live(q)), El.Eval.vals(ds, a, False{})) == True{} : Bool},
  +et0: {D.A.plugs(fs, Bk.Term.App{q, Bk.Term.Prj{h}, a}) == t : Bk.Term}, +afs: D.AFs.ok(ds, fs),
  +hmem: N.Le(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), Nat.max(D.Mem.cells(st0), D.Need(ds, st0, t))),
  +hmc: {D.Mem.cells(st0) == Nat.sub(U32.to_nat(nx), U32.to_nat(fi)) : Nat},
  +hS: N.Le(D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi), D.Stat(D.Mem.cells(st0), D.St.cells(st0), D.St.first(st0))),
  +hC: N.Le(Nat.add(Pg.Term.size(a), Nat.add(Pg.Term.size(Bk.Term.Prj{h}), Nat.add(frs.sz(fs), 1n+List.length(&2, D.AF, fs)))), Pg.Term.size(t)),
  +efi: {D.St.first(st0) == fi : U32},
  +hs: D.HS(ds, ks, img, m, nx, fi, im, [D.Rt{y, a}, D.Rt{x, Bk.Term.Prj{h}}], Nil{}, fs, sp, pend, Con{p0, ps0}),
  hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{y, a}, D.Rt{x, Bk.Term.Prj{h}}], Nil{}, sp, fs, Con{p0, ps0}, zs),
  +hl: {List.length(&2, U32, regs) == 63n : Nat},
  +h11: {List.get(&2, U32, regs, 11n) == Some{x} : Maybe<&2, U32>}, +h12: {List.get(&2, U32, regs, 12n) == Some{y} : Maybe<&2, U32>},
  +h14: {List.get(&2, U32, regs, 14n) == Some{Mc.Img.quan(q)} : Maybe<&2, U32>},
  +h2: {List.get(&2, U32, regs, 2n) == Some{sp} : Maybe<&2, U32>}, +h3: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>}) ->
  PB(ds, ks, img, st0, t, w, lim, Cr.Cir.exec(f, Mc.M.need(Mc.M.and(Mc.M.ne(Mc.M.g(Mc.R.q()), Mc.M.c(0)), Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.y())), Mc.M.c(Mc.T.tup()))), Mc.M.do([Mc.M.set(Mc.R.p(), Mc.M.q(Mc.M.g(Mc.R.y()))), Mc.M.set(Mc.R.z(), Mc.M.f(2n, Mc.M.g(Mc.R.y()))), Mc.M.set(Mc.R.k(), Mc.M.f(3n, Mc.M.g(Mc.R.y()))), Mc.M.inc(Mc.R.z()), Mc.M.inc(Mc.R.k()), Mc.M.push(Mc.M.header(Mc.K.app_val(), Mc.M.g(Mc.R.q()), Mc.M.c(Mc.F.known())), Mc.M.g(Mc.R.k()), Mc.M.c(0)), Mc.M.push(Mc.M.header(Mc.K.app_val(), Mc.M.fld(Mc.M.g(Mc.R.p()), Mc.M.g(Mc.R.q())), Mc.M.and(Mc.M.c(Mc.F.known()), Mc.M.sub(Mc.M.c(0), Mc.M.ne(Mc.M.g(Mc.R.p()), Mc.M.c(0))))), Mc.M.g(Mc.R.z()), Mc.M.c(0)), Mc.M.set(Mc.R.n(), Mc.M.f(2n, Mc.M.g(Mc.R.x()))), Mc.M.inc(Mc.R.n()), Mc.M.dec(Mc.R.y()), Mc.M.dec(Mc.R.x()), Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.n())), Mc.M.set(Mc.R.mode(), Mc.M.c(0))])), X.X.st(regs, m, nx, fi, im, pg, lim, inp))):
  match q:
    case Bk.Quan.Q0{}:
      prj.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, h, y, Bk.Quan.Q0{}, a, {==}, hva, et0, afs, hmem, hmc, hS, hC, efi, hs, hac, hl, h11, h12, h14, h2, h3)
    case Bk.Quan.Q1{}:
      match a:
        case Bk.Term.Var{+i}:
          prj.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, h, y, Bk.Quan.Q1{}, Bk.Term.Var{i}, {==}, hva, et0, afs, hmem, hmc, hS, hC, efi, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Ref{+i}:
          prj.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, h, y, Bk.Quan.Q1{}, Bk.Term.Ref{i}, {==}, hva, et0, afs, hmem, hmc, hS, hC, efi, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Ann{+i0, +i1}:
          prj.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, h, y, Bk.Quan.Q1{}, Bk.Term.Ann{i0, i1}, {==}, hva, et0, afs, hmem, hmc, hS, hC, efi, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Let{+i0, +i1, +i2}:
          prj.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, h, y, Bk.Quan.Q1{}, Bk.Term.Let{i0, i1, i2}, {==}, hva, et0, afs, hmem, hmc, hS, hC, efi, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Typ{+i}:
          prj.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, h, y, Bk.Quan.Q1{}, Bk.Term.Typ{i}, {==}, hva, et0, afs, hmem, hmc, hS, hC, efi, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Min{+i0, +i1}:
          prj.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, h, y, Bk.Quan.Q1{}, Bk.Term.Min{i0, i1}, {==}, hva, et0, afs, hmem, hmc, hS, hC, efi, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.All{+i0, +i1, +i2}:
          prj.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, h, y, Bk.Quan.Q1{}, Bk.Term.All{i0, i1, i2}, {==}, hva, et0, afs, hmem, hmc, hS, hC, efi, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Lam{+i0, +i1}:
          prj.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, h, y, Bk.Quan.Q1{}, Bk.Term.Lam{i0, i1}, {==}, hva, et0, afs, hmem, hmc, hS, hC, efi, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.App{+i0, +i1, +i2}:
          prj.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, h, y, Bk.Quan.Q1{}, Bk.Term.App{i0, i1, i2}, {==}, hva, et0, afs, hmem, hmc, hS, hC, efi, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Sig{+i0, +i1, +i2}:
          prj.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, h, y, Bk.Quan.Q1{}, Bk.Term.Sig{i0, i1, i2}, {==}, hva, et0, afs, hmem, hmc, hS, hC, efi, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Tup{+r, +a1, +a2}:
          prj.lv(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, h, y, Bk.Quan.Q1{}, r, a1, a2, {==}, hva, et0, afs, hmem, hmc, hS, hC, efi, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Prj{+i}:
          prj.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, h, y, Bk.Quan.Q1{}, Bk.Term.Prj{i}, {==}, hva, et0, afs, hmem, hmc, hS, hC, efi, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Enu{+i}:
          prj.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, h, y, Bk.Quan.Q1{}, Bk.Term.Enu{i}, {==}, hva, et0, afs, hmem, hmc, hS, hC, efi, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Lab{+i}:
          prj.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, h, y, Bk.Quan.Q1{}, Bk.Term.Lab{i}, {==}, hva, et0, afs, hmem, hmc, hS, hC, efi, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Mat{+i0, +i1, +i2}:
          prj.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, h, y, Bk.Quan.Q1{}, Bk.Term.Mat{i0, i1, i2}, {==}, hva, et0, afs, hmem, hmc, hS, hC, efi, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Efq{}:
          prj.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, h, y, Bk.Quan.Q1{}, Bk.Term.Efq{}, {==}, hva, et0, afs, hmem, hmc, hS, hC, efi, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Eql{+i0, +i1, +i2}:
          prj.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, h, y, Bk.Quan.Q1{}, Bk.Term.Eql{i0, i1, i2}, {==}, hva, et0, afs, hmem, hmc, hS, hC, efi, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Rfl{}:
          prj.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, h, y, Bk.Quan.Q1{}, Bk.Term.Rfl{}, {==}, hva, et0, afs, hmem, hmc, hS, hC, efi, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Rwt{+i0, +i1, +i2}:
          prj.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, h, y, Bk.Quan.Q1{}, Bk.Term.Rwt{i0, i1, i2}, {==}, hva, et0, afs, hmem, hmc, hS, hC, efi, hs, hac, hl, h11, h12, h14, h2, h3)
    case Bk.Quan.Q2{}:
      match a:
        case Bk.Term.Var{+i}:
          prj.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, h, y, Bk.Quan.Q2{}, Bk.Term.Var{i}, {==}, hva, et0, afs, hmem, hmc, hS, hC, efi, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Ref{+i}:
          prj.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, h, y, Bk.Quan.Q2{}, Bk.Term.Ref{i}, {==}, hva, et0, afs, hmem, hmc, hS, hC, efi, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Ann{+i0, +i1}:
          prj.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, h, y, Bk.Quan.Q2{}, Bk.Term.Ann{i0, i1}, {==}, hva, et0, afs, hmem, hmc, hS, hC, efi, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Let{+i0, +i1, +i2}:
          prj.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, h, y, Bk.Quan.Q2{}, Bk.Term.Let{i0, i1, i2}, {==}, hva, et0, afs, hmem, hmc, hS, hC, efi, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Typ{+i}:
          prj.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, h, y, Bk.Quan.Q2{}, Bk.Term.Typ{i}, {==}, hva, et0, afs, hmem, hmc, hS, hC, efi, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Min{+i0, +i1}:
          prj.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, h, y, Bk.Quan.Q2{}, Bk.Term.Min{i0, i1}, {==}, hva, et0, afs, hmem, hmc, hS, hC, efi, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.All{+i0, +i1, +i2}:
          prj.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, h, y, Bk.Quan.Q2{}, Bk.Term.All{i0, i1, i2}, {==}, hva, et0, afs, hmem, hmc, hS, hC, efi, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Lam{+i0, +i1}:
          prj.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, h, y, Bk.Quan.Q2{}, Bk.Term.Lam{i0, i1}, {==}, hva, et0, afs, hmem, hmc, hS, hC, efi, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.App{+i0, +i1, +i2}:
          prj.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, h, y, Bk.Quan.Q2{}, Bk.Term.App{i0, i1, i2}, {==}, hva, et0, afs, hmem, hmc, hS, hC, efi, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Sig{+i0, +i1, +i2}:
          prj.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, h, y, Bk.Quan.Q2{}, Bk.Term.Sig{i0, i1, i2}, {==}, hva, et0, afs, hmem, hmc, hS, hC, efi, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Tup{+r, +a1, +a2}:
          prj.lv(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, h, y, Bk.Quan.Q2{}, r, a1, a2, {==}, hva, et0, afs, hmem, hmc, hS, hC, efi, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Prj{+i}:
          prj.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, h, y, Bk.Quan.Q2{}, Bk.Term.Prj{i}, {==}, hva, et0, afs, hmem, hmc, hS, hC, efi, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Enu{+i}:
          prj.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, h, y, Bk.Quan.Q2{}, Bk.Term.Enu{i}, {==}, hva, et0, afs, hmem, hmc, hS, hC, efi, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Lab{+i}:
          prj.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, h, y, Bk.Quan.Q2{}, Bk.Term.Lab{i}, {==}, hva, et0, afs, hmem, hmc, hS, hC, efi, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Mat{+i0, +i1, +i2}:
          prj.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, h, y, Bk.Quan.Q2{}, Bk.Term.Mat{i0, i1, i2}, {==}, hva, et0, afs, hmem, hmc, hS, hC, efi, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Efq{}:
          prj.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, h, y, Bk.Quan.Q2{}, Bk.Term.Efq{}, {==}, hva, et0, afs, hmem, hmc, hS, hC, efi, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Eql{+i0, +i1, +i2}:
          prj.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, h, y, Bk.Quan.Q2{}, Bk.Term.Eql{i0, i1, i2}, {==}, hva, et0, afs, hmem, hmc, hS, hC, efi, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Rfl{}:
          prj.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, h, y, Bk.Quan.Q2{}, Bk.Term.Rfl{}, {==}, hva, et0, afs, hmem, hmc, hS, hC, efi, hs, hac, hl, h11, h12, h14, h2, h3)
        case Bk.Term.Rwt{+i0, +i1, +i2}:
          prj.hlt(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, h, y, Bk.Quan.Q2{}, Bk.Term.Rwt{i0, i1, i2}, {==}, hva, et0, afs, hmem, hmc, hS, hC, efi, hs, hac, hl, h11, h12, h14, h2, h3)

# M.redex, on a λ-match of pairs
def prj.redex(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st0: Cr.Cir.State, +t: Bk.Term, +w: Nat, +lim: U32, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +inp: List<&2, Word(8n)>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32, +p0: U32, +ps0: List<&2, U32>, +zs: List<&2, D.Rt>,
  +x: U32, +h: Bk.Term, +y: U32, +q: Bk.Quan, +a: Bk.Term,
  +hva: {Bool.or(Bool.not(El.Quan.live(q)), El.Eval.vals(ds, a, False{})) == True{} : Bool},
  +et0: {D.A.plugs(fs, Bk.Term.App{q, Bk.Term.Prj{h}, a}) == t : Bk.Term}, +afs: D.AFs.ok(ds, fs),
  +hmem: N.Le(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), Nat.max(D.Mem.cells(st0), D.Need(ds, st0, t))),
  +hmc: {D.Mem.cells(st0) == Nat.sub(U32.to_nat(nx), U32.to_nat(fi)) : Nat},
  +hS: N.Le(D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi), D.Stat(D.Mem.cells(st0), D.St.cells(st0), D.St.first(st0))),
  +hC: N.Le(Nat.add(Pg.Term.size(a), Nat.add(Pg.Term.size(Bk.Term.Prj{h}), Nat.add(frs.sz(fs), 1n+List.length(&2, D.AF, fs)))), Pg.Term.size(t)),
  +efi: {D.St.first(st0) == fi : U32},
  +hs: D.HS(ds, ks, img, m, nx, fi, im, [D.Rt{y, a}, D.Rt{x, Bk.Term.Prj{h}}], Nil{}, fs, sp, pend, Con{p0, ps0}),
  hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{y, a}, D.Rt{x, Bk.Term.Prj{h}}], Nil{}, sp, fs, Con{p0, ps0}, zs),
  +hl: {List.length(&2, U32, regs) == 63n : Nat},
  +h11: {List.get(&2, U32, regs, 11n) == Some{x} : Maybe<&2, U32>}, +h12: {List.get(&2, U32, regs, 12n) == Some{y} : Maybe<&2, U32>},
  +h14: {List.get(&2, U32, regs, 14n) == Some{Mc.Img.quan(q)} : Maybe<&2, U32>},
  +h2: {List.get(&2, U32, regs, 2n) == Some{sp} : Maybe<&2, U32>}, +h3: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>}) ->
  PB(ds, ks, img, st0, t, w, lim, Cr.Cir.exec(f, Mc.M.redex(), X.X.st(regs, m, nx, fi, im, pg, lim, inp))):
  +isx = hs.r2(ds, ks, img, m, nx, fi, im, y, a, x, Bk.Term.Prj{h}, Nil{}, fs, sp, pend, Con{p0, ps0}, hs)
  %prj.sel(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, x, h, h11, isx) : PB(ds, ks, img, st0, t, w, lim, _)
  prj.go(f, ds, ks, img, st0, t, w, lim, regs, m, nx, fi, im, pg, inp, fs, sp, pend, p0, ps0, zs, x, h, y, q, a, hva, et0, afs, hmem, hmc, hS, hC, efi, hs, hac, hl, h11, h12, h14, h2, h3)

# mv.ret.app.prj and mv.ret.fun.prj, as the λ-match moves; t's nodes give
# the core of need.prj (hc.app, hc.fun)

def hc.app(+kind: D.FK, +q: Bk.Quan, +k: Bool, +a: Bk.Term, +b: Bk.Term, +fs: List<&2, D.AF>, +m: Cr.Cir.Cells, +sp: U32, +v: Bk.Term, -t: Bk.Term,
  h38: {U32.is_eq(D.FK.tag(kind), 38) == False{} : Bool}, et: {D.A.plugs(Con{D.AF{kind, q, k, a, b}, fs}, v) == t : Bk.Term}) ->
  N.Le(Nat.add(Pg.Term.size(a), Nat.add(Pg.Term.size(v), Nat.add(frs.sz(fs), 1n+List.length(&2, D.AF, fs)))), Pg.Term.size(t)):
  +f1 = D.Fd(1n, m, sp)
  +V = Pg.Term.size(v)
  +S = Pg.Term.size(a)
  +R = frs.sz(fs)
  +L = List.length(&2, D.AF, fs)
  +C = Nat.add(S, Nat.add(V, Nat.add(R, 1n+L)))
  %et : N.Le(C, Pg.Term.size(_))
  +FR = D.Fr.rts(fs, m, f1)
  +FC = D.Fr.cells(fs, m, f1)
  +Fb = D.Fr.rts.b(m, sp, kind, b)
  %Equal.sym(Nat, Pg.Term.size(D.A.plugs(Con{D.AF{kind, q, k, a, b}, fs}, v)), Nat.add(V, Nat.add(Nat.add(S, D.Rts.size(List.append(&2, D.Rt, Fb, FR))), 1n+List.length(&2, U32, FC))),
      A1.plugs.size(Con{D.AF{kind, q, k, a, b}, fs}, m, sp, v)) : N.Le(C, _)
  %Equal.sym(List<&2, D.Rt>, Fb, Nil{}, frb.nil(kind, m, sp, b, h38)) : N.Le(C, Nat.add(V, Nat.add(Nat.add(S, D.Rts.size(List.append(&2, D.Rt, _, FR))), 1n+List.length(&2, U32, FC))))
  %Equal.sym(Nat, D.Rts.size(FR), R, rts.sz(fs, m, f1)) : N.Le(C, Nat.add(V, Nat.add(Nat.add(S, _), 1n+List.length(&2, U32, FC))))
  %Equal.sym(Nat, List.length(&2, U32, FC), L, cells.len(fs, m, f1)) : N.Le(C, Nat.add(V, Nat.add(Nat.add(S, R), 1n+_)))
  %Equal.sym(Nat, Nat.add(Nat.add(S, R), 1n+L), Nat.add(S, Nat.add(R, 1n+L)), N.add_assoc(S, R, 1n+L)) : N.Le(C, Nat.add(V, _))
  %Equal.sym(Nat, Nat.add(V, Nat.add(S, Nat.add(R, 1n+L))), C, N.add_swap(V, S, Nat.add(R, 1n+L))) : N.Le(C, _)
  N.le_refl(C)

def hc.fun(+q: Bk.Quan, +k: Bool, +g: Bk.Term, +b: Bk.Term, +fs: List<&2, D.AF>, +m: Cr.Cir.Cells, +sp: U32, +v: Bk.Term, -t: Bk.Term,
  et: {D.A.plugs(Con{D.AF{D.FK.fun{}, q, k, g, b}, fs}, v) == t : Bk.Term}) ->
  N.Le(Nat.add(Pg.Term.size(v), Nat.add(Pg.Term.size(g), Nat.add(frs.sz(fs), 1n+List.length(&2, D.AF, fs)))), Pg.Term.size(t)):
  +f1 = D.Fd(1n, m, sp)
  +V = Pg.Term.size(v)
  +G = Pg.Term.size(g)
  +R = frs.sz(fs)
  +L = List.length(&2, D.AF, fs)
  +C = Nat.add(V, Nat.add(G, Nat.add(R, 1n+L)))
  %et : N.Le(C, Pg.Term.size(_))
  +FR = D.Fr.rts(fs, m, f1)
  +FC = D.Fr.cells(fs, m, f1)
  %Equal.sym(Nat, Pg.Term.size(D.A.plugs(Con{D.AF{D.FK.fun{}, q, k, g, b}, fs}, v)), Nat.add(V, Nat.add(Nat.add(G, D.Rts.size(FR)), 1n+List.length(&2, U32, FC))),
      A1.plugs.size(Con{D.AF{D.FK.fun{}, q, k, g, b}, fs}, m, sp, v)) : N.Le(C, _)
  %Equal.sym(Nat, D.Rts.size(FR), R, rts.sz(fs, m, f1)) : N.Le(C, Nat.add(V, Nat.add(Nat.add(G, _), 1n+List.length(&2, U32, FC))))
  %Equal.sym(Nat, List.length(&2, U32, FC), L, cells.len(fs, m, f1)) : N.Le(C, Nat.add(V, Nat.add(Nat.add(G, R), 1n+_)))
  %Equal.sym(Nat, Nat.add(Nat.add(G, R), 1n+L), Nat.add(G, Nat.add(R, 1n+L)), N.add_assoc(G, R, 1n+L)) : N.Le(C, Nat.add(V, _))
  N.le_refl(C)

# the own cells after the pop: no STATIC one more
def stat.pop(+n: Nat, +m: Cr.Cir.Cells, +sp: U32, +pend: U32, +fi: U32) -> N.Le(D.Stat(n, M1(m, sp, pend), fi), D.Stat(n, m, fi)):
  N.le_rw_l(D.Stat(n, m, fi), D.Stat(n, M1(m, sp, pend), fi), D.Stat(n, m, fi),
    Equal.sym(Nat, D.Stat(n, D.Put1([D.W1{sp, pend}], m), fi), D.Stat(n, m, fi), A1.stat.put1(n, [D.W1{sp, pend}], m, fi)), N.le_refl(D.Stat(n, m, fi)))

def prj.app.mv(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +h: Bk.Term, +kind: D.FK, +q: Bk.Quan, +k: Bool, +a: Bk.Term, +b: Bk.Term, +zs: List<&2, D.Rt>,
  +et0: {D.A.plugs(fs, Bk.Term.App{q, Bk.Term.Prj{h}, a}) == t : Bk.Term},
  +et: {D.A.plugs(Con{D.AF{kind, q, k, a, b}, fs}, Bk.Term.Prj{h}) == t : Bk.Term},
  +hok: {Bool.or(Bool.not(k), El.Eval.vals(ds, a, False{})) == True{} : Bool},
  +h38: {U32.is_eq(D.FK.tag(kind), 38) == False{} : Bool}, +hk: {K.FK.isapp(kind) == True{} : Bool},
  +hsq: {Bool.and(El.Quan.live(q), Bool.not(k)) == False{} : Bool}, +afs: D.AFs.ok(ds, fs),
  +isf: D.Is(ds, m, im, fi, nx, ks, img, foc, Bk.Term.Prj{h}), +frs: D.Frs(ds, m, im, fi, nx, ks, img, ps, sp, Con{D.AF{kind, q, k, a, b}, fs}),
  +hp: D.Heap(m, nx, fi, im, [foc], pend, ps), +io2: D.ImgOK(ds, ks, img, m, im, fi, nx),
  +hac0: D.AccK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{foc, Bk.Term.Prj{h}}], Nil{}, sp, Con{D.AF{kind, q, k, a, b}, fs}, ps, zs)) ->
  K.MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  (+f => (%pre.app(f, kind, rest, foc, sp, pend, m, nx, fi, im, pg, lim, inp, q, k, hk, hsq, fr.z(ds, m, im, fi, nx, ks, img, ps, sp, kind, q, k, a, b, fs, frs), fr.c(ds, m, im, fi, nx, ks, img, ps, sp, kind, q, k, a, b, fs, frs), fr.t(ds, m, im, fi, nx, ks, img, ps, sp, kind, q, k, a, b, fs, frs), fr.q(ds, m, im, fi, nx, ks, img, ps, sp, kind, q, k, a, b, fs, frs), fr.k(ds, m, im, fi, nx, ks, img, ps, sp, kind, q, k, a, b, fs, frs)) : PB(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, lim, _);
      prj.redex(f, ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, lim, R.pre(D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, sp, D.FK.tag(kind), foc, D.Fd(2n, m, sp)), M1(m, sp, pend), nx, fi, im, pg, inp, fs, D.Fd(1n, m, sp), sp, sp, ps, zs,
        foc, h, D.Fd(2n, m, sp), q, a, hva.of(El.Quan.live(q), k, El.Eval.vals(ds, a, False{}), hsq, hok), et0, afs, le.max.l(D.Mem.cells(D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)), D.Need(ds, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t)), {==}, stat.pop(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, sp, pend, fi), hc.app(kind, q, k, a, b, fs, m, sp, Bk.Term.Prj{h}, t, h38, et), {==},
        hsk.pop(ds, ks, img, m, nx, fi, im, Bk.Term.Prj{h}, fs, foc, sp, pend, ps, kind, q, k, a, b, h38, isf, hp, io2, frs), acc.pop(ds, ks, img, m, nx, fi, im, Bk.Term.Prj{h}, fs, foc, sp, pend, ps, kind, q, k, a, b, zs, h38, frs, hac0),
        pre.l(D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, sp, D.FK.tag(kind), foc, D.Fd(2n, m, sp), rg.len(rest, foc, 1, sp, pend)), pre.r11(D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, sp, D.FK.tag(kind), foc, D.Fd(2n, m, sp), rg.len(rest, foc, 1, sp, pend)), pre.r12(D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, sp, D.FK.tag(kind), foc, D.Fd(2n, m, sp), rg.len(rest, foc, 1, sp, pend)), pre.q(D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, sp, D.FK.tag(kind), foc, D.Fd(2n, m, sp), rg.len(rest, foc, 1, sp, pend), q, fr.q(ds, m, im, fi, nx, ks, img, ps, sp, kind, q, k, a, b, fs, frs)), pre.r2(D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, sp, D.FK.tag(kind), foc, D.Fd(2n, m, sp), rg.len(rest, foc, 1, sp, pend)), pre.r3(D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, sp, D.FK.tag(kind), foc, D.Fd(2n, m, sp), rg.len(rest, foc, 1, sp, pend)))),
    (0n, (%pre.app(0n, kind, rest, foc, sp, pend, m, nx, fi, im, pg, lim, inp, q, k, hk, hsq, fr.z(ds, m, im, fi, nx, ks, img, ps, sp, kind, q, k, a, b, fs, frs), fr.c(ds, m, im, fi, nx, ks, img, ps, sp, kind, q, k, a, b, fs, frs), fr.t(ds, m, im, fi, nx, ks, img, ps, sp, kind, q, k, a, b, fs, frs), fr.q(ds, m, im, fi, nx, ks, img, ps, sp, kind, q, k, a, b, fs, frs), fr.k(ds, m, im, fi, nx, ks, img, ps, sp, kind, q, k, a, b, fs, frs)) : D.Ends(_);
      %prj.sel(0n, ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, lim, R.pre(D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, sp, D.FK.tag(kind), foc, D.Fd(2n, m, sp)), M1(m, sp, pend), nx, fi, im, pg, inp, foc, h, pre.r11(D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, sp, D.FK.tag(kind), foc, D.Fd(2n, m, sp), rg.len(rest, foc, 1, sp, pend)), hs.r2(ds, ks, img, M1(m, sp, pend), nx, fi, im, D.Fd(2n, m, sp), a, foc, Bk.Term.Prj{h}, Nil{}, fs, D.Fd(1n, m, sp), sp, Con{sp, ps}, hsk.pop(ds, ks, img, m, nx, fi, im, Bk.Term.Prj{h}, fs, foc, sp, pend, ps, kind, q, k, a, b, h38, isf, hp, io2, frs))) : D.Ends(_);
      ends.nw(0n, X.sel.t(X.sel.e(Mc.M.redex())), X.X.st(R.pre(D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, sp, D.FK.tag(kind), foc, D.Fd(2n, m, sp)), M1(m, sp, pend), nx, fi, im, pg, lim, inp), {==}))))

def prj.fun.mv(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +h: Bk.Term, +q: Bk.Quan, +k: Bool, +v: Bk.Term, +b: Bk.Term, +zs: List<&2, D.Rt>,
  +et0: {D.A.plugs(fs, Bk.Term.App{q, Bk.Term.Prj{h}, v}) == t : Bk.Term},
  +et: {D.A.plugs(Con{D.AF{D.FK.fun{}, q, k, Bk.Term.Prj{h}, b}, fs}, v) == t : Bk.Term},
  +evv: {El.Eval.vals(ds, v, False{}) == True{} : Bool}, +afs: D.AFs.ok(ds, fs),
  +isf: D.Is(ds, m, im, fi, nx, ks, img, foc, v), +frs: D.Frs(ds, m, im, fi, nx, ks, img, ps, sp, Con{D.AF{D.FK.fun{}, q, k, Bk.Term.Prj{h}, b}, fs}),
  +hp: D.Heap(m, nx, fi, im, [foc], pend, ps), +io2: D.ImgOK(ds, ks, img, m, im, fi, nx),
  +hac0: D.AccK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{foc, v}], Nil{}, sp, Con{D.AF{D.FK.fun{}, q, k, Bk.Term.Prj{h}, b}, fs}, ps, zs)) ->
  K.MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  (+f => (%pre.fun(f, rest, foc, sp, pend, m, nx, fi, im, pg, lim, inp, fr.z(ds, m, im, fi, nx, ks, img, ps, sp, D.FK.fun{}, q, k, Bk.Term.Prj{h}, b, fs, frs), fr.c(ds, m, im, fi, nx, ks, img, ps, sp, D.FK.fun{}, q, k, Bk.Term.Prj{h}, b, fs, frs), fr.t(ds, m, im, fi, nx, ks, img, ps, sp, D.FK.fun{}, q, k, Bk.Term.Prj{h}, b, fs, frs)) : PB(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, lim, _);
      prj.redex(f, ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, lim, R.pre(D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, sp, 34, D.Fd(2n, m, sp), foc), M1(m, sp, pend), nx, fi, im, pg, inp, fs, D.Fd(1n, m, sp), sp, sp, ps, zs,
        D.Fd(2n, m, sp), h, foc, q, v, D.or.r(Bool.not(El.Quan.live(q)), El.Eval.vals(ds, v, False{}), evv), et0, afs, le.max.l(D.Mem.cells(D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)), D.Need(ds, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t)), {==}, stat.pop(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, sp, pend, fi), hc.fun(q, k, Bk.Term.Prj{h}, b, fs, m, sp, v, t, et), {==},
        hsk.swap(ds, ks, img, M1(m, sp, pend), nx, fi, im, D.Fd(2n, m, sp), Bk.Term.Prj{h}, foc, v, Nil{}, fs, D.Fd(1n, m, sp), sp, Con{sp, ps}, hsk.pop(ds, ks, img, m, nx, fi, im, v, fs, foc, sp, pend, ps, D.FK.fun{}, q, k, Bk.Term.Prj{h}, b, {==}, isf, hp, io2, frs)), acc.swap(ds, ks, img, M1(m, sp, pend), nx, fi, im, D.Rt{D.Fd(2n, m, sp), Bk.Term.Prj{h}}, D.Rt{foc, v}, Nil{}, D.Fd(1n, m, sp), fs, Con{sp, ps}, zs, acc.pop(ds, ks, img, m, nx, fi, im, v, fs, foc, sp, pend, ps, D.FK.fun{}, q, k, Bk.Term.Prj{h}, b, zs, {==}, frs, hac0)),
        pre.l(D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, sp, 34, D.Fd(2n, m, sp), foc, rg.len(rest, foc, 1, sp, pend)), pre.r11(D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, sp, 34, D.Fd(2n, m, sp), foc, rg.len(rest, foc, 1, sp, pend)), pre.r12(D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, sp, 34, D.Fd(2n, m, sp), foc, rg.len(rest, foc, 1, sp, pend)), pre.q(D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, sp, 34, D.Fd(2n, m, sp), foc, rg.len(rest, foc, 1, sp, pend), q, fr.q(ds, m, im, fi, nx, ks, img, ps, sp, D.FK.fun{}, q, k, Bk.Term.Prj{h}, b, fs, frs)), pre.r2(D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, sp, 34, D.Fd(2n, m, sp), foc, rg.len(rest, foc, 1, sp, pend)), pre.r3(D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, sp, 34, D.Fd(2n, m, sp), foc, rg.len(rest, foc, 1, sp, pend)))),
    (0n, (%pre.fun(0n, rest, foc, sp, pend, m, nx, fi, im, pg, lim, inp, fr.z(ds, m, im, fi, nx, ks, img, ps, sp, D.FK.fun{}, q, k, Bk.Term.Prj{h}, b, fs, frs), fr.c(ds, m, im, fi, nx, ks, img, ps, sp, D.FK.fun{}, q, k, Bk.Term.Prj{h}, b, fs, frs), fr.t(ds, m, im, fi, nx, ks, img, ps, sp, D.FK.fun{}, q, k, Bk.Term.Prj{h}, b, fs, frs)) : D.Ends(_);
      %prj.sel(0n, ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, lim, R.pre(D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, sp, 34, D.Fd(2n, m, sp), foc), M1(m, sp, pend), nx, fi, im, pg, inp, D.Fd(2n, m, sp), h, pre.r11(D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, sp, 34, D.Fd(2n, m, sp), foc, rg.len(rest, foc, 1, sp, pend)), hs.r2(ds, ks, img, M1(m, sp, pend), nx, fi, im, foc, v, D.Fd(2n, m, sp), Bk.Term.Prj{h}, Nil{}, fs, D.Fd(1n, m, sp), sp, Con{sp, ps}, hsk.swap(ds, ks, img, M1(m, sp, pend), nx, fi, im, D.Fd(2n, m, sp), Bk.Term.Prj{h}, foc, v, Nil{}, fs, D.Fd(1n, m, sp), sp, Con{sp, ps}, hsk.pop(ds, ks, img, m, nx, fi, im, v, fs, foc, sp, pend, ps, D.FK.fun{}, q, k, Bk.Term.Prj{h}, b, {==}, isf, hp, io2, frs)))) : D.Ends(_);
      ends.nw(0n, X.sel.t(X.sel.e(Mc.M.redex())), X.X.st(R.pre(D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, sp, 34, D.Fd(2n, m, sp), foc), M1(m, sp, pend), nx, fi, im, pg, lim, inp), {==}))))

# The moves of move_kit.bend that this file proves
# ------------------------------------------------

def K.mv.ret.app.prj(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, h, kind, q, k, a, b, iv, hk, hs):
  match kind:
    case D.FK.arg{}:
      match iv:
        case Tuple{Tuple{+et, Tuple{_, Tuple{_, Tuple{Tuple{hok, afs}, Tuple{_, Tuple{isf, Tuple{frs, Tuple{hp, Tuple{io2, _}}}}}}}}}, Tuple{zs, hac}}:
          prj.app.mv(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, h, D.FK.arg{}, q, k, a, b, zs, et, et, hok, {==}, hk, hs, afs, isf, frs, hp, io2, hac)
    case D.FK.val{}:
      match iv:
        case Tuple{Tuple{+et, Tuple{_, Tuple{_, Tuple{Tuple{hok, afs}, Tuple{_, Tuple{isf, Tuple{frs, Tuple{hp, Tuple{io2, _}}}}}}}}}, Tuple{zs, hac}}:
          prj.app.mv(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, h, D.FK.val{}, q, k, a, b, zs, et, et, hok, {==}, hk, hs, afs, isf, frs, hp, io2, hac)
    case D.FK.fun{}:
      D.bool.ft(K.MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w), hk)
    case D.FK.let{}:
      D.bool.ft(K.MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w), hk)
    case D.FK.tupb{}:
      D.bool.ft(K.MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w), hk)
    case D.FK.tupa{}:
      D.bool.ft(K.MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w), hk)
    case D.FK.rwt{}:
      D.bool.ft(K.MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w), hk)
    case D.FK.minb{}:
      D.bool.ft(K.MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w), hk)
    case D.FK.mina{}:
      D.bool.ft(K.MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w), hk)

def K.mv.ret.fun.prj(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, h, focus, q, k, b, iv):
  match iv:
    case Tuple{Tuple{+et, Tuple{_, Tuple{evv, Tuple{Tuple{_, afs}, Tuple{_, Tuple{isf, Tuple{frs, Tuple{hp, Tuple{io2, _}}}}}}}}}, Tuple{zs, hac}}:
      prj.fun.mv(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, h, q, k, focus, b, zs, et, et, evv, afs, isf, frs, hp, io2, hac)

def K.mv.ret.app.mat(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, j, h, n, kind, q, k, a, b, iv, hk, hs):
  match kind:
    case D.FK.arg{}:
      match iv:
        case Tuple{Tuple{et, Tuple{_, Tuple{_, Tuple{Tuple{hok, afs}, Tuple{_, Tuple{isf, Tuple{frs, Tuple{hp, Tuple{io2, _}}}}}}}}}, Tuple{zs, hac}}:
          mat.app.mv(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, j, h, n, D.FK.arg{}, q, k, a, b, zs, et, hok, {==}, hk, hs, afs, isf, frs, hp, io2, hac)
    case D.FK.val{}:
      match iv:
        case Tuple{Tuple{et, Tuple{_, Tuple{_, Tuple{Tuple{hok, afs}, Tuple{_, Tuple{isf, Tuple{frs, Tuple{hp, Tuple{io2, _}}}}}}}}}, Tuple{zs, hac}}:
          mat.app.mv(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, j, h, n, D.FK.val{}, q, k, a, b, zs, et, hok, {==}, hk, hs, afs, isf, frs, hp, io2, hac)
    case D.FK.fun{}:
      D.bool.ft(K.MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w), hk)
    case D.FK.let{}:
      D.bool.ft(K.MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w), hk)
    case D.FK.tupb{}:
      D.bool.ft(K.MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w), hk)
    case D.FK.tupa{}:
      D.bool.ft(K.MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w), hk)
    case D.FK.rwt{}:
      D.bool.ft(K.MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w), hk)
    case D.FK.minb{}:
      D.bool.ft(K.MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w), hk)
    case D.FK.mina{}:
      D.bool.ft(K.MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w), hk)

def K.mv.ret.fun.mat(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, j, h, n, focus, q, k, b, iv):
  match iv:
    case Tuple{Tuple{et, Tuple{_, Tuple{evv, Tuple{Tuple{_, afs}, Tuple{_, Tuple{isf, Tuple{frs, Tuple{hp, Tuple{io2, _}}}}}}}}}, Tuple{zs, hac}}:
      mat.fun.mv(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, j, h, n, q, k, focus, b, zs, et, evv, afs, isf, frs, hp, io2, hac)
