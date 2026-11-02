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
