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
