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
