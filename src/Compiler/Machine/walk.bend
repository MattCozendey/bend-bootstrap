# compiler: layer B, M.walk gives Eval.walk (U7)
# ==============================================
#
# walk.post and walk.done of move_kit.bend: M.walk's rounds (λ, λ-match of pairs and labels, App
# of a local, Efq) give Eval.walk; the K.arg chains grow by at most 2 cells a round.
# Filled by U7; U0 left each as ?TODO.
#
# The proof reads the walk's code with U6's WP (data_walk.bend). A phase that
# runs inside it (M.data, in a λ's round) comes in by its law, an Ok of its
# run, through WP.of.

import Base
import ../../Book/impl.bend as Bk
import ../../Shared/shared.bend as Sd
import ../../Eval/impl.bend as El
import ../../Program/impl.bend as Pg
import ../../Wasm/impl.bend as Wa
import ../Cir/impl.bend as Cr
import ./impl.bend as Mc
import ./definitions.bend as D
import ./statement_runs.bend as X
import ./data_walk.bend as DW
import ./move_kit.bend as K
import ../need_big.bend as N
import ./heap_ops.bend as HO
import ./accounting.bend as AC
import ./data_check.bend as DC
import ./moves_match.bend as MM

# Phases inside WP
# ----------------
#
# For a statement whose allocs are M.alloc's (the else of an if) and that
# emits nothing (Wf), an Ok of its run with the fuel F is its WP for F
# (WP.of): a run that gives a value had accesses that Cir allows (ob.of),
# and each part of a run gives what the rest needs.

# its allocs are M.alloc's, and it emits nothing
def Wf(s: Cr.Cir.Stmt) -> Bool:
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
    case Cr.Cir.Stmt.seq{a, b}:
      Bool.and(Wf(a), Wf(b))
    case Cr.Cir.Stmt.if{_, t, e}:
      match e:
        case Cr.Cir.Stmt.alloc{_}:
          True{}
        case e2:
          Bool.and(Wf(t), Wf(e2))
    case Cr.Cir.Stmt.while{_, b}:
      Wf(b)
    case Cr.Cir.Stmt.halt{_}:
      True{}

def wf.l(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def wf.r(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      DW.tf({b == True{} : Bool}, h)

def u.inj(+a: U32, -b: U32, e: {Some{a} == Some{b} : Maybe<&2, U32>}) -> {a == b : U32}:
  Equal.cong(Maybe<&2, U32>, U32, y => Maybe.default(&2, U32, y, a), Some{a}, Some{b}, e)

def u.none(-G: Type, -x: U32, e: {None{} == Some{x} : Maybe<&2, U32>}) -> G:
  Empty.absurd(G, X.k.none_some(x, e))

def u.dflt(-mv: Maybe<&2, U32>, -x: U32, h: {mv == Some{x} : Maybe<&2, U32>}) -> {Maybe.default(&2, U32, mv, 0) == x : U32}:
  (%Equal.sym(Maybe<&2, U32>, mv, Some{x}, h) : {Maybe.default(&2, U32, _, 0) == x : U32}; {==})

def u.some(-mv: Maybe<&2, U32>, -x: U32, h: {mv == Some{x} : Maybe<&2, U32>}) -> DW.IsSome(mv):
  (%Equal.sym(Maybe<&2, U32>, mv, Some{x}, h) : DW.IsSome(_); Unit{})

# a read that gives x
def ob.get(-mv: Maybe<&2, U32>, -x: U32, +h: {mv == Some{x} : Maybe<&2, U32>}) ->
  DW.IsSome(mv) & {Maybe.default(&2, U32, mv, 0) == x : U32}:
  (u.some(mv, x, h), u.dflt(mv, x, h))

def ob.op.of(+o: Wa.Wasm.Op, +a: Cr.Cir.Expr, +b: Cr.Cir.Expr, +st: Cr.Cir.State, +xa: U32, +xb: U32, +x: U32,
  pa: DW.Ob(a, st) & {DW.Ev(a, st) == xa : U32}, pb: DW.Ob(b, st) & {DW.Ev(b, st) == xb : U32},
  h: {Some{Wa.Wasm.op(o, xa, xb)} == Some{x} : Maybe<&2, U32>}) ->
  DW.Ob(Cr.Cir.Expr.op{o, a, b}, st) & {DW.Ev(Cr.Cir.Expr.op{o, a, b}, st) == x : U32}:
  (oa, va) = pa
  (ob, vb) = pb
  (%Equal.sym(U32, DW.Ev(a, st), xa, va) : DW.Ob(Cr.Cir.Expr.op{o, a, b}, st) & {Wa.Wasm.op(o, _, DW.Ev(b, st)) == x : U32};
   %Equal.sym(U32, DW.Ev(b, st), xb, vb) : DW.Ob(Cr.Cir.Expr.op{o, a, b}, st) & {Wa.Wasm.op(o, xa, _) == x : U32};
   ((oa, ob), u.inj(Wa.Wasm.op(o, xa, xb), x, h)))

def ob.op(+o: Wa.Wasm.Op, +a: Cr.Cir.Expr, +b: Cr.Cir.Expr, +st: Cr.Cir.State, +ma: Maybe<&2, U32>, +mb: Maybe<&2, U32>, +x: U32,
  ea: {Cr.Cir.eval(a, st) == ma : Maybe<&2, U32>}, eb: {Cr.Cir.eval(b, st) == mb : Maybe<&2, U32>},
  h: {Cr.Cir.eval.op(o, ma, mb) == Some{x} : Maybe<&2, U32>},
  ka: @xa: U32 -> {Cr.Cir.eval(a, st) == Some{xa} : Maybe<&2, U32>} -> DW.Ob(a, st) & {DW.Ev(a, st) == xa : U32},
  kb: @xb: U32 -> {Cr.Cir.eval(b, st) == Some{xb} : Maybe<&2, U32>} -> DW.Ob(b, st) & {DW.Ev(b, st) == xb : U32}) ->
  DW.Ob(Cr.Cir.Expr.op{o, a, b}, st) & {DW.Ev(Cr.Cir.Expr.op{o, a, b}, st) == x : U32}:
  match ma mb:
    case Some{+xa} Some{+xb}:
      ob.op.of(o, a, b, st, xa, xb, x, ka(xa, ea), kb(xb, eb), h)
    case None{} _:
      u.none(DW.Ob(Cr.Cir.Expr.op{o, a, b}, st) & {DW.Ev(Cr.Cir.Expr.op{o, a, b}, st) == x : U32}, x, h)
    case Some{_} None{}:
      u.none(DW.Ob(Cr.Cir.Expr.op{o, a, b}, st) & {DW.Ev(Cr.Cir.Expr.op{o, a, b}, st) == x : U32}, x, h)

def ob.eqz.of(+a: Cr.Cir.Expr, +st: Cr.Cir.State, +xa: U32, +x: U32, pa: DW.Ob(a, st) & {DW.Ev(a, st) == xa : U32},
  h: {Some{Bool.to_u32(U32.is_zero(xa))} == Some{x} : Maybe<&2, U32>}) ->
  DW.Ob(Cr.Cir.Expr.eqz{a}, st) & {DW.Ev(Cr.Cir.Expr.eqz{a}, st) == x : U32}:
  (oa, va) = pa
  (%Equal.sym(U32, DW.Ev(a, st), xa, va) : DW.Ob(Cr.Cir.Expr.eqz{a}, st) & {Bool.to_u32(U32.is_zero(_)) == x : U32};
   (oa, u.inj(Bool.to_u32(U32.is_zero(xa)), x, h)))

def ob.eqz(+a: Cr.Cir.Expr, +st: Cr.Cir.State, +ma: Maybe<&2, U32>, +x: U32, ea: {Cr.Cir.eval(a, st) == ma : Maybe<&2, U32>},
  h: {Cr.Cir.eval.eqz(ma) == Some{x} : Maybe<&2, U32>},
  ka: @xa: U32 -> {Cr.Cir.eval(a, st) == Some{xa} : Maybe<&2, U32>} -> DW.Ob(a, st) & {DW.Ev(a, st) == xa : U32}) ->
  DW.Ob(Cr.Cir.Expr.eqz{a}, st) & {DW.Ev(Cr.Cir.Expr.eqz{a}, st) == x : U32}:
  match ma:
    case Some{+xa}:
      ob.eqz.of(a, st, xa, x, ka(xa, ea), h)
    case None{}:
      u.none(DW.Ob(Cr.Cir.Expr.eqz{a}, st) & {DW.Ev(Cr.Cir.Expr.eqz{a}, st) == x : U32}, x, h)

def ob.cell(b: Bool, +k: Nat, +cells: Cr.Cir.Cells, +i: U32, +x: U32, h: {Cr.Cir.eval.field.if(b, k, cells, i) == Some{x} : Maybe<&2, U32>}) ->
  {True{} == b : Bool} & {Cr.Cir.Cell.get(k, Cr.Cir.Cells.get(cells, i)) == x : U32}:
  match b:
    case True{}:
      ({==}, u.inj(Cr.Cir.Cell.get(k, Cr.Cir.Cells.get(cells, i)), x, h))
    case False{}:
      u.none({True{} == False{} : Bool} & {Cr.Cir.Cell.get(k, Cr.Cir.Cells.get(cells, i)) == x : U32}, x, h)

def ob.field.of(+k: Nat, +c: Cr.Cir.Expr, +regs: List<&2, U32>, +cells: Cr.Cir.Cells, +next: U32, +first: U32, +image: U32, +pages: U32,
  +limit: U32, +input: List<&2, Word(8n)>, +out: List<&2, Word(8n)>, +outn: U32, +i: U32, +x: U32,
  pc: DW.Ob(c, Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}) &
    {DW.Ev(c, Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}) == i : U32},
  pk: {True{} == Cr.Cir.is_cell(i, image, first, next) : Bool} & {Cr.Cir.Cell.get(k, Cr.Cir.Cells.get(cells, i)) == x : U32}) ->
  DW.Ob(Cr.Cir.Expr.field{k, c}, Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}) &
    {DW.Ev(Cr.Cir.Expr.field{k, c}, Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}) == x : U32}:
  (oc, vc) = pc
  (hok, hx) = pk
  +s0 = {Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn} : Cr.Cir.State}
  (%Equal.sym(U32, DW.Ev(c, s0), i, vc) : (DW.Ob(c, s0) & DW.CellOk(_, s0)) & {DW.Ev.field(k, _, s0) == x : U32};
   ((oc, hok), hx))

def ob.field(+k: Nat, +c: Cr.Cir.Expr, +st: Cr.Cir.State, +mc: Maybe<&2, U32>, +x: U32, ec: {Cr.Cir.eval(c, st) == mc : Maybe<&2, U32>},
  h: {Cr.Cir.eval.field(k, mc, st) == Some{x} : Maybe<&2, U32>},
  kc: @xc: U32 -> {Cr.Cir.eval(c, st) == Some{xc} : Maybe<&2, U32>} -> DW.Ob(c, st) & {DW.Ev(c, st) == xc : U32}) ->
  DW.Ob(Cr.Cir.Expr.field{k, c}, st) & {DW.Ev(Cr.Cir.Expr.field{k, c}, st) == x : U32}:
  match st:
    case Cr.Cir.State{+regs, +cells, +next, +first, +image, +pages, +limit, +input, +out, +outn}:
      match mc:
        case Some{+i}:
          ob.field.of(k, c, regs, cells, next, first, image, pages, limit, input, out, outn, i, x, kc(i, ec),
            ob.cell(Cr.Cir.is_cell(i, image, first, next), k, cells, i, x, h))
        case None{}:
          u.none(DW.Ob(Cr.Cir.Expr.field{k, c}, Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}) &
            {DW.Ev(Cr.Cir.Expr.field{k, c}, Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}) == x : U32}, x, h)

def ob.byte.of(+i: Cr.Cir.Expr, +st: Cr.Cir.State, +xi: U32, +x: U32, pi: DW.Ob(i, st) & {DW.Ev(i, st) == xi : U32},
  +h: {Cr.Cir.eval.byte(Some{xi}, Cr.Cir.eval.input(st)) == Some{x} : Maybe<&2, U32>}) ->
  DW.Ob(Cr.Cir.Expr.byte{i}, st) & {DW.Ev(Cr.Cir.Expr.byte{i}, st) == x : U32}:
  (oi, vi) = pi
  (%Equal.sym(U32, DW.Ev(i, st), xi, vi) :
    (DW.Ob(i, st) & DW.IsSome(Cr.Cir.eval.byte(Some{_}, Cr.Cir.eval.input(st)))) & {Maybe.default(&2, U32, Cr.Cir.eval.byte(Some{_}, Cr.Cir.eval.input(st)), 0) == x : U32};
   ((oi, u.some(Cr.Cir.eval.byte(Some{xi}, Cr.Cir.eval.input(st)), x, h)), u.dflt(Cr.Cir.eval.byte(Some{xi}, Cr.Cir.eval.input(st)), x, h)))

def ob.byte(+i: Cr.Cir.Expr, +st: Cr.Cir.State, +mi: Maybe<&2, U32>, +x: U32, ei: {Cr.Cir.eval(i, st) == mi : Maybe<&2, U32>},
  h: {Cr.Cir.eval.byte(mi, Cr.Cir.eval.input(st)) == Some{x} : Maybe<&2, U32>},
  ki: @xi: U32 -> {Cr.Cir.eval(i, st) == Some{xi} : Maybe<&2, U32>} -> DW.Ob(i, st) & {DW.Ev(i, st) == xi : U32}) ->
  DW.Ob(Cr.Cir.Expr.byte{i}, st) & {DW.Ev(Cr.Cir.Expr.byte{i}, st) == x : U32}:
  match mi:
    case Some{+xi}:
      ob.byte.of(i, st, xi, x, ki(xi, ei), h)
    case None{}:
      u.none(DW.Ob(Cr.Cir.Expr.byte{i}, st) & {DW.Ev(Cr.Cir.Expr.byte{i}, st) == x : U32}, x, h)

# a run of e that gives x: Cir allows its accesses, and Ev gives x
def ob.of(+e: Cr.Cir.Expr, +st: Cr.Cir.State, +x: U32, +h: {Cr.Cir.eval(e, st) == Some{x} : Maybe<&2, U32>}) ->
  DW.Ob(e, st) & {DW.Ev(e, st) == x : U32}:
  match e:
    case Cr.Cir.Expr.const{+n}:
      (Unit{}, u.inj(n, x, h))
    case Cr.Cir.Expr.get{+r}:
      ob.get(Cr.Cir.eval.get(r, st), x, h)
    case Cr.Cir.Expr.op{+o, +a, +b}:
      ob.op(o, a, b, st, Cr.Cir.eval(a, st), Cr.Cir.eval(b, st), x, {==}, {==}, h,
        xa => ha => ob.of(a, st, xa, ha), xb => hb => ob.of(b, st, xb, hb))
    case Cr.Cir.Expr.eqz{+a}:
      ob.eqz(a, st, Cr.Cir.eval(a, st), x, {==}, h, xa => ha => ob.of(a, st, xa, ha))
    case Cr.Cir.Expr.field{+k, +c}:
      ob.field(k, c, st, Cr.Cir.eval(c, st), x, {==}, h, xc => hc => ob.of(c, st, xc, hc))
    case Cr.Cir.Expr.byte{+i}:
      ob.byte(i, st, Cr.Cir.eval(i, st), x, {==}, h, xi => hi => ob.of(i, st, xi, hi))
    case Cr.Cir.Expr.size{}:
      (Unit{}, u.dflt(Cr.Cir.eval.size(st), x, h))

# a run, then more: each end of the first part gives what the rest needs
def wpo.unthen(o: Cr.Cir.Out, -k: Cr.Cir.State -> Cr.Cir.Out, -Q: Cr.Cir.State -> Type, +B: Nat, +lim: U32,
  h: DW.Ok(Cr.Cir.exec.then(o, k), Q, B, lim)) -> DW.Ok(o, t => DW.Ok(k(t), Q, B, lim), B, lim):
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
      h

def wpo.set.if(b: Bool, +regs: List<&2, U32>, +r: Nat, +x: U32, +cells: Cr.Cir.Cells, +next: U32, +first: U32, +image: U32, +pages: U32,
  +limit: U32, +input: List<&2, Word(8n)>, +out: List<&2, Word(8n)>, +outn: U32, -Q: Cr.Cir.State -> Type, +B: Nat, +lim: U32,
  h: DW.Ok(Cr.Cir.exec.set.of(Cr.Cir.regs.set.if(b, regs, r, x), Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}), Q, B, lim)) ->
  DW.Tr(b) & Q(Cr.Cir.State{List.set(&2, U32, regs, r, x), cells, next, first, image, pages, limit, input, out, outn}):
  match b:
    case True{}:
      (Unit{}, h)
    case False{}:
      Empty.absurd(DW.Tr(False{}) & Q(Cr.Cir.State{List.set(&2, U32, regs, r, x), cells, next, first, image, pages, limit, input, out, outn}), h)

def wpo.set.of(+r: Nat, +e: Cr.Cir.Expr, +regs: List<&2, U32>, +cells: Cr.Cir.Cells, +next: U32, +first: U32, +image: U32, +pages: U32,
  +limit: U32, +input: List<&2, Word(8n)>, +out: List<&2, Word(8n)>, +outn: U32, +x: U32, -Q: Cr.Cir.State -> Type, +B: Nat, +lim: U32,
  pe: DW.Ob(e, Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}) &
    {DW.Ev(e, Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}) == x : U32},
  h: DW.Ok(Cr.Cir.exec.set.of(Cr.Cir.regs.set(regs, r, x), Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}), Q, B, lim)) ->
  DW.Ob(e, Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}) &
    DW.WP.set(r, DW.Ev(e, Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}), Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}, Q):
  (oe, ve) = pe
  +s0 = {Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn} : Cr.Cir.State}
  (%Equal.sym(U32, DW.Ev(e, s0), x, ve) : DW.Ob(e, s0) & DW.WP.set(r, _, s0, Q);
   (oe, wpo.set.if(Nat.is_lt(r, List.length(&2, U32, regs)), regs, r, x, cells, next, first, image, pages, limit, input, out, outn,
     Q, B, lim, h)))

def wpo.set(+r: Nat, +e: Cr.Cir.Expr, +st: Cr.Cir.State, +mv: Maybe<&2, U32>, -Q: Cr.Cir.State -> Type, +B: Nat, +lim: U32,
  ev: {Cr.Cir.eval(e, st) == mv : Maybe<&2, U32>}, h: DW.Ok(Cr.Cir.exec.set(r, mv, st), Q, B, lim)) ->
  DW.Ob(e, st) & DW.WP.set(r, DW.Ev(e, st), st, Q):
  match st:
    case Cr.Cir.State{+regs, +cells, +next, +first, +image, +pages, +limit, +input, +out, +outn}:
      match mv:
        case None{}:
          Empty.absurd(DW.Ob(e, Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}) &
            DW.WP.set(r, DW.Ev(e, Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}),
              Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}, Q), h)
        case Some{+x}:
          wpo.set.of(r, e, regs, cells, next, first, image, pages, limit, input, out, outn, x, Q, B, lim,
            ob.of(e, Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}, x, ev), h)

def wpo.store.if(b: Bool, +k: Nat, +i: U32, +x: U32, +regs: List<&2, U32>, +cells: Cr.Cir.Cells, +next: U32, +first: U32, +image: U32,
  +pages: U32, +limit: U32, +input: List<&2, Word(8n)>, +out: List<&2, Word(8n)>, +outn: U32, -Q: Cr.Cir.State -> Type, +B: Nat, +lim: U32,
  eb: {Cr.Cir.is_cell(i, image, first, next) == b : Bool},
  h: DW.Ok(Cr.Cir.exec.store.if(b, k, i, x, Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}), Q, B, lim)) ->
  DW.WP.store(k, i, x, Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}, Q):
  match b:
    case True{}:
      (Equal.sym(Bool, Cr.Cir.is_cell(i, image, first, next), True{}, eb), h)
    case False{}:
      Empty.absurd(DW.WP.store(k, i, x, Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}, Q), h)

def wpo.store.of(+k: Nat, +c: Cr.Cir.Expr, +v: Cr.Cir.Expr, +regs: List<&2, U32>, +cells: Cr.Cir.Cells, +next: U32, +first: U32, +image: U32,
  +pages: U32, +limit: U32, +input: List<&2, Word(8n)>, +out: List<&2, Word(8n)>, +outn: U32, +i: U32, +x: U32, -Q: Cr.Cir.State -> Type,
  +B: Nat, +lim: U32,
  pc: DW.Ob(c, Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}) &
    {DW.Ev(c, Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}) == i : U32},
  pv: DW.Ob(v, Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}) &
    {DW.Ev(v, Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}) == x : U32},
  h: DW.Ok(Cr.Cir.exec.store.if(Cr.Cir.is_cell(i, image, first, next), k, i, x, Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}), Q, B, lim)) ->
  DW.Ob(c, Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}) &
    (DW.Ob(v, Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}) &
     DW.WP.store(k, DW.Ev(c, Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}),
       DW.Ev(v, Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}), Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}, Q)):
  (oc, vc) = pc
  (ov, vv) = pv
  +s0 = {Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn} : Cr.Cir.State}
  (%Equal.sym(U32, DW.Ev(c, s0), i, vc) : DW.Ob(c, s0) & (DW.Ob(v, s0) & DW.WP.store(k, _, DW.Ev(v, s0), s0, Q));
   %Equal.sym(U32, DW.Ev(v, s0), x, vv) : DW.Ob(c, s0) & (DW.Ob(v, s0) & DW.WP.store(k, i, _, s0, Q));
   (oc, (ov, wpo.store.if(Cr.Cir.is_cell(i, image, first, next), k, i, x, regs, cells, next, first, image, pages, limit, input, out, outn,
     Q, B, lim, {==}, h))))

def wpo.store(+k: Nat, +c: Cr.Cir.Expr, +v: Cr.Cir.Expr, +st: Cr.Cir.State, +mc: Maybe<&2, U32>, +mv: Maybe<&2, U32>, -Q: Cr.Cir.State -> Type,
  +B: Nat, +lim: U32, ec: {Cr.Cir.eval(c, st) == mc : Maybe<&2, U32>}, ev: {Cr.Cir.eval(v, st) == mv : Maybe<&2, U32>},
  h: DW.Ok(Cr.Cir.exec.store(k, mc, mv, st), Q, B, lim)) ->
  DW.Ob(c, st) & (DW.Ob(v, st) & DW.WP.store(k, DW.Ev(c, st), DW.Ev(v, st), st, Q)):
  match st:
    case Cr.Cir.State{+regs, +cells, +next, +first, +image, +pages, +limit, +input, +out, +outn}:
      match mc mv:
        case Some{+i} Some{+x}:
          wpo.store.of(k, c, v, regs, cells, next, first, image, pages, limit, input, out, outn, i, x, Q, B, lim,
            ob.of(c, Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}, i, ec), ob.of(v, Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}, x, ev), h)
        case None{} _:
          Empty.absurd(DW.Ob(c, Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}) & (DW.Ob(v, Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}) & DW.WP.store(k, DW.Ev(c, Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}), DW.Ev(v, Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}), Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}, Q)), h)
        case Some{_} None{}:
          Empty.absurd(DW.Ob(c, Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}) & (DW.Ob(v, Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}) & DW.WP.store(k, DW.Ev(c, Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}), DW.Ev(v, Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}), Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}, Q)), h)

def wpo.ifq(z: Bool, -ka: (Cr.Cir.State -> Type) -> Type, -kb: (Cr.Cir.State -> Type) -> Type, -Q: Cr.Cir.State -> Type, +B: Nat, +lim: U32,
  -yes: Unit -> Cr.Cir.Out, -no: Unit -> Cr.Cir.Out, h: DW.Ok(Cr.Cir.exec.if.of(z, yes, no), Q, B, lim),
  gy: DW.Ok(yes(Unit{}), Q, B, lim) -> ka(Q), gn: DW.Ok(no(Unit{}), Q, B, lim) -> kb(Q)) -> DW.IfQ(z, ka, kb, Q):
  match z:
    case False{}:
      gy(h)
    case True{}:
      gn(h)

def wpo.if.of(+F: Nat, +c: Cr.Cir.Expr, +t: Cr.Cir.Stmt, +e: Cr.Cir.Stmt, +st: Cr.Cir.State, +v: U32, -Q: Cr.Cir.State -> Type,
  +B: Nat, +lim: U32, pc: DW.Ob(c, st) & {DW.Ev(c, st) == v : U32},
  h: DW.Ok(Cr.Cir.exec.if(Some{v}, u => Cr.Cir.exec(F, t, st), u => Cr.Cir.exec(F, e, st)), Q, B, lim),
  gt: DW.Ok(Cr.Cir.exec(F, t, st), Q, B, lim) -> DW.WP(t, F, st, x => Q(x), B, lim),
  ge: DW.Ok(Cr.Cir.exec(F, e, st), Q, B, lim) -> DW.WP(e, F, st, x => Q(x), B, lim)) ->
  DW.Ob(c, st) & DW.IfQ(U32.is_zero(DW.Ev(c, st)), q => DW.WP(t, F, st, x => q(x), B, lim), q => DW.WP(e, F, st, x => q(x), B, lim), Q):
  (oc, vc) = pc
  (%Equal.sym(U32, DW.Ev(c, st), v, vc) :
    DW.Ob(c, st) & DW.IfQ(U32.is_zero(_), q => DW.WP(t, F, st, x => q(x), B, lim), q => DW.WP(e, F, st, x => q(x), B, lim), Q);
   (oc, wpo.ifq(U32.is_zero(v), q => DW.WP(t, F, st, x => q(x), B, lim), q => DW.WP(e, F, st, x => q(x), B, lim), Q, B, lim,
     u => Cr.Cir.exec(F, t, st), u => Cr.Cir.exec(F, e, st), h, gt, ge)))

def wpo.if.go(+F: Nat, +c: Cr.Cir.Expr, +t: Cr.Cir.Stmt, +e: Cr.Cir.Stmt, +st: Cr.Cir.State, +mc: Maybe<&2, U32>, -Q: Cr.Cir.State -> Type,
  +B: Nat, +lim: U32, ec: {Cr.Cir.eval(c, st) == mc : Maybe<&2, U32>},
  h: DW.Ok(Cr.Cir.exec.if(mc, u => Cr.Cir.exec(F, t, st), u => Cr.Cir.exec(F, e, st)), Q, B, lim),
  gt: DW.Ok(Cr.Cir.exec(F, t, st), Q, B, lim) -> DW.WP(t, F, st, x => Q(x), B, lim),
  ge: DW.Ok(Cr.Cir.exec(F, e, st), Q, B, lim) -> DW.WP(e, F, st, x => Q(x), B, lim)) ->
  DW.Ob(c, st) & DW.IfQ(U32.is_zero(DW.Ev(c, st)), q => DW.WP(t, F, st, x => q(x), B, lim), q => DW.WP(e, F, st, x => q(x), B, lim), Q):
  match mc:
    case None{}:
      Empty.absurd(DW.Ob(c, st) & DW.IfQ(U32.is_zero(DW.Ev(c, st)), q => DW.WP(t, F, st, x => q(x), B, lim), q => DW.WP(e, F, st, x => q(x), B, lim), Q), h)
    case Some{+v}:
      wpo.if.of(F, c, t, e, st, v, Q, B, lim, ob.of(c, st, v, ec), h, gt, ge)

# an if: one whose else is an alloc (M.alloc) is given whole
def wpo.if(+e: Cr.Cir.Stmt, +F: Nat, +c: Cr.Cir.Expr, +t: Cr.Cir.Stmt, +st: Cr.Cir.State, -Q: Cr.Cir.State -> Type, +B: Nat, +lim: U32,
  +hw: {Wf(Cr.Cir.Stmt.if{c, t, e}) == True{} : Bool},
  h: DW.Ok(Cr.Cir.exec.if(Cr.Cir.eval(c, st), u => Cr.Cir.exec(F, t, st), u => Cr.Cir.exec(F, e, st)), Q, B, lim),
  gt: {Wf(t) == True{} : Bool} -> DW.Ok(Cr.Cir.exec(F, t, st), Q, B, lim) -> DW.WP(t, F, st, x => Q(x), B, lim),
  ge: {Wf(e) == True{} : Bool} -> DW.Ok(Cr.Cir.exec(F, e, st), Q, B, lim) -> DW.WP(e, F, st, x => Q(x), B, lim)) ->
  DW.WP.if(e, F, c, t, st, Q, B, lim, q => DW.WP(t, F, st, x => q(x), B, lim), q => DW.WP(e, F, st, x => q(x), B, lim)):
  match e:
    case Cr.Cir.Stmt.alloc{+r}:
      match F:
        case 0n:
          h
        case 1n+(+g):
          h
    case Cr.Cir.Stmt.nop{}:
      wpo.if.go(F, c, t, Cr.Cir.Stmt.nop{}, st, Cr.Cir.eval(c, st), Q, B, lim, {==}, h,
        ht => gt(wf.l(Wf(t), Wf(Cr.Cir.Stmt.nop{}), hw), ht), he => ge(wf.r(Wf(t), Wf(Cr.Cir.Stmt.nop{}), hw), he))
    case Cr.Cir.Stmt.set{+r2, +e2}:
      wpo.if.go(F, c, t, Cr.Cir.Stmt.set{r2, e2}, st, Cr.Cir.eval(c, st), Q, B, lim, {==}, h,
        ht => gt(wf.l(Wf(t), Wf(Cr.Cir.Stmt.set{r2, e2}), hw), ht), he => ge(wf.r(Wf(t), Wf(Cr.Cir.Stmt.set{r2, e2}), hw), he))
    case Cr.Cir.Stmt.store{+k2, +c2, +v2}:
      wpo.if.go(F, c, t, Cr.Cir.Stmt.store{k2, c2, v2}, st, Cr.Cir.eval(c, st), Q, B, lim, {==}, h,
        ht => gt(wf.l(Wf(t), Wf(Cr.Cir.Stmt.store{k2, c2, v2}), hw), ht), he => ge(wf.r(Wf(t), Wf(Cr.Cir.Stmt.store{k2, c2, v2}), hw), he))
    case Cr.Cir.Stmt.emit{+v2}:
      wpo.if.go(F, c, t, Cr.Cir.Stmt.emit{v2}, st, Cr.Cir.eval(c, st), Q, B, lim, {==}, h,
        ht => gt(wf.l(Wf(t), Wf(Cr.Cir.Stmt.emit{v2}), hw), ht), he => ge(wf.r(Wf(t), Wf(Cr.Cir.Stmt.emit{v2}), hw), he))
    case Cr.Cir.Stmt.seq{+a2, +b2}:
      wpo.if.go(F, c, t, Cr.Cir.Stmt.seq{a2, b2}, st, Cr.Cir.eval(c, st), Q, B, lim, {==}, h,
        ht => gt(wf.l(Wf(t), Wf(Cr.Cir.Stmt.seq{a2, b2}), hw), ht), he => ge(wf.r(Wf(t), Wf(Cr.Cir.Stmt.seq{a2, b2}), hw), he))
    case Cr.Cir.Stmt.if{+c2, +t2, +e2}:
      wpo.if.go(F, c, t, Cr.Cir.Stmt.if{c2, t2, e2}, st, Cr.Cir.eval(c, st), Q, B, lim, {==}, h,
        ht => gt(wf.l(Wf(t), Wf(Cr.Cir.Stmt.if{c2, t2, e2}), hw), ht), he => ge(wf.r(Wf(t), Wf(Cr.Cir.Stmt.if{c2, t2, e2}), hw), he))
    case Cr.Cir.Stmt.while{+c2, +b2}:
      wpo.if.go(F, c, t, Cr.Cir.Stmt.while{c2, b2}, st, Cr.Cir.eval(c, st), Q, B, lim, {==}, h,
        ht => gt(wf.l(Wf(t), Wf(Cr.Cir.Stmt.while{c2, b2}), hw), ht), he => ge(wf.r(Wf(t), Wf(Cr.Cir.Stmt.while{c2, b2}), hw), he))
    case Cr.Cir.Stmt.halt{+s2}:
      wpo.if.go(F, c, t, Cr.Cir.Stmt.halt{s2}, st, Cr.Cir.eval(c, st), Q, B, lim, {==}, h,
        ht => gt(wf.l(Wf(t), Wf(Cr.Cir.Stmt.halt{s2}), hw), ht), he => ge(wf.r(Wf(t), Wf(Cr.Cir.Stmt.halt{s2}), hw), he))

def wpo.whq(z: Bool, -kb: (Cr.Cir.State -> Type) -> Type, -Q: Cr.Cir.State -> Type, +B: Nat, +lim: U32, +st: Cr.Cir.State,
  -yes: Unit -> Cr.Cir.Out, h: DW.Ok(Cr.Cir.exec.if.of(z, yes, u => Cr.Cir.Out.next{st}), Q, B, lim),
  gy: DW.Ok(yes(Unit{}), Q, B, lim) -> kb(Q)) -> DW.WhQ(z, kb, Q, st):
  match z:
    case False{}:
      gy(h)
    case True{}:
      h

def wpo.wh.of(+g: Nat, +c: Cr.Cir.Expr, +b: Cr.Cir.Stmt, +st: Cr.Cir.State, +v: U32, -Q: Cr.Cir.State -> Type, +B: Nat, +lim: U32,
  pc: DW.Ob(c, st) & {DW.Ev(c, st) == v : U32},
  h: DW.Ok(Cr.Cir.exec.if(Some{v}, u => Cr.Cir.exec.then(Cr.Cir.exec(g, b, st), t => Cr.Cir.exec(g, Cr.Cir.Stmt.while{c, b}, t)), u => Cr.Cir.Out.next{st}), Q, B, lim),
  gb: DW.Ok(Cr.Cir.exec.then(Cr.Cir.exec(g, b, st), t => Cr.Cir.exec(g, Cr.Cir.Stmt.while{c, b}, t)), Q, B, lim) ->
    DW.WP(b, g, st, t => DW.WP(Cr.Cir.Stmt.while{c, b}, g, t, x => Q(x), B, lim), B, lim)) ->
  DW.Ob(c, st) & DW.WhQ(U32.is_zero(DW.Ev(c, st)), q => DW.WP(b, g, st, t => DW.WP(Cr.Cir.Stmt.while{c, b}, g, t, x => q(x), B, lim), B, lim), Q, st):
  (oc, vc) = pc
  (%Equal.sym(U32, DW.Ev(c, st), v, vc) :
    DW.Ob(c, st) & DW.WhQ(U32.is_zero(_), q => DW.WP(b, g, st, t => DW.WP(Cr.Cir.Stmt.while{c, b}, g, t, x => q(x), B, lim), B, lim), Q, st);
   (oc, wpo.whq(U32.is_zero(v), q => DW.WP(b, g, st, t => DW.WP(Cr.Cir.Stmt.while{c, b}, g, t, x => q(x), B, lim), B, lim), Q, B, lim, st,
     u => Cr.Cir.exec.then(Cr.Cir.exec(g, b, st), t => Cr.Cir.exec(g, Cr.Cir.Stmt.while{c, b}, t)), h, gb)))

# a round of a while
def wpo.wh(+g: Nat, +c: Cr.Cir.Expr, +b: Cr.Cir.Stmt, +st: Cr.Cir.State, +mc: Maybe<&2, U32>, -Q: Cr.Cir.State -> Type, +B: Nat, +lim: U32,
  ec: {Cr.Cir.eval(c, st) == mc : Maybe<&2, U32>},
  h: DW.Ok(Cr.Cir.exec.if(mc, u => Cr.Cir.exec.then(Cr.Cir.exec(g, b, st), t => Cr.Cir.exec(g, Cr.Cir.Stmt.while{c, b}, t)), u => Cr.Cir.Out.next{st}), Q, B, lim),
  gb: DW.Ok(Cr.Cir.exec.then(Cr.Cir.exec(g, b, st), t => Cr.Cir.exec(g, Cr.Cir.Stmt.while{c, b}, t)), Q, B, lim) ->
    DW.WP(b, g, st, t => DW.WP(Cr.Cir.Stmt.while{c, b}, g, t, x => Q(x), B, lim), B, lim)) ->
  DW.Ob(c, st) & DW.WhQ(U32.is_zero(DW.Ev(c, st)), q => DW.WP(b, g, st, t => DW.WP(Cr.Cir.Stmt.while{c, b}, g, t, x => q(x), B, lim), B, lim), Q, st):
  match mc:
    case None{}:
      Empty.absurd(DW.Ob(c, st) & DW.WhQ(U32.is_zero(DW.Ev(c, st)), q => DW.WP(b, g, st, t => DW.WP(Cr.Cir.Stmt.while{c, b}, g, t, x => q(x), B, lim), B, lim), Q, st), h)
    case Some{+v}:
      wpo.wh.of(g, c, b, st, v, Q, B, lim, ob.of(c, st, v, ec), h, gb)

# an Ok of a run with the fuel F is its WP for F, when its allocs are
# M.alloc's and it emits nothing
def WP.of(+F: Nat, +s: Cr.Cir.Stmt, +st: Cr.Cir.State, -Q: Cr.Cir.State -> Type, +B: Nat, +lim: U32,
  +hw: {Wf(s) == True{} : Bool}, h: DW.Ok(Cr.Cir.exec(F, s, st), Q, B, lim)) -> DW.WP(s, F, st, Q, B, lim):
  match F:
    case 0n:
      match s:
        case Cr.Cir.Stmt.nop{}:
          h
        case Cr.Cir.Stmt.set{+r, +e}:
          wpo.set(r, e, st, Cr.Cir.eval(e, st), Q, B, lim, {==}, h)
        case Cr.Cir.Stmt.store{+k, +c, +v}:
          wpo.store(k, c, v, st, Cr.Cir.eval(c, st), Cr.Cir.eval(v, st), Q, B, lim, {==}, {==}, h)
        case Cr.Cir.Stmt.alloc{+r}:
          DW.tf(DW.WP(Cr.Cir.Stmt.alloc{r}, F, st, Q, B, lim), hw)
        case Cr.Cir.Stmt.emit{+v}:
          DW.tf(DW.WP(Cr.Cir.Stmt.emit{v}, F, st, Q, B, lim), hw)
        case Cr.Cir.Stmt.seq{+a, +b}:
          WP.of(F, a, st, t => DW.WP(b, F, t, Q, B, lim), B, lim, wf.l(Wf(a), Wf(b), hw),
            DW.OkMono(Cr.Cir.exec(F, a, st), t => DW.Ok(Cr.Cir.exec(F, b, t), Q, B, lim), t => DW.WP(b, F, t, Q, B, lim), B, lim,
              wpo.unthen(Cr.Cir.exec(F, a, st), t => Cr.Cir.exec(F, b, t), Q, B, lim, h),
              t => ht => WP.of(F, b, t, Q, B, lim, wf.r(Wf(a), Wf(b), hw), ht)))
        case Cr.Cir.Stmt.if{+c, +t, +e}:
          wpo.if(e, F, c, t, st, Q, B, lim, hw, h,
            ht => hh => WP.of(F, t, st, x => Q(x), B, lim, ht, DW.OkMono(Cr.Cir.exec(F, t, st), Q, x => Q(x), B, lim, hh, u => p => p)),
            he => hh => WP.of(F, e, st, x => Q(x), B, lim, he, DW.OkMono(Cr.Cir.exec(F, e, st), Q, x => Q(x), B, lim, hh, u => p => p)))
        case Cr.Cir.Stmt.while{+c, +b}:
          Unit{}
        case Cr.Cir.Stmt.halt{+v}:
          h
    case 1n+(+g):
      match s:
        case Cr.Cir.Stmt.nop{}:
          h
        case Cr.Cir.Stmt.set{+r, +e}:
          wpo.set(r, e, st, Cr.Cir.eval(e, st), Q, B, lim, {==}, h)
        case Cr.Cir.Stmt.store{+k, +c, +v}:
          wpo.store(k, c, v, st, Cr.Cir.eval(c, st), Cr.Cir.eval(v, st), Q, B, lim, {==}, {==}, h)
        case Cr.Cir.Stmt.alloc{+r}:
          DW.tf(DW.WP(Cr.Cir.Stmt.alloc{r}, F, st, Q, B, lim), hw)
        case Cr.Cir.Stmt.emit{+v}:
          DW.tf(DW.WP(Cr.Cir.Stmt.emit{v}, F, st, Q, B, lim), hw)
        case Cr.Cir.Stmt.seq{+a, +b}:
          WP.of(F, a, st, t => DW.WP(b, F, t, Q, B, lim), B, lim, wf.l(Wf(a), Wf(b), hw),
            DW.OkMono(Cr.Cir.exec(F, a, st), t => DW.Ok(Cr.Cir.exec(F, b, t), Q, B, lim), t => DW.WP(b, F, t, Q, B, lim), B, lim,
              wpo.unthen(Cr.Cir.exec(F, a, st), t => Cr.Cir.exec(F, b, t), Q, B, lim, h),
              t => ht => WP.of(F, b, t, Q, B, lim, wf.r(Wf(a), Wf(b), hw), ht)))
        case Cr.Cir.Stmt.if{+c, +t, +e}:
          wpo.if(e, F, c, t, st, Q, B, lim, hw, h,
            ht => hh => WP.of(F, t, st, x => Q(x), B, lim, ht, DW.OkMono(Cr.Cir.exec(F, t, st), Q, x => Q(x), B, lim, hh, u => p => p)),
            he => hh => WP.of(F, e, st, x => Q(x), B, lim, he, DW.OkMono(Cr.Cir.exec(F, e, st), Q, x => Q(x), B, lim, hh, u => p => p)))
        case Cr.Cir.Stmt.while{+c, +b}:
          wpo.wh(g, c, b, st, Cr.Cir.eval(c, st), Q, B, lim, {==}, h,
            hb => WP.of(g, b, st, t => DW.WP(Cr.Cir.Stmt.while{c, b}, g, t, x => Q(x), B, lim), B, lim, hw,
              DW.OkMono(Cr.Cir.exec(g, b, st), t => DW.Ok(Cr.Cir.exec(g, Cr.Cir.Stmt.while{c, b}, t), Q, B, lim),
                t => DW.WP(Cr.Cir.Stmt.while{c, b}, g, t, x => Q(x), B, lim), B, lim,
                wpo.unthen(Cr.Cir.exec(g, b, st), t => Cr.Cir.exec(g, Cr.Cir.Stmt.while{c, b}, t), Q, B, lim, hb),
                +t => ht => WP.of(g, Cr.Cir.Stmt.while{c, b}, t, x => Q(x), B, lim, hw,
                  DW.OkMono(Cr.Cir.exec(g, Cr.Cir.Stmt.while{c, b}, t), Q, x => Q(x), B, lim, ht, u => p => p)))))
        case Cr.Cir.Stmt.halt{+v}:
          h

# Registers
# ---------
#
# A state of the walk is X.st of its 63 registers and its cells. The rounds
# set registers of Walk.scr() only, so every register of keep stays (Kept);
# a register's value is read through the sets after it (X.L.gs, X.L.go).

# Nat.is_eq says equal: equal
def nat.eq.t(+a: Nat, +b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      DW.tf({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      DW.tf({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, x => 1n+x, p, q, nat.eq.t(p, q, h))

def mem.ne.b(b: Bool, +scr: List<&2, Nat>, +r: Nat, +j: Nat, eb: {Nat.is_eq(r, j) == b : Bool}, hr: {D.Nat.mem(scr, r) == True{} : Bool},
  hj: {D.Nat.mem(scr, j) == False{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      DW.tf({True{} == False{} : Bool}, Equal.trans(Bool, False{}, D.Nat.mem(scr, r), True{},
        (%Equal.sym(Nat, r, j, nat.eq.t(r, j, eb)) : {False{} == D.Nat.mem(scr, _) : Bool}; Equal.sym(Bool, D.Nat.mem(scr, j), False{}, hj)), hr))

# a register of scr is none of keep's, which Disj keeps out of scr
def mem.ne(+scr: List<&2, Nat>, +r: Nat, +j: Nat, hr: {D.Nat.mem(scr, r) == True{} : Bool}, hj: {D.Nat.mem(scr, j) == False{} : Bool}) ->
  {Nat.is_eq(r, j) == False{} : Bool}:
  mem.ne.b(Nat.is_eq(r, j), scr, r, j, {==}, hr, hj)

# a set of r keeps the register j
def l.go(xs: List<&2, U32>, r: Nat, j: Nat, +v: U32, ne: {Nat.is_eq(r, j) == False{} : Bool}) ->
  {List.get(&2, U32, List.set(&2, U32, xs, r, v), j) == List.get(&2, U32, xs, j) : Maybe<&2, U32>}:
  match xs r j:
    case Nil{} _ _:
      {==}
    case Con{x, t} 0n 0n:
      DW.ft({Some{v} == Some{x} : Maybe<&2, U32>}, ne)
    case Con{x, t} 0n 1n+q:
      {==}
    case Con{x, t} 1n+p 0n:
      {==}
    case Con{x, t} 1n+p 1n+q:
      l.go(t, p, q, v, ne)

# a set of a register of scr keeps the registers of keep, which Disj keeps out of scr
def kept.set(+regs: List<&2, U32>, +regs1: List<&2, U32>, keep: List<&2, Nat>, +scr: List<&2, Nat>, +r: Nat, +v: U32,
  +hk: {D.Disj(keep, scr) == True{} : Bool}, +hr: {D.Nat.mem(scr, r) == True{} : Bool}, h: D.Kept(regs, regs1, keep)) ->
  D.Kept(regs, List.set(&2, U32, regs1, r, v), keep):
  match keep:
    case Nil{}:
      Unit{}
    case Con{+j, rest}:
      (hj, hrs) = h
      (Equal.trans(Maybe<&2, U32>, List.get(&2, U32, List.set(&2, U32, regs1, r, v), j), List.get(&2, U32, regs1, j), List.get(&2, U32, regs, j),
         l.go(regs1, r, j, v, mem.ne(scr, r, j, hr, D.not.t(D.Nat.mem(scr, j), D.and.l(Bool.not(D.Nat.mem(scr, j)), D.Disj(rest, scr), hk)))), hj),
       kept.set(regs, regs1, rest, scr, r, v, D.and.r(Bool.not(D.Nat.mem(scr, j)), D.Disj(rest, scr), hk), hr, hrs))

# Tests of the walk's code
# -----------------------

# the test of wt's tag against K, with the cell c in wt: Cir allows it
def tag.ob(+regs1: List<&2, U32>, +m1: Cr.Cir.Cells, +nx1: U32, +fi: U32, +im: U32, +pg1: U32, +lim: U32, +inp: List<&2, Word(8n)>,
  +c: U32, +K: U32, hr: {List.get(&2, U32, regs1, 19n) == Some{c} : Maybe<&2, U32>}, hc: {Cr.Cir.is_cell(c, im, fi, nx1) == True{} : Bool}) ->
  DW.Ob(Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wt())), Mc.M.c(K)), X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp)):
  (%Equal.sym(Maybe<&2, U32>, List.get(&2, U32, regs1, 19n), Some{c}, hr) :
    ((DW.IsSome(_) & DW.CellOk(Maybe.default(&2, U32, _, 0), X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp))) & Unit) & Unit;
   (((Unit{}, Equal.sym(Bool, Cr.Cir.is_cell(c, im, fi, nx1), True{}, hc)), Unit{}), Unit{}))

# its value, for the tag tg of c
def tag.ev(+regs1: List<&2, U32>, +m1: Cr.Cir.Cells, +nx1: U32, +fi: U32, +im: U32, +pg1: U32, +lim: U32, +inp: List<&2, Word(8n)>,
  +c: U32, +K: U32, +tg: U32, hr: {List.get(&2, U32, regs1, 19n) == Some{c} : Maybe<&2, U32>}, htg: {D.Tg(m1, c) == tg : U32}) ->
  {DW.Ev(Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wt())), Mc.M.c(K)), X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp)) == Bool.to_u32(U32.is_eq(tg, K)) : U32}:
  (%Equal.sym(Maybe<&2, U32>, List.get(&2, U32, regs1, 19n), Some{c}, hr) :
    {Bool.to_u32(U32.is_eq(U32.and(Cr.Cir.Cell.get(0n, Cr.Cir.Cells.get(m1, Maybe.default(&2, U32, _, 0))), 63), K)) == Bool.to_u32(U32.is_eq(tg, K)) : U32};
   (%Equal.sym(U32, D.Tg(m1, c), tg, htg) : {Bool.to_u32(U32.is_eq(_, K)) == Bool.to_u32(U32.is_eq(tg, K)) : U32}; {==}))

# The dispatch
# ------------
#
# M.walk's loop runs W.body() while wres is 0: the tests of wt's tag pick
# the round of a λ, a λ-match of pairs or of labels, an App, Efq, or a leaf
# (W.e1() to W.e4() are the tests after the first).

def sel.w(x: Cr.Cir.Stmt) -> Cr.Cir.Stmt:
  match x:
    case Cr.Cir.Stmt.while{_, b}:
      b
    case _:
      Cr.Cir.Stmt.nop{}

def W.loop() -> Cr.Cir.Stmt:
  X.sel.a(X.sel.b(X.sel.b(X.sel.b(Mc.M.walk()))))

def W.e4() -> Cr.Cir.Stmt:
  Mc.M.if(Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wt())), Mc.M.c(Mc.T.efq())),
    Mc.M.set(Mc.R.wres(), Mc.M.pick(Mc.M.eq(Mc.M.g(Mc.R.wargs()), Mc.M.c(0)), Mc.M.c(2), Mc.M.c(3))),
    Mc.M.set(Mc.R.wres(), Mc.M.c(1)))

def W.e3() -> Cr.Cir.Stmt:
  Mc.M.if(Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wt())), Mc.M.c(Mc.T.app())), Mc.M.walk.app(), W.e4())

def W.e2() -> Cr.Cir.Stmt:
  Mc.M.if(Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wt())), Mc.M.c(Mc.T.mat())), Mc.M.walk.mat(), W.e3())

def W.e1() -> Cr.Cir.Stmt:
  Mc.M.if(Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wt())), Mc.M.c(Mc.T.prj())), Mc.M.walk.prj(), W.e2())

def W.body() -> Cr.Cir.Stmt:
  Mc.M.if(Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wt())), Mc.M.c(Mc.T.lam())), Mc.M.walk.lam(), W.e1())

# M.walk's loop is a while on wres of W.body()
def W.loop.eq() -> {W.loop() == Mc.M.while(Mc.M.eq(Mc.M.g(Mc.R.wres()), Mc.M.c(0)), W.body()) : Cr.Cir.Stmt}:
  {==}

def is.alloc(s: Cr.Cir.Stmt) -> Bool:
  match s:
    case Cr.Cir.Stmt.alloc{_}:
      True{}
    case _:
      False{}

# a test of wt's tag that fails: the else, for an else that is no alloc
def disp.no(+e: Cr.Cir.Stmt, +g: Nat, +t: Cr.Cir.Stmt, +regs1: List<&2, U32>, +m1: Cr.Cir.Cells, +nx1: U32, +fi: U32, +im: U32,
  +pg1: U32, +lim: U32, +inp: List<&2, Word(8n)>, -K: Cr.Cir.State -> Type, +B: Nat, +c: U32, +K0: U32, +tg: U32,
  hea: {is.alloc(e) == False{} : Bool}, +hr: {List.get(&2, U32, regs1, 19n) == Some{c} : Maybe<&2, U32>},
  hc: {Cr.Cir.is_cell(c, im, fi, nx1) == True{} : Bool}, htg: {D.Tg(m1, c) == tg : U32}, hn: {U32.is_eq(tg, K0) == False{} : Bool},
  w: DW.WP(e, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => K(x), B, lim)) ->
  DW.WP(Cr.Cir.Stmt.if{Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wt())), Mc.M.c(K0)), t, e}, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), K, B, lim):
  match e:
    case Cr.Cir.Stmt.alloc{+r}:
      DW.ft(DW.WP(Cr.Cir.Stmt.if{Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wt())), Mc.M.c(K0)), t, Cr.Cir.Stmt.alloc{r}}, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), K, B, lim), hea)
    case Cr.Cir.Stmt.nop{}:
      (tag.ob(regs1, m1, nx1, fi, im, pg1, lim, inp, c, K0, hr, hc),
       (%Equal.sym(U32, DW.Ev(Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wt())), Mc.M.c(K0)), X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp)), Bool.to_u32(U32.is_eq(tg, K0)), tag.ev(regs1, m1, nx1, fi, im, pg1, lim, inp, c, K0, tg, hr, htg)) :
          DW.IfQ(U32.is_zero(_), q => DW.WP(t, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.nop{}, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), K);
        %Equal.sym(Bool, U32.is_eq(tg, K0), False{}, hn) :
          DW.IfQ(U32.is_zero(Bool.to_u32(_)), q => DW.WP(t, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.nop{}, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), K);
        w))
    case Cr.Cir.Stmt.set{+r2, +e2}:
      (tag.ob(regs1, m1, nx1, fi, im, pg1, lim, inp, c, K0, hr, hc),
       (%Equal.sym(U32, DW.Ev(Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wt())), Mc.M.c(K0)), X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp)), Bool.to_u32(U32.is_eq(tg, K0)), tag.ev(regs1, m1, nx1, fi, im, pg1, lim, inp, c, K0, tg, hr, htg)) :
          DW.IfQ(U32.is_zero(_), q => DW.WP(t, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.set{r2, e2}, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), K);
        %Equal.sym(Bool, U32.is_eq(tg, K0), False{}, hn) :
          DW.IfQ(U32.is_zero(Bool.to_u32(_)), q => DW.WP(t, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.set{r2, e2}, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), K);
        w))
    case Cr.Cir.Stmt.store{+k2, +c2, +v2}:
      (tag.ob(regs1, m1, nx1, fi, im, pg1, lim, inp, c, K0, hr, hc),
       (%Equal.sym(U32, DW.Ev(Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wt())), Mc.M.c(K0)), X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp)), Bool.to_u32(U32.is_eq(tg, K0)), tag.ev(regs1, m1, nx1, fi, im, pg1, lim, inp, c, K0, tg, hr, htg)) :
          DW.IfQ(U32.is_zero(_), q => DW.WP(t, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.store{k2, c2, v2}, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), K);
        %Equal.sym(Bool, U32.is_eq(tg, K0), False{}, hn) :
          DW.IfQ(U32.is_zero(Bool.to_u32(_)), q => DW.WP(t, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.store{k2, c2, v2}, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), K);
        w))
    case Cr.Cir.Stmt.emit{+v2}:
      (tag.ob(regs1, m1, nx1, fi, im, pg1, lim, inp, c, K0, hr, hc),
       (%Equal.sym(U32, DW.Ev(Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wt())), Mc.M.c(K0)), X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp)), Bool.to_u32(U32.is_eq(tg, K0)), tag.ev(regs1, m1, nx1, fi, im, pg1, lim, inp, c, K0, tg, hr, htg)) :
          DW.IfQ(U32.is_zero(_), q => DW.WP(t, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.emit{v2}, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), K);
        %Equal.sym(Bool, U32.is_eq(tg, K0), False{}, hn) :
          DW.IfQ(U32.is_zero(Bool.to_u32(_)), q => DW.WP(t, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.emit{v2}, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), K);
        w))
    case Cr.Cir.Stmt.seq{+a2, +b2}:
      (tag.ob(regs1, m1, nx1, fi, im, pg1, lim, inp, c, K0, hr, hc),
       (%Equal.sym(U32, DW.Ev(Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wt())), Mc.M.c(K0)), X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp)), Bool.to_u32(U32.is_eq(tg, K0)), tag.ev(regs1, m1, nx1, fi, im, pg1, lim, inp, c, K0, tg, hr, htg)) :
          DW.IfQ(U32.is_zero(_), q => DW.WP(t, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.seq{a2, b2}, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), K);
        %Equal.sym(Bool, U32.is_eq(tg, K0), False{}, hn) :
          DW.IfQ(U32.is_zero(Bool.to_u32(_)), q => DW.WP(t, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.seq{a2, b2}, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), K);
        w))
    case Cr.Cir.Stmt.if{+c2, +t2, +e2}:
      (tag.ob(regs1, m1, nx1, fi, im, pg1, lim, inp, c, K0, hr, hc),
       (%Equal.sym(U32, DW.Ev(Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wt())), Mc.M.c(K0)), X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp)), Bool.to_u32(U32.is_eq(tg, K0)), tag.ev(regs1, m1, nx1, fi, im, pg1, lim, inp, c, K0, tg, hr, htg)) :
          DW.IfQ(U32.is_zero(_), q => DW.WP(t, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.if{c2, t2, e2}, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), K);
        %Equal.sym(Bool, U32.is_eq(tg, K0), False{}, hn) :
          DW.IfQ(U32.is_zero(Bool.to_u32(_)), q => DW.WP(t, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.if{c2, t2, e2}, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), K);
        w))
    case Cr.Cir.Stmt.while{+c2, +b2}:
      (tag.ob(regs1, m1, nx1, fi, im, pg1, lim, inp, c, K0, hr, hc),
       (%Equal.sym(U32, DW.Ev(Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wt())), Mc.M.c(K0)), X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp)), Bool.to_u32(U32.is_eq(tg, K0)), tag.ev(regs1, m1, nx1, fi, im, pg1, lim, inp, c, K0, tg, hr, htg)) :
          DW.IfQ(U32.is_zero(_), q => DW.WP(t, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.while{c2, b2}, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), K);
        %Equal.sym(Bool, U32.is_eq(tg, K0), False{}, hn) :
          DW.IfQ(U32.is_zero(Bool.to_u32(_)), q => DW.WP(t, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.while{c2, b2}, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), K);
        w))
    case Cr.Cir.Stmt.halt{+s2}:
      (tag.ob(regs1, m1, nx1, fi, im, pg1, lim, inp, c, K0, hr, hc),
       (%Equal.sym(U32, DW.Ev(Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wt())), Mc.M.c(K0)), X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp)), Bool.to_u32(U32.is_eq(tg, K0)), tag.ev(regs1, m1, nx1, fi, im, pg1, lim, inp, c, K0, tg, hr, htg)) :
          DW.IfQ(U32.is_zero(_), q => DW.WP(t, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.halt{s2}, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), K);
        %Equal.sym(Bool, U32.is_eq(tg, K0), False{}, hn) :
          DW.IfQ(U32.is_zero(Bool.to_u32(_)), q => DW.WP(t, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.halt{s2}, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), K);
        w))

# a set of a register below 63, then the end
def wp.set.k(+g: Nat, +r: Nat, +v: U32, +regs1: List<&2, U32>, +m1: Cr.Cir.Cells, +nx1: U32, +fi: U32, +im: U32, +pg1: U32, +lim: U32,
  +inp: List<&2, Word(8n)>, -K: Cr.Cir.State -> Type, +B: Nat, hl: {List.length(&2, U32, regs1) == 63n : Nat},
  hr: {Nat.is_lt(r, 63n) == True{} : Bool}, k: K(X.X.st(List.set(&2, U32, regs1, r, v), m1, nx1, fi, im, pg1, lim, inp))) ->
  DW.WP(Cr.Cir.Stmt.set{r, Cr.Cir.Expr.const{v}}, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), K, B, lim):
  (Unit{}, ((%Equal.sym(Nat, List.length(&2, U32, regs1), 63n, hl) : DW.Tr(Nat.is_lt(r, _)); (%Equal.sym(Bool, Nat.is_lt(r, 63n), True{}, hr) : DW.Tr(_); Unit{})), k))

# a round at a leaf of none of the walk's kinds: wres gets 1
def disp.other(+g: Nat, +regs1: List<&2, U32>, +m1: Cr.Cir.Cells, +nx1: U32, +fi: U32, +im: U32, +pg1: U32, +lim: U32,
  +inp: List<&2, Word(8n)>, -K: Cr.Cir.State -> Type, +B: Nat, +c: U32, +tg: U32,
  +hr: {List.get(&2, U32, regs1, 19n) == Some{c} : Maybe<&2, U32>}, +hc: {Cr.Cir.is_cell(c, im, fi, nx1) == True{} : Bool},
  +htg: {D.Tg(m1, c) == tg : U32},
  h7: {U32.is_eq(tg, Mc.T.lam()) == False{} : Bool}, h11: {U32.is_eq(tg, Mc.T.prj()) == False{} : Bool},
  h14: {U32.is_eq(tg, Mc.T.mat()) == False{} : Bool}, h8: {U32.is_eq(tg, Mc.T.app()) == False{} : Bool},
  h15: {U32.is_eq(tg, Mc.T.efq()) == False{} : Bool}, hl: {List.length(&2, U32, regs1) == 63n : Nat},
  k: K(X.X.st(List.set(&2, U32, regs1, 26n, 1), m1, nx1, fi, im, pg1, lim, inp))) ->
  DW.WP(W.body(), g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), K, B, lim):
  disp.no(W.e1(), g, Mc.M.walk.lam(), regs1, m1, nx1, fi, im, pg1, lim, inp, K, B, c, Mc.T.lam(), tg, {==}, hr, hc, htg, h7,
    disp.no(W.e2(), g, Mc.M.walk.prj(), regs1, m1, nx1, fi, im, pg1, lim, inp, x => K(x), B, c, Mc.T.prj(), tg, {==}, hr, hc, htg, h11,
      disp.no(W.e3(), g, Mc.M.walk.mat(), regs1, m1, nx1, fi, im, pg1, lim, inp, x => K(x), B, c, Mc.T.mat(), tg, {==}, hr, hc, htg, h14,
        disp.no(W.e4(), g, Mc.M.walk.app(), regs1, m1, nx1, fi, im, pg1, lim, inp, x => K(x), B, c, Mc.T.app(), tg, {==}, hr, hc, htg, h8,
          disp.no(Mc.M.set(Mc.R.wres(), Mc.M.c(1)), g, Mc.M.set(Mc.R.wres(), Mc.M.pick(Mc.M.eq(Mc.M.g(Mc.R.wargs()), Mc.M.c(0)), Mc.M.c(2), Mc.M.c(3))),
            regs1, m1, nx1, fi, im, pg1, lim, inp, x => K(x), B, c, Mc.T.efq(), tg, {==}, hr, hc, htg, h15,
            wp.set.k(g, 26n, 1, regs1, m1, nx1, fi, im, pg1, lim, inp, x => K(x), B, hl, {==}, k))))))

# a test of wt's tag that passes: the then
def disp.yes(+e: Cr.Cir.Stmt, +g: Nat, +t: Cr.Cir.Stmt, +regs1: List<&2, U32>, +m1: Cr.Cir.Cells, +nx1: U32, +fi: U32, +im: U32,
  +pg1: U32, +lim: U32, +inp: List<&2, Word(8n)>, -K: Cr.Cir.State -> Type, +B: Nat, +c: U32, +K0: U32, +tg: U32,
  hea: {is.alloc(e) == False{} : Bool}, +hr: {List.get(&2, U32, regs1, 19n) == Some{c} : Maybe<&2, U32>},
  hc: {Cr.Cir.is_cell(c, im, fi, nx1) == True{} : Bool}, htg: {D.Tg(m1, c) == tg : U32}, hy: {U32.is_eq(tg, K0) == True{} : Bool},
  w: DW.WP(t, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => K(x), B, lim)) ->
  DW.WP(Cr.Cir.Stmt.if{Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wt())), Mc.M.c(K0)), t, e}, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), K, B, lim):
  match e:
    case Cr.Cir.Stmt.alloc{+r}:
      DW.ft(DW.WP(Cr.Cir.Stmt.if{Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wt())), Mc.M.c(K0)), t, Cr.Cir.Stmt.alloc{r}}, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), K, B, lim), hea)
    case Cr.Cir.Stmt.nop{}:
      (tag.ob(regs1, m1, nx1, fi, im, pg1, lim, inp, c, K0, hr, hc),
       (%Equal.sym(U32, DW.Ev(Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wt())), Mc.M.c(K0)), X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp)), Bool.to_u32(U32.is_eq(tg, K0)), tag.ev(regs1, m1, nx1, fi, im, pg1, lim, inp, c, K0, tg, hr, htg)) :
          DW.IfQ(U32.is_zero(_), q => DW.WP(t, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.nop{}, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), K);
        %Equal.sym(Bool, U32.is_eq(tg, K0), True{}, hy) :
          DW.IfQ(U32.is_zero(Bool.to_u32(_)), q => DW.WP(t, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.nop{}, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), K);
        w))
    case Cr.Cir.Stmt.set{+r2, +e2}:
      (tag.ob(regs1, m1, nx1, fi, im, pg1, lim, inp, c, K0, hr, hc),
       (%Equal.sym(U32, DW.Ev(Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wt())), Mc.M.c(K0)), X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp)), Bool.to_u32(U32.is_eq(tg, K0)), tag.ev(regs1, m1, nx1, fi, im, pg1, lim, inp, c, K0, tg, hr, htg)) :
          DW.IfQ(U32.is_zero(_), q => DW.WP(t, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.set{r2, e2}, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), K);
        %Equal.sym(Bool, U32.is_eq(tg, K0), True{}, hy) :
          DW.IfQ(U32.is_zero(Bool.to_u32(_)), q => DW.WP(t, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.set{r2, e2}, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), K);
        w))
    case Cr.Cir.Stmt.store{+k2, +c2, +v2}:
      (tag.ob(regs1, m1, nx1, fi, im, pg1, lim, inp, c, K0, hr, hc),
       (%Equal.sym(U32, DW.Ev(Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wt())), Mc.M.c(K0)), X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp)), Bool.to_u32(U32.is_eq(tg, K0)), tag.ev(regs1, m1, nx1, fi, im, pg1, lim, inp, c, K0, tg, hr, htg)) :
          DW.IfQ(U32.is_zero(_), q => DW.WP(t, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.store{k2, c2, v2}, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), K);
        %Equal.sym(Bool, U32.is_eq(tg, K0), True{}, hy) :
          DW.IfQ(U32.is_zero(Bool.to_u32(_)), q => DW.WP(t, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.store{k2, c2, v2}, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), K);
        w))
    case Cr.Cir.Stmt.emit{+v2}:
      (tag.ob(regs1, m1, nx1, fi, im, pg1, lim, inp, c, K0, hr, hc),
       (%Equal.sym(U32, DW.Ev(Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wt())), Mc.M.c(K0)), X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp)), Bool.to_u32(U32.is_eq(tg, K0)), tag.ev(regs1, m1, nx1, fi, im, pg1, lim, inp, c, K0, tg, hr, htg)) :
          DW.IfQ(U32.is_zero(_), q => DW.WP(t, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.emit{v2}, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), K);
        %Equal.sym(Bool, U32.is_eq(tg, K0), True{}, hy) :
          DW.IfQ(U32.is_zero(Bool.to_u32(_)), q => DW.WP(t, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.emit{v2}, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), K);
        w))
    case Cr.Cir.Stmt.seq{+a2, +b2}:
      (tag.ob(regs1, m1, nx1, fi, im, pg1, lim, inp, c, K0, hr, hc),
       (%Equal.sym(U32, DW.Ev(Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wt())), Mc.M.c(K0)), X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp)), Bool.to_u32(U32.is_eq(tg, K0)), tag.ev(regs1, m1, nx1, fi, im, pg1, lim, inp, c, K0, tg, hr, htg)) :
          DW.IfQ(U32.is_zero(_), q => DW.WP(t, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.seq{a2, b2}, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), K);
        %Equal.sym(Bool, U32.is_eq(tg, K0), True{}, hy) :
          DW.IfQ(U32.is_zero(Bool.to_u32(_)), q => DW.WP(t, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.seq{a2, b2}, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), K);
        w))
    case Cr.Cir.Stmt.if{+c2, +t2, +e2}:
      (tag.ob(regs1, m1, nx1, fi, im, pg1, lim, inp, c, K0, hr, hc),
       (%Equal.sym(U32, DW.Ev(Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wt())), Mc.M.c(K0)), X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp)), Bool.to_u32(U32.is_eq(tg, K0)), tag.ev(regs1, m1, nx1, fi, im, pg1, lim, inp, c, K0, tg, hr, htg)) :
          DW.IfQ(U32.is_zero(_), q => DW.WP(t, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.if{c2, t2, e2}, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), K);
        %Equal.sym(Bool, U32.is_eq(tg, K0), True{}, hy) :
          DW.IfQ(U32.is_zero(Bool.to_u32(_)), q => DW.WP(t, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.if{c2, t2, e2}, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), K);
        w))
    case Cr.Cir.Stmt.while{+c2, +b2}:
      (tag.ob(regs1, m1, nx1, fi, im, pg1, lim, inp, c, K0, hr, hc),
       (%Equal.sym(U32, DW.Ev(Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wt())), Mc.M.c(K0)), X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp)), Bool.to_u32(U32.is_eq(tg, K0)), tag.ev(regs1, m1, nx1, fi, im, pg1, lim, inp, c, K0, tg, hr, htg)) :
          DW.IfQ(U32.is_zero(_), q => DW.WP(t, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.while{c2, b2}, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), K);
        %Equal.sym(Bool, U32.is_eq(tg, K0), True{}, hy) :
          DW.IfQ(U32.is_zero(Bool.to_u32(_)), q => DW.WP(t, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.while{c2, b2}, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), K);
        w))
    case Cr.Cir.Stmt.halt{+s2}:
      (tag.ob(regs1, m1, nx1, fi, im, pg1, lim, inp, c, K0, hr, hc),
       (%Equal.sym(U32, DW.Ev(Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wt())), Mc.M.c(K0)), X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp)), Bool.to_u32(U32.is_eq(tg, K0)), tag.ev(regs1, m1, nx1, fi, im, pg1, lim, inp, c, K0, tg, hr, htg)) :
          DW.IfQ(U32.is_zero(_), q => DW.WP(t, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.halt{s2}, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), K);
        %Equal.sym(Bool, U32.is_eq(tg, K0), True{}, hy) :
          DW.IfQ(U32.is_zero(Bool.to_u32(_)), q => DW.WP(t, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.halt{s2}, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => q(x), B, lim), K);
        w))

# the rounds that the tags of a λ, a λ-match of pairs, of labels, an App and Efq pick
def disp.lam(+g: Nat, +regs1: List<&2, U32>, +m1: Cr.Cir.Cells, +nx1: U32, +fi: U32, +im: U32, +pg1: U32, +lim: U32,
  +inp: List<&2, Word(8n)>, -K: Cr.Cir.State -> Type, +B: Nat, +c: U32,
  +hr: {List.get(&2, U32, regs1, 19n) == Some{c} : Maybe<&2, U32>}, +hc: {Cr.Cir.is_cell(c, im, fi, nx1) == True{} : Bool},
  +htg: {D.Tg(m1, c) == 7 : U32}, w: DW.WP(Mc.M.walk.lam(), g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => K(x), B, lim)) ->
  DW.WP(W.body(), g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), K, B, lim):
  disp.yes(W.e1(), g, Mc.M.walk.lam(), regs1, m1, nx1, fi, im, pg1, lim, inp, K, B, c, Mc.T.lam(), 7, {==}, hr, hc, htg, {==}, w)

def disp.prj(+g: Nat, +regs1: List<&2, U32>, +m1: Cr.Cir.Cells, +nx1: U32, +fi: U32, +im: U32, +pg1: U32, +lim: U32,
  +inp: List<&2, Word(8n)>, -K: Cr.Cir.State -> Type, +B: Nat, +c: U32,
  +hr: {List.get(&2, U32, regs1, 19n) == Some{c} : Maybe<&2, U32>}, +hc: {Cr.Cir.is_cell(c, im, fi, nx1) == True{} : Bool},
  +htg: {D.Tg(m1, c) == 11 : U32}, w: DW.WP(Mc.M.walk.prj(), g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => K(x), B, lim)) ->
  DW.WP(W.body(), g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), K, B, lim):
  disp.no(W.e1(), g, Mc.M.walk.lam(), regs1, m1, nx1, fi, im, pg1, lim, inp, K, B, c, Mc.T.lam(), 11, {==}, hr, hc, htg, {==},
    disp.yes(W.e2(), g, Mc.M.walk.prj(), regs1, m1, nx1, fi, im, pg1, lim, inp, x => K(x), B, c, Mc.T.prj(), 11, {==}, hr, hc, htg, {==}, w))

def disp.mat(+g: Nat, +regs1: List<&2, U32>, +m1: Cr.Cir.Cells, +nx1: U32, +fi: U32, +im: U32, +pg1: U32, +lim: U32,
  +inp: List<&2, Word(8n)>, -K: Cr.Cir.State -> Type, +B: Nat, +c: U32,
  +hr: {List.get(&2, U32, regs1, 19n) == Some{c} : Maybe<&2, U32>}, +hc: {Cr.Cir.is_cell(c, im, fi, nx1) == True{} : Bool},
  +htg: {D.Tg(m1, c) == 14 : U32}, w: DW.WP(Mc.M.walk.mat(), g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => K(x), B, lim)) ->
  DW.WP(W.body(), g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), K, B, lim):
  disp.no(W.e1(), g, Mc.M.walk.lam(), regs1, m1, nx1, fi, im, pg1, lim, inp, K, B, c, Mc.T.lam(), 14, {==}, hr, hc, htg, {==},
    disp.no(W.e2(), g, Mc.M.walk.prj(), regs1, m1, nx1, fi, im, pg1, lim, inp, x => K(x), B, c, Mc.T.prj(), 14, {==}, hr, hc, htg, {==},
      disp.yes(W.e3(), g, Mc.M.walk.mat(), regs1, m1, nx1, fi, im, pg1, lim, inp, x => K(x), B, c, Mc.T.mat(), 14, {==}, hr, hc, htg, {==}, w)))

def disp.app(+g: Nat, +regs1: List<&2, U32>, +m1: Cr.Cir.Cells, +nx1: U32, +fi: U32, +im: U32, +pg1: U32, +lim: U32,
  +inp: List<&2, Word(8n)>, -K: Cr.Cir.State -> Type, +B: Nat, +c: U32,
  +hr: {List.get(&2, U32, regs1, 19n) == Some{c} : Maybe<&2, U32>}, +hc: {Cr.Cir.is_cell(c, im, fi, nx1) == True{} : Bool},
  +htg: {D.Tg(m1, c) == 8 : U32}, w: DW.WP(Mc.M.walk.app(), g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => K(x), B, lim)) ->
  DW.WP(W.body(), g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), K, B, lim):
  disp.no(W.e1(), g, Mc.M.walk.lam(), regs1, m1, nx1, fi, im, pg1, lim, inp, K, B, c, Mc.T.lam(), 8, {==}, hr, hc, htg, {==},
    disp.no(W.e2(), g, Mc.M.walk.prj(), regs1, m1, nx1, fi, im, pg1, lim, inp, x => K(x), B, c, Mc.T.prj(), 8, {==}, hr, hc, htg, {==},
      disp.no(W.e3(), g, Mc.M.walk.mat(), regs1, m1, nx1, fi, im, pg1, lim, inp, x => K(x), B, c, Mc.T.mat(), 8, {==}, hr, hc, htg, {==},
        disp.yes(W.e4(), g, Mc.M.walk.app(), regs1, m1, nx1, fi, im, pg1, lim, inp, x => K(x), B, c, Mc.T.app(), 8, {==}, hr, hc, htg, {==}, w))))

def disp.efq(+g: Nat, +regs1: List<&2, U32>, +m1: Cr.Cir.Cells, +nx1: U32, +fi: U32, +im: U32, +pg1: U32, +lim: U32,
  +inp: List<&2, Word(8n)>, -K: Cr.Cir.State -> Type, +B: Nat, +c: U32,
  +hr: {List.get(&2, U32, regs1, 19n) == Some{c} : Maybe<&2, U32>}, +hc: {Cr.Cir.is_cell(c, im, fi, nx1) == True{} : Bool},
  +htg: {D.Tg(m1, c) == 15 : U32},
  w: DW.WP(Mc.M.set(Mc.R.wres(), Mc.M.pick(Mc.M.eq(Mc.M.g(Mc.R.wargs()), Mc.M.c(0)), Mc.M.c(2), Mc.M.c(3))), g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), x => K(x), B, lim)) ->
  DW.WP(W.body(), g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), K, B, lim):
  disp.no(W.e1(), g, Mc.M.walk.lam(), regs1, m1, nx1, fi, im, pg1, lim, inp, K, B, c, Mc.T.lam(), 15, {==}, hr, hc, htg, {==},
    disp.no(W.e2(), g, Mc.M.walk.prj(), regs1, m1, nx1, fi, im, pg1, lim, inp, x => K(x), B, c, Mc.T.prj(), 15, {==}, hr, hc, htg, {==},
      disp.no(W.e3(), g, Mc.M.walk.mat(), regs1, m1, nx1, fi, im, pg1, lim, inp, x => K(x), B, c, Mc.T.mat(), 15, {==}, hr, hc, htg, {==},
        disp.no(W.e4(), g, Mc.M.walk.app(), regs1, m1, nx1, fi, im, pg1, lim, inp, x => K(x), B, c, Mc.T.app(), 15, {==}, hr, hc, htg, {==},
          disp.yes(Mc.M.set(Mc.R.wres(), Mc.M.c(1)), g, Mc.M.set(Mc.R.wres(), Mc.M.pick(Mc.M.eq(Mc.M.g(Mc.R.wargs()), Mc.M.c(0)), Mc.M.c(2), Mc.M.c(3))),
            regs1, m1, nx1, fi, im, pg1, lim, inp, x => K(x), B, c, Mc.T.efq(), 15, {==}, hr, hc, htg, {==}, w)))))

# The loop
# --------
#
# A round of M.walk's loop starts in a state of WS: the subtree s of the case
# tree at the STATIC cell c in wt, held first among HS's borrowed terms; the
# locals e (the chain env in wenv, wn of them) and the arguments left ys (the
# chain args in wargs), where Eval.walk(tt, Nil, xs) is Eval.walk(s,
# terms(e), ys); the chains (Ag), what the walk keeps (Kept.cells), and Acc
# with the chains among the temporaries. A round ends in such a state (WJ's
# Inl) or, with wres set, in WalkQ (WJ's Inr).

# the walk's registers wt, wenv, wargs, wn and pend, and keep's
def WR(+regs: List<&2, U32>, +keep: List<&2, Nat>, +regs2: List<&2, U32>, +c: U32, +env: U32, +n: Nat, +args: U32,
  +pend2: U32) -> Data:
  D.P2({List.length(&2, U32, regs2) == 63n : Nat}, D.P2(D.Kept(regs, regs2, keep),
  D.P2({List.get(&2, U32, regs2, 19n) == Some{c} : Maybe<&2, U32>}, D.P2({List.get(&2, U32, regs2, 20n) == Some{env} : Maybe<&2, U32>},
  D.P2({List.get(&2, U32, regs2, 21n) == Some{args} : Maybe<&2, U32>},
  D.P2({List.get(&2, U32, regs2, 25n) == Some{U32.from_nat(n)} : Maybe<&2, U32>},
    {List.get(&2, U32, regs2, 3n) == Some{pend2} : Maybe<&2, U32>}))))))

# each term of ts has at most n nodes
def TS.le(ts: List<&2, Bk.Term>, +n: Nat) -> Data:
  match ts:
    case Nil{}:
      Unit
    case Con{t, rest}:
      D.P2(N.Le(Pg.Term.size(t), n), TS.le(rest, n))

def ts.le.mono(ts: List<&2, Bk.Term>, +n: Nat, +n2: Nat, h: TS.le(ts, n), +hn: N.Le(n, n2)) -> TS.le(ts, n2):
  match ts:
    case Nil{}:
      Unit{}
    case Con{+t, +rest}:
      (h1, hr) = h
      (N.le_trans(Pg.Term.size(t), n, n2, h1, hn), ts.le.mono(rest, n, n2, hr, hn))

def ts.le.self(ts: List<&2, Bk.Term>) -> TS.le(ts, 1n+D.Terms.size(ts)):
  match ts:
    case Nil{}:
      Unit{}
    case Con{+t, +rest}:
      (N.le_succ(Pg.Term.size(t), Nat.add(Pg.Term.size(t), D.Terms.size(rest)), N.le_add_r(Pg.Term.size(t), D.Terms.size(rest))),
       ts.le.mono(rest, 1n+D.Terms.size(rest), 1n+Nat.add(Pg.Term.size(t), D.Terms.size(rest)), ts.le.self(rest),
         N.le_add_l(Pg.Term.size(t), D.Terms.size(rest))))

def mem.app.r(ys: List<&2, U32>, +zs: List<&2, U32>, +c: U32, h: {D.Mem(zs, c) == True{} : Bool}) ->
  {D.Mem(List.append(&2, U32, ys, zs), c) == True{} : Bool}:
  match ys:
    case Nil{}:
      h
    case Con{+y, +rest}:
      D.or.r(U32.is_eq(y, c), D.Mem(List.append(&2, U32, rest, zs), c), mem.app.r(rest, zs, c, h))

def allin.app.r(xs: List<&2, U32>, +ys: List<&2, U32>, +zs: List<&2, U32>, +h: {D.AllIn(xs, zs) == True{} : Bool}) ->
  {D.AllIn(xs, List.append(&2, U32, ys, zs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      D.and.i(D.Mem(List.append(&2, U32, ys, zs), x), D.AllIn(rest, List.append(&2, U32, ys, zs)),
        mem.app.r(ys, zs, x, D.and.l(D.Mem(zs, x), D.AllIn(rest, zs), h)),
        allin.app.r(rest, ys, zs, D.and.r(D.Mem(zs, x), D.AllIn(rest, zs), h)))

# the heap: HS with the subtree first among the borrowed terms, the chains,
# what the walk keeps, no more STATIC own cells than at the start, Acc with
# the chains among the temporaries, the chains' cells below nx of ps ++ es or
# term cells (as the walk took them), the budget's measure (Acc.need, and two
# cells a node of the tree left), the nodes of the chains' terms (at most
# 1 + those of xs) and the own cells within the walk's budget (WalkQ's bound)
def WH(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32,
  +fi: U32, +im: U32, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>,
  +tc: U32, +tt: Bk.Term, +a: U32, +xs: List<&2, El.Arg>, +xs0: List<&2, D.TmpE>, +m2: Cr.Cir.Cells, +nx2: U32,
  +c: U32, +s: Bk.Term, +env: U32, +e: List<&2, El.Arg>, +args: U32, +ys: List<&2, El.Arg>, +pend2: U32,
  +ps2: List<&2, U32>) -> Data:
  D.P2(D.HS(ds, ks, img, m2, nx2, fi, im, os, Con{D.Rt{c, s}, Con{D.Rt{tc, tt}, bs}}, fs, sp, pend2, ps2),
  D.P2(D.Ag(ds, m2, im, fi, nx2, ks, img, ps2, os, Nil{}, env, e),
  D.P2(D.Ag(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, ys),
  D.P2(D.Kept.cells(m, nx, fi, ps, D.Tmp.cells(D.Ag.cells(xs, m, a)), m2, nx2, ps2),
  D.P2(N.Le(D.Stat(Nat.sub(U32.to_nat(nx2), U32.to_nat(fi)), m2, fi), D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi)),
  D.P2(D.Ex(List<&2, D.Rt>, zs2 => D.AccK(True{}, ds, ks, img, m2, nx2, fi, im, os,
      List.append(&2, D.TmpE, D.Ag.cells(e, m2, env), List.append(&2, D.TmpE, D.Ag.cells(ys, m2, args), xs0)), sp, fs, ps2, zs2)),
  D.P2({D.PsSub.lt(D.Tmp.cells(List.append(&2, D.TmpE, D.Ag.cells(e, m2, env), D.Ag.cells(ys, m2, args))),
      List.append(&2, U32, ps, D.Tmp.cells(D.Ag.cells(xs, m, a))), m, nx) == True{} : Bool},
  D.P2(N.Le(Nat.add(D.Acc.need(m2, nx2, fi, os,
      List.append(&2, D.TmpE, D.Ag.cells(e, m2, env), List.append(&2, D.TmpE, D.Ag.cells(ys, m2, args), xs0)), sp, fs), Nat.mul(2n, Pg.Term.size(s))),
    Nat.add(D.Acc.need(m, nx, fi, os, List.append(&2, D.TmpE, D.Ag.cells(xs, m, a), xs0), sp, fs), Nat.mul(2n, Pg.Term.size(tt)))),
    D.P2(TS.le(List.append(&2, Bk.Term, D.Arg.terms(e), D.Arg.terms(ys)), 1n+D.Terms.size(D.Arg.terms(xs))),
      N.Le(Nat.sub(U32.to_nat(nx2), U32.to_nat(fi)),
        Nat.max(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), D.Walk.need(m, nx, fi, os, xs0, sp, fs, tt, a, xs))))))))))))

# a round's start
def WS(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +keep: List<&2, Nat>, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32,
  +ps: List<&2, U32>, +tc: U32, +tt: Bk.Term, +a: U32, +xs: List<&2, El.Arg>, +xs0: List<&2, D.TmpE>,
  +regs2: List<&2, U32>, +m2: Cr.Cir.Cells, +nx2: U32, +c: U32, +s: Bk.Term, +env: U32, +e: List<&2, El.Arg>, +args: U32,
  +ys: List<&2, El.Arg>, +pend2: U32, +ps2: List<&2, U32>) -> Data:
  D.P2(WR(regs, keep, regs2, c, env, List.length(&2, El.Arg, e), args, pend2),
  D.P2({List.get(&2, U32, regs2, 26n) == Some{0} : Maybe<&2, U32>},
  D.P2({El.Eval.walk(tt, Nil{}, xs) == El.Eval.walk(s, D.Arg.terms(e), ys) : Maybe<Maybe<Bk.Term>>},
  D.P2({D.Fl(m2, c, 1024) == True{} : Bool},
    WH(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, s, env, e, args, ys, pend2, ps2)))))

# the ghost state of a round's start
type WG is Data:
  WG{regs2: List<&2, U32>, m2: Cr.Cir.Cells, nx2: U32, pg2: U32, c: U32, s: Bk.Term, env: U32, e: List<&2, El.Arg>, args: U32, ys: List<&2, El.Arg>, pend2: U32, ps2: List<&2, U32>}

def WG.at(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +keep: List<&2, Nat>, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>,
  +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +tc: U32, +tt: Bk.Term, +a: U32, +xs: List<&2, El.Arg>, +xs0: List<&2, D.TmpE>,
  w: WG, t: Cr.Cir.State) -> Data:
  match w:
    case WG{+regs2, +m2, +nx2, +pg2, +c, +s, +env, +e, +args, +ys, +pend2, +ps2}:
      D.P2({t == X.X.st(regs2, m2, nx2, fi, im, pg2, lim, inp) : Cr.Cir.State},
        WS(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, s, env, e, args, ys, pend2, ps2))

# a round's end
def WJ(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +keep: List<&2, Nat>, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>,
  +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +tc: U32, +tt: Bk.Term, +a: U32, +xs: List<&2, El.Arg>, +xs0: List<&2, D.TmpE>,
  t: Cr.Cir.State) -> Type:
  Or(D.Ex(WG, w => WG.at(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, w, t)),
    D.WalkQ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, Con{D.Rt{tc, tt}, bs}, fs, sp, ps, tt, a, xs, xs0, t))

# HS keeps its terms without the first borrowed one
def hs.tail(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32,
  +fi: U32, +im: U32, +os: List<&2, D.Rt>, r: D.Rt, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32,
  +ps: List<&2, U32>, h: D.HS(ds, ks, img, m, nx, fi, im, os, Con{r, bs}, fs, sp, pend, ps)) ->
  D.HS(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps):
  match r:
    case D.Rt{+c, +u}:
      (ho, h1) = h
      (hb, h2) = h1
      (_, hb2) = hb
      (hh, h3) = h2
      (_, hh2) = hh
      (ho, (hb2, (hh2, h3)))

# the parts of WR, of WH and of HS that the rounds read
def wr.len(-regs: List<&2, U32>, -keep: List<&2, Nat>, -regs2: List<&2, U32>, -c: U32, -env: U32, -n: Nat, -args: U32, -pend2: U32,
  h: WR(regs, keep, regs2, c, env, n, args, pend2)) -> {List.length(&2, U32, regs2) == 63n : Nat}:
  (x, _) = h
  x

def wr.r19(-regs: List<&2, U32>, -keep: List<&2, Nat>, -regs2: List<&2, U32>, -c: U32, -env: U32, -n: Nat, -args: U32, -pend2: U32,
  h: WR(regs, keep, regs2, c, env, n, args, pend2)) -> {List.get(&2, U32, regs2, 19n) == Some{c} : Maybe<&2, U32>}:
  (_, h1) = h
  (_, h2) = h1
  (x, _) = h2
  x

def wr.r21(-regs: List<&2, U32>, -keep: List<&2, Nat>, -regs2: List<&2, U32>, -c: U32, -env: U32, -n: Nat, -args: U32, -pend2: U32,
  h: WR(regs, keep, regs2, c, env, n, args, pend2)) -> {List.get(&2, U32, regs2, 21n) == Some{args} : Maybe<&2, U32>}:
  (_, h1) = h
  (_, h2) = h1
  (_, h3) = h2
  (_, h4) = h3
  (x, _) = h4
  x

def hs.is(-ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -m: Cr.Cir.Cells, -nx: U32,
  -fi: U32, -im: U32, -os: List<&2, D.Rt>, -c: U32, -u: Bk.Term, -bs: List<&2, D.Rt>, -fs: List<&2, D.AF>, -sp: U32, -pend: U32,
  -ps: List<&2, U32>, h: D.HS(ds, ks, img, m, nx, fi, im, os, Con{D.Rt{c, u}, bs}, fs, sp, pend, ps)) ->
  D.Is(ds, m, im, fi, nx, ks, img, c, u):
  (_, h1) = h
  (hb, _) = h1
  (x, _) = hb
  x

def nd.cell(-ds: List<&2, Bk.Def>, -im: U32, -fi: U32, -nx: U32, -c: U32, -x: Cr.Cir.Cell, -t: Bk.Term, -tag: U32,
  h: D.Nd(ds, im, fi, nx, c, x, t, tag)) -> {Cr.Cir.is_cell(c, im, fi, nx) == True{} : Bool}:
  (y, _) = h
  y

def nd.tag(-ds: List<&2, Bk.Def>, -im: U32, -fi: U32, -nx: U32, -c: U32, -x: Cr.Cir.Cell, -t: Bk.Term, -tag: U32,
  h: D.Nd(ds, im, fi, nx, c, x, t, tag)) -> {D.TgW(Cr.Cir.Cell.get(0n, x)) == tag : U32}:
  (_, h1) = h
  (_, h2) = h1
  (y, _) = h2
  y

# the cell c of the subtree s that HS holds first: a cell, of s's tag
def hs.cell(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32,
  +fi: U32, +im: U32, +os: List<&2, D.Rt>, +c: U32, +u: Bk.Term, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32,
  +ps: List<&2, U32>, h: D.HS(ds, ks, img, m, nx, fi, im, os, Con{D.Rt{c, u}, bs}, fs, sp, pend, ps)) ->
  {Cr.Cir.is_cell(c, im, fi, nx) == True{} : Bool}:
  nd.cell(ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), u, D.A.tag(u),
    D.is.nd(ds, m, im, fi, nx, ks, img, c, u, hs.is(ds, ks, img, m, nx, fi, im, os, c, u, bs, fs, sp, pend, ps, h)))

def hs.tg(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32,
  +fi: U32, +im: U32, +os: List<&2, D.Rt>, +c: U32, +u: Bk.Term, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32,
  +ps: List<&2, U32>, h: D.HS(ds, ks, img, m, nx, fi, im, os, Con{D.Rt{c, u}, bs}, fs, sp, pend, ps)) ->
  {D.Tg(m, c) == D.A.tag(u) : U32}:
  nd.tag(ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), u, D.A.tag(u),
    D.is.nd(ds, m, im, fi, nx, ks, img, c, u, hs.is(ds, ks, img, m, nx, fi, im, os, c, u, bs, fs, sp, pend, ps, h)))

def wh.hs(-ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -m: Cr.Cir.Cells, -nx: U32,
  -fi: U32, -im: U32, -os: List<&2, D.Rt>, -bs: List<&2, D.Rt>, -fs: List<&2, D.AF>, -sp: U32, -ps: List<&2, U32>,
  -tc: U32, -tt: Bk.Term, -a: U32, -xs: List<&2, El.Arg>, -xs0: List<&2, D.TmpE>, -m2: Cr.Cir.Cells, -nx2: U32,
  -c: U32, -s: Bk.Term, -env: U32, -e: List<&2, El.Arg>, -args: U32, -ys: List<&2, El.Arg>, -pend2: U32,
  -ps2: List<&2, U32>, h: WH(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, s, env, e, args, ys, pend2, ps2)) ->
  D.HS(ds, ks, img, m2, nx2, fi, im, os, Con{D.Rt{c, s}, Con{D.Rt{tc, tt}, bs}}, fs, sp, pend2, ps2):
  (x, _) = h
  x

def wh.args(-ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -m: Cr.Cir.Cells, -nx: U32,
  -fi: U32, -im: U32, -os: List<&2, D.Rt>, -bs: List<&2, D.Rt>, -fs: List<&2, D.AF>, -sp: U32, -ps: List<&2, U32>,
  -tc: U32, -tt: Bk.Term, -a: U32, -xs: List<&2, El.Arg>, -xs0: List<&2, D.TmpE>, -m2: Cr.Cir.Cells, -nx2: U32,
  -c: U32, -s: Bk.Term, -env: U32, -e: List<&2, El.Arg>, -args: U32, -ys: List<&2, El.Arg>, -pend2: U32,
  -ps2: List<&2, U32>, h: WH(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, s, env, e, args, ys, pend2, ps2)) ->
  D.Ag(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, ys):
  (_, h1) = h
  (_, h2) = h1
  (x, _) = h2
  x

def wh.kc(-ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -m: Cr.Cir.Cells, -nx: U32,
  -fi: U32, -im: U32, -os: List<&2, D.Rt>, -bs: List<&2, D.Rt>, -fs: List<&2, D.AF>, -sp: U32, -ps: List<&2, U32>,
  -tc: U32, -tt: Bk.Term, -a: U32, -xs: List<&2, El.Arg>, -xs0: List<&2, D.TmpE>, -m2: Cr.Cir.Cells, -nx2: U32,
  -c: U32, -s: Bk.Term, -env: U32, -e: List<&2, El.Arg>, -args: U32, -ys: List<&2, El.Arg>, -pend2: U32,
  -ps2: List<&2, U32>, h: WH(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, s, env, e, args, ys, pend2, ps2)) ->
  D.Kept.cells(m, nx, fi, ps, D.Tmp.cells(D.Ag.cells(xs, m, a)), m2, nx2, ps2):
  (_, h1) = h
  (_, h2) = h1
  (_, h3) = h2
  (x, _) = h3
  x

def wh.st(-ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -m: Cr.Cir.Cells, -nx: U32,
  -fi: U32, -im: U32, -os: List<&2, D.Rt>, -bs: List<&2, D.Rt>, -fs: List<&2, D.AF>, -sp: U32, -ps: List<&2, U32>,
  -tc: U32, -tt: Bk.Term, -a: U32, -xs: List<&2, El.Arg>, -xs0: List<&2, D.TmpE>, -m2: Cr.Cir.Cells, -nx2: U32,
  -c: U32, -s: Bk.Term, -env: U32, -e: List<&2, El.Arg>, -args: U32, -ys: List<&2, El.Arg>, -pend2: U32,
  -ps2: List<&2, U32>, h: WH(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, s, env, e, args, ys, pend2, ps2)) ->
  N.Le(D.Stat(Nat.sub(U32.to_nat(nx2), U32.to_nat(fi)), m2, fi), D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi)):
  (_, h1) = h
  (_, h2) = h1
  (_, h3) = h2
  (_, h4) = h3
  (x, _) = h4
  x

def wh.mem(-ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -m: Cr.Cir.Cells, -nx: U32,
  -fi: U32, -im: U32, -os: List<&2, D.Rt>, -bs: List<&2, D.Rt>, -fs: List<&2, D.AF>, -sp: U32, -ps: List<&2, U32>,
  -tc: U32, -tt: Bk.Term, -a: U32, -xs: List<&2, El.Arg>, -xs0: List<&2, D.TmpE>, -m2: Cr.Cir.Cells, -nx2: U32,
  -c: U32, -s: Bk.Term, -env: U32, -e: List<&2, El.Arg>, -args: U32, -ys: List<&2, El.Arg>, -pend2: U32,
  -ps2: List<&2, U32>, h: WH(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, s, env, e, args, ys, pend2, ps2)) ->
  N.Le(Nat.sub(U32.to_nat(nx2), U32.to_nat(fi)),
    Nat.max(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), D.Walk.need(m, nx, fi, os, xs0, sp, fs, tt, a, xs))):
  (_, h1) = h
  (_, h2) = h1
  (_, h3) = h2
  (_, h4) = h3
  (_, h5) = h4
  (_, h6) = h5
  (_, h7) = h6
  (_, h8) = h7
  (_, x) = h8
  x

# a chain with an argument is no 0
def ag.nz(-ds: List<&2, Bk.Def>, -m: Cr.Cir.Cells, -im: U32, -fi: U32, -nx: U32, -ks: List<&2, List<&2, Word(8n)>>,
  -img: List<&2, Bk.Term>, -ps: List<&2, U32>, -os: List<&2, D.Rt>, -vs: List<&2, U32>, -a: U32, -q: Bk.Quan, -x: Bk.Term,
  -rest: List<&2, El.Arg>, h: D.Ag(ds, m, im, fi, nx, ks, img, ps, os, vs, a, Con{El.Arg{q, x}, rest})) ->
  {U32.is_eq(a, 0) == False{} : Bool}:
  (y, _) = h
  y

# the parts of WS that the rounds read
def ws.wr(-ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -regs: List<&2, U32>, -m: Cr.Cir.Cells,
  -nx: U32, -fi: U32, -im: U32, -keep: List<&2, Nat>, -os: List<&2, D.Rt>, -bs: List<&2, D.Rt>, -fs: List<&2, D.AF>, -sp: U32,
  -ps: List<&2, U32>, -tc: U32, -tt: Bk.Term, -a: U32, -xs: List<&2, El.Arg>, -xs0: List<&2, D.TmpE>,
  -regs2: List<&2, U32>, -m2: Cr.Cir.Cells, -nx2: U32, -c: U32, -s: Bk.Term, -env: U32, -e: List<&2, El.Arg>, -args: U32,
  -ys: List<&2, El.Arg>, -pend2: U32, -ps2: List<&2, U32>,
  w: WS(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, s, env, e, args, ys, pend2, ps2)) ->
  WR(regs, keep, regs2, c, env, List.length(&2, El.Arg, e), args, pend2):
  (x, _) = w
  x

def ws.r26(-ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -regs: List<&2, U32>, -m: Cr.Cir.Cells,
  -nx: U32, -fi: U32, -im: U32, -keep: List<&2, Nat>, -os: List<&2, D.Rt>, -bs: List<&2, D.Rt>, -fs: List<&2, D.AF>, -sp: U32,
  -ps: List<&2, U32>, -tc: U32, -tt: Bk.Term, -a: U32, -xs: List<&2, El.Arg>, -xs0: List<&2, D.TmpE>,
  -regs2: List<&2, U32>, -m2: Cr.Cir.Cells, -nx2: U32, -c: U32, -s: Bk.Term, -env: U32, -e: List<&2, El.Arg>, -args: U32,
  -ys: List<&2, El.Arg>, -pend2: U32, -ps2: List<&2, U32>,
  w: WS(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, s, env, e, args, ys, pend2, ps2)) ->
  {List.get(&2, U32, regs2, 26n) == Some{0} : Maybe<&2, U32>}:
  (_, w1) = w
  (x, _) = w1
  x

def ws.ev(-ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -regs: List<&2, U32>, -m: Cr.Cir.Cells,
  -nx: U32, -fi: U32, -im: U32, -keep: List<&2, Nat>, -os: List<&2, D.Rt>, -bs: List<&2, D.Rt>, -fs: List<&2, D.AF>, -sp: U32,
  -ps: List<&2, U32>, -tc: U32, -tt: Bk.Term, -a: U32, -xs: List<&2, El.Arg>, -xs0: List<&2, D.TmpE>,
  -regs2: List<&2, U32>, -m2: Cr.Cir.Cells, -nx2: U32, -c: U32, -s: Bk.Term, -env: U32, -e: List<&2, El.Arg>, -args: U32,
  -ys: List<&2, El.Arg>, -pend2: U32, -ps2: List<&2, U32>,
  w: WS(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, s, env, e, args, ys, pend2, ps2)) ->
  {El.Eval.walk(tt, Nil{}, xs) == El.Eval.walk(s, D.Arg.terms(e), ys) : Maybe<Maybe<Bk.Term>>}:
  (_, w1) = w
  (_, w2) = w1
  (x, _) = w2
  x

def ws.st(-ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -regs: List<&2, U32>, -m: Cr.Cir.Cells,
  -nx: U32, -fi: U32, -im: U32, -keep: List<&2, Nat>, -os: List<&2, D.Rt>, -bs: List<&2, D.Rt>, -fs: List<&2, D.AF>, -sp: U32,
  -ps: List<&2, U32>, -tc: U32, -tt: Bk.Term, -a: U32, -xs: List<&2, El.Arg>, -xs0: List<&2, D.TmpE>,
  -regs2: List<&2, U32>, -m2: Cr.Cir.Cells, -nx2: U32, -c: U32, -s: Bk.Term, -env: U32, -e: List<&2, El.Arg>, -args: U32,
  -ys: List<&2, El.Arg>, -pend2: U32, -ps2: List<&2, U32>,
  w: WS(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, s, env, e, args, ys, pend2, ps2)) ->
  {D.Fl(m2, c, 1024) == True{} : Bool}:
  (_, w1) = w
  (_, w2) = w1
  (_, w3) = w2
  (x, _) = w3
  x

def ws.wh(-ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -regs: List<&2, U32>, -m: Cr.Cir.Cells,
  -nx: U32, -fi: U32, -im: U32, -keep: List<&2, Nat>, -os: List<&2, D.Rt>, -bs: List<&2, D.Rt>, -fs: List<&2, D.AF>, -sp: U32,
  -ps: List<&2, U32>, -tc: U32, -tt: Bk.Term, -a: U32, -xs: List<&2, El.Arg>, -xs0: List<&2, D.TmpE>,
  -regs2: List<&2, U32>, -m2: Cr.Cir.Cells, -nx2: U32, -c: U32, -s: Bk.Term, -env: U32, -e: List<&2, El.Arg>, -args: U32,
  -ys: List<&2, El.Arg>, -pend2: U32, -ps2: List<&2, U32>,
  w: WS(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, s, env, e, args, ys, pend2, ps2)) ->
  WH(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, s, env, e, args, ys, pend2, ps2):
  (_, w1) = w
  (_, w2) = w1
  (_, w3) = w2
  (_, x) = w3
  x

def ws.hs(-ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -regs: List<&2, U32>, -m: Cr.Cir.Cells,
  -nx: U32, -fi: U32, -im: U32, -keep: List<&2, Nat>, -os: List<&2, D.Rt>, -bs: List<&2, D.Rt>, -fs: List<&2, D.AF>, -sp: U32,
  -ps: List<&2, U32>, -tc: U32, -tt: Bk.Term, -a: U32, -xs: List<&2, El.Arg>, -xs0: List<&2, D.TmpE>,
  -regs2: List<&2, U32>, -m2: Cr.Cir.Cells, -nx2: U32, -c: U32, -s: Bk.Term, -env: U32, -e: List<&2, El.Arg>, -args: U32,
  -ys: List<&2, El.Arg>, -pend2: U32, -ps2: List<&2, U32>,
  w: WS(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, s, env, e, args, ys, pend2, ps2)) ->
  D.HS(ds, ks, img, m2, nx2, fi, im, os, Con{D.Rt{c, s}, Con{D.Rt{tc, tt}, bs}}, fs, sp, pend2, ps2):
  (_, w1) = w
  (_, w2) = w1
  (_, w3) = w2
  (_, hh) = w3
  (x, _) = hh
  x

# a round that sets wres to res: WalkQ, from the walk's registers, what it
# keeps, its STATIC own cells, HS when res is not 3, and WalkR
def ex.q(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +keep: List<&2, Nat>, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>,
  +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +tc: U32, +tt: Bk.Term, +a: U32, +xs: List<&2, El.Arg>, +xs0: List<&2, D.TmpE>,
  +res: U32, +regs2: List<&2, U32>, +m2: Cr.Cir.Cells, +nx2: U32, +pg2: U32, +c: U32, +env: U32, +n: Nat, +args: U32,
  +pend2: U32, +ps2: List<&2, U32>, hw: WR(regs, keep, regs2, c, env, n, args, pend2),
  hk: {D.Disj(keep, D.Walk.scr()) == True{} : Bool},
  hkc: D.Kept.cells(m, nx, fi, ps, D.Tmp.cells(D.Ag.cells(xs, m, a)), m2, nx2, ps2),
  hst: N.Le(D.Stat(Nat.sub(U32.to_nat(nx2), U32.to_nat(fi)), m2, fi), D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi)),
  hmem: N.Le(Nat.sub(U32.to_nat(nx2), U32.to_nat(fi)),
    Nat.max(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), D.Walk.need(m, nx, fi, os, xs0, sp, fs, tt, a, xs))),
  hh: D.DataH(U32.is_ne(res, 3), D.HS(ds, ks, img, m2, nx2, fi, im, os, Con{D.Rt{tc, tt}, bs}, fs, sp, pend2, ps2)),
  hr: D.WalkR(ds, ks, img, m2, nx2, fi, im, ps2, os, sp, fs, xs0, tt, xs, res, c, env, U32.from_nat(n), args)) ->
  D.WalkQ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, Con{D.Rt{tc, tt}, bs}, fs, sp, ps, tt, a, xs, xs0,
    X.X.st(List.set(&2, U32, regs2, 26n, res), m2, nx2, fi, im, pg2, lim, inp)):
  (+hl, w1) = hw
  (hkp, w2) = w1
  (h19, w3) = w2
  (h20, w4) = w3
  (h21, w5) = w4
  (h25, h3) = w5
  (({==}, ({==}, ({==}, ({==}, ({==}, ({==}, (X.L.len(regs2, 26n, res, 63n, hl), kept.set(regs, regs2, keep, D.Walk.scr(), 26n, res, hk, {==}, hkp)))))))),
   (hst, (hmem, (res, (c, (env, (U32.from_nat(n), (args, (pend2, (ps2,
     (X.L.gs(regs2, 26n, res, X.L.lt(regs2, 26n, hl, {==})),
     (X.L.go(regs2, 26n, 19n, res, c, {==}, h19),
     (X.L.go(regs2, 26n, 20n, res, env, {==}, h20),
     (X.L.go(regs2, 26n, 25n, res, U32.from_nat(n), {==}, h25),
     (X.L.go(regs2, 26n, 21n, res, args, {==}, h21),
     (X.L.go(regs2, 26n, 3n, res, pend2, {==}, h3),
     (hkc, (hh, hr))))))))))))))))))

# wres 1, at the leaf s
def ex.one(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +keep: List<&2, Nat>, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>,
  +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +tc: U32, +tt: Bk.Term, +a: U32, +xs: List<&2, El.Arg>, +xs0: List<&2, D.TmpE>,
  +regs2: List<&2, U32>, +m2: Cr.Cir.Cells, +nx2: U32, +pg2: U32, +c: U32, +s: Bk.Term, +env: U32, +e: List<&2, El.Arg>, +args: U32,
  +ys: List<&2, El.Arg>, +pend2: U32, +ps2: List<&2, U32>,
  hw: WR(regs, keep, regs2, c, env, List.length(&2, El.Arg, e), args, pend2), hk: {D.Disj(keep, D.Walk.scr()) == True{} : Bool},
  hev: {El.Eval.walk(tt, Nil{}, xs) == Some{Some{El.Term.spine(ys, El.Term.subst(s, D.Arg.terms(e), 0n))}} : Maybe<Maybe<Bk.Term>>},
  hst: {D.Fl(m2, c, 1024) == True{} : Bool},
  hh: WH(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, s, env, e, args, ys, pend2, ps2)) ->
  D.WalkQ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, Con{D.Rt{tc, tt}, bs}, fs, sp, ps, tt, a, xs, xs0,
    X.X.st(List.set(&2, U32, regs2, 26n, 1), m2, nx2, fi, im, pg2, lim, inp)):
  (+hs, h1) = hh
  (hge, h2) = h1
  (hga, h3) = h2
  (hkc, h4) = h3
  (hst2, h5) = h4
  (hac, h6) = h5
  (_, h7) = h6
  (_, h8) = h7
  (_, hmem) = h8
  ex.q(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, 1, regs2, m2, nx2, pg2, c, env,
    List.length(&2, El.Arg, e), args, pend2, ps2, hw, hk, hkc, hst2, hmem,
    hs.tail(ds, ks, img, m2, nx2, fi, im, os, D.Rt{c, s}, Con{D.Rt{tc, tt}, bs}, fs, sp, pend2, ps2, hs),
    Inl{({==}, (s, (e, (ys, (hev, (hs.is(ds, ks, img, m2, nx2, fi, im, os, c, s, Con{D.Rt{tc, tt}, bs}, fs, sp, pend2, ps2, hs),
      (hst, ({==}, (hge, (hga, hac))))))))))})

# wres 2: the walk needs more arguments
def ex.two(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +keep: List<&2, Nat>, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>,
  +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +tc: U32, +tt: Bk.Term, +a: U32, +xs: List<&2, El.Arg>, +xs0: List<&2, D.TmpE>,
  +regs2: List<&2, U32>, +m2: Cr.Cir.Cells, +nx2: U32, +pg2: U32, +c: U32, +s: Bk.Term, +env: U32, +e: List<&2, El.Arg>, +args: U32,
  +ys: List<&2, El.Arg>, +pend2: U32, +ps2: List<&2, U32>,
  hw: WR(regs, keep, regs2, c, env, List.length(&2, El.Arg, e), args, pend2), hk: {D.Disj(keep, D.Walk.scr()) == True{} : Bool},
  hev: {El.Eval.walk(tt, Nil{}, xs) == Some{None{}} : Maybe<Maybe<Bk.Term>>},
  hh: WH(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, s, env, e, args, ys, pend2, ps2)) ->
  D.WalkQ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, Con{D.Rt{tc, tt}, bs}, fs, sp, ps, tt, a, xs, xs0,
    X.X.st(List.set(&2, U32, regs2, 26n, 2), m2, nx2, fi, im, pg2, lim, inp)):
  (hs, h1) = hh
  (hge, h2) = h1
  (hga, h3) = h2
  (hkc, h4) = h3
  (hst2, h5) = h4
  (hac, h6) = h5
  (_, h7) = h6
  (_, h8) = h7
  (_, hmem) = h8
  ex.q(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, 2, regs2, m2, nx2, pg2, c, env,
    List.length(&2, El.Arg, e), args, pend2, ps2, hw, hk, hkc, hst2, hmem,
    hs.tail(ds, ks, img, m2, nx2, fi, im, os, D.Rt{c, s}, Con{D.Rt{tc, tt}, bs}, fs, sp, pend2, ps2, hs),
    Inr{Inl{({==}, (hev, (e, (ys, (hge, (hga, hac))))))}})

# wres 3: no walk exists
def ex.three(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +keep: List<&2, Nat>, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>,
  +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +tc: U32, +tt: Bk.Term, +a: U32, +xs: List<&2, El.Arg>, +xs0: List<&2, D.TmpE>,
  +regs2: List<&2, U32>, +m2: Cr.Cir.Cells, +nx2: U32, +pg2: U32, +c: U32, +env: U32, +n: Nat, +args: U32, +pend2: U32,
  +ps2: List<&2, U32>, hw: WR(regs, keep, regs2, c, env, n, args, pend2), hk: {D.Disj(keep, D.Walk.scr()) == True{} : Bool},
  hev: {El.Eval.walk(tt, Nil{}, xs) == None{} : Maybe<Maybe<Bk.Term>>},
  hkc: D.Kept.cells(m, nx, fi, ps, D.Tmp.cells(D.Ag.cells(xs, m, a)), m2, nx2, ps2),
  hst: N.Le(D.Stat(Nat.sub(U32.to_nat(nx2), U32.to_nat(fi)), m2, fi), D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi)),
  hmem: N.Le(Nat.sub(U32.to_nat(nx2), U32.to_nat(fi)),
    Nat.max(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), D.Walk.need(m, nx, fi, os, xs0, sp, fs, tt, a, xs)))) ->
  D.WalkQ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, Con{D.Rt{tc, tt}, bs}, fs, sp, ps, tt, a, xs, xs0,
    X.X.st(List.set(&2, U32, regs2, 26n, 3), m2, nx2, fi, im, pg2, lim, inp)):
  ex.q(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, 3, regs2, m2, nx2, pg2, c, env,
    n, args, pend2, ps2, hw, hk, hkc, hst, hmem, Unit{}, Inr{Inr{({==}, hev)}})

# the loop's test, wres == 0, at a state whose wres is v
def lp.ob(+regs3: List<&2, U32>, +m3: Cr.Cir.Cells, +nx3: U32, +fi3: U32, +im3: U32, +pg3: U32, +lim3: U32,
  +inp3: List<&2, Word(8n)>, +out3: List<&2, Word(8n)>, +outn3: U32, +v: U32,
  h: {List.get(&2, U32, regs3, 26n) == Some{v} : Maybe<&2, U32>}) ->
  DW.Ob(Mc.M.eq(Mc.M.g(Mc.R.wres()), Mc.M.c(0)), Cr.Cir.State{regs3, m3, nx3, fi3, im3, pg3, lim3, inp3, out3, outn3}):
  (%Equal.sym(Maybe<&2, U32>, List.get(&2, U32, regs3, 26n), Some{v}, h) : DW.IsSome(_) & Unit; (Unit{}, Unit{}))

def lp.ev(+regs3: List<&2, U32>, +m3: Cr.Cir.Cells, +nx3: U32, +fi3: U32, +im3: U32, +pg3: U32, +lim3: U32,
  +inp3: List<&2, Word(8n)>, +out3: List<&2, Word(8n)>, +outn3: U32, +v: U32,
  h: {List.get(&2, U32, regs3, 26n) == Some{v} : Maybe<&2, U32>}) ->
  {DW.Ev(Mc.M.eq(Mc.M.g(Mc.R.wres()), Mc.M.c(0)), Cr.Cir.State{regs3, m3, nx3, fi3, im3, pg3, lim3, inp3, out3, outn3}) == Bool.to_u32(U32.is_eq(v, 0)) : U32}:
  (%Equal.sym(Maybe<&2, U32>, List.get(&2, U32, regs3, 26n), Some{v}, h) :
    {Bool.to_u32(U32.is_eq(Maybe.default(&2, U32, _, 0), 0)) == Bool.to_u32(U32.is_eq(v, 0)) : U32}; {==})

# WalkR's wres is 1, 2 or 3
def ex.ne0(-ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -m2: Cr.Cir.Cells, -nx2: U32,
  -fi: U32, -im: U32, -ps2: List<&2, U32>, -os: List<&2, D.Rt>, -sp: U32, -fs: List<&2, D.AF>, -xs0: List<&2, D.TmpE>, -tt: Bk.Term,
  -xs: List<&2, El.Arg>, +res: U32, -wt2: U32, -env: U32, -wn: U32, -args: U32,
  hr: D.WalkR(ds, ks, img, m2, nx2, fi, im, ps2, os, sp, fs, xs0, tt, xs, res, wt2, env, wn, args)) ->
  {U32.is_eq(res, 0) == False{} : Bool} & D.WalkR(ds, ks, img, m2, nx2, fi, im, ps2, os, sp, fs, xs0, tt, xs, res, wt2, env, wn, args):
  match hr:
    case Inl{x}:
      (+e1, x2) = x
      ((%Equal.sym(U32, res, 1, e1) : {U32.is_eq(_, 0) == False{} : Bool}; {==}), Inl{(e1, x2)})
    case Inr{y}:
      match y:
        case Inl{x}:
          (+e2, x2) = x
          ((%Equal.sym(U32, res, 2, e2) : {U32.is_eq(_, 0) == False{} : Bool}; {==}), Inr{Inl{(e2, x2)}})
        case Inr{x}:
          (+e3, x2) = x
          ((%Equal.sym(U32, res, 3, e3) : {U32.is_eq(_, 0) == False{} : Bool}; {==}), Inr{Inr{(e3, x2)}})

# the loop's statement
def W.while() -> Cr.Cir.Stmt:
  Cr.Cir.Stmt.while{Mc.M.eq(Mc.M.g(Mc.R.wres()), Mc.M.c(0)), W.body()}

# the loop's end, with the test's value
def W.end.k(+h: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +keep: List<&2, Nat>,
  +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +tc: U32, +tt: Bk.Term,
  +a: U32, +xs: List<&2, El.Arg>, +xs0: List<&2, D.TmpE>, +B: Nat,
  +regs3: List<&2, U32>, +m3: Cr.Cir.Cells, +nx3: U32, +fi3: U32, +im3: U32, +pg3: U32, +lim3: U32, +inp3: List<&2, Word(8n)>,
  +out3: List<&2, Word(8n)>, +outn3: U32, +res: U32, +wt2: U32, +env: U32, +wn: U32, +args: U32, +pend2: U32, +ps2: List<&2, U32>,
  sm: D.Same(regs, fi, im, lim, inp, keep, Cr.Cir.State{regs3, m3, nx3, fi3, im3, pg3, lim3, inp3, out3, outn3}),
  hst: N.Le(D.Stat(D.Mem.cells(Cr.Cir.State{regs3, m3, nx3, fi3, im3, pg3, lim3, inp3, out3, outn3}), D.St.cells(Cr.Cir.State{regs3, m3, nx3, fi3, im3, pg3, lim3, inp3, out3, outn3}),
    D.St.first(Cr.Cir.State{regs3, m3, nx3, fi3, im3, pg3, lim3, inp3, out3, outn3})), D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi)),
  hmem: N.Le(D.Mem.cells(Cr.Cir.State{regs3, m3, nx3, fi3, im3, pg3, lim3, inp3, out3, outn3}),
    Nat.max(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), D.Walk.need(m, nx, fi, os, xs0, sp, fs, tt, a, xs))),
  +h26: D.Reg(Cr.Cir.State{regs3, m3, nx3, fi3, im3, pg3, lim3, inp3, out3, outn3}, 26n, res), r19: D.Reg(Cr.Cir.State{regs3, m3, nx3, fi3, im3, pg3, lim3, inp3, out3, outn3}, 19n, wt2), r20: D.Reg(Cr.Cir.State{regs3, m3, nx3, fi3, im3, pg3, lim3, inp3, out3, outn3}, 20n, env),
  r25: D.Reg(Cr.Cir.State{regs3, m3, nx3, fi3, im3, pg3, lim3, inp3, out3, outn3}, 25n, wn), r21: D.Reg(Cr.Cir.State{regs3, m3, nx3, fi3, im3, pg3, lim3, inp3, out3, outn3}, 21n, args), r3: D.Reg(Cr.Cir.State{regs3, m3, nx3, fi3, im3, pg3, lim3, inp3, out3, outn3}, 3n, pend2),
  kc: D.Kept.cells(m, nx, fi, ps, D.Tmp.cells(D.Ag.cells(xs, m, a)), m3, nx3, ps2),
  dh: D.DataH(U32.is_ne(res, 3), D.HS(ds, ks, img, m3, nx3, fi, im, os, Con{D.Rt{tc, tt}, bs}, fs, sp, pend2, ps2)),
  p: {U32.is_eq(res, 0) == False{} : Bool} & D.WalkR(ds, ks, img, m3, nx3, fi, im, ps2, os, sp, fs, xs0, tt, xs, res, wt2, env, wn, args)) ->
  DW.WP(W.while(), 1n+h, Cr.Cir.State{regs3, m3, nx3, fi3, im3, pg3, lim3, inp3, out3, outn3}, st2 => D.WalkQ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, Con{D.Rt{tc, tt}, bs}, fs, sp, ps, tt, a, xs, xs0, st2), B, lim):
  (hz, hr) = p
  (lp.ob(regs3, m3, nx3, fi3, im3, pg3, lim3, inp3, out3, outn3, res, h26),
   (%Equal.sym(U32, DW.Ev(Mc.M.eq(Mc.M.g(Mc.R.wres()), Mc.M.c(0)), Cr.Cir.State{regs3, m3, nx3, fi3, im3, pg3, lim3, inp3, out3, outn3}), Bool.to_u32(U32.is_eq(res, 0)),
       lp.ev(regs3, m3, nx3, fi3, im3, pg3, lim3, inp3, out3, outn3, res, h26)) :
      DW.WhQ(U32.is_zero(_), k => DW.WP(W.body(), h, Cr.Cir.State{regs3, m3, nx3, fi3, im3, pg3, lim3, inp3, out3, outn3}, u => DW.WP(W.while(), h, u, x => k(x), B, lim), B, lim), st2 => D.WalkQ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, Con{D.Rt{tc, tt}, bs}, fs, sp, ps, tt, a, xs, xs0, st2), Cr.Cir.State{regs3, m3, nx3, fi3, im3, pg3, lim3, inp3, out3, outn3});
    %Equal.sym(Bool, U32.is_eq(res, 0), False{}, hz) :
      DW.WhQ(U32.is_zero(Bool.to_u32(_)), k => DW.WP(W.body(), h, Cr.Cir.State{regs3, m3, nx3, fi3, im3, pg3, lim3, inp3, out3, outn3}, u => DW.WP(W.while(), h, u, x => k(x), B, lim), B, lim), st2 => D.WalkQ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, Con{D.Rt{tc, tt}, bs}, fs, sp, ps, tt, a, xs, xs0, st2), Cr.Cir.State{regs3, m3, nx3, fi3, im3, pg3, lim3, inp3, out3, outn3});
    (sm, (hst, (hmem, (res, (wt2, (env, (wn, (args, (pend2, (ps2, (h26, (r19, (r20, (r25, (r21, (r3, (kc, (dh, hr))))))))))))))))))))


# the loop ends at a state of WalkQ, whose wres is not 0
def W.end(+h: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +keep: List<&2, Nat>,
  +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +tc: U32, +tt: Bk.Term,
  +a: U32, +xs: List<&2, El.Arg>, +xs0: List<&2, D.TmpE>, +B: Nat, t: Cr.Cir.State,
  q: D.WalkQ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, Con{D.Rt{tc, tt}, bs}, fs, sp, ps, tt, a, xs, xs0, t)) ->
  DW.WP(W.while(), 1n+h, t, st2 => D.WalkQ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, Con{D.Rt{tc, tt}, bs}, fs, sp, ps, tt, a, xs, xs0, st2), B, lim):
  match t:
    case Cr.Cir.State{+regs3, +m3, +nx3, +fi3, +im3, +pg3, +lim3, +inp3, +out3, +outn3}:
      (sm, q0) = q
      (hst, q1) = q0
      (hmem, q2) = q1
      (+res, q3) = q2
      (+wt2, q4) = q3
      (+env, q5) = q4
      (+wn, q6) = q5
      (+args, q7) = q6
      (+pend2, q8) = q7
      (+ps2, q9) = q8
      (+h26, q10) = q9
      (r19, q11) = q10
      (r20, q12) = q11
      (r25, q13) = q12
      (r21, q14) = q13
      (r3, q15) = q14
      (kc, q16) = q15
      (dh, hr) = q16
      W.end.k(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, regs3, m3, nx3, fi3, im3, pg3, lim3, inp3, out3, outn3, res, wt2, env, wn, args, pend2, ps2,
        sm, hst, hmem, h26, r19, r20, r25, r21, r3, kc, dh, ex.ne0(ds, ks, img, m3, nx3, fi, im, ps2, os, sp, fs, xs0, tt, xs, res, wt2, env, wn, args, hr))

# a set of a register below 63 to v, whatever the value's expression
def wp.set.v(+r: Nat, +v: U32, +regs1: List<&2, U32>, +m1: Cr.Cir.Cells, +nx1: U32, +fi: U32, +im: U32, +pg1: U32, +lim: U32,
  +inp: List<&2, Word(8n)>, -K: Cr.Cir.State -> Type, hl: {List.length(&2, U32, regs1) == 63n : Nat},
  hr: {Nat.is_lt(r, 63n) == True{} : Bool}, k: K(X.X.st(List.set(&2, U32, regs1, r, v), m1, nx1, fi, im, pg1, lim, inp))) ->
  DW.WP.set(r, v, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), K):
  ((%Equal.sym(Nat, List.length(&2, U32, regs1), 63n, hl) : DW.Tr(Nat.is_lt(r, _)); (%Equal.sym(Bool, Nat.is_lt(r, 63n), True{}, hr) : DW.Tr(_); Unit{})), k)

# Efq's set of wres, by wargs: 2 when it is 0, else 3
def efq.val(+st: Cr.Cir.State, +x: U32, h: {Cr.Cir.eval(Mc.M.g(Mc.R.wargs()), st) == Some{x} : Maybe<&2, U32>}) ->
  {Cr.Cir.eval(Mc.M.pick(Mc.M.eq(Mc.M.g(Mc.R.wargs()), Mc.M.c(0)), Mc.M.c(2), Mc.M.c(3)), st) ==
    Some{U32.or(U32.and(2, U32.sub(0, Bool.to_u32(U32.is_eq(x, 0)))), U32.and(3, U32.sub(Bool.to_u32(U32.is_eq(x, 0)), 1)))} : Maybe<&2, U32>}:
  +b = Bool.to_u32(U32.is_eq(x, 0))
  +ce = Mc.M.eq(Mc.M.g(Mc.R.wargs()), Mc.M.c(0))
  +he = X.ev.op(Wa.Wasm.Op.eq{}, Mc.M.g(Mc.R.wargs()), Mc.M.c(0), st, x, 0, h, {==})
  X.ev.op(Wa.Wasm.Op.or{}, Mc.M.and(Mc.M.c(2), Mc.M.sub(Mc.M.c(0), ce)), Mc.M.and(Mc.M.c(3), Mc.M.sub(ce, Mc.M.c(1))), st,
    U32.and(2, U32.sub(0, b)), U32.and(3, U32.sub(b, 1)),
    X.ev.op(Wa.Wasm.Op.and{}, Mc.M.c(2), Mc.M.sub(Mc.M.c(0), ce), st, 2, U32.sub(0, b), {==},
      X.ev.op(Wa.Wasm.Op.sub{}, Mc.M.c(0), ce, st, 0, b, {==}, he)),
    X.ev.op(Wa.Wasm.Op.and{}, Mc.M.c(3), Mc.M.sub(ce, Mc.M.c(1)), st, 3, U32.sub(b, 1), {==},
      X.ev.op(Wa.Wasm.Op.sub{}, ce, Mc.M.c(1), st, b, 1, he, {==})))

def wp.set.p(+r: Nat, +e: Cr.Cir.Expr, +v: U32, +regs1: List<&2, U32>, +m1: Cr.Cir.Cells, +nx1: U32, +fi: U32, +im: U32, +pg1: U32,
  +lim: U32, +inp: List<&2, Word(8n)>, -K: Cr.Cir.State -> Type,
  p: DW.Ob(e, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp)) & {DW.Ev(e, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp)) == v : U32},
  w: DW.WP.set(r, v, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), K)) ->
  DW.Ob(e, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp)) &
    DW.WP.set(r, DW.Ev(e, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp)), X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), K):
  (oe, ve) = p
  (oe, (%Equal.sym(U32, DW.Ev(e, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp)), v, ve) :
    DW.WP.set(r, _, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), K); w))

# a set of r to the value v of e
def wp.set.e(+r: Nat, +e: Cr.Cir.Expr, +v: U32, +regs1: List<&2, U32>, +m1: Cr.Cir.Cells, +nx1: U32, +fi: U32, +im: U32, +pg1: U32,
  +lim: U32, +inp: List<&2, Word(8n)>, +g: Nat, -K: Cr.Cir.State -> Type, +B: Nat,
  he: {Cr.Cir.eval(e, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp)) == Some{v} : Maybe<&2, U32>},
  hl: {List.length(&2, U32, regs1) == 63n : Nat}, hr: {Nat.is_lt(r, 63n) == True{} : Bool},
  k: K(X.X.st(List.set(&2, U32, regs1, r, v), m1, nx1, fi, im, pg1, lim, inp))) ->
  DW.WP(Cr.Cir.Stmt.set{r, e}, g, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), K, B, lim):
  wp.set.p(r, e, v, regs1, m1, nx1, fi, im, pg1, lim, inp, K, ob.of(e, X.X.st(regs1, m1, nx1, fi, im, pg1, lim, inp), v, he),
    wp.set.v(r, v, regs1, m1, nx1, fi, im, pg1, lim, inp, K, hl, hr, k))

# the round of Efq: wres 2 when there is no argument, else 3
def round.efq(+h: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +keep: List<&2, Nat>,
  +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +tc: U32, +tt: Bk.Term,
  +a: U32, +xs: List<&2, El.Arg>, +xs0: List<&2, D.TmpE>, +B: Nat, +hk: {D.Disj(keep, D.Walk.scr()) == True{} : Bool},
  +regs2: List<&2, U32>, +m2: Cr.Cir.Cells, +nx2: U32, +pg2: U32, +c: U32, +env: U32, +e: List<&2, El.Arg>,
  +args: U32, +ys: List<&2, El.Arg>, +pend2: U32, +ps2: List<&2, U32>,
  +w: WS(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Efq{}, env, e, args, ys, pend2, ps2)) ->
  DW.WP(Mc.M.set(Mc.R.wres(), Mc.M.pick(Mc.M.eq(Mc.M.g(Mc.R.wargs()), Mc.M.c(0)), Mc.M.c(2), Mc.M.c(3))), h,
    X.X.st(regs2, m2, nx2, fi, im, pg2, lim, inp),
    u => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, u), B, lim):
  match ys:
    case Nil{}:
      wp.set.e(26n, Mc.M.pick(Mc.M.eq(Mc.M.g(Mc.R.wargs()), Mc.M.c(0)), Mc.M.c(2), Mc.M.c(3)), 2, regs2, m2, nx2, fi, im, pg2, lim, inp, h, u => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, u), B,
        (%wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Efq{}, env, e, args, Nil{}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Efq{}, env, e, args, Nil{}, pend2, ps2, w)) :
          {Cr.Cir.eval(Mc.M.pick(Mc.M.eq(Mc.M.g(Mc.R.wargs()), Mc.M.c(0)), Mc.M.c(2), Mc.M.c(3)), X.X.st(regs2, m2, nx2, fi, im, pg2, lim, inp)) == Some{U32.or(U32.and(2, U32.sub(0, Bool.to_u32(U32.is_eq(_, 0)))), U32.and(3, U32.sub(Bool.to_u32(U32.is_eq(_, 0)), 1)))} : Maybe<&2, U32>};
         efq.val(X.X.st(regs2, m2, nx2, fi, im, pg2, lim, inp), args, wr.r21(regs, keep, regs2, c, env, List.length(&2, El.Arg, e), args, pend2, ws.wr(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Efq{}, env, e, args, Nil{}, pend2, ps2, w)))),
        wr.len(regs, keep, regs2, c, env, List.length(&2, El.Arg, e), args, pend2, ws.wr(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Efq{}, env, e, args, Nil{}, pend2, ps2, w)), {==},
        Inr{ex.two(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, pg2, c, Bk.Term.Efq{}, env, e, args, Nil{}, pend2, ps2,
          ws.wr(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Efq{}, env, e, args, Nil{}, pend2, ps2, w), hk, ws.ev(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Efq{}, env, e, args, Nil{}, pend2, ps2, w), ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Efq{}, env, e, args, Nil{}, pend2, ps2, w))})
    case Con{El.Arg{+q0, +x0}, +rest}:
      wp.set.e(26n, Mc.M.pick(Mc.M.eq(Mc.M.g(Mc.R.wargs()), Mc.M.c(0)), Mc.M.c(2), Mc.M.c(3)), 3, regs2, m2, nx2, fi, im, pg2, lim, inp, h, u => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, u), B,
        (%ag.nz(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, x0, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Efq{}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Efq{}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, w))) :
          {Cr.Cir.eval(Mc.M.pick(Mc.M.eq(Mc.M.g(Mc.R.wargs()), Mc.M.c(0)), Mc.M.c(2), Mc.M.c(3)), X.X.st(regs2, m2, nx2, fi, im, pg2, lim, inp)) == Some{U32.or(U32.and(2, U32.sub(0, Bool.to_u32(_))), U32.and(3, U32.sub(Bool.to_u32(_), 1)))} : Maybe<&2, U32>};
         efq.val(X.X.st(regs2, m2, nx2, fi, im, pg2, lim, inp), args, wr.r21(regs, keep, regs2, c, env, List.length(&2, El.Arg, e), args, pend2, ws.wr(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Efq{}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, w)))),
        wr.len(regs, keep, regs2, c, env, List.length(&2, El.Arg, e), args, pend2, ws.wr(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Efq{}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, w)), {==},
        Inr{ex.three(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, pg2, c, env, List.length(&2, El.Arg, e), args, pend2, ps2,
          ws.wr(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Efq{}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, w), hk, ws.ev(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Efq{}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, w), wh.kc(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Efq{}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Efq{}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, w)), wh.st(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Efq{}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Efq{}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, w)), wh.mem(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Efq{}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Efq{}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, w)))})

# a round at a leaf of none of the walk's kinds: wres 1
def round.leaf(+h: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +keep: List<&2, Nat>,
  +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +tc: U32, +tt: Bk.Term,
  +a: U32, +xs: List<&2, El.Arg>, +xs0: List<&2, D.TmpE>, +B: Nat, +hk: {D.Disj(keep, D.Walk.scr()) == True{} : Bool},
  +regs2: List<&2, U32>, +m2: Cr.Cir.Cells, +nx2: U32, +pg2: U32, +c: U32, +s: Bk.Term, +env: U32, +e: List<&2, El.Arg>,
  +args: U32, +ys: List<&2, El.Arg>, +pend2: U32, +ps2: List<&2, U32>,
  +w: WS(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, s, env, e, args, ys, pend2, ps2),
  h7: {U32.is_eq(D.A.tag(s), Mc.T.lam()) == False{} : Bool}, h11: {U32.is_eq(D.A.tag(s), Mc.T.prj()) == False{} : Bool},
  h14: {U32.is_eq(D.A.tag(s), Mc.T.mat()) == False{} : Bool}, h8: {U32.is_eq(D.A.tag(s), Mc.T.app()) == False{} : Bool},
  h15: {U32.is_eq(D.A.tag(s), Mc.T.efq()) == False{} : Bool},
  hlf: {El.Eval.walk(s, D.Arg.terms(e), ys) == Some{Some{El.Term.spine(ys, El.Term.subst(s, D.Arg.terms(e), 0n))}} : Maybe<Maybe<Bk.Term>>}) ->
  DW.WP(W.body(), h, X.X.st(regs2, m2, nx2, fi, im, pg2, lim, inp),
    u => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, u), B, lim):
  disp.other(h, regs2, m2, nx2, fi, im, pg2, lim, inp, u => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, u), B, c, D.A.tag(s),
    wr.r19(regs, keep, regs2, c, env, List.length(&2, El.Arg, e), args, pend2, ws.wr(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, s, env, e, args, ys, pend2, ps2, w)), hs.cell(ds, ks, img, m2, nx2, fi, im, os, c, s, Con{D.Rt{tc, tt}, bs}, fs, sp, pend2, ps2, ws.hs(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, s, env, e, args, ys, pend2, ps2, w)),
    hs.tg(ds, ks, img, m2, nx2, fi, im, os, c, s, Con{D.Rt{tc, tt}, bs}, fs, sp, pend2, ps2, ws.hs(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, s, env, e, args, ys, pend2, ps2, w)), h7, h11, h14, h8, h15, wr.len(regs, keep, regs2, c, env, List.length(&2, El.Arg, e), args, pend2, ws.wr(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, s, env, e, args, ys, pend2, ps2, w)),
    Inr{ex.one(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, pg2, c, s, env, e, args, ys, pend2, ps2, ws.wr(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, s, env, e, args, ys, pend2, ps2, w), hk,
      Equal.trans(Maybe<Maybe<Bk.Term>>, El.Eval.walk(tt, Nil{}, xs), El.Eval.walk(s, D.Arg.terms(e), ys),
        Some{Some{El.Term.spine(ys, El.Term.subst(s, D.Arg.terms(e), 0n))}}, ws.ev(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, s, env, e, args, ys, pend2, ps2, w), hlf),
      ws.st(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, s, env, e, args, ys, pend2, ps2, w), ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, s, env, e, args, ys, pend2, ps2, w))})

# Tests
# -----
#
# A test of the walk's code is a Bool b (as Bool.to_u32): an if takes its
# then when b holds, else its else (an else that is no alloc).

def t.and(a: Bool, b: Bool) -> {U32.and(Bool.to_u32(a), Bool.to_u32(b)) == Bool.to_u32(Bool.and(a, b)) : U32}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def ne.quan(q: Bk.Quan) -> {U32.is_ne(Mc.Img.quan(q), 0) == El.Quan.live(q) : Bool}:
  match q:
    case Bk.Quan.Q0{}:
      {==}
    case Bk.Quan.Q1{}:
      {==}
    case Bk.Quan.Q2{}:
      {==}

# an if whose test is b, when b is True: the then
def wp.if.bt.p(+e: Cr.Cir.Stmt, +F: Nat, +c: Cr.Cir.Expr, +t: Cr.Cir.Stmt, +st: Cr.Cir.State, -K: Cr.Cir.State -> Type, +B: Nat,
  +lim: U32, +b: Bool, hea: {is.alloc(e) == False{} : Bool}, p: DW.Ob(c, st) & {DW.Ev(c, st) == Bool.to_u32(b) : U32},
  hb: {b == True{} : Bool}, k: DW.WP(t, F, st, x => K(x), B, lim)) ->
  DW.WP(Cr.Cir.Stmt.if{c, t, e}, F, st, K, B, lim):
  match e:
    case Cr.Cir.Stmt.alloc{+r}:
      DW.ft(DW.WP(Cr.Cir.Stmt.if{c, t, Cr.Cir.Stmt.alloc{r}}, F, st, K, B, lim), hea)
    case Cr.Cir.Stmt.nop{}:
      (oc, ve) = p
      (oc, (%Equal.sym(U32, DW.Ev(c, st), Bool.to_u32(b), ve) : DW.IfQ(U32.is_zero(_), q => DW.WP(t, F, st, x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.nop{}, F, st, x => q(x), B, lim), K);
        %Equal.sym(Bool, b, True{}, hb) : DW.IfQ(U32.is_zero(Bool.to_u32(_)), q => DW.WP(t, F, st, x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.nop{}, F, st, x => q(x), B, lim), K);
        k))
    case Cr.Cir.Stmt.set{+r2, +e2}:
      (oc, ve) = p
      (oc, (%Equal.sym(U32, DW.Ev(c, st), Bool.to_u32(b), ve) : DW.IfQ(U32.is_zero(_), q => DW.WP(t, F, st, x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.set{r2, e2}, F, st, x => q(x), B, lim), K);
        %Equal.sym(Bool, b, True{}, hb) : DW.IfQ(U32.is_zero(Bool.to_u32(_)), q => DW.WP(t, F, st, x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.set{r2, e2}, F, st, x => q(x), B, lim), K);
        k))
    case Cr.Cir.Stmt.store{+k2, +c2, +v2}:
      (oc, ve) = p
      (oc, (%Equal.sym(U32, DW.Ev(c, st), Bool.to_u32(b), ve) : DW.IfQ(U32.is_zero(_), q => DW.WP(t, F, st, x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.store{k2, c2, v2}, F, st, x => q(x), B, lim), K);
        %Equal.sym(Bool, b, True{}, hb) : DW.IfQ(U32.is_zero(Bool.to_u32(_)), q => DW.WP(t, F, st, x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.store{k2, c2, v2}, F, st, x => q(x), B, lim), K);
        k))
    case Cr.Cir.Stmt.emit{+v2}:
      (oc, ve) = p
      (oc, (%Equal.sym(U32, DW.Ev(c, st), Bool.to_u32(b), ve) : DW.IfQ(U32.is_zero(_), q => DW.WP(t, F, st, x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.emit{v2}, F, st, x => q(x), B, lim), K);
        %Equal.sym(Bool, b, True{}, hb) : DW.IfQ(U32.is_zero(Bool.to_u32(_)), q => DW.WP(t, F, st, x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.emit{v2}, F, st, x => q(x), B, lim), K);
        k))
    case Cr.Cir.Stmt.seq{+a2, +b2}:
      (oc, ve) = p
      (oc, (%Equal.sym(U32, DW.Ev(c, st), Bool.to_u32(b), ve) : DW.IfQ(U32.is_zero(_), q => DW.WP(t, F, st, x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.seq{a2, b2}, F, st, x => q(x), B, lim), K);
        %Equal.sym(Bool, b, True{}, hb) : DW.IfQ(U32.is_zero(Bool.to_u32(_)), q => DW.WP(t, F, st, x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.seq{a2, b2}, F, st, x => q(x), B, lim), K);
        k))
    case Cr.Cir.Stmt.if{+c2, +t2, +e2}:
      (oc, ve) = p
      (oc, (%Equal.sym(U32, DW.Ev(c, st), Bool.to_u32(b), ve) : DW.IfQ(U32.is_zero(_), q => DW.WP(t, F, st, x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.if{c2, t2, e2}, F, st, x => q(x), B, lim), K);
        %Equal.sym(Bool, b, True{}, hb) : DW.IfQ(U32.is_zero(Bool.to_u32(_)), q => DW.WP(t, F, st, x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.if{c2, t2, e2}, F, st, x => q(x), B, lim), K);
        k))
    case Cr.Cir.Stmt.while{+c2, +b2}:
      (oc, ve) = p
      (oc, (%Equal.sym(U32, DW.Ev(c, st), Bool.to_u32(b), ve) : DW.IfQ(U32.is_zero(_), q => DW.WP(t, F, st, x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.while{c2, b2}, F, st, x => q(x), B, lim), K);
        %Equal.sym(Bool, b, True{}, hb) : DW.IfQ(U32.is_zero(Bool.to_u32(_)), q => DW.WP(t, F, st, x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.while{c2, b2}, F, st, x => q(x), B, lim), K);
        k))
    case Cr.Cir.Stmt.halt{+s2}:
      (oc, ve) = p
      (oc, (%Equal.sym(U32, DW.Ev(c, st), Bool.to_u32(b), ve) : DW.IfQ(U32.is_zero(_), q => DW.WP(t, F, st, x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.halt{s2}, F, st, x => q(x), B, lim), K);
        %Equal.sym(Bool, b, True{}, hb) : DW.IfQ(U32.is_zero(Bool.to_u32(_)), q => DW.WP(t, F, st, x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.halt{s2}, F, st, x => q(x), B, lim), K);
        k))

def wp.if.bt(+e: Cr.Cir.Stmt, +F: Nat, +c: Cr.Cir.Expr, +t: Cr.Cir.Stmt, +st: Cr.Cir.State, -K: Cr.Cir.State -> Type, +B: Nat,
  +lim: U32, +b: Bool, hea: {is.alloc(e) == False{} : Bool}, hc: {Cr.Cir.eval(c, st) == Some{Bool.to_u32(b)} : Maybe<&2, U32>},
  hb: {b == True{} : Bool}, k: DW.WP(t, F, st, x => K(x), B, lim)) ->
  DW.WP(Cr.Cir.Stmt.if{c, t, e}, F, st, K, B, lim):
  wp.if.bt.p(e, F, c, t, st, K, B, lim, b, hea, ob.of(c, st, Bool.to_u32(b), hc), hb, k)

# an if whose test is b, when b is False: the else
def wp.if.be.p(+e: Cr.Cir.Stmt, +F: Nat, +c: Cr.Cir.Expr, +t: Cr.Cir.Stmt, +st: Cr.Cir.State, -K: Cr.Cir.State -> Type, +B: Nat,
  +lim: U32, +b: Bool, hea: {is.alloc(e) == False{} : Bool}, p: DW.Ob(c, st) & {DW.Ev(c, st) == Bool.to_u32(b) : U32},
  hb: {b == False{} : Bool}, k: DW.WP(e, F, st, x => K(x), B, lim)) ->
  DW.WP(Cr.Cir.Stmt.if{c, t, e}, F, st, K, B, lim):
  match e:
    case Cr.Cir.Stmt.alloc{+r}:
      DW.ft(DW.WP(Cr.Cir.Stmt.if{c, t, Cr.Cir.Stmt.alloc{r}}, F, st, K, B, lim), hea)
    case Cr.Cir.Stmt.nop{}:
      (oc, ve) = p
      (oc, (%Equal.sym(U32, DW.Ev(c, st), Bool.to_u32(b), ve) : DW.IfQ(U32.is_zero(_), q => DW.WP(t, F, st, x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.nop{}, F, st, x => q(x), B, lim), K);
        %Equal.sym(Bool, b, False{}, hb) : DW.IfQ(U32.is_zero(Bool.to_u32(_)), q => DW.WP(t, F, st, x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.nop{}, F, st, x => q(x), B, lim), K);
        k))
    case Cr.Cir.Stmt.set{+r2, +e2}:
      (oc, ve) = p
      (oc, (%Equal.sym(U32, DW.Ev(c, st), Bool.to_u32(b), ve) : DW.IfQ(U32.is_zero(_), q => DW.WP(t, F, st, x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.set{r2, e2}, F, st, x => q(x), B, lim), K);
        %Equal.sym(Bool, b, False{}, hb) : DW.IfQ(U32.is_zero(Bool.to_u32(_)), q => DW.WP(t, F, st, x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.set{r2, e2}, F, st, x => q(x), B, lim), K);
        k))
    case Cr.Cir.Stmt.store{+k2, +c2, +v2}:
      (oc, ve) = p
      (oc, (%Equal.sym(U32, DW.Ev(c, st), Bool.to_u32(b), ve) : DW.IfQ(U32.is_zero(_), q => DW.WP(t, F, st, x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.store{k2, c2, v2}, F, st, x => q(x), B, lim), K);
        %Equal.sym(Bool, b, False{}, hb) : DW.IfQ(U32.is_zero(Bool.to_u32(_)), q => DW.WP(t, F, st, x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.store{k2, c2, v2}, F, st, x => q(x), B, lim), K);
        k))
    case Cr.Cir.Stmt.emit{+v2}:
      (oc, ve) = p
      (oc, (%Equal.sym(U32, DW.Ev(c, st), Bool.to_u32(b), ve) : DW.IfQ(U32.is_zero(_), q => DW.WP(t, F, st, x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.emit{v2}, F, st, x => q(x), B, lim), K);
        %Equal.sym(Bool, b, False{}, hb) : DW.IfQ(U32.is_zero(Bool.to_u32(_)), q => DW.WP(t, F, st, x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.emit{v2}, F, st, x => q(x), B, lim), K);
        k))
    case Cr.Cir.Stmt.seq{+a2, +b2}:
      (oc, ve) = p
      (oc, (%Equal.sym(U32, DW.Ev(c, st), Bool.to_u32(b), ve) : DW.IfQ(U32.is_zero(_), q => DW.WP(t, F, st, x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.seq{a2, b2}, F, st, x => q(x), B, lim), K);
        %Equal.sym(Bool, b, False{}, hb) : DW.IfQ(U32.is_zero(Bool.to_u32(_)), q => DW.WP(t, F, st, x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.seq{a2, b2}, F, st, x => q(x), B, lim), K);
        k))
    case Cr.Cir.Stmt.if{+c2, +t2, +e2}:
      (oc, ve) = p
      (oc, (%Equal.sym(U32, DW.Ev(c, st), Bool.to_u32(b), ve) : DW.IfQ(U32.is_zero(_), q => DW.WP(t, F, st, x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.if{c2, t2, e2}, F, st, x => q(x), B, lim), K);
        %Equal.sym(Bool, b, False{}, hb) : DW.IfQ(U32.is_zero(Bool.to_u32(_)), q => DW.WP(t, F, st, x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.if{c2, t2, e2}, F, st, x => q(x), B, lim), K);
        k))
    case Cr.Cir.Stmt.while{+c2, +b2}:
      (oc, ve) = p
      (oc, (%Equal.sym(U32, DW.Ev(c, st), Bool.to_u32(b), ve) : DW.IfQ(U32.is_zero(_), q => DW.WP(t, F, st, x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.while{c2, b2}, F, st, x => q(x), B, lim), K);
        %Equal.sym(Bool, b, False{}, hb) : DW.IfQ(U32.is_zero(Bool.to_u32(_)), q => DW.WP(t, F, st, x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.while{c2, b2}, F, st, x => q(x), B, lim), K);
        k))
    case Cr.Cir.Stmt.halt{+s2}:
      (oc, ve) = p
      (oc, (%Equal.sym(U32, DW.Ev(c, st), Bool.to_u32(b), ve) : DW.IfQ(U32.is_zero(_), q => DW.WP(t, F, st, x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.halt{s2}, F, st, x => q(x), B, lim), K);
        %Equal.sym(Bool, b, False{}, hb) : DW.IfQ(U32.is_zero(Bool.to_u32(_)), q => DW.WP(t, F, st, x => q(x), B, lim), q => DW.WP(Cr.Cir.Stmt.halt{s2}, F, st, x => q(x), B, lim), K);
        k))

def wp.if.be(+e: Cr.Cir.Stmt, +F: Nat, +c: Cr.Cir.Expr, +t: Cr.Cir.Stmt, +st: Cr.Cir.State, -K: Cr.Cir.State -> Type, +B: Nat,
  +lim: U32, +b: Bool, hea: {is.alloc(e) == False{} : Bool}, hc: {Cr.Cir.eval(c, st) == Some{Bool.to_u32(b)} : Maybe<&2, U32>},
  hb: {b == False{} : Bool}, k: DW.WP(e, F, st, x => K(x), B, lim)) ->
  DW.WP(Cr.Cir.Stmt.if{c, t, e}, F, st, K, B, lim):
  wp.if.be.p(e, F, c, t, st, K, B, lim, b, hea, ob.of(c, st, Bool.to_u32(b), hc), hb, k)

# Scratch registers
# -----------------

# WR is kept by a set of a scratch register of the walk: one of Walk.scr(),
# none of wt, wenv, wargs, wn, pend
def wr.set(+r: Nat, +v: U32, +regs: List<&2, U32>, +keep: List<&2, Nat>, +regs2: List<&2, U32>, +c: U32, +env: U32, +n: Nat,
  +args: U32, +pend2: U32, +hk: {D.Disj(keep, D.Walk.scr()) == True{} : Bool}, hr: {D.Nat.mem(D.Walk.scr(), r) == True{} : Bool},
  h19: {Nat.is_eq(r, 19n) == False{} : Bool}, h20: {Nat.is_eq(r, 20n) == False{} : Bool}, h21: {Nat.is_eq(r, 21n) == False{} : Bool},
  h25: {Nat.is_eq(r, 25n) == False{} : Bool}, h3: {Nat.is_eq(r, 3n) == False{} : Bool},
  w: WR(regs, keep, regs2, c, env, n, args, pend2)) -> WR(regs, keep, List.set(&2, U32, regs2, r, v), c, env, n, args, pend2):
  (hl, w1) = w
  (hkp, w2) = w1
  (g19, w3) = w2
  (g20, w4) = w3
  (g21, w5) = w4
  (g25, g3) = w5
  (X.L.len(regs2, r, v, 63n, hl), (kept.set(regs, regs2, keep, D.Walk.scr(), r, v, hk, hr, hkp),
   (X.L.go(regs2, r, 19n, v, c, h19, g19), (X.L.go(regs2, r, 20n, v, env, h20, g20), (X.L.go(regs2, r, 21n, v, args, h21, g21),
   (X.L.go(regs2, r, 25n, v, U32.from_nat(n), h25, g25), X.L.go(regs2, r, 3n, v, pend2, h3, g3)))))))

# WS is kept by such a set that keeps wres too
def ws.set(+r: Nat, +v: U32, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +keep: List<&2, Nat>, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32,
  +ps: List<&2, U32>, +tc: U32, +tt: Bk.Term, +a: U32, +xs: List<&2, El.Arg>, +xs0: List<&2, D.TmpE>,
  +regs2: List<&2, U32>, +m2: Cr.Cir.Cells, +nx2: U32, +c: U32, +s: Bk.Term, +env: U32, +e: List<&2, El.Arg>, +args: U32,
  +ys: List<&2, El.Arg>, +pend2: U32, +ps2: List<&2, U32>, +hk: {D.Disj(keep, D.Walk.scr()) == True{} : Bool},
  hr: {D.Nat.mem(D.Walk.scr(), r) == True{} : Bool}, h19: {Nat.is_eq(r, 19n) == False{} : Bool}, h20: {Nat.is_eq(r, 20n) == False{} : Bool},
  h21: {Nat.is_eq(r, 21n) == False{} : Bool}, h25: {Nat.is_eq(r, 25n) == False{} : Bool}, h26: {Nat.is_eq(r, 26n) == False{} : Bool},
  h3: {Nat.is_eq(r, 3n) == False{} : Bool},
  w: WS(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, s, env, e, args, ys, pend2, ps2)) ->
  WS(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, regs2, r, v), m2, nx2, c, s, env, e, args, ys, pend2, ps2):
  (hw, w1) = w
  (g26, w2) = w1
  (wr.set(r, v, regs, keep, regs2, c, env, List.length(&2, El.Arg, e), args, pend2, hk, hr, h19, h20, h21, h25, h3, hw),
   (X.L.go(regs2, r, 26n, v, 0, h26, g26), w2))

# a round that goes on sets one of the walk's own registers (wt, wenv,
# wargs, wn), whose values WR reads: WR with the register's new value (WS is
# not kept: its other parts read them too)

def wr.s19(+v: U32, +regs: List<&2, U32>, +keep: List<&2, Nat>, +regs2: List<&2, U32>, +c: U32, +env: U32, +n: Nat,
  +args: U32, +pend2: U32, +hk: {D.Disj(keep, D.Walk.scr()) == True{} : Bool},
  w: WR(regs, keep, regs2, c, env, n, args, pend2)) ->
  WR(regs, keep, List.set(&2, U32, regs2, 19n, v), v, env, n, args, pend2):
  (+hl, w1) = w
  (hkp, w2) = w1
  (g19, w3) = w2
  (g20, w4) = w3
  (g21, w5) = w4
  (g25, g3) = w5
  (X.L.len(regs2, 19n, v, 63n, hl), (kept.set(regs, regs2, keep, D.Walk.scr(), 19n, v, hk, {==}, hkp),
   (X.L.gs(regs2, 19n, v, X.L.lt(regs2, 19n, hl, {==})), (X.L.go(regs2, 19n, 20n, v, env, {==}, g20),
   (X.L.go(regs2, 19n, 21n, v, args, {==}, g21), (X.L.go(regs2, 19n, 25n, v, U32.from_nat(n), {==}, g25),
    X.L.go(regs2, 19n, 3n, v, pend2, {==}, g3)))))))

def wr.s20(+v: U32, +regs: List<&2, U32>, +keep: List<&2, Nat>, +regs2: List<&2, U32>, +c: U32, +env: U32, +n: Nat,
  +args: U32, +pend2: U32, +hk: {D.Disj(keep, D.Walk.scr()) == True{} : Bool},
  w: WR(regs, keep, regs2, c, env, n, args, pend2)) ->
  WR(regs, keep, List.set(&2, U32, regs2, 20n, v), c, v, n, args, pend2):
  (+hl, w1) = w
  (hkp, w2) = w1
  (g19, w3) = w2
  (g20, w4) = w3
  (g21, w5) = w4
  (g25, g3) = w5
  (X.L.len(regs2, 20n, v, 63n, hl), (kept.set(regs, regs2, keep, D.Walk.scr(), 20n, v, hk, {==}, hkp),
   (X.L.go(regs2, 20n, 19n, v, c, {==}, g19), (X.L.gs(regs2, 20n, v, X.L.lt(regs2, 20n, hl, {==})),
   (X.L.go(regs2, 20n, 21n, v, args, {==}, g21), (X.L.go(regs2, 20n, 25n, v, U32.from_nat(n), {==}, g25),
    X.L.go(regs2, 20n, 3n, v, pend2, {==}, g3)))))))

def wr.s21(+v: U32, +regs: List<&2, U32>, +keep: List<&2, Nat>, +regs2: List<&2, U32>, +c: U32, +env: U32, +n: Nat,
  +args: U32, +pend2: U32, +hk: {D.Disj(keep, D.Walk.scr()) == True{} : Bool},
  w: WR(regs, keep, regs2, c, env, n, args, pend2)) ->
  WR(regs, keep, List.set(&2, U32, regs2, 21n, v), c, env, n, v, pend2):
  (+hl, w1) = w
  (hkp, w2) = w1
  (g19, w3) = w2
  (g20, w4) = w3
  (g21, w5) = w4
  (g25, g3) = w5
  (X.L.len(regs2, 21n, v, 63n, hl), (kept.set(regs, regs2, keep, D.Walk.scr(), 21n, v, hk, {==}, hkp),
   (X.L.go(regs2, 21n, 19n, v, c, {==}, g19), (X.L.go(regs2, 21n, 20n, v, env, {==}, g20),
   (X.L.gs(regs2, 21n, v, X.L.lt(regs2, 21n, hl, {==})), (X.L.go(regs2, 21n, 25n, v, U32.from_nat(n), {==}, g25),
    X.L.go(regs2, 21n, 3n, v, pend2, {==}, g3)))))))

def wr.s25(+n2: Nat, +regs: List<&2, U32>, +keep: List<&2, Nat>, +regs2: List<&2, U32>, +c: U32, +env: U32, +n: Nat,
  +args: U32, +pend2: U32, +hk: {D.Disj(keep, D.Walk.scr()) == True{} : Bool},
  w: WR(regs, keep, regs2, c, env, n, args, pend2)) ->
  WR(regs, keep, List.set(&2, U32, regs2, 25n, U32.from_nat(n2)), c, env, n2, args, pend2):
  (+hl, w1) = w
  (hkp, w2) = w1
  (g19, w3) = w2
  (g20, w4) = w3
  (g21, w5) = w4
  (g25, g3) = w5
  (X.L.len(regs2, 25n, U32.from_nat(n2), 63n, hl), (kept.set(regs, regs2, keep, D.Walk.scr(), 25n, U32.from_nat(n2), hk, {==}, hkp),
   (X.L.go(regs2, 25n, 19n, U32.from_nat(n2), c, {==}, g19), (X.L.go(regs2, 25n, 20n, U32.from_nat(n2), env, {==}, g20),
   (X.L.go(regs2, 25n, 21n, U32.from_nat(n2), args, {==}, g21), (X.L.gs(regs2, 25n, U32.from_nat(n2), X.L.lt(regs2, 25n, hl, {==})),
    X.L.go(regs2, 25n, 3n, U32.from_nat(n2), pend2, {==}, g3)))))))

# a release sets pend (register 3) to the released cell
def wr.s3(+v: U32, +regs: List<&2, U32>, +keep: List<&2, Nat>, +regs2: List<&2, U32>, +c: U32, +env: U32, +n: Nat,
  +args: U32, +pend2: U32, +hk: {D.Disj(keep, D.Walk.scr()) == True{} : Bool},
  w: WR(regs, keep, regs2, c, env, n, args, pend2)) ->
  WR(regs, keep, List.set(&2, U32, regs2, 3n, v), c, env, n, args, v):
  (+hl, w1) = w
  (hkp, w2) = w1
  (g19, w3) = w2
  (g20, w4) = w3
  (g21, w5) = w4
  (g25, g3) = w5
  (X.L.len(regs2, 3n, v, 63n, hl), (kept.set(regs, regs2, keep, D.Walk.scr(), 3n, v, hk, {==}, hkp),
   (X.L.go(regs2, 3n, 19n, v, c, {==}, g19), (X.L.go(regs2, 3n, 20n, v, env, {==}, g20),
   (X.L.go(regs2, 3n, 21n, v, args, {==}, g21), (X.L.go(regs2, 3n, 25n, v, U32.from_nat(n), {==}, g25),
    X.L.gs(regs2, 3n, v, X.L.lt(regs2, 3n, hl, {==}))))))))

# the parts of an argument's K.arg that the rounds read
def ag.cell(-ds: List<&2, Bk.Def>, -m: Cr.Cir.Cells, -im: U32, -fi: U32, -nx: U32, -ks: List<&2, List<&2, Word(8n)>>,
  -img: List<&2, Bk.Term>, -ps: List<&2, U32>, -os: List<&2, D.Rt>, -vs: List<&2, U32>, -a: U32, -q: Bk.Quan, -x: Bk.Term,
  -rest: List<&2, El.Arg>, h: D.Ag(ds, m, im, fi, nx, ks, img, ps, os, vs, a, Con{El.Arg{q, x}, rest})) ->
  {Cr.Cir.is_cell(a, im, fi, nx) == True{} : Bool}:
  (_, h1) = h
  (y, _) = h1
  y

def ag.qs(-ds: List<&2, Bk.Def>, -m: Cr.Cir.Cells, -im: U32, -fi: U32, -nx: U32, -ks: List<&2, List<&2, Word(8n)>>,
  -img: List<&2, Bk.Term>, -ps: List<&2, U32>, -os: List<&2, D.Rt>, -vs: List<&2, U32>, -a: U32, -q: Bk.Quan, -x: Bk.Term,
  -rest: List<&2, El.Arg>, h: D.Ag(ds, m, im, fi, nx, ks, img, ps, os, vs, a, Con{El.Arg{q, x}, rest})) ->
  D.Qs(Cr.Cir.Cells.get(m, a), q):
  (_, h1) = h
  (_, h2) = h1
  (_, h3) = h2
  (_, h4) = h3
  (_, h5) = h4
  (_, h6) = h5
  (y, _) = h6
  y

def ag.is(-ds: List<&2, Bk.Def>, -m: Cr.Cir.Cells, -im: U32, -fi: U32, -nx: U32, -ks: List<&2, List<&2, Word(8n)>>,
  -img: List<&2, Bk.Term>, -ps: List<&2, U32>, -os: List<&2, D.Rt>, -vs: List<&2, U32>, -a: U32, -q: Bk.Quan, -x: Bk.Term,
  -rest: List<&2, El.Arg>, h: D.Ag(ds, m, im, fi, nx, ks, img, ps, os, vs, a, Con{El.Arg{q, x}, rest})) ->
  D.Is(ds, m, im, fi, nx, ks, img, D.Fd(2n, m, a), x):
  (_, h1) = h
  (_, h2) = h1
  (_, h3) = h2
  (_, h4) = h3
  (_, h5) = h4
  (_, h6) = h5
  (_, h7) = h6
  (_, h8) = h7
  (_, h9) = h8
  (y, _) = h9
  y

# Ag's clause 9: the cell is not OWNED, or its term is a Var
def ag.fl(+ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +os: List<&2, D.Rt>, +vs: List<&2, U32>, +a: U32, +q: Bk.Quan, +x: Bk.Term,
  +rest: List<&2, El.Arg>, h: D.Ag(ds, m, im, fi, nx, ks, img, ps, os, vs, a, Con{El.Arg{q, x}, rest})) ->
  {Bool.or(Bool.not(D.Fl(m, a, 4096)), D.Term.is_var(x)) == True{} : Bool}:
  (_, h1) = h
  (_, h2) = h1
  (_, h3) = h2
  (_, h4) = h3
  (_, h5) = h4
  (_, h6) = h5
  (_, h7) = h6
  (_, h8) = h7
  (y, _) = h8
  y

# a Lab argument's K.arg holds nothing: its temporary has no root
def ag.cells.lab(+ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +os: List<&2, D.Rt>, +vs: List<&2, U32>, +a: U32, +q: Bk.Quan,
  +j: List<&2, Word(8n)>, +rest: List<&2, El.Arg>, +b: Bool, eb: {D.Fl(m, a, 4096) == b : Bool},
  h: D.Ag(ds, m, im, fi, nx, ks, img, ps, os, vs, a, Con{El.Arg{q, Bk.Term.Lab{j}}, rest})) ->
  {D.Ag.cells(Con{El.Arg{q, Bk.Term.Lab{j}}, rest}, m, a) == Con{D.TmpE{a, Nil{}}, D.Ag.cells(rest, m, D.Fd(1n, m, a))} : List<&2, D.TmpE>}:
  match b:
    case False{}:
      (%Equal.sym(Bool, D.Fl(m, a, 4096), False{}, eb) :
        {Con{D.TmpE{a, Bool.pick(List<&2, D.Rt>, _, [D.Rt{D.Fd(2n, m, a), Bk.Term.Lab{j}}], Nil{})}, D.Ag.cells(rest, m, D.Fd(1n, m, a))} == Con{D.TmpE{a, Nil{}}, D.Ag.cells(rest, m, D.Fd(1n, m, a))} : List<&2, D.TmpE>};
       {==})
    case True{}:
      D.bool.ft({Con{D.TmpE{a, Bool.pick(List<&2, D.Rt>, D.Fl(m, a, 4096), [D.Rt{D.Fd(2n, m, a), Bk.Term.Lab{j}}], Nil{})}, D.Ag.cells(rest, m, D.Fd(1n, m, a))} == Con{D.TmpE{a, Nil{}}, D.Ag.cells(rest, m, D.Fd(1n, m, a))} : List<&2, D.TmpE>},
        (%eb : {Bool.or(Bool.not(_), D.Term.is_var(Bk.Term.Lab{j})) == True{} : Bool};
         ag.fl(ds, m, im, fi, nx, ks, img, ps, os, vs, a, q, Bk.Term.Lab{j}, rest, h)))

# a cell that stands for a term is a cell, of the term's tag
def is.cell(+ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +c: U32, +t: Bk.Term, h: D.Is(ds, m, im, fi, nx, ks, img, c, t)) ->
  {Cr.Cir.is_cell(c, im, fi, nx) == True{} : Bool}:
  nd.cell(ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), t, D.A.tag(t), D.is.nd(ds, m, im, fi, nx, ks, img, c, t, h))

def is.tg(+ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +c: U32, +t: Bk.Term, h: D.Is(ds, m, im, fi, nx, ks, img, c, t)) -> {D.Tg(m, c) == D.A.tag(t) : U32}:
  nd.tag(ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), t, D.A.tag(t), D.is.nd(ds, m, im, fi, nx, ks, img, c, t, h))

# The start of a round
# --------------------
#
# The rounds of a λ and of the λ-matches begin with a test of wargs: with
# no argument left, wres 2 (the walk needs more arguments).

def r.nil(+h: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +keep: List<&2, Nat>,
  +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +tc: U32, +tt: Bk.Term,
  +a: U32, +xs: List<&2, El.Arg>, +xs0: List<&2, D.TmpE>, +B: Nat, +hk: {D.Disj(keep, D.Walk.scr()) == True{} : Bool},
  +regs2: List<&2, U32>, +m2: Cr.Cir.Cells, +nx2: U32, +pg2: U32, +c: U32, +s: Bk.Term, +env: U32, +e: List<&2, El.Arg>,
  +args: U32, +pend2: U32, +ps2: List<&2, U32>, +E1: Cr.Cir.Stmt, +E2: Cr.Cir.Stmt,
  +w: WS(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, s, env, e, args, Nil{}, pend2, ps2),
  hn: {El.Eval.walk(s, D.Arg.terms(e), Nil{}) == Some{None{}} : Maybe<Maybe<Bk.Term>>}) ->
  DW.WP(Cr.Cir.Stmt.if{Mc.M.eq(Mc.M.g(Mc.R.wargs()), Mc.M.c(0)), Mc.M.set(Mc.R.wres(), Mc.M.c(2)), Cr.Cir.Stmt.seq{E1, E2}}, h,
    X.X.st(regs2, m2, nx2, fi, im, pg2, lim, inp), u => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, u), B, lim):
  wp.if.bt(Cr.Cir.Stmt.seq{E1, E2}, h, Mc.M.eq(Mc.M.g(Mc.R.wargs()), Mc.M.c(0)), Mc.M.set(Mc.R.wres(), Mc.M.c(2)),
    X.X.st(regs2, m2, nx2, fi, im, pg2, lim, inp), u => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, u), B, lim, U32.is_eq(args, 0), {==},
    X.ev.op(Wa.Wasm.Op.eq{}, Mc.M.g(Mc.R.wargs()), Mc.M.c(0), X.X.st(regs2, m2, nx2, fi, im, pg2, lim, inp), args, 0,
      wr.r21(regs, keep, regs2, c, env, List.length(&2, El.Arg, e), args, pend2, ws.wr(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, s, env, e, args, Nil{}, pend2, ps2, w)), {==}),
    (%Equal.sym(U32, args, 0, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, s, env, e, args, Nil{}, pend2, ps2,
        ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, s, env, e, args, Nil{}, pend2, ps2, w))) :
      {U32.is_eq(_, 0) == True{} : Bool}; {==}),
    wp.set.k(h, 26n, 2, regs2, m2, nx2, fi, im, pg2, lim, inp, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B,
      wr.len(regs, keep, regs2, c, env, List.length(&2, El.Arg, e), args, pend2, ws.wr(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, s, env, e, args, Nil{}, pend2, ps2, w)), {==},
      Inr{ex.two(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, pg2, c, s, env, e, args, Nil{}, pend2, ps2,
        ws.wr(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, s, env, e, args, Nil{}, pend2, ps2, w), hk,
        Equal.trans(Maybe<Maybe<Bk.Term>>, El.Eval.walk(tt, Nil{}, xs), El.Eval.walk(s, D.Arg.terms(e), Nil{}), Some{None{}},
          ws.ev(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, s, env, e, args, Nil{}, pend2, ps2, w), hn),
        ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, s, env, e, args, Nil{}, pend2, ps2, w))}))

# with an argument left: the else
def r.con(+h: Nat, +regs2: List<&2, U32>, +m2: Cr.Cir.Cells, +nx2: U32, +fi: U32, +im: U32, +pg2: U32, +lim: U32,
  +inp: List<&2, Word(8n)>, -K: Cr.Cir.State -> Type, +B: Nat, +args: U32, +E1: Cr.Cir.Stmt, +E2: Cr.Cir.Stmt,
  h21: {List.get(&2, U32, regs2, 21n) == Some{args} : Maybe<&2, U32>}, hz: {U32.is_eq(args, 0) == False{} : Bool},
  k: DW.WP(Cr.Cir.Stmt.seq{E1, E2}, h, X.X.st(regs2, m2, nx2, fi, im, pg2, lim, inp), x => K(x), B, lim)) ->
  DW.WP(Cr.Cir.Stmt.if{Mc.M.eq(Mc.M.g(Mc.R.wargs()), Mc.M.c(0)), Mc.M.set(Mc.R.wres(), Mc.M.c(2)), Cr.Cir.Stmt.seq{E1, E2}}, h,
    X.X.st(regs2, m2, nx2, fi, im, pg2, lim, inp), K, B, lim):
  wp.if.be(Cr.Cir.Stmt.seq{E1, E2}, h, Mc.M.eq(Mc.M.g(Mc.R.wargs()), Mc.M.c(0)), Mc.M.set(Mc.R.wres(), Mc.M.c(2)),
    X.X.st(regs2, m2, nx2, fi, im, pg2, lim, inp), K, B, lim, U32.is_eq(args, 0), {==},
    X.ev.op(Wa.Wasm.Op.eq{}, Mc.M.g(Mc.R.wargs()), Mc.M.c(0), X.X.st(regs2, m2, nx2, fi, im, pg2, lim, inp), args, 0, h21, {==}),
    hz, k)

def t.and.c(a: Bool, b: Bool) -> {U32.and(Bool.to_u32(a), Bool.to_u32(b)) == Bool.to_u32(Bool.and(b, a)) : U32}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# The round of a λ-match of labels
# --------------------------------
#
# walk.mat reads the first argument (wa its K.arg, wq its quantity, wx its
# term's cell): a live Lab takes the first case when the label is the
# λ-match's name (the argument leaves the chain), else the other; anything
# else, wres 3.

def Wm.e() -> Cr.Cir.Stmt:
  X.sel.e(Mc.M.walk.mat())

def Wm.r1() -> Cr.Cir.Stmt:
  X.sel.b(Wm.e())

def Wm.r2() -> Cr.Cir.Stmt:
  X.sel.b(Wm.r1())

def Wm.r3() -> Cr.Cir.Stmt:
  X.sel.b(Wm.r2())

def Wm.lab() -> Cr.Cir.Stmt:
  X.sel.t(X.sel.a(Wm.r3()))

# the test of walk.mat, after the reads of the first argument: its term is
# a Lab and its quantity live
def mat.test(+regs2: List<&2, U32>, +m2: Cr.Cir.Cells, +nx2: U32, +fi: U32, +im: U32, +pg2: U32, +lim: U32, +inp: List<&2, Word(8n)>,
  +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +args: U32, +q0: Bk.Quan, +x0: Bk.Term,
  hl: {List.length(&2, U32, regs2) == 63n : Nat}, hq: D.Qs(Cr.Cir.Cells.get(m2, args), q0),
  +his: D.Is(ds, m2, im, fi, nx2, ks, img, D.Fd(2n, m2, args), x0)) ->
  {Cr.Cir.eval(Mc.M.and(Mc.M.ne(Mc.M.g(Mc.R.wq()), Mc.M.c(0)), Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wx())), Mc.M.c(Mc.T.lab()))), X.X.st(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), 23n, D.Fd(2n, m2, args)), m2, nx2, fi, im, pg2, lim, inp)) == Some{Bool.to_u32(Bool.and(U32.is_eq(D.A.tag(x0), 13), El.Quan.live(q0)))} : Maybe<&2, U32>}:
  +l3 = X.L.len(regs2, 22n, args, 63n, hl)
  +l4 = X.L.len(List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args), 63n, l3)
  +e24 = X.L.go(List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), 23n, 24n, D.Fd(2n, m2, args), D.Qn(m2, args), {==}, X.L.gs(List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args), X.L.lt(List.set(&2, U32, regs2, 22n, args), 24n, l3, {==})))
  +e23 = X.L.gs(List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), 23n, D.Fd(2n, m2, args), X.L.lt(List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), 23n, l4, {==}))
  +st5 = X.X.st(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), 23n, D.Fd(2n, m2, args)), m2, nx2, fi, im, pg2, lim, inp)
  +tg = D.Tg(m2, D.Fd(2n, m2, args))
  +ene = X.ev.op(Wa.Wasm.Op.ne{}, Mc.M.g(Mc.R.wq()), Mc.M.c(0), st5, D.Qn(m2, args), 0, e24, {==})
  +etg = X.ev.opw(Wa.Wasm.Op.and{}, Mc.M.f(0n, Mc.M.g(Mc.R.wx())), Mc.M.c(63), st5, D.Fd(0n, m2, D.Fd(2n, m2, args)), 63, tg,
    X.ev.fld(0n, Mc.M.g(Mc.R.wx()), st5, D.Fd(2n, m2, args), e23, is.cell(ds, m2, im, fi, nx2, ks, img, D.Fd(2n, m2, args), x0, his)), {==}, {==})
  +eeq = X.ev.op(Wa.Wasm.Op.eq{}, Mc.M.tag(Mc.M.g(Mc.R.wx())), Mc.M.c(Mc.T.lab()), st5, tg, 13, etg, {==})
  (%is.tg(ds, m2, im, fi, nx2, ks, img, D.Fd(2n, m2, args), x0, his) :
     {Cr.Cir.eval(Mc.M.and(Mc.M.ne(Mc.M.g(Mc.R.wq()), Mc.M.c(0)), Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wx())), Mc.M.c(Mc.T.lab()))), st5) == Some{Bool.to_u32(Bool.and(U32.is_eq(_, 13), El.Quan.live(q0)))} : Maybe<&2, U32>};
   %ne.quan(q0) : {Cr.Cir.eval(Mc.M.and(Mc.M.ne(Mc.M.g(Mc.R.wq()), Mc.M.c(0)), Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wx())), Mc.M.c(Mc.T.lab()))), st5) == Some{Bool.to_u32(Bool.and(U32.is_eq(tg, 13), _))} : Maybe<&2, U32>};
   %hq : {Cr.Cir.eval(Mc.M.and(Mc.M.ne(Mc.M.g(Mc.R.wq()), Mc.M.c(0)), Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wx())), Mc.M.c(Mc.T.lab()))), st5) == Some{Bool.to_u32(Bool.and(U32.is_eq(tg, 13), U32.is_ne(_, 0)))} : Maybe<&2, U32>};
   X.ev.opw(Wa.Wasm.Op.and{}, Mc.M.ne(Mc.M.g(Mc.R.wq()), Mc.M.c(0)), Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wx())), Mc.M.c(Mc.T.lab())), st5,
     Bool.to_u32(U32.is_ne(D.Qn(m2, args), 0)), Bool.to_u32(U32.is_eq(tg, 13)), Bool.to_u32(Bool.and(U32.is_eq(tg, 13), U32.is_ne(D.Qn(m2, args), 0))),
     ene, eeq, t.and.c(U32.is_ne(D.Qn(m2, args), 0), U32.is_eq(tg, 13))))

# the test fails: wres 3, and no walk exists
def mat.fail(+h: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +keep: List<&2, Nat>,
  +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +tc: U32, +tt: Bk.Term,
  +a: U32, +xs: List<&2, El.Arg>, +xs0: List<&2, D.TmpE>, +B: Nat, +hk: {D.Disj(keep, D.Walk.scr()) == True{} : Bool},
  +regs2: List<&2, U32>, +m2: Cr.Cir.Cells, +nx2: U32, +pg2: U32, +c: U32, +k: List<&2, Word(8n)>, +h0: Bk.Term, +n0: Bk.Term,
  +env: U32, +e: List<&2, El.Arg>, +args: U32, +q0: Bk.Quan, +x0: Bk.Term, +rest: List<&2, El.Arg>, +pend2: U32, +ps2: List<&2, U32>,
  +w5: WS(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), 23n, D.Fd(2n, m2, args)), m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2),
  +b: Bool, hb: {b == False{} : Bool}, hc: {Cr.Cir.eval(Mc.M.and(Mc.M.ne(Mc.M.g(Mc.R.wq()), Mc.M.c(0)), Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wx())), Mc.M.c(Mc.T.lab()))), X.X.st(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), 23n, D.Fd(2n, m2, args)), m2, nx2, fi, im, pg2, lim, inp)) == Some{Bool.to_u32(b)} : Maybe<&2, U32>},
  hn: {El.Eval.walk(Bk.Term.Mat{k, h0, n0}, D.Arg.terms(e), Con{El.Arg{q0, x0}, rest}) == None{} : Maybe<Maybe<Bk.Term>>}) ->
  DW.WP(X.sel.a(Wm.r3()), h, X.X.st(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), 23n, D.Fd(2n, m2, args)), m2, nx2, fi, im, pg2, lim, inp), t => DW.WP(Cr.Cir.Stmt.nop{}, h, t, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, lim):
  wp.if.be(Mc.M.set(Mc.R.wres(), Mc.M.c(3)), h, Mc.M.and(Mc.M.ne(Mc.M.g(Mc.R.wq()), Mc.M.c(0)), Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wx())), Mc.M.c(Mc.T.lab()))), Wm.lab(), X.X.st(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), 23n, D.Fd(2n, m2, args)), m2, nx2, fi, im, pg2, lim, inp), t => DW.WP(Cr.Cir.Stmt.nop{}, h, t, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, lim, b, {==}, hc, hb,
    wp.set.k(h, 26n, 3, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), 23n, D.Fd(2n, m2, args)), m2, nx2, fi, im, pg2, lim, inp, x => DW.WP(Cr.Cir.Stmt.nop{}, h, x, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B,
      wr.len(regs, keep, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), 23n, D.Fd(2n, m2, args)), c, env, List.length(&2, El.Arg, e), args, pend2, ws.wr(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), 23n, D.Fd(2n, m2, args)), m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, w5)), {==},
      Inr{ex.three(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), 23n, D.Fd(2n, m2, args)), m2, nx2, pg2, c, env, List.length(&2, El.Arg, e), args, pend2, ps2,
        ws.wr(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), 23n, D.Fd(2n, m2, args)), m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, w5), hk,
        Equal.trans(Maybe<Maybe<Bk.Term>>, El.Eval.walk(tt, Nil{}, xs), El.Eval.walk(Bk.Term.Mat{k, h0, n0}, D.Arg.terms(e), Con{El.Arg{q0, x0}, rest}), None{},
          ws.ev(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), 23n, D.Fd(2n, m2, args)), m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, w5), hn),
        wh.kc(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), 23n, D.Fd(2n, m2, args)), m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, w5)), wh.st(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), 23n, D.Fd(2n, m2, args)), m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, w5)), wh.mem(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), 23n, D.Fd(2n, m2, args)), m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, w5)))}))

# the walk of a live label whose name is the case's: the case's first arm
def mat.ev.hit(+q0: Bk.Quan, +j: List<&2, Word(8n)>, +k: List<&2, Word(8n)>, +h0: Bk.Term, +n0: Bk.Term,
  +e: List<&2, Bk.Term>, +rest: List<&2, El.Arg>,
  hq: {El.Quan.live(q0) == True{} : Bool}, hj: {Sd.Name.is_eq(j, k) == True{} : Bool}) ->
  {El.Eval.walk(Bk.Term.Mat{k, h0, n0}, e, Con{El.Arg{q0, Bk.Term.Lab{j}}, rest}) ==
    El.Eval.walk(h0, e, rest) : Maybe<Maybe<Bk.Term>>}:
  (%Equal.sym(Bool, El.Quan.live(q0), True{}, hq) :
     {El.Eval.walk.if(_, El.Eval.walk.pick(Sd.Name.is_eq(j, k), El.Eval.walk(h0, e, rest), El.Eval.walk(n0, e, Con{El.Arg{q0, Bk.Term.Lab{j}}, rest}))) ==
      El.Eval.walk(h0, e, rest) : Maybe<Maybe<Bk.Term>>};
   %Equal.sym(Bool, Sd.Name.is_eq(j, k), True{}, hj) :
     {El.Eval.walk.pick(_, El.Eval.walk(h0, e, rest), El.Eval.walk(n0, e, Con{El.Arg{q0, Bk.Term.Lab{j}}, rest})) ==
      El.Eval.walk(h0, e, rest) : Maybe<Maybe<Bk.Term>>};
   {==})

# the walk of a live label of another name: the case's second arm
def mat.ev.miss(+q0: Bk.Quan, +j: List<&2, Word(8n)>, +k: List<&2, Word(8n)>, +h0: Bk.Term, +n0: Bk.Term,
  +e: List<&2, Bk.Term>, +rest: List<&2, El.Arg>,
  hq: {El.Quan.live(q0) == True{} : Bool}, hj: {Sd.Name.is_eq(j, k) == False{} : Bool}) ->
  {El.Eval.walk(Bk.Term.Mat{k, h0, n0}, e, Con{El.Arg{q0, Bk.Term.Lab{j}}, rest}) ==
    El.Eval.walk(n0, e, Con{El.Arg{q0, Bk.Term.Lab{j}}, rest}) : Maybe<Maybe<Bk.Term>>}:
  (%Equal.sym(Bool, El.Quan.live(q0), True{}, hq) :
     {El.Eval.walk.if(_, El.Eval.walk.pick(Sd.Name.is_eq(j, k), El.Eval.walk(h0, e, rest), El.Eval.walk(n0, e, Con{El.Arg{q0, Bk.Term.Lab{j}}, rest}))) ==
      El.Eval.walk(n0, e, Con{El.Arg{q0, Bk.Term.Lab{j}}, rest}) : Maybe<Maybe<Bk.Term>>};
   %Equal.sym(Bool, Sd.Name.is_eq(j, k), False{}, hj) :
     {El.Eval.walk.pick(_, El.Eval.walk(h0, e, rest), El.Eval.walk(n0, e, Con{El.Arg{q0, Bk.Term.Lab{j}}, rest})) ==
      El.Eval.walk(n0, e, Con{El.Arg{q0, Bk.Term.Lab{j}}, rest}) : Maybe<Maybe<Bk.Term>>};
   {==})

# a live Lab: the test passes; the case on the label
def mat.lab(+h: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +keep: List<&2, Nat>,
  +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +tc: U32, +tt: Bk.Term,
  +a: U32, +xs: List<&2, El.Arg>, +xs0: List<&2, D.TmpE>, +B: Nat, +hk: {D.Disj(keep, D.Walk.scr()) == True{} : Bool},
  +regs2: List<&2, U32>, +m2: Cr.Cir.Cells, +nx2: U32, +pg2: U32, +c: U32, +k: List<&2, Word(8n)>, +h0: Bk.Term, +n0: Bk.Term,
  +env: U32, +e: List<&2, El.Arg>, +args: U32, +q0: Bk.Quan, +j: List<&2, Word(8n)>, +rest: List<&2, El.Arg>, +pend2: U32, +ps2: List<&2, U32>,
  +w5: WS(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), 23n, D.Fd(2n, m2, args)), m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Lab{j}}, rest}, pend2, ps2),
  hq: {El.Quan.live(q0) == True{} : Bool}) ->
  DW.WP(Wm.lab(), h, X.X.st(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), 23n, D.Fd(2n, m2, args)), m2, nx2, fi, im, pg2, lim, inp), x => DW.WP(Cr.Cir.Stmt.nop{}, h, x, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, lim):
  ?TODO

def mat.labq(+h: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +keep: List<&2, Nat>,
  +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +tc: U32, +tt: Bk.Term,
  +a: U32, +xs: List<&2, El.Arg>, +xs0: List<&2, D.TmpE>, +B: Nat, +hk: {D.Disj(keep, D.Walk.scr()) == True{} : Bool},
  +regs2: List<&2, U32>, +m2: Cr.Cir.Cells, +nx2: U32, +pg2: U32, +c: U32, +k: List<&2, Word(8n)>, +h0: Bk.Term, +n0: Bk.Term,
  +env: U32, +e: List<&2, El.Arg>, +args: U32, +q0: Bk.Quan, +j: List<&2, Word(8n)>, +rest: List<&2, El.Arg>, +pend2: U32, +ps2: List<&2, U32>,
  +w: WS(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Lab{j}}, rest}, pend2, ps2),
  +w5: WS(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), 23n, D.Fd(2n, m2, args)), m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Lab{j}}, rest}, pend2, ps2),
  +hl: {List.length(&2, U32, regs2) == 63n : Nat}) ->
  DW.WP(X.sel.a(Wm.r3()), h, X.X.st(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), 23n, D.Fd(2n, m2, args)), m2, nx2, fi, im, pg2, lim, inp), t => DW.WP(Cr.Cir.Stmt.nop{}, h, t, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, lim):
  match q0:
    case Bk.Quan.Q0{}:
      mat.fail(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, k, h0, n0, env, e, args, Bk.Quan.Q0{}, Bk.Term.Lab{j}, rest, pend2, ps2, w5, Bool.and(U32.is_eq(D.A.tag(Bk.Term.Lab{j}), 13), El.Quan.live(Bk.Quan.Q0{})), {==},
        mat.test(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, args, Bk.Quan.Q0{}, Bk.Term.Lab{j}, hl, ag.qs(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, Bk.Quan.Q0{}, Bk.Term.Lab{j}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{Bk.Quan.Q0{}, Bk.Term.Lab{j}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{Bk.Quan.Q0{}, Bk.Term.Lab{j}}, rest}, pend2, ps2, w))), ag.is(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, Bk.Quan.Q0{}, Bk.Term.Lab{j}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{Bk.Quan.Q0{}, Bk.Term.Lab{j}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{Bk.Quan.Q0{}, Bk.Term.Lab{j}}, rest}, pend2, ps2, w)))), {==})
    case Bk.Quan.Q1{}:
      wp.if.bt(Mc.M.set(Mc.R.wres(), Mc.M.c(3)), h, Mc.M.and(Mc.M.ne(Mc.M.g(Mc.R.wq()), Mc.M.c(0)), Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wx())), Mc.M.c(Mc.T.lab()))), Wm.lab(), X.X.st(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), 23n, D.Fd(2n, m2, args)), m2, nx2, fi, im, pg2, lim, inp), t => DW.WP(Cr.Cir.Stmt.nop{}, h, t, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, lim,
        Bool.and(U32.is_eq(D.A.tag(Bk.Term.Lab{j}), 13), El.Quan.live(Bk.Quan.Q1{})), {==}, mat.test(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, args, Bk.Quan.Q1{}, Bk.Term.Lab{j}, hl, ag.qs(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, Bk.Quan.Q1{}, Bk.Term.Lab{j}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{Bk.Quan.Q1{}, Bk.Term.Lab{j}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{Bk.Quan.Q1{}, Bk.Term.Lab{j}}, rest}, pend2, ps2, w))), ag.is(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, Bk.Quan.Q1{}, Bk.Term.Lab{j}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{Bk.Quan.Q1{}, Bk.Term.Lab{j}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{Bk.Quan.Q1{}, Bk.Term.Lab{j}}, rest}, pend2, ps2, w)))), {==},
        mat.lab(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, k, h0, n0, env, e, args, Bk.Quan.Q1{}, j, rest, pend2, ps2, w5, {==}))
    case Bk.Quan.Q2{}:
      wp.if.bt(Mc.M.set(Mc.R.wres(), Mc.M.c(3)), h, Mc.M.and(Mc.M.ne(Mc.M.g(Mc.R.wq()), Mc.M.c(0)), Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wx())), Mc.M.c(Mc.T.lab()))), Wm.lab(), X.X.st(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), 23n, D.Fd(2n, m2, args)), m2, nx2, fi, im, pg2, lim, inp), t => DW.WP(Cr.Cir.Stmt.nop{}, h, t, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, lim,
        Bool.and(U32.is_eq(D.A.tag(Bk.Term.Lab{j}), 13), El.Quan.live(Bk.Quan.Q2{})), {==}, mat.test(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, args, Bk.Quan.Q2{}, Bk.Term.Lab{j}, hl, ag.qs(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, Bk.Quan.Q2{}, Bk.Term.Lab{j}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{Bk.Quan.Q2{}, Bk.Term.Lab{j}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{Bk.Quan.Q2{}, Bk.Term.Lab{j}}, rest}, pend2, ps2, w))), ag.is(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, Bk.Quan.Q2{}, Bk.Term.Lab{j}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{Bk.Quan.Q2{}, Bk.Term.Lab{j}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{Bk.Quan.Q2{}, Bk.Term.Lab{j}}, rest}, pend2, ps2, w)))), {==},
        mat.lab(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, k, h0, n0, env, e, args, Bk.Quan.Q2{}, j, rest, pend2, ps2, w5, {==}))

# the test of walk.mat, by the first argument's form and quantity
def mat.if(+h: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +keep: List<&2, Nat>,
  +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +tc: U32, +tt: Bk.Term,
  +a: U32, +xs: List<&2, El.Arg>, +xs0: List<&2, D.TmpE>, +B: Nat, +hk: {D.Disj(keep, D.Walk.scr()) == True{} : Bool},
  +regs2: List<&2, U32>, +m2: Cr.Cir.Cells, +nx2: U32, +pg2: U32, +c: U32, +k: List<&2, Word(8n)>, +h0: Bk.Term, +n0: Bk.Term,
  +env: U32, +e: List<&2, El.Arg>, +args: U32, +q0: Bk.Quan, +x0: Bk.Term, +rest: List<&2, El.Arg>, +pend2: U32, +ps2: List<&2, U32>,
  +w: WS(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2),
  +w5: WS(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), 23n, D.Fd(2n, m2, args)), m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2),
  +hl: {List.length(&2, U32, regs2) == 63n : Nat}) ->
  DW.WP(X.sel.a(Wm.r3()), h, X.X.st(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), 23n, D.Fd(2n, m2, args)), m2, nx2, fi, im, pg2, lim, inp), t => DW.WP(Cr.Cir.Stmt.nop{}, h, t, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, lim):
  match x0:
    case Bk.Term.Var{+i}:
      mat.fail(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, k, h0, n0, env, e, args, q0, Bk.Term.Var{i}, rest, pend2, ps2, w5, Bool.and(U32.is_eq(D.A.tag(Bk.Term.Var{i}), 13), El.Quan.live(q0)), {==},
        mat.test(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, args, q0, Bk.Term.Var{i}, hl, ag.qs(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Var{i}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Var{i}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Var{i}}, rest}, pend2, ps2, w))), ag.is(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Var{i}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Var{i}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Var{i}}, rest}, pend2, ps2, w)))), {==})
    case Bk.Term.Ref{+kk}:
      mat.fail(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, k, h0, n0, env, e, args, q0, Bk.Term.Ref{kk}, rest, pend2, ps2, w5, Bool.and(U32.is_eq(D.A.tag(Bk.Term.Ref{kk}), 13), El.Quan.live(q0)), {==},
        mat.test(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, args, q0, Bk.Term.Ref{kk}, hl, ag.qs(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Ref{kk}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Ref{kk}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Ref{kk}}, rest}, pend2, ps2, w))), ag.is(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Ref{kk}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Ref{kk}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Ref{kk}}, rest}, pend2, ps2, w)))), {==})
    case Bk.Term.Ann{+y1, +y2}:
      mat.fail(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, k, h0, n0, env, e, args, q0, Bk.Term.Ann{y1, y2}, rest, pend2, ps2, w5, Bool.and(U32.is_eq(D.A.tag(Bk.Term.Ann{y1, y2}), 13), El.Quan.live(q0)), {==},
        mat.test(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, args, q0, Bk.Term.Ann{y1, y2}, hl, ag.qs(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Ann{y1, y2}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Ann{y1, y2}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Ann{y1, y2}}, rest}, pend2, ps2, w))), ag.is(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Ann{y1, y2}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Ann{y1, y2}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Ann{y1, y2}}, rest}, pend2, ps2, w)))), {==})
    case Bk.Term.Let{+q1, +v1, +f1}:
      mat.fail(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, k, h0, n0, env, e, args, q0, Bk.Term.Let{q1, v1, f1}, rest, pend2, ps2, w5, Bool.and(U32.is_eq(D.A.tag(Bk.Term.Let{q1, v1, f1}), 13), El.Quan.live(q0)), {==},
        mat.test(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, args, q0, Bk.Term.Let{q1, v1, f1}, hl, ag.qs(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Let{q1, v1, f1}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Let{q1, v1, f1}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Let{q1, v1, f1}}, rest}, pend2, ps2, w))), ag.is(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Let{q1, v1, f1}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Let{q1, v1, f1}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Let{q1, v1, f1}}, rest}, pend2, ps2, w)))), {==})
    case Bk.Term.Typ{+y1}:
      mat.fail(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, k, h0, n0, env, e, args, q0, Bk.Term.Typ{y1}, rest, pend2, ps2, w5, Bool.and(U32.is_eq(D.A.tag(Bk.Term.Typ{y1}), 13), El.Quan.live(q0)), {==},
        mat.test(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, args, q0, Bk.Term.Typ{y1}, hl, ag.qs(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Typ{y1}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Typ{y1}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Typ{y1}}, rest}, pend2, ps2, w))), ag.is(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Typ{y1}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Typ{y1}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Typ{y1}}, rest}, pend2, ps2, w)))), {==})
    case Bk.Term.Min{+y1, +y2}:
      mat.fail(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, k, h0, n0, env, e, args, q0, Bk.Term.Min{y1, y2}, rest, pend2, ps2, w5, Bool.and(U32.is_eq(D.A.tag(Bk.Term.Min{y1, y2}), 13), El.Quan.live(q0)), {==},
        mat.test(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, args, q0, Bk.Term.Min{y1, y2}, hl, ag.qs(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Min{y1, y2}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Min{y1, y2}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Min{y1, y2}}, rest}, pend2, ps2, w))), ag.is(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Min{y1, y2}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Min{y1, y2}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Min{y1, y2}}, rest}, pend2, ps2, w)))), {==})
    case Bk.Term.All{+q1, +y1, +y2}:
      mat.fail(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, k, h0, n0, env, e, args, q0, Bk.Term.All{q1, y1, y2}, rest, pend2, ps2, w5, Bool.and(U32.is_eq(D.A.tag(Bk.Term.All{q1, y1, y2}), 13), El.Quan.live(q0)), {==},
        mat.test(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, args, q0, Bk.Term.All{q1, y1, y2}, hl, ag.qs(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.All{q1, y1, y2}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.All{q1, y1, y2}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.All{q1, y1, y2}}, rest}, pend2, ps2, w))), ag.is(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.All{q1, y1, y2}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.All{q1, y1, y2}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.All{q1, y1, y2}}, rest}, pend2, ps2, w)))), {==})
    case Bk.Term.Lam{+q1, +f1}:
      mat.fail(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, k, h0, n0, env, e, args, q0, Bk.Term.Lam{q1, f1}, rest, pend2, ps2, w5, Bool.and(U32.is_eq(D.A.tag(Bk.Term.Lam{q1, f1}), 13), El.Quan.live(q0)), {==},
        mat.test(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, args, q0, Bk.Term.Lam{q1, f1}, hl, ag.qs(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Lam{q1, f1}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Lam{q1, f1}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Lam{q1, f1}}, rest}, pend2, ps2, w))), ag.is(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Lam{q1, f1}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Lam{q1, f1}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Lam{q1, f1}}, rest}, pend2, ps2, w)))), {==})
    case Bk.Term.App{+q1, +f1, +y1}:
      mat.fail(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, k, h0, n0, env, e, args, q0, Bk.Term.App{q1, f1, y1}, rest, pend2, ps2, w5, Bool.and(U32.is_eq(D.A.tag(Bk.Term.App{q1, f1, y1}), 13), El.Quan.live(q0)), {==},
        mat.test(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, args, q0, Bk.Term.App{q1, f1, y1}, hl, ag.qs(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.App{q1, f1, y1}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.App{q1, f1, y1}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.App{q1, f1, y1}}, rest}, pend2, ps2, w))), ag.is(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.App{q1, f1, y1}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.App{q1, f1, y1}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.App{q1, f1, y1}}, rest}, pend2, ps2, w)))), {==})
    case Bk.Term.Sig{+q1, +y1, +y2}:
      mat.fail(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, k, h0, n0, env, e, args, q0, Bk.Term.Sig{q1, y1, y2}, rest, pend2, ps2, w5, Bool.and(U32.is_eq(D.A.tag(Bk.Term.Sig{q1, y1, y2}), 13), El.Quan.live(q0)), {==},
        mat.test(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, args, q0, Bk.Term.Sig{q1, y1, y2}, hl, ag.qs(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Sig{q1, y1, y2}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Sig{q1, y1, y2}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Sig{q1, y1, y2}}, rest}, pend2, ps2, w))), ag.is(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Sig{q1, y1, y2}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Sig{q1, y1, y2}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Sig{q1, y1, y2}}, rest}, pend2, ps2, w)))), {==})
    case Bk.Term.Tup{+q1, +y1, +y2}:
      mat.fail(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, k, h0, n0, env, e, args, q0, Bk.Term.Tup{q1, y1, y2}, rest, pend2, ps2, w5, Bool.and(U32.is_eq(D.A.tag(Bk.Term.Tup{q1, y1, y2}), 13), El.Quan.live(q0)), {==},
        mat.test(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, args, q0, Bk.Term.Tup{q1, y1, y2}, hl, ag.qs(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Tup{q1, y1, y2}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Tup{q1, y1, y2}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Tup{q1, y1, y2}}, rest}, pend2, ps2, w))), ag.is(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Tup{q1, y1, y2}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Tup{q1, y1, y2}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Tup{q1, y1, y2}}, rest}, pend2, ps2, w)))), {==})
    case Bk.Term.Prj{+h1}:
      mat.fail(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, k, h0, n0, env, e, args, q0, Bk.Term.Prj{h1}, rest, pend2, ps2, w5, Bool.and(U32.is_eq(D.A.tag(Bk.Term.Prj{h1}), 13), El.Quan.live(q0)), {==},
        mat.test(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, args, q0, Bk.Term.Prj{h1}, hl, ag.qs(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Prj{h1}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Prj{h1}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Prj{h1}}, rest}, pend2, ps2, w))), ag.is(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Prj{h1}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Prj{h1}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Prj{h1}}, rest}, pend2, ps2, w)))), {==})
    case Bk.Term.Enu{+kk}:
      mat.fail(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, k, h0, n0, env, e, args, q0, Bk.Term.Enu{kk}, rest, pend2, ps2, w5, Bool.and(U32.is_eq(D.A.tag(Bk.Term.Enu{kk}), 13), El.Quan.live(q0)), {==},
        mat.test(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, args, q0, Bk.Term.Enu{kk}, hl, ag.qs(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Enu{kk}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Enu{kk}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Enu{kk}}, rest}, pend2, ps2, w))), ag.is(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Enu{kk}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Enu{kk}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Enu{kk}}, rest}, pend2, ps2, w)))), {==})
    case Bk.Term.Mat{+kk, +h1, +n1}:
      mat.fail(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, k, h0, n0, env, e, args, q0, Bk.Term.Mat{kk, h1, n1}, rest, pend2, ps2, w5, Bool.and(U32.is_eq(D.A.tag(Bk.Term.Mat{kk, h1, n1}), 13), El.Quan.live(q0)), {==},
        mat.test(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, args, q0, Bk.Term.Mat{kk, h1, n1}, hl, ag.qs(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Mat{kk, h1, n1}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Mat{kk, h1, n1}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Mat{kk, h1, n1}}, rest}, pend2, ps2, w))), ag.is(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Mat{kk, h1, n1}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Mat{kk, h1, n1}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Mat{kk, h1, n1}}, rest}, pend2, ps2, w)))), {==})
    case Bk.Term.Efq{}:
      mat.fail(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, k, h0, n0, env, e, args, q0, Bk.Term.Efq{}, rest, pend2, ps2, w5, Bool.and(U32.is_eq(D.A.tag(Bk.Term.Efq{}), 13), El.Quan.live(q0)), {==},
        mat.test(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, args, q0, Bk.Term.Efq{}, hl, ag.qs(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Efq{}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Efq{}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Efq{}}, rest}, pend2, ps2, w))), ag.is(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Efq{}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Efq{}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Efq{}}, rest}, pend2, ps2, w)))), {==})
    case Bk.Term.Eql{+y1, +y2, +y3}:
      mat.fail(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, k, h0, n0, env, e, args, q0, Bk.Term.Eql{y1, y2, y3}, rest, pend2, ps2, w5, Bool.and(U32.is_eq(D.A.tag(Bk.Term.Eql{y1, y2, y3}), 13), El.Quan.live(q0)), {==},
        mat.test(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, args, q0, Bk.Term.Eql{y1, y2, y3}, hl, ag.qs(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Eql{y1, y2, y3}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Eql{y1, y2, y3}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Eql{y1, y2, y3}}, rest}, pend2, ps2, w))), ag.is(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Eql{y1, y2, y3}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Eql{y1, y2, y3}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Eql{y1, y2, y3}}, rest}, pend2, ps2, w)))), {==})
    case Bk.Term.Rfl{}:
      mat.fail(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, k, h0, n0, env, e, args, q0, Bk.Term.Rfl{}, rest, pend2, ps2, w5, Bool.and(U32.is_eq(D.A.tag(Bk.Term.Rfl{}), 13), El.Quan.live(q0)), {==},
        mat.test(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, args, q0, Bk.Term.Rfl{}, hl, ag.qs(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Rfl{}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Rfl{}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Rfl{}}, rest}, pend2, ps2, w))), ag.is(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Rfl{}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Rfl{}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Rfl{}}, rest}, pend2, ps2, w)))), {==})
    case Bk.Term.Rwt{+y1, +y2, +y3}:
      mat.fail(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, k, h0, n0, env, e, args, q0, Bk.Term.Rwt{y1, y2, y3}, rest, pend2, ps2, w5, Bool.and(U32.is_eq(D.A.tag(Bk.Term.Rwt{y1, y2, y3}), 13), El.Quan.live(q0)), {==},
        mat.test(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, args, q0, Bk.Term.Rwt{y1, y2, y3}, hl, ag.qs(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Rwt{y1, y2, y3}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Rwt{y1, y2, y3}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Rwt{y1, y2, y3}}, rest}, pend2, ps2, w))), ag.is(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Rwt{y1, y2, y3}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Rwt{y1, y2, y3}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, Bk.Term.Rwt{y1, y2, y3}}, rest}, pend2, ps2, w)))), {==})
    case Bk.Term.Lab{+j}:
      mat.labq(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, k, h0, n0, env, e, args, q0, j, rest, pend2, ps2, w, w5, hl)


# walk.mat with an argument: the reads of its K.arg, then the test
def mat.go(+h: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +keep: List<&2, Nat>,
  +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +tc: U32, +tt: Bk.Term,
  +a: U32, +xs: List<&2, El.Arg>, +xs0: List<&2, D.TmpE>, +B: Nat, +hk: {D.Disj(keep, D.Walk.scr()) == True{} : Bool},
  +regs2: List<&2, U32>, +m2: Cr.Cir.Cells, +nx2: U32, +pg2: U32, +c: U32, +k: List<&2, Word(8n)>, +h0: Bk.Term, +n0: Bk.Term,
  +env: U32, +e: List<&2, El.Arg>, +args: U32, +q0: Bk.Quan, +x0: Bk.Term, +rest: List<&2, El.Arg>, +pend2: U32, +ps2: List<&2, U32>,
  +w: WS(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2)) ->
  DW.WP(Cr.Cir.Stmt.seq{X.sel.a(Wm.e()), X.sel.b(Wm.e())}, h, X.X.st(regs2, m2, nx2, fi, im, pg2, lim, inp), x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim):
  +hl = wr.len(regs, keep, regs2, c, env, List.length(&2, El.Arg, e), args, pend2, ws.wr(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, w))
  +l3 = X.L.len(regs2, 22n, args, 63n, hl)
  +l4 = X.L.len(List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args), 63n, l3)
  +hca = ag.cell(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, x0, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, w)))
  +e22 = X.L.gs(regs2, 22n, args, X.L.lt(regs2, 22n, hl, {==}))
  +eq = X.ev.opw(Wa.Wasm.Op.and{}, Mc.M.shr(Mc.M.f(0n, Mc.M.g(Mc.R.wa())), Mc.M.c(6)), Mc.M.c(3), X.X.st(List.set(&2, U32, regs2, 22n, args), m2, nx2, fi, im, pg2, lim, inp),
    Wa.Wasm.op(Wa.Wasm.Op.shr_u{}, D.Fd(0n, m2, args), 6), 3, D.Qn(m2, args),
    X.ev.op(Wa.Wasm.Op.shr_u{}, Mc.M.f(0n, Mc.M.g(Mc.R.wa())), Mc.M.c(6), X.X.st(List.set(&2, U32, regs2, 22n, args), m2, nx2, fi, im, pg2, lim, inp), D.Fd(0n, m2, args), 6,
      X.ev.fld(0n, Mc.M.g(Mc.R.wa()), X.X.st(List.set(&2, U32, regs2, 22n, args), m2, nx2, fi, im, pg2, lim, inp), args, e22, hca), {==}), {==}, {==})
  +ex = X.ev.fld(2n, Mc.M.g(Mc.R.wa()), X.X.st(List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), m2, nx2, fi, im, pg2, lim, inp), args, X.L.go(List.set(&2, U32, regs2, 22n, args), 24n, 22n, D.Qn(m2, args), args, {==}, e22), hca)
  wp.set.e(22n, Mc.M.g(Mc.R.wargs()), args, regs2, m2, nx2, fi, im, pg2, lim, inp, h, t => DW.WP(Wm.r1(), h, t, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B,
    wr.r21(regs, keep, regs2, c, env, List.length(&2, El.Arg, e), args, pend2, ws.wr(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, w)), hl, {==},
    wp.set.e(24n, Mc.M.q(Mc.M.g(Mc.R.wa())), D.Qn(m2, args), List.set(&2, U32, regs2, 22n, args), m2, nx2, fi, im, pg2, lim, inp, h, t => DW.WP(Wm.r2(), h, t, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B,
      eq, l3, {==},
      wp.set.e(23n, Mc.M.f(2n, Mc.M.g(Mc.R.wa())), D.Fd(2n, m2, args), List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), m2, nx2, fi, im, pg2, lim, inp, h, t => DW.WP(Wm.r3(), h, t, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B,
        ex, l4, {==},
        mat.if(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, k, h0, n0, env, e, args, q0, x0, rest, pend2, ps2, w, ws.set(23n, D.Fd(2n, m2, args), ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, hk, {==}, {==}, {==}, {==}, {==}, {==}, {==}, ws.set(24n, D.Qn(m2, args), ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, regs2, 22n, args), m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, hk, {==}, {==}, {==}, {==}, {==}, {==}, {==}, ws.set(22n, args, ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, hk, {==}, {==}, {==}, {==}, {==}, {==}, {==}, w))), hl))))

# the round of a λ-match of labels: it takes a case on the first argument, or wres 2 or 3
def round.mat(+h: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +keep: List<&2, Nat>,
  +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +tc: U32, +tt: Bk.Term,
  +a: U32, +xs: List<&2, El.Arg>, +xs0: List<&2, D.TmpE>, +B: Nat, +hk: {D.Disj(keep, D.Walk.scr()) == True{} : Bool},
  +regs2: List<&2, U32>, +m2: Cr.Cir.Cells, +nx2: U32, +pg2: U32, +c: U32, +k: List<&2, Word(8n)>, +h0: Bk.Term, +n0: Bk.Term,
  +env: U32, +e: List<&2, El.Arg>, +args: U32, +ys: List<&2, El.Arg>, +pend2: U32, +ps2: List<&2, U32>,
  +w: WS(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, ys, pend2, ps2)) ->
  DW.WP(Mc.M.walk.mat(), h, X.X.st(regs2, m2, nx2, fi, im, pg2, lim, inp), u => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, u), B, lim):
  match ys:
    case Nil{}:
      r.nil(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, pend2, ps2, X.sel.a(Wm.e()), X.sel.b(Wm.e()), w, {==})
    case Con{El.Arg{+q0, +x0}, +rest}:
      r.con(h, regs2, m2, nx2, fi, im, pg2, lim, inp, u => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, u), B, args, X.sel.a(Wm.e()), X.sel.b(Wm.e()),
        wr.r21(regs, keep, regs2, c, env, List.length(&2, El.Arg, e), args, pend2, ws.wr(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, w)), ag.nz(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, x0, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, w))),
        mat.go(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, k, h0, n0, env, e, args, q0, x0, rest, pend2, ps2, w))

# The round of a λ-match of pairs
# --------------------------------
#
# walk.prj reads the first argument as walk.mat does: a live Tup is split
# into its fields; anything else, wres 3.

def Wp.e() -> Cr.Cir.Stmt:
  X.sel.e(Mc.M.walk.prj())

def Wp.r1() -> Cr.Cir.Stmt:
  X.sel.b(Wp.e())

def Wp.r2() -> Cr.Cir.Stmt:
  X.sel.b(Wp.r1())

def Wp.r3() -> Cr.Cir.Stmt:
  X.sel.b(Wp.r2())

def Wp.tup() -> Cr.Cir.Stmt:
  X.sel.t(X.sel.a(Wp.r3()))

# the test of walk.prj, after the reads of the first argument: its term is
# a Tup and its quantity live
def prj.test(+regs2: List<&2, U32>, +m2: Cr.Cir.Cells, +nx2: U32, +fi: U32, +im: U32, +pg2: U32, +lim: U32, +inp: List<&2, Word(8n)>,
  +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +args: U32, +q0: Bk.Quan, +x0: Bk.Term,
  hl: {List.length(&2, U32, regs2) == 63n : Nat}, hq: D.Qs(Cr.Cir.Cells.get(m2, args), q0),
  +his: D.Is(ds, m2, im, fi, nx2, ks, img, D.Fd(2n, m2, args), x0)) ->
  {Cr.Cir.eval(Mc.M.and(Mc.M.ne(Mc.M.g(Mc.R.wq()), Mc.M.c(0)), Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wx())), Mc.M.c(Mc.T.tup()))), X.X.st(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), 23n, D.Fd(2n, m2, args)), m2, nx2, fi, im, pg2, lim, inp)) == Some{Bool.to_u32(Bool.and(U32.is_eq(D.A.tag(x0), 10), El.Quan.live(q0)))} : Maybe<&2, U32>}:
  +l3 = X.L.len(regs2, 22n, args, 63n, hl)
  +l4 = X.L.len(List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args), 63n, l3)
  +e24 = X.L.go(List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), 23n, 24n, D.Fd(2n, m2, args), D.Qn(m2, args), {==}, X.L.gs(List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args), X.L.lt(List.set(&2, U32, regs2, 22n, args), 24n, l3, {==})))
  +e23 = X.L.gs(List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), 23n, D.Fd(2n, m2, args), X.L.lt(List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), 23n, l4, {==}))
  +st5 = X.X.st(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), 23n, D.Fd(2n, m2, args)), m2, nx2, fi, im, pg2, lim, inp)
  +tg = D.Tg(m2, D.Fd(2n, m2, args))
  +ene = X.ev.op(Wa.Wasm.Op.ne{}, Mc.M.g(Mc.R.wq()), Mc.M.c(0), st5, D.Qn(m2, args), 0, e24, {==})
  +etg = X.ev.opw(Wa.Wasm.Op.and{}, Mc.M.f(0n, Mc.M.g(Mc.R.wx())), Mc.M.c(63), st5, D.Fd(0n, m2, D.Fd(2n, m2, args)), 63, tg,
    X.ev.fld(0n, Mc.M.g(Mc.R.wx()), st5, D.Fd(2n, m2, args), e23, is.cell(ds, m2, im, fi, nx2, ks, img, D.Fd(2n, m2, args), x0, his)), {==}, {==})
  +eeq = X.ev.op(Wa.Wasm.Op.eq{}, Mc.M.tag(Mc.M.g(Mc.R.wx())), Mc.M.c(Mc.T.tup()), st5, tg, 10, etg, {==})
  (%is.tg(ds, m2, im, fi, nx2, ks, img, D.Fd(2n, m2, args), x0, his) :
     {Cr.Cir.eval(Mc.M.and(Mc.M.ne(Mc.M.g(Mc.R.wq()), Mc.M.c(0)), Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wx())), Mc.M.c(Mc.T.tup()))), st5) == Some{Bool.to_u32(Bool.and(U32.is_eq(_, 10), El.Quan.live(q0)))} : Maybe<&2, U32>};
   %ne.quan(q0) : {Cr.Cir.eval(Mc.M.and(Mc.M.ne(Mc.M.g(Mc.R.wq()), Mc.M.c(0)), Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wx())), Mc.M.c(Mc.T.tup()))), st5) == Some{Bool.to_u32(Bool.and(U32.is_eq(tg, 10), _))} : Maybe<&2, U32>};
   %hq : {Cr.Cir.eval(Mc.M.and(Mc.M.ne(Mc.M.g(Mc.R.wq()), Mc.M.c(0)), Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wx())), Mc.M.c(Mc.T.tup()))), st5) == Some{Bool.to_u32(Bool.and(U32.is_eq(tg, 10), U32.is_ne(_, 0)))} : Maybe<&2, U32>};
   X.ev.opw(Wa.Wasm.Op.and{}, Mc.M.ne(Mc.M.g(Mc.R.wq()), Mc.M.c(0)), Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wx())), Mc.M.c(Mc.T.tup())), st5,
     Bool.to_u32(U32.is_ne(D.Qn(m2, args), 0)), Bool.to_u32(U32.is_eq(tg, 10)), Bool.to_u32(Bool.and(U32.is_eq(tg, 10), U32.is_ne(D.Qn(m2, args), 0))),
     ene, eeq, t.and.c(U32.is_ne(D.Qn(m2, args), 0), U32.is_eq(tg, 10))))

# the test fails: wres 3, and no walk exists
def prj.fail(+h: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +keep: List<&2, Nat>,
  +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +tc: U32, +tt: Bk.Term,
  +a: U32, +xs: List<&2, El.Arg>, +xs0: List<&2, D.TmpE>, +B: Nat, +hk: {D.Disj(keep, D.Walk.scr()) == True{} : Bool},
  +regs2: List<&2, U32>, +m2: Cr.Cir.Cells, +nx2: U32, +pg2: U32, +c: U32, +h0: Bk.Term,
  +env: U32, +e: List<&2, El.Arg>, +args: U32, +q0: Bk.Quan, +x0: Bk.Term, +rest: List<&2, El.Arg>, +pend2: U32, +ps2: List<&2, U32>,
  +w5: WS(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), 23n, D.Fd(2n, m2, args)), m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2),
  +b: Bool, hb: {b == False{} : Bool}, hc: {Cr.Cir.eval(Mc.M.and(Mc.M.ne(Mc.M.g(Mc.R.wq()), Mc.M.c(0)), Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wx())), Mc.M.c(Mc.T.tup()))), X.X.st(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), 23n, D.Fd(2n, m2, args)), m2, nx2, fi, im, pg2, lim, inp)) == Some{Bool.to_u32(b)} : Maybe<&2, U32>},
  hn: {El.Eval.walk(Bk.Term.Prj{h0}, D.Arg.terms(e), Con{El.Arg{q0, x0}, rest}) == None{} : Maybe<Maybe<Bk.Term>>}) ->
  DW.WP(X.sel.a(Wp.r3()), h, X.X.st(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), 23n, D.Fd(2n, m2, args)), m2, nx2, fi, im, pg2, lim, inp), t => DW.WP(Cr.Cir.Stmt.nop{}, h, t, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, lim):
  wp.if.be(Mc.M.set(Mc.R.wres(), Mc.M.c(3)), h, Mc.M.and(Mc.M.ne(Mc.M.g(Mc.R.wq()), Mc.M.c(0)), Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wx())), Mc.M.c(Mc.T.tup()))), Wp.tup(), X.X.st(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), 23n, D.Fd(2n, m2, args)), m2, nx2, fi, im, pg2, lim, inp), t => DW.WP(Cr.Cir.Stmt.nop{}, h, t, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, lim, b, {==}, hc, hb,
    wp.set.k(h, 26n, 3, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), 23n, D.Fd(2n, m2, args)), m2, nx2, fi, im, pg2, lim, inp, x => DW.WP(Cr.Cir.Stmt.nop{}, h, x, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B,
      wr.len(regs, keep, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), 23n, D.Fd(2n, m2, args)), c, env, List.length(&2, El.Arg, e), args, pend2, ws.wr(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), 23n, D.Fd(2n, m2, args)), m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, w5)), {==},
      Inr{ex.three(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), 23n, D.Fd(2n, m2, args)), m2, nx2, pg2, c, env, List.length(&2, El.Arg, e), args, pend2, ps2,
        ws.wr(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), 23n, D.Fd(2n, m2, args)), m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, w5), hk,
        Equal.trans(Maybe<Maybe<Bk.Term>>, El.Eval.walk(tt, Nil{}, xs), El.Eval.walk(Bk.Term.Prj{h0}, D.Arg.terms(e), Con{El.Arg{q0, x0}, rest}), None{},
          ws.ev(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), 23n, D.Fd(2n, m2, args)), m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, w5), hn),
        wh.kc(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), 23n, D.Fd(2n, m2, args)), m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, w5)), wh.st(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), 23n, D.Fd(2n, m2, args)), m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, w5)), wh.mem(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), 23n, D.Fd(2n, m2, args)), m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, w5)))}))

# the walk of a live pair: its split (Eval.walk's Prj rule, live)
def prj.ev(+h0: Bk.Term, +q0: Bk.Quan, +r1: Bk.Quan, +a1: Bk.Term, +b1: Bk.Term, +e: List<&2, Bk.Term>, +rest: List<&2, El.Arg>,
  hq: {El.Quan.live(q0) == True{} : Bool}) ->
  {El.Eval.walk(Bk.Term.Prj{h0}, e, Con{El.Arg{q0, Bk.Term.Tup{r1, a1, b1}}, rest}) ==
    El.Eval.walk(h0, e, Con{El.Arg{El.Quan.fld(r1, q0), a1}, Con{El.Arg{q0, b1}, rest}}) : Maybe<Maybe<Bk.Term>>}:
  (%Equal.sym(Bool, El.Quan.live(q0), True{}, hq) :
     {El.Eval.walk.if(_, El.Eval.walk(h0, e, Con{El.Arg{El.Quan.fld(r1, q0), a1}, Con{El.Arg{q0, b1}, rest}})) ==
      El.Eval.walk(h0, e, Con{El.Arg{El.Quan.fld(r1, q0), a1}, Con{El.Arg{q0, b1}, rest}}) : Maybe<Maybe<Bk.Term>>};
   {==})

# a live Tup: the test passes; its split
def prj.tup(+h: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +keep: List<&2, Nat>,
  +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +tc: U32, +tt: Bk.Term,
  +a: U32, +xs: List<&2, El.Arg>, +xs0: List<&2, D.TmpE>, +B: Nat, +hk: {D.Disj(keep, D.Walk.scr()) == True{} : Bool},
  +regs2: List<&2, U32>, +m2: Cr.Cir.Cells, +nx2: U32, +pg2: U32, +c: U32, +h0: Bk.Term,
  +env: U32, +e: List<&2, El.Arg>, +args: U32, +q0: Bk.Quan, +r1: Bk.Quan, +a1: Bk.Term, +b1: Bk.Term, +rest: List<&2, El.Arg>, +pend2: U32, +ps2: List<&2, U32>,
  +w5: WS(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), 23n, D.Fd(2n, m2, args)), m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Tup{r1, a1, b1}}, rest}, pend2, ps2),
  hq: {El.Quan.live(q0) == True{} : Bool}) ->
  DW.WP(Wp.tup(), h, X.X.st(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), 23n, D.Fd(2n, m2, args)), m2, nx2, fi, im, pg2, lim, inp), x => DW.WP(Cr.Cir.Stmt.nop{}, h, x, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, lim):
  ?TODO

def prj.tupq(+h: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +keep: List<&2, Nat>,
  +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +tc: U32, +tt: Bk.Term,
  +a: U32, +xs: List<&2, El.Arg>, +xs0: List<&2, D.TmpE>, +B: Nat, +hk: {D.Disj(keep, D.Walk.scr()) == True{} : Bool},
  +regs2: List<&2, U32>, +m2: Cr.Cir.Cells, +nx2: U32, +pg2: U32, +c: U32, +h0: Bk.Term,
  +env: U32, +e: List<&2, El.Arg>, +args: U32, +q0: Bk.Quan, +r1: Bk.Quan, +a1: Bk.Term, +b1: Bk.Term, +rest: List<&2, El.Arg>, +pend2: U32, +ps2: List<&2, U32>,
  +w: WS(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Tup{r1, a1, b1}}, rest}, pend2, ps2),
  +w5: WS(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), 23n, D.Fd(2n, m2, args)), m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Tup{r1, a1, b1}}, rest}, pend2, ps2),
  +hl: {List.length(&2, U32, regs2) == 63n : Nat}) ->
  DW.WP(X.sel.a(Wp.r3()), h, X.X.st(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), 23n, D.Fd(2n, m2, args)), m2, nx2, fi, im, pg2, lim, inp), t => DW.WP(Cr.Cir.Stmt.nop{}, h, t, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, lim):
  match q0:
    case Bk.Quan.Q0{}:
      prj.fail(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, h0, env, e, args, Bk.Quan.Q0{}, Bk.Term.Tup{r1, a1, b1}, rest, pend2, ps2, w5, Bool.and(U32.is_eq(D.A.tag(Bk.Term.Tup{r1, a1, b1}), 10), El.Quan.live(Bk.Quan.Q0{})), {==},
        prj.test(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, args, Bk.Quan.Q0{}, Bk.Term.Tup{r1, a1, b1}, hl, ag.qs(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, Bk.Quan.Q0{}, Bk.Term.Tup{r1, a1, b1}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{Bk.Quan.Q0{}, Bk.Term.Tup{r1, a1, b1}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{Bk.Quan.Q0{}, Bk.Term.Tup{r1, a1, b1}}, rest}, pend2, ps2, w))), ag.is(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, Bk.Quan.Q0{}, Bk.Term.Tup{r1, a1, b1}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{Bk.Quan.Q0{}, Bk.Term.Tup{r1, a1, b1}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{Bk.Quan.Q0{}, Bk.Term.Tup{r1, a1, b1}}, rest}, pend2, ps2, w)))), {==})
    case Bk.Quan.Q1{}:
      wp.if.bt(Mc.M.set(Mc.R.wres(), Mc.M.c(3)), h, Mc.M.and(Mc.M.ne(Mc.M.g(Mc.R.wq()), Mc.M.c(0)), Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wx())), Mc.M.c(Mc.T.tup()))), Wp.tup(), X.X.st(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), 23n, D.Fd(2n, m2, args)), m2, nx2, fi, im, pg2, lim, inp), t => DW.WP(Cr.Cir.Stmt.nop{}, h, t, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, lim,
        Bool.and(U32.is_eq(D.A.tag(Bk.Term.Tup{r1, a1, b1}), 10), El.Quan.live(Bk.Quan.Q1{})), {==}, prj.test(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, args, Bk.Quan.Q1{}, Bk.Term.Tup{r1, a1, b1}, hl, ag.qs(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, Bk.Quan.Q1{}, Bk.Term.Tup{r1, a1, b1}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{Bk.Quan.Q1{}, Bk.Term.Tup{r1, a1, b1}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{Bk.Quan.Q1{}, Bk.Term.Tup{r1, a1, b1}}, rest}, pend2, ps2, w))), ag.is(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, Bk.Quan.Q1{}, Bk.Term.Tup{r1, a1, b1}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{Bk.Quan.Q1{}, Bk.Term.Tup{r1, a1, b1}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{Bk.Quan.Q1{}, Bk.Term.Tup{r1, a1, b1}}, rest}, pend2, ps2, w)))), {==},
        prj.tup(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, h0, env, e, args, Bk.Quan.Q1{}, r1, a1, b1, rest, pend2, ps2, w5, {==}))
    case Bk.Quan.Q2{}:
      wp.if.bt(Mc.M.set(Mc.R.wres(), Mc.M.c(3)), h, Mc.M.and(Mc.M.ne(Mc.M.g(Mc.R.wq()), Mc.M.c(0)), Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wx())), Mc.M.c(Mc.T.tup()))), Wp.tup(), X.X.st(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), 23n, D.Fd(2n, m2, args)), m2, nx2, fi, im, pg2, lim, inp), t => DW.WP(Cr.Cir.Stmt.nop{}, h, t, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, lim,
        Bool.and(U32.is_eq(D.A.tag(Bk.Term.Tup{r1, a1, b1}), 10), El.Quan.live(Bk.Quan.Q2{})), {==}, prj.test(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, args, Bk.Quan.Q2{}, Bk.Term.Tup{r1, a1, b1}, hl, ag.qs(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, Bk.Quan.Q2{}, Bk.Term.Tup{r1, a1, b1}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{Bk.Quan.Q2{}, Bk.Term.Tup{r1, a1, b1}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{Bk.Quan.Q2{}, Bk.Term.Tup{r1, a1, b1}}, rest}, pend2, ps2, w))), ag.is(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, Bk.Quan.Q2{}, Bk.Term.Tup{r1, a1, b1}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{Bk.Quan.Q2{}, Bk.Term.Tup{r1, a1, b1}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{Bk.Quan.Q2{}, Bk.Term.Tup{r1, a1, b1}}, rest}, pend2, ps2, w)))), {==},
        prj.tup(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, h0, env, e, args, Bk.Quan.Q2{}, r1, a1, b1, rest, pend2, ps2, w5, {==}))

# the test of walk.prj, by the first argument's form and quantity
def prj.if(+h: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +keep: List<&2, Nat>,
  +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +tc: U32, +tt: Bk.Term,
  +a: U32, +xs: List<&2, El.Arg>, +xs0: List<&2, D.TmpE>, +B: Nat, +hk: {D.Disj(keep, D.Walk.scr()) == True{} : Bool},
  +regs2: List<&2, U32>, +m2: Cr.Cir.Cells, +nx2: U32, +pg2: U32, +c: U32, +h0: Bk.Term,
  +env: U32, +e: List<&2, El.Arg>, +args: U32, +q0: Bk.Quan, +x0: Bk.Term, +rest: List<&2, El.Arg>, +pend2: U32, +ps2: List<&2, U32>,
  +w: WS(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2),
  +w5: WS(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), 23n, D.Fd(2n, m2, args)), m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2),
  +hl: {List.length(&2, U32, regs2) == 63n : Nat}) ->
  DW.WP(X.sel.a(Wp.r3()), h, X.X.st(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), 23n, D.Fd(2n, m2, args)), m2, nx2, fi, im, pg2, lim, inp), t => DW.WP(Cr.Cir.Stmt.nop{}, h, t, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, lim):
  match x0:
    case Bk.Term.Var{+i}:
      prj.fail(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, h0, env, e, args, q0, Bk.Term.Var{i}, rest, pend2, ps2, w5, Bool.and(U32.is_eq(D.A.tag(Bk.Term.Var{i}), 10), El.Quan.live(q0)), {==},
        prj.test(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, args, q0, Bk.Term.Var{i}, hl, ag.qs(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Var{i}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Var{i}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Var{i}}, rest}, pend2, ps2, w))), ag.is(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Var{i}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Var{i}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Var{i}}, rest}, pend2, ps2, w)))), {==})
    case Bk.Term.Ref{+kk}:
      prj.fail(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, h0, env, e, args, q0, Bk.Term.Ref{kk}, rest, pend2, ps2, w5, Bool.and(U32.is_eq(D.A.tag(Bk.Term.Ref{kk}), 10), El.Quan.live(q0)), {==},
        prj.test(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, args, q0, Bk.Term.Ref{kk}, hl, ag.qs(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Ref{kk}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Ref{kk}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Ref{kk}}, rest}, pend2, ps2, w))), ag.is(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Ref{kk}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Ref{kk}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Ref{kk}}, rest}, pend2, ps2, w)))), {==})
    case Bk.Term.Ann{+y1, +y2}:
      prj.fail(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, h0, env, e, args, q0, Bk.Term.Ann{y1, y2}, rest, pend2, ps2, w5, Bool.and(U32.is_eq(D.A.tag(Bk.Term.Ann{y1, y2}), 10), El.Quan.live(q0)), {==},
        prj.test(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, args, q0, Bk.Term.Ann{y1, y2}, hl, ag.qs(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Ann{y1, y2}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Ann{y1, y2}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Ann{y1, y2}}, rest}, pend2, ps2, w))), ag.is(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Ann{y1, y2}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Ann{y1, y2}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Ann{y1, y2}}, rest}, pend2, ps2, w)))), {==})
    case Bk.Term.Let{+q1, +v1, +f1}:
      prj.fail(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, h0, env, e, args, q0, Bk.Term.Let{q1, v1, f1}, rest, pend2, ps2, w5, Bool.and(U32.is_eq(D.A.tag(Bk.Term.Let{q1, v1, f1}), 10), El.Quan.live(q0)), {==},
        prj.test(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, args, q0, Bk.Term.Let{q1, v1, f1}, hl, ag.qs(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Let{q1, v1, f1}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Let{q1, v1, f1}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Let{q1, v1, f1}}, rest}, pend2, ps2, w))), ag.is(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Let{q1, v1, f1}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Let{q1, v1, f1}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Let{q1, v1, f1}}, rest}, pend2, ps2, w)))), {==})
    case Bk.Term.Typ{+y1}:
      prj.fail(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, h0, env, e, args, q0, Bk.Term.Typ{y1}, rest, pend2, ps2, w5, Bool.and(U32.is_eq(D.A.tag(Bk.Term.Typ{y1}), 10), El.Quan.live(q0)), {==},
        prj.test(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, args, q0, Bk.Term.Typ{y1}, hl, ag.qs(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Typ{y1}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Typ{y1}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Typ{y1}}, rest}, pend2, ps2, w))), ag.is(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Typ{y1}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Typ{y1}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Typ{y1}}, rest}, pend2, ps2, w)))), {==})
    case Bk.Term.Min{+y1, +y2}:
      prj.fail(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, h0, env, e, args, q0, Bk.Term.Min{y1, y2}, rest, pend2, ps2, w5, Bool.and(U32.is_eq(D.A.tag(Bk.Term.Min{y1, y2}), 10), El.Quan.live(q0)), {==},
        prj.test(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, args, q0, Bk.Term.Min{y1, y2}, hl, ag.qs(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Min{y1, y2}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Min{y1, y2}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Min{y1, y2}}, rest}, pend2, ps2, w))), ag.is(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Min{y1, y2}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Min{y1, y2}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Min{y1, y2}}, rest}, pend2, ps2, w)))), {==})
    case Bk.Term.All{+q1, +y1, +y2}:
      prj.fail(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, h0, env, e, args, q0, Bk.Term.All{q1, y1, y2}, rest, pend2, ps2, w5, Bool.and(U32.is_eq(D.A.tag(Bk.Term.All{q1, y1, y2}), 10), El.Quan.live(q0)), {==},
        prj.test(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, args, q0, Bk.Term.All{q1, y1, y2}, hl, ag.qs(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.All{q1, y1, y2}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.All{q1, y1, y2}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.All{q1, y1, y2}}, rest}, pend2, ps2, w))), ag.is(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.All{q1, y1, y2}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.All{q1, y1, y2}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.All{q1, y1, y2}}, rest}, pend2, ps2, w)))), {==})
    case Bk.Term.Lam{+q1, +f1}:
      prj.fail(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, h0, env, e, args, q0, Bk.Term.Lam{q1, f1}, rest, pend2, ps2, w5, Bool.and(U32.is_eq(D.A.tag(Bk.Term.Lam{q1, f1}), 10), El.Quan.live(q0)), {==},
        prj.test(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, args, q0, Bk.Term.Lam{q1, f1}, hl, ag.qs(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Lam{q1, f1}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Lam{q1, f1}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Lam{q1, f1}}, rest}, pend2, ps2, w))), ag.is(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Lam{q1, f1}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Lam{q1, f1}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Lam{q1, f1}}, rest}, pend2, ps2, w)))), {==})
    case Bk.Term.App{+q1, +f1, +y1}:
      prj.fail(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, h0, env, e, args, q0, Bk.Term.App{q1, f1, y1}, rest, pend2, ps2, w5, Bool.and(U32.is_eq(D.A.tag(Bk.Term.App{q1, f1, y1}), 10), El.Quan.live(q0)), {==},
        prj.test(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, args, q0, Bk.Term.App{q1, f1, y1}, hl, ag.qs(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.App{q1, f1, y1}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.App{q1, f1, y1}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.App{q1, f1, y1}}, rest}, pend2, ps2, w))), ag.is(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.App{q1, f1, y1}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.App{q1, f1, y1}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.App{q1, f1, y1}}, rest}, pend2, ps2, w)))), {==})
    case Bk.Term.Sig{+q1, +y1, +y2}:
      prj.fail(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, h0, env, e, args, q0, Bk.Term.Sig{q1, y1, y2}, rest, pend2, ps2, w5, Bool.and(U32.is_eq(D.A.tag(Bk.Term.Sig{q1, y1, y2}), 10), El.Quan.live(q0)), {==},
        prj.test(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, args, q0, Bk.Term.Sig{q1, y1, y2}, hl, ag.qs(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Sig{q1, y1, y2}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Sig{q1, y1, y2}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Sig{q1, y1, y2}}, rest}, pend2, ps2, w))), ag.is(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Sig{q1, y1, y2}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Sig{q1, y1, y2}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Sig{q1, y1, y2}}, rest}, pend2, ps2, w)))), {==})
    case Bk.Term.Lab{+kk}:
      prj.fail(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, h0, env, e, args, q0, Bk.Term.Lab{kk}, rest, pend2, ps2, w5, Bool.and(U32.is_eq(D.A.tag(Bk.Term.Lab{kk}), 10), El.Quan.live(q0)), {==},
        prj.test(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, args, q0, Bk.Term.Lab{kk}, hl, ag.qs(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Lab{kk}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Lab{kk}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Lab{kk}}, rest}, pend2, ps2, w))), ag.is(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Lab{kk}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Lab{kk}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Lab{kk}}, rest}, pend2, ps2, w)))), {==})
    case Bk.Term.Prj{+h1}:
      prj.fail(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, h0, env, e, args, q0, Bk.Term.Prj{h1}, rest, pend2, ps2, w5, Bool.and(U32.is_eq(D.A.tag(Bk.Term.Prj{h1}), 10), El.Quan.live(q0)), {==},
        prj.test(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, args, q0, Bk.Term.Prj{h1}, hl, ag.qs(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Prj{h1}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Prj{h1}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Prj{h1}}, rest}, pend2, ps2, w))), ag.is(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Prj{h1}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Prj{h1}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Prj{h1}}, rest}, pend2, ps2, w)))), {==})
    case Bk.Term.Enu{+kk}:
      prj.fail(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, h0, env, e, args, q0, Bk.Term.Enu{kk}, rest, pend2, ps2, w5, Bool.and(U32.is_eq(D.A.tag(Bk.Term.Enu{kk}), 10), El.Quan.live(q0)), {==},
        prj.test(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, args, q0, Bk.Term.Enu{kk}, hl, ag.qs(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Enu{kk}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Enu{kk}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Enu{kk}}, rest}, pend2, ps2, w))), ag.is(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Enu{kk}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Enu{kk}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Enu{kk}}, rest}, pend2, ps2, w)))), {==})
    case Bk.Term.Mat{+kk, +h1, +n1}:
      prj.fail(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, h0, env, e, args, q0, Bk.Term.Mat{kk, h1, n1}, rest, pend2, ps2, w5, Bool.and(U32.is_eq(D.A.tag(Bk.Term.Mat{kk, h1, n1}), 10), El.Quan.live(q0)), {==},
        prj.test(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, args, q0, Bk.Term.Mat{kk, h1, n1}, hl, ag.qs(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Mat{kk, h1, n1}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Mat{kk, h1, n1}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Mat{kk, h1, n1}}, rest}, pend2, ps2, w))), ag.is(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Mat{kk, h1, n1}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Mat{kk, h1, n1}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Mat{kk, h1, n1}}, rest}, pend2, ps2, w)))), {==})
    case Bk.Term.Efq{}:
      prj.fail(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, h0, env, e, args, q0, Bk.Term.Efq{}, rest, pend2, ps2, w5, Bool.and(U32.is_eq(D.A.tag(Bk.Term.Efq{}), 10), El.Quan.live(q0)), {==},
        prj.test(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, args, q0, Bk.Term.Efq{}, hl, ag.qs(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Efq{}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Efq{}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Efq{}}, rest}, pend2, ps2, w))), ag.is(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Efq{}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Efq{}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Efq{}}, rest}, pend2, ps2, w)))), {==})
    case Bk.Term.Eql{+y1, +y2, +y3}:
      prj.fail(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, h0, env, e, args, q0, Bk.Term.Eql{y1, y2, y3}, rest, pend2, ps2, w5, Bool.and(U32.is_eq(D.A.tag(Bk.Term.Eql{y1, y2, y3}), 10), El.Quan.live(q0)), {==},
        prj.test(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, args, q0, Bk.Term.Eql{y1, y2, y3}, hl, ag.qs(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Eql{y1, y2, y3}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Eql{y1, y2, y3}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Eql{y1, y2, y3}}, rest}, pend2, ps2, w))), ag.is(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Eql{y1, y2, y3}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Eql{y1, y2, y3}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Eql{y1, y2, y3}}, rest}, pend2, ps2, w)))), {==})
    case Bk.Term.Rfl{}:
      prj.fail(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, h0, env, e, args, q0, Bk.Term.Rfl{}, rest, pend2, ps2, w5, Bool.and(U32.is_eq(D.A.tag(Bk.Term.Rfl{}), 10), El.Quan.live(q0)), {==},
        prj.test(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, args, q0, Bk.Term.Rfl{}, hl, ag.qs(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Rfl{}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Rfl{}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Rfl{}}, rest}, pend2, ps2, w))), ag.is(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Rfl{}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Rfl{}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Rfl{}}, rest}, pend2, ps2, w)))), {==})
    case Bk.Term.Rwt{+y1, +y2, +y3}:
      prj.fail(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, h0, env, e, args, q0, Bk.Term.Rwt{y1, y2, y3}, rest, pend2, ps2, w5, Bool.and(U32.is_eq(D.A.tag(Bk.Term.Rwt{y1, y2, y3}), 10), El.Quan.live(q0)), {==},
        prj.test(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, args, q0, Bk.Term.Rwt{y1, y2, y3}, hl, ag.qs(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Rwt{y1, y2, y3}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Rwt{y1, y2, y3}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Rwt{y1, y2, y3}}, rest}, pend2, ps2, w))), ag.is(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, Bk.Term.Rwt{y1, y2, y3}, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Rwt{y1, y2, y3}}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, Bk.Term.Rwt{y1, y2, y3}}, rest}, pend2, ps2, w)))), {==})
    case Bk.Term.Tup{+r1, +a1, +b1}:
      prj.tupq(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, h0, env, e, args, q0, r1, a1, b1, rest, pend2, ps2, w, w5, hl)


# walk.prj with an argument: the reads of its K.arg, then the test
def prj.go(+h: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +keep: List<&2, Nat>,
  +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +tc: U32, +tt: Bk.Term,
  +a: U32, +xs: List<&2, El.Arg>, +xs0: List<&2, D.TmpE>, +B: Nat, +hk: {D.Disj(keep, D.Walk.scr()) == True{} : Bool},
  +regs2: List<&2, U32>, +m2: Cr.Cir.Cells, +nx2: U32, +pg2: U32, +c: U32, +h0: Bk.Term,
  +env: U32, +e: List<&2, El.Arg>, +args: U32, +q0: Bk.Quan, +x0: Bk.Term, +rest: List<&2, El.Arg>, +pend2: U32, +ps2: List<&2, U32>,
  +w: WS(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2)) ->
  DW.WP(Cr.Cir.Stmt.seq{X.sel.a(Wp.e()), X.sel.b(Wp.e())}, h, X.X.st(regs2, m2, nx2, fi, im, pg2, lim, inp), x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim):
  +hl = wr.len(regs, keep, regs2, c, env, List.length(&2, El.Arg, e), args, pend2, ws.wr(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, w))
  +l3 = X.L.len(regs2, 22n, args, 63n, hl)
  +l4 = X.L.len(List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args), 63n, l3)
  +hca = ag.cell(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, x0, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, w)))
  +e22 = X.L.gs(regs2, 22n, args, X.L.lt(regs2, 22n, hl, {==}))
  +eq = X.ev.opw(Wa.Wasm.Op.and{}, Mc.M.shr(Mc.M.f(0n, Mc.M.g(Mc.R.wa())), Mc.M.c(6)), Mc.M.c(3), X.X.st(List.set(&2, U32, regs2, 22n, args), m2, nx2, fi, im, pg2, lim, inp),
    Wa.Wasm.op(Wa.Wasm.Op.shr_u{}, D.Fd(0n, m2, args), 6), 3, D.Qn(m2, args),
    X.ev.op(Wa.Wasm.Op.shr_u{}, Mc.M.f(0n, Mc.M.g(Mc.R.wa())), Mc.M.c(6), X.X.st(List.set(&2, U32, regs2, 22n, args), m2, nx2, fi, im, pg2, lim, inp), D.Fd(0n, m2, args), 6,
      X.ev.fld(0n, Mc.M.g(Mc.R.wa()), X.X.st(List.set(&2, U32, regs2, 22n, args), m2, nx2, fi, im, pg2, lim, inp), args, e22, hca), {==}), {==}, {==})
  +ex = X.ev.fld(2n, Mc.M.g(Mc.R.wa()), X.X.st(List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), m2, nx2, fi, im, pg2, lim, inp), args, X.L.go(List.set(&2, U32, regs2, 22n, args), 24n, 22n, D.Qn(m2, args), args, {==}, e22), hca)
  wp.set.e(22n, Mc.M.g(Mc.R.wargs()), args, regs2, m2, nx2, fi, im, pg2, lim, inp, h, t => DW.WP(Wp.r1(), h, t, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B,
    wr.r21(regs, keep, regs2, c, env, List.length(&2, El.Arg, e), args, pend2, ws.wr(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, w)), hl, {==},
    wp.set.e(24n, Mc.M.q(Mc.M.g(Mc.R.wa())), D.Qn(m2, args), List.set(&2, U32, regs2, 22n, args), m2, nx2, fi, im, pg2, lim, inp, h, t => DW.WP(Wp.r2(), h, t, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B,
      eq, l3, {==},
      wp.set.e(23n, Mc.M.f(2n, Mc.M.g(Mc.R.wa())), D.Fd(2n, m2, args), List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), m2, nx2, fi, im, pg2, lim, inp, h, t => DW.WP(Wp.r3(), h, t, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B,
        ex, l4, {==},
        prj.if(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, h0, env, e, args, q0, x0, rest, pend2, ps2, w, ws.set(23n, D.Fd(2n, m2, args), ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, D.Qn(m2, args)), m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, hk, {==}, {==}, {==}, {==}, {==}, {==}, {==}, ws.set(24n, D.Qn(m2, args), ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, regs2, 22n, args), m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, hk, {==}, {==}, {==}, {==}, {==}, {==}, {==}, ws.set(22n, args, ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, hk, {==}, {==}, {==}, {==}, {==}, {==}, {==}, w))), hl))))

# the round of a λ-match of pairs: it splits the first argument, or wres 2 or 3
def round.prj(+h: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +keep: List<&2, Nat>,
  +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +tc: U32, +tt: Bk.Term,
  +a: U32, +xs: List<&2, El.Arg>, +xs0: List<&2, D.TmpE>, +B: Nat, +hk: {D.Disj(keep, D.Walk.scr()) == True{} : Bool},
  +regs2: List<&2, U32>, +m2: Cr.Cir.Cells, +nx2: U32, +pg2: U32, +c: U32, +h0: Bk.Term,
  +env: U32, +e: List<&2, El.Arg>, +args: U32, +ys: List<&2, El.Arg>, +pend2: U32, +ps2: List<&2, U32>,
  +w: WS(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, ys, pend2, ps2)) ->
  DW.WP(Mc.M.walk.prj(), h, X.X.st(regs2, m2, nx2, fi, im, pg2, lim, inp), u => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, u), B, lim):
  match ys:
    case Nil{}:
      r.nil(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, Bk.Term.Prj{h0}, env, e, args, pend2, ps2, X.sel.a(Wp.e()), X.sel.b(Wp.e()), w, {==})
    case Con{El.Arg{+q0, +x0}, +rest}:
      r.con(h, regs2, m2, nx2, fi, im, pg2, lim, inp, u => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, u), B, args, X.sel.a(Wp.e()), X.sel.b(Wp.e()),
        wr.r21(regs, keep, regs2, c, env, List.length(&2, El.Arg, e), args, pend2, ws.wr(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, w)), ag.nz(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, x0, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, w))),
        prj.go(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, h0, env, e, args, q0, x0, rest, pend2, ps2, w))

# The round of a λ
# ----------------
#
# walk.lam reads the first argument as walk.mat does, and wok: the λ and
# the argument both live or both dead. A λ of quantity 2 checks that the
# argument is Data (M.data) for wok; with wok the argument becomes a local,
# else wres 3.

def Wl.e() -> Cr.Cir.Stmt:
  X.sel.e(Mc.M.walk.lam())

def Wl.r1() -> Cr.Cir.Stmt:
  X.sel.b(Wl.e())

def Wl.r2() -> Cr.Cir.Stmt:
  X.sel.b(Wl.r1())

def Wl.r3() -> Cr.Cir.Stmt:
  X.sel.b(Wl.r2())

def Wl.r4() -> Cr.Cir.Stmt:
  X.sel.b(Wl.r3())

def Wl.r5() -> Cr.Cir.Stmt:
  X.sel.b(Wl.r4())

# the quantity of a λ's cell
def is.lam.qs(-ds: List<&2, Bk.Def>, -m: Cr.Cir.Cells, -im: U32, -fi: U32, -nx: U32, -ks: List<&2, List<&2, Word(8n)>>,
  -img: List<&2, Bk.Term>, -c: U32, -p: Bk.Quan, -f: Bk.Term, h: D.Is(ds, m, im, fi, nx, ks, img, c, Bk.Term.Lam{p, f})) ->
  D.Qs(Cr.Cir.Cells.get(m, c), p):
  (_, h1) = h
  (y, _) = h1
  y

# the quantity of the argument's K.arg, as walk.lam reads it
def lam.q(+regs2: List<&2, U32>, +m2: Cr.Cir.Cells, +nx2: U32, +fi: U32, +im: U32, +pg2: U32, +lim: U32, +inp: List<&2, Word(8n)>,
  +args: U32, +q0: Bk.Quan, hl: {List.length(&2, U32, regs2) == 63n : Nat}, hca: {Cr.Cir.is_cell(args, im, fi, nx2) == True{} : Bool},
  hq: D.Qs(Cr.Cir.Cells.get(m2, args), q0)) ->
  {Cr.Cir.eval(Mc.M.q(Mc.M.g(Mc.R.wa())), X.X.st(List.set(&2, U32, regs2, 22n, args), m2, nx2, fi, im, pg2, lim, inp)) == Some{Mc.Img.quan(q0)} : Maybe<&2, U32>}:
  (%hq : {Cr.Cir.eval(Mc.M.q(Mc.M.g(Mc.R.wa())), X.X.st(List.set(&2, U32, regs2, 22n, args), m2, nx2, fi, im, pg2, lim, inp)) == Some{_} : Maybe<&2, U32>};
   X.ev.opw(Wa.Wasm.Op.and{}, Mc.M.shr(Mc.M.f(0n, Mc.M.g(Mc.R.wa())), Mc.M.c(6)), Mc.M.c(3), X.X.st(List.set(&2, U32, regs2, 22n, args), m2, nx2, fi, im, pg2, lim, inp),
     Wa.Wasm.op(Wa.Wasm.Op.shr_u{}, D.Fd(0n, m2, args), 6), 3, D.Qn(m2, args),
     X.ev.op(Wa.Wasm.Op.shr_u{}, Mc.M.f(0n, Mc.M.g(Mc.R.wa())), Mc.M.c(6), X.X.st(List.set(&2, U32, regs2, 22n, args), m2, nx2, fi, im, pg2, lim, inp), D.Fd(0n, m2, args), 6,
       X.ev.fld(0n, Mc.M.g(Mc.R.wa()), X.X.st(List.set(&2, U32, regs2, 22n, args), m2, nx2, fi, im, pg2, lim, inp), args, X.L.gs(regs2, 22n, args, X.L.lt(regs2, 22n, hl, {==})), hca), {==}), {==}, {==}))

# the λ's quantity, as walk.lam reads it from wt
def lam.p(+rr: List<&2, U32>, +m2: Cr.Cir.Cells, +nx2: U32, +fi: U32, +im: U32, +pg2: U32, +lim: U32, +inp: List<&2, Word(8n)>,
  +c: U32, +p: Bk.Quan, h19: {List.get(&2, U32, rr, 19n) == Some{c} : Maybe<&2, U32>}, hc: {Cr.Cir.is_cell(c, im, fi, nx2) == True{} : Bool},
  hq: D.Qs(Cr.Cir.Cells.get(m2, c), p)) ->
  {Cr.Cir.eval(Mc.M.q(Mc.M.g(Mc.R.wt())), X.X.st(rr, m2, nx2, fi, im, pg2, lim, inp)) == Some{Mc.Img.quan(p)} : Maybe<&2, U32>}:
  (%hq : {Cr.Cir.eval(Mc.M.q(Mc.M.g(Mc.R.wt())), X.X.st(rr, m2, nx2, fi, im, pg2, lim, inp)) == Some{_} : Maybe<&2, U32>};
   X.ev.opw(Wa.Wasm.Op.and{}, Mc.M.shr(Mc.M.f(0n, Mc.M.g(Mc.R.wt())), Mc.M.c(6)), Mc.M.c(3), X.X.st(rr, m2, nx2, fi, im, pg2, lim, inp),
     Wa.Wasm.op(Wa.Wasm.Op.shr_u{}, D.Fd(0n, m2, c), 6), 3, D.Qn(m2, c),
     X.ev.op(Wa.Wasm.Op.shr_u{}, Mc.M.f(0n, Mc.M.g(Mc.R.wt())), Mc.M.c(6), X.X.st(rr, m2, nx2, fi, im, pg2, lim, inp), D.Fd(0n, m2, c), 6,
       X.ev.fld(0n, Mc.M.g(Mc.R.wt()), X.X.st(rr, m2, nx2, fi, im, pg2, lim, inp), c, h19, hc), {==}), {==}, {==}))

# wok: the λ and the argument both live or both dead
def lam.ok(+regs2: List<&2, U32>, +m2: Cr.Cir.Cells, +nx2: U32, +fi: U32, +im: U32, +pg2: U32, +lim: U32, +inp: List<&2, Word(8n)>,
  +c: U32, +p: Bk.Quan, +args: U32, +q0: Bk.Quan, hl: {List.length(&2, U32, regs2) == 63n : Nat},
  h19: {List.get(&2, U32, regs2, 19n) == Some{c} : Maybe<&2, U32>}, hc: {Cr.Cir.is_cell(c, im, fi, nx2) == True{} : Bool},
  hq: D.Qs(Cr.Cir.Cells.get(m2, c), p)) ->
  {Cr.Cir.eval(Mc.M.eq(Mc.M.ne(Mc.M.q(Mc.M.g(Mc.R.wt())), Mc.M.c(0)), Mc.M.ne(Mc.M.g(Mc.R.wq()), Mc.M.c(0))), X.X.st(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(q0)), 23n, D.Fd(2n, m2, args)), m2, nx2, fi, im, pg2, lim, inp)) == Some{Bool.to_u32(U32.is_eq(Bool.to_u32(El.Quan.live(p)), Bool.to_u32(El.Quan.live(q0))))} : Maybe<&2, U32>}:
  +l3 = X.L.len(regs2, 22n, args, 63n, hl)
  +l4 = X.L.len(List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(q0), 63n, l3)
  +e19 = X.L.go(List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(q0)), 23n, 19n, D.Fd(2n, m2, args), c, {==}, X.L.go(List.set(&2, U32, regs2, 22n, args), 24n, 19n, Mc.Img.quan(q0), c, {==}, X.L.go(regs2, 22n, 19n, args, c, {==}, h19)))
  +e24 = X.L.go(List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(q0)), 23n, 24n, D.Fd(2n, m2, args), Mc.Img.quan(q0), {==}, X.L.gs(List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(q0), X.L.lt(List.set(&2, U32, regs2, 22n, args), 24n, l3, {==})))
  +st5 = X.X.st(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(q0)), 23n, D.Fd(2n, m2, args)), m2, nx2, fi, im, pg2, lim, inp)
  (%ne.quan(p) : {Cr.Cir.eval(Mc.M.eq(Mc.M.ne(Mc.M.q(Mc.M.g(Mc.R.wt())), Mc.M.c(0)), Mc.M.ne(Mc.M.g(Mc.R.wq()), Mc.M.c(0))), st5) == Some{Bool.to_u32(U32.is_eq(Bool.to_u32(_), Bool.to_u32(El.Quan.live(q0))))} : Maybe<&2, U32>};
   %ne.quan(q0) : {Cr.Cir.eval(Mc.M.eq(Mc.M.ne(Mc.M.q(Mc.M.g(Mc.R.wt())), Mc.M.c(0)), Mc.M.ne(Mc.M.g(Mc.R.wq()), Mc.M.c(0))), st5) == Some{Bool.to_u32(U32.is_eq(Bool.to_u32(U32.is_ne(Mc.Img.quan(p), 0)), Bool.to_u32(_)))} : Maybe<&2, U32>};
   X.ev.op(Wa.Wasm.Op.eq{}, Mc.M.ne(Mc.M.q(Mc.M.g(Mc.R.wt())), Mc.M.c(0)), Mc.M.ne(Mc.M.g(Mc.R.wq()), Mc.M.c(0)), st5,
     Bool.to_u32(U32.is_ne(Mc.Img.quan(p), 0)), Bool.to_u32(U32.is_ne(Mc.Img.quan(q0), 0)),
     X.ev.op(Wa.Wasm.Op.ne{}, Mc.M.q(Mc.M.g(Mc.R.wt())), Mc.M.c(0), st5, Mc.Img.quan(p), 0,
       lam.p(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(q0)), 23n, D.Fd(2n, m2, args)), m2, nx2, fi, im, pg2, lim, inp, c, p, e19, hc, hq), {==}),
     X.ev.op(Wa.Wasm.Op.ne{}, Mc.M.g(Mc.R.wq()), Mc.M.c(0), st5, Mc.Img.quan(q0), 0, e24, {==})))

# the test of the data check: wok, and the λ's quantity is 2
def lam.t1(+regs2: List<&2, U32>, +m2: Cr.Cir.Cells, +nx2: U32, +fi: U32, +im: U32, +pg2: U32, +lim: U32, +inp: List<&2, Word(8n)>,
  +c: U32, +p: Bk.Quan, +args: U32, +q0: Bk.Quan, hl: {List.length(&2, U32, regs2) == 63n : Nat},
  h19: {List.get(&2, U32, regs2, 19n) == Some{c} : Maybe<&2, U32>}, hc: {Cr.Cir.is_cell(c, im, fi, nx2) == True{} : Bool},
  hq: D.Qs(Cr.Cir.Cells.get(m2, c), p)) ->
  {Cr.Cir.eval(Mc.M.and(Mc.M.g(Mc.R.wok()), Mc.M.eq(Mc.M.q(Mc.M.g(Mc.R.wt())), Mc.M.c(2))), X.X.st(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(q0)), 23n, D.Fd(2n, m2, args)), 27n, Bool.to_u32(U32.is_eq(Bool.to_u32(El.Quan.live(p)), Bool.to_u32(El.Quan.live(q0))))), m2, nx2, fi, im, pg2, lim, inp)) == Some{U32.and(Bool.to_u32(U32.is_eq(Bool.to_u32(El.Quan.live(p)), Bool.to_u32(El.Quan.live(q0)))), Bool.to_u32(U32.is_eq(Mc.Img.quan(p), 2)))} : Maybe<&2, U32>}:
  +l3 = X.L.len(regs2, 22n, args, 63n, hl)
  +l4 = X.L.len(List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(q0), 63n, l3)
  +l5 = X.L.len(List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(q0)), 23n, D.Fd(2n, m2, args), 63n, l4)
  +e19 = X.L.go(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(q0)), 23n, D.Fd(2n, m2, args)), 27n, 19n, Bool.to_u32(U32.is_eq(Bool.to_u32(El.Quan.live(p)), Bool.to_u32(El.Quan.live(q0)))), c, {==}, X.L.go(List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(q0)), 23n, 19n, D.Fd(2n, m2, args), c, {==},
    X.L.go(List.set(&2, U32, regs2, 22n, args), 24n, 19n, Mc.Img.quan(q0), c, {==}, X.L.go(regs2, 22n, 19n, args, c, {==}, h19))))
  X.ev.op(Wa.Wasm.Op.and{}, Mc.M.g(Mc.R.wok()), Mc.M.eq(Mc.M.q(Mc.M.g(Mc.R.wt())), Mc.M.c(2)), X.X.st(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(q0)), 23n, D.Fd(2n, m2, args)), 27n, Bool.to_u32(U32.is_eq(Bool.to_u32(El.Quan.live(p)), Bool.to_u32(El.Quan.live(q0))))), m2, nx2, fi, im, pg2, lim, inp),
    Bool.to_u32(U32.is_eq(Bool.to_u32(El.Quan.live(p)), Bool.to_u32(El.Quan.live(q0)))), Bool.to_u32(U32.is_eq(Mc.Img.quan(p), 2)), X.L.gs(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(q0)), 23n, D.Fd(2n, m2, args)), 27n, Bool.to_u32(U32.is_eq(Bool.to_u32(El.Quan.live(p)), Bool.to_u32(El.Quan.live(q0)))), X.L.lt(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(q0)), 23n, D.Fd(2n, m2, args)), 27n, l5, {==})),
    X.ev.op(Wa.Wasm.Op.eq{}, Mc.M.q(Mc.M.g(Mc.R.wt())), Mc.M.c(2), X.X.st(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(q0)), 23n, D.Fd(2n, m2, args)), 27n, Bool.to_u32(U32.is_eq(Bool.to_u32(El.Quan.live(p)), Bool.to_u32(El.Quan.live(q0))))), m2, nx2, fi, im, pg2, lim, inp), Mc.Img.quan(p), 2,
      lam.p(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(q0)), 23n, D.Fd(2n, m2, args)), 27n, Bool.to_u32(U32.is_eq(Bool.to_u32(El.Quan.live(p)), Bool.to_u32(El.Quan.live(q0))))), m2, nx2, fi, im, pg2, lim, inp, c, p, e19, hc, hq), {==}))

# both live or both dead fails: no check, and wres 3 (no walk)
def lam.fail(+h: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +keep: List<&2, Nat>,
  +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +tc: U32, +tt: Bk.Term,
  +a: U32, +xs: List<&2, El.Arg>, +xs0: List<&2, D.TmpE>, +B: Nat, +hk: {D.Disj(keep, D.Walk.scr()) == True{} : Bool},
  +regs2: List<&2, U32>, +m2: Cr.Cir.Cells, +nx2: U32, +pg2: U32, +c: U32, +p: Bk.Quan, +f: Bk.Term,
  +env: U32, +e: List<&2, El.Arg>, +args: U32, +q0: Bk.Quan, +x0: Bk.Term, +rest: List<&2, El.Arg>, +pend2: U32, +ps2: List<&2, U32>,
  +w6: WS(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(q0)), 23n, D.Fd(2n, m2, args)), 27n, Bool.to_u32(U32.is_eq(Bool.to_u32(El.Quan.live(p)), Bool.to_u32(El.Quan.live(q0))))), m2, nx2, c, Bk.Term.Lam{p, f}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2),
  hc1: {Cr.Cir.eval(Mc.M.and(Mc.M.g(Mc.R.wok()), Mc.M.eq(Mc.M.q(Mc.M.g(Mc.R.wt())), Mc.M.c(2))), X.X.st(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(q0)), 23n, D.Fd(2n, m2, args)), 27n, Bool.to_u32(U32.is_eq(Bool.to_u32(El.Quan.live(p)), Bool.to_u32(El.Quan.live(q0))))), m2, nx2, fi, im, pg2, lim, inp)) == Some{Bool.to_u32(False{})} : Maybe<&2, U32>},
  hc2: {Cr.Cir.eval(Mc.M.g(Mc.R.wok()), X.X.st(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(q0)), 23n, D.Fd(2n, m2, args)), 27n, Bool.to_u32(U32.is_eq(Bool.to_u32(El.Quan.live(p)), Bool.to_u32(El.Quan.live(q0))))), m2, nx2, fi, im, pg2, lim, inp)) == Some{Bool.to_u32(False{})} : Maybe<&2, U32>},
  hn: {El.Eval.walk(Bk.Term.Lam{p, f}, D.Arg.terms(e), Con{El.Arg{q0, x0}, rest}) == None{} : Maybe<Maybe<Bk.Term>>}) ->
  DW.WP(Wl.r4(), h, X.X.st(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(q0)), 23n, D.Fd(2n, m2, args)), 27n, Bool.to_u32(U32.is_eq(Bool.to_u32(El.Quan.live(p)), Bool.to_u32(El.Quan.live(q0))))), m2, nx2, fi, im, pg2, lim, inp), x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim):
  wp.if.be(Cr.Cir.Stmt.nop{}, h, Mc.M.and(Mc.M.g(Mc.R.wok()), Mc.M.eq(Mc.M.q(Mc.M.g(Mc.R.wt())), Mc.M.c(2))), X.sel.t(X.sel.a(Wl.r4())), X.X.st(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(q0)), 23n, D.Fd(2n, m2, args)), 27n, Bool.to_u32(U32.is_eq(Bool.to_u32(El.Quan.live(p)), Bool.to_u32(El.Quan.live(q0))))), m2, nx2, fi, im, pg2, lim, inp), t => DW.WP(Wl.r5(), h, t, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, lim,
    False{}, {==}, hc1, {==},
    wp.if.be(Mc.M.set(Mc.R.wres(), Mc.M.c(3)), h, Mc.M.g(Mc.R.wok()), X.sel.t(X.sel.a(Wl.r5())), X.X.st(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(q0)), 23n, D.Fd(2n, m2, args)), 27n, Bool.to_u32(U32.is_eq(Bool.to_u32(El.Quan.live(p)), Bool.to_u32(El.Quan.live(q0))))), m2, nx2, fi, im, pg2, lim, inp), t => DW.WP(Cr.Cir.Stmt.nop{}, h, t, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, lim,
      False{}, {==}, hc2, {==},
      wp.set.k(h, 26n, 3, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(q0)), 23n, D.Fd(2n, m2, args)), 27n, Bool.to_u32(U32.is_eq(Bool.to_u32(El.Quan.live(p)), Bool.to_u32(El.Quan.live(q0))))), m2, nx2, fi, im, pg2, lim, inp, x => DW.WP(Cr.Cir.Stmt.nop{}, h, x, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B,
        wr.len(regs, keep, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(q0)), 23n, D.Fd(2n, m2, args)), 27n, Bool.to_u32(U32.is_eq(Bool.to_u32(El.Quan.live(p)), Bool.to_u32(El.Quan.live(q0))))), c, env, List.length(&2, El.Arg, e), args, pend2, ws.wr(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(q0)), 23n, D.Fd(2n, m2, args)), 27n, Bool.to_u32(U32.is_eq(Bool.to_u32(El.Quan.live(p)), Bool.to_u32(El.Quan.live(q0))))), m2, nx2, c, Bk.Term.Lam{p, f}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, w6)), {==},
        Inr{ex.three(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(q0)), 23n, D.Fd(2n, m2, args)), 27n, Bool.to_u32(U32.is_eq(Bool.to_u32(El.Quan.live(p)), Bool.to_u32(El.Quan.live(q0))))), m2, nx2, pg2, c, env, List.length(&2, El.Arg, e), args, pend2, ps2,
          ws.wr(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(q0)), 23n, D.Fd(2n, m2, args)), 27n, Bool.to_u32(U32.is_eq(Bool.to_u32(El.Quan.live(p)), Bool.to_u32(El.Quan.live(q0))))), m2, nx2, c, Bk.Term.Lam{p, f}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, w6), hk,
          Equal.trans(Maybe<Maybe<Bk.Term>>, El.Eval.walk(tt, Nil{}, xs), El.Eval.walk(Bk.Term.Lam{p, f}, D.Arg.terms(e), Con{El.Arg{q0, x0}, rest}), None{},
            ws.ev(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(q0)), 23n, D.Fd(2n, m2, args)), 27n, Bool.to_u32(U32.is_eq(Bool.to_u32(El.Quan.live(p)), Bool.to_u32(El.Quan.live(q0))))), m2, nx2, c, Bk.Term.Lam{p, f}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, w6), hn),
          wh.kc(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Lam{p, f}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(q0)), 23n, D.Fd(2n, m2, args)), 27n, Bool.to_u32(U32.is_eq(Bool.to_u32(El.Quan.live(p)), Bool.to_u32(El.Quan.live(q0))))), m2, nx2, c, Bk.Term.Lam{p, f}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, w6)), wh.st(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Lam{p, f}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(q0)), 23n, D.Fd(2n, m2, args)), 27n, Bool.to_u32(U32.is_eq(Bool.to_u32(El.Quan.live(p)), Bool.to_u32(El.Quan.live(q0))))), m2, nx2, c, Bk.Term.Lam{p, f}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, w6)), wh.mem(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Lam{p, f}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(q0)), 23n, D.Fd(2n, m2, args)), 27n, Bool.to_u32(U32.is_eq(Bool.to_u32(El.Quan.live(p)), Bool.to_u32(El.Quan.live(q0))))), m2, nx2, c, Bk.Term.Lam{p, f}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, w6)))})))

# both live or both dead: the check when the λ's quantity is 2, then the
# argument becomes a local
# the walk of a λ whose argument binds: the body, with the argument bound
def lam.ev(+p: Bk.Quan, +f: Bk.Term, +q0: Bk.Quan, +x0: Bk.Term, +e: List<&2, Bk.Term>, +rest: List<&2, El.Arg>,
  hb: {El.Quan.binds(p, q0, x0) == True{} : Bool}) ->
  {El.Eval.walk(Bk.Term.Lam{p, f}, e, Con{El.Arg{q0, x0}, rest}) ==
    El.Eval.walk(f, Con{x0, e}, rest) : Maybe<Maybe<Bk.Term>>}:
  (%Equal.sym(Bool, El.Quan.binds(p, q0, x0), True{}, hb) :
     {El.Eval.walk.if(_, El.Eval.walk(f, Con{x0, e}, rest)) == El.Eval.walk(f, Con{x0, e}, rest) : Maybe<Maybe<Bk.Term>>};
   {==})

def lam.live(+h: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +keep: List<&2, Nat>,
  +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +tc: U32, +tt: Bk.Term,
  +a: U32, +xs: List<&2, El.Arg>, +xs0: List<&2, D.TmpE>, +B: Nat, +hk: {D.Disj(keep, D.Walk.scr()) == True{} : Bool},
  +regs2: List<&2, U32>, +m2: Cr.Cir.Cells, +nx2: U32, +pg2: U32, +c: U32, +p: Bk.Quan, +f: Bk.Term,
  +env: U32, +e: List<&2, El.Arg>, +args: U32, +q0: Bk.Quan, +x0: Bk.Term, +rest: List<&2, El.Arg>, +pend2: U32, +ps2: List<&2, U32>,
  +w6: WS(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(q0)), 23n, D.Fd(2n, m2, args)), 27n, Bool.to_u32(U32.is_eq(Bool.to_u32(El.Quan.live(p)), Bool.to_u32(El.Quan.live(q0))))), m2, nx2, c, Bk.Term.Lam{p, f}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2),
  hlv: {El.Quan.lives_as(p, q0) == True{} : Bool}) ->
  DW.WP(Wl.r4(), h, X.X.st(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(q0)), 23n, D.Fd(2n, m2, args)), 27n, Bool.to_u32(U32.is_eq(Bool.to_u32(El.Quan.live(p)), Bool.to_u32(El.Quan.live(q0))))), m2, nx2, fi, im, pg2, lim, inp), x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim):
  ?TODO

# walk.lam's tests, by the two quantities
def lam.chk(+h: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +keep: List<&2, Nat>,
  +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +tc: U32, +tt: Bk.Term,
  +a: U32, +xs: List<&2, El.Arg>, +xs0: List<&2, D.TmpE>, +B: Nat, +hk: {D.Disj(keep, D.Walk.scr()) == True{} : Bool},
  +regs2: List<&2, U32>, +m2: Cr.Cir.Cells, +nx2: U32, +pg2: U32, +c: U32, +p: Bk.Quan, +f: Bk.Term,
  +env: U32, +e: List<&2, El.Arg>, +args: U32, +q0: Bk.Quan, +x0: Bk.Term, +rest: List<&2, El.Arg>, +pend2: U32, +ps2: List<&2, U32>,
  +w6: WS(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(q0)), 23n, D.Fd(2n, m2, args)), 27n, Bool.to_u32(U32.is_eq(Bool.to_u32(El.Quan.live(p)), Bool.to_u32(El.Quan.live(q0))))), m2, nx2, c, Bk.Term.Lam{p, f}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2),
  +hl: {List.length(&2, U32, regs2) == 63n : Nat}, +h19: {List.get(&2, U32, regs2, 19n) == Some{c} : Maybe<&2, U32>},
  +hc: {Cr.Cir.is_cell(c, im, fi, nx2) == True{} : Bool}, +hqp: D.Qs(Cr.Cir.Cells.get(m2, c), p)) ->
  DW.WP(Wl.r4(), h, X.X.st(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(q0)), 23n, D.Fd(2n, m2, args)), 27n, Bool.to_u32(U32.is_eq(Bool.to_u32(El.Quan.live(p)), Bool.to_u32(El.Quan.live(q0))))), m2, nx2, fi, im, pg2, lim, inp), x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim):
  match p q0:
    case Bk.Quan.Q0{} Bk.Quan.Q0{}:
      lam.live(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, Bk.Quan.Q0{}, f, env, e, args, Bk.Quan.Q0{}, x0, rest, pend2, ps2, w6, {==})
    case Bk.Quan.Q0{} Bk.Quan.Q1{}:
      lam.fail(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, Bk.Quan.Q0{}, f, env, e, args, Bk.Quan.Q1{}, x0, rest, pend2, ps2, w6, lam.t1(regs2, m2, nx2, fi, im, pg2, lim, inp, c, Bk.Quan.Q0{}, args, Bk.Quan.Q1{}, hl, h19, hc, hqp),
        X.L.gs(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(Bk.Quan.Q1{})), 23n, D.Fd(2n, m2, args)), 27n, Bool.to_u32(U32.is_eq(Bool.to_u32(El.Quan.live(Bk.Quan.Q0{})), Bool.to_u32(El.Quan.live(Bk.Quan.Q1{})))), X.L.lt(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(Bk.Quan.Q1{})), 23n, D.Fd(2n, m2, args)), 27n, X.L.len(List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(Bk.Quan.Q1{})), 23n, D.Fd(2n, m2, args), 63n, X.L.len(List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(Bk.Quan.Q1{}), 63n, X.L.len(regs2, 22n, args, 63n, hl))), {==})), {==})
    case Bk.Quan.Q0{} Bk.Quan.Q2{}:
      lam.fail(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, Bk.Quan.Q0{}, f, env, e, args, Bk.Quan.Q2{}, x0, rest, pend2, ps2, w6, lam.t1(regs2, m2, nx2, fi, im, pg2, lim, inp, c, Bk.Quan.Q0{}, args, Bk.Quan.Q2{}, hl, h19, hc, hqp),
        X.L.gs(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(Bk.Quan.Q2{})), 23n, D.Fd(2n, m2, args)), 27n, Bool.to_u32(U32.is_eq(Bool.to_u32(El.Quan.live(Bk.Quan.Q0{})), Bool.to_u32(El.Quan.live(Bk.Quan.Q2{})))), X.L.lt(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(Bk.Quan.Q2{})), 23n, D.Fd(2n, m2, args)), 27n, X.L.len(List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(Bk.Quan.Q2{})), 23n, D.Fd(2n, m2, args), 63n, X.L.len(List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(Bk.Quan.Q2{}), 63n, X.L.len(regs2, 22n, args, 63n, hl))), {==})), {==})
    case Bk.Quan.Q1{} Bk.Quan.Q0{}:
      lam.fail(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, Bk.Quan.Q1{}, f, env, e, args, Bk.Quan.Q0{}, x0, rest, pend2, ps2, w6, lam.t1(regs2, m2, nx2, fi, im, pg2, lim, inp, c, Bk.Quan.Q1{}, args, Bk.Quan.Q0{}, hl, h19, hc, hqp),
        X.L.gs(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(Bk.Quan.Q0{})), 23n, D.Fd(2n, m2, args)), 27n, Bool.to_u32(U32.is_eq(Bool.to_u32(El.Quan.live(Bk.Quan.Q1{})), Bool.to_u32(El.Quan.live(Bk.Quan.Q0{})))), X.L.lt(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(Bk.Quan.Q0{})), 23n, D.Fd(2n, m2, args)), 27n, X.L.len(List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(Bk.Quan.Q0{})), 23n, D.Fd(2n, m2, args), 63n, X.L.len(List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(Bk.Quan.Q0{}), 63n, X.L.len(regs2, 22n, args, 63n, hl))), {==})), {==})
    case Bk.Quan.Q1{} Bk.Quan.Q1{}:
      lam.live(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, Bk.Quan.Q1{}, f, env, e, args, Bk.Quan.Q1{}, x0, rest, pend2, ps2, w6, {==})
    case Bk.Quan.Q1{} Bk.Quan.Q2{}:
      lam.live(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, Bk.Quan.Q1{}, f, env, e, args, Bk.Quan.Q2{}, x0, rest, pend2, ps2, w6, {==})
    case Bk.Quan.Q2{} Bk.Quan.Q0{}:
      lam.fail(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, Bk.Quan.Q2{}, f, env, e, args, Bk.Quan.Q0{}, x0, rest, pend2, ps2, w6, lam.t1(regs2, m2, nx2, fi, im, pg2, lim, inp, c, Bk.Quan.Q2{}, args, Bk.Quan.Q0{}, hl, h19, hc, hqp),
        X.L.gs(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(Bk.Quan.Q0{})), 23n, D.Fd(2n, m2, args)), 27n, Bool.to_u32(U32.is_eq(Bool.to_u32(El.Quan.live(Bk.Quan.Q2{})), Bool.to_u32(El.Quan.live(Bk.Quan.Q0{})))), X.L.lt(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(Bk.Quan.Q0{})), 23n, D.Fd(2n, m2, args)), 27n, X.L.len(List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(Bk.Quan.Q0{})), 23n, D.Fd(2n, m2, args), 63n, X.L.len(List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(Bk.Quan.Q0{}), 63n, X.L.len(regs2, 22n, args, 63n, hl))), {==})), {==})
    case Bk.Quan.Q2{} Bk.Quan.Q1{}:
      lam.live(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, Bk.Quan.Q2{}, f, env, e, args, Bk.Quan.Q1{}, x0, rest, pend2, ps2, w6, {==})
    case Bk.Quan.Q2{} Bk.Quan.Q2{}:
      lam.live(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, Bk.Quan.Q2{}, f, env, e, args, Bk.Quan.Q2{}, x0, rest, pend2, ps2, w6, {==})

# walk.lam with an argument: the reads of its K.arg and wok, then the tests
def lam.go(+h: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +keep: List<&2, Nat>,
  +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +tc: U32, +tt: Bk.Term,
  +a: U32, +xs: List<&2, El.Arg>, +xs0: List<&2, D.TmpE>, +B: Nat, +hk: {D.Disj(keep, D.Walk.scr()) == True{} : Bool},
  +regs2: List<&2, U32>, +m2: Cr.Cir.Cells, +nx2: U32, +pg2: U32, +c: U32, +p: Bk.Quan, +f: Bk.Term,
  +env: U32, +e: List<&2, El.Arg>, +args: U32, +q0: Bk.Quan, +x0: Bk.Term, +rest: List<&2, El.Arg>, +pend2: U32, +ps2: List<&2, U32>,
  +w: WS(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Lam{p, f}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2)) ->
  DW.WP(Cr.Cir.Stmt.seq{X.sel.a(Wl.e()), X.sel.b(Wl.e())}, h, X.X.st(regs2, m2, nx2, fi, im, pg2, lim, inp), x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim):
  +hl = wr.len(regs, keep, regs2, c, env, List.length(&2, El.Arg, e), args, pend2, ws.wr(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Lam{p, f}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, w))
  +l3 = X.L.len(regs2, 22n, args, 63n, hl)
  +l4 = X.L.len(List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(q0), 63n, l3)
  +l5 = X.L.len(List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(q0)), 23n, D.Fd(2n, m2, args), 63n, l4)
  +hca = ag.cell(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, x0, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Lam{p, f}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Lam{p, f}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, w)))
  +e22 = X.L.gs(regs2, 22n, args, X.L.lt(regs2, 22n, hl, {==}))
  +h19 = wr.r19(regs, keep, regs2, c, env, List.length(&2, El.Arg, e), args, pend2, ws.wr(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Lam{p, f}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, w))
  +hc = hs.cell(ds, ks, img, m2, nx2, fi, im, os, c, Bk.Term.Lam{p, f}, Con{D.Rt{tc, tt}, bs}, fs, sp, pend2, ps2, ws.hs(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Lam{p, f}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, w))
  +hqp = is.lam.qs(ds, m2, im, fi, nx2, ks, img, c, p, f, hs.is(ds, ks, img, m2, nx2, fi, im, os, c, Bk.Term.Lam{p, f}, Con{D.Rt{tc, tt}, bs}, fs, sp, pend2, ps2, ws.hs(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Lam{p, f}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, w)))
  +ex = X.ev.fld(2n, Mc.M.g(Mc.R.wa()), X.X.st(List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(q0)), m2, nx2, fi, im, pg2, lim, inp), args, X.L.go(List.set(&2, U32, regs2, 22n, args), 24n, 22n, Mc.Img.quan(q0), args, {==}, e22), hca)
  wp.set.e(22n, Mc.M.g(Mc.R.wargs()), args, regs2, m2, nx2, fi, im, pg2, lim, inp, h, t => DW.WP(Wl.r1(), h, t, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B,
    wr.r21(regs, keep, regs2, c, env, List.length(&2, El.Arg, e), args, pend2, ws.wr(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Lam{p, f}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, w)), hl, {==},
    wp.set.e(24n, Mc.M.q(Mc.M.g(Mc.R.wa())), Mc.Img.quan(q0), List.set(&2, U32, regs2, 22n, args), m2, nx2, fi, im, pg2, lim, inp, h, t => DW.WP(Wl.r2(), h, t, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B,
      lam.q(regs2, m2, nx2, fi, im, pg2, lim, inp, args, q0, hl, hca, ag.qs(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, x0, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Lam{p, f}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Lam{p, f}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, w)))), l3, {==},
      wp.set.e(23n, Mc.M.f(2n, Mc.M.g(Mc.R.wa())), D.Fd(2n, m2, args), List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(q0)), m2, nx2, fi, im, pg2, lim, inp, h, t => DW.WP(Wl.r3(), h, t, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B,
        ex, l4, {==},
        wp.set.e(27n, Mc.M.eq(Mc.M.ne(Mc.M.q(Mc.M.g(Mc.R.wt())), Mc.M.c(0)), Mc.M.ne(Mc.M.g(Mc.R.wq()), Mc.M.c(0))), Bool.to_u32(U32.is_eq(Bool.to_u32(El.Quan.live(p)), Bool.to_u32(El.Quan.live(q0)))), List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(q0)), 23n, D.Fd(2n, m2, args)), m2, nx2, fi, im, pg2, lim, inp, h, t => DW.WP(Wl.r4(), h, t, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B,
          lam.ok(regs2, m2, nx2, fi, im, pg2, lim, inp, c, p, args, q0, hl, h19, hc, hqp), l5, {==},
          lam.chk(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, p, f, env, e, args, q0, x0, rest, pend2, ps2, ws.set(27n, Bool.to_u32(U32.is_eq(Bool.to_u32(El.Quan.live(p)), Bool.to_u32(El.Quan.live(q0)))), ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(q0)), 23n, D.Fd(2n, m2, args)), m2, nx2, c, Bk.Term.Lam{p, f}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, hk, {==}, {==}, {==}, {==}, {==}, {==}, {==}, ws.set(23n, D.Fd(2n, m2, args), ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, List.set(&2, U32, regs2, 22n, args), 24n, Mc.Img.quan(q0)), m2, nx2, c, Bk.Term.Lam{p, f}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, hk, {==}, {==}, {==}, {==}, {==}, {==}, {==}, ws.set(24n, Mc.Img.quan(q0), ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, regs2, 22n, args), m2, nx2, c, Bk.Term.Lam{p, f}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, hk, {==}, {==}, {==}, {==}, {==}, {==}, {==}, ws.set(22n, args, ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Lam{p, f}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, hk, {==}, {==}, {==}, {==}, {==}, {==}, {==}, w)))), hl, h19, hc, hqp)))))

# the round of a λ: it binds the first argument, or wres 2 or 3
def round.lam(+h: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +keep: List<&2, Nat>,
  +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +tc: U32, +tt: Bk.Term,
  +a: U32, +xs: List<&2, El.Arg>, +xs0: List<&2, D.TmpE>, +B: Nat, +hk: {D.Disj(keep, D.Walk.scr()) == True{} : Bool},
  +regs2: List<&2, U32>, +m2: Cr.Cir.Cells, +nx2: U32, +pg2: U32, +c: U32, +p: Bk.Quan, +f: Bk.Term,
  +env: U32, +e: List<&2, El.Arg>, +args: U32, +ys: List<&2, El.Arg>, +pend2: U32, +ps2: List<&2, U32>,
  +w: WS(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Lam{p, f}, env, e, args, ys, pend2, ps2)) ->
  DW.WP(Mc.M.walk.lam(), h, X.X.st(regs2, m2, nx2, fi, im, pg2, lim, inp), u => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, u), B, lim):
  match ys:
    case Nil{}:
      r.nil(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, Bk.Term.Lam{p, f}, env, e, args, pend2, ps2, X.sel.a(Wl.e()), X.sel.b(Wl.e()), w, {==})
    case Con{El.Arg{+q0, +x0}, +rest}:
      r.con(h, regs2, m2, nx2, fi, im, pg2, lim, inp, u => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, u), B, args, X.sel.a(Wl.e()), X.sel.b(Wl.e()),
        wr.r21(regs, keep, regs2, c, env, List.length(&2, El.Arg, e), args, pend2, ws.wr(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Lam{p, f}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, w)), ag.nz(ds, m2, im, fi, nx2, ks, img, ps2, os, D.Ag.vars(e, m2, env), args, q0, x0, rest, wh.args(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, m2, nx2, c, Bk.Term.Lam{p, f}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Lam{p, f}, env, e, args, Con{El.Arg{q0, x0}, rest}, pend2, ps2, w))),
        lam.go(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, p, f, env, e, args, q0, x0, rest, pend2, ps2, w))

# The round of an App
# -------------------
#
# walk.app reads the App's argument (wx): a Var whose App's head (wh, by
# the loop down the spine) takes an argument makes the local or the free
# variable the first argument; anything else is a leaf, wres 1.

def Wap.r1() -> Cr.Cir.Stmt:
  X.sel.b(Mc.M.walk.app())

def Wap.if1() -> Cr.Cir.Stmt:
  X.sel.a(Wap.r1())

def Wap.e1() -> Cr.Cir.Stmt:
  X.sel.e(Wap.if1())

def Wap.e2() -> Cr.Cir.Stmt:
  X.sel.b(Wap.e1())

def Wap.e3() -> Cr.Cir.Stmt:
  X.sel.b(Wap.e2())

def Wap.e4() -> Cr.Cir.Stmt:
  X.sel.b(Wap.e3())

def Wap.push() -> Cr.Cir.Stmt:
  X.sel.e(X.sel.a(Wap.e4()))

# the loop to the head
def Wap.wh() -> Cr.Cir.Stmt:
  Cr.Cir.Stmt.while{Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wh())), Mc.M.c(Mc.T.app())), Mc.M.set(Mc.R.wh(), Mc.M.f(2n, Mc.M.g(Mc.R.wh())))}

# a set of a register twice
def l.ss(xs: List<&2, U32>, r: Nat, +v: U32, +w: U32) ->
  {List.set(&2, U32, List.set(&2, U32, xs, r, v), r, w) == List.set(&2, U32, xs, r, w) : List<&2, U32>}:
  match xs r:
    case Nil{} _:
      {==}
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+p:
      Equal.cong(List<&2, U32>, List<&2, U32>, l => Con{x, l}, List.set(&2, U32, List.set(&2, U32, t, p, v), p, w),
        List.set(&2, U32, t, p, w), l.ss(t, p, v, w))

# the parts of an App's cell: f in field 2, the argument in field 3
def is.app.f(-ds: List<&2, Bk.Def>, -m: Cr.Cir.Cells, -im: U32, -fi: U32, -nx: U32, -ks: List<&2, List<&2, Word(8n)>>,
  -img: List<&2, Bk.Term>, -c: U32, -q: Bk.Quan, -f: Bk.Term, -y: Bk.Term, h: D.Is(ds, m, im, fi, nx, ks, img, c, Bk.Term.App{q, f, y})) ->
  D.Is(ds, m, im, fi, nx, ks, img, D.Fd(2n, m, c), f):
  (_, h1) = h
  (_, h2) = h1
  (hf, _) = h2
  (_, z) = hf
  z

def is.app.y(-ds: List<&2, Bk.Def>, -m: Cr.Cir.Cells, -im: U32, -fi: U32, -nx: U32, -ks: List<&2, List<&2, Word(8n)>>,
  -img: List<&2, Bk.Term>, -c: U32, -q: Bk.Quan, -f: Bk.Term, -y: Bk.Term, h: D.Is(ds, m, im, fi, nx, ks, img, c, Bk.Term.App{q, f, y})) ->
  D.Is(ds, m, im, fi, nx, ks, img, D.Fd(3n, m, c), y):
  (_, h1) = h
  (_, h2) = h1
  (_, hy) = h2
  (_, z) = hy
  z

# the head of a term that is no App is itself
def head.na(t: Bk.Term, h: {U32.is_eq(D.A.tag(t), 8) == False{} : Bool}) -> {El.Term.head(t) == t : Bk.Term}:
  match t:
    case Bk.Term.Var{+i}:
      {==}
    case Bk.Term.Ref{+kk}:
      {==}
    case Bk.Term.Ann{+y1, +y2}:
      {==}
    case Bk.Term.Let{+q1, +v1, +f1}:
      {==}
    case Bk.Term.Typ{+y1}:
      {==}
    case Bk.Term.Min{+y1, +y2}:
      {==}
    case Bk.Term.All{+q1, +y1, +y2}:
      {==}
    case Bk.Term.Lam{+q1, +f1}:
      {==}
    case Bk.Term.App{+q1, +f1, +y1}:
      DW.ft({El.Term.head(Bk.Term.App{q1, f1, y1}) == Bk.Term.App{q1, f1, y1} : Bk.Term}, h)
    case Bk.Term.Sig{+q1, +y1, +y2}:
      {==}
    case Bk.Term.Tup{+q1, +y1, +y2}:
      {==}
    case Bk.Term.Prj{+h1}:
      {==}
    case Bk.Term.Enu{+kk}:
      {==}
    case Bk.Term.Lab{+kk}:
      {==}
    case Bk.Term.Mat{+kk, +h1, +n1}:
      {==}
    case Bk.Term.Efq{}:
      {==}
    case Bk.Term.Eql{+y1, +y2, +y3}:
      {==}
    case Bk.Term.Rfl{}:
      {==}
    case Bk.Term.Rwt{+y1, +y2, +y3}:
      {==}

# M.takes of a term's tag: the term takes an argument
def tk.takes(t: Bk.Term) -> {U32.or(U32.or(Bool.to_u32(U32.is_eq(D.A.tag(t), 7)), Bool.to_u32(U32.is_eq(D.A.tag(t), 11))), U32.or(Bool.to_u32(U32.is_eq(D.A.tag(t), 14)), Bool.to_u32(U32.is_eq(D.A.tag(t), 15)))) == Bool.to_u32(El.Term.takes(t)) : U32}:
  match t:
    case Bk.Term.Var{+i}:
      {==}
    case Bk.Term.Ref{+kk}:
      {==}
    case Bk.Term.Ann{+y1, +y2}:
      {==}
    case Bk.Term.Let{+q1, +v1, +f1}:
      {==}
    case Bk.Term.Typ{+y1}:
      {==}
    case Bk.Term.Min{+y1, +y2}:
      {==}
    case Bk.Term.All{+q1, +y1, +y2}:
      {==}
    case Bk.Term.Lam{+q1, +f1}:
      {==}
    case Bk.Term.App{+q1, +f1, +y1}:
      {==}
    case Bk.Term.Sig{+q1, +y1, +y2}:
      {==}
    case Bk.Term.Tup{+q1, +y1, +y2}:
      {==}
    case Bk.Term.Prj{+h1}:
      {==}
    case Bk.Term.Enu{+kk}:
      {==}
    case Bk.Term.Lab{+kk}:
      {==}
    case Bk.Term.Mat{+kk, +h1, +n1}:
      {==}
    case Bk.Term.Efq{}:
      {==}
    case Bk.Term.Eql{+y1, +y2, +y3}:
      {==}
    case Bk.Term.Rfl{}:
      {==}
    case Bk.Term.Rwt{+y1, +y2, +y3}:
      {==}

# a while whose test is b, when b is True: a round of the loop
def wp.wh.bt.p(+h: Nat, +c: Cr.Cir.Expr, +body: Cr.Cir.Stmt, +st: Cr.Cir.State, -K: Cr.Cir.State -> Type, +B: Nat, +lim: U32, +b: Bool,
  p: DW.Ob(c, st) & {DW.Ev(c, st) == Bool.to_u32(b) : U32}, hb: {b == True{} : Bool}, k: DW.WP(body, h, st, t => DW.WP(Cr.Cir.Stmt.while{c, body}, h, t, x => K(x), B, lim), B, lim)) ->
  DW.WP(Cr.Cir.Stmt.while{c, body}, 1n+h, st, K, B, lim):
  (oc, ve) = p
  (oc, (%Equal.sym(U32, DW.Ev(c, st), Bool.to_u32(b), ve) :
     DW.WhQ(U32.is_zero(_), q => DW.WP(body, h, st, t => DW.WP(Cr.Cir.Stmt.while{c, body}, h, t, x => q(x), B, lim), B, lim), K, st);
   %Equal.sym(Bool, b, True{}, hb) :
     DW.WhQ(U32.is_zero(Bool.to_u32(_)), q => DW.WP(body, h, st, t => DW.WP(Cr.Cir.Stmt.while{c, body}, h, t, x => q(x), B, lim), B, lim), K, st);
   k))

def wp.wh.bt(+h: Nat, +c: Cr.Cir.Expr, +body: Cr.Cir.Stmt, +st: Cr.Cir.State, -K: Cr.Cir.State -> Type, +B: Nat, +lim: U32, +b: Bool,
  hc: {Cr.Cir.eval(c, st) == Some{Bool.to_u32(b)} : Maybe<&2, U32>}, hb: {b == True{} : Bool}, k: DW.WP(body, h, st, t => DW.WP(Cr.Cir.Stmt.while{c, body}, h, t, x => K(x), B, lim), B, lim)) ->
  DW.WP(Cr.Cir.Stmt.while{c, body}, 1n+h, st, K, B, lim):
  wp.wh.bt.p(h, c, body, st, K, B, lim, b, ob.of(c, st, Bool.to_u32(b), hc), hb, k)

# a while whose test is b, when b is False: the loop's end
def wp.wh.be.p(+h: Nat, +c: Cr.Cir.Expr, +body: Cr.Cir.Stmt, +st: Cr.Cir.State, -K: Cr.Cir.State -> Type, +B: Nat, +lim: U32, +b: Bool,
  p: DW.Ob(c, st) & {DW.Ev(c, st) == Bool.to_u32(b) : U32}, hb: {b == False{} : Bool}, k: K(st)) ->
  DW.WP(Cr.Cir.Stmt.while{c, body}, 1n+h, st, K, B, lim):
  (oc, ve) = p
  (oc, (%Equal.sym(U32, DW.Ev(c, st), Bool.to_u32(b), ve) :
     DW.WhQ(U32.is_zero(_), q => DW.WP(body, h, st, t => DW.WP(Cr.Cir.Stmt.while{c, body}, h, t, x => q(x), B, lim), B, lim), K, st);
   %Equal.sym(Bool, b, False{}, hb) :
     DW.WhQ(U32.is_zero(Bool.to_u32(_)), q => DW.WP(body, h, st, t => DW.WP(Cr.Cir.Stmt.while{c, body}, h, t, x => q(x), B, lim), B, lim), K, st);
   k))

def wp.wh.be(+h: Nat, +c: Cr.Cir.Expr, +body: Cr.Cir.Stmt, +st: Cr.Cir.State, -K: Cr.Cir.State -> Type, +B: Nat, +lim: U32, +b: Bool,
  hc: {Cr.Cir.eval(c, st) == Some{Bool.to_u32(b)} : Maybe<&2, U32>}, hb: {b == False{} : Bool}, k: K(st)) ->
  DW.WP(Cr.Cir.Stmt.while{c, body}, 1n+h, st, K, B, lim):
  wp.wh.be.p(h, c, body, st, K, B, lim, b, ob.of(c, st, Bool.to_u32(b), hc), hb, k)

# the loop's test at the cell v of the term g: g is an App
def hd.ev(+rr: List<&2, U32>, +m2: Cr.Cir.Cells, +nx2: U32, +fi: U32, +im: U32, +pg2: U32, +lim: U32, +inp: List<&2, Word(8n)>,
  +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +v: U32, +g: Bk.Term,
  h29: {List.get(&2, U32, rr, 29n) == Some{v} : Maybe<&2, U32>}, +hv: D.Is(ds, m2, im, fi, nx2, ks, img, v, g)) ->
  {Cr.Cir.eval(Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wh())), Mc.M.c(Mc.T.app())), X.X.st(rr, m2, nx2, fi, im, pg2, lim, inp)) == Some{Bool.to_u32(U32.is_eq(D.A.tag(g), 8))} : Maybe<&2, U32>}:
  +st = X.X.st(rr, m2, nx2, fi, im, pg2, lim, inp)
  (%is.tg(ds, m2, im, fi, nx2, ks, img, v, g, hv) : {Cr.Cir.eval(Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wh())), Mc.M.c(Mc.T.app())), st) == Some{Bool.to_u32(U32.is_eq(_, 8))} : Maybe<&2, U32>};
   X.ev.op(Wa.Wasm.Op.eq{}, Mc.M.tag(Mc.M.g(Mc.R.wh())), Mc.M.c(Mc.T.app()), st, D.Tg(m2, v), 8,
     X.ev.opw(Wa.Wasm.Op.and{}, Mc.M.f(0n, Mc.M.g(Mc.R.wh())), Mc.M.c(63), st, D.Fd(0n, m2, v), 63, D.Tg(m2, v),
       X.ev.fld(0n, Mc.M.g(Mc.R.wh()), st, v, h29, is.cell(ds, m2, im, fi, nx2, ks, img, v, g, hv)), {==}, {==}), {==}))

# the loop to the head of f, from the cell v of g, a part of f's spine with
# f's head: it ends at the head's cell
def hd.loop(g0: Nat, +R1: List<&2, U32>, +m2: Cr.Cir.Cells, +nx2: U32, +fi: U32, +im: U32, +pg2: U32, +lim: U32,
  +inp: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +f: Bk.Term,
  -K: Cr.Cir.State -> Type, +B: Nat, +hl: {List.length(&2, U32, R1) == 63n : Nat}, +v: U32, g: Bk.Term,
  +hv: D.Is(ds, m2, im, fi, nx2, ks, img, v, g), hh: {El.Term.head(g) == El.Term.head(f) : Bk.Term},
  k: @v2: U32 -> @g2: Bk.Term -> D.Is(ds, m2, im, fi, nx2, ks, img, v2, g2) -> {El.Term.head(g2) == El.Term.head(f) : Bk.Term} ->
    {U32.is_eq(D.A.tag(g2), 8) == False{} : Bool} -> K(X.X.st(List.set(&2, U32, R1, 29n, v2), m2, nx2, fi, im, pg2, lim, inp))) ->
  DW.WP(Wap.wh(), g0, X.X.st(List.set(&2, U32, R1, 29n, v), m2, nx2, fi, im, pg2, lim, inp), K, B, lim):
  match g0:
    case 0n:
      Unit{}
    case 1n+(+h):
      match g:
        case Bk.Term.Var{+i}:
          wp.wh.be(h, Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wh())), Mc.M.c(Mc.T.app())), Mc.M.set(Mc.R.wh(), Mc.M.f(2n, Mc.M.g(Mc.R.wh()))), X.X.st(List.set(&2, U32, R1, 29n, v), m2, nx2, fi, im, pg2, lim, inp), K, B, lim, U32.is_eq(D.A.tag(Bk.Term.Var{i}), 8), hd.ev(List.set(&2, U32, R1, 29n, v), m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, v, Bk.Term.Var{i}, X.L.gs(R1, 29n, v, X.L.lt(R1, 29n, hl, {==})), hv), {==},
            k(v, Bk.Term.Var{i}, hv, hh, {==}))
        case Bk.Term.Ref{+kk}:
          wp.wh.be(h, Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wh())), Mc.M.c(Mc.T.app())), Mc.M.set(Mc.R.wh(), Mc.M.f(2n, Mc.M.g(Mc.R.wh()))), X.X.st(List.set(&2, U32, R1, 29n, v), m2, nx2, fi, im, pg2, lim, inp), K, B, lim, U32.is_eq(D.A.tag(Bk.Term.Ref{kk}), 8), hd.ev(List.set(&2, U32, R1, 29n, v), m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, v, Bk.Term.Ref{kk}, X.L.gs(R1, 29n, v, X.L.lt(R1, 29n, hl, {==})), hv), {==},
            k(v, Bk.Term.Ref{kk}, hv, hh, {==}))
        case Bk.Term.Ann{+y1, +y2}:
          wp.wh.be(h, Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wh())), Mc.M.c(Mc.T.app())), Mc.M.set(Mc.R.wh(), Mc.M.f(2n, Mc.M.g(Mc.R.wh()))), X.X.st(List.set(&2, U32, R1, 29n, v), m2, nx2, fi, im, pg2, lim, inp), K, B, lim, U32.is_eq(D.A.tag(Bk.Term.Ann{y1, y2}), 8), hd.ev(List.set(&2, U32, R1, 29n, v), m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, v, Bk.Term.Ann{y1, y2}, X.L.gs(R1, 29n, v, X.L.lt(R1, 29n, hl, {==})), hv), {==},
            k(v, Bk.Term.Ann{y1, y2}, hv, hh, {==}))
        case Bk.Term.Let{+q1, +v1, +f1}:
          wp.wh.be(h, Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wh())), Mc.M.c(Mc.T.app())), Mc.M.set(Mc.R.wh(), Mc.M.f(2n, Mc.M.g(Mc.R.wh()))), X.X.st(List.set(&2, U32, R1, 29n, v), m2, nx2, fi, im, pg2, lim, inp), K, B, lim, U32.is_eq(D.A.tag(Bk.Term.Let{q1, v1, f1}), 8), hd.ev(List.set(&2, U32, R1, 29n, v), m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, v, Bk.Term.Let{q1, v1, f1}, X.L.gs(R1, 29n, v, X.L.lt(R1, 29n, hl, {==})), hv), {==},
            k(v, Bk.Term.Let{q1, v1, f1}, hv, hh, {==}))
        case Bk.Term.Typ{+y1}:
          wp.wh.be(h, Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wh())), Mc.M.c(Mc.T.app())), Mc.M.set(Mc.R.wh(), Mc.M.f(2n, Mc.M.g(Mc.R.wh()))), X.X.st(List.set(&2, U32, R1, 29n, v), m2, nx2, fi, im, pg2, lim, inp), K, B, lim, U32.is_eq(D.A.tag(Bk.Term.Typ{y1}), 8), hd.ev(List.set(&2, U32, R1, 29n, v), m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, v, Bk.Term.Typ{y1}, X.L.gs(R1, 29n, v, X.L.lt(R1, 29n, hl, {==})), hv), {==},
            k(v, Bk.Term.Typ{y1}, hv, hh, {==}))
        case Bk.Term.Min{+y1, +y2}:
          wp.wh.be(h, Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wh())), Mc.M.c(Mc.T.app())), Mc.M.set(Mc.R.wh(), Mc.M.f(2n, Mc.M.g(Mc.R.wh()))), X.X.st(List.set(&2, U32, R1, 29n, v), m2, nx2, fi, im, pg2, lim, inp), K, B, lim, U32.is_eq(D.A.tag(Bk.Term.Min{y1, y2}), 8), hd.ev(List.set(&2, U32, R1, 29n, v), m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, v, Bk.Term.Min{y1, y2}, X.L.gs(R1, 29n, v, X.L.lt(R1, 29n, hl, {==})), hv), {==},
            k(v, Bk.Term.Min{y1, y2}, hv, hh, {==}))
        case Bk.Term.All{+q1, +y1, +y2}:
          wp.wh.be(h, Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wh())), Mc.M.c(Mc.T.app())), Mc.M.set(Mc.R.wh(), Mc.M.f(2n, Mc.M.g(Mc.R.wh()))), X.X.st(List.set(&2, U32, R1, 29n, v), m2, nx2, fi, im, pg2, lim, inp), K, B, lim, U32.is_eq(D.A.tag(Bk.Term.All{q1, y1, y2}), 8), hd.ev(List.set(&2, U32, R1, 29n, v), m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, v, Bk.Term.All{q1, y1, y2}, X.L.gs(R1, 29n, v, X.L.lt(R1, 29n, hl, {==})), hv), {==},
            k(v, Bk.Term.All{q1, y1, y2}, hv, hh, {==}))
        case Bk.Term.Lam{+q1, +f1}:
          wp.wh.be(h, Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wh())), Mc.M.c(Mc.T.app())), Mc.M.set(Mc.R.wh(), Mc.M.f(2n, Mc.M.g(Mc.R.wh()))), X.X.st(List.set(&2, U32, R1, 29n, v), m2, nx2, fi, im, pg2, lim, inp), K, B, lim, U32.is_eq(D.A.tag(Bk.Term.Lam{q1, f1}), 8), hd.ev(List.set(&2, U32, R1, 29n, v), m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, v, Bk.Term.Lam{q1, f1}, X.L.gs(R1, 29n, v, X.L.lt(R1, 29n, hl, {==})), hv), {==},
            k(v, Bk.Term.Lam{q1, f1}, hv, hh, {==}))
        case Bk.Term.App{+q1, +f1, +y1}:
          wp.wh.bt(h, Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wh())), Mc.M.c(Mc.T.app())), Mc.M.set(Mc.R.wh(), Mc.M.f(2n, Mc.M.g(Mc.R.wh()))), X.X.st(List.set(&2, U32, R1, 29n, v), m2, nx2, fi, im, pg2, lim, inp), K, B, lim, U32.is_eq(D.A.tag(Bk.Term.App{q1, f1, y1}), 8), hd.ev(List.set(&2, U32, R1, 29n, v), m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, v, Bk.Term.App{q1, f1, y1}, X.L.gs(R1, 29n, v, X.L.lt(R1, 29n, hl, {==})), hv), {==},
            wp.set.e(29n, Mc.M.f(2n, Mc.M.g(Mc.R.wh())), D.Fd(2n, m2, v), List.set(&2, U32, R1, 29n, v), m2, nx2, fi, im, pg2, lim, inp, h,
              t => DW.WP(Cr.Cir.Stmt.while{Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wh())), Mc.M.c(Mc.T.app())), Mc.M.set(Mc.R.wh(), Mc.M.f(2n, Mc.M.g(Mc.R.wh())))}, h, t, x => K(x), B, lim), B,
              X.ev.fld(2n, Mc.M.g(Mc.R.wh()), X.X.st(List.set(&2, U32, R1, 29n, v), m2, nx2, fi, im, pg2, lim, inp), v, X.L.gs(R1, 29n, v, X.L.lt(R1, 29n, hl, {==})), is.cell(ds, m2, im, fi, nx2, ks, img, v, Bk.Term.App{q1, f1, y1}, hv)),
              X.L.len(R1, 29n, v, 63n, hl), {==},
              (%Equal.sym(List<&2, U32>, List.set(&2, U32, List.set(&2, U32, R1, 29n, v), 29n, D.Fd(2n, m2, v)), List.set(&2, U32, R1, 29n, D.Fd(2n, m2, v)), l.ss(R1, 29n, v, D.Fd(2n, m2, v))) :
                DW.WP(Cr.Cir.Stmt.while{Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wh())), Mc.M.c(Mc.T.app())), Mc.M.set(Mc.R.wh(), Mc.M.f(2n, Mc.M.g(Mc.R.wh())))}, h, X.X.st(_, m2, nx2, fi, im, pg2, lim, inp), x => K(x), B, lim);
               hd.loop(h, R1, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, f, x => K(x), B, hl, D.Fd(2n, m2, v), f1,
                 is.app.f(ds, m2, im, fi, nx2, ks, img, v, q1, f1, y1, hv), hh, k))))
        case Bk.Term.Sig{+q1, +y1, +y2}:
          wp.wh.be(h, Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wh())), Mc.M.c(Mc.T.app())), Mc.M.set(Mc.R.wh(), Mc.M.f(2n, Mc.M.g(Mc.R.wh()))), X.X.st(List.set(&2, U32, R1, 29n, v), m2, nx2, fi, im, pg2, lim, inp), K, B, lim, U32.is_eq(D.A.tag(Bk.Term.Sig{q1, y1, y2}), 8), hd.ev(List.set(&2, U32, R1, 29n, v), m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, v, Bk.Term.Sig{q1, y1, y2}, X.L.gs(R1, 29n, v, X.L.lt(R1, 29n, hl, {==})), hv), {==},
            k(v, Bk.Term.Sig{q1, y1, y2}, hv, hh, {==}))
        case Bk.Term.Tup{+q1, +y1, +y2}:
          wp.wh.be(h, Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wh())), Mc.M.c(Mc.T.app())), Mc.M.set(Mc.R.wh(), Mc.M.f(2n, Mc.M.g(Mc.R.wh()))), X.X.st(List.set(&2, U32, R1, 29n, v), m2, nx2, fi, im, pg2, lim, inp), K, B, lim, U32.is_eq(D.A.tag(Bk.Term.Tup{q1, y1, y2}), 8), hd.ev(List.set(&2, U32, R1, 29n, v), m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, v, Bk.Term.Tup{q1, y1, y2}, X.L.gs(R1, 29n, v, X.L.lt(R1, 29n, hl, {==})), hv), {==},
            k(v, Bk.Term.Tup{q1, y1, y2}, hv, hh, {==}))
        case Bk.Term.Prj{+h1}:
          wp.wh.be(h, Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wh())), Mc.M.c(Mc.T.app())), Mc.M.set(Mc.R.wh(), Mc.M.f(2n, Mc.M.g(Mc.R.wh()))), X.X.st(List.set(&2, U32, R1, 29n, v), m2, nx2, fi, im, pg2, lim, inp), K, B, lim, U32.is_eq(D.A.tag(Bk.Term.Prj{h1}), 8), hd.ev(List.set(&2, U32, R1, 29n, v), m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, v, Bk.Term.Prj{h1}, X.L.gs(R1, 29n, v, X.L.lt(R1, 29n, hl, {==})), hv), {==},
            k(v, Bk.Term.Prj{h1}, hv, hh, {==}))
        case Bk.Term.Enu{+kk}:
          wp.wh.be(h, Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wh())), Mc.M.c(Mc.T.app())), Mc.M.set(Mc.R.wh(), Mc.M.f(2n, Mc.M.g(Mc.R.wh()))), X.X.st(List.set(&2, U32, R1, 29n, v), m2, nx2, fi, im, pg2, lim, inp), K, B, lim, U32.is_eq(D.A.tag(Bk.Term.Enu{kk}), 8), hd.ev(List.set(&2, U32, R1, 29n, v), m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, v, Bk.Term.Enu{kk}, X.L.gs(R1, 29n, v, X.L.lt(R1, 29n, hl, {==})), hv), {==},
            k(v, Bk.Term.Enu{kk}, hv, hh, {==}))
        case Bk.Term.Lab{+kk}:
          wp.wh.be(h, Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wh())), Mc.M.c(Mc.T.app())), Mc.M.set(Mc.R.wh(), Mc.M.f(2n, Mc.M.g(Mc.R.wh()))), X.X.st(List.set(&2, U32, R1, 29n, v), m2, nx2, fi, im, pg2, lim, inp), K, B, lim, U32.is_eq(D.A.tag(Bk.Term.Lab{kk}), 8), hd.ev(List.set(&2, U32, R1, 29n, v), m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, v, Bk.Term.Lab{kk}, X.L.gs(R1, 29n, v, X.L.lt(R1, 29n, hl, {==})), hv), {==},
            k(v, Bk.Term.Lab{kk}, hv, hh, {==}))
        case Bk.Term.Mat{+kk, +h1, +n1}:
          wp.wh.be(h, Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wh())), Mc.M.c(Mc.T.app())), Mc.M.set(Mc.R.wh(), Mc.M.f(2n, Mc.M.g(Mc.R.wh()))), X.X.st(List.set(&2, U32, R1, 29n, v), m2, nx2, fi, im, pg2, lim, inp), K, B, lim, U32.is_eq(D.A.tag(Bk.Term.Mat{kk, h1, n1}), 8), hd.ev(List.set(&2, U32, R1, 29n, v), m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, v, Bk.Term.Mat{kk, h1, n1}, X.L.gs(R1, 29n, v, X.L.lt(R1, 29n, hl, {==})), hv), {==},
            k(v, Bk.Term.Mat{kk, h1, n1}, hv, hh, {==}))
        case Bk.Term.Efq{}:
          wp.wh.be(h, Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wh())), Mc.M.c(Mc.T.app())), Mc.M.set(Mc.R.wh(), Mc.M.f(2n, Mc.M.g(Mc.R.wh()))), X.X.st(List.set(&2, U32, R1, 29n, v), m2, nx2, fi, im, pg2, lim, inp), K, B, lim, U32.is_eq(D.A.tag(Bk.Term.Efq{}), 8), hd.ev(List.set(&2, U32, R1, 29n, v), m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, v, Bk.Term.Efq{}, X.L.gs(R1, 29n, v, X.L.lt(R1, 29n, hl, {==})), hv), {==},
            k(v, Bk.Term.Efq{}, hv, hh, {==}))
        case Bk.Term.Eql{+y1, +y2, +y3}:
          wp.wh.be(h, Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wh())), Mc.M.c(Mc.T.app())), Mc.M.set(Mc.R.wh(), Mc.M.f(2n, Mc.M.g(Mc.R.wh()))), X.X.st(List.set(&2, U32, R1, 29n, v), m2, nx2, fi, im, pg2, lim, inp), K, B, lim, U32.is_eq(D.A.tag(Bk.Term.Eql{y1, y2, y3}), 8), hd.ev(List.set(&2, U32, R1, 29n, v), m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, v, Bk.Term.Eql{y1, y2, y3}, X.L.gs(R1, 29n, v, X.L.lt(R1, 29n, hl, {==})), hv), {==},
            k(v, Bk.Term.Eql{y1, y2, y3}, hv, hh, {==}))
        case Bk.Term.Rfl{}:
          wp.wh.be(h, Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wh())), Mc.M.c(Mc.T.app())), Mc.M.set(Mc.R.wh(), Mc.M.f(2n, Mc.M.g(Mc.R.wh()))), X.X.st(List.set(&2, U32, R1, 29n, v), m2, nx2, fi, im, pg2, lim, inp), K, B, lim, U32.is_eq(D.A.tag(Bk.Term.Rfl{}), 8), hd.ev(List.set(&2, U32, R1, 29n, v), m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, v, Bk.Term.Rfl{}, X.L.gs(R1, 29n, v, X.L.lt(R1, 29n, hl, {==})), hv), {==},
            k(v, Bk.Term.Rfl{}, hv, hh, {==}))
        case Bk.Term.Rwt{+y1, +y2, +y3}:
          wp.wh.be(h, Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.wh())), Mc.M.c(Mc.T.app())), Mc.M.set(Mc.R.wh(), Mc.M.f(2n, Mc.M.g(Mc.R.wh()))), X.X.st(List.set(&2, U32, R1, 29n, v), m2, nx2, fi, im, pg2, lim, inp), K, B, lim, U32.is_eq(D.A.tag(Bk.Term.Rwt{y1, y2, y3}), 8), hd.ev(List.set(&2, U32, R1, 29n, v), m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, v, Bk.Term.Rwt{y1, y2, y3}, X.L.gs(R1, 29n, v, X.L.lt(R1, 29n, hl, {==})), hv), {==},
            k(v, Bk.Term.Rwt{y1, y2, y3}, hv, hh, {==}))

# the test of walk.app's argument: it is no Var
def app.t1(+regs2: List<&2, U32>, +m2: Cr.Cir.Cells, +nx2: U32, +fi: U32, +im: U32, +pg2: U32, +lim: U32, +inp: List<&2, Word(8n)>,
  +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32, +y: Bk.Term,
  hl: {List.length(&2, U32, regs2) == 63n : Nat}, +hy: D.Is(ds, m2, im, fi, nx2, ks, img, D.Fd(3n, m2, c), y)) ->
  {Cr.Cir.eval(Mc.M.ne(Mc.M.tag(Mc.M.g(Mc.R.wx())), Mc.M.c(Mc.T.var())), X.X.st(List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, fi, im, pg2, lim, inp)) == Some{Bool.to_u32(U32.is_ne(D.A.tag(y), 0))} : Maybe<&2, U32>}:
  +st = X.X.st(List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, fi, im, pg2, lim, inp)
  (%is.tg(ds, m2, im, fi, nx2, ks, img, D.Fd(3n, m2, c), y, hy) : {Cr.Cir.eval(Mc.M.ne(Mc.M.tag(Mc.M.g(Mc.R.wx())), Mc.M.c(Mc.T.var())), st) == Some{Bool.to_u32(U32.is_ne(_, 0))} : Maybe<&2, U32>};
   X.ev.op(Wa.Wasm.Op.ne{}, Mc.M.tag(Mc.M.g(Mc.R.wx())), Mc.M.c(Mc.T.var()), st, D.Tg(m2, D.Fd(3n, m2, c)), 0,
     X.ev.opw(Wa.Wasm.Op.and{}, Mc.M.f(0n, Mc.M.g(Mc.R.wx())), Mc.M.c(63), st, D.Fd(0n, m2, D.Fd(3n, m2, c)), 63, D.Tg(m2, D.Fd(3n, m2, c)),
       X.ev.fld(0n, Mc.M.g(Mc.R.wx()), st, D.Fd(3n, m2, c), X.L.gs(regs2, 23n, D.Fd(3n, m2, c), X.L.lt(regs2, 23n, hl, {==})),
         is.cell(ds, m2, im, fi, nx2, ks, img, D.Fd(3n, m2, c), y, hy)), {==}, {==}), {==}))

# M.takes at the head's cell
def app.tke(+rr: List<&2, U32>, +m2: Cr.Cir.Cells, +nx2: U32, +fi: U32, +im: U32, +pg2: U32, +lim: U32, +inp: List<&2, Word(8n)>,
  +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +v2: U32, +g2: Bk.Term,
  h29: {List.get(&2, U32, rr, 29n) == Some{v2} : Maybe<&2, U32>}, +hv: D.Is(ds, m2, im, fi, nx2, ks, img, v2, g2)) ->
  {Cr.Cir.eval(Mc.M.takes(Mc.M.tag(Mc.M.g(Mc.R.wh()))), X.X.st(rr, m2, nx2, fi, im, pg2, lim, inp)) == Some{Bool.to_u32(El.Term.takes(g2))} : Maybe<&2, U32>}:
  +st = X.X.st(rr, m2, nx2, fi, im, pg2, lim, inp)
  +tg = D.Tg(m2, v2)
  +et = X.ev.opw(Wa.Wasm.Op.and{}, Mc.M.f(0n, Mc.M.g(Mc.R.wh())), Mc.M.c(63), st, D.Fd(0n, m2, v2), 63, tg,
    X.ev.fld(0n, Mc.M.g(Mc.R.wh()), st, v2, h29, is.cell(ds, m2, im, fi, nx2, ks, img, v2, g2, hv)), {==}, {==})
  +tgx = Mc.M.tag(Mc.M.g(Mc.R.wh()))
  (%tk.takes(g2) : {Cr.Cir.eval(Mc.M.takes(Mc.M.tag(Mc.M.g(Mc.R.wh()))), st) == Some{_} : Maybe<&2, U32>};
   %is.tg(ds, m2, im, fi, nx2, ks, img, v2, g2, hv) :
     {Cr.Cir.eval(Mc.M.takes(Mc.M.tag(Mc.M.g(Mc.R.wh()))), st) == Some{U32.or(U32.or(Bool.to_u32(U32.is_eq(_, 7)), Bool.to_u32(U32.is_eq(_, 11))), U32.or(Bool.to_u32(U32.is_eq(_, 14)), Bool.to_u32(U32.is_eq(_, 15))))} : Maybe<&2, U32>};
   X.ev.op(Wa.Wasm.Op.or{}, Mc.M.or(Mc.M.eq(tgx, Mc.M.c(Mc.T.lam())), Mc.M.eq(tgx, Mc.M.c(Mc.T.prj()))),
     Mc.M.or(Mc.M.eq(tgx, Mc.M.c(Mc.T.mat())), Mc.M.eq(tgx, Mc.M.c(Mc.T.efq()))), st,
     U32.or(Bool.to_u32(U32.is_eq(tg, 7)), Bool.to_u32(U32.is_eq(tg, 11))), U32.or(Bool.to_u32(U32.is_eq(tg, 14)), Bool.to_u32(U32.is_eq(tg, 15))),
     X.ev.op(Wa.Wasm.Op.or{}, Mc.M.eq(tgx, Mc.M.c(Mc.T.lam())), Mc.M.eq(tgx, Mc.M.c(Mc.T.prj())), st,
       Bool.to_u32(U32.is_eq(tg, 7)), Bool.to_u32(U32.is_eq(tg, 11)),
       X.ev.op(Wa.Wasm.Op.eq{}, tgx, Mc.M.c(Mc.T.lam()), st, tg, 7, et, {==}),
       X.ev.op(Wa.Wasm.Op.eq{}, tgx, Mc.M.c(Mc.T.prj()), st, tg, 11, et, {==})),
     X.ev.op(Wa.Wasm.Op.or{}, Mc.M.eq(tgx, Mc.M.c(Mc.T.mat())), Mc.M.eq(tgx, Mc.M.c(Mc.T.efq())), st,
       Bool.to_u32(U32.is_eq(tg, 14)), Bool.to_u32(U32.is_eq(tg, 15)),
       X.ev.op(Wa.Wasm.Op.eq{}, tgx, Mc.M.c(Mc.T.mat()), st, tg, 14, et, {==}),
       X.ev.op(Wa.Wasm.Op.eq{}, tgx, Mc.M.c(Mc.T.efq()), st, tg, 15, et, {==}))))

# the walk at an App of a Var whose head, g2, takes no argument: a leaf
def app.leaf2.ev(+q: Bk.Quan, +f: Bk.Term, +vv: Nat, +E: List<&2, Bk.Term>, +ys: List<&2, El.Arg>, +g2: Bk.Term,
  hh: {El.Term.head(g2) == El.Term.head(f) : Bk.Term}, hna: {U32.is_eq(D.A.tag(g2), 8) == False{} : Bool},
  ht: {El.Term.takes(g2) == False{} : Bool}) ->
  {El.Eval.walk(Bk.Term.App{q, f, Bk.Term.Var{vv}}, E, ys) ==
    Some{Some{El.Term.spine(ys, El.Term.subst(Bk.Term.App{q, f, Bk.Term.Var{vv}}, E, 0n))}} : Maybe<Maybe<Bk.Term>>}:
  +hf = Equal.trans(Bk.Term, El.Term.head(f), El.Term.head(g2), g2, Equal.sym(Bk.Term, El.Term.head(g2), El.Term.head(f), hh), head.na(g2, hna))
  (%Equal.sym(Bk.Term, El.Term.head(f), g2, hf) :
     {El.Eval.walk.app(El.Term.takes(_), El.Eval.walk(f, E, Con{El.Arg{q, El.Env.sub(E, vv)}, ys}),
       El.Term.spine(ys, El.Term.subst(Bk.Term.App{q, f, Bk.Term.Var{vv}}, E, 0n))) ==
       Some{Some{El.Term.spine(ys, El.Term.subst(Bk.Term.App{q, f, Bk.Term.Var{vv}}, E, 0n))}} : Maybe<Maybe<Bk.Term>>};
   %Equal.sym(Bool, El.Term.takes(g2), False{}, ht) :
     {El.Eval.walk.app(_, El.Eval.walk(f, E, Con{El.Arg{q, El.Env.sub(E, vv)}, ys}),
       El.Term.spine(ys, El.Term.subst(Bk.Term.App{q, f, Bk.Term.Var{vv}}, E, 0n))) ==
       Some{Some{El.Term.spine(ys, El.Term.subst(Bk.Term.App{q, f, Bk.Term.Var{vv}}, E, 0n))}} : Maybe<Maybe<Bk.Term>>};
   {==})

# the head takes an argument: the local or the free variable goes first
# among the arguments
def app.push(+h: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +keep: List<&2, Nat>,
  +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +tc: U32, +tt: Bk.Term,
  +a: U32, +xs: List<&2, El.Arg>, +xs0: List<&2, D.TmpE>, +B: Nat, +hk: {D.Disj(keep, D.Walk.scr()) == True{} : Bool},
  +regs2: List<&2, U32>, +m2: Cr.Cir.Cells, +nx2: U32, +pg2: U32, +c: U32, +q: Bk.Quan, +f: Bk.Term, +vv: Nat,
  +env: U32, +e: List<&2, El.Arg>, +args: U32, +ys: List<&2, El.Arg>, +pend2: U32, +ps2: List<&2, U32>, +v2: U32, +g2: Bk.Term,
  +w: WS(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Var{vv}}, env, e, args, ys, pend2, ps2),
  hv: D.Is(ds, m2, im, fi, nx2, ks, img, v2, g2), hh: {El.Term.head(g2) == El.Term.head(f) : Bk.Term},
  hna: {U32.is_eq(D.A.tag(g2), 8) == False{} : Bool}, ht: {El.Term.takes(g2) == True{} : Bool}) ->
  DW.WP(Wap.push(), h, X.X.st(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), 29n, v2), 27n, Bool.to_u32(El.Term.takes(g2))), m2, nx2, fi, im, pg2, lim, inp), y => DW.WP(Cr.Cir.Stmt.nop{}, h, y, x => DW.WP(Cr.Cir.Stmt.nop{}, h, x, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, lim), B, lim):
  ?TODO

# walk.app's test of the head g2 at v2: it takes an argument, or wres 1
def app.tk(+h: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +keep: List<&2, Nat>,
  +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +tc: U32, +tt: Bk.Term,
  +a: U32, +xs: List<&2, El.Arg>, +xs0: List<&2, D.TmpE>, +B: Nat, +hk: {D.Disj(keep, D.Walk.scr()) == True{} : Bool},
  +regs2: List<&2, U32>, +m2: Cr.Cir.Cells, +nx2: U32, +pg2: U32, +c: U32, +q: Bk.Quan, +f: Bk.Term, +vv: Nat,
  +env: U32, +e: List<&2, El.Arg>, +args: U32, +ys: List<&2, El.Arg>, +pend2: U32, +ps2: List<&2, U32>, +v2: U32, +g2: Bk.Term,
  +w: WS(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Var{vv}}, env, e, args, ys, pend2, ps2),
  +hv: D.Is(ds, m2, im, fi, nx2, ks, img, v2, g2), +hh: {El.Term.head(g2) == El.Term.head(f) : Bk.Term},
  +hna: {U32.is_eq(D.A.tag(g2), 8) == False{} : Bool}, +hl: {List.length(&2, U32, regs2) == 63n : Nat},
  bt: Bool, +ebt: {El.Term.takes(g2) == bt : Bool}) ->
  DW.WP(X.sel.a(Wap.e4()), h, X.X.st(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), 29n, v2), 27n, Bool.to_u32(El.Term.takes(g2))), m2, nx2, fi, im, pg2, lim, inp), t => DW.WP(Cr.Cir.Stmt.nop{}, h, t, x => DW.WP(Cr.Cir.Stmt.nop{}, h, x, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, lim), B, lim):
  match bt:
    case False{}:
      +l1 = X.L.len(regs2, 23n, D.Fd(3n, m2, c), 63n, hl)
      +l2 = X.L.len(List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), 29n, v2, 63n, l1)
      +l3 = X.L.len(List.set(&2, U32, List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), 29n, v2), 27n, Bool.to_u32(El.Term.takes(g2)), 63n, l2)
      +hc2 = X.ev.eqz(Mc.M.g(Mc.R.wok()), X.X.st(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), 29n, v2), 27n, Bool.to_u32(El.Term.takes(g2))), m2, nx2, fi, im, pg2, lim, inp), Bool.to_u32(El.Term.takes(g2)), X.L.gs(List.set(&2, U32, List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), 29n, v2), 27n, Bool.to_u32(El.Term.takes(g2)), X.L.lt(List.set(&2, U32, List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), 29n, v2), 27n, l2, {==})))
      wp.if.bt(Wap.push(), h, Mc.M.not(Mc.M.g(Mc.R.wok())), Mc.M.set(Mc.R.wres(), Mc.M.c(1)), X.X.st(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), 29n, v2), 27n, Bool.to_u32(El.Term.takes(g2))), m2, nx2, fi, im, pg2, lim, inp), t => DW.WP(Cr.Cir.Stmt.nop{}, h, t, x => DW.WP(Cr.Cir.Stmt.nop{}, h, x, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, lim), B, lim,
        U32.is_zero(Bool.to_u32(El.Term.takes(g2))), {==}, hc2,
        (%Equal.sym(Bool, El.Term.takes(g2), False{}, ebt) : {U32.is_zero(Bool.to_u32(_)) == True{} : Bool}; {==}),
        wp.set.k(h, 26n, 1, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), 29n, v2), 27n, Bool.to_u32(El.Term.takes(g2))), m2, nx2, fi, im, pg2, lim, inp, y => DW.WP(Cr.Cir.Stmt.nop{}, h, y, x => DW.WP(Cr.Cir.Stmt.nop{}, h, x, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, lim), B, l3, {==},
          Inr{ex.one(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), 29n, v2), 27n, Bool.to_u32(El.Term.takes(g2))), m2, nx2, pg2, c, Bk.Term.App{q, f, Bk.Term.Var{vv}}, env, e, args, ys, pend2, ps2, wr.set(27n, Bool.to_u32(El.Term.takes(g2)), regs, keep, List.set(&2, U32, List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), 29n, v2), c, env, List.length(&2, El.Arg, e), args, pend2, hk, {==}, {==}, {==}, {==}, {==}, {==}, wr.set(29n, v2, regs, keep, List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), c, env, List.length(&2, El.Arg, e), args, pend2, hk, {==}, {==}, {==}, {==}, {==}, {==}, wr.set(23n, D.Fd(3n, m2, c), regs, keep, regs2, c, env, List.length(&2, El.Arg, e), args, pend2, hk, {==}, {==}, {==}, {==}, {==}, {==}, ws.wr(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Var{vv}}, env, e, args, ys, pend2, ps2, w)))), hk,
            Equal.trans(Maybe<Maybe<Bk.Term>>, El.Eval.walk(tt, Nil{}, xs), El.Eval.walk(Bk.Term.App{q, f, Bk.Term.Var{vv}}, D.Arg.terms(e), ys),
              Some{Some{El.Term.spine(ys, El.Term.subst(Bk.Term.App{q, f, Bk.Term.Var{vv}}, D.Arg.terms(e), 0n))}}, ws.ev(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Var{vv}}, env, e, args, ys, pend2, ps2, w),
              app.leaf2.ev(q, f, vv, D.Arg.terms(e), ys, g2, hh, hna, ebt)),
            ws.st(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Var{vv}}, env, e, args, ys, pend2, ps2, w), ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Var{vv}}, env, e, args, ys, pend2, ps2, w))}))
    case True{}:
      +l1 = X.L.len(regs2, 23n, D.Fd(3n, m2, c), 63n, hl)
      +l2 = X.L.len(List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), 29n, v2, 63n, l1)
      +l3 = X.L.len(List.set(&2, U32, List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), 29n, v2), 27n, Bool.to_u32(El.Term.takes(g2)), 63n, l2)
      +hc2 = X.ev.eqz(Mc.M.g(Mc.R.wok()), X.X.st(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), 29n, v2), 27n, Bool.to_u32(El.Term.takes(g2))), m2, nx2, fi, im, pg2, lim, inp), Bool.to_u32(El.Term.takes(g2)), X.L.gs(List.set(&2, U32, List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), 29n, v2), 27n, Bool.to_u32(El.Term.takes(g2)), X.L.lt(List.set(&2, U32, List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), 29n, v2), 27n, l2, {==})))
      wp.if.be(Wap.push(), h, Mc.M.not(Mc.M.g(Mc.R.wok())), Mc.M.set(Mc.R.wres(), Mc.M.c(1)), X.X.st(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), 29n, v2), 27n, Bool.to_u32(El.Term.takes(g2))), m2, nx2, fi, im, pg2, lim, inp), t => DW.WP(Cr.Cir.Stmt.nop{}, h, t, x => DW.WP(Cr.Cir.Stmt.nop{}, h, x, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, lim), B, lim,
        U32.is_zero(Bool.to_u32(El.Term.takes(g2))), {==}, hc2,
        (%Equal.sym(Bool, El.Term.takes(g2), True{}, ebt) : {U32.is_zero(Bool.to_u32(_)) == False{} : Bool}; {==}),
        app.push(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, q, f, vv, env, e, args, ys, pend2, ps2, v2, g2, w, hv, hh, hna, ebt))

# after the loop: wok, M.takes of the head's tag, then the test
def app.after(+h: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +keep: List<&2, Nat>,
  +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +tc: U32, +tt: Bk.Term,
  +a: U32, +xs: List<&2, El.Arg>, +xs0: List<&2, D.TmpE>, +B: Nat, +hk: {D.Disj(keep, D.Walk.scr()) == True{} : Bool},
  +regs2: List<&2, U32>, +m2: Cr.Cir.Cells, +nx2: U32, +pg2: U32, +c: U32, +q: Bk.Quan, +f: Bk.Term, +vv: Nat,
  +env: U32, +e: List<&2, El.Arg>, +args: U32, +ys: List<&2, El.Arg>, +pend2: U32, +ps2: List<&2, U32>, +v2: U32, +g2: Bk.Term,
  +w: WS(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Var{vv}}, env, e, args, ys, pend2, ps2),
  +hv: D.Is(ds, m2, im, fi, nx2, ks, img, v2, g2), +hh: {El.Term.head(g2) == El.Term.head(f) : Bk.Term},
  +hna: {U32.is_eq(D.A.tag(g2), 8) == False{} : Bool}, +hl: {List.length(&2, U32, regs2) == 63n : Nat}) ->
  DW.WP(Wap.e3(), h, X.X.st(List.set(&2, U32, List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), 29n, v2), m2, nx2, fi, im, pg2, lim, inp), x => DW.WP(Cr.Cir.Stmt.nop{}, h, x, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, lim):
  +l1 = X.L.len(regs2, 23n, D.Fd(3n, m2, c), 63n, hl)
  +l2 = X.L.len(List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), 29n, v2, 63n, l1)
  wp.set.e(27n, Mc.M.takes(Mc.M.tag(Mc.M.g(Mc.R.wh()))), Bool.to_u32(El.Term.takes(g2)), List.set(&2, U32, List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), 29n, v2), m2, nx2, fi, im, pg2, lim, inp, h,
    t => DW.WP(Wap.e4(), h, t, x => DW.WP(Cr.Cir.Stmt.nop{}, h, x, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, lim), B,
    app.tke(List.set(&2, U32, List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), 29n, v2), m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, v2, g2, X.L.gs(List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), 29n, v2, X.L.lt(List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), 29n, l1, {==})), hv),
    l2, {==},
    app.tk(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, q, f, vv, env, e, args, ys, pend2, ps2, v2, g2, w, hv, hh, hna, hl, El.Term.takes(g2), {==}))

# an App of a Var: wh gets f's cell, the loop to its head, then the rest
def app.var(+h: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +keep: List<&2, Nat>,
  +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +tc: U32, +tt: Bk.Term,
  +a: U32, +xs: List<&2, El.Arg>, +xs0: List<&2, D.TmpE>, +B: Nat, +hk: {D.Disj(keep, D.Walk.scr()) == True{} : Bool},
  +regs2: List<&2, U32>, +m2: Cr.Cir.Cells, +nx2: U32, +pg2: U32, +c: U32, +q: Bk.Quan, +f: Bk.Term, +vv: Nat,
  +env: U32, +e: List<&2, El.Arg>, +args: U32, +ys: List<&2, El.Arg>, +pend2: U32, +ps2: List<&2, U32>,
  +w: WS(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Var{vv}}, env, e, args, ys, pend2, ps2), +hl: {List.length(&2, U32, regs2) == 63n : Nat},
  +h19: {List.get(&2, U32, regs2, 19n) == Some{c} : Maybe<&2, U32>}, +hc: {Cr.Cir.is_cell(c, im, fi, nx2) == True{} : Bool}) ->
  DW.WP(Wap.e1(), h, X.X.st(List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, fi, im, pg2, lim, inp), x => DW.WP(Cr.Cir.Stmt.nop{}, h, x, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, lim):
  +l1 = X.L.len(regs2, 23n, D.Fd(3n, m2, c), 63n, hl)
  wp.set.e(29n, Mc.M.f(2n, Mc.M.g(Mc.R.wt())), D.Fd(2n, m2, c), List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, fi, im, pg2, lim, inp, h,
    t => DW.WP(Wap.e2(), h, t, x => DW.WP(Cr.Cir.Stmt.nop{}, h, x, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, lim), B,
    X.ev.fld(2n, Mc.M.g(Mc.R.wt()), X.X.st(List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, fi, im, pg2, lim, inp), c, X.L.go(regs2, 23n, 19n, D.Fd(3n, m2, c), c, {==}, h19), hc), l1, {==},
    hd.loop(h, List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, f, t => DW.WP(Wap.e3(), h, t, x => DW.WP(Cr.Cir.Stmt.nop{}, h, x, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, lim), B, l1,
      D.Fd(2n, m2, c), f, is.app.f(ds, m2, im, fi, nx2, ks, img, c, q, f, Bk.Term.Var{vv}, hs.is(ds, ks, img, m2, nx2, fi, im, os, c, Bk.Term.App{q, f, Bk.Term.Var{vv}}, Con{D.Rt{tc, tt}, bs}, fs, sp, pend2, ps2, ws.hs(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Var{vv}}, env, e, args, ys, pend2, ps2, w))), {==},
      v2 => g2 => hv2 => hh2 => hna2 => app.after(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, q, f, vv, env, e, args, ys, pend2, ps2, v2, g2, w, hv2, hh2, hna2, hl)))

# walk.app's first test, by the App's argument's form: a Var, or a leaf
def app.if1(+h: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +keep: List<&2, Nat>,
  +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +tc: U32, +tt: Bk.Term,
  +a: U32, +xs: List<&2, El.Arg>, +xs0: List<&2, D.TmpE>, +B: Nat, +hk: {D.Disj(keep, D.Walk.scr()) == True{} : Bool},
  +regs2: List<&2, U32>, +m2: Cr.Cir.Cells, +nx2: U32, +pg2: U32, +c: U32, +q: Bk.Quan, +f: Bk.Term, +y: Bk.Term,
  +env: U32, +e: List<&2, El.Arg>, +args: U32, +ys: List<&2, El.Arg>, +pend2: U32, +ps2: List<&2, U32>,
  +w: WS(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, y}, env, e, args, ys, pend2, ps2), +hl: {List.length(&2, U32, regs2) == 63n : Nat},
  +h19: {List.get(&2, U32, regs2, 19n) == Some{c} : Maybe<&2, U32>}, +hc: {Cr.Cir.is_cell(c, im, fi, nx2) == True{} : Bool}) ->
  DW.WP(Wap.if1(), h, X.X.st(List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, fi, im, pg2, lim, inp), t => DW.WP(Cr.Cir.Stmt.nop{}, h, t, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, lim):
  match y:
    case Bk.Term.Var{+vv}:
      wp.if.be(Wap.e1(), h, Mc.M.ne(Mc.M.tag(Mc.M.g(Mc.R.wx())), Mc.M.c(Mc.T.var())), Mc.M.set(Mc.R.wres(), Mc.M.c(1)), X.X.st(List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, fi, im, pg2, lim, inp), t => DW.WP(Cr.Cir.Stmt.nop{}, h, t, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, lim,
        U32.is_ne(D.A.tag(Bk.Term.Var{vv}), 0), {==},
        app.t1(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, c, Bk.Term.Var{vv}, hl, is.app.y(ds, m2, im, fi, nx2, ks, img, c, q, f, Bk.Term.Var{vv}, hs.is(ds, ks, img, m2, nx2, fi, im, os, c, Bk.Term.App{q, f, Bk.Term.Var{vv}}, Con{D.Rt{tc, tt}, bs}, fs, sp, pend2, ps2, ws.hs(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Var{vv}}, env, e, args, ys, pend2, ps2, w)))), {==},
        app.var(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, q, f, vv, env, e, args, ys, pend2, ps2, w, hl, h19, hc))
    case Bk.Term.Ref{+kk}:
      wp.if.bt(Wap.e1(), h, Mc.M.ne(Mc.M.tag(Mc.M.g(Mc.R.wx())), Mc.M.c(Mc.T.var())), Mc.M.set(Mc.R.wres(), Mc.M.c(1)), X.X.st(List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, fi, im, pg2, lim, inp), t => DW.WP(Cr.Cir.Stmt.nop{}, h, t, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, lim,
        U32.is_ne(D.A.tag(Bk.Term.Ref{kk}), 0), {==},
        app.t1(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, c, Bk.Term.Ref{kk}, hl, is.app.y(ds, m2, im, fi, nx2, ks, img, c, q, f, Bk.Term.Ref{kk}, hs.is(ds, ks, img, m2, nx2, fi, im, os, c, Bk.Term.App{q, f, Bk.Term.Ref{kk}}, Con{D.Rt{tc, tt}, bs}, fs, sp, pend2, ps2, ws.hs(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Ref{kk}}, env, e, args, ys, pend2, ps2, w)))), {==},
        wp.set.k(h, 26n, 1, List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, fi, im, pg2, lim, inp, x => DW.WP(Cr.Cir.Stmt.nop{}, h, x, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, X.L.len(regs2, 23n, D.Fd(3n, m2, c), 63n, hl), {==},
          Inr{ex.one(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, pg2, c, Bk.Term.App{q, f, Bk.Term.Ref{kk}}, env, e, args, ys, pend2, ps2, wr.set(23n, D.Fd(3n, m2, c), regs, keep, regs2, c, env, List.length(&2, El.Arg, e), args, pend2, hk, {==}, {==}, {==}, {==}, {==}, {==}, ws.wr(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Ref{kk}}, env, e, args, ys, pend2, ps2, w)), hk,
            Equal.trans(Maybe<Maybe<Bk.Term>>, El.Eval.walk(tt, Nil{}, xs), El.Eval.walk(Bk.Term.App{q, f, Bk.Term.Ref{kk}}, D.Arg.terms(e), ys),
              Some{Some{El.Term.spine(ys, El.Term.subst(Bk.Term.App{q, f, Bk.Term.Ref{kk}}, D.Arg.terms(e), 0n))}}, ws.ev(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Ref{kk}}, env, e, args, ys, pend2, ps2, w), {==}),
            ws.st(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Ref{kk}}, env, e, args, ys, pend2, ps2, w), ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Ref{kk}}, env, e, args, ys, pend2, ps2, w))}))
    case Bk.Term.Ann{+y1, +y2}:
      wp.if.bt(Wap.e1(), h, Mc.M.ne(Mc.M.tag(Mc.M.g(Mc.R.wx())), Mc.M.c(Mc.T.var())), Mc.M.set(Mc.R.wres(), Mc.M.c(1)), X.X.st(List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, fi, im, pg2, lim, inp), t => DW.WP(Cr.Cir.Stmt.nop{}, h, t, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, lim,
        U32.is_ne(D.A.tag(Bk.Term.Ann{y1, y2}), 0), {==},
        app.t1(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, c, Bk.Term.Ann{y1, y2}, hl, is.app.y(ds, m2, im, fi, nx2, ks, img, c, q, f, Bk.Term.Ann{y1, y2}, hs.is(ds, ks, img, m2, nx2, fi, im, os, c, Bk.Term.App{q, f, Bk.Term.Ann{y1, y2}}, Con{D.Rt{tc, tt}, bs}, fs, sp, pend2, ps2, ws.hs(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Ann{y1, y2}}, env, e, args, ys, pend2, ps2, w)))), {==},
        wp.set.k(h, 26n, 1, List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, fi, im, pg2, lim, inp, x => DW.WP(Cr.Cir.Stmt.nop{}, h, x, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, X.L.len(regs2, 23n, D.Fd(3n, m2, c), 63n, hl), {==},
          Inr{ex.one(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, pg2, c, Bk.Term.App{q, f, Bk.Term.Ann{y1, y2}}, env, e, args, ys, pend2, ps2, wr.set(23n, D.Fd(3n, m2, c), regs, keep, regs2, c, env, List.length(&2, El.Arg, e), args, pend2, hk, {==}, {==}, {==}, {==}, {==}, {==}, ws.wr(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Ann{y1, y2}}, env, e, args, ys, pend2, ps2, w)), hk,
            Equal.trans(Maybe<Maybe<Bk.Term>>, El.Eval.walk(tt, Nil{}, xs), El.Eval.walk(Bk.Term.App{q, f, Bk.Term.Ann{y1, y2}}, D.Arg.terms(e), ys),
              Some{Some{El.Term.spine(ys, El.Term.subst(Bk.Term.App{q, f, Bk.Term.Ann{y1, y2}}, D.Arg.terms(e), 0n))}}, ws.ev(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Ann{y1, y2}}, env, e, args, ys, pend2, ps2, w), {==}),
            ws.st(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Ann{y1, y2}}, env, e, args, ys, pend2, ps2, w), ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Ann{y1, y2}}, env, e, args, ys, pend2, ps2, w))}))
    case Bk.Term.Let{+q1, +v1, +f1}:
      wp.if.bt(Wap.e1(), h, Mc.M.ne(Mc.M.tag(Mc.M.g(Mc.R.wx())), Mc.M.c(Mc.T.var())), Mc.M.set(Mc.R.wres(), Mc.M.c(1)), X.X.st(List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, fi, im, pg2, lim, inp), t => DW.WP(Cr.Cir.Stmt.nop{}, h, t, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, lim,
        U32.is_ne(D.A.tag(Bk.Term.Let{q1, v1, f1}), 0), {==},
        app.t1(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, c, Bk.Term.Let{q1, v1, f1}, hl, is.app.y(ds, m2, im, fi, nx2, ks, img, c, q, f, Bk.Term.Let{q1, v1, f1}, hs.is(ds, ks, img, m2, nx2, fi, im, os, c, Bk.Term.App{q, f, Bk.Term.Let{q1, v1, f1}}, Con{D.Rt{tc, tt}, bs}, fs, sp, pend2, ps2, ws.hs(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Let{q1, v1, f1}}, env, e, args, ys, pend2, ps2, w)))), {==},
        wp.set.k(h, 26n, 1, List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, fi, im, pg2, lim, inp, x => DW.WP(Cr.Cir.Stmt.nop{}, h, x, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, X.L.len(regs2, 23n, D.Fd(3n, m2, c), 63n, hl), {==},
          Inr{ex.one(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, pg2, c, Bk.Term.App{q, f, Bk.Term.Let{q1, v1, f1}}, env, e, args, ys, pend2, ps2, wr.set(23n, D.Fd(3n, m2, c), regs, keep, regs2, c, env, List.length(&2, El.Arg, e), args, pend2, hk, {==}, {==}, {==}, {==}, {==}, {==}, ws.wr(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Let{q1, v1, f1}}, env, e, args, ys, pend2, ps2, w)), hk,
            Equal.trans(Maybe<Maybe<Bk.Term>>, El.Eval.walk(tt, Nil{}, xs), El.Eval.walk(Bk.Term.App{q, f, Bk.Term.Let{q1, v1, f1}}, D.Arg.terms(e), ys),
              Some{Some{El.Term.spine(ys, El.Term.subst(Bk.Term.App{q, f, Bk.Term.Let{q1, v1, f1}}, D.Arg.terms(e), 0n))}}, ws.ev(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Let{q1, v1, f1}}, env, e, args, ys, pend2, ps2, w), {==}),
            ws.st(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Let{q1, v1, f1}}, env, e, args, ys, pend2, ps2, w), ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Let{q1, v1, f1}}, env, e, args, ys, pend2, ps2, w))}))
    case Bk.Term.Typ{+y1}:
      wp.if.bt(Wap.e1(), h, Mc.M.ne(Mc.M.tag(Mc.M.g(Mc.R.wx())), Mc.M.c(Mc.T.var())), Mc.M.set(Mc.R.wres(), Mc.M.c(1)), X.X.st(List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, fi, im, pg2, lim, inp), t => DW.WP(Cr.Cir.Stmt.nop{}, h, t, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, lim,
        U32.is_ne(D.A.tag(Bk.Term.Typ{y1}), 0), {==},
        app.t1(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, c, Bk.Term.Typ{y1}, hl, is.app.y(ds, m2, im, fi, nx2, ks, img, c, q, f, Bk.Term.Typ{y1}, hs.is(ds, ks, img, m2, nx2, fi, im, os, c, Bk.Term.App{q, f, Bk.Term.Typ{y1}}, Con{D.Rt{tc, tt}, bs}, fs, sp, pend2, ps2, ws.hs(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Typ{y1}}, env, e, args, ys, pend2, ps2, w)))), {==},
        wp.set.k(h, 26n, 1, List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, fi, im, pg2, lim, inp, x => DW.WP(Cr.Cir.Stmt.nop{}, h, x, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, X.L.len(regs2, 23n, D.Fd(3n, m2, c), 63n, hl), {==},
          Inr{ex.one(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, pg2, c, Bk.Term.App{q, f, Bk.Term.Typ{y1}}, env, e, args, ys, pend2, ps2, wr.set(23n, D.Fd(3n, m2, c), regs, keep, regs2, c, env, List.length(&2, El.Arg, e), args, pend2, hk, {==}, {==}, {==}, {==}, {==}, {==}, ws.wr(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Typ{y1}}, env, e, args, ys, pend2, ps2, w)), hk,
            Equal.trans(Maybe<Maybe<Bk.Term>>, El.Eval.walk(tt, Nil{}, xs), El.Eval.walk(Bk.Term.App{q, f, Bk.Term.Typ{y1}}, D.Arg.terms(e), ys),
              Some{Some{El.Term.spine(ys, El.Term.subst(Bk.Term.App{q, f, Bk.Term.Typ{y1}}, D.Arg.terms(e), 0n))}}, ws.ev(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Typ{y1}}, env, e, args, ys, pend2, ps2, w), {==}),
            ws.st(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Typ{y1}}, env, e, args, ys, pend2, ps2, w), ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Typ{y1}}, env, e, args, ys, pend2, ps2, w))}))
    case Bk.Term.Min{+y1, +y2}:
      wp.if.bt(Wap.e1(), h, Mc.M.ne(Mc.M.tag(Mc.M.g(Mc.R.wx())), Mc.M.c(Mc.T.var())), Mc.M.set(Mc.R.wres(), Mc.M.c(1)), X.X.st(List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, fi, im, pg2, lim, inp), t => DW.WP(Cr.Cir.Stmt.nop{}, h, t, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, lim,
        U32.is_ne(D.A.tag(Bk.Term.Min{y1, y2}), 0), {==},
        app.t1(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, c, Bk.Term.Min{y1, y2}, hl, is.app.y(ds, m2, im, fi, nx2, ks, img, c, q, f, Bk.Term.Min{y1, y2}, hs.is(ds, ks, img, m2, nx2, fi, im, os, c, Bk.Term.App{q, f, Bk.Term.Min{y1, y2}}, Con{D.Rt{tc, tt}, bs}, fs, sp, pend2, ps2, ws.hs(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Min{y1, y2}}, env, e, args, ys, pend2, ps2, w)))), {==},
        wp.set.k(h, 26n, 1, List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, fi, im, pg2, lim, inp, x => DW.WP(Cr.Cir.Stmt.nop{}, h, x, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, X.L.len(regs2, 23n, D.Fd(3n, m2, c), 63n, hl), {==},
          Inr{ex.one(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, pg2, c, Bk.Term.App{q, f, Bk.Term.Min{y1, y2}}, env, e, args, ys, pend2, ps2, wr.set(23n, D.Fd(3n, m2, c), regs, keep, regs2, c, env, List.length(&2, El.Arg, e), args, pend2, hk, {==}, {==}, {==}, {==}, {==}, {==}, ws.wr(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Min{y1, y2}}, env, e, args, ys, pend2, ps2, w)), hk,
            Equal.trans(Maybe<Maybe<Bk.Term>>, El.Eval.walk(tt, Nil{}, xs), El.Eval.walk(Bk.Term.App{q, f, Bk.Term.Min{y1, y2}}, D.Arg.terms(e), ys),
              Some{Some{El.Term.spine(ys, El.Term.subst(Bk.Term.App{q, f, Bk.Term.Min{y1, y2}}, D.Arg.terms(e), 0n))}}, ws.ev(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Min{y1, y2}}, env, e, args, ys, pend2, ps2, w), {==}),
            ws.st(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Min{y1, y2}}, env, e, args, ys, pend2, ps2, w), ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Min{y1, y2}}, env, e, args, ys, pend2, ps2, w))}))
    case Bk.Term.All{+q1, +y1, +y2}:
      wp.if.bt(Wap.e1(), h, Mc.M.ne(Mc.M.tag(Mc.M.g(Mc.R.wx())), Mc.M.c(Mc.T.var())), Mc.M.set(Mc.R.wres(), Mc.M.c(1)), X.X.st(List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, fi, im, pg2, lim, inp), t => DW.WP(Cr.Cir.Stmt.nop{}, h, t, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, lim,
        U32.is_ne(D.A.tag(Bk.Term.All{q1, y1, y2}), 0), {==},
        app.t1(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, c, Bk.Term.All{q1, y1, y2}, hl, is.app.y(ds, m2, im, fi, nx2, ks, img, c, q, f, Bk.Term.All{q1, y1, y2}, hs.is(ds, ks, img, m2, nx2, fi, im, os, c, Bk.Term.App{q, f, Bk.Term.All{q1, y1, y2}}, Con{D.Rt{tc, tt}, bs}, fs, sp, pend2, ps2, ws.hs(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.All{q1, y1, y2}}, env, e, args, ys, pend2, ps2, w)))), {==},
        wp.set.k(h, 26n, 1, List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, fi, im, pg2, lim, inp, x => DW.WP(Cr.Cir.Stmt.nop{}, h, x, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, X.L.len(regs2, 23n, D.Fd(3n, m2, c), 63n, hl), {==},
          Inr{ex.one(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, pg2, c, Bk.Term.App{q, f, Bk.Term.All{q1, y1, y2}}, env, e, args, ys, pend2, ps2, wr.set(23n, D.Fd(3n, m2, c), regs, keep, regs2, c, env, List.length(&2, El.Arg, e), args, pend2, hk, {==}, {==}, {==}, {==}, {==}, {==}, ws.wr(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.All{q1, y1, y2}}, env, e, args, ys, pend2, ps2, w)), hk,
            Equal.trans(Maybe<Maybe<Bk.Term>>, El.Eval.walk(tt, Nil{}, xs), El.Eval.walk(Bk.Term.App{q, f, Bk.Term.All{q1, y1, y2}}, D.Arg.terms(e), ys),
              Some{Some{El.Term.spine(ys, El.Term.subst(Bk.Term.App{q, f, Bk.Term.All{q1, y1, y2}}, D.Arg.terms(e), 0n))}}, ws.ev(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.All{q1, y1, y2}}, env, e, args, ys, pend2, ps2, w), {==}),
            ws.st(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.All{q1, y1, y2}}, env, e, args, ys, pend2, ps2, w), ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.All{q1, y1, y2}}, env, e, args, ys, pend2, ps2, w))}))
    case Bk.Term.Lam{+q1, +f1}:
      wp.if.bt(Wap.e1(), h, Mc.M.ne(Mc.M.tag(Mc.M.g(Mc.R.wx())), Mc.M.c(Mc.T.var())), Mc.M.set(Mc.R.wres(), Mc.M.c(1)), X.X.st(List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, fi, im, pg2, lim, inp), t => DW.WP(Cr.Cir.Stmt.nop{}, h, t, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, lim,
        U32.is_ne(D.A.tag(Bk.Term.Lam{q1, f1}), 0), {==},
        app.t1(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, c, Bk.Term.Lam{q1, f1}, hl, is.app.y(ds, m2, im, fi, nx2, ks, img, c, q, f, Bk.Term.Lam{q1, f1}, hs.is(ds, ks, img, m2, nx2, fi, im, os, c, Bk.Term.App{q, f, Bk.Term.Lam{q1, f1}}, Con{D.Rt{tc, tt}, bs}, fs, sp, pend2, ps2, ws.hs(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Lam{q1, f1}}, env, e, args, ys, pend2, ps2, w)))), {==},
        wp.set.k(h, 26n, 1, List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, fi, im, pg2, lim, inp, x => DW.WP(Cr.Cir.Stmt.nop{}, h, x, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, X.L.len(regs2, 23n, D.Fd(3n, m2, c), 63n, hl), {==},
          Inr{ex.one(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, pg2, c, Bk.Term.App{q, f, Bk.Term.Lam{q1, f1}}, env, e, args, ys, pend2, ps2, wr.set(23n, D.Fd(3n, m2, c), regs, keep, regs2, c, env, List.length(&2, El.Arg, e), args, pend2, hk, {==}, {==}, {==}, {==}, {==}, {==}, ws.wr(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Lam{q1, f1}}, env, e, args, ys, pend2, ps2, w)), hk,
            Equal.trans(Maybe<Maybe<Bk.Term>>, El.Eval.walk(tt, Nil{}, xs), El.Eval.walk(Bk.Term.App{q, f, Bk.Term.Lam{q1, f1}}, D.Arg.terms(e), ys),
              Some{Some{El.Term.spine(ys, El.Term.subst(Bk.Term.App{q, f, Bk.Term.Lam{q1, f1}}, D.Arg.terms(e), 0n))}}, ws.ev(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Lam{q1, f1}}, env, e, args, ys, pend2, ps2, w), {==}),
            ws.st(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Lam{q1, f1}}, env, e, args, ys, pend2, ps2, w), ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Lam{q1, f1}}, env, e, args, ys, pend2, ps2, w))}))
    case Bk.Term.App{+q1, +f1, +y1}:
      wp.if.bt(Wap.e1(), h, Mc.M.ne(Mc.M.tag(Mc.M.g(Mc.R.wx())), Mc.M.c(Mc.T.var())), Mc.M.set(Mc.R.wres(), Mc.M.c(1)), X.X.st(List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, fi, im, pg2, lim, inp), t => DW.WP(Cr.Cir.Stmt.nop{}, h, t, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, lim,
        U32.is_ne(D.A.tag(Bk.Term.App{q1, f1, y1}), 0), {==},
        app.t1(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, c, Bk.Term.App{q1, f1, y1}, hl, is.app.y(ds, m2, im, fi, nx2, ks, img, c, q, f, Bk.Term.App{q1, f1, y1}, hs.is(ds, ks, img, m2, nx2, fi, im, os, c, Bk.Term.App{q, f, Bk.Term.App{q1, f1, y1}}, Con{D.Rt{tc, tt}, bs}, fs, sp, pend2, ps2, ws.hs(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.App{q1, f1, y1}}, env, e, args, ys, pend2, ps2, w)))), {==},
        wp.set.k(h, 26n, 1, List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, fi, im, pg2, lim, inp, x => DW.WP(Cr.Cir.Stmt.nop{}, h, x, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, X.L.len(regs2, 23n, D.Fd(3n, m2, c), 63n, hl), {==},
          Inr{ex.one(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, pg2, c, Bk.Term.App{q, f, Bk.Term.App{q1, f1, y1}}, env, e, args, ys, pend2, ps2, wr.set(23n, D.Fd(3n, m2, c), regs, keep, regs2, c, env, List.length(&2, El.Arg, e), args, pend2, hk, {==}, {==}, {==}, {==}, {==}, {==}, ws.wr(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.App{q1, f1, y1}}, env, e, args, ys, pend2, ps2, w)), hk,
            Equal.trans(Maybe<Maybe<Bk.Term>>, El.Eval.walk(tt, Nil{}, xs), El.Eval.walk(Bk.Term.App{q, f, Bk.Term.App{q1, f1, y1}}, D.Arg.terms(e), ys),
              Some{Some{El.Term.spine(ys, El.Term.subst(Bk.Term.App{q, f, Bk.Term.App{q1, f1, y1}}, D.Arg.terms(e), 0n))}}, ws.ev(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.App{q1, f1, y1}}, env, e, args, ys, pend2, ps2, w), {==}),
            ws.st(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.App{q1, f1, y1}}, env, e, args, ys, pend2, ps2, w), ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.App{q1, f1, y1}}, env, e, args, ys, pend2, ps2, w))}))
    case Bk.Term.Sig{+q1, +y1, +y2}:
      wp.if.bt(Wap.e1(), h, Mc.M.ne(Mc.M.tag(Mc.M.g(Mc.R.wx())), Mc.M.c(Mc.T.var())), Mc.M.set(Mc.R.wres(), Mc.M.c(1)), X.X.st(List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, fi, im, pg2, lim, inp), t => DW.WP(Cr.Cir.Stmt.nop{}, h, t, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, lim,
        U32.is_ne(D.A.tag(Bk.Term.Sig{q1, y1, y2}), 0), {==},
        app.t1(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, c, Bk.Term.Sig{q1, y1, y2}, hl, is.app.y(ds, m2, im, fi, nx2, ks, img, c, q, f, Bk.Term.Sig{q1, y1, y2}, hs.is(ds, ks, img, m2, nx2, fi, im, os, c, Bk.Term.App{q, f, Bk.Term.Sig{q1, y1, y2}}, Con{D.Rt{tc, tt}, bs}, fs, sp, pend2, ps2, ws.hs(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Sig{q1, y1, y2}}, env, e, args, ys, pend2, ps2, w)))), {==},
        wp.set.k(h, 26n, 1, List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, fi, im, pg2, lim, inp, x => DW.WP(Cr.Cir.Stmt.nop{}, h, x, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, X.L.len(regs2, 23n, D.Fd(3n, m2, c), 63n, hl), {==},
          Inr{ex.one(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, pg2, c, Bk.Term.App{q, f, Bk.Term.Sig{q1, y1, y2}}, env, e, args, ys, pend2, ps2, wr.set(23n, D.Fd(3n, m2, c), regs, keep, regs2, c, env, List.length(&2, El.Arg, e), args, pend2, hk, {==}, {==}, {==}, {==}, {==}, {==}, ws.wr(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Sig{q1, y1, y2}}, env, e, args, ys, pend2, ps2, w)), hk,
            Equal.trans(Maybe<Maybe<Bk.Term>>, El.Eval.walk(tt, Nil{}, xs), El.Eval.walk(Bk.Term.App{q, f, Bk.Term.Sig{q1, y1, y2}}, D.Arg.terms(e), ys),
              Some{Some{El.Term.spine(ys, El.Term.subst(Bk.Term.App{q, f, Bk.Term.Sig{q1, y1, y2}}, D.Arg.terms(e), 0n))}}, ws.ev(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Sig{q1, y1, y2}}, env, e, args, ys, pend2, ps2, w), {==}),
            ws.st(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Sig{q1, y1, y2}}, env, e, args, ys, pend2, ps2, w), ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Sig{q1, y1, y2}}, env, e, args, ys, pend2, ps2, w))}))
    case Bk.Term.Tup{+q1, +y1, +y2}:
      wp.if.bt(Wap.e1(), h, Mc.M.ne(Mc.M.tag(Mc.M.g(Mc.R.wx())), Mc.M.c(Mc.T.var())), Mc.M.set(Mc.R.wres(), Mc.M.c(1)), X.X.st(List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, fi, im, pg2, lim, inp), t => DW.WP(Cr.Cir.Stmt.nop{}, h, t, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, lim,
        U32.is_ne(D.A.tag(Bk.Term.Tup{q1, y1, y2}), 0), {==},
        app.t1(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, c, Bk.Term.Tup{q1, y1, y2}, hl, is.app.y(ds, m2, im, fi, nx2, ks, img, c, q, f, Bk.Term.Tup{q1, y1, y2}, hs.is(ds, ks, img, m2, nx2, fi, im, os, c, Bk.Term.App{q, f, Bk.Term.Tup{q1, y1, y2}}, Con{D.Rt{tc, tt}, bs}, fs, sp, pend2, ps2, ws.hs(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Tup{q1, y1, y2}}, env, e, args, ys, pend2, ps2, w)))), {==},
        wp.set.k(h, 26n, 1, List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, fi, im, pg2, lim, inp, x => DW.WP(Cr.Cir.Stmt.nop{}, h, x, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, X.L.len(regs2, 23n, D.Fd(3n, m2, c), 63n, hl), {==},
          Inr{ex.one(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, pg2, c, Bk.Term.App{q, f, Bk.Term.Tup{q1, y1, y2}}, env, e, args, ys, pend2, ps2, wr.set(23n, D.Fd(3n, m2, c), regs, keep, regs2, c, env, List.length(&2, El.Arg, e), args, pend2, hk, {==}, {==}, {==}, {==}, {==}, {==}, ws.wr(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Tup{q1, y1, y2}}, env, e, args, ys, pend2, ps2, w)), hk,
            Equal.trans(Maybe<Maybe<Bk.Term>>, El.Eval.walk(tt, Nil{}, xs), El.Eval.walk(Bk.Term.App{q, f, Bk.Term.Tup{q1, y1, y2}}, D.Arg.terms(e), ys),
              Some{Some{El.Term.spine(ys, El.Term.subst(Bk.Term.App{q, f, Bk.Term.Tup{q1, y1, y2}}, D.Arg.terms(e), 0n))}}, ws.ev(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Tup{q1, y1, y2}}, env, e, args, ys, pend2, ps2, w), {==}),
            ws.st(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Tup{q1, y1, y2}}, env, e, args, ys, pend2, ps2, w), ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Tup{q1, y1, y2}}, env, e, args, ys, pend2, ps2, w))}))
    case Bk.Term.Prj{+h1}:
      wp.if.bt(Wap.e1(), h, Mc.M.ne(Mc.M.tag(Mc.M.g(Mc.R.wx())), Mc.M.c(Mc.T.var())), Mc.M.set(Mc.R.wres(), Mc.M.c(1)), X.X.st(List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, fi, im, pg2, lim, inp), t => DW.WP(Cr.Cir.Stmt.nop{}, h, t, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, lim,
        U32.is_ne(D.A.tag(Bk.Term.Prj{h1}), 0), {==},
        app.t1(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, c, Bk.Term.Prj{h1}, hl, is.app.y(ds, m2, im, fi, nx2, ks, img, c, q, f, Bk.Term.Prj{h1}, hs.is(ds, ks, img, m2, nx2, fi, im, os, c, Bk.Term.App{q, f, Bk.Term.Prj{h1}}, Con{D.Rt{tc, tt}, bs}, fs, sp, pend2, ps2, ws.hs(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Prj{h1}}, env, e, args, ys, pend2, ps2, w)))), {==},
        wp.set.k(h, 26n, 1, List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, fi, im, pg2, lim, inp, x => DW.WP(Cr.Cir.Stmt.nop{}, h, x, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, X.L.len(regs2, 23n, D.Fd(3n, m2, c), 63n, hl), {==},
          Inr{ex.one(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, pg2, c, Bk.Term.App{q, f, Bk.Term.Prj{h1}}, env, e, args, ys, pend2, ps2, wr.set(23n, D.Fd(3n, m2, c), regs, keep, regs2, c, env, List.length(&2, El.Arg, e), args, pend2, hk, {==}, {==}, {==}, {==}, {==}, {==}, ws.wr(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Prj{h1}}, env, e, args, ys, pend2, ps2, w)), hk,
            Equal.trans(Maybe<Maybe<Bk.Term>>, El.Eval.walk(tt, Nil{}, xs), El.Eval.walk(Bk.Term.App{q, f, Bk.Term.Prj{h1}}, D.Arg.terms(e), ys),
              Some{Some{El.Term.spine(ys, El.Term.subst(Bk.Term.App{q, f, Bk.Term.Prj{h1}}, D.Arg.terms(e), 0n))}}, ws.ev(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Prj{h1}}, env, e, args, ys, pend2, ps2, w), {==}),
            ws.st(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Prj{h1}}, env, e, args, ys, pend2, ps2, w), ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Prj{h1}}, env, e, args, ys, pend2, ps2, w))}))
    case Bk.Term.Enu{+kk}:
      wp.if.bt(Wap.e1(), h, Mc.M.ne(Mc.M.tag(Mc.M.g(Mc.R.wx())), Mc.M.c(Mc.T.var())), Mc.M.set(Mc.R.wres(), Mc.M.c(1)), X.X.st(List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, fi, im, pg2, lim, inp), t => DW.WP(Cr.Cir.Stmt.nop{}, h, t, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, lim,
        U32.is_ne(D.A.tag(Bk.Term.Enu{kk}), 0), {==},
        app.t1(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, c, Bk.Term.Enu{kk}, hl, is.app.y(ds, m2, im, fi, nx2, ks, img, c, q, f, Bk.Term.Enu{kk}, hs.is(ds, ks, img, m2, nx2, fi, im, os, c, Bk.Term.App{q, f, Bk.Term.Enu{kk}}, Con{D.Rt{tc, tt}, bs}, fs, sp, pend2, ps2, ws.hs(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Enu{kk}}, env, e, args, ys, pend2, ps2, w)))), {==},
        wp.set.k(h, 26n, 1, List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, fi, im, pg2, lim, inp, x => DW.WP(Cr.Cir.Stmt.nop{}, h, x, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, X.L.len(regs2, 23n, D.Fd(3n, m2, c), 63n, hl), {==},
          Inr{ex.one(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, pg2, c, Bk.Term.App{q, f, Bk.Term.Enu{kk}}, env, e, args, ys, pend2, ps2, wr.set(23n, D.Fd(3n, m2, c), regs, keep, regs2, c, env, List.length(&2, El.Arg, e), args, pend2, hk, {==}, {==}, {==}, {==}, {==}, {==}, ws.wr(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Enu{kk}}, env, e, args, ys, pend2, ps2, w)), hk,
            Equal.trans(Maybe<Maybe<Bk.Term>>, El.Eval.walk(tt, Nil{}, xs), El.Eval.walk(Bk.Term.App{q, f, Bk.Term.Enu{kk}}, D.Arg.terms(e), ys),
              Some{Some{El.Term.spine(ys, El.Term.subst(Bk.Term.App{q, f, Bk.Term.Enu{kk}}, D.Arg.terms(e), 0n))}}, ws.ev(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Enu{kk}}, env, e, args, ys, pend2, ps2, w), {==}),
            ws.st(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Enu{kk}}, env, e, args, ys, pend2, ps2, w), ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Enu{kk}}, env, e, args, ys, pend2, ps2, w))}))
    case Bk.Term.Lab{+kk}:
      wp.if.bt(Wap.e1(), h, Mc.M.ne(Mc.M.tag(Mc.M.g(Mc.R.wx())), Mc.M.c(Mc.T.var())), Mc.M.set(Mc.R.wres(), Mc.M.c(1)), X.X.st(List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, fi, im, pg2, lim, inp), t => DW.WP(Cr.Cir.Stmt.nop{}, h, t, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, lim,
        U32.is_ne(D.A.tag(Bk.Term.Lab{kk}), 0), {==},
        app.t1(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, c, Bk.Term.Lab{kk}, hl, is.app.y(ds, m2, im, fi, nx2, ks, img, c, q, f, Bk.Term.Lab{kk}, hs.is(ds, ks, img, m2, nx2, fi, im, os, c, Bk.Term.App{q, f, Bk.Term.Lab{kk}}, Con{D.Rt{tc, tt}, bs}, fs, sp, pend2, ps2, ws.hs(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Lab{kk}}, env, e, args, ys, pend2, ps2, w)))), {==},
        wp.set.k(h, 26n, 1, List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, fi, im, pg2, lim, inp, x => DW.WP(Cr.Cir.Stmt.nop{}, h, x, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, X.L.len(regs2, 23n, D.Fd(3n, m2, c), 63n, hl), {==},
          Inr{ex.one(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, pg2, c, Bk.Term.App{q, f, Bk.Term.Lab{kk}}, env, e, args, ys, pend2, ps2, wr.set(23n, D.Fd(3n, m2, c), regs, keep, regs2, c, env, List.length(&2, El.Arg, e), args, pend2, hk, {==}, {==}, {==}, {==}, {==}, {==}, ws.wr(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Lab{kk}}, env, e, args, ys, pend2, ps2, w)), hk,
            Equal.trans(Maybe<Maybe<Bk.Term>>, El.Eval.walk(tt, Nil{}, xs), El.Eval.walk(Bk.Term.App{q, f, Bk.Term.Lab{kk}}, D.Arg.terms(e), ys),
              Some{Some{El.Term.spine(ys, El.Term.subst(Bk.Term.App{q, f, Bk.Term.Lab{kk}}, D.Arg.terms(e), 0n))}}, ws.ev(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Lab{kk}}, env, e, args, ys, pend2, ps2, w), {==}),
            ws.st(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Lab{kk}}, env, e, args, ys, pend2, ps2, w), ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Lab{kk}}, env, e, args, ys, pend2, ps2, w))}))
    case Bk.Term.Mat{+kk, +h1, +n1}:
      wp.if.bt(Wap.e1(), h, Mc.M.ne(Mc.M.tag(Mc.M.g(Mc.R.wx())), Mc.M.c(Mc.T.var())), Mc.M.set(Mc.R.wres(), Mc.M.c(1)), X.X.st(List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, fi, im, pg2, lim, inp), t => DW.WP(Cr.Cir.Stmt.nop{}, h, t, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, lim,
        U32.is_ne(D.A.tag(Bk.Term.Mat{kk, h1, n1}), 0), {==},
        app.t1(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, c, Bk.Term.Mat{kk, h1, n1}, hl, is.app.y(ds, m2, im, fi, nx2, ks, img, c, q, f, Bk.Term.Mat{kk, h1, n1}, hs.is(ds, ks, img, m2, nx2, fi, im, os, c, Bk.Term.App{q, f, Bk.Term.Mat{kk, h1, n1}}, Con{D.Rt{tc, tt}, bs}, fs, sp, pend2, ps2, ws.hs(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Mat{kk, h1, n1}}, env, e, args, ys, pend2, ps2, w)))), {==},
        wp.set.k(h, 26n, 1, List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, fi, im, pg2, lim, inp, x => DW.WP(Cr.Cir.Stmt.nop{}, h, x, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, X.L.len(regs2, 23n, D.Fd(3n, m2, c), 63n, hl), {==},
          Inr{ex.one(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, pg2, c, Bk.Term.App{q, f, Bk.Term.Mat{kk, h1, n1}}, env, e, args, ys, pend2, ps2, wr.set(23n, D.Fd(3n, m2, c), regs, keep, regs2, c, env, List.length(&2, El.Arg, e), args, pend2, hk, {==}, {==}, {==}, {==}, {==}, {==}, ws.wr(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Mat{kk, h1, n1}}, env, e, args, ys, pend2, ps2, w)), hk,
            Equal.trans(Maybe<Maybe<Bk.Term>>, El.Eval.walk(tt, Nil{}, xs), El.Eval.walk(Bk.Term.App{q, f, Bk.Term.Mat{kk, h1, n1}}, D.Arg.terms(e), ys),
              Some{Some{El.Term.spine(ys, El.Term.subst(Bk.Term.App{q, f, Bk.Term.Mat{kk, h1, n1}}, D.Arg.terms(e), 0n))}}, ws.ev(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Mat{kk, h1, n1}}, env, e, args, ys, pend2, ps2, w), {==}),
            ws.st(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Mat{kk, h1, n1}}, env, e, args, ys, pend2, ps2, w), ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Mat{kk, h1, n1}}, env, e, args, ys, pend2, ps2, w))}))
    case Bk.Term.Efq{}:
      wp.if.bt(Wap.e1(), h, Mc.M.ne(Mc.M.tag(Mc.M.g(Mc.R.wx())), Mc.M.c(Mc.T.var())), Mc.M.set(Mc.R.wres(), Mc.M.c(1)), X.X.st(List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, fi, im, pg2, lim, inp), t => DW.WP(Cr.Cir.Stmt.nop{}, h, t, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, lim,
        U32.is_ne(D.A.tag(Bk.Term.Efq{}), 0), {==},
        app.t1(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, c, Bk.Term.Efq{}, hl, is.app.y(ds, m2, im, fi, nx2, ks, img, c, q, f, Bk.Term.Efq{}, hs.is(ds, ks, img, m2, nx2, fi, im, os, c, Bk.Term.App{q, f, Bk.Term.Efq{}}, Con{D.Rt{tc, tt}, bs}, fs, sp, pend2, ps2, ws.hs(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Efq{}}, env, e, args, ys, pend2, ps2, w)))), {==},
        wp.set.k(h, 26n, 1, List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, fi, im, pg2, lim, inp, x => DW.WP(Cr.Cir.Stmt.nop{}, h, x, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, X.L.len(regs2, 23n, D.Fd(3n, m2, c), 63n, hl), {==},
          Inr{ex.one(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, pg2, c, Bk.Term.App{q, f, Bk.Term.Efq{}}, env, e, args, ys, pend2, ps2, wr.set(23n, D.Fd(3n, m2, c), regs, keep, regs2, c, env, List.length(&2, El.Arg, e), args, pend2, hk, {==}, {==}, {==}, {==}, {==}, {==}, ws.wr(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Efq{}}, env, e, args, ys, pend2, ps2, w)), hk,
            Equal.trans(Maybe<Maybe<Bk.Term>>, El.Eval.walk(tt, Nil{}, xs), El.Eval.walk(Bk.Term.App{q, f, Bk.Term.Efq{}}, D.Arg.terms(e), ys),
              Some{Some{El.Term.spine(ys, El.Term.subst(Bk.Term.App{q, f, Bk.Term.Efq{}}, D.Arg.terms(e), 0n))}}, ws.ev(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Efq{}}, env, e, args, ys, pend2, ps2, w), {==}),
            ws.st(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Efq{}}, env, e, args, ys, pend2, ps2, w), ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Efq{}}, env, e, args, ys, pend2, ps2, w))}))
    case Bk.Term.Eql{+y1, +y2, +y3}:
      wp.if.bt(Wap.e1(), h, Mc.M.ne(Mc.M.tag(Mc.M.g(Mc.R.wx())), Mc.M.c(Mc.T.var())), Mc.M.set(Mc.R.wres(), Mc.M.c(1)), X.X.st(List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, fi, im, pg2, lim, inp), t => DW.WP(Cr.Cir.Stmt.nop{}, h, t, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, lim,
        U32.is_ne(D.A.tag(Bk.Term.Eql{y1, y2, y3}), 0), {==},
        app.t1(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, c, Bk.Term.Eql{y1, y2, y3}, hl, is.app.y(ds, m2, im, fi, nx2, ks, img, c, q, f, Bk.Term.Eql{y1, y2, y3}, hs.is(ds, ks, img, m2, nx2, fi, im, os, c, Bk.Term.App{q, f, Bk.Term.Eql{y1, y2, y3}}, Con{D.Rt{tc, tt}, bs}, fs, sp, pend2, ps2, ws.hs(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Eql{y1, y2, y3}}, env, e, args, ys, pend2, ps2, w)))), {==},
        wp.set.k(h, 26n, 1, List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, fi, im, pg2, lim, inp, x => DW.WP(Cr.Cir.Stmt.nop{}, h, x, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, X.L.len(regs2, 23n, D.Fd(3n, m2, c), 63n, hl), {==},
          Inr{ex.one(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, pg2, c, Bk.Term.App{q, f, Bk.Term.Eql{y1, y2, y3}}, env, e, args, ys, pend2, ps2, wr.set(23n, D.Fd(3n, m2, c), regs, keep, regs2, c, env, List.length(&2, El.Arg, e), args, pend2, hk, {==}, {==}, {==}, {==}, {==}, {==}, ws.wr(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Eql{y1, y2, y3}}, env, e, args, ys, pend2, ps2, w)), hk,
            Equal.trans(Maybe<Maybe<Bk.Term>>, El.Eval.walk(tt, Nil{}, xs), El.Eval.walk(Bk.Term.App{q, f, Bk.Term.Eql{y1, y2, y3}}, D.Arg.terms(e), ys),
              Some{Some{El.Term.spine(ys, El.Term.subst(Bk.Term.App{q, f, Bk.Term.Eql{y1, y2, y3}}, D.Arg.terms(e), 0n))}}, ws.ev(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Eql{y1, y2, y3}}, env, e, args, ys, pend2, ps2, w), {==}),
            ws.st(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Eql{y1, y2, y3}}, env, e, args, ys, pend2, ps2, w), ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Eql{y1, y2, y3}}, env, e, args, ys, pend2, ps2, w))}))
    case Bk.Term.Rfl{}:
      wp.if.bt(Wap.e1(), h, Mc.M.ne(Mc.M.tag(Mc.M.g(Mc.R.wx())), Mc.M.c(Mc.T.var())), Mc.M.set(Mc.R.wres(), Mc.M.c(1)), X.X.st(List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, fi, im, pg2, lim, inp), t => DW.WP(Cr.Cir.Stmt.nop{}, h, t, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, lim,
        U32.is_ne(D.A.tag(Bk.Term.Rfl{}), 0), {==},
        app.t1(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, c, Bk.Term.Rfl{}, hl, is.app.y(ds, m2, im, fi, nx2, ks, img, c, q, f, Bk.Term.Rfl{}, hs.is(ds, ks, img, m2, nx2, fi, im, os, c, Bk.Term.App{q, f, Bk.Term.Rfl{}}, Con{D.Rt{tc, tt}, bs}, fs, sp, pend2, ps2, ws.hs(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Rfl{}}, env, e, args, ys, pend2, ps2, w)))), {==},
        wp.set.k(h, 26n, 1, List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, fi, im, pg2, lim, inp, x => DW.WP(Cr.Cir.Stmt.nop{}, h, x, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, X.L.len(regs2, 23n, D.Fd(3n, m2, c), 63n, hl), {==},
          Inr{ex.one(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, pg2, c, Bk.Term.App{q, f, Bk.Term.Rfl{}}, env, e, args, ys, pend2, ps2, wr.set(23n, D.Fd(3n, m2, c), regs, keep, regs2, c, env, List.length(&2, El.Arg, e), args, pend2, hk, {==}, {==}, {==}, {==}, {==}, {==}, ws.wr(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Rfl{}}, env, e, args, ys, pend2, ps2, w)), hk,
            Equal.trans(Maybe<Maybe<Bk.Term>>, El.Eval.walk(tt, Nil{}, xs), El.Eval.walk(Bk.Term.App{q, f, Bk.Term.Rfl{}}, D.Arg.terms(e), ys),
              Some{Some{El.Term.spine(ys, El.Term.subst(Bk.Term.App{q, f, Bk.Term.Rfl{}}, D.Arg.terms(e), 0n))}}, ws.ev(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Rfl{}}, env, e, args, ys, pend2, ps2, w), {==}),
            ws.st(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Rfl{}}, env, e, args, ys, pend2, ps2, w), ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Rfl{}}, env, e, args, ys, pend2, ps2, w))}))
    case Bk.Term.Rwt{+y1, +y2, +y3}:
      wp.if.bt(Wap.e1(), h, Mc.M.ne(Mc.M.tag(Mc.M.g(Mc.R.wx())), Mc.M.c(Mc.T.var())), Mc.M.set(Mc.R.wres(), Mc.M.c(1)), X.X.st(List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, fi, im, pg2, lim, inp), t => DW.WP(Cr.Cir.Stmt.nop{}, h, t, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, lim,
        U32.is_ne(D.A.tag(Bk.Term.Rwt{y1, y2, y3}), 0), {==},
        app.t1(regs2, m2, nx2, fi, im, pg2, lim, inp, ds, ks, img, c, Bk.Term.Rwt{y1, y2, y3}, hl, is.app.y(ds, m2, im, fi, nx2, ks, img, c, q, f, Bk.Term.Rwt{y1, y2, y3}, hs.is(ds, ks, img, m2, nx2, fi, im, os, c, Bk.Term.App{q, f, Bk.Term.Rwt{y1, y2, y3}}, Con{D.Rt{tc, tt}, bs}, fs, sp, pend2, ps2, ws.hs(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Rwt{y1, y2, y3}}, env, e, args, ys, pend2, ps2, w)))), {==},
        wp.set.k(h, 26n, 1, List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, fi, im, pg2, lim, inp, x => DW.WP(Cr.Cir.Stmt.nop{}, h, x, x => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, x), B, lim), B, X.L.len(regs2, 23n, D.Fd(3n, m2, c), 63n, hl), {==},
          Inr{ex.one(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, List.set(&2, U32, regs2, 23n, D.Fd(3n, m2, c)), m2, nx2, pg2, c, Bk.Term.App{q, f, Bk.Term.Rwt{y1, y2, y3}}, env, e, args, ys, pend2, ps2, wr.set(23n, D.Fd(3n, m2, c), regs, keep, regs2, c, env, List.length(&2, El.Arg, e), args, pend2, hk, {==}, {==}, {==}, {==}, {==}, {==}, ws.wr(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Rwt{y1, y2, y3}}, env, e, args, ys, pend2, ps2, w)), hk,
            Equal.trans(Maybe<Maybe<Bk.Term>>, El.Eval.walk(tt, Nil{}, xs), El.Eval.walk(Bk.Term.App{q, f, Bk.Term.Rwt{y1, y2, y3}}, D.Arg.terms(e), ys),
              Some{Some{El.Term.spine(ys, El.Term.subst(Bk.Term.App{q, f, Bk.Term.Rwt{y1, y2, y3}}, D.Arg.terms(e), 0n))}}, ws.ev(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Rwt{y1, y2, y3}}, env, e, args, ys, pend2, ps2, w), {==}),
            ws.st(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Rwt{y1, y2, y3}}, env, e, args, ys, pend2, ps2, w), ws.wh(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, Bk.Term.Rwt{y1, y2, y3}}, env, e, args, ys, pend2, ps2, w))}))

# the round of an App: the local of its Var goes first among the arguments, or wres 1
def round.app(+h: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +keep: List<&2, Nat>,
  +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +tc: U32, +tt: Bk.Term,
  +a: U32, +xs: List<&2, El.Arg>, +xs0: List<&2, D.TmpE>, +B: Nat, +hk: {D.Disj(keep, D.Walk.scr()) == True{} : Bool},
  +regs2: List<&2, U32>, +m2: Cr.Cir.Cells, +nx2: U32, +pg2: U32, +c: U32, +q: Bk.Quan, +f: Bk.Term, +y: Bk.Term,
  +env: U32, +e: List<&2, El.Arg>, +args: U32, +ys: List<&2, El.Arg>, +pend2: U32, +ps2: List<&2, U32>,
  +w: WS(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, y}, env, e, args, ys, pend2, ps2)) ->
  DW.WP(Mc.M.walk.app(), h, X.X.st(regs2, m2, nx2, fi, im, pg2, lim, inp), u => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, u), B, lim):
  +hl = wr.len(regs, keep, regs2, c, env, List.length(&2, El.Arg, e), args, pend2, ws.wr(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, y}, env, e, args, ys, pend2, ps2, w))
  +h19 = wr.r19(regs, keep, regs2, c, env, List.length(&2, El.Arg, e), args, pend2, ws.wr(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, y}, env, e, args, ys, pend2, ps2, w))
  +hc = hs.cell(ds, ks, img, m2, nx2, fi, im, os, c, Bk.Term.App{q, f, y}, Con{D.Rt{tc, tt}, bs}, fs, sp, pend2, ps2, ws.hs(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, y}, env, e, args, ys, pend2, ps2, w))
  wp.set.e(23n, Mc.M.f(3n, Mc.M.g(Mc.R.wt())), D.Fd(3n, m2, c), regs2, m2, nx2, fi, im, pg2, lim, inp, h,
    t => DW.WP(Wap.r1(), h, t, u => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, u), B, lim), B,
    X.ev.fld(3n, Mc.M.g(Mc.R.wt()), X.X.st(regs2, m2, nx2, fi, im, pg2, lim, inp), c, h19, hc), hl, {==},
    app.if1(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, q, f, y, env, e, args, ys, pend2, ps2, w, hl, h19, hc))

# a round, from a round's start: by the subtree's form, which wt's tag tells
def W.round(+h: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +keep: List<&2, Nat>,
  +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +tc: U32, +tt: Bk.Term,
  +a: U32, +xs: List<&2, El.Arg>, +xs0: List<&2, D.TmpE>, +B: Nat, +hk: {D.Disj(keep, D.Walk.scr()) == True{} : Bool},
  +regs2: List<&2, U32>, +m2: Cr.Cir.Cells, +nx2: U32, +pg2: U32, +c: U32, +s: Bk.Term, +env: U32, +e: List<&2, El.Arg>,
  +args: U32, +ys: List<&2, El.Arg>, +pend2: U32, +ps2: List<&2, U32>,
  +w: WS(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, s, env, e, args, ys, pend2, ps2)) ->
  DW.WP(W.body(), h, X.X.st(regs2, m2, nx2, fi, im, pg2, lim, inp),
    u => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, u), B, lim):
  match s:
    case Bk.Term.Lam{+p, +f}:
      disp.lam(h, regs2, m2, nx2, fi, im, pg2, lim, inp, u => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, u), B, c,
        wr.r19(regs, keep, regs2, c, env, List.length(&2, El.Arg, e), args, pend2, ws.wr(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Lam{p, f}, env, e, args, ys, pend2, ps2, w)),
        hs.cell(ds, ks, img, m2, nx2, fi, im, os, c, Bk.Term.Lam{p, f}, Con{D.Rt{tc, tt}, bs}, fs, sp, pend2, ps2, ws.hs(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Lam{p, f}, env, e, args, ys, pend2, ps2, w)),
        hs.tg(ds, ks, img, m2, nx2, fi, im, os, c, Bk.Term.Lam{p, f}, Con{D.Rt{tc, tt}, bs}, fs, sp, pend2, ps2, ws.hs(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Lam{p, f}, env, e, args, ys, pend2, ps2, w)),
        round.lam(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, p, f, env, e, args, ys, pend2, ps2, w))
    case Bk.Term.Prj{+h0}:
      disp.prj(h, regs2, m2, nx2, fi, im, pg2, lim, inp, u => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, u), B, c,
        wr.r19(regs, keep, regs2, c, env, List.length(&2, El.Arg, e), args, pend2, ws.wr(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, ys, pend2, ps2, w)),
        hs.cell(ds, ks, img, m2, nx2, fi, im, os, c, Bk.Term.Prj{h0}, Con{D.Rt{tc, tt}, bs}, fs, sp, pend2, ps2, ws.hs(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, ys, pend2, ps2, w)),
        hs.tg(ds, ks, img, m2, nx2, fi, im, os, c, Bk.Term.Prj{h0}, Con{D.Rt{tc, tt}, bs}, fs, sp, pend2, ps2, ws.hs(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Prj{h0}, env, e, args, ys, pend2, ps2, w)),
        round.prj(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, h0, env, e, args, ys, pend2, ps2, w))
    case Bk.Term.Mat{+k, +h0, +n0}:
      disp.mat(h, regs2, m2, nx2, fi, im, pg2, lim, inp, u => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, u), B, c,
        wr.r19(regs, keep, regs2, c, env, List.length(&2, El.Arg, e), args, pend2, ws.wr(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, ys, pend2, ps2, w)),
        hs.cell(ds, ks, img, m2, nx2, fi, im, os, c, Bk.Term.Mat{k, h0, n0}, Con{D.Rt{tc, tt}, bs}, fs, sp, pend2, ps2, ws.hs(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, ys, pend2, ps2, w)),
        hs.tg(ds, ks, img, m2, nx2, fi, im, os, c, Bk.Term.Mat{k, h0, n0}, Con{D.Rt{tc, tt}, bs}, fs, sp, pend2, ps2, ws.hs(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Mat{k, h0, n0}, env, e, args, ys, pend2, ps2, w)),
        round.mat(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, k, h0, n0, env, e, args, ys, pend2, ps2, w))
    case Bk.Term.App{+q, +f, +y}:
      disp.app(h, regs2, m2, nx2, fi, im, pg2, lim, inp, u => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, u), B, c,
        wr.r19(regs, keep, regs2, c, env, List.length(&2, El.Arg, e), args, pend2, ws.wr(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, y}, env, e, args, ys, pend2, ps2, w)),
        hs.cell(ds, ks, img, m2, nx2, fi, im, os, c, Bk.Term.App{q, f, y}, Con{D.Rt{tc, tt}, bs}, fs, sp, pend2, ps2, ws.hs(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, y}, env, e, args, ys, pend2, ps2, w)),
        hs.tg(ds, ks, img, m2, nx2, fi, im, os, c, Bk.Term.App{q, f, y}, Con{D.Rt{tc, tt}, bs}, fs, sp, pend2, ps2, ws.hs(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.App{q, f, y}, env, e, args, ys, pend2, ps2, w)),
        round.app(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, q, f, y, env, e, args, ys, pend2, ps2, w))
    case Bk.Term.Efq{}:
      disp.efq(h, regs2, m2, nx2, fi, im, pg2, lim, inp, u => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, u), B, c,
        wr.r19(regs, keep, regs2, c, env, List.length(&2, El.Arg, e), args, pend2, ws.wr(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Efq{}, env, e, args, ys, pend2, ps2, w)),
        hs.cell(ds, ks, img, m2, nx2, fi, im, os, c, Bk.Term.Efq{}, Con{D.Rt{tc, tt}, bs}, fs, sp, pend2, ps2, ws.hs(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Efq{}, env, e, args, ys, pend2, ps2, w)),
        hs.tg(ds, ks, img, m2, nx2, fi, im, os, c, Bk.Term.Efq{}, Con{D.Rt{tc, tt}, bs}, fs, sp, pend2, ps2, ws.hs(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, Bk.Term.Efq{}, env, e, args, ys, pend2, ps2, w)),
        round.efq(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, env, e, args, ys, pend2, ps2, w))
    case Bk.Term.Var{+i}:
      round.leaf(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, Bk.Term.Var{i}, env, e, args, ys, pend2, ps2, w,
        {==}, {==}, {==}, {==}, {==}, {==})
    case Bk.Term.Ref{+k}:
      round.leaf(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, Bk.Term.Ref{k}, env, e, args, ys, pend2, ps2, w,
        {==}, {==}, {==}, {==}, {==}, {==})
    case Bk.Term.Ann{+x, +y}:
      round.leaf(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, Bk.Term.Ann{x, y}, env, e, args, ys, pend2, ps2, w,
        {==}, {==}, {==}, {==}, {==}, {==})
    case Bk.Term.Let{+q, +v, +f}:
      round.leaf(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, Bk.Term.Let{q, v, f}, env, e, args, ys, pend2, ps2, w,
        {==}, {==}, {==}, {==}, {==}, {==})
    case Bk.Term.Typ{+x}:
      round.leaf(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, Bk.Term.Typ{x}, env, e, args, ys, pend2, ps2, w,
        {==}, {==}, {==}, {==}, {==}, {==})
    case Bk.Term.Min{+x, +y}:
      round.leaf(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, Bk.Term.Min{x, y}, env, e, args, ys, pend2, ps2, w,
        {==}, {==}, {==}, {==}, {==}, {==})
    case Bk.Term.All{+q, +x, +y}:
      round.leaf(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, Bk.Term.All{q, x, y}, env, e, args, ys, pend2, ps2, w,
        {==}, {==}, {==}, {==}, {==}, {==})
    case Bk.Term.Sig{+q, +x, +y}:
      round.leaf(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, Bk.Term.Sig{q, x, y}, env, e, args, ys, pend2, ps2, w,
        {==}, {==}, {==}, {==}, {==}, {==})
    case Bk.Term.Tup{+q, +x, +y}:
      round.leaf(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, Bk.Term.Tup{q, x, y}, env, e, args, ys, pend2, ps2, w,
        {==}, {==}, {==}, {==}, {==}, {==})
    case Bk.Term.Enu{+k}:
      round.leaf(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, Bk.Term.Enu{k}, env, e, args, ys, pend2, ps2, w,
        {==}, {==}, {==}, {==}, {==}, {==})
    case Bk.Term.Lab{+k}:
      round.leaf(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, Bk.Term.Lab{k}, env, e, args, ys, pend2, ps2, w,
        {==}, {==}, {==}, {==}, {==}, {==})
    case Bk.Term.Eql{+x, +y, +z}:
      round.leaf(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, Bk.Term.Eql{x, y, z}, env, e, args, ys, pend2, ps2, w,
        {==}, {==}, {==}, {==}, {==}, {==})
    case Bk.Term.Rfl{}:
      round.leaf(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, Bk.Term.Rfl{}, env, e, args, ys, pend2, ps2, w,
        {==}, {==}, {==}, {==}, {==}, {==})
    case Bk.Term.Rwt{+x, +y, +z}:
      round.leaf(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, Bk.Term.Rwt{x, y, z}, env, e, args, ys, pend2, ps2, w,
        {==}, {==}, {==}, {==}, {==}, {==})

# the loop, from a round's end
def W.go(g: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +keep: List<&2, Nat>,
  +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +tc: U32, +tt: Bk.Term,
  +a: U32, +xs: List<&2, El.Arg>, +xs0: List<&2, D.TmpE>, +B: Nat, +hk: {D.Disj(keep, D.Walk.scr()) == True{} : Bool},
  t: Cr.Cir.State, j: WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, t)) ->
  DW.WP(W.while(), g, t,
    st2 => D.WalkQ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, Con{D.Rt{tc, tt}, bs}, fs, sp, ps, tt, a, xs, xs0, st2), B, lim):
  match g:
    case 0n:
      Unit{}
    case 1n+(+h):
      match j:
        case Inl{p}:
          (w, hw) = p
          match w:
            case WG{+regs2, +m2, +nx2, +pg2, +c, +s, +env, +e, +args, +ys, +pend2, +ps2}:
              (heq, +ws) = hw
              (%Equal.sym(Cr.Cir.State, t, X.X.st(regs2, m2, nx2, fi, im, pg2, lim, inp), heq) :
                DW.WP(W.while(), 1n+h, _, st2 => D.WalkQ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, Con{D.Rt{tc, tt}, bs}, fs, sp, ps, tt, a, xs, xs0, st2), B, lim);
               (lp.ob(regs2, m2, nx2, fi, im, pg2, lim, inp, Nil{}, 0, 0, ws.r26(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, s, env, e, args, ys, pend2, ps2, ws)),
                (%Equal.sym(U32, DW.Ev(Mc.M.eq(Mc.M.g(Mc.R.wres()), Mc.M.c(0)), X.X.st(regs2, m2, nx2, fi, im, pg2, lim, inp)), Bool.to_u32(U32.is_eq(0, 0)),
                    lp.ev(regs2, m2, nx2, fi, im, pg2, lim, inp, Nil{}, 0, 0, ws.r26(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, regs2, m2, nx2, c, s, env, e, args, ys, pend2, ps2, ws))) :
                   DW.WhQ(U32.is_zero(_), k => DW.WP(W.body(), h, X.X.st(regs2, m2, nx2, fi, im, pg2, lim, inp), u => DW.WP(W.while(), h, u, x => k(x), B, lim), B, lim), st2 => D.WalkQ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, Con{D.Rt{tc, tt}, bs}, fs, sp, ps, tt, a, xs, xs0, st2), X.X.st(regs2, m2, nx2, fi, im, pg2, lim, inp));
                 DW.Mono(W.body(), h, X.X.st(regs2, m2, nx2, fi, im, pg2, lim, inp), u => WJ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, u),
                   u => DW.WP(W.while(), h, u, x => D.WalkQ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, Con{D.Rt{tc, tt}, bs}, fs, sp, ps, tt, a, xs, xs0, x), B, lim), B, lim,
                   W.round(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, regs2, m2, nx2, pg2, c, s, env, e, args, ys, pend2, ps2, ws),
                   u => j2 => W.go(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk, u, j2)))))
        case Inr{q}:
          W.end(h, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, t, q)

# Cells of the machine's own kinds
# --------------------------------
#
# A cell of a tag of 19 or more (a K.arg, a frame, a check) has no pointer:
# every pointer is to a term cell (Pts), every owned root a term's cell.

def ne.lt19(b: Bool, +m: Cr.Cir.Cells, +x: U32, +z: U32, eb: {U32.is_eq(x, z) == b : Bool},
  hx: {U32.is_lt(D.Tg(m, x), 19) == True{} : Bool}, hz: {U32.is_lt(D.Tg(m, z), 19) == False{} : Bool}) ->
  {U32.is_eq(x, z) == False{} : Bool}:
  match b:
    case False{}:
      eb
    case True{}:
      DW.tf({U32.is_eq(x, z) == False{} : Bool},
        Equal.trans(Bool, False{}, U32.is_lt(D.Tg(m, z), 19), True{}, Equal.sym(Bool, U32.is_lt(D.Tg(m, z), 19), False{}, hz),
          (%D.u32.eq(x, z, eb) : {U32.is_lt(D.Tg(m, _), 19) == True{} : Bool}; hx)))

def rcl.lt0(xs: List<&2, U32>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +z: U32,
  +hz: {U32.is_lt(D.Tg(m, z), 19) == False{} : Bool}, +h: {D.Lt.all(xs, m, im, fi, nx) == True{} : Bool}) ->
  {D.RcL(xs, z) == 0n : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      +hx = D.and.l(D.LtC(x, Cr.Cir.Cells.get(m, x), im, fi, nx), D.Lt.all(rest, m, im, fi, nx), h)
      +ht = D.and.r(U32.is_lt(x, nx), U32.is_lt(D.Tg(m, x), 19),
        D.and.l(Bool.and(U32.is_lt(x, nx), U32.is_lt(D.Tg(m, x), 19)),
          Bool.and(Cr.Cir.is_cell(x, im, fi, nx), Bool.or(D.Own(fi, nx, x), D.Fl(m, x, 1024))), hx))
      (%Equal.sym(Bool, U32.is_eq(x, z), False{}, ne.lt19(U32.is_eq(x, z), m, x, z, {==}, ht, hz)) :
         {Nat.add(D.Nat.of(_), D.RcL(rest, z)) == 0n : Nat};
       rcl.lt0(rest, m, im, fi, nx, z, hz, D.and.r(D.LtC(x, Cr.Cir.Cells.get(m, x), im, fi, nx), D.Lt.all(rest, m, im, fi, nx), h)))

def pc.lt0(n: Nat, +m: Cr.Cir.Cells, +ps: List<&2, U32>, +o: U32, +im: U32, +fi: U32, +nx: U32, +z: U32,
  +hz: {U32.is_lt(D.Tg(m, z), 19) == False{} : Bool}, +h: {D.Pts(n, m, ps, o, im, fi, nx) == True{} : Bool}) ->
  {D.Pc(n, m, ps, o, z) == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      (%Equal.sym(Nat, D.RcL(D.Fs(m, ps, o), z), 0n,
          rcl.lt0(D.Fs(m, ps, o), m, im, fi, nx, z, hz, D.and.l(D.Lt.all(D.Fs(m, ps, o), m, im, fi, nx), D.Pts(p, m, ps, U32.inc(o), im, fi, nx), h))) :
         {Nat.add(_, D.Pc(p, m, ps, U32.inc(o), z)) == 0n : Nat};
       pc.lt0(p, m, ps, U32.inc(o), im, fi, nx, z, hz, D.and.r(D.Lt.all(D.Fs(m, ps, o), m, im, fi, nx), D.Pts(p, m, ps, U32.inc(o), im, fi, nx), h)))

# a term's tag is below 19
def atag.lt(t: Bk.Term) -> {U32.is_lt(D.A.tag(t), 19) == True{} : Bool}:
  match t:
    case Bk.Term.Var{+i}:
      {==}
    case Bk.Term.Ref{+k}:
      {==}
    case Bk.Term.Ann{+y1, +y2}:
      {==}
    case Bk.Term.Let{+q1, +v1, +f1}:
      {==}
    case Bk.Term.Typ{+y1}:
      {==}
    case Bk.Term.Min{+y1, +y2}:
      {==}
    case Bk.Term.All{+q1, +y1, +y2}:
      {==}
    case Bk.Term.Lam{+q1, +f1}:
      {==}
    case Bk.Term.App{+q1, +f1, +y1}:
      {==}
    case Bk.Term.Sig{+q1, +y1, +y2}:
      {==}
    case Bk.Term.Tup{+q1, +y1, +y2}:
      {==}
    case Bk.Term.Prj{+h1}:
      {==}
    case Bk.Term.Enu{+k}:
      {==}
    case Bk.Term.Lab{+k}:
      {==}
    case Bk.Term.Mat{+k, +h1, +n1}:
      {==}
    case Bk.Term.Efq{}:
      {==}
    case Bk.Term.Eql{+y1, +y2, +y3}:
      {==}
    case Bk.Term.Rfl{}:
      {==}
    case Bk.Term.Rwt{+y1, +y2, +y3}:
      {==}

# no owned root is z
def rts.lt0(os: List<&2, D.Rt>, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +z: U32, +hz: {U32.is_lt(D.Tg(m, z), 19) == False{} : Bool},
  h: D.Rts(ds, m, im, fi, nx, ks, img, os)) -> {D.RcL(D.Rt.cells(os), z) == 0n : Nat}:
  match os:
    case Nil{}:
      {==}
    case Con{D.Rt{+r, +u}, +rest}:
      (+hi, hr) = h
      +ht = {(%Equal.sym(U32, D.Tg(m, r), D.A.tag(u), is.tg(ds, m, im, fi, nx, ks, img, r, u, hi)) :
        {U32.is_lt(_, 19) == True{} : Bool}; atag.lt(u)) : {U32.is_lt(D.Tg(m, r), 19) == True{} : Bool}}
      (%Equal.sym(Bool, U32.is_eq(r, z), False{}, ne.lt19(U32.is_eq(r, z), m, r, z, {==}, ht, hz)) :
         {Nat.add(D.Nat.of(_), D.RcL(D.Rt.cells(rest), z)) == 0n : Nat};
       rts.lt0(rest, ds, m, im, fi, nx, ks, img, z, hz, hr))

def hs.pts(-ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -m: Cr.Cir.Cells, -nx: U32,
  -fi: U32, -im: U32, -os: List<&2, D.Rt>, -bs: List<&2, D.Rt>, -fs: List<&2, D.AF>, -sp: U32, -pend: U32,
  -ps: List<&2, U32>, h: D.HS(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps)) ->
  {D.Pts(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, ps, fi, im, fi, nx) == True{} : Bool}:
  (_, h1) = h
  (_, h2) = h1
  (_, h3) = h2
  (_, h4) = h3
  (hp, _) = h4
  (_, p1) = hp
  (_, p2) = p1
  (_, p3) = p2
  (x, _) = p3
  x

def hs.os(-ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -m: Cr.Cir.Cells, -nx: U32,
  -fi: U32, -im: U32, -os: List<&2, D.Rt>, -bs: List<&2, D.Rt>, -fs: List<&2, D.AF>, -sp: U32, -pend: U32,
  -ps: List<&2, U32>, h: D.HS(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps)) -> D.Rts(ds, m, im, fi, nx, ks, img, os):
  (x, _) = h
  x

# a cell of a tag of 19 or more has no pointer
def ptr.lt0(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32,
  +fi: U32, +im: U32, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32,
  +ps: List<&2, U32>, +z: U32, +hz: {U32.is_lt(D.Tg(m, z), 19) == False{} : Bool},
  +h: D.HS(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps)) ->
  {D.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, D.Rt.cells(os), z) == 0n : Nat}:
  +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
  (%Equal.sym(Nat, D.Pc(n, m, ps, fi, z), 0n, pc.lt0(n, m, ps, fi, im, fi, nx, z, hz, hs.pts(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps, h))) :
     {Nat.add(_, D.RcL(D.Rt.cells(os), z)) == 0n : Nat};
   (%Equal.sym(Nat, D.RcL(D.Rt.cells(os), z), 0n, rts.lt0(os, ds, m, im, fi, nx, ks, img, z, hz, hs.os(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps, h))) :
      {Nat.add(0n, _) == 0n : Nat}; {==}))

# The chains under a store
# ------------------------
#
# Ag reads the chain's cells, its terms' cells (Is), and os's nodes: a store
# at a cell z that is none of them, with no pointer and not STATIC, keeps it
# (is.fz, Nodes.fz).

def fl.eq(+m2: Cr.Cir.Cells, +m: Cr.Cir.Cells, +a: U32, +f: U32, ec: {Cr.Cir.Cells.get(m2, a) == Cr.Cir.Cells.get(m, a) : Cr.Cir.Cell}) ->
  {D.Fl(m2, a, f) == D.Fl(m, a, f) : Bool}:
  (%Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(m2, a), Cr.Cir.Cells.get(m, a), ec) :
    {U32.is_ne(U32.and(Cr.Cir.Cell.get(0n, _), f), 0) == D.Fl(m, a, f) : Bool}; {==})

def fd.eq(+k: Nat, +m2: Cr.Cir.Cells, +m: Cr.Cir.Cells, +a: U32, ec: {Cr.Cir.Cells.get(m2, a) == Cr.Cir.Cells.get(m, a) : Cr.Cir.Cell}) ->
  {D.Fd(k, m2, a) == D.Fd(k, m, a) : U32}:
  (%Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(m2, a), Cr.Cir.Cells.get(m, a), ec) :
    {Cr.Cir.Cell.get(k, _) == D.Fd(k, m, a) : U32}; {==})

def tg.eq(+m2: Cr.Cir.Cells, +m: Cr.Cir.Cells, +a: U32, ec: {Cr.Cir.Cells.get(m2, a) == Cr.Cir.Cells.get(m, a) : Cr.Cir.Cell}) ->
  {D.Tg(m2, a) == D.Tg(m, a) : U32}:
  (%Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(m2, a), Cr.Cir.Cells.get(m, a), ec) :
    {U32.and(Cr.Cir.Cell.get(0n, _), 63) == D.Tg(m, a) : U32}; {==})

# the chain's cells and its terms' cells
def Ag.all(xs: List<&2, El.Arg>, +m: Cr.Cir.Cells, +a: U32) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{_, +rest}:
      Con{a, Con{D.Fd(2n, m, a), Ag.all(rest, m, D.Fd(1n, m, a))}}

# Ag.vars after the store
def ag.vars.fz(xs: List<&2, El.Arg>, +m: Cr.Cir.Cells, +a: U32, +z: U32, +x: Cr.Cir.Cell,
  +hn: {D.NeAll(Ag.all(xs, m, a), z) == True{} : Bool}) ->
  {D.Ag.vars(xs, Cr.Cir.Cells.set(m, z, x), a) == D.Ag.vars(xs, m, a) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      +m2 = Cr.Cir.Cells.set(m, z, x)
      +ec = D.cl.go(m, a, z, x, D.neall.hd(a, z, Con{D.Fd(2n, m, a), Ag.all(rest, m, D.Fd(1n, m, a))}, hn))
      +hr = D.neall.tl(D.Fd(2n, m, a), z, Ag.all(rest, m, D.Fd(1n, m, a)),
        D.neall.tl(a, z, Con{D.Fd(2n, m, a), Ag.all(rest, m, D.Fd(1n, m, a))}, hn))
      (%Equal.sym(Bool, D.Fl(m2, a, 4096), D.Fl(m, a, 4096), fl.eq(m2, m, a, 4096, ec)) :
         {Bool.pick(List<&2, U32>, _, Con{D.Fd(2n, m2, a), D.Ag.vars(rest, m2, D.Fd(1n, m2, a))}, D.Ag.vars(rest, m2, D.Fd(1n, m2, a))) ==
           D.Ag.vars(Con{y, rest}, m, a) : List<&2, U32>};
       %Equal.sym(U32, D.Fd(2n, m2, a), D.Fd(2n, m, a), fd.eq(2n, m2, m, a, ec)) :
         {Bool.pick(List<&2, U32>, D.Fl(m, a, 4096), Con{_, D.Ag.vars(rest, m2, D.Fd(1n, m2, a))}, D.Ag.vars(rest, m2, D.Fd(1n, m2, a))) ==
           D.Ag.vars(Con{y, rest}, m, a) : List<&2, U32>};
       %Equal.sym(U32, D.Fd(1n, m2, a), D.Fd(1n, m, a), fd.eq(1n, m2, m, a, ec)) :
         {Bool.pick(List<&2, U32>, D.Fl(m, a, 4096), Con{D.Fd(2n, m, a), D.Ag.vars(rest, m2, _)}, D.Ag.vars(rest, m2, _)) ==
           D.Ag.vars(Con{y, rest}, m, a) : List<&2, U32>};
       %Equal.sym(List<&2, U32>, D.Ag.vars(rest, m2, D.Fd(1n, m, a)), D.Ag.vars(rest, m, D.Fd(1n, m, a)), ag.vars.fz(rest, m, D.Fd(1n, m, a), z, x, hr)) :
         {Bool.pick(List<&2, U32>, D.Fl(m, a, 4096), Con{D.Fd(2n, m, a), _}, _) == D.Ag.vars(Con{y, rest}, m, a) : List<&2, U32>};
       {==})

# Ag after a store at z: none of the chain's cells or of its terms' cells,
# not a root, with no pointer, not STATIC
def ag.fz(xs: List<&2, El.Arg>, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +os: List<&2, D.Rt>, +vs: List<&2, U32>,
  +a: U32, +z: U32, +xc: Cr.Cir.Cell, +tbl: D.Tbl(m, im, fi, nx),
  +hz0: {D.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, D.Rt.cells(os), z) == 0n : Nat},
  +hzs: {D.Fl(m, z, 1024) == False{} : Bool}, +hro: {D.NeAll(D.Rt.cells(os), z) == True{} : Bool},
  +ho: D.Rts(ds, m, im, fi, nx, ks, img, os), +hn: {D.NeAll(Ag.all(xs, m, a), z) == True{} : Bool},
  h: D.Ag(ds, m, im, fi, nx, ks, img, ps, os, vs, a, xs)) ->
  D.Ag(ds, Cr.Cir.Cells.set(m, z, xc), im, fi, nx, ks, img, ps, os, vs, a, xs):
  match xs:
    case Nil{}:
      h
    case Con{El.Arg{+q, +x}, +rest}:
      (h0, g1) = h
      (h1, g2) = g1
      (h2, g3) = g2
      (h3, g4) = g3
      (h4, g5) = g4
      (h5, g6) = g5
      (h6, g7) = g6
      (h7, g8) = g7
      (h8, g9) = g8
      (h9, g10) = g9
      (h10, g11) = g10
      (h11, h12) = g11
      +m2 = Cr.Cir.Cells.set(m, z, xc)
      +y = D.Fd(2n, m, a)
      +f1 = D.Fd(1n, m, a)
      +tl = {Con{y, Ag.all(rest, m, f1)} : List<&2, U32>}
      +ec = D.cl.go(m, a, z, xc, D.neall.hd(a, z, tl, hn))
      +hn1 = D.neall.tl(a, z, tl, hn)
      +ey = D.cl.go(m, y, z, xc, D.neall.hd(y, z, Ag.all(rest, m, f1), hn1))
      +hr = D.neall.tl(y, z, Ag.all(rest, m, f1), hn1)
      +e2 = fd.eq(2n, m2, m, a, ec)
      +e1 = fd.eq(1n, m2, m, a, ec)
      +ef4 = fl.eq(m2, m, a, 4096, ec)
      +efy = fl.eq(m2, m, y, 1024, ey)
      +en = D.Nodes.fz(True{}, os, ds, m, im, fi, nx, ks, img, ps, D.Rt.cells(os), z, xc, y, tbl, hz0, hzs, hro, ho)
      +ev = ag.vars.fz(rest, m, f1, z, xc, hr)
      (h0, (h1, (h2,
       ((%Equal.sym(Bool, D.Fl(m2, a, 1024), D.Fl(m, a, 1024), fl.eq(m2, m, a, 1024, ec)) : {_ == False{} : Bool}; h3),
       (h4,
       ((%Equal.sym(U32, D.Tg(m2, a), D.Tg(m, a), tg.eq(m2, m, a, ec)) : {_ == 41 : U32}; h5),
       ((%Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(m2, a), Cr.Cir.Cells.get(m, a), ec) : D.Qs(_, q); h6),
       ((%Equal.sym(Bool, D.Fl(m2, a, 2048), D.Fl(m, a, 2048), fl.eq(m2, m, a, 2048, ec)) :
          {Bool.or(Bool.not(_), El.Eval.vals(ds, x, False{})) == True{} : Bool}; h7),
       ((%Equal.sym(Bool, D.Fl(m2, a, 4096), D.Fl(m, a, 4096), ef4) : {Bool.or(Bool.not(_), D.Term.is_var(x)) == True{} : Bool}; h8),
       ((%Equal.sym(U32, D.Fd(2n, m2, a), y, e2) : D.Is(ds, m2, im, fi, nx, ks, img, _, x);
         D.is.fz(True{}, x, ds, m, im, fi, nx, ks, img, ps, D.Rt.cells(os), z, xc, y, tbl, hz0, hzs,
           D.neall.hd(y, z, Ag.all(rest, m, f1), hn1), h9)),
       ((%Equal.sym(U32, D.Fd(2n, m2, a), y, e2) :
           {Bool.or(D.Fl(m2, a, 4096), Bool.or(D.Fl(m2, _, 1024), Bool.or(D.Nodes(os, m2, _),
             Bool.or(D.Mem(vs, _), D.Mem(D.Ag.vars(rest, m2, D.Fd(1n, m2, a)), _))))) == True{} : Bool};
         %Equal.sym(U32, D.Fd(1n, m2, a), f1, e1) :
           {Bool.or(D.Fl(m2, a, 4096), Bool.or(D.Fl(m2, y, 1024), Bool.or(D.Nodes(os, m2, y),
             Bool.or(D.Mem(vs, y), D.Mem(D.Ag.vars(rest, m2, _), y))))) == True{} : Bool};
         %Equal.sym(Bool, D.Fl(m2, a, 4096), D.Fl(m, a, 4096), ef4) :
           {Bool.or(_, Bool.or(D.Fl(m2, y, 1024), Bool.or(D.Nodes(os, m2, y),
             Bool.or(D.Mem(vs, y), D.Mem(D.Ag.vars(rest, m2, f1), y))))) == True{} : Bool};
         %Equal.sym(Bool, D.Fl(m2, y, 1024), D.Fl(m, y, 1024), efy) :
           {Bool.or(D.Fl(m, a, 4096), Bool.or(_, Bool.or(D.Nodes(os, m2, y),
             Bool.or(D.Mem(vs, y), D.Mem(D.Ag.vars(rest, m2, f1), y))))) == True{} : Bool};
         %Equal.sym(Bool, D.Nodes(os, m2, y), D.Nodes(os, m, y), en) :
           {Bool.or(D.Fl(m, a, 4096), Bool.or(D.Fl(m, y, 1024), Bool.or(_,
             Bool.or(D.Mem(vs, y), D.Mem(D.Ag.vars(rest, m2, f1), y))))) == True{} : Bool};
         %Equal.sym(List<&2, U32>, D.Ag.vars(rest, m2, f1), D.Ag.vars(rest, m, f1), ev) :
           {Bool.or(D.Fl(m, a, 4096), Bool.or(D.Fl(m, y, 1024), Bool.or(D.Nodes(os, m, y),
             Bool.or(D.Mem(vs, y), D.Mem(_, y))))) == True{} : Bool};
         h10),
       ((%Equal.sym(U32, D.Fd(2n, m2, a), y, e2) : {Bool.or(D.Fl(m2, _, 1024), Bool.not(D.Mem(ps, _))) == True{} : Bool};
         %Equal.sym(Bool, D.Fl(m2, y, 1024), D.Fl(m, y, 1024), efy) : {Bool.or(_, Bool.not(D.Mem(ps, y))) == True{} : Bool};
         h11),
        (%Equal.sym(U32, D.Fd(1n, m2, a), f1, e1) : D.Ag(ds, m2, im, fi, nx, ks, img, ps, os, vs, _, rest);
         ag.fz(rest, ds, m, im, fi, nx, ks, img, ps, os, vs, f1, z, xc, tbl, hz0, hzs, hro, ho, hr, h12))))))))))))))

# What the walk keeps under a store
# ---------------------------------
#
# A store at z keeps Kept.cells when z, below the start's nx, is one of ps ++
# es or a term cell of the start's cells (as PsSub.lt says of a pend list):
# Kept.go's cells are below nx.

def u.lt.t.of(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), h: N.Le(1n+x, y)) -> {Cmp.is_lt(c) == True{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({False{} == True{} : Bool}, N.not_succ_le(y, N.le_rw_l(1n+x, 1n+y, y, Equal.cong(Nat, Nat, z => 1n+z, x, y, r), h)))
    case GT{}:
      Empty.absurd({False{} == True{} : Bool}, N.not_succ_le(y, N.le_trans(1n+y, x, y, r, N.weaken(x, y, h))))

def u.lt.t(+a: U32, +b: U32, h: N.Le(1n+U32.to_nat(a), U32.to_nat(b))) -> {U32.is_lt(a, b) == True{} : Bool}:
  u.lt.t.of(U32.cmp(a, b), U32.to_nat(a), U32.to_nat(b), N.U32.rel(a, b), h)

def sub.z(a: Nat, b: Nat, h: {Nat.is_le(a, b) == False{} : Bool}) -> {Nat.sub(b, a) == 0n : Nat}:
  match a b:
    case 0n 0n:
      DW.ft({Nat.sub(0n, 0n) == 0n : Nat}, h)
    case 0n 1n+q:
      DW.ft({Nat.sub(1n+q, 0n) == 0n : Nat}, h)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      sub.z(p, q, h)

def kne.lt(b: Bool, +L: List<&2, U32>, +m: Cr.Cir.Cells, +c: U32, +nx: U32, +z: U32, eb: {U32.is_eq(c, z) == b : Bool},
  eo: {Bool.or(D.Mem(L, c), U32.is_lt(D.Tg(m, c), 19)) == False{} : Bool}, hc: {U32.is_lt(c, nx) == True{} : Bool},
  hz: {Bool.or(Bool.not(U32.is_lt(z, nx)), Bool.or(D.Mem(L, z), U32.is_lt(D.Tg(m, z), 19))) == True{} : Bool}) ->
  {U32.is_eq(c, z) == False{} : Bool}:
  match b:
    case False{}:
      eb
    case True{}:
      DW.ft({U32.is_eq(c, z) == False{} : Bool},
        Equal.trans(Bool, True{}, Bool.or(Bool.not(U32.is_lt(c, nx)), Bool.or(D.Mem(L, c), U32.is_lt(D.Tg(m, c), 19))), False{},
          Equal.sym(Bool, Bool.or(Bool.not(U32.is_lt(c, nx)), Bool.or(D.Mem(L, c), U32.is_lt(D.Tg(m, c), 19))), True{},
            (%Equal.sym(U32, c, z, D.u32.eq(c, z, eb)) :
               {Bool.or(Bool.not(U32.is_lt(_, nx)), Bool.or(D.Mem(L, _), U32.is_lt(D.Tg(m, _), 19))) == True{} : Bool}; hz)),
          (%Equal.sym(Bool, U32.is_lt(c, nx), True{}, hc) :
             {Bool.or(Bool.not(_), Bool.or(D.Mem(L, c), U32.is_lt(D.Tg(m, c), 19))) == False{} : Bool}; eo)))

def kat.fz(b: Bool, +m: Cr.Cir.Cells, +m2: Cr.Cir.Cells, +L: List<&2, U32>, +c: U32, +nx: U32, +z: U32, +xc: Cr.Cir.Cell,
  eb: {Bool.or(D.Mem(L, c), U32.is_lt(D.Tg(m, c), 19)) == b : Bool}, hc: {U32.is_lt(c, nx) == True{} : Bool},
  hz: {Bool.or(Bool.not(U32.is_lt(z, nx)), Bool.or(D.Mem(L, z), U32.is_lt(D.Tg(m, z), 19))) == True{} : Bool},
  h: D.Kept.if(b, {Cr.Cir.Cells.get(m2, c) == Cr.Cir.Cells.get(m, c) : Cr.Cir.Cell})) ->
  D.Kept.if(b, {Cr.Cir.Cells.get(Cr.Cir.Cells.set(m2, z, xc), c) == Cr.Cir.Cells.get(m, c) : Cr.Cir.Cell}):
  match b:
    case True{}:
      Unit{}
    case False{}:
      Equal.trans(Cr.Cir.Cell, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m2, z, xc), c), Cr.Cir.Cells.get(m2, c), Cr.Cir.Cells.get(m, c),
        D.cl.go(m2, c, z, xc, kne.lt(U32.is_eq(c, z), L, m, c, nx, z, {==}, eb, hc, hz)), h)

def kg.fz(k: Nat, +m: Cr.Cir.Cells, +m2: Cr.Cir.Cells, +L: List<&2, U32>, +c: U32, +nx: U32, +z: U32, +xc: Cr.Cir.Cell,
  hb: N.Le(Nat.add(U32.to_nat(c), k), U32.to_nat(nx)),
  +hz: {Bool.or(Bool.not(U32.is_lt(z, nx)), Bool.or(D.Mem(L, z), U32.is_lt(D.Tg(m, z), 19))) == True{} : Bool},
  h: D.Kept.go(k, m, m2, L, c)) -> D.Kept.go(k, m, Cr.Cir.Cells.set(m2, z, xc), L, c):
  match k:
    case 0n:
      Unit{}
    case 1n+(+p):
      (h1, hr) = h
      +tc = U32.to_nat(c)
      +hb2 = {N.le_rw_l(Nat.add(tc, 1n+p), 1n+Nat.add(tc, p), U32.to_nat(nx), N.add_succ_r(tc, p), hb) : N.Le(1n+Nat.add(tc, p), U32.to_nat(nx))}
      +h1c = N.le_trans(1n+tc, 1n+Nat.add(tc, p), U32.to_nat(nx), N.le_add_r(tc, p), hb2)
      +ei = D.u.inc(c, nx, h1c)
      (kat.fz(Bool.or(D.Mem(L, c), U32.is_lt(D.Tg(m, c), 19)), m, m2, L, c, nx, z, xc, {==}, u.lt.t(c, nx, h1c), hz, h1),
       kg.fz(p, m, m2, L, U32.inc(c), nx, z, xc,
         (%Equal.sym(Nat, U32.to_nat(U32.inc(c)), 1n+tc, ei) : N.Le(Nat.add(_, p), U32.to_nat(nx)); hb2), hz, hr))

def kc.go(bl: Bool, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +m2: Cr.Cir.Cells, +L: List<&2, U32>, +z: U32, +xc: Cr.Cir.Cell,
  ebl: {Nat.is_le(U32.to_nat(fi), U32.to_nat(nx)) == bl : Bool},
  hz: {Bool.or(Bool.not(U32.is_lt(z, nx)), Bool.or(D.Mem(L, z), U32.is_lt(D.Tg(m, z), 19))) == True{} : Bool},
  h: D.Kept.go(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, m2, L, fi)) ->
  D.Kept.go(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, Cr.Cir.Cells.set(m2, z, xc), L, fi):
  match bl:
    case True{}:
      kg.fz(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, m2, L, fi, nx, z, xc,
        (%Equal.sym(Nat, Nat.add(U32.to_nat(fi), Nat.sub(U32.to_nat(nx), U32.to_nat(fi))), U32.to_nat(nx),
            D.add.sub(U32.to_nat(fi), U32.to_nat(nx), N.toT(Nat.is_le(U32.to_nat(fi), U32.to_nat(nx)), ebl))) :
          N.Le(_, U32.to_nat(nx)); N.le_refl(U32.to_nat(nx))), hz, h)
    case False{}:
      (%Equal.sym(Nat, Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), 0n, sub.z(U32.to_nat(fi), U32.to_nat(nx), ebl)) :
         D.Kept.go(_, m, Cr.Cir.Cells.set(m2, z, xc), L, fi); Unit{})

# Kept.cells after a store at z
def kc.fz(+m: Cr.Cir.Cells, +nx: U32, +fi: U32, +ps: List<&2, U32>, +es: List<&2, U32>, +m2: Cr.Cir.Cells, +nx2: U32,
  +ps2: List<&2, U32>, +z: U32, +xc: Cr.Cir.Cell,
  hz: {Bool.or(Bool.not(U32.is_lt(z, nx)), Bool.or(D.Mem(List.append(&2, U32, ps, es), z), U32.is_lt(D.Tg(m, z), 19))) == True{} : Bool},
  h: D.Kept.cells(m, nx, fi, ps, es, m2, nx2, ps2)) -> D.Kept.cells(m, nx, fi, ps, es, Cr.Cir.Cells.set(m2, z, xc), nx2, ps2):
  (h1, h2) = h
  (hg, h3) = h2
  (h1, (kc.go(Nat.is_le(U32.to_nat(fi), U32.to_nat(nx)), m, nx, fi, m2, List.append(&2, U32, ps, es), z, xc, {==}, hz, hg), h3))

# The walk
# --------
#
# M.walk sets wenv, wn and wres to 0: a round's start, with the whole tree
# and the arguments xs, no local, and the cells as they are; then the loop.

# HS with its first borrowed term twice
def hs.dup(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32,
  +fi: U32, +im: U32, +os: List<&2, D.Rt>, r: D.Rt, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32,
  +ps: List<&2, U32>, h: D.HS(ds, ks, img, m, nx, fi, im, os, Con{r, bs}, fs, sp, pend, ps)) ->
  D.HS(ds, ks, img, m, nx, fi, im, os, Con{r, Con{r, bs}}, fs, sp, pend, ps):
  match r:
    case D.Rt{+c, +u}:
      (ho, h1) = h
      (hb, h2) = h1
      (+hi, hbr) = hb
      (hh, h3) = h2
      (+hc, hhr) = hh
      (ho, ((hi, (hi, hbr)), ((hc, (hc, hhr)), h3)))

# the registers keep their values
def kept.refl(+regs: List<&2, U32>, keep: List<&2, Nat>) -> D.Kept(regs, regs, keep):
  match keep:
    case Nil{}:
      Unit{}
    case Con{+j, rest}:
      ({==}, kept.refl(regs, rest))

def u.le.refl(+x: U32) -> {U32.is_le(x, x) == True{} : Bool}:
  match x:
    case U32{+w}:
      (%DW.W.refl(32n, w) : {Cmp.is_le(_) == True{} : Bool}; {==})

def kept.at.refl(b: Bool, +m: Cr.Cir.Cells, +c: U32) -> D.Kept.if(b, {Cr.Cir.Cells.get(m, c) == Cr.Cir.Cells.get(m, c) : Cr.Cir.Cell}):
  match b:
    case True{}:
      Unit{}
    case False{}:
      {==}

def kept.go.refl(n: Nat, +m: Cr.Cir.Cells, +xs: List<&2, U32>, +c: U32) -> D.Kept.go(n, m, m, xs, c):
  match n:
    case 0n:
      Unit{}
    case 1n+(+p):
      (kept.at.refl(Bool.or(D.Mem(xs, c), U32.is_lt(D.Tg(m, c), 19)), m, c), kept.go.refl(p, m, xs, U32.inc(c)))

def mem.app.l(ys: List<&2, U32>, +zs: List<&2, U32>, +q: U32, h: {D.Mem(ys, q) == True{} : Bool}) ->
  {D.Mem(List.append(&2, U32, ys, zs), q) == True{} : Bool}:
  match ys:
    case Nil{}:
      DW.tf({D.Mem(zs, q) == True{} : Bool}, h)
    case Con{+y, +rest}:
      D.or.cases(U32.is_eq(y, q), D.Mem(rest, q), {D.Mem(List.append(&2, U32, Con{y, rest}, zs), q) == True{} : Bool}, h,
        e0 => D.or.l(U32.is_eq(y, q), D.Mem(List.append(&2, U32, rest, zs), q), e0),
        e1 => D.or.r(U32.is_eq(y, q), D.Mem(List.append(&2, U32, rest, zs), q), mem.app.l(rest, zs, q, e1)))

def allin.app(xs: List<&2, U32>, +ys: List<&2, U32>, +zs: List<&2, U32>, +h: {D.AllIn(xs, ys) == True{} : Bool}) ->
  {D.AllIn(xs, List.append(&2, U32, ys, zs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      D.and.i(D.Mem(List.append(&2, U32, ys, zs), x), D.AllIn(rest, List.append(&2, U32, ys, zs)),
        mem.app.l(ys, zs, x, D.and.l(D.Mem(ys, x), D.AllIn(rest, ys), h)),
        allin.app(rest, ys, zs, D.and.r(D.Mem(ys, x), D.AllIn(rest, ys), h)))

def or.nt(a: Bool) -> {Bool.or(Bool.not(a), True{}) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# each cell of qs, all in ys, is in ys
def pssub.in(qs: List<&2, U32>, +ys: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +h: {D.AllIn(qs, ys) == True{} : Bool}) ->
  {D.PsSub.lt(qs, ys, m, nx) == True{} : Bool}:
  match qs:
    case Nil{}:
      {==}
    case Con{+q, +rest}:
      (%Equal.sym(Bool, D.Mem(ys, q), True{}, D.and.l(D.Mem(ys, q), D.AllIn(rest, ys), h)) :
         {Bool.and(Bool.or(Bool.not(U32.is_lt(q, nx)), Bool.or(_, U32.is_lt(D.Tg(m, q), 19))), D.PsSub.lt(rest, ys, m, nx)) == True{} : Bool};
       %Equal.sym(Bool, D.PsSub.lt(rest, ys, m, nx), True{}, pssub.in(rest, ys, m, nx, D.and.r(D.Mem(ys, q), D.AllIn(rest, ys), h))) :
         {Bool.and(Bool.or(Bool.not(U32.is_lt(q, nx)), True{}), _) == True{} : Bool};
       %Equal.sym(Bool, Bool.or(Bool.not(U32.is_lt(q, nx)), True{}), True{}, or.nt(U32.is_lt(q, nx))) :
         {Bool.and(_, True{}) == True{} : Bool};
       {==})

# a phase that changes nothing keeps everything
def kc.refl(+m: Cr.Cir.Cells, +nx: U32, +fi: U32, +ps: List<&2, U32>, +es: List<&2, U32>) ->
  D.Kept.cells(m, nx, fi, ps, es, m, nx, ps):
  (u.le.refl(nx), (kept.go.refl(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, List.append(&2, U32, ps, es), fi),
    pssub.in(ps, List.append(&2, U32, ps, es), m, nx, allin.app(ps, ps, es, D.allin.refl(ps)))))

def W.t1() -> Cr.Cir.Stmt:
  X.sel.b(Mc.M.walk())

def W.t2() -> Cr.Cir.Stmt:
  X.sel.b(W.t1())

def W.t3() -> Cr.Cir.Stmt:
  X.sel.b(W.t2())

# the own cells at the walk's start are within its budget (WalkQ's bound)
def le.max.l(+a: Nat, +b: Nat) -> N.Le(a, Nat.max(a, b)):
  match a:
    case 0n:
      N.le_zero(b)
    case 1n+p:
      match b:
        case 0n:
          N.le_refl(1n+p)
        case 1n+q:
          le.max.l(p, q)

# M.walk, as WP: its three sets, then the loop from the first round's start
def walk.wp(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +keep: List<&2, Nat>,
  +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>, +tc: U32,
  +tt: Bk.Term, +a: U32, +xs: List<&2, El.Arg>, +xs0: List<&2, D.TmpE>, +zs: List<&2, D.Rt>, +B: Nat,
  hs: D.HS(ds, ks, img, m, nx, fi, im, os, Con{D.Rt{tc, tt}, bs}, fs, sp, pend, ps),
  hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, os, List.append(&2, D.TmpE, D.Ag.cells(xs, m, a), xs0), sp, fs, ps, zs),
  hst: {D.Fl(m, tc, 1024) == True{} : Bool},
  +hl: {List.length(&2, U32, regs) == 63n : Nat},
  ht: {List.get(&2, U32, regs, 19n) == Some{tc} : Maybe<&2, U32>},
  ha: {List.get(&2, U32, regs, 21n) == Some{a} : Maybe<&2, U32>},
  hp: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>},
  args: D.Ag(ds, m, im, fi, nx, ks, img, ps, os, Nil{}, a, xs),
  +hk: {D.Disj(keep, D.Walk.scr()) == True{} : Bool}) ->
  DW.WP(Mc.M.walk(), f, X.X.st(regs, m, nx, fi, im, pg, lim, inp),
    st2 => D.WalkQ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, Con{D.Rt{tc, tt}, bs}, fs, sp, ps, tt, a, xs, xs0, st2), B, lim):
  +r1 = List.set(&2, U32, regs, 20n, 0)
  +r2 = List.set(&2, U32, r1, 25n, 0)
  +r3 = List.set(&2, U32, r2, 26n, 0)
  +l1 = X.L.len(regs, 20n, 0, 63n, hl)
  +l2 = X.L.len(r1, 25n, 0, 63n, l1)
  +l3 = X.L.len(r2, 26n, 0, 63n, l2)
  +k1 = kept.set(regs, regs, keep, D.Walk.scr(), 20n, 0, hk, {==}, kept.refl(regs, keep))
  +k2 = kept.set(regs, r1, keep, D.Walk.scr(), 25n, 0, hk, {==}, k1)
  +k3 = kept.set(regs, r2, keep, D.Walk.scr(), 26n, 0, hk, {==}, k2)
  +g19 = X.L.go(r2, 26n, 19n, 0, tc, {==}, X.L.go(r1, 25n, 19n, 0, tc, {==}, X.L.go(regs, 20n, 19n, 0, tc, {==}, ht)))
  +g20 = X.L.go(r2, 26n, 20n, 0, 0, {==}, X.L.go(r1, 25n, 20n, 0, 0, {==}, X.L.gs(regs, 20n, 0, X.L.lt(regs, 20n, hl, {==}))))
  +g21 = X.L.go(r2, 26n, 21n, 0, a, {==}, X.L.go(r1, 25n, 21n, 0, a, {==}, X.L.go(regs, 20n, 21n, 0, a, {==}, ha)))
  +g25 = X.L.go(r2, 26n, 25n, 0, 0, {==}, X.L.gs(r1, 25n, 0, X.L.lt(r1, 25n, l1, {==})))
  +g26 = X.L.gs(r2, 26n, 0, X.L.lt(r2, 26n, l2, {==}))
  +g3 = X.L.go(r2, 26n, 3n, 0, pend, {==}, X.L.go(r1, 25n, 3n, 0, pend, {==}, X.L.go(regs, 20n, 3n, 0, pend, {==}, hp)))
  +ws = {((l3, (k3, (g19, (g20, (g21, (g25, g3)))))), (g26, ({==}, (hst,
      (hs.dup(ds, ks, img, m, nx, fi, im, os, D.Rt{tc, tt}, bs, fs, sp, pend, ps, hs), ({==}, (args,
        (kc.refl(m, nx, fi, ps, D.Tmp.cells(D.Ag.cells(xs, m, a))), (N.le_refl(D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi)), ((zs, hac),
        (pssub.in(D.Tmp.cells(D.Ag.cells(xs, m, a)), List.append(&2, U32, ps, D.Tmp.cells(D.Ag.cells(xs, m, a))), m, nx,
           allin.app.r(D.Tmp.cells(D.Ag.cells(xs, m, a)), ps, D.Tmp.cells(D.Ag.cells(xs, m, a)), D.allin.refl(D.Tmp.cells(D.Ag.cells(xs, m, a))))),
        (N.le_refl(Nat.add(D.Acc.need(m, nx, fi, os, List.append(&2, D.TmpE, D.Ag.cells(xs, m, a), xs0), sp, fs), Nat.mul(2n, Pg.Term.size(tt)))),
          (ts.le.self(D.Arg.terms(xs)),
            le.max.l(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), D.Walk.need(m, nx, fi, os, xs0, sp, fs, tt, a, xs))))))))))))))) :
    WS(ds, ks, img, regs, m, nx, fi, im, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, r3, m, nx, tc, tt, 0, Nil{}, a, xs, pend, ps)}
  wp.set.k(f, 20n, 0, regs, m, nx, fi, im, pg, lim, inp, t => DW.WP(W.t1(), f, t, st2 => D.WalkQ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, Con{D.Rt{tc, tt}, bs}, fs, sp, ps, tt, a, xs, xs0, st2), B, lim), B, hl, {==},
    wp.set.k(f, 25n, 0, r1, m, nx, fi, im, pg, lim, inp, t => DW.WP(W.t2(), f, t, st2 => D.WalkQ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, Con{D.Rt{tc, tt}, bs}, fs, sp, ps, tt, a, xs, xs0, st2), B, lim), B, l1, {==},
      wp.set.k(f, 26n, 0, r2, m, nx, fi, im, pg, lim, inp, t => DW.WP(W.t3(), f, t, st2 => D.WalkQ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, Con{D.Rt{tc, tt}, bs}, fs, sp, ps, tt, a, xs, xs0, st2), B, lim), B, l2, {==},
        DW.Mono(W.while(), f, X.X.st(r3, m, nx, fi, im, pg, lim, inp), st2 => D.WalkQ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, Con{D.Rt{tc, tt}, bs}, fs, sp, ps, tt, a, xs, xs0, st2), t => DW.WP(Cr.Cir.Stmt.nop{}, f, t, st2 => D.WalkQ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, Con{D.Rt{tc, tt}, bs}, fs, sp, ps, tt, a, xs, xs0, st2), B, lim), B, lim,
          W.go(f, ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, bs, fs, sp, ps, tc, tt, a, xs, xs0, B, hk,
            X.X.st(r3, m, nx, fi, im, pg, lim, inp),
            Inl{(WG{r3, m, nx, pg, tc, tt, 0, Nil{}, a, xs, pend, ps}, ({==}, ws))}),
          t => q => q))))

# the budget of walk.post
def W.B(+m: Cr.Cir.Cells, +nx: U32, +fi: U32, +os: List<&2, D.Rt>, +sp: U32, +fs: List<&2, D.AF>, +tt: Bk.Term, +a: U32,
  +xs: List<&2, El.Arg>, +xs0: List<&2, D.TmpE>) -> Nat:
  D.Cells.bytes(fi, Nat.add(D.Acc.need(m, nx, fi, os, List.append(&2, D.TmpE, D.Ag.cells(xs, m, a), xs0), sp, fs),
    1n+Nat.add(Nat.mul(2n, Pg.Term.size(tt)), D.Terms.size(D.Arg.terms(xs)))))

# The temporaries' order (U7)
# ---------------------------
# WH's AccK holds the chains' cells with Ag.cells and then xs0; a round that
# releases an argument releases the chain's first cell, which is the first
# temporary of the arguments but not of the list (the environment's cells come
# first). AccK's other facts are sets, but Tmp.ok's distinctness reads the
# cells of the rest, so mat.lab needs the order to be no matter.

# the cells of A ++ B are those of A and then those of B
def tmp.cells.app(A: List<&2, D.TmpE>, +B: List<&2, D.TmpE>) ->
  {D.Tmp.cells(List.append(&2, D.TmpE, A, B)) == List.append(&2, U32, D.Tmp.cells(A), D.Tmp.cells(B)) : List<&2, U32>}:
  match A:
    case Nil{}:
      {==}
    case Con{D.TmpE{c, h}, +rest}:
      Equal.cong(List<&2, U32>, List<&2, U32>, l => Con{c, l}, D.Tmp.cells(List.append(&2, D.TmpE, rest, B)),
        List.append(&2, U32, D.Tmp.cells(rest), D.Tmp.cells(B)), tmp.cells.app(rest, B))

# and the terms that they hold are those of A and then those of B
def tmp.held.app(A: List<&2, D.TmpE>, +B: List<&2, D.TmpE>) ->
  {D.Tmp.held(List.append(&2, D.TmpE, A, B)) == List.append(&2, D.Rt, D.Tmp.held(A), D.Tmp.held(B)) : List<&2, D.Rt>}:
  match A:
    case Nil{}:
      {==}
    case Con{D.TmpE{c, h}, +rest}:
      %Equal.sym(List<&2, D.Rt>, D.Tmp.held(List.append(&2, D.TmpE, rest, B)),
          List.append(&2, D.Rt, D.Tmp.held(rest), D.Tmp.held(B)), tmp.held.app(rest, B)) :
        {List.append(&2, D.Rt, h, _) == List.append(&2, D.Rt, List.append(&2, D.Rt, h, D.Tmp.held(rest)), D.Tmp.held(B)) : List<&2, D.Rt>}
      Equal.sym(List<&2, D.Rt>, List.append(&2, D.Rt, List.append(&2, D.Rt, h, D.Tmp.held(rest)), D.Tmp.held(B)),
        List.append(&2, D.Rt, h, List.append(&2, D.Rt, D.Tmp.held(rest), D.Tmp.held(B))), AC.app.assoc(h, D.Tmp.held(rest), D.Tmp.held(B)))

# an or of two Bools is False when both are
def or.ff(a: Bool, +b: Bool, ha: {a == False{} : Bool}, hb: {b == False{} : Bool}) -> {Bool.or(a, b) == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({Bool.or(True{}, b) == False{} : Bool}, N.true_ne_false(ha))
    case False{}:
      hb

# no cell of A ++ B is out: no cell of A or of B is
def mem.f.app.l(+A: List<&2, D.TmpE>, +B: List<&2, D.TmpE>, +c: U32,
  h: {D.Mem(D.Tmp.cells(List.append(&2, D.TmpE, A, B)), c) == False{} : Bool}) ->
  {D.Mem(D.Tmp.cells(A), c) == False{} : Bool}:
  D.or.f.l(D.Mem(D.Tmp.cells(A), c), D.Mem(D.Tmp.cells(B), c),
    (%AC.mem.app(D.Tmp.cells(A), D.Tmp.cells(B), c) : {_ == False{} : Bool};
     (%tmp.cells.app(A, B) : {D.Mem(_, c) == False{} : Bool}; h)))

def mem.f.app.r(+A: List<&2, D.TmpE>, +B: List<&2, D.TmpE>, +c: U32,
  h: {D.Mem(D.Tmp.cells(List.append(&2, D.TmpE, A, B)), c) == False{} : Bool}) ->
  {D.Mem(D.Tmp.cells(B), c) == False{} : Bool}:
  D.or.f.r(D.Mem(D.Tmp.cells(A), c), D.Mem(D.Tmp.cells(B), c),
    (%AC.mem.app(D.Tmp.cells(A), D.Tmp.cells(B), c) : {_ == False{} : Bool};
     (%tmp.cells.app(A, B) : {D.Mem(_, c) == False{} : Bool}; h)))

def mem.f.app(+A: List<&2, D.TmpE>, +B: List<&2, D.TmpE>, +c: U32, +ha: {D.Mem(D.Tmp.cells(A), c) == False{} : Bool},
  +hb: {D.Mem(D.Tmp.cells(B), c) == False{} : Bool}) -> {D.Mem(D.Tmp.cells(List.append(&2, D.TmpE, A, B)), c) == False{} : Bool}:
  Equal.trans(Bool, D.Mem(D.Tmp.cells(List.append(&2, D.TmpE, A, B)), c),
    D.Mem(List.append(&2, U32, D.Tmp.cells(A), D.Tmp.cells(B)), c), False{},
    Equal.cong(List<&2, U32>, Bool, l => D.Mem(l, c), D.Tmp.cells(List.append(&2, D.TmpE, A, B)),
      List.append(&2, U32, D.Tmp.cells(A), D.Tmp.cells(B)), tmp.cells.app(A, B)),
    Equal.trans(Bool, D.Mem(List.append(&2, U32, D.Tmp.cells(A), D.Tmp.cells(B)), c),
      Bool.or(D.Mem(D.Tmp.cells(A), c), D.Mem(D.Tmp.cells(B), c)), False{},
      AC.mem.app(D.Tmp.cells(A), D.Tmp.cells(B), c),
      or.ff(D.Mem(D.Tmp.cells(A), c), D.Mem(D.Tmp.cells(B), c), ha, hb)))

# a cell that no temporary of rest has is no cell of a temporary added first
def mem.f.cons(+ca: U32, +rest: List<&2, D.TmpE>, +c: U32, +he: {U32.is_eq(ca, c) == False{} : Bool},
  +hr: {D.Mem(D.Tmp.cells(rest), c) == False{} : Bool}) -> {D.Mem(Con{ca, D.Tmp.cells(rest)}, c) == False{} : Bool}:
  or.ff(U32.is_eq(ca, c), D.Mem(D.Tmp.cells(rest), c), he, hr)

# The single temporary moved to the front (U7)
# -------------------------------------------
# mat.lab releases the first cell of the arguments' chain, which sits after the
# environment's cells: AccK's temporaries go from X ++ [z] ++ C to [z] ++ X ++ C.
# AccK's other facts are sets (Cov and Clo read Mem), and the terms that the
# temporaries hold do not change (the moved one, a Lab's argument, holds none),
# so only Tmp.ok needs the move: (a) dropping z shrinks every remaining tail,
# (b) z's own facts come out of the list, (c) z is in no cell before it.

# A ++ B ++ C, with A's, B's and C's
def tmp.app.assoc(A: List<&2, D.TmpE>, +B: List<&2, D.TmpE>, +C: List<&2, D.TmpE>) ->
  {List.append(&2, D.TmpE, List.append(&2, D.TmpE, A, B), C) == List.append(&2, D.TmpE, A, List.append(&2, D.TmpE, B, C)) : List<&2, D.TmpE>}:
  match A:
    case Nil{}:
      {==}
    case Con{D.TmpE{c, h}, +rest}:
      %tmp.app.assoc(rest, B, C) : {Con{D.TmpE{c, h}, List.append(&2, D.TmpE, List.append(&2, D.TmpE, rest, B), C)} == Con{D.TmpE{c, h}, _} : List<&2, D.TmpE>}
      {==}

# a cell of a suffix is a cell of the suffix with a temporary put first
def mem.ins(+p: U32, +fr: List<&2, U32>, +L: List<&2, U32>, +x: U32,
  h: {D.Mem(List.append(&2, U32, fr, L), x) == True{} : Bool}) ->
  {D.Mem(List.append(&2, U32, fr, Con{p, L}), x) == True{} : Bool}:
  D.or.cases(D.Mem(fr, x), D.Mem(L, x), {D.Mem(List.append(&2, U32, fr, Con{p, L}), x) == True{} : Bool}, AC.mem.split(fr, L, x, h),
    e => AC.mem.inl(fr, Con{p, L}, x, e),
    e => AC.mem.inr(fr, Con{p, L}, x, D.or.r(U32.is_eq(p, x), D.Mem(L, x), e)))

# and a cell that a suffix with a temporary put first does not hold is no cell of the suffix
def mem.ins.f(+p: U32, +fr: List<&2, U32>, +L: List<&2, U32>, +x: U32,
  h: {D.Mem(List.append(&2, U32, fr, Con{p, L}), x) == False{} : Bool}) ->
  {D.Mem(List.append(&2, U32, fr, L), x) == False{} : Bool}:
  AC.bool.mt(D.Mem(List.append(&2, U32, fr, L), x), D.Mem(List.append(&2, U32, fr, Con{p, L}), x),
    e => mem.ins(p, fr, L, x, e), h)

# Tmp.ok of a list with a temporary dropped: every other tail only shrinks
def tmp.ok.del.z(X: List<&2, D.TmpE>, +z: U32, +C: List<&2, D.TmpE>, +m: Cr.Cir.Cells, +fi: U32, +nx: U32,
  +ps: List<&2, U32>, +rs: List<&2, D.Rt>,
  +h: {D.Tmp.ok(List.append(&2, D.TmpE, X, Con{D.TmpE{z, Nil{}}, C}), m, fi, nx, ps, rs) == True{} : Bool}) ->
  {D.Tmp.ok(List.append(&2, D.TmpE, X, C), m, fi, nx, ps, rs) == True{} : Bool}:
  match X:
    case Nil{}:
      AC.tok.rest(z, Nil{}, C, m, fi, nx, ps, rs, h)
    case Con{D.TmpE{+c, +hc}, +rest}:
      +tail = List.append(&2, D.TmpE, rest, Con{D.TmpE{z, Nil{}}, C})
      +ih = tmp.ok.del.z(rest, z, C, m, fi, nx, ps, rs, AC.tok.rest(c, hc, tail, m, fi, nx, ps, rs, h))
      +hd = {(%tmp.cells.app(rest, Con{D.TmpE{z, Nil{}}, C}) : {D.Mem(_, c) == False{} : Bool};
          AC.tok.dist(c, hc, tail, m, fi, nx, ps, rs, h)) :
        {D.Mem(List.append(&2, U32, D.Tmp.cells(rest), Con{z, D.Tmp.cells(C)}), c) == False{} : Bool}}
      +p3 = {(%Equal.sym(List<&2, U32>, D.Tmp.cells(List.append(&2, D.TmpE, rest, C)), List.append(&2, U32, D.Tmp.cells(rest), D.Tmp.cells(C)), tmp.cells.app(rest, C)) :
          {D.Mem(_, c) == False{} : Bool};
        mem.ins.f(z, D.Tmp.cells(rest), D.Tmp.cells(C), c, hd)) :
        {D.Mem(D.Tmp.cells(List.append(&2, D.TmpE, rest, C)), c) == False{} : Bool}}
      AC.tok.mk(c, hc, List.append(&2, D.TmpE, rest, C), m, fi, nx, ps, rs,
        AC.tok.own(c, hc, tail, m, fi, nx, ps, rs, h),
        AC.tok.fl(c, hc, tail, m, fi, nx, ps, rs, h),
        AC.tok.ps(c, hc, tail, m, fi, nx, ps, rs, h),
        p3,
        AC.tok.nd(c, hc, tail, m, fi, nx, ps, rs, h),
        AC.tok.fs(c, hc, tail, m, fi, nx, ps, rs, h),
        ih)

# Tmp.ok of the entry z, out of the list before it
def tmp.ok.at.z(X: List<&2, D.TmpE>, +z: U32, +C: List<&2, D.TmpE>, +m: Cr.Cir.Cells, +fi: U32, +nx: U32,
  +ps: List<&2, U32>, +rs: List<&2, D.Rt>,
  +h: {D.Tmp.ok(List.append(&2, D.TmpE, X, Con{D.TmpE{z, Nil{}}, C}), m, fi, nx, ps, rs) == True{} : Bool}) ->
  {D.Tmp.ok(Con{D.TmpE{z, Nil{}}, C}, m, fi, nx, ps, rs) == True{} : Bool}:
  match X:
    case Nil{}:
      h
    case Con{D.TmpE{+c, +hc}, +rest}:
      tmp.ok.at.z(rest, z, C, m, fi, nx, ps, rs,
        AC.tok.rest(c, hc, List.append(&2, D.TmpE, rest, Con{D.TmpE{z, Nil{}}, C}), m, fi, nx, ps, rs, h))

# the moved temporary is in no cell before it: the entries before it exclude their tails
def tmp.ok.notmem(X: List<&2, D.TmpE>, +z: U32, +C: List<&2, D.TmpE>, +m: Cr.Cir.Cells, +fi: U32, +nx: U32,
  +ps: List<&2, U32>, +rs: List<&2, D.Rt>,
  +h: {D.Tmp.ok(List.append(&2, D.TmpE, X, Con{D.TmpE{z, Nil{}}, C}), m, fi, nx, ps, rs) == True{} : Bool}) ->
  {D.Mem(D.Tmp.cells(X), z) == False{} : Bool}:
  match X:
    case Nil{}:
      {==}
    case Con{D.TmpE{+c, +hc}, +rest}:
      +tail = List.append(&2, D.TmpE, rest, Con{D.TmpE{z, Nil{}}, C})
      +hd = {(%tmp.cells.app(rest, Con{D.TmpE{z, Nil{}}, C}) : {D.Mem(_, c) == False{} : Bool};
          AC.tok.dist(c, hc, tail, m, fi, nx, ps, rs, h)) :
        {D.Mem(List.append(&2, U32, D.Tmp.cells(rest), Con{z, D.Tmp.cells(C)}), c) == False{} : Bool}}
      +h2 = {(%AC.mem.app(D.Tmp.cells(rest), Con{z, D.Tmp.cells(C)}, c) : {_ == False{} : Bool}; hd) :
        {Bool.or(D.Mem(D.Tmp.cells(rest), c), D.Mem(Con{z, D.Tmp.cells(C)}, c)) == False{} : Bool}}
      +hz = D.or.f.l(U32.is_eq(z, c), D.Mem(D.Tmp.cells(C), c),
        D.or.f.r(D.Mem(D.Tmp.cells(rest), c), D.Mem(Con{z, D.Tmp.cells(C)}, c), h2))
      or.ff(U32.is_eq(c, z), D.Mem(D.Tmp.cells(rest), z), D.ne.sym(z, c, hz),
        tmp.ok.notmem(rest, z, C, m, fi, nx, ps, rs, AC.tok.rest(c, hc, tail, m, fi, nx, ps, rs, h)))

# Tmp.ok with the single temporary z moved to the front
def tmp.ok.move(+z: U32, +X: List<&2, D.TmpE>, +C: List<&2, D.TmpE>, +m: Cr.Cir.Cells, +fi: U32, +nx: U32,
  +ps: List<&2, U32>, +rs: List<&2, D.Rt>,
  +h: {D.Tmp.ok(List.append(&2, D.TmpE, X, Con{D.TmpE{z, Nil{}}, C}), m, fi, nx, ps, rs) == True{} : Bool}) ->
  {D.Tmp.ok(Con{D.TmpE{z, Nil{}}, List.append(&2, D.TmpE, X, C)}, m, fi, nx, ps, rs) == True{} : Bool}:
  +hz = tmp.ok.at.z(X, z, C, m, fi, nx, ps, rs, h)
  +ht = tmp.ok.del.z(X, z, C, m, fi, nx, ps, rs, h)
  +hn = tmp.ok.notmem(X, z, C, m, fi, nx, ps, rs, h)
  +hzc = AC.tok.dist(z, Nil{}, C, m, fi, nx, ps, rs, hz)
  +p3 = {(%Equal.sym(Bool, D.Mem(List.append(&2, U32, D.Tmp.cells(X), D.Tmp.cells(C)), z),
        Bool.or(D.Mem(D.Tmp.cells(X), z), D.Mem(D.Tmp.cells(C), z)), AC.mem.app(D.Tmp.cells(X), D.Tmp.cells(C), z)) :
      {_ == False{} : Bool};
      or.ff(D.Mem(D.Tmp.cells(X), z), D.Mem(D.Tmp.cells(C), z), hn, hzc)) :
    {D.Mem(List.append(&2, U32, D.Tmp.cells(X), D.Tmp.cells(C)), z) == False{} : Bool}}
  AC.tok.mk(z, Nil{}, List.append(&2, D.TmpE, X, C), m, fi, nx, ps, rs,
    AC.tok.own(z, Nil{}, C, m, fi, nx, ps, rs, hz),
    AC.tok.fl(z, Nil{}, C, m, fi, nx, ps, rs, hz),
    AC.tok.ps(z, Nil{}, C, m, fi, nx, ps, rs, hz),
    (%Equal.sym(List<&2, U32>, D.Tmp.cells(List.append(&2, D.TmpE, X, C)), List.append(&2, U32, D.Tmp.cells(X), D.Tmp.cells(C)), tmp.cells.app(X, C)) :
      {D.Mem(_, z) == False{} : Bool};
      p3),
    AC.tok.nd(z, Nil{}, C, m, fi, nx, ps, rs, hz),
    AC.tok.fs(z, Nil{}, C, m, fi, nx, ps, rs, hz),
    ht)

# AccK under one temporary moved to the front (U7)
# ------------------------------------------------
# WH's AccK holds the chains' cells in order, and mat.lab releases the head of
# the arguments' chain, which is not first when the environment's chain is not
# empty; acc.release needs it first. AccK's facts are about sets, except this
# order: Cov and Clo read Mem of the cells, RtsK and Tmp.ok read the terms that
# the temporaries hold (the Lab argument holds none).

# (A ++ B) ++ C is A ++ (B ++ C), for the cells' lists
def app.assoc.u(A: List<&2, U32>, +B: List<&2, U32>, +C: List<&2, U32>) ->
  {List.append(&2, U32, List.append(&2, U32, A, B), C) == List.append(&2, U32, A, List.append(&2, U32, B, C)) : List<&2, U32>}:
  match A:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      %app.assoc.u(rest, B, C) : {Con{y, List.append(&2, U32, List.append(&2, U32, rest, B), C)} == Con{y, _} : List<&2, U32>}
      {==}

# (A ++ (B ++ C)) ++ D is A ++ (B ++ (C ++ D))
def app.assoc.u3(A: List<&2, U32>, +B: List<&2, U32>, +C: List<&2, U32>, +D: List<&2, U32>) ->
  {List.append(&2, U32, List.append(&2, U32, A, List.append(&2, U32, B, C)), D) ==
    List.append(&2, U32, A, List.append(&2, U32, B, List.append(&2, U32, C, D))) : List<&2, U32>}:
  Equal.trans(List<&2, U32>,
    List.append(&2, U32, List.append(&2, U32, A, List.append(&2, U32, B, C)), D),
    List.append(&2, U32, A, List.append(&2, U32, List.append(&2, U32, B, C), D)),
    List.append(&2, U32, A, List.append(&2, U32, B, List.append(&2, U32, C, D))),
    app.assoc.u(A, List.append(&2, U32, B, C), D),
    Equal.cong(List<&2, U32>, List<&2, U32>, l => List.append(&2, U32, A, l),
      List.append(&2, U32, List.append(&2, U32, B, C), D),
      List.append(&2, U32, B, List.append(&2, U32, C, D)), app.assoc.u(B, C, D)))

# the temporaries hold no term of the first one: its cell holds none
def tmp.held.hd(+z: U32, +C: List<&2, D.TmpE>) ->
  {D.Tmp.held(Con{D.TmpE{z, Nil{}}, C}) == D.Tmp.held(C) : List<&2, D.Rt>}:
  {==}

def tmp.held.move(+X: List<&2, D.TmpE>, +z: U32, +C: List<&2, D.TmpE>) ->
  {D.Tmp.held(List.append(&2, D.TmpE, X, Con{D.TmpE{z, Nil{}}, C})) ==
    D.Tmp.held(Con{D.TmpE{z, Nil{}}, List.append(&2, D.TmpE, X, C)}) : List<&2, D.Rt>}:
  Equal.trans(List<&2, D.Rt>, D.Tmp.held(List.append(&2, D.TmpE, X, Con{D.TmpE{z, Nil{}}, C})),
    List.append(&2, D.Rt, D.Tmp.held(X), D.Tmp.held(C)),
    D.Tmp.held(Con{D.TmpE{z, Nil{}}, List.append(&2, D.TmpE, X, C)}),
    Equal.trans(List<&2, D.Rt>, D.Tmp.held(List.append(&2, D.TmpE, X, Con{D.TmpE{z, Nil{}}, C})),
      List.append(&2, D.Rt, D.Tmp.held(X), D.Tmp.held(Con{D.TmpE{z, Nil{}}, C})),
      List.append(&2, D.Rt, D.Tmp.held(X), D.Tmp.held(C)),
      tmp.held.app(X, Con{D.TmpE{z, Nil{}}, C}),
      Equal.cong(List<&2, D.Rt>, List<&2, D.Rt>, l => List.append(&2, D.Rt, D.Tmp.held(X), l),
        D.Tmp.held(Con{D.TmpE{z, Nil{}}, C}), D.Tmp.held(C), tmp.held.hd(z, C))),
    Equal.sym(List<&2, D.Rt>, D.Tmp.held(Con{D.TmpE{z, Nil{}}, List.append(&2, D.TmpE, X, C)}),
      List.append(&2, D.Rt, D.Tmp.held(X), D.Tmp.held(C)),
      Equal.trans(List<&2, D.Rt>, D.Tmp.held(Con{D.TmpE{z, Nil{}}, List.append(&2, D.TmpE, X, C)}),
        D.Tmp.held(List.append(&2, D.TmpE, X, C)),
        List.append(&2, D.Rt, D.Tmp.held(X), D.Tmp.held(C)),
        tmp.held.hd(z, List.append(&2, D.TmpE, X, C)),
        tmp.held.app(X, C))))

# Cov does not change when the roots are rewritten to an equal list
def cov.rw(n: Nat, +m: Cr.Cir.Cells, +c: U32, +rs1: List<&2, D.Rt>, +rs2: List<&2, D.Rt>, +xs: List<&2, U32>,
  +e: {rs1 == rs2 : List<&2, D.Rt>}) ->
  {D.Cov(n, m, c, rs1, xs) == D.Cov(n, m, c, rs2, xs) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+(+k):
      %Equal.cong(List<&2, D.Rt>, Bool, l => D.Nodes(l, m, c), rs1, rs2, e) :
        {Bool.and(Bool.or(D.Fl(m, c, 1024), Bool.or(D.Nodes(rs1, m, c), D.Mem(xs, c))), D.Cov(k, m, U32.inc(c), rs1, xs)) ==
          Bool.and(Bool.or(D.Fl(m, c, 1024), Bool.or(_, D.Mem(xs, c))), D.Cov(k, m, U32.inc(c), rs2, xs)) : Bool}
      %cov.rw(k, m, U32.inc(c), rs1, rs2, xs, e) :
        {Bool.and(Bool.or(D.Fl(m, c, 1024), Bool.or(D.Nodes(rs1, m, c), D.Mem(xs, c))), D.Cov(k, m, U32.inc(c), rs1, xs)) ==
          Bool.and(Bool.or(D.Fl(m, c, 1024), Bool.or(D.Nodes(rs1, m, c), D.Mem(xs, c))), _) : Bool}
      {==}

# All.held does not change when two blocks of the cells trade places
def all.held.swap(ys: List<&2, U32>, +m: Cr.Cir.Cells, +P: List<&2, U32>, +A: List<&2, U32>, +B: List<&2, U32>,
  +C: List<&2, U32>, +hc: List<&2, U32>) ->
  {D.All.held(ys, m, List.append(&2, U32, P, List.append(&2, U32, A, List.append(&2, U32, B, C))), hc) ==
    D.All.held(ys, m, List.append(&2, U32, P, List.append(&2, U32, B, List.append(&2, U32, A, C))), hc) : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      +X1 = List.append(&2, U32, P, List.append(&2, U32, A, List.append(&2, U32, B, C)))
      +X2 = List.append(&2, U32, P, List.append(&2, U32, B, List.append(&2, U32, A, C)))
      %AC.mem.perm(P, A, B, C, y) :
        {Bool.and(Bool.or(D.Fl(m, y, 1024), Bool.or(D.Mem(X1, y), D.Mem(hc, y))), D.All.held(rest, m, X1, hc)) ==
          Bool.and(Bool.or(D.Fl(m, y, 1024), Bool.or(_, D.Mem(hc, y))), D.All.held(rest, m, X2, hc)) : Bool}
      %all.held.swap(rest, m, P, A, B, C, hc) :
        {Bool.and(Bool.or(D.Fl(m, y, 1024), Bool.or(D.Mem(X1, y), D.Mem(hc, y))), D.All.held(rest, m, X1, hc)) ==
          Bool.and(Bool.or(D.Fl(m, y, 1024), Bool.or(D.Mem(X1, y), D.Mem(hc, y))), _) : Bool}
      {==}

# Clo does not change when two blocks of the cells trade places
def clo.swap(n: Nat, +m: Cr.Cir.Cells, +c: U32, +ps: List<&2, U32>, +P: List<&2, U32>, +A: List<&2, U32>,
  +B: List<&2, U32>, +C: List<&2, U32>, +hc: List<&2, U32>) ->
  {D.Clo(n, m, c, ps, List.append(&2, U32, P, List.append(&2, U32, A, List.append(&2, U32, B, C))), hc) ==
    D.Clo(n, m, c, ps, List.append(&2, U32, P, List.append(&2, U32, B, List.append(&2, U32, A, C))), hc) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+(+k):
      +X1 = List.append(&2, U32, P, List.append(&2, U32, A, List.append(&2, U32, B, C)))
      +X2 = List.append(&2, U32, P, List.append(&2, U32, B, List.append(&2, U32, A, C)))
      +F = D.Fs(m, ps, c)
      +S1 = Bool.or(Bool.not(D.Fl(m, c, 1024)), D.All.static(F, m))
      %AC.mem.perm(P, A, B, C, c) :
        {Bool.and(Bool.and(S1, Bool.or(Bool.not(D.Mem(X1, c)), D.All.held(F, m, X1, hc))), D.Clo(k, m, U32.inc(c), ps, X1, hc)) ==
          Bool.and(Bool.and(S1, Bool.or(Bool.not(_), D.All.held(F, m, X2, hc))), D.Clo(k, m, U32.inc(c), ps, X2, hc)) : Bool}
      %all.held.swap(F, m, P, A, B, C, hc) :
        {Bool.and(Bool.and(S1, Bool.or(Bool.not(D.Mem(X1, c)), D.All.held(F, m, X1, hc))), D.Clo(k, m, U32.inc(c), ps, X1, hc)) ==
          Bool.and(Bool.and(S1, Bool.or(Bool.not(D.Mem(X1, c)), _)), D.Clo(k, m, U32.inc(c), ps, X2, hc)) : Bool}
      %clo.swap(k, m, U32.inc(c), ps, P, A, B, C, hc) :
        {Bool.and(Bool.and(S1, Bool.or(Bool.not(D.Mem(X1, c)), D.All.held(F, m, X1, hc))), D.Clo(k, m, U32.inc(c), ps, X1, hc)) ==
          Bool.and(Bool.and(S1, Bool.or(Bool.not(D.Mem(X1, c)), D.All.held(F, m, X1, hc))), _) : Bool}
      {==}

# the terms of A stand for their terms, and A is B
def rtsk.rw(+dk: Bool, A: List<&2, D.Rt>, +B: List<&2, D.Rt>, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32,
  +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +e: {A == B : List<&2, D.Rt>}, h: D.RtsK(dk, ds, m, im, fi, nx, ks, img, A)) -> D.RtsK(dk, ds, m, im, fi, nx, ks, img, B):
  %e : D.RtsK(dk, ds, m, im, fi, nx, ks, img, _)
  h

# AccK with the one temporary z moved from after X to the front
def acck.move(+dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +rs: List<&2, D.Rt>, +X: List<&2, D.TmpE>, +z: U32,
  +C: List<&2, D.TmpE>, +sp: U32, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  hac: D.AccK(dk, ds, ks, img, m, nx, fi, im, rs, List.append(&2, D.TmpE, X, Con{D.TmpE{z, Nil{}}, C}), sp, fs, ps, zs)) ->
  D.AccK(dk, ds, ks, img, m, nx, fi, im, rs, Con{D.TmpE{z, Nil{}}, List.append(&2, D.TmpE, X, C)}, sp, fs, ps, zs):
  match hac:
    case Tuple{hz, Tuple{hh, Tuple{he, Tuple{hc, Tuple{hcl, htok}}}}}:
      +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
      +XO = List.append(&2, D.TmpE, X, Con{D.TmpE{z, Nil{}}, C})
      +XN = List.append(&2, D.TmpE, Con{D.TmpE{z, Nil{}}, Nil{}}, List.append(&2, D.TmpE, X, C))
      +csX = D.Tmp.cells(X)
      +csC = D.Tmp.cells(C)
      +csO = D.Tmp.cells(XO)
      +csN = D.Tmp.cells(XN)
      +hlO = D.Tmp.held(XO)
      +hlN = D.Tmp.held(XN)
      +frt = D.Fr.rts(fs, m, sp)
      +frc = D.Fr.cells(fs, m, sp)
      +RS_O = List.append(&2, D.Rt, rs, List.append(&2, D.Rt, hlO, List.append(&2, D.Rt, frt, zs)))
      +RS_N = List.append(&2, D.Rt, rs, List.append(&2, D.Rt, hlN, List.append(&2, D.Rt, frt, zs)))
      +OBL = List.append(&2, U32, frc, List.append(&2, U32, csO, ps))
      +NBL = List.append(&2, U32, frc, List.append(&2, U32, csN, ps))
      +e_hl = tmp.held.move(X, z, C)
      +e_rs = Equal.cong(List<&2, D.Rt>, List<&2, D.Rt>,
        l => List.append(&2, D.Rt, rs, List.append(&2, D.Rt, l, List.append(&2, D.Rt, frt, zs))), hlO, hlN, e_hl)
      +hh2 = {(%e_hl : D.RtsK(dk, ds, m, im, fi, nx, ks, img, _); hh) : D.RtsK(dk, ds, m, im, fi, nx, ks, img, hlN)}
      +e_csO = tmp.cells.app(X, Con{D.TmpE{z, Nil{}}, C})
      +e_csN = Equal.cong(List<&2, U32>, List<&2, U32>, l => Con{z, l},
        D.Tmp.cells(List.append(&2, D.TmpE, X, C)), List.append(&2, U32, csX, csC), tmp.cells.app(X, C))
      +O2 = List.append(&2, U32, frc, List.append(&2, U32, List.append(&2, U32, csX, Con{z, csC}), ps))
      +O3 = List.append(&2, U32, frc, List.append(&2, U32, csX, List.append(&2, U32, Con{z, csC}, ps)))
      +eO1 = Equal.cong(List<&2, U32>, List<&2, U32>, l => List.append(&2, U32, frc, List.append(&2, U32, l, ps)),
        csO, List.append(&2, U32, csX, Con{z, csC}), e_csO)
      +eO2 = Equal.cong(List<&2, U32>, List<&2, U32>, l => List.append(&2, U32, frc, l),
        List.append(&2, U32, List.append(&2, U32, csX, Con{z, csC}), ps),
        List.append(&2, U32, csX, List.append(&2, U32, Con{z, csC}, ps)), app.assoc.u(csX, Con{z, csC}, ps))
      +eO = Equal.trans(List<&2, U32>, OBL, O2, O3, eO1, eO2)
      +N2 = List.append(&2, U32, frc, List.append(&2, U32, Con{z, List.append(&2, U32, csX, csC)}, ps))
      +N3 = List.append(&2, U32, frc, Con{z, List.append(&2, U32, csX, List.append(&2, U32, csC, ps))})
      +eN1 = Equal.cong(List<&2, U32>, List<&2, U32>, l => List.append(&2, U32, frc, List.append(&2, U32, l, ps)),
        csN, Con{z, List.append(&2, U32, csX, csC)}, e_csN)
      +eN2 = Equal.cong(List<&2, U32>, List<&2, U32>, l => List.append(&2, U32, frc, l),
        List.append(&2, U32, Con{z, List.append(&2, U32, csX, csC)}, ps), Con{z, List.append(&2, U32, csX, List.append(&2, U32, csC, ps))},
        Equal.cong(List<&2, U32>, List<&2, U32>, l => Con{z, l}, List.append(&2, U32, List.append(&2, U32, csX, csC), ps),
          List.append(&2, U32, csX, List.append(&2, U32, csC, ps)), app.assoc.u(csX, csC, ps)))
      +eN = Equal.trans(List<&2, U32>, NBL, N2, N3, eN1, eN2)
      +C1 = D.Cov(n, m, fi, RS_O, OBL)
      +C2 = D.Cov(n, m, fi, RS_N, OBL)
      +C3 = D.Cov(n, m, fi, RS_N, O3)
      +C4 = D.Cov(n, m, fi, RS_N, N3)
      +C5 = D.Cov(n, m, fi, RS_N, NBL)
      +hc2 = AC.cov.mv(C1, C2, cov.rw(n, m, fi, RS_O, RS_N, OBL, e_rs), hc)
      +hc3 = AC.cov.mv(C2, C3, Equal.cong(List<&2, U32>, Bool, w => D.Cov(n, m, fi, RS_N, w), OBL, O3, eO), hc2)
      +hc4 = AC.cov.mv(C3, C4, AC.cov.perm.x(n, m, fi, RS_N, frc, csX, Con{z, Nil{}}, List.append(&2, U32, csC, ps)), hc3)
      +hc5 = AC.cov.mv(C4, C5, Equal.cong(List<&2, U32>, Bool, w => D.Cov(n, m, fi, RS_N, w), N3, NBL,
        Equal.sym(List<&2, U32>, NBL, N3, eN)), hc4)
      +e_rh = Equal.cong(List<&2, D.Rt>, List<&2, U32>, l => D.Rt.cells(l), hlO, hlN, e_hl)
      +K1 = D.Clo(n, m, fi, ps, List.append(&2, U32, csX, Con{z, csC}), D.Rt.cells(hlO))
      +K2 = D.Clo(n, m, fi, ps, Con{z, List.append(&2, U32, csX, csC)}, D.Rt.cells(hlO))
      +K3 = D.Clo(n, m, fi, ps, Con{z, List.append(&2, U32, csX, csC)}, D.Rt.cells(hlN))
      +K4 = D.Clo(n, m, fi, ps, csN, D.Rt.cells(hlN))
      +hcl1 = AC.cov.mv(D.Clo(n, m, fi, ps, csO, D.Rt.cells(hlO)), K1,
        Equal.cong(List<&2, U32>, Bool, w => D.Clo(n, m, fi, ps, w, D.Rt.cells(hlO)), csO,
          List.append(&2, U32, csX, Con{z, csC}), e_csO), hcl)
      +hcl2 = AC.cov.mv(K1, K2, clo.swap(n, m, fi, ps, Nil{}, csX, Con{z, Nil{}}, csC, D.Rt.cells(hlO)), hcl1)
      +hcl3 = AC.cov.mv(K2, K3, Equal.cong(List<&2, U32>, Bool,
        w => D.Clo(n, m, fi, ps, Con{z, List.append(&2, U32, csX, csC)}, w), D.Rt.cells(hlO), D.Rt.cells(hlN), e_rh), hcl2)
      +hcl4 = AC.cov.mv(K3, K4, Equal.cong(List<&2, U32>, Bool, w => D.Clo(n, m, fi, ps, w, D.Rt.cells(hlN)),
        Con{z, List.append(&2, U32, csX, csC)}, csN,
        Equal.sym(List<&2, U32>, csN, Con{z, List.append(&2, U32, csX, csC)}, e_csN)), hcl3)
      +htok1 = AC.cov.mv(D.Tmp.ok(XO, m, fi, nx, ps, RS_O), D.Tmp.ok(XO, m, fi, nx, ps, RS_N),
        Equal.cong(List<&2, D.Rt>, Bool, w => D.Tmp.ok(XO, m, fi, nx, ps, w), RS_O, RS_N, e_rs), htok)
      +htok2 = tmp.ok.move(z, X, C, m, fi, nx, ps, RS_N, htok1)
      (hz, (hh2, (he, (hc5, (hcl4, htok2)))))

# The premises walk.post and walk.done of move_kit.bend (U7; U0 left them as ?TODO)
# ------------------------------------------------------------------------------

def K.walk.post(f, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, keep, os, bs, fs, sp, pend, ps, tc, tt, a, xs, xs0, zs, hs, hac, hst, hl, ht, ha, hp, args, hk):
  DW.Sim(f, Mc.M.walk(), X.X.st(regs, m, nx, fi, im, pg, lim, inp),
    st2 => D.WalkQ(ds, ks, img, regs, m, nx, fi, im, lim, inp, keep, os, Con{D.Rt{tc, tt}, bs}, fs, sp, ps, tt, a, xs, xs0, st2),
    W.B(m, nx, fi, os, sp, fs, tt, a, xs, xs0), lim,
    walk.wp(f, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, keep, os, bs, fs, sp, pend, ps, tc, tt, a, xs, xs0, zs,
      W.B(m, nx, fi, os, sp, fs, tt, a, xs, xs0), hs, hac, hst, hl, ht, ha, hp, args, hk))

def K.walk.done(ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, os, bs, fs, sp, pend, ps, tc, tt, a, xs, hs, hst, hl, ht, ha, hp, args):
  ?TODO
