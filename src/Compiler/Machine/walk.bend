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
import ../../Wasm/impl.bend as Wa
import ../Cir/impl.bend as Cr
import ./impl.bend as Mc
import ./definitions.bend as D
import ./statement_runs.bend as X
import ./data_walk.bend as DW
import ./move_kit.bend as K

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

# The premises walk.post and walk.done of move_kit.bend (U7; U0 left them as ?TODO)
# ------------------------------------------------------------------------------

def K.walk.post(f, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, keep, os, bs, fs, sp, pend, ps, tc, tt, a, xs, xs0, zs, hs, hac, hst, hl, ht, ha, hp, args, hk):
  ?TODO

def K.walk.done(ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, os, bs, fs, sp, pend, ps, tc, tt, a, xs, hs, hst, hl, ht, ha, hp, args):
  ?TODO
