# compiler: layer B, the machine
# ==============================
#
# The shared definitions (the invariant, the heap, Post, the premises' named
# types, the store and cell kit) live in definitions.bend (D); the
# execution equations of the machine's statements in statement_runs.bend (X).
# This file keeps the premises (open until the phases' lemmas exist), the
# moves, the loop and the assembly.
#
# mach.safe, mach.sound and mach.complete of runs_as_eval.bend, with exactly their
# types (mach.safe.proof, mach.sound.proof, mach.complete.proof, at the end
# of "The run"), from the invariant of the machine (Inv) and one lemma per
# move. The Lean machine (lean, Interpreter/Machine.lean, Interpreter/Machine/*.lean) is
# the template: a move is an admin move that keeps the term, or one step of
# Eval, and keeps what the state knows.
#
# Kit (Post): what a statement's outcome may be, for any fuel (dn False) or
# for a fuel that ends it (dn True); more fuel keeps an outcome that ends
# (mono).
#
# Terms of states (A.*): a focus, to evaluate (mode 0) or a value (mode 1),
# and its frames (AF), the innermost first; their term (A.plugs) and the
# measure of the admin moves (A.w), which every admin move makes smaller.
#
# Inv(ds, ks, img, st, t, w): between two rounds, the state st holds an
# abstract state (Wit) of the term t and the measure w: the registers RG
# (focus, mode, sp, pend, then R59); the focus' cell and the frames' parts
# stand for their terms (Is, by recursion on the term, in the machine's own
# U32 forms, with VALUE, DATA and fv true of them); the frames (Frs); the
# counts and the pend list (Heap: a term cell counts at least its pointers,
# the pend list's cells have none, a pointer is below next); the image (ImgOK:
# the table, the defs' bodies, the labels of Q0 to Q2, the names); no output.
#
# Moves (MV, mv.*): one round of the main loop (B.body) from a state that Inv
# finds is, for any fuel, an admin move (Inv of the same term, a smaller
# measure), a step (Inv of u with Eval.step(ds, t) == Some{u}), a halt as HR
# says (0: t's bytes; 2: no step and no result), or out of memory; and it
# ends with some fuel. round.mv picks the move by the abstract state; the
# premises on M.copy, M.data, M.walk, M.out and M.input are open defs
# (copy.post, data.post, walk.post, out.post, input.post and their .done).
#
# The loop: loop.post (by induction on the fuel) gives only what Eval gives;
# loop.done (by induction on Eval's steps, then on the measure) finds a fuel
# that gives it, or runs out of memory.
#
# Proven: the kit, mono, the loop, the run from Cir.result's start, the
# three lemmas; the choice of the moves (round.post, round.done); the moves
# mv.ev.val, mv.ev.former, mv.ev.var and mv.out. Open (?TODO): the other
# moves, the premises above, the frame conditions of allocation (is.pend,
# is.fresh), Eval's ev.stops and ev.stuck, and mach.memory with what it
# needs (round.peak, round.room).

import Base
import ../../Book/impl.bend as Bk
import ../../Eval/impl.bend as El
import ../../Wasm/impl.bend as Wa
import ../../Program/impl.bend as Pg
import ../Cir/impl.bend as Cr
import ./impl.bend as Mc
import ./cell_terms.bend as T
import ../need_big.bend as N
import ./definitions.bend as D
import ./statement_runs.bend as X
import ./eval_facts.bend as EV
import ./cell_stands_for.bend as PI
import ./out_bytes_from_is.bend as OI
import ./swap_moves.bend as SW
import ./cir_fits.bend as CF

# Open: the premises (the phases' lemmas)
# ---------------------------------------
#
# Each is a lemma of a phase file, with exactly this type: its conclusion is
# the named type of definitions.bend.


def copy.post(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +r: Nat, +src: Nat,
  +keep: List<&2, Nat>, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>,
  +c: U32, +t: Bk.Term, +ce: U32, +es: List<&2, El.Arg>,
  hs: D.HS(ds, ks, img, m, nx, fi, im, os, Con{D.Rt{c, t}, bs}, fs, sp, pend, ps),
  hl: {List.length(&2, U32, regs) == 63n : Nat},
  hc: {List.get(&2, U32, regs, src) == Some{c} : Maybe<&2, U32>},
  hp: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>},
  he: {List.get(&2, U32, regs, 36n) == Some{ce} : Maybe<&2, U32>},
  hn: {List.get(&2, U32, regs, 37n) == Some{U32.from_nat(List.length(&2, El.Arg, es))} : Maybe<&2, U32>},
  env: D.Ag(ds, m, im, fi, nx, ks, img, ps, os, ce, es),
  hr: {Bool.and(Nat.is_lt(r, 63n), Bool.not(D.Nat.mem([3n, 39n], r))) == True{} : Bool},
  hsrc: {D.Nat.mem([4n, 5n, 6n, 7n, 39n], src) == False{} : Bool},
  ho: N.Le(List.length(&2, D.Rt, os), 64n),
  hv: {D.Terms.below(D.Arg.terms(es), U32.to_nat(2147483648)) == True{} : Bool},
  hk: {D.Disj(keep, D.Copy.scr(r)) == True{} : Bool}) ->
  D.CopyPost(f, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, r, src, keep, os, bs, fs, sp, pend, ps, c, t, ce, es, hs, hl, hc, hp, he, hn, env, hr, hsrc, ho, hv, hk):
  ?TODO


def copy.done(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +r: Nat, +src: Nat,
  +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>,
  +c: U32, +t: Bk.Term, +ce: U32, +es: List<&2, El.Arg>,
  hs: D.HS(ds, ks, img, m, nx, fi, im, os, Con{D.Rt{c, t}, bs}, fs, sp, pend, ps),
  hl: {List.length(&2, U32, regs) == 63n : Nat},
  hc: {List.get(&2, U32, regs, src) == Some{c} : Maybe<&2, U32>},
  hp: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>},
  he: {List.get(&2, U32, regs, 36n) == Some{ce} : Maybe<&2, U32>},
  hn: {List.get(&2, U32, regs, 37n) == Some{U32.from_nat(List.length(&2, El.Arg, es))} : Maybe<&2, U32>},
  env: D.Ag(ds, m, im, fi, nx, ks, img, ps, os, ce, es),
  hr: {Bool.and(Nat.is_lt(r, 63n), Bool.not(D.Nat.mem([3n, 39n], r))) == True{} : Bool},
  hsrc: {D.Nat.mem([4n, 5n, 6n, 7n, 39n], src) == False{} : Bool},
  ho: N.Le(List.length(&2, D.Rt, os), 64n)) ->
  D.CopyDone(ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, r, src, os, bs, fs, sp, pend, ps, c, t, ce, es, hs, hl, hc, hp, he, hn, env, hr, hsrc, ho):
  ?TODO


def data.post(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +r: Nat,
  +keep: List<&2, Nat>, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>,
  +c: U32, +v: Bk.Term,
  hs: D.HS(ds, ks, img, m, nx, fi, im, os, Con{D.Rt{c, v}, bs}, fs, sp, pend, ps),
  hl: {List.length(&2, U32, regs) == 63n : Nat},
  hc: {List.get(&2, U32, regs, r) == Some{c} : Maybe<&2, U32>},
  hp: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>},
  hr: {D.Nat.mem(D.Data.scr(), r) == False{} : Bool},
  hk: {D.Disj(keep, D.Data.scr()) == True{} : Bool}) ->
  D.DataPost(f, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, r, keep, os, bs, fs, sp, pend, ps, c, v, hs, hl, hc, hp, hr, hk):
  ?TODO


def data.done(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +r: Nat,
  +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>,
  +c: U32, +v: Bk.Term,
  hs: D.HS(ds, ks, img, m, nx, fi, im, os, Con{D.Rt{c, v}, bs}, fs, sp, pend, ps),
  hl: {List.length(&2, U32, regs) == 63n : Nat},
  hc: {List.get(&2, U32, regs, r) == Some{c} : Maybe<&2, U32>},
  hp: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>},
  hr: {D.Nat.mem(D.Data.scr(), r) == False{} : Bool}) ->
  D.DataDone(ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, r, os, bs, fs, sp, pend, ps, c, v, hs, hl, hc, hp, hr):
  ?TODO


def walk.post(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>,
  +keep: List<&2, Nat>, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>,
  +tc: U32, +tt: Bk.Term, +a: U32, +xs: List<&2, El.Arg>,
  hs: D.HS(ds, ks, img, m, nx, fi, im, os, Con{D.Rt{tc, tt}, bs}, fs, sp, pend, ps),
  hst: {D.Fl(m, tc, 1024) == True{} : Bool},
  hl: {List.length(&2, U32, regs) == 63n : Nat},
  ht: {List.get(&2, U32, regs, 19n) == Some{tc} : Maybe<&2, U32>},
  ha: {List.get(&2, U32, regs, 21n) == Some{a} : Maybe<&2, U32>},
  hp: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>},
  args: D.Ag(ds, m, im, fi, nx, ks, img, ps, os, a, xs),
  hk: {D.Disj(keep, D.Walk.scr()) == True{} : Bool}) ->
  D.WalkPost(f, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, keep, os, bs, fs, sp, pend, ps, tc, tt, a, xs, hs, hst, hl, ht, ha, hp, args, hk):
  ?TODO


def walk.done(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>,
  +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>,
  +tc: U32, +tt: Bk.Term, +a: U32, +xs: List<&2, El.Arg>,
  hs: D.HS(ds, ks, img, m, nx, fi, im, os, Con{D.Rt{tc, tt}, bs}, fs, sp, pend, ps),
  hst: {D.Fl(m, tc, 1024) == True{} : Bool},
  hl: {List.length(&2, U32, regs) == 63n : Nat},
  ht: {List.get(&2, U32, regs, 19n) == Some{tc} : Maybe<&2, U32>},
  ha: {List.get(&2, U32, regs, 21n) == Some{a} : Maybe<&2, U32>},
  hp: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>},
  args: D.Ag(ds, m, im, fi, nx, ks, img, ps, os, a, xs)) ->
  D.WalkDone(ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, os, bs, fs, sp, pend, ps, tc, tt, a, xs, hs, hst, hl, ht, ha, hp, args):
  ?TODO


def out.post(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32,
  +pend: U32, +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>,
  +v: Bk.Term, +ks2: List<&2, List<&2, Word(8n)>>,
  +hv: D.Is(ds, m, im, fi, nx, ks, img, foc, v),
  +hk: {ks == Mc.Img.known(ks2) : List<&2, List<&2, Word(8n)>>}) ->
  D.OutPost(f, ds, ks, img, foc, pend, rest, m, nx, fi, im, pg, lim, inp, v, ks2, hv, hk):
  OI.out.post(f, ds, ks, img, foc, pend, rest, m, nx, fi, im, pg, lim, inp, v, ks2, hv, hk,
    PI.is.tm(ds, m, im, fi, nx, ks, img, foc, v, hv))


def out.done(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32,
  +pend: U32, +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>,
  +v: Bk.Term, +ks2: List<&2, List<&2, Word(8n)>>,
  +hv: D.Is(ds, m, im, fi, nx, ks, img, foc, v),
  +hk: {ks == Mc.Img.known(ks2) : List<&2, List<&2, Word(8n)>>}) ->
  D.OutDone(ds, ks, img, foc, pend, rest, m, nx, fi, im, pg, lim, inp, v, ks2, hv, hk):
  OI.out.done(ds, ks, img, foc, pend, rest, m, nx, fi, im, pg, lim, inp, v, ks2, hv, hk,
    PI.is.tm(ds, m, im, fi, nx, ks, img, foc, v, hv))


# Open: the start (start_input.bend). From St0, with the image of a book that
# Book.read reads, M.input ends with InvIn, or runs out of memory, for any
# fuel; and with some fuel it ends.
def input.post(+f: Nat, +p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +m: U32, +k: U32, +len: U32,
  +pg: U32, +lim: U32, +first: U32,
  rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  small: {Mc.Img.small(p, 0) == True{} : Bool},
  s: D.Start(Mc.Img.cells(ds), i, m, k, len, pg, lim, first)) ->
  D.InputPost(f, p, ds, i, m, k, len, pg, lim, first, rd, small, s):
  ?TODO


def input.done(+p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +m: U32, +k: U32, +len: U32,
  +pg: U32, +lim: U32, +first: U32,
  rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  small: {Mc.Img.small(p, 0) == True{} : Bool},
  s: D.Start(Mc.Img.cells(ds), i, m, k, len, pg, lim, first)) ->
  D.InputDone(p, ds, i, m, k, len, pg, lim, first, rd, small, s):
  ?TODO



# Open lemmas
# -----------
#
# Each is a premise of the proofs below, in the shape that they use; a body
# ?TODO is still open.

# Eval: a value has no step (Lean's eval_value)
def ev.stops(+ds: List<&2, Bk.Def>, +t: Bk.Term, h: {El.Eval.vals(ds, t, False{}) == True{} : Bool}) ->
  {El.Eval.step(ds, t) == None{} : Maybe<Bk.Term>}:
  EV.ev.stops(ds, t, h)

# a term with a step is no value
def vals.of(b: Bool, +ds: List<&2, Bk.Def>, +t: Bk.Term, -u: Bk.Term, eb: {El.Eval.vals(ds, t, False{}) == b : Bool},
  es: {El.Eval.step(ds, t) == Some{u} : Maybe<Bk.Term>}) -> {El.Eval.vals(ds, t, False{}) == False{} : Bool}:
  match b:
    case False{}:
      eb
    case True{}:
      Empty.absurd({El.Eval.vals(ds, t, False{}) == False{} : Bool},
        D.st.ne(u, Equal.trans(Maybe<Bk.Term>, None{}, El.Eval.step(ds, t), Some{u},
          Equal.sym(Maybe<Bk.Term>, El.Eval.step(ds, t), None{}, ev.stops(ds, t, eb)), es)))

# Inv's facts of that state, with the abstract state of ret, focus and fs
def IV(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +t: Bk.Term, +w: Nat, +ret: Bool, +focus: Bk.Term,
  +fs: List<&2, D.AF>, +ps: List<&2, U32>) -> Data:
  D.InvOf(ds, ks, img, D.RG(foc, Bool.to_u32(ret), sp, pend, D.R59.list(rest)), m, nx, fi, im, Nil{}, 0, t, w, ret, focus, fs, foc, sp,
    pend, ps, rest)

# a move from st: for any fuel, a round that goes on (Rnd) or halts as HR
# says; and a fuel with which it ends
def MV(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st: Cr.Cir.State, +t: Bk.Term, +w: Nat) ->
  Type:
  (@f: Nat -> D.Post(False{}, Cr.Cir.exec(f, D.B.body(), st), s => D.Rnd(ds, ks, img, t, w, s), s => st2 => D.HR(ds, t, s, st2))) &
    D.Ex(Nat, f => D.Ends(Cr.Cir.exec(f, D.B.body(), st)))

def mv.post(+f: Nat, -ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -st: Cr.Cir.State,
  -t: Bk.Term, -w: Nat, h: MV(ds, ks, img, st, t, w)) ->
  D.Post(False{}, Cr.Cir.exec(f, D.B.body(), st), s => D.Rnd(ds, ks, img, t, w, s), s => st2 => D.HR(ds, t, s, st2)):
  match h:
    case Tuple{p, _}:
      p(f)

def mv.done(-ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -st: Cr.Cir.State, -t: Bk.Term,
  -w: Nat, h: MV(ds, ks, img, st, t, w)) -> D.Ex(Nat, f => D.Ends(Cr.Cir.exec(f, D.B.body(), st))):
  match h:
    case Tuple{_, d}:
      d

# a frame of App q □ x: app_arg or app_val
def FK.isapp(k: D.FK) -> Bool:
  match k:
    case D.FK.arg{}:
      True{}
    case D.FK.val{}:
      True{}
    case _:
      False{}

# a value by its form, as the table says (I.table's field 4): every former but
# Tup
def A.tbl(t: Bk.Term) -> Bool:
  match t:
    case Bk.Term.Typ{_}:
      True{}
    case Bk.Term.All{_, _, _}:
      True{}
    case Bk.Term.Lam{_, _}:
      True{}
    case Bk.Term.Sig{_, _, _}:
      True{}
    case Bk.Term.Prj{_}:
      True{}
    case Bk.Term.Enu{_}:
      True{}
    case Bk.Term.Lab{_}:
      True{}
    case Bk.Term.Mat{_, _, _}:
      True{}
    case Bk.Term.Efq{}:
      True{}
    case Bk.Term.Eql{_, _, _}:
      True{}
    case Bk.Term.Rfl{}:
      True{}
    case _:
      False{}

# a λ, a λ-match of pairs or of labels: the redexes of M.redex's first cases
def A.node(t: Bk.Term) -> Bool:
  match t:
    case Bk.Term.Lam{_, _}:
      True{}
    case Bk.Term.Prj{_}:
      True{}
    case Bk.Term.Mat{_, _, _}:
      True{}
    case _:
      False{}

# the table's cell of the tag of a term's cell is a cell
def vt.of(-m: Cr.Cir.Cells, -im: U32, -fi: U32, -nx: U32, -f0: U32, +focus: Bk.Term, etag: {D.TgW(f0) == D.A.tag(focus) : U32},
  tb: D.Tbl(m, im, fi, nx)) -> {Cr.Cir.is_cell(U32.add(272, U32.and(f0, 63)), im, fi, nx) == True{} : Bool}:
  %Equal.sym(U32, D.TgW(f0), D.A.tag(focus), etag) : {Cr.Cir.is_cell(U32.add(272, _), im, fi, nx) == True{} : Bool}
  D.tbl.at(m, im, fi, nx, focus, tb)

# the test of M.ev on a cell flagged VALUE is not 0
def nz.of(-f0: U32, +e4: U32, hv: {U32.is_ne(U32.and(f0, 256), 0) == True{} : Bool}) ->
  {U32.is_zero(U32.or(Bool.to_u32(U32.is_ne(U32.and(f0, 256), 0)), Bool.to_u32(U32.is_ne(e4, 0)))) == False{} : Bool}:
  %Equal.sym(Bool, U32.is_ne(U32.and(f0, 256), 0), True{}, hv) :
    {U32.is_zero(U32.or(Bool.to_u32(_), Bool.to_u32(U32.is_ne(e4, 0)))) == False{} : Bool}
  D.or1(U32.is_ne(e4, 0))

# field 4 of the table's cell of a tag: 1 for a value by its form
def A.f4(t: Bk.Term) -> U32:
  match t:
    case Bk.Term.Var{_}:
      0
    case Bk.Term.Ref{_}:
      0
    case Bk.Term.Ann{_, _}:
      0
    case Bk.Term.Let{_, _, _}:
      0
    case Bk.Term.Typ{_}:
      1
    case Bk.Term.Min{_, _}:
      0
    case Bk.Term.All{_, _, _}:
      1
    case Bk.Term.Lam{_, _}:
      1
    case Bk.Term.App{_, _, _}:
      0
    case Bk.Term.Sig{_, _, _}:
      1
    case Bk.Term.Tup{_, _, _}:
      0
    case Bk.Term.Prj{_}:
      1
    case Bk.Term.Enu{_}:
      1
    case Bk.Term.Lab{_}:
      1
    case Bk.Term.Mat{_, _, _}:
      1
    case Bk.Term.Efq{}:
      1
    case Bk.Term.Eql{_, _, _}:
      1
    case Bk.Term.Rfl{}:
      1
    case Bk.Term.Rwt{_, _, _}:
      0

def tbl.f4(-m: Cr.Cir.Cells, -im: U32, -fi: U32, -nx: U32, t: Bk.Term, h: D.Tbl(m, im, fi, nx)) ->
  {D.Fd(4n, m, U32.add(272, D.A.tag(t))) == A.f4(t) : U32}:
  match t:
    case Bk.Term.Var{_}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}:
          e
    case Bk.Term.Ref{_}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}:
          e
    case Bk.Term.Ann{_, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}:
          e
    case Bk.Term.Let{_, _, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}:
          e
    case Bk.Term.Typ{_}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}:
          e
    case Bk.Term.Min{_, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}:
          e
    case Bk.Term.All{_, _, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          e
    case Bk.Term.Lam{_, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          e
    case Bk.Term.App{_, _, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          e
    case Bk.Term.Sig{_, _, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          e
    case Bk.Term.Tup{_, _, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          e
    case Bk.Term.Prj{_}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          e
    case Bk.Term.Enu{_}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          e
    case Bk.Term.Lab{_}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          e
    case Bk.Term.Mat{_, _, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          e
    case Bk.Term.Efq{}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          e
    case Bk.Term.Eql{_, _, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          e
    case Bk.Term.Rfl{}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          e
    case Bk.Term.Rwt{_, _, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          e


# a value by its form, as the table says, has field 4 set
def f4.one(t: Bk.Term, hf: {A.tbl(t) == True{} : Bool}) -> {A.f4(t) == 1 : U32}:
  match t:
    case Bk.Term.Var{+x0}:
      D.bool.ft({A.f4(Bk.Term.Var{x0}) == 1 : U32}, hf)
    case Bk.Term.Ref{+x0}:
      D.bool.ft({A.f4(Bk.Term.Ref{x0}) == 1 : U32}, hf)
    case Bk.Term.Ann{+x0, +x1}:
      D.bool.ft({A.f4(Bk.Term.Ann{x0, x1}) == 1 : U32}, hf)
    case Bk.Term.Let{+x0, +x1, +x2}:
      D.bool.ft({A.f4(Bk.Term.Let{x0, x1, x2}) == 1 : U32}, hf)
    case Bk.Term.Typ{+x0}:
      {==}
    case Bk.Term.Min{+x0, +x1}:
      D.bool.ft({A.f4(Bk.Term.Min{x0, x1}) == 1 : U32}, hf)
    case Bk.Term.All{+x0, +x1, +x2}:
      {==}
    case Bk.Term.Lam{+x0, +x1}:
      {==}
    case Bk.Term.App{+x0, +x1, +x2}:
      D.bool.ft({A.f4(Bk.Term.App{x0, x1, x2}) == 1 : U32}, hf)
    case Bk.Term.Sig{+x0, +x1, +x2}:
      {==}
    case Bk.Term.Tup{+x0, +x1, +x2}:
      D.bool.ft({A.f4(Bk.Term.Tup{x0, x1, x2}) == 1 : U32}, hf)
    case Bk.Term.Prj{+x0}:
      {==}
    case Bk.Term.Enu{+x0}:
      {==}
    case Bk.Term.Lab{+x0}:
      {==}
    case Bk.Term.Mat{+x0, +x1, +x2}:
      {==}
    case Bk.Term.Efq{}:
      {==}
    case Bk.Term.Eql{+x0, +x1, +x2}:
      {==}
    case Bk.Term.Rfl{}:
      {==}
    case Bk.Term.Rwt{+x0, +x1, +x2}:
      D.bool.ft({A.f4(Bk.Term.Rwt{x0, x1, x2}) == 1 : U32}, hf)

# a value by its form, as the table says, is a value
def tbl.vals(+ds: List<&2, Bk.Def>, t: Bk.Term, hf: {A.tbl(t) == True{} : Bool}) ->
  {Bool.or(Bool.not(True{}), El.Eval.vals(ds, t, False{})) == True{} : Bool}:
  match t:
    case Bk.Term.Var{+x0}:
      D.bool.ft({Bool.or(Bool.not(True{}), El.Eval.vals(ds, Bk.Term.Var{x0}, False{})) == True{} : Bool}, hf)
    case Bk.Term.Ref{+x0}:
      D.bool.ft({Bool.or(Bool.not(True{}), El.Eval.vals(ds, Bk.Term.Ref{x0}, False{})) == True{} : Bool}, hf)
    case Bk.Term.Ann{+x0, +x1}:
      D.bool.ft({Bool.or(Bool.not(True{}), El.Eval.vals(ds, Bk.Term.Ann{x0, x1}, False{})) == True{} : Bool}, hf)
    case Bk.Term.Let{+x0, +x1, +x2}:
      D.bool.ft({Bool.or(Bool.not(True{}), El.Eval.vals(ds, Bk.Term.Let{x0, x1, x2}, False{})) == True{} : Bool}, hf)
    case Bk.Term.Typ{+x0}:
      {==}
    case Bk.Term.Min{+x0, +x1}:
      D.bool.ft({Bool.or(Bool.not(True{}), El.Eval.vals(ds, Bk.Term.Min{x0, x1}, False{})) == True{} : Bool}, hf)
    case Bk.Term.All{+x0, +x1, +x2}:
      {==}
    case Bk.Term.Lam{+x0, +x1}:
      {==}
    case Bk.Term.App{+x0, +x1, +x2}:
      D.bool.ft({Bool.or(Bool.not(True{}), El.Eval.vals(ds, Bk.Term.App{x0, x1, x2}, False{})) == True{} : Bool}, hf)
    case Bk.Term.Sig{+x0, +x1, +x2}:
      {==}
    case Bk.Term.Tup{+x0, +x1, +x2}:
      D.bool.ft({Bool.or(Bool.not(True{}), El.Eval.vals(ds, Bk.Term.Tup{x0, x1, x2}, False{})) == True{} : Bool}, hf)
    case Bk.Term.Prj{+x0}:
      {==}
    case Bk.Term.Enu{+x0}:
      {==}
    case Bk.Term.Lab{+x0}:
      {==}
    case Bk.Term.Mat{+x0, +x1, +x2}:
      {==}
    case Bk.Term.Efq{}:
      {==}
    case Bk.Term.Eql{+x0, +x1, +x2}:
      {==}
    case Bk.Term.Rfl{}:
      {==}
    case Bk.Term.Rwt{+x0, +x1, +x2}:
      D.bool.ft({Bool.or(Bool.not(True{}), El.Eval.vals(ds, Bk.Term.Rwt{x0, x1, x2}, False{})) == True{} : Bool}, hf)

def or1r(b: Bool) -> {U32.is_zero(U32.or(Bool.to_u32(b), 1)) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the test of M.ev on a value by its form is not 0
def nzf.of(-m: Cr.Cir.Cells, -im: U32, -fi: U32, -nx: U32, +f0: U32, +focus: Bk.Term, etag: {D.TgW(f0) == D.A.tag(focus) : U32},
  tb: D.Tbl(m, im, fi, nx), hf: {A.tbl(focus) == True{} : Bool}) ->
  {U32.is_zero(U32.or(Bool.to_u32(U32.is_ne(U32.and(f0, 256), 0)),
    Bool.to_u32(U32.is_ne(Cr.Cir.Cell.get(4n, Cr.Cir.Cells.get(m, U32.add(272, U32.and(f0, 63)))), 0)))) == False{} : Bool}:
  %Equal.sym(U32, D.TgW(f0), D.A.tag(focus), etag) :
    {U32.is_zero(U32.or(Bool.to_u32(U32.is_ne(U32.and(f0, 256), 0)),
      Bool.to_u32(U32.is_ne(Cr.Cir.Cell.get(4n, Cr.Cir.Cells.get(m, U32.add(272, _))), 0)))) == False{} : Bool}
  %Equal.sym(U32, D.Fd(4n, m, U32.add(272, D.A.tag(focus))), A.f4(focus), tbl.f4(m, im, fi, nx, focus, tb)) :
    {U32.is_zero(U32.or(Bool.to_u32(U32.is_ne(U32.and(f0, 256), 0)), Bool.to_u32(U32.is_ne(_, 0)))) == False{} : Bool}
  %Equal.sym(U32, A.f4(focus), 1, f4.one(focus, hf)) :
    {U32.is_zero(U32.or(Bool.to_u32(U32.is_ne(U32.and(f0, 256), 0)), Bool.to_u32(U32.is_ne(_, 0)))) == False{} : Bool}
  or1r(U32.is_ne(U32.and(f0, 256), 0))

# the test of M.ev on a value by its form, from the facts of its cell
def nzf.go(-ds: List<&2, Bk.Def>, -im: U32, -fi: U32, -nx: U32, +foc: U32, +m: Cr.Cir.Cells, +focus: Bk.Term,
  nd: D.Nd(ds, im, fi, nx, foc, Cr.Cir.Cells.get(m, foc), focus, D.A.tag(focus)), tb: D.Tbl(m, im, fi, nx),
  hf: {A.tbl(focus) == True{} : Bool}) ->
  {U32.is_zero(U32.or(Bool.to_u32(U32.is_ne(U32.and(D.Fd(0n, m, foc), 256), 0)), Bool.to_u32(U32.is_ne(Cr.Cir.Cell.get(4n, Cr.Cir.Cells.get(m, U32.add(272, U32.and(D.Fd(0n, m, foc), 63)))), 0)))) == False{} : Bool}:
  match nd:
    case Tuple{_, Tuple{_, Tuple{etag, _}}}:
      nzf.of(m, im, fi, nx, D.Fd(0n, m, foc), focus, etag, tb, hf)

# M.ev, past its first statement, and past its second
def B.cond2() -> Cr.Cir.Expr:
  Mc.M.or(Mc.M.flag(Mc.M.g(Mc.R.c()), Mc.F.value()), Mc.M.ne(Mc.M.entry(4n, Mc.M.g(Mc.R.c())), Mc.M.c(0)))

# a halt
def eq.halt(+f: Nat, +x: U32, +st: Cr.Cir.State) -> {Cr.Cir.exec(f, Cr.Cir.Stmt.halt{x}, st) == Cr.Cir.Out.halt{x, st} : Cr.Cir.Out}:
  match f:
    case 0n:
      {==}
    case 1n+g:
      {==}

# a then b, when a halts
def eq.seq.h(+f: Nat, a: Cr.Cir.Stmt, +b: Cr.Cir.Stmt, +st: Cr.Cir.State, +x: U32, +st1: Cr.Cir.State,
  e1: {Cr.Cir.exec(f, a, st) == Cr.Cir.Out.halt{x, st1} : Cr.Cir.Out}) ->
  {Cr.Cir.exec(f, Cr.Cir.Stmt.seq{a, b}, st) == Cr.Cir.Out.halt{x, st1} : Cr.Cir.Out}:
  match f:
    case 0n:
      %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(0n, a, st), Cr.Cir.Out.halt{x, st1}, e1) :
        {Cr.Cir.exec.then(_, u => Cr.Cir.exec(0n, b, u)) == Cr.Cir.Out.halt{x, st1} : Cr.Cir.Out}
      {==}
    case 1n+g:
      %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(1n+g, a, st), Cr.Cir.Out.halt{x, st1}, e1) :
        {Cr.Cir.exec.then(_, u => Cr.Cir.exec(1n+g, b, u)) == Cr.Cir.Out.halt{x, st1} : Cr.Cir.Out}
      {==}

# a test of the tag of a cell whose tag is another
def tag.ne(+f0: U32, +tag: U32, +x: U32, etag: {D.TgW(f0) == tag : U32}, e: {U32.is_eq(tag, x) == False{} : Bool}) ->
  {U32.is_zero(Wa.Wasm.op(Wa.Wasm.Op.eq{}, D.TgW(f0), x)) == True{} : Bool}:
  %Equal.sym(U32, D.TgW(f0), tag, etag) : {U32.is_zero(Wa.Wasm.op(Wa.Wasm.Op.eq{}, _, x)) == True{} : Bool}
  %Equal.sym(Bool, U32.is_eq(tag, x), False{}, e) : {U32.is_zero(Bool.to_u32(_)) == True{} : Bool}
  {==}

# the test of M.ev on a cell not flagged VALUE, whose tag's table field 4 is 0, is 0
def z.of(-m: Cr.Cir.Cells, -im: U32, -fi: U32, -nx: U32, +f0: U32, +focus: Bk.Term, etag: {D.TgW(f0) == D.A.tag(focus) : U32},
  tb: D.Tbl(m, im, fi, nx), hv: {U32.is_ne(U32.and(f0, 256), 0) == False{} : Bool}, h0: {A.f4(focus) == 0 : U32}) ->
  {U32.is_zero(U32.or(Bool.to_u32(U32.is_ne(U32.and(f0, 256), 0)),
    Bool.to_u32(U32.is_ne(Cr.Cir.Cell.get(4n, Cr.Cir.Cells.get(m, U32.add(272, U32.and(f0, 63)))), 0)))) == True{} : Bool}:
  %Equal.sym(U32, D.TgW(f0), D.A.tag(focus), etag) :
    {U32.is_zero(U32.or(Bool.to_u32(U32.is_ne(U32.and(f0, 256), 0)),
      Bool.to_u32(U32.is_ne(Cr.Cir.Cell.get(4n, Cr.Cir.Cells.get(m, U32.add(272, _))), 0)))) == True{} : Bool}
  %Equal.sym(U32, D.Fd(4n, m, U32.add(272, D.A.tag(focus))), A.f4(focus), tbl.f4(m, im, fi, nx, focus, tb)) :
    {U32.is_zero(U32.or(Bool.to_u32(U32.is_ne(U32.and(f0, 256), 0)), Bool.to_u32(U32.is_ne(_, 0)))) == True{} : Bool}
  %Equal.sym(U32, A.f4(focus), 0, h0) :
    {U32.is_zero(U32.or(Bool.to_u32(U32.is_ne(U32.and(f0, 256), 0)), Bool.to_u32(U32.is_ne(_, 0)))) == True{} : Bool}
  %Equal.sym(Bool, U32.is_ne(U32.and(f0, 256), 0), False{}, hv) :
    {U32.is_zero(U32.or(Bool.to_u32(_), Bool.to_u32(U32.is_ne(0, 0)))) == True{} : Bool}
  {==}

# Eval: a focus with no step that is no value makes its frames' term so
def ev.stuck(+ds: List<&2, Bk.Def>, fs: List<&2, D.AF>, +u: Bk.Term, hfs: D.AFs.ok(ds, fs),
  hs: {El.Eval.step(ds, u) == None{} : Maybe<Bk.Term>}, hv: {El.Eval.vals(ds, u, False{}) == False{} : Bool}) ->
  D.P2({El.Eval.step(ds, D.A.plugs(fs, u)) == None{} : Maybe<Bk.Term>}, {El.Eval.vals(ds, D.A.plugs(fs, u), False{}) == False{} : Bool}):
  EV.ev.stuck(ds, fs, u, hfs, hs, hv)

# a halt of a round, from a term equal to t
def hr.eq(+ds: List<&2, Bk.Def>, -u: Bk.Term, -t: Bk.Term, -s: U32, -st: Cr.Cir.State, e: {u == t : Bk.Term},
  h: D.HR(ds, u, s, st)) -> D.HR(ds, t, s, st):
  %e : D.HR(ds, _, s, st)
  h

# a halt with 2 from a term that is stuck
def hr.stuck(+ds: List<&2, Bk.Def>, +t: Bk.Term, -st: Cr.Cir.State,
  h: D.P2({El.Eval.step(ds, t) == None{} : Maybe<Bk.Term>}, {El.Eval.vals(ds, t, False{}) == False{} : Bool})) -> D.HR(ds, t, 2, st):
  match h:
    case Tuple{es, ev}:
      Inr{({==}, (es, D.res.nv(ds, t, ev)))}

# M.ev's tests of the tag, from the last
def B.e6() -> Cr.Cir.Stmt:
  Mc.M.if(Mc.M.eq(Mc.M.g(Mc.R.tag()), Mc.M.c(Mc.T.min())), Mc.M.ev.min(), Mc.M.halt(2))

def B.e5() -> Cr.Cir.Stmt:
  Mc.M.if(Mc.M.eq(Mc.M.g(Mc.R.tag()), Mc.M.c(Mc.T.rwt())), Mc.M.ev.rwt(), B.e6())

def B.e4() -> Cr.Cir.Stmt:
  Mc.M.if(Mc.M.eq(Mc.M.g(Mc.R.tag()), Mc.M.c(Mc.T.tup())), Mc.M.ev.tup(), B.e5())

def B.e3() -> Cr.Cir.Stmt:
  Mc.M.if(Mc.M.eq(Mc.M.g(Mc.R.tag()), Mc.M.c(Mc.T.let())), Mc.M.ev.let(), B.e4())

def B.e2() -> Cr.Cir.Stmt:
  Mc.M.if(Mc.M.eq(Mc.M.g(Mc.R.tag()), Mc.M.c(Mc.T.ann())), Mc.M.ev.ann(), B.e3())

def B.e1() -> Cr.Cir.Stmt:
  Mc.M.if(Mc.M.eq(Mc.M.g(Mc.R.tag()), Mc.M.c(Mc.T.ref())), Mc.M.ev.ref(), B.e2())

def B.else() -> Cr.Cir.Stmt:
  Mc.M.if(Mc.M.eq(Mc.M.g(Mc.R.tag()), Mc.M.c(Mc.T.app())), Mc.M.ev.app(), B.e1())

def B.ev2() -> Cr.Cir.Stmt:
  Mc.M.do([Mc.M.set(Mc.R.tag(), Mc.M.tag(Mc.M.g(Mc.R.c()))), Mc.M.if(B.cond2(), Mc.M.set(Mc.R.mode(), Mc.M.c(1)), B.else())])

def B.ev3() -> Cr.Cir.Stmt:
  Mc.M.do([Mc.M.if(B.cond2(), Mc.M.set(Mc.R.mode(), Mc.M.c(1)), B.else())])

# M.ev's first two statements, from a state of mode 0: c and tag get the
# focus' cell and its tag
def ev.st1(+foc: U32, +sp: U32, +pend: U32, +r4: U32, +r5: U32, +r6: U32, +r7: U32, +r8: U32, +r9: U32, +r10: U32, +r11: U32, +r12: U32, +r13: U32, +r14: U32, +r15: U32, +r16: U32, +r17: U32, +r18: U32, +r19: U32, +r20: U32, +r21: U32, +r22: U32, +r23: U32, +r24: U32, +r25: U32, +r26: U32, +r27: U32, +r28: U32, +r29: U32, +r30: U32, +r31: U32, +r32: U32, +r33: U32, +r34: U32, +r35: U32, +r36: U32, +r37: U32, +r38: U32, +r39: U32, +r40: U32, +r41: U32, +r42: U32, +r43: U32, +r44: U32, +r45: U32, +r46: U32, +r47: U32, +r48: U32, +r49: U32, +r50: U32, +r51: U32, +r52: U32, +r53: U32, +r54: U32, +r55: U32, +r56: U32, +r57: U32, +r58: U32, +r59: U32, +r60: U32, +r61: U32, +r62: U32, +m: Cr.Cir.Cells, +nx: U32, +fi: U32,
  +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>) -> Cr.Cir.State:
  D.St.set(D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), 8n, foc)

def ev.st2(+foc: U32, +sp: U32, +pend: U32, +r4: U32, +r5: U32, +r6: U32, +r7: U32, +r8: U32, +r9: U32, +r10: U32, +r11: U32, +r12: U32, +r13: U32, +r14: U32, +r15: U32, +r16: U32, +r17: U32, +r18: U32, +r19: U32, +r20: U32, +r21: U32, +r22: U32, +r23: U32, +r24: U32, +r25: U32, +r26: U32, +r27: U32, +r28: U32, +r29: U32, +r30: U32, +r31: U32, +r32: U32, +r33: U32, +r34: U32, +r35: U32, +r36: U32, +r37: U32, +r38: U32, +r39: U32, +r40: U32, +r41: U32, +r42: U32, +r43: U32, +r44: U32, +r45: U32, +r46: U32, +r47: U32, +r48: U32, +r49: U32, +r50: U32, +r51: U32, +r52: U32, +r53: U32, +r54: U32, +r55: U32, +r56: U32, +r57: U32, +r58: U32, +r59: U32, +r60: U32, +r61: U32, +r62: U32, +m: Cr.Cir.Cells, +nx: U32, +fi: U32,
  +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>) -> Cr.Cir.State:
  D.St.set(ev.st1(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp), 10n, D.TgW(D.Fd(0n, m, foc)))

# a round from mode 0 whose focus' cell c is flagged VALUE: c and tag are
# set, then the mode is 1
def ev.val.E(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32,
  +pend: U32, +r4: U32, +r5: U32, +r6: U32, +r7: U32, +r8: U32, +r9: U32, +r10: U32, +r11: U32, +r12: U32, +r13: U32, +r14: U32, +r15: U32, +r16: U32, +r17: U32, +r18: U32, +r19: U32, +r20: U32, +r21: U32, +r22: U32, +r23: U32, +r24: U32, +r25: U32, +r26: U32, +r27: U32, +r28: U32, +r29: U32, +r30: U32, +r31: U32, +r32: U32, +r33: U32, +r34: U32, +r35: U32, +r36: U32, +r37: U32, +r38: U32, +r39: U32, +r40: U32, +r41: U32, +r42: U32, +r43: U32, +r44: U32, +r45: U32, +r46: U32, +r47: U32, +r48: U32, +r49: U32, +r50: U32, +r51: U32, +r52: U32, +r53: U32, +r54: U32, +r55: U32, +r56: U32, +r57: U32, +r58: U32, +r59: U32, +r60: U32, +r61: U32, +r62: U32, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32,
  +inp: List<&2, Word(8n)>, +focus: Bk.Term,
  +nd: D.Nd(ds, im, fi, nx, foc, Cr.Cir.Cells.get(m, foc), focus, D.A.tag(focus)),
  +tb: D.Tbl(m, im, fi, nx), +nz2: {U32.is_zero(U32.or(Bool.to_u32(U32.is_ne(U32.and(D.Fd(0n, m, foc), 256), 0)), Bool.to_u32(U32.is_ne(Cr.Cir.Cell.get(4n, Cr.Cir.Cells.get(m, U32.add(272, U32.and(D.Fd(0n, m, foc), 63)))), 0)))) == False{} : Bool}) ->
  {Cr.Cir.exec(f, D.B.body(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)) ==
    Cr.Cir.Out.next{D.St.set(ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp), 1n, 1)} : Cr.Cir.Out}:
  match nd:
    case Tuple{+valid, Tuple{_, Tuple{+etag, _}}}:
      +st1 = ev.st1(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)
      +st2 = ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)
      +st3 = D.St.set(st2, 1n, 1)
      +f0 = D.Fd(0n, m, foc)
      +ef1 = D.ev.fld(0n, Mc.M.g(Mc.R.c()), D.St.regs(st1), m, nx, fi, im, pg, lim, inp, Nil{}, 0, foc, {==}, valid)
      +ef2 = D.ev.fld(0n, Mc.M.g(Mc.R.c()), D.St.regs(st2), m, nx, fi, im, pg, lim, inp, Nil{}, 0, foc, {==}, valid)
      +etg = D.ev.op(Wa.Wasm.Op.and{}, Mc.M.f(0n, Mc.M.g(Mc.R.c())), Mc.M.c(63), st1, f0, 63, ef1, {==})
      +etg2 = D.ev.op(Wa.Wasm.Op.and{}, Mc.M.f(0n, Mc.M.g(Mc.R.c())), Mc.M.c(63), st2, f0, 63, ef2, {==})
      +efl = D.ev.op(Wa.Wasm.Op.ne{}, Mc.M.and(Mc.M.f(0n, Mc.M.g(Mc.R.c())), Mc.M.c(256)), Mc.M.c(0), st2, Wa.Wasm.op(Wa.Wasm.Op.and{}, f0, 256), 0,
        D.ev.op(Wa.Wasm.Op.and{}, Mc.M.f(0n, Mc.M.g(Mc.R.c())), Mc.M.c(256), st2, f0, 256, ef2, {==}), {==})
      +addr = Wa.Wasm.op(Wa.Wasm.Op.add{}, 272, Wa.Wasm.op(Wa.Wasm.Op.and{}, f0, 63))
      +eadr = D.ev.op(Wa.Wasm.Op.add{}, Mc.M.c(272), Mc.M.tag(Mc.M.g(Mc.R.c())), st2, 272, Wa.Wasm.op(Wa.Wasm.Op.and{}, f0, 63), {==}, etg2)
      +vt = vt.of(m, im, fi, nx, f0, focus, etag, tb)
      +e4 = Cr.Cir.Cell.get(4n, Cr.Cir.Cells.get(m, addr))
      +ee4 = D.ev.fld(4n, Mc.M.add(Mc.M.c(272), Mc.M.tag(Mc.M.g(Mc.R.c()))), D.St.regs(st2), m, nx, fi, im, pg, lim, inp, Nil{}, 0, addr, eadr, vt)
      +ene = D.ev.op(Wa.Wasm.Op.ne{}, Mc.M.entry(4n, Mc.M.g(Mc.R.c())), Mc.M.c(0), st2, e4, 0, ee4, {==})
      +flv = Wa.Wasm.op(Wa.Wasm.Op.ne{}, Wa.Wasm.op(Wa.Wasm.Op.and{}, f0, 256), 0)
      +nev = Wa.Wasm.op(Wa.Wasm.Op.ne{}, e4, 0)
      +ec2 = D.ev.op(Wa.Wasm.Op.or{}, Mc.M.flag(Mc.M.g(Mc.R.c()), Mc.F.value()), Mc.M.ne(Mc.M.entry(4n, Mc.M.g(Mc.R.c())), Mc.M.c(0)), st2, flv, nev, efl, ene)
      +e3a = Equal.trans(Cr.Cir.Out, Cr.Cir.exec(f, Cr.Cir.Stmt.if{B.cond2(), Mc.M.set(Mc.R.mode(), Mc.M.c(1)), B.else()}, st2),
        Cr.Cir.exec(f, Mc.M.set(Mc.R.mode(), Mc.M.c(1)), st2), Cr.Cir.Out.next{st3},
        D.eq.if.t(f, B.cond2(), Mc.M.set(Mc.R.mode(), Mc.M.c(1)), B.else(), st2, Wa.Wasm.op(Wa.Wasm.Op.or{}, flv, nev), ec2, nz2),
        D.eq.set(f, 1n, Mc.M.c(1), st2, 1, {==}, {==}))
      %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, D.B.body(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(f, Mc.M.ev(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)),
        D.eq.if.t(f, Mc.M.eq(Mc.M.g(Mc.R.mode()), Mc.M.c(0)), Mc.M.ev(), Mc.M.ret(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), 1, {==}, {==})) :
        {_ == Cr.Cir.Out.next{st3} : Cr.Cir.Out}
      %D.rw.seq(f, Mc.M.set(Mc.R.c(), Mc.M.g(Mc.R.focus())), B.ev2(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), st1,
        D.eq.set(f, 8n, Mc.M.g(Mc.R.focus()), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), foc, {==}, {==})) : {_ == Cr.Cir.Out.next{st3} : Cr.Cir.Out}
      %D.rw.seq(f, Mc.M.set(Mc.R.tag(), Mc.M.tag(Mc.M.g(Mc.R.c()))), B.ev3(), st1, st2,
        D.eq.set(f, 10n, Mc.M.tag(Mc.M.g(Mc.R.c())), st1, D.TgW(f0), etg, {==})) : {_ == Cr.Cir.Out.next{st3} : Cr.Cir.Out}
      %D.rw.seq(f, Cr.Cir.Stmt.if{B.cond2(), Mc.M.set(Mc.R.mode(), Mc.M.c(1)), B.else()}, Cr.Cir.Stmt.nop{}, st2, st3, e3a) :
        {_ == Cr.Cir.Out.next{st3} : Cr.Cir.Out}
      %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, Cr.Cir.Stmt.nop{}, st3), Cr.Cir.Out.next{st3}, D.eq.nop(f, st3)) :
        {_ == Cr.Cir.Out.next{st3} : Cr.Cir.Out}
      {==}

# the table of the image
def img.tbl(-ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -m: Cr.Cir.Cells, -im: U32,
  -fi: U32, -nx: U32, io: D.ImgOK(ds, ks, img, m, im, fi, nx)) -> D.Tbl(m, im, fi, nx):
  match io:
    case Tuple{tb, _}:
      tb

# a cell flagged VALUE stands for a value
def nd.val(-ds: List<&2, Bk.Def>, -im: U32, -fi: U32, -nx: U32, -c: U32, -x: Cr.Cir.Cell, -t: Bk.Term, -tag: U32,
  nd: D.Nd(ds, im, fi, nx, c, x, t, tag), hv: {D.FlW(Cr.Cir.Cell.get(0n, x), 256) == True{} : Bool}) ->
  {Bool.or(Bool.not(True{}), El.Eval.vals(ds, t, False{})) == True{} : Bool}:
  match nd:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{nv, _}}}}:
      %hv : {Bool.or(Bool.not(_), El.Eval.vals(ds, t, False{})) == True{} : Bool}
      nv

# mode 1 costs less than mode 0 by the focus' measure
def ret.lt(+focus: Bk.Term, +fs: List<&2, D.AF>, -w: Nat, ew: {D.A.w(False{}, focus, fs) == w : Nat}) ->
  N.Le(1n+D.A.w(True{}, focus, fs), w):
  %ew : N.Le(1n+D.A.w(True{}, focus, fs), _)
  N.add_mono(1n, D.A.w3(focus), D.A.w.frames(fs), D.A.w.frames(fs), D.A.w3.pos(focus), N.le_refl(D.A.w.frames(fs)))

def ev.val.mv(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32,
  +pend: U32, +r4: U32, +r5: U32, +r6: U32, +r7: U32, +r8: U32, +r9: U32, +r10: U32, +r11: U32, +r12: U32, +r13: U32, +r14: U32, +r15: U32, +r16: U32, +r17: U32, +r18: U32, +r19: U32, +r20: U32, +r21: U32, +r22: U32, +r23: U32, +r24: U32, +r25: U32, +r26: U32, +r27: U32, +r28: U32, +r29: U32, +r30: U32, +r31: U32, +r32: U32, +r33: U32, +r34: U32, +r35: U32, +r36: U32, +r37: U32, +r38: U32, +r39: U32, +r40: U32, +r41: U32, +r42: U32, +r43: U32, +r44: U32, +r45: U32, +r46: U32, +r47: U32, +r48: U32, +r49: U32, +r50: U32, +r51: U32, +r52: U32, +r53: U32, +r54: U32, +r55: U32, +r56: U32, +r57: U32, +r58: U32, +r59: U32, +r60: U32, +r61: U32, +r62: U32, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32,
  +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +focus: Bk.Term,
  +et: {D.A.plugs(fs, focus) == t : Bk.Term}, ew: {D.A.w(False{}, focus, fs) == w : Nat}, +afs: D.AFs.ok(ds, fs),
  +isf: D.Is(ds, m, im, fi, nx, ks, img, foc, focus), +frs: D.Frs(ds, m, im, fi, nx, ks, img, ps, sp, fs),
  +hp: D.Heap(m, nx, fi, im, [foc], pend, ps), +io: D.ImgOK(ds, ks, img, m, im, fi, nx),
  +nz2: {U32.is_zero(U32.or(Bool.to_u32(U32.is_ne(U32.and(D.Fd(0n, m, foc), 256), 0)), Bool.to_u32(U32.is_ne(Cr.Cir.Cell.get(4n, Cr.Cir.Cells.get(m, U32.add(272, U32.and(D.Fd(0n, m, foc), 63)))), 0)))) == False{} : Bool},
  +evv: {Bool.or(Bool.not(True{}), El.Eval.vals(ds, focus, False{})) == True{} : Bool}) ->
  MV(ds, ks, img, D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), t, w):
  +nd = D.is.nd(ds, m, im, fi, nx, ks, img, foc, focus, isf)
  +tb = img.tbl(ds, ks, img, m, im, fi, nx, io)
  +w2 = D.A.w(True{}, focus, fs)
  +inv3 = {(D.Wit{True{}, focus, fs, foc, sp, pend, ps, D.R59.of(D.St.regs(D.St.set(ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp), 1n, 1)))},
    (et, ({==}, (evv,
    (afs, ({==}, (isf, (frs, (hp, (io, ({==}, {==}))))))))))) : D.Inv(ds, ks, img, D.St.set(ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp), 1n, 1), t, w2)}
  +lt = ret.lt(focus, fs, w, ew)
  (f => (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, D.B.body(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)), Cr.Cir.Out.next{D.St.set(ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp), 1n, 1)},
      ev.val.E(f, ds, ks, img, foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp, focus, nd, tb, nz2)) :
      D.Post(False{}, _, s => D.Rnd(ds, ks, img, t, w, s), s => st2 => D.HR(ds, t, s, st2));
      Inl{(w2, (inv3, lt))}),
   (0n, (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec(0n, D.B.body(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)), Cr.Cir.Out.next{D.St.set(ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp), 1n, 1)},
      ev.val.E(0n, ds, ks, img, foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp, focus, nd, tb, nz2)) : D.Ends(_);
      Unit{})))

# the tests of M.ev on a cell of the tag 0: none takes it, a halt with 2
def B.chain0(+f: Nat, +st: Cr.Cir.State, +f0: U32,
  +etag: {D.TgW(f0) == 0 : U32}, +er: {Cr.Cir.eval(Mc.M.g(Mc.R.tag()), st) == Some{D.TgW(f0)} : Maybe<&2, U32>}) ->
  {Cr.Cir.exec(f, B.else(), st) == Cr.Cir.Out.halt{2, st} : Cr.Cir.Out}:
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, B.else(), st), Cr.Cir.exec(f, B.e1(), st),
    D.eq.if.e(f, Mc.M.eq(Mc.M.g(Mc.R.tag()), Mc.M.c(8)), Mc.M.ev.app(), B.e1(), st, Wa.Wasm.op(Wa.Wasm.Op.eq{}, D.TgW(f0), 8),
      D.ev.op(Wa.Wasm.Op.eq{}, Mc.M.g(Mc.R.tag()), Mc.M.c(8), st, D.TgW(f0), 8, er, {==}), tag.ne(f0, 0, 8, etag, {==}))) :
    {_ == Cr.Cir.Out.halt{2, st} : Cr.Cir.Out}
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, B.e1(), st), Cr.Cir.exec(f, B.e2(), st),
    D.eq.if.e(f, Mc.M.eq(Mc.M.g(Mc.R.tag()), Mc.M.c(1)), Mc.M.ev.ref(), B.e2(), st, Wa.Wasm.op(Wa.Wasm.Op.eq{}, D.TgW(f0), 1),
      D.ev.op(Wa.Wasm.Op.eq{}, Mc.M.g(Mc.R.tag()), Mc.M.c(1), st, D.TgW(f0), 1, er, {==}), tag.ne(f0, 0, 1, etag, {==}))) :
    {_ == Cr.Cir.Out.halt{2, st} : Cr.Cir.Out}
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, B.e2(), st), Cr.Cir.exec(f, B.e3(), st),
    D.eq.if.e(f, Mc.M.eq(Mc.M.g(Mc.R.tag()), Mc.M.c(2)), Mc.M.ev.ann(), B.e3(), st, Wa.Wasm.op(Wa.Wasm.Op.eq{}, D.TgW(f0), 2),
      D.ev.op(Wa.Wasm.Op.eq{}, Mc.M.g(Mc.R.tag()), Mc.M.c(2), st, D.TgW(f0), 2, er, {==}), tag.ne(f0, 0, 2, etag, {==}))) :
    {_ == Cr.Cir.Out.halt{2, st} : Cr.Cir.Out}
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, B.e3(), st), Cr.Cir.exec(f, B.e4(), st),
    D.eq.if.e(f, Mc.M.eq(Mc.M.g(Mc.R.tag()), Mc.M.c(3)), Mc.M.ev.let(), B.e4(), st, Wa.Wasm.op(Wa.Wasm.Op.eq{}, D.TgW(f0), 3),
      D.ev.op(Wa.Wasm.Op.eq{}, Mc.M.g(Mc.R.tag()), Mc.M.c(3), st, D.TgW(f0), 3, er, {==}), tag.ne(f0, 0, 3, etag, {==}))) :
    {_ == Cr.Cir.Out.halt{2, st} : Cr.Cir.Out}
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, B.e4(), st), Cr.Cir.exec(f, B.e5(), st),
    D.eq.if.e(f, Mc.M.eq(Mc.M.g(Mc.R.tag()), Mc.M.c(10)), Mc.M.ev.tup(), B.e5(), st, Wa.Wasm.op(Wa.Wasm.Op.eq{}, D.TgW(f0), 10),
      D.ev.op(Wa.Wasm.Op.eq{}, Mc.M.g(Mc.R.tag()), Mc.M.c(10), st, D.TgW(f0), 10, er, {==}), tag.ne(f0, 0, 10, etag, {==}))) :
    {_ == Cr.Cir.Out.halt{2, st} : Cr.Cir.Out}
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, B.e5(), st), Cr.Cir.exec(f, B.e6(), st),
    D.eq.if.e(f, Mc.M.eq(Mc.M.g(Mc.R.tag()), Mc.M.c(18)), Mc.M.ev.rwt(), B.e6(), st, Wa.Wasm.op(Wa.Wasm.Op.eq{}, D.TgW(f0), 18),
      D.ev.op(Wa.Wasm.Op.eq{}, Mc.M.g(Mc.R.tag()), Mc.M.c(18), st, D.TgW(f0), 18, er, {==}), tag.ne(f0, 0, 18, etag, {==}))) :
    {_ == Cr.Cir.Out.halt{2, st} : Cr.Cir.Out}
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, B.e6(), st), Cr.Cir.exec(f, Mc.M.halt(2), st),
    D.eq.if.e(f, Mc.M.eq(Mc.M.g(Mc.R.tag()), Mc.M.c(5)), Mc.M.ev.min(), Mc.M.halt(2), st, Wa.Wasm.op(Wa.Wasm.Op.eq{}, D.TgW(f0), 5),
      D.ev.op(Wa.Wasm.Op.eq{}, Mc.M.g(Mc.R.tag()), Mc.M.c(5), st, D.TgW(f0), 5, er, {==}), tag.ne(f0, 0, 5, etag, {==}))) :
    {_ == Cr.Cir.Out.halt{2, st} : Cr.Cir.Out}
  eq.halt(f, 2, st)

# a round from mode 0 whose focus' cell is a variable: no case of M.ev takes
# it, a halt with 2
def ev.var.E(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32,
  +pend: U32, +r4: U32, +r5: U32, +r6: U32, +r7: U32, +r8: U32, +r9: U32, +r10: U32, +r11: U32, +r12: U32, +r13: U32, +r14: U32, +r15: U32, +r16: U32, +r17: U32, +r18: U32, +r19: U32, +r20: U32, +r21: U32, +r22: U32, +r23: U32, +r24: U32, +r25: U32, +r26: U32, +r27: U32, +r28: U32, +r29: U32, +r30: U32, +r31: U32, +r32: U32, +r33: U32, +r34: U32, +r35: U32, +r36: U32, +r37: U32, +r38: U32, +r39: U32, +r40: U32, +r41: U32, +r42: U32, +r43: U32, +r44: U32, +r45: U32, +r46: U32, +r47: U32, +r48: U32, +r49: U32, +r50: U32, +r51: U32, +r52: U32, +r53: U32, +r54: U32, +r55: U32, +r56: U32, +r57: U32, +r58: U32, +r59: U32, +r60: U32, +r61: U32, +r62: U32, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32,
  +inp: List<&2, Word(8n)>, +i: Nat,
  +nd: D.Nd(ds, im, fi, nx, foc, Cr.Cir.Cells.get(m, foc), Bk.Term.Var{i}, 0),
  +tb: D.Tbl(m, im, fi, nx), +hv: {D.Fl(m, foc, 256) == False{} : Bool}) ->
  {Cr.Cir.exec(f, D.B.body(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)) == Cr.Cir.Out.halt{2, ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)} : Cr.Cir.Out}:
  match nd:
    case Tuple{+valid, Tuple{_, Tuple{+etag, _}}}:
      +st1 = ev.st1(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)
      +st2 = ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)
      +f0 = D.Fd(0n, m, foc)
      +ef1 = D.ev.fld(0n, Mc.M.g(Mc.R.c()), D.St.regs(st1), m, nx, fi, im, pg, lim, inp, Nil{}, 0, foc, {==}, valid)
      +ef2 = D.ev.fld(0n, Mc.M.g(Mc.R.c()), D.St.regs(st2), m, nx, fi, im, pg, lim, inp, Nil{}, 0, foc, {==}, valid)
      +etg = D.ev.op(Wa.Wasm.Op.and{}, Mc.M.f(0n, Mc.M.g(Mc.R.c())), Mc.M.c(63), st1, f0, 63, ef1, {==})
      +etg2 = D.ev.op(Wa.Wasm.Op.and{}, Mc.M.f(0n, Mc.M.g(Mc.R.c())), Mc.M.c(63), st2, f0, 63, ef2, {==})
      +efl = D.ev.op(Wa.Wasm.Op.ne{}, Mc.M.and(Mc.M.f(0n, Mc.M.g(Mc.R.c())), Mc.M.c(256)), Mc.M.c(0), st2, Wa.Wasm.op(Wa.Wasm.Op.and{}, f0, 256), 0,
        D.ev.op(Wa.Wasm.Op.and{}, Mc.M.f(0n, Mc.M.g(Mc.R.c())), Mc.M.c(256), st2, f0, 256, ef2, {==}), {==})
      +addr = Wa.Wasm.op(Wa.Wasm.Op.add{}, 272, Wa.Wasm.op(Wa.Wasm.Op.and{}, f0, 63))
      +eadr = D.ev.op(Wa.Wasm.Op.add{}, Mc.M.c(272), Mc.M.tag(Mc.M.g(Mc.R.c())), st2, 272, Wa.Wasm.op(Wa.Wasm.Op.and{}, f0, 63), {==}, etg2)
      +vt = vt.of(m, im, fi, nx, f0, Bk.Term.Var{i}, etag, tb)
      +e4 = Cr.Cir.Cell.get(4n, Cr.Cir.Cells.get(m, addr))
      +ee4 = D.ev.fld(4n, Mc.M.add(Mc.M.c(272), Mc.M.tag(Mc.M.g(Mc.R.c()))), D.St.regs(st2), m, nx, fi, im, pg, lim, inp, Nil{}, 0, addr, eadr, vt)
      +ene = D.ev.op(Wa.Wasm.Op.ne{}, Mc.M.entry(4n, Mc.M.g(Mc.R.c())), Mc.M.c(0), st2, e4, 0, ee4, {==})
      +flv = Wa.Wasm.op(Wa.Wasm.Op.ne{}, Wa.Wasm.op(Wa.Wasm.Op.and{}, f0, 256), 0)
      +nev = Wa.Wasm.op(Wa.Wasm.Op.ne{}, e4, 0)
      +ec2 = D.ev.op(Wa.Wasm.Op.or{}, Mc.M.flag(Mc.M.g(Mc.R.c()), Mc.F.value()), Mc.M.ne(Mc.M.entry(4n, Mc.M.g(Mc.R.c())), Mc.M.c(0)), st2, flv, nev, efl, ene)
      +z2 = z.of(m, im, fi, nx, f0, Bk.Term.Var{i}, etag, tb, hv, {==})
      +e3a = Equal.trans(Cr.Cir.Out, Cr.Cir.exec(f, Cr.Cir.Stmt.if{B.cond2(), Mc.M.set(Mc.R.mode(), Mc.M.c(1)), B.else()}, st2),
        Cr.Cir.exec(f, B.else(), st2), Cr.Cir.Out.halt{2, st2},
        D.eq.if.e(f, B.cond2(), Mc.M.set(Mc.R.mode(), Mc.M.c(1)), B.else(), st2, Wa.Wasm.op(Wa.Wasm.Op.or{}, flv, nev), ec2, z2),
        B.chain0(f, st2, f0, etag, {==}))
      %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, D.B.body(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(f, Mc.M.ev(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)),
        D.eq.if.t(f, Mc.M.eq(Mc.M.g(Mc.R.mode()), Mc.M.c(0)), Mc.M.ev(), Mc.M.ret(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), 1, {==}, {==})) :
        {_ == Cr.Cir.Out.halt{2, st2} : Cr.Cir.Out}
      %D.rw.seq(f, Mc.M.set(Mc.R.c(), Mc.M.g(Mc.R.focus())), B.ev2(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), st1,
        D.eq.set(f, 8n, Mc.M.g(Mc.R.focus()), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), foc, {==}, {==})) : {_ == Cr.Cir.Out.halt{2, st2} : Cr.Cir.Out}
      %D.rw.seq(f, Mc.M.set(Mc.R.tag(), Mc.M.tag(Mc.M.g(Mc.R.c()))), B.ev3(), st1, st2,
        D.eq.set(f, 10n, Mc.M.tag(Mc.M.g(Mc.R.c())), st1, D.TgW(f0), etg, {==})) : {_ == Cr.Cir.Out.halt{2, st2} : Cr.Cir.Out}
      eq.seq.h(f, Cr.Cir.Stmt.if{B.cond2(), Mc.M.set(Mc.R.mode(), Mc.M.c(1)), B.else()}, Cr.Cir.Stmt.nop{}, st2, 2, st2, e3a)

# the parts of an if, to name the parts of a statement of impl.bend without
# copying them
def stmt.cond(x: Cr.Cir.Stmt) -> Cr.Cir.Expr:
  match x:
    case Cr.Cir.Stmt.if{c, _, _}:
      c
    case _:
      Cr.Cir.Expr.const{0}

def stmt.then(x: Cr.Cir.Stmt) -> Cr.Cir.Stmt:
  match x:
    case Cr.Cir.Stmt.if{_, t, _}:
      t
    case _:
      Cr.Cir.Stmt.nop{}

def stmt.else(x: Cr.Cir.Stmt) -> Cr.Cir.Stmt:
  match x:
    case Cr.Cir.Stmt.if{_, _, e}:
      e
    case _:
      Cr.Cir.Stmt.nop{}

# a weaker outcome
def post.map(dn: Bool, o: Cr.Cir.Out, -Q1: Cr.Cir.State -> Type, -Q2: Cr.Cir.State -> Type, -H1: U32 -> Cr.Cir.State -> Type,
  -H2: U32 -> Cr.Cir.State -> Type, h: D.Post(dn, o, Q1, H1), q: @st: Cr.Cir.State -> Q1(st) -> Q2(st),
  hh: @s: U32 -> @st: Cr.Cir.State -> H1(s, st) -> H2(s, st)) -> D.Post(dn, o, Q2, H2):
  match o:
    case Cr.Cir.Out.next{st}:
      q(st, h)
    case Cr.Cir.Out.halt{s, st}:
      hh(s, st, h)
    case Cr.Cir.Out.out_of_memory{}:
      Unit{}
    case Cr.Cir.Out.trap{}:
      h
    case Cr.Cir.Out.not_done{}:
      h

# the result of a value is its bytes
def res.val(+ds: List<&2, Bk.Def>, +v: Bk.Term, -x: Maybe<&2, List<&2, Word(8n)>>, ev: {El.Eval.vals(ds, v, False{}) == True{} : Bool},
  eu: {Pg.Program.unbytes(v) == x : Maybe<&2, List<&2, Word(8n)>>}) -> {Pg.Program.result(ds, Some{v}) == x : Maybe<&2, List<&2, Word(8n)>>}:
  %Equal.sym(Bool, El.Eval.vals(ds, v, False{}), True{}, ev) : {Pg.Program.result.if(_, v) == x : Maybe<&2, List<&2, Word(8n)>>}
  eu

# M.out's halts are a round's, from its value v
def out.hr(+ds: List<&2, Bk.Def>, +v: Bk.Term, +ev: {El.Eval.vals(ds, v, False{}) == True{} : Bool}, -s: U32, -st2: Cr.Cir.State,
  h: D.OutH(v, s, st2)) -> D.HR(ds, v, s, st2):
  match h:
    case Inl{x}:
      (e0, eu) = x
      Inl{(e0, (ev.stops(ds, v, ev), res.val(ds, v, Some{List.reverse(&2, Word(8n), D.St.out(st2))}, ev, eu)))}
    case Inr{x}:
      (e2, eu) = x
      Inr{(e2, (ev.stops(ds, v, ev), res.val(ds, v, None{}, ev, eu)))}

# a round from mode 1 with no frame is M.out
def out.E(+f: Nat, +foc: U32, +pend: U32, +r4: U32, +r5: U32, +r6: U32, +r7: U32, +r8: U32, +r9: U32, +r10: U32, +r11: U32, +r12: U32, +r13: U32, +r14: U32, +r15: U32, +r16: U32, +r17: U32, +r18: U32, +r19: U32, +r20: U32, +r21: U32, +r22: U32, +r23: U32, +r24: U32, +r25: U32, +r26: U32, +r27: U32, +r28: U32, +r29: U32, +r30: U32, +r31: U32, +r32: U32, +r33: U32, +r34: U32, +r35: U32, +r36: U32, +r37: U32, +r38: U32, +r39: U32, +r40: U32, +r41: U32, +r42: U32, +r43: U32, +r44: U32, +r45: U32, +r46: U32, +r47: U32, +r48: U32, +r49: U32, +r50: U32, +r51: U32, +r52: U32, +r53: U32, +r54: U32, +r55: U32, +r56: U32, +r57: U32, +r58: U32, +r59: U32, +r60: U32, +r61: U32, +r62: U32, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32,
  +inp: List<&2, Word(8n)>) -> {Cr.Cir.exec(f, D.B.body(), D.S(foc, 1, 0, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)) == Cr.Cir.exec(f, Mc.M.out(), D.S(foc, 1, 0, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)) : Cr.Cir.Out}:
  Equal.trans(Cr.Cir.Out, Cr.Cir.exec(f, D.B.body(), D.S(foc, 1, 0, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(f, Mc.M.ret(), D.S(foc, 1, 0, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(f, Mc.M.out(), D.S(foc, 1, 0, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)),
    D.eq.if.e(f, Mc.M.eq(Mc.M.g(Mc.R.mode()), Mc.M.c(0)), Mc.M.ev(), Mc.M.ret(), D.S(foc, 1, 0, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), 0, {==}, {==}),
    D.eq.if.t(f, stmt.cond(Mc.M.ret()), stmt.then(Mc.M.ret()), stmt.else(Mc.M.ret()), D.S(foc, 1, 0, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), 1, {==}, {==}))

def out.mv(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +pend: U32,
  +r4: U32, +r5: U32, +r6: U32, +r7: U32, +r8: U32, +r9: U32, +r10: U32, +r11: U32, +r12: U32, +r13: U32, +r14: U32, +r15: U32, +r16: U32, +r17: U32, +r18: U32, +r19: U32, +r20: U32, +r21: U32, +r22: U32, +r23: U32, +r24: U32, +r25: U32, +r26: U32, +r27: U32, +r28: U32, +r29: U32, +r30: U32, +r31: U32, +r32: U32, +r33: U32, +r34: U32, +r35: U32, +r36: U32, +r37: U32, +r38: U32, +r39: U32, +r40: U32, +r41: U32, +r42: U32, +r43: U32, +r44: U32, +r45: U32, +r46: U32, +r47: U32, +r48: U32, +r49: U32, +r50: U32, +r51: U32, +r52: U32, +r53: U32, +r54: U32, +r55: U32, +r56: U32, +r57: U32, +r58: U32, +r59: U32, +r60: U32, +r61: U32, +r62: U32, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>,
  +t: Bk.Term, +w: Nat, +focus: Bk.Term, +et: {focus == t : Bk.Term},
  +ev: {El.Eval.vals(ds, focus, False{}) == True{} : Bool}, +isf: D.Is(ds, m, im, fi, nx, ks, img, foc, focus),
  +ks2: List<&2, List<&2, Word(8n)>>, +hk: {ks == Mc.Img.known(ks2) : List<&2, List<&2, Word(8n)>>}) ->
  MV(ds, ks, img, D.S(foc, 1, 0, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), t, w):
  +od = out.done(ds, ks, img, foc, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp, focus, ks2, isf, hk)
  +f1 = D.Ex.fst(Nat, f => D.Ends(Cr.Cir.exec(f, Mc.M.out(), D.S(foc, 1, 0, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp))), od)
  (+f => (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, D.B.body(), D.S(foc, 1, 0, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(f, Mc.M.out(), D.S(foc, 1, 0, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)),
      out.E(f, foc, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)) :
      D.Post(False{}, _, s => D.Rnd(ds, ks, img, t, w, s), s => st2 => D.HR(ds, t, s, st2));
      post.map(False{}, Cr.Cir.exec(f, Mc.M.out(), D.S(foc, 1, 0, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)), st => Empty, s => D.Rnd(ds, ks, img, t, w, s),
        s => st2 => D.OutH(focus, s, st2), s => st2 => D.HR(ds, t, s, st2),
        out.post(f, ds, ks, img, foc, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp, focus, ks2, isf, hk),
        st => h => Empty.absurd(D.Rnd(ds, ks, img, t, w, st), h),
        s => st2 => h => hr.eq(ds, focus, t, s, st2, et, out.hr(ds, focus, ev, s, st2, h)))),
   (f1, (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f1, D.B.body(), D.S(foc, 1, 0, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(f1, Mc.M.out(), D.S(foc, 1, 0, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)),
      out.E(f1, foc, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)) : D.Ends(_);
      D.Ex.snd(Nat, f => D.Ends(Cr.Cir.exec(f, Mc.M.out(), D.S(foc, 1, 0, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp))), od))))

# the image's names, the machine's first
def img.ks(-ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -m: Cr.Cir.Cells, -im: U32,
  -fi: U32, -nx: U32, io: D.ImgOK(ds, ks, img, m, im, fi, nx)) -> D.Ex(List<&2, List<&2, Word(8n)>>, ks2 => {ks == Mc.Img.known(ks2) : List<&2, List<&2, Word(8n)>>}):
  match io:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{k, _}}}}}}:
      k

# The moves, one lemma each (open where the body is ?TODO)

# mode 0, a focus flagged VALUE: a value, mode 1; an admin move
def mv.ev.val(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +focus: Bk.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, False{}, focus, fs, ps), +hv: {D.Fl(m, foc, 256) == True{} : Bool}) ->
  MV(ds, ks, img, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  match rest:
    case D.R59{+r4, +r5, +r6, +r7, +r8, +r9, +r10, +r11, +r12, +r13, +r14, +r15, +r16, +r17, +r18, +r19, +r20, +r21, +r22, +r23, +r24, +r25, +r26, +r27, +r28, +r29, +r30, +r31, +r32, +r33, +r34, +r35, +r36, +r37, +r38, +r39, +r40, +r41, +r42, +r43, +r44, +r45, +r46, +r47, +r48, +r49, +r50, +r51, +r52, +r53, +r54, +r55, +r56, +r57, +r58, +r59, +r60, +r61, +r62}:
      match iv:
        case Tuple{+et, Tuple{+ew, Tuple{_, Tuple{+afs, Tuple{_, Tuple{+isf, Tuple{+frs, Tuple{+hp, Tuple{+io, Tuple{_, _}}}}}}}}}}:
          +nd = D.is.nd(ds, m, im, fi, nx, ks, img, foc, focus, isf)
          ev.val.mv(ds, ks, img, foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, focus, et, ew, afs, isf, frs, hp,
            io, nz.of(D.Fd(0n, m, foc), Cr.Cir.Cell.get(4n, Cr.Cir.Cells.get(m, U32.add(272, U32.and(D.Fd(0n, m, foc), 63)))), hv),
            nd.val(ds, im, fi, nx, foc, Cr.Cir.Cells.get(m, foc), focus, D.A.tag(focus), nd, hv))

# mode 0, a focus that is a value by its form, as the table says (A.tbl): mode 1; an admin move
def mv.ev.former(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +focus: Bk.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, False{}, focus, fs, ps), +hf: {A.tbl(focus) == True{} : Bool}) ->
  MV(ds, ks, img, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  match rest:
    case D.R59{+r4, +r5, +r6, +r7, +r8, +r9, +r10, +r11, +r12, +r13, +r14, +r15, +r16, +r17, +r18, +r19, +r20, +r21, +r22, +r23, +r24, +r25, +r26, +r27, +r28, +r29, +r30, +r31, +r32, +r33, +r34, +r35, +r36, +r37, +r38, +r39, +r40, +r41, +r42, +r43, +r44, +r45, +r46, +r47, +r48, +r49, +r50, +r51, +r52, +r53, +r54, +r55, +r56, +r57, +r58, +r59, +r60, +r61, +r62}:
      match iv:
        case Tuple{+et, Tuple{+ew, Tuple{_, Tuple{+afs, Tuple{_, Tuple{+isf, Tuple{+frs, Tuple{+hp, Tuple{+io, Tuple{_, _}}}}}}}}}}:
          +nd = D.is.nd(ds, m, im, fi, nx, ks, img, foc, focus, isf)
          ev.val.mv(ds, ks, img, foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, focus, et, ew, afs, isf, frs, hp,
            io, nzf.go(ds, im, fi, nx, foc, m, focus, nd, img.tbl(ds, ks, img, m, im, fi, nx, io), hf), tbl.vals(ds, focus, hf))

# mode 0, a variable: free in the whole term, which has no step and is no value; halt 2
def mv.ev.var(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +i: Nat,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, False{}, Bk.Term.Var{i}, fs, ps), +hv: {D.Fl(m, foc, 256) == False{} : Bool}) ->
  MV(ds, ks, img, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  match rest:
    case D.R59{+r4, +r5, +r6, +r7, +r8, +r9, +r10, +r11, +r12, +r13, +r14, +r15, +r16, +r17, +r18, +r19, +r20, +r21, +r22, +r23, +r24, +r25, +r26, +r27, +r28, +r29, +r30, +r31, +r32, +r33, +r34, +r35, +r36, +r37, +r38, +r39, +r40, +r41, +r42, +r43, +r44, +r45, +r46, +r47, +r48, +r49, +r50, +r51, +r52, +r53, +r54, +r55, +r56, +r57, +r58, +r59, +r60, +r61, +r62}:
      match iv:
        case Tuple{+et, Tuple{_, Tuple{_, Tuple{+afs, Tuple{_, Tuple{+isf, Tuple{_, Tuple{_, Tuple{+io, Tuple{_, _}}}}}}}}}}:
          +nd = D.is.nd(ds, m, im, fi, nx, ks, img, foc, Bk.Term.Var{i}, isf)
          +tb = img.tbl(ds, ks, img, m, im, fi, nx, io)
          hr = hr.eq(ds, D.A.plugs(fs, Bk.Term.Var{i}), t, 2, ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp), et,
            hr.stuck(ds, D.A.plugs(fs, Bk.Term.Var{i}), ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp), ev.stuck(ds, fs, Bk.Term.Var{i}, afs, {==}, {==})))
          (f => (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, D.B.body(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)), Cr.Cir.Out.halt{2, ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)},
              ev.var.E(f, ds, ks, img, foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp, i, nd, tb, hv)) :
              D.Post(False{}, _, s => D.Rnd(ds, ks, img, t, w, s), s => st2 => D.HR(ds, t, s, st2));
              hr),
           (0n, (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec(0n, D.B.body(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)), Cr.Cir.Out.halt{2, ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)},
              ev.var.E(0n, ds, ks, img, foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp, i, nd, tb, hv)) : D.Ends(_);
              Unit{})))

# mode 0, Ref k: the call of k on no arguments (M.call, with M.walk and M.copy): a step to the copy of its leaf; or, when its case tree takes an argument, mode 1, an admin move; halt 2 when no walk exists
def mv.ev.ref(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +k: List<&2, Word(8n)>,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, False{}, Bk.Term.Ref{k}, fs, ps), +hv: {D.Fl(m, foc, 256) == False{} : Bool}) ->
  MV(ds, ks, img, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 0, Ann x y: x, a step
def mv.ev.ann(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +x: Bk.Term, +y: Bk.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, False{}, Bk.Term.Ann{x, y}, fs, ps), +hv: {D.Fl(m, foc, 256) == False{} : Bool}) ->
  MV(ds, ks, img, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 0, Let q v b with q live: v in the frame Let q □ b; an admin move
def mv.ev.let(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +q: Bk.Quan, +v: Bk.Term, +b: Bk.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, False{}, Bk.Term.Let{q, v, b}, fs, ps), +hv: {D.Fl(m, foc, 256) == False{} : Bool}, +hq: {El.Quan.live(q) == True{} : Bool}) ->
  MV(ds, ks, img, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 0, Let q v b with q dead: b with v put in (M.copy), a step
def mv.ev.unlet(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +q: Bk.Quan, +v: Bk.Term, +b: Bk.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, False{}, Bk.Term.Let{q, v, b}, fs, ps), +hv: {D.Fl(m, foc, 256) == False{} : Bool}, +hq: {El.Quan.live(q) == False{} : Bool}) ->
  MV(ds, ks, img, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 0, App q g x: g in the frame App q □ x; an admin move
def mv.ev.app(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +q: Bk.Quan, +g: Bk.Term, +x: Bk.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, False{}, Bk.Term.App{q, g, x}, fs, ps), +hv: {D.Fl(m, foc, 256) == False{} : Bool}) ->
  MV(ds, ks, img, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 0, Tup q a b with q live, not flagged VALUE: a in the frame Tup q □ b; an admin move
def mv.ev.tup(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +q: Bk.Quan, +a: Bk.Term, +b: Bk.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, False{}, Bk.Term.Tup{q, a, b}, fs, ps), +hv: {D.Fl(m, foc, 256) == False{} : Bool}, +hq: {El.Quan.live(q) == True{} : Bool}) ->
  MV(ds, ks, img, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 0, Tup q a b with q dead, not flagged VALUE: b in the frame Tup q a □; an admin move
def mv.ev.tup0(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +q: Bk.Quan, +a: Bk.Term, +b: Bk.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, False{}, Bk.Term.Tup{q, a, b}, fs, ps), +hv: {D.Fl(m, foc, 256) == False{} : Bool}, +hq: {El.Quan.live(q) == False{} : Bool}) ->
  MV(ds, ks, img, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 0, Rwt e p b: e in the frame Rwt □ p b; an admin move
def mv.ev.rwt(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +e: Bk.Term, +p: Bk.Term, +b: Bk.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, False{}, Bk.Term.Rwt{e, p, b}, fs, ps), +hv: {D.Fl(m, foc, 256) == False{} : Bool}) ->
  MV(ds, ks, img, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 0, Min a b: a in the frame Min □ b; an admin move
def mv.ev.min(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +a: Bk.Term, +b: Bk.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, False{}, Bk.Term.Min{a, b}, fs, ps), +hv: {D.Fl(m, foc, 256) == False{} : Bool}) ->
  MV(ds, ks, img, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 1, no frame: M.out halts with 0 and the bytes of the value (Program.unbytes), or with 2 when it is no list of bytes
def mv.out(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +focus: Bk.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Nil{}, ps)) ->
  MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  match rest:
    case D.R59{+r4, +r5, +r6, +r7, +r8, +r9, +r10, +r11, +r12, +r13, +r14, +r15, +r16, +r17, +r18, +r19, +r20, +r21, +r22, +r23, +r24, +r25, +r26, +r27, +r28, +r29, +r30, +r31, +r32, +r33, +r34, +r35, +r36, +r37, +r38, +r39, +r40, +r41, +r42, +r43, +r44, +r45, +r46, +r47, +r48, +r49, +r50, +r51, +r52, +r53, +r54, +r55, +r56, +r57, +r58, +r59, +r60, +r61, +r62}:
      match iv:
        case Tuple{+et, Tuple{_, Tuple{+evv, Tuple{_, Tuple{_, Tuple{+isf, Tuple{+frs, Tuple{_, Tuple{+io, Tuple{_, _}}}}}}}}}}:
          +k = img.ks(ds, ks, img, m, im, fi, nx, io)
          %Equal.sym(U32, sp, 0, frs) : MV(ds, ks, img, D.S(foc, 1, _, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), t, w)
          out.mv(ds, ks, img, foc, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp, t, w, focus, et, evv, isf,
            D.Ex.fst(List<&2, List<&2, Word(8n)>>, ks2 => {ks == Mc.Img.known(ks2) : List<&2, List<&2, Word(8n)>>}, k),
            D.Ex.snd(List<&2, List<&2, Word(8n)>>, ks2 => {ks == Mc.Img.known(ks2) : List<&2, List<&2, Word(8n)>>}, k))

# mode 1, App q □ a (app_arg, app_val) with q live and a not known: a to evaluate, in the frame App q v □; an admin move
def mv.ret.swap(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +focus: Bk.Term, +kind: D.FK, +q: Bk.Quan, +k: Bool, +a: Bk.Term, +b: Bk.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Con{D.AF{kind, q, k, a, b}, fs}, ps), +hk: {FK.isapp(kind) == True{} : Bool}, +hs: {Bool.and(El.Quan.live(q), Bool.not(k)) == True{} : Bool}) ->
  MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  match kind:
    case D.FK.arg{}:
      SW.sw.app.mv(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, focus, D.FK.arg{}, q, k, a, b, iv, {==}, hs)
    case D.FK.val{}:
      SW.sw.app.mv(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, focus, D.FK.val{}, q, k, a, b, iv, {==}, hs)
    case D.FK.fun{}:
      D.bool.ft(MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w), hk)
    case D.FK.let{}:
      D.bool.ft(MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w), hk)
    case D.FK.tupb{}:
      D.bool.ft(MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w), hk)
    case D.FK.tupa{}:
      D.bool.ft(MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w), hk)
    case D.FK.rwt{}:
      D.bool.ft(MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w), hk)
    case D.FK.minb{}:
      D.bool.ft(MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w), hk)
    case D.FK.mina{}:
      D.bool.ft(MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w), hk)

# mode 1, App q v □ a (app_arg, app_val), when q is dead or a known: the redex of a λ (Eval.redex): its body with the argument put in (M.data, M.copy), a step; halt 2 when the λ does not bind it
def mv.ret.app.lam(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +r: Bk.Quan, +h: Bk.Term, +kind: D.FK, +q: Bk.Quan, +k: Bool, +a: Bk.Term, +b: Bk.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, Bk.Term.Lam{r, h}, Con{D.AF{kind, q, k, a, b}, fs}, ps), +hk: {FK.isapp(kind) == True{} : Bool}, +hs: {Bool.and(El.Quan.live(q), Bool.not(k)) == False{} : Bool}) ->
  MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 1, App q g □ (app_fun), with the value v: the redex of a λ (Eval.redex): its body with the argument put in (M.data, M.copy), a step; halt 2 when the λ does not bind it
def mv.ret.fun.lam(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +r: Bk.Quan, +h: Bk.Term, +focus: Bk.Term, +q: Bk.Quan, +k: Bool, +b: Bk.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Con{D.AF{D.FK.fun{}, q, k, Bk.Term.Lam{r, h}, b}, fs}, ps)) ->
  MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 1, App q v □ a (app_arg, app_val), when q is dead or a known: the redex of a λ-match of pairs: its case on the pair's fields, a step; halt 2 when the argument is no live pair
def mv.ret.app.prj(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +h: Bk.Term, +kind: D.FK, +q: Bk.Quan, +k: Bool, +a: Bk.Term, +b: Bk.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, Bk.Term.Prj{h}, Con{D.AF{kind, q, k, a, b}, fs}, ps), +hk: {FK.isapp(kind) == True{} : Bool}, +hs: {Bool.and(El.Quan.live(q), Bool.not(k)) == False{} : Bool}) ->
  MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 1, App q g □ (app_fun), with the value v: the redex of a λ-match of pairs: its case on the pair's fields, a step; halt 2 when the argument is no live pair
def mv.ret.fun.prj(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +h: Bk.Term, +focus: Bk.Term, +q: Bk.Quan, +k: Bool, +b: Bk.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Con{D.AF{D.FK.fun{}, q, k, Bk.Term.Prj{h}, b}, fs}, ps)) ->
  MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 1, App q v □ a (app_arg, app_val), when q is dead or a known: the redex of a λ-match of labels: the case of the label, a step; halt 2 when the argument is no live label
def mv.ret.app.mat(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +j: List<&2, Word(8n)>, +h: Bk.Term, +n: Bk.Term, +kind: D.FK, +q: Bk.Quan, +k: Bool, +a: Bk.Term, +b: Bk.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, Bk.Term.Mat{j, h, n}, Con{D.AF{kind, q, k, a, b}, fs}, ps), +hk: {FK.isapp(kind) == True{} : Bool}, +hs: {Bool.and(El.Quan.live(q), Bool.not(k)) == False{} : Bool}) ->
  MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 1, App q g □ (app_fun), with the value v: the redex of a λ-match of labels: the case of the label, a step; halt 2 when the argument is no live label
def mv.ret.fun.mat(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +j: List<&2, Word(8n)>, +h: Bk.Term, +n: Bk.Term, +focus: Bk.Term, +q: Bk.Quan, +k: Bool, +b: Bk.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Con{D.AF{D.FK.fun{}, q, k, Bk.Term.Mat{j, h, n}, b}, fs}, ps)) ->
  MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 1, App q v □ a (app_arg, app_val), when q is dead or a known: the redex of any other value: a call (M.call, with M.walk and M.copy) of the def at the head of its spine: a step to the copy of its leaf, or a value that waits for more arguments (an admin move); halt 2 when no walk exists
def mv.ret.app.call(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +focus: Bk.Term, +kind: D.FK, +q: Bk.Quan, +k: Bool, +a: Bk.Term, +b: Bk.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Con{D.AF{kind, q, k, a, b}, fs}, ps), +hk: {FK.isapp(kind) == True{} : Bool}, +hs: {Bool.and(El.Quan.live(q), Bool.not(k)) == False{} : Bool}, +hn: {A.node(focus) == False{} : Bool}) ->
  MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 1, App q g □ (app_fun), with the value v: the redex of any other value: a call (M.call, with M.walk and M.copy) of the def at the head of its spine: a step to the copy of its leaf, or a value that waits for more arguments (an admin move); halt 2 when no walk exists
def mv.ret.fun.call(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +g: Bk.Term, +focus: Bk.Term, +q: Bk.Quan, +k: Bool, +b: Bk.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Con{D.AF{D.FK.fun{}, q, k, g, b}, fs}, ps), +hn: {A.node(g) == False{} : Bool}) ->
  MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 1, Let q □ a, with the value v: a with v put in (M.data, M.copy), a step; halt 2 when q is 2 and v is no Data
def mv.ret.let(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +focus: Bk.Term, +q: Bk.Quan, +k: Bool, +a: Bk.Term, +b: Bk.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Con{D.AF{D.FK.let{}, q, k, a, b}, fs}, ps)) ->
  MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 1, Tup q □ a, with the value v: a to evaluate, in the frame Tup q v □; an admin move
def mv.ret.tupb(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +focus: Bk.Term, +q: Bk.Quan, +k: Bool, +a: Bk.Term, +b: Bk.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Con{D.AF{D.FK.tupb{}, q, k, a, b}, fs}, ps)) ->
  MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 1, Tup q a □, with the value v: the value Tup q a v; an admin move
def mv.ret.tupa(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +focus: Bk.Term, +q: Bk.Quan, +k: Bool, +a: Bk.Term, +b: Bk.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Con{D.AF{D.FK.tupa{}, q, k, a, b}, fs}, ps)) ->
  MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 1, Rwt □ a b, with the value v: b when v is Rfl, a step; else halt 2
def mv.ret.rwt(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +focus: Bk.Term, +q: Bk.Quan, +k: Bool, +a: Bk.Term, +b: Bk.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Con{D.AF{D.FK.rwt{}, q, k, a, b}, fs}, ps)) ->
  MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 1, Min □ a, with the value v: a to evaluate, in the frame Min v □; an admin move
def mv.ret.minb(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +focus: Bk.Term, +q: Bk.Quan, +k: Bool, +a: Bk.Term, +b: Bk.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Con{D.AF{D.FK.minb{}, q, k, a, b}, fs}, ps)) ->
  MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 1, Min a □, with the value v: the meet of a and v, a step, when both are labels of quantities; else halt 2
def mv.ret.mina(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +focus: Bk.Term, +q: Bk.Quan, +k: Bool, +a: Bk.Term, +b: Bk.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Con{D.AF{D.FK.mina{}, q, k, a, b}, fs}, ps)) ->
  MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# The choice of the move
# ----------------------

# mode 0: by the flag VALUE of the focus' cell, then by its term
def round.ev(b: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +focus: Bk.Term, eb: {D.Fl(m, foc, 256) == b : Bool},
  iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, False{}, focus, fs, ps)) -> MV(ds, ks, img, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  match b:
    case True{}:
      mv.ev.val(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, focus, iv, eb)
    case False{}:
      match focus:
        case Bk.Term.Var{+i}:
          mv.ev.var(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, i, iv, eb)
        case Bk.Term.Ref{+k}:
          mv.ev.ref(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, k, iv, eb)
        case Bk.Term.Ann{+x, +y}:
          mv.ev.ann(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, x, y, iv, eb)
        case Bk.Term.Let{+q, +v, +b2}:
          match q:
            case Bk.Quan.Q0{}:
              mv.ev.unlet(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Quan.Q0{}, v, b2, iv, eb, {==})
            case Bk.Quan.Q1{}:
              mv.ev.let(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Quan.Q1{}, v, b2, iv, eb, {==})
            case Bk.Quan.Q2{}:
              mv.ev.let(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Quan.Q2{}, v, b2, iv, eb, {==})
        case Bk.Term.Typ{+x}:
          mv.ev.former(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Typ{x}, iv, {==})
        case Bk.Term.Min{+a, +b2}:
          mv.ev.min(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, a, b2, iv, eb)
        case Bk.Term.All{+q, +a, +b2}:
          mv.ev.former(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.All{q, a, b2}, iv, {==})
        case Bk.Term.Lam{+q, +b2}:
          mv.ev.former(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Lam{q, b2}, iv, {==})
        case Bk.Term.App{+q, +g, +x}:
          mv.ev.app(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, g, x, iv, eb)
        case Bk.Term.Sig{+q, +a, +b2}:
          mv.ev.former(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Sig{q, a, b2}, iv, {==})
        case Bk.Term.Tup{+q, +a, +b2}:
          match q:
            case Bk.Quan.Q0{}:
              mv.ev.tup0(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Quan.Q0{}, a, b2, iv, eb, {==})
            case Bk.Quan.Q1{}:
              mv.ev.tup(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Quan.Q1{}, a, b2, iv, eb, {==})
            case Bk.Quan.Q2{}:
              mv.ev.tup(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Quan.Q2{}, a, b2, iv, eb, {==})
        case Bk.Term.Prj{+h}:
          mv.ev.former(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Prj{h}, iv, {==})
        case Bk.Term.Enu{+e}:
          mv.ev.former(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Enu{e}, iv, {==})
        case Bk.Term.Lab{+k}:
          mv.ev.former(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Lab{k}, iv, {==})
        case Bk.Term.Mat{+k, +h, +n}:
          mv.ev.former(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Mat{k, h, n}, iv, {==})
        case Bk.Term.Efq{}:
          mv.ev.former(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Efq{}, iv, {==})
        case Bk.Term.Eql{+a, +b2, +y}:
          mv.ev.former(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Eql{a, b2, y}, iv, {==})
        case Bk.Term.Rfl{}:
          mv.ev.former(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Rfl{}, iv, {==})
        case Bk.Term.Rwt{+e, +p2, +b2}:
          mv.ev.rwt(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, e, p2, b2, iv, eb)

# mode 1, App q □ a: swap when q is live and a is not known; else the redex, by
# the value's term
def round.app(b: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +focus: Bk.Term, +kind: D.FK, +q: Bk.Quan, +k: Bool, +a: Bk.Term, +bb: Bk.Term,
  eb: {Bool.and(El.Quan.live(q), Bool.not(k)) == b : Bool}, hk: {FK.isapp(kind) == True{} : Bool},
  iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Con{D.AF{kind, q, k, a, bb}, fs}, ps)) -> MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  match b:
    case True{}:
      mv.ret.swap(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, focus, kind, q, k, a, bb, iv, hk, eb)
    case False{}:
      match focus:
        case Bk.Term.Var{+i}:
          mv.ret.app.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Var{i}, kind, q, k, a, bb, iv, hk, eb, {==})
        case Bk.Term.Ref{+kk}:
          mv.ret.app.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Ref{kk}, kind, q, k, a, bb, iv, hk, eb, {==})
        case Bk.Term.Ann{+x, +y}:
          mv.ret.app.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Ann{x, y}, kind, q, k, a, bb, iv, hk, eb, {==})
        case Bk.Term.Let{+qq, +v, +b2}:
          mv.ret.app.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Let{qq, v, b2}, kind, q, k, a, bb, iv, hk, eb, {==})
        case Bk.Term.Typ{+x}:
          mv.ret.app.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Typ{x}, kind, q, k, a, bb, iv, hk, eb, {==})
        case Bk.Term.Min{+aa, +b2}:
          mv.ret.app.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Min{aa, b2}, kind, q, k, a, bb, iv, hk, eb, {==})
        case Bk.Term.All{+qq, +aa, +b2}:
          mv.ret.app.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.All{qq, aa, b2}, kind, q, k, a, bb, iv, hk, eb, {==})
        case Bk.Term.Lam{+r, +b2}:
          mv.ret.app.lam(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, r, b2, kind, q, k, a, bb, iv, hk, eb)
        case Bk.Term.App{+qq, +g, +x}:
          mv.ret.app.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.App{qq, g, x}, kind, q, k, a, bb, iv, hk, eb, {==})
        case Bk.Term.Sig{+qq, +aa, +b2}:
          mv.ret.app.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Sig{qq, aa, b2}, kind, q, k, a, bb, iv, hk, eb, {==})
        case Bk.Term.Tup{+qq, +aa, +b2}:
          mv.ret.app.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Tup{qq, aa, b2}, kind, q, k, a, bb, iv, hk, eb, {==})
        case Bk.Term.Prj{+h}:
          mv.ret.app.prj(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, h, kind, q, k, a, bb, iv, hk, eb)
        case Bk.Term.Enu{+e}:
          mv.ret.app.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Enu{e}, kind, q, k, a, bb, iv, hk, eb, {==})
        case Bk.Term.Lab{+kk}:
          mv.ret.app.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Lab{kk}, kind, q, k, a, bb, iv, hk, eb, {==})
        case Bk.Term.Mat{+kk, +h, +n}:
          mv.ret.app.mat(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, kk, h, n, kind, q, k, a, bb, iv, hk, eb)
        case Bk.Term.Efq{}:
          mv.ret.app.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Efq{}, kind, q, k, a, bb, iv, hk, eb, {==})
        case Bk.Term.Eql{+aa, +b2, +y}:
          mv.ret.app.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Eql{aa, b2, y}, kind, q, k, a, bb, iv, hk, eb, {==})
        case Bk.Term.Rfl{}:
          mv.ret.app.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Rfl{}, kind, q, k, a, bb, iv, hk, eb, {==})
        case Bk.Term.Rwt{+e, +p2, +b2}:
          mv.ret.app.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Rwt{e, p2, b2}, kind, q, k, a, bb, iv, hk, eb, {==})

# mode 1, App q g □: the redex, by the function's term
def round.fun(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +focus: Bk.Term, +q: Bk.Quan, +k: Bool, +g: Bk.Term, +bb: Bk.Term,
  iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Con{D.AF{D.FK.fun{}, q, k, g, bb}, fs}, ps)) -> MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  match g:
    case Bk.Term.Var{+i}:
      mv.ret.fun.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Var{i}, focus, q, k, bb, iv, {==})
    case Bk.Term.Ref{+kk}:
      mv.ret.fun.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Ref{kk}, focus, q, k, bb, iv, {==})
    case Bk.Term.Ann{+x, +y}:
      mv.ret.fun.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Ann{x, y}, focus, q, k, bb, iv, {==})
    case Bk.Term.Let{+r, +v, +b2}:
      mv.ret.fun.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Let{r, v, b2}, focus, q, k, bb, iv, {==})
    case Bk.Term.Typ{+x}:
      mv.ret.fun.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Typ{x}, focus, q, k, bb, iv, {==})
    case Bk.Term.Min{+a, +b2}:
      mv.ret.fun.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Min{a, b2}, focus, q, k, bb, iv, {==})
    case Bk.Term.All{+r, +a, +b2}:
      mv.ret.fun.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.All{r, a, b2}, focus, q, k, bb, iv, {==})
    case Bk.Term.Lam{+r, +b2}:
      mv.ret.fun.lam(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, r, b2, focus, q, k, bb, iv)
    case Bk.Term.App{+r, +g, +x}:
      mv.ret.fun.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.App{r, g, x}, focus, q, k, bb, iv, {==})
    case Bk.Term.Sig{+r, +a, +b2}:
      mv.ret.fun.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Sig{r, a, b2}, focus, q, k, bb, iv, {==})
    case Bk.Term.Tup{+r, +a, +b2}:
      mv.ret.fun.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Tup{r, a, b2}, focus, q, k, bb, iv, {==})
    case Bk.Term.Prj{+h}:
      mv.ret.fun.prj(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, h, focus, q, k, bb, iv)
    case Bk.Term.Enu{+e}:
      mv.ret.fun.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Enu{e}, focus, q, k, bb, iv, {==})
    case Bk.Term.Lab{+kk}:
      mv.ret.fun.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Lab{kk}, focus, q, k, bb, iv, {==})
    case Bk.Term.Mat{+kk, +h, +n}:
      mv.ret.fun.mat(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, kk, h, n, focus, q, k, bb, iv)
    case Bk.Term.Efq{}:
      mv.ret.fun.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Efq{}, focus, q, k, bb, iv, {==})
    case Bk.Term.Eql{+a, +b2, +y}:
      mv.ret.fun.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Eql{a, b2, y}, focus, q, k, bb, iv, {==})
    case Bk.Term.Rfl{}:
      mv.ret.fun.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Rfl{}, focus, q, k, bb, iv, {==})
    case Bk.Term.Rwt{+e, +p2, +b2}:
      mv.ret.fun.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, Bk.Term.Rwt{e, p2, b2}, focus, q, k, bb, iv, {==})

# the move of a state that Inv finds: by the mode, then by the focus or the
# top frame
def round.go(+ret: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +focus: Bk.Term,
  iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, ret, focus, fs, ps)) -> MV(ds, ks, img, D.S(foc, Bool.to_u32(ret), sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  match ret:
    case False{}:
      round.ev(D.Fl(m, foc, 256), ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, focus, {==}, iv)
    case True{}:
      match fs:
        case Nil{}:
          mv.out(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, focus, iv)
        case Con{D.AF{+kind, +q, +k, +a, +bb}, +fs2}:
          match kind:
            case D.FK.arg{}:
              round.app(Bool.and(El.Quan.live(q), Bool.not(k)), ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs2, ps, focus, D.FK.arg{}, q, k, a, bb, {==}, {==}, iv)
            case D.FK.val{}:
              round.app(Bool.and(El.Quan.live(q), Bool.not(k)), ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs2, ps, focus, D.FK.val{}, q, k, a, bb, {==}, {==}, iv)
            case D.FK.fun{}:
              round.fun(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs2, ps, focus, q, k, a, bb, iv)
            case D.FK.let{}:
              mv.ret.let(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs2, ps, focus, q, k, a, bb, iv)
            case D.FK.tupb{}:
              mv.ret.tupb(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs2, ps, focus, q, k, a, bb, iv)
            case D.FK.tupa{}:
              mv.ret.tupa(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs2, ps, focus, q, k, a, bb, iv)
            case D.FK.rwt{}:
              mv.ret.rwt(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs2, ps, focus, q, k, a, bb, iv)
            case D.FK.minb{}:
              mv.ret.minb(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs2, ps, focus, q, k, a, bb, iv)
            case D.FK.mina{}:
              mv.ret.mina(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs2, ps, focus, q, k, a, bb, iv)

# the registers, the output and its length that Inv finds
def inv.regs(-ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -regs: List<&2, U32>, -m: Cr.Cir.Cells, -nx: U32, -fi: U32, -im: U32, -out: List<&2, Word(8n)>, -outn: U32, -t: Bk.Term, -w: Nat, -ret: Bool, -focus: Bk.Term, -fs: List<&2, D.AF>, -foc: U32, -sp: U32, -pend: U32, -ps: List<&2, U32>, -rest: D.R59, iw: D.InvOf(ds, ks, img, regs, m, nx, fi, im, out, outn, t, w, ret, focus, fs, foc, sp, pend, ps, rest)) ->
  {regs == D.RG(foc, Bool.to_u32(ret), sp, pend, D.R59.list(rest)) : List<&2, U32>}:
  match iw:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}:
      e

def inv.out(-ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -regs: List<&2, U32>, -m: Cr.Cir.Cells, -nx: U32, -fi: U32, -im: U32, -out: List<&2, Word(8n)>, -outn: U32, -t: Bk.Term, -w: Nat, -ret: Bool, -focus: Bk.Term, -fs: List<&2, D.AF>, -foc: U32, -sp: U32, -pend: U32, -ps: List<&2, U32>, -rest: D.R59, iw: D.InvOf(ds, ks, img, regs, m, nx, fi, im, out, outn, t, w, ret, focus, fs, foc, sp, pend, ps, rest)) -> {out == Nil{} : List<&2, Word(8n)>}:
  match iw:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}:
      e

def inv.outn(-ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -regs: List<&2, U32>, -m: Cr.Cir.Cells, -nx: U32, -fi: U32, -im: U32, -out: List<&2, Word(8n)>, -outn: U32, -t: Bk.Term, -w: Nat, -ret: Bool, -focus: Bk.Term, -fs: List<&2, D.AF>, -foc: U32, -sp: U32, -pend: U32, -ps: List<&2, U32>, -rest: D.R59, iw: D.InvOf(ds, ks, img, regs, m, nx, fi, im, out, outn, t, w, ret, focus, fs, foc, sp, pend, ps, rest)) -> {outn == 0 : U32}:
  match iw:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, e}}}}}}}}}}:
      e

# Inv's facts, in the state that it finds
def iv.of(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +out: List<&2, Word(8n)>, +outn: U32, +t: Bk.Term, +w: Nat, +ret: Bool, +focus: Bk.Term, +fs: List<&2, D.AF>, +foc: U32, +sp: U32, +pend: U32, +ps: List<&2, U32>, +rest: D.R59,
  er: {regs == D.RG(foc, Bool.to_u32(ret), sp, pend, D.R59.list(rest)) : List<&2, U32>}, eo: {out == Nil{} : List<&2, Word(8n)>},
  en: {outn == 0 : U32}, iw: D.InvOf(ds, ks, img, regs, m, nx, fi, im, out, outn, t, w, ret, focus, fs, foc, sp, pend, ps, rest)) ->
  IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, ret, focus, fs, ps):
  %er : D.InvOf(ds, ks, img, _, m, nx, fi, im, Nil{}, 0, t, w, ret, focus, fs, foc, sp, pend, ps, rest)
  %eo : D.InvOf(ds, ks, img, regs, m, nx, fi, im, _, 0, t, w, ret, focus, fs, foc, sp, pend, ps, rest)
  %en : D.InvOf(ds, ks, img, regs, m, nx, fi, im, out, _, t, w, ret, focus, fs, foc, sp, pend, ps, rest)
  iw

def round.iw(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +out: List<&2, Word(8n)>, +outn: U32, +t: Bk.Term, +w: Nat, +ret: Bool, +focus: Bk.Term, +fs: List<&2, D.AF>, +foc: U32, +sp: U32, +pend: U32, +ps: List<&2, U32>, +rest: D.R59, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +iw: D.InvOf(ds, ks, img, regs, m, nx, fi, im, out, outn, t, w, ret, focus, fs, foc, sp, pend, ps, rest)) ->
  MV(ds, ks, img, Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, out, outn}, t, w):
  +er = inv.regs(ds, ks, img, regs, m, nx, fi, im, out, outn, t, w, ret, focus, fs, foc, sp, pend, ps, rest, iw)
  +eo = inv.out(ds, ks, img, regs, m, nx, fi, im, out, outn, t, w, ret, focus, fs, foc, sp, pend, ps, rest, iw)
  +en = inv.outn(ds, ks, img, regs, m, nx, fi, im, out, outn, t, w, ret, focus, fs, foc, sp, pend, ps, rest, iw)
  %Equal.sym(List<&2, U32>, regs, D.RG(foc, Bool.to_u32(ret), sp, pend, D.R59.list(rest)), er) :
    MV(ds, ks, img, Cr.Cir.State{_, m, nx, fi, im, pg, lim, inp, out, outn}, t, w)
  %Equal.sym(List<&2, Word(8n)>, out, Nil{}, eo) :
    MV(ds, ks, img, Cr.Cir.State{D.RG(foc, Bool.to_u32(ret), sp, pend, D.R59.list(rest)), m, nx, fi, im, pg, lim, inp, _, outn}, t, w)
  %Equal.sym(U32, outn, 0, en) :
    MV(ds, ks, img, Cr.Cir.State{D.RG(foc, Bool.to_u32(ret), sp, pend, D.R59.list(rest)), m, nx, fi, im, pg, lim, inp, Nil{}, _}, t, w)
  round.go(ret, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, focus,
    iv.of(ds, ks, img, regs, m, nx, fi, im, out, outn, t, w, ret, focus, fs, foc, sp, pend, ps, rest, er, eo, en, iw))

def round.wit(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +out: List<&2, Word(8n)>, +outn: U32,
  +t: Bk.Term, +w: Nat, inv: D.Inv(ds, ks, img, Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, out, outn}, t, w)) ->
  MV(ds, ks, img, Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, out, outn}, t, w):
  (x, iw) = inv
  match x:
    case D.Wit{+ret, +focus, +fs, +foc, +sp, +pend, +ps, +rest}:
      round.iw(ds, ks, img, regs, m, nx, fi, im, out, outn, t, w, ret, focus, fs, foc, sp, pend, ps, rest, pg, lim, inp, iw)

# the move of a state of the invariant
def round.mv(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, st: Cr.Cir.State, +t: Bk.Term,
  +w: Nat, inv: D.Inv(ds, ks, img, st, t, w)) -> MV(ds, ks, img, st, t, w):
  match st:
    case Cr.Cir.State{+regs, +m, +nx, +fi, +im, +pg, +lim, +inp, +out, +outn}:
      round.wit(ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, out, outn, t, w, inv)

# a round of the main loop, for any fuel: an admin move, a step, a halt that
# says what Eval gives, or out of memory
def round.post(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +st: Cr.Cir.State, +t: Bk.Term, +w: Nat, inv: D.Inv(ds, ks, img, st, t, w)) ->
  D.Post(False{}, Cr.Cir.exec(f, D.B.body(), st), s => D.Rnd(ds, ks, img, t, w, s), s => st2 => D.HR(ds, t, s, st2)):
  mv.post(f, ds, ks, img, st, t, w, round.mv(ds, ks, img, st, t, w, inv))

# a round of the main loop ends, with some fuel
def round.done(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st: Cr.Cir.State,
  +t: Bk.Term, +w: Nat, inv: D.Inv(ds, ks, img, st, t, w)) -> D.Ex(Nat, f => D.Ends(Cr.Cir.exec(f, D.B.body(), st))):
  mv.done(ds, ks, img, st, t, w, round.mv(ds, ks, img, st, t, w, inv))

# The loop gives what Eval gives
# ------------------------------

# a weaker halt
def post.wk(dn: Bool, o: Cr.Cir.Out, -Q: Cr.Cir.State -> Type, -H1: U32 -> Cr.Cir.State -> Type,
  -H2: U32 -> Cr.Cir.State -> Type, h: D.Post(dn, o, Q, H1), hh: @s: U32 -> @st: Cr.Cir.State -> H1(s, st) -> H2(s, st)) ->
  D.Post(dn, o, Q, H2):
  match o:
    case Cr.Cir.Out.next{st}:
      h
    case Cr.Cir.Out.halt{s, st}:
      hh(s, st, h)
    case Cr.Cir.Out.out_of_memory{}:
      Unit{}
    case Cr.Cir.Out.trap{}:
      h
    case Cr.Cir.Out.not_done{}:
      h

# no result after a term with no step
def none.after(+j: Nat, +ds: List<&2, Bk.Def>, +t: Bk.Term, es: {El.Eval.step(ds, t) == None{} : Maybe<Bk.Term>}) ->
  {Pg.Program.result(ds, El.Eval.steps(1n+j, ds, t)) == None{} : Maybe<&2, List<&2, Word(8n)>>}:
  %Equal.sym(Maybe<Bk.Term>, El.Eval.step(ds, t), None{}, es) : {Pg.Program.result(ds, El.Eval.run(j, ds, _)) == None{} : Maybe<&2, List<&2, Word(8n)>>}
  %Equal.sym(Maybe<Bk.Term>, El.Eval.run(j, ds, None{}), None{}, D.run.none(j, ds)) : {Pg.Program.result(ds, _) == None{} : Maybe<&2, List<&2, Word(8n)>>}
  {==}

# no result ever, from a term with no step and no result
def he.none(k: Nat, +ds: List<&2, Bk.Def>, +t: Bk.Term, +es: {El.Eval.step(ds, t) == None{} : Maybe<Bk.Term>},
  er: {Pg.Program.result(ds, Some{t}) == None{} : Maybe<&2, List<&2, Word(8n)>>}) ->
  {Pg.Program.result(ds, El.Eval.steps(k, ds, t)) == None{} : Maybe<&2, List<&2, Word(8n)>>}:
  match k:
    case 0n:
      er
    case 1n+(+j):
      none.after(j, ds, t, es)

# a round's halt says what the loop's says
def he.of(+ds: List<&2, Bk.Def>, +t: Bk.Term, -s: U32, -st: Cr.Cir.State, h: D.HR(ds, t, s, st)) -> D.HE(ds, t, s, st):
  match h:
    case Inl{x}:
      (e0, r) = x
      (es, er) = r
      Inl{(e0, (0n, er))}
    case Inr{x}:
      (e2, r) = x
      (es, er) = r
      Inr{(e2, k => he.none(k, ds, t, es, er))}

# the result after a step, from the result of its term
def step.res(+j: Nat, +ds: List<&2, Bk.Def>, +t: Bk.Term, -u: Bk.Term, -x: Maybe<&2, List<&2, Word(8n)>>,
  es: {El.Eval.step(ds, t) == Some{u} : Maybe<Bk.Term>},
  e: {Pg.Program.result(ds, El.Eval.steps(j, ds, u)) == x : Maybe<&2, List<&2, Word(8n)>>}) ->
  {Pg.Program.result(ds, El.Eval.steps(1n+j, ds, t)) == x : Maybe<&2, List<&2, Word(8n)>>}:
  %Equal.sym(Maybe<Bk.Term>, El.Eval.step(ds, t), Some{u}, es) : {Pg.Program.result(ds, El.Eval.run(j, ds, _)) == x : Maybe<&2, List<&2, Word(8n)>>}
  e

# the result of a term from that of its step
def res.step(+j: Nat, +ds: List<&2, Bk.Def>, +t: Bk.Term, -u: Bk.Term, -x: Maybe<&2, List<&2, Word(8n)>>,
  es: {El.Eval.step(ds, t) == Some{u} : Maybe<Bk.Term>},
  e: {Pg.Program.result(ds, El.Eval.steps(1n+j, ds, t)) == x : Maybe<&2, List<&2, Word(8n)>>}) ->
  {Pg.Program.result(ds, El.Eval.steps(j, ds, u)) == x : Maybe<&2, List<&2, Word(8n)>>}:
  %es : {Pg.Program.result(ds, El.Eval.run(j, ds, _)) == x : Maybe<&2, List<&2, Word(8n)>>}
  e

def he.all(k: Nat, +ds: List<&2, Bk.Def>, +t: Bk.Term, +u: Bk.Term, +es: {El.Eval.step(ds, t) == Some{u} : Maybe<Bk.Term>},
  g: @k: Nat -> {Pg.Program.result(ds, El.Eval.steps(k, ds, u)) == None{} : Maybe<&2, List<&2, Word(8n)>>}) ->
  {Pg.Program.result(ds, El.Eval.steps(k, ds, t)) == None{} : Maybe<&2, List<&2, Word(8n)>>}:
  match k:
    case 0n:
      D.res.nv(ds, t, vals.of(El.Eval.vals(ds, t, False{}), ds, t, u, {==}, es))
    case 1n+(+j):
      step.res(j, ds, t, u, None{}, es, g(j))

# a halt of the loop after a step says what Eval gives before the step
def he.step(+ds: List<&2, Bk.Def>, +t: Bk.Term, +u: Bk.Term, +es: {El.Eval.step(ds, t) == Some{u} : Maybe<Bk.Term>},
  -s: U32, -st: Cr.Cir.State, h: D.HE(ds, u, s, st)) -> D.HE(ds, t, s, st):
  match h:
    case Inl{x}:
      (e0, r) = x
      (+k, ek) = r
      Inl{(e0, (1n+k, step.res(k, ds, t, u, Some{List.reverse(&2, Word(8n), D.St.out(st))}, es, ek)))}
    case Inr{x}:
      (e2, g) = x
      Inr{(e2, k => he.all(k, ds, t, u, es, g))}

# after a round that goes on: the loop from the next state, by ia after an
# admin move and by ist after a step
def loop.next(+p: Nat, +ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, +u: Cr.Cir.State,
  +t: Bk.Term, -w: Nat, r: D.Rnd(ds, ks, img, t, w, u),
  ia: @w2: Nat -> D.Inv(ds, ks, img, u, t, w2) ->
    D.Post(False{}, Cr.Cir.exec(p, D.B.loop(), u), s => Empty, s => st2 => D.HE(ds, t, s, st2)),
  ist: @v: Bk.Term -> @w2: Nat -> D.Inv(ds, ks, img, u, v, w2) ->
    D.Post(False{}, Cr.Cir.exec(p, D.B.loop(), u), s => Empty, s => st2 => D.HE(ds, v, s, st2))) ->
  D.Post(False{}, Cr.Cir.exec(p, D.B.loop(), u), s => Empty, s => st2 => D.HE(ds, t, s, st2)):
  match r:
    case Inl{a}:
      (w2, r2) = a
      (inv2, lt) = r2
      ia(w2, inv2)
    case Inr{b}:
      (+v, r2) = b
      (+es, r3) = r2
      (w2, inv2) = r3
      post.wk(False{}, Cr.Cir.exec(p, D.B.loop(), u), s => Empty, s => st2 => D.HE(ds, v, s, st2), s => st2 => D.HE(ds, t, s, st2),
        ist(v, w2, inv2), s => st2 => h => he.step(ds, t, v, es, s, st2, h))

# the main loop, from a state of the invariant of the term t, halts only as
# HE says, with any fuel: by induction on the fuel
def loop.post(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st: Cr.Cir.State,
  +t: Bk.Term, +w: Nat, inv: D.Inv(ds, ks, img, st, t, w)) ->
  D.Post(False{}, Cr.Cir.exec(f, D.B.loop(), st), s => Empty, s => st2 => D.HE(ds, t, s, st2)):
  match f:
    case 0n:
      Unit{}
    case 1n+p:
      D.post.then(False{}, Cr.Cir.exec(p, D.B.body(), st), u => Cr.Cir.exec(p, D.B.loop(), u), s => D.Rnd(ds, ks, img, t, w, s),
        s => Empty, s => st2 => D.HR(ds, t, s, st2), s => st2 => D.HE(ds, t, s, st2),
        round.post(p, ds, ks, img, st, t, w, inv),
        s => st2 => h => he.of(ds, t, s, st2, h),
        +u => r => loop.next(p, ds, ks, img, u, t, w, r, w2 => i2 => loop.post(p, ds, ks, img, u, t, w2, i2),
          v => w2 => i2 => loop.post(p, ds, ks, img, u, v, w2, i2)))

# The loop reaches what Eval reaches
# ----------------------------------

def good.ends(-o: List<&2, Word(8n)>, r: Cr.Cir.Out, g: D.Good(o, r)) -> D.Ends(r):
  match r:
    case Cr.Cir.Out.next{_}:
      Unit{}
    case Cr.Cir.Out.halt{_, _}:
      Unit{}
    case Cr.Cir.Out.out_of_memory{}:
      Unit{}
    case Cr.Cir.Out.trap{}:
      Unit{}
    case Cr.Cir.Out.not_done{}:
      g

def good.then(-o: List<&2, Word(8n)>, r: Cr.Cir.Out, -k: Cr.Cir.State -> Cr.Cir.Out, g: D.Good(o, r)) ->
  D.Good(o, Cr.Cir.exec.then(r, k)):
  match r:
    case Cr.Cir.Out.next{st}:
      Empty.absurd(D.Good(o, k(st)), g)
    case Cr.Cir.Out.halt{s, st}:
      g
    case Cr.Cir.Out.out_of_memory{}:
      Unit{}
    case Cr.Cir.Out.trap{}:
      g
    case Cr.Cir.Out.not_done{}:
      g

def ends.eq(-a: Cr.Cir.Out, -b: Cr.Cir.Out, e: {a == b : Cr.Cir.Out}, d: D.Ends(b)) -> D.Ends(a):
  %Equal.sym(Cr.Cir.Out, a, b, e) : D.Ends(_)
  d

# a round that halts or runs out of memory with the fuel f0 ends the loop the
# same with 1 + f0
def out.fin(-o: List<&2, Word(8n)>, +f0: Nat, -st: Cr.Cir.State, r: Cr.Cir.Out, er: {Cr.Cir.exec(f0, D.B.body(), st) == r : Cr.Cir.Out},
  g: D.Good(o, r)) -> D.Good(o, Cr.Cir.exec(1n+f0, D.B.loop(), st)):
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f0, D.B.body(), st), r, er) : D.Good(o, Cr.Cir.exec.then(_, u => Cr.Cir.exec(f0, D.B.loop(), u)))
  good.then(o, r, u => Cr.Cir.exec(f0, D.B.loop(), u), g)

# a round that goes on with the fuel f0, then the loop with n1, are the loop
# with 1 + f0 + n1
def next.fin(+o: List<&2, Word(8n)>, +f0: Nat, +n1: Nat, +st: Cr.Cir.State, +u: Cr.Cir.State,
  +er: {Cr.Cir.exec(f0, D.B.body(), st) == Cr.Cir.Out.next{u} : Cr.Cir.Out},
  +g1: D.Good(o, Cr.Cir.exec(n1, D.B.loop(), u))) -> D.Good(o, Cr.Cir.exec(1n+Nat.add(f0, n1), D.B.loop(), st)):
  +n = Nat.add(f0, n1)
  +d0 = ends.eq(Cr.Cir.exec(f0, D.B.body(), st), Cr.Cir.Out.next{u}, er, Unit{})
  +e1 = Equal.trans(Cr.Cir.Out, Cr.Cir.Out.next{u}, Cr.Cir.exec(f0, D.B.body(), st), Cr.Cir.exec(n, D.B.body(), st),
    Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f0, D.B.body(), st), Cr.Cir.Out.next{u}, er),
    D.mono(f0, n, D.B.body(), st, N.le_add_r(f0, n1), d0))
  +e2 = D.mono(n1, n, D.B.loop(), u, N.le_add_l(f0, n1), good.ends(o, Cr.Cir.exec(n1, D.B.loop(), u), g1))
  %e1 : D.Good(o, Cr.Cir.exec.then(_, v => Cr.Cir.exec(n, D.B.loop(), v)))
  %e2 : D.Good(o, _)
  g1

# a round that halts, from a term from which Eval reaches the bytes o: the
# loop gives them
def loop.halt(k: Nat, +ds: List<&2, Bk.Def>, +t: Bk.Term, -s: U32, +st2: Cr.Cir.State, +o: List<&2, Word(8n)>,
  e: {Pg.Program.result(ds, El.Eval.steps(k, ds, t)) == Some{o} : Maybe<&2, List<&2, Word(8n)>>},
  h: D.HR(ds, t, s, st2)) -> D.Good(o, Cr.Cir.Out.halt{s, st2}):
  match k:
    case 0n:
      match h:
        case Inl{x}:
          (e0, r) = x
          (es, er) = r
          (e0, D.mb.inj(List.reverse(&2, Word(8n), D.St.out(st2)), o,
            Equal.trans(Maybe<&2, List<&2, Word(8n)>>, Some{List.reverse(&2, Word(8n), D.St.out(st2))}, Pg.Program.result(ds, Some{t}), Some{o},
              Equal.sym(Maybe<&2, List<&2, Word(8n)>>, Pg.Program.result(ds, Some{t}), Some{List.reverse(&2, Word(8n), D.St.out(st2))}, er), e)))
        case Inr{x}:
          (e2, r) = x
          (es, er) = r
          Empty.absurd(D.Good(o, Cr.Cir.Out.halt{s, st2}), D.mb.ne(o,
            Equal.trans(Maybe<&2, List<&2, Word(8n)>>, None{}, Pg.Program.result(ds, Some{t}), Some{o},
              Equal.sym(Maybe<&2, List<&2, Word(8n)>>, Pg.Program.result(ds, Some{t}), None{}, er), e)))
    case 1n+(+j):
      match h:
        case Inl{x}:
          (e0, r) = x
          (es, er) = r
          Empty.absurd(D.Good(o, Cr.Cir.Out.halt{s, st2}), D.mb.ne(o,
            Equal.trans(Maybe<&2, List<&2, Word(8n)>>, None{}, Pg.Program.result(ds, El.Eval.steps(1n+j, ds, t)), Some{o},
              Equal.sym(Maybe<&2, List<&2, Word(8n)>>, Pg.Program.result(ds, El.Eval.steps(1n+j, ds, t)), None{}, none.after(j, ds, t, es)), e)))
        case Inr{x}:
          (e2, r) = x
          (es, er) = r
          Empty.absurd(D.Good(o, Cr.Cir.Out.halt{s, st2}), D.mb.ne(o,
            Equal.trans(Maybe<&2, List<&2, Word(8n)>>, None{}, Pg.Program.result(ds, El.Eval.steps(1n+j, ds, t)), Some{o},
              Equal.sym(Maybe<&2, List<&2, Word(8n)>>, Pg.Program.result(ds, El.Eval.steps(1n+j, ds, t)), None{}, none.after(j, ds, t, es)), e)))

# a step from a term from which Eval reaches the bytes o at once: none
def loop.step0(+ds: List<&2, Bk.Def>, +t: Bk.Term, +u: Bk.Term, -o: List<&2, Word(8n)>,
  e: {Pg.Program.result(ds, Some{t}) == Some{o} : Maybe<&2, List<&2, Word(8n)>>},
  es: {El.Eval.step(ds, t) == Some{u} : Maybe<Bk.Term>}) -> Empty:
  D.mb.ne(o, Equal.trans(Maybe<&2, List<&2, Word(8n)>>, None{}, Pg.Program.result(ds, Some{t}), Some{o},
    Equal.sym(Maybe<&2, List<&2, Word(8n)>>, Pg.Program.result(ds, Some{t}), None{},
      D.res.nv(ds, t, vals.of(El.Eval.vals(ds, t, False{}), ds, t, u, {==}, es))), e))

# when Eval reaches the bytes o from t within k steps, the loop gives them or
# runs out of memory, with some fuel: by induction on k, and on b, above the
# measure of the admin moves; r0 is the round with the fuel f0, that ends
def loop.done(k: Nat, b: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +st: Cr.Cir.State, +t: Bk.Term, +w: Nat, +o: List<&2, Word(8n)>, +hw: N.Le(1n+w, b),
  +e: {Pg.Program.result(ds, El.Eval.steps(k, ds, t)) == Some{o} : Maybe<&2, List<&2, Word(8n)>>},
  +f0: Nat, r0: Cr.Cir.Out, +er: {Cr.Cir.exec(f0, D.B.body(), st) == r0 : Cr.Cir.Out}, d0: D.Ends(r0),
  p0: D.Post(False{}, r0, s => D.Rnd(ds, ks, img, t, w, s), s => st2 => D.HR(ds, t, s, st2))) ->
  D.Ex(Nat, n => D.Good(o, Cr.Cir.exec(n, D.B.loop(), st))):
  match k:
    case 0n:
      match b:
        case 0n:
          Empty.absurd(D.Ex(Nat, n => D.Good(o, Cr.Cir.exec(n, D.B.loop(), st))), hw)
        case 1n+(+c):
          match r0:
            case Cr.Cir.Out.next{+u}:
              match p0:
                case Inl{+a}:
                  +w2 = D.adm.w(ds, ks, img, u, t, w, a)
                  +inv2 = D.adm.inv(ds, ks, img, u, t, w, a)
                  +lt = D.adm.lt(ds, ks, img, u, t, w, a)
                  +rd = round.done(ds, ks, img, u, t, w2, inv2)
                  +f1 = D.Ex.fst(Nat, f => D.Ends(Cr.Cir.exec(f, D.B.body(), u)), rd)
                  +ld = loop.done(0n, c, ds, ks, img, u, t, w2, o, N.le_trans(1n+w2, w, c, lt, hw), e, f1,
                    Cr.Cir.exec(f1, D.B.body(), u), {==}, D.Ex.snd(Nat, f => D.Ends(Cr.Cir.exec(f, D.B.body(), u)), rd),
                    round.post(f1, ds, ks, img, u, t, w2, inv2))
                  +n1 = D.Ex.fst(Nat, n => D.Good(o, Cr.Cir.exec(n, D.B.loop(), u)), ld)
                  (1n+Nat.add(f0, n1), next.fin(o, f0, n1, st, u, er, D.Ex.snd(Nat, n => D.Good(o, Cr.Cir.exec(n, D.B.loop(), u)), ld)))
                case Inr{+x}:
                  +v = D.stp.u(ds, ks, img, u, t, x)
                  +es = D.stp.es(ds, ks, img, u, t, x)
                  +w2 = D.stp.w(ds, ks, img, u, t, x)
                  +inv2 = D.stp.inv(ds, ks, img, u, t, x)
                  Empty.absurd(D.Ex(Nat, n => D.Good(o, Cr.Cir.exec(n, D.B.loop(), st))), loop.step0(ds, t, v, o, e, es))
            case Cr.Cir.Out.halt{+s, +st2}:
              (1n+f0, out.fin(o, f0, st, Cr.Cir.Out.halt{s, st2}, er, loop.halt(0n, ds, t, s, st2, o, e, p0)))
            case Cr.Cir.Out.out_of_memory{}:
              (1n+f0, out.fin(o, f0, st, Cr.Cir.Out.out_of_memory{}, er, Unit{}))
            case Cr.Cir.Out.trap{}:
              Empty.absurd(D.Ex(Nat, n => D.Good(o, Cr.Cir.exec(n, D.B.loop(), st))), p0)
            case Cr.Cir.Out.not_done{}:
              Empty.absurd(D.Ex(Nat, n => D.Good(o, Cr.Cir.exec(n, D.B.loop(), st))), d0)
    case 1n+(+j):
      match b:
        case 0n:
          Empty.absurd(D.Ex(Nat, n => D.Good(o, Cr.Cir.exec(n, D.B.loop(), st))), hw)
        case 1n+(+c):
          match r0:
            case Cr.Cir.Out.next{+u}:
              match p0:
                case Inl{+a}:
                  +w2 = D.adm.w(ds, ks, img, u, t, w, a)
                  +inv2 = D.adm.inv(ds, ks, img, u, t, w, a)
                  +lt = D.adm.lt(ds, ks, img, u, t, w, a)
                  +rd = round.done(ds, ks, img, u, t, w2, inv2)
                  +f1 = D.Ex.fst(Nat, f => D.Ends(Cr.Cir.exec(f, D.B.body(), u)), rd)
                  +ld = loop.done(1n+j, c, ds, ks, img, u, t, w2, o, N.le_trans(1n+w2, w, c, lt, hw), e, f1,
                    Cr.Cir.exec(f1, D.B.body(), u), {==}, D.Ex.snd(Nat, f => D.Ends(Cr.Cir.exec(f, D.B.body(), u)), rd),
                    round.post(f1, ds, ks, img, u, t, w2, inv2))
                  +n1 = D.Ex.fst(Nat, n => D.Good(o, Cr.Cir.exec(n, D.B.loop(), u)), ld)
                  (1n+Nat.add(f0, n1), next.fin(o, f0, n1, st, u, er, D.Ex.snd(Nat, n => D.Good(o, Cr.Cir.exec(n, D.B.loop(), u)), ld)))
                case Inr{+x}:
                  +v = D.stp.u(ds, ks, img, u, t, x)
                  +es = D.stp.es(ds, ks, img, u, t, x)
                  +w2 = D.stp.w(ds, ks, img, u, t, x)
                  +inv2 = D.stp.inv(ds, ks, img, u, t, x)
                  +rd = round.done(ds, ks, img, u, v, w2, inv2)
                  +f1 = D.Ex.fst(Nat, f => D.Ends(Cr.Cir.exec(f, D.B.body(), u)), rd)
                  +ld = loop.done(j, 1n+w2, ds, ks, img, u, v, w2, o, N.le_refl(1n+w2), res.step(j, ds, t, v, Some{o}, es, e), f1,
                    Cr.Cir.exec(f1, D.B.body(), u), {==}, D.Ex.snd(Nat, f => D.Ends(Cr.Cir.exec(f, D.B.body(), u)), rd),
                    round.post(f1, ds, ks, img, u, v, w2, inv2))
                  +n1 = D.Ex.fst(Nat, n => D.Good(o, Cr.Cir.exec(n, D.B.loop(), u)), ld)
                  (1n+Nat.add(f0, n1), next.fin(o, f0, n1, st, u, er, D.Ex.snd(Nat, n => D.Good(o, Cr.Cir.exec(n, D.B.loop(), u)), ld)))
            case Cr.Cir.Out.halt{+s, +st2}:
              (1n+f0, out.fin(o, f0, st, Cr.Cir.Out.halt{s, st2}, er, loop.halt(1n+j, ds, t, s, st2, o, e, p0)))
            case Cr.Cir.Out.out_of_memory{}:
              (1n+f0, out.fin(o, f0, st, Cr.Cir.Out.out_of_memory{}, er, Unit{}))
            case Cr.Cir.Out.trap{}:
              Empty.absurd(D.Ex(Nat, n => D.Good(o, Cr.Cir.exec(n, D.B.loop(), st))), p0)
            case Cr.Cir.Out.not_done{}:
              Empty.absurd(D.Ex(Nat, n => D.Good(o, Cr.Cir.exec(n, D.B.loop(), st))), d0)

# the loop, from a state of the invariant
def loop.start(k: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +st: Cr.Cir.State, +t: Bk.Term, +w: Nat, +o: List<&2, Word(8n)>, +inv: D.Inv(ds, ks, img, st, t, w),
  +e: {Pg.Program.result(ds, El.Eval.steps(k, ds, t)) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}) ->
  D.Ex(Nat, n => D.Good(o, Cr.Cir.exec(n, D.B.loop(), st))):
  +rd = round.done(ds, ks, img, st, t, w, inv)
  +f0 = D.Ex.fst(Nat, f => D.Ends(Cr.Cir.exec(f, D.B.body(), st)), rd)
  loop.done(k, 1n+w, ds, ks, img, st, t, w, o, N.le_refl(1n+w), e, f0, Cr.Cir.exec(f0, D.B.body(), st), {==},
    D.Ex.snd(Nat, f => D.Ends(Cr.Cir.exec(f, D.B.body(), st)), rd), round.post(f0, ds, ks, img, st, t, w, inv))

def res.alloced(r: Maybe<&2, U32>, fuel: Nat, prog: Cr.Cir.Stmt, +regs: Nat, +cells: List<&2, Cr.Cir.Cell>, +k: U32,
  +len: U32, +lim: U32, +i: List<&2, Word(8n)>, +m: U32, -P: Wa.Wasm.Outcome -> Type, po: P(Wa.Wasm.Outcome.out_of_memory{}),
  ek: {k == Cr.Wasm.encode.len(Cr.Cir.Cell, cells) : U32},
  em: {U32.is_le(Cr.Cir.pages(Cr.Cir.input.at(k)), m) == True{} : Bool},
  elim: {lim == Wa.Wasm.min(m, 65536) : U32},
  el: {Wa.Wasm.length32(i) == Some{len} : Maybe<&2, U32>},
  er: {Cr.Cir.alloc.pages(k, len, Cr.Cir.pages(Cr.Cir.input.at(k)), lim) == r : Maybe<&2, U32>},
  g: @k2: U32 -> @len2: U32 -> @p2: U32 -> @lim2: U32 -> @first2: U32 -> D.Start(cells, i, m, k2, len2, p2, lim2, first2) ->
    P(Cr.Cir.ended(Cr.Cir.exec(fuel, prog, D.St0(regs, cells, first2, k2, p2, lim2, i))))) ->
  P(Cr.Cir.result.alloced(r, fuel, prog, regs, cells, k, U32.add(Cr.Cir.input.at(k), len), lim, i)):
  match r:
    case None{}:
      po
    case Some{+p}:
      g(k, len, p, lim, Cr.Cir.first(k, U32.add(Cr.Cir.input.at(k), len)), (ek, (em, (elim, (el, (er, {==}))))))

def res.sized(nl: Maybe<&2, U32>, fuel: Nat, prog: Cr.Cir.Stmt, +regs: Nat, +cells: List<&2, Cr.Cir.Cell>, +k: U32,
  +lim: U32, +i: List<&2, Word(8n)>, +m: U32, -P: Wa.Wasm.Outcome -> Type, po: P(Wa.Wasm.Outcome.out_of_memory{}),
  ek: {k == Cr.Wasm.encode.len(Cr.Cir.Cell, cells) : U32},
  em: {U32.is_le(Cr.Cir.pages(Cr.Cir.input.at(k)), m) == True{} : Bool},
  elim: {lim == Wa.Wasm.min(m, 65536) : U32},
  el: {Wa.Wasm.length32(i) == nl : Maybe<&2, U32>},
  g: @k2: U32 -> @len2: U32 -> @p2: U32 -> @lim2: U32 -> @first2: U32 -> D.Start(cells, i, m, k2, len2, p2, lim2, first2) ->
    P(Cr.Cir.ended(Cr.Cir.exec(fuel, prog, D.St0(regs, cells, first2, k2, p2, lim2, i))))) ->
  P(Cr.Cir.result.sized(nl, fuel, prog, regs, cells, k, Cr.Cir.pages(Cr.Cir.input.at(k)), lim, i)):
  match nl:
    case None{}:
      po
    case Some{+len}:
      res.alloced(Cr.Cir.alloc.pages(k, len, Cr.Cir.pages(Cr.Cir.input.at(k)), lim), fuel, prog, regs, cells, k, len, lim, i, m,
        P, po, ek, em, elim, el, {==}, g)

def res.memory(ok: Bool, fuel: Nat, prog: Cr.Cir.Stmt, +regs: Nat, +cells: List<&2, Cr.Cir.Cell>, +k: U32,
  +lim: U32, +i: List<&2, Word(8n)>, +m: U32, -P: Wa.Wasm.Outcome -> Type, po: P(Wa.Wasm.Outcome.out_of_memory{}),
  ek: {k == Cr.Wasm.encode.len(Cr.Cir.Cell, cells) : U32},
  em: {U32.is_le(Cr.Cir.pages(Cr.Cir.input.at(k)), m) == ok : Bool},
  elim: {lim == Wa.Wasm.min(m, 65536) : U32},
  g: @k2: U32 -> @len2: U32 -> @p2: U32 -> @lim2: U32 -> @first2: U32 -> D.Start(cells, i, m, k2, len2, p2, lim2, first2) ->
    P(Cr.Cir.ended(Cr.Cir.exec(fuel, prog, D.St0(regs, cells, first2, k2, p2, lim2, i))))) ->
  P(Cr.Cir.result.memory(ok, fuel, prog, regs, cells, k, Cr.Cir.pages(Cr.Cir.input.at(k)), lim, i)):
  match ok:
    case False{}:
      po
    case True{}:
      res.sized(Wa.Wasm.length32(i), fuel, prog, regs, cells, k, lim, i, m, P, po, ek, em, elim, {==}, g)

# what holds of every run from the start, and of out of memory, holds of
# Cir.result
def res.on(fuel: Nat, prog: Cr.Cir.Stmt, +regs: Nat, +cells: List<&2, Cr.Cir.Cell>, +i: List<&2, Word(8n)>, +m: U32,
  -P: Wa.Wasm.Outcome -> Type, po: P(Wa.Wasm.Outcome.out_of_memory{}),
  g: @k2: U32 -> @len2: U32 -> @p2: U32 -> @lim2: U32 -> @first2: U32 -> D.Start(cells, i, m, k2, len2, p2, lim2, first2) ->
    P(Cr.Cir.ended(Cr.Cir.exec(fuel, prog, D.St0(regs, cells, first2, k2, p2, lim2, i))))) ->
  P(Cr.Cir.result(fuel, prog, regs, cells, i, m)):
  res.memory(U32.is_le(Cr.Cir.pages(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), m), fuel, prog, regs, cells,
    Cr.Wasm.encode.len(Cr.Cir.Cell, cells), Wa.Wasm.min(m, 65536), i, m, P, po, {==}, {==}, {==}, g)

def rex.alloced(r: Maybe<&2, U32>, prog: Cr.Cir.Stmt, +regs: Nat, +cells: List<&2, Cr.Cir.Cell>, +k: U32,
  +len: U32, +lim: U32, +i: List<&2, Word(8n)>, +m: U32, -P: Wa.Wasm.Outcome -> Type, po: P(Wa.Wasm.Outcome.out_of_memory{}),
  ek: {k == Cr.Wasm.encode.len(Cr.Cir.Cell, cells) : U32},
  em: {U32.is_le(Cr.Cir.pages(Cr.Cir.input.at(k)), m) == True{} : Bool},
  elim: {lim == Wa.Wasm.min(m, 65536) : U32},
  el: {Wa.Wasm.length32(i) == Some{len} : Maybe<&2, U32>},
  er: {Cr.Cir.alloc.pages(k, len, Cr.Cir.pages(Cr.Cir.input.at(k)), lim) == r : Maybe<&2, U32>},
  g: @k2: U32 -> @len2: U32 -> @p2: U32 -> @lim2: U32 -> @first2: U32 -> D.Start(cells, i, m, k2, len2, p2, lim2, first2) ->
    &n: Nat -> P(Cr.Cir.ended(Cr.Cir.exec(n, prog, D.St0(regs, cells, first2, k2, p2, lim2, i))))) ->
  &n: Nat -> P(Cr.Cir.result.alloced(r, n, prog, regs, cells, k, U32.add(Cr.Cir.input.at(k), len), lim, i)):
  match r:
    case None{}:
      (0n, po)
    case Some{+p}:
      g(k, len, p, lim, Cr.Cir.first(k, U32.add(Cr.Cir.input.at(k), len)), (ek, (em, (elim, (el, (er, {==}))))))

def rex.sized(nl: Maybe<&2, U32>, prog: Cr.Cir.Stmt, +regs: Nat, +cells: List<&2, Cr.Cir.Cell>, +k: U32,
  +lim: U32, +i: List<&2, Word(8n)>, +m: U32, -P: Wa.Wasm.Outcome -> Type, po: P(Wa.Wasm.Outcome.out_of_memory{}),
  ek: {k == Cr.Wasm.encode.len(Cr.Cir.Cell, cells) : U32},
  em: {U32.is_le(Cr.Cir.pages(Cr.Cir.input.at(k)), m) == True{} : Bool},
  elim: {lim == Wa.Wasm.min(m, 65536) : U32},
  el: {Wa.Wasm.length32(i) == nl : Maybe<&2, U32>},
  g: @k2: U32 -> @len2: U32 -> @p2: U32 -> @lim2: U32 -> @first2: U32 -> D.Start(cells, i, m, k2, len2, p2, lim2, first2) ->
    &n: Nat -> P(Cr.Cir.ended(Cr.Cir.exec(n, prog, D.St0(regs, cells, first2, k2, p2, lim2, i))))) ->
  &n: Nat -> P(Cr.Cir.result.sized(nl, n, prog, regs, cells, k, Cr.Cir.pages(Cr.Cir.input.at(k)), lim, i)):
  match nl:
    case None{}:
      (0n, po)
    case Some{+len}:
      rex.alloced(Cr.Cir.alloc.pages(k, len, Cr.Cir.pages(Cr.Cir.input.at(k)), lim), prog, regs, cells, k, len, lim, i, m,
        P, po, ek, em, elim, el, {==}, g)

def rex.memory(ok: Bool, prog: Cr.Cir.Stmt, +regs: Nat, +cells: List<&2, Cr.Cir.Cell>, +k: U32,
  +lim: U32, +i: List<&2, Word(8n)>, +m: U32, -P: Wa.Wasm.Outcome -> Type, po: P(Wa.Wasm.Outcome.out_of_memory{}),
  ek: {k == Cr.Wasm.encode.len(Cr.Cir.Cell, cells) : U32},
  em: {U32.is_le(Cr.Cir.pages(Cr.Cir.input.at(k)), m) == ok : Bool},
  elim: {lim == Wa.Wasm.min(m, 65536) : U32},
  g: @k2: U32 -> @len2: U32 -> @p2: U32 -> @lim2: U32 -> @first2: U32 -> D.Start(cells, i, m, k2, len2, p2, lim2, first2) ->
    &n: Nat -> P(Cr.Cir.ended(Cr.Cir.exec(n, prog, D.St0(regs, cells, first2, k2, p2, lim2, i))))) ->
  &n: Nat -> P(Cr.Cir.result.memory(ok, n, prog, regs, cells, k, Cr.Cir.pages(Cr.Cir.input.at(k)), lim, i)):
  match ok:
    case False{}:
      (0n, po)
    case True{}:
      rex.sized(Wa.Wasm.length32(i), prog, regs, cells, k, lim, i, m, P, po, ek, em, elim, {==}, g)

# a fuel for each run from the start gives one for Cir.result, which runs out
# of memory or runs from the same start with any fuel
def res.ex(prog: Cr.Cir.Stmt, +regs: Nat, +cells: List<&2, Cr.Cir.Cell>, +i: List<&2, Word(8n)>, +m: U32,
  -P: Wa.Wasm.Outcome -> Type, po: P(Wa.Wasm.Outcome.out_of_memory{}),
  g: @k2: U32 -> @len2: U32 -> @p2: U32 -> @lim2: U32 -> @first2: U32 -> D.Start(cells, i, m, k2, len2, p2, lim2, first2) ->
    &n: Nat -> P(Cr.Cir.ended(Cr.Cir.exec(n, prog, D.St0(regs, cells, first2, k2, p2, lim2, i))))) ->
  &n: Nat -> P(Cr.Cir.result(n, prog, regs, cells, i, m)):
  rex.memory(U32.is_le(Cr.Cir.pages(Cr.Cir.input.at(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))), m), prog, regs, cells,
    Cr.Wasm.encode.len(Cr.Cir.Cell, cells), Wa.Wasm.min(m, 65536), i, m, P, po, {==}, {==}, {==}, g)

# The machine gives what Eval gives
# ---------------------------------

def run.loop(+n: Nat, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +st2: Cr.Cir.State,
  q: D.Ex(Nat, w => D.Inv(ds, T.tm.names(ds), T.tm.img(ds), st2, Pg.Program.start(i), w))) ->
  D.Post(False{}, Cr.Cir.exec(n, Cr.Cir.Stmt.seq{D.B.loop(), Cr.Cir.Stmt.nop{}}, st2), st => Unit,
    s2 => st3 => D.HE(ds, Pg.Program.start(i), s2, st3)):
  (w, inv) = q
  D.post.seq(n, False{}, D.B.loop(), Cr.Cir.Stmt.nop{}, st2, s => Empty, s => Unit, s2 => st3 => D.HE(ds, Pg.Program.start(i), s2, st3),
    s2 => st3 => D.HE(ds, Pg.Program.start(i), s2, st3),
    loop.post(n, ds, T.tm.names(ds), T.tm.img(ds), st2, Pg.Program.start(i), w, inv),
    s2 => st3 => h => h, st3 => h => Empty.absurd(D.Post(False{}, Cr.Cir.exec(n, Cr.Cir.Stmt.nop{}, st3), s => Unit,
      s2 => st4 => D.HE(ds, Pg.Program.start(i), s2, st4)), h))

def run.rest(+n: Nat, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +st1: Cr.Cir.State, q1: D.InvIn(ds, i, st1)) ->
  D.Post(False{}, Cr.Cir.exec(n, D.B.rest(), st1), st => Unit, s2 => st2 => D.HE(ds, Pg.Program.start(i), s2, st2)):
  (len, ex) = q1
  D.post.seq(n, False{}, Mc.M.set(Mc.R.mode(), Mc.M.c(0)), Cr.Cir.Stmt.seq{D.B.loop(), Cr.Cir.Stmt.nop{}}, st1,
    st2 => D.Ex(Nat, w => D.Inv(ds, T.tm.names(ds), T.tm.img(ds), st2, Pg.Program.start(i), w)), st => Unit,
    s2 => st2 => Empty, s2 => st2 => D.HE(ds, Pg.Program.start(i), s2, st2),
    (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec(n, Mc.M.set(Mc.R.mode(), Mc.M.c(0)), st1), Cr.Cir.Out.next{D.Mode0(st1)}, D.setmode(n, st1, len)) :
      D.Post(False{}, _, st2 => D.Ex(Nat, w => D.Inv(ds, T.tm.names(ds), T.tm.img(ds), st2, Pg.Program.start(i), w)), s2 => st2 => Empty);
     ex),
    s2 => st2 => h => Empty.absurd(D.HE(ds, Pg.Program.start(i), s2, st2), h),
    st2 => q2 => run.loop(n, ds, i, st2, q2))

# a run of Mach.code from the start halts only as HE says, from Program.start
def run.post(+n: Nat, +p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +m: U32, +k: U32, +len: U32,
  +pg: U32, +lim: U32, +first: U32,
  rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  small: {Mc.Img.small(p, 0) == True{} : Bool},
  s: D.Start(Mc.Img.cells(ds), i, m, k, len, pg, lim, first)) ->
  D.Post(False{}, Cr.Cir.exec(n, Mc.Mach.code(), D.St0(Mc.Mach.regs(), Mc.Img.cells(ds), first, k, pg, lim, i)), st => Unit,
    s2 => st2 => D.HE(ds, Pg.Program.start(i), s2, st2)):
  D.post.seq(n, False{}, Mc.M.input(), D.B.rest(), D.St0(Mc.Mach.regs(), Mc.Img.cells(ds), first, k, pg, lim, i),
    st => D.InvIn(ds, i, st), st => Unit, s2 => st2 => Empty, s2 => st2 => D.HE(ds, Pg.Program.start(i), s2, st2),
    input.post(n, p, ds, i, m, k, len, pg, lim, first, rd, small, s),
    s2 => st2 => h => Empty.absurd(D.HE(ds, Pg.Program.start(i), s2, st2), h),
    st1 => q1 => run.rest(n, ds, i, st1, q1))

# the outcomes that are no trap
def oc.nt(x: Wa.Wasm.Outcome) -> Type:
  match x:
    case Wa.Wasm.Outcome.result{_}:
      Unit
    case Wa.Wasm.Outcome.out_of_memory{}:
      Unit
    case Wa.Wasm.Outcome.no_result{}:
      Unit
    case Wa.Wasm.Outcome.unsupported{}:
      Unit
    case Wa.Wasm.Outcome.trap{}:
      Empty
    case Wa.Wasm.Outcome.not_done{}:
      Unit

# the outcomes that are no result
def oc.nr(x: Wa.Wasm.Outcome) -> Type:
  match x:
    case Wa.Wasm.Outcome.result{_}:
      Empty
    case Wa.Wasm.Outcome.out_of_memory{}:
      Unit
    case Wa.Wasm.Outcome.no_result{}:
      Unit
    case Wa.Wasm.Outcome.unsupported{}:
      Unit
    case Wa.Wasm.Outcome.trap{}:
      Unit
    case Wa.Wasm.Outcome.not_done{}:
      Unit

def oc.get(x: Wa.Wasm.Outcome, d: List<&2, Word(8n)>) -> List<&2, Word(8n)>:
  match x:
    case Wa.Wasm.Outcome.result{y}:
      y
    case _:
      d

# result is one to one
def oc.inj(+a: List<&2, Word(8n)>, -b: List<&2, Word(8n)>, e: {Wa.Wasm.Outcome.result{a} == Wa.Wasm.Outcome.result{b} : Wa.Wasm.Outcome}) ->
  {a == b : List<&2, Word(8n)>}:
  Equal.cong(Wa.Wasm.Outcome, List<&2, Word(8n)>, x => oc.get(x, a), Wa.Wasm.Outcome.result{a}, Wa.Wasm.Outcome.result{b}, e)

# a run that halts with 0 gives its output as the host reads it
def ended0(-s: U32, -fits: Bool, +out: List<&2, Word(8n)>, e0: {s == 0 : U32}) ->
  {Cr.Cir.ended.halt(U32.is_eq(s, 0), U32.is_eq(s, 1), U32.is_eq(s, 2), fits, out) == Cr.Cir.ended.output(fits, out) : Wa.Wasm.Outcome}:
  %Equal.sym(U32, s, 0, e0) : {Cr.Cir.ended.halt(U32.is_eq(_, 0), U32.is_eq(_, 1), U32.is_eq(_, 2), fits, out) == Cr.Cir.ended.output(fits, out) : Wa.Wasm.Outcome}
  {==}

# a run that halts with 2 gives no result
def ended2(-s: U32, -fits: Bool, +out: List<&2, Word(8n)>, e2: {s == 2 : U32}) ->
  {Cr.Cir.ended.halt(U32.is_eq(s, 0), U32.is_eq(s, 1), U32.is_eq(s, 2), fits, out) == Wa.Wasm.Outcome.no_result{} : Wa.Wasm.Outcome}:
  %Equal.sym(U32, s, 2, e2) : {Cr.Cir.ended.halt(U32.is_eq(_, 0), U32.is_eq(_, 1), U32.is_eq(_, 2), fits, out) == Wa.Wasm.Outcome.no_result{} : Wa.Wasm.Outcome}
  {==}

# an output that the host reads as the result x is its bytes: one that does
# not fit gives a trap
def output.inj(fits: Bool, +out: List<&2, Word(8n)>, -x: List<&2, Word(8n)>,
  e: {Cr.Cir.ended.output(fits, out) == Wa.Wasm.Outcome.result{x} : Wa.Wasm.Outcome}) ->
  {List.reverse(&2, Word(8n), out) == x : List<&2, Word(8n)>}:
  match fits:
    case True{}:
      oc.inj(List.reverse(&2, Word(8n), out), x, e)
    case False{}:
      Empty.absurd({List.reverse(&2, Word(8n), out) == x : List<&2, Word(8n)>}, (%e : oc.nr(_); Unit{}))

# at halt 0, the output fits in the memory, as the host checks (Cir.ended)
def HaltFits(o: Cr.Cir.Out) -> Type:
  match o:
    case Cr.Cir.Out.halt{s, Cr.Cir.State{_, _, nx, _, _, pg, _, _, _, on}}:
      {s == 0 : U32} -> {Wa.Wasm.fits(pg, Cr.Cir.at(nx), on) == True{} : Bool}
    case _:
      Unit

# an outcome that fits (CF.FitsOut) has its output in the memory at halt 0
def halt.fits(o: Cr.Cir.Out, h: CF.FitsOut(o)) -> HaltFits(o):
  match o:
    case Cr.Cir.Out.next{st}:
      Unit{}
    case Cr.Cir.Out.halt{s, Cr.Cir.State{rg, m, +nx, fi, im, +pg, lim, inp, out, +on}}:
      e0 => CF.fits.wasm(nx, pg, on, h)
    case Cr.Cir.Out.out_of_memory{}:
      Unit{}
    case Cr.Cir.Out.trap{}:
      Unit{}
    case Cr.Cir.Out.not_done{}:
      Unit{}

# a run of Mach.code from the start has its output in the memory at halt 0:
# the start's pend register holds 0, so the run fits (CF.fits.code), and what
# fits passes the host's check (CF.fits.wasm, in halt.fits)
def code.fits(+n: Nat, +cells: List<&2, Cr.Cir.Cell>, +first: U32, +k: U32, +pg: U32, +lim: U32, +i: List<&2, Word(8n)>) ->
  HaltFits(Cr.Cir.exec(n, Mc.Mach.code(), D.St0(Mc.Mach.regs(), cells, first, k, pg, lim, i))):
  halt.fits(Cr.Cir.exec(n, Mc.Mach.code(), D.St0(Mc.Mach.regs(), cells, first, k, pg, lim, i)),
    CF.fits.code(n, D.St0(Mc.Mach.regs(), cells, first, k, pg, lim, i), {==}))

# a run that halts only as HE says, with its output in the memory at halt 0,
# never traps
def safe.end(o: Cr.Cir.Out, -ds: List<&2, Bk.Def>, -t: Bk.Term,
  h: D.Post(False{}, o, st => Unit, s => st2 => D.HE(ds, t, s, st2)), hf: HaltFits(o)) ->
  {Cr.Cir.ended(o) != Wa.Wasm.Outcome.trap{} : Wa.Wasm.Outcome}:
  match o:
    case Cr.Cir.Out.next{st}:
      e => (%e : oc.nt(_); Unit{})
    case Cr.Cir.Out.halt{s, Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, +out, outn}}:
      match h:
        case Inl{x}:
          (+e0, r) = x
          %Equal.sym(Wa.Wasm.Outcome, Cr.Cir.ended.halt(U32.is_eq(s, 0), U32.is_eq(s, 1), U32.is_eq(s, 2), Wa.Wasm.fits(pg, Cr.Cir.at(nx), outn), out),
            Cr.Cir.ended.output(Wa.Wasm.fits(pg, Cr.Cir.at(nx), outn), out), ended0(s, Wa.Wasm.fits(pg, Cr.Cir.at(nx), outn), out, e0)) :
            {_ != Wa.Wasm.Outcome.trap{} : Wa.Wasm.Outcome}
          %Equal.sym(Bool, Wa.Wasm.fits(pg, Cr.Cir.at(nx), outn), True{}, hf(e0)) : {Cr.Cir.ended.output(_, out) != Wa.Wasm.Outcome.trap{} : Wa.Wasm.Outcome}
          e => (%e : oc.nt(_); Unit{})
        case Inr{x}:
          (e2, r) = x
          %Equal.sym(Wa.Wasm.Outcome, Cr.Cir.ended.halt(U32.is_eq(s, 0), U32.is_eq(s, 1), U32.is_eq(s, 2), Wa.Wasm.fits(pg, Cr.Cir.at(nx), outn), out),
            Wa.Wasm.Outcome.no_result{}, ended2(s, Wa.Wasm.fits(pg, Cr.Cir.at(nx), outn), out, e2)) : {_ != Wa.Wasm.Outcome.trap{} : Wa.Wasm.Outcome}
          e => (%e : oc.nt(_); Unit{})
    case Cr.Cir.Out.out_of_memory{}:
      e => (%e : oc.nt(_); Unit{})
    case Cr.Cir.Out.trap{}:
      Empty.absurd({Wa.Wasm.Outcome.trap{} != Wa.Wasm.Outcome.trap{} : Wa.Wasm.Outcome}, h)
    case Cr.Cir.Out.not_done{}:
      e => (%e : oc.nt(_); Unit{})

# a result of a run that halts only as HE says is one that Eval reaches
def sound.end(o: Cr.Cir.Out, +ds: List<&2, Bk.Def>, +t: Bk.Term, +x: List<&2, Word(8n)>,
  h: D.Post(False{}, o, st => Unit, s => st2 => D.HE(ds, t, s, st2)),
  e: {Cr.Cir.ended(o) == Wa.Wasm.Outcome.result{x} : Wa.Wasm.Outcome}) ->
  &k: Nat -> {Pg.Program.result(ds, El.Eval.steps(k, ds, t)) == Some{x} : Maybe<&2, List<&2, Word(8n)>>}:
  match o:
    case Cr.Cir.Out.next{st}:
      Empty.absurd(&k: Nat -> {Pg.Program.result(ds, El.Eval.steps(k, ds, t)) == Some{x} : Maybe<&2, List<&2, Word(8n)>>},
        (%e : oc.nr(_); Unit{}))
    case Cr.Cir.Out.halt{s, Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, +out, outn}}:
      match h:
        case Inl{y}:
          (e0, r) = y
          (+k, ek) = r
          +rx = output.inj(Wa.Wasm.fits(pg, Cr.Cir.at(nx), outn), out, x,
            Equal.trans(Wa.Wasm.Outcome, Cr.Cir.ended.output(Wa.Wasm.fits(pg, Cr.Cir.at(nx), outn), out),
              Cr.Cir.ended.halt(U32.is_eq(s, 0), U32.is_eq(s, 1), U32.is_eq(s, 2), Wa.Wasm.fits(pg, Cr.Cir.at(nx), outn), out), Wa.Wasm.Outcome.result{x},
              Equal.sym(Wa.Wasm.Outcome, Cr.Cir.ended.halt(U32.is_eq(s, 0), U32.is_eq(s, 1), U32.is_eq(s, 2), Wa.Wasm.fits(pg, Cr.Cir.at(nx), outn), out),
                Cr.Cir.ended.output(Wa.Wasm.fits(pg, Cr.Cir.at(nx), outn), out), ended0(s, Wa.Wasm.fits(pg, Cr.Cir.at(nx), outn), out, e0)), e))
          (k, (%rx :
            {Pg.Program.result(ds, El.Eval.steps(k, ds, t)) == Some{_} : Maybe<&2, List<&2, Word(8n)>>}; ek))
        case Inr{y}:
          (e2, g) = y
          Empty.absurd(&k: Nat -> {Pg.Program.result(ds, El.Eval.steps(k, ds, t)) == Some{x} : Maybe<&2, List<&2, Word(8n)>>},
            (%Equal.trans(Wa.Wasm.Outcome, Wa.Wasm.Outcome.no_result{},
              Cr.Cir.ended.halt(U32.is_eq(s, 0), U32.is_eq(s, 1), U32.is_eq(s, 2), Wa.Wasm.fits(pg, Cr.Cir.at(nx), outn), out), Wa.Wasm.Outcome.result{x},
              Equal.sym(Wa.Wasm.Outcome, Cr.Cir.ended.halt(U32.is_eq(s, 0), U32.is_eq(s, 1), U32.is_eq(s, 2), Wa.Wasm.fits(pg, Cr.Cir.at(nx), outn), out),
                Wa.Wasm.Outcome.no_result{}, ended2(s, Wa.Wasm.fits(pg, Cr.Cir.at(nx), outn), out, e2)), e) : oc.nr(_); Unit{}))
    case Cr.Cir.Out.out_of_memory{}:
      Empty.absurd(&k: Nat -> {Pg.Program.result(ds, El.Eval.steps(k, ds, t)) == Some{x} : Maybe<&2, List<&2, Word(8n)>>},
        (%e : oc.nr(_); Unit{}))
    case Cr.Cir.Out.trap{}:
      Empty.absurd(&k: Nat -> {Pg.Program.result(ds, El.Eval.steps(k, ds, t)) == Some{x} : Maybe<&2, List<&2, Word(8n)>>}, h)
    case Cr.Cir.Out.not_done{}:
      Empty.absurd(&k: Nat -> {Pg.Program.result(ds, El.Eval.steps(k, ds, t)) == Some{x} : Maybe<&2, List<&2, Word(8n)>>},
        (%e : oc.nr(_); Unit{}))

# a run that gives the bytes o, or runs out of memory, ends so, when its
# output is in the memory at halt 0
def good.end(+o: List<&2, Word(8n)>, r: Cr.Cir.Out, g: D.Good(o, r), hf: HaltFits(r)) ->
  Or({Cr.Cir.ended(r) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome}, {Cr.Cir.ended(r) == Wa.Wasm.Outcome.out_of_memory{} : Wa.Wasm.Outcome}):
  match r:
    case Cr.Cir.Out.next{st}:
      Empty.absurd(Or({Wa.Wasm.Outcome.no_result{} == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome},
        {Wa.Wasm.Outcome.no_result{} == Wa.Wasm.Outcome.out_of_memory{} : Wa.Wasm.Outcome}), g)
    case Cr.Cir.Out.halt{s, Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, +out, outn}}:
      (+e0, eo) = g
      Inl{Equal.trans(Wa.Wasm.Outcome, Cr.Cir.ended.halt(U32.is_eq(s, 0), U32.is_eq(s, 1), U32.is_eq(s, 2), Wa.Wasm.fits(pg, Cr.Cir.at(nx), outn), out),
        Cr.Cir.ended.output(Wa.Wasm.fits(pg, Cr.Cir.at(nx), outn), out), Wa.Wasm.Outcome.result{o}, ended0(s, Wa.Wasm.fits(pg, Cr.Cir.at(nx), outn), out, e0),
        (%Equal.sym(Bool, Wa.Wasm.fits(pg, Cr.Cir.at(nx), outn), True{}, hf(e0)) : {Cr.Cir.ended.output(_, out) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome};
          Equal.cong(List<&2, Word(8n)>, Wa.Wasm.Outcome, y => Wa.Wasm.Outcome.result{y}, List.reverse(&2, Word(8n), out), o, eo)))}
    case Cr.Cir.Out.out_of_memory{}:
      Inr{{==}}
    case Cr.Cir.Out.trap{}:
      Empty.absurd(Or({Wa.Wasm.Outcome.trap{} == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome},
        {Wa.Wasm.Outcome.trap{} == Wa.Wasm.Outcome.out_of_memory{} : Wa.Wasm.Outcome}), g)
    case Cr.Cir.Out.not_done{}:
      Empty.absurd(Or({Wa.Wasm.Outcome.not_done{} == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome},
        {Wa.Wasm.Outcome.not_done{} == Wa.Wasm.Outcome.out_of_memory{} : Wa.Wasm.Outcome}), g)

# M.input with the fuel f1, then the loop with n2, are Mach.code with
# 1 + f1 + n2
def run.fin(+o: List<&2, Word(8n)>, +f1: Nat, +n2: Nat, +st0: Cr.Cir.State, +st1: Cr.Cir.State,
  +er1: {Cr.Cir.exec(f1, Mc.M.input(), st0) == Cr.Cir.Out.next{st1} : Cr.Cir.Out},
  +len: {List.length(&2, U32, D.St.regs(st1)) == 63n : Nat},
  +g2: D.Good(o, Cr.Cir.exec(n2, D.B.loop(), D.Mode0(st1)))) -> D.Good(o, Cr.Cir.exec(1n+Nat.add(f1, n2), Mc.Mach.code(), st0)):
  +n = {1n+Nat.add(f1, n2) : Nat}
  +d1 = ends.eq(Cr.Cir.exec(f1, Mc.M.input(), st0), Cr.Cir.Out.next{st1}, er1, Unit{})
  +e1 = Equal.trans(Cr.Cir.Out, Cr.Cir.Out.next{st1}, Cr.Cir.exec(f1, Mc.M.input(), st0), Cr.Cir.exec(n, Mc.M.input(), st0),
    Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f1, Mc.M.input(), st0), Cr.Cir.Out.next{st1}, er1),
    D.mono(f1, n, Mc.M.input(), st0, N.le_succ(f1, Nat.add(f1, n2), N.le_add_r(f1, n2)), d1))
  +e2 = Equal.sym(Cr.Cir.Out, Cr.Cir.exec(n, Mc.M.set(Mc.R.mode(), Mc.M.c(0)), st1), Cr.Cir.Out.next{D.Mode0(st1)}, D.setmode(n, st1, len))
  +e3 = D.mono(n2, n, D.B.loop(), D.Mode0(st1), N.le_succ(n2, Nat.add(f1, n2), N.le_add_l(f1, n2)),
    good.ends(o, Cr.Cir.exec(n2, D.B.loop(), D.Mode0(st1)), g2))
  %e1 : D.Good(o, Cr.Cir.exec.then(_, s1 => Cr.Cir.exec(n, D.B.rest(), s1)))
  %e2 : D.Good(o, Cr.Cir.exec.then(_, s2 => Cr.Cir.exec(n, Cr.Cir.Stmt.seq{D.B.loop(), Cr.Cir.Stmt.nop{}}, s2)))
  %e3 : D.Good(o, Cr.Cir.exec.then(_, s3 => Cr.Cir.exec(n, Cr.Cir.Stmt.nop{}, s3)))
  good.then(o, Cr.Cir.exec(n2, D.B.loop(), D.Mode0(st1)), s3 => Cr.Cir.exec(n, Cr.Cir.Stmt.nop{}, s3), g2)

# M.input that runs out of memory with the fuel f1 ends Mach.code so with 1 + f1
def oom.fin(-o: List<&2, Word(8n)>, +f1: Nat, +st0: Cr.Cir.State,
  er1: {Cr.Cir.exec(f1, Mc.M.input(), st0) == Cr.Cir.Out.out_of_memory{} : Cr.Cir.Out}) ->
  D.Good(o, Cr.Cir.exec(1n+f1, Mc.Mach.code(), st0)):
  +n = {1n+f1 : Nat}
  +er = er1
  +e1 = Equal.trans(Cr.Cir.Out, Cr.Cir.Out.out_of_memory{}, Cr.Cir.exec(f1, Mc.M.input(), st0), Cr.Cir.exec(n, Mc.M.input(), st0),
    Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f1, Mc.M.input(), st0), Cr.Cir.Out.out_of_memory{}, er),
    D.mono(f1, n, Mc.M.input(), st0, N.le_succ(f1, f1, N.le_refl(f1)), ends.eq(Cr.Cir.exec(f1, Mc.M.input(), st0), Cr.Cir.Out.out_of_memory{}, er, Unit{})))
  %e1 : D.Good(o, Cr.Cir.exec.then(_, s1 => Cr.Cir.exec(n, D.B.rest(), s1)))
  Unit{}

def run.next(k: Nat, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +o: List<&2, Word(8n)>, +f1: Nat, +st0: Cr.Cir.State,
  +st1: Cr.Cir.State, +er1: {Cr.Cir.exec(f1, Mc.M.input(), st0) == Cr.Cir.Out.next{st1} : Cr.Cir.Out},
  +len: {List.length(&2, U32, D.St.regs(st1)) == 63n : Nat}, +w: Nat,
  +inv: D.Inv(ds, T.tm.names(ds), T.tm.img(ds), D.Mode0(st1), Pg.Program.start(i), w),
  +e: {Pg.Program.result(ds, El.Eval.steps(k, ds, Pg.Program.start(i))) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}) ->
  D.Ex(Nat, n => D.Good(o, Cr.Cir.exec(n, Mc.Mach.code(), st0))):
  +ls = loop.start(k, ds, T.tm.names(ds), T.tm.img(ds), D.Mode0(st1), Pg.Program.start(i), w, o, inv, e)
  +n2 = D.Ex.fst(Nat, n => D.Good(o, Cr.Cir.exec(n, D.B.loop(), D.Mode0(st1))), ls)
  (1n+Nat.add(f1, n2), run.fin(o, f1, n2, st0, st1, er1, len, D.Ex.snd(Nat, n => D.Good(o, Cr.Cir.exec(n, D.B.loop(), D.Mode0(st1))), ls)))

def run.done.r(k: Nat, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +o: List<&2, Word(8n)>, +f1: Nat, +st0: Cr.Cir.State,
  r1: Cr.Cir.Out, +er1: {Cr.Cir.exec(f1, Mc.M.input(), st0) == r1 : Cr.Cir.Out}, d1: D.Ends(r1),
  p1: D.Post(False{}, r1, st => D.InvIn(ds, i, st), s2 => st2 => Empty),
  +e: {Pg.Program.result(ds, El.Eval.steps(k, ds, Pg.Program.start(i))) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}) ->
  D.Ex(Nat, n => D.Good(o, Cr.Cir.exec(n, Mc.Mach.code(), st0))):
  match r1:
    case Cr.Cir.Out.next{+st1}:
      (len, q) = p1
      (w, inv) = q
      run.next(k, ds, i, o, f1, st0, st1, er1, len, w, inv, e)
    case Cr.Cir.Out.halt{s, st}:
      Empty.absurd(D.Ex(Nat, n => D.Good(o, Cr.Cir.exec(n, Mc.Mach.code(), st0))), p1)
    case Cr.Cir.Out.out_of_memory{}:
      (1n+f1, oom.fin(o, f1, st0, er1))
    case Cr.Cir.Out.trap{}:
      Empty.absurd(D.Ex(Nat, n => D.Good(o, Cr.Cir.exec(n, Mc.Mach.code(), st0))), p1)
    case Cr.Cir.Out.not_done{}:
      Empty.absurd(D.Ex(Nat, n => D.Good(o, Cr.Cir.exec(n, Mc.Mach.code(), st0))), d1)

# when Eval reaches the bytes o from Program.start(i), a run of Mach.code from
# the start gives them, or runs out of memory, with some fuel
def run.done(k: Nat, +p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +m: U32, +o: List<&2, Word(8n)>, +kk: U32,
  +len: U32, +pg: U32, +lim: U32, +first: U32,
  +rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  +small: {Mc.Img.small(p, 0) == True{} : Bool},
  +s: D.Start(Mc.Img.cells(ds), i, m, kk, len, pg, lim, first),
  +e: {Pg.Program.result(ds, El.Eval.steps(k, ds, Pg.Program.start(i))) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}) ->
  D.Ex(Nat, n => D.Good(o, Cr.Cir.exec(n, Mc.Mach.code(), D.St0(Mc.Mach.regs(), Mc.Img.cells(ds), first, kk, pg, lim, i)))):
  +st0 = D.St0(Mc.Mach.regs(), Mc.Img.cells(ds), first, kk, pg, lim, i)
  +id = input.done(p, ds, i, m, kk, len, pg, lim, first, rd, small, s)
  +f1 = D.Ex.fst(Nat, f => D.Ends(Cr.Cir.exec(f, Mc.M.input(), st0)), id)
  run.done.r(k, ds, i, o, f1, st0, Cr.Cir.exec(f1, Mc.M.input(), st0), {==}, D.Ex.snd(Nat, f => D.Ends(Cr.Cir.exec(f, Mc.M.input(), st0)), id),
    input.post(f1, p, ds, i, m, kk, len, pg, lim, first, rd, small, s), e)

def comp.of(k: Nat, +p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +m: U32, +o: List<&2, Word(8n)>, +kk: U32,
  +len: U32, +pg: U32, +lim: U32, +first: U32,
  +rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  +small: {Mc.Img.small(p, 0) == True{} : Bool},
  +s: D.Start(Mc.Img.cells(ds), i, m, kk, len, pg, lim, first),
  +e: {Pg.Program.result(ds, El.Eval.steps(k, ds, Pg.Program.start(i))) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}) ->
  &n: Nat -> Or({Cr.Cir.ended(Cr.Cir.exec(n, Mc.Mach.code(), D.St0(Mc.Mach.regs(), Mc.Img.cells(ds), first, kk, pg, lim, i))) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome},
    {Cr.Cir.ended(Cr.Cir.exec(n, Mc.Mach.code(), D.St0(Mc.Mach.regs(), Mc.Img.cells(ds), first, kk, pg, lim, i))) == Wa.Wasm.Outcome.out_of_memory{} : Wa.Wasm.Outcome}):
  +st0 = D.St0(Mc.Mach.regs(), Mc.Img.cells(ds), first, kk, pg, lim, i)
  +rn = run.done(k, p, ds, i, m, o, kk, len, pg, lim, first, rd, small, s, e)
  +n = D.Ex.fst(Nat, n => D.Good(o, Cr.Cir.exec(n, Mc.Mach.code(), st0)), rn)
  (n, good.end(o, Cr.Cir.exec(n, Mc.Mach.code(), st0), D.Ex.snd(Nat, n => D.Good(o, Cr.Cir.exec(n, Mc.Mach.code(), st0)), rn),
    code.fits(n, Mc.Img.cells(ds), first, kk, pg, lim, i)))

# Layer B
# -------
#
# The lemmas of runs_as_eval.bend, with exactly their types.

# B: the machine never makes an access that its module could not make the
# same way
def mach.safe.proof(
  +p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +m: U32, +n: Nat,
  rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  small: {Mc.Img.small(p, 0) == True{} : Bool}
) -> {Cr.Cir.result(n, Mc.Mach.code(), Mc.Mach.regs(), Mc.Img.cells(ds), i, m) != Wa.Wasm.Outcome.trap{} : Wa.Wasm.Outcome}:
  res.on(n, Mc.Mach.code(), Mc.Mach.regs(), Mc.Img.cells(ds), i, m, x => {x != Wa.Wasm.Outcome.trap{} : Wa.Wasm.Outcome},
    e => (%e : oc.nt(_); Unit{}),
    +kk => +len => +pg => +lim => +first => s =>
      safe.end(Cr.Cir.exec(n, Mc.Mach.code(), D.St0(Mc.Mach.regs(), Mc.Img.cells(ds), first, kk, pg, lim, i)), ds, Pg.Program.start(i),
        run.post(n, p, ds, i, m, kk, len, pg, lim, first, rd, small, s), code.fits(n, Mc.Img.cells(ds), first, kk, pg, lim, i)))

# B: a result of the machine is the list of bytes of a value that Eval reaches
def mach.sound.proof(
  +p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +m: U32, +n: Nat, +o: List<&2, Word(8n)>,
  rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  small: {Mc.Img.small(p, 0) == True{} : Bool},
  e: {Cr.Cir.result(n, Mc.Mach.code(), Mc.Mach.regs(), Mc.Img.cells(ds), i, m) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome}
) -> &k:Nat -> {Pg.Program.result(ds, El.Eval.steps(k, ds, Pg.Program.start(i))) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}:
  res.on(n, Mc.Mach.code(), Mc.Mach.regs(), Mc.Img.cells(ds), i, m,
    x => {x == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome} ->
      &k:Nat -> {Pg.Program.result(ds, El.Eval.steps(k, ds, Pg.Program.start(i))) == Some{o} : Maybe<&2, List<&2, Word(8n)>>},
    e2 => Empty.absurd(&k:Nat -> {Pg.Program.result(ds, El.Eval.steps(k, ds, Pg.Program.start(i))) == Some{o} : Maybe<&2, List<&2, Word(8n)>>},
      (%e2 : oc.nr(_); Unit{})),
    +kk => +len => +pg => +lim => +first => s => e2 =>
      sound.end(Cr.Cir.exec(n, Mc.Mach.code(), D.St0(Mc.Mach.regs(), Mc.Img.cells(ds), first, kk, pg, lim, i)), ds, Pg.Program.start(i), o,
        run.post(n, p, ds, i, m, kk, len, pg, lim, first, rd, small, s), e2), e)

# B: when Eval reaches a list of bytes, the machine gives it, or runs out of
# memory
def mach.complete.proof(
  +p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +m: U32, +k: Nat, +o: List<&2, Word(8n)>,
  rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  small: {Mc.Img.small(p, 0) == True{} : Bool},
  e: {Pg.Program.result(ds, El.Eval.steps(k, ds, Pg.Program.start(i))) == Some{o} : Maybe<&2, List<&2, Word(8n)>>}
) -> &n:Nat -> Or({Cr.Cir.result(n, Mc.Mach.code(), Mc.Mach.regs(), Mc.Img.cells(ds), i, m) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome},
  {Cr.Cir.result(n, Mc.Mach.code(), Mc.Mach.regs(), Mc.Img.cells(ds), i, m) == Wa.Wasm.Outcome.out_of_memory{} : Wa.Wasm.Outcome}):
  res.ex(Mc.Mach.code(), Mc.Mach.regs(), Mc.Img.cells(ds), i, m,
    x => Or({x == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome}, {x == Wa.Wasm.Outcome.out_of_memory{} : Wa.Wasm.Outcome}),
    Inr{{==}},
    +kk => +len => +pg => +lim => +first => s => comp.of(k, p, ds, i, m, o, kk, len, pg, lim, first, rd, small, s, e))

# Open: a round keeps the machine's cells within the peak of its term
def round.peak(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +st: Cr.Cir.State, +t: Bk.Term, +w: Nat, inv: D.Inv(ds, ks, img, st, t, w)) ->
  D.Post(False{}, Cr.Cir.exec(f, D.B.body(), st), s => N.Le(D.Mem.cells(s), Nat.max(D.Mem.cells(st), D.Peak(t))), s => st2 => Unit):
  ?TODO

# Open: a round whose memory has room for the peak of its term, and for the
# output, does not run out of memory
def round.room(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +st: Cr.Cir.State, +t: Bk.Term, +w: Nat, inv: D.Inv(ds, ks, img, st, t, w),
  room: N.Le(Nat.add(Nat.mul(20n, Nat.add(U32.to_nat(D.St.first(st)), Nat.max(D.Mem.cells(st), D.Peak(t)))), Pg.Term.size(t)),
    U32.to_nat(U32.shln(Wa.Wasm.min(D.St.lim(st), 65536), 16n)))) ->
  D.NoOom(Cr.Cir.exec(f, D.B.body(), st)):
  ?TODO

# B: with the memory of AGENTS.md 3.9.1.4, the machine gives the list of bytes
# (open: from round.peak and round.room as above)
def mach.memory.proof(
  +p: List<&2, Word(8n)>, +ds: List<&2, Bk.Def>, +i: List<&2, Word(8n)>, +m: U32, +k: Nat, +o: List<&2, Word(8n)>,
  rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>},
  small: {Mc.Img.small(p, 0) == True{} : Bool},
  e: {Pg.Program.result(ds, El.Eval.steps(k, ds, Pg.Program.start(i))) == Some{o} : Maybe<&2, List<&2, Word(8n)>>},
  big: {Nat.is_le(Pg.Program.need(p, i, k), Pg.Program.memory(m)) == True{} : Bool}
) -> &n:Nat -> {Cr.Cir.result(n, Mc.Mach.code(), Mc.Mach.regs(), Mc.Img.cells(ds), i, m) == Wa.Wasm.Outcome.result{o} : Wa.Wasm.Outcome}:
  ?TODO
