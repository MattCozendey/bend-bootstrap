# compiler: layer B4, the routines of the machine
# ===============================================
#
# One Tot law per routine of Machine/impl.bend: what its Cir code does, for
# some fuel, within a budget of bytes (out of memory only below it), never a
# trap. The primitives (alloc, make, release, nth) give their state exactly
# (Alloc.st, Make.st, Release.st, Nth.st); the routines that moves call (inc,
# dec, push, pop, swap, one, release.arg, release.all, copy, walk, out, input)
# say what they do to the heap invariant H (heap/spec.bend): its roots, frames
# and chains, as the abstract machine (am/spec.bend) holds them. A routine
# writes only the registers of its scratch list (Mc.M.<routine>.scr()) and the
# target that its caller names (Same, Kept). Two heap lemmas join the exact
# states to H: a new term node over owned roots (h.node), and a new argument
# cell on a chain (h.arg).
#
# Inv says that a state holds an abstract state: its mode; H with the focus
# as the one owned root, at the depth 0, the frames from sp, and no chain.

import Base
import ../../../Shared/shared.bend as Sd
import ../../../Book/impl.bend as Bk
import ../../../Eval/impl.bend as El
import ../../../Program/impl.bend as Pg
import ../../Cir/impl.bend as Cr
import ../impl.bend as Mc
import ../shared.bend as K
import ../logic/spec.bend as Lg
import ../canon/spec.bend as C
import ../am/spec.bend as A
import ../heap/spec.bend as Hp
import ../image/spec.bend as I

# Frames of a routine
# -------------------

# the registers of ws aside, st2 has the registers of st; the limit, the
# input, first, the image and the output are the same
def Same(+st: Cr.Cir.State, +st2: Cr.Cir.State, +ws: List<&2, Nat>) -> Bool:
  Lg.Regs.kept(Lg.St.regs(st), Lg.St.regs(st2), ws, 0n) && U32.is_eq(Lg.St.limit(st2), Lg.St.limit(st)) &&
    Sd.Name.is_eq(Lg.St.input(st2), Lg.St.input(st)) && U32.is_eq(Lg.St.first(st2), Lg.St.first(st)) &&
    U32.is_eq(Lg.St.image(st2), Lg.St.image(st)) && U32.is_eq(Lg.St.outn(st2), Lg.St.outn(st)) &&
    Sd.Name.is_eq(Lg.St.out(st2), Lg.St.out(st))

# Same, and the cells of L keep their fields 0, 2, 3 and 4
def Kept(+st: Cr.Cir.State, +st2: Cr.Cir.State, +L: List<&2, U32>, +ws: List<&2, Nat>) -> Bool:
  Hp.Agree(L, Lg.St.cells(st), Lg.St.cells(st2)) && Same(st, st2, ws)

def Live.sub(xs: List<&2, U32>, +ys: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, rest}:
      K.Mem(ys, x) && Live.sub(rest, ys)

# L2 is among the cells of L, and no longer
def Shrunk(+L2: List<&2, U32>, +L: List<&2, U32>) -> Bool:
  Live.sub(L2, L) && Nat.is_le(List.length(&2, U32, L2), List.length(&2, U32, L))

# Expressions
# -----------

def Ev.field(+k: Nat, r: Maybe<&2, U32>, +x: Hp.Cx, +st: Cr.Cir.State, +L: List<&2, U32>) -> Maybe<&2, U32>:
  match r:
    case Some{+c}:
      Bool.pick(Maybe<&2, U32>, Hp.V.in(x, st, L, c), Some{Hp.Fd(k, Lg.St.cells(st), c)}, None{})
    case None{}:
      None{}

# the value of e in st (Cir.eval), when it reads no register of ws and only
# the fields of live cells (L) and of the image's STATIC cells: then a new
# cell, a store to it, or a write to a register of ws keeps it
def Ev(e: Cr.Cir.Expr, +x: Hp.Cx, +st: Cr.Cir.State, +L: List<&2, U32>, +ws: List<&2, Nat>) -> Maybe<&2, U32>:
  match e:
    case Cr.Cir.Expr.const{n}:
      Some{n}
    case Cr.Cir.Expr.get{+r}:
      Bool.pick(Maybe<&2, U32>, K.Has(ws, r), None{}, Lg.Reg(st, r))
    case Cr.Cir.Expr.op{o, a, b}:
      Cr.Cir.eval.op(o, Ev(a, x, st, L, ws), Ev(b, x, st, L, ws))
    case Cr.Cir.Expr.eqz{a}:
      Cr.Cir.eval.eqz(Ev(a, x, st, L, ws))
    case Cr.Cir.Expr.field{k, c}:
      Ev.field(k, Ev(c, x, st, L, ws), x, st, L)
    case Cr.Cir.Expr.byte{i}:
      Cr.Cir.eval.byte(Ev(i, x, st, L, ws), Lg.St.input(st))
    case Cr.Cir.Expr.size{}:
      Cr.Cir.eval.size(st)

def Evs.con(r: Maybe<&2, U32>, rs: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match r rs:
    case Some{v} Some{vs}:
      Some{Con{v, vs}}
    case _ _:
      None{}

def Evs(es: List<&2, Cr.Cir.Expr>, +x: Hp.Cx, +st: Cr.Cir.State, +L: List<&2, U32>, +ws: List<&2, Nat>) ->
  Maybe<&2, List<&2, U32>>:
  match es:
    case Nil{}:
      Some{[]}
    case Con{e, rest}:
      Evs.con(Ev(e, x, st, L, ws), Evs(rest, x, st, L, ws))

# Exact states
# ------------

# the cell that M.alloc takes: the free list's head, or a new one (next)
def Alloc.cell(+st: Cr.Cir.State) -> U32:
  Bool.pick(U32, U32.is_zero(Lg.St.reg(st, Mc.R.free())), Lg.St.next(st), Lg.St.reg(st, Mc.R.free()))

def Alloc.or(r: Maybe<&2, U32>, +p: U32) -> U32:
  match r:
    case Some{v}:
      v
    case None{}:
      p

# the pages once a new cell is taken (Cir.room); the same when the memory
# cannot grow (then M.alloc is out of memory)
def Alloc.pages(+st: Cr.Cir.State) -> U32:
  Alloc.or(Cr.Cir.room(U32.add(Cr.Cir.at(Lg.St.next(st)), 19), Lg.St.pages(st), Lg.St.limit(st)), Lg.St.pages(st))

# st with the whole cell c set to v
def Alloc.put(st: Cr.Cir.State, +c: U32, v: Cr.Cir.Cell) -> Cr.Cir.State:
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      Cr.Cir.State{regs, Cr.Cir.Cells.set(cells, c, v), next, first, image, pages, limit, input, out, outn}

def Alloc.st.of(zero: Bool, +st: Cr.Cir.State, +r: Nat) -> Cr.Cir.State:
  match zero:
    case True{}:
      Lg.St.alloc(st, r, Alloc.pages(st))
    case False{}:
      +f = Lg.St.reg(st, Mc.R.free())
      Alloc.put(Lg.St.set(Lg.St.set(st, r, f), Mc.R.free(), Hp.Fd(1n, Lg.St.cells(st), f)), f, Cr.Cir.Cell.zero())

# the register free after M.alloc: the next of the free list's head, or 0
def Alloc.free(+st: Cr.Cir.State) -> U32:
  Bool.pick(U32, U32.is_zero(Lg.St.reg(st, Mc.R.free())), 0, Hp.Fd(1n, Lg.St.cells(st), Lg.St.reg(st, Mc.R.free())))

# the state after M.alloc(r): r holds Alloc.cell, all zeros; the free list
# moves on, or next does
def Alloc.st(+st: Cr.Cir.State, +r: Nat) -> Cr.Cir.State:
  Alloc.st.of(U32.is_zero(Lg.St.reg(st, Mc.R.free())), st, r)

# the state after M.make(r, ..): M.alloc's, with the cell v there
def Make.st(+st: Cr.Cir.State, +r: Nat, v: Cr.Cir.Cell) -> Cr.Cir.State:
  Alloc.put(Alloc.st(st, r), Alloc.cell(st), v)

# the state after M.release of the cell c: FREE, at the head of the free list
def Release.st(+st: Cr.Cir.State, +c: U32) -> Cr.Cir.State:
  Lg.St.set(Lg.St.store(Lg.St.store(st, 0n, c, Mc.K.free()), 1n, c, Lg.St.reg(st, Mc.R.free())), Mc.R.free(), c)

# the cell j steps down a chain (by field 1) from c
def Nth(j: Nat, +m: Cr.Cir.Cells, +c: U32) -> U32:
  match j:
    case 0n:
      c
    case 1n+i:
      Nth(i, m, Hp.Fd(1n, m, c))

# the state after M.nth, which ends at the cell c
def Nth.st(+st: Cr.Cir.State, +c: U32) -> Cr.Cir.State:
  Lg.St.set(Lg.St.set(st, Mc.R.t2(), c), Mc.R.t1(), 0)

# Frames and arguments
# --------------------

# the header of the frame fr's cell (M.header of its kind, quantity, KNOWN)
def Fr.header(fr: A.AF) -> U32:
  match fr:
    case A.AF{kind, q, k, _, _}:
      U32.or(U32.or(A.FK.tag(kind), U32.shln(Mc.Img.quan(q), 6n)), Bool.pick(U32, k, Mc.F.known(), 0))

def Fr.a(fr: A.AF) -> Bk.Term:
  match fr:
    case A.AF{_, _, _, a, _}:
      a

def Push.rts.of(kind: A.FK, +ca: U32, +cb: U32, a: Bk.Term, b: Bk.Term, rs: List<&2, Hp.Rt>) -> List<&2, Hp.Rt>:
  match kind:
    case A.FK.rwt{}:
      Con{Hp.Rt{ca, 2n, a}, Con{Hp.Rt{cb, 0n, b}, rs}}
    case k:
      Con{Hp.Rt{ca, Hp.V.FK.depth(k), a}, rs}

# the roots that the frame fr takes from its fields 2 (ca) and 3 (cb, Rwt's
# only), around rs: its terms, at their depths
def Push.rts(fr: A.AF, +ca: U32, +cb: U32, rs: List<&2, Hp.Rt>) -> List<&2, Hp.Rt>:
  match fr:
    case A.AF{kind, _, _, a, b}:
      Push.rts.of(kind, ca, cb, a, b, rs)

# a frame that M.swap may take or give: its term at the depth 0, no other
def Swap.kind(k: A.FK) -> Bool:
  match k:
    case A.FK.let{}:
      False{}
    case A.FK.rwt{}:
      False{}
    case _:
      True{}

# M.swap turns the frame fr into fr2, whose term is v
def Swap.ok(fr: A.AF, fr2: A.AF, +v: Bk.Term) -> Bool:
  match fr fr2:
    case A.AF{k1, _, _, _, _} A.AF{k2, _, _, a2, _}:
      Swap.kind(k1) && Swap.kind(k2) && C.Term.is_eq(a2, v)

# the header of an argument cell of ag
def Arg.header(ag: A.Ag) -> U32:
  match ag:
    case A.Ag{q, k, _}:
      U32.or(U32.or(Mc.K.arg(), U32.shln(Mc.Img.quan(q), 6n)), Bool.pick(U32, k, Mc.F.known(), 0))

def Arg.t(ag: A.Ag) -> Bk.Term:
  match ag:
    case A.Ag{_, _, t}:
      t

def Cells.is_eq(xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{x, xr} Con{y, yr}:
      U32.is_eq(x, y) && Cells.is_eq(xr, yr)
    case _ _:
      False{}

def Rts.cs(rs: List<&2, Hp.Rt>) -> List<&2, U32>:
  match rs:
    case Nil{}:
      []
    case Con{Hp.Rt{c, _, _}, rest}:
      Con{c, Rts.cs(rest)}

# the new cell n of st2 reads as t at the depth 0, with no real variable free,
# and its counted pointers are the cells of the roots ps, in order
def Node.ok(+x: Hp.Cx, +st2: Cr.Cir.State, +n: U32, ps: List<&2, Hp.Rt>, +t: Bk.Term) -> Bool:
  Hp.V.held.at(x, st2, n, 0n, t) && Cells.is_eq(Rts.cs(ps), Hp.Ptrs(Lg.St.cells(st2), n))

def Ag.is_eq(a: A.Ag, b: A.Ag) -> Bool:
  match a b:
    case A.Ag{p, j, s} A.Ag{q, k, t}:
      C.Quan.is_eq(p, q) && Hp.V.beq(j, k) && C.Term.is_eq(s, t)

def Ags.is_eq(as: List<&2, A.Ag>, bs: List<&2, A.Ag>) -> Bool:
  match as bs:
    case Nil{} Nil{}:
      True{}
    case Con{a, ar} Con{b, br}:
      Ag.is_eq(a, b) && Ags.is_eq(ar, br)
    case _ _:
      False{}

# The copy and the walk
# ---------------------

# the register of a copy's source: wt (a call's leaf) or z (a λ's or a let's
# body)
def Copy.src(wt: Bool) -> Nat:
  match wt:
    case True{}:
      Mc.R.wt()
    case False{}:
      Mc.R.z()

# the depth of the source's term: 0 for a leaf (its variables are the walk's
# locals), 1 for a body (under its binder)
def Copy.depth(wt: Bool) -> Nat:
  match wt:
    case True{}:
      0n
    case False{}:
      1n

# the bytes of a copy of t with the locals es: the cells up to first, the live
# ones, its root and one per node of its result
def Copy.budget(+x: Hp.Cx, +L: List<&2, U32>, +t: Bk.Term, +es: List<&2, A.Ag>) -> Nat:
  I.Cells.bytes(Hp.Cx.fi(x), Nat.add(List.length(&2, U32, L), Nat.add(1n, Pg.Term.size(A.AM.copy(t, es)))))

# the bytes of a walk of the case tree tt: two cells a node at most (an
# argument and a poison)
def Walk.budget(+x: Hp.Cx, +L: List<&2, U32>, +tt: Bk.Term) -> Nat:
  I.Cells.bytes(Hp.Cx.fi(x), Nat.add(List.length(&2, U32, L), Nat.mul(2n, Pg.Term.size(tt))))

# the registers of the walk's end, as the abstract walk w ends: a leaf (wres
# 1, wt its cell, the locals e and the arguments left ys); it waits (wres 2,
# no argument left); no walk (wres 3)
def Walk.res(+x: Hp.Cx, +st2: Cr.Cir.State, +e2: List<&2, A.Ag>, +ys2: List<&2, A.Ag>, w: A.AW) -> Bool:
  match w:
    case A.AW.leaf{u, e, ys}:
      I.Mb.is(Lg.Reg(st2, Mc.R.wres()), 1) && Ags.is_eq(e2, e) && Ags.is_eq(ys2, ys) &&
        Hp.V.img(x, Lg.St.cells(st2), Lg.St.reg(st2, Mc.R.wt())) && Hp.V.is(Hp.V.at(x, st2, Lg.St.reg(st2, Mc.R.wt()), 0n), u)
    case A.AW.waits{}:
      I.Mb.is(Lg.Reg(st2, Mc.R.wres()), 2) && U32.is_zero(Lg.St.reg(st2, Mc.R.wargs()))
    case A.AW.none{}:
      I.Mb.is(Lg.Reg(st2, Mc.R.wres()), 3)

# the end of a walk of tt from st, as w: H with the chains of the locals (wenv,
# wn of them) and of the arguments left (wargs) in front; the walk's registers
# as w says; at most two more cells a node of tt
def Walk.post(+x: Hp.Cx, +st: Cr.Cir.State, +st2: Cr.Cir.State, +L: List<&2, U32>, +L2: List<&2, U32>,
  +rs: List<&2, Hp.Rt>, +fs: List<&2, A.AF>, +chs: List<&2, Hp.Ch>, +tt: Bk.Term, +e2: List<&2, A.Ag>,
  +ys2: List<&2, A.Ag>, w: A.AW) -> Bool:
  Hp.H(x, st2, L2, rs, fs, Con{Hp.Ch{Lg.St.reg(st2, Mc.R.wenv()), e2}, Con{Hp.Ch{Lg.St.reg(st2, Mc.R.wargs()), ys2}, chs}}) &&
    Same(st, st2, Mc.M.walk.scr()) &&
    Nat.is_le(List.length(&2, U32, L2), Nat.add(List.length(&2, U32, L), Nat.mul(2n, Pg.Term.size(tt)))) &&
    I.Mb.is(Lg.Reg(st2, Mc.R.wn()), U32.from_nat(List.length(&2, A.Ag, e2))) && Walk.res(x, st2, e2, ys2, w)

# The output and the input
# ------------------------

def Out.end.of(r: Maybe<&2, List<&2, Word(8n)>>, +k: U32, +st2: Cr.Cir.State) -> Bool:
  match r:
    case Some{bs}:
      U32.is_eq(k, 0) && Sd.Name.is_eq(List.reverse(&2, Word(8n), Lg.St.out(st2)), bs)
    case None{}:
      U32.is_eq(k, 2)

# M.out's halt k from the value v: 0 with the bytes of v (the output, the last
# first), or 2 when v is no list of bytes
def Out.end(+v: Bk.Term, +k: U32, +st2: Cr.Cir.State) -> Bool:
  Out.end.of(Pg.Program.unbytes(v), k, st2)

# the bytes that M.out may need: the output's, after next
def Out.budget(+st: Cr.Cir.State, +v: Bk.Term) -> Nat:
  Nat.add(Nat.mul(20n, U32.to_nat(Lg.St.next(st))), Pg.Term.size(v))

# the bytes that M.input may need: 3 cells a byte of the list, 24 of a new
# byte of the cache, and the focus
def Input.budget(+first: U32, i: List<&2, Word(8n)>) -> Nat:
  I.Cells.bytes(first, Nat.add(1n, Nat.mul(27n, List.length(&2, Word(8n), i))))

# the state with the mode 0 (Mach.code's set after M.input)
def Mode0(+st: Cr.Cir.State) -> Cr.Cir.State:
  Lg.St.set(st, Mc.R.mode(), 0)

# The state invariant
# -------------------

def Inv.mode(+st: Cr.Cir.State, ret: Bool) -> Bool:
  I.Mb.is(Lg.Reg(st, Mc.R.mode()), Bool.pick(U32, ret, 1, 0))

# the state st holds the abstract state s: the mode register; H, with the
# live cells of st, the focus as the one owned root at the depth 0 (its term
# s.focus), the frames from sp holding s.fs, no chain; so the image is intact
# and there is no output yet
def Inv(+x: Hp.Cx, +st: Cr.Cir.State, s: A.AS) -> Bool:
  match s:
    case A.AS{ret, t, fs}:
      Inv.mode(st, ret) && Hp.H(x, st, Hp.V.Live(st), [Hp.Rt{Lg.St.reg(st, Mc.R.focus()), 0n, t}], fs, [])

# Laws
# ----

# LAW: M.alloc(r): r gets the free list's head or a new cell, all zeros
# (Alloc.st), and next stays at most 214748364; out of memory only below the
# cells up to first + |L| + 1
law alloc.spec:
  for +x: Hp.Cx
  for +st: Cr.Cir.State
  for +L: List<&2, U32>
  for +r: Nat
  for +hs: {Hp.Room(x, st, L) == True{} : Bool}
  for +hr: {Nat.is_lt(r, Mc.Mach.regs()) && Bool.not(Nat.is_eq(r, Mc.R.free())) == True{} : Bool}
  Lg.Tot(Mc.M.alloc(r), st, I.Cells.bytes(Hp.Cx.fi(x), 1n+List.length(&2, U32, L)),
    st2 => {st2 == Alloc.st(st, r) : Cr.Cir.State} & {U32.is_le(Lg.St.next(st2), 214748364) == True{} : Bool}, Lg.No)

# LAW: M.make(r, h, a, b, c), with the values hv, av, bv, cv of its
# expressions (Ev: they read neither r nor free, and only live or image
# cells): r gets M.alloc's cell, which holds them, and one pointer; next stays
# at most 214748364
law make.spec:
  for +x: Hp.Cx
  for +st: Cr.Cir.State
  for +L: List<&2, U32>
  for +r: Nat
  for +h: Cr.Cir.Expr
  for +a: Cr.Cir.Expr
  for +b: Cr.Cir.Expr
  for +c: Cr.Cir.Expr
  for +hv: U32
  for +av: U32
  for +bv: U32
  for +cv: U32
  for +hs: {Hp.Room(x, st, L) == True{} : Bool}
  for +hr: {Nat.is_lt(r, Mc.Mach.regs()) && Bool.not(Nat.is_eq(r, Mc.R.free())) == True{} : Bool}
  for +he: {Evs([h, a, b, c], x, st, L, [r, Mc.R.free()]) == Some{[hv, av, bv, cv]} : Maybe<&2, List<&2, U32>>}
  Lg.Tot(Mc.M.make(r, h, a, b, c), st, I.Cells.bytes(Hp.Cx.fi(x), 1n+List.length(&2, U32, L)),
    st2 => {st2 == Make.st(st, r, Cr.Cir.Cell{hv, 1, av, bv, cv}) : Cr.Cir.State} & {U32.is_le(Lg.St.next(st2), 214748364) == True{} : Bool}, Lg.No)

# LAW: M.release(r), of an own cell c: c is FREE, at the head of the free
# list (Release.st)
law release.spec:
  for +st: Cr.Cir.State
  for +r: Nat
  for +c: U32
  for +hr: {Lg.Reg(st, r) == Some{c} : Maybe<&2, U32>}
  for +hc: {Cr.Cir.is_cell(c, Lg.St.image(st), Lg.St.first(st), Lg.St.next(st)) &&
    Nat.is_lt(Mc.R.free(), Lg.St.nregs(st)) == True{} : Bool}
  Lg.Tot(Mc.M.release(r), st, 0n, st2 => {st2 == Release.st(st, c) : Cr.Cir.State}, Lg.No)

# LAW: M.nth, from the chain's cell ce in t2, j (below its length) in t1: t2
# gets the cell j steps down, t1 is 0 (Nth.st)
law nth.spec:
  for +x: Hp.Cx
  for +st: Cr.Cir.State
  for +ce: U32
  for +as: List<&2, A.Ag>
  for +j: Nat
  for +hc: {Hp.Chs([Hp.Ch{ce, as}], x, st) == True{} : Bool}
  for +he: {Lg.Reg(st, Mc.R.t2()) == Some{ce} : Maybe<&2, U32>}
  for +hj: {Lg.Reg(st, Mc.R.t1()) == Some{U32.from_nat(j)} : Maybe<&2, U32>}
  for +hl: {Nat.is_lt(j, List.length(&2, A.Ag, as)) == True{} : Bool}
  Lg.Tot(Mc.M.nth(), st, 0n, st2 => {st2 == Nth.st(st, Nth(j, Lg.St.cells(st), ce)) : Cr.Cir.State}, Lg.No)

# LAW: M.inc(r), of a cell c that reads as t at d (no real variable free
# there, V.rc), live or of the image: c gains a pointer, and is one more root
# (at most 64 roots: no count wraps, h.count)
law inc.spec:
  for +x: Hp.Cx
  for +st: Cr.Cir.State
  for +L: List<&2, U32>
  for +rs: List<&2, Hp.Rt>
  for +fs: List<&2, A.AF>
  for +chs: List<&2, Hp.Ch>
  for +r: Nat
  for +c: U32
  for +d: Nat
  for +t: Bk.Term
  for +hs: {Hp.H(x, st, L, rs, fs, chs) == True{} : Bool}
  for +hr: {Lg.Reg(st, r) == Some{c} : Maybe<&2, U32>}
  for +hn: {Hp.V.Held(x, st, L, c, d, t) && Hp.V.rc(U32.to_nat(Lg.St.next(st)), Lg.St.cells(st), c, d) == True{} : Bool}
  for +hb: {Nat.is_le(List.length(&2, Hp.Rt, rs), 64n) == True{} : Bool}
  Lg.Tot(Mc.M.inc(r), st, 0n, st2 => {Hp.H(x, st2, L, Con{Hp.Rt{c, d, t}, rs}, fs, chs) && Kept(st, st2, L, []) == True{} : Bool},
    Lg.No)

# LAW: M.dec(r): the root of r loses its pointer; each cell that then has
# none is freed, at once and in cascade; no cell is taken
law dec.spec:
  for +x: Hp.Cx
  for +st: Cr.Cir.State
  for +L: List<&2, U32>
  for +rs: List<&2, Hp.Rt>
  for +fs: List<&2, A.AF>
  for +chs: List<&2, Hp.Ch>
  for +r: Nat
  for +c: U32
  for +d: Nat
  for +t: Bk.Term
  for +hs: {Hp.H(x, st, L, Con{Hp.Rt{c, d, t}, rs}, fs, chs) == True{} : Bool}
  for +hr: {Lg.Reg(st, r) == Some{c} : Maybe<&2, U32>}
  for +hw: {K.Has(Mc.M.dec.scr(), r) == False{} : Bool}
  Lg.Tot(Mc.M.dec(r), st, 0n,
    st2 => &L2:List<&2, U32> -> {Hp.H(x, st2, L2, rs, fs, chs) && Kept(st, st2, L2, Mc.M.dec.scr()) && Shrunk(L2, L) == True{} : Bool},
    Lg.No)

# LAW: M.push(h, a, b), with h the header of the frame fr and a (b, Rwt's
# only) its terms' cells, owned: fr is the top frame; one cell is taken
law push.spec:
  for +x: Hp.Cx
  for +st: Cr.Cir.State
  for +L: List<&2, U32>
  for +rs: List<&2, Hp.Rt>
  for +fs: List<&2, A.AF>
  for +chs: List<&2, Hp.Ch>
  for +fr: A.AF
  for +h: Cr.Cir.Expr
  for +a: Cr.Cir.Expr
  for +b: Cr.Cir.Expr
  for +ca: U32
  for +cb: U32
  for +hs: {Hp.H(x, st, L, Push.rts(fr, ca, cb, rs), fs, chs) == True{} : Bool}
  for +he: {Evs([h, a, b], x, st, L, [Mc.R.fr(), Mc.R.free()]) == Some{[Fr.header(fr), ca, cb]} : Maybe<&2, List<&2, U32>>}
  Lg.Tot(Mc.M.push(h, a, b), st, I.Cells.bytes(Hp.Cx.fi(x), 1n+List.length(&2, U32, L)),
    st2 => &L2:List<&2, U32> -> {Hp.H(x, st2, L2, rs, Con{fr, fs}, chs) && Kept(st, st2, L, Mc.M.push.scr()) &&
      Nat.is_le(List.length(&2, U32, L2), 1n+List.length(&2, U32, L)) == True{} : Bool},
    Lg.No)

# LAW: M.pop(): the top frame fr leaves the stack and is free; its terms'
# cells (fields 2 and 3 of the old top) are owned roots
law pop.spec:
  for +x: Hp.Cx
  for +st: Cr.Cir.State
  for +L: List<&2, U32>
  for +rs: List<&2, Hp.Rt>
  for +fr: A.AF
  for +fs: List<&2, A.AF>
  for +chs: List<&2, Hp.Ch>
  for +hs: {Hp.H(x, st, L, rs, Con{fr, fs}, chs) == True{} : Bool}
  Lg.Tot(Mc.M.pop(), st, 0n,
    st2 => &L2:List<&2, U32> -> {Hp.H(x, st2, L2,
      Push.rts(fr, Hp.Fd(2n, Lg.St.cells(st), Lg.St.reg(st, Mc.R.sp())), Hp.Fd(3n, Lg.St.cells(st), Lg.St.reg(st, Mc.R.sp())), rs),
      fs, chs) && Kept(st, st2, L2, Mc.M.pop.scr()) && Shrunk(L2, L) == True{} : Bool},
    Lg.No)

# LAW: M.swap(h), with the top frame fr in h and h's value the header of
# fr2, whose term is the focus' v: the top frame is fr2; its old term (field
# 2) is the focus, an owned root, to evaluate
law swap.spec:
  for +x: Hp.Cx
  for +st: Cr.Cir.State
  for +L: List<&2, U32>
  for +rs: List<&2, Hp.Rt>
  for +fs: List<&2, A.AF>
  for +chs: List<&2, Hp.Ch>
  for +fr: A.AF
  for +fr2: A.AF
  for +v: Bk.Term
  for +h: Cr.Cir.Expr
  for +hs: {Hp.H(x, st, L, Con{Hp.Rt{Lg.St.reg(st, Mc.R.focus()), 0n, v}, rs}, Con{fr, fs}, chs) == True{} : Bool}
  for +hh: {I.Mb.is(Lg.Reg(st, Mc.R.h()), Lg.St.reg(st, Mc.R.sp())) && Swap.ok(fr, fr2, v) == True{} : Bool}
  for +he: {Ev(h, x, st, L, Mc.M.swap.scr()) == Some{Fr.header(fr2)} : Maybe<&2, U32>}
  Lg.Tot(Mc.M.swap(h), st, 0n,
    st2 => {Hp.H(x, st2, L, Con{Hp.Rt{Hp.Fd(2n, Lg.St.cells(st), Lg.St.reg(st, Mc.R.sp())), 0n, Fr.a(fr)}, rs}, Con{fr2, fs}, chs) &&
      I.Mb.is(Lg.Reg(st2, Mc.R.focus()), Hp.Fd(2n, Lg.St.cells(st), Lg.St.reg(st, Mc.R.sp()))) && I.Mb.is(Lg.Reg(st2, Mc.R.mode()), 0) &&
      Same(st, st2, Mc.M.swap.scr()) == True{} : Bool},
    Lg.No)

# LAW: M.one(r), of an owned root c of t: a new chain of one local (Q0, not
# KNOWN) takes c's pointer; wa and cenv hold its cell, clen is 1
law one.spec:
  for +x: Hp.Cx
  for +st: Cr.Cir.State
  for +L: List<&2, U32>
  for +rs: List<&2, Hp.Rt>
  for +fs: List<&2, A.AF>
  for +chs: List<&2, Hp.Ch>
  for +r: Nat
  for +c: U32
  for +t: Bk.Term
  for +hs: {Hp.H(x, st, L, Con{Hp.Rt{c, 0n, t}, rs}, fs, chs) == True{} : Bool}
  for +hr: {Lg.Reg(st, r) == Some{c} : Maybe<&2, U32>}
  for +hw: {Nat.is_lt(r, Mc.Mach.regs()) && Bool.not(K.Has(Mc.M.one.scr(), r)) == True{} : Bool}
  Lg.Tot(Mc.M.one(r), st, I.Cells.bytes(Hp.Cx.fi(x), 1n+List.length(&2, U32, L)),
    st2 => &n:U32 -> &L2:List<&2, U32> -> {I.Mb.is(Lg.Reg(st2, Mc.R.wa()), n) && I.Mb.is(Lg.Reg(st2, Mc.R.cenv()), n) &&
      I.Mb.is(Lg.Reg(st2, Mc.R.clen()), 1) && Hp.H(x, st2, L2, rs, fs, Con{Hp.Ch{n, [A.Ag{Bk.Quan.Q0{}, False{}, t}]}, chs}) &&
      Kept(st, st2, L, Mc.M.one.scr()) && Nat.is_le(List.length(&2, U32, L2), 1n+List.length(&2, U32, L)) == True{} : Bool},
    Lg.No)

# LAW: M.release.arg(a), of the head c of a chain: c is free and its term
# loses its pointer (dec.spec's cascade); the chain goes on from c's field 1
law release_arg.spec:
  for +x: Hp.Cx
  for +st: Cr.Cir.State
  for +L: List<&2, U32>
  for +rs: List<&2, Hp.Rt>
  for +fs: List<&2, A.AF>
  for +chs: List<&2, Hp.Ch>
  for +a: Nat
  for +c: U32
  for +ag: A.Ag
  for +as: List<&2, A.Ag>
  for +hs: {Hp.H(x, st, L, rs, fs, Con{Hp.Ch{c, Con{ag, as}}, chs}) == True{} : Bool}
  for +hr: {Lg.Reg(st, a) == Some{c} : Maybe<&2, U32>}
  for +hw: {Nat.is_lt(a, Mc.Mach.regs()) && Bool.not(K.Has(Mc.M.release.arg.scr(), a)) == True{} : Bool}
  Lg.Tot(Mc.M.release.arg(a), st, 0n,
    st2 => &L2:List<&2, U32> -> {Hp.H(x, st2, L2, rs, fs, Con{Hp.Ch{Hp.Fd(1n, Lg.St.cells(st), c), as}, chs}) &&
      Kept(st, st2, L2, Mc.M.release.arg.scr()) && Shrunk(L2, L) == True{} : Bool},
    Lg.No)

# LAW: M.release.all(l), of a whole chain from c: each of its cells is
# released (release_arg.spec); l is 0
law release_all.spec:
  for +x: Hp.Cx
  for +st: Cr.Cir.State
  for +L: List<&2, U32>
  for +rs: List<&2, Hp.Rt>
  for +fs: List<&2, A.AF>
  for +chs: List<&2, Hp.Ch>
  for +l: Nat
  for +c: U32
  for +as: List<&2, A.Ag>
  for +hs: {Hp.H(x, st, L, rs, fs, Con{Hp.Ch{c, as}, chs}) == True{} : Bool}
  for +hr: {Lg.Reg(st, l) == Some{c} : Maybe<&2, U32>}
  for +hw: {Nat.is_lt(l, Mc.Mach.regs()) && Bool.not(K.Has(Mc.M.release.all.scr(), l)) == True{} : Bool}
  Lg.Tot(Mc.M.release.all(l), st, 0n,
    st2 => &L2:List<&2, U32> -> {Hp.H(x, st2, L2, rs, fs, chs) && I.Mb.is(Lg.Reg(st2, l), 0) &&
      Kept(st, st2, L2, Con{l, Mc.M.release.all.scr()}) && Shrunk(L2, L) == True{} : Bool},
    Lg.No)

# LAW: M.copy(n, src), src wt (a call's leaf, read at the depth 0) or z (a
# λ's or a let's body, at the depth 1): the cell c of src reads as t at that
# depth, live or STATIC; the chain from cenv holds the locals es, and clen is
# their number; the source is STATIC, or at least as deep as the locals are
# many (else a poison of it would become a local). n gets a new owned root of
# the canonical form of t with es put in (AM.copy); the cells of L keep their
# fields 0, 2, 3, 4; out of memory only below Copy.budget (at most 64 roots)
law copy.spec:
  for +x: Hp.Cx
  for +st: Cr.Cir.State
  for +L: List<&2, U32>
  for +rs: List<&2, Hp.Rt>
  for +fs: List<&2, A.AF>
  for +chs: List<&2, Hp.Ch>
  for +wt: Bool
  for +c: U32
  for +t: Bk.Term
  for +ce: U32
  for +es: List<&2, A.Ag>
  for +hs: {Hp.H(x, st, L, rs, fs, Con{Hp.Ch{ce, es}, chs}) == True{} : Bool}
  for +hc: {I.Mb.is(Lg.Reg(st, Copy.src(wt)), c) && Hp.V.Held(x, st, L, c, Copy.depth(wt), t) &&
    (Nat.is_le(List.length(&2, A.Ag, es), Copy.depth(wt)) || Hp.Fl(Lg.St.cells(st), c, Mc.F.static())) == True{} : Bool}
  for +he: {I.Mb.is(Lg.Reg(st, Mc.R.cenv()), ce) && I.Mb.is(Lg.Reg(st, Mc.R.clen()), U32.from_nat(List.length(&2, A.Ag, es))) ==
    True{} : Bool}
  for +hb: {Nat.is_le(List.length(&2, Hp.Rt, rs), 64n) == True{} : Bool}
  Lg.Tot(Mc.M.copy(Mc.R.n(), Copy.src(wt)), st, Copy.budget(x, L, t, es),
    st2 => &n:U32 -> &L2:List<&2, U32> -> {I.Mb.is(Lg.Reg(st2, Mc.R.n()), n) &&
      Hp.H(x, st2, L2, Con{Hp.Rt{n, 0n, A.AM.copy(t, es)}, rs}, fs, Con{Hp.Ch{ce, es}, chs}) &&
      Kept(st, st2, L, Con{Mc.R.n(), Mc.M.copy.scr()}) &&
      Nat.is_le(List.length(&2, U32, L2), Nat.add(List.length(&2, U32, L), Pg.Term.size(A.AM.copy(t, es)))) == True{} : Bool},
    Lg.No)

# LAW: M.walk(): the case tree at wt (a STATIC cell of the image, of the term
# tt), on the chain of arguments at wargs (xs), walks as AM.walk walks it:
# Walk.post; the arguments' cells move to wenv, are split or released; out of
# memory only below Walk.budget (at most 64 roots)
law walk.spec:
  for +x: Hp.Cx
  for +st: Cr.Cir.State
  for +L: List<&2, U32>
  for +rs: List<&2, Hp.Rt>
  for +fs: List<&2, A.AF>
  for +chs: List<&2, Hp.Ch>
  for +tc: U32
  for +tt: Bk.Term
  for +ca: U32
  for +xs: List<&2, A.Ag>
  for +hs: {Hp.H(x, st, L, rs, fs, Con{Hp.Ch{ca, xs}, chs}) == True{} : Bool}
  for +hw: {I.Mb.is(Lg.Reg(st, Mc.R.wt()), tc) && I.Mb.is(Lg.Reg(st, Mc.R.wargs()), ca) && Hp.V.img(x, Lg.St.cells(st), tc) &&
    Hp.V.is(Hp.V.at(x, st, tc, 0n), tt) == True{} : Bool}
  for +hb: {Nat.is_le(List.length(&2, Hp.Rt, rs), 64n) == True{} : Bool}
  Lg.Tot(Mc.M.walk(), st, Walk.budget(x, L, tt),
    st2 => &L2:List<&2, U32> -> &e2:List<&2, A.Ag> -> &ys2:List<&2, A.Ag> ->
      {Walk.post(x, st, st2, L, L2, rs, fs, chs, tt, e2, ys2, A.AM.walk(Hp.Cx.ds(x), tt, [], xs)) == True{} : Bool},
    Lg.No)

# LAW: M.out(), in mode 1 with no frame, from the focus' cell of the value v:
# halt 0 with the bytes of v (Program.unbytes) as its output, or halt 2 when
# v is no list of bytes; it takes no cell; out of memory only when the output
# does not fit after next
law out.spec:
  for +x: Hp.Cx
  for +st: Cr.Cir.State
  for +v: Bk.Term
  for +iv: {Inv(x, st, A.AS{True{}, v, []}) == True{} : Bool}
  Lg.Tot(Mc.M.out(), st, Out.budget(st, v), st2 => Empty, k => st2 => {Out.end(v, k, st2) == True{} : Bool})

# LAW: M.input(), from Cir.result's start of a book that Book.read reads: the
# focus holds the start term, as Inv asks once the mode is 0; out of memory
# only below the cells up to first + 1 + 27 |i|
law input.spec:
  for +p: List<&2, Word(8n)>
  for +ds: List<&2, Bk.Def>
  for +i: List<&2, Word(8n)>
  for +m: U32
  for +k: U32
  for +len: U32
  for +pg: U32
  for +lim: U32
  for +first: U32
  for +rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>}
  for +small: {Mc.Img.small(p, 0) == True{} : Bool}
  for +s: {I.Start(Mc.Img.cells(ds), i, m, k, len, pg, lim, first) == True{} : Bool}
  Lg.Tot(Mc.M.input(), I.St0(Mc.Mach.regs(), Mc.Img.cells(ds), first, k, pg, lim, i), Input.budget(first, i),
    st => {Inv(I.Cx.of(ds, k, first), Mode0(st), A.AS{False{}, Pg.Program.start(i), []}) == True{} : Bool},
    Lg.No)

# LAW: a new term node over owned roots: M.make(r, ..) of a cell v whose
# counted pointers are the cells of the roots ps (in order), and that reads
# as t: the node is live, an owned root of t, and holds the roots' pointers
law h.node:
  for +x: Hp.Cx
  for +st: Cr.Cir.State
  for +L: List<&2, U32>
  for +rs: List<&2, Hp.Rt>
  for +fs: List<&2, A.AF>
  for +chs: List<&2, Hp.Ch>
  for +r: Nat
  for +v: Cr.Cir.Cell
  for +ps: List<&2, Hp.Rt>
  for +t: Bk.Term
  for +hs: {Hp.H(x, st, L, List.append(&2, Hp.Rt, ps, rs), fs, chs) == True{} : Bool}
  for +hr: {Nat.is_lt(r, Mc.Mach.regs()) && Bool.not(Nat.is_eq(r, Mc.R.free())) && Bool.not(Nat.is_eq(r, Mc.R.sp())) ==
    True{} : Bool}
  for +hn: {U32.is_le(Lg.St.next(Make.st(st, r, v)), 214748364) == True{} : Bool}
  for +hc: {U32.is_eq(Cr.Cir.Cell.get(1n, v), 1) && Hp.V.counted(Cr.Cir.Cells.set(Lg.St.cells(st), Alloc.cell(st), v), Alloc.cell(st)) &&
    Node.ok(x, Make.st(st, r, v), Alloc.cell(st), ps, t) == True{} : Bool}
  {Hp.H(x, Make.st(st, r, v), Con{Alloc.cell(st), L}, Con{Hp.Rt{Alloc.cell(st), 0n, t}, rs}, fs, chs) == True{} : Bool}

# LAW: a new argument cell, of the owned root c of ag's term, at the head of
# the chain from ln (M.make(r, its header, c, 0, 0), then field 1 := ln):
# the chain from the new cell holds ag, then the chain's arguments
law h.arg:
  for +x: Hp.Cx
  for +st: Cr.Cir.State
  for +L: List<&2, U32>
  for +rs: List<&2, Hp.Rt>
  for +fs: List<&2, A.AF>
  for +chs: List<&2, Hp.Ch>
  for +r: Nat
  for +ag: A.Ag
  for +c: U32
  for +ln: U32
  for +as: List<&2, A.Ag>
  for +hs: {Hp.H(x, st, L, Con{Hp.Rt{c, 0n, Arg.t(ag)}, rs}, fs, Con{Hp.Ch{ln, as}, chs}) == True{} : Bool}
  for +hr: {Nat.is_lt(r, Mc.Mach.regs()) && Bool.not(Nat.is_eq(r, Mc.R.free())) && Bool.not(Nat.is_eq(r, Mc.R.sp())) ==
    True{} : Bool}
  for +hn: {U32.is_le(Lg.St.next(Make.st(st, r, Cr.Cir.Cell{Arg.header(ag), 1, c, 0, 0})), 214748364) == True{} : Bool}
  {Hp.H(x, Lg.St.store(Make.st(st, r, Cr.Cir.Cell{Arg.header(ag), 1, c, 0, 0}), 1n, Alloc.cell(st), ln),
    Con{Alloc.cell(st), L}, rs, fs, Con{Hp.Ch{Alloc.cell(st), Con{ag, as}}, chs}) == True{} : Bool}

# LAW: the registers after M.alloc(r): r holds the new cell, free the next of
# the free list (0 when it was empty), every other register is kept
law alloc.reg:
  for +st: Cr.Cir.State
  for +r: Nat
  for +q: Nat
  for +hr: {Nat.is_lt(r, Lg.St.nregs(st)) && Nat.is_lt(Mc.R.free(), Lg.St.nregs(st)) && Bool.not(Nat.is_eq(r, Mc.R.free())) ==
    True{} : Bool}
  {Lg.Reg(Alloc.st(st, r), q) == Bool.pick(Maybe<&2, U32>, Nat.is_eq(r, q), Some{Alloc.cell(st)},
    Bool.pick(Maybe<&2, U32>, Nat.is_eq(Mc.R.free(), q), Some{Alloc.free(st)}, Lg.Reg(st, q))) : Maybe<&2, U32>}

# LAW: and after M.make(r, ..): the same
law make.reg:
  for +st: Cr.Cir.State
  for +r: Nat
  for +v: Cr.Cir.Cell
  for +q: Nat
  for +hr: {Nat.is_lt(r, Lg.St.nregs(st)) && Nat.is_lt(Mc.R.free(), Lg.St.nregs(st)) && Bool.not(Nat.is_eq(r, Mc.R.free())) ==
    True{} : Bool}
  {Lg.Reg(Make.st(st, r, v), q) == Bool.pick(Maybe<&2, U32>, Nat.is_eq(r, q), Some{Alloc.cell(st)},
    Bool.pick(Maybe<&2, U32>, Nat.is_eq(Mc.R.free(), q), Some{Alloc.free(st)}, Lg.Reg(st, q))) : Maybe<&2, U32>}
