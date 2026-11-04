# compiler: smoke checks of logic/spec.bend and header/spec.bend (P2, lane S1)
# ============================================================================
#
# Test c (bend2 kinds): computed checks, by {==}, that the defs of the logic
# and the header say what they should on small Cir programs and states: WP
# unfolds a closed program to its run, a while inside it is Tot, Tot holds
# with a concrete fuel, the primitive laws' budgets are right at their edges
# (exec.alloc, wp.alloc, wp.emit), the frame (St.kept, Cir.writes) and the
# table and header readers give the machine's values. They stand until the
# laws are proven (tot.of_wp, wp.of_tot, exec.alloc, wp.alloc, wp.emit,
# tot.frame, hd.*_of replace them); the redesign's P5 deletes this file. It
# is outside main's closure.

import Base
import ../../Program/impl.bend as Pg
import ../Cir/impl.bend as Cr
import ./impl.bend as Mc
import ./shared.bend as K
import ./logic/spec.bend as Lg
import ./header/spec.bend as Hs

# States
# ------

# a state of n registers, all 0, no cells, next at cell nx, first at cell 2,
# the image of cell 1, the memory of p pages and the limit lim
def smk.st(n: Nat, +nx: U32, +p: U32, +lim: U32) -> Cr.Cir.State:
  Cr.Cir.State{List.replicate(U32, n, 0), Cr.Cir.Cells.none{}, nx, 2, 1, p, lim, [], [], 0}

# the post: register r holds v
def smk.is(+r: Nat, +v: U32, x: Cr.Cir.State) -> Type:
  {Lg.Reg(x, r) == Some{v} : Maybe<&2, U32>}

# WP on closed code
# -----------------

# two sets: register 1 gets 5 + 1
def smk.wp_set() -> Lg.WP(Mc.M.do([Mc.M.set(0n, Mc.M.c(5)), Mc.M.set(1n, Mc.M.add(Mc.M.g(0n), Mc.M.c(1)))]), 0n,
  h => x => smk.is(1n, 6, x), Lg.No, smk.st(4n, 2, 1, 1)):
  {==}

# an if takes the branch of its condition
def smk.wp_if() -> Lg.WP(Mc.M.do([Mc.M.set(0n, Mc.M.c(3)),
  Mc.M.if(Mc.M.eq(Mc.M.g(0n), Mc.M.c(3)), Mc.M.set(1n, Mc.M.c(7)), Mc.M.set(1n, Mc.M.c(8)))]), 0n,
  h => x => smk.is(1n, 7, x), Lg.No, smk.st(4n, 2, 1, 1)):
  {==}

# M.alloc (a new cell, as the free list is empty), then a store into it; the
# budget is the alloc's 20 (next + 1) bytes
def smk.wp_make() -> Lg.WP(Mc.M.make(2n, Mc.M.c(842), Mc.M.c(0), Mc.M.c(0), Mc.M.c(0)), 60n,
  h => x => {Lg.St.fd(x, 0n, 2) == 842 : U32} & smk.is(2n, 2, x), Lg.No, smk.st(53n, 2, 1, 1)):
  ({==}, {==})

# a halt: its post H
def smk.wp_halt() -> Lg.WP(Mc.M.do([Mc.M.set(0n, Mc.M.c(1)), Mc.M.need(Mc.M.eq(Mc.M.g(0n), Mc.M.c(0)), Mc.M.set(1n, Mc.M.c(1)))]), 0n,
  h => x => Empty, k => x => {k == 2 : U32}, smk.st(4n, 2, 1, 1)):
  {==}

# a while inside WP is Tot: M.nth walks 2 steps down a chain (cells 2 -> 3
# -> 4 by field 1); Tot holds with the fuel 3
def smk.chain() -> Cr.Cir.State:
  Lg.St.set(Lg.St.set(Lg.St.store(Lg.St.store(smk.st(53n, 5, 1, 1), 1n, 2, 3), 1n, 3, 4), Mc.R.t1(), 2), Mc.R.t2(), 2)

def smk.wp_while() -> Lg.WP(Mc.M.nth(), 0n, h => x => smk.is(Mc.R.t2(), 4, x), Lg.No, smk.chain()):
  (3n, {==})

# Budgets at their edges
# ----------------------

# an alloc at next 3275 with a limit of one page fits (20 * 3276 <= 65536);
# at next 3276 it runs out of memory, and the limit is below 20 * 3277
def smk.alloc_fits() -> Lg.WP(Cr.Cir.Stmt.alloc{0n}, 65520n, h => x => smk.is(0n, 3275, x), Lg.No, smk.st(1n, 3275, 1, 1)):
  {==}

def smk.alloc_full() -> {Cr.Cir.exec(0n, Cr.Cir.Stmt.alloc{0n}, smk.st(1n, 3276, 1, 1)) == Cr.Cir.Out.out_of_memory{} : Cr.Cir.Out}:
  {==}

def smk.alloc_bound() -> {Nat.is_lt(Lg.Lim(smk.st(1n, 3276, 1, 1)), Nat.mul(20n, Nat.add(3276n, 1n))) == True{} : Bool}:
  {==}

# an emit at next 3276 with outn 15 needs byte 65535: it fits in one page;
# with outn 16, byte 65536 does not, and the limit is below 20 next + 17
def smk.emit_st(+n: U32) -> Cr.Cir.State:
  Cr.Cir.State{[0], Cr.Cir.Cells.none{}, 3276, 2, 1, 1, 1, [], [], n}

def smk.emit_fits() -> Lg.WP(Cr.Cir.Stmt.emit{Mc.M.c(65)}, 65536n, h => x => {Lg.St.outn(x) == 16 : U32}, Lg.No, smk.emit_st(15)):
  {==}

def smk.emit_full() -> {Cr.Cir.exec(0n, Cr.Cir.Stmt.emit{Mc.M.c(65)}, smk.emit_st(16)) == Cr.Cir.Out.out_of_memory{} : Cr.Cir.Out}:
  {==}

def smk.emit_bound() -> {Nat.is_lt(Lg.Lim(smk.emit_st(16)), Nat.add(Nat.mul(20n, 3276n), Nat.add(16n, 1n))) == True{} : Bool}:
  {==}

# The frame
# ---------

# M.dec's code writes only its scratch registers and none other; M.alloc's
# writes its target too
def smk.dec_writes() -> {K.Sub(Lg.Cir.writes(Mc.M.dec(Mc.R.x())), Mc.M.dec.scr()) == True{} : Bool}:
  {==}

def smk.alloc_writes() -> {K.Sub(Lg.Cir.writes(Mc.M.alloc(Mc.R.n())), Con{Mc.R.n(), Mc.M.alloc.scr()}) == True{} : Bool}:
  {==}

def smk.copy_writes() -> {K.Sub(Lg.Cir.writes(Mc.M.copy(Mc.R.n(), Mc.R.wt())), Con{Mc.R.n(), Mc.M.copy.scr()}) == True{} : Bool}:
  {==}

def smk.walk_writes() -> {K.Sub(Lg.Cir.writes(Mc.M.walk()), Mc.M.walk.scr()) == True{} : Bool}:
  {==}

# only M.out emits, of the routines
def smk.emits() -> {Bool.and(Lg.Cir.emits(Mc.M.out()), Bool.not(Lg.Cir.emits(Mc.M.copy(Mc.R.n(), Mc.R.wt())))) == True{} : Bool}:
  {==}

# a set keeps every other register, and a store keeps them all
def smk.kept() -> {Lg.St.kept(smk.st(4n, 2, 1, 1), Lg.St.set(Lg.St.store(smk.st(4n, 2, 1, 1), 0n, 1, 9), 2n, 7), [2n]) == True{} : Bool}:
  {==}

def smk.not_kept() -> {Lg.St.kept(smk.st(4n, 2, 1, 1), Lg.St.set(smk.st(4n, 2, 1, 1), 2n, 7), [1n]) == False{} : Bool}:
  {==}

# The table and the header
# ------------------------

# the counted fields by tag: App 2 and 3; Lam 2; Mat 3 and 4; Ref, Var none;
# frames 2; Rwt's frame 2 and 3; an argument 2; FREE none
def smk.mask() -> {[Hs.Tbl.mask(Mc.T.app()), Hs.Tbl.mask(Mc.T.lam()), Hs.Tbl.mask(Mc.T.mat()), Hs.Tbl.mask(Mc.T.ref()),
  Hs.Tbl.mask(Mc.T.var()), Hs.Tbl.mask(Mc.K.app_arg()), Hs.Tbl.mask(Mc.K.rwt()), Hs.Tbl.mask(Mc.K.min_a()),
  Hs.Tbl.mask(Mc.K.arg()), Hs.Tbl.mask(Mc.K.free())] == [3, 1, 6, 0, 0, 1, 3, 1, 1, 0] : List<&2, U32>}:
  {==}

# the binders: Lam's body 1, Let's body 1, All's B 1, Rwt's P 2, App's parts 0
def smk.bind() -> {[Hs.Tbl.bind(Mc.T.lam(), 2n), Hs.Tbl.bind(Mc.T.let(), 2n), Hs.Tbl.bind(Mc.T.let(), 3n),
  Hs.Tbl.bind(6, 3n), Hs.Tbl.bind(Mc.T.rwt(), 3n), Hs.Tbl.bind(Mc.T.rwt(), 4n), Hs.Tbl.bind(Mc.T.app(), 3n)] ==
  [1n, 0n, 1n, 1n, 2n, 0n, 0n] : List<&2, Nat>}:
  {==}

# a value by its form: Lam, Lab, Rfl yes; Tup, App, Var no
def smk.former() -> {[Hs.Tbl.former(Mc.T.lam()), Hs.Tbl.former(Mc.T.lab()), Hs.Tbl.former(Mc.T.rfl()),
  Hs.Tbl.former(Mc.T.tup()), Hs.Tbl.former(Mc.T.app()), Hs.Tbl.former(Mc.T.var())] ==
  [True{}, True{}, True{}, False{}, False{}, False{}] : List<&2, Bool>}:
  {==}

# the input's headers: a pair at quantity 1, VALUE and DATA, STATIC or not
def smk.hd_input() -> {[Mc.M.h.static(), Mc.M.h.data()] == [Mc.Img.header(Mc.T.tup(), 1, 1792, 0), Mc.Img.header(Mc.T.tup(), 1, 768, 0)] : List<&2, U32>}:
  {==}

# the parts of a header, read back (hd.*_of's instances)
def smk.hd_parts() -> {[Hs.Hd.tag(Mc.Img.header(14, 2, 4352, 524287)), Hs.Hd.q(Mc.Img.header(14, 2, 4352, 524287)),
  Hs.Hd.fv(Mc.Img.header(14, 2, 4352, 524287)), Hs.Hd.todo(Mc.Img.header(14, 2, 4096, 5))] == [14, 2, 524287, 40960] : List<&2, U32>}:
  {==}

def smk.hd_flags() -> {[Hs.Hd.has(Mc.Img.header(14, 2, 4352, 524287), Mc.F.build()), Hs.Hd.has(Mc.Img.header(14, 2, 4352, 524287), Mc.F.value()),
  Hs.Hd.has(Mc.Img.header(14, 2, 4352, 524287), Mc.F.data())] == [True{}, True{}, False{}] : List<&2, Bool>}:
  {==}

# the copy root's header: a Prj, BUILD, with field 2 to copy
def smk.hd_root() -> {Hs.Hd.todo(U32.or(U32.or(Mc.T.prj(), Mc.F.build()), 8192)) == 8192 : U32}:
  {==}
