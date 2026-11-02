# compiler: the output fits at halt 0 (layer B)
# =============================================
#
# At halt 0, Cir.ended gives the output only when its outn bytes at byte
# 20 × next fit in the memory's pages, as the host checks (Wasm.fits); else
# a trap. No run of Mach.code ends in that trap, by facts of Cir alone: the
# cells before next and the output after them lie in the memory (Fits) once
# M.input has made its last cell, the focus (fits.input); every statement
# keeps Fits (fits.exec), as an alloc and an emit grow the pages to hold
# what they add (fits.alloc); and Fits is the host's check (fits.wasm).
# So a halt of Mach.code fits (fits.code).

import Base
import ../../Wasm/impl.bend as Wa
import ../Cir/impl.bend as Cr
import ./impl.bend as Mc
import ../need_big.bend as N
import ../Cir/halt.bend as PH
import ../Cir/simulation_steps.bend as S

# Statements
# ----------

# the bytes of a memory of p pages that 32-bit addresses reach: 2^16 × p,
# up to 2^16 pages
def Mem.bytes(+p: U32) -> Nat:
  N.D(16n, U32.to_nat(Wa.Wasm.min(p, 65536)))

# the cells before next, 20 bytes each, and the outn bytes of the output
# after them lie in the memory of pg pages
def Fits.of(+nx: U32, +pg: U32, +on: U32) -> Data:
  N.Le(Nat.add(PH.H.t20(U32.to_nat(nx)), U32.to_nat(on)), Mem.bytes(pg))

# the state's cells and output lie in its memory
def Fits(st: Cr.Cir.State) -> Data:
  match st:
    case Cr.Cir.State{_, _, nx, _, _, pg, _, _, _, on}:
      Fits.of(nx, pg, on)

# what an outcome keeps: the state after it, or at its halt, fits; any
# other outcome keeps nothing
def FitsOut(o: Cr.Cir.Out) -> Data:
  match o:
    case Cr.Cir.Out.next{st}:
      Fits(st)
    case Cr.Cir.Out.halt{_, st}:
      Fits(st)
    case _:
      Unit

# the cells that M.input takes are new: no cell to reuse (the pend
# register holds 0), and next is at least first
def NewCells(st: Cr.Cir.State) -> Data:
  match st:
    case Cr.Cir.State{rg, _, nx, fi, _, _, _, _, _, _}:
      S.P2({List.get(&2, U32, rg, Mc.R.pend()) == Some{0} : Maybe<&2, U32>}, N.Le(U32.to_nat(fi), U32.to_nat(nx)))

# the state fits, and the machine has a cell of its own (first < next)
def Made(st: Cr.Cir.State) -> Data:
  match st:
    case Cr.Cir.State{_, _, +nx, fi, _, pg, _, _, _, on}:
      S.P2(Fits.of(nx, pg, on), N.Le(1n+U32.to_nat(fi), U32.to_nat(nx)))

# what M.input gives: a state of which Made holds, never a halt; or another
# end (out of memory, out of fuel)
def MadeOut(o: Cr.Cir.Out) -> Data:
  match o:
    case Cr.Cir.Out.next{st}:
      Made(st)
    case Cr.Cir.Out.halt{_, _}:
      Empty
    case _:
      Unit

# an alloc that goes on gives Fits whatever held before: it takes no cell
# once the output began (outn = 0 after it), and the pages that it leaves
# hold its cell, the bytes up to 20 (next + 1)
def fits.alloc(r: Nat, +st: Cr.Cir.State) -> FitsOut(Cr.Cir.exec.alloc(r, st)):
  ?TODO

# every statement keeps Fits, with any fuel: set, store, nop and halt change
# none of next, outn and pages; an alloc gives it (fits.alloc); an emit grows
# the pages to hold its byte, at 20 next + outn
def fits.exec(+f: Nat, s: Cr.Cir.Stmt, +st: Cr.Cir.State, +h: Fits(st)) -> FitsOut(Cr.Cir.exec(f, s, st)):
  ?TODO

# M.input ends with M.make of the focus: from a state whose cells to take
# are new, its alloc takes a new cell, so the state after M.input fits and
# has a cell of the machine's own; M.input never halts
def fits.input(+f: Nat, +st: Cr.Cir.State, h: NewCells(st)) -> MadeOut(Cr.Cir.exec(f, Mc.M.input(), st)):
  ?TODO

# Fits is the host's check of the output at halt 0, as Cir.ended makes it:
# 20 next + outn <= 2^32 needs next < 214748365, so 20 × next does not wrap
def fits.wasm(+nx: U32, +pg: U32, +on: U32, h: Fits.of(nx, pg, on)) ->
  {Wa.Wasm.fits(pg, Cr.Cir.at(nx), on) == True{} : Bool}:
  ?TODO

# a run of Mach.code from a state whose cells to take are new: the state
# after it, or at its halt, fits (fits.input, then fits.exec)
def fits.code(+f: Nat, +st: Cr.Cir.State, h: NewCells(st)) -> FitsOut(Cr.Cir.exec(f, Mc.Mach.code(), st)):
  ?TODO
