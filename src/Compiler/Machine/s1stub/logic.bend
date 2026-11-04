# STUB of lane S1's Machine/logic/spec.bend (P2): the names that lane S2 uses, as S1's work in
# progress writes them (no laws), so that S2's files load before S1 lands. At the merge with w/s1,
# each import of this file becomes an import of Machine/logic/spec.bend, and this file is deleted.

import Base
import ../../../Shared/shared.bend as Sd
import ./kit.bend as K
import ../../../Program/impl.bend as Pg
import ../../Cir/impl.bend as Cr

# register r of the state st; nothing when there is no register r
def Reg(st: Cr.Cir.State, +r: Nat) -> Maybe<&2, U32>:
  Cr.Cir.eval.get(r, st)

def St.regs(st: Cr.Cir.State) -> List<&2, U32>:
  match st:
    case Cr.Cir.State{regs, _, _, _, _, _, _, _, _, _}:
      regs

# the number of registers
def St.nregs(st: Cr.Cir.State) -> Nat:
  List.length(&2, U32, St.regs(st))

def St.cells(st: Cr.Cir.State) -> Cr.Cir.Cells:
  match st:
    case Cr.Cir.State{_, cells, _, _, _, _, _, _, _, _}:
      cells

def St.next(st: Cr.Cir.State) -> U32:
  match st:
    case Cr.Cir.State{_, _, next, _, _, _, _, _, _, _}:
      next

def St.first(st: Cr.Cir.State) -> U32:
  match st:
    case Cr.Cir.State{_, _, _, first, _, _, _, _, _, _}:
      first

def St.image(st: Cr.Cir.State) -> U32:
  match st:
    case Cr.Cir.State{_, _, _, _, image, _, _, _, _, _}:
      image

def St.pages(st: Cr.Cir.State) -> U32:
  match st:
    case Cr.Cir.State{_, _, _, _, _, pages, _, _, _, _}:
      pages

def St.limit(st: Cr.Cir.State) -> U32:
  match st:
    case Cr.Cir.State{_, _, _, _, _, _, limit, _, _, _}:
      limit

def St.input(st: Cr.Cir.State) -> List<&2, Word(8n)>:
  match st:
    case Cr.Cir.State{_, _, _, _, _, _, _, input, _, _}:
      input

def St.out(st: Cr.Cir.State) -> List<&2, Word(8n)>:
  match st:
    case Cr.Cir.State{_, _, _, _, _, _, _, _, out, _}:
      out

def St.outn(st: Cr.Cir.State) -> U32:
  match st:
    case Cr.Cir.State{_, _, _, _, _, _, _, _, _, outn}:
      outn

# the memory limit of st, in bytes, as Program.memory counts it
def Lim(st: Cr.Cir.State) -> Nat:
  Pg.Program.memory(St.limit(st))

# st with the register r set to v
def St.set(st: Cr.Cir.State, +r: Nat, v: U32) -> Cr.Cir.State:
  match st:
    case Cr.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      Cr.Cir.State{List.set(&2, U32, regs, r, v), cells, next, first, image, pages, limit, input, out, outn}

# st with the field k of the cell c set to v
def St.store(st: Cr.Cir.State, +k: Nat, +c: U32, v: U32) -> Cr.Cir.State:
  match st:
    case Cr.Cir.State{regs, +cells, next, first, image, pages, limit, input, out, outn}:
      Cr.Cir.State{regs, Cr.Cir.Cells.set(cells, c, Cr.Cir.Cell.set(k, Cr.Cir.Cells.get(cells, c), v)), next, first, image,
        pages, limit, input, out, outn}

# st after a new cell (alloc): the register r holds the cell next, all zeros;
# next moves on; the memory has p pages
def St.alloc(st: Cr.Cir.State, +r: Nat, p: U32) -> Cr.Cir.State:
  match st:
    case Cr.Cir.State{regs, cells, +next, first, image, _, limit, input, out, outn}:
      Cr.Cir.State{List.set(&2, U32, regs, r, next), Cr.Cir.Cells.set(cells, next, Cr.Cir.Cell.zero()), U32.inc(next),
        first, image, p, limit, input, out, outn}

# the outcome o is good: next with Q, a halt with H, out of memory only when
# the limit lim has fewer than b bytes; never a trap, never out of fuel
def Ok(o: Cr.Cir.Out, +lim: Nat, +b: Nat, Q: Cr.Cir.State -> Type, H: U32 -> Cr.Cir.State -> Type) -> Type:
  match o:
    case Cr.Cir.Out.next{st}:
      Q(st)
    case Cr.Cir.Out.halt{s, st}:
      H(s, st)
    case Cr.Cir.Out.out_of_memory{}:
      {Nat.is_lt(lim, b) == True{} : Bool}
    case Cr.Cir.Out.trap{}:
      Empty
    case Cr.Cir.Out.not_done{}:
      Empty

# Tot: with some fuel, s runs from st to a good outcome
def Tot(s: Cr.Cir.Stmt, +st: Cr.Cir.State, +b: Nat, -Q: Cr.Cir.State -> Type, -H: U32 -> Cr.Cir.State -> Type) -> Type:
  &f:Nat -> Ok(Cr.Cir.exec(f, s, st), Lim(st), b, Q, H)

# no halt
def No(s: U32, st: Cr.Cir.State) -> Type:
  Empty

# each register of rs2 from the i-th is the one of rs, but those of ws; as
# many registers
def Regs.kept(rs: List<&2, U32>, +rs2: List<&2, U32>, +ws: List<&2, Nat>, +i: Nat) -> Bool:
  match rs rs2:
    case Nil{} Nil{}:
      True{}
    case Con{x, xr} Con{y, yr}:
      (K.Has(ws, i) || U32.is_eq(x, y)) && Regs.kept(xr, yr, ws, 1n+i)
    case _ _:
      False{}
