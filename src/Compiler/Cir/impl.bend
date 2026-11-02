import Base
import ../../Shared/shared.bend as Sd
import ../../Wasm/impl.bend as Wa

# Cir
# ===
#
# The language of the machine (Cir), and its translation to a WASM module
# (Compiler/impl.bend says how the compiler uses them).

# Encoding
# --------
#
# The bytes of a module of the subset, as Wasm.decode.module reads them.

def Wasm.encode.leb.if(last: Bool, b: U32, more: Unit -> List<&2, Word(8n)>) -> List<&2, Word(8n)>:
  match last:
    case True{}:
      [Sd.Byte.from_u32(b)]
    case False{}:
      Con{Sd.Byte.from_u32(U32.or(b, 128)), more(Unit{})}

def Wasm.encode.uleb.go(fuel: Nat, +v: U32) -> List<&2, Word(8n)>:
  match fuel:
    case 0n:
      []
    case 1n+f:
      +r = U32.shrn(v, 7n)
      Wasm.encode.leb.if(U32.is_zero(r), U32.and(v, 127), u => Wasm.encode.uleb.go(f, r))

# a U32 as unsigned LEB128 (spec 5.2.2): seven bits a byte, the lowest first
def Wasm.encode.uleb(v: U32) -> List<&2, Word(8n)>:
  Wasm.encode.uleb.go(5n, v)

# the bits that an arithmetic shift right by 7 brings in at the top
def Wasm.encode.sign(neg: Bool) -> U32:
  match neg:
    case True{}:
      4261412864
    case False{}:
      0

def Wasm.encode.sleb.go(fuel: Nat, +v: U32) -> List<&2, Word(8n)>:
  match fuel:
    case 0n:
      []
    case 1n+f:
      +b = U32.and(v, 127)
      +r = U32.or(U32.shrn(v, 7n), Wasm.encode.sign(U32.is_ne(U32.and(v, 2147483648), 0)))
      +low = U32.is_zero(U32.and(b, 64))
      Wasm.encode.leb.if((U32.is_zero(r) && low) || (U32.is_eq(r, 4294967295) && Bool.not(low)), b,
        u => Wasm.encode.sleb.go(f, r))

# a U32 as signed 32-bit LEB128 (spec 5.2.2), of its two's complement value
def Wasm.encode.sleb(v: U32) -> List<&2, Word(8n)>:
  Wasm.encode.sleb.go(5n, v)

# the number of items of a list
def Wasm.encode.len(-A: Data, xs: List<&2, A>) -> U32:
  match xs:
    case Nil{}:
      0
    case Con{_, rest}:
      U32.inc(Wasm.encode.len(A, rest))

# a vector (spec 5.1.3): the number n of its items, then their bytes
def Wasm.encode.vec(n: U32, items: List<&2, Word(8n)>) -> List<&2, Word(8n)>:
  List.append(&2, Word(8n), Wasm.encode.uleb(n), items)

# bytes after their number: a vector of bytes or a name (spec 5.1.3, 5.2.4)
def Wasm.encode.sized(+c: List<&2, Word(8n)>) -> List<&2, Word(8n)>:
  Wasm.encode.vec(Wasm.encode.len(Word(8n), c), c)

def Wasm.encode.opcode(o: Wa.Wasm.Op) -> U32:
  match o:
    case Wa.Wasm.Op.add{}:
      106
    case Wa.Wasm.Op.sub{}:
      107
    case Wa.Wasm.Op.and{}:
      113
    case Wa.Wasm.Op.or{}:
      114
    case Wa.Wasm.Op.shl{}:
      116
    case Wa.Wasm.Op.shr_u{}:
      118
    case Wa.Wasm.Op.eq{}:
      70
    case Wa.Wasm.Op.ne{}:
      71
    case Wa.Wasm.Op.lt_u{}:
      73
    case Wa.Wasm.Op.gt_u{}:
      75
    case Wa.Wasm.Op.le_u{}:
      77
    case Wa.Wasm.Op.ge_u{}:
      79

# an opcode and its immediate, then the bytes acc
def Wasm.encode.with(op: U32, imm: List<&2, Word(8n)>, acc: List<&2, Word(8n)>) -> List<&2, Word(8n)>:
  Con{Sd.Byte.from_u32(op), List.append(&2, Word(8n), imm, acc)}

# the instructions xs (spec 5.4), then the bytes acc; a load or a store names
# the natural alignment of its width
def Wasm.encode.instrs(xs: List<&2, Wa.Wasm.Instr>, acc: List<&2, Word(8n)>) -> List<&2, Word(8n)>:
  match xs:
    case Nil{}:
      acc
    case Con{x, rest}:
      match x:
        case Wa.Wasm.Instr.const{n}:
          Wasm.encode.with(65, Wasm.encode.sleb(n), Wasm.encode.instrs(rest, acc))
        case Wa.Wasm.Instr.local_get{i}:
          Wasm.encode.with(32, Wasm.encode.uleb(i), Wasm.encode.instrs(rest, acc))
        case Wa.Wasm.Instr.local_set{i}:
          Wasm.encode.with(33, Wasm.encode.uleb(i), Wasm.encode.instrs(rest, acc))
        case Wa.Wasm.Instr.local_tee{i}:
          Wasm.encode.with(34, Wasm.encode.uleb(i), Wasm.encode.instrs(rest, acc))
        case Wa.Wasm.Instr.op{o}:
          Con{Sd.Byte.from_u32(Wasm.encode.opcode(o)), Wasm.encode.instrs(rest, acc)}
        case Wa.Wasm.Instr.eqz{}:
          Con{Sd.Byte.from_u32(69), Wasm.encode.instrs(rest, acc)}
        case Wa.Wasm.Instr.load{o}:
          Wasm.encode.with(40, Con{Sd.Byte.from_u32(2), Wasm.encode.uleb(o)}, Wasm.encode.instrs(rest, acc))
        case Wa.Wasm.Instr.load8_u{o}:
          Wasm.encode.with(45, Con{Sd.Byte.from_u32(0), Wasm.encode.uleb(o)}, Wasm.encode.instrs(rest, acc))
        case Wa.Wasm.Instr.store{o}:
          Wasm.encode.with(54, Con{Sd.Byte.from_u32(2), Wasm.encode.uleb(o)}, Wasm.encode.instrs(rest, acc))
        case Wa.Wasm.Instr.store8{o}:
          Wasm.encode.with(58, Con{Sd.Byte.from_u32(0), Wasm.encode.uleb(o)}, Wasm.encode.instrs(rest, acc))
        case Wa.Wasm.Instr.memory_size{}:
          Con{Sd.Byte.from_u32(63), Con{Sd.Byte.from_u32(0), Wasm.encode.instrs(rest, acc)}}
        case Wa.Wasm.Instr.memory_grow{}:
          Con{Sd.Byte.from_u32(64), Con{Sd.Byte.from_u32(0), Wasm.encode.instrs(rest, acc)}}
        case Wa.Wasm.Instr.block{body}:
          Con{Sd.Byte.from_u32(2), Con{Sd.Byte.from_u32(64), Wasm.encode.instrs(body, Con{Sd.Byte.from_u32(11), Wasm.encode.instrs(rest, acc)})}}
        case Wa.Wasm.Instr.loop{body}:
          Con{Sd.Byte.from_u32(3), Con{Sd.Byte.from_u32(64), Wasm.encode.instrs(body, Con{Sd.Byte.from_u32(11), Wasm.encode.instrs(rest, acc)})}}
        case Wa.Wasm.Instr.br{l}:
          Wasm.encode.with(12, Wasm.encode.uleb(l), Wasm.encode.instrs(rest, acc))
        case Wa.Wasm.Instr.br_if{l}:
          Wasm.encode.with(13, Wasm.encode.uleb(l), Wasm.encode.instrs(rest, acc))

# the value type i32, n times
def Wasm.encode.i32s(n: Nat) -> List<&2, Word(8n)>:
  match n:
    case 0n:
      []
    case 1n+p:
      Con{Sd.Byte.from_u32(127), Wasm.encode.i32s(p)}

# a function's type (spec 5.3.6): 0x60, then its parameters and results
def Wasm.encode.functype(f: Wa.Wasm.Func) -> List<&2, Word(8n)>:
  match f:
    case Wa.Wasm.Func{p, q, _, _}:
      Con{Sd.Byte.from_u32(96), List.append(&2, Word(8n), Wasm.encode.sized(Wasm.encode.i32s(p)), Wasm.encode.sized(Wasm.encode.i32s(q)))}

def Wasm.encode.functypes(fs: List<&2, Wa.Wasm.Func>) -> List<&2, Word(8n)>:
  match fs:
    case Nil{}:
      []
    case Con{f, rest}:
      List.append(&2, Word(8n), Wasm.encode.functype(f), Wasm.encode.functypes(rest))

# the function section: function i has type i
def Wasm.encode.indices(fs: List<&2, Wa.Wasm.Func>, +i: U32) -> List<&2, Word(8n)>:
  match fs:
    case Nil{}:
      []
    case Con{_, rest}:
      List.append(&2, Word(8n), Wasm.encode.uleb(i), Wasm.encode.indices(rest, U32.inc(i)))

# a function's locals after its parameters (spec 5.5.13): one group of n
# locals of i32, or none
def Wasm.encode.locals(+n: Nat) -> List<&2, Word(8n)>:
  match n:
    case 0n:
      [Sd.Byte.from_u32(0)]
    case 1n+_:
      Con{Sd.Byte.from_u32(1), List.append(&2, Word(8n), Wasm.encode.uleb(U32.from_nat(n)), [Sd.Byte.from_u32(127)])}

# a function's code (spec 5.5.13): its size, its locals, its body and its end
def Wasm.encode.code(f: Wa.Wasm.Func) -> List<&2, Word(8n)>:
  match f:
    case Wa.Wasm.Func{_, _, n, body}:
      Wasm.encode.sized(List.append(&2, Word(8n), Wasm.encode.locals(n), Wasm.encode.instrs(body, [Sd.Byte.from_u32(11)])))

def Wasm.encode.codes(fs: List<&2, Wa.Wasm.Func>) -> List<&2, Word(8n)>:
  match fs:
    case Nil{}:
      []
    case Con{f, rest}:
      List.append(&2, Word(8n), Wasm.encode.code(f), Wasm.encode.codes(rest))

# an export (spec 5.5.10): its name, then 0 and a function index, or 2 and
# memory 0
def Wasm.encode.export(e: Wa.Wasm.Export) -> List<&2, Word(8n)>:
  match e:
    case Wa.Wasm.Export.func{name, i}:
      List.append(&2, Word(8n), Wasm.encode.sized(name), Con{Sd.Byte.from_u32(0), Wasm.encode.uleb(i)})
    case Wa.Wasm.Export.memory{name}:
      List.append(&2, Word(8n), Wasm.encode.sized(name), [Sd.Byte.from_u32(2), Sd.Byte.from_u32(0)])

def Wasm.encode.exports(es: List<&2, Wa.Wasm.Export>) -> List<&2, Word(8n)>:
  match es:
    case Nil{}:
      []
    case Con{e, rest}:
      List.append(&2, Word(8n), Wasm.encode.export(e), Wasm.encode.exports(rest))

# a section (spec 5.5.2): its id, its size and its content c; then the bytes
# acc
def Wasm.encode.section(id: U32, c: List<&2, Word(8n)>, acc: List<&2, Word(8n)>) -> List<&2, Word(8n)>:
  Con{Sd.Byte.from_u32(id), List.append(&2, Word(8n), Wasm.encode.sized(c), acc)}

# the memory section, when there is a memory: one memory, of limits 0 and a
# minimum (spec 5.3.7)
def Wasm.encode.memory(m: Maybe<&2, Wa.Wasm.Limits>, acc: List<&2, Word(8n)>) -> List<&2, Word(8n)>:
  match m:
    case None{}:
      acc
    case Some{Wa.Wasm.Limits{min}}:
      Wasm.encode.section(5, Con{Sd.Byte.from_u32(1), Con{Sd.Byte.from_u32(0), Wasm.encode.uleb(min)}}, acc)

# the data section, when there is a segment: 0, an active segment of memory
# 0, its offset as the constant expression i32.const n end, then its bytes
def Wasm.encode.data(d: Maybe<&2, Wa.Wasm.Segment>) -> List<&2, Word(8n)>:
  match d:
    case None{}:
      []
    case Some{Wa.Wasm.Segment{o, bs}}:
      Wasm.encode.section(11, Con{Sd.Byte.from_u32(1), Con{Sd.Byte.from_u32(0), Con{Sd.Byte.from_u32(65),
        List.append(&2, Word(8n), Wasm.encode.sleb(o), Con{Sd.Byte.from_u32(11), Wasm.encode.sized(bs)})}}}, [])

# a module of the subset (spec 5.5.15): its header, then its sections in the
# order of their ids; function i has type i
def Wasm.encode(m: Wa.Wasm.Module) -> List<&2, Word(8n)>:
  match m:
    case Wa.Wasm.Module{+fs, mem, +es, d}:
      +n = Wasm.encode.len(Wa.Wasm.Func, fs)
      List.append(&2, Word(8n), Wa.Wasm.header(),
        Wasm.encode.section(1, Wasm.encode.vec(n, Wasm.encode.functypes(fs)),
          Wasm.encode.section(3, Wasm.encode.vec(n, Wasm.encode.indices(fs, 0)),
            Wasm.encode.memory(mem,
              Wasm.encode.section(7, Wasm.encode.vec(Wasm.encode.len(Wa.Wasm.Export, es), Wasm.encode.exports(es)),
                Wasm.encode.section(10, Wasm.encode.vec(n, Wasm.encode.codes(fs)), Wasm.encode.data(d)))))))

# Cir
# ---
#
# The language of the machine: statements over U32 registers, a memory of
# cells of five U32 fields, the input's bytes and the output's. Cell c is the
# 20 bytes from byte 20 × c of the module's memory: cells 1 to `image` hold
# the book, the input's bytes follow them, and the machine's own cells start
# at `first`. The memory grows by the pages that an access needs, as in the
# module that Cir.module makes, so that Cir.exec says what that module does. An access that the module could
# not make in the same way traps: the machine makes none.

# a cell: five fields
type Cir.Cell is Data:
  Cir.Cell{f0: U32, f1: U32, f2: U32, f3: U32, f4: U32}

def Cir.Cell.zero() -> Cir.Cell:
  Cir.Cell{0, 0, 0, 0, 0}

# field k of a cell, from 0 to 4
def Cir.Cell.get(k: Nat, c: Cir.Cell) -> U32:
  match k c:
    case 0n Cir.Cell{a, _, _, _, _}:
      a
    case 1n Cir.Cell{_, b, _, _, _}:
      b
    case 2n Cir.Cell{_, _, x, _, _}:
      x
    case 3n Cir.Cell{_, _, _, y, _}:
      y
    case _ Cir.Cell{_, _, _, _, z}:
      z

def Cir.Cell.set(k: Nat, c: Cir.Cell, v: U32) -> Cir.Cell:
  match k c:
    case 0n Cir.Cell{_, b, x, y, z}:
      Cir.Cell{v, b, x, y, z}
    case 1n Cir.Cell{a, _, x, y, z}:
      Cir.Cell{a, v, x, y, z}
    case 2n Cir.Cell{a, b, _, y, z}:
      Cir.Cell{a, b, v, y, z}
    case 3n Cir.Cell{a, b, x, _, z}:
      Cir.Cell{a, b, x, v, z}
    case _ Cir.Cell{a, b, x, y, _}:
      Cir.Cell{a, b, x, y, v}

# the cells, by the bits of their number, the lowest first; a missing cell is
# all zeros
type Cir.Cells is Data:
  Cir.Cells.none{}
  Cir.Cells.one{c: Cir.Cell}
  Cir.Cells.node{lo: Cir.Cells, hi: Cir.Cells}

def Cir.Cells.get.at(n: Nat, w: Word(n), m: Cir.Cells) -> Cir.Cell:
  match n:
    case 0n:
      match m:
        case Cir.Cells.one{c}:
          c
        case _:
          Cir.Cell.zero()
    case 1n+p:
      match w:
        case WCon{bit, t}:
          match bit m:
            case False{} Cir.Cells.node{lo, _}:
              Cir.Cells.get.at(p, t, lo)
            case True{} Cir.Cells.node{_, hi}:
              Cir.Cells.get.at(p, t, hi)
            case _ _:
              Cir.Cell.zero()

def Cir.Cells.set.at(n: Nat, w: Word(n), m: Cir.Cells, c: Cir.Cell) -> Cir.Cells:
  match n:
    case 0n:
      Cir.Cells.one{c}
    case 1n+p:
      match w:
        case WCon{bit, t}:
          match bit m:
            case False{} Cir.Cells.node{lo, hi}:
              Cir.Cells.node{Cir.Cells.set.at(p, t, lo, c), hi}
            case True{} Cir.Cells.node{lo, hi}:
              Cir.Cells.node{lo, Cir.Cells.set.at(p, t, hi, c)}
            case False{} _:
              Cir.Cells.node{Cir.Cells.set.at(p, t, Cir.Cells.none{}, c), Cir.Cells.none{}}
            case True{} _:
              Cir.Cells.node{Cir.Cells.none{}, Cir.Cells.set.at(p, t, Cir.Cells.none{}, c)}

# the cell numbered i
def Cir.Cells.get(m: Cir.Cells, i: U32) -> Cir.Cell:
  match i:
    case U32{w}:
      Cir.Cells.get.at(32n, w, m)

def Cir.Cells.set(m: Cir.Cells, i: U32, c: Cir.Cell) -> Cir.Cells:
  match i:
    case U32{w}:
      Cir.Cells.set.at(32n, w, m, c)

# the registers r of a Cir program are Nat; its cells' fields are numbered 0
# to 4
type Cir.Expr is Data:
  Cir.Expr.const{n: U32}
  Cir.Expr.get{r: Nat}
  Cir.Expr.op{op: Wa.Wasm.Op, a: Cir.Expr, b: Cir.Expr}
  Cir.Expr.eqz{a: Cir.Expr}
  Cir.Expr.field{k: Nat, c: Cir.Expr}
  Cir.Expr.byte{i: Cir.Expr}
  Cir.Expr.size{}

# a while repeats its body while its condition is not 0; halt ends the run
# with a status: 0 a result, 2 no result
type Cir.Stmt is Data:
  Cir.Stmt.nop{}
  Cir.Stmt.set{r: Nat, e: Cir.Expr}
  Cir.Stmt.store{k: Nat, c: Cir.Expr, v: Cir.Expr}
  Cir.Stmt.alloc{r: Nat}
  Cir.Stmt.emit{v: Cir.Expr}
  Cir.Stmt.seq{a: Cir.Stmt, b: Cir.Stmt}
  Cir.Stmt.if{c: Cir.Expr, t: Cir.Stmt, e: Cir.Stmt}
  Cir.Stmt.while{c: Cir.Expr, body: Cir.Stmt}
  Cir.Stmt.halt{s: U32}

# the state of a run: the registers; the cells, the first never used (next),
# the first of the machine's own (first) and the last of the book's (image);
# the memory's size and the limit of its growth, in pages; the input; and the
# output, the last byte first, with its length
type Cir.State is Data:
  Cir.State{
    regs: List<&2, U32>, cells: Cir.Cells, next: U32, first: U32, image: U32,
    pages: U32, limit: U32, input: List<&2, Word(8n)>, out: List<&2, Word(8n)>, outn: U32}

# how a statement ends: after it, with the state; halted, with a status; out
# of memory; with an access that the module could not make in the same way;
# or out of fuel
type Cir.Out is Data:
  Cir.Out.next{st: Cir.State}
  Cir.Out.halt{s: U32, st: Cir.State}
  Cir.Out.out_of_memory{}
  Cir.Out.trap{}
  Cir.Out.not_done{}

# the cell i is one the machine may use: one of the book's, or one of its own
# that it took
def Cir.is_cell(+i: U32, +image: U32, +first: U32, +next: U32) -> Bool:
  (Bool.not(U32.is_zero(i)) && U32.is_le(i, image)) || (U32.is_le(first, i) && U32.is_lt(i, next))

def Cir.eval.op(o: Wa.Wasm.Op, a: Maybe<&2, U32>, b: Maybe<&2, U32>) -> Maybe<&2, U32>:
  match a b:
    case Some{x} Some{y}:
      Some{Wa.Wasm.op(o, x, y)}
    case _ _:
      None{}

def Cir.eval.eqz(a: Maybe<&2, U32>) -> Maybe<&2, U32>:
  match a:
    case Some{x}:
      Some{Bool.to_u32(U32.is_zero(x))}
    case None{}:
      None{}

def Cir.eval.field.if(ok: Bool, k: Nat, cells: Cir.Cells, i: U32) -> Maybe<&2, U32>:
  match ok:
    case True{}:
      Some{Cir.Cell.get(k, Cir.Cells.get(cells, i))}
    case False{}:
      None{}

def Cir.eval.field(k: Nat, c: Maybe<&2, U32>, st: Cir.State) -> Maybe<&2, U32>:
  match c st:
    case Some{+i} Cir.State{_, cells, next, first, image, _, _, _, _, _}:
      Cir.eval.field.if(Cir.is_cell(i, image, first, next), k, cells, i)
    case None{} _:
      None{}

def Cir.eval.byte.of(b: Maybe<&2, Word(8n)>) -> Maybe<&2, U32>:
  match b:
    case Some{x}:
      Some{Sd.Byte.to_u32(x)}
    case None{}:
      None{}

# the value of the input's byte i
def Cir.eval.byte(i: Maybe<&2, U32>, input: List<&2, Word(8n)>) -> Maybe<&2, U32>:
  match i:
    case Some{x}:
      Cir.eval.byte.of(List.get(&2, Word(8n), input, U32.to_nat(x)))
    case None{}:
      None{}

def Cir.eval.size(st: Cir.State) -> Maybe<&2, U32>:
  match st:
    case Cir.State{_, _, _, _, _, _, _, input, _, _}:
      Some{Wasm.encode.len(Word(8n), input)}

def Cir.eval.get(r: Nat, st: Cir.State) -> Maybe<&2, U32>:
  match st:
    case Cir.State{regs, _, _, _, _, _, _, _, _, _}:
      List.get(&2, U32, regs, r)

def Cir.eval.input(st: Cir.State) -> List<&2, Word(8n)>:
  match st:
    case Cir.State{_, _, _, _, _, _, _, input, _, _}:
      input

# the value of an expression; nothing for an access that traps
def Cir.eval(e: Cir.Expr, +st: Cir.State) -> Maybe<&2, U32>:
  match e:
    case Cir.Expr.const{n}:
      Some{n}
    case Cir.Expr.get{r}:
      Cir.eval.get(r, st)
    case Cir.Expr.op{o, a, b}:
      Cir.eval.op(o, Cir.eval(a, st), Cir.eval(b, st))
    case Cir.Expr.eqz{a}:
      Cir.eval.eqz(Cir.eval(a, st))
    case Cir.Expr.field{k, c}:
      Cir.eval.field(k, Cir.eval(c, st), st)
    case Cir.Expr.byte{i}:
      Cir.eval.byte(Cir.eval(i, st), Cir.eval.input(st))
    case Cir.Expr.size{}:
      Cir.eval.size(st)

def Cir.regs.set.if(ok: Bool, regs: List<&2, U32>, r: Nat, v: U32) -> Maybe<&2, List<&2, U32>>:
  match ok:
    case True{}:
      Some{List.set(&2, U32, regs, r, v)}
    case False{}:
      None{}

# the registers with r set to v, when there is a register r
def Cir.regs.set(+regs: List<&2, U32>, +r: Nat, v: U32) -> Maybe<&2, List<&2, U32>>:
  Cir.regs.set.if(Nat.is_lt(r, List.length(&2, U32, regs)), regs, r, v)

def Cir.exec.set.of(regs: Maybe<&2, List<&2, U32>>, st: Cir.State) -> Cir.Out:
  match regs st:
    case Some{rs} Cir.State{_, cells, next, first, image, pages, limit, input, out, outn}:
      Cir.Out.next{Cir.State{rs, cells, next, first, image, pages, limit, input, out, outn}}
    case None{} _:
      Cir.Out.trap{}

def Cir.exec.set(r: Nat, v: Maybe<&2, U32>, +st: Cir.State) -> Cir.Out:
  match v st:
    case Some{x} Cir.State{regs, _, _, _, _, _, _, _, _, _}:
      Cir.exec.set.of(Cir.regs.set(regs, r, x), st)
    case None{} _:
      Cir.Out.trap{}

def Cir.exec.store.if(ok: Bool, k: Nat, +i: U32, v: U32, st: Cir.State) -> Cir.Out:
  match ok st:
    case True{} Cir.State{regs, +cells, next, first, image, pages, limit, input, out, outn}:
      Cir.Out.next{Cir.State{regs, Cir.Cells.set(cells, i, Cir.Cell.set(k, Cir.Cells.get(cells, i), v)), next, first, image, pages, limit, input, out, outn}}
    case False{} _:
      Cir.Out.trap{}

def Cir.exec.store(k: Nat, c: Maybe<&2, U32>, v: Maybe<&2, U32>, +st: Cir.State) -> Cir.Out:
  match c v st:
    case Some{+i} Some{x} Cir.State{_, _, +next, +first, +image, _, _, _, _, _}:
      Cir.exec.store.if(Cir.is_cell(i, image, first, next), k, i, x, st)
    case _ _ _:
      Cir.Out.trap{}

# a register holds the cell i, made all zeros
def Cir.exec.took(r: Nat, +i: U32, st: Cir.State, next: U32, pages: U32) -> Cir.Out:
  match st:
    case Cir.State{regs, cells, _, first, image, _, limit, input, out, outn}:
      Cir.exec.set(r, Some{i},
        Cir.State{regs, Cir.Cells.set(cells, i, Cir.Cell.zero()), next, first, image, pages, limit, input, out, outn})

def Cir.room.if(inside: Bool, can_grow: Bool, p: U32, need: U32) -> Maybe<&2, U32>:
  match inside can_grow:
    case True{} _:
      Some{p}
    case False{} True{}:
      Some{need}
    case False{} False{}:
      None{}

# the pages that the memory has once the byte b is in it, when it holds p
# pages and may grow to lim: (b >> 16) + 1 at least; none when it cannot grow
# that far
def Cir.room(b: U32, +p: U32, +lim: U32) -> Maybe<&2, U32>:
  +need = U32.inc(U32.shrn(b, 16n))
  Cir.room.if(U32.is_le(need, p), U32.is_le(need, lim), p, need)

# 20 × c, the first byte of the cell c
def Cir.at(+c: U32) -> U32:
  U32.add(U32.shln(c, 4n), U32.shln(c, 2n))

def Cir.exec.bump.of(r: Nat, +next: U32, st: Cir.State, pages: Maybe<&2, U32>) -> Cir.Out:
  match pages:
    case Some{p}:
      Cir.exec.took(r, next, st, U32.inc(next), p)
    case None{}:
      Cir.Out.out_of_memory{}

def Cir.exec.bump.if(fits: Bool, r: Nat, +next: U32, +pages: U32, lim: U32, st: Cir.State) -> Cir.Out:
  match fits:
    case True{}:
      Cir.exec.bump.of(r, next, st, Cir.room(U32.add(Cir.at(next), 19), pages, lim))
    case False{}:
      Cir.Out.out_of_memory{}

def Cir.exec.alloc.if(no_out: Bool, r: Nat, +st: Cir.State) -> Cir.Out:
  match no_out st:
    case True{} Cir.State{_, _, +next, _, _, +pages, lim, _, _, _}:
      Cir.exec.bump.if(U32.is_lt(next, 214748364), r, next, pages, lim, st)
    case False{} _:
      Cir.Out.trap{}

# a register gets a new cell, all zeros, which may grow the memory; out of
# memory when the memory cannot grow. Once
# the output has begun, no cell may be taken: they would overlap
def Cir.exec.alloc(r: Nat, +st: Cir.State) -> Cir.Out:
  match st:
    case Cir.State{_, _, _, _, _, _, _, _, _, outn}:
      Cir.exec.alloc.if(U32.is_zero(outn), r, st)

def Cir.exec.emit.of(pages: Maybe<&2, U32>, v: U32, st: Cir.State) -> Cir.Out:
  match pages st:
    case Some{p} Cir.State{regs, cells, next, first, image, _, limit, input, out, outn}:
      Cir.Out.next{Cir.State{regs, cells, next, first, image, p, limit, input, Con{Sd.Byte.from_u32(v), out}, U32.inc(outn)}}
    case None{} _:
      Cir.Out.out_of_memory{}

def Cir.exec.emit.if(ok: Bool, +b: U32, v: U32, +st: Cir.State) -> Cir.Out:
  match ok st:
    case True{} Cir.State{_, _, _, _, _, +pages, lim, _, _, _}:
      Cir.exec.emit.of(Cir.room(b, pages, lim), v, st)
    case False{} _:
      Cir.Out.out_of_memory{}

# the low byte of v goes at the end of the output, which lies after
# the cells, at byte 20 × next; out of memory when the memory cannot grow to
# hold it
def Cir.exec.emit(v: Maybe<&2, U32>, +st: Cir.State) -> Cir.Out:
  match v st:
    case Some{x} Cir.State{_, _, +next, _, _, _, _, _, _, +outn}:
      +b = U32.add(Cir.at(next), outn)
      Cir.exec.emit.if(U32.is_lt(next, 214748365) && U32.is_ge(b, outn), b, x, st)
    case None{} _:
      Cir.Out.trap{}

def Cir.exec.then(r: Cir.Out, more: Cir.State -> Cir.Out) -> Cir.Out:
  match r:
    case Cir.Out.next{st}:
      more(st)
    case Cir.Out.halt{s, st}:
      Cir.Out.halt{s, st}
    case Cir.Out.out_of_memory{}:
      Cir.Out.out_of_memory{}
    case Cir.Out.trap{}:
      Cir.Out.trap{}
    case Cir.Out.not_done{}:
      Cir.Out.not_done{}

def Cir.exec.if.of(zero: Bool, yes: Unit -> Cir.Out, no: Unit -> Cir.Out) -> Cir.Out:
  match zero:
    case False{}:
      yes(Unit{})
    case True{}:
      no(Unit{})

def Cir.exec.if(c: Maybe<&2, U32>, yes: Unit -> Cir.Out, no: Unit -> Cir.Out) -> Cir.Out:
  match c:
    case Some{x}:
      Cir.exec.if.of(U32.is_zero(x), yes, no)
    case None{}:
      Cir.Out.trap{}

# a run of the statement s from the state st; each round of a while takes a
# unit of fuel
def Cir.exec(+fuel: Nat, s: Cir.Stmt, +st: Cir.State) -> Cir.Out:
  match fuel s:
    case _ Cir.Stmt.nop{}:
      Cir.Out.next{st}
    case _ Cir.Stmt.set{r, e}:
      Cir.exec.set(r, Cir.eval(e, st), st)
    case _ Cir.Stmt.store{k, c, v}:
      Cir.exec.store(k, Cir.eval(c, st), Cir.eval(v, st), st)
    case _ Cir.Stmt.alloc{r}:
      Cir.exec.alloc(r, st)
    case _ Cir.Stmt.emit{v}:
      Cir.exec.emit(Cir.eval(v, st), st)
    case _ Cir.Stmt.seq{a, b}:
      Cir.exec.then(Cir.exec(fuel, a, st), t => Cir.exec(fuel, b, t))
    case _ Cir.Stmt.if{c, t, e}:
      Cir.exec.if(Cir.eval(c, st), u => Cir.exec(fuel, t, st), u => Cir.exec(fuel, e, st))
    case 0n Cir.Stmt.while{_, _}:
      Cir.Out.not_done{}
    case 1n+f Cir.Stmt.while{+c, +body}:
      Cir.exec.if(Cir.eval(c, st),
        u => Cir.exec.then(Cir.exec(f, body, st), t => Cir.exec(f, Cir.Stmt.while{c, body}, t)),
        u => Cir.Out.next{st})
    case _ Cir.Stmt.halt{s}:
      Cir.Out.halt{s, st}

# Translation
# -----------
#
# Cir.module: the module of a Cir program, with the book's cells as the data
# of its memory, from byte 20. Its function run (see Host) keeps, in its locals 2 to
# 7, the status it returns, the first cell never used, the output's length and
# three scratch values; register r of the program is local 8 + r. Every
# branch out of run is the last instruction of a block of its own, as the subset asks. Its
# function alloc takes the input's bytes just after the book's cells.

def Cir.l.status() -> U32:
  2

def Cir.l.next() -> U32:
  3

def Cir.l.outn() -> U32:
  4

def Cir.l.tmp() -> U32:
  5

def Cir.l.need() -> U32:
  6

def Cir.l.addr() -> U32:
  7

def Cir.l.reg(r: Nat) -> U32:
  U32.add(8, U32.from_nat(r))

def Cir.i.get(l: U32) -> Wa.Wasm.Instr:
  Wa.Wasm.Instr.local_get{l}

def Cir.i.set(l: U32) -> Wa.Wasm.Instr:
  Wa.Wasm.Instr.local_set{l}

def Cir.i.op(o: Wa.Wasm.Op) -> Wa.Wasm.Instr:
  Wa.Wasm.Instr.op{o}

def Cir.i.const(n: U32) -> Wa.Wasm.Instr:
  Wa.Wasm.Instr.const{n}

# the cell number on the stack, turned into its first byte, 20 × c; then acc
def Cir.code.at(acc: List<&2, Wa.Wasm.Instr>) -> List<&2, Wa.Wasm.Instr>:
  Con{Wa.Wasm.Instr.local_tee{Cir.l.tmp()}, Con{Cir.i.const(4), Con{Cir.i.op(Wa.Wasm.Op.shl{}),
    Con{Cir.i.get(Cir.l.tmp()), Con{Cir.i.const(2), Con{Cir.i.op(Wa.Wasm.Op.shl{}),
      Con{Cir.i.op(Wa.Wasm.Op.add{}), acc}}}}}}}

# an expression, whose value it leaves on the stack; then acc
def Cir.code.expr(e: Cir.Expr, acc: List<&2, Wa.Wasm.Instr>) -> List<&2, Wa.Wasm.Instr>:
  match e:
    case Cir.Expr.const{n}:
      Con{Cir.i.const(n), acc}
    case Cir.Expr.get{r}:
      Con{Cir.i.get(Cir.l.reg(r)), acc}
    case Cir.Expr.op{o, a, b}:
      Cir.code.expr(a, Cir.code.expr(b, Con{Cir.i.op(o), acc}))
    case Cir.Expr.eqz{a}:
      Cir.code.expr(a, Con{Wa.Wasm.Instr.eqz{}, acc})
    case Cir.Expr.field{k, c}:
      Cir.code.expr(c, Cir.code.at(Con{Wa.Wasm.Instr.load{U32.shln(U32.from_nat(k), 2n)}, acc}))
    case Cir.Expr.byte{i}:
      Cir.code.expr(i, Con{Cir.i.get(0), Con{Cir.i.op(Wa.Wasm.Op.add{}), Con{Wa.Wasm.Instr.load8_u{0}, acc}}})
    case Cir.Expr.size{}:
      Con{Cir.i.get(1), acc}

# the status s, then a branch out of run: the label d + 1 levels out, from a
# block of its own at d levels inside run's block
def Cir.code.exit(s: U32, d: Nat) -> Wa.Wasm.Instr:
  Wa.Wasm.Instr.block{[Cir.i.const(s), Cir.i.set(Cir.l.status()), Wa.Wasm.Instr.br{U32.from_nat(1n+d)}]}

# the instructions cond, which leave a Bool; when it is 0, out of memory
def Cir.code.unless(cond: List<&2, Wa.Wasm.Instr>, d: Nat, acc: List<&2, Wa.Wasm.Instr>) -> List<&2, Wa.Wasm.Instr>:
  Con{Wa.Wasm.Instr.block{List.append(&2, Wa.Wasm.Instr, cond, [Wa.Wasm.Instr.br_if{0}, Cir.code.exit(1, 1n+d)])}, acc}

# the memory grows to the pages in local need, when it has fewer; out of
# memory when it cannot
def Cir.code.grow(d: Nat, acc: List<&2, Wa.Wasm.Instr>) -> List<&2, Wa.Wasm.Instr>:
  Con{Wa.Wasm.Instr.block{Con{Cir.i.get(Cir.l.need()), Con{Wa.Wasm.Instr.memory_size{}, Con{Cir.i.op(Wa.Wasm.Op.le_u{}),
    Con{Wa.Wasm.Instr.br_if{0},
      Cir.code.unless([Cir.i.get(Cir.l.need()), Wa.Wasm.Instr.memory_size{}, Cir.i.op(Wa.Wasm.Op.sub{}),
        Wa.Wasm.Instr.memory_grow{}, Cir.i.const(4294967295), Cir.i.op(Wa.Wasm.Op.ne{})], 1n+d, [])}}}}}, acc}

# the pages (b >> 16) + 1 that the byte b on the stack needs, into local need
def Cir.code.need(acc: List<&2, Wa.Wasm.Instr>) -> List<&2, Wa.Wasm.Instr>:
  Con{Cir.i.const(16), Con{Cir.i.op(Wa.Wasm.Op.shr_u{}), Con{Cir.i.const(1), Con{Cir.i.op(Wa.Wasm.Op.add{}),
    Con{Cir.i.set(Cir.l.need()), acc}}}}}

# the five fields of the cell at the byte in local addr, made 0
def Cir.code.zero(acc: List<&2, Wa.Wasm.Instr>) -> List<&2, Wa.Wasm.Instr>:
  Con{Cir.i.get(Cir.l.addr()), Con{Cir.i.const(0), Con{Wa.Wasm.Instr.store{0},
  Con{Cir.i.get(Cir.l.addr()), Con{Cir.i.const(0), Con{Wa.Wasm.Instr.store{4},
  Con{Cir.i.get(Cir.l.addr()), Con{Cir.i.const(0), Con{Wa.Wasm.Instr.store{8},
  Con{Cir.i.get(Cir.l.addr()), Con{Cir.i.const(0), Con{Wa.Wasm.Instr.store{12},
  Con{Cir.i.get(Cir.l.addr()), Con{Cir.i.const(0), Con{Wa.Wasm.Instr.store{16}, acc}}}}}}}}}}}}}}}

# Cir.exec.alloc: a new cell, when the memory can grow to hold it; then the
# cell made 0
def Cir.code.alloc(+r: U32, +d: Nat, acc: List<&2, Wa.Wasm.Instr>) -> List<&2, Wa.Wasm.Instr>:
  Cir.code.unless([Cir.i.get(Cir.l.next()), Cir.i.const(214748364), Cir.i.op(Wa.Wasm.Op.lt_u{})], d,
    Con{Cir.i.get(Cir.l.next()), Cir.code.at(Con{Cir.i.const(19), Con{Cir.i.op(Wa.Wasm.Op.add{}),
      Cir.code.need(Cir.code.grow(d,
        Con{Cir.i.get(Cir.l.next()), Con{Cir.i.set(r),
        Con{Cir.i.get(Cir.l.next()), Con{Cir.i.const(1), Con{Cir.i.op(Wa.Wasm.Op.add{}), Con{Cir.i.set(Cir.l.next()),
        Con{Cir.i.get(r), Cir.code.at(Con{Cir.i.set(Cir.l.addr()), Cir.code.zero(acc)})}}}}}}}))}})})

# Cir.exec.emit: the byte at 20 × next + outn, after the memory grows to hold
# it
def Cir.code.emit(v: Cir.Expr, +d: Nat, acc: List<&2, Wa.Wasm.Instr>) -> List<&2, Wa.Wasm.Instr>:
  Con{Cir.i.get(Cir.l.next()), Cir.code.at(Con{Cir.i.get(Cir.l.outn()), Con{Cir.i.op(Wa.Wasm.Op.add{}),
    Con{Cir.i.set(Cir.l.addr()),
      Cir.code.unless([Cir.i.get(Cir.l.next()), Cir.i.const(214748365), Cir.i.op(Wa.Wasm.Op.lt_u{}),
        Cir.i.get(Cir.l.addr()), Cir.i.get(Cir.l.outn()), Cir.i.op(Wa.Wasm.Op.ge_u{}), Cir.i.op(Wa.Wasm.Op.and{})], d,
        Con{Cir.i.get(Cir.l.addr()), Cir.code.need(Cir.code.grow(d,
          Con{Cir.i.get(Cir.l.addr()), Cir.code.expr(v, Con{Wa.Wasm.Instr.store8{0},
            Con{Cir.i.get(Cir.l.outn()), Con{Cir.i.const(1), Con{Cir.i.op(Wa.Wasm.Op.add{}),
              Con{Cir.i.set(Cir.l.outn()), acc}}}}})}))})}}})}

# for a result, the output's first byte, 20 × next, at byte 0, and its length
# at byte 4 (see Host)
def Cir.code.result(ok: Bool) -> List<&2, Wa.Wasm.Instr>:
  match ok:
    case True{}:
      Con{Cir.i.const(0), Con{Cir.i.get(Cir.l.next()), Cir.code.at(
        [Wa.Wasm.Instr.store{0}, Cir.i.const(0), Cir.i.get(Cir.l.outn()), Wa.Wasm.Instr.store{4}])}}
    case False{}:
      []

def Cir.code.halt(+s: U32, d: Nat) -> Wa.Wasm.Instr:
  Wa.Wasm.Instr.block{Con{Cir.i.const(s), Con{Cir.i.set(Cir.l.status()),
    List.append(&2, Wa.Wasm.Instr, Cir.code.result(U32.is_zero(s)), [Wa.Wasm.Instr.br{U32.from_nat(1n+d)}])}}}

# a statement at d levels inside run's block; then acc
def Cir.code.stmt(s: Cir.Stmt, +d: Nat, acc: List<&2, Wa.Wasm.Instr>) -> List<&2, Wa.Wasm.Instr>:
  match s:
    case Cir.Stmt.nop{}:
      acc
    case Cir.Stmt.set{r, e}:
      Cir.code.expr(e, Con{Cir.i.set(Cir.l.reg(r)), acc})
    case Cir.Stmt.store{k, c, v}:
      Cir.code.expr(c, Cir.code.at(Cir.code.expr(v, Con{Wa.Wasm.Instr.store{U32.shln(U32.from_nat(k), 2n)}, acc})))
    case Cir.Stmt.alloc{r}:
      Cir.code.alloc(Cir.l.reg(r), d, acc)
    case Cir.Stmt.emit{v}:
      Cir.code.emit(v, d, acc)
    case Cir.Stmt.seq{a, b}:
      Cir.code.stmt(a, d, Cir.code.stmt(b, d, acc))
    case Cir.Stmt.if{c, t, e}:
      Con{Wa.Wasm.Instr.block{Con{
        Wa.Wasm.Instr.block{Cir.code.expr(c, Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{0},
          Cir.code.stmt(t, 2n+d, [Wa.Wasm.Instr.br{1}])}})},
        Cir.code.stmt(e, 1n+d, [])}}, acc}
    case Cir.Stmt.while{c, body}:
      Con{Wa.Wasm.Instr.block{[Wa.Wasm.Instr.loop{Cir.code.expr(c, Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{1},
        Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])}})}]}, acc}
    case Cir.Stmt.halt{s}:
      Con{Cir.code.halt(s, d), acc}

# the first byte of the input: just after cells 0 to k
def Cir.input.at(k: U32) -> U32:
  Cir.at(U32.inc(k))

# alloc(n) (see Host): the first byte of the input's n bytes, just after the book's
# k cells, once the memory holds them; -1 when it cannot. The input ends below
# byte 4294967280, so that the cells after it have numbers below 2^32 / 20
def Cir.alloc(+k: U32) -> Wa.Wasm.Func:
  +a = Cir.input.at(k)
  Wa.Wasm.Func{1n, 1n, 3n, [
    Cir.i.const(4294967295), Cir.i.set(2),
    Cir.i.const(a), Cir.i.get(0), Cir.i.op(Wa.Wasm.Op.add{}), Cir.i.set(1),
    Wa.Wasm.Instr.block{[
      Cir.i.get(1), Cir.i.const(a), Cir.i.op(Wa.Wasm.Op.lt_u{}), Wa.Wasm.Instr.br_if{0},
      Cir.i.get(1), Cir.i.const(4294967280), Cir.i.op(Wa.Wasm.Op.gt_u{}), Wa.Wasm.Instr.br_if{0},
      Cir.i.get(1), Cir.i.const(1), Cir.i.op(Wa.Wasm.Op.sub{}), Cir.i.const(16), Cir.i.op(Wa.Wasm.Op.shr_u{}),
      Cir.i.const(1), Cir.i.op(Wa.Wasm.Op.add{}), Cir.i.set(3),
      Wa.Wasm.Instr.block{[
        Cir.i.get(3), Wa.Wasm.Instr.memory_size{}, Cir.i.op(Wa.Wasm.Op.le_u{}), Wa.Wasm.Instr.br_if{0},
        Cir.i.get(3), Wa.Wasm.Instr.memory_size{}, Cir.i.op(Wa.Wasm.Op.sub{}), Wa.Wasm.Instr.memory_grow{},
        Cir.i.const(4294967295), Cir.i.op(Wa.Wasm.Op.eq{}), Wa.Wasm.Instr.br_if{1}]},
      Cir.i.const(a), Cir.i.set(2)]},
    Cir.i.get(2)]}

# run(a, n) (see Host): the first cell after the input, then the program; the
# status that it ends with
def Cir.run(prog: Cir.Stmt, regs: Nat, k: U32) -> Wa.Wasm.Func:
  Wa.Wasm.Func{2n, 1n, 6n+regs, [
    Cir.i.const(2), Cir.i.set(Cir.l.status()),
    Cir.i.get(0), Cir.i.get(1), Cir.i.op(Wa.Wasm.Op.add{}), Cir.i.set(Cir.l.addr()),
    Cir.i.const(U32.inc(k)), Cir.i.set(Cir.l.next()),
    Wa.Wasm.Instr.block{[Wa.Wasm.Instr.loop{Con{Cir.i.get(Cir.l.next()), Cir.code.at(
      [Cir.i.get(Cir.l.addr()), Cir.i.op(Wa.Wasm.Op.ge_u{}), Wa.Wasm.Instr.br_if{1},
       Cir.i.get(Cir.l.next()), Cir.i.const(1), Cir.i.op(Wa.Wasm.Op.add{}), Cir.i.set(Cir.l.next()),
       Wa.Wasm.Instr.br{0}])}}]},
    Wa.Wasm.Instr.block{Cir.code.stmt(prog, 0n, [])},
    Cir.i.get(Cir.l.status())]}

# the pages that bytes 0 to b - 1 need, for b above 0
def Cir.pages(b: U32) -> U32:
  U32.inc(U32.shrn(U32.sub(b, 1), 16n))

# the bytes of the word w, the lowest first; then acc
def Cir.word.bytes(+w: U32, acc: List<&2, Word(8n)>) -> List<&2, Word(8n)>:
  Con{Sd.Byte.from_u32(w), Con{Sd.Byte.from_u32(U32.shrn(w, 8n)), Con{Sd.Byte.from_u32(U32.shrn(w, 16n)),
    Con{Sd.Byte.from_u32(U32.shrn(w, 24n)), acc}}}}

# the bytes of the cells, 20 for each: its fields in order
def Cir.bytes(cs: List<&2, Cir.Cell>) -> List<&2, Word(8n)>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{Cir.Cell{a, b, c, d, e}, rest}:
      Cir.word.bytes(a, Cir.word.bytes(b, Cir.word.bytes(c, Cir.word.bytes(d, Cir.word.bytes(e, Cir.bytes(rest))))))

# the module of the program prog with regs registers, whose memory holds the
# cells from cell 1: memory, alloc and run
def Cir.module(prog: Cir.Stmt, regs: Nat, +cells: List<&2, Cir.Cell>) -> Wa.Wasm.Module:
  +k = Wasm.encode.len(Cir.Cell, cells)
  Wa.Wasm.Module{
    [Cir.alloc(k), Cir.run(prog, regs, k)],
    Some{Wa.Wasm.Limits{Cir.pages(Cir.input.at(k))}},
    [Wa.Wasm.Export.memory{Wa.Wasm.name.memory()}, Wa.Wasm.Export.func{Wa.Wasm.name.alloc(), 0},
     Wa.Wasm.Export.func{Wa.Wasm.name.run(), 1}],
    Some{Wa.Wasm.Segment{20, Cir.bytes(cells)}}}

# Runs
# ----
#
# Cir.result: what Cir says that a run of the module of Cir.module gives, as
# the host runs it (see Host): the memory of the module's minimum, when the host
# allows that many pages; the input after the cells, when alloc can make
# room for it; then the program, from the first cell after the input, until
# it halts: with 0, its bytes; with 1, out of memory; with 2, no result.

# the cells cs, from the cell i on
def Cir.load(cs: List<&2, Cir.Cell>, +i: U32, m: Cir.Cells) -> Cir.Cells:
  match cs:
    case Nil{}:
      m
    case Con{c, rest}:
      Cir.load(rest, U32.inc(i), Cir.Cells.set(m, i, c))

def Cir.ended.halt(zero: Bool, one: Bool, two: Bool, out: List<&2, Word(8n)>) -> Wa.Wasm.Outcome:
  match zero one two:
    case True{} _ _:
      Wa.Wasm.Outcome.result{List.reverse(&2, Word(8n), out)}
    case False{} True{} _:
      Wa.Wasm.Outcome.out_of_memory{}
    case False{} False{} True{}:
      Wa.Wasm.Outcome.no_result{}
    case False{} False{} False{}:
      Wa.Wasm.Outcome.trap{}

# how a run ends, by how its program ended; past its end, run gives the
# status 2
def Cir.ended(r: Cir.Out) -> Wa.Wasm.Outcome:
  match r:
    case Cir.Out.next{_}:
      Wa.Wasm.Outcome.no_result{}
    case Cir.Out.halt{+s, Cir.State{_, _, _, _, _, _, _, _, out, _}}:
      Cir.ended.halt(U32.is_eq(s, 0), U32.is_eq(s, 1), U32.is_eq(s, 2), out)
    case Cir.Out.out_of_memory{}:
      Wa.Wasm.Outcome.out_of_memory{}
    case Cir.Out.trap{}:
      Wa.Wasm.Outcome.trap{}
    case Cir.Out.not_done{}:
      Wa.Wasm.Outcome.not_done{}

# the first cell after the image's k cells whose first byte is past end, as
# run's first loop finds it: (end - 1) / 20 + 1 is end / 20 rounded up, with no
# wrap, since end is at least 20
def Cir.first(+k: U32, +end: U32) -> U32:
  Bool.pick(U32, U32.is_ge(Cir.at(U32.inc(k)), end), U32.inc(k), U32.inc(U32.div(U32.sub(end, 1), 20)))

def Cir.alloc.grow(enough: Bool, can: Bool, p: U32, need: U32) -> Maybe<&2, U32>:
  match enough can:
    case True{} _:
      Some{p}
    case False{} True{}:
      Some{need}
    case False{} False{}:
      None{}

def Cir.alloc.end(bad: Bool, +end: U32, +p: U32, +lim: U32) -> Maybe<&2, U32>:
  match bad:
    case True{}:
      None{}
    case False{}:
      +need = Cir.pages(end)
      Cir.alloc.grow(U32.is_le(need, p), U32.is_le(need, lim), p, need)

# the pages of the memory after alloc(n) (Cir.alloc), when it holds p pages
# and may grow to lim: none when it gives -1
def Cir.alloc.pages(+k: U32, +n: U32, +p: U32, +lim: U32) -> Maybe<&2, U32>:
  +a = Cir.input.at(k)
  +end = U32.add(a, n)
  Cir.alloc.end(U32.is_lt(end, a) || U32.is_gt(end, 4294967280), end, p, lim)

def Cir.result.alloced(r: Maybe<&2, U32>, fuel: Nat, prog: Cir.Stmt, +regs: Nat, cells: List<&2, Cir.Cell>,
  +k: U32, +end: U32, +lim: U32, i: List<&2, Word(8n)>) -> Wa.Wasm.Outcome:
  match r:
    case None{}:
      Wa.Wasm.Outcome.out_of_memory{}
    case Some{p}:
      +first = Cir.first(k, end)
      Cir.ended(Cir.exec(fuel, prog, Cir.State{
        List.replicate(U32, regs, 0), Cir.load(cells, 1, Cir.Cells.none{}), first, first, k, p, lim, i, Nil{}, 0}))

def Cir.result.sized(n: Maybe<&2, U32>, fuel: Nat, prog: Cir.Stmt, +regs: Nat, cells: List<&2, Cir.Cell>,
  +k: U32, +p: U32, +lim: U32, +i: List<&2, Word(8n)>) -> Wa.Wasm.Outcome:
  match n:
    case None{}:
      Wa.Wasm.Outcome.out_of_memory{}
    case Some{+len}:
      Cir.result.alloced(Cir.alloc.pages(k, len, p, lim), fuel, prog, regs, cells, k,
        U32.add(Cir.input.at(k), len), lim, i)

def Cir.result.memory(ok: Bool, fuel: Nat, prog: Cir.Stmt, +regs: Nat, cells: List<&2, Cir.Cell>, +k: U32,
  +p: U32, +lim: U32, +i: List<&2, Word(8n)>) -> Wa.Wasm.Outcome:
  match ok:
    case False{}:
      Wa.Wasm.Outcome.out_of_memory{}
    case True{}:
      Cir.result.sized(Wa.Wasm.length32(i), fuel, prog, regs, cells, k, p, lim, i)

# what a run of the module of Cir.module(prog, regs, cells) on the input i
# with at most m pages gives, by Cir.exec with the fuel
def Cir.result(fuel: Nat, prog: Cir.Stmt, +regs: Nat, +cells: List<&2, Cir.Cell>, +i: List<&2, Word(8n)>, +m: U32) ->
  Wa.Wasm.Outcome:
  +k = Wasm.encode.len(Cir.Cell, cells)
  +p = Cir.pages(Cir.input.at(k))
  Cir.result.memory(U32.is_le(p, m), fuel, prog, regs, cells, k, p, Wa.Wasm.min(m, 65536), i)
