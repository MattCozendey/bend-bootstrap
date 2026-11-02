import Base
import ../Shared/shared.bend as Sd

# Wasm
# ====
#
# The part of WebAssembly that our compiler uses (AGENTS.md 3.9.1.2), as the
# WebAssembly core spec defines it.
# Wasm.run(f, w, i, e) runs the module of the bytes w on the input bytes i,
# in at most f steps, on the engine e (Host), which decides what the spec
# leaves open: the most pages (of 64 KiB) of memory, and the grows that it
# refuses. A module
# outside the subset gives unsupported and does not run. The subset is in
# every version of the spec (1.0, 2.0, 3.0); where they decode a number with
# more bits, the model reads the 32 bits of 1.0, so it accepts only what
# every version accepts, and it runs that as every version does.

# Types
# -----

# how a run ends (see Host)
type Wasm.Outcome is Data:
  Wasm.Outcome.result{bytes: List<&2, Word(8n)>}
  Wasm.Outcome.out_of_memory{}
  Wasm.Outcome.no_result{}
  Wasm.Outcome.unsupported{}
  Wasm.Outcome.trap{}
  Wasm.Outcome.not_done{}

# the binary operators on i32; a comparison gives 1 or 0
type Wasm.Op is Data:
  Wasm.Op.add{}
  Wasm.Op.sub{}
  Wasm.Op.and{}
  Wasm.Op.or{}
  Wasm.Op.shl{}
  Wasm.Op.shr_u{}
  Wasm.Op.eq{}
  Wasm.Op.ne{}
  Wasm.Op.lt_u{}
  Wasm.Op.gt_u{}
  Wasm.Op.le_u{}
  Wasm.Op.ge_u{}

# an instruction; a block or a loop holds its body, and takes and gives
# no values
type Wasm.Instr is Data:
  Wasm.Instr.const{n: U32}
  Wasm.Instr.local_get{i: U32}
  Wasm.Instr.local_set{i: U32}
  Wasm.Instr.local_tee{i: U32}
  Wasm.Instr.op{op: Wasm.Op}
  Wasm.Instr.eqz{}
  Wasm.Instr.load{offset: U32}
  Wasm.Instr.load8_u{offset: U32}
  Wasm.Instr.store{offset: U32}
  Wasm.Instr.store8{offset: U32}
  Wasm.Instr.memory_size{}
  Wasm.Instr.memory_grow{}
  Wasm.Instr.block{body: List<&2, Wasm.Instr>}
  Wasm.Instr.loop{body: List<&2, Wasm.Instr>}
  Wasm.Instr.br{l: U32}
  Wasm.Instr.br_if{l: U32}

# a function type: its numbers of i32 parameters and results
type Wasm.Type is Data:
  Wasm.Type{params: Nat, results: Nat}

# a function: the index of its type, its number of i32 locals (after the
# parameters), and its body
type Wasm.Func is Data:
  Wasm.Func{typeidx: U32, locals: Nat, body: List<&2, Wasm.Instr>}

# an export: of a function, by its index, or of the memory
type Wasm.Export is Data:
  Wasm.Export.func{name: List<&2, Word(8n)>, index: U32}
  Wasm.Export.memory{name: List<&2, Word(8n)>}

# the limits of the memory: its minimum, in pages; the subset has no maximum
type Wasm.Limits is Data:
  Wasm.Limits{min: U32}

# an active data segment of the memory: where it starts, and its bytes
type Wasm.Segment is Data:
  Wasm.Segment{offset: U32, bytes: List<&2, Word(8n)>}

# a module of the subset; its functions name its types by index
type Wasm.Module is Data:
  Wasm.Module{
    types: List<&2, Wasm.Type>,
    funcs: List<&2, Wasm.Func>,
    memory: Maybe<&2, Wasm.Limits>,
    exports: List<&2, Wasm.Export>,
    data: Maybe<&2, Wasm.Segment>}

# Decoding
# --------
#
# The binary format (spec, chapter 5). A decoder takes bytes and gives the
# value that they start with and the bytes after it, or None when they are
# malformed or leave the subset.

# a decoded value and the bytes after it
type Wasm.Decoded<-A: Data> is Data:
  Wasm.Decoded{x: A, rest: List<&2, Word(8n)>}

# x, when ok holds
def Wasm.decode.keep(-A: Data, ok: Bool, x: A, rest: List<&2, Word(8n)>) -> Maybe<&2, Wasm.Decoded<A>>:
  match ok:
    case True{}:
      Some{Wasm.Decoded{x, rest}}
    case False{}:
      None{}

# a last byte is below 2^7; after a byte that goes on, more decodes the rest
def Wasm.decode.leb.if(
  last: Bool, ok: Bool, x: U32, rest: List<&2, Word(8n)>, more: List<&2, Word(8n)> -> Maybe<&2, Wasm.Decoded<U32>>
) -> Maybe<&2, Wasm.Decoded<U32>>:
  match last:
    case True{}:
      Wasm.decode.keep(U32, ok, x, rest)
    case False{}:
      more(rest)

# the low 7 bits of the byte b, then the bits of the number after it
def Wasm.decode.leb.more(+b: U32, m: Maybe<&2, Wasm.Decoded<U32>>) -> Maybe<&2, Wasm.Decoded<U32>>:
  match m:
    case None{}:
      None{}
    case Some{Wasm.Decoded{x, rest}}:
      Some{Wasm.Decoded{U32.or(U32.and(b, 127), U32.shln(x, 7n)), rest}}

# uN, an unsigned LEB128 number of at most n bits (spec 5.1):
#   a byte n < 2^7 with n < 2^N is n; a byte n >= 2^7 with N > 7, then
#   m of u(N-7), is 2^7 * m + (n - 2^7)
def Wasm.decode.uleb(n: Nat, bs: List<&2, Word(8n)>) -> Maybe<&2, Wasm.Decoded<U32>>:
  match n bs:
    case _ Nil{}:
      None{}
    case 8n+p Con{b, rest}:
      +v = Sd.Byte.to_u32(b)
      Wasm.decode.leb.if(U32.is_lt(v, 128), True{}, v, rest,
        r => Wasm.decode.leb.more(v, Wasm.decode.uleb(1n+p, r)))
    case +k Con{b, rest}:
      +v = Sd.Byte.to_u32(b)
      Wasm.decode.leb.if(U32.is_lt(v, 128), U32.is_lt(v, U32.shln(1, k)), v, rest, r => None{})

# a last byte of a signed number of n <= 7 bits: n < 2^6 with n < 2^(N-1)
# is n; 2^6 <= n < 2^7 with n >= 2^7 - 2^(N-1) is n - 2^7
def Wasm.decode.sleb.last(n: Nat, +b: U32) -> Bool:
  +h = U32.shln(1, Nat.sub(n, 1n))
  (U32.is_lt(b, 64) && U32.is_lt(b, h)) || (U32.is_ge(b, 64) && U32.is_ge(b, U32.sub(128, h)))

def Wasm.decode.sleb.pick(low: Bool, b: U32) -> U32:
  match low:
    case True{}:
      b
    case False{}:
      U32.sub(b, 128)

# a last byte below 2^6 stands for itself, one from 2^6 up for b - 2^7
def Wasm.decode.sleb.sign(+b: U32) -> U32:
  Wasm.decode.sleb.pick(U32.is_lt(b, 64), b)

# sN, a signed LEB128 number of at most n bits, as its 32 bits (spec 5.1):
#   the last byte is as in sleb.last; a byte n >= 2^7 with N > 7, then i of
#   s(N-7), is 2^7 * i + (n - 2^7)
def Wasm.decode.sleb(n: Nat, bs: List<&2, Word(8n)>) -> Maybe<&2, Wasm.Decoded<U32>>:
  match n bs:
    case _ Nil{}:
      None{}
    case 8n+p Con{b, rest}:
      +v = Sd.Byte.to_u32(b)
      Wasm.decode.leb.if(U32.is_lt(v, 128), True{}, Wasm.decode.sleb.sign(v), rest,
        r => Wasm.decode.leb.more(v, Wasm.decode.sleb(1n+p, r)))
    case +k Con{b, rest}:
      +v = Sd.Byte.to_u32(b)
      Wasm.decode.leb.if(U32.is_lt(v, 128), Wasm.decode.sleb.last(k, v), Wasm.decode.sleb.sign(v),
        rest, r => None{})

def Wasm.decode.u32(bs: List<&2, Word(8n)>) -> Maybe<&2, Wasm.Decoded<U32>>:
  Wasm.decode.uleb(32n, bs)

# the byte of the value b, exactly
def Wasm.decode.byte(+b: U32, bs: List<&2, Word(8n)>) -> Maybe<&2, Wasm.Decoded<U32>>:
  match bs:
    case Nil{}:
      None{}
    case Con{c, rest}:
      +v = Sd.Byte.to_u32(c)
      Wasm.decode.keep(U32, U32.is_eq(b, v), v, rest)

# the number of bytes, as a U32 when it fits
def Wasm.length32.if(full: Bool, more: Unit -> Maybe<&2, U32>) -> Maybe<&2, U32>:
  match full:
    case True{}:
      None{}
    case False{}:
      more(Unit{})

def Wasm.length32.go(xs: List<&2, Word(8n)>, +n: U32) -> Maybe<&2, U32>:
  match xs:
    case Nil{}:
      Some{n}
    case Con{_, rest}:
      Wasm.length32.if(U32.is_eq(n, 4294967295), u => Wasm.length32.go(rest, U32.inc(n)))

def Wasm.length32(xs: List<&2, Word(8n)>) -> Maybe<&2, U32>:
  Wasm.length32.go(xs, 0)

# the value of m and the bytes after it, then f of them
def Wasm.decode.bind(
  -A: Data, -B: Data, m: Maybe<&2, Wasm.Decoded<A>>, f: A -> List<&2, Word(8n)> -> Maybe<&2, Wasm.Decoded<B>>
) -> Maybe<&2, Wasm.Decoded<B>>:
  match m:
    case None{}:
      None{}
    case Some{Wasm.Decoded{x, rest}}:
      f(x, rest)

# the item x, then the items of m
def Wasm.decode.cons(-A: Data, x: A, m: Maybe<&2, Wasm.Decoded<List<&2, A>>>) -> Maybe<&2, Wasm.Decoded<List<&2, A>>>:
  match m:
    case None{}:
      None{}
    case Some{Wasm.Decoded{xs, rest}}:
      Some{Wasm.Decoded{Con{x, xs}, rest}}

# the value of m, when it takes all of the bytes
def Wasm.decode.done(-A: Data, m: Maybe<&2, Wasm.Decoded<A>>) -> Maybe<&2, A>:
  match m:
    case Some{Wasm.Decoded{x, Nil{}}}:
      Some{x}
    case _:
      None{}

# the value of m, when it takes all of its bytes, then the bytes after
def Wasm.decode.whole(-A: Data, m: Maybe<&2, Wasm.Decoded<A>>, after: List<&2, Word(8n)>) -> Maybe<&2, Wasm.Decoded<A>>:
  match m:
    case Some{Wasm.Decoded{x, Nil{}}}:
      Some{Wasm.Decoded{x, after}}
    case _:
      None{}

def Wasm.has.if(zero: Bool, more: Unit -> Bool) -> Bool:
  match zero:
    case True{}:
      True{}
    case False{}:
      more(Unit{})

# xs holds at least n bytes
def Wasm.has(xs: List<&2, Word(8n)>, +n: U32) -> Bool:
  match xs:
    case Nil{}:
      U32.is_zero(n)
    case Con{_, rest}:
      Wasm.has.if(U32.is_zero(n), u => Wasm.has(rest, U32.sub(n, 1)))

def Wasm.decode.count.if(ok: Bool, n: U32, rest: List<&2, Word(8n)>) -> Maybe<&2, Wasm.Decoded<Nat>>:
  match ok:
    case True{}:
      Some{Wasm.Decoded{U32.to_nat(n), rest}}
    case False{}:
      None{}

# the length of a vector (spec 5.1: list), which counts items of a byte or
# more, so no more than the bytes after it; only then is it made a Nat, as a
# larger one could take as many steps to make as it counts
def Wasm.decode.count(bs: List<&2, Word(8n)>) -> Maybe<&2, Wasm.Decoded<Nat>>:
  Wasm.decode.bind(U32, Nat, Wasm.decode.u32(bs), +n => +r =>
    Wasm.decode.count.if(Wasm.has(r, n), n, r))

# n bytes
def Wasm.decode.take(n: Nat, bs: List<&2, Word(8n)>) -> Maybe<&2, Wasm.Decoded<List<&2, Word(8n)>>>:
  match n:
    case 0n:
      Some{Wasm.Decoded{Nil{}, bs}}
    case 1n+p:
      match bs:
        case Nil{}:
          None{}
        case Con{b, rest}:
          Wasm.decode.cons(Word(8n), b, Wasm.decode.take(p, rest))

# n items, each decoded by d
def Wasm.decode.items(
  ~A: Data, ~d: List<&2, Word(8n)> -> Maybe<&2, Wasm.Decoded<A>>, n: Nat, bs: List<&2, Word(8n)>
) -> Maybe<&2, Wasm.Decoded<List<&2, A>>>:
  match n:
    case 0n:
      Some{Wasm.Decoded{Nil{}, bs}}
    case 1n+p:
      Wasm.decode.bind(A, List<&2, A>, d(bs), x => r => Wasm.decode.cons(A, x, Wasm.decode.items(~A, ~d, p, r)))

# a vector of items, each decoded by d
def Wasm.decode.vec(
  ~A: Data, ~d: List<&2, Word(8n)> -> Maybe<&2, Wasm.Decoded<A>>, bs: List<&2, Word(8n)>
) -> Maybe<&2, Wasm.Decoded<List<&2, A>>>:
  Wasm.decode.bind(Nat, List<&2, A>, Wasm.decode.count(bs), n => r => Wasm.decode.items(~A, ~d, n, r))

# vec(byte)
def Wasm.decode.bytes(bs: List<&2, Word(8n)>) -> Maybe<&2, Wasm.Decoded<List<&2, Word(8n)>>>:
  Wasm.decode.bind(Nat, List<&2, Word(8n)>, Wasm.decode.count(bs), n => r => Wasm.decode.take(n, r))

# every byte is ASCII
def Wasm.is_ascii(xs: List<&2, Word(8n)>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{b, rest}:
      U32.is_lt(Sd.Byte.to_u32(b), 128) && Wasm.is_ascii(rest)

# a name (spec 5.1); the subset takes ASCII names only, which are UTF-8
def Wasm.decode.name(bs: List<&2, Word(8n)>) -> Maybe<&2, Wasm.Decoded<List<&2, Word(8n)>>>:
  Wasm.decode.bind(List<&2, Word(8n)>, List<&2, Word(8n)>, Wasm.decode.bytes(bs), +xs => r =>
    Wasm.decode.keep(List<&2, Word(8n)>, Wasm.is_ascii(xs), xs, r))

# every byte is 0x7F, the value type i32
def Wasm.is_i32s(xs: List<&2, Word(8n)>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{b, rest}:
      U32.is_eq(Sd.Byte.to_u32(b), 127) && Wasm.is_i32s(rest)

# a result type (spec 5.2): a vector of value types, all i32; its length
def Wasm.decode.i32s(bs: List<&2, Word(8n)>) -> Maybe<&2, Wasm.Decoded<Nat>>:
  Wasm.decode.bind(List<&2, Word(8n)>, Nat, Wasm.decode.bytes(bs), +xs => r =>
    Wasm.decode.keep(Nat, Wasm.is_i32s(xs), List.length(&2, Word(8n), xs), r))

# a function type (spec 5.2): 0x60, then its parameters' and results' types
def Wasm.decode.functype(bs: List<&2, Word(8n)>) -> Maybe<&2, Wasm.Decoded<Wasm.Type>>:
  Wasm.decode.bind(U32, Wasm.Type, Wasm.decode.byte(96, bs), t => r =>
    Wasm.decode.bind(Nat, Wasm.Type, Wasm.decode.i32s(r), p => r2 =>
      Wasm.decode.bind(Nat, Wasm.Type, Wasm.decode.i32s(r2), q => r3 =>
        Some{Wasm.Decoded{Wasm.Type{p, q}, r3}})))

# a memory type (spec 5.2): its limits, of a memory of 32-bit addresses: the
# flag 0, for a minimum alone, then the minimum
def Wasm.decode.limits(bs: List<&2, Word(8n)>) -> Maybe<&2, Wasm.Decoded<Wasm.Limits>>:
  Wasm.decode.bind(U32, Wasm.Limits, Wasm.decode.byte(0, bs), f => r =>
    Wasm.decode.bind(U32, Wasm.Limits, Wasm.decode.u32(r), n => r2 =>
      Some{Wasm.Decoded{Wasm.Limits{n}, r2}}))

def Wasm.decode.export.kind(
  kind: Nat, name: List<&2, Word(8n)>, bs: List<&2, Word(8n)>
) -> Maybe<&2, Wasm.Decoded<Wasm.Export>>:
  match kind:
    case 0n:
      Wasm.decode.bind(U32, Wasm.Export, Wasm.decode.u32(bs), i => r =>
        Some{Wasm.Decoded{Wasm.Export.func{name, i}, r}})
    case 2n:
      Wasm.decode.bind(U32, Wasm.Export, Wasm.decode.u32(bs), +i => r =>
        Wasm.decode.keep(Wasm.Export, U32.is_zero(i), Wasm.Export.memory{name}, r))
    case _:
      None{}

# an export's description: 0x00 and a function index, or 0x02 and memory 0
def Wasm.decode.export.of(name: List<&2, Word(8n)>, bs: List<&2, Word(8n)>) -> Maybe<&2, Wasm.Decoded<Wasm.Export>>:
  match bs:
    case Nil{}:
      None{}
    case Con{kind, rest}:
      Wasm.decode.export.kind(Word.to_nat(8n, kind), name, rest)

# an export (spec 5.4): a name and a description
def Wasm.decode.export(bs: List<&2, Word(8n)>) -> Maybe<&2, Wasm.Decoded<Wasm.Export>>:
  Wasm.decode.bind(List<&2, Word(8n)>, Wasm.Export, Wasm.decode.name(bs), n => r => Wasm.decode.export.of(n, r))

# the head of an instruction: an instruction, the start of a block or a loop,
# or the end of a block
type Wasm.Token is Data:
  Wasm.Token.instr{x: Wasm.Instr}
  Wasm.Token.start{loop: Bool}
  Wasm.Token.end{}

def Wasm.decode.as(x: Wasm.Instr, bs: List<&2, Word(8n)>) -> Maybe<&2, Wasm.Decoded<Wasm.Token>>:
  Some{Wasm.Decoded{Wasm.Token.instr{x}, bs}}

# an instruction with a u32 immediate, which k turns into the instruction
def Wasm.decode.index(k: U32 -> Wasm.Instr, bs: List<&2, Word(8n)>) -> Maybe<&2, Wasm.Decoded<Wasm.Token>>:
  Wasm.decode.bind(U32, Wasm.Token, Wasm.decode.u32(bs), i => r => Wasm.decode.as(k(i), r))

# the start of a block or a loop (spec 5.3): its block type, which must be
# 0x40 (no values)
def Wasm.decode.block(loop: Bool, bs: List<&2, Word(8n)>) -> Maybe<&2, Wasm.Decoded<Wasm.Token>>:
  Wasm.decode.bind(U32, Wasm.Token, Wasm.decode.byte(64, bs), t => r =>
    Some{Wasm.Decoded{Wasm.Token.start{loop}, r}})

def Wasm.decode.memarg.if(ok: Bool, k: U32 -> Wasm.Instr, bs: List<&2, Word(8n)>) -> Maybe<&2, Wasm.Decoded<Wasm.Token>>:
  match ok:
    case True{}:
      Wasm.decode.bind(U32, Wasm.Token, Wasm.decode.u32(bs), o => r => Wasm.decode.as(k(o), r))
    case False{}:
      None{}

# a load or store (spec 5.3): its alignment, as a power of 2 no more than
# max (the access's width; spec 3.4), then its offset; an alignment of 2^6
# or more names another memory, outside the subset
def Wasm.decode.memarg(max: U32, k: U32 -> Wasm.Instr, bs: List<&2, Word(8n)>) -> Maybe<&2, Wasm.Decoded<Wasm.Token>>:
  Wasm.decode.bind(U32, Wasm.Token, Wasm.decode.u32(bs), a => r => Wasm.decode.memarg.if(U32.is_le(a, max), k, r))

# memory.size or memory.grow: memory 0, as the one byte 0x00 of 1.0
def Wasm.decode.memory(x: Wasm.Instr, bs: List<&2, Word(8n)>) -> Maybe<&2, Wasm.Decoded<Wasm.Token>>:
  Wasm.decode.bind(U32, Wasm.Token, Wasm.decode.byte(0, bs), z => r => Wasm.decode.as(x, r))

# i32.const (spec 5.3): a signed 32-bit LEB128 number
def Wasm.decode.const(bs: List<&2, Word(8n)>) -> Maybe<&2, Wasm.Decoded<Wasm.Token>>:
  Wasm.decode.bind(U32, Wasm.Token, Wasm.decode.sleb(32n, bs), n => r => Wasm.decode.as(Wasm.Instr.const{n}, r))

# the head of the instruction of opcode op (spec 5.3), with its immediates
def Wasm.decode.token(op: Nat, bs: List<&2, Word(8n)>) -> Maybe<&2, Wasm.Decoded<Wasm.Token>>:
  match op:
    case 2n:
      Wasm.decode.block(False{}, bs)
    case 3n:
      Wasm.decode.block(True{}, bs)
    case 11n:
      Some{Wasm.Decoded{Wasm.Token.end{}, bs}}
    case 12n:
      Wasm.decode.index(l => Wasm.Instr.br{l}, bs)
    case 13n:
      Wasm.decode.index(l => Wasm.Instr.br_if{l}, bs)
    case 32n:
      Wasm.decode.index(i => Wasm.Instr.local_get{i}, bs)
    case 33n:
      Wasm.decode.index(i => Wasm.Instr.local_set{i}, bs)
    case 34n:
      Wasm.decode.index(i => Wasm.Instr.local_tee{i}, bs)
    case 40n:
      Wasm.decode.memarg(2, o => Wasm.Instr.load{o}, bs)
    case 45n:
      Wasm.decode.memarg(0, o => Wasm.Instr.load8_u{o}, bs)
    case 54n:
      Wasm.decode.memarg(2, o => Wasm.Instr.store{o}, bs)
    case 58n:
      Wasm.decode.memarg(0, o => Wasm.Instr.store8{o}, bs)
    case 63n:
      Wasm.decode.memory(Wasm.Instr.memory_size{}, bs)
    case 64n:
      Wasm.decode.memory(Wasm.Instr.memory_grow{}, bs)
    case 65n:
      Wasm.decode.const(bs)
    case 69n:
      Wasm.decode.as(Wasm.Instr.eqz{}, bs)
    case 70n:
      Wasm.decode.as(Wasm.Instr.op{Wasm.Op.eq{}}, bs)
    case 71n:
      Wasm.decode.as(Wasm.Instr.op{Wasm.Op.ne{}}, bs)
    case 73n:
      Wasm.decode.as(Wasm.Instr.op{Wasm.Op.lt_u{}}, bs)
    case 75n:
      Wasm.decode.as(Wasm.Instr.op{Wasm.Op.gt_u{}}, bs)
    case 77n:
      Wasm.decode.as(Wasm.Instr.op{Wasm.Op.le_u{}}, bs)
    case 79n:
      Wasm.decode.as(Wasm.Instr.op{Wasm.Op.ge_u{}}, bs)
    case 106n:
      Wasm.decode.as(Wasm.Instr.op{Wasm.Op.add{}}, bs)
    case 107n:
      Wasm.decode.as(Wasm.Instr.op{Wasm.Op.sub{}}, bs)
    case 113n:
      Wasm.decode.as(Wasm.Instr.op{Wasm.Op.and{}}, bs)
    case 114n:
      Wasm.decode.as(Wasm.Instr.op{Wasm.Op.or{}}, bs)
    case 116n:
      Wasm.decode.as(Wasm.Instr.op{Wasm.Op.shl{}}, bs)
    case 118n:
      Wasm.decode.as(Wasm.Instr.op{Wasm.Op.shr_u{}}, bs)
    case _:
      None{}

# an open block: whether it is a loop, and the instructions before it in its
# own block, the last first
type Wasm.Open is Data:
  Wasm.Open{loop: Bool, before: List<&2, Wasm.Instr>}

def Wasm.decode.closed(loop: Bool, body: List<&2, Wasm.Instr>) -> Wasm.Instr:
  match loop:
    case True{}:
      Wasm.Instr.loop{body}
    case False{}:
      Wasm.Instr.block{body}

# an end: of the outermost block, its instructions; of an open block, the
# block joins the instructions before it
def Wasm.decode.instrs.end(
  st: List<&2, Wasm.Open>,
  xs: List<&2, Wasm.Instr>,
  r: List<&2, Word(8n)>,
  more: List<&2, Word(8n)> -> List<&2, Wasm.Instr> -> List<&2, Wasm.Open> -> Maybe<&2, Wasm.Decoded<List<&2, Wasm.Instr>>>
) -> Maybe<&2, Wasm.Decoded<List<&2, Wasm.Instr>>>:
  match st:
    case Nil{}:
      Some{Wasm.Decoded{List.reverse(&2, Wasm.Instr, xs), r}}
    case Con{Wasm.Open{loop, before}, outer}:
      more(r, Con{Wasm.decode.closed(loop, List.reverse(&2, Wasm.Instr, xs)), before}, outer)

# the next head, after the instructions xs (the last first) of the innermost
# open block, inside the open blocks st (the innermost first)
def Wasm.decode.instrs.then(
  t: Maybe<&2, Wasm.Decoded<Wasm.Token>>,
  xs: List<&2, Wasm.Instr>,
  st: List<&2, Wasm.Open>,
  more: List<&2, Word(8n)> -> List<&2, Wasm.Instr> -> List<&2, Wasm.Open> -> Maybe<&2, Wasm.Decoded<List<&2, Wasm.Instr>>>
) -> Maybe<&2, Wasm.Decoded<List<&2, Wasm.Instr>>>:
  match t:
    case None{}:
      None{}
    case Some{Wasm.Decoded{Wasm.Token.instr{x}, r}}:
      more(r, Con{x, xs}, st)
    case Some{Wasm.Decoded{Wasm.Token.start{loop}, r}}:
      more(r, Nil{}, Con{Wasm.Open{loop, xs}, st})
    case Some{Wasm.Decoded{Wasm.Token.end{}, r}}:
      Wasm.decode.instrs.end(st, xs, r, more)

# the instructions up to the end (0x0B) of their block, and the bytes after
# it, one head at a time, as the reader of Book reads its tokens: xs and st
# hold the instructions and open blocks so far. Each head takes a byte or
# more, so fuel of the bytes' length always suffices.
def Wasm.decode.instrs.go(
  fuel: Nat, bs: List<&2, Word(8n)>, xs: List<&2, Wasm.Instr>, st: List<&2, Wasm.Open>
) -> Maybe<&2, Wasm.Decoded<List<&2, Wasm.Instr>>>:
  match fuel bs:
    case 0n _:
      None{}
    case 1n+p Nil{}:
      None{}
    case 1n+p Con{op, rest}:
      Wasm.decode.instrs.then(Wasm.decode.token(Word.to_nat(8n, op), rest), xs, st,
        r => ys => st2 => Wasm.decode.instrs.go(p, r, ys, st2))

def Wasm.decode.instrs(fuel: Nat, bs: List<&2, Word(8n)>) -> Maybe<&2, Wasm.Decoded<List<&2, Wasm.Instr>>>:
  Wasm.decode.instrs.go(fuel, bs, Nil{}, Nil{})

# a function's code
type Wasm.Code is Data:
  Wasm.Code{locals: Nat, body: List<&2, Wasm.Instr>}

# a group of locals (spec 5.4): their number, then their type, i32
def Wasm.decode.local(bs: List<&2, Word(8n)>) -> Maybe<&2, Wasm.Decoded<U32>>:
  Wasm.decode.bind(U32, U32, Wasm.decode.u32(bs), n => r =>
    Wasm.decode.bind(U32, U32, Wasm.decode.byte(127, r), t => r2 => Some{Wasm.Decoded{n, r2}}))

def Wasm.locals.if(ok: Bool, more: Unit -> Maybe<&2, U32>) -> Maybe<&2, U32>:
  match ok:
    case True{}:
      more(Unit{})
    case False{}:
      None{}

# the number of locals of the groups ns, from acc: at most 50000, the
# limit of the JS API (engines take no more; the spec allows fewer than 2^32)
def Wasm.locals.sum(ns: List<&2, U32>, +acc: U32) -> Maybe<&2, U32>:
  match ns:
    case Nil{}:
      Some{acc}
    case Con{+n, rest}:
      +s = U32.add(acc, n)
      Wasm.locals.if(U32.is_le(n, 50000) && U32.is_le(s, 50000), u => Wasm.locals.sum(rest, s))

def Wasm.decode.func.body(
  n: Maybe<&2, U32>, +bs: List<&2, Word(8n)>
) -> Maybe<&2, Wasm.Decoded<Wasm.Code>>:
  match n:
    case None{}:
      None{}
    case Some{k}:
      Wasm.decode.bind(List<&2, Wasm.Instr>, Wasm.Code, Wasm.decode.instrs(1n+List.length(&2, Word(8n), bs), bs), b => r =>
        Some{Wasm.Decoded{Wasm.Code{U32.to_nat(k), b}, r}})

# a function's code (spec 5.4): its groups of locals, then its body
def Wasm.decode.func(bs: List<&2, Word(8n)>) -> Maybe<&2, Wasm.Decoded<Wasm.Code>>:
  Wasm.decode.bind(List<&2, U32>, Wasm.Code, Wasm.decode.vec(~U32, ~Wasm.decode.local, bs), ns => r =>
    Wasm.decode.func.body(Wasm.locals.sum(ns, 0), r))

# an entry of the code section (spec 5.4): its size, then exactly that many
# bytes of code
def Wasm.decode.code(bs: List<&2, Word(8n)>) -> Maybe<&2, Wasm.Decoded<Wasm.Code>>:
  Wasm.decode.bind(Nat, Wasm.Code, Wasm.decode.count(bs), n => r =>
    Wasm.decode.bind(List<&2, Word(8n)>, Wasm.Code, Wasm.decode.take(n, r), c => r2 =>
      Wasm.decode.whole(Wasm.Code, Wasm.decode.func(c), r2)))

def Wasm.decode.data.if(ok: Bool, bs: List<&2, Word(8n)>) -> Maybe<&2, Wasm.Decoded<Wasm.Segment>>:
  match ok:
    case True{}:
      Wasm.decode.bind(U32, Wasm.Segment, Wasm.decode.byte(65, bs), c => r =>
        Wasm.decode.bind(U32, Wasm.Segment, Wasm.decode.sleb(32n, r), k => r2 =>
          Wasm.decode.bind(U32, Wasm.Segment, Wasm.decode.byte(11, r2), e => r3 =>
            Wasm.decode.bind(List<&2, Word(8n)>, Wasm.Segment, Wasm.decode.bytes(r3), b => r4 =>
              Some{Wasm.Decoded{Wasm.Segment{k, b}, r4}}))))
    case False{}:
      None{}

# a data segment (spec 5.4): 0, an active one of memory 0, then its offset,
# which in the subset is the constant expression i32.const n end, then its
# bytes
def Wasm.decode.data(bs: List<&2, Word(8n)>) -> Maybe<&2, Wasm.Decoded<Wasm.Segment>>:
  Wasm.decode.bind(U32, Wasm.Segment, Wasm.decode.u32(bs), flag => r => Wasm.decode.data.if(U32.is_zero(flag), r))

# a section (spec 5.4): its id, its size, then exactly that many bytes
type Wasm.Section is Data:
  Wasm.Section{id: U32, content: List<&2, Word(8n)>}

def Wasm.decode.section(bs: List<&2, Word(8n)>) -> Maybe<&2, Wasm.Decoded<Wasm.Section>>:
  match bs:
    case Nil{}:
      None{}
    case Con{id, rest}:
      Wasm.decode.bind(Nat, Wasm.Section, Wasm.decode.count(rest), n => r =>
        Wasm.decode.bind(List<&2, Word(8n)>, Wasm.Section, Wasm.decode.take(n, r), c => r2 =>
          Some{Wasm.Decoded{Wasm.Section{Sd.Byte.to_u32(id), c}, r2}}))

def Wasm.decode.sections.cons(x: Wasm.Section, m: Maybe<&2, List<&2, Wasm.Section>>) -> Maybe<&2, List<&2, Wasm.Section>>:
  match m:
    case None{}:
      None{}
    case Some{xs}:
      Some{Con{x, xs}}

def Wasm.decode.sections.got(
  m: Maybe<&2, Wasm.Decoded<Wasm.Section>>, more: List<&2, Word(8n)> -> Maybe<&2, List<&2, Wasm.Section>>
) -> Maybe<&2, List<&2, Wasm.Section>>:
  match m:
    case None{}:
      None{}
    case Some{Wasm.Decoded{x, rest}}:
      Wasm.decode.sections.cons(x, more(rest))

# the sections up to the end of the bytes; each takes 2 bytes or more, so
# fuel of the bytes' length always suffices
def Wasm.decode.sections(fuel: Nat, bs: List<&2, Word(8n)>) -> Maybe<&2, List<&2, Wasm.Section>>:
  match fuel bs:
    case _ Nil{}:
      Some{Nil{}}
    case 0n Con{_, _}:
      None{}
    case 1n+f Con{b, rest}:
      Wasm.decode.sections.got(Wasm.decode.section(Con{b, rest}), r => Wasm.decode.sections(f, r))

# the subset's sections: 1 type, 3 function, 5 memory, 7 export, 10
# code and 11 data; the spec's order for them is this numeric order
def Wasm.section.is_known(+id: U32) -> Bool:
  U32.is_eq(id, 1) || U32.is_eq(id, 3) || U32.is_eq(id, 5) || U32.is_eq(id, 7) || U32.is_eq(id, 10) || U32.is_eq(id, 11)

# the sections are of the subset, each at most once and in order (spec 5.4)
def Wasm.sections.is_ordered(ss: List<&2, Wasm.Section>, +last: U32) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case Con{Wasm.Section{+id, _}, rest}:
      Wasm.section.is_known(id) && U32.is_gt(id, last) && Wasm.sections.is_ordered(rest, id)

def Wasm.sections.find.if(
  hit: Bool, c: List<&2, Word(8n)>, more: Unit -> Maybe<&2, List<&2, Word(8n)>>
) -> Maybe<&2, List<&2, Word(8n)>>:
  match hit:
    case True{}:
      Some{c}
    case False{}:
      more(Unit{})

# the content of the section of the id, if any
def Wasm.sections.find(ss: List<&2, Wasm.Section>, +id: U32) -> Maybe<&2, List<&2, Word(8n)>>:
  match ss:
    case Nil{}:
      None{}
    case Con{Wasm.Section{k, c}, rest}:
      Wasm.sections.find.if(U32.is_eq(k, id), c, u => Wasm.sections.find(rest, id))

# the items of a section (spec 5.4), its whole content; none without it
def Wasm.decode.part(
  ~A: Data, ~d: List<&2, Word(8n)> -> Maybe<&2, Wasm.Decoded<A>>, c: Maybe<&2, List<&2, Word(8n)>>
) -> Maybe<&2, List<&2, A>>:
  match c:
    case None{}:
      Some{Nil{}}
    case Some{bs}:
      Wasm.decode.done(List<&2, A>, Wasm.decode.vec(~A, ~d, bs))

# at most one item: the subset has one memory and one data segment at most
def Wasm.decode.one(-A: Data, m: Maybe<&2, List<&2, A>>) -> Maybe<&2, Maybe<&2, A>>:
  match m:
    case Some{Nil{}}:
      Some{None{}}
    case Some{Con{x, Nil{}}}:
      Some{Some{x}}
    case _:
      None{}

def Wasm.funcs.cons(f: Wasm.Func, m: Maybe<&2, List<&2, Wasm.Func>>) -> Maybe<&2, List<&2, Wasm.Func>>:
  match m:
    case None{}:
      None{}
    case Some{fs}:
      Some{Con{f, fs}}

# the functions, of the function section's type indices and the code
# section's codes, one each (spec 5.4)
def Wasm.funcs.of(idx: List<&2, U32>, cs: List<&2, Wasm.Code>) -> Maybe<&2, List<&2, Wasm.Func>>:
  match idx cs:
    case Nil{} Nil{}:
      Some{Nil{}}
    case Con{i, idx2} Con{Wasm.Code{n, b}, cs2}:
      Wasm.funcs.cons(Wasm.Func{i, n, b}, Wasm.funcs.of(idx2, cs2))
    case _ _:
      None{}

def Wasm.decode.module.parts(
  +ss: List<&2, Wasm.Section>
) -> Maybe<&2, Wasm.Module>:
  Maybe.bind(&2, List<&2, Wasm.Type>, Wasm.Module, Wasm.decode.part(~Wasm.Type, ~Wasm.decode.functype, Wasm.sections.find(ss, 1)), ts =>
    Maybe.bind(&2, List<&2, U32>, Wasm.Module, Wasm.decode.part(~U32, ~Wasm.decode.u32, Wasm.sections.find(ss, 3)), idx =>
      Maybe.bind(&2, Maybe<&2, Wasm.Limits>, Wasm.Module,
        Wasm.decode.one(Wasm.Limits, Wasm.decode.part(~Wasm.Limits, ~Wasm.decode.limits, Wasm.sections.find(ss, 5))), mem =>
        Maybe.bind(&2, List<&2, Wasm.Export>, Wasm.Module, Wasm.decode.part(~Wasm.Export, ~Wasm.decode.export, Wasm.sections.find(ss, 7)), es =>
          Maybe.bind(&2, List<&2, Wasm.Code>, Wasm.Module, Wasm.decode.part(~Wasm.Code, ~Wasm.decode.code, Wasm.sections.find(ss, 10)), cs =>
            Maybe.bind(&2, Maybe<&2, Wasm.Segment>, Wasm.Module,
              Wasm.decode.one(Wasm.Segment, Wasm.decode.part(~Wasm.Segment, ~Wasm.decode.data, Wasm.sections.find(ss, 11))), seg =>
              Maybe.bind(&2, List<&2, Wasm.Func>, Wasm.Module, Wasm.funcs.of(idx, cs), fs =>
                Some{Wasm.Module{ts, fs, mem, es, seg}})))))))

def Wasm.decode.module.if(ok: Bool, +ss: List<&2, Wasm.Section>) -> Maybe<&2, Wasm.Module>:
  match ok:
    case True{}:
      Wasm.decode.module.parts(ss)
    case False{}:
      None{}

def Wasm.decode.module.sections(m: Maybe<&2, List<&2, Wasm.Section>>) -> Maybe<&2, Wasm.Module>:
  match m:
    case None{}:
      None{}
    case Some{+ss}:
      Wasm.decode.module.if(Wasm.sections.is_ordered(ss, 0), ss)

# the sections after a right header
def Wasm.decode.sections.if(ok: Bool, +rest: List<&2, Word(8n)>) -> Maybe<&2, List<&2, Wasm.Section>>:
  match ok:
    case True{}:
      Wasm.decode.sections(List.length(&2, Word(8n), rest), rest)
    case False{}:
      None{}

# the 8 bytes that begin a module (spec 5.5.15): the magic \0asm, then version 1
def Wasm.header() -> List<&2, Word(8n)>:
  [Sd.Byte.from_u32(0), Sd.Byte.from_u32(97), Sd.Byte.from_u32(115), Sd.Byte.from_u32(109),
    Sd.Byte.from_u32(1), Sd.Byte.from_u32(0), Sd.Byte.from_u32(0), Sd.Byte.from_u32(0)]

def Wasm.decode.module.header(m: Maybe<&2, Wasm.Decoded<List<&2, Word(8n)>>>) -> Maybe<&2, Wasm.Module>:
  match m:
    case None{}:
      None{}
    case Some{Wasm.Decoded{h, +rest}}:
      Wasm.decode.module.sections(
        Wasm.decode.sections.if(Sd.Name.is_eq(h, Wasm.header()), rest))

# a module (spec 5.4): the header, then its sections
def Wasm.decode.module(bs: List<&2, Word(8n)>) -> Maybe<&2, Wasm.Module>:
  Wasm.decode.module.header(Wasm.decode.take(8n, bs))

# Validation
# ----------
#
# The spec's rules for the subset's instructions (spec 3.4) and modules
# (spec 3.5). Every value is an i32, so a type is a number of values: a
# label's type is the number of values that a branch to it takes.

# a stack's height at the end of instructions, relative to their block's
# start, or any after a branch
type Wasm.Height is Data:
  Wasm.Height.at{h: Nat}
  Wasm.Height.any{}

def Wasm.valid.if(ok: Bool, more: Unit -> Maybe<&2, Wasm.Height>) -> Maybe<&2, Wasm.Height>:
  match ok:
    case True{}:
      more(Unit{})
    case False{}:
      None{}

def Wasm.valid.label.if(zero: Bool, a: Nat, more: Unit -> Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match zero:
    case True{}:
      Some{a}
    case False{}:
      more(Unit{})

# the type of the label l, from the innermost
def Wasm.valid.label(labels: List<&2, Nat>, +l: U32) -> Maybe<&2, Nat>:
  match labels:
    case Nil{}:
      None{}
    case Con{a, rest}:
      Wasm.valid.label.if(U32.is_zero(l), a, u => Wasm.valid.label(rest, U32.sub(l, 1)))

def Wasm.type.at.if(zero: Bool, t: Wasm.Type, more: Unit -> Maybe<&2, Wasm.Type>) -> Maybe<&2, Wasm.Type>:
  match zero:
    case True{}:
      Some{t}
    case False{}:
      more(Unit{})

# the type of index i
def Wasm.type.at(ts: List<&2, Wasm.Type>, +i: U32) -> Maybe<&2, Wasm.Type>:
  match ts:
    case Nil{}:
      None{}
    case Con{t, rest}:
      Wasm.type.at.if(U32.is_zero(i), t, u => Wasm.type.at(rest, U32.sub(i, 1)))

# a block's body ends with no values left, or after a branch
def Wasm.valid.is_empty(m: Maybe<&2, Wasm.Height>) -> Bool:
  match m:
    case Some{Wasm.Height.at{0n}}:
      True{}
    case Some{Wasm.Height.any{}}:
      True{}
    case _:
      False{}

# br l takes the label's values
def Wasm.valid.br(a: Maybe<&2, Nat>, h: Nat) -> Bool:
  match a:
    case None{}:
      False{}
    case Some{k}:
      Nat.is_ge(h, k)

# br_if l takes the label's values and the condition, and leaves the values
def Wasm.valid.br_if(a: Maybe<&2, Nat>, h: Nat) -> Bool:
  match a:
    case None{}:
      False{}
    case Some{k}:
      Nat.is_ge(h, 1n+k)

# the instructions xs from the height h: the height at their end, or None
# when they are invalid; labels holds the labels' types, innermost first,
# locals the number of locals, and mem says the module has a memory. The
# subset takes no instruction after br in its block.
def Wasm.valid.go(
  xs: List<&2, Wasm.Instr>, +h: Nat, +labels: List<&2, Nat>, +locals: U32, +mem: Bool
) -> Maybe<&2, Wasm.Height>:
  match xs:
    case Nil{}:
      Some{Wasm.Height.at{h}}
    case Con{Wasm.Instr.const{_}, rest}:
      Wasm.valid.go(rest, 1n+h, labels, locals, mem)
    case Con{Wasm.Instr.local_get{i}, rest}:
      Wasm.valid.if(U32.is_lt(i, locals), u => Wasm.valid.go(rest, 1n+h, labels, locals, mem))
    case Con{Wasm.Instr.local_set{i}, rest}:
      Wasm.valid.if(U32.is_lt(i, locals) && Nat.is_ge(h, 1n), u => Wasm.valid.go(rest, Nat.sub(h, 1n), labels, locals, mem))
    case Con{Wasm.Instr.local_tee{i}, rest}:
      Wasm.valid.if(U32.is_lt(i, locals) && Nat.is_ge(h, 1n), u => Wasm.valid.go(rest, h, labels, locals, mem))
    case Con{Wasm.Instr.op{_}, rest}:
      Wasm.valid.if(Nat.is_ge(h, 2n), u => Wasm.valid.go(rest, Nat.sub(h, 1n), labels, locals, mem))
    case Con{Wasm.Instr.eqz{}, rest}:
      Wasm.valid.if(Nat.is_ge(h, 1n), u => Wasm.valid.go(rest, h, labels, locals, mem))
    case Con{Wasm.Instr.load{_}, rest}:
      Wasm.valid.if(mem && Nat.is_ge(h, 1n), u => Wasm.valid.go(rest, h, labels, locals, mem))
    case Con{Wasm.Instr.load8_u{_}, rest}:
      Wasm.valid.if(mem && Nat.is_ge(h, 1n), u => Wasm.valid.go(rest, h, labels, locals, mem))
    case Con{Wasm.Instr.store{_}, rest}:
      Wasm.valid.if(mem && Nat.is_ge(h, 2n), u => Wasm.valid.go(rest, Nat.sub(h, 2n), labels, locals, mem))
    case Con{Wasm.Instr.store8{_}, rest}:
      Wasm.valid.if(mem && Nat.is_ge(h, 2n), u => Wasm.valid.go(rest, Nat.sub(h, 2n), labels, locals, mem))
    case Con{Wasm.Instr.memory_size{}, rest}:
      Wasm.valid.if(mem, u => Wasm.valid.go(rest, 1n+h, labels, locals, mem))
    case Con{Wasm.Instr.memory_grow{}, rest}:
      Wasm.valid.if(mem && Nat.is_ge(h, 1n), u => Wasm.valid.go(rest, h, labels, locals, mem))
    case Con{Wasm.Instr.block{body}, rest}:
      Wasm.valid.if(Wasm.valid.is_empty(Wasm.valid.go(body, 0n, Con{0n, labels}, locals, mem)),
        u => Wasm.valid.go(rest, h, labels, locals, mem))
    case Con{Wasm.Instr.loop{body}, rest}:
      Wasm.valid.if(Wasm.valid.is_empty(Wasm.valid.go(body, 0n, Con{0n, labels}, locals, mem)),
        u => Wasm.valid.go(rest, h, labels, locals, mem))
    case Con{Wasm.Instr.br{l}, rest}:
      Wasm.valid.if(Wasm.valid.br(Wasm.valid.label(labels, l), h) && List.is_empty(&2, Wasm.Instr, rest),
        u => Some{Wasm.Height.any{}})
    case Con{Wasm.Instr.br_if{l}, rest}:
      Wasm.valid.if(Wasm.valid.br_if(Wasm.valid.label(labels, l), h),
        u => Wasm.valid.go(rest, Nat.sub(h, 1n), labels, locals, mem))

# a function's body ends with its results, or after a branch
def Wasm.valid.is_results(m: Maybe<&2, Wasm.Height>, q: Nat) -> Bool:
  match m:
    case Some{Wasm.Height.at{h}}:
      Nat.is_eq(h, q)
    case Some{Wasm.Height.any{}}:
      True{}
    case _:
      False{}

# a function of the type t (spec 3.5): its locals are its parameters, then
# its n locals; its body's label, and its end, take its results
def Wasm.valid.func.of(t: Maybe<&2, Wasm.Type>, n: Nat, body: List<&2, Wasm.Instr>, +mem: Bool) -> Bool:
  match t:
    case None{}:
      False{}
    case Some{Wasm.Type{p, +q}}:
      Wasm.valid.is_results(Wasm.valid.go(body, 0n, [q], U32.from_nat(Nat.add(p, n)), mem), q)

# a function (spec 3.5), of the type of its index
def Wasm.valid.func(types: List<&2, Wasm.Type>, +mem: Bool, f: Wasm.Func) -> Bool:
  match f:
    case Wasm.Func{x, n, body}:
      Wasm.valid.func.of(Wasm.type.at(types, x), n, body, mem)

def Wasm.valid.funcs(+types: List<&2, Wasm.Type>, +mem: Bool, fs: List<&2, Wasm.Func>) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case Con{f, rest}:
      Wasm.valid.func(types, mem, f) && Wasm.valid.funcs(types, mem, rest)

# memory limits (spec 3.2): at most 2^16 pages
def Wasm.valid.memory(m: Maybe<&2, Wasm.Limits>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{Wasm.Limits{min}}:
      U32.is_le(min, 65536)

def Wasm.export.name(e: Wasm.Export) -> List<&2, Word(8n)>:
  match e:
    case Wasm.Export.func{n, _}:
      n
    case Wasm.Export.memory{n}:
      n

# no export of es is named n
def Wasm.valid.is_new(+n: List<&2, Word(8n)>, es: List<&2, Wasm.Export>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Con{e, rest}:
      Bool.not(Sd.Name.is_eq(n, Wasm.export.name(e))) && Wasm.valid.is_new(n, rest)

# exports (spec 3.5): of a function that exists, or of the memory when there
# is one, each with its own name
def Wasm.valid.exports(es: List<&2, Wasm.Export>, +funcs: U32, +mem: Bool) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Con{Wasm.Export.func{+n, i}, +rest}:
      U32.is_lt(i, funcs) && Wasm.valid.is_new(n, rest) && Wasm.valid.exports(rest, funcs, mem)
    case Con{Wasm.Export.memory{+n}, +rest}:
      mem && Wasm.valid.is_new(n, rest) && Wasm.valid.exports(rest, funcs, mem)

# a data segment needs a memory (spec 3.5)
def Wasm.valid.data(seg: Maybe<&2, Wasm.Segment>, mem: Bool) -> Bool:
  match seg:
    case None{}:
      True{}
    case Some{_}:
      mem

# a module (spec 3.5)
def Wasm.valid.module(m: Wasm.Module) -> Bool:
  match m:
    case Wasm.Module{ts, +fs, +memory, es, seg}:
      +mem = Maybe.is_some(&2, Wasm.Limits, memory)
      Wasm.valid.memory(memory) && Wasm.valid.funcs(ts, mem, fs) &&
        Wasm.valid.exports(es, U32.from_nat(List.length(&2, Wasm.Func, fs)), mem) && Wasm.valid.data(seg, mem)

# Running
# -------
#
# Execution (spec 4.4): one step per instruction, and one more at the end
# of each block.

# the bytes of a memory: a tree over the 32 bits of an address, lowest bit
# first; zero stands for bytes that are all 0
type Wasm.Bytes is Data:
  Wasm.Bytes.zero{}
  Wasm.Bytes.byte{b: Word(8n)}
  Wasm.Bytes.node{lo: Wasm.Bytes, hi: Wasm.Bytes}

# a value read, and the bytes that it was read from
type Wasm.Peek<-A: Data> is Data:
  Wasm.Peek{v: A, m: Wasm.Bytes}

def Wasm.Bytes.peek.lo(r: Wasm.Peek<Word(8n)>, hi: Wasm.Bytes) -> Wasm.Peek<Word(8n)>:
  match r:
    case Wasm.Peek{b, lo}:
      Wasm.Peek{b, Wasm.Bytes.node{lo, hi}}

def Wasm.Bytes.peek.hi(lo: Wasm.Bytes, r: Wasm.Peek<Word(8n)>) -> Wasm.Peek<Word(8n)>:
  match r:
    case Wasm.Peek{b, hi}:
      Wasm.Peek{b, Wasm.Bytes.node{lo, hi}}

# the byte at the address of the n bits w, and the bytes again
def Wasm.Bytes.peek(n: Nat, w: Word(n), m: Wasm.Bytes) -> Wasm.Peek<Word(8n)>:
  match n:
    case 0n:
      match m:
        case Wasm.Bytes.byte{+b}:
          Wasm.Peek{b, Wasm.Bytes.byte{b}}
        case Wasm.Bytes.zero{}:
          Wasm.Peek{Word.zero(8n), Wasm.Bytes.zero{}}
        case Wasm.Bytes.node{lo, hi}:
          Wasm.Peek{Word.zero(8n), Wasm.Bytes.node{lo, hi}}
    case 1n+p:
      match w:
        case WCon{bit, t}:
          match bit:
            case False{}:
              match m:
                case Wasm.Bytes.node{lo, hi}:
                  Wasm.Bytes.peek.lo(Wasm.Bytes.peek(p, t, lo), hi)
                case Wasm.Bytes.zero{}:
                  Wasm.Peek{Word.zero(8n), Wasm.Bytes.zero{}}
                case Wasm.Bytes.byte{b}:
                  Wasm.Peek{Word.zero(8n), Wasm.Bytes.byte{b}}
            case True{}:
              match m:
                case Wasm.Bytes.node{lo, hi}:
                  Wasm.Bytes.peek.hi(lo, Wasm.Bytes.peek(p, t, hi))
                case Wasm.Bytes.zero{}:
                  Wasm.Peek{Word.zero(8n), Wasm.Bytes.zero{}}
                case Wasm.Bytes.byte{b}:
                  Wasm.Peek{Word.zero(8n), Wasm.Bytes.byte{b}}

# the bytes with b at the address of the n bits w
def Wasm.Bytes.set(n: Nat, w: Word(n), m: Wasm.Bytes, b: Word(8n)) -> Wasm.Bytes:
  match n:
    case 0n:
      Wasm.Bytes.byte{b}
    case 1n+p:
      match w:
        case WCon{bit, t}:
          match bit:
            case False{}:
              match m:
                case Wasm.Bytes.node{lo, hi}:
                  Wasm.Bytes.node{Wasm.Bytes.set(p, t, lo, b), hi}
                case _:
                  Wasm.Bytes.node{Wasm.Bytes.set(p, t, Wasm.Bytes.zero{}, b), Wasm.Bytes.zero{}}
            case True{}:
              match m:
                case Wasm.Bytes.node{lo, hi}:
                  Wasm.Bytes.node{lo, Wasm.Bytes.set(p, t, hi, b)}
                case _:
                  Wasm.Bytes.node{Wasm.Bytes.zero{}, Wasm.Bytes.set(p, t, Wasm.Bytes.zero{}, b)}

def Wasm.read8(m: Wasm.Bytes, a: U32) -> Wasm.Peek<Word(8n)>:
  match a:
    case U32{w}:
      Wasm.Bytes.peek(32n, w, m)

# a byte read, as its value: load8_u extends it with 0 bits (spec 4.4.7)
def Wasm.peek.value(r: Wasm.Peek<Word(8n)>) -> Wasm.Peek<U32>:
  match r:
    case Wasm.Peek{b, m}:
      Wasm.Peek{Sd.Byte.to_u32(b), m}

def Wasm.write8(m: Wasm.Bytes, a: U32, b: Word(8n)) -> Wasm.Bytes:
  match a:
    case U32{w}:
      Wasm.Bytes.set(32n, w, m, b)

def Wasm.read32.b3(v: U32, r: Wasm.Peek<Word(8n)>) -> Wasm.Peek<U32>:
  match r:
    case Wasm.Peek{b, m}:
      Wasm.Peek{U32.or(v, U32.shln(Sd.Byte.to_u32(b), 24n)), m}

def Wasm.read32.b2(v: U32, r: Wasm.Peek<Word(8n)>, +a: U32) -> Wasm.Peek<U32>:
  match r:
    case Wasm.Peek{b, m}:
      Wasm.read32.b3(U32.or(v, U32.shln(Sd.Byte.to_u32(b), 16n)), Wasm.read8(m, U32.add(a, 3)))

def Wasm.read32.b1(v: U32, r: Wasm.Peek<Word(8n)>, +a: U32) -> Wasm.Peek<U32>:
  match r:
    case Wasm.Peek{b, m}:
      Wasm.read32.b2(U32.or(v, U32.shln(Sd.Byte.to_u32(b), 8n)), Wasm.read8(m, U32.add(a, 2)), a)

def Wasm.read32.b0(r: Wasm.Peek<Word(8n)>, +a: U32) -> Wasm.Peek<U32>:
  match r:
    case Wasm.Peek{b, m}:
      Wasm.read32.b1(Sd.Byte.to_u32(b), Wasm.read8(m, U32.add(a, 1)), a)

# the 4 bytes from a, lowest first (spec 4.4.7: little-endian), and the bytes
def Wasm.read32(m: Wasm.Bytes, +a: U32) -> Wasm.Peek<U32>:
  Wasm.read32.b0(Wasm.read8(m, a), a)

def Wasm.write32(m: Wasm.Bytes, +a: U32, +v: U32) -> Wasm.Bytes:
  Wasm.write8(
    Wasm.write8(
      Wasm.write8(Wasm.write8(m, a, Sd.Byte.from_u32(v)), U32.add(a, 1), Sd.Byte.from_u32(U32.shrn(v, 8n))),
      U32.add(a, 2), Sd.Byte.from_u32(U32.shrn(v, 16n))),
    U32.add(a, 3), Sd.Byte.from_u32(U32.shrn(v, 24n)))

def Wasm.read.bytes.of(r: Wasm.Peek<Word(8n)>, more: Wasm.Bytes -> List<&2, Word(8n)>) -> List<&2, Word(8n)>:
  match r:
    case Wasm.Peek{b, m}:
      Con{b, more(m)}

# the n bytes from a
def Wasm.read.bytes(n: Nat, m: Wasm.Bytes, +a: U32) -> List<&2, Word(8n)>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Wasm.read.bytes.of(Wasm.read8(m, a), m2 => Wasm.read.bytes(p, m2, U32.inc(a)))

# the bytes xs, written from a on
def Wasm.write.bytes(xs: List<&2, Word(8n)>, +a: U32, m: Wasm.Bytes) -> Wasm.Bytes:
  match xs:
    case Nil{}:
      m
    case Con{x, rest}:
      Wasm.write.bytes(rest, U32.inc(a), Wasm.write8(m, a, x))

# len bytes from start fit in p pages of 2^16 bytes: start + len, as an
# integer (spec 4.4.7), is at most p * 2^16. A sum that wraps is 2^32 only when
# it wraps to 0, and 2^32 bytes fit in 65536 pages
def Wasm.fits.end(wrap: Bool, +p: U32, +end: U32) -> Bool:
  match wrap:
    case True{}:
      U32.is_zero(end) && U32.is_le(65536, p)
    case False{}:
      U32.is_zero(end) || U32.is_lt(U32.shrn(U32.sub(end, 1), 16n), p)

def Wasm.fits(+p: U32, +start: U32, +len: U32) -> Bool:
  +end = U32.add(start, len)
  Wasm.fits.end(U32.is_lt(end, start), p, end)

# an access of w bytes at a + o is inside the memory of p pages (spec 4.4.7);
# the sum a + o does not wrap
def Wasm.inside(+p: U32, +a: U32, +o: U32, w: U32) -> Bool:
  +ea = U32.add(a, o)
  Bool.not(U32.is_lt(ea, a)) && Wasm.fits(p, ea, w)

# a binary operator on i32 (spec 4.3.2); a shift is by its count mod 32
def Wasm.op(o: Wasm.Op, +a: U32, +b: U32) -> U32:
  match o:
    case Wasm.Op.add{}:
      U32.add(a, b)
    case Wasm.Op.sub{}:
      U32.sub(a, b)
    case Wasm.Op.and{}:
      U32.and(a, b)
    case Wasm.Op.or{}:
      U32.or(a, b)
    case Wasm.Op.shl{}:
      U32.shln(a, U32.to_nat(U32.and(b, 31)))
    case Wasm.Op.shr_u{}:
      U32.shrn(a, U32.to_nat(U32.and(b, 31)))
    case Wasm.Op.eq{}:
      Bool.to_u32(U32.is_eq(a, b))
    case Wasm.Op.ne{}:
      Bool.to_u32(U32.is_ne(a, b))
    case Wasm.Op.lt_u{}:
      Bool.to_u32(U32.is_lt(a, b))
    case Wasm.Op.gt_u{}:
      Bool.to_u32(U32.is_gt(a, b))
    case Wasm.Op.le_u{}:
      Bool.to_u32(U32.is_le(a, b))
    case Wasm.Op.ge_u{}:
      Bool.to_u32(U32.is_ge(a, b))

# a memory (spec 4.2): its size and the limit of its growth, in pages; the
# engine's answers to its grows within that limit, in order (Wasm.Engine);
# and its bytes
type Wasm.Memory is Data:
  Wasm.Memory{pages: U32, limit: U32, grows: List<&2, Bool>, bytes: Wasm.Bytes}

# a label (spec 4.2): for a loop, its body, which a branch runs again; the
# instructions after its block; and the stack's height when it began
type Wasm.Label is Data:
  Wasm.Label{loop: Maybe<&2, List<&2, Wasm.Instr>>, rest: List<&2, Wasm.Instr>, height: Nat}

# a running function (spec 4.2): the instructions left in its innermost
# block, its labels (innermost first), its number of results, its stack (top
# first) and its locals
type Wasm.Frame is Data:
  Wasm.Frame{
    code: List<&2, Wasm.Instr>,
    labels: List<&2, Wasm.Label>,
    results: Nat,
    stack: List<&2, U32>,
    locals: List<&2, U32>}

# the result of a step: the next frame, the function's results, or a trap,
# with the memory's state
type Wasm.Step is Data:
  Wasm.Step.next{f: Wasm.Frame, mem: Wasm.Memory}
  Wasm.Step.done{results: List<&2, U32>, mem: Wasm.Memory}
  Wasm.Step.trap{mem: Wasm.Memory}

# a function's n results: the n values on top of the stack, which holds the
# top first; the first result first (spec 4.4.10)
def Wasm.results(stack: List<&2, U32>, n: Nat) -> List<&2, U32>:
  List.reverse(&2, U32, List.take(&2, U32, stack, n))

# the end of a block (spec 4.4.8): its label goes, and the instructions after
# it run; at the end of the function, it gives its results
def Wasm.step.end(
  labels: List<&2, Wasm.Label>, +results: Nat, stack: List<&2, U32>, locals: List<&2, U32>, mem: Wasm.Memory
) -> Wasm.Step:
  match labels:
    case Nil{}:
      Wasm.Step.done{Wasm.results(stack, results), mem}
    case Con{Wasm.Label{_, after, _}, outer}:
      Wasm.Step.next{Wasm.Frame{after, outer, results, stack, locals}, mem}

def Wasm.step.br.to(
  loop: Maybe<&2, List<&2, Wasm.Instr>>,
  after: List<&2, Wasm.Instr>,
  h: Nat,
  outer: List<&2, Wasm.Label>,
  results: Nat,
  kept: List<&2, U32>,
  locals: List<&2, U32>,
  mem: Wasm.Memory
) -> Wasm.Step:
  match loop:
    case None{}:
      Wasm.Step.next{Wasm.Frame{after, outer, results, kept, locals}, mem}
    case Some{+body}:
      Wasm.Step.next{Wasm.Frame{body, Con{Wasm.Label{Some{body}, after, h}, outer}, results, kept, locals}, mem}

# a branch (spec 4.4.8) to the first label of ls: to the end of its block, or
# to the start of its loop again, with the stack cut to the label's height;
# past every label, the function returns its results
def Wasm.step.br(
  ls: List<&2, Wasm.Label>, +results: Nat, +stack: List<&2, U32>, locals: List<&2, U32>, mem: Wasm.Memory
) -> Wasm.Step:
  match ls:
    case Nil{}:
      Wasm.Step.done{Wasm.results(stack, results), mem}
    case Con{Wasm.Label{loop, after, +h}, outer}:
      Wasm.step.br.to(loop, after, h, outer, results,
        List.drop(&2, U32, stack, Nat.sub(List.length(&2, U32, stack), h)), locals, mem)

def Wasm.step.set(
  i: U32, rest: List<&2, Wasm.Instr>, labels: List<&2, Wasm.Label>, results: Nat, stack: List<&2, U32>,
  locals: List<&2, U32>, mem: Wasm.Memory
) -> Wasm.Step:
  match stack:
    case Con{v, s}:
      Wasm.Step.next{Wasm.Frame{rest, labels, results, s, List.set(&2, U32, locals, U32.to_nat(i), v)}, mem}
    case Nil{}:
      Wasm.Step.trap{mem}

def Wasm.step.tee(
  i: U32, rest: List<&2, Wasm.Instr>, labels: List<&2, Wasm.Label>, results: Nat, stack: List<&2, U32>,
  locals: List<&2, U32>, mem: Wasm.Memory
) -> Wasm.Step:
  match stack:
    case Con{+v, s}:
      Wasm.Step.next{Wasm.Frame{rest, labels, results, Con{v, s}, List.set(&2, U32, locals, U32.to_nat(i), v)}, mem}
    case Nil{}:
      Wasm.Step.trap{mem}

def Wasm.step.op(
  o: Wasm.Op, rest: List<&2, Wasm.Instr>, labels: List<&2, Wasm.Label>, results: Nat, stack: List<&2, U32>,
  locals: List<&2, U32>, mem: Wasm.Memory
) -> Wasm.Step:
  match stack:
    case Con{b, Con{a, s}}:
      Wasm.Step.next{Wasm.Frame{rest, labels, results, Con{Wasm.op(o, a, b), s}, locals}, mem}
    case _:
      Wasm.Step.trap{mem}

def Wasm.step.eqz(
  rest: List<&2, Wasm.Instr>, labels: List<&2, Wasm.Label>, results: Nat, stack: List<&2, U32>,
  locals: List<&2, U32>, mem: Wasm.Memory
) -> Wasm.Step:
  match stack:
    case Con{a, s}:
      Wasm.Step.next{Wasm.Frame{rest, labels, results, Con{Bool.to_u32(U32.is_zero(a)), s}, locals}, mem}
    case Nil{}:
      Wasm.Step.trap{mem}

def Wasm.load.of(wide: Bool, m: Wasm.Bytes, a: U32) -> Wasm.Peek<U32>:
  match wide:
    case True{}:
      Wasm.read32(m, a)
    case False{}:
      Wasm.peek.value(Wasm.read8(m, a))

def Wasm.step.peeked(
  r: Wasm.Peek<U32>, p: U32, lim: U32, gs: List<&2, Bool>, rest: List<&2, Wasm.Instr>, labels: List<&2, Wasm.Label>,
  results: Nat, s: List<&2, U32>, locals: List<&2, U32>
) -> Wasm.Step:
  match r:
    case Wasm.Peek{v, bytes}:
      Wasm.Step.next{Wasm.Frame{rest, labels, results, Con{v, s}, locals}, Wasm.Memory{p, lim, gs, bytes}}

def Wasm.step.loaded(
  ok: Bool, wide: Bool, ea: U32, rest: List<&2, Wasm.Instr>, labels: List<&2, Wasm.Label>, results: Nat,
  s: List<&2, U32>, locals: List<&2, U32>, mem: Wasm.Memory
) -> Wasm.Step:
  match ok:
    case True{}:
      match mem:
        case Wasm.Memory{p, lim, gs, bytes}:
          Wasm.step.peeked(Wasm.load.of(wide, bytes, ea), p, lim, gs, rest, labels, results, s, locals)
    case False{}:
      Wasm.Step.trap{mem}

# i32.load or i32.load8_u (spec 4.4.7): the w bytes at the address plus the
# offset o, or a trap when they are outside the memory
def Wasm.step.load(
  +o: U32, +w: U32, rest: List<&2, Wasm.Instr>, labels: List<&2, Wasm.Label>, results: Nat,
  stack: List<&2, U32>, locals: List<&2, U32>, mem: Wasm.Memory
) -> Wasm.Step:
  match stack:
    case Con{+a, s}:
      match mem:
        case Wasm.Memory{+p, lim, gs, bytes}:
          Wasm.step.loaded(Wasm.inside(p, a, o, w), U32.is_eq(w, 4), U32.add(a, o),
            rest, labels, results, s, locals, Wasm.Memory{p, lim, gs, bytes})
    case Nil{}:
      Wasm.Step.trap{mem}

def Wasm.store.of(wide: Bool, m: Wasm.Bytes, a: U32, v: U32) -> Wasm.Bytes:
  match wide:
    case True{}:
      Wasm.write32(m, a, v)
    case False{}:
      Wasm.write8(m, a, Sd.Byte.from_u32(v))

def Wasm.step.stored(
  ok: Bool, wide: Bool, ea: U32, v: U32, rest: List<&2, Wasm.Instr>, labels: List<&2, Wasm.Label>,
  results: Nat, s: List<&2, U32>, locals: List<&2, U32>, mem: Wasm.Memory
) -> Wasm.Step:
  match ok:
    case True{}:
      match mem:
        case Wasm.Memory{p, lim, gs, bytes}:
          Wasm.Step.next{Wasm.Frame{rest, labels, results, s, locals}, Wasm.Memory{p, lim, gs, Wasm.store.of(wide, bytes, ea, v)}}
    case False{}:
      Wasm.Step.trap{mem}

# i32.store or i32.store8 (spec 4.4.7): the value's w low bytes at the
# address plus the offset o, or a trap when they are outside the memory
def Wasm.step.store(
  +o: U32, +w: U32, rest: List<&2, Wasm.Instr>, labels: List<&2, Wasm.Label>, results: Nat,
  stack: List<&2, U32>, locals: List<&2, U32>, mem: Wasm.Memory
) -> Wasm.Step:
  match stack:
    case Con{v, Con{+a, s}}:
      match mem:
        case Wasm.Memory{+p, lim, gs, bytes}:
          Wasm.step.stored(Wasm.inside(p, a, o, w), U32.is_eq(w, 4), U32.add(a, o), v,
            rest, labels, results, s, locals, Wasm.Memory{p, lim, gs, bytes})
    case _:
      Wasm.Step.trap{mem}

# memory.size (spec 4.4.7): the size, in pages
def Wasm.step.size(
  rest: List<&2, Wasm.Instr>, labels: List<&2, Wasm.Label>, results: Nat, stack: List<&2, U32>,
  locals: List<&2, U32>, mem: Wasm.Memory
) -> Wasm.Step:
  match mem:
    case Wasm.Memory{+p, lim, gs, bytes}:
      Wasm.Step.next{Wasm.Frame{rest, labels, results, Con{p, stack}, locals}, Wasm.Memory{p, lim, gs, bytes}}

def Wasm.step.grown(
  ok: Bool, p: U32, n: U32, lim: U32, gs: List<&2, Bool>, bytes: Wasm.Bytes, rest: List<&2, Wasm.Instr>,
  labels: List<&2, Wasm.Label>, results: Nat, s: List<&2, U32>, locals: List<&2, U32>
) -> Wasm.Step:
  match ok:
    case True{}:
      Wasm.Step.next{Wasm.Frame{rest, labels, results, Con{p, s}, locals}, Wasm.Memory{n, lim, gs, bytes}}
    case False{}:
      Wasm.Step.next{Wasm.Frame{rest, labels, results, Con{4294967295, s}, locals}, Wasm.Memory{p, lim, gs, bytes}}

# the engine's answer to a grow within the limit: past its answers, it
# grants it
def Wasm.grants(gs: List<&2, Bool>) -> Bool:
  match gs:
    case Nil{}:
      True{}
    case Con{g, _}:
      g

# a grow within the limit (in) takes the engine's next answer; past the
# limit, it fails, and takes none
def Wasm.step.within(
  in: Bool, p: U32, n: U32, lim: U32, +gs: List<&2, Bool>, bytes: Wasm.Bytes, rest: List<&2, Wasm.Instr>,
  labels: List<&2, Wasm.Label>, results: Nat, s: List<&2, U32>, locals: List<&2, U32>
) -> Wasm.Step:
  match in:
    case True{}:
      Wasm.step.grown(Wasm.grants(gs), p, n, lim, List.drop(&2, Bool, gs, 1n), bytes, rest, labels, results, s, locals)
    case False{}:
      Wasm.step.grown(False{}, p, n, lim, gs, bytes, rest, labels, results, s, locals)

# memory.grow (spec 4.4.7): by d pages, giving the old size, when the new
# size is within the limit and the engine grants it; else -1, with no
# change. The spec lets an engine refuse any grow (memory.grow-fail)
def Wasm.step.grow(
  rest: List<&2, Wasm.Instr>, labels: List<&2, Wasm.Label>, results: Nat, stack: List<&2, U32>,
  locals: List<&2, U32>, mem: Wasm.Memory
) -> Wasm.Step:
  match stack:
    case Con{d, s}:
      match mem:
        case Wasm.Memory{+p, +lim, gs, bytes}:
          +n = U32.add(p, d)
          Wasm.step.within(U32.is_ge(n, p) && U32.is_le(n, lim), p, n, lim, gs, bytes, rest, labels, results, s, locals)
    case Nil{}:
      Wasm.Step.trap{mem}

def Wasm.step.br_if.if(
  zero: Bool, l: U32, rest: List<&2, Wasm.Instr>, labels: List<&2, Wasm.Label>, results: Nat,
  s: List<&2, U32>, locals: List<&2, U32>, mem: Wasm.Memory
) -> Wasm.Step:
  match zero:
    case True{}:
      Wasm.Step.next{Wasm.Frame{rest, labels, results, s, locals}, mem}
    case False{}:
      Wasm.step.br(List.drop(&2, Wasm.Label, labels, U32.to_nat(l)), results, s, locals, mem)

# br_if l (spec 4.4.8): a branch to l unless the value is 0
def Wasm.step.br_if(
  l: U32, rest: List<&2, Wasm.Instr>, labels: List<&2, Wasm.Label>, results: Nat, stack: List<&2, U32>,
  locals: List<&2, U32>, mem: Wasm.Memory
) -> Wasm.Step:
  match stack:
    case Con{c, s}:
      Wasm.step.br_if.if(U32.is_zero(c), l, rest, labels, results, s, locals, mem)
    case Nil{}:
      Wasm.Step.trap{mem}

# one step of the instruction x, with the instructions rest after it in its
# block (spec 4.4)
def Wasm.step.instr(
  x: Wasm.Instr, rest: List<&2, Wasm.Instr>, labels: List<&2, Wasm.Label>, results: Nat,
  +stack: List<&2, U32>, +locals: List<&2, U32>, mem: Wasm.Memory
) -> Wasm.Step:
  match x:
    case Wasm.Instr.const{n}:
      Wasm.Step.next{Wasm.Frame{rest, labels, results, Con{n, stack}, locals}, mem}
    case Wasm.Instr.local_get{i}:
      Wasm.Step.next{Wasm.Frame{rest, labels, results,
        Con{Maybe.default(&2, U32, List.get(&2, U32, locals, U32.to_nat(i)), 0), stack}, locals}, mem}
    case Wasm.Instr.local_set{i}:
      Wasm.step.set(i, rest, labels, results, stack, locals, mem)
    case Wasm.Instr.local_tee{i}:
      Wasm.step.tee(i, rest, labels, results, stack, locals, mem)
    case Wasm.Instr.op{o}:
      Wasm.step.op(o, rest, labels, results, stack, locals, mem)
    case Wasm.Instr.eqz{}:
      Wasm.step.eqz(rest, labels, results, stack, locals, mem)
    case Wasm.Instr.load{o}:
      Wasm.step.load(o, 4, rest, labels, results, stack, locals, mem)
    case Wasm.Instr.load8_u{o}:
      Wasm.step.load(o, 1, rest, labels, results, stack, locals, mem)
    case Wasm.Instr.store{o}:
      Wasm.step.store(o, 4, rest, labels, results, stack, locals, mem)
    case Wasm.Instr.store8{o}:
      Wasm.step.store(o, 1, rest, labels, results, stack, locals, mem)
    case Wasm.Instr.memory_size{}:
      Wasm.step.size(rest, labels, results, stack, locals, mem)
    case Wasm.Instr.memory_grow{}:
      Wasm.step.grow(rest, labels, results, stack, locals, mem)
    case Wasm.Instr.block{body}:
      Wasm.Step.next{Wasm.Frame{body,
        Con{Wasm.Label{None{}, rest, List.length(&2, U32, stack)}, labels}, results, stack, locals}, mem}
    case Wasm.Instr.loop{+body}:
      Wasm.Step.next{Wasm.Frame{body,
        Con{Wasm.Label{Some{body}, rest, List.length(&2, U32, stack)}, labels}, results, stack, locals}, mem}
    case Wasm.Instr.br{l}:
      Wasm.step.br(List.drop(&2, Wasm.Label, labels, U32.to_nat(l)), results, stack, locals, mem)
    case Wasm.Instr.br_if{l}:
      Wasm.step.br_if(l, rest, labels, results, stack, locals, mem)

# one step of a running function
def Wasm.step(f: Wasm.Frame, mem: Wasm.Memory) -> Wasm.Step:
  match f:
    case Wasm.Frame{code, labels, results, stack, locals}:
      match code:
        case Nil{}:
          Wasm.step.end(labels, results, stack, locals, mem)
        case Con{x, rest}:
          Wasm.step.instr(x, rest, labels, results, stack, locals, mem)

# how a call ends: its results, the memory, and the steps that it took; a
# trap, with the memory; or no end within the fuel
type Wasm.Call is Data:
  Wasm.Call.done{results: List<&2, U32>, mem: Wasm.Memory, steps: Nat}
  Wasm.Call.trap{mem: Wasm.Memory}
  Wasm.Call.not_done{}

# the call c, after one more step
def Wasm.call.plus(c: Wasm.Call) -> Wasm.Call:
  match c:
    case Wasm.Call.done{rs, m, n}:
      Wasm.Call.done{rs, m, 1n+n}
    case Wasm.Call.trap{m}:
      Wasm.Call.trap{m}
    case Wasm.Call.not_done{}:
      Wasm.Call.not_done{}

def Wasm.call.stepped(s: Wasm.Step, more: Wasm.Frame -> Wasm.Memory -> Wasm.Call) -> Wasm.Call:
  match s:
    case Wasm.Step.next{f, m}:
      Wasm.call.plus(more(f, m))
    case Wasm.Step.done{rs, m}:
      Wasm.Call.done{rs, m, 1n}
    case Wasm.Step.trap{m}:
      Wasm.Call.trap{m}

# the steps of a running function, one per unit of fuel
def Wasm.call.go(fuel: Nat, f: Wasm.Frame, mem: Wasm.Memory) -> Wasm.Call:
  match fuel:
    case 0n:
      Wasm.Call.not_done{}
    case 1n+k:
      Wasm.call.stepped(Wasm.step(f, mem), g => m => Wasm.call.go(k, g, m))

# a call of the function, of q results, to the arguments, in order (spec
# 4.4.10): its locals are the arguments, then its own locals at 0
def Wasm.call(fuel: Nat, q: Nat, func: Wasm.Func, args: List<&2, U32>, mem: Wasm.Memory) -> Wasm.Call:
  match func:
    case Wasm.Func{_, n, body}:
      Wasm.call.go(fuel, Wasm.Frame{body, Nil{}, q, Nil{}, List.append(&2, U32, args, List.replicate(U32, n, 0))}, mem)

# Instances
# ---------
#
# Instantiation (spec 4.5.4) and invocation (spec 4.5.5), as the host does
# them: the spec's own tests use these.

# an instance (spec 4.2): its module, and the state of its memory
type Wasm.Instance is Data:
  Wasm.Instance{module: Wasm.Module, mem: Wasm.Memory}

# how an instantiation ends
type Wasm.Made is Data:
  Wasm.Made.instance{i: Wasm.Instance}
  Wasm.Made.unsupported{}
  Wasm.Made.out_of_memory{}
  Wasm.Made.trap{}

def Wasm.min.if(le: Bool, a: U32, b: U32) -> U32:
  match le:
    case True{}:
      a
    case False{}:
      b

def Wasm.min(+a: U32, +b: U32) -> U32:
  Wasm.min.if(U32.is_le(a, b), a, b)

def Wasm.memory.of.if(ok: Bool, mem: Wasm.Memory) -> Maybe<&2, Wasm.Memory>:
  match ok:
    case True{}:
      Some{mem}
    case False{}:
      None{}

# the memory of the limits, at its minimum, when that fits in m pages, and
# whose growth stops at m pages and at 2^16 pages (4 GiB), with the engine's
# answers gs to its grows; a module without one gets a memory of no pages,
# which it cannot use
def Wasm.memory.of(l: Maybe<&2, Wasm.Limits>, +m: U32, gs: List<&2, Bool>) -> Maybe<&2, Wasm.Memory>:
  match l:
    case None{}:
      Some{Wasm.Memory{0, 0, gs, Wasm.Bytes.zero{}}}
    case Some{Wasm.Limits{+min}}:
      Wasm.memory.of.if(U32.is_le(min, m), Wasm.Memory{min, Wasm.min(m, 65536), gs, Wasm.Bytes.zero{}})

def Wasm.fits.len(+p: U32, +k: U32, n: Maybe<&2, U32>) -> Bool:
  match n:
    case None{}:
      False{}
    case Some{len}:
      Wasm.fits(p, k, len)

def Wasm.memory.init.if(ok: Bool, p: U32, lim: U32, gs: List<&2, Bool>, bytes: Wasm.Bytes) -> Maybe<&2, Wasm.Memory>:
  match ok:
    case True{}:
      Some{Wasm.Memory{p, lim, gs, bytes}}
    case False{}:
      None{}

# the memory with the data segment's bytes from its offset (spec 4.5.4), or
# None, a trap, when they do not fit
def Wasm.memory.init(seg: Maybe<&2, Wasm.Segment>, mem: Wasm.Memory) -> Maybe<&2, Wasm.Memory>:
  match seg:
    case None{}:
      Some{mem}
    case Some{Wasm.Segment{+k, +xs}}:
      match mem:
        case Wasm.Memory{+p, lim, gs, bytes}:
          Wasm.memory.init.if(Wasm.fits.len(p, k, Wasm.length32(xs)), p, lim, gs, Wasm.write.bytes(xs, k, bytes))

def Wasm.instantiate.made(m: Maybe<&2, Wasm.Memory>, module: Wasm.Module) -> Wasm.Made:
  match m:
    case None{}:
      Wasm.Made.trap{}
    case Some{mem}:
      Wasm.Made.instance{Wasm.Instance{module, mem}}

def Wasm.instantiate.sized(m: Maybe<&2, Wasm.Memory>, seg: Maybe<&2, Wasm.Segment>, module: Wasm.Module) -> Wasm.Made:
  match m:
    case None{}:
      Wasm.Made.out_of_memory{}
    case Some{mem}:
      Wasm.instantiate.made(Wasm.memory.init(seg, mem), module)

def Wasm.instantiate.valid(ok: Bool, module: Wasm.Module, +m: U32, gs: List<&2, Bool>) -> Wasm.Made:
  match ok:
    case False{}:
      Wasm.Made.unsupported{}
    case True{}:
      match module:
        case Wasm.Module{ts, fs, +memory, es, +seg}:
          Wasm.instantiate.sized(Wasm.memory.of(memory, m, gs), seg, Wasm.Module{ts, fs, memory, es, seg})

def Wasm.instantiate.decoded(m: Maybe<&2, Wasm.Module>, +lim: U32, gs: List<&2, Bool>) -> Wasm.Made:
  match m:
    case None{}:
      Wasm.Made.unsupported{}
    case Some{+module}:
      Wasm.instantiate.valid(Wasm.valid.module(module), module, lim, gs)

# an instance of the module of the bytes w, with at most m pages of memory,
# and the engine's answers gs to the memory's grows
def Wasm.instantiate(w: List<&2, Word(8n)>, m: U32, gs: List<&2, Bool>) -> Wasm.Made:
  Wasm.instantiate.decoded(Wasm.decode.module(w), m, gs)

def Wasm.export.find.if(hit: Bool, i: U32, more: Unit -> Maybe<&2, U32>) -> Maybe<&2, U32>:
  match hit:
    case True{}:
      Some{i}
    case False{}:
      more(Unit{})

# the index of the function exported as name
def Wasm.export.find(es: List<&2, Wasm.Export>, +name: List<&2, Word(8n)>) -> Maybe<&2, U32>:
  match es:
    case Nil{}:
      None{}
    case Con{Wasm.Export.func{n, i}, rest}:
      Wasm.export.find.if(Sd.Name.is_eq(n, name), i, u => Wasm.export.find(rest, name))
    case Con{Wasm.Export.memory{_}, rest}:
      Wasm.export.find(rest, name)

# the memory is exported as name
def Wasm.export.has_memory(es: List<&2, Wasm.Export>, +name: List<&2, Word(8n)>) -> Bool:
  match es:
    case Nil{}:
      False{}
    case Con{Wasm.Export.memory{n}, rest}:
      Sd.Name.is_eq(n, name) || Wasm.export.has_memory(rest, name)
    case Con{Wasm.Export.func{_, _}, rest}:
      Wasm.export.has_memory(rest, name)

def Wasm.func.at.if(zero: Bool, f: Wasm.Func, more: Unit -> Maybe<&2, Wasm.Func>) -> Maybe<&2, Wasm.Func>:
  match zero:
    case True{}:
      Some{f}
    case False{}:
      more(Unit{})

# the function of index i
def Wasm.func.at(fs: List<&2, Wasm.Func>, +i: U32) -> Maybe<&2, Wasm.Func>:
  match fs:
    case Nil{}:
      None{}
    case Con{f, rest}:
      Wasm.func.at.if(U32.is_zero(i), f, u => Wasm.func.at(rest, U32.sub(i, 1)))

# the function exported as name, if any
def Wasm.export.func(+fs: List<&2, Wasm.Func>, es: List<&2, Wasm.Export>, name: List<&2, Word(8n)>) -> Maybe<&2, Wasm.Func>:
  Maybe.bind(&2, U32, Wasm.Func, Wasm.export.find(es, name), i => Wasm.func.at(fs, i))

# the type has p parameters and q results
def Wasm.type.is(t: Maybe<&2, Wasm.Type>, p: Nat, q: Nat) -> Bool:
  match t:
    case None{}:
      False{}
    case Some{Wasm.Type{a, b}}:
      Nat.is_eq(a, p) && Nat.is_eq(b, q)

# the function's type, of the module's types ts, has p parameters and q
# results
def Wasm.func.is_type(ts: List<&2, Wasm.Type>, f: Maybe<&2, Wasm.Func>, p: Nat, q: Nat) -> Bool:
  match f:
    case None{}:
      False{}
    case Some{Wasm.Func{x, _, _}}:
      Wasm.type.is(Wasm.type.at(ts, x), p, q)

# how an invocation ends: its results, with the instance after it and the
# steps that it took; a trap, with the instance after it; no end within the
# fuel; or no such function
type Wasm.Invoked is Data:
  Wasm.Invoked.values{vs: List<&2, U32>, i: Wasm.Instance, steps: Nat}
  Wasm.Invoked.trap{i: Wasm.Instance}
  Wasm.Invoked.not_done{}
  Wasm.Invoked.unsupported{}

def Wasm.invoked(c: Wasm.Call, module: Wasm.Module) -> Wasm.Invoked:
  match c:
    case Wasm.Call.done{vs, mem, n}:
      Wasm.Invoked.values{vs, Wasm.Instance{module, mem}, n}
    case Wasm.Call.trap{mem}:
      Wasm.Invoked.trap{Wasm.Instance{module, mem}}
    case Wasm.Call.not_done{}:
      Wasm.Invoked.not_done{}

def Wasm.invoke.arity(
  ok: Bool, q: Nat, f: Wasm.Func, fuel: Nat, args: List<&2, U32>, mem: Wasm.Memory, module: Wasm.Module
) -> Wasm.Invoked:
  match ok:
    case True{}:
      Wasm.invoked(Wasm.call(fuel, q, f, args, mem), module)
    case False{}:
      Wasm.Invoked.unsupported{}

# a call of the function f, of the type t
def Wasm.invoke.typed(
  t: Maybe<&2, Wasm.Type>, f: Wasm.Func, fuel: Nat, +args: List<&2, U32>, mem: Wasm.Memory, module: Wasm.Module
) -> Wasm.Invoked:
  match t:
    case None{}:
      Wasm.Invoked.unsupported{}
    case Some{Wasm.Type{p, q}}:
      Wasm.invoke.arity(Nat.is_eq(p, List.length(&2, U32, args)), q, f, fuel, args, mem, module)

def Wasm.invoke.found(
  f: Maybe<&2, Wasm.Func>, types: List<&2, Wasm.Type>, fuel: Nat, args: List<&2, U32>, mem: Wasm.Memory,
  module: Wasm.Module
) -> Wasm.Invoked:
  match f:
    case None{}:
      Wasm.Invoked.unsupported{}
    case Some{Wasm.Func{+x, n, body}}:
      Wasm.invoke.typed(Wasm.type.at(types, x), Wasm.Func{x, n, body}, fuel, args, mem, module)

# a call of the function exported as name, with the arguments in order, in at
# most fuel steps; unsupported when no such function takes as many arguments
def Wasm.invoke(fuel: Nat, inst: Wasm.Instance, name: List<&2, Word(8n)>, args: List<&2, U32>) -> Wasm.Invoked:
  match inst:
    case Wasm.Instance{module, mem}:
      match module:
        case Wasm.Module{+ts, +fs, memory, +es, seg}:
          Wasm.invoke.found(Wasm.export.func(fs, es, name), ts, fuel, args, mem, Wasm.Module{ts, fs, memory, es, seg})

# Host
# ----
#
# How a compiled program runs. Its module exports its memory as
# "memory", alloc, of 1 parameter and 1 result, and run, of 2 parameters
# and 1 result. The host calls alloc(n) for the n bytes of the input; -1
# means out of memory. It writes the input from the address that alloc
# gives, then calls run(address, n), which gives 0 for a result, 1 for out of
# memory and 2 for no result. For a result, bytes 0 to 3 of the memory hold
# the output's address, and bytes 4 to 7 its length. The two calls take at
# most f steps in all.

# the names that the host uses, as ASCII bytes
def Wasm.name.memory() -> List<&2, Word(8n)>:
  [Sd.Byte.from_u32(109), Sd.Byte.from_u32(101), Sd.Byte.from_u32(109), Sd.Byte.from_u32(111), Sd.Byte.from_u32(114), Sd.Byte.from_u32(121)]

def Wasm.name.alloc() -> List<&2, Word(8n)>:
  [Sd.Byte.from_u32(97), Sd.Byte.from_u32(108), Sd.Byte.from_u32(108), Sd.Byte.from_u32(111), Sd.Byte.from_u32(99)]

def Wasm.name.run() -> List<&2, Word(8n)>:
  [Sd.Byte.from_u32(114), Sd.Byte.from_u32(117), Sd.Byte.from_u32(110)]

def Wasm.run.output.if(ok: Bool, bytes: Wasm.Bytes, a: U32, n: U32) -> Wasm.Outcome:
  match ok:
    case True{}:
      Wasm.Outcome.result{Wasm.read.bytes(U32.to_nat(n), bytes, a)}
    case False{}:
      Wasm.Outcome.trap{}

def Wasm.run.output.n(+p: U32, +a: U32, r: Wasm.Peek<U32>) -> Wasm.Outcome:
  match r:
    case Wasm.Peek{+n, bytes}:
      Wasm.run.output.if(Wasm.fits(p, a, n), bytes, a, n)

def Wasm.run.output.a(+p: U32, r: Wasm.Peek<U32>) -> Wasm.Outcome:
  match r:
    case Wasm.Peek{a, bytes}:
      Wasm.run.output.n(p, a, Wasm.read32(bytes, 4))

def Wasm.run.output.at(ok: Bool, p: U32, bytes: Wasm.Bytes) -> Wasm.Outcome:
  match ok:
    case True{}:
      Wasm.run.output.a(p, Wasm.read32(bytes, 0))
    case False{}:
      Wasm.Outcome.trap{}

# the output: the length at byte 4 of the bytes from the address at byte 0
def Wasm.run.output(mem: Wasm.Memory) -> Wasm.Outcome:
  match mem:
    case Wasm.Memory{+p, _, _, bytes}:
      Wasm.run.output.at(Wasm.fits(p, 0, 8), p, bytes)

def Wasm.run.status(zero: Bool, one: Bool, two: Bool, mem: Wasm.Memory) -> Wasm.Outcome:
  match zero one two:
    case True{} _ _:
      Wasm.run.output(mem)
    case False{} True{} _:
      Wasm.Outcome.out_of_memory{}
    case False{} False{} True{}:
      Wasm.Outcome.no_result{}
    case False{} False{} False{}:
      Wasm.Outcome.trap{}

# what run gave
def Wasm.run.ran(r: Wasm.Invoked) -> Wasm.Outcome:
  match r:
    case Wasm.Invoked.values{Con{+s, _}, Wasm.Instance{_, mem}, _}:
      Wasm.run.status(U32.is_eq(s, 0), U32.is_eq(s, 1), U32.is_eq(s, 2), mem)
    case Wasm.Invoked.trap{_}:
      Wasm.Outcome.trap{}
    case Wasm.Invoked.not_done{}:
      Wasm.Outcome.not_done{}
    case Wasm.Invoked.unsupported{}:
      Wasm.Outcome.unsupported{}
    case _:
      Wasm.Outcome.trap{}

def Wasm.run.written(ok: Bool, f: Nat, inst: Wasm.Instance, a: U32, n: U32) -> Wasm.Outcome:
  match ok:
    case True{}:
      Wasm.run.ran(Wasm.invoke(f, inst, Wasm.name.run(), [a, n]))
    case False{}:
      Wasm.Outcome.trap{}

# the input written from the address a, when its n bytes fit
def Wasm.run.input(f: Nat, inst: Wasm.Instance, +a: U32, +n: U32, i: List<&2, Word(8n)>) -> Wasm.Outcome:
  match inst:
    case Wasm.Instance{module, mem}:
      match mem:
        case Wasm.Memory{+p, lim, gs, bytes}:
          Wasm.run.written(Wasm.fits(p, a, n), f,
            Wasm.Instance{module, Wasm.Memory{p, lim, gs, Wasm.write.bytes(i, a, bytes)}}, a, n)

def Wasm.run.alloced.if(full: Bool, f: Nat, inst: Wasm.Instance, a: U32, n: U32, i: List<&2, Word(8n)>) -> Wasm.Outcome:
  match full:
    case True{}:
      Wasm.Outcome.out_of_memory{}
    case False{}:
      Wasm.run.input(f, inst, a, n, i)

# what alloc gave: the input's address, or -1 for out of memory; run then
# has the steps that alloc left
def Wasm.run.alloced(r: Wasm.Invoked, f: Nat, n: U32, i: List<&2, Word(8n)>) -> Wasm.Outcome:
  match r:
    case Wasm.Invoked.values{Con{+a, _}, inst, used}:
      Wasm.run.alloced.if(U32.is_eq(a, 4294967295), Nat.sub(f, used), inst, a, n, i)
    case Wasm.Invoked.trap{_}:
      Wasm.Outcome.trap{}
    case Wasm.Invoked.not_done{}:
      Wasm.Outcome.not_done{}
    case Wasm.Invoked.unsupported{}:
      Wasm.Outcome.unsupported{}
    case _:
      Wasm.Outcome.trap{}

# the input's length: an input of 2^32 bytes or more cannot fit in memory
def Wasm.run.sized(n: Maybe<&2, U32>, +f: Nat, inst: Wasm.Instance, i: List<&2, Word(8n)>) -> Wasm.Outcome:
  match n:
    case None{}:
      Wasm.Outcome.out_of_memory{}
    case Some{+k}:
      Wasm.run.alloced(Wasm.invoke(f, inst, Wasm.name.alloc(), [k]), f, k, i)

# the module exports what the host uses
def Wasm.run.is_host(inst: Wasm.Instance) -> Bool:
  match inst:
    case Wasm.Instance{Wasm.Module{+ts, +fs, _, +es, _}, _}:
      Wasm.export.has_memory(es, Wasm.name.memory()) &&
        Wasm.func.is_type(ts, Wasm.export.func(fs, es, Wasm.name.alloc()), 1n, 1n) &&
        Wasm.func.is_type(ts, Wasm.export.func(fs, es, Wasm.name.run()), 2n, 1n)

def Wasm.run.instance(ok: Bool, f: Nat, inst: Wasm.Instance, +i: List<&2, Word(8n)>) -> Wasm.Outcome:
  match ok:
    case True{}:
      Wasm.run.sized(Wasm.length32(i), f, inst, i)
    case False{}:
      Wasm.Outcome.unsupported{}

def Wasm.run.made(f: Nat, made: Wasm.Made, i: List<&2, Word(8n)>) -> Wasm.Outcome:
  match made:
    case Wasm.Made.instance{+inst}:
      Wasm.run.instance(Wasm.run.is_host(inst), f, inst, i)
    case Wasm.Made.unsupported{}:
      Wasm.Outcome.unsupported{}
    case Wasm.Made.out_of_memory{}:
      Wasm.Outcome.out_of_memory{}
    case Wasm.Made.trap{}:
      Wasm.Outcome.trap{}

# what an engine decides that the spec leaves open: the most pages that it
# gives a memory, and its answers to grows within that limit, in order
# (False refuses one; past the list, it grants each)
type Wasm.Engine is Data:
  Wasm.Engine{pages: U32, grows: List<&2, Bool>}

# a run of the module of the bytes w on the input bytes i, in at most f
# steps of its functions, on the engine e
def Wasm.run(f: Nat, w: List<&2, Word(8n)>, i: List<&2, Word(8n)>, e: Wasm.Engine) -> Wasm.Outcome:
  match e:
    case Wasm.Engine{m, gs}:
      Wasm.run.made(f, Wasm.instantiate(w, m, gs), i)
