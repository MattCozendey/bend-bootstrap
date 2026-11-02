# compiler: the round trip of a function body's instructions
# ===========================================================
#
# Wasm.decode.instrs, with the fuel that Wasm.decode.func.body gives it,
# reads back the instructions that Wasm.encode.instrs writes, then the end
# 0x0B (instrs.round, at the end), for every list of instructions.
#
# The induction (run) goes on the instruction tree: the bytes of xs, then
# more, with fuel |bytes| + k, read as the heads of xs (each one fuel; a
# block's body by the hypothesis on it), then go on at more with fuel
# |more| + left(xs, k), xs reversed onto those so far.

import Base
import ../../Shared/shared.bend as Sd
import ../../Wasm/impl.bend as Wa
import ./impl.bend as Cr
import ./leb_round_trip.bend as L
import ../need_big.bend as N

# Booleans
# --------

def and.l(a: Bool, b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      L.ft({False{} == True{} : Bool}, h)

def and.r(a: Bool, b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      L.ft({b == True{} : Bool}, h)

def not.t(b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {False{} == b : Bool}:
  match b:
    case True{}:
      L.ft({False{} == True{} : Bool}, h)
    case False{}:
      {==}

# Nat
# ---

def add.succ(a: Nat, +k: Nat) -> {Nat.add(a, 1n+k) == 1n+Nat.add(a, k) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, n => 1n+n, Nat.add(p, 1n+k), 1n+Nat.add(p, k), add.succ(p, k))

def add.one(a: Nat) -> {Nat.add(a, 1n) == 1n+a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, n => 1n+n, Nat.add(p, 1n), 1n+p, add.one(p))

# the fuel of the bytes of I then E, and k more, is that of E and of I and k
def add.len(I: List<&2, Word(8n)>, +E: List<&2, Word(8n)>, +k: Nat) ->
  {Nat.add(List.length(&2, Word(8n), List.append(&2, Word(8n), I, E)), k) ==
    Nat.add(List.length(&2, Word(8n), E), Nat.add(List.length(&2, Word(8n), I), k)) : Nat}:
  match I:
    case Nil{}:
      {==}
    case Con{i, +t}:
      Equal.trans(Nat, 1n+Nat.add(List.length(&2, Word(8n), List.append(&2, Word(8n), t, E)), k),
        1n+Nat.add(List.length(&2, Word(8n), E), Nat.add(List.length(&2, Word(8n), t), k)),
        Nat.add(List.length(&2, Word(8n), E), 1n+Nat.add(List.length(&2, Word(8n), t), k)),
        Equal.cong(Nat, Nat, n => 1n+n, Nat.add(List.length(&2, Word(8n), List.append(&2, Word(8n), t, E)), k),
          Nat.add(List.length(&2, Word(8n), E), Nat.add(List.length(&2, Word(8n), t), k)), add.len(t, E, k)),
        Equal.sym(Nat, Nat.add(List.length(&2, Word(8n), E), 1n+Nat.add(List.length(&2, Word(8n), t), k)),
          1n+Nat.add(List.length(&2, Word(8n), E), Nat.add(List.length(&2, Word(8n), t), k)),
          add.succ(List.length(&2, Word(8n), E), Nat.add(List.length(&2, Word(8n), t), k))))

# Lists
# -----

def append.nil(xs: List<&2, Wa.Wasm.Instr>) -> {List.append(&2, Wa.Wasm.Instr, xs, []) == xs : List<&2, Wa.Wasm.Instr>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, t}:
      Equal.cong(List<&2, Wa.Wasm.Instr>, List<&2, Wa.Wasm.Instr>, l => Con{x, l},
        List.append(&2, Wa.Wasm.Instr, t, []), t, append.nil(t))

def rev.rev(xs: List<&2, Wa.Wasm.Instr>, acc: List<&2, Wa.Wasm.Instr>, +zs: List<&2, Wa.Wasm.Instr>) ->
  {List.reverse.go(&2, Wa.Wasm.Instr, List.reverse.go(&2, Wa.Wasm.Instr, xs, acc), zs) ==
    List.reverse.go(&2, Wa.Wasm.Instr, acc, List.append(&2, Wa.Wasm.Instr, xs, zs)) : List<&2, Wa.Wasm.Instr>}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      rev.rev(t, Con{x, acc}, zs)

# xs reversed twice
def rev2(+xs: List<&2, Wa.Wasm.Instr>) ->
  {xs == List.reverse(&2, Wa.Wasm.Instr, List.reverse.go(&2, Wa.Wasm.Instr, xs, [])) : List<&2, Wa.Wasm.Instr>}:
  Equal.sym(List<&2, Wa.Wasm.Instr>, List.reverse(&2, Wa.Wasm.Instr, List.reverse.go(&2, Wa.Wasm.Instr, xs, [])), xs,
    Equal.trans(List<&2, Wa.Wasm.Instr>, List.reverse(&2, Wa.Wasm.Instr, List.reverse.go(&2, Wa.Wasm.Instr, xs, [])),
      List.append(&2, Wa.Wasm.Instr, xs, []), xs, rev.rev(xs, [], []), append.nil(xs)))

# Words
# -----

# t minus 0, with a carry in (no borrow), is t
def Word.sub0(n: Nat, t: Word(n)) -> {Word.adc(n, t, Word.zero(n), True{}, True{}) == t : Word(n)}:
  match n:
    case 0n:
      match t:
        case WNil{}:
          {==}
    case 1n+p:
      match t:
        case WCon{True{}, +r}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w}, Word.adc(p, r, Word.zero(p), True{}, True{}), r, Word.sub0(p, r))
        case WCon{False{}, +r}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.adc(p, r, Word.zero(p), True{}, True{}), r, Word.sub0(p, r))

# t + 1, minus 0 with a borrow, is t
def Word.sub_inc(n: Nat, t: Word(n)) -> {Word.adc(n, Word.inc(n, t), Word.zero(n), True{}, False{}) == t : Word(n)}:
  match n:
    case 0n:
      match t:
        case WNil{}:
          {==}
    case 1n+p:
      match t:
        case WCon{True{}, +r}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w}, Word.adc(p, Word.inc(p, r), Word.zero(p), True{}, False{}), r, Word.sub_inc(p, r))
        case WCon{False{}, +r}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.adc(p, r, Word.zero(p), True{}, True{}), r, Word.sub0(p, r))

# t + 1 - 1 is t
def Word.inc_dec(n: Nat, t: Word(1n+n)) -> {Word.sub(1n+n, Word.inc(1n+n, t), WCon{True{}, Word.zero(n)}) == t : Word(1n+n)}:
  match t:
    case WCon{True{}, +r}:
      Equal.cong(Word(n), Word(1n+n), w => WCon{True{}, w}, Word.adc(n, Word.inc(n, r), Word.zero(n), True{}, False{}), r, Word.sub_inc(n, r))
    case WCon{False{}, +r}:
      Equal.cong(Word(n), Word(1n+n), w => WCon{False{}, w}, Word.adc(n, r, Word.zero(n), True{}, True{}), r, Word.sub0(n, r))

def U32.inc_dec(a: U32) -> {a == U32.sub(U32.inc(a), 1) : U32}:
  match a:
    case U32{+x}:
      Equal.sym(U32, U32.sub(U32.inc(U32{x}), 1), U32{x},
        Equal.cong(Word(32n), U32, w => U32{w}, Word.sub(32n, Word.inc(32n, x), WCon{True{}, Word.zero(31n)}), x, Word.inc_dec(31n, x)))

def Cmp.fin_ff(c: Cmp) -> {Cmp.is_eq(Word.cmp.fin(False{}, False{}, c)) == Cmp.is_eq(c) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

# t + 1, when not 0, counts one more than t
def Word.inc_nat(n: Nat, t: Word(n), h: {False{} == Cmp.is_eq(Word.cmp(n, Word.inc(n, t), Word.zero(n))) : Bool}) ->
  {Word.to_nat(n, Word.inc(n, t)) == 1n+Word.to_nat(n, t) : Nat}:
  match n:
    case 0n:
      match t:
        case WNil{}:
          L.ft({Word.to_nat(0n, WNil{}) == 1n : Nat}, h)
    case 1n+(+p):
      match t:
        case WCon{False{}, r}:
          {==}
        case WCon{True{}, +r}:
          +c = Word.cmp(p, Word.inc(p, r), Word.zero(p))
          +ih = Word.inc_nat(p, r, Equal.trans(Bool, False{}, Cmp.is_eq(Word.cmp.fin(False{}, False{}, c)), Cmp.is_eq(c), h, Cmp.fin_ff(c)))
          %Equal.sym(Nat, Word.to_nat(p, Word.inc(p, r)), 1n+Word.to_nat(p, r), ih) : {Nat.double(_) == 2n+Nat.double(Word.to_nat(p, r)) : Nat}
          {==}

def U32.inc_nat(a: U32, h: {False{} == U32.is_zero(U32.inc(a)) : Bool}) -> {U32.to_nat(U32.inc(a)) == 1n+U32.to_nat(a) : Nat}:
  match a:
    case U32{x}:
      Word.inc_nat(32n, x, h)

# Wasm.has
# --------

def has.cons.if(b: Bool, +n: U32, +z: Word(8n), +r: List<&2, Word(8n)>,
  ih: {Wa.Wasm.has(r, U32.sub(n, 1)) == True{} : Bool} -> {Wa.Wasm.has(Con{z, r}, U32.sub(n, 1)) == True{} : Bool},
  h: {Wa.Wasm.has.if(b, u => Wa.Wasm.has(r, U32.sub(n, 1))) == True{} : Bool}) ->
  {Wa.Wasm.has.if(b, u => Wa.Wasm.has(Con{z, r}, U32.sub(n, 1))) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih(h)

# a byte more keeps n bytes
def has.cons(L: List<&2, Word(8n)>, +y: Word(8n), +n: U32, h: {Wa.Wasm.has(L, n) == True{} : Bool}) ->
  {Wa.Wasm.has(Con{y, L}, n) == True{} : Bool}:
  match L:
    case Nil{}:
      %Equal.sym(Bool, U32.is_zero(n), True{}, h) : {Wa.Wasm.has.if(_, u => Wa.Wasm.has([], U32.sub(n, 1))) == True{} : Bool}
      {==}
    case Con{+z, +r}:
      has.cons.if(U32.is_zero(n), n, z, r, e => has.cons(r, z, U32.sub(n, 1), e), h)

def has.append(zs: List<&2, Word(8n)>, +L: List<&2, Word(8n)>, +n: U32, h: {Wa.Wasm.has(L, n) == True{} : Bool}) ->
  {Wa.Wasm.has(List.append(&2, Word(8n), zs, L), n) == True{} : Bool}:
  match zs:
    case Nil{}:
      h
    case Con{+z, +t}:
      has.cons(List.append(&2, Word(8n), t, L), z, n, has.append(t, L, n, h))

def has.inc(+y: Word(8n), +zs: List<&2, Word(8n)>, +L: List<&2, Word(8n)>, +w: U32,
  hz: {False{} == U32.is_zero(U32.inc(w)) : Bool}, h: {Wa.Wasm.has(L, w) == True{} : Bool}) ->
  {Wa.Wasm.has(Con{y, List.append(&2, Word(8n), zs, L)}, U32.inc(w)) == True{} : Bool}:
  %hz : {Wa.Wasm.has.if(_, u => Wa.Wasm.has(List.append(&2, Word(8n), zs, L), U32.sub(U32.inc(w), 1))) == True{} : Bool}
  %U32.inc_dec(w) : {Wa.Wasm.has(List.append(&2, Word(8n), zs, L), _) == True{} : Bool}
  has.append(zs, L, w, h)

def has.leb(c: Bool, +b: U32, more: Unit -> List<&2, Word(8n)>, +L: List<&2, Word(8n)>, +w: U32,
  hz: {False{} == U32.is_zero(U32.inc(w)) : Bool}, h: {Wa.Wasm.has(L, w) == True{} : Bool}) ->
  {Wa.Wasm.has(List.append(&2, Word(8n), Cr.Wasm.encode.leb.if(c, b, more), L), U32.inc(w)) == True{} : Bool}:
  match c:
    case True{}:
      has.inc(Sd.Byte.from_u32(b), [], L, w, hz, h)
    case False{}:
      has.inc(Sd.Byte.from_u32(U32.or(b, 128)), more(Unit{}), L, w, hz, h)

def has.uleb(+v: U32, +L: List<&2, Word(8n)>, +w: U32,
  hz: {False{} == U32.is_zero(U32.inc(w)) : Bool}, h: {Wa.Wasm.has(L, w) == True{} : Bool}) ->
  {Wa.Wasm.has(List.append(&2, Word(8n), Cr.Wasm.encode.uleb(v), L), U32.inc(w)) == True{} : Bool}:
  has.leb(U32.is_zero(U32.shrn(v, 7n)), U32.and(v, 127), u => Cr.Wasm.encode.uleb.go(4n, U32.shrn(v, 7n)), L, w, hz, h)

# Heads
# -----

def uleb.back(+v: U32, +rest: List<&2, Word(8n)>) ->
  {Some{Wa.Wasm.Decoded{v, rest}} == Wa.Wasm.decode.uleb(32n, List.append(&2, Word(8n), Cr.Wasm.encode.uleb(v), rest)) : Maybe<&2, Wa.Wasm.Decoded<U32>>}:
  Equal.sym(Maybe<&2, Wa.Wasm.Decoded<U32>>, Wa.Wasm.decode.uleb(32n, List.append(&2, Word(8n), Cr.Wasm.encode.uleb(v), rest)),
    Some{Wa.Wasm.Decoded{v, rest}}, L.uleb.round(v, rest))

def sleb.back(+v: U32, +rest: List<&2, Word(8n)>) ->
  {Some{Wa.Wasm.Decoded{v, rest}} == Wa.Wasm.decode.sleb(32n, List.append(&2, Word(8n), Cr.Wasm.encode.sleb(v), rest)) : Maybe<&2, Wa.Wasm.Decoded<U32>>}:
  Equal.sym(Maybe<&2, Wa.Wasm.Decoded<U32>>, Wa.Wasm.decode.sleb(32n, List.append(&2, Word(8n), Cr.Wasm.encode.sleb(v), rest)),
    Some{Wa.Wasm.Decoded{v, rest}}, L.sleb.round(v, rest))

def tok.const(+n: U32, +E: List<&2, Word(8n)>) ->
  {Wa.Wasm.decode.const(List.append(&2, Word(8n), Cr.Wasm.encode.sleb(n), E)) ==
    Some{Wa.Wasm.Decoded{Wa.Wasm.Token.instr{Wa.Wasm.Instr.const{n}}, E}} : Maybe<&2, Wa.Wasm.Decoded<Wa.Wasm.Token>>}:
  %sleb.back(n, E) : {Wa.Wasm.decode.bind(U32, Wa.Wasm.Token, _, m => r => Wa.Wasm.decode.as(Wa.Wasm.Instr.const{m}, r)) ==
    Some{Wa.Wasm.Decoded{Wa.Wasm.Token.instr{Wa.Wasm.Instr.const{n}}, E}} : Maybe<&2, Wa.Wasm.Decoded<Wa.Wasm.Token>>}
  {==}

def tok.index(k: U32 -> Wa.Wasm.Instr, +i: U32, +E: List<&2, Word(8n)>) ->
  {Wa.Wasm.decode.index(k, List.append(&2, Word(8n), Cr.Wasm.encode.uleb(i), E)) ==
    Some{Wa.Wasm.Decoded{Wa.Wasm.Token.instr{k(i)}, E}} : Maybe<&2, Wa.Wasm.Decoded<Wa.Wasm.Token>>}:
  %uleb.back(i, E) : {Wa.Wasm.decode.bind(U32, Wa.Wasm.Token, _, j => r => Wa.Wasm.decode.as(k(j), r)) ==
    Some{Wa.Wasm.Decoded{Wa.Wasm.Token.instr{k(i)}, E}} : Maybe<&2, Wa.Wasm.Decoded<Wa.Wasm.Token>>}
  {==}

def tok.memarg(k: U32 -> Wa.Wasm.Instr, +o: U32, +E: List<&2, Word(8n)>) ->
  {Wa.Wasm.decode.memarg.if(True{}, k, List.append(&2, Word(8n), Cr.Wasm.encode.uleb(o), E)) ==
    Some{Wa.Wasm.Decoded{Wa.Wasm.Token.instr{k(o)}, E}} : Maybe<&2, Wa.Wasm.Decoded<Wa.Wasm.Token>>}:
  %uleb.back(o, E) : {Wa.Wasm.decode.bind(U32, Wa.Wasm.Token, _, j => r => Wa.Wasm.decode.as(k(j), r)) ==
    Some{Wa.Wasm.Decoded{Wa.Wasm.Token.instr{k(o)}, E}} : Maybe<&2, Wa.Wasm.Decoded<Wa.Wasm.Token>>}
  {==}

def tok.op(o: Wa.Wasm.Op, +E: List<&2, Word(8n)>) ->
  {Wa.Wasm.decode.token(Word.to_nat(8n, Sd.Byte.from_u32(Cr.Wasm.encode.opcode(o))), E) ==
    Some{Wa.Wasm.Decoded{Wa.Wasm.Token.instr{Wa.Wasm.Instr.op{o}}, E}} : Maybe<&2, Wa.Wasm.Decoded<Wa.Wasm.Token>>}:
  match o:
    case Wa.Wasm.Op.add{}:
      {==}
    case Wa.Wasm.Op.sub{}:
      {==}
    case Wa.Wasm.Op.and{}:
      {==}
    case Wa.Wasm.Op.or{}:
      {==}
    case Wa.Wasm.Op.shl{}:
      {==}
    case Wa.Wasm.Op.shr_u{}:
      {==}
    case Wa.Wasm.Op.eq{}:
      {==}
    case Wa.Wasm.Op.ne{}:
      {==}
    case Wa.Wasm.Op.lt_u{}:
      {==}
    case Wa.Wasm.Op.gt_u{}:
      {==}
    case Wa.Wasm.Op.le_u{}:
      {==}
    case Wa.Wasm.Op.ge_u{}:
      {==}

# Block types
# -----------

# a comparison LT is not EQ
def lt.ne(c: Cmp, h: {Cmp.is_lt(c) == True{} : Bool}) -> {Cmp.is_eq(c) == False{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      L.ft({True{} == False{} : Bool}, h)
    case GT{}:
      L.ft({False{} == False{} : Bool}, h)

# a number below 64 is not 127
def lt64.ne127(c: Cmp, d: Cmp, +A: Nat, r1: N.Rel(c, A, 64n), r2: N.Rel(d, A, 127n), h: {Cmp.is_lt(c) == True{} : Bool}) ->
  {Cmp.is_eq(d) == False{} : Bool}:
  match c:
    case LT{}:
      match d:
        case LT{}:
          {==}
        case EQ{}:
          Empty.absurd({True{} == False{} : Bool}, N.le_rw_l(1n+A, 128n, 64n, Equal.cong(Nat, Nat, z => 1n+z, A, 127n, r2), r1))
        case GT{}:
          {==}
    case EQ{}:
      L.ft({Cmp.is_eq(d) == False{} : Bool}, h)
    case GT{}:
      L.ft({Cmp.is_eq(d) == False{} : Bool}, h)

# a type index whose first byte goes on (at least 2^7): that byte is
# neither 0x40 nor 0x7F
def bt.index.more(+x: U32, +B: List<&2, Word(8n)>,
  hs: {Wa.Wasm.decode.s33(Con{Sd.Byte.from_u32(U32.or(U32.and(x, 127), 128)), List.append(&2, Word(8n), Cr.Wasm.encode.s33.go(4n, U32.shrn(x, 7n)), B)}) == Some{Wa.Wasm.Decoded{x, B}} : Maybe<&2, Wa.Wasm.Decoded<U32>>}) ->
  {Wa.Wasm.decode.blocktype(Con{Sd.Byte.from_u32(U32.or(U32.and(x, 127), 128)), List.append(&2, Word(8n), Cr.Wasm.encode.s33.go(4n, U32.shrn(x, 7n)), B)}) == Some{Wa.Wasm.Decoded{Wa.Wasm.Blocktype.index{x}, B}} : Maybe<&2, Wa.Wasm.Decoded<Wa.Wasm.Blocktype>>}:
  +R = List.append(&2, Word(8n), Cr.Wasm.encode.s33.go(4n, U32.shrn(x, 7n)), B)
  %Equal.sym(U32, Sd.Byte.to_u32(Sd.Byte.from_u32(U32.or(U32.and(x, 127), 128))), U32.or(U32.and(x, 127), 128), L.Byte.or128(x)) :
    {Wa.Wasm.decode.blocktype.if(U32.is_eq(_, 64), U32.is_eq(_, 127), R, Con{Sd.Byte.from_u32(U32.or(U32.and(x, 127), 128)), R}) == Some{Wa.Wasm.Decoded{Wa.Wasm.Blocktype.index{x}, B}} : Maybe<&2, Wa.Wasm.Decoded<Wa.Wasm.Blocktype>>}
  %Equal.sym(Bool, U32.is_eq(U32.or(U32.and(x, 127), 128), 64), False{}, L.U32.or128_ne64(x)) :
    {Wa.Wasm.decode.blocktype.if(_, U32.is_eq(U32.or(U32.and(x, 127), 128), 127), R, Con{Sd.Byte.from_u32(U32.or(U32.and(x, 127), 128)), R}) == Some{Wa.Wasm.Decoded{Wa.Wasm.Blocktype.index{x}, B}} : Maybe<&2, Wa.Wasm.Decoded<Wa.Wasm.Blocktype>>}
  %Equal.sym(Bool, U32.is_eq(U32.or(U32.and(x, 127), 128), 127), False{}, L.U32.or128_ne127(x)) :
    {Wa.Wasm.decode.blocktype.if(False{}, _, R, Con{Sd.Byte.from_u32(U32.or(U32.and(x, 127), 128)), R}) == Some{Wa.Wasm.Decoded{Wa.Wasm.Blocktype.index{x}, B}} : Maybe<&2, Wa.Wasm.Decoded<Wa.Wasm.Blocktype>>}
  %Equal.sym(Maybe<&2, Wa.Wasm.Decoded<U32>>, Wa.Wasm.decode.s33(Con{Sd.Byte.from_u32(U32.or(U32.and(x, 127), 128)), R}), Some{Wa.Wasm.Decoded{x, B}}, hs) :
    {Wa.Wasm.decode.bind(U32, Wa.Wasm.Blocktype, _, y => r => Some{Wa.Wasm.Decoded{Wa.Wasm.Blocktype.index{y}, r}}) == Some{Wa.Wasm.Decoded{Wa.Wasm.Blocktype.index{x}, B}} : Maybe<&2, Wa.Wasm.Decoded<Wa.Wasm.Blocktype>>}
  {==}

# the bytes of a type index read back as it, by its first byte: the last
# (below 2^6), or one that goes on
def bt.index(z1: Bool, z2: Bool, +x: U32, +B: List<&2, Word(8n)>, +ez2: {U32.is_lt(U32.and(x, 127), 64) == z2 : Bool},
  hs: {Wa.Wasm.decode.s33(List.append(&2, Word(8n), Cr.Wasm.encode.leb.if(Bool.and(z1, z2), U32.and(x, 127), u => Cr.Wasm.encode.s33.go(4n, U32.shrn(x, 7n))), B)) == Some{Wa.Wasm.Decoded{x, B}} : Maybe<&2, Wa.Wasm.Decoded<U32>>}) ->
  {Wa.Wasm.decode.blocktype(List.append(&2, Word(8n), Cr.Wasm.encode.leb.if(Bool.and(z1, z2), U32.and(x, 127), u => Cr.Wasm.encode.s33.go(4n, U32.shrn(x, 7n))), B)) == Some{Wa.Wasm.Decoded{Wa.Wasm.Blocktype.index{x}, B}} : Maybe<&2, Wa.Wasm.Decoded<Wa.Wasm.Blocktype>>}:
  match z1 z2:
    case True{} True{}:
      +a = U32.and(x, 127)
      %Equal.sym(U32, Sd.Byte.to_u32(Sd.Byte.from_u32(U32.and(x, 127))), U32.and(x, 127), L.Byte.low7(x)) :
        {Wa.Wasm.decode.blocktype.if(U32.is_eq(_, 64), U32.is_eq(_, 127), B, Con{Sd.Byte.from_u32(U32.and(x, 127)), B}) == Some{Wa.Wasm.Decoded{Wa.Wasm.Blocktype.index{x}, B}} : Maybe<&2, Wa.Wasm.Decoded<Wa.Wasm.Blocktype>>}
      %Equal.sym(Bool, U32.is_eq(U32.and(x, 127), 64), False{}, lt.ne(U32.cmp(U32.and(x, 127), 64), ez2)) :
        {Wa.Wasm.decode.blocktype.if(_, U32.is_eq(U32.and(x, 127), 127), B, Con{Sd.Byte.from_u32(U32.and(x, 127)), B}) == Some{Wa.Wasm.Decoded{Wa.Wasm.Blocktype.index{x}, B}} : Maybe<&2, Wa.Wasm.Decoded<Wa.Wasm.Blocktype>>}
      %Equal.sym(Bool, U32.is_eq(U32.and(x, 127), 127), False{}, lt64.ne127(U32.cmp(U32.and(x, 127), 64), U32.cmp(U32.and(x, 127), 127), U32.to_nat(U32.and(x, 127)),
        N.U32.rel(U32.and(x, 127), 64), N.U32.rel(U32.and(x, 127), 127), ez2)) :
        {Wa.Wasm.decode.blocktype.if(False{}, _, B, Con{Sd.Byte.from_u32(U32.and(x, 127)), B}) == Some{Wa.Wasm.Decoded{Wa.Wasm.Blocktype.index{x}, B}} : Maybe<&2, Wa.Wasm.Decoded<Wa.Wasm.Blocktype>>}
      %Equal.sym(Maybe<&2, Wa.Wasm.Decoded<U32>>, Wa.Wasm.decode.s33(Con{Sd.Byte.from_u32(U32.and(x, 127)), B}), Some{Wa.Wasm.Decoded{x, B}}, hs) :
        {Wa.Wasm.decode.bind(U32, Wa.Wasm.Blocktype, _, y => r => Some{Wa.Wasm.Decoded{Wa.Wasm.Blocktype.index{y}, r}}) == Some{Wa.Wasm.Decoded{Wa.Wasm.Blocktype.index{x}, B}} : Maybe<&2, Wa.Wasm.Decoded<Wa.Wasm.Blocktype>>}
      {==}
    case True{} False{}:
      bt.index.more(x, B, hs)
    case False{} _:
      bt.index.more(x, B, hs)

# a block type, encoded then decoded, is itself
def bt.round(bt: Wa.Wasm.Blocktype, +B: List<&2, Word(8n)>) ->
  {Wa.Wasm.decode.blocktype(List.append(&2, Word(8n), Cr.Wasm.encode.blocktype(bt), B)) == Some{Wa.Wasm.Decoded{bt, B}} : Maybe<&2, Wa.Wasm.Decoded<Wa.Wasm.Blocktype>>}:
  match bt:
    case Wa.Wasm.Blocktype.empty{}:
      {==}
    case Wa.Wasm.Blocktype.i32{}:
      {==}
    case Wa.Wasm.Blocktype.index{+x}:
      bt.index(U32.is_zero(U32.shrn(x, 7n)), U32.is_lt(U32.and(x, 127), 64), x, B, {==}, L.s33.round(x, B))

# Fuel
# ----

# the fuel left after the instructions xs, from k, beside the bytes after them
def left(xs: List<&2, Wa.Wasm.Instr>, k: Nat) -> Nat:
  match xs:
    case Nil{}:
      k
    case Con{x, rest}:
      match x:
        case Wa.Wasm.Instr.const{n}:
          left(rest, Nat.add(List.length(&2, Word(8n), Cr.Wasm.encode.sleb(n)), k))
        case Wa.Wasm.Instr.local_get{i}:
          left(rest, Nat.add(List.length(&2, Word(8n), Cr.Wasm.encode.uleb(i)), k))
        case Wa.Wasm.Instr.local_set{i}:
          left(rest, Nat.add(List.length(&2, Word(8n), Cr.Wasm.encode.uleb(i)), k))
        case Wa.Wasm.Instr.local_tee{i}:
          left(rest, Nat.add(List.length(&2, Word(8n), Cr.Wasm.encode.uleb(i)), k))
        case Wa.Wasm.Instr.op{o}:
          left(rest, k)
        case Wa.Wasm.Instr.eqz{}:
          left(rest, k)
        case Wa.Wasm.Instr.load{o}:
          left(rest, Nat.add(1n+List.length(&2, Word(8n), Cr.Wasm.encode.uleb(o)), k))
        case Wa.Wasm.Instr.load8_u{o}:
          left(rest, Nat.add(1n+List.length(&2, Word(8n), Cr.Wasm.encode.uleb(o)), k))
        case Wa.Wasm.Instr.store{o}:
          left(rest, Nat.add(1n+List.length(&2, Word(8n), Cr.Wasm.encode.uleb(o)), k))
        case Wa.Wasm.Instr.store8{o}:
          left(rest, Nat.add(1n+List.length(&2, Word(8n), Cr.Wasm.encode.uleb(o)), k))
        case Wa.Wasm.Instr.memory_size{}:
          left(rest, 1n+k)
        case Wa.Wasm.Instr.memory_grow{}:
          left(rest, 1n+k)
        case Wa.Wasm.Instr.block{bt, body}:
          left(rest, left(body, Nat.add(List.length(&2, Word(8n), Cr.Wasm.encode.blocktype(bt)), k)))
        case Wa.Wasm.Instr.loop{bt, body}:
          left(rest, left(body, Nat.add(List.length(&2, Word(8n), Cr.Wasm.encode.blocktype(bt)), k)))
        case Wa.Wasm.Instr.br{l}:
          left(rest, Nat.add(List.length(&2, Word(8n), Cr.Wasm.encode.uleb(l)), k))
        case Wa.Wasm.Instr.br_if{l}:
          left(rest, Nat.add(List.length(&2, Word(8n), Cr.Wasm.encode.uleb(l)), k))

# The decoder's steps
# -------------------

# the decoding after the instructions rest, from the fuel k, with x read
def after(+rest: List<&2, Wa.Wasm.Instr>, +more: List<&2, Word(8n)>, k: Nat, x: Wa.Wasm.Instr,
  ys: List<&2, Wa.Wasm.Instr>, st: List<&2, Wa.Wasm.Open>) -> Maybe<&2, Wa.Wasm.Decoded<List<&2, Wa.Wasm.Instr>>>:
  Wa.Wasm.decode.instrs.go(Nat.add(List.length(&2, Word(8n), more), left(rest, k)), more,
    List.reverse.go(&2, Wa.Wasm.Instr, rest, Con{x, ys}), st)

# one head that is an instruction
def step(+op: Word(8n), +bs: List<&2, Word(8n)>, +E: List<&2, Word(8n)>, +x: Wa.Wasm.Instr, +k: Nat, +k2: Nat,
  +ys: List<&2, Wa.Wasm.Instr>, +st: List<&2, Wa.Wasm.Open>, +g: Maybe<&2, Wa.Wasm.Decoded<List<&2, Wa.Wasm.Instr>>>,
  tok: {Wa.Wasm.decode.token(Word.to_nat(8n, op), bs) == Some{Wa.Wasm.Decoded{Wa.Wasm.Token.instr{x}, E}} : Maybe<&2, Wa.Wasm.Decoded<Wa.Wasm.Token>>},
  fe: {Nat.add(List.length(&2, Word(8n), bs), k) == Nat.add(List.length(&2, Word(8n), E), k2) : Nat},
  ih: {Wa.Wasm.decode.instrs.go(Nat.add(List.length(&2, Word(8n), E), k2), E, Con{x, ys}, st) == g : Maybe<&2, Wa.Wasm.Decoded<List<&2, Wa.Wasm.Instr>>>}) ->
  {Wa.Wasm.decode.instrs.go(1n+Nat.add(List.length(&2, Word(8n), bs), k), Con{op, bs}, ys, st) == g : Maybe<&2, Wa.Wasm.Decoded<List<&2, Wa.Wasm.Instr>>>}:
  %Equal.sym(Maybe<&2, Wa.Wasm.Decoded<Wa.Wasm.Token>>, Wa.Wasm.decode.token(Word.to_nat(8n, op), bs),
    Some{Wa.Wasm.Decoded{Wa.Wasm.Token.instr{x}, E}}, tok) :
    {Wa.Wasm.decode.instrs.then(_, ys, st, r => zs => st2 => Wa.Wasm.decode.instrs.go(Nat.add(List.length(&2, Word(8n), bs), k), r, zs, st2)) == g : Maybe<&2, Wa.Wasm.Decoded<List<&2, Wa.Wasm.Instr>>>}
  %Equal.sym(Nat, Nat.add(List.length(&2, Word(8n), bs), k), Nat.add(List.length(&2, Word(8n), E), k2), fe) :
    {Wa.Wasm.decode.instrs.go(_, E, Con{x, ys}, st) == g : Maybe<&2, Wa.Wasm.Decoded<List<&2, Wa.Wasm.Instr>>>}
  ih

# an instruction of opcode op and immediate I
def simple(+op: U32, +I: List<&2, Word(8n)>, +rest: List<&2, Wa.Wasm.Instr>, +more: List<&2, Word(8n)>, +x: Wa.Wasm.Instr, +k: Nat,
  +ys: List<&2, Wa.Wasm.Instr>, +st: List<&2, Wa.Wasm.Open>,
  tok: {Wa.Wasm.decode.token(Word.to_nat(8n, Sd.Byte.from_u32(op)), List.append(&2, Word(8n), I, Cr.Wasm.encode.instrs(rest, more))) ==
    Some{Wa.Wasm.Decoded{Wa.Wasm.Token.instr{x}, Cr.Wasm.encode.instrs(rest, more)}} : Maybe<&2, Wa.Wasm.Decoded<Wa.Wasm.Token>>},
  ih: {Wa.Wasm.decode.instrs.go(Nat.add(List.length(&2, Word(8n), Cr.Wasm.encode.instrs(rest, more)), Nat.add(List.length(&2, Word(8n), I), k)),
    Cr.Wasm.encode.instrs(rest, more), Con{x, ys}, st) == after(rest, more, Nat.add(List.length(&2, Word(8n), I), k), x, ys, st) : Maybe<&2, Wa.Wasm.Decoded<List<&2, Wa.Wasm.Instr>>>}) ->
  {Wa.Wasm.decode.instrs.go(1n+Nat.add(List.length(&2, Word(8n), List.append(&2, Word(8n), I, Cr.Wasm.encode.instrs(rest, more))), k),
    Con{Sd.Byte.from_u32(op), List.append(&2, Word(8n), I, Cr.Wasm.encode.instrs(rest, more))}, ys, st) ==
    after(rest, more, Nat.add(List.length(&2, Word(8n), I), k), x, ys, st) : Maybe<&2, Wa.Wasm.Decoded<List<&2, Wa.Wasm.Instr>>>}:
  +E = Cr.Wasm.encode.instrs(rest, more)
  step(Sd.Byte.from_u32(op), List.append(&2, Word(8n), I, E), E, x, k, Nat.add(List.length(&2, Word(8n), I), k), ys, st,
    after(rest, more, Nat.add(List.length(&2, Word(8n), I), k), x, ys, st), tok, add.len(I, E, k), ih)

# The round trip
# --------------

# the bytes of xs, then more, read with ys and the open blocks st so far:
# the decoder reads the heads of xs, one fuel each, and goes on at more
def run(xs: List<&2, Wa.Wasm.Instr>, +more: List<&2, Word(8n)>, +k: Nat, +ys: List<&2, Wa.Wasm.Instr>,
  +st: List<&2, Wa.Wasm.Open>) ->
  {Wa.Wasm.decode.instrs.go(Nat.add(List.length(&2, Word(8n), Cr.Wasm.encode.instrs(xs, more)), k), Cr.Wasm.encode.instrs(xs, more), ys, st) ==
    Wa.Wasm.decode.instrs.go(Nat.add(List.length(&2, Word(8n), more), left(xs, k)), more, List.reverse.go(&2, Wa.Wasm.Instr, xs, ys), st) : Maybe<&2, Wa.Wasm.Decoded<List<&2, Wa.Wasm.Instr>>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +rest}:
      match x:
        case Wa.Wasm.Instr.const{+n}:
          simple(65, Cr.Wasm.encode.sleb(n), rest, more, Wa.Wasm.Instr.const{n}, k, ys, st, tok.const(n, Cr.Wasm.encode.instrs(rest, more)),
            run(rest, more, Nat.add(List.length(&2, Word(8n), Cr.Wasm.encode.sleb(n)), k), Con{Wa.Wasm.Instr.const{n}, ys}, st))
        case Wa.Wasm.Instr.local_get{+i}:
          simple(32, Cr.Wasm.encode.uleb(i), rest, more, Wa.Wasm.Instr.local_get{i}, k, ys, st, tok.index(j => Wa.Wasm.Instr.local_get{j}, i, Cr.Wasm.encode.instrs(rest, more)),
            run(rest, more, Nat.add(List.length(&2, Word(8n), Cr.Wasm.encode.uleb(i)), k), Con{Wa.Wasm.Instr.local_get{i}, ys}, st))
        case Wa.Wasm.Instr.local_set{+i}:
          simple(33, Cr.Wasm.encode.uleb(i), rest, more, Wa.Wasm.Instr.local_set{i}, k, ys, st, tok.index(j => Wa.Wasm.Instr.local_set{j}, i, Cr.Wasm.encode.instrs(rest, more)),
            run(rest, more, Nat.add(List.length(&2, Word(8n), Cr.Wasm.encode.uleb(i)), k), Con{Wa.Wasm.Instr.local_set{i}, ys}, st))
        case Wa.Wasm.Instr.local_tee{+i}:
          simple(34, Cr.Wasm.encode.uleb(i), rest, more, Wa.Wasm.Instr.local_tee{i}, k, ys, st, tok.index(j => Wa.Wasm.Instr.local_tee{j}, i, Cr.Wasm.encode.instrs(rest, more)),
            run(rest, more, Nat.add(List.length(&2, Word(8n), Cr.Wasm.encode.uleb(i)), k), Con{Wa.Wasm.Instr.local_tee{i}, ys}, st))
        case Wa.Wasm.Instr.op{+o}:
          simple(Cr.Wasm.encode.opcode(o), [], rest, more, Wa.Wasm.Instr.op{o}, k, ys, st,
            tok.op(o, Cr.Wasm.encode.instrs(rest, more)), run(rest, more, k, Con{Wa.Wasm.Instr.op{o}, ys}, st))
        case Wa.Wasm.Instr.eqz{}:
          simple(69, [], rest, more, Wa.Wasm.Instr.eqz{}, k, ys, st, {==},
            run(rest, more, Nat.add(List.length(&2, Word(8n), []), k), Con{Wa.Wasm.Instr.eqz{}, ys}, st))
        case Wa.Wasm.Instr.load{+o}:
          simple(40, Con{Sd.Byte.from_u32(2), Cr.Wasm.encode.uleb(o)}, rest, more, Wa.Wasm.Instr.load{o}, k, ys, st,
            tok.memarg(j => Wa.Wasm.Instr.load{j}, o, Cr.Wasm.encode.instrs(rest, more)),
            run(rest, more, Nat.add(List.length(&2, Word(8n), Con{Sd.Byte.from_u32(2), Cr.Wasm.encode.uleb(o)}), k), Con{Wa.Wasm.Instr.load{o}, ys}, st))
        case Wa.Wasm.Instr.load8_u{+o}:
          simple(45, Con{Sd.Byte.from_u32(0), Cr.Wasm.encode.uleb(o)}, rest, more, Wa.Wasm.Instr.load8_u{o}, k, ys, st,
            tok.memarg(j => Wa.Wasm.Instr.load8_u{j}, o, Cr.Wasm.encode.instrs(rest, more)),
            run(rest, more, Nat.add(List.length(&2, Word(8n), Con{Sd.Byte.from_u32(0), Cr.Wasm.encode.uleb(o)}), k), Con{Wa.Wasm.Instr.load8_u{o}, ys}, st))
        case Wa.Wasm.Instr.store{+o}:
          simple(54, Con{Sd.Byte.from_u32(2), Cr.Wasm.encode.uleb(o)}, rest, more, Wa.Wasm.Instr.store{o}, k, ys, st,
            tok.memarg(j => Wa.Wasm.Instr.store{j}, o, Cr.Wasm.encode.instrs(rest, more)),
            run(rest, more, Nat.add(List.length(&2, Word(8n), Con{Sd.Byte.from_u32(2), Cr.Wasm.encode.uleb(o)}), k), Con{Wa.Wasm.Instr.store{o}, ys}, st))
        case Wa.Wasm.Instr.store8{+o}:
          simple(58, Con{Sd.Byte.from_u32(0), Cr.Wasm.encode.uleb(o)}, rest, more, Wa.Wasm.Instr.store8{o}, k, ys, st,
            tok.memarg(j => Wa.Wasm.Instr.store8{j}, o, Cr.Wasm.encode.instrs(rest, more)),
            run(rest, more, Nat.add(List.length(&2, Word(8n), Con{Sd.Byte.from_u32(0), Cr.Wasm.encode.uleb(o)}), k), Con{Wa.Wasm.Instr.store8{o}, ys}, st))
        case Wa.Wasm.Instr.memory_size{}:
          simple(63, [Sd.Byte.from_u32(0)], rest, more, Wa.Wasm.Instr.memory_size{}, k, ys, st, {==},
            run(rest, more, Nat.add(List.length(&2, Word(8n), [Sd.Byte.from_u32(0)]), k), Con{Wa.Wasm.Instr.memory_size{}, ys}, st))
        case Wa.Wasm.Instr.memory_grow{}:
          simple(64, [Sd.Byte.from_u32(0)], rest, more, Wa.Wasm.Instr.memory_grow{}, k, ys, st, {==},
            run(rest, more, Nat.add(List.length(&2, Word(8n), [Sd.Byte.from_u32(0)]), k), Con{Wa.Wasm.Instr.memory_grow{}, ys}, st))
        case Wa.Wasm.Instr.block{+bt, +body}:
          +R = Cr.Wasm.encode.instrs(rest, more)
          +B = Cr.Wasm.encode.instrs(body, Con{Sd.Byte.from_u32(11), R})
          +T = Cr.Wasm.encode.blocktype(bt)
          +k0 = Nat.add(List.length(&2, Word(8n), T), k)
          +k1 = left(body, k0)
          +os = {Con{Wa.Wasm.Open{False{}, bt, ys}, st} : List<&2, Wa.Wasm.Open>}
          +g = after(rest, more, k1, Wa.Wasm.Instr.block{bt, body}, ys, st)
          %Equal.sym(Maybe<&2, Wa.Wasm.Decoded<Wa.Wasm.Blocktype>>, Wa.Wasm.decode.blocktype(List.append(&2, Word(8n), T, B)), Some{Wa.Wasm.Decoded{bt, B}}, bt.round(bt, B)) :
            {Wa.Wasm.decode.instrs.then(Wa.Wasm.decode.bind(Wa.Wasm.Blocktype, Wa.Wasm.Token, _, b => r => Some{Wa.Wasm.Decoded{Wa.Wasm.Token.start{False{}, b}, r}}), ys, st,
              r => zs => st2 => Wa.Wasm.decode.instrs.go(Nat.add(List.length(&2, Word(8n), List.append(&2, Word(8n), T, B)), k), r, zs, st2)) == g : Maybe<&2, Wa.Wasm.Decoded<List<&2, Wa.Wasm.Instr>>>}
          %Equal.sym(Nat, Nat.add(List.length(&2, Word(8n), List.append(&2, Word(8n), T, B)), k), Nat.add(List.length(&2, Word(8n), B), k0), add.len(T, B, k)) :
            {Wa.Wasm.decode.instrs.go(_, B, [], os) == g : Maybe<&2, Wa.Wasm.Decoded<List<&2, Wa.Wasm.Instr>>>}
          %Equal.sym(Maybe<&2, Wa.Wasm.Decoded<List<&2, Wa.Wasm.Instr>>>, Wa.Wasm.decode.instrs.go(Nat.add(List.length(&2, Word(8n), B), k0), B, [], os),
            Wa.Wasm.decode.instrs.go(Nat.add(List.length(&2, Word(8n), Con{Sd.Byte.from_u32(11), R}), k1), Con{Sd.Byte.from_u32(11), R}, List.reverse.go(&2, Wa.Wasm.Instr, body, []), os),
            run(body, Con{Sd.Byte.from_u32(11), R}, k0, [], os)) : {_ == g : Maybe<&2, Wa.Wasm.Decoded<List<&2, Wa.Wasm.Instr>>>}
          %rev2(body) : {Wa.Wasm.decode.instrs.go(Nat.add(List.length(&2, Word(8n), R), k1), R, Con{Wa.Wasm.Instr.block{bt, _}, ys}, st) == g : Maybe<&2, Wa.Wasm.Decoded<List<&2, Wa.Wasm.Instr>>>}
          run(rest, more, k1, Con{Wa.Wasm.Instr.block{bt, body}, ys}, st)
        case Wa.Wasm.Instr.loop{+bt, +body}:
          +R = Cr.Wasm.encode.instrs(rest, more)
          +B = Cr.Wasm.encode.instrs(body, Con{Sd.Byte.from_u32(11), R})
          +T = Cr.Wasm.encode.blocktype(bt)
          +k0 = Nat.add(List.length(&2, Word(8n), T), k)
          +k1 = left(body, k0)
          +os = {Con{Wa.Wasm.Open{True{}, bt, ys}, st} : List<&2, Wa.Wasm.Open>}
          +g = after(rest, more, k1, Wa.Wasm.Instr.loop{bt, body}, ys, st)
          %Equal.sym(Maybe<&2, Wa.Wasm.Decoded<Wa.Wasm.Blocktype>>, Wa.Wasm.decode.blocktype(List.append(&2, Word(8n), T, B)), Some{Wa.Wasm.Decoded{bt, B}}, bt.round(bt, B)) :
            {Wa.Wasm.decode.instrs.then(Wa.Wasm.decode.bind(Wa.Wasm.Blocktype, Wa.Wasm.Token, _, b => r => Some{Wa.Wasm.Decoded{Wa.Wasm.Token.start{True{}, b}, r}}), ys, st,
              r => zs => st2 => Wa.Wasm.decode.instrs.go(Nat.add(List.length(&2, Word(8n), List.append(&2, Word(8n), T, B)), k), r, zs, st2)) == g : Maybe<&2, Wa.Wasm.Decoded<List<&2, Wa.Wasm.Instr>>>}
          %Equal.sym(Nat, Nat.add(List.length(&2, Word(8n), List.append(&2, Word(8n), T, B)), k), Nat.add(List.length(&2, Word(8n), B), k0), add.len(T, B, k)) :
            {Wa.Wasm.decode.instrs.go(_, B, [], os) == g : Maybe<&2, Wa.Wasm.Decoded<List<&2, Wa.Wasm.Instr>>>}
          %Equal.sym(Maybe<&2, Wa.Wasm.Decoded<List<&2, Wa.Wasm.Instr>>>, Wa.Wasm.decode.instrs.go(Nat.add(List.length(&2, Word(8n), B), k0), B, [], os),
            Wa.Wasm.decode.instrs.go(Nat.add(List.length(&2, Word(8n), Con{Sd.Byte.from_u32(11), R}), k1), Con{Sd.Byte.from_u32(11), R}, List.reverse.go(&2, Wa.Wasm.Instr, body, []), os),
            run(body, Con{Sd.Byte.from_u32(11), R}, k0, [], os)) : {_ == g : Maybe<&2, Wa.Wasm.Decoded<List<&2, Wa.Wasm.Instr>>>}
          %rev2(body) : {Wa.Wasm.decode.instrs.go(Nat.add(List.length(&2, Word(8n), R), k1), R, Con{Wa.Wasm.Instr.loop{bt, _}, ys}, st) == g : Maybe<&2, Wa.Wasm.Decoded<List<&2, Wa.Wasm.Instr>>>}
          run(rest, more, k1, Con{Wa.Wasm.Instr.loop{bt, body}, ys}, st)
        case Wa.Wasm.Instr.br{+l}:
          simple(12, Cr.Wasm.encode.uleb(l), rest, more, Wa.Wasm.Instr.br{l}, k, ys, st, tok.index(j => Wa.Wasm.Instr.br{j}, l, Cr.Wasm.encode.instrs(rest, more)),
            run(rest, more, Nat.add(List.length(&2, Word(8n), Cr.Wasm.encode.uleb(l)), k), Con{Wa.Wasm.Instr.br{l}, ys}, st))
        case Wa.Wasm.Instr.br_if{+l}:
          simple(13, Cr.Wasm.encode.uleb(l), rest, more, Wa.Wasm.Instr.br_if{l}, k, ys, st, tok.index(j => Wa.Wasm.Instr.br_if{j}, l, Cr.Wasm.encode.instrs(rest, more)),
            run(rest, more, Nat.add(List.length(&2, Word(8n), Cr.Wasm.encode.uleb(l)), k), Con{Wa.Wasm.Instr.br_if{l}, ys}, st))

# a function body's instructions, encoded then decoded as
# Wasm.decode.func.body does, are themselves
def instrs.round(+xs: List<&2, Wa.Wasm.Instr>) ->
  {Wa.Wasm.decode.instrs(1n+List.length(&2, Word(8n), Cr.Wasm.encode.instrs(xs, [Sd.Byte.from_u32(11)])), Cr.Wasm.encode.instrs(xs, [Sd.Byte.from_u32(11)])) ==
    Some{Wa.Wasm.Decoded{xs, []}} : Maybe<&2, Wa.Wasm.Decoded<List<&2, Wa.Wasm.Instr>>>}:
  +bs = Cr.Wasm.encode.instrs(xs, [Sd.Byte.from_u32(11)])
  %add.one(List.length(&2, Word(8n), bs)) :
    {Wa.Wasm.decode.instrs.go(_, bs, [], []) == Some{Wa.Wasm.Decoded{xs, []}} : Maybe<&2, Wa.Wasm.Decoded<List<&2, Wa.Wasm.Instr>>>}
  %Equal.sym(Maybe<&2, Wa.Wasm.Decoded<List<&2, Wa.Wasm.Instr>>>,
    Wa.Wasm.decode.instrs.go(Nat.add(List.length(&2, Word(8n), bs), 1n), bs, [], []),
    Wa.Wasm.decode.instrs.go(Nat.add(List.length(&2, Word(8n), [Sd.Byte.from_u32(11)]), left(xs, 1n)), [Sd.Byte.from_u32(11)], List.reverse.go(&2, Wa.Wasm.Instr, xs, []), []),
    run(xs, [Sd.Byte.from_u32(11)], 1n, [], [])) :
    {_ == Some{Wa.Wasm.Decoded{xs, []}} : Maybe<&2, Wa.Wasm.Decoded<List<&2, Wa.Wasm.Instr>>>}
  %rev2(xs) : {Some{Wa.Wasm.Decoded{_, []}} == Some{Wa.Wasm.Decoded{xs, []}} : Maybe<&2, Wa.Wasm.Decoded<List<&2, Wa.Wasm.Instr>>>}
  {==}
