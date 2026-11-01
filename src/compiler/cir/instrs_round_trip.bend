# compiler: the round trip of a function body's instructions
# ===========================================================
#
# Wasm.decode.instrs, with the fuel that Wasm.decode.func.body gives it,
# reads back the instructions that Wasm.encode.instrs writes, then the end
# 0x0B (instrs.round, at the end), for every list of instructions whose
# br_tables each have a labels count that fits a U32 (fits): a br_table of
# 2^32 labels or more wraps Wasm.encode.len, and the decoder then fails.
#
# The induction (run) goes on the instruction tree: the bytes of xs, then
# more, with fuel |bytes| + k, read as the heads of xs (each one fuel; a
# block's body by the hypothesis on it), then go on at more with fuel
# |more| + left(xs, k), xs reversed onto those so far.

import Base
import ../../shared/shared.bend as Sd
import ../../wasm/impl.bend as Wa
import ./impl.bend as Cr
import ./leb_round_trip.bend as L

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

# Instructions that fit
# ---------------------
#
# A br_table's labels count fits a U32: the number of each suffix of its
# labels, plus one, is not 0. A list of 2^32 labels or more would wrap
# Wasm.encode.len, and the round trip fails on it.

def fits.labels(ls: List<&2, U32>) -> Bool:
  match ls:
    case Nil{}:
      True{}
    case Con{_, +rest}:
      Bool.and(Bool.not(U32.is_zero(U32.inc(Cr.Wasm.encode.len(U32, rest)))), fits.labels(rest))

def fits(xs: List<&2, Wa.Wasm.Instr>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, rest}:
      match x:
        case Wa.Wasm.Instr.block{body}:
          Bool.and(fits(body), fits(rest))
        case Wa.Wasm.Instr.loop{body}:
          Bool.and(fits(body), fits(rest))
        case Wa.Wasm.Instr.br_table{ls, l}:
          Bool.and(fits.labels(ls), fits(rest))
        case o:
          fits(rest)

# the number of labels, as a Nat
def labels.nat(ls: List<&2, U32>, +h: {fits.labels(ls) == True{} : Bool}) ->
  {List.length(&2, U32, ls) == U32.to_nat(Cr.Wasm.encode.len(U32, ls)) : Nat}:
  match ls:
    case Nil{}:
      {==}
    case Con{l, +rest}:
      +z = U32.is_zero(U32.inc(Cr.Wasm.encode.len(U32, rest)))
      +ih = labels.nat(rest, and.r(Bool.not(z), fits.labels(rest), h))
      +e = U32.inc_nat(Cr.Wasm.encode.len(U32, rest), not.t(z, and.l(Bool.not(z), fits.labels(rest), h)))
      Equal.trans(Nat, 1n+List.length(&2, U32, rest), 1n+U32.to_nat(Cr.Wasm.encode.len(U32, rest)),
        U32.to_nat(U32.inc(Cr.Wasm.encode.len(U32, rest))),
        Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, U32, rest), U32.to_nat(Cr.Wasm.encode.len(U32, rest)), ih),
        Equal.sym(Nat, U32.to_nat(U32.inc(Cr.Wasm.encode.len(U32, rest))), 1n+U32.to_nat(Cr.Wasm.encode.len(U32, rest)), e))

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

# the labels then A hold as many bytes as there are labels
def has.labels(ls: List<&2, U32>, +A: List<&2, Word(8n)>, +h: {fits.labels(ls) == True{} : Bool}) ->
  {Wa.Wasm.has(Cr.Wasm.encode.labels(ls, A), Cr.Wasm.encode.len(U32, ls)) == True{} : Bool}:
  match ls:
    case Nil{}:
      match A:
        case Nil{}:
          {==}
        case Con{_, _}:
          {==}
    case Con{+l, +rest}:
      +z = U32.is_zero(U32.inc(Cr.Wasm.encode.len(U32, rest)))
      has.uleb(l, Cr.Wasm.encode.labels(rest, A), Cr.Wasm.encode.len(U32, rest),
        not.t(z, and.l(Bool.not(z), fits.labels(rest), h)),
        has.labels(rest, A, and.r(Bool.not(z), fits.labels(rest), h)))

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

# the labels of a br_table, one by one
def tok.items(ls: List<&2, U32>, +A: List<&2, Word(8n)>) ->
  {Wa.Wasm.decode.items(~U32, ~Wa.Wasm.decode.u32, List.length(&2, U32, ls), Cr.Wasm.encode.labels(ls, A)) ==
    Some{Wa.Wasm.Decoded{ls, A}} : Maybe<&2, Wa.Wasm.Decoded<List<&2, U32>>>}:
  match ls:
    case Nil{}:
      {==}
    case Con{+l, +rest}:
      %uleb.back(l, Cr.Wasm.encode.labels(rest, A)) : {Wa.Wasm.decode.bind(U32, List<&2, U32>, _,
        x => r => Wa.Wasm.decode.cons(U32, x, Wa.Wasm.decode.items(~U32, ~Wa.Wasm.decode.u32, List.length(&2, U32, rest), r))) ==
        Some{Wa.Wasm.Decoded{Con{l, rest}, A}} : Maybe<&2, Wa.Wasm.Decoded<List<&2, U32>>>}
      %Equal.sym(Maybe<&2, Wa.Wasm.Decoded<List<&2, U32>>>,
        Wa.Wasm.decode.items(~U32, ~Wa.Wasm.decode.u32, List.length(&2, U32, rest), Cr.Wasm.encode.labels(rest, A)),
        Some{Wa.Wasm.Decoded{rest, A}}, tok.items(rest, A)) :
        {Wa.Wasm.decode.cons(U32, l, _) == Some{Wa.Wasm.Decoded{Con{l, rest}, A}} : Maybe<&2, Wa.Wasm.Decoded<List<&2, U32>>>}
      {==}

def tok.count(+ls: List<&2, U32>, +A: List<&2, Word(8n)>, +h: {fits.labels(ls) == True{} : Bool}) ->
  {Wa.Wasm.decode.count(List.append(&2, Word(8n), Cr.Wasm.encode.uleb(Cr.Wasm.encode.len(U32, ls)), Cr.Wasm.encode.labels(ls, A))) ==
    Some{Wa.Wasm.Decoded{List.length(&2, U32, ls), Cr.Wasm.encode.labels(ls, A)}} : Maybe<&2, Wa.Wasm.Decoded<Nat>>}:
  +n = Cr.Wasm.encode.len(U32, ls)
  +B = Cr.Wasm.encode.labels(ls, A)
  %uleb.back(n, B) : {Wa.Wasm.decode.bind(U32, Nat, _, +m => +r => Wa.Wasm.decode.count.if(Wa.Wasm.has(r, m), m, r)) ==
    Some{Wa.Wasm.Decoded{List.length(&2, U32, ls), B}} : Maybe<&2, Wa.Wasm.Decoded<Nat>>}
  %Equal.sym(Bool, Wa.Wasm.has(B, n), True{}, has.labels(ls, A, h)) :
    {Wa.Wasm.decode.count.if(_, n, B) == Some{Wa.Wasm.Decoded{List.length(&2, U32, ls), B}} : Maybe<&2, Wa.Wasm.Decoded<Nat>>}
  %labels.nat(ls, h) : {Some{Wa.Wasm.Decoded{_, B}} == Some{Wa.Wasm.Decoded{List.length(&2, U32, ls), B}} : Maybe<&2, Wa.Wasm.Decoded<Nat>>}
  {==}

def tok.vec(+ls: List<&2, U32>, +A: List<&2, Word(8n)>, +h: {fits.labels(ls) == True{} : Bool}) ->
  {Wa.Wasm.decode.vec(~U32, ~Wa.Wasm.decode.u32, List.append(&2, Word(8n), Cr.Wasm.encode.uleb(Cr.Wasm.encode.len(U32, ls)), Cr.Wasm.encode.labels(ls, A))) ==
    Some{Wa.Wasm.Decoded{ls, A}} : Maybe<&2, Wa.Wasm.Decoded<List<&2, U32>>>}:
  %Equal.sym(Maybe<&2, Wa.Wasm.Decoded<Nat>>,
    Wa.Wasm.decode.count(List.append(&2, Word(8n), Cr.Wasm.encode.uleb(Cr.Wasm.encode.len(U32, ls)), Cr.Wasm.encode.labels(ls, A))),
    Some{Wa.Wasm.Decoded{List.length(&2, U32, ls), Cr.Wasm.encode.labels(ls, A)}}, tok.count(ls, A, h)) :
    {Wa.Wasm.decode.bind(Nat, List<&2, U32>, _, n => r => Wa.Wasm.decode.items(~U32, ~Wa.Wasm.decode.u32, n, r)) ==
      Some{Wa.Wasm.Decoded{ls, A}} : Maybe<&2, Wa.Wasm.Decoded<List<&2, U32>>>}
  tok.items(ls, A)

def tok.table(+ls: List<&2, U32>, +l: U32, +E: List<&2, Word(8n)>, +h: {fits.labels(ls) == True{} : Bool}) ->
  {Wa.Wasm.decode.table(List.append(&2, Word(8n), Cr.Wasm.encode.uleb(Cr.Wasm.encode.len(U32, ls)),
      Cr.Wasm.encode.labels(ls, List.append(&2, Word(8n), Cr.Wasm.encode.uleb(l), E)))) ==
    Some{Wa.Wasm.Decoded{Wa.Wasm.Token.instr{Wa.Wasm.Instr.br_table{ls, l}}, E}} : Maybe<&2, Wa.Wasm.Decoded<Wa.Wasm.Token>>}:
  +A = List.append(&2, Word(8n), Cr.Wasm.encode.uleb(l), E)
  %Equal.sym(Maybe<&2, Wa.Wasm.Decoded<List<&2, U32>>>,
    Wa.Wasm.decode.vec(~U32, ~Wa.Wasm.decode.u32, List.append(&2, Word(8n), Cr.Wasm.encode.uleb(Cr.Wasm.encode.len(U32, ls)), Cr.Wasm.encode.labels(ls, A))),
    Some{Wa.Wasm.Decoded{ls, A}}, tok.vec(ls, A, h)) :
    {Wa.Wasm.decode.bind(List<&2, U32>, Wa.Wasm.Token, _, ms => r =>
      Wa.Wasm.decode.bind(U32, Wa.Wasm.Token, Wa.Wasm.decode.u32(r), j => r2 => Wa.Wasm.decode.as(Wa.Wasm.Instr.br_table{ms, j}, r2))) ==
      Some{Wa.Wasm.Decoded{Wa.Wasm.Token.instr{Wa.Wasm.Instr.br_table{ls, l}}, E}} : Maybe<&2, Wa.Wasm.Decoded<Wa.Wasm.Token>>}
  %uleb.back(l, E) : {Wa.Wasm.decode.bind(U32, Wa.Wasm.Token, _, j => r2 => Wa.Wasm.decode.as(Wa.Wasm.Instr.br_table{ls, j}, r2)) ==
      Some{Wa.Wasm.Decoded{Wa.Wasm.Token.instr{Wa.Wasm.Instr.br_table{ls, l}}, E}} : Maybe<&2, Wa.Wasm.Decoded<Wa.Wasm.Token>>}
  {==}

# Fuel
# ----

# the fuel left after the labels ls, from k
def lab(ls: List<&2, U32>, k: Nat) -> Nat:
  match ls:
    case Nil{}:
      k
    case Con{l, rest}:
      lab(rest, Nat.add(List.length(&2, Word(8n), Cr.Wasm.encode.uleb(l)), k))

def lab.len(ls: List<&2, U32>, +A: List<&2, Word(8n)>, +k: Nat) ->
  {Nat.add(List.length(&2, Word(8n), Cr.Wasm.encode.labels(ls, A)), k) == Nat.add(List.length(&2, Word(8n), A), lab(ls, k)) : Nat}:
  match ls:
    case Nil{}:
      {==}
    case Con{+l, +rest}:
      +k2 = Nat.add(List.length(&2, Word(8n), Cr.Wasm.encode.uleb(l)), k)
      Equal.trans(Nat, Nat.add(List.length(&2, Word(8n), List.append(&2, Word(8n), Cr.Wasm.encode.uleb(l), Cr.Wasm.encode.labels(rest, A))), k),
        Nat.add(List.length(&2, Word(8n), Cr.Wasm.encode.labels(rest, A)), k2),
        Nat.add(List.length(&2, Word(8n), A), lab(rest, k2)),
        add.len(Cr.Wasm.encode.uleb(l), Cr.Wasm.encode.labels(rest, A), k), lab.len(rest, A, k2))

# the fuel of a br_table's immediates
def table.len(+ls: List<&2, U32>, +l: U32, +E: List<&2, Word(8n)>, +k: Nat) ->
  {Nat.add(List.length(&2, Word(8n), List.append(&2, Word(8n), Cr.Wasm.encode.uleb(Cr.Wasm.encode.len(U32, ls)),
      Cr.Wasm.encode.labels(ls, List.append(&2, Word(8n), Cr.Wasm.encode.uleb(l), E)))), k) ==
    Nat.add(List.length(&2, Word(8n), E), Nat.add(List.length(&2, Word(8n), Cr.Wasm.encode.uleb(l)),
      lab(ls, Nat.add(List.length(&2, Word(8n), Cr.Wasm.encode.uleb(Cr.Wasm.encode.len(U32, ls))), k)))) : Nat}:
  +N = Cr.Wasm.encode.uleb(Cr.Wasm.encode.len(U32, ls))
  +A = List.append(&2, Word(8n), Cr.Wasm.encode.uleb(l), E)
  +k1 = Nat.add(List.length(&2, Word(8n), N), k)
  Equal.trans(Nat, Nat.add(List.length(&2, Word(8n), List.append(&2, Word(8n), N, Cr.Wasm.encode.labels(ls, A))), k),
    Nat.add(List.length(&2, Word(8n), Cr.Wasm.encode.labels(ls, A)), k1),
    Nat.add(List.length(&2, Word(8n), E), Nat.add(List.length(&2, Word(8n), Cr.Wasm.encode.uleb(l)), lab(ls, k1))),
    add.len(N, Cr.Wasm.encode.labels(ls, A), k),
    Equal.trans(Nat, Nat.add(List.length(&2, Word(8n), Cr.Wasm.encode.labels(ls, A)), k1),
      Nat.add(List.length(&2, Word(8n), A), lab(ls, k1)),
      Nat.add(List.length(&2, Word(8n), E), Nat.add(List.length(&2, Word(8n), Cr.Wasm.encode.uleb(l)), lab(ls, k1))),
      lab.len(ls, A, k1), add.len(Cr.Wasm.encode.uleb(l), E, lab(ls, k1))))

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
        case Wa.Wasm.Instr.block{body}:
          left(rest, left(body, 1n+k))
        case Wa.Wasm.Instr.loop{body}:
          left(rest, left(body, 1n+k))
        case Wa.Wasm.Instr.br{l}:
          left(rest, Nat.add(List.length(&2, Word(8n), Cr.Wasm.encode.uleb(l)), k))
        case Wa.Wasm.Instr.br_if{l}:
          left(rest, Nat.add(List.length(&2, Word(8n), Cr.Wasm.encode.uleb(l)), k))
        case Wa.Wasm.Instr.br_table{+ls, l}:
          left(rest, Nat.add(List.length(&2, Word(8n), Cr.Wasm.encode.uleb(l)),
            lab(ls, Nat.add(List.length(&2, Word(8n), Cr.Wasm.encode.uleb(Cr.Wasm.encode.len(U32, ls))), k))))

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
  +st: List<&2, Wa.Wasm.Open>, +h: {fits(xs) == True{} : Bool}) ->
  {Wa.Wasm.decode.instrs.go(Nat.add(List.length(&2, Word(8n), Cr.Wasm.encode.instrs(xs, more)), k), Cr.Wasm.encode.instrs(xs, more), ys, st) ==
    Wa.Wasm.decode.instrs.go(Nat.add(List.length(&2, Word(8n), more), left(xs, k)), more, List.reverse.go(&2, Wa.Wasm.Instr, xs, ys), st) : Maybe<&2, Wa.Wasm.Decoded<List<&2, Wa.Wasm.Instr>>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +rest}:
      match x:
        case Wa.Wasm.Instr.const{+n}:
          simple(65, Cr.Wasm.encode.sleb(n), rest, more, Wa.Wasm.Instr.const{n}, k, ys, st, tok.const(n, Cr.Wasm.encode.instrs(rest, more)),
            run(rest, more, Nat.add(List.length(&2, Word(8n), Cr.Wasm.encode.sleb(n)), k), Con{Wa.Wasm.Instr.const{n}, ys}, st, h))
        case Wa.Wasm.Instr.local_get{+i}:
          simple(32, Cr.Wasm.encode.uleb(i), rest, more, Wa.Wasm.Instr.local_get{i}, k, ys, st, tok.index(j => Wa.Wasm.Instr.local_get{j}, i, Cr.Wasm.encode.instrs(rest, more)),
            run(rest, more, Nat.add(List.length(&2, Word(8n), Cr.Wasm.encode.uleb(i)), k), Con{Wa.Wasm.Instr.local_get{i}, ys}, st, h))
        case Wa.Wasm.Instr.local_set{+i}:
          simple(33, Cr.Wasm.encode.uleb(i), rest, more, Wa.Wasm.Instr.local_set{i}, k, ys, st, tok.index(j => Wa.Wasm.Instr.local_set{j}, i, Cr.Wasm.encode.instrs(rest, more)),
            run(rest, more, Nat.add(List.length(&2, Word(8n), Cr.Wasm.encode.uleb(i)), k), Con{Wa.Wasm.Instr.local_set{i}, ys}, st, h))
        case Wa.Wasm.Instr.local_tee{+i}:
          simple(34, Cr.Wasm.encode.uleb(i), rest, more, Wa.Wasm.Instr.local_tee{i}, k, ys, st, tok.index(j => Wa.Wasm.Instr.local_tee{j}, i, Cr.Wasm.encode.instrs(rest, more)),
            run(rest, more, Nat.add(List.length(&2, Word(8n), Cr.Wasm.encode.uleb(i)), k), Con{Wa.Wasm.Instr.local_tee{i}, ys}, st, h))
        case Wa.Wasm.Instr.op{+o}:
          simple(Cr.Wasm.encode.opcode(o), [], rest, more, Wa.Wasm.Instr.op{o}, k, ys, st,
            tok.op(o, Cr.Wasm.encode.instrs(rest, more)), run(rest, more, k, Con{Wa.Wasm.Instr.op{o}, ys}, st, h))
        case Wa.Wasm.Instr.eqz{}:
          simple(69, [], rest, more, Wa.Wasm.Instr.eqz{}, k, ys, st, {==},
            run(rest, more, Nat.add(List.length(&2, Word(8n), []), k), Con{Wa.Wasm.Instr.eqz{}, ys}, st, h))
        case Wa.Wasm.Instr.load{+o}:
          simple(40, Con{Sd.Byte.from_u32(2), Cr.Wasm.encode.uleb(o)}, rest, more, Wa.Wasm.Instr.load{o}, k, ys, st,
            tok.memarg(j => Wa.Wasm.Instr.load{j}, o, Cr.Wasm.encode.instrs(rest, more)),
            run(rest, more, Nat.add(List.length(&2, Word(8n), Con{Sd.Byte.from_u32(2), Cr.Wasm.encode.uleb(o)}), k), Con{Wa.Wasm.Instr.load{o}, ys}, st, h))
        case Wa.Wasm.Instr.load8_u{+o}:
          simple(45, Con{Sd.Byte.from_u32(0), Cr.Wasm.encode.uleb(o)}, rest, more, Wa.Wasm.Instr.load8_u{o}, k, ys, st,
            tok.memarg(j => Wa.Wasm.Instr.load8_u{j}, o, Cr.Wasm.encode.instrs(rest, more)),
            run(rest, more, Nat.add(List.length(&2, Word(8n), Con{Sd.Byte.from_u32(0), Cr.Wasm.encode.uleb(o)}), k), Con{Wa.Wasm.Instr.load8_u{o}, ys}, st, h))
        case Wa.Wasm.Instr.store{+o}:
          simple(54, Con{Sd.Byte.from_u32(2), Cr.Wasm.encode.uleb(o)}, rest, more, Wa.Wasm.Instr.store{o}, k, ys, st,
            tok.memarg(j => Wa.Wasm.Instr.store{j}, o, Cr.Wasm.encode.instrs(rest, more)),
            run(rest, more, Nat.add(List.length(&2, Word(8n), Con{Sd.Byte.from_u32(2), Cr.Wasm.encode.uleb(o)}), k), Con{Wa.Wasm.Instr.store{o}, ys}, st, h))
        case Wa.Wasm.Instr.store8{+o}:
          simple(58, Con{Sd.Byte.from_u32(0), Cr.Wasm.encode.uleb(o)}, rest, more, Wa.Wasm.Instr.store8{o}, k, ys, st,
            tok.memarg(j => Wa.Wasm.Instr.store8{j}, o, Cr.Wasm.encode.instrs(rest, more)),
            run(rest, more, Nat.add(List.length(&2, Word(8n), Con{Sd.Byte.from_u32(0), Cr.Wasm.encode.uleb(o)}), k), Con{Wa.Wasm.Instr.store8{o}, ys}, st, h))
        case Wa.Wasm.Instr.memory_size{}:
          simple(63, [Sd.Byte.from_u32(0)], rest, more, Wa.Wasm.Instr.memory_size{}, k, ys, st, {==},
            run(rest, more, Nat.add(List.length(&2, Word(8n), [Sd.Byte.from_u32(0)]), k), Con{Wa.Wasm.Instr.memory_size{}, ys}, st, h))
        case Wa.Wasm.Instr.memory_grow{}:
          simple(64, [Sd.Byte.from_u32(0)], rest, more, Wa.Wasm.Instr.memory_grow{}, k, ys, st, {==},
            run(rest, more, Nat.add(List.length(&2, Word(8n), [Sd.Byte.from_u32(0)]), k), Con{Wa.Wasm.Instr.memory_grow{}, ys}, st, h))
        case Wa.Wasm.Instr.block{+body}:
          +R = Cr.Wasm.encode.instrs(rest, more)
          +B = Cr.Wasm.encode.instrs(body, Con{Sd.Byte.from_u32(11), R})
          +k1 = left(body, 1n+k)
          +os = {Con{Wa.Wasm.Open{False{}, ys}, st} : List<&2, Wa.Wasm.Open>}
          +g = after(rest, more, k1, Wa.Wasm.Instr.block{body}, ys, st)
          %add.succ(List.length(&2, Word(8n), B), k) : {Wa.Wasm.decode.instrs.go(_, B, [], os) == g : Maybe<&2, Wa.Wasm.Decoded<List<&2, Wa.Wasm.Instr>>>}
          %Equal.sym(Maybe<&2, Wa.Wasm.Decoded<List<&2, Wa.Wasm.Instr>>>, Wa.Wasm.decode.instrs.go(Nat.add(List.length(&2, Word(8n), B), 1n+k), B, [], os),
            Wa.Wasm.decode.instrs.go(Nat.add(List.length(&2, Word(8n), Con{Sd.Byte.from_u32(11), R}), k1), Con{Sd.Byte.from_u32(11), R}, List.reverse.go(&2, Wa.Wasm.Instr, body, []), os),
            run(body, Con{Sd.Byte.from_u32(11), R}, 1n+k, [], os, and.l(fits(body), fits(rest), h))) : {_ == g : Maybe<&2, Wa.Wasm.Decoded<List<&2, Wa.Wasm.Instr>>>}
          %rev2(body) : {Wa.Wasm.decode.instrs.go(Nat.add(List.length(&2, Word(8n), R), k1), R, Con{Wa.Wasm.Instr.block{_}, ys}, st) == g : Maybe<&2, Wa.Wasm.Decoded<List<&2, Wa.Wasm.Instr>>>}
          run(rest, more, k1, Con{Wa.Wasm.Instr.block{body}, ys}, st, and.r(fits(body), fits(rest), h))
        case Wa.Wasm.Instr.loop{+body}:
          +R = Cr.Wasm.encode.instrs(rest, more)
          +B = Cr.Wasm.encode.instrs(body, Con{Sd.Byte.from_u32(11), R})
          +k1 = left(body, 1n+k)
          +os = {Con{Wa.Wasm.Open{True{}, ys}, st} : List<&2, Wa.Wasm.Open>}
          +g = after(rest, more, k1, Wa.Wasm.Instr.loop{body}, ys, st)
          %add.succ(List.length(&2, Word(8n), B), k) : {Wa.Wasm.decode.instrs.go(_, B, [], os) == g : Maybe<&2, Wa.Wasm.Decoded<List<&2, Wa.Wasm.Instr>>>}
          %Equal.sym(Maybe<&2, Wa.Wasm.Decoded<List<&2, Wa.Wasm.Instr>>>, Wa.Wasm.decode.instrs.go(Nat.add(List.length(&2, Word(8n), B), 1n+k), B, [], os),
            Wa.Wasm.decode.instrs.go(Nat.add(List.length(&2, Word(8n), Con{Sd.Byte.from_u32(11), R}), k1), Con{Sd.Byte.from_u32(11), R}, List.reverse.go(&2, Wa.Wasm.Instr, body, []), os),
            run(body, Con{Sd.Byte.from_u32(11), R}, 1n+k, [], os, and.l(fits(body), fits(rest), h))) : {_ == g : Maybe<&2, Wa.Wasm.Decoded<List<&2, Wa.Wasm.Instr>>>}
          %rev2(body) : {Wa.Wasm.decode.instrs.go(Nat.add(List.length(&2, Word(8n), R), k1), R, Con{Wa.Wasm.Instr.loop{_}, ys}, st) == g : Maybe<&2, Wa.Wasm.Decoded<List<&2, Wa.Wasm.Instr>>>}
          run(rest, more, k1, Con{Wa.Wasm.Instr.loop{body}, ys}, st, and.r(fits(body), fits(rest), h))
        case Wa.Wasm.Instr.br{+l}:
          simple(12, Cr.Wasm.encode.uleb(l), rest, more, Wa.Wasm.Instr.br{l}, k, ys, st, tok.index(j => Wa.Wasm.Instr.br{j}, l, Cr.Wasm.encode.instrs(rest, more)),
            run(rest, more, Nat.add(List.length(&2, Word(8n), Cr.Wasm.encode.uleb(l)), k), Con{Wa.Wasm.Instr.br{l}, ys}, st, h))
        case Wa.Wasm.Instr.br_if{+l}:
          simple(13, Cr.Wasm.encode.uleb(l), rest, more, Wa.Wasm.Instr.br_if{l}, k, ys, st, tok.index(j => Wa.Wasm.Instr.br_if{j}, l, Cr.Wasm.encode.instrs(rest, more)),
            run(rest, more, Nat.add(List.length(&2, Word(8n), Cr.Wasm.encode.uleb(l)), k), Con{Wa.Wasm.Instr.br_if{l}, ys}, st, h))
        case Wa.Wasm.Instr.br_table{+ls, +l}:
          +E = Cr.Wasm.encode.instrs(rest, more)
          +x = {Wa.Wasm.Instr.br_table{ls, l} : Wa.Wasm.Instr}
          +k2 = Nat.add(List.length(&2, Word(8n), Cr.Wasm.encode.uleb(l)),
            lab(ls, Nat.add(List.length(&2, Word(8n), Cr.Wasm.encode.uleb(Cr.Wasm.encode.len(U32, ls))), k)))
          +bs = List.append(&2, Word(8n), Cr.Wasm.encode.uleb(Cr.Wasm.encode.len(U32, ls)),
            Cr.Wasm.encode.labels(ls, List.append(&2, Word(8n), Cr.Wasm.encode.uleb(l), E)))
          step(Sd.Byte.from_u32(14), bs, E, x, k, k2, ys, st, after(rest, more, k2, x, ys, st),
            tok.table(ls, l, E, and.l(fits.labels(ls), fits(rest), h)), table.len(ls, l, E, k),
            run(rest, more, k2, Con{x, ys}, st, and.r(fits.labels(ls), fits(rest), h)))

# a function body's instructions, encoded then decoded as
# Wasm.decode.func.body does, are themselves (when each br_table's labels
# count fits a U32)
def instrs.round(+xs: List<&2, Wa.Wasm.Instr>, +h: {fits(xs) == True{} : Bool}) ->
  {Wa.Wasm.decode.instrs(1n+List.length(&2, Word(8n), Cr.Wasm.encode.instrs(xs, [Sd.Byte.from_u32(11)])), Cr.Wasm.encode.instrs(xs, [Sd.Byte.from_u32(11)])) ==
    Some{Wa.Wasm.Decoded{xs, []}} : Maybe<&2, Wa.Wasm.Decoded<List<&2, Wa.Wasm.Instr>>>}:
  +bs = Cr.Wasm.encode.instrs(xs, [Sd.Byte.from_u32(11)])
  %add.one(List.length(&2, Word(8n), bs)) :
    {Wa.Wasm.decode.instrs.go(_, bs, [], []) == Some{Wa.Wasm.Decoded{xs, []}} : Maybe<&2, Wa.Wasm.Decoded<List<&2, Wa.Wasm.Instr>>>}
  %Equal.sym(Maybe<&2, Wa.Wasm.Decoded<List<&2, Wa.Wasm.Instr>>>,
    Wa.Wasm.decode.instrs.go(Nat.add(List.length(&2, Word(8n), bs), 1n), bs, [], []),
    Wa.Wasm.decode.instrs.go(Nat.add(List.length(&2, Word(8n), [Sd.Byte.from_u32(11)]), left(xs, 1n)), [Sd.Byte.from_u32(11)], List.reverse.go(&2, Wa.Wasm.Instr, xs, []), []),
    run(xs, [Sd.Byte.from_u32(11)], 1n, [], [], h)) :
    {_ == Some{Wa.Wasm.Decoded{xs, []}} : Maybe<&2, Wa.Wasm.Decoded<List<&2, Wa.Wasm.Instr>>>}
  %rev2(xs) : {Some{Wa.Wasm.Decoded{_, []}} == Some{Wa.Wasm.Decoded{xs, []}} : Maybe<&2, Wa.Wasm.Decoded<List<&2, Wa.Wasm.Instr>>>}
  {==}
