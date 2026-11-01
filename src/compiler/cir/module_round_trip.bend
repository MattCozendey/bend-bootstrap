# compiler: the round trip of the compiler's modules
# ==================================================
#
# Wasm.decode.module reads back the module of Cir.module that Wasm.encode
# writes (module.round, at the end). The bytes are the header and six
# sections whose contents stay variables (secs.six reads them back, with fuel
# of the form g + |rest|); the parts are then decoded one by one: the memory's
# limits (part.mem), the two codes (part.code, with I.instrs.round on each
# body; fits.stmt shows that Cir.code.stmt emits no br_table) and the data
# segment (part.data). The sizes that must fit a U32 come from the premises
# with the limits kept as variables (round.sized), so that the checker never
# expands 2^26, 2^32 - 1 or 50000.

import Base
import ../../shared/shared.bend as Sd
import ../../wasm/impl.bend as Wa
import ./impl.bend as Cr
import ./leb_round_trip.bend as L
import ./instrs_round_trip.bend as I
import ../need_big.bend as N
import ../img_small.bend as G

# Lists
# -----

def app.nil(-A: Data, xs: List<&2, A>) -> {List.append(&2, A, xs, []) == xs : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, t}:
      Equal.cong(List<&2, A>, List<&2, A>, l => Con{x, l}, List.append(&2, A, t, []), t, app.nil(A, t))

def app.assoc(-A: Data, xs: List<&2, A>, +ys: List<&2, A>, +zs: List<&2, A>) ->
  {List.append(&2, A, List.append(&2, A, xs, ys), zs) == List.append(&2, A, xs, List.append(&2, A, ys, zs)) : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, t}:
      Equal.cong(List<&2, A>, List<&2, A>, l => Con{x, l},
        List.append(&2, A, List.append(&2, A, t, ys), zs), List.append(&2, A, t, List.append(&2, A, ys, zs)), app.assoc(A, t, ys, zs))

def len.app(-A: Data, xs: List<&2, A>, +ys: List<&2, A>) ->
  {List.length(&2, A, List.append(&2, A, xs, ys)) == Nat.add(List.length(&2, A, xs), List.length(&2, A, ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, A, List.append(&2, A, t, ys)),
        Nat.add(List.length(&2, A, t), List.length(&2, A, ys)), len.app(A, t, ys))

def add.assoc(a: Nat, +b: Nat, +c: Nat) -> {Nat.add(a, Nat.add(b, c)) == Nat.add(Nat.add(a, b), c) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, n => 1n+n, Nat.add(p, Nat.add(b, c)), Nat.add(Nat.add(p, b), c), add.assoc(p, b, c))

# the bytes xs, then ys: |xs| of them are xs
def take.app(xs: List<&2, Word(8n)>, +ys: List<&2, Word(8n)>) ->
  {Wa.Wasm.decode.take(List.length(&2, Word(8n), xs), List.append(&2, Word(8n), xs, ys)) == Some{Wa.Wasm.Decoded{xs, ys}} : Maybe<&2, Wa.Wasm.Decoded<List<&2, Word(8n)>>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(Maybe<&2, Wa.Wasm.Decoded<List<&2, Word(8n)>>>, Wa.Wasm.decode.take(List.length(&2, Word(8n), t), List.append(&2, Word(8n), t, ys)),
        Some{Wa.Wasm.Decoded{t, ys}}, take.app(t, ys)) :
        {Wa.Wasm.decode.cons(Word(8n), x, _) == Some{Wa.Wasm.Decoded{Con{x, t}, ys}} : Maybe<&2, Wa.Wasm.Decoded<List<&2, Word(8n)>>>}
      {==}

# every list holds 0 bytes
def has0(xs: List<&2, Word(8n)>) -> {Wa.Wasm.has(xs, 0) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{_, _}:
      {==}

# Lengths that fit a U32
# ----------------------

# 1 + a fits a word: a + 1 is not 0
def nz.go(b: Bool, +w: Word(32n), e: {U32.is_zero(U32{Word.inc(32n, w)}) == b : Bool},
  l: N.Le(1n, Word.to_nat(32n, Word.inc(32n, w)))) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      +z = L.Word.eq_zero(32n, Word.inc(32n, w), e)
      Empty.absurd({True{} == False{} : Bool},
        N.le_rw_r(1n, Word.to_nat(32n, Word.inc(32n, w)), Word.to_nat(32n, Word.zero(32n)),
          Equal.cong(Word(32n), Nat, x => Word.to_nat(32n, x), Word.inc(32n, w), Word.zero(32n), z), l))

def nz.of(a: U32, l: N.Le(1n, U32.to_nat(U32.inc(a)))) -> {U32.is_zero(U32.inc(a)) == False{} : Bool}:
  match a:
    case U32{+w}:
      nz.go(U32.is_zero(U32{Word.inc(32n, w)}), w, {==}, l)

def nz(+a: U32, +M: U32, h: N.Le(1n+U32.to_nat(a), U32.to_nat(M))) -> {U32.is_zero(U32.inc(a)) == False{} : Bool}:
  nz.of(a, N.le_trans(1n, 1n+U32.to_nat(a), U32.to_nat(U32.inc(a)), N.le_zero(U32.to_nat(a)), G.U32.inc_ge(a, M, h)))

# each suffix of the bytes bs has a length, plus one, that is not 0 in a U32
def fits.bytes(bs: List<&2, Word(8n)>) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case Con{_, +rest}:
      Bool.and(Bool.not(U32.is_zero(U32.inc(Cr.Wasm.encode.len(Word(8n), rest)))), fits.bytes(rest))

# the number of the bytes bs, as a Nat
def bytes.nat(bs: List<&2, Word(8n)>, +h: {fits.bytes(bs) == True{} : Bool}) ->
  {List.length(&2, Word(8n), bs) == U32.to_nat(Cr.Wasm.encode.len(Word(8n), bs)) : Nat}:
  match bs:
    case Nil{}:
      {==}
    case Con{b, +rest}:
      +z = U32.is_zero(U32.inc(Cr.Wasm.encode.len(Word(8n), rest)))
      +ih = bytes.nat(rest, I.and.r(Bool.not(z), fits.bytes(rest), h))
      +e = I.U32.inc_nat(Cr.Wasm.encode.len(Word(8n), rest), I.not.t(z, I.and.l(Bool.not(z), fits.bytes(rest), h)))
      Equal.trans(Nat, 1n+List.length(&2, Word(8n), rest), 1n+U32.to_nat(Cr.Wasm.encode.len(Word(8n), rest)),
        U32.to_nat(U32.inc(Cr.Wasm.encode.len(Word(8n), rest))),
        Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, Word(8n), rest), U32.to_nat(Cr.Wasm.encode.len(Word(8n), rest)), ih),
        Equal.sym(Nat, U32.to_nat(U32.inc(Cr.Wasm.encode.len(Word(8n), rest))), 1n+U32.to_nat(Cr.Wasm.encode.len(Word(8n), rest)), e))

# a list of at most M bytes: each suffix's length, plus one, is not 0
def fits.of_le(xs: List<&2, Word(8n)>, +M: U32, +h: N.Le(List.length(&2, Word(8n), xs), U32.to_nat(M))) -> {fits.bytes(xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{_, +t}:
      +ih = fits.of_le(t, M, N.weaken(List.length(&2, Word(8n), t), U32.to_nat(M), h))
      +n = bytes.nat(t, ih)
      +h2 = N.le_rw_l(1n+List.length(&2, Word(8n), t), 1n+U32.to_nat(Cr.Wasm.encode.len(Word(8n), t)), U32.to_nat(M),
        Equal.cong(Nat, Nat, k => 1n+k, List.length(&2, Word(8n), t), U32.to_nat(Cr.Wasm.encode.len(Word(8n), t)), n), h)
      +z = nz(Cr.Wasm.encode.len(Word(8n), t), M, h2)
      %Equal.sym(Bool, U32.is_zero(U32.inc(Cr.Wasm.encode.len(Word(8n), t))), False{}, z) : {Bool.and(Bool.not(_), fits.bytes(t)) == True{} : Bool}
      ih

# xs, then A, hold as many bytes as xs has
def has.app(xs: List<&2, Word(8n)>, +A: List<&2, Word(8n)>, +h: {fits.bytes(xs) == True{} : Bool}) ->
  {Wa.Wasm.has(List.append(&2, Word(8n), xs, A), Cr.Wasm.encode.len(Word(8n), xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      has0(A)
    case Con{+y, +t}:
      +z = U32.is_zero(U32.inc(Cr.Wasm.encode.len(Word(8n), t)))
      I.has.inc(y, [], List.append(&2, Word(8n), t, A), Cr.Wasm.encode.len(Word(8n), t),
        I.not.t(z, I.and.l(Bool.not(z), fits.bytes(t), h)),
        has.app(t, A, I.and.r(Bool.not(z), fits.bytes(t), h)))

# Vectors and sections
# --------------------

# the number of the bytes c, then c and acc: |c|
def count.sized(+c: List<&2, Word(8n)>, +acc: List<&2, Word(8n)>, +h: {fits.bytes(c) == True{} : Bool}) ->
  {Wa.Wasm.decode.count(List.append(&2, Word(8n), Cr.Wasm.encode.uleb(Cr.Wasm.encode.len(Word(8n), c)), List.append(&2, Word(8n), c, acc))) ==
    Some{Wa.Wasm.Decoded{List.length(&2, Word(8n), c), List.append(&2, Word(8n), c, acc)}} : Maybe<&2, Wa.Wasm.Decoded<Nat>>}:
  +X = List.append(&2, Word(8n), c, acc)
  +v = Cr.Wasm.encode.len(Word(8n), c)
  %I.uleb.back(v, X) : {Wa.Wasm.decode.bind(U32, Nat, _, +n => +r => Wa.Wasm.decode.count.if(Wa.Wasm.has(r, n), n, r)) ==
    Some{Wa.Wasm.Decoded{List.length(&2, Word(8n), c), X}} : Maybe<&2, Wa.Wasm.Decoded<Nat>>}
  %Equal.sym(Bool, Wa.Wasm.has(X, v), True{}, has.app(c, acc, h)) : {Wa.Wasm.decode.count.if(_, v, X) ==
    Some{Wa.Wasm.Decoded{List.length(&2, Word(8n), c), X}} : Maybe<&2, Wa.Wasm.Decoded<Nat>>}
  %bytes.nat(c, h) : {Some{Wa.Wasm.Decoded{_, X}} == Some{Wa.Wasm.Decoded{List.length(&2, Word(8n), c), X}} : Maybe<&2, Wa.Wasm.Decoded<Nat>>}
  {==}

# a section of the content c, then acc
def sec.round(+id: U32, +c: List<&2, Word(8n)>, +acc: List<&2, Word(8n)>, +h: {fits.bytes(c) == True{} : Bool}) ->
  {Wa.Wasm.decode.section(Cr.Wasm.encode.section(id, c, acc)) == Some{Wa.Wasm.Decoded{Wa.Wasm.Section{Sd.Byte.to_u32(Sd.Byte.from_u32(id)), c}, acc}} : Maybe<&2, Wa.Wasm.Decoded<Wa.Wasm.Section>>}:
  +u = Cr.Wasm.encode.uleb(Cr.Wasm.encode.len(Word(8n), c))
  +X = List.append(&2, Word(8n), c, acc)
  %Equal.sym(List<&2, Word(8n)>, List.append(&2, Word(8n), List.append(&2, Word(8n), u, c), acc), List.append(&2, Word(8n), u, X), app.assoc(Word(8n), u, c, acc)) :
    {Wa.Wasm.decode.section(Con{Sd.Byte.from_u32(id), _}) == Some{Wa.Wasm.Decoded{Wa.Wasm.Section{Sd.Byte.to_u32(Sd.Byte.from_u32(id)), c}, acc}} : Maybe<&2, Wa.Wasm.Decoded<Wa.Wasm.Section>>}
  %Equal.sym(Maybe<&2, Wa.Wasm.Decoded<Nat>>, Wa.Wasm.decode.count(List.append(&2, Word(8n), u, X)), Some{Wa.Wasm.Decoded{List.length(&2, Word(8n), c), X}}, count.sized(c, acc, h)) :
    {Wa.Wasm.decode.bind(Nat, Wa.Wasm.Section, _, n => r =>
      Wa.Wasm.decode.bind(List<&2, Word(8n)>, Wa.Wasm.Section, Wa.Wasm.decode.take(n, r), c2 => r2 =>
        Some{Wa.Wasm.Decoded{Wa.Wasm.Section{Sd.Byte.to_u32(Sd.Byte.from_u32(id)), c2}, r2}})) == Some{Wa.Wasm.Decoded{Wa.Wasm.Section{Sd.Byte.to_u32(Sd.Byte.from_u32(id)), c}, acc}} : Maybe<&2, Wa.Wasm.Decoded<Wa.Wasm.Section>>}
  %Equal.sym(Maybe<&2, Wa.Wasm.Decoded<List<&2, Word(8n)>>>, Wa.Wasm.decode.take(List.length(&2, Word(8n), c), X), Some{Wa.Wasm.Decoded{c, acc}}, take.app(c, acc)) :
    {Wa.Wasm.decode.bind(List<&2, Word(8n)>, Wa.Wasm.Section, _, c2 => r2 =>
        Some{Wa.Wasm.Decoded{Wa.Wasm.Section{Sd.Byte.to_u32(Sd.Byte.from_u32(id)), c2}, r2}}) == Some{Wa.Wasm.Decoded{Wa.Wasm.Section{Sd.Byte.to_u32(Sd.Byte.from_u32(id)), c}, acc}} : Maybe<&2, Wa.Wasm.Decoded<Wa.Wasm.Section>>}
  {==}

# the fuel g + |the section|: 1 more than g, its size, and the bytes after it
def fuel.sec(+g: Nat, +id: U32, +c: List<&2, Word(8n)>, +acc: List<&2, Word(8n)>) ->
  {Nat.add(g, List.length(&2, Word(8n), Cr.Wasm.encode.section(id, c, acc))) ==
    1n+Nat.add(Nat.add(g, List.length(&2, Word(8n), Cr.Wasm.encode.sized(c))), List.length(&2, Word(8n), acc)) : Nat}:
  +s = Cr.Wasm.encode.sized(c)
  +ls = List.length(&2, Word(8n), s)
  +la = List.length(&2, Word(8n), acc)
  +lx = List.length(&2, Word(8n), List.append(&2, Word(8n), s, acc))
  Equal.trans(Nat, Nat.add(g, 1n+lx), 1n+Nat.add(g, lx), 1n+Nat.add(Nat.add(g, ls), la),
    I.add.succ(g, lx),
    Equal.cong(Nat, Nat, n => 1n+n, Nat.add(g, lx), Nat.add(Nat.add(g, ls), la),
      Equal.trans(Nat, Nat.add(g, lx), Nat.add(g, Nat.add(ls, la)), Nat.add(Nat.add(g, ls), la),
        Equal.cong(Nat, Nat, n => Nat.add(g, n), lx, Nat.add(ls, la), len.app(Word(8n), s, acc)),
        add.assoc(g, ls, la))))

# the sections, from one of the content c
def secs.step(+g: Nat, +id: U32, +c: List<&2, Word(8n)>, +acc: List<&2, Word(8n)>, -ss: List<&2, Wa.Wasm.Section>,
  +h: {fits.bytes(c) == True{} : Bool},
  rest: {Wa.Wasm.decode.sections(Nat.add(Nat.add(g, List.length(&2, Word(8n), Cr.Wasm.encode.sized(c))), List.length(&2, Word(8n), acc)), acc) == Some{ss} : Maybe<&2, List<&2, Wa.Wasm.Section>>}
) -> {Wa.Wasm.decode.sections(Nat.add(g, List.length(&2, Word(8n), Cr.Wasm.encode.section(id, c, acc))), Cr.Wasm.encode.section(id, c, acc)) ==
    Some{Con{Wa.Wasm.Section{Sd.Byte.to_u32(Sd.Byte.from_u32(id)), c}, ss}} : Maybe<&2, List<&2, Wa.Wasm.Section>>}:
  +S = Cr.Wasm.encode.section(id, c, acc)
  +F = Nat.add(Nat.add(g, List.length(&2, Word(8n), Cr.Wasm.encode.sized(c))), List.length(&2, Word(8n), acc))
  %Equal.sym(Nat, Nat.add(g, List.length(&2, Word(8n), S)), 1n+F, fuel.sec(g, id, c, acc)) :
    {Wa.Wasm.decode.sections(_, S) == Some{Con{Wa.Wasm.Section{Sd.Byte.to_u32(Sd.Byte.from_u32(id)), c}, ss}} : Maybe<&2, List<&2, Wa.Wasm.Section>>}
  %Equal.sym(Maybe<&2, Wa.Wasm.Decoded<Wa.Wasm.Section>>, Wa.Wasm.decode.section(S), Some{Wa.Wasm.Decoded{Wa.Wasm.Section{Sd.Byte.to_u32(Sd.Byte.from_u32(id)), c}, acc}}, sec.round(id, c, acc, h)) :
    {Wa.Wasm.decode.sections.got(_, r => Wa.Wasm.decode.sections(F, r)) == Some{Con{Wa.Wasm.Section{Sd.Byte.to_u32(Sd.Byte.from_u32(id)), c}, ss}} : Maybe<&2, List<&2, Wa.Wasm.Section>>}
  %Equal.sym(Maybe<&2, List<&2, Wa.Wasm.Section>>, Wa.Wasm.decode.sections(F, acc), Some{ss}, rest) :
    {Wa.Wasm.decode.sections.cons(Wa.Wasm.Section{Sd.Byte.to_u32(Sd.Byte.from_u32(id)), c}, _) == Some{Con{Wa.Wasm.Section{Sd.Byte.to_u32(Sd.Byte.from_u32(id)), c}, ss}} : Maybe<&2, List<&2, Wa.Wasm.Section>>}
  {==}

def secs.nil(f: Nat) -> {Wa.Wasm.decode.sections(f, []) == Some{[]} : Maybe<&2, List<&2, Wa.Wasm.Section>>}:
  match f:
    case 0n:
      {==}
    case 1n+p:
      {==}

# the six sections of the contents c1 to c11
def secs.bytes(c1: List<&2, Word(8n)>, c3: List<&2, Word(8n)>, c5: List<&2, Word(8n)>, c7: List<&2, Word(8n)>, c10: List<&2, Word(8n)>, c11: List<&2, Word(8n)>) -> List<&2, Word(8n)>:
  Cr.Wasm.encode.section(1, c1, Cr.Wasm.encode.section(3, c3, Cr.Wasm.encode.section(5, c5,
    Cr.Wasm.encode.section(7, c7, Cr.Wasm.encode.section(10, c10, Cr.Wasm.encode.section(11, c11, []))))))

def secs.six(+c1: List<&2, Word(8n)>, +c3: List<&2, Word(8n)>, +c5: List<&2, Word(8n)>, +c7: List<&2, Word(8n)>, +c10: List<&2, Word(8n)>, +c11: List<&2, Word(8n)>,
  +h1: {fits.bytes(c1) == True{} : Bool}, +h3: {fits.bytes(c3) == True{} : Bool}, +h5: {fits.bytes(c5) == True{} : Bool},
  +h7: {fits.bytes(c7) == True{} : Bool}, +h10: {fits.bytes(c10) == True{} : Bool}, +h11: {fits.bytes(c11) == True{} : Bool}
) -> {Wa.Wasm.decode.sections(List.length(&2, Word(8n), secs.bytes(c1, c3, c5, c7, c10, c11)), secs.bytes(c1, c3, c5, c7, c10, c11)) ==
    Some{[Wa.Wasm.Section{1, c1}, Wa.Wasm.Section{3, c3}, Wa.Wasm.Section{5, c5}, Wa.Wasm.Section{7, c7}, Wa.Wasm.Section{10, c10}, Wa.Wasm.Section{11, c11}]} :
    Maybe<&2, List<&2, Wa.Wasm.Section>>}:
  +S11 = Cr.Wasm.encode.section(11, c11, [])
  +S10 = Cr.Wasm.encode.section(10, c10, S11)
  +S7 = Cr.Wasm.encode.section(7, c7, S10)
  +S5 = Cr.Wasm.encode.section(5, c5, S7)
  +S3 = Cr.Wasm.encode.section(3, c3, S5)
  +g1 = Nat.add(0n, List.length(&2, Word(8n), Cr.Wasm.encode.sized(c1)))
  +g3 = Nat.add(g1, List.length(&2, Word(8n), Cr.Wasm.encode.sized(c3)))
  +g5 = Nat.add(g3, List.length(&2, Word(8n), Cr.Wasm.encode.sized(c5)))
  +g7 = Nat.add(g5, List.length(&2, Word(8n), Cr.Wasm.encode.sized(c7)))
  +g10 = Nat.add(g7, List.length(&2, Word(8n), Cr.Wasm.encode.sized(c10)))
  +g11 = Nat.add(g10, List.length(&2, Word(8n), Cr.Wasm.encode.sized(c11)))
  secs.step(0n, 1, c1, S3, [Wa.Wasm.Section{3, c3}, Wa.Wasm.Section{5, c5}, Wa.Wasm.Section{7, c7}, Wa.Wasm.Section{10, c10}, Wa.Wasm.Section{11, c11}], h1,
    secs.step(g1, 3, c3, S5, [Wa.Wasm.Section{5, c5}, Wa.Wasm.Section{7, c7}, Wa.Wasm.Section{10, c10}, Wa.Wasm.Section{11, c11}], h3,
      secs.step(g3, 5, c5, S7, [Wa.Wasm.Section{7, c7}, Wa.Wasm.Section{10, c10}, Wa.Wasm.Section{11, c11}], h5,
        secs.step(g5, 7, c7, S10, [Wa.Wasm.Section{10, c10}, Wa.Wasm.Section{11, c11}], h7,
          secs.step(g7, 10, c10, S11, [Wa.Wasm.Section{11, c11}], h10,
            secs.step(g10, 11, c11, [], [], h11, secs.nil(Nat.add(g11, 0n))))))))

# Modules
# -------

# Wasm.decode.module.parts, from the decoded items of its sections
def parts(
  ts: Maybe<&2, List<&2, Wa.Wasm.Type>>, idx: Maybe<&2, List<&2, U32>>, mem: Maybe<&2, Maybe<&2, Wa.Wasm.Limits>>,
  es: Maybe<&2, List<&2, Wa.Wasm.Export>>, cs: Maybe<&2, List<&2, Wa.Wasm.Code>>, seg: Maybe<&2, Maybe<&2, Wa.Wasm.Segment>>
) -> Maybe<&2, Wa.Wasm.Module>:
  Maybe.bind(&2, List<&2, Wa.Wasm.Type>, Wa.Wasm.Module, ts, ts2 =>
    Maybe.bind(&2, List<&2, U32>, Wa.Wasm.Module, idx, idx2 =>
      Maybe.bind(&2, Maybe<&2, Wa.Wasm.Limits>, Wa.Wasm.Module, mem, mem2 =>
        Maybe.bind(&2, List<&2, Wa.Wasm.Export>, Wa.Wasm.Module, es, es2 =>
          Maybe.bind(&2, List<&2, Wa.Wasm.Code>, Wa.Wasm.Module, cs, cs2 =>
            Maybe.bind(&2, Maybe<&2, Wa.Wasm.Segment>, Wa.Wasm.Module, seg, seg2 =>
              Maybe.bind(&2, List<&2, Wa.Wasm.Func>, Wa.Wasm.Module, Wa.Wasm.funcs.of(ts2, idx2, cs2), fs =>
                Some{Wa.Wasm.Module{fs, mem2, es2, seg2}})))))))

# a module of the six sections decodes to the items of their contents
def mod.of(+c1: List<&2, Word(8n)>, +c3: List<&2, Word(8n)>, +c5: List<&2, Word(8n)>, +c7: List<&2, Word(8n)>, +c10: List<&2, Word(8n)>, +c11: List<&2, Word(8n)>,
  +h1: {fits.bytes(c1) == True{} : Bool}, +h3: {fits.bytes(c3) == True{} : Bool}, +h5: {fits.bytes(c5) == True{} : Bool},
  +h7: {fits.bytes(c7) == True{} : Bool}, +h10: {fits.bytes(c10) == True{} : Bool}, +h11: {fits.bytes(c11) == True{} : Bool}
) -> {Wa.Wasm.decode.module(Con{Sd.Byte.from_u32(0), Con{Sd.Byte.from_u32(97), Con{Sd.Byte.from_u32(115), Con{Sd.Byte.from_u32(109), Con{Sd.Byte.from_u32(1), Con{Sd.Byte.from_u32(0), Con{Sd.Byte.from_u32(0), Con{Sd.Byte.from_u32(0), secs.bytes(c1, c3, c5, c7, c10, c11)}}}}}}}}) ==
    parts(Wa.Wasm.decode.part(~Wa.Wasm.Type, ~Wa.Wasm.decode.functype, Some{c1}),
      Wa.Wasm.decode.part(~U32, ~Wa.Wasm.decode.u32, Some{c3}),
      Wa.Wasm.decode.one(Wa.Wasm.Limits, Wa.Wasm.decode.part(~Wa.Wasm.Limits, ~Wa.Wasm.decode.limits, Some{c5})),
      Wa.Wasm.decode.part(~Wa.Wasm.Export, ~Wa.Wasm.decode.export, Some{c7}),
      Wa.Wasm.decode.part(~Wa.Wasm.Code, ~Wa.Wasm.decode.code, Some{c10}),
      Wa.Wasm.decode.one(Wa.Wasm.Segment, Wa.Wasm.decode.part(~Wa.Wasm.Segment, ~Wa.Wasm.decode.data, Some{c11}))) : Maybe<&2, Wa.Wasm.Module>}:
  +B = secs.bytes(c1, c3, c5, c7, c10, c11)
  %Equal.sym(Maybe<&2, List<&2, Wa.Wasm.Section>>, Wa.Wasm.decode.sections(List.length(&2, Word(8n), B), B),
    Some{[Wa.Wasm.Section{1, c1}, Wa.Wasm.Section{3, c3}, Wa.Wasm.Section{5, c5}, Wa.Wasm.Section{7, c7}, Wa.Wasm.Section{10, c10}, Wa.Wasm.Section{11, c11}]},
    secs.six(c1, c3, c5, c7, c10, c11, h1, h3, h5, h7, h10, h11)) :
    {Wa.Wasm.decode.module.sections(_) ==
    parts(Wa.Wasm.decode.part(~Wa.Wasm.Type, ~Wa.Wasm.decode.functype, Some{c1}),
      Wa.Wasm.decode.part(~U32, ~Wa.Wasm.decode.u32, Some{c3}),
      Wa.Wasm.decode.one(Wa.Wasm.Limits, Wa.Wasm.decode.part(~Wa.Wasm.Limits, ~Wa.Wasm.decode.limits, Some{c5})),
      Wa.Wasm.decode.part(~Wa.Wasm.Export, ~Wa.Wasm.decode.export, Some{c7}),
      Wa.Wasm.decode.part(~Wa.Wasm.Code, ~Wa.Wasm.decode.code, Some{c10}),
      Wa.Wasm.decode.one(Wa.Wasm.Segment, Wa.Wasm.decode.part(~Wa.Wasm.Segment, ~Wa.Wasm.decode.data, Some{c11}))) : Maybe<&2, Wa.Wasm.Module>}
  {==}

# The memory section
# ------------------

# a vector of one item, then the byte y
def count1(+y: Word(8n), +U: List<&2, Word(8n)>) -> {Wa.Wasm.decode.count(Con{Sd.Byte.from_u32(1), Con{y, U}}) == Some{Wa.Wasm.Decoded{1n, Con{y, U}}} : Maybe<&2, Wa.Wasm.Decoded<Nat>>}:
  %Equal.sym(Bool, Wa.Wasm.has(Con{y, U}, 1), True{}, has0(U)) :
    {Wa.Wasm.decode.count.if(_, 1, Con{y, U}) == Some{Wa.Wasm.Decoded{1n, Con{y, U}}} : Maybe<&2, Wa.Wasm.Decoded<Nat>>}
  {==}

def lim(+P: U32) -> {Wa.Wasm.decode.limits(Con{Sd.Byte.from_u32(0), Cr.Wasm.encode.uleb(P)}) == Some{Wa.Wasm.Decoded{Wa.Wasm.Limits{P, None{}}, []}} : Maybe<&2, Wa.Wasm.Decoded<Wa.Wasm.Limits>>}:
  +U = Cr.Wasm.encode.uleb(P)
  %app.nil(Word(8n), U) : {Wa.Wasm.decode.limits(Con{Sd.Byte.from_u32(0), _}) == Some{Wa.Wasm.Decoded{Wa.Wasm.Limits{P, None{}}, []}} : Maybe<&2, Wa.Wasm.Decoded<Wa.Wasm.Limits>>}
  %I.uleb.back(P, []) : {Wa.Wasm.decode.bind(U32, Wa.Wasm.Limits, _, n => r => Some{Wa.Wasm.Decoded{Wa.Wasm.Limits{n, None{}}, r}}) ==
    Some{Wa.Wasm.Decoded{Wa.Wasm.Limits{P, None{}}, []}} : Maybe<&2, Wa.Wasm.Decoded<Wa.Wasm.Limits>>}
  {==}

# the memory section's content decodes to its limits
def part.mem(+P: U32) ->
  {Wa.Wasm.decode.one(Wa.Wasm.Limits, Wa.Wasm.decode.part(~Wa.Wasm.Limits, ~Wa.Wasm.decode.limits, Some{Con{Sd.Byte.from_u32(1), Con{Sd.Byte.from_u32(0), Cr.Wasm.encode.uleb(P)}}})) ==
    Some{Some{Wa.Wasm.Limits{P, None{}}}} : Maybe<&2, Maybe<&2, Wa.Wasm.Limits>>}:
  +U = Cr.Wasm.encode.uleb(P)
  %Equal.sym(Maybe<&2, Wa.Wasm.Decoded<Nat>>, Wa.Wasm.decode.count(Con{Sd.Byte.from_u32(1), Con{Sd.Byte.from_u32(0), U}}), Some{Wa.Wasm.Decoded{1n, Con{Sd.Byte.from_u32(0), U}}}, count1(Sd.Byte.from_u32(0), U)) :
    {Wa.Wasm.decode.one(Wa.Wasm.Limits, Wa.Wasm.decode.done(List<&2, Wa.Wasm.Limits>,
      Wa.Wasm.decode.bind(Nat, List<&2, Wa.Wasm.Limits>, _, n => r => Wa.Wasm.decode.items(~Wa.Wasm.Limits, ~Wa.Wasm.decode.limits, n, r)))) ==
      Some{Some{Wa.Wasm.Limits{P, None{}}}} : Maybe<&2, Maybe<&2, Wa.Wasm.Limits>>}
  %Equal.sym(Maybe<&2, Wa.Wasm.Decoded<Wa.Wasm.Limits>>, Wa.Wasm.decode.limits(Con{Sd.Byte.from_u32(0), U}), Some{Wa.Wasm.Decoded{Wa.Wasm.Limits{P, None{}}, []}}, lim(P)) :
    {Wa.Wasm.decode.one(Wa.Wasm.Limits, Wa.Wasm.decode.done(List<&2, Wa.Wasm.Limits>,
      Wa.Wasm.decode.bind(Wa.Wasm.Limits, List<&2, Wa.Wasm.Limits>, _, x => r =>
        Wa.Wasm.decode.cons(Wa.Wasm.Limits, x, Wa.Wasm.decode.items(~Wa.Wasm.Limits, ~Wa.Wasm.decode.limits, 0n, r))))) ==
      Some{Some{Wa.Wasm.Limits{P, None{}}}} : Maybe<&2, Maybe<&2, Wa.Wasm.Limits>>}
  {==}

# The data section
# ----------------

def dbytes(+B: List<&2, Word(8n)>, +h: {fits.bytes(B) == True{} : Bool}) ->
  {Wa.Wasm.decode.bytes(Cr.Wasm.encode.sized(B)) == Some{Wa.Wasm.Decoded{B, []}} : Maybe<&2, Wa.Wasm.Decoded<List<&2, Word(8n)>>>}:
  +u = Cr.Wasm.encode.uleb(Cr.Wasm.encode.len(Word(8n), B))
  %app.nil(Word(8n), B) : {Wa.Wasm.decode.bytes(List.append(&2, Word(8n), u, _)) == Some{Wa.Wasm.Decoded{B, []}} : Maybe<&2, Wa.Wasm.Decoded<List<&2, Word(8n)>>>}
  %Equal.sym(Maybe<&2, Wa.Wasm.Decoded<Nat>>, Wa.Wasm.decode.count(List.append(&2, Word(8n), u, List.append(&2, Word(8n), B, []))),
    Some{Wa.Wasm.Decoded{List.length(&2, Word(8n), B), List.append(&2, Word(8n), B, [])}}, count.sized(B, [], h)) :
    {Wa.Wasm.decode.bind(Nat, List<&2, Word(8n)>, _, n => r => Wa.Wasm.decode.take(n, r)) == Some{Wa.Wasm.Decoded{B, []}} : Maybe<&2, Wa.Wasm.Decoded<List<&2, Word(8n)>>>}
  take.app(B, [])

def ddata(+B: List<&2, Word(8n)>, +h: {fits.bytes(B) == True{} : Bool}) ->
  {Wa.Wasm.decode.data(Con{Sd.Byte.from_u32(0), Con{Sd.Byte.from_u32(65), List.append(&2, Word(8n), Cr.Wasm.encode.sleb(20), Con{Sd.Byte.from_u32(11), Cr.Wasm.encode.sized(B)})}}) ==
    Some{Wa.Wasm.Decoded{Wa.Wasm.Segment{20, B}, []}} : Maybe<&2, Wa.Wasm.Decoded<Wa.Wasm.Segment>>}:
  %Equal.sym(Maybe<&2, Wa.Wasm.Decoded<List<&2, Word(8n)>>>, Wa.Wasm.decode.bytes(Cr.Wasm.encode.sized(B)), Some{Wa.Wasm.Decoded{B, []}}, dbytes(B, h)) :
    {Wa.Wasm.decode.bind(List<&2, Word(8n)>, Wa.Wasm.Segment, _, b => r4 => Some{Wa.Wasm.Decoded{Wa.Wasm.Segment{20, b}, r4}}) ==
      Some{Wa.Wasm.Decoded{Wa.Wasm.Segment{20, B}, []}} : Maybe<&2, Wa.Wasm.Decoded<Wa.Wasm.Segment>>}
  {==}

# the data section's content decodes to its segment
def part.data(+B: List<&2, Word(8n)>, +h: {fits.bytes(B) == True{} : Bool}) ->
  {Wa.Wasm.decode.one(Wa.Wasm.Segment, Wa.Wasm.decode.part(~Wa.Wasm.Segment, ~Wa.Wasm.decode.data,
    Some{Con{Sd.Byte.from_u32(1), Con{Sd.Byte.from_u32(0), Con{Sd.Byte.from_u32(65), List.append(&2, Word(8n), Cr.Wasm.encode.sleb(20), Con{Sd.Byte.from_u32(11), Cr.Wasm.encode.sized(B)})}}}})) ==
    Some{Some{Wa.Wasm.Segment{20, B}}} : Maybe<&2, Maybe<&2, Wa.Wasm.Segment>>}:
  +U = {Con{Sd.Byte.from_u32(65), List.append(&2, Word(8n), Cr.Wasm.encode.sleb(20), Con{Sd.Byte.from_u32(11), Cr.Wasm.encode.sized(B)})} : List<&2, Word(8n)>}
  %Equal.sym(Maybe<&2, Wa.Wasm.Decoded<Nat>>, Wa.Wasm.decode.count(Con{Sd.Byte.from_u32(1), Con{Sd.Byte.from_u32(0), U}}), Some{Wa.Wasm.Decoded{1n, Con{Sd.Byte.from_u32(0), U}}}, count1(Sd.Byte.from_u32(0), U)) :
    {Wa.Wasm.decode.one(Wa.Wasm.Segment, Wa.Wasm.decode.done(List<&2, Wa.Wasm.Segment>,
      Wa.Wasm.decode.bind(Nat, List<&2, Wa.Wasm.Segment>, _, n => r => Wa.Wasm.decode.items(~Wa.Wasm.Segment, ~Wa.Wasm.decode.data, n, r)))) ==
      Some{Some{Wa.Wasm.Segment{20, B}}} : Maybe<&2, Maybe<&2, Wa.Wasm.Segment>>}
  %Equal.sym(Maybe<&2, Wa.Wasm.Decoded<Wa.Wasm.Segment>>, Wa.Wasm.decode.data(Con{Sd.Byte.from_u32(0), U}), Some{Wa.Wasm.Decoded{Wa.Wasm.Segment{20, B}, []}}, ddata(B, h)) :
    {Wa.Wasm.decode.one(Wa.Wasm.Segment, Wa.Wasm.decode.done(List<&2, Wa.Wasm.Segment>,
      Wa.Wasm.decode.bind(Wa.Wasm.Segment, List<&2, Wa.Wasm.Segment>, _, x => r =>
        Wa.Wasm.decode.cons(Wa.Wasm.Segment, x, Wa.Wasm.decode.items(~Wa.Wasm.Segment, ~Wa.Wasm.decode.data, 0n, r))))) ==
      Some{Some{Wa.Wasm.Segment{20, B}}} : Maybe<&2, Maybe<&2, Wa.Wasm.Segment>>}
  {==}

# The code section
# ----------------

# an entry of the code section, whose code X decodes to Cd
def code.round(+X: List<&2, Word(8n)>, +rest: List<&2, Word(8n)>, -Cd: Wa.Wasm.Code, +hF: {fits.bytes(X) == True{} : Bool},
  d: {Wa.Wasm.decode.func(X) == Some{Wa.Wasm.Decoded{Cd, []}} : Maybe<&2, Wa.Wasm.Decoded<Wa.Wasm.Code>>}) ->
  {Wa.Wasm.decode.code(List.append(&2, Word(8n), Cr.Wasm.encode.sized(X), rest)) == Some{Wa.Wasm.Decoded{Cd, rest}} : Maybe<&2, Wa.Wasm.Decoded<Wa.Wasm.Code>>}:
  +u = Cr.Wasm.encode.uleb(Cr.Wasm.encode.len(Word(8n), X))
  +Y = List.append(&2, Word(8n), X, rest)
  %Equal.sym(List<&2, Word(8n)>, List.append(&2, Word(8n), List.append(&2, Word(8n), u, X), rest), List.append(&2, Word(8n), u, Y), app.assoc(Word(8n), u, X, rest)) :
    {Wa.Wasm.decode.code(_) == Some{Wa.Wasm.Decoded{Cd, rest}} : Maybe<&2, Wa.Wasm.Decoded<Wa.Wasm.Code>>}
  %Equal.sym(Maybe<&2, Wa.Wasm.Decoded<Nat>>, Wa.Wasm.decode.count(List.append(&2, Word(8n), u, Y)), Some{Wa.Wasm.Decoded{List.length(&2, Word(8n), X), Y}}, count.sized(X, rest, hF)) :
    {Wa.Wasm.decode.bind(Nat, Wa.Wasm.Code, _, n => r =>
      Wa.Wasm.decode.bind(List<&2, Word(8n)>, Wa.Wasm.Code, Wa.Wasm.decode.take(n, r), c => r2 =>
        Wa.Wasm.decode.whole(Wa.Wasm.Code, Wa.Wasm.decode.func(c), r2))) == Some{Wa.Wasm.Decoded{Cd, rest}} : Maybe<&2, Wa.Wasm.Decoded<Wa.Wasm.Code>>}
  %Equal.sym(Maybe<&2, Wa.Wasm.Decoded<List<&2, Word(8n)>>>, Wa.Wasm.decode.take(List.length(&2, Word(8n), X), Y), Some{Wa.Wasm.Decoded{X, rest}}, take.app(X, rest)) :
    {Wa.Wasm.decode.bind(List<&2, Word(8n)>, Wa.Wasm.Code, _, c => r2 =>
        Wa.Wasm.decode.whole(Wa.Wasm.Code, Wa.Wasm.decode.func(c), r2)) == Some{Wa.Wasm.Decoded{Cd, rest}} : Maybe<&2, Wa.Wasm.Decoded<Wa.Wasm.Code>>}
  %Equal.sym(Maybe<&2, Wa.Wasm.Decoded<Wa.Wasm.Code>>, Wa.Wasm.decode.func(X), Some{Wa.Wasm.Decoded{Cd, []}}, d) :
    {Wa.Wasm.decode.whole(Wa.Wasm.Code, _, rest) == Some{Wa.Wasm.Decoded{Cd, rest}} : Maybe<&2, Wa.Wasm.Decoded<Wa.Wasm.Code>>}
  {==}

# two entries hold 2 bytes
def has.two(+ya: Word(8n), +ta: List<&2, Word(8n)>, +Z: List<&2, Word(8n)>) ->
  {Wa.Wasm.has(List.append(&2, Word(8n), Cr.Wasm.encode.sized(Con{ya, ta}), Z), 2) == True{} : Bool}:
  +u = Cr.Wasm.encode.uleb(Cr.Wasm.encode.len(Word(8n), Con{ya, ta}))
  %Equal.sym(List<&2, Word(8n)>, List.append(&2, Word(8n), List.append(&2, Word(8n), u, Con{ya, ta}), Z), List.append(&2, Word(8n), u, Con{ya, List.append(&2, Word(8n), ta, Z)}),
    app.assoc(Word(8n), u, Con{ya, ta}, Z)) : {Wa.Wasm.has(_, 2) == True{} : Bool}
  I.has.uleb(Cr.Wasm.encode.len(Word(8n), Con{ya, ta}), Con{ya, List.append(&2, Word(8n), ta, Z)}, 1, {==}, has0(List.append(&2, Word(8n), ta, Z)))

# the code section's content, of two functions, decodes to their codes
def part.code(+ya: Word(8n), +ta: List<&2, Word(8n)>, +XR: List<&2, Word(8n)>, -CA: Wa.Wasm.Code, -CR: Wa.Wasm.Code,
  +hA: {fits.bytes(Con{ya, ta}) == True{} : Bool}, +hR: {fits.bytes(XR) == True{} : Bool},
  dA: {Wa.Wasm.decode.func(Con{ya, ta}) == Some{Wa.Wasm.Decoded{CA, []}} : Maybe<&2, Wa.Wasm.Decoded<Wa.Wasm.Code>>},
  dR: {Wa.Wasm.decode.func(XR) == Some{Wa.Wasm.Decoded{CR, []}} : Maybe<&2, Wa.Wasm.Decoded<Wa.Wasm.Code>>}) ->
  {Wa.Wasm.decode.part(~Wa.Wasm.Code, ~Wa.Wasm.decode.code,
    Some{Con{Sd.Byte.from_u32(2), List.append(&2, Word(8n), Cr.Wasm.encode.sized(Con{ya, ta}), List.append(&2, Word(8n), Cr.Wasm.encode.sized(XR), []))}}) ==
    Some{[CA, CR]} : Maybe<&2, List<&2, Wa.Wasm.Code>>}:
  +ZR = List.append(&2, Word(8n), Cr.Wasm.encode.sized(XR), [])
  +Y = List.append(&2, Word(8n), Cr.Wasm.encode.sized(Con{ya, ta}), ZR)
  %Equal.sym(Bool, Wa.Wasm.has(Y, 2), True{}, has.two(ya, ta, ZR)) :
    {Wa.Wasm.decode.done(List<&2, Wa.Wasm.Code>, Wa.Wasm.decode.bind(Nat, List<&2, Wa.Wasm.Code>, Wa.Wasm.decode.count.if(_, 2, Y), n => r =>
      Wa.Wasm.decode.items(~Wa.Wasm.Code, ~Wa.Wasm.decode.code, n, r))) == Some{[CA, CR]} : Maybe<&2, List<&2, Wa.Wasm.Code>>}
  %Equal.sym(Maybe<&2, Wa.Wasm.Decoded<Wa.Wasm.Code>>, Wa.Wasm.decode.code(Y), Some{Wa.Wasm.Decoded{CA, ZR}}, code.round(Con{ya, ta}, ZR, CA, hA, dA)) :
    {Wa.Wasm.decode.done(List<&2, Wa.Wasm.Code>, Wa.Wasm.decode.bind(Wa.Wasm.Code, List<&2, Wa.Wasm.Code>, _, x => r =>
      Wa.Wasm.decode.cons(Wa.Wasm.Code, x, Wa.Wasm.decode.items(~Wa.Wasm.Code, ~Wa.Wasm.decode.code, 1n, r)))) == Some{[CA, CR]} : Maybe<&2, List<&2, Wa.Wasm.Code>>}
  %Equal.sym(Maybe<&2, Wa.Wasm.Decoded<Wa.Wasm.Code>>, Wa.Wasm.decode.code(ZR), Some{Wa.Wasm.Decoded{CR, []}}, code.round(XR, [], CR, hR, dR)) :
    {Wa.Wasm.decode.done(List<&2, Wa.Wasm.Code>, Wa.Wasm.decode.cons(Wa.Wasm.Code, CA, Wa.Wasm.decode.bind(Wa.Wasm.Code, List<&2, Wa.Wasm.Code>, _, x => r =>
      Wa.Wasm.decode.cons(Wa.Wasm.Code, x, Wa.Wasm.decode.items(~Wa.Wasm.Code, ~Wa.Wasm.decode.code, 0n, r))))) == Some{[CA, CR]} : Maybe<&2, List<&2, Wa.Wasm.Code>>}
  {==}

# 0 + w = w
def Word.add0(n: Nat, w: Word(n)) -> {Word.adc(n, Word.zero(n), w, False{}, False{}) == w : Word(n)}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          Equal.cong(Word(p), Word(1n+p), x => WCon{False{}, x}, Word.adc(p, Word.zero(p), t, False{}, False{}), t, Word.add0(p, t))
        case WCon{True{}, t}:
          Equal.cong(Word(p), Word(1n+p), x => WCon{True{}, x}, Word.adc(p, Word.zero(p), t, False{}, False{}), t, Word.add0(p, t))

def U32.add0(x: U32) -> {U32.add(0, x) == x : U32}:
  match x:
    case U32{w}:
      Equal.cong(Word(32n), U32, y => U32{y}, Word.adc(32n, Word.zero(32n), w, False{}, False{}), w, Word.add0(32n, w))

# a function's code of 3 locals, whose body decodes to b
def func.three(+bs: List<&2, Word(8n)>, -b: List<&2, Wa.Wasm.Instr>,
  h: {Wa.Wasm.decode.instrs(1n+List.length(&2, Word(8n), bs), bs) == Some{Wa.Wasm.Decoded{b, []}} : Maybe<&2, Wa.Wasm.Decoded<List<&2, Wa.Wasm.Instr>>>}) ->
  {Wa.Wasm.decode.func(Con{Sd.Byte.from_u32(1), Con{Sd.Byte.from_u32(3), Con{Sd.Byte.from_u32(127), bs}}}) == Some{Wa.Wasm.Decoded{Wa.Wasm.Code{3n, b}, []}} : Maybe<&2, Wa.Wasm.Decoded<Wa.Wasm.Code>>}:
  %Equal.sym(Maybe<&2, Wa.Wasm.Decoded<List<&2, Wa.Wasm.Instr>>>, Wa.Wasm.decode.instrs(1n+List.length(&2, Word(8n), bs), bs),
    Some{Wa.Wasm.Decoded{b, []}}, h) :
    {Wa.Wasm.decode.bind(List<&2, Wa.Wasm.Instr>, Wa.Wasm.Code, _, x => r => Some{Wa.Wasm.Decoded{Wa.Wasm.Code{U32.to_nat(3), x}, r}}) ==
      Some{Wa.Wasm.Decoded{Wa.Wasm.Code{3n, b}, []}} : Maybe<&2, Wa.Wasm.Decoded<Wa.Wasm.Code>>}
  {==}

# one group of N locals, then the bytes IR
def has.locals(+N: U32, +IR: List<&2, Word(8n)>) ->
  {Wa.Wasm.has(List.append(&2, Word(8n), List.append(&2, Word(8n), Cr.Wasm.encode.uleb(N), [Sd.Byte.from_u32(127)]), IR), 1) == True{} : Bool}:
  +u = Cr.Wasm.encode.uleb(N)
  %Equal.sym(List<&2, Word(8n)>, List.append(&2, Word(8n), List.append(&2, Word(8n), u, [Sd.Byte.from_u32(127)]), IR), List.append(&2, Word(8n), u, Con{Sd.Byte.from_u32(127), IR}), app.assoc(Word(8n), u, [Sd.Byte.from_u32(127)], IR)) :
    {Wa.Wasm.has(_, 1) == True{} : Bool}
  I.has.uleb(N, Con{Sd.Byte.from_u32(127), IR}, 0, {==}, has0(Con{Sd.Byte.from_u32(127), IR}))

def local.round(+N: U32, +IR: List<&2, Word(8n)>) ->
  {Wa.Wasm.decode.local(List.append(&2, Word(8n), List.append(&2, Word(8n), Cr.Wasm.encode.uleb(N), [Sd.Byte.from_u32(127)]), IR)) == Some{Wa.Wasm.Decoded{N, IR}} : Maybe<&2, Wa.Wasm.Decoded<U32>>}:
  +u = Cr.Wasm.encode.uleb(N)
  %Equal.sym(List<&2, Word(8n)>, List.append(&2, Word(8n), List.append(&2, Word(8n), u, [Sd.Byte.from_u32(127)]), IR), List.append(&2, Word(8n), u, Con{Sd.Byte.from_u32(127), IR}), app.assoc(Word(8n), u, [Sd.Byte.from_u32(127)], IR)) :
    {Wa.Wasm.decode.local(_) == Some{Wa.Wasm.Decoded{N, IR}} : Maybe<&2, Wa.Wasm.Decoded<U32>>}
  %I.uleb.back(N, Con{Sd.Byte.from_u32(127), IR}) :
    {Wa.Wasm.decode.bind(U32, U32, _, n => r => Wa.Wasm.decode.bind(U32, U32, Wa.Wasm.decode.byte(127, r), t => r2 => Some{Wa.Wasm.Decoded{n, r2}})) ==
      Some{Wa.Wasm.Decoded{N, IR}} : Maybe<&2, Wa.Wasm.Decoded<U32>>}
  {==}

def locals.one(+N: U32, +hN: {U32.is_le(N, 50000) == True{} : Bool}) -> {Wa.Wasm.locals.sum([N], 0) == Some{N} : Maybe<&2, U32>}:
  %Equal.sym(U32, U32.add(0, N), N, U32.add0(N)) : {Wa.Wasm.locals.if(Bool.and(U32.is_le(N, 50000), U32.is_le(_, 50000)), u => Wa.Wasm.locals.sum([], _)) == Some{N} : Maybe<&2, U32>}
  %Equal.sym(Bool, U32.is_le(N, 50000), True{}, hN) : {Wa.Wasm.locals.if(Bool.and(_, _), u => Wa.Wasm.locals.sum([], N)) == Some{N} : Maybe<&2, U32>}
  {==}

# a function's code of one group of N locals, whose body decodes to b
def func.many(+N: U32, -n: Nat, +IR: List<&2, Word(8n)>, -b: List<&2, Wa.Wasm.Instr>,
  +hN: {U32.is_le(N, 50000) == True{} : Bool}, eN: {U32.to_nat(N) == n : Nat},
  h: {Wa.Wasm.decode.instrs(1n+List.length(&2, Word(8n), IR), IR) == Some{Wa.Wasm.Decoded{b, []}} : Maybe<&2, Wa.Wasm.Decoded<List<&2, Wa.Wasm.Instr>>>}) ->
  {Wa.Wasm.decode.func(Con{Sd.Byte.from_u32(1), List.append(&2, Word(8n), List.append(&2, Word(8n), Cr.Wasm.encode.uleb(N), [Sd.Byte.from_u32(127)]), IR)}) ==
    Some{Wa.Wasm.Decoded{Wa.Wasm.Code{n, b}, []}} : Maybe<&2, Wa.Wasm.Decoded<Wa.Wasm.Code>>}:
  +W = List.append(&2, Word(8n), List.append(&2, Word(8n), Cr.Wasm.encode.uleb(N), [Sd.Byte.from_u32(127)]), IR)
  %Equal.sym(Bool, Wa.Wasm.has(W, 1), True{}, has.locals(N, IR)) :
    {Wa.Wasm.decode.bind(List<&2, U32>, Wa.Wasm.Code,
      Wa.Wasm.decode.bind(Nat, List<&2, U32>, Wa.Wasm.decode.count.if(_, 1, W), n => r => Wa.Wasm.decode.items(~U32, ~Wa.Wasm.decode.local, n, r)),
      ns => r => Wa.Wasm.decode.func.body(Wa.Wasm.locals.sum(ns, 0), r)) == Some{Wa.Wasm.Decoded{Wa.Wasm.Code{n, b}, []}} : Maybe<&2, Wa.Wasm.Decoded<Wa.Wasm.Code>>}
  %Equal.sym(Maybe<&2, Wa.Wasm.Decoded<U32>>, Wa.Wasm.decode.local(W), Some{Wa.Wasm.Decoded{N, IR}}, local.round(N, IR)) :
    {Wa.Wasm.decode.bind(List<&2, U32>, Wa.Wasm.Code,
      Wa.Wasm.decode.bind(U32, List<&2, U32>, _, x => r => Wa.Wasm.decode.cons(U32, x, Wa.Wasm.decode.items(~U32, ~Wa.Wasm.decode.local, 0n, r))),
      ns => r => Wa.Wasm.decode.func.body(Wa.Wasm.locals.sum(ns, 0), r)) == Some{Wa.Wasm.Decoded{Wa.Wasm.Code{n, b}, []}} : Maybe<&2, Wa.Wasm.Decoded<Wa.Wasm.Code>>}
  %Equal.sym(Maybe<&2, U32>, Wa.Wasm.locals.sum([N], 0), Some{N}, locals.one(N, hN)) :
    {Wa.Wasm.decode.func.body(_, IR) == Some{Wa.Wasm.Decoded{Wa.Wasm.Code{n, b}, []}} : Maybe<&2, Wa.Wasm.Decoded<Wa.Wasm.Code>>}
  %Equal.sym(Maybe<&2, Wa.Wasm.Decoded<List<&2, Wa.Wasm.Instr>>>, Wa.Wasm.decode.instrs(1n+List.length(&2, Word(8n), IR), IR),
    Some{Wa.Wasm.Decoded{b, []}}, h) :
    {Wa.Wasm.decode.bind(List<&2, Wa.Wasm.Instr>, Wa.Wasm.Code, _, x => r => Some{Wa.Wasm.Decoded{Wa.Wasm.Code{U32.to_nat(N), x}, r}}) ==
      Some{Wa.Wasm.Decoded{Wa.Wasm.Code{n, b}, []}} : Maybe<&2, Wa.Wasm.Decoded<Wa.Wasm.Code>>}
  %Equal.sym(Nat, U32.to_nat(N), n, eN) : {Some{Wa.Wasm.Decoded{Wa.Wasm.Code{_, b}, []}} == Some{Wa.Wasm.Decoded{Wa.Wasm.Code{n, b}, []}} : Maybe<&2, Wa.Wasm.Decoded<Wa.Wasm.Code>>}
  {==}

# Cir.code emits no br_table
# --------------------------

def fits.expr(e: Cr.Cir.Expr, +acc: List<&2, Wa.Wasm.Instr>) -> {I.fits(Cr.Cir.code.expr(e, acc)) == I.fits(acc) : Bool}:
  match e:
    case Cr.Cir.Expr.const{n}:
      {==}
    case Cr.Cir.Expr.get{r}:
      {==}
    case Cr.Cir.Expr.op{+o, +a, +b}:
      +X = Cr.Cir.code.expr(b, Con{Cr.Cir.i.op(o), acc})
      Equal.trans(Bool, I.fits(Cr.Cir.code.expr(a, X)), I.fits(X), I.fits(acc), fits.expr(a, X), fits.expr(b, Con{Cr.Cir.i.op(o), acc}))
    case Cr.Cir.Expr.eqz{+a}:
      fits.expr(a, Con{Wa.Wasm.Instr.eqz{}, acc})
    case Cr.Cir.Expr.field{+k, +c}:
      fits.expr(c, Cr.Cir.code.at(Con{Wa.Wasm.Instr.load{U32.shln(U32.from_nat(k), 2n)}, acc}))
    case Cr.Cir.Expr.byte{+i}:
      fits.expr(i, Con{Cr.Cir.i.get(0), Con{Cr.Cir.i.op(Wa.Wasm.Op.add{}), Con{Wa.Wasm.Instr.load8_u{0}, acc}}})
    case Cr.Cir.Expr.size{}:
      {==}

def fits.result(z: Bool, +l: U32) -> {I.fits(List.append(&2, Wa.Wasm.Instr, Cr.Cir.code.result(z), [Wa.Wasm.Instr.br{l}])) == True{} : Bool}:
  match z:
    case True{}:
      {==}
    case False{}:
      {==}

def fits.stmt(s: Cr.Cir.Stmt, +d: Nat, +acc: List<&2, Wa.Wasm.Instr>) -> {I.fits(Cr.Cir.code.stmt(s, d, acc)) == I.fits(acc) : Bool}:
  match s:
    case Cr.Cir.Stmt.nop{}:
      {==}
    case Cr.Cir.Stmt.set{+r, +e}:
      fits.expr(e, Con{Cr.Cir.i.set(Cr.Cir.l.reg(r)), acc})
    case Cr.Cir.Stmt.store{+k, +c, +v}:
      +X = Cr.Cir.code.expr(v, Con{Wa.Wasm.Instr.store{U32.shln(U32.from_nat(k), 2n)}, acc})
      Equal.trans(Bool, I.fits(Cr.Cir.code.expr(c, Cr.Cir.code.at(X))), I.fits(X), I.fits(acc),
        fits.expr(c, Cr.Cir.code.at(X)), fits.expr(v, Con{Wa.Wasm.Instr.store{U32.shln(U32.from_nat(k), 2n)}, acc}))
    case Cr.Cir.Stmt.alloc{+r}:
      {==}
    case Cr.Cir.Stmt.emit{+v}:
      fits.expr(v, Con{Wa.Wasm.Instr.store8{0},
        Con{Cr.Cir.i.get(Cr.Cir.l.outn()), Con{Cr.Cir.i.const(1), Con{Cr.Cir.i.op(Wa.Wasm.Op.add{}),
          Con{Cr.Cir.i.set(Cr.Cir.l.outn()), acc}}}}})
    case Cr.Cir.Stmt.seq{+a, +b}:
      +X = Cr.Cir.code.stmt(b, d, acc)
      Equal.trans(Bool, I.fits(Cr.Cir.code.stmt(a, d, X)), I.fits(X), I.fits(acc), fits.stmt(a, d, X), fits.stmt(b, d, acc))
    case Cr.Cir.Stmt.if{+c, +t, +e}:
      +T = Cr.Cir.code.stmt(t, 2n+d, [Wa.Wasm.Instr.br{1}])
      +X = {Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{0}, T}} : List<&2, Wa.Wasm.Instr>}
      +E = Cr.Cir.code.stmt(e, 1n+d, [])
      +e1 = Equal.trans(Bool, I.fits(Cr.Cir.code.expr(c, X)), I.fits(T), True{}, fits.expr(c, X), fits.stmt(t, 2n+d, [Wa.Wasm.Instr.br{1}]))
      %Equal.sym(Bool, I.fits(Cr.Cir.code.expr(c, X)), True{}, e1) : {Bool.and(Bool.and(_, I.fits(E)), I.fits(acc)) == I.fits(acc) : Bool}
      %Equal.sym(Bool, I.fits(E), True{}, fits.stmt(e, 1n+d, [])) : {Bool.and(Bool.and(True{}, _), I.fits(acc)) == I.fits(acc) : Bool}
      {==}
    case Cr.Cir.Stmt.while{+c, +body}:
      +T = Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])
      +X = {Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{1}, T}} : List<&2, Wa.Wasm.Instr>}
      +e1 = Equal.trans(Bool, I.fits(Cr.Cir.code.expr(c, X)), I.fits(T), True{}, fits.expr(c, X), fits.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}]))
      %Equal.sym(Bool, I.fits(Cr.Cir.code.expr(c, X)), True{}, e1) : {Bool.and(Bool.and(_, True{}), I.fits(acc)) == I.fits(acc) : Bool}
      {==}
    case Cr.Cir.Stmt.halt{+s}:
      %Equal.sym(Bool, I.fits(List.append(&2, Wa.Wasm.Instr, Cr.Cir.code.result(U32.is_zero(s)), [Wa.Wasm.Instr.br{U32.from_nat(1n+d)}])), True{},
        fits.result(U32.is_zero(s), U32.from_nat(1n+d))) : {Bool.and(_, I.fits(acc)) == I.fits(acc) : Bool}
      {==}

# The module
# ----------

def body(f: Wa.Wasm.Func) -> List<&2, Wa.Wasm.Instr>:
  match f:
    case Wa.Wasm.Func{_, _, _, b}:
      b

def fits.alloc(+k: U32) -> {I.fits(body(Cr.Cir.alloc(k))) == True{} : Bool}:
  {==}

def fits.run(+prog: Cr.Cir.Stmt, +regs: Nat, +k: U32) -> {I.fits(body(Cr.Cir.run(prog, regs, k))) == True{} : Bool}:
  %Equal.sym(Bool, I.fits(Cr.Cir.code.stmt(prog, 0n, [])), True{}, fits.stmt(prog, 0n, [])) : {Bool.and(_, True{}) == True{} : Bool}
  {==}

# the code of alloc, after its size
def XA(+k: U32) -> List<&2, Word(8n)>:
  Con{Sd.Byte.from_u32(1), Con{Sd.Byte.from_u32(3), Con{Sd.Byte.from_u32(127), Cr.Wasm.encode.instrs(body(Cr.Cir.alloc(k)), [Sd.Byte.from_u32(11)])}}}

# the code of run, after its size
def XR(+prog: Cr.Cir.Stmt, +regs: Nat, +k: U32) -> List<&2, Word(8n)>:
  Con{Sd.Byte.from_u32(1), List.append(&2, Word(8n), List.append(&2, Word(8n), Cr.Wasm.encode.uleb(U32.from_nat(6n+regs)), [Sd.Byte.from_u32(127)]),
    Cr.Wasm.encode.instrs(body(Cr.Cir.run(prog, regs, k)), [Sd.Byte.from_u32(11)]))}

def c10(+prog: Cr.Cir.Stmt, +regs: Nat, +k: U32) -> List<&2, Word(8n)>:
  Con{Sd.Byte.from_u32(2), List.append(&2, Word(8n), Cr.Wasm.encode.sized(XA(k)), List.append(&2, Word(8n), Cr.Wasm.encode.sized(XR(prog, regs, k)), []))}

def c11(+cells: List<&2, Cr.Cir.Cell>) -> List<&2, Word(8n)>:
  Con{Sd.Byte.from_u32(1), Con{Sd.Byte.from_u32(0), Con{Sd.Byte.from_u32(65), List.append(&2, Word(8n), Cr.Wasm.encode.sleb(20), Con{Sd.Byte.from_u32(11), Cr.Wasm.encode.sized(Cr.Cir.bytes(cells))})}}}

def c5(+k: U32) -> List<&2, Word(8n)>:
  Con{Sd.Byte.from_u32(1), Con{Sd.Byte.from_u32(0), Cr.Wasm.encode.uleb(Cr.Cir.pages(Cr.Cir.input.at(k)))}}

def fs(+prog: Cr.Cir.Stmt, +regs: Nat, +k: U32) -> List<&2, Wa.Wasm.Func>:
  [Cr.Cir.alloc(k), Cr.Cir.run(prog, regs, k)]

def es() -> List<&2, Wa.Wasm.Export>:
  [Wa.Wasm.Export.memory{Wa.Wasm.name.memory()}, Wa.Wasm.Export.func{Wa.Wasm.name.alloc(), 0}, Wa.Wasm.Export.func{Wa.Wasm.name.run(), 1}]

def c1(+prog: Cr.Cir.Stmt, +regs: Nat, +k: U32) -> List<&2, Word(8n)>:
  Cr.Wasm.encode.vec(2, Cr.Wasm.encode.functypes(fs(prog, regs, k)))

def c3(+prog: Cr.Cir.Stmt, +regs: Nat, +k: U32) -> List<&2, Word(8n)>:
  Cr.Wasm.encode.vec(2, Cr.Wasm.encode.indices(fs(prog, regs, k), 0))

def c7() -> List<&2, Word(8n)>:
  Cr.Wasm.encode.vec(3, Cr.Wasm.encode.exports(es()))

def enc(+prog: Cr.Cir.Stmt, +regs: Nat, +cells: List<&2, Cr.Cir.Cell>) ->
  {Cr.Wasm.encode(Cr.Cir.module(prog, regs, cells)) ==
    Con{Sd.Byte.from_u32(0), Con{Sd.Byte.from_u32(97), Con{Sd.Byte.from_u32(115), Con{Sd.Byte.from_u32(109), Con{Sd.Byte.from_u32(1), Con{Sd.Byte.from_u32(0), Con{Sd.Byte.from_u32(0), Con{Sd.Byte.from_u32(0),
      secs.bytes(c1(prog, regs, Cr.Wasm.encode.len(Cr.Cir.Cell, cells)), c3(prog, regs, Cr.Wasm.encode.len(Cr.Cir.Cell, cells)),
        c5(Cr.Wasm.encode.len(Cr.Cir.Cell, cells)), c7(), c10(prog, regs, Cr.Wasm.encode.len(Cr.Cir.Cell, cells)), c11(cells))}}}}}}}} : List<&2, Word(8n)>}:
  {==}

def round.of(+prog: Cr.Cir.Stmt, +regs: Nat, +cells: List<&2, Cr.Cir.Cell>,
  +h5: {fits.bytes(c5(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))) == True{} : Bool},
  +h10: {fits.bytes(c10(prog, regs, Cr.Wasm.encode.len(Cr.Cir.Cell, cells))) == True{} : Bool},
  +h11: {fits.bytes(c11(cells)) == True{} : Bool},
  +hA: {fits.bytes(XA(Cr.Wasm.encode.len(Cr.Cir.Cell, cells))) == True{} : Bool},
  +hR: {fits.bytes(XR(prog, regs, Cr.Wasm.encode.len(Cr.Cir.Cell, cells))) == True{} : Bool},
  +hB: {fits.bytes(Cr.Cir.bytes(cells)) == True{} : Bool},
  +hN: {U32.is_le(U32.from_nat(6n+regs), 50000) == True{} : Bool},
  eN: {U32.to_nat(U32.from_nat(6n+regs)) == 6n+regs : Nat}
) -> {Wa.Wasm.decode.module(Cr.Wasm.encode(Cr.Cir.module(prog, regs, cells))) == Some{Cr.Cir.module(prog, regs, cells)} : Maybe<&2, Wa.Wasm.Module>}:
  +k = Cr.Wasm.encode.len(Cr.Cir.Cell, cells)
  +M = Cr.Cir.module(prog, regs, cells)
  +A = Cr.Cir.alloc(k)
  +R = Cr.Cir.run(prog, regs, k)
  +IA = Cr.Wasm.encode.instrs(body(A), [Sd.Byte.from_u32(11)])
  +IR = Cr.Wasm.encode.instrs(body(R), [Sd.Byte.from_u32(11)])
  +N = U32.from_nat(6n+regs)
  +CA = {Wa.Wasm.Code{3n, body(A)} : Wa.Wasm.Code}
  +CR = {Wa.Wasm.Code{6n+regs, body(R)} : Wa.Wasm.Code}
  +dA = func.three(IA, body(A), I.instrs.round(body(A), fits.alloc(k)))
  +dR = func.many(N, 6n+regs, IR, body(R), hN, eN, I.instrs.round(body(R), fits.run(prog, regs, k)))
  +p10 = part.code(Sd.Byte.from_u32(1), {Con{Sd.Byte.from_u32(3), Con{Sd.Byte.from_u32(127), IA}} : List<&2, Word(8n)>}, XR(prog, regs, k), CA, CR, hA, hR, dA, dR)
  +p5 = part.mem(Cr.Cir.pages(Cr.Cir.input.at(k)))
  +p11 = part.data(Cr.Cir.bytes(cells), hB)
  +q1 = Wa.Wasm.decode.part(~Wa.Wasm.Type, ~Wa.Wasm.decode.functype, Some{c1(prog, regs, k)})
  +q3 = Wa.Wasm.decode.part(~U32, ~Wa.Wasm.decode.u32, Some{c3(prog, regs, k)})
  +q7 = Wa.Wasm.decode.part(~Wa.Wasm.Export, ~Wa.Wasm.decode.export, Some{c7()})
  +q5 = Wa.Wasm.decode.one(Wa.Wasm.Limits, Wa.Wasm.decode.part(~Wa.Wasm.Limits, ~Wa.Wasm.decode.limits, Some{c5(k)}))
  +q10 = Wa.Wasm.decode.part(~Wa.Wasm.Code, ~Wa.Wasm.decode.code, Some{c10(prog, regs, k)})
  +q11 = Wa.Wasm.decode.one(Wa.Wasm.Segment, Wa.Wasm.decode.part(~Wa.Wasm.Segment, ~Wa.Wasm.decode.data, Some{c11(cells)}))
  +m = mod.of(c1(prog, regs, k), c3(prog, regs, k), c5(k), c7(), c10(prog, regs, k), c11(cells), {==}, {==}, h5, {==}, h10, h11)
  +L5 = {Some{Some{Wa.Wasm.Limits{Cr.Cir.pages(Cr.Cir.input.at(k)), None{}}}} : Maybe<&2, Maybe<&2, Wa.Wasm.Limits>>}
  +L10 = {Some{[CA, CR]} : Maybe<&2, List<&2, Wa.Wasm.Code>>}
  +L11 = {Some{Some{Wa.Wasm.Segment{20, Cr.Cir.bytes(cells)}}} : Maybe<&2, Maybe<&2, Wa.Wasm.Segment>>}
  +rest = {(
    %Equal.sym(Maybe<&2, Maybe<&2, Wa.Wasm.Limits>>, q5, L5, p5) : {parts(q1, q3, _, q7, q10, q11) == Some{M} : Maybe<&2, Wa.Wasm.Module>}
    %Equal.sym(Maybe<&2, List<&2, Wa.Wasm.Code>>, q10, L10, p10) : {parts(q1, q3, L5, q7, _, q11) == Some{M} : Maybe<&2, Wa.Wasm.Module>}
    %Equal.sym(Maybe<&2, Maybe<&2, Wa.Wasm.Segment>>, q11, L11, p11) : {parts(q1, q3, L5, q7, L10, _) == Some{M} : Maybe<&2, Wa.Wasm.Module>}
    {==}) : {parts(q1, q3, q5, q7, q10, q11) == Some{M} : Maybe<&2, Wa.Wasm.Module>}}
  Equal.trans(Maybe<&2, Wa.Wasm.Module>, Wa.Wasm.decode.module(Cr.Wasm.encode(M)), parts(q1, q3, q5, q7, q10, q11), Some{M}, m, rest)

# Sizes
# -----

def ulen.if(c: Bool, +b: U32, +f: Nat, +r: U32, ih: N.Le(List.length(&2, Word(8n), Cr.Wasm.encode.uleb.go(f, r)), f)) ->
  N.Le(List.length(&2, Word(8n), Cr.Wasm.encode.leb.if(c, b, u => Cr.Wasm.encode.uleb.go(f, r))), 1n+f):
  match c:
    case True{}:
      N.le_zero(f)
    case False{}:
      ih

# the unsigned LEB128 bytes of k rounds are at most k
def ulen(+k: Nat, +v: U32) -> N.Le(List.length(&2, Word(8n), Cr.Wasm.encode.uleb.go(k, v)), k):
  match k:
    case 0n:
      Unit{}
    case 1n+f:
      +r = U32.shrn(v, 7n)
      ulen.if(U32.is_zero(r), U32.and(v, 127), f, r, ulen(f, r))

# a < b as a <= b
def lt_le(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> N.Le(1n+a, b):
  match a b:
    case 0n 0n:
      L.ft(N.Le(1n, 0n), h)
    case 0n 1n+q:
      N.le_zero(q)
    case 1n+p 0n:
      L.ft(N.Le(2n+p, 0n), h)
    case 1n+p 1n+q:
      lt_le(p, q, h)

# a <= b gives 2^k a <= 2^k b
def D_mono(+k: Nat, +a: Nat, +b: Nat, h: N.Le(a, b)) -> N.Le(N.D(k, a), N.D(k, b)):
  match k:
    case 0n:
      h
    case 1n+q:
      N.double_mono(N.D(q, a), N.D(q, b), D_mono(q, a, b, h))

# 1 <= y gives 1 + y <= 2y
def lt_double(+y: Nat, h: N.Le(1n, y)) -> N.Le(1n+y, Nat.double(y)):
  match y:
    case 0n:
      Empty.absurd(N.Le(1n, 0n), h)
    case 1n+p:
      G.le_double(p)

# the bytes of the cells: at most 32 for each
def bytes.le(cs: List<&2, Cr.Cir.Cell>) -> N.Le(List.length(&2, Word(8n), Cr.Cir.bytes(cs)), N.D(5n, List.length(&2, Cr.Cir.Cell, cs))):
  match cs:
    case Nil{}:
      Unit{}
    case Con{Cr.Cir.Cell{a, b, c, d, e}, +rest}:
      N.add_mono(20n, 32n, List.length(&2, Word(8n), Cr.Cir.bytes(rest)), N.D(5n, List.length(&2, Cr.Cir.Cell, rest)), Unit{}, bytes.le(rest))

# the number of n, as a U32, is n, when n <= M
def tofrom(+n: Nat, +M: U32, +h: N.Le(n, U32.to_nat(M))) -> {U32.to_nat(U32.from_nat(n)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      +x = U32.from_nat(p)
      +ih = tofrom(p, M, N.weaken(p, U32.to_nat(M), h))
      +h2 = N.le_rw_l(1n+p, 1n+U32.to_nat(x), U32.to_nat(M), Equal.cong(Nat, Nat, q => 1n+q, p, U32.to_nat(x), Equal.sym(Nat, U32.to_nat(x), p, ih)), h)
      +e = I.U32.inc_nat(x, Equal.sym(Bool, U32.is_zero(U32.inc(x)), False{}, nz(x, M, h2)))
      Equal.trans(Nat, U32.to_nat(U32.inc(x)), 1n+U32.to_nat(x), 1n+p, e, Equal.cong(Nat, Nat, q => 1n+q, U32.to_nat(x), p, ih))

# x <= y makes the comparison at most EQ
def le_true(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), h: N.Le(x, y)) -> {Cmp.is_le(c) == True{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({False{} == True{} : Bool}, N.not_succ_le(y, N.le_trans(1n+y, x, y, r, h)))

# X sits inside u, X, then Z
def le.mid(+u: List<&2, Word(8n)>, +X: List<&2, Word(8n)>, +Z: List<&2, Word(8n)>) ->
  N.Le(List.length(&2, Word(8n), X), List.length(&2, Word(8n), List.append(&2, Word(8n), List.append(&2, Word(8n), u, X), Z))):
  +lu = List.length(&2, Word(8n), u)
  +lx = List.length(&2, Word(8n), X)
  +ux = List.append(&2, Word(8n), u, X)
  +lux = List.length(&2, Word(8n), ux)
  N.le_trans(lx, lux, List.length(&2, Word(8n), List.append(&2, Word(8n), ux, Z)),
    N.le_rw_r(lx, Nat.add(lu, lx), lux, Equal.sym(Nat, lux, Nat.add(lu, lx), len.app(Word(8n), u, X)), N.le_add_l(lu, lx)),
    N.le_rw_r(lux, Nat.add(lux, List.length(&2, Word(8n), Z)), List.length(&2, Word(8n), List.append(&2, Word(8n), ux, Z)),
      Equal.sym(Nat, List.length(&2, Word(8n), List.append(&2, Word(8n), ux, Z)), Nat.add(lux, List.length(&2, Word(8n), Z)), len.app(Word(8n), ux, Z)),
      N.le_add_r(lux, List.length(&2, Word(8n), Z))))

# X sits at the end of P, X
def le.tail(+P: List<&2, Word(8n)>, +X: List<&2, Word(8n)>) -> N.Le(List.length(&2, Word(8n), X), List.length(&2, Word(8n), List.append(&2, Word(8n), P, X))):
  +lp = List.length(&2, Word(8n), P)
  +lx = List.length(&2, Word(8n), X)
  N.le_rw_r(lx, Nat.add(lp, lx), List.length(&2, Word(8n), List.append(&2, Word(8n), P, X)),
    Equal.sym(Nat, List.length(&2, Word(8n), List.append(&2, Word(8n), P, X)), Nat.add(lp, lx), len.app(Word(8n), P, X)), N.le_add_l(lp, lx))

def codes(+prog: Cr.Cir.Stmt, +regs: Nat, +k: U32) -> List<&2, Word(8n)>:
  Cr.Wasm.encode.codes([Cr.Cir.alloc(k), Cr.Cir.run(prog, regs, k)])

def fits.c10(+prog: Cr.Cir.Stmt, +regs: Nat, +k: U32, +M: U32, +h: N.Le(1n+List.length(&2, Word(8n), codes(prog, regs, k)), U32.to_nat(M))) ->
  {fits.bytes(c10(prog, regs, k)) == True{} : Bool}:
  fits.of_le(c10(prog, regs, k), M, h)

def fits.XA(+prog: Cr.Cir.Stmt, +regs: Nat, +k: U32, +M: U32, +h: N.Le(1n+List.length(&2, Word(8n), codes(prog, regs, k)), U32.to_nat(M))) ->
  {fits.bytes(XA(k)) == True{} : Bool}:
  +ZR = List.append(&2, Word(8n), Cr.Wasm.encode.sized(XR(prog, regs, k)), [])
  +Y = List.append(&2, Word(8n), Cr.Wasm.encode.sized(XA(k)), ZR)
  fits.of_le(XA(k), M, N.le_trans(List.length(&2, Word(8n), XA(k)), List.length(&2, Word(8n), Y), U32.to_nat(M),
    le.mid(Cr.Wasm.encode.uleb(Cr.Wasm.encode.len(Word(8n), XA(k))), XA(k), ZR), N.weaken(List.length(&2, Word(8n), Y), U32.to_nat(M), h)))

def fits.XR(+prog: Cr.Cir.Stmt, +regs: Nat, +k: U32, +M: U32, +h: N.Le(1n+List.length(&2, Word(8n), codes(prog, regs, k)), U32.to_nat(M))) ->
  {fits.bytes(XR(prog, regs, k)) == True{} : Bool}:
  +X = XR(prog, regs, k)
  +ZR = List.append(&2, Word(8n), Cr.Wasm.encode.sized(X), [])
  +Y = List.append(&2, Word(8n), Cr.Wasm.encode.sized(XA(k)), ZR)
  fits.of_le(X, M, N.le_trans(List.length(&2, Word(8n), X), List.length(&2, Word(8n), Y), U32.to_nat(M),
    N.le_trans(List.length(&2, Word(8n), X), List.length(&2, Word(8n), ZR), List.length(&2, Word(8n), Y),
      le.mid(Cr.Wasm.encode.uleb(Cr.Wasm.encode.len(Word(8n), X)), X, []), le.tail(Cr.Wasm.encode.sized(XA(k)), ZR)),
    N.weaken(List.length(&2, Word(8n), Y), U32.to_nat(M), h)))

# the memory section's content: at most 7 bytes
def fits.c5(+k: U32) -> {fits.bytes(c5(k)) == True{} : Bool}:
  +P = Cr.Cir.pages(Cr.Cir.input.at(k))
  +x = List.length(&2, Word(8n), Cr.Wasm.encode.uleb(P))
  fits.of_le(c5(k), 255, N.le_trans(2n+x, 7n, U32.to_nat(255), ulen(5n, P), Unit{}))

# 4294967295 is the word of 32 set bits
def lit_MAX() -> {4294967295 == U32{N.ones(32n, 32n)} : U32}:
  {==}

# 1 + 4294967295 = 2^32
def val_MAX() -> {1n+U32.to_nat(4294967295) == N.D(32n, 1n) : Nat}:
  %Equal.sym(U32, 4294967295, U32{N.ones(32n, 32n)}, lit_MAX()) : {1n+U32.to_nat(_) == N.D(32n, 1n) : Nat}
  %Equal.sym(Nat, U32.to_nat(U32{N.ones(32n, 32n)}), Word.to_nat(32n, N.ones(32n, 32n)), N.u32_to_nat(N.ones(32n, 32n))) : {1n+_ == N.D(32n, 1n) : Nat}
  N.ones_val(32n, 32n, Unit{})

def step32(+a: Nat, +b: Nat, h: N.Le(a, 5n+b)) -> N.Le(5n+a, 32n+b):
  N.le_trans(a, 5n+b, 27n+b, h, N.le_add_l(22n, b))

# y <= M, when 1 + M = 2y and 1 <= y
def le.half(+y: Nat, +m: Nat, vm: {1n+m == Nat.double(y) : Nat}, hy: N.Le(1n, y)) -> N.Le(y, m):
  N.le_rw_r(1n+y, Nat.double(y), 1n+m, Equal.sym(Nat, 1n+m, Nat.double(y), vm), lt_double(y, hy))

# 2^q <= M, when 1 + M = 2^(1 + q)
def le.pow(+q: Nat, +m: Nat, vm: {1n+m == N.D(1n+q, 1n) : Nat}) -> N.Le(N.D(q, 1n), m):
  le.half(N.D(q, 1n), m, vm, G.D_ge(q, 1n))

# the data section's content, of fewer than h26 cells (to_nat(K) = h26), has
# at most y31 = 2^5 h26 <= M bytes
def le.c11(+cells: List<&2, Cr.Cir.Cell>, +K: U32, +M: U32, +h26: Nat, +y31: Nat,
  vK: {U32.to_nat(K) == h26 : Nat}, e31: {N.D(5n, h26) == y31 : Nat}, l31: N.Le(y31, U32.to_nat(M)),
  hL: N.Le(1n+List.length(&2, Cr.Cir.Cell, cells), U32.to_nat(K))) -> N.Le(List.length(&2, Word(8n), c11(cells)), U32.to_nat(M)):
  +B = Cr.Cir.bytes(cells)
  +l = List.length(&2, Cr.Cir.Cell, cells)
  +u = Cr.Wasm.encode.uleb(Cr.Wasm.encode.len(Word(8n), B))
  +x = List.length(&2, Word(8n), u)
  +y = List.length(&2, Word(8n), B)
  +d5 = N.D(5n, l)
  +a = List.length(&2, Word(8n), List.append(&2, Word(8n), u, B))
  +s3 = N.add_mono(x, 5n, y, d5, ulen(5n, Cr.Wasm.encode.len(Word(8n), B)), bytes.le(cells))
  +s4 = N.le_rw_l(Nat.add(x, y), a, Nat.add(5n, d5), Equal.sym(Nat, a, Nat.add(x, y), len.app(Word(8n), u, B)), s3)
  +s45 = {step32(a, d5, s4) : N.Le(5n+a, N.D(5n, 1n+l))}
  +s5 = D_mono(5n, 1n+l, h26, N.le_rw_r(1n+l, U32.to_nat(K), h26, vK, hL))
  +s6 = N.le_rw_r(5n+a, N.D(5n, h26), y31, e31, N.le_trans(5n+a, N.D(5n, 1n+l), N.D(5n, h26), s45, s5))
  N.le_trans(5n+a, y31, U32.to_nat(M), s6, l31)

def fits.B(+cells: List<&2, Cr.Cir.Cell>, +M: U32, +h: N.Le(List.length(&2, Word(8n), c11(cells)), U32.to_nat(M))) ->
  {fits.bytes(Cr.Cir.bytes(cells)) == True{} : Bool}:
  +B = Cr.Cir.bytes(cells)
  +u = Cr.Wasm.encode.uleb(Cr.Wasm.encode.len(Word(8n), B))
  +a = List.length(&2, Word(8n), List.append(&2, Word(8n), u, B))
  fits.of_le(B, M, N.le_trans(List.length(&2, Word(8n), B), a, U32.to_nat(M), le.tail(u, B),
    N.le_trans(a, 5n+a, U32.to_nat(M), N.le_add_l(5n, a), h)))

# the round trip, with the limits as variables: K = 2^26 cells, M = 2^32 - 1
# bytes, W = 50000 locals
def round.sized(+prog: Cr.Cir.Stmt, +regs: Nat, +cells: List<&2, Cr.Cir.Cell>, +K: U32, +M: U32, +W: U32,
  vK: {U32.to_nat(K) == N.D(26n, 1n) : Nat}, vM: {1n+U32.to_nat(M) == N.D(32n, 1n) : Nat}, eW: {W == 50000 : U32},
  hc: N.Le(1n+List.length(&2, Cr.Cir.Cell, cells), U32.to_nat(K)),
  +hr: N.Le(6n+regs, U32.to_nat(W)),
  +hs: N.Le(1n+List.length(&2, Word(8n), Cr.Wasm.encode.codes([Cr.Cir.alloc(Cr.Wasm.encode.len(Cr.Cir.Cell, cells)),
    Cr.Cir.run(prog, regs, Cr.Wasm.encode.len(Cr.Cir.Cell, cells))])), U32.to_nat(M))
) -> {Wa.Wasm.decode.module(Cr.Wasm.encode(Cr.Cir.module(prog, regs, cells))) == Some{Cr.Cir.module(prog, regs, cells)} : Maybe<&2, Wa.Wasm.Module>}:
  +k = Cr.Wasm.encode.len(Cr.Cir.Cell, cells)
  +N = U32.from_nat(6n+regs)
  +l31 = le.pow(31n, U32.to_nat(M), vM)
  +h11 = le.c11(cells, K, M, N.D(26n, 1n), N.D(31n, 1n), vK, N.D_add(5n, 26n, 31n, 1n, {==}), l31, hc)
  +eN = tofrom(6n+regs, W, hr)
  +hNW = le_true(U32.cmp(N, W), U32.to_nat(N), U32.to_nat(W), N.U32.rel(N, W),
    N.le_rw_l(6n+regs, U32.to_nat(N), U32.to_nat(W), Equal.sym(Nat, U32.to_nat(N), 6n+regs, eN), hr))
  +hN = {(%eW : {U32.is_le(N, _) == True{} : Bool}; hNW) : {U32.is_le(N, 50000) == True{} : Bool}}
  round.of(prog, regs, cells, fits.c5(k), fits.c10(prog, regs, k, M, hs), fits.of_le(c11(cells), M, h11),
    fits.XA(prog, regs, k, M, hs), fits.XR(prog, regs, k, M, hs), fits.B(cells, M, h11), hN, eN)

# The round trip
# --------------
#
# Wasm.decode.module reads back the module of Cir.module that Wasm.encode
# writes, when it has fewer than 2^26 cells, at most 50000 locals in run, and
# a code section of fewer than 2^32 - 1 bytes. The program needs no premise:
# Cir.code.stmt emits no br_table (fits.stmt).
def module.round(+prog: Cr.Cir.Stmt, +regs: Nat, +cells: List<&2, Cr.Cir.Cell>,
  hc: {Nat.is_lt(List.length(&2, Cr.Cir.Cell, cells), U32.to_nat(67108864)) == True{} : Bool},
  +hr: {Nat.is_le(6n+regs, U32.to_nat(50000)) == True{} : Bool},
  hs: {Nat.is_lt(List.length(&2, Word(8n), Cr.Wasm.encode.codes([Cr.Cir.alloc(Cr.Wasm.encode.len(Cr.Cir.Cell, cells)),
    Cr.Cir.run(prog, regs, Cr.Wasm.encode.len(Cr.Cir.Cell, cells))])), U32.to_nat(4294967295)) == True{} : Bool}
) -> {Wa.Wasm.decode.module(Cr.Wasm.encode(Cr.Cir.module(prog, regs, cells))) == Some{Cr.Cir.module(prog, regs, cells)} : Maybe<&2, Wa.Wasm.Module>}:
  round.sized(prog, regs, cells, 67108864, 4294967295, 50000, G.val_M2(), val_MAX(), {==},
    lt_le(List.length(&2, Cr.Cir.Cell, cells), U32.to_nat(67108864), hc),
    N.toLe(6n+regs, U32.to_nat(50000), hr),
    lt_le(List.length(&2, Word(8n), Cr.Wasm.encode.codes([Cr.Cir.alloc(Cr.Wasm.encode.len(Cr.Cir.Cell, cells)), Cr.Cir.run(prog, regs, Cr.Wasm.encode.len(Cr.Cir.Cell, cells))])), U32.to_nat(4294967295), hs))
