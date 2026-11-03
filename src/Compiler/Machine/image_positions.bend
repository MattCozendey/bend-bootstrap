# compiler: where Img.go puts a term's cells (layer B)
# ====================================================
#
# Img.go lays a term's cells out backwards from the cell upto, in pre-order:
# its root is as many cells before upto as the term has nodes. Counted
# forwards (Up, n cells past a cell), the nodes of t past its root are upto
# (go.at.up, with PG.Nsz's count, whose order is Img.go's), and Img.size
# counts them (size.up), so the body that Img.bodies lays out at the cell at
# has its root at at (body.at). The only arithmetic of words: an addition
# of one more is one more (W1), and (x - 1) + 1 = x.

import Base
import ../../Book/impl.bend as Bk
import ../Cir/impl.bend as Cr
import ./impl.bend as Mc
import ../img_small.bend as PG
import ../Cir/instrs_round_trip.bend as PI
import ./image_layout.bend as IL

# Words
# -----

# a carry in is one more
def W2(n: Nat, a: Word(n), b: Word(n)) -> {Word.adc(n, a, b, False{}, True{}) == Word.inc(n, Word.adc(n, a, b, False{}, False{})) : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+(+p):
      match a b:
        case WCon{False{}, +x} WCon{False{}, +y}:
          {==}
        case WCon{False{}, +x} WCon{True{}, +y}:
          Equal.cong(Word(p), Word(1n+p), z => WCon{False{}, z}, Word.adc(p, x, y, False{}, True{}), Word.inc(p, Word.adc(p, x, y, False{}, False{})), W2(p, x, y))
        case WCon{True{}, +x} WCon{False{}, +y}:
          Equal.cong(Word(p), Word(1n+p), z => WCon{False{}, z}, Word.adc(p, x, y, False{}, True{}), Word.inc(p, Word.adc(p, x, y, False{}, False{})), W2(p, x, y))
        case WCon{True{}, +x} WCon{True{}, +y}:
          {==}

# a + (b + 1) = (a + b) + 1, with any carry in
def W1(n: Nat, a: Word(n), b: Word(n), c: Bool) -> {Word.adc(n, a, Word.inc(n, b), False{}, c) == Word.inc(n, Word.adc(n, a, b, False{}, c)) : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+(+p):
      match a b c:
        case WCon{False{}, +x} WCon{False{}, +y} False{}:
          {==}
        case WCon{False{}, +x} WCon{False{}, +y} True{}:
          Equal.cong(Word(p), Word(1n+p), z => WCon{False{}, z}, Word.adc(p, x, y, False{}, True{}), Word.inc(p, Word.adc(p, x, y, False{}, False{})), W2(p, x, y))
        case WCon{True{}, +x} WCon{False{}, +y} False{}:
          Equal.cong(Word(p), Word(1n+p), z => WCon{False{}, z}, Word.adc(p, x, y, False{}, True{}), Word.inc(p, Word.adc(p, x, y, False{}, False{})), W2(p, x, y))
        case WCon{True{}, +x} WCon{False{}, +y} True{}:
          {==}
        case WCon{False{}, +x} WCon{True{}, +y} False{}:
          Equal.cong(Word(p), Word(1n+p), z => WCon{False{}, z}, Word.adc(p, x, Word.inc(p, y), False{}, False{}), Word.inc(p, Word.adc(p, x, y, False{}, False{})), W1(p, x, y, False{}))
        case WCon{False{}, +x} WCon{True{}, +y} True{}:
          Equal.cong(Word(p), Word(1n+p), z => WCon{True{}, z}, Word.adc(p, x, Word.inc(p, y), False{}, False{}), Word.adc(p, x, y, False{}, True{}),
            Equal.trans(Word(p), Word.adc(p, x, Word.inc(p, y), False{}, False{}), Word.inc(p, Word.adc(p, x, y, False{}, False{})), Word.adc(p, x, y, False{}, True{}),
              W1(p, x, y, False{}), Equal.sym(Word(p), Word.adc(p, x, y, False{}, True{}), Word.inc(p, Word.adc(p, x, y, False{}, False{})), W2(p, x, y))))
        case WCon{True{}, +x} WCon{True{}, +y} False{}:
          Equal.cong(Word(p), Word(1n+p), z => WCon{True{}, z}, Word.adc(p, x, Word.inc(p, y), False{}, False{}), Word.adc(p, x, y, False{}, True{}),
            Equal.trans(Word(p), Word.adc(p, x, Word.inc(p, y), False{}, False{}), Word.inc(p, Word.adc(p, x, y, False{}, False{})), Word.adc(p, x, y, False{}, True{}),
              W1(p, x, y, False{}), Equal.sym(Word(p), Word.adc(p, x, y, False{}, True{}), Word.inc(p, Word.adc(p, x, y, False{}, False{})), W2(p, x, y))))
        case WCon{True{}, +x} WCon{True{}, +y} True{}:
          Equal.cong(Word(p), Word(1n+p), z => WCon{False{}, z}, Word.adc(p, x, Word.inc(p, y), False{}, True{}), Word.inc(p, Word.adc(p, x, y, False{}, True{})), W1(p, x, y, True{}))

# a + 0 = a
def W3(n: Nat, a: Word(n)) -> {Word.adc(n, a, Word.zero(n), False{}, False{}) == a : Word(n)}:
  match n:
    case 0n:
      match a:
        case WNil{}:
          {==}
    case 1n+(+p):
      match a:
        case WCon{False{}, +x}:
          Equal.cong(Word(p), Word(1n+p), z => WCon{False{}, z}, Word.adc(p, x, Word.zero(p), False{}, False{}), x, W3(p, x))
        case WCon{True{}, +x}:
          Equal.cong(Word(p), Word(1n+p), z => WCon{True{}, z}, Word.adc(p, x, Word.zero(p), False{}, False{}), x, W3(p, x))

def add.inc(+a: U32, +b: U32) -> {U32.add(a, U32.inc(b)) == U32.inc(U32.add(a, b)) : U32}:
  match a b:
    case U32{+x} U32{+y}:
      Equal.cong(Word(32n), U32, z => U32{z}, Word.adc(32n, x, Word.inc(32n, y), False{}, False{}), Word.inc(32n, Word.adc(32n, x, y, False{}, False{})),
        W1(32n, x, y, False{}))

def add.zero(+a: U32) -> {U32.add(a, 0) == a : U32}:
  match a:
    case U32{+x}:
      Equal.cong(Word(32n), U32, z => U32{z}, Word.adc(32n, x, Word.zero(32n), False{}, False{}), x, W3(32n, x))

# Counting cells
# --------------

# one cell past n cells past a is n cells past one past a
def up.inc(n: Nat, +a: U32) -> {U32.inc(IL.Up(n, a)) == IL.Up(n, U32.inc(a)) : U32}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      up.inc(p, U32.inc(a))

# m + n cells past a are n cells past m cells past a
def up.add(m: Nat, +n: Nat, +a: U32) -> {IL.Up(Nat.add(m, n), a) == IL.Up(n, IL.Up(m, a)) : U32}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      up.add(p, n, U32.inc(a))

# a + (n cells past b) is n cells past a + b
def add.up(n: Nat, +a: U32, +b: U32) -> {U32.add(a, IL.Up(n, b)) == IL.Up(n, U32.add(a, b)) : U32}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %add.inc(a, b) : {U32.add(a, IL.Up(p, U32.inc(b))) == IL.Up(p, _) : U32}
      add.up(p, a, U32.inc(b))

# n cells past x and past y are one cell only when x is y
def up.inj(n: Nat, +x: U32, +y: U32, e: {IL.Up(n, x) == IL.Up(n, y) : U32}) -> {x == y : U32}:
  match n:
    case 0n:
      e
    case 1n+p:
      +ih = up.inj(p, U32.inc(x), U32.inc(y), e)
      Equal.trans(U32, x, U32.sub(U32.inc(x), 1), y, PI.U32.inc_dec(x),
        Equal.trans(U32, U32.sub(U32.inc(x), 1), U32.sub(U32.inc(y), 1), y,
          Equal.cong(U32, U32, z => U32.sub(z, 1), U32.inc(x), U32.inc(y), ih),
          Equal.sym(U32, y, U32.sub(U32.inc(y), 1), PI.U32.inc_dec(y))))

# Img.size counts the nodes
# -------------------------

# a + 1 is one cell past a
def sz.leaf(+a: U32) -> {U32.add(a, 1) == U32.inc(a) : U32}:
  Equal.trans(U32, U32.add(a, U32.inc(0)), U32.inc(U32.add(a, 0)), U32.inc(a), add.inc(a, 0),
    Equal.cong(U32, U32, z => U32.inc(z), U32.add(a, 0), a, add.zero(a)))

# a node of one part of sx cells
def sz.one(+a: U32, +sx: U32, +nx: Nat, ex: {U32.add(a, sx) == IL.Up(nx, a) : U32}) ->
  {U32.add(a, U32.inc(sx)) == IL.Up(nx, U32.inc(a)) : U32}:
  Equal.trans(U32, U32.add(a, U32.inc(sx)), U32.inc(U32.add(a, sx)), IL.Up(nx, U32.inc(a)), add.inc(a, sx),
    Equal.trans(U32, U32.inc(U32.add(a, sx)), U32.inc(IL.Up(nx, a)), IL.Up(nx, U32.inc(a)),
      Equal.cong(U32, U32, z => U32.inc(z), U32.add(a, sx), IL.Up(nx, a), ex), up.inc(nx, a)))

# a + (sx + sy) is ny cells past nx cells past a
def sz.sum(+a: U32, +sx: U32, +sy: U32, +nx: Nat, +ny: Nat, ex: {U32.add(a, sx) == IL.Up(nx, a) : U32},
  ey: {U32.add(sx, sy) == IL.Up(ny, sx) : U32}) -> {U32.add(a, U32.add(sx, sy)) == IL.Up(ny, IL.Up(nx, a)) : U32}:
  %Equal.sym(U32, U32.add(sx, sy), IL.Up(ny, sx), ey) : {U32.add(a, _) == IL.Up(ny, IL.Up(nx, a)) : U32}
  Equal.trans(U32, U32.add(a, IL.Up(ny, sx)), IL.Up(ny, U32.add(a, sx)), IL.Up(ny, IL.Up(nx, a)), add.up(ny, a, sx),
    Equal.cong(U32, U32, z => IL.Up(ny, z), U32.add(a, sx), IL.Up(nx, a), ex))

# a node of two parts of sx and sy cells
def sz.two(+a: U32, +sx: U32, +sy: U32, +nx: Nat, +ny: Nat, ex: {U32.add(a, sx) == IL.Up(nx, a) : U32},
  ey: {U32.add(sx, sy) == IL.Up(ny, sx) : U32}) ->
  {U32.add(a, U32.inc(U32.add(sx, sy))) == IL.Up(Nat.add(nx, ny), U32.inc(a)) : U32}:
  %Equal.sym(U32, IL.Up(Nat.add(nx, ny), U32.inc(a)), IL.Up(ny, IL.Up(nx, U32.inc(a))), up.add(nx, ny, U32.inc(a))) :
    {U32.add(a, U32.inc(U32.add(sx, sy))) == _ : U32}
  Equal.trans(U32, U32.add(a, U32.inc(U32.add(sx, sy))), U32.inc(U32.add(a, U32.add(sx, sy))), IL.Up(ny, IL.Up(nx, U32.inc(a))),
    add.inc(a, U32.add(sx, sy)),
    Equal.trans(U32, U32.inc(U32.add(a, U32.add(sx, sy))), U32.inc(IL.Up(ny, IL.Up(nx, a))), IL.Up(ny, IL.Up(nx, U32.inc(a))),
      Equal.cong(U32, U32, z => U32.inc(z), U32.add(a, U32.add(sx, sy)), IL.Up(ny, IL.Up(nx, a)), sz.sum(a, sx, sy, nx, ny, ex, ey)),
      Equal.trans(U32, U32.inc(IL.Up(ny, IL.Up(nx, a))), IL.Up(ny, U32.inc(IL.Up(nx, a))), IL.Up(ny, IL.Up(nx, U32.inc(a))),
        up.inc(ny, IL.Up(nx, a)), Equal.cong(U32, U32, z => IL.Up(ny, z), U32.inc(IL.Up(nx, a)), IL.Up(nx, U32.inc(a)), up.inc(nx, a)))))

# a node of three parts of sx, sy and sz cells
def sz.three(+a: U32, +sx: U32, +sy: U32, +sz: U32, +nx: Nat, +ny: Nat, +nz: Nat, ex: {U32.add(a, sx) == IL.Up(nx, a) : U32},
  ey: {U32.add(sx, sy) == IL.Up(ny, sx) : U32}, ez: {U32.add(sy, sz) == IL.Up(nz, sy) : U32}) ->
  {U32.add(a, U32.inc(U32.add(sx, U32.add(sy, sz)))) == IL.Up(Nat.add(nx, Nat.add(ny, nz)), U32.inc(a)) : U32}:
  sz.two(a, sx, U32.add(sy, sz), nx, Nat.add(ny, nz), ex,
    Equal.trans(U32, U32.add(sx, U32.add(sy, sz)), IL.Up(nz, IL.Up(ny, sx)), IL.Up(Nat.add(ny, nz), sx), sz.sum(sx, sy, sz, ny, nz, ey, ez),
      Equal.sym(U32, IL.Up(Nat.add(ny, nz), sx), IL.Up(nz, IL.Up(ny, sx)), up.add(ny, nz, sx))))

# a + Img.size(t) is t's nodes past a
def size.up(t: Bk.Term, +a: U32) -> {U32.add(a, Mc.Img.size(t)) == IL.Up(PG.Nsz(t, 0n), a) : U32}:
  match t:
    case Bk.Term.Var{_}:
      sz.leaf(a)
    case Bk.Term.Ref{_}:
      sz.leaf(a)
    case Bk.Term.Ann{+x, +y}:
      %PG.dec_r(x, PG.Nsz(y, 0n)) : {U32.add(a, U32.inc(U32.add(Mc.Img.size(x), Mc.Img.size(y)))) == IL.Up(_, U32.inc(a)) : U32}
      sz.two(a, Mc.Img.size(x), Mc.Img.size(y), PG.Nsz(x, 0n), PG.Nsz(y, 0n), size.up(x, a), size.up(y, Mc.Img.size(x)))
    case Bk.Term.Let{_, +x, +y}:
      %PG.dec_r(x, PG.Nsz(y, 0n)) : {U32.add(a, U32.inc(U32.add(Mc.Img.size(x), Mc.Img.size(y)))) == IL.Up(_, U32.inc(a)) : U32}
      sz.two(a, Mc.Img.size(x), Mc.Img.size(y), PG.Nsz(x, 0n), PG.Nsz(y, 0n), size.up(x, a), size.up(y, Mc.Img.size(x)))
    case Bk.Term.Typ{+x}:
      sz.one(a, Mc.Img.size(x), PG.Nsz(x, 0n), size.up(x, a))
    case Bk.Term.Min{+x, +y}:
      %PG.dec_r(x, PG.Nsz(y, 0n)) : {U32.add(a, U32.inc(U32.add(Mc.Img.size(x), Mc.Img.size(y)))) == IL.Up(_, U32.inc(a)) : U32}
      sz.two(a, Mc.Img.size(x), Mc.Img.size(y), PG.Nsz(x, 0n), PG.Nsz(y, 0n), size.up(x, a), size.up(y, Mc.Img.size(x)))
    case Bk.Term.All{_, +x, +y}:
      %PG.dec_r(x, PG.Nsz(y, 0n)) : {U32.add(a, U32.inc(U32.add(Mc.Img.size(x), Mc.Img.size(y)))) == IL.Up(_, U32.inc(a)) : U32}
      sz.two(a, Mc.Img.size(x), Mc.Img.size(y), PG.Nsz(x, 0n), PG.Nsz(y, 0n), size.up(x, a), size.up(y, Mc.Img.size(x)))
    case Bk.Term.Lam{_, +x}:
      sz.one(a, Mc.Img.size(x), PG.Nsz(x, 0n), size.up(x, a))
    case Bk.Term.App{_, +x, +y}:
      %PG.dec_r(x, PG.Nsz(y, 0n)) : {U32.add(a, U32.inc(U32.add(Mc.Img.size(x), Mc.Img.size(y)))) == IL.Up(_, U32.inc(a)) : U32}
      sz.two(a, Mc.Img.size(x), Mc.Img.size(y), PG.Nsz(x, 0n), PG.Nsz(y, 0n), size.up(x, a), size.up(y, Mc.Img.size(x)))
    case Bk.Term.Sig{_, +x, +y}:
      %PG.dec_r(x, PG.Nsz(y, 0n)) : {U32.add(a, U32.inc(U32.add(Mc.Img.size(x), Mc.Img.size(y)))) == IL.Up(_, U32.inc(a)) : U32}
      sz.two(a, Mc.Img.size(x), Mc.Img.size(y), PG.Nsz(x, 0n), PG.Nsz(y, 0n), size.up(x, a), size.up(y, Mc.Img.size(x)))
    case Bk.Term.Tup{_, +x, +y}:
      %PG.dec_r(x, PG.Nsz(y, 0n)) : {U32.add(a, U32.inc(U32.add(Mc.Img.size(x), Mc.Img.size(y)))) == IL.Up(_, U32.inc(a)) : U32}
      sz.two(a, Mc.Img.size(x), Mc.Img.size(y), PG.Nsz(x, 0n), PG.Nsz(y, 0n), size.up(x, a), size.up(y, Mc.Img.size(x)))
    case Bk.Term.Prj{+x}:
      sz.one(a, Mc.Img.size(x), PG.Nsz(x, 0n), size.up(x, a))
    case Bk.Term.Enu{_}:
      sz.leaf(a)
    case Bk.Term.Lab{_}:
      sz.leaf(a)
    case Bk.Term.Mat{_, +x, +y}:
      %PG.dec_r(x, PG.Nsz(y, 0n)) : {U32.add(a, U32.inc(U32.add(Mc.Img.size(x), Mc.Img.size(y)))) == IL.Up(_, U32.inc(a)) : U32}
      sz.two(a, Mc.Img.size(x), Mc.Img.size(y), PG.Nsz(x, 0n), PG.Nsz(y, 0n), size.up(x, a), size.up(y, Mc.Img.size(x)))
    case Bk.Term.Efq{}:
      sz.leaf(a)
    case Bk.Term.Eql{+x, +y, +z}:
      %PG.dec_r(x, PG.Nsz(y, PG.Nsz(z, 0n))) :
        {U32.add(a, U32.inc(U32.add(Mc.Img.size(x), U32.add(Mc.Img.size(y), Mc.Img.size(z))))) == IL.Up(_, U32.inc(a)) : U32}
      %PG.dec_r(y, PG.Nsz(z, 0n)) :
        {U32.add(a, U32.inc(U32.add(Mc.Img.size(x), U32.add(Mc.Img.size(y), Mc.Img.size(z))))) == IL.Up(Nat.add(PG.Nsz(x, 0n), _), U32.inc(a)) : U32}
      sz.three(a, Mc.Img.size(x), Mc.Img.size(y), Mc.Img.size(z), PG.Nsz(x, 0n), PG.Nsz(y, 0n), PG.Nsz(z, 0n), size.up(x, a),
        size.up(y, Mc.Img.size(x)), size.up(z, Mc.Img.size(y)))
    case Bk.Term.Rfl{}:
      sz.leaf(a)
    case Bk.Term.Rwt{+x, +y, +z}:
      %PG.dec_r(x, PG.Nsz(y, PG.Nsz(z, 0n))) :
        {U32.add(a, U32.inc(U32.add(Mc.Img.size(x), U32.add(Mc.Img.size(y), Mc.Img.size(z))))) == IL.Up(_, U32.inc(a)) : U32}
      %PG.dec_r(y, PG.Nsz(z, 0n)) :
        {U32.add(a, U32.inc(U32.add(Mc.Img.size(x), U32.add(Mc.Img.size(y), Mc.Img.size(z))))) == IL.Up(Nat.add(PG.Nsz(x, 0n), _), U32.inc(a)) : U32}
      sz.three(a, Mc.Img.size(x), Mc.Img.size(y), Mc.Img.size(z), PG.Nsz(x, 0n), PG.Nsz(y, 0n), PG.Nsz(z, 0n), size.up(x, a),
        size.up(y, Mc.Img.size(x)), size.up(z, Mc.Img.size(y)))

# Img.go's root
# -------------

# a node's cell, one before its first part's (or before upto, for a leaf)
def at.node(+ax: U32, +upto: U32, +nx: Nat, +k: Nat, ex: {IL.Up(nx, ax) == IL.Up(k, upto) : U32}) ->
  {IL.Up(nx, U32.inc(U32.sub(ax, 1))) == IL.Up(k, upto) : U32}:
  %Equal.sym(U32, U32.inc(U32.sub(ax, 1)), ax, IL.u32.dec_inc(ax)) : {IL.Up(nx, _) == IL.Up(k, upto) : U32}
  ex

# the nodes of t past its root are the cell upto (each plus k)
def go.at.up(t: Bk.Term, +ids: Mc.Img.Trie, +refs: Mc.Img.Trie, +upto: U32, +acc: List<&2, Cr.Cir.Cell>, +k: Nat) ->
  {IL.Up(PG.Nsz(t, k), Mc.Img.Out.at(Mc.Img.go(t, ids, refs, upto, acc))) == IL.Up(k, upto) : U32}:
  match t:
    case Bk.Term.Var{_}:
      at.node(upto, upto, k, k, {==})
    case Bk.Term.Ref{_}:
      at.node(upto, upto, k, k, {==})
    case Bk.Term.Ann{+x, +y}:
      at.node(Mc.Img.Out.at(Mc.Img.go(x, ids, refs, Mc.Img.Out.at(Mc.Img.go(y, ids, refs, upto, acc)), Mc.Img.Out.cells(Mc.Img.go(y, ids, refs, upto, acc)))), upto, PG.Nsz(x, PG.Nsz(y, k)), k,
        Equal.trans(U32, IL.Up(PG.Nsz(x, PG.Nsz(y, k)), Mc.Img.Out.at(Mc.Img.go(x, ids, refs, Mc.Img.Out.at(Mc.Img.go(y, ids, refs, upto, acc)), Mc.Img.Out.cells(Mc.Img.go(y, ids, refs, upto, acc))))), IL.Up(PG.Nsz(y, k), Mc.Img.Out.at(Mc.Img.go(y, ids, refs, upto, acc))), IL.Up(k, upto),
          go.at.up(x, ids, refs, Mc.Img.Out.at(Mc.Img.go(y, ids, refs, upto, acc)), Mc.Img.Out.cells(Mc.Img.go(y, ids, refs, upto, acc)), PG.Nsz(y, k)), go.at.up(y, ids, refs, upto, acc, k)))
    case Bk.Term.Let{_, +x, +y}:
      at.node(Mc.Img.Out.at(Mc.Img.go(x, ids, refs, Mc.Img.Out.at(Mc.Img.go(y, ids, refs, upto, acc)), Mc.Img.Out.cells(Mc.Img.go(y, ids, refs, upto, acc)))), upto, PG.Nsz(x, PG.Nsz(y, k)), k,
        Equal.trans(U32, IL.Up(PG.Nsz(x, PG.Nsz(y, k)), Mc.Img.Out.at(Mc.Img.go(x, ids, refs, Mc.Img.Out.at(Mc.Img.go(y, ids, refs, upto, acc)), Mc.Img.Out.cells(Mc.Img.go(y, ids, refs, upto, acc))))), IL.Up(PG.Nsz(y, k), Mc.Img.Out.at(Mc.Img.go(y, ids, refs, upto, acc))), IL.Up(k, upto),
          go.at.up(x, ids, refs, Mc.Img.Out.at(Mc.Img.go(y, ids, refs, upto, acc)), Mc.Img.Out.cells(Mc.Img.go(y, ids, refs, upto, acc)), PG.Nsz(y, k)), go.at.up(y, ids, refs, upto, acc, k)))
    case Bk.Term.Typ{+x}:
      at.node(Mc.Img.Out.at(Mc.Img.go(x, ids, refs, upto, acc)), upto, PG.Nsz(x, k), k, go.at.up(x, ids, refs, upto, acc, k))
    case Bk.Term.Min{+x, +y}:
      at.node(Mc.Img.Out.at(Mc.Img.go(x, ids, refs, Mc.Img.Out.at(Mc.Img.go(y, ids, refs, upto, acc)), Mc.Img.Out.cells(Mc.Img.go(y, ids, refs, upto, acc)))), upto, PG.Nsz(x, PG.Nsz(y, k)), k,
        Equal.trans(U32, IL.Up(PG.Nsz(x, PG.Nsz(y, k)), Mc.Img.Out.at(Mc.Img.go(x, ids, refs, Mc.Img.Out.at(Mc.Img.go(y, ids, refs, upto, acc)), Mc.Img.Out.cells(Mc.Img.go(y, ids, refs, upto, acc))))), IL.Up(PG.Nsz(y, k), Mc.Img.Out.at(Mc.Img.go(y, ids, refs, upto, acc))), IL.Up(k, upto),
          go.at.up(x, ids, refs, Mc.Img.Out.at(Mc.Img.go(y, ids, refs, upto, acc)), Mc.Img.Out.cells(Mc.Img.go(y, ids, refs, upto, acc)), PG.Nsz(y, k)), go.at.up(y, ids, refs, upto, acc, k)))
    case Bk.Term.All{_, +x, +y}:
      at.node(Mc.Img.Out.at(Mc.Img.go(x, ids, refs, Mc.Img.Out.at(Mc.Img.go(y, ids, refs, upto, acc)), Mc.Img.Out.cells(Mc.Img.go(y, ids, refs, upto, acc)))), upto, PG.Nsz(x, PG.Nsz(y, k)), k,
        Equal.trans(U32, IL.Up(PG.Nsz(x, PG.Nsz(y, k)), Mc.Img.Out.at(Mc.Img.go(x, ids, refs, Mc.Img.Out.at(Mc.Img.go(y, ids, refs, upto, acc)), Mc.Img.Out.cells(Mc.Img.go(y, ids, refs, upto, acc))))), IL.Up(PG.Nsz(y, k), Mc.Img.Out.at(Mc.Img.go(y, ids, refs, upto, acc))), IL.Up(k, upto),
          go.at.up(x, ids, refs, Mc.Img.Out.at(Mc.Img.go(y, ids, refs, upto, acc)), Mc.Img.Out.cells(Mc.Img.go(y, ids, refs, upto, acc)), PG.Nsz(y, k)), go.at.up(y, ids, refs, upto, acc, k)))
    case Bk.Term.Lam{_, +x}:
      at.node(Mc.Img.Out.at(Mc.Img.go(x, ids, refs, upto, acc)), upto, PG.Nsz(x, k), k, go.at.up(x, ids, refs, upto, acc, k))
    case Bk.Term.App{_, +x, +y}:
      at.node(Mc.Img.Out.at(Mc.Img.go(x, ids, refs, Mc.Img.Out.at(Mc.Img.go(y, ids, refs, upto, acc)), Mc.Img.Out.cells(Mc.Img.go(y, ids, refs, upto, acc)))), upto, PG.Nsz(x, PG.Nsz(y, k)), k,
        Equal.trans(U32, IL.Up(PG.Nsz(x, PG.Nsz(y, k)), Mc.Img.Out.at(Mc.Img.go(x, ids, refs, Mc.Img.Out.at(Mc.Img.go(y, ids, refs, upto, acc)), Mc.Img.Out.cells(Mc.Img.go(y, ids, refs, upto, acc))))), IL.Up(PG.Nsz(y, k), Mc.Img.Out.at(Mc.Img.go(y, ids, refs, upto, acc))), IL.Up(k, upto),
          go.at.up(x, ids, refs, Mc.Img.Out.at(Mc.Img.go(y, ids, refs, upto, acc)), Mc.Img.Out.cells(Mc.Img.go(y, ids, refs, upto, acc)), PG.Nsz(y, k)), go.at.up(y, ids, refs, upto, acc, k)))
    case Bk.Term.Sig{_, +x, +y}:
      at.node(Mc.Img.Out.at(Mc.Img.go(x, ids, refs, Mc.Img.Out.at(Mc.Img.go(y, ids, refs, upto, acc)), Mc.Img.Out.cells(Mc.Img.go(y, ids, refs, upto, acc)))), upto, PG.Nsz(x, PG.Nsz(y, k)), k,
        Equal.trans(U32, IL.Up(PG.Nsz(x, PG.Nsz(y, k)), Mc.Img.Out.at(Mc.Img.go(x, ids, refs, Mc.Img.Out.at(Mc.Img.go(y, ids, refs, upto, acc)), Mc.Img.Out.cells(Mc.Img.go(y, ids, refs, upto, acc))))), IL.Up(PG.Nsz(y, k), Mc.Img.Out.at(Mc.Img.go(y, ids, refs, upto, acc))), IL.Up(k, upto),
          go.at.up(x, ids, refs, Mc.Img.Out.at(Mc.Img.go(y, ids, refs, upto, acc)), Mc.Img.Out.cells(Mc.Img.go(y, ids, refs, upto, acc)), PG.Nsz(y, k)), go.at.up(y, ids, refs, upto, acc, k)))
    case Bk.Term.Tup{_, +x, +y}:
      at.node(Mc.Img.Out.at(Mc.Img.go(x, ids, refs, Mc.Img.Out.at(Mc.Img.go(y, ids, refs, upto, acc)), Mc.Img.Out.cells(Mc.Img.go(y, ids, refs, upto, acc)))), upto, PG.Nsz(x, PG.Nsz(y, k)), k,
        Equal.trans(U32, IL.Up(PG.Nsz(x, PG.Nsz(y, k)), Mc.Img.Out.at(Mc.Img.go(x, ids, refs, Mc.Img.Out.at(Mc.Img.go(y, ids, refs, upto, acc)), Mc.Img.Out.cells(Mc.Img.go(y, ids, refs, upto, acc))))), IL.Up(PG.Nsz(y, k), Mc.Img.Out.at(Mc.Img.go(y, ids, refs, upto, acc))), IL.Up(k, upto),
          go.at.up(x, ids, refs, Mc.Img.Out.at(Mc.Img.go(y, ids, refs, upto, acc)), Mc.Img.Out.cells(Mc.Img.go(y, ids, refs, upto, acc)), PG.Nsz(y, k)), go.at.up(y, ids, refs, upto, acc, k)))
    case Bk.Term.Prj{+x}:
      at.node(Mc.Img.Out.at(Mc.Img.go(x, ids, refs, upto, acc)), upto, PG.Nsz(x, k), k, go.at.up(x, ids, refs, upto, acc, k))
    case Bk.Term.Enu{_}:
      at.node(upto, upto, k, k, {==})
    case Bk.Term.Lab{_}:
      at.node(upto, upto, k, k, {==})
    case Bk.Term.Mat{_, +x, +y}:
      at.node(Mc.Img.Out.at(Mc.Img.go(x, ids, refs, Mc.Img.Out.at(Mc.Img.go(y, ids, refs, upto, acc)), Mc.Img.Out.cells(Mc.Img.go(y, ids, refs, upto, acc)))), upto, PG.Nsz(x, PG.Nsz(y, k)), k,
        Equal.trans(U32, IL.Up(PG.Nsz(x, PG.Nsz(y, k)), Mc.Img.Out.at(Mc.Img.go(x, ids, refs, Mc.Img.Out.at(Mc.Img.go(y, ids, refs, upto, acc)), Mc.Img.Out.cells(Mc.Img.go(y, ids, refs, upto, acc))))), IL.Up(PG.Nsz(y, k), Mc.Img.Out.at(Mc.Img.go(y, ids, refs, upto, acc))), IL.Up(k, upto),
          go.at.up(x, ids, refs, Mc.Img.Out.at(Mc.Img.go(y, ids, refs, upto, acc)), Mc.Img.Out.cells(Mc.Img.go(y, ids, refs, upto, acc)), PG.Nsz(y, k)), go.at.up(y, ids, refs, upto, acc, k)))
    case Bk.Term.Efq{}:
      at.node(upto, upto, k, k, {==})
    case Bk.Term.Eql{+x, +y, +z}:
      at.node(Mc.Img.Out.at(Mc.Img.go(x, ids, refs, Mc.Img.Out.at(Mc.Img.go(y, ids, refs, Mc.Img.Out.at(Mc.Img.go(z, ids, refs, upto, acc)), Mc.Img.Out.cells(Mc.Img.go(z, ids, refs, upto, acc)))), Mc.Img.Out.cells(Mc.Img.go(y, ids, refs, Mc.Img.Out.at(Mc.Img.go(z, ids, refs, upto, acc)), Mc.Img.Out.cells(Mc.Img.go(z, ids, refs, upto, acc)))))), upto, PG.Nsz(x, PG.Nsz(y, PG.Nsz(z, k))), k,
        Equal.trans(U32, IL.Up(PG.Nsz(x, PG.Nsz(y, PG.Nsz(z, k))), Mc.Img.Out.at(Mc.Img.go(x, ids, refs, Mc.Img.Out.at(Mc.Img.go(y, ids, refs, Mc.Img.Out.at(Mc.Img.go(z, ids, refs, upto, acc)), Mc.Img.Out.cells(Mc.Img.go(z, ids, refs, upto, acc)))), Mc.Img.Out.cells(Mc.Img.go(y, ids, refs, Mc.Img.Out.at(Mc.Img.go(z, ids, refs, upto, acc)), Mc.Img.Out.cells(Mc.Img.go(z, ids, refs, upto, acc))))))), IL.Up(PG.Nsz(y, PG.Nsz(z, k)), Mc.Img.Out.at(Mc.Img.go(y, ids, refs, Mc.Img.Out.at(Mc.Img.go(z, ids, refs, upto, acc)), Mc.Img.Out.cells(Mc.Img.go(z, ids, refs, upto, acc))))), IL.Up(k, upto),
          go.at.up(x, ids, refs, Mc.Img.Out.at(Mc.Img.go(y, ids, refs, Mc.Img.Out.at(Mc.Img.go(z, ids, refs, upto, acc)), Mc.Img.Out.cells(Mc.Img.go(z, ids, refs, upto, acc)))), Mc.Img.Out.cells(Mc.Img.go(y, ids, refs, Mc.Img.Out.at(Mc.Img.go(z, ids, refs, upto, acc)), Mc.Img.Out.cells(Mc.Img.go(z, ids, refs, upto, acc)))), PG.Nsz(y, PG.Nsz(z, k))),
          Equal.trans(U32, IL.Up(PG.Nsz(y, PG.Nsz(z, k)), Mc.Img.Out.at(Mc.Img.go(y, ids, refs, Mc.Img.Out.at(Mc.Img.go(z, ids, refs, upto, acc)), Mc.Img.Out.cells(Mc.Img.go(z, ids, refs, upto, acc))))), IL.Up(PG.Nsz(z, k), Mc.Img.Out.at(Mc.Img.go(z, ids, refs, upto, acc))), IL.Up(k, upto),
            go.at.up(y, ids, refs, Mc.Img.Out.at(Mc.Img.go(z, ids, refs, upto, acc)), Mc.Img.Out.cells(Mc.Img.go(z, ids, refs, upto, acc)), PG.Nsz(z, k)), go.at.up(z, ids, refs, upto, acc, k))))
    case Bk.Term.Rfl{}:
      at.node(upto, upto, k, k, {==})
    case Bk.Term.Rwt{+x, +y, +z}:
      at.node(Mc.Img.Out.at(Mc.Img.go(x, ids, refs, Mc.Img.Out.at(Mc.Img.go(y, ids, refs, Mc.Img.Out.at(Mc.Img.go(z, ids, refs, upto, acc)), Mc.Img.Out.cells(Mc.Img.go(z, ids, refs, upto, acc)))), Mc.Img.Out.cells(Mc.Img.go(y, ids, refs, Mc.Img.Out.at(Mc.Img.go(z, ids, refs, upto, acc)), Mc.Img.Out.cells(Mc.Img.go(z, ids, refs, upto, acc)))))), upto, PG.Nsz(x, PG.Nsz(y, PG.Nsz(z, k))), k,
        Equal.trans(U32, IL.Up(PG.Nsz(x, PG.Nsz(y, PG.Nsz(z, k))), Mc.Img.Out.at(Mc.Img.go(x, ids, refs, Mc.Img.Out.at(Mc.Img.go(y, ids, refs, Mc.Img.Out.at(Mc.Img.go(z, ids, refs, upto, acc)), Mc.Img.Out.cells(Mc.Img.go(z, ids, refs, upto, acc)))), Mc.Img.Out.cells(Mc.Img.go(y, ids, refs, Mc.Img.Out.at(Mc.Img.go(z, ids, refs, upto, acc)), Mc.Img.Out.cells(Mc.Img.go(z, ids, refs, upto, acc))))))), IL.Up(PG.Nsz(y, PG.Nsz(z, k)), Mc.Img.Out.at(Mc.Img.go(y, ids, refs, Mc.Img.Out.at(Mc.Img.go(z, ids, refs, upto, acc)), Mc.Img.Out.cells(Mc.Img.go(z, ids, refs, upto, acc))))), IL.Up(k, upto),
          go.at.up(x, ids, refs, Mc.Img.Out.at(Mc.Img.go(y, ids, refs, Mc.Img.Out.at(Mc.Img.go(z, ids, refs, upto, acc)), Mc.Img.Out.cells(Mc.Img.go(z, ids, refs, upto, acc)))), Mc.Img.Out.cells(Mc.Img.go(y, ids, refs, Mc.Img.Out.at(Mc.Img.go(z, ids, refs, upto, acc)), Mc.Img.Out.cells(Mc.Img.go(z, ids, refs, upto, acc)))), PG.Nsz(y, PG.Nsz(z, k))),
          Equal.trans(U32, IL.Up(PG.Nsz(y, PG.Nsz(z, k)), Mc.Img.Out.at(Mc.Img.go(y, ids, refs, Mc.Img.Out.at(Mc.Img.go(z, ids, refs, upto, acc)), Mc.Img.Out.cells(Mc.Img.go(z, ids, refs, upto, acc))))), IL.Up(PG.Nsz(z, k), Mc.Img.Out.at(Mc.Img.go(z, ids, refs, upto, acc))), IL.Up(k, upto),
            go.at.up(y, ids, refs, Mc.Img.Out.at(Mc.Img.go(z, ids, refs, upto, acc)), Mc.Img.Out.cells(Mc.Img.go(z, ids, refs, upto, acc)), PG.Nsz(z, k)), go.at.up(z, ids, refs, upto, acc, k))))

# the root of a body that Img.bodies lays out at the cell at is at
def body.at(+v: Bk.Term, +ids: Mc.Img.Trie, +refs: Mc.Img.Trie, +at: U32, +acc: List<&2, Cr.Cir.Cell>) ->
  {Mc.Img.Out.at(Mc.Img.go(v, ids, refs, U32.add(at, Mc.Img.size(v)), acc)) == at : U32}:
  +r = Mc.Img.Out.at(Mc.Img.go(v, ids, refs, U32.add(at, Mc.Img.size(v)), acc))
  up.inj(PG.Nsz(v, 0n), r, at,
    Equal.trans(U32, IL.Up(PG.Nsz(v, 0n), r), U32.add(at, Mc.Img.size(v)), IL.Up(PG.Nsz(v, 0n), at),
      go.at.up(v, ids, refs, U32.add(at, Mc.Img.size(v)), acc, 0n), size.up(v, at)))
