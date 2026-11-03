# compiler: the walk of a copy
# ============================
#
# M.copy.walk keeps a stack of new cells (frames), each a copy of a source
# cell whose parts it copies in order: a part is done (its field holds the
# copy, a cell of Mo.F of the part's term under the frame's depth and the
# binders above the part), current (its field holds the frame above, which
# copies it), pending (its field still holds the source's part, a cell of
# its term), or no part of the tag. The top frame has no current part; each
# frame below it has one, the last part that is not pending. The walk's
# invariant (WI) holds of each round: the frames from the stack register,
# the cells that may be read (all but the garbage and the frames), the
# allocation's invariant, the roots and the kept cells, and a measure that
# bounds the rounds left and the counts that they add.

import Base
import ../../Book/impl.bend as Bk
import ../../Program/impl.bend as Pg
import ../Cir/impl.bend as Cr
import ./impl.bend as Mc
import ./cell_terms.bend as T
import ../need_big.bend as N
import ./copy_substitution.bend as D
import ./copy_kit.bend as K
import ./statement_runs.bend as Sr

# The tags
# --------

# the field k (2, 3 or 4) of a cell of the tag tg is a part of its term
def Tg.u(tg: Nat, +k: Nat) -> Bool:
  match tg:
    case 2n:
      Bool.or(Nat.is_eq(k, 2n), Nat.is_eq(k, 3n))
    case 3n:
      Bool.or(Nat.is_eq(k, 2n), Nat.is_eq(k, 3n))
    case 4n:
      Nat.is_eq(k, 2n)
    case 5n:
      Bool.or(Nat.is_eq(k, 2n), Nat.is_eq(k, 3n))
    case 6n:
      Bool.or(Nat.is_eq(k, 2n), Nat.is_eq(k, 3n))
    case 7n:
      Nat.is_eq(k, 2n)
    case 8n:
      Bool.or(Nat.is_eq(k, 2n), Nat.is_eq(k, 3n))
    case 9n:
      Bool.or(Nat.is_eq(k, 2n), Nat.is_eq(k, 3n))
    case 10n:
      Bool.or(Nat.is_eq(k, 2n), Nat.is_eq(k, 3n))
    case 11n:
      Nat.is_eq(k, 2n)
    case 14n:
      Bool.or(Nat.is_eq(k, 3n), Nat.is_eq(k, 4n))
    case 16n:
      Bool.or(Nat.is_eq(k, 2n), Bool.or(Nat.is_eq(k, 3n), Nat.is_eq(k, 4n)))
    case 18n:
      Bool.or(Nat.is_eq(k, 2n), Bool.or(Nat.is_eq(k, 3n), Nat.is_eq(k, 4n)))
    case _:
      False{}

# the binders above the field k of a cell of the tag tg
def Tg.b(tg: Nat, +k: Nat) -> Nat:
  match tg:
    case 3n:
      Bool.pick(Nat, Nat.is_eq(k, 3n), 1n, 0n)
    case 6n:
      Bool.pick(Nat, Nat.is_eq(k, 3n), 1n, 0n)
    case 7n:
      Bool.pick(Nat, Nat.is_eq(k, 2n), 1n, 0n)
    case 9n:
      Bool.pick(Nat, Nat.is_eq(k, 3n), 1n, 0n)
    case 18n:
      Bool.pick(Nat, Nat.is_eq(k, 3n), 2n, 0n)
    case _:
      0n

# a tag that a walk copies: a term's, but no Var, Ref or Enu (which it never
# pushes)
def Tg.ok(+tg: Nat) -> Bool:
  match tg:
    case 0n:
      False{}
    case 1n:
      False{}
    case 12n:
      False{}
    case _:
      Nat.is_le(tg, 18n)

# The frames
# ----------

type St is Data:
  St.un{}
  St.pe{}
  St.dn{}
  St.cu{}

# a frame: the new cell n, the low byte h of its header (its tag and
# quantity), its source's field 2 x2 (a name, for Lab and Mat) and source
# term T, the cells x and terms t of the source's parts, their statuses, and
# its depth d
type Fr is Data:
  Fr{n: U32, h: U32, x2: U32, T: Bk.Term, y2: U32, y3: U32, y4: U32, t2: Bk.Term, t3: Bk.Term, t4: Bk.Term,
    s2: St, s3: St, s4: St, d: Nat}

# what the copy needs of a part's term: a shift's variables fit it
def MoOK(+mo: D.Mo, t: Bk.Term) -> Bool:
  match mo:
    case D.Mo.shift{a}:
      D.Fit(t, U32.from_nat(a))
    case D.Mo.subst{_}:
      True{}

# the field v of a frame, of the part of status s: the source's cell x, or
# its copy, of Mo.F(mo, t, dd), or the frame above (cn, of the source term
# cT, at the depth cd)
def FS(+mo: D.Mo, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +K: U32, +F: U32,
  +X: List<&2, U32>, +N: U32, +v: U32, +x: U32, +t: Bk.Term, s: St, +dd: Nat, +cn: U32, +cT: Bk.Term, +cd: Nat) -> Data:
  match s:
    case St.un{}:
      {v == x : U32}
    case St.pe{}:
      D.P2({v == x : U32}, D.P2(D.Ex(Nat, g => {D.Tm(g, m, ks, img, K, F, X, N, x) == Some{t} : Maybe<&2, Bk.Term>}),
        {MoOK(mo, t) == True{} : Bool}))
    case St.dn{}:
      D.Ex(Nat, g => {D.Tm(g, m, ks, img, K, F, X, N, v) == Some{D.Mo.F(mo, t, dd)} : Maybe<&2, Bk.Term>})
    case St.cu{}:
      D.P2({v == cn : U32}, D.P2({cT == t : Bk.Term}, {cd == dd : Nat}))

def St.is_pe(s: St) -> Bool:
  match s:
    case St.pe{}:
      True{}
    case _:
      False{}

# the bit of the todo bits for a pending part of field k (M.todo.bit)
def Bit(+s: St, +b: U32) -> U32:
  Bool.pick(U32, St.is_pe(s), b, 0)

# some part is pending
def HasPe(+s2: St, +s3: St, +s4: St) -> Bool:
  Bool.or(St.is_pe(s2), Bool.or(St.is_pe(s3), St.is_pe(s4)))

# the todo bits of a frame, from bit 8 (bits 0 to 2 here)
def Todo(+s2: St, +s3: St, +s4: St) -> U32:
  U32.or(Bit(s2, 1), U32.or(Bit(s3, 2), Bit(s4, 4)))

# the statuses of the parts: un for the fields that are no part of the tag; in
# order, done parts, then (below the top) one current part, then pending ones
def Ph(s: St) -> Nat:
  match s:
    case St.un{}:
      0n
    case St.dn{}:
      1n
    case St.cu{}:
      2n
    case St.pe{}:
      3n

def Ph.cu(s: St) -> Nat:
  match s:
    case St.cu{}:
      1n
    case _:
      0n

def St.is_un(s: St) -> Bool:
  match s:
    case St.un{}:
      True{}
    case _:
      False{}

def Bo.eq(a: Bool, b: Bool) -> Bool:
  match a:
    case True{}:
      b
    case False{}:
      Bool.not(b)

# the phases of the used parts are in order: a field that is no part is skipped
def SOK.go(s: St, +p: Nat) -> Nat:
  match s:
    case St.un{}:
      p
    case _:
      Ph(s)

def SOK(+tg: Nat, +top: Bool, +s2: St, +s3: St, +s4: St) -> Bool:
  +p2 = SOK.go(s2, 1n)
  +p3 = SOK.go(s3, p2)
  +p4 = SOK.go(s4, p3)
  Bool.and(Bool.and(Bool.and(Bo.eq(Tg.u(tg, 2n), Bool.not(St.is_un(s2))),
    Bo.eq(Tg.u(tg, 3n), Bool.not(St.is_un(s3)))), Bo.eq(Tg.u(tg, 4n), Bool.not(St.is_un(s4)))),
  Bool.and(Bool.and(Nat.is_le(p2, p3), Nat.is_le(p3, p4)),
    Nat.is_eq(Nat.add(Ph.cu(s2), Nat.add(Ph.cu(s3), Ph.cu(s4))), Bool.pick(Nat, top, 0n, 1n))))

# the tag of the header byte h
def Fr.tag(+h: U32) -> Nat:
  U32.to_nat(U32.and(h, 63))

# the source term of a frame: of its tag and quantity, the name in field 2,
# and the terms of its parts
def Fr.src(+h: U32, +n: U32, +y2: U32, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +t2: Bk.Term, +t3: Bk.Term,
  +t4: Bk.Term) -> Maybe<&2, Bk.Term>:
  T.tm.cell(Fr.tag(h), T.tm.quan(U32.and(U32.shrn(h, 6n), 3)), n, y2, ks, img, u => Some{t2}, u => Some{t3}, u => Some{t4})

# the frame fr, the top one (top) or below the frame (cn, cT, cd): its cell
# holds the header h with the todo bits of its pending parts, and its parts
# by their statuses; it is one of the machine's own cells, which may not be
# read (one of X), with a tag that the walk copies
def FrOK(+mo: D.Mo, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +K: U32, +F: U32,
  +X: List<&2, U32>, +N: U32, fr: Fr, +top: Bool, +cn: U32, +cT: Bk.Term, +cd: Nat) -> Data:
  match fr:
    case Fr{+n, +h, +x2, +T0, +y2, +y3, +y4, +t2, +t3, +t4, +s2, +s3, +s4, +d}:
      +tg = Fr.tag(h)
      D.P2({D.Fd(0n, m, n) == U32.or(h, U32.shln(Todo(s2, s3, s4), 8n)) : U32},
      D.P2(FS(mo, m, ks, img, K, F, X, N, D.Fd(2n, m, n), y2, t2, s2, Nat.add(d, Tg.b(tg, 2n)), cn, cT, cd),
      D.P2(FS(mo, m, ks, img, K, F, X, N, D.Fd(3n, m, n), y3, t3, s3, Nat.add(d, Tg.b(tg, 3n)), cn, cT, cd),
      D.P2(FS(mo, m, ks, img, K, F, X, N, D.Fd(4n, m, n), y4, t4, s4, Nat.add(d, Tg.b(tg, 4n)), cn, cT, cd),
      D.P2({SOK(tg, top, s2, s3, s4) == True{} : Bool},
      D.P2({Tg.ok(tg) == True{} : Bool},
      D.P2({U32.and(h, 255) == h : U32},
      D.P2({x2 == y2 : U32},
      D.P2({Fr.src(h, n, y2, ks, img, t2, t3, t4) == Some{T0} : Maybe<&2, Bk.Term>},
      D.P2({Cr.Cir.is_cell(n, K, F, N) == True{} : Bool},
      D.P2({U32.is_le(F, n) == True{} : Bool},
        {D.Has(X, n) == True{} : Bool})))))))))))

# the frames frs, from the cell at on, linked by field 1, the top first (top),
# each below the one before (cn, cT, cd); 0 after the last
def Frs(+mo: D.Mo, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +K: U32, +F: U32,
  +X: List<&2, U32>, +N: U32, frs: List<&2, Fr>, +at: U32, +top: Bool, +cn: U32, +cT: Bk.Term, +cd: Nat) -> Data:
  match frs:
    case Nil{}:
      {at == 0 : U32}
    case Con{+fr, rest}:
      match fr:
        case Fr{+n, +h, +x2, +T0, +y2, +y3, +y4, +t2, +t3, +t4, +s2, +s3, +s4, +d}:
          D.P2({at == n : U32},
          D.P2(FrOK(mo, m, ks, img, K, F, X, N, Fr{n, h, x2, T0, y2, y3, y4, t2, t3, t4, s2, s3, s4, d}, top, cn, cT, cd),
            Frs(mo, m, ks, img, K, F, X, N, rest, D.Fd(1n, m, n), False{}, n, T0, d)))

# the cells of the frames
def Ns(frs: List<&2, Fr>) -> List<&2, U32>:
  match frs:
    case Nil{}:
      Nil{}
    case Con{Fr{n, _, _, _, _, _, _, _, _, _, _, _, _, _}, rest}:
      Con{n, Ns(rest)}

# twice the nodes of a pending part
def Wp(s: St, t: Bk.Term) -> Nat:
  match s:
    case St.pe{}:
      Nat.double(D.Sz(t))
    case _:
      0n

# the measure of the frames: a round for each, and two for each node of a
# pending part
def Wm(frs: List<&2, Fr>) -> Nat:
  match frs:
    case Nil{}:
      0n
    case Con{Fr{_, _, _, _, _, _, _, t2, t3, t4, s2, s3, s4, _}, rest}:
      1n+Nat.add(Wp(s2, t2), Nat.add(Wp(s3, t3), Nat.add(Wp(s4, t4), Wm(rest))))

# the last of the frames is the root: a Prj of the source's cell x, of the term
# t, at the depth 0, in the cell root; once the frames are gone, the root's field 2 holds the
# copy, of Mo.F(mo, t, 0)
def Root(+mo: D.Mo, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +K: U32, +F: U32,
  +X: List<&2, U32>, +N: U32, frs: List<&2, Fr>, +root: U32, +x: U32, +t: Bk.Term) -> Data:
  match frs:
    case Nil{}:
      D.Ex(Nat, g => {D.Tm(g, m, ks, img, K, F, X, N, D.Fd(2n, m, root)) == Some{D.Mo.F(mo, t, 0n)} : Maybe<&2, Bk.Term>})
    case Con{Fr{n, h, _, _, y2, _, _, t2, _, _, _, _, _, d}, Nil{}}:
      D.P2({n == root : U32}, D.P2({h == 11 : U32}, D.P2({y2 == x : U32}, D.P2({t2 == t : Bk.Term}, {d == 0n : Nat}))))
    case Con{_, rest}:
      Root(mo, m, ks, img, K, F, X, N, rest, root, x, t)

# no frame's cell is in P
def Dj(xs: List<&2, U32>, +P: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, rest}:
      Bool.and(Bool.not(D.Has(P, x)), Dj(rest, P))

# the depth d of each frame and twice its source's nodes are at most B: a part
# under it never wraps its U32 depth
def DB(frs: List<&2, Fr>, +B: Nat) -> Bool:
  match frs:
    case Nil{}:
      True{}
    case Con{Fr{_, _, _, T0, _, _, _, _, _, _, _, _, _, d}, rest}:
      Bool.and(Nat.is_le(Nat.add(d, Nat.double(D.Sz(T0))), B), DB(rest, B))

# the depth register holds the top frame's depth
def Dp(frs: List<&2, Fr>, +depth: U32) -> Data:
  match frs:
    case Nil{}:
      Unit
    case Con{Fr{_, _, _, _, _, _, _, _, _, _, _, _, _, d}, _}:
      {depth == U32.from_nat(d) : U32}

# The allocation
# --------------

# the registers xs with 3 to 7 (pend, dx, dr, aq, am) set to the values a
def Rp(+a: List<&2, U32>, xs: List<&2, U32>) -> List<&2, U32>:
  D.Ups([D.Up{3n, T.tm.reg(a, 0n)}, D.Up{4n, T.tm.reg(a, 1n)}, D.Up{5n, T.tm.reg(a, 2n)}, D.Up{6n, T.tm.reg(a, 3n)},
    D.Up{7n, T.tm.reg(a, 4n)}], xs)

# a write of field 1 (a count or a link) of the cell x
type W1 is Data:
  W1{x: U32, v: U32}

# the cells m after the writes ws, the last first (definitions.bend's Put1)
def W1s(ws: List<&2, W1>, +m: Cr.Cir.Cells) -> Cr.Cir.Cells:
  match ws:
    case Nil{}:
      m
    case Con{W1{+x, +v}, +rest}:
      K.St1(W1s(rest, m), x, v)

# each write is to a part of the cell c (by its mask, D.Ow)
def W1s.pt(ws: List<&2, W1>, +m: Cr.Cir.Cells, +c: U32) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case Con{W1{+x, _}, rest}:
      Bool.and(Nat.is_lt(0n, D.Ow(m, c, x)), W1s.pt(rest, m, c))

# the writes keep every field but 1 of every cell
def fd.w1s(ws: List<&2, W1>, +m: Cr.Cir.Cells, +k: Nat, +hk: {Nat.is_eq(k, 1n) == False{} : Bool}, +y: U32) ->
  {D.Fd(k, W1s(ws, m), y) == D.Fd(k, m, y) : U32}:
  match ws:
    case Nil{}:
      {==}
    case Con{W1{+x, +v}, +rest}:
      Equal.trans(U32, D.Fd(k, K.St1(W1s(rest, m), x, v), y), D.Fd(k, W1s(rest, m), y), D.Fd(k, m, y),
        K.fd.st1(W1s(rest, m), x, v, k, hk, y), fd.w1s(rest, m, k, hk, y))

# so they keep the flags, masks and pointers
def stc.w1s(+ws: List<&2, W1>, +m: Cr.Cir.Cells, +y: U32) -> {D.Stc(W1s(ws, m), y) == D.Stc(m, y) : Bool}:
  K.stc.eq(W1s(ws, m), m, y, fd.w1s(ws, m, 0n, {==}, y))

def am.w1s(+ws: List<&2, W1>, +m: Cr.Cir.Cells, +o: U32) -> {D.Am(W1s(ws, m), o) == D.Am(m, o) : U32}:
  K.am.eq(W1s(ws, m), m, o, fd.w1s(ws, m, 0n, {==}, o), fd.w1s(ws, m, 2n, {==}, U32.add(272, U32.and(D.Fd(0n, m, o), 63))))

def ow.w1s(+ws: List<&2, W1>, +m: Cr.Cir.Cells, +o: U32, +c: U32) -> {D.Ow(W1s(ws, m), o, c) == D.Ow(m, o, c) : Nat}:
  K.ow.eq(W1s(ws, m), m, o, c, am.w1s(ws, m, o), fd.w1s(ws, m, 2n, {==}, o), fd.w1s(ws, m, 3n, {==}, o), fd.w1s(ws, m, 4n, {==}, o))

def ps.w1s(+ws: List<&2, W1>, +m: Cr.Cir.Cells, +Q: List<&2, U32>, +o: U32) -> {D.Ps(W1s(ws, m), Q, o) == D.Ps(m, Q, o) : List<&2, U32>}:
  K.ps.eq(W1s(ws, m), m, Q, o, fd.w1s(ws, m, 0n, {==}, o), fd.w1s(ws, m, 2n, {==}, U32.add(272, U32.and(D.Fd(0n, m, o), 63))),
    fd.w1s(ws, m, 2n, {==}, o), fd.w1s(ws, m, 3n, {==}, o), fd.w1s(ws, m, 4n, {==}, o))

def pp.w1s(L: List<&2, U32>, +ws: List<&2, W1>, +m: Cr.Cir.Cells, +c: U32) -> {D.Pp(L, W1s(ws, m), c) == D.Pp(L, m, c) : Nat}:
  match L:
    case Nil{}:
      {==}
    case Con{+o, +rest}:
      %Equal.sym(Nat, D.Ow(W1s(ws, m), o, c), D.Ow(m, o, c), ow.w1s(ws, m, o, c)) :
        {Nat.add(_, D.Pp(rest, W1s(ws, m), c)) == Nat.add(D.Ow(m, o, c), D.Pp(rest, m, c)) : Nat}
      %Equal.sym(Nat, D.Pp(rest, W1s(ws, m), c), D.Pp(rest, m, c), pp.w1s(rest, ws, m, c)) :
        {Nat.add(D.Ow(m, o, c), _) == Nat.add(D.Ow(m, o, c), D.Pp(rest, m, c)) : Nat}
      {==}

def pc.w1s(n: Nat, +ws: List<&2, W1>, +m: Cr.Cir.Cells, +Q: List<&2, U32>, +o: U32, +c: U32) ->
  {D.Pc(n, W1s(ws, m), Q, o, c) == D.Pc(n, m, Q, o, c) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      %Equal.sym(List<&2, U32>, D.Ps(W1s(ws, m), Q, o), D.Ps(m, Q, o), ps.w1s(ws, m, Q, o)) :
        {Nat.add(D.Occ(_, c), D.Pc(p, W1s(ws, m), Q, U32.inc(o), c)) == Nat.add(D.Occ(D.Ps(m, Q, o), c), D.Pc(p, m, Q, U32.inc(o), c)) : Nat}
      %Equal.sym(Nat, D.Pc(p, W1s(ws, m), Q, U32.inc(o), c), D.Pc(p, m, Q, U32.inc(o), c), pc.w1s(p, ws, m, Q, U32.inc(o), c)) :
        {Nat.add(D.Occ(D.Ps(m, Q, o), c), _) == Nat.add(D.Occ(D.Ps(m, Q, o), c), D.Pc(p, m, Q, U32.inc(o), c)) : Nat}
      {==}

def lt.w1s(n: Nat, +ws: List<&2, W1>, +m: Cr.Cir.Cells, +Q: List<&2, U32>, +o: U32, +N: U32) ->
  {D.Lt(n, W1s(ws, m), Q, o, N) == D.Lt(n, m, Q, o, N) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      %Equal.sym(List<&2, U32>, D.Ps(W1s(ws, m), Q, o), D.Ps(m, Q, o), ps.w1s(ws, m, Q, o)) :
        {Bool.and(D.All.lt(_, N), D.Lt(p, W1s(ws, m), Q, U32.inc(o), N)) == Bool.and(D.All.lt(D.Ps(m, Q, o), N), D.Lt(p, m, Q, U32.inc(o), N)) : Bool}
      %Equal.sym(Bool, D.Lt(p, W1s(ws, m), Q, U32.inc(o), N), D.Lt(p, m, Q, U32.inc(o), N), lt.w1s(p, ws, m, Q, U32.inc(o), N)) :
        {Bool.and(D.All.lt(D.Ps(m, Q, o), N), _) == Bool.and(D.All.lt(D.Ps(m, Q, o), N), D.Lt(p, m, Q, U32.inc(o), N)) : Bool}
      {==}

# a write to a part of c is not to y, of which c has no part
def ne.ow(b: Bool, +m: Cr.Cir.Cells, +c: U32, +x: U32, +y: U32, eb: {U32.is_eq(y, x) == b : Bool},
  hx: {Nat.is_lt(0n, D.Ow(m, c, x)) == True{} : Bool}, h0: {D.Ow(m, c, y) == 0n : Nat}) -> {U32.is_eq(y, x) == False{} : Bool}:
  match b:
    case True{}:
      +e = K.U.eq(y, x, eb)
      +h1 = {%e : {D.Ow(m, c, _) == 0n : Nat}; h0 : {D.Ow(m, c, x) == 0n : Nat}}
      K.Bo.tf({U32.is_eq(y, x) == False{} : Bool}, (%h1 : {Nat.is_lt(0n, _) == True{} : Bool}; hx))
    case False{}:
      eb

# the writes to the parts of c keep each cell y of which c has no part
def w1s.get(ws: List<&2, W1>, +m: Cr.Cir.Cells, +c: U32, +y: U32, h: {W1s.pt(ws, m, c) == True{} : Bool},
  +h0: {D.Ow(m, c, y) == 0n : Nat}) -> {Cr.Cir.Cells.get(W1s(ws, m), y) == Cr.Cir.Cells.get(m, y) : Cr.Cir.Cell}:
  match ws:
    case Nil{}:
      {==}
    case Con{W1{+x, +v}, +rest}:
      +h2 = h
      +M = W1s(rest, m)
      +ne = ne.ow(U32.is_eq(y, x), m, c, x, y, {==}, K.Bo.and_l(Nat.is_lt(0n, D.Ow(m, c, x)), W1s.pt(rest, m, c), h2), h0)
      Equal.trans(Cr.Cir.Cell, Cr.Cir.Cells.get(K.St1(M, x, v), y), Cr.Cir.Cells.get(M, y), Cr.Cir.Cells.get(m, y),
        K.Cl.get_ne(M, y, x, Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(M, x), v), ne),
        w1s.get(rest, m, c, y, K.Bo.and_r(Nat.is_lt(0n, D.Ow(m, c, x)), W1s.pt(rest, m, c), h2), h0))

# xs without its first x
def Del(xs: List<&2, U32>, +x: U32) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+y, +rest}:
      Bool.pick(List<&2, U32>, U32.is_eq(y, x), rest, Con{y, Del(rest, x)})

# what M.alloc did: the cell c, a new one (fresh) or the first of the pend
# list, after the writes ws of field 1 (counts and links) of the parts that
# its reuse dropped; the garbage P2 and pend list Q2 after it, and the
# registers 3 to 7
type Aw is Data:
  Aw{c: U32, fresh: Bool, P2: List<&2, U32>, Q2: List<&2, U32>, ws: List<&2, W1>, a: List<&2, U32>}

def Al.how(fresh: Bool, +P: List<&2, U32>, +c: U32, +P2: List<&2, U32>, +nx: U32, +nx2: U32) -> Data:
  match fresh:
    case True{}:
      D.P2({c == nx : U32}, D.P2({P2 == P : List<&2, U32>}, D.P2({nx2 == U32.inc(nx) : U32},
        {U32.is_lt(nx, 214748364) == True{} : Bool})))
    case False{}:
      D.P2({D.Has(P, c) == True{} : Bool}, D.P2({P2 == Del(P, c) : List<&2, U32>}, {nx2 == nx : U32}))

def Al.post(+r: Nat, +R: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +K: U32, +F: U32, +P: List<&2, U32>,
  +Q: List<&2, U32>, +zs: List<&2, D.Zs>, w: Aw, +rg: List<&2, U32>, +ms: Cr.Cir.Cells, +nx2: U32) -> Data:
  match w:
    case Aw{+c, +fresh, +P2, +Q2, +ws, +a}:
      +n = Nat.sub(U32.to_nat(nx), U32.to_nat(F))
      +n2 = Nat.sub(U32.to_nat(nx2), U32.to_nat(F))
      D.P2({rg == List.set(&2, U32, Rp(a, D.Rg.ex(63n, R, 0n)), r, c) : List<&2, U32>},
      D.P2({ms == Cr.Cir.Cells.set(W1s(ws, m), c, Cr.Cir.Cell.zero()) : Cr.Cir.Cells},
      D.P2({W1s.pt(ws, m, c) == True{} : Bool},
      D.P2(Al.how(fresh, P, c, P2, nx, nx2),
      D.P2({D.AL(ms, T.tm.reg(a, 0n), P2, Q2, zs, K, F, nx2) == True{} : Bool},
      D.P2({U32.is_le(F, c) == True{} : Bool},
      D.P2({Cr.Cir.is_cell(c, K, F, nx2) == True{} : Bool},
      D.P2({D.Has(P2, c) == False{} : Bool},
      D.P2(D.Tb(ms),
      D.P2({D.Kept(n, m, ms, F, [c], P2, F, n, n2, Q, Q2, Nil{}, Nil{}) == True{} : Bool},
        {D.Pc(n2, ms, Q2, F, c) == 0n : Nat}))))))))))

# the budget of an allocation from the pend list Q at next nx: a new cell
# is taken only when Q is empty, and needs 20 (nx + 1) bytes
def Al.b(+Q: List<&2, U32>, +nx: U32) -> Nat:
  match Q:
    case Nil{}:
      Nat.mul(20n, 1n+U32.to_nat(nx))
    case Con{_, _}:
      0n

# The allocation's run: a new cell
# --------------------------------

# 291 <= nx, and K < nx, for the cells from F on
def al.hz(+K: U32, +F: U32, +nx: U32, hk: {U32.is_le(290, K) == True{} : Bool}, hkf: {U32.is_lt(K, F) == True{} : Bool},
  hfn: {U32.is_le(F, nx) == True{} : Bool}) -> N.Le(291n, U32.to_nat(nx)):
  N.le_trans(291n, 1n+U32.to_nat(K), U32.to_nat(nx), K.U.le(290, K, hk),
    N.le_trans(1n+U32.to_nat(K), U32.to_nat(F), U32.to_nat(nx), K.U.lt(K, F, hkf), K.U.le(F, nx, hfn)))

def al.hk(+K: U32, +F: U32, +nx: U32, hkf: {U32.is_lt(K, F) == True{} : Bool}, hfn: {U32.is_le(F, nx) == True{} : Bool}) ->
  N.Le(1n+U32.to_nat(K), U32.to_nat(nx)):
  N.le_trans(1n+U32.to_nat(K), U32.to_nat(F), U32.to_nat(nx), K.U.lt(K, F, hkf), K.U.le(F, nx, hfn))

# the new cell nx is a cell once next is nx + 1
def al.cell.new(+K: U32, +F: U32, +nx: U32, hfn: {U32.is_le(F, nx) == True{} : Bool},
  hb: N.Le(1n+U32.to_nat(nx), U32.to_nat(214748364))) -> {Cr.Cir.is_cell(nx, K, F, U32.inc(nx)) == True{} : Bool}:
  +X = U32.to_nat(nx)
  K.Bo.or_ir(Bool.and(Bool.not(U32.is_zero(nx)), U32.is_le(nx, K)), Bool.and(U32.is_le(F, nx), U32.is_lt(nx, U32.inc(nx))),
    K.Bo.and_i(U32.is_le(F, nx), U32.is_lt(nx, U32.inc(nx)), hfn,
      K.U.lt_t(nx, U32.inc(nx), N.le_rw_r(1n+X, 1n+X, U32.to_nat(U32.inc(nx)),
        Equal.sym(Nat, U32.to_nat(U32.inc(nx)), 1n+X, K.Ar.u.inc(nx, 214748364, hb)), N.le_refl(1n+X)))))

# Cir's alloc takes nx, when the memory has room: the registers rg get it in r
def al.took(+r: Nat, +R: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +F: U32, +K: U32, +pg: U32, +L: U32,
  +I: List<&2, Word(8n)>, +p: U32, hr: {Nat.is_lt(r, 63n) == True{} : Bool}) ->
  {Cr.Cir.exec.bump.of(r, nx, D.S(D.Rg.ex(63n, R, 0n), m, nx, F, K, pg, L, I), Some{p}) ==
    Cr.Cir.Out.next{D.S(List.set(&2, U32, D.Rg.ex(63n, R, 0n), r, nx), Cr.Cir.Cells.set(m, nx, Cr.Cir.Cell.zero()), U32.inc(nx), F, K, p, L, I)} : Cr.Cir.Out}:
  +regs = D.Rg.ex(63n, R, 0n)
  +M2 = Cr.Cir.Cells.set(m, nx, Cr.Cir.Cell.zero())
  %Equal.sym(Bool, Nat.is_lt(r, 63n), True{}, hr) :
    {Cr.Cir.exec.set.of(Cr.Cir.regs.set.if(_, regs, r, nx), Cr.Cir.State{regs, M2, U32.inc(nx), F, K, p, L, I, Nil{}, 0}) ==
      Cr.Cir.Out.next{D.S(List.set(&2, U32, regs, r, nx), M2, U32.inc(nx), F, K, p, L, I)} : Cr.Cir.Out}
  {==}

# the registers with pend 0, and with pend set to 0
def al.rp0(+R: List<&2, U32>, e3: {T.tm.reg(R, 3n) == 0 : U32}) ->
  {D.Rg.ex(63n, R, 0n) == Rp([0, T.tm.reg(R, 4n), T.tm.reg(R, 5n), T.tm.reg(R, 6n), T.tm.reg(R, 7n)], D.Rg.ex(63n, R, 0n)) : List<&2, U32>}:
  %e3 : {D.Rg.ex(63n, R, 0n) == Rp([_, T.tm.reg(R, 4n), T.tm.reg(R, 5n), T.tm.reg(R, 6n), T.tm.reg(R, 7n)], D.Rg.ex(63n, R, 0n)) : List<&2, U32>}
  {==}

# a new cell nx, when the memory has room: Al.post of it
def al.fresh.got(+r: Nat, +R: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +F: U32, +K: U32, +pg: U32, +L: U32,
  +I: List<&2, Word(8n)>, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +p: U32,
  +hal: {D.AL(m, 0, P, Nil{}, zs, K, F, nx) == True{} : Bool}, +e3: {T.tm.reg(R, 3n) == 0 : U32},
  +hr: {Nat.is_lt(r, 63n) == True{} : Bool}, +hk: {U32.is_le(290, K) == True{} : Bool}, +hkf: {U32.is_lt(K, F) == True{} : Bool},
  +hfn: {U32.is_le(F, nx) == True{} : Bool}, +tb: D.Tb(m), +eb: {U32.is_lt(nx, 214748364) == True{} : Bool}) ->
  D.Ok(Cr.Cir.exec.bump.of(r, nx, D.S(D.Rg.ex(63n, R, 0n), m, nx, F, K, pg, L, I), Some{p}), F, K, L, I, Al.b(Nil{}, nx),
    rg => ms => nx2 => pg2 => D.Ex(Aw, w => Al.post(r, R, m, nx, K, F, P, Nil{}, zs, w, rg, ms, nx2))):
  (t0, _) = tb
  +regs = D.Rg.ex(63n, R, 0n)
  +M2 = Cr.Cir.Cells.set(m, nx, Cr.Cir.Cell.zero())
  +N2 = U32.inc(nx)
  +n = Nat.sub(U32.to_nat(nx), U32.to_nat(F))
  +n2 = Nat.sub(U32.to_nat(N2), U32.to_nat(F))
  +a = {[0, T.tm.reg(R, 4n), T.tm.reg(R, 5n), T.tm.reg(R, 6n), T.tm.reg(R, 7n)] : List<&2, U32>}
  +hz = al.hz(K, F, nx, hk, hkf, hfn)
  +hk1 = al.hk(K, F, nx, hkf, hfn)
  +hb = K.U.lt(nx, 214748364, eb)
  +C1 = D.AL.cells(P, m, P, Nil{}, zs, K, F, nx)
  +L1 = D.Lt(n, m, Nil{}, F, nx)
  +ha = {hal : {Bool.and(D.Nodup(P), Bool.and(C1, L1)) == True{} : Bool}}
  +hr2 = K.Bo.and_r(D.Nodup(P), Bool.and(C1, L1), ha)
  +hc = K.Bo.and_l(C1, L1, hr2)
  +hlt = K.Bo.and_r(C1, L1, hr2)
  +cnt = Equal.sym(Nat, n2, 1n+n, K.Ar.cnt.new(F, nx, hfn, hb))
  +e0 = {{==} : {0 == T.tm.reg(a, 0n) : U32}}
  K.Ok.eq(Cr.Cir.exec.bump.of(r, nx, D.S(regs, m, nx, F, K, pg, L, I), Some{p}), Cr.Cir.Out.next{D.S(List.set(&2, U32, regs, r, nx), M2, N2, F, K, p, L, I)},
    F, K, L, I, Al.b(Nil{}, nx), rg => ms => nx2 => pg2 => D.Ex(Aw, w => Al.post(r, R, m, nx, K, F, P, Nil{}, zs, w, rg, ms, nx2)),
    Equal.sym(Cr.Cir.Out, Cr.Cir.exec.bump.of(r, nx, D.S(regs, m, nx, F, K, pg, L, I), Some{p}),
      Cr.Cir.Out.next{D.S(List.set(&2, U32, regs, r, nx), M2, N2, F, K, p, L, I)}, al.took(r, R, m, nx, F, K, pg, L, I, p, hr)),
    K.Ok.next(List.set(&2, U32, regs, r, nx), M2, N2, F, K, p, L, I, Al.b(Nil{}, nx),
      rg => ms => nx2 => pg2 => D.Ex(Aw, w => Al.post(r, R, m, nx, K, F, P, Nil{}, zs, w, rg, ms, nx2)),
      (Aw{nx, True{}, P, Nil{}, Nil{}, a},
        (Equal.cong(List<&2, U32>, List<&2, U32>, xs => List.set(&2, U32, xs, r, nx), regs, Rp(a, regs), al.rp0(R, e3)),
        ({==},
        ({==},
        (({==}, ({==}, ({==}, eb))),
        ((%e0 : {D.AL(M2, _, P, Nil{}, zs, K, F, N2) == True{} : Bool}; K.al.fresh(m, P, zs, K, F, nx, hal, t0, hz, hfn, hb, hk1)),
        (hfn,
        (al.cell.new(K, F, nx, hfn, hb),
        (K.has.lt(P, m, P, Nil{}, zs, K, F, nx, nx, N.le_refl(U32.to_nat(nx)), hc),
        (K.tb.set(m, nx, Cr.Cir.Cell.zero(), hz, tb),
        ((%cnt : {D.Kept(n, m, M2, F, [nx], P, F, n, _, Nil{}, Nil{}, Nil{}, Nil{}) == True{} : Bool};
          K.kept.fresh(n, m, nx, F, P, F, K.Ar.ne.own(F, nx, hfn), t0, hz, hfn)),
        (%cnt : {D.Pc(_, M2, Nil{}, F, nx) == 0n : Nat};
          (%Equal.sym(Nat, D.Pc(1n+n, M2, Nil{}, F, nx), D.Pc(n, m, Nil{}, F, nx), K.pc.new(m, F, nx, Nil{}, nx, t0, hz, hfn)) :
            {_ == 0n : Nat}; K.lt.pc0(n, m, Nil{}, F, nx, hlt))))))))))))))))

# a new cell, or out of memory for want of room
def al.fresh.room(mo: Maybe<&2, U32>, +r: Nat, +R: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +F: U32, +K: U32, +pg: U32,
  +L: U32, +I: List<&2, Word(8n)>, +P: List<&2, U32>, +zs: List<&2, D.Zs>,
  emo: {Cr.Cir.room(U32.add(Cr.Cir.at(nx), 19), pg, L) == mo : Maybe<&2, U32>},
  hal: {D.AL(m, 0, P, Nil{}, zs, K, F, nx) == True{} : Bool}, e3: {T.tm.reg(R, 3n) == 0 : U32},
  hr: {Nat.is_lt(r, 63n) == True{} : Bool}, hk: {U32.is_le(290, K) == True{} : Bool}, hkf: {U32.is_lt(K, F) == True{} : Bool},
  hfn: {U32.is_le(F, nx) == True{} : Bool}, tb: D.Tb(m), eb: {U32.is_lt(nx, 214748364) == True{} : Bool}) ->
  D.Ok(Cr.Cir.exec.bump.of(r, nx, D.S(D.Rg.ex(63n, R, 0n), m, nx, F, K, pg, L, I), mo), F, K, L, I, Al.b(Nil{}, nx),
    rg => ms => nx2 => pg2 => D.Ex(Aw, w => Al.post(r, R, m, nx, K, F, P, Nil{}, zs, w, rg, ms, nx2))):
  match mo:
    case None{}:
      K.oom.room(L, pg, nx, emo)
    case Some{+p}:
      al.fresh.got(r, R, m, nx, F, K, pg, L, I, P, zs, p, hal, e3, hr, hk, hkf, hfn, tb, eb)

# next below 214748364 gives a new cell or out of memory for want of room;
# else out of memory
def al.fresh.fits(b: Bool, +r: Nat, +R: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +F: U32, +K: U32, +pg: U32,
  +L: U32, +I: List<&2, Word(8n)>, +P: List<&2, U32>, +zs: List<&2, D.Zs>, eb: {U32.is_lt(nx, 214748364) == b : Bool},
  hal: {D.AL(m, 0, P, Nil{}, zs, K, F, nx) == True{} : Bool}, e3: {T.tm.reg(R, 3n) == 0 : U32},
  hr: {Nat.is_lt(r, 63n) == True{} : Bool}, hk: {U32.is_le(290, K) == True{} : Bool}, hkf: {U32.is_lt(K, F) == True{} : Bool},
  hfn: {U32.is_le(F, nx) == True{} : Bool}, tb: D.Tb(m)) ->
  D.Ok(Cr.Cir.exec.bump.if(b, r, nx, pg, L, D.S(D.Rg.ex(63n, R, 0n), m, nx, F, K, pg, L, I)), F, K, L, I, Al.b(Nil{}, nx),
    rg => ms => nx2 => pg2 => D.Ex(Aw, w => Al.post(r, R, m, nx, K, F, P, Nil{}, zs, w, rg, ms, nx2))):
  match b:
    case False{}:
      K.oom.big(L, nx, eb)
    case True{}:
      al.fresh.room(Cr.Cir.room(U32.add(Cr.Cir.at(nx), 19), pg, L), r, R, m, nx, F, K, pg, L, I, P, zs, {==}, hal, e3, hr,
        hk, hkf, hfn, tb, eb)

# M.alloc(r) with an empty pend list: Cir's alloc
def al.fresh.ok(+f: Nat, +r: Nat, +R: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +F: U32, +K: U32, +pg: U32, +L: U32,
  +I: List<&2, Word(8n)>, +P: List<&2, U32>, +zs: List<&2, D.Zs>,
  hal: {D.AL(m, T.tm.reg(R, 3n), P, Nil{}, zs, K, F, nx) == True{} : Bool}, hr: {Nat.is_lt(r, 63n) == True{} : Bool},
  hk: {U32.is_le(290, K) == True{} : Bool}, hkf: {U32.is_lt(K, F) == True{} : Bool}, hfn: {U32.is_le(F, nx) == True{} : Bool},
  tb: D.Tb(m)) ->
  D.Ok(Cr.Cir.exec(1n+f, Mc.M.alloc(r), D.S(D.Rg.ex(63n, R, 0n), m, nx, F, K, pg, L, I)), F, K, L, I, Al.b(Nil{}, nx),
    rg => ms => nx2 => pg2 => D.Ex(Aw, w => Al.post(r, R, m, nx, K, F, P, Nil{}, zs, w, rg, ms, nx2))):
  +regs = D.Rg.ex(63n, R, 0n)
  +st = D.S(regs, m, nx, F, K, pg, L, I)
  +pd = T.tm.reg(R, 3n)
  +h2 = hal
  +ch = K.Bo.and_l(D.Chain(Nil{}, m, pd), D.Nodup(Nil{}), K.Bo.and_l(Bool.and(D.Chain(Nil{}, m, pd), D.Nodup(Nil{})),
    Bool.and(Bool.and(D.Sub(Nil{}, P), D.Nodup(P)), Bool.and(D.AL.cells(P, m, P, Nil{}, zs, K, F, nx),
      D.Lt(Nat.sub(U32.to_nat(nx), U32.to_nat(F)), m, Nil{}, F, nx))), h2))
  +e3 = K.U.eq(pd, 0, ch)
  +hal0 = {%e3 : {D.AL(m, _, P, Nil{}, zs, K, F, nx) == True{} : Bool}; h2 : {D.AL(m, 0, P, Nil{}, zs, K, F, nx) == True{} : Bool}}
  +h3 = {%e3 : {List.get(&2, U32, regs, 3n) == Some{_} : Maybe<&2, U32>}; {==} : {List.get(&2, U32, regs, 3n) == Some{0} : Maybe<&2, U32>}}
  +ex1 = {{==} : {Sr.X.st(regs, m, nx, F, K, pg, L, I) == st : Cr.Cir.State}}
  +e1 = {%ex1 : {Cr.Cir.exec(1n+f, Mc.M.alloc(r), _) == Cr.Cir.exec.alloc(r, _) : Cr.Cir.Out}; Sr.alloc.eq.fresh(1n+f, regs, m, nx, F, K, pg, L, I, r, h3) :
    {Cr.Cir.exec(1n+f, Mc.M.alloc(r), st) == Cr.Cir.exec.alloc(r, st) : Cr.Cir.Out}}
  +o2 = Cr.Cir.exec.bump.if(U32.is_lt(nx, 214748364), r, nx, pg, L, st)
  K.Ok.eq(Cr.Cir.exec(1n+f, Mc.M.alloc(r), st), o2, F, K, L, I, Al.b(Nil{}, nx),
    rg => ms => nx2 => pg2 => D.Ex(Aw, w => Al.post(r, R, m, nx, K, F, P, Nil{}, zs, w, rg, ms, nx2)),
    Equal.trans(Cr.Cir.Out, o2, Cr.Cir.exec.alloc(r, st), Cr.Cir.exec(1n+f, Mc.M.alloc(r), st), {==},
      Equal.sym(Cr.Cir.Out, Cr.Cir.exec(1n+f, Mc.M.alloc(r), st), Cr.Cir.exec.alloc(r, st), e1)),
    al.fresh.fits(U32.is_lt(nx, 214748364), r, R, m, nx, F, K, pg, L, I, P, zs, {==}, hal0, e3, hr, hk, hkf, hfn, tb))

# M.alloc(r): the cell that it gives is a new one or the first of the pend
# list, whose reuse drops the counts of its parts; the allocation's invariant
# holds again, without that cell; the other cells keep their fields 0, 2 to 4
# and their counts follow their pointers (Kept), and none points to the cell;
# it runs out of memory only for a new cell
def Al.ok(+f: Nat, +r: Nat, +R: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +F: U32, +K: U32, +pg: U32, +L: U32,
  +I: List<&2, Word(8n)>, +P: List<&2, U32>, +Q: List<&2, U32>, +zs: List<&2, D.Zs>,
  hal: {D.AL(m, T.tm.reg(R, 3n), P, Q, zs, K, F, nx) == True{} : Bool},
  hr: {Bool.and(Nat.is_lt(r, 63n), Bool.not(Bool.and(Nat.is_le(3n, r), Nat.is_le(r, 7n)))) == True{} : Bool},
  hk: {U32.is_le(290, K) == True{} : Bool}, hkf: {U32.is_lt(K, F) == True{} : Bool}, hfn: {U32.is_le(F, nx) == True{} : Bool},
  tb: D.Tb(m)) ->
  D.Ok(Cr.Cir.exec(1n+f, Mc.M.alloc(r), D.S(D.Rg.ex(63n, R, 0n), m, nx, F, K, pg, L, I)), F, K, L, I, Al.b(Q, nx),
    rg => ms => nx2 => pg2 => D.Ex(Aw, w => Al.post(r, R, m, nx, K, F, P, Q, zs, w, rg, ms, nx2))):
  ?TODO

# no garbage cell of P points to the cells ns
def Pz(ns: List<&2, U32>, +P: List<&2, U32>, +m: Cr.Cir.Cells) -> Bool:
  match ns:
    case Nil{}:
      True{}
    case Con{+n, rest}:
      Bool.and(Nat.is_eq(D.Pp(P, m, n), 0n), Pz(rest, P, m))

# What a walk keeps from its start
# --------------------------------

# the start's cells m0, garbage P0, pend list Q0 and next N0, the cells E
# that the walk may not read, the roots rs, the temporaries ts, the kept
# cells kc, the base B0 of the own cells, the zombie sizes zs, the roots S
# that the result is made of (the source and the locals), and the mode hx
# (the result's term is exact when hx)
type Sc is Data:
  Sc{m0: Cr.Cir.Cells, P0: List<&2, U32>, Q0: List<&2, U32>, N0: U32, E: List<&2, U32>, rs: List<&2, D.Rt>,
    ts: List<&2, D.Tmp>, kc: List<&2, D.Kc>, B0: Nat, zs: List<&2, D.Zs>, S: List<&2, D.Rt>, hx: Bool}

# The accounting
# --------------
#
# What a round of the walk keeps of the copy's accounting (the cover, the
# closure, the count and what stays: copy_substitution.bend's Pre and Post):
# the walk's cells (the root and the frames' cells) are temporaries of the
# walk, and the done parts are roots; a pending part counts its nodes, still
# to make, and its source's pointer, which no count counts.

# the walk's cells: the root, and the frames' cells
def Wl(+root: U32, frs: List<&2, Fr>) -> List<&2, U32>:
  Con{root, Ns(frs)}

# the nodes of a part of the status s still to make: its copy's, when it is
# pending
def Pd.at(+mo: D.Mo, s: St, t: Bk.Term, +dd: Nat) -> Nat:
  match s:
    case St.pe{}:
      Pg.Term.size(D.Mo.F(mo, t, dd))
    case _:
      0n

# the nodes that the frames' pending parts still make
def Pd(+mo: D.Mo, frs: List<&2, Fr>) -> Nat:
  match frs:
    case Nil{}:
      0n
    case Con{Fr{_, +h, _, _, _, _, _, +t2, +t3, +t4, +s2, +s3, +s4, +d}, rest}:
      +tg = Fr.tag(h)
      Nat.add(Pd.at(mo, s2, t2, Nat.add(d, Tg.b(tg, 2n))), Nat.add(Pd.at(mo, s3, t3, Nat.add(d, Tg.b(tg, 3n))),
        Nat.add(Pd.at(mo, s4, t4, Nat.add(d, Tg.b(tg, 4n))), Pd(mo, rest))))

# the source's cell y of a part of the status s, when it is pending
def Pe.at(s: St, +y: U32, +rest: List<&2, U32>) -> List<&2, U32>:
  match s:
    case St.pe{}:
      Con{y, rest}
    case _:
      rest

# the sources' cells of the frames' pending parts, which their fields point to
def Pe(frs: List<&2, Fr>) -> List<&2, U32>:
  match frs:
    case Nil{}:
      Nil{}
    case Con{Fr{_, _, _, _, +y2, +y3, +y4, _, _, _, +s2, +s3, +s4, _}, rest}:
      Pe.at(s2, y2, Pe.at(s3, y3, Pe.at(s4, y4, Pe(rest))))

# the copy in the field v of a part of the status s, as a root, when it is done
def Dn.at(+mo: D.Mo, s: St, +v: U32, t: Bk.Term, +dd: Nat, +rest: List<&2, D.Rt>) -> List<&2, D.Rt>:
  match s:
    case St.dn{}:
      Con{D.Rt{0n, v, D.Mo.F(mo, t, dd)}, rest}
    case _:
      rest

# the frames' done parts, as roots
def Dn(+mo: D.Mo, +m: Cr.Cir.Cells, frs: List<&2, Fr>) -> List<&2, D.Rt>:
  match frs:
    case Nil{}:
      Nil{}
    case Con{Fr{+n, +h, _, _, _, _, _, +t2, +t3, +t4, +s2, +s3, +s4, +d}, rest}:
      +tg = Fr.tag(h)
      Dn.at(mo, s2, D.Fd(2n, m, n), t2, Nat.add(d, Tg.b(tg, 2n)), Dn.at(mo, s3, D.Fd(3n, m, n), t3, Nat.add(d, Tg.b(tg, 3n)),
        Dn.at(mo, s4, D.Fd(4n, m, n), t4, Nat.add(d, Tg.b(tg, 4n)), Dn(mo, m, rest))))

# each of the cells T, but the cells ws, holds no flag
def NfX(T: List<&2, U32>, +ms: Cr.Cir.Cells, +ws: List<&2, U32>) -> Bool:
  match T:
    case Nil{}:
      True{}
    case Con{+c, rest}:
      Bool.and(Bool.or(D.Has(ws, c), U32.is_zero(U32.and(D.Fd(0n, ms, c), 7936))), NfX(rest, ms, ws))

# the accounting at a round of a walk of the mode mo, from the start's cells
# m0, garbage P0 and next N0, of the source term t: the cover (the done
# parts among the roots, the walk's cells among the temporaries' cells), the
# closure (but at the walk's cells), the start's count (B0), the count of
# the cells taken so far (with the nodes that the pending parts still make,
# at most the result's and the root), the frames and their pending nodes
# within the same, the taken cells T (the walk's among them, the others with
# no flag), what stays, and next at most 214748364 once it grows
def Acc(+mo: D.Mo, +m0: Cr.Cir.Cells, +K: U32, +F: U32, +P0: List<&2, U32>, +Q0: List<&2, U32>, +N0: U32, +E: List<&2, U32>,
  +rs: List<&2, D.Rt>, +ts: List<&2, D.Tmp>, +B0: Nat, +t: Bk.Term, +m: Cr.Cir.Cells, +nx: U32, +frs: List<&2, Fr>,
  +P: List<&2, U32>, +Q: List<&2, U32>, +root: U32, +T: List<&2, U32>) -> Data:
  +n = Nat.sub(U32.to_nat(nx), U32.to_nat(F))
  +n0 = Nat.sub(U32.to_nat(N0), U32.to_nat(F))
  +hl = D.Tmp.held(ts)
  +wl = Wl(root, frs)
  +C = {1n+Pg.Term.size(D.Mo.F(mo, t, 0n)) : Nat}
  D.P2({D.Cv(n, m, F, P, List.append(&2, D.Rt, rs, List.append(&2, D.Rt, hl, Dn(mo, m, frs))),
    List.append(&2, U32, wl, List.append(&2, U32, D.Tmp.cells(ts), E))) == True{} : Bool},
  D.P2({D.Clo(n, m, F, Q, D.Tmp.cells(ts), D.Rt.cells(hl), List.append(&2, U32, wl, E)) == True{} : Bool},
  D.P2(N.Le(n0, Nat.add(B0, List.length(&2, U32, P0))),
  D.P2(N.Le(Nat.add(U32.to_nat(nx), Nat.add(List.length(&2, U32, P0), Pd(mo, frs))),
    Nat.add(U32.to_nat(N0), Nat.add(List.length(&2, U32, P), C))),
  D.P2(N.Le(Nat.add(Pd(mo, frs), List.length(&2, Fr, frs)), C),
  D.P2({D.Incl.go(T, P0, N0) == True{} : Bool},
  D.P2({D.Sub(wl, T) == True{} : Bool},
  D.P2({NfX(T, m, wl) == True{} : Bool},
  D.P2({D.Same(U32.to_nat(K), m0, m, 1) == True{} : Bool},
  D.P2({D.Kept(n0, m0, m, F, T, P, F, n0, n, Q0, Q, Pe(frs), Nil{}) == True{} : Bool},
    {Bool.or(U32.is_eq(nx, N0), U32.is_le(nx, 214748364)) == True{} : Bool}))))))))))
